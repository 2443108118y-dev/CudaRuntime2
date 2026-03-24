#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <thread>
#include <atomic>
#include <mutex>
#include <chrono>
#include <iomanip>
#include <csignal>
#include <cstring>
#include <openssl/evp.h>
#include <openssl/ec.h>
#include <openssl/obj_mac.h>
#include <openssl/sha.h>
#include <openssl/ripemd.h>
#include <openssl/bn.h>
#include <openssl/aes.h>

// ---------- 全局配置 ----------
const std::string ENCRYPTED_KEY = "6PnQmAyBky9ZXJyZBv9QSGRUXkKh9HfnVsZWPn4YtcwoKy5vufUgfA3Ld7";
const std::string TARGET_ADDRESS = "1JxWyNrkgYvgsHu8hVQZqTXEB9RftRGP5m";
std::atomic<bool> found(false);
std::atomic<size_t> tested_count(0);
std::atomic<bool> exit_progress(false);
std::mutex cout_mutex;

// ---------- Base58 解码 ----------
bool base58_decode(const std::string& encoded, std::vector<uint8_t>& out) {
    const char* base58_chars = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    std::vector<uint8_t> temp(encoded.size() * 2, 0);
    size_t out_len = 0;
    for (char c : encoded) {
        const char* pos = strchr(base58_chars, c);
        if (!pos) return false;
        int carry = pos - base58_chars;
        for (size_t i = 0; i < out_len; ++i) {
            carry += temp[i] * 58;
            temp[i] = carry & 0xFF;
            carry >>= 8;
        }
        while (carry) {
            temp[out_len++] = carry & 0xFF;
            carry >>= 8;
        }
    }
    // 处理前导零
    for (size_t i = 0; i < encoded.size() && encoded[i] == '1'; ++i) {
        temp[out_len++] = 0;
    }
    out.assign(temp.rbegin(), temp.rbegin() + out_len);
    return true;
}

// ---------- 双 SHA256 ----------
void sha256d(const uint8_t* data, size_t len, uint8_t* out) {
    uint8_t hash1[SHA256_DIGEST_LENGTH];
    SHA256(data, len, hash1);
    SHA256(hash1, SHA256_DIGEST_LENGTH, out);
}

// ---------- 从私钥字节生成比特币地址 ----------
bool private_key_to_address(const std::vector<uint8_t>& priv_key, bool compressed, std::string& address) {
    EC_KEY* ec_key = EC_KEY_new_by_curve_name(NID_secp256k1);
    if (!ec_key) return false;
    BIGNUM* bn = BN_bin2bn(priv_key.data(), priv_key.size(), nullptr);
    if (!bn) {
        EC_KEY_free(ec_key);
        return false;
    }
    EC_KEY_set_private_key(ec_key, bn);
    const EC_POINT* pub_key = EC_KEY_get0_public_key(ec_key);
    if (!pub_key) {
        EC_KEY_generate_key(ec_key);
        pub_key = EC_KEY_get0_public_key(ec_key);
    }
    BN_free(bn);
    if (!pub_key) {
        EC_KEY_free(ec_key);
        return false;
    }
    uint8_t pub_bytes[65];
    size_t pub_len;
    if (compressed) {
        pub_len = EC_POINT_point2oct(EC_KEY_get0_group(ec_key), pub_key, POINT_CONVERSION_COMPRESSED, pub_bytes, 33, nullptr);
    }
    else {
        pub_len = EC_POINT_point2oct(EC_KEY_get0_group(ec_key), pub_key, POINT_CONVERSION_UNCOMPRESSED, pub_bytes, 65, nullptr);
    }
    EC_KEY_free(ec_key);
    if (pub_len == 0) return false;
    uint8_t sha[SHA256_DIGEST_LENGTH];
    SHA256(pub_bytes, pub_len, sha);
    uint8_t ripe[RIPEMD160_DIGEST_LENGTH];
    RIPEMD160(sha, SHA256_DIGEST_LENGTH, ripe);
    std::vector<uint8_t> addr_hash(1 + RIPEMD160_DIGEST_LENGTH);
    addr_hash[0] = 0x00;
    memcpy(&addr_hash[1], ripe, RIPEMD160_DIGEST_LENGTH);
    uint8_t checksum[SHA256_DIGEST_LENGTH];
    sha256d(addr_hash.data(), addr_hash.size(), checksum);
    addr_hash.insert(addr_hash.end(), checksum, checksum + 4);
    const char* base58_chars = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    std::vector<uint8_t> temp(addr_hash.size() * 2);
    size_t out_len = 0;
    for (uint8_t b : addr_hash) {
        int carry = b;
        for (size_t i = 0; i < out_len; ++i) {
            carry += temp[i] * 256;
            temp[i] = carry % 58;
            carry /= 58;
        }
        while (carry) {
            temp[out_len++] = carry % 58;
            carry /= 58;
        }
    }
    address.clear();
    for (size_t i = 0; i < addr_hash.size() && addr_hash[i] == 0; ++i) {
        address += '1';
    }
    for (size_t i = out_len; i > 0; --i) {
        address += base58_chars[temp[i - 1]];
    }
    return true;
}

// ---------- BIP-38 解密核心 ----------
// 注意：此函数实现基于 BIP-38 规范，但盐和加密数据的长度处理需根据实际格式调整。
// 若发现解密失败率高，请参考官方实现（如 Bitcoin Core）确认长度。
bool bip38_decrypt(const std::string& encrypted, const std::string& password,
    std::vector<uint8_t>& priv_key_out, bool& compressed) {
    // 1. Base58Check 解码
    std::vector<uint8_t> data;
    if (!base58_decode(encrypted, data)) return false;
    if (data.size() < 7) return false;
    // 验证校验和
    size_t len = data.size() - 4;
    uint8_t checksum_calc[SHA256_DIGEST_LENGTH];
    sha256d(data.data(), len, checksum_calc);
    if (memcmp(checksum_calc, data.data() + len, 4) != 0) return false;
    data.resize(len); // 去掉校验和

    // 2. 检查版本和标志
    if (data[0] != 0x01 || data[1] != 0x42) return false;
    uint8_t flag = data[2];
    compressed = (flag & 0x20) != 0;
    uint8_t address_hash[4];
    memcpy(address_hash, &data[3], 4);

    // 3. 提取盐和加密数据
    size_t offset = 7; // 前7字节: 版本(2)+flag(1)+hash(4)
    std::vector<uint8_t> salt;
    std::vector<uint8_t> encrypted_part;
    if (compressed) {
        // 压缩格式: 盐16字节, 加密数据48字节(32字节私钥+4字节校验和+12字节混淆)
        if (data.size() < offset + 16 + 48) return false;
        salt.assign(data.begin() + offset, data.begin() + offset + 16);
        encrypted_part.assign(data.begin() + offset + 16, data.begin() + offset + 16 + 48);
    }
    else {
        // 非压缩格式: 盐8字节, 加密数据36字节(32字节私钥+4字节校验和)
        if (data.size() < offset + 8 + 36) return false;
        salt.assign(data.begin() + offset, data.begin() + offset + 8);
        encrypted_part.assign(data.begin() + offset + 8, data.begin() + offset + 8 + 36);
    }

    // 4. 使用 scrypt 派生密钥
    uint8_t derived[64];
    if (EVP_PBE_scrypt(password.c_str(), password.size(),
        salt.data(), salt.size(),
        16384, 8, 8,      // N, r, p
        0, derived, 64) != 1) {
        return false;
    }

    // 5. 准备 AES 解密
    const uint8_t* key1 = derived;        // 前32字节作为 AES 密钥
    const uint8_t* key2 = derived + 32;   // 后32字节用于 XOR

    // 6. 解密
    EVP_CIPHER_CTX* ctx = EVP_CIPHER_CTX_new();
    if (!ctx) return false;
    EVP_DecryptInit_ex(ctx, EVP_aes_256_ecb(), nullptr, key1, nullptr);
    EVP_CIPHER_CTX_set_padding(ctx, 0); // ECB 模式不需要填充

    std::vector<uint8_t> decrypted(encrypted_part.size());
    int out_len = 0, temp_len = 0;
    if (EVP_DecryptUpdate(ctx, decrypted.data(), &out_len, encrypted_part.data(), encrypted_part.size()) != 1) {
        EVP_CIPHER_CTX_free(ctx);
        return false;
    }
    if (EVP_DecryptFinal_ex(ctx, decrypted.data() + out_len, &temp_len) != 1) {
        EVP_CIPHER_CTX_free(ctx);
        return false;
    }
    out_len += temp_len;
    EVP_CIPHER_CTX_free(ctx);

    // 7. 与 key2 进行 XOR
    for (size_t i = 0; i < decrypted.size(); ++i) {
        decrypted[i] ^= key2[i % 32];
    }

    // 8. 提取私钥和校验和
    std::vector<uint8_t> priv_key;
    uint8_t checksum_expected[4];
    if (compressed) {
        // 压缩格式: 前32字节私钥, 接着4字节校验和, 最后12字节忽略
        if (decrypted.size() < 32 + 4) return false;
        priv_key.assign(decrypted.begin(), decrypted.begin() + 32);
        memcpy(checksum_expected, decrypted.data() + 32, 4);
        // 验证校验和: 对私钥进行双SHA256，取前4字节
        uint8_t chk[SHA256_DIGEST_LENGTH];
        sha256d(priv_key.data(), priv_key.size(), chk);
        if (memcmp(chk, checksum_expected, 4) != 0) return false;
    }
    else {
        // 非压缩格式: 前32字节私钥，接着4字节校验和
        if (decrypted.size() < 32 + 4) return false;
        priv_key.assign(decrypted.begin(), decrypted.begin() + 32);
        memcpy(checksum_expected, decrypted.data() + 32, 4);
        uint8_t chk[SHA256_DIGEST_LENGTH];
        sha256d(priv_key.data(), priv_key.size(), chk);
        if (memcmp(chk, checksum_expected, 4) != 0) return false;
    }

    // 9. 验证地址哈希（快速筛选）
    std::string addr_test;
    if (!private_key_to_address(priv_key, compressed, addr_test)) return false;
    std::vector<uint8_t> addr_data;
    if (!base58_decode(addr_test, addr_data)) return false;
    if (addr_data.size() < 4 + 20) return false;
    uint8_t calc_hash[4];
    memcpy(calc_hash, &addr_data[1], 4);
    if (memcmp(calc_hash, address_hash, 4) != 0) return false;

    priv_key_out = std::move(priv_key);
    return true;
}

// ---------- 工作线程 ----------
void worker(const std::vector<std::string>& passwords, size_t start, size_t end) {
    try {
        for (size_t i = start; i < end && !found.load(); ++i) {
            const std::string& pwd = passwords[i];
            std::vector<uint8_t> priv_key;
            bool compressed = false;
            if (bip38_decrypt(ENCRYPTED_KEY, pwd, priv_key, compressed)) {
                std::string addr;
                if (private_key_to_address(priv_key, compressed, addr) && addr == TARGET_ADDRESS) {
                    found.store(true);
                    std::lock_guard<std::mutex> lock(cout_mutex);
                    std::cout << "\n密码找到: " << pwd << std::endl;
                    return;
                }
            }
            tested_count.fetch_add(1, std::memory_order_relaxed);
        }
    }
    catch (const std::exception& e) {
        std::lock_guard<std::mutex> lock(cout_mutex);
        std::cerr << "\n线程异常: " << e.what() << std::endl;
    }
    catch (...) {
        std::lock_guard<std::mutex> lock(cout_mutex);
        std::cerr << "\n线程发生未知异常" << std::endl;
    }
}

// ---------- 加载字典 ----------
std::vector<std::string> load_dictionary(const std::string& filename) {
    std::vector<std::string> passwords;
    std::ifstream file(filename, std::ios::binary);
    if (!file.is_open()) {
        return passwords;
    }
    std::string line;
    while (std::getline(file, line)) {
        if (!line.empty() && line.back() == '\r') line.pop_back();
        if (!line.empty()) passwords.push_back(line);
    }
    return passwords;
}

// ---------- 信号处理 ----------
volatile std::sig_atomic_t signal_received = 0;
void signal_handler(int sig) {
    if (sig == SIGINT) {
        signal_received = 1;
        found.store(true);
        exit_progress.store(true);
    }
}

int main() {
    std::signal(SIGINT, signal_handler);

    std::string dict_path;
    std::vector<std::string> candidates;
    while (candidates.empty()) {
        std::cout << "请输入字典文件路径 (输入 quit 退出): ";
        std::getline(std::cin, dict_path);
        if (dict_path == "quit") return 0;
        // 去除引号
        if (!dict_path.empty() && dict_path.front() == '\"' && dict_path.back() == '\"') {
            dict_path = dict_path.substr(1, dict_path.length() - 2);
        }
        candidates = load_dictionary(dict_path);
        if (candidates.empty()) {
            std::cout << "无法打开文件或文件为空，请重新输入。" << std::endl;
        }
    }

    size_t total = candidates.size();
    std::cout << "已加载 " << total << " 个密码，开始枚举..." << std::endl;

    unsigned int num_threads = std::thread::hardware_concurrency();
    if (num_threads == 0) num_threads = 4;
    std::cout << "使用 " << num_threads << " 个线程" << std::endl;

    std::vector<std::thread> workers;
    size_t chunk = total / num_threads;
    for (unsigned int t = 0; t < num_threads; ++t) {
        size_t start = t * chunk;
        size_t end = (t == num_threads - 1) ? total : start + chunk;
        workers.emplace_back(worker, std::ref(candidates), start, end);
    }

    // 进度显示线程
    auto progress_thread = std::thread([total]() {
        auto start_time = std::chrono::steady_clock::now();
        while (!found.load() && !exit_progress.load()) {
            std::this_thread::sleep_for(std::chrono::seconds(1));
            if (found.load() || exit_progress.load()) break;
            size_t current = tested_count.load(std::memory_order_relaxed);
            auto now = std::chrono::steady_clock::now();
            double elapsed = std::chrono::duration<double>(now - start_time).count();
            double speed = 0.0;
            if (elapsed > 0) {
                speed = current / elapsed;
            }
            double percent = (double)current / total * 100.0;
            double remaining = (total - current) / (speed + 1e-9);

            std::lock_guard<std::mutex> lock(cout_mutex);
            std::cout << "\r进度: " << current << "/" << total << " ("
                << std::fixed << std::setprecision(2) << percent << "%)  "
                << "速度: " << std::fixed << std::setprecision(0) << speed << " 个/秒  "
                << "剩余: " << std::fixed << std::setprecision(0) << remaining << " 秒    ";
            std::cout.flush();
        }
        });

    // 等待所有工作线程结束
    for (auto& th : workers) {
        th.join();
    }
    exit_progress.store(true);
    if (progress_thread.joinable()) progress_thread.join();

    // 输出最终统计
    size_t final_tested = tested_count.load();
    std::cout << "\n实际测试密码数: " << final_tested << std::endl;
    if (final_tested < total) {
        std::cout << "警告: 有 " << (total - final_tested) << " 个密码未被测试 (可能线程异常退出)" << std::endl;
    }

    if (signal_received) {
        std::cout << "程序被用户中断。" << std::endl;
    }
    else if (!found.load()) {
        std::cout << "字典中未找到密码。" << std::endl;
    }

    return 0;
}