#include <array>
#include <cstdint>
#include <cstdio>
#include <algorithm>

class GaloisField {
public:
    explicit GaloisField(uint16_t irreducible_polynomial)
        : polynomial_(irreducible_polynomial),
          reduction_byte_(static_cast<uint8_t>(irreducible_polynomial & 0xFF)) {
        generate_sboxes();
    }

    [[nodiscard]] uint8_t add(uint8_t a, uint8_t b) const noexcept {
        return static_cast<uint8_t>(a ^ b);
    }

    [[nodiscard]] uint8_t multiply(uint8_t a, uint8_t b) const noexcept {
        uint8_t result = 0;
        uint8_t multiplicand = a;
        for (int i = 0; i < 8; ++i) {
            const uint8_t mask = static_cast<uint8_t>(-((b >> i) & 1));
            result = static_cast<uint8_t>(result ^ (multiplicand & mask));
            multiplicand = xtime(multiplicand);
        }
        return result;
    }

    [[nodiscard]] uint8_t power(uint8_t base, uint8_t exponent) const noexcept {
        uint8_t result = 1;
        uint8_t current = base;
        for (int i = 0; i < 8; ++i) {
            const uint8_t mask = static_cast<uint8_t>(-((exponent >> i) & 1));
            const uint8_t selected =
                static_cast<uint8_t>((current & mask) | ((~mask) & 0x01));
            result = multiply(result, selected);
            current = multiply(current, current);
        }
        return result;
    }

    [[nodiscard]] uint8_t inverse(uint8_t a) const noexcept {
        return power(a, 254);
    }

    [[nodiscard]] const std::array<uint8_t, 256>& sbox() const noexcept {
        return sbox_;
    }

    [[nodiscard]] const std::array<uint8_t, 256>& inv_sbox() const noexcept {
        return inv_sbox_;
    }

private:
    [[nodiscard]] uint8_t xtime(uint8_t value) const noexcept {
        const uint8_t mask = static_cast<uint8_t>(-(value >> 7));
        return static_cast<uint8_t>((value << 1) ^ (mask & reduction_byte_));
    }

    [[nodiscard]] uint8_t affine(uint8_t value) const noexcept {
        uint8_t result = value;
        uint8_t rotated = value;
        for (int i = 0; i < 4; ++i) {
            rotated = static_cast<uint8_t>((rotated << 1) | (rotated >> 7));
            result = static_cast<uint8_t>(result ^ rotated);
        }
        return static_cast<uint8_t>(result ^ 0x63);
    }

    void generate_sboxes() noexcept {
        for (int i = 0; i < 256; ++i) {
            const uint8_t inv = inverse(static_cast<uint8_t>(i));
            sbox_[i] = affine(inv);
        }
        for (int i = 0; i < 256; ++i) {
            inv_sbox_[sbox_[i]] = static_cast<uint8_t>(i);
        }
    }

    uint16_t polynomial_;
    uint8_t reduction_byte_;
    std::array<uint8_t, 256> sbox_{};
    std::array<uint8_t, 256> inv_sbox_{};
};

class Aes128 {
public:
    static constexpr int BLOCK_SIZE = 16;
    static constexpr int NUM_ROUNDS = 10;
    using Block = std::array<uint8_t, BLOCK_SIZE>;

    Aes128(const GaloisField& gf, const Block& key)
        : gf_(gf) {
        expand_key(key);
    }

    void encrypt_block(const Block& plaintext, Block& ciphertext) const noexcept {
        Block state = plaintext;
        add_round_key(state, 0);
        for (int round = 1; round < NUM_ROUNDS; ++round) {
            sub_bytes(state);
            shift_rows(state);
            mix_columns(state);
            add_round_key(state, round);
        }
        sub_bytes(state);
        shift_rows(state);
        add_round_key(state, NUM_ROUNDS);
        ciphertext = state;
    }

    void decrypt_block(const Block& ciphertext, Block& plaintext) const noexcept {
        Block state = ciphertext;
        add_round_key(state, NUM_ROUNDS);
        for (int round = NUM_ROUNDS - 1; round > 0; --round) {
            inv_shift_rows(state);
            inv_sub_bytes(state);
            add_round_key(state, round);
            inv_mix_columns(state);
        }
        inv_shift_rows(state);
        inv_sub_bytes(state);
        add_round_key(state, 0);
        plaintext = state;
    }

private:
    void expand_key(const Block& key) noexcept {
        constexpr std::array<uint8_t, 10> RCON =
            {0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36};
        for (int i = 0; i < 16; ++i) {
            round_keys_[i] = key[i];
        }
        for (int i = 4; i < 44; ++i) {
            uint8_t temp[4];
            for (int j = 0; j < 4; ++j) {
                temp[j] = round_keys_[4 * (i - 1) + j];
            }
            if (i % 4 == 0) {
                const uint8_t first = temp[0];
                temp[0] = temp[1];
                temp[1] = temp[2];
                temp[2] = temp[3];
                temp[3] = first;
                for (int j = 0; j < 4; ++j) {
                    temp[j] = gf_.sbox()[temp[j]];
                }
                temp[0] = static_cast<uint8_t>(temp[0] ^ RCON[i / 4 - 1]);
            }
            for (int j = 0; j < 4; ++j) {
                round_keys_[4 * i + j] =
                    static_cast<uint8_t>(round_keys_[4 * (i - 4) + j] ^ temp[j]);
            }
        }
    }

    void add_round_key(Block& state, int round) const noexcept {
        for (int i = 0; i < 16; ++i) {
            state[i] = static_cast<uint8_t>(state[i] ^ round_keys_[round * 16 + i]);
        }
    }

    void sub_bytes(Block& state) const noexcept {
        for (int i = 0; i < 16; ++i) {
            state[i] = gf_.sbox()[state[i]];
        }
    }

    void inv_sub_bytes(Block& state) const noexcept {
        for (int i = 0; i < 16; ++i) {
            state[i] = gf_.inv_sbox()[state[i]];
        }
    }

    void shift_rows(Block& state) const noexcept {
        Block tmp{};
        for (int r = 0; r < 4; ++r) {
            for (int c = 0; c < 4; ++c) {
                tmp[r + 4 * c] = state[r + 4 * ((c + r) % 4)];
            }
        }
        state = tmp;
    }

    void inv_shift_rows(Block& state) const noexcept {
        Block tmp{};
        for (int r = 0; r < 4; ++r) {
            for (int c = 0; c < 4; ++c) {
                tmp[r + 4 * ((c + r) % 4)] = state[r + 4 * c];
            }
        }
        state = tmp;
    }

    void mix_columns(Block& state) const noexcept {
        for (int c = 0; c < 4; ++c) {
            const uint8_t a0 = state[4 * c + 0];
            const uint8_t a1 = state[4 * c + 1];
            const uint8_t a2 = state[4 * c + 2];
            const uint8_t a3 = state[4 * c + 3];
            state[4 * c + 0] = static_cast<uint8_t>(
                gf_.multiply(a0, 0x02) ^ gf_.multiply(a1, 0x03) ^ a2 ^ a3);
            state[4 * c + 1] = static_cast<uint8_t>(
                a0 ^ gf_.multiply(a1, 0x02) ^ gf_.multiply(a2, 0x03) ^ a3);
            state[4 * c + 2] = static_cast<uint8_t>(
                a0 ^ a1 ^ gf_.multiply(a2, 0x02) ^ gf_.multiply(a3, 0x03));
            state[4 * c + 3] = static_cast<uint8_t>(
                gf_.multiply(a0, 0x03) ^ a1 ^ a2 ^ gf_.multiply(a3, 0x02));
        }
    }

    void inv_mix_columns(Block& state) const noexcept {
        for (int c = 0; c < 4; ++c) {
            const uint8_t a0 = state[4 * c + 0];
            const uint8_t a1 = state[4 * c + 1];
            const uint8_t a2 = state[4 * c + 2];
            const uint8_t a3 = state[4 * c + 3];
            state[4 * c + 0] = static_cast<uint8_t>(
                gf_.multiply(a0, 0x0E) ^ gf_.multiply(a1, 0x0B) ^
                gf_.multiply(a2, 0x0D) ^ gf_.multiply(a3, 0x09));
            state[4 * c + 1] = static_cast<uint8_t>(
                gf_.multiply(a0, 0x09) ^ gf_.multiply(a1, 0x0E) ^
                gf_.multiply(a2, 0x0B) ^ gf_.multiply(a3, 0x0D));
            state[4 * c + 2] = static_cast<uint8_t>(
                gf_.multiply(a0, 0x0D) ^ gf_.multiply(a1, 0x09) ^
                gf_.multiply(a2, 0x0E) ^ gf_.multiply(a3, 0x0B));
            state[4 * c + 3] = static_cast<uint8_t>(
                gf_.multiply(a0, 0x0B) ^ gf_.multiply(a1, 0x0D) ^
                gf_.multiply(a2, 0x09) ^ gf_.multiply(a3, 0x0E));
        }
    }

    const GaloisField& gf_;
    std::array<uint8_t, 16 * (NUM_ROUNDS + 1)> round_keys_{};
};

class Gcm {
public:
    static constexpr int TAG_SIZE = 16;
    static constexpr int MAX_DATA_SIZE = 4096;
    using Tag = std::array<uint8_t, TAG_SIZE>;
    using Block = Aes128::Block;

    struct Buffer {
        std::array<uint8_t, MAX_DATA_SIZE> data{};
        size_t size = 0;
    };

    explicit Gcm(const Aes128& cipher)
        : cipher_(cipher) {
        Block zero{};
        cipher_.encrypt_block(zero, hash_key_);
    }

    void seal(const Buffer& iv,
              const Buffer& plaintext,
              const Buffer& aad,
              Buffer& ciphertext,
              Tag& tag) const {
        Block j0;
        compute_j0(iv, j0);

        ciphertext.size = plaintext.size;
        Block counter = j0;
        for (size_t i = 0; i < plaintext.size; i += 16) {
            inc32(counter);
            Block keystream;
            cipher_.encrypt_block(counter, keystream);
            const size_t n = std::min<size_t>(16, plaintext.size - i);
            for (size_t j = 0; j < n; ++j) {
                ciphertext.data[i + j] =
                    static_cast<uint8_t>(plaintext.data[i + j] ^ keystream[j]);
            }
        }

        Block auth;
        ghash(aad, ciphertext, auth);
        Block ek_j0;
        cipher_.encrypt_block(j0, ek_j0);
        for (int i = 0; i < TAG_SIZE; ++i) {
            tag[i] = static_cast<uint8_t>(auth[i] ^ ek_j0[i]);
        }
    }

    bool open(const Buffer& iv,
              const Buffer& ciphertext,
              const Buffer& aad,
              const Tag& tag,
              Buffer& plaintext) const {
        Block j0;
        compute_j0(iv, j0);

        Block auth;
        ghash(aad, ciphertext, auth);
        Block ek_j0;
        cipher_.encrypt_block(j0, ek_j0);
        Tag expected{};
        for (int i = 0; i < TAG_SIZE; ++i) {
            expected[i] = static_cast<uint8_t>(auth[i] ^ ek_j0[i]);
        }

        if (!constant_time_equal(expected, tag)) {
            return false;
        }

        plaintext.size = ciphertext.size;
        Block counter = j0;
        for (size_t i = 0; i < ciphertext.size; i += 16) {
            inc32(counter);
            Block keystream;
            cipher_.encrypt_block(counter, keystream);
            const size_t n = std::min<size_t>(16, ciphertext.size - i);
            for (size_t j = 0; j < n; ++j) {
                plaintext.data[i + j] =
                    static_cast<uint8_t>(ciphertext.data[i + j] ^ keystream[j]);
            }
        }
        return true;
    }

private:
    static constexpr uint8_t REDUCTION_BYTE = 0xE1;

    static void inc32(Aes128::Block& counter) noexcept {
        uint32_t value = (static_cast<uint32_t>(counter[12]) << 24)
                       | (static_cast<uint32_t>(counter[13]) << 16)
                       | (static_cast<uint32_t>(counter[14]) << 8)
                       | static_cast<uint32_t>(counter[15]);
        value += 1;
        counter[12] = static_cast<uint8_t>(value >> 24);
        counter[13] = static_cast<uint8_t>(value >> 16);
        counter[14] = static_cast<uint8_t>(value >> 8);
        counter[15] = static_cast<uint8_t>(value);
    }

    static bool constant_time_equal(const Tag& a, const Tag& b) noexcept {
        uint8_t diff = 0;
        for (int i = 0; i < TAG_SIZE; ++i) {
            diff = static_cast<uint8_t>(diff | (a[i] ^ b[i]));
        }
        return diff == 0;
    }

    static void encode_be64(uint8_t* out, uint64_t value) noexcept {
        for (int i = 0; i < 8; ++i) {
            out[i] = static_cast<uint8_t>(value >> (8 * (7 - i)));
        }
    }

    void gf128_mul(const Block& x, const Block& y, Block& out) const {
        Block z{};
        Block v = y;
        for (int i = 0; i < 128; ++i) {
            const uint8_t bit =
                static_cast<uint8_t>((x[i / 8] >> (7 - (i % 8))) & 1);
            const uint8_t mask = static_cast<uint8_t>(-bit);
            for (int j = 0; j < 16; ++j) {
                z[j] = static_cast<uint8_t>(z[j] ^ (v[j] & mask));
            }
            const uint8_t lsb = static_cast<uint8_t>(v[15] & 1);
            const uint8_t red = static_cast<uint8_t>(-lsb);
            for (int j = 15; j > 0; --j) {
                v[j] = static_cast<uint8_t>((v[j] >> 1) | (v[j - 1] << 7));
            }
            v[0] = static_cast<uint8_t>((v[0] >> 1) ^ (REDUCTION_BYTE & red));
        }
        out = z;
    }

    void process_block(Block& y, const Block& block) const {
        Block x{};
        for (int i = 0; i < 16; ++i) {
            x[i] = static_cast<uint8_t>(y[i] ^ block[i]);
        }
        gf128_mul(x, hash_key_, y);
    }

    void ghash(const Buffer& aad, const Buffer& ciphertext, Block& out) const {
        Block y{};
        for (size_t i = 0; i < aad.size; i += 16) {
            Block block{};
            const size_t n = std::min<size_t>(16, aad.size - i);
            for (size_t j = 0; j < n; ++j) {
                block[j] = aad.data[i + j];
            }
            process_block(y, block);
        }
        for (size_t i = 0; i < ciphertext.size; i += 16) {
            Block block{};
            const size_t n = std::min<size_t>(16, ciphertext.size - i);
            for (size_t j = 0; j < n; ++j) {
                block[j] = ciphertext.data[i + j];
            }
            process_block(y, block);
        }
        Block length_block{};
        encode_be64(length_block.data(), static_cast<uint64_t>(aad.size) * 8);
        encode_be64(length_block.data() + 8,
                    static_cast<uint64_t>(ciphertext.size) * 8);
        process_block(y, length_block);
        out = y;
    }

    void compute_j0(const Buffer& iv, Block& j0) const {
        if (iv.size == 12) {
            j0.fill(0);
            for (int i = 0; i < 12; ++i) {
                j0[i] = iv.data[i];
            }
            j0[15] = 1;
            return;
        }
        Block y{};
        for (size_t i = 0; i < iv.size; i += 16) {
            Block block{};
            const size_t n = std::min<size_t>(16, iv.size - i);
            for (size_t j = 0; j < n; ++j) {
                block[j] = iv.data[i + j];
            }
            process_block(y, block);
        }
        Block length_block{};
        encode_be64(length_block.data() + 8, static_cast<uint64_t>(iv.size) * 8);
        process_block(y, length_block);
        j0 = y;
    }

    const Aes128& cipher_;
    Block hash_key_{};
};

namespace {

void print_hex(const char* label, const uint8_t* data, size_t len) {
    std::printf("%s: ", label);
    for (size_t i = 0; i < len; ++i) {
        std::printf("%02X", data[i]);
    }
    std::printf("\n");
}

bool test_gf_inverse(const GaloisField& gf) {
    for (int a = 1; a < 256; ++a) {
        const uint8_t inv = gf.inverse(static_cast<uint8_t>(a));
        if (gf.multiply(static_cast<uint8_t>(a), inv) != 0x01) {
            return false;
        }
    }
    return gf.inverse(0x00) == 0x00;
}

bool test_sbox_bijection(const GaloisField& gf) {
    bool seen[256] = {};
    for (int i = 0; i < 256; ++i) {
        const uint8_t s = gf.sbox()[i];
        if (seen[s]) {
            return false;
        }
        seen[s] = true;
    }
    return true;
}

bool test_aes_roundtrip(const Aes128& cipher) {
    Aes128::Block plain = {0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,
                           0x88,0x99,0xAA,0xBB,0xCC,0xDD,0xEE,0xFF};
    Aes128::Block ct{};
    Aes128::Block pt{};
    cipher.encrypt_block(plain, ct);
    cipher.decrypt_block(ct, pt);
    return plain == pt;
}

bool test_gcm_roundtrip(const Gcm& gcm) {
    Gcm::Buffer iv{};
    iv.size = 12;
    iv.data[11] = 1;
    Gcm::Buffer pt{};
    pt.size = 20;
    for (size_t i = 0; i < pt.size; ++i) {
        pt.data[i] = static_cast<uint8_t>(i + 1);
    }
    Gcm::Buffer aad{};
    aad.size = 6;
    const uint8_t aad_bytes[6] = {'h','e','a','d','e','r'};
    for (size_t i = 0; i < 6; ++i) {
        aad.data[i] = aad_bytes[i];
    }
    Gcm::Buffer ct;
    Gcm::Buffer rt;
    Gcm::Tag tag{};
    gcm.seal(iv, pt, aad, ct, tag);
    if (!gcm.open(iv, ct, aad, tag, rt)) {
        return false;
    }
    if (rt.size != pt.size) {
        return false;
    }
    for (size_t i = 0; i < pt.size; ++i) {
        if (rt.data[i] != pt.data[i]) {
            return false;
        }
    }
    return true;
}

bool test_gcm_tag_tampering(const Gcm& gcm) {
    Gcm::Buffer iv{};
    iv.size = 12;
    Gcm::Buffer pt{};
    pt.size = 16;
    for (size_t i = 0; i < pt.size; ++i) {
        pt.data[i] = 0xAB;
    }
    Gcm::Buffer aad{};
    aad.size = 8;
    for (size_t i = 0; i < aad.size; ++i) {
        aad.data[i] = 0xCD;
    }
    Gcm::Buffer ct;
    Gcm::Buffer rt;
    Gcm::Tag tag{};
    gcm.seal(iv, pt, aad, ct, tag);
    tag[0] ^= 0x01;
    return !gcm.open(iv, ct, aad, tag, rt);
}

bool test_empty_inputs(const Gcm& gcm) {
    Gcm::Buffer iv{};
    iv.size = 12;
    Gcm::Buffer pt{};
    Gcm::Buffer aad{};
    Gcm::Buffer ct;
    Gcm::Buffer rt;
    Gcm::Tag tag{};
    gcm.seal(iv, pt, aad, ct, tag);
    if (ct.size != 0) {
        return false;
    }
    return gcm.open(iv, ct, aad, tag, rt) && rt.size == 0;
}

}

int main() {
    const GaloisField gf(0x12B);
    const Aes128 cipher(gf, {0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
                             0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F});
    const Gcm gcm(cipher);

    print_hex("S-box[0x00] (variant 0x12B)", &gf.sbox()[0x00], 1);
    print_hex("S-box[0x01] (variant 0x12B)", &gf.sbox()[0x01], 1);
    print_hex("S-box[0x02] (variant 0x12B)", &gf.sbox()[0x02], 1);
    print_hex("S-box[0x53] (variant 0x12B)", &gf.sbox()[0x53], 1);

    std::printf("GF inverse test:            %s\n", test_gf_inverse(gf) ? "OK" : "FAIL");
    std::printf("S-box bijection test:       %s\n", test_sbox_bijection(gf) ? "OK" : "FAIL");
    std::printf("AES-128 roundtrip test:     %s\n", test_aes_roundtrip(cipher) ? "OK" : "FAIL");
    std::printf("GCM roundtrip test:         %s\n", test_gcm_roundtrip(gcm) ? "OK" : "FAIL");
    std::printf("GCM tag tampering test:     %s\n", test_gcm_tag_tampering(gcm) ? "OK" : "FAIL");
    std::printf("GCM empty-input test:       %s\n", test_empty_inputs(gcm) ? "OK" : "FAIL");

    Gcm::Buffer demo_iv{};
    demo_iv.size = 12;
    const uint8_t iv_bytes[12] = {0xCA,0xFE,0xBA,0xBE,0xFA,0xCE,0xDB,0xAD,
                                  0xDE,0xAD,0xBE,0xEF};
    for (int i = 0; i < 12; ++i) {
        demo_iv.data[i] = iv_bytes[i];
    }

    Gcm::Buffer demo_pt{};
    demo_pt.size = 12;
    const uint8_t pt_bytes[12] = {'G','a','l','o','i','s',' ','+',' ','G','C','M'};
    for (int i = 0; i < 12; ++i) {
        demo_pt.data[i] = pt_bytes[i];
    }

    Gcm::Buffer demo_aad{};
    demo_aad.size = 3;
    const uint8_t aad_bytes[3] = {'h','d','r'};
    for (int i = 0; i < 3; ++i) {
        demo_aad.data[i] = aad_bytes[i];
    }

    Gcm::Buffer demo_ct;
    Gcm::Tag demo_tag{};
    gcm.seal(demo_iv, demo_pt, demo_aad, demo_ct, demo_tag);
    print_hex("Demo ciphertext", demo_ct.data.data(), demo_ct.size);
    print_hex("Demo tag      ", demo_tag.data(), demo_tag.size());

    return 0;
}