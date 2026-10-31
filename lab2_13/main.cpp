#include <iostream>
#include <string>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <stdexcept>
#include <cstring>
#include <clocale>
#include <cstdlib>

namespace RSA13 {

static const size_t MAX_WORDS = 256;

class BigNum {
public:
    uint32_t words[MAX_WORDS];
    size_t len;

    BigNum() : len(1) { words[0] = 0; }
    BigNum(uint64_t v) {
        if (v == 0) { len = 1; words[0] = 0; }
        else { len = 0; words[len++] = (uint32_t)(v & 0xFFFFFFFF); if (v >> 32) words[len++] = (uint32_t)(v >> 32); }
        norm();
    }
    BigNum(const std::string& s) {
        std::string h = s;
        if (h.rfind("0x", 0) == 0 || h.rfind("0X", 0) == 0) h = h.substr(2);
        while (h.length() % 8) h = "0" + h;
        len = 0;
        for (int i = (int)h.length() - 8; i >= 0; i -= 8)
            words[len++] = (uint32_t)std::stoul(h.substr(i, 8), nullptr, 16);
        norm();
    }
    void norm() { while (len > 1 && words[len - 1] == 0) --len; }

    int cmp(const BigNum& o) const {
        if (len != o.len) return len < o.len ? -1 : 1;
        for (int i = (int)len - 1; i >= 0; --i) if (words[i] != o.words[i]) return words[i] < o.words[i] ? -1 : 1;
        return 0;
    }
    bool operator< (const BigNum& o) const { return cmp(o) < 0; }
    bool operator> (const BigNum& o) const { return cmp(o) > 0; }
    bool operator<=(const BigNum& o) const { return cmp(o) <= 0; }
    bool operator>=(const BigNum& o) const { return cmp(o) >= 0; }
    bool operator==(const BigNum& o) const { return cmp(o) == 0; }
    bool operator!=(const BigNum& o) const { return cmp(o) != 0; }

    void shr1() {
        uint32_t c = 0;
        for (int i = (int)len - 1; i >= 0; --i) {
            uint64_t t = ((uint64_t)c << 32) | words[i];
            words[i] = (uint32_t)(t >> 1);
            c = (uint32_t)(t & 1);
        }
        norm();
    }
    void subInPlace(const BigNum& o) {
        int64_t b = 0;
        for (size_t i = 0; i < len; ++i) {
            int64_t d = (int64_t)words[i] - b - (i < o.len ? o.words[i] : 0);
            if (d < 0) { d += 0x100000000LL; b = 1; } else b = 0;
            words[i] = (uint32_t)(d & 0xFFFFFFFF);
        }
        norm();
    }
    bool bit(size_t i) const {
        size_t w = i / 32, b = i % 32;
        if (w >= len) return false;
        return (words[w] >> b) & 1;
    }
    BigNum operator+(const BigNum& o) const {
        BigNum r; r.len = 0; uint64_t c = 0;
        size_t n = std::max(len, o.len);
        for (size_t i = 0; i < n || c; ++i) {
            uint64_t s = c + (i < len ? words[i] : 0) + (i < o.len ? o.words[i] : 0);
            r.words[r.len++] = (uint32_t)(s & 0xFFFFFFFF);
            c = s >> 32;
        }
        r.norm(); return r;
    }
    BigNum operator-(const BigNum& o) const {
        if (*this < o) return BigNum(0);
        BigNum r = *this; r.subInPlace(o); return r;
    }
    BigNum operator*(const BigNum& o) const {
        if (len + o.len + 1 > MAX_WORDS) throw std::runtime_error("mul: overflow");
        BigNum r; r.len = len + o.len;
        for (size_t i = 0; i < r.len; ++i) r.words[i] = 0;
        for (size_t i = 0; i < len; ++i) {
        uint64_t c = 0;
        for (size_t j = 0; j < o.len; ++j) {
            uint64_t t = (uint64_t)r.words[i + j] + c + (uint64_t)words[i] * o.words[j];
            r.words[i + j] = (uint32_t)(t & 0xFFFFFFFF);
            c = t >> 32;
            }
        size_t k = i + o.len;
        while (c) {
            if (k >= MAX_WORDS) throw std::runtime_error("mul: carry overflow");
            uint64_t t = (uint64_t)r.words[k] + c;
            r.words[k] = (uint32_t)(t & 0xFFFFFFFF);
            c = t >> 32;
            ++k;
            }
        }
        r.norm();
        return r;
    }
    BigNum operator<<(size_t s) const {
        if (s == 0 || (len == 1 && words[0] == 0)) return *this;
        BigNum r; size_t ws = s / 32, bs = s % 32; r.len = 0;
        if (ws + len + 1 > MAX_WORDS) throw std::runtime_error("shl: overflow");
        for (size_t i = 0; i < ws; ++i) r.words[r.len++] = 0;
        uint64_t c = 0;
        for (size_t i = 0; i < len; ++i) {
            uint64_t t = ((uint64_t)words[i] << bs) | c;
            r.words[r.len++] = (uint32_t)(t & 0xFFFFFFFF);
            c = t >> 32;
        }
        if (c) r.words[r.len++] = (uint32_t)c;
        r.norm();
        return r;
    }
    BigNum operator>>(size_t s) const {
        size_t ws = s / 32, bs = s % 32;
        if (ws >= len) return BigNum(0);
        BigNum r; r.len = 0; uint64_t c = 0;
        for (int i = (int)len - 1; i >= (int)ws; --i) {
            uint64_t t = (c << 32) | words[i];
            r.words[r.len++] = (uint32_t)(t >> bs);
            c = t & ((1ULL << bs) - 1);
        }
        std::reverse(r.words, r.words + r.len);
        r.norm(); return r;
    }
    size_t bits() const {
        if (len == 1 && words[0] == 0) return 0;
        size_t b = (len - 1) * 32;
        uint32_t t = words[len - 1];
        while (t) { b++; t >>= 1; }
        return b;
    }
    static void divmod(const BigNum& a, const BigNum& b, BigNum& q, BigNum& r) {
        if (b == BigNum(0)) throw std::runtime_error("div by 0");
        if (a < b) { q = 0; r = a; return; }
        r = a;
        size_t sh = a.bits() - b.bits();
        BigNum sb = b << sh;
        q.len = (sh / 32) + 1;
        for (size_t i = 0; i < q.len; ++i) q.words[i] = 0;
        for (int i = (int)sh; i >= 0; --i) {
            if (r >= sb) { r.subInPlace(sb); q.words[i / 32] |= (1U << (i % 32)); }
            sb.shr1();
        }
        q.norm(); r.norm();
    }
    BigNum operator/(const BigNum& o) const { BigNum q, r; divmod(*this, o, q, r); return q; }
    BigNum operator%(const BigNum& o) const { BigNum q, r; divmod(*this, o, q, r); return r; }

    static void cmov(BigNum& d, const BigNum& s, uint32_t m) {
    size_t n = std::max(d.len, s.len);
        if (n > MAX_WORDS) throw std::runtime_error("cmov: overflow");
        for (size_t i = d.len; i < n; ++i) d.words[i] = 0;
        d.len = n;
        for (size_t i = 0; i < n; ++i) {
            uint32_t x = (i < s.len) ? s.words[i] : 0;
            d.words[i] = (d.words[i] & ~m) | (x & m);
        }
        d.norm();
    }
    static uint32_t zeroMask(const BigNum& a) {
        uint32_t x = 0;
        for (size_t i = 0; i < a.len; ++i) x |= a.words[i];
        return x == 0 ? 0xFFFFFFFFu : 0u;
    }
    static uint32_t evenMask(const BigNum& a) {
        return ((a.words[0] & 1) == 0) ? 0xFFFFFFFFu : 0u;
    }
};

namespace CM {
    BigNum powMod(const BigNum& bIn, const BigNum& e, const BigNum& m) {
        if (m == BigNum(1)) return BigNum(0);
        BigNum r = 1, b = bIn % m;
        size_t n = e.bits();
        for (size_t i = 0; i < n; ++i) {
            if (e.bit(i)) r = (r * b) % m;
            if (i + 1 < n) b = (b * b) % m;
        }
        return r;
    }
    BigNum invMod(BigNum a, BigNum m) {
        BigNum m0 = m, x0 = 0, x1 = 1;
        if (m == BigNum(1)) return 0;
        while (a > BigNum(1)) {
            if (m == BigNum(0)) break;
            BigNum q, r;
            BigNum::divmod(a, m, q, r);
            a = m; m = r;
            BigNum qx0 = (q * x0) % m0;
            BigNum nx = (x1 >= qx0) ? (x1 - qx0) : (m0 - ((qx0 - x1) % m0));
            x1 = x0; x0 = nx;
        }
        return x1 % m0;
    }
    BigNum ctBinaryInv(BigNum a, const BigNum& mod) {
        if (mod == BigNum(1)) return BigNum(0);
        BigNum u = a % mod, v = mod, x1 = 1, x2 = 0;
        size_t N = 2 * mod.bits() + 2;
        for (size_t i = 0; i < N; ++i) {
            uint32_t ue = BigNum::evenMask(u);
            {
                BigNum us = u; us.shr1();
                BigNum xp = x1 + mod;
                uint32_t xo = (x1.words[0] & 1) ? 0xFFFFFFFFu : 0u;
                BigNum::cmov(x1, xp, ue & xo);
                BigNum xs = x1; xs.shr1();
                BigNum::cmov(u, us, ue);
                BigNum::cmov(x1, xs, ue);
            }
            uint32_t ve = BigNum::evenMask(v);
            {
                BigNum vs = v; vs.shr1();
                BigNum xp = x2 + mod;
                uint32_t xo = (x2.words[0] & 1) ? 0xFFFFFFFFu : 0u;
                BigNum::cmov(x2, xp, ve & xo);
                BigNum xs = x2; xs.shr1();
                BigNum::cmov(v, vs, ve);
                BigNum::cmov(x2, xs, ve);
            }
            int c = u.cmp(v);
            uint32_t ge = (c >= 0) ? 0xFFFFFFFFu : 0u;
            BigNum um = (u >= v) ? (u - v) : BigNum(0);
            BigNum vm = (v >= u) ? (v - u) : BigNum(0);
            BigNum x12 = (x1 >= x2) ? (x1 - x2) : (mod - ((x2 - x1) % mod));
            BigNum x21 = (x2 >= x1) ? (x2 - x1) : (mod - ((x1 - x2) % mod));
            BigNum::cmov(u, um, ge);
            BigNum::cmov(x1, x12, ge);
            BigNum::cmov(v, vm, ~ge);
            BigNum::cmov(x2, x21, ~ge);
            if (BigNum::zeroMask(u)) break;
        }
        return x2 % mod;
    }
}

namespace SHA256 {
    static const uint32_t K[64] = {
        0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
        0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
        0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
        0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
        0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
        0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
        0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
        0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
    };
    static inline uint32_t rr(uint32_t x, int n) { return (x >> n) | (x << (32 - n)); }
    struct Hash32 { uint8_t b[32]; };

    Hash32 hash(const uint8_t* m, size_t mlen) {
        uint32_t h[8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
                         0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
        size_t total = mlen + 1;
        while (total % 64 != 56) total++;
        total += 8;
        uint8_t d[1024 + 128];
        for (size_t i = 0; i < mlen; ++i) d[i] = m[i];
        d[mlen] = 0x80;
        for (size_t i = mlen + 1; i < total - 8; ++i) d[i] = 0;
        uint64_t bl = (uint64_t)mlen * 8;
        for (int i = 7; i >= 0; --i) d[total - 1 - i] = (uint8_t)((bl >> (i * 8)) & 0xFF);

        for (size_t off = 0; off < total; off += 64) {
            uint32_t w[64];
            for (int i = 0; i < 16; ++i)
                w[i] = ((uint32_t)d[off+i*4] << 24) | ((uint32_t)d[off+i*4+1] << 16)
                     | ((uint32_t)d[off+i*4+2] << 8) | d[off+i*4+3];
            for (int i = 16; i < 64; ++i) {
                uint32_t s0 = rr(w[i-15],7) ^ rr(w[i-15],18) ^ (w[i-15] >> 3);
                uint32_t s1 = rr(w[i-2],17) ^ rr(w[i-2],19) ^ (w[i-2] >> 10);
                w[i] = w[i-16] + s0 + w[i-7] + s1;
            }
            uint32_t a=h[0],b=h[1],c=h[2],dd=h[3],e=h[4],f=h[5],g=h[6],hh=h[7];
            for (int i = 0; i < 64; ++i) {
                uint32_t S1 = rr(e,6) ^ rr(e,11) ^ rr(e,25);
                uint32_t ch = (e & f) ^ (~e & g);
                uint32_t t1 = hh + S1 + ch + K[i] + w[i];
                uint32_t S0 = rr(a,2) ^ rr(a,13) ^ rr(a,22);
                uint32_t mj = (a & b) ^ (a & c) ^ (b & c);
                uint32_t t2 = S0 + mj;
                hh=g; g=f; f=e; e=dd+t1; dd=c; c=b; b=a; a=t1+t2;
            }
            h[0]+=a; h[1]+=b; h[2]+=c; h[3]+=dd; h[4]+=e; h[5]+=f; h[6]+=g; h[7]+=hh;
        }
        Hash32 out;
        for (int i = 0; i < 8; ++i) {
            out.b[i*4]   = (uint8_t)((h[i] >> 24) & 0xFF);
            out.b[i*4+1] = (uint8_t)((h[i] >> 16) & 0xFF);
            out.b[i*4+2] = (uint8_t)((h[i] >> 8) & 0xFF);
            out.b[i*4+3] = (uint8_t)(h[i] & 0xFF);
        }
        return out;
    }
}

namespace MGF1 {
    static const size_t MAX_OUT = 512;
    void mask(const uint8_t* seed, size_t seed_len, uint8_t* out, size_t out_len) {
        if (out_len > MAX_OUT) throw std::runtime_error("MGF1 overflow");
        uint8_t buf[MAX_OUT + 32];
        size_t blocks = (out_len + 31) / 32;
        for (size_t b = 0; b < blocks; ++b) {
            uint8_t in[512 + 4];
            std::memcpy(in, seed, seed_len);
            uint32_t ctr = (uint32_t)b;
            in[seed_len]     = (uint8_t)((ctr >> 24) & 0xFF);
            in[seed_len + 1] = (uint8_t)((ctr >> 16) & 0xFF);
            in[seed_len + 2] = (uint8_t)((ctr >> 8) & 0xFF);
            in[seed_len + 3] = (uint8_t)(ctr & 0xFF);
            auto h = SHA256::hash(in, seed_len + 4);
            std::memcpy(buf + b * 32, h.b, 32);
        }
        std::memcpy(out, buf, out_len);
    }
    void mask_xor(uint8_t* data, size_t data_len, const uint8_t* seed, size_t seed_len) {
        uint8_t tmp[MAX_OUT];
        mask(seed, seed_len, tmp, data_len);
        for (size_t i = 0; i < data_len; ++i) data[i] ^= tmp[i];
    }
}

namespace OAEP {
    constexpr size_t MOD_BYTES = 256;   // 2048 бит
    constexpr size_t H_LEN     = 32;    // SHA-256
    constexpr size_t DB_LEN    = MOD_BYTES - H_LEN - 1; // 223
    constexpr size_t MAX_MSG   = MOD_BYTES - 2 * H_LEN - 2; // 190

    struct Buf { uint8_t b[MOD_BYTES]; size_t n; };

    Buf pad(const uint8_t* in, size_t inlen) {
        if (inlen > MAX_MSG) throw std::runtime_error("payload too large");
        auto lh = SHA256::hash(nullptr, 0);

        uint8_t db[DB_LEN];
        std::memcpy(db, lh.b, H_LEN);
        size_t ps_len = DB_LEN - H_LEN - 1 - inlen;
        for (size_t i = 0; i < ps_len; ++i) db[H_LEN + i] = 0;
        db[H_LEN + ps_len] = 0x01;
        std::memcpy(db + H_LEN + ps_len + 1, in, inlen);

        uint8_t seed[H_LEN];
        for (size_t i = 0; i < H_LEN; ++i) seed[i] = (uint8_t)(std::rand() & 0xFF);

        MGF1::mask_xor(db, DB_LEN, seed, H_LEN);
        MGF1::mask_xor(seed, H_LEN, db, DB_LEN);

        Buf out;
        out.n = MOD_BYTES;
        out.b[0] = 0x00;
        std::memcpy(out.b + 1, seed, H_LEN);
        std::memcpy(out.b + 1 + H_LEN, db, DB_LEN);
        return out;
    }

    Buf unpad(const uint8_t* em, size_t emlen) {
        if (emlen != MOD_BYTES) throw std::runtime_error("OAEP: bad length");
        uint8_t seed[H_LEN], db[DB_LEN];
        std::memcpy(seed, em + 1, H_LEN);
        std::memcpy(db, em + 1 + H_LEN, DB_LEN);

        MGF1::mask_xor(seed, H_LEN, db, DB_LEN);
        MGF1::mask_xor(db, DB_LEN, seed, H_LEN);

        auto lh = SHA256::hash(nullptr, 0);

        uint32_t bad = 0;
        bad |= (uint32_t)em[0];
        for (size_t i = 0; i < H_LEN; ++i) bad |= (uint32_t)(db[i] ^ lh.b[i]);

        size_t one_pos = DB_LEN;
        uint32_t found = 0;
        for (size_t i = H_LEN; i < DB_LEN; ++i) {
            uint32_t is_one  = (db[i] == 0x01) ? 1u : 0u;
            uint32_t is_zero = (db[i] == 0x00) ? 1u : 0u;
            uint32_t first   = (found ^ 1u) & is_one;
            one_pos = first ? i : one_pos;
            found  |= first;
            bad |= (found ^ 1u) & (1u - is_zero);
        }
        bad |= (found ^ 1u);

        if (bad != 0) throw std::runtime_error("OAEP: invalid padding");

        Buf out;
        out.n = DB_LEN - one_pos - 1;
        std::memcpy(out.b, db + one_pos + 1, out.n);
        return out;
    }
}

namespace U {
    BigNum pack(const uint8_t* b, size_t n) {
        BigNum r; r.len = 0;
        if (n == 0) { r.words[r.len++] = 0; return r; }
        size_t p = (4 - (n % 4)) % 4;
        uint8_t buf[520];
        for (size_t i = 0; i < p; ++i) buf[i] = 0;
        for (size_t i = 0; i < n; ++i) buf[p + i] = b[i];
        size_t total = p + n;
        for (size_t i = 0; i < total; i += 4) {
            uint32_t w = ((uint32_t)buf[i] << 24) | ((uint32_t)buf[i+1] << 16) | ((uint32_t)buf[i+2] << 8) | buf[i+3];
            r.words[r.len++] = w;
        }
        std::reverse(r.words, r.words + r.len);
        r.norm();
        return r;
    }
    void unpack(const BigNum& v, uint8_t* out, size_t t) {
        uint8_t o[520]; size_t olen = 0;
        for (int i = (int)v.len - 1; i >= 0; --i) {
            uint32_t w = v.words[i];
            o[olen++] = (uint8_t)((w >> 24) & 0xFF);
            o[olen++] = (uint8_t)((w >> 16) & 0xFF);
            o[olen++] = (uint8_t)((w >> 8) & 0xFF);
            o[olen++] = (uint8_t)(w & 0xFF);
        }
        size_t s = 0;
        while (s + 1 < olen && o[s] == 0) s++;
        size_t cnt = olen - s;
        if (cnt < t) {
            size_t pad = t - cnt;
            for (size_t i = 0; i < pad; ++i) out[i] = 0;
            for (size_t i = 0; i < cnt; ++i) out[pad + i] = o[s + i];
        } else {
            for (size_t i = 0; i < t; ++i) out[i] = o[s + (cnt - t) + i];
        }
    }
}

struct Pub { BigNum N, e; };
struct Priv { BigNum p, q, d, dP, dQ, qInv; };

// p: 1024-битное простое (Oakley Group 2, RFC 2409)
static const char* P_HEX =
    "FFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD1"
    "29024E088A67CC74020BBEA63B139B22514A08798E3404DD"
    "EF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245"
    "E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7ED"
    "EE386BFB5A899FA5AE9F24117C4B1FE649286651ECE65381"
    "FFFFFFFFFFFFFFFF";

// q: 1024-битное простое (Oakley Group 1, RFC 2409 — другой набор, p ≠ q)
static const char* Q_HEX =
    "B10B8F96A080E01DDE92DE5EAE5D54EC52C99FBCFB06A3C6"
    "9A6A9DCA52D23B616073E28675A23D189838EF1E2EE652C0"
    "13ECB4AEA906112324975C3D49B83BFACCBDD7D90C4BD70"
    "98488E9C219A73724EFFD6FAE5644738FAA31A4FF55BCCC0"
    "A151AF5F0DC8B4BD45BF37DF365C1A65E68CFDA76D4DA708"
    "DF1FB2BC2E4A4371";

void setup(Pub& pub, Priv& priv) {
    BigNum p(P_HEX), q(Q_HEX);
    if (p == q) throw std::runtime_error("p == q");
    pub.N = p * q;
    pub.e = 65537;
    BigNum phi = (p - 1) * (q - 1);
    BigNum d = CM::invMod(pub.e, phi);
    priv.p = p;
    priv.q = q;
    priv.d = d;
    priv.dP = d % (p - 1);
    priv.dQ = d % (q - 1);
    priv.qInv = CM::ctBinaryInv(q, p);
    if ((q * priv.qInv) % p != BigNum(1)) throw std::runtime_error("qInv self-test failed");
}

BigNum encrypt(const BigNum& m, const Pub& k) { return CM::powMod(m, k.e, k.N); }

BigNum decrypt(const BigNum& c, const Priv& k) {
    BigNum m1 = CM::powMod(c, k.dP, k.p), m2 = CM::powMod(c, k.dQ, k.q);
    BigNum diff = (m1 >= m2) ? (m1 - m2) : (k.p - (m2 - m1));
    BigNum h = (diff * k.qInv) % k.p;
    return m2 + h * k.q;
}

void test(const uint8_t* payload, size_t plen, const Pub& pub, const Priv& priv) {
    std::cout << "Input: " << plen << " bytes. ";
    auto t0 = std::chrono::high_resolution_clock::now();
    try {
        auto padded = OAEP::pad(payload, plen);
        BigNum m = U::pack(padded.b, padded.n);
        BigNum c = encrypt(m, pub);
        BigNum dec = decrypt(c, priv);
        uint8_t dp[OAEP::MOD_BYTES];
        U::unpack(dec, dp, OAEP::MOD_BYTES);
        auto out = OAEP::unpad(dp, OAEP::MOD_BYTES);
        if (out.n != plen) throw std::runtime_error("length mismatch");
        for (size_t i = 0; i < plen; ++i)
            if (out.b[i] != payload[i]) throw std::runtime_error("byte mismatch");
        std::cout << "OK (" << out.n << " bytes)\n";
    } catch (const std::exception& e) {
        std::cout << "Error: " << e.what() << "\n";
    }
    auto t1 = std::chrono::high_resolution_clock::now();
    auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count();
    std::cout << "    Time: " << ms << " ms\n";
}

}

int main() {
    std::srand(0xC0FFEE);
    RSA13::Pub pub;
    RSA13::Priv priv;
    try { RSA13::setup(pub, priv); }
    catch (const std::exception& e) { std::cerr << "setup error: " << e.what() << "\n"; return 1; }

    RSA13::test(nullptr, 0, pub, priv);

    uint8_t big[190];
    for (size_t i = 0; i < 190; ++i) big[i] = 0xAB;
    RSA13::test(big, 190, pub, priv);

    const char* s = "RSA-2048 OAEP SHA-256 Variant 13";
    RSA13::test((const uint8_t*)s, std::strlen(s), pub, priv);

    return 0;
}