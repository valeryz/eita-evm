/*
 * blake2f.c — EIP-152 BLAKE2b F compression function precompile (0x09).
 *
 * Input layout (exactly 213 bytes):
 *   bytes  0.. 4 : rounds (u32 big-endian)
 *   bytes  4.. 68: h      (8x u64 little-endian)
 *   bytes 68..196: m      (16x u64 little-endian)
 *   bytes 196..212: t     (2x u64 little-endian)
 *   byte 212      : f     (0 or 1)
 *
 * Output (64 bytes): updated h, 8x u64 little-endian.
 *
 * Returns 1 on success, 0 on invalid input (wrong length / bad f flag).
 * Gas (rounds * 1) is charged by the caller.
 */

#include <stdint.h>
#include <string.h>
#include <stddef.h>
#ifndef EITA_NO_LEAN_WRAPPER
#include <lean/lean.h>
#endif

static const uint64_t IV[8] = {
    0x6a09e667f3bcc908ULL, 0xbb67ae8584caa73bULL,
    0x3c6ef372fe94f82bULL, 0xa54ff53a5f1d36f1ULL,
    0x510e527fade682d1ULL, 0x9b05688c2b3e6c1fULL,
    0x1f83d9abfb41bd6bULL, 0x5be0cd19137e2179ULL,
};

static const uint8_t SIGMA[12][16] = {
    { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,10,11,12,13,14,15},
    {14,10, 4, 8, 9,15,13, 6, 1,12, 0, 2,11, 7, 5, 3},
    {11, 8,12, 0, 5, 2,15,13,10,14, 3, 6, 7, 1, 9, 4},
    { 7, 9, 3, 1,13,12,11,14, 2, 6, 5,10, 4, 0,15, 8},
    { 9, 0, 5, 7, 2, 4,10,15,14, 1,11,12, 6, 8, 3,13},
    { 2,12, 6,10, 0,11, 8, 3, 4,13, 7, 5,15,14, 1, 9},
    {12, 5, 1,15,14,13, 4,10, 0, 7, 6, 3, 9, 2, 8,11},
    {13,11, 7,14,12, 1, 3, 9, 5, 0,15, 4, 8, 6, 2,10},
    { 6,15,14, 9,11, 3, 0, 8,12, 2,13, 7, 1, 4,10, 5},
    {10, 2, 8, 4, 7, 6, 1, 5,15,11, 9,14, 3,12,13, 0},
    /* For >10 rounds, sigma indices repeat modulo 10. */
    { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,10,11,12,13,14,15},
    {14,10, 4, 8, 9,15,13, 6, 1,12, 0, 2,11, 7, 5, 3},
};

static inline uint64_t rotr64(uint64_t x, unsigned n) {
    return (x >> n) | (x << (64 - n));
}

#define G(a, b, c, d, x, y) do {    \
    v[a] = v[a] + v[b] + (x);       \
    v[d] = rotr64(v[d] ^ v[a], 32); \
    v[c] = v[c] + v[d];             \
    v[b] = rotr64(v[b] ^ v[c], 24); \
    v[a] = v[a] + v[b] + (y);       \
    v[d] = rotr64(v[d] ^ v[a], 16); \
    v[c] = v[c] + v[d];             \
    v[b] = rotr64(v[b] ^ v[c], 63); \
} while (0)

static uint64_t load_le64(const uint8_t *p) {
    uint64_t v = 0;
    for (int i = 7; i >= 0; i--) v = (v << 8) | p[i];
    return v;
}

static void store_le64(uint8_t *p, uint64_t v) {
    for (int i = 0; i < 8; i++) { p[i] = (uint8_t)v; v >>= 8; }
}

int eita_blake2f(const uint8_t *src, size_t src_len, uint8_t out[64]) {
    if (src_len != 213) return 0;
    uint8_t f_byte = src[212];
    if (f_byte != 0 && f_byte != 1) return 0;

    uint32_t rounds = ((uint32_t)src[0] << 24) | ((uint32_t)src[1] << 16) |
                      ((uint32_t)src[2] << 8)  |  (uint32_t)src[3];

    uint64_t h[8], m[16], t[2];
    for (int i = 0; i < 8;  i++) h[i] = load_le64(src + 4   + 8 * i);
    for (int i = 0; i < 16; i++) m[i] = load_le64(src + 68  + 8 * i);
    t[0] = load_le64(src + 196);
    t[1] = load_le64(src + 204);

    uint64_t v[16];
    for (int i = 0; i < 8; i++) { v[i] = h[i]; v[i + 8] = IV[i]; }
    v[12] ^= t[0];
    v[13] ^= t[1];
    if (f_byte) v[14] = ~v[14];

    for (uint32_t r = 0; r < rounds; r++) {
        const uint8_t *s = SIGMA[r % 10];
        G(0, 4,  8, 12, m[s[0]],  m[s[1]]);
        G(1, 5,  9, 13, m[s[2]],  m[s[3]]);
        G(2, 6, 10, 14, m[s[4]],  m[s[5]]);
        G(3, 7, 11, 15, m[s[6]],  m[s[7]]);
        G(0, 5, 10, 15, m[s[8]],  m[s[9]]);
        G(1, 6, 11, 12, m[s[10]], m[s[11]]);
        G(2, 7,  8, 13, m[s[12]], m[s[13]]);
        G(3, 4,  9, 14, m[s[14]], m[s[15]]);
    }

    for (int i = 0; i < 8; i++) {
        h[i] ^= v[i] ^ v[i + 8];
        store_le64(out + 8 * i, h[i]);
    }
    return 1;
}

#ifndef EITA_NO_LEAN_WRAPPER
/* Lean binding for the cryptoTests differential test (this C against the pure-Lean
 * RFC 7693 F, Evm.Crypto.Blake2f). Empty ByteArray on invalid input. */
LEAN_EXPORT lean_obj_res lean_blake2f(b_lean_obj_arg input) {
    uint8_t out[64];
    if (!eita_blake2f(lean_sarray_cptr(input), lean_sarray_size(input), out))
        return lean_alloc_sarray(1, 0, 0);
    lean_obj_res o = lean_alloc_sarray(1, 64, 64);
    memcpy(lean_sarray_cptr(o), out, 64);
    return o;
}
#endif
