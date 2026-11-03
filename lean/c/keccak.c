/*
 * keccak.c — Ethereum-style Keccak-256 (pre-FIPS-202; pad byte 0x01).
 *
 * Used by Lean via the @[extern] binding `lean_keccak256`. The state
 * machine is the standard Keccak-f[1600] with rate=1088 bits, capacity=
 * 512 bits, 24 rounds.
 *
 * The permutation keeps the 25 lanes in locals (rho and pi fused into one
 * pass, chi out of it): the loop-over-arrays form (tiny_sha3) was 12 % of the
 * x86-64 near-tip replay. Ethereum's 0x01 padding instead of SHA-3's 0x06.
 * Assumes a little-endian host.
 */

#include <stdint.h>
#include <string.h>
#include <stddef.h>
#ifndef EITA_NO_LEAN_WRAPPER
#include <lean/lean.h>
#endif

#define ROTL64(x, y) (((x) << (y)) | ((x) >> (64 - (y))))

static const uint64_t keccakf_rndc[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL,
    0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL,
    0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL,
    0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL,
    0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL,
    0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL,
    0x0000000080000001ULL, 0x8000000080008008ULL
};

static void keccakf(uint64_t st[25]) {
    /* Keccak-f[1600] with the 25 lanes in locals, one round per iteration:
       theta, then rho+pi straight into B (B[y,2x+3y] = rot(A[x,y]^D[x], r[x,y])),
       chi from B back into A, iota. a<x><y> is lane x+5y of st. */
    uint64_t a00 = st[0], a10 = st[1], a20 = st[2], a30 = st[3], a40 = st[4], a01 = st[5], a11 = st[6], a21 = st[7], a31 = st[8], a41 = st[9], a02 = st[10], a12 = st[11], a22 = st[12], a32 = st[13], a42 = st[14], a03 = st[15], a13 = st[16], a23 = st[17], a33 = st[18], a43 = st[19], a04 = st[20], a14 = st[21], a24 = st[22], a34 = st[23], a44 = st[24];
    for (int r = 0; r < 24; r++) {
        uint64_t c0 = a00 ^ a01 ^ a02 ^ a03 ^ a04;
        uint64_t c1 = a10 ^ a11 ^ a12 ^ a13 ^ a14;
        uint64_t c2 = a20 ^ a21 ^ a22 ^ a23 ^ a24;
        uint64_t c3 = a30 ^ a31 ^ a32 ^ a33 ^ a34;
        uint64_t c4 = a40 ^ a41 ^ a42 ^ a43 ^ a44;
        uint64_t d0 = c4 ^ ROTL64(c1, 1);
        uint64_t d1 = c0 ^ ROTL64(c2, 1);
        uint64_t d2 = c1 ^ ROTL64(c3, 1);
        uint64_t d3 = c2 ^ ROTL64(c4, 1);
        uint64_t d4 = c3 ^ ROTL64(c0, 1);
        uint64_t b00 = (a00 ^ d0); uint64_t b10 = ROTL64(a11 ^ d1, 44); uint64_t b20 = ROTL64(a22 ^ d2, 43); uint64_t b30 = ROTL64(a33 ^ d3, 21); uint64_t b40 = ROTL64(a44 ^ d4, 14);
        uint64_t b01 = ROTL64(a30 ^ d3, 28); uint64_t b11 = ROTL64(a41 ^ d4, 20); uint64_t b21 = ROTL64(a02 ^ d0, 3); uint64_t b31 = ROTL64(a13 ^ d1, 45); uint64_t b41 = ROTL64(a24 ^ d2, 61);
        uint64_t b02 = ROTL64(a10 ^ d1, 1); uint64_t b12 = ROTL64(a21 ^ d2, 6); uint64_t b22 = ROTL64(a32 ^ d3, 25); uint64_t b32 = ROTL64(a43 ^ d4, 8); uint64_t b42 = ROTL64(a04 ^ d0, 18);
        uint64_t b03 = ROTL64(a40 ^ d4, 27); uint64_t b13 = ROTL64(a01 ^ d0, 36); uint64_t b23 = ROTL64(a12 ^ d1, 10); uint64_t b33 = ROTL64(a23 ^ d2, 15); uint64_t b43 = ROTL64(a34 ^ d3, 56);
        uint64_t b04 = ROTL64(a20 ^ d2, 62); uint64_t b14 = ROTL64(a31 ^ d3, 55); uint64_t b24 = ROTL64(a42 ^ d4, 39); uint64_t b34 = ROTL64(a03 ^ d0, 41); uint64_t b44 = ROTL64(a14 ^ d1, 2);
        a00 = b00 ^ (~b10 & b20); a10 = b10 ^ (~b20 & b30); a20 = b20 ^ (~b30 & b40); a30 = b30 ^ (~b40 & b00); a40 = b40 ^ (~b00 & b10);
        a01 = b01 ^ (~b11 & b21); a11 = b11 ^ (~b21 & b31); a21 = b21 ^ (~b31 & b41); a31 = b31 ^ (~b41 & b01); a41 = b41 ^ (~b01 & b11);
        a02 = b02 ^ (~b12 & b22); a12 = b12 ^ (~b22 & b32); a22 = b22 ^ (~b32 & b42); a32 = b32 ^ (~b42 & b02); a42 = b42 ^ (~b02 & b12);
        a03 = b03 ^ (~b13 & b23); a13 = b13 ^ (~b23 & b33); a23 = b23 ^ (~b33 & b43); a33 = b33 ^ (~b43 & b03); a43 = b43 ^ (~b03 & b13);
        a04 = b04 ^ (~b14 & b24); a14 = b14 ^ (~b24 & b34); a24 = b24 ^ (~b34 & b44); a34 = b34 ^ (~b44 & b04); a44 = b44 ^ (~b04 & b14);
        a00 ^= keccakf_rndc[r];
    }
    st[0] = a00; st[1] = a10; st[2] = a20; st[3] = a30; st[4] = a40; st[5] = a01; st[6] = a11; st[7] = a21; st[8] = a31; st[9] = a41; st[10] = a02; st[11] = a12; st[12] = a22; st[13] = a32; st[14] = a42; st[15] = a03; st[16] = a13; st[17] = a23; st[18] = a33; st[19] = a43; st[20] = a04; st[21] = a14; st[22] = a24; st[23] = a34; st[24] = a44;
}


/* Compute Ethereum's Keccak-256 of `in[0..len)` into `out[0..32)`.
   Non-static so ecrecover.c can pull the public-key bytes through it. */
void keccak256(const uint8_t *in, size_t len, uint8_t out[32]) {
    uint64_t st[25];
    uint8_t *sb = (uint8_t *)st;
    const size_t rate = 136;  /* 1088 / 8 */
    size_t i;

    memset(st, 0, sizeof(st));

    while (len >= rate) {
        for (i = 0; i < rate / 8; i++) { uint64_t w; memcpy(&w, in + 8 * i, 8); st[i] ^= w; }
        keccakf(st);
        in += rate;
        len -= rate;
    }

    /* Pad: 0x01 at position `len`, 0x80 at position rate-1 (may overlap
       in the single-byte case len == rate-1). */
    uint8_t pad[136];
    memset(pad, 0, sizeof(pad));
    memcpy(pad, in, len);
    pad[len] |= 0x01;
    pad[rate - 1] |= 0x80;

    for (i = 0; i < rate / 8; i++) { uint64_t w; memcpy(&w, pad + 8 * i, 8); st[i] ^= w; }
    keccakf(st);

    memcpy(out, sb, 32);
}

/* `eita_keccak256` is the canonical plain-C name used by libeita.dylib's
   ARM64 KECCAK256 handler. Older callers (lean/c/ecrecover.c) still use the
   short `keccak256` name — same function, two symbols. */
void eita_keccak256(const uint8_t *in, size_t len, uint8_t out[32]) {
    keccak256(in, len, out);
}

#ifndef EITA_NO_LEAN_WRAPPER
/* Lean FFI entry point: ByteArray → ByteArray. */
LEAN_EXPORT lean_obj_res lean_keccak256(b_lean_obj_arg input) {
    size_t n = lean_sarray_size(input);
    const uint8_t *src = lean_sarray_cptr(input);

    lean_obj_res out = lean_alloc_sarray(1, 32, 32);
    keccak256(src, n, lean_sarray_cptr(out));
    return out;
}
#endif
