/*
 * bn254.cpp — Lean FFI for the EIP-196 / EIP-197 alt_bn128 (BN254)
 * precompiles. Wraps mcl (Mitsunari's curve library, MCL_BN_SNARK1
 * curve flavor = Ethereum's alt_bn128) and exposes three functions
 * with the precompile-shaped Lean signatures:
 *
 *   lean_bn254_add(input64)     -> ByteArray 64  (EIP-196, 0x06)
 *   lean_bn254_mul(input96)     -> ByteArray 64  (EIP-196, 0x07)
 *   lean_bn254_pairing(input)   -> ByteArray 32  (EIP-197, 0x08)
 *
 * All inputs are zero-padded on the right if shorter than the
 * expected length (matching EELS semantics). All outputs are
 * fixed-size big-endian.
 *
 * Linked against libmcl (Homebrew: brew install mcl).
 */

#define MCL_DONT_USE_OPENSSL
#define MCL_USE_VINT
#define MCL_VINT_FIXED_BUFFER
#define MCL_SIZEOF_UNIT 8
/* The installed libmcl was built with MCL_FP_BIT=384 (BLS12-381
 * sized). bn_c256.h compiles to MCLBN_COMPILED_TIME_VAR=44 which
 * mismatches the dylib's CTV=46 and makes mclBn_init reject every
 * curve. bn_c384_256.h matches the dylib's build (Fp=384, Fr=256)
 * and runs BN254 internally via SNARK1 just fine — the EVM-shaped
 * 32-byte BE serialization is independent of the internal Fp
 * representation. */
#include <mcl/bn_c384_256.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#ifndef EITA_NO_LEAN_WRAPPER
#include <lean/lean.h>
#endif

/*
 * mcl's active curve is process-global, and mcl is PINNED to BN254
 * (MCL_BN_SNARK1 == alt_bn128) for the life of the process: the EIP-2537
 * BLS12-381 precompiles are built on blst instead, because re-initialising
 * mcl to switch families cost 2.8 ms per round trip and was charged no gas.
 * eita_mcl_curve() is the only caller of mclBn_init and refuses any other
 * curve, so nothing can invalidate the Montgomery form these values are
 * stored in. See mcl_curve.h.
 *
 * Returns 1 if mcl is ready to call into, 0 if init failed (typically a
 * build-config / MCLBN_COMPILED_TIME_VAR mismatch with the headers). On a
 * failure we DO NOT call any subsequent mcl APIs — they would either
 * return garbage or segfault on edge inputs (e.g. ecpairing on points
 * just past the field modulus). Callers fall back to returning zero
 * outputs in that case, matching the pre-FFI stub behaviour.
 */
#include "mcl_curve.h"
static int ensure_init(void) { return eita_mcl_curve(MCL_BN_SNARK1); }

/*
 * BN254 base field modulus (big-endian):
 *   p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
 *     = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
 *
 * EELS rejects any Fp coordinate whose raw 32-byte BE value is >= p
 * (`Fq.from_bytes` raises). mcl's `setBigEndianMod` silently reduces,
 * so we have to compare the raw bytes ourselves before accepting.
 */
static const uint8_t BN254_FIELD_MODULUS[32] = {
    0x30,0x64,0x4e,0x72,0xe1,0x31,0xa0,0x29,
    0xb8,0x50,0x45,0xb6,0x81,0x81,0x58,0x5d,
    0x97,0x81,0x6a,0x91,0x68,0x71,0xca,0x8d,
    0x3c,0x20,0x8c,0x16,0xd8,0x7c,0xfd,0x47,
};

/* Returns 1 iff `bytes` (32 BE) is < p. */
static int fp_in_range(const uint8_t *bytes) {
    for (int i = 0; i < 32; i++) {
        if (bytes[i] < BN254_FIELD_MODULUS[i]) return 1;
        if (bytes[i] > BN254_FIELD_MODULUS[i]) return 0;
    }
    return 0;  /* equal: not strictly less */
}

/*
 * Decode a 32-byte big-endian Fp element from `src` into mclBnFp.
 * Returns 0 on success, non-zero if the value is >= field modulus.
 */
static int fp_from_be(mclBnFp *out, const uint8_t *src) {
    if (!fp_in_range(src)) return 1;
    return mclBnFp_setBigEndianMod(out, src, 32);
}

/*
 * EVM serialization for G1: 64 bytes = (x:32 BE) || (y:32 BE).
 * (0, 0) is treated as the point at infinity.
 * Returns 0 on success; non-zero if the point is not on the curve.
 */
static int g1_from_be(mclBnG1 *out, const uint8_t *src) {
    static const uint8_t zero64[64] = {0};
    if (memcmp(src, zero64, 64) == 0) {
        mclBnG1_clear(out);  // point at infinity
        return 0;
    }
    mclBnFp x, y;
    if (fp_from_be(&x, src) != 0) return 1;
    if (fp_from_be(&y, src + 32) != 0) return 1;
    // Set affine (x, y) and z = 1 via the projective constructor
    mclBnFp_setInt(&out->z, 1);
    out->x = x;
    out->y = y;
    if (!mclBnG1_isValid(out)) return 1;
    return 0;
}

/*
 * EVM serialization for G2: 128 bytes = (x_im:32 || x_re:32 || y_im:32 || y_re:32) BE.
 * NOTE the Im/Re ordering — Ethereum uses big-endian by component, with
 * imaginary first (matches the original Solidity precompile spec).
 */
static int g2_from_be(mclBnG2 *out, const uint8_t *src) {
    static const uint8_t zero128[128] = {0};
    if (memcmp(src, zero128, 128) == 0) {
        mclBnG2_clear(out);
        return 0;
    }
    mclBnFp x_im, x_re, y_im, y_re;
    if (fp_from_be(&x_im, src) != 0) return 1;
    if (fp_from_be(&x_re, src + 32) != 0) return 1;
    if (fp_from_be(&y_im, src + 64) != 0) return 1;
    if (fp_from_be(&y_re, src + 96) != 0) return 1;
    out->x.d[0] = x_re;
    out->x.d[1] = x_im;
    out->y.d[0] = y_re;
    out->y.d[1] = y_im;
    mclBnFp_setInt32(&out->z.d[0], 1);
    // Zero the imaginary part of z by serializing a zero into it
    uint8_t zero32[32] = {0};
    mclBnFp_setLittleEndian(&out->z.d[1], zero32, 32);
    if (!mclBnG2_isValid(out)) return 1;
    return 0;
}

/* Encode G1 to EVM 64-byte form: (x:32 BE) || (y:32 BE), zeros for infinity. */
static void g1_to_be(uint8_t *dst, const mclBnG1 *g) {
    if (mclBnG1_isZero(g)) {
        memset(dst, 0, 64);
        return;
    }
    // Normalize to affine before serializing.
    mclBnG1 normalized;
    mclBnG1_normalize(&normalized, g);
    mclBnFp_serialize(dst,      32, &normalized.x);
    mclBnFp_serialize(dst + 32, 32, &normalized.y);
    // mcl serializes little-endian; reverse to big-endian
    for (int i = 0; i < 16; i++) {
        uint8_t t = dst[i]; dst[i] = dst[31 - i]; dst[31 - i] = t;
        t = dst[32 + i]; dst[32 + i] = dst[63 - i]; dst[63 - i] = t;
    }
}

/* ---------- Lean exports ----------
 *
 * These must have C linkage so the Lean-emitted C call sites can find
 * them through the unmangled `lean_bn254_*` symbols; without `extern
 * "C"` C++ would mangle the names and the link would fail.
 */

/* Pad `in` to `n` bytes on the right with zeros. */
static void pad_input(const uint8_t *src, size_t src_n, uint8_t *dst, size_t n) {
    size_t copy = src_n < n ? src_n : n;
    memcpy(dst, src, copy);
    if (copy < n) memset(dst + copy, 0, n - copy);
}

extern "C" {

/* Convention: a successful ECADD / ECMUL result is exactly 64 bytes
 * of (x:32 BE) || (y:32 BE). Invalid-input failure (point off curve,
 * coordinate ≥ field modulus, etc.) is signalled by a zero return,
 * which callers map to OOG — matching EELS's `OutOfGasError` for
 * malformed inputs. mcl-init failure also yields a 64-byte zero
 * output (treated as success-with-zero-point, matching the pre-FFI
 * stub behaviour). */

/* Plain-C entry points. Output buffers must be sized:
 *   add/mul: 64 bytes
 *   pairing: 32 bytes
 * Return 1 on success (including "valid input that produced an output"),
 * 0 on invalid input (caller treats as OOG). */

int eita_bn254_add(const uint8_t *src, size_t n, uint8_t out[64]) {
    int ok = ensure_init();
    uint8_t buf[128];
    pad_input(src, n, buf, 128);
    if (!ok) { memset(out, 0, 64); return 1; }
    mclBnG1 p, q, r;
    if (g1_from_be(&p, buf) != 0 || g1_from_be(&q, buf + 64) != 0) return 0;
    mclBnG1_add(&r, &p, &q);
    g1_to_be(out, &r);
    return 1;
}

int eita_bn254_mul(const uint8_t *src, size_t n, uint8_t out[64]) {
    int ok = ensure_init();
    uint8_t buf[96];
    pad_input(src, n, buf, 96);
    if (!ok) { memset(out, 0, 64); return 1; }
    mclBnG1 p, r;
    mclBnFr s;
    if (g1_from_be(&p, buf) != 0) return 0;
    mclBnFr_setBigEndianMod(&s, buf + 64, 32);
    mclBnG1_mul(&r, &p, &s);
    g1_to_be(out, &r);
    return 1;
}

int eita_bn254_pairing(const uint8_t *src, size_t n, uint8_t out[32]) {
    int ok = ensure_init();
    if (!ok) { memset(out, 0, 32); return 1; }
    /* EELS raises OutOfGasError on input.size % 192 != 0. */
    if (n % 192 != 0) return 0;
    size_t k = n / 192;
    memset(out, 0, 31);
    if (k == 0) { out[31] = 1; return 1; }
    mclBnGT acc;
    int first = 1;
    for (size_t i = 0; i < k; i++) {
        const uint8_t *blk = src + i * 192;
        mclBnG1 g1;
        mclBnG2 g2;
        if (g1_from_be(&g1, blk) != 0 || g2_from_be(&g2, blk + 64) != 0) return 0;
        mclBnGT e;
        mclBn_pairing(&e, &g1, &g2);
        if (first) { acc = e; first = 0; }
        else       { mclBnGT_mul(&acc, &acc, &e); }
    }
    out[31] = mclBnGT_isOne(&acc) ? 1 : 0;
    return 1;
}

#ifndef EITA_NO_LEAN_WRAPPER
LEAN_EXPORT lean_obj_res lean_bn254_add(b_lean_obj_arg input) {
    size_t n = lean_sarray_size(input);
    const uint8_t *src = lean_sarray_cptr(input);
    uint8_t buf[64];
    if (!eita_bn254_add(src, n, buf)) return lean_alloc_sarray(1, 0, 0);
    lean_obj_res out = lean_alloc_sarray(1, 64, 64);
    memcpy(lean_sarray_cptr(out), buf, 64);
    return out;
}

LEAN_EXPORT lean_obj_res lean_bn254_mul(b_lean_obj_arg input) {
    size_t n = lean_sarray_size(input);
    const uint8_t *src = lean_sarray_cptr(input);
    uint8_t buf[64];
    if (!eita_bn254_mul(src, n, buf)) return lean_alloc_sarray(1, 0, 0);
    lean_obj_res out = lean_alloc_sarray(1, 64, 64);
    memcpy(lean_sarray_cptr(out), buf, 64);
    return out;
}

LEAN_EXPORT lean_obj_res lean_bn254_pairing(b_lean_obj_arg input) {
    size_t n = lean_sarray_size(input);
    const uint8_t *src = lean_sarray_cptr(input);
    uint8_t buf[32];
    if (!eita_bn254_pairing(src, n, buf)) return lean_alloc_sarray(1, 0, 0);
    lean_obj_res out = lean_alloc_sarray(1, 32, 32);
    memcpy(lean_sarray_cptr(out), buf, 32);
    return out;
}
#endif

} /* extern "C" */
