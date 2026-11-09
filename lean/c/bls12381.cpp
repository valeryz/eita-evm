/*
 * bls12381.cpp — FFI for the EIP-2537 BLS12-381 precompiles (0x0b .. 0x11):
 *
 *   0x0b G1ADD          256 B -> 128 B
 *   0x0c G1MSM          160k B -> 128 B
 *   0x0d G2ADD          512 B -> 256 B
 *   0x0e G2MSM          288k B -> 256 B
 *   0x0f PAIRING_CHECK  384k B -> 32 B
 *   0x10 MAP_FP_TO_G1    64 B -> 128 B
 *   0x11 MAP_FP2_TO_G2  128 B -> 256 B
 *
 * Every entry point returns 1 on success with `out` filled, and 0 on ANY
 * invalid input. Unlike the EIP-196/197 BN254 precompiles, EIP-2537 does NOT
 * right-pad a short input: lengths are exact (ADD, MAP) or an exact non-zero
 * multiple (MSM, PAIRING), and a wrong length is a hard failure that consumes
 * all the gas the caller forwarded.
 *
 * Built on blst (vendor/blst, pinned release). blst was chosen over mcl for one
 * structural reason: mcl keeps the active curve in process-global state, so
 * serving BN254 and BLS12-381 from it meant re-initialising on every change of
 * family. Measured, that cost 2.8 ms per round trip against 0.78 ms for a
 * 2-pair pairing check, and it was charged no gas — a transaction alternating a
 * 375-gas G1ADD with a 150-gas BN254 add could buy roughly 80 seconds of
 * switching inside one 30M-gas block. blst carries no global curve state, so
 * mcl now stays pinned to BN254 forever (see mcl_curve.h) and the stall is
 * unrepresentable rather than merely avoided.
 *
 * Encoding (confirmed against the canonical outputs in
 * lean/c/testdata/bls12381-vectors.json, not just read off the EIP):
 *
 *   field element  64 B = 16 bytes that must be ZERO || 48-byte big-endian
 *                  value that must be strictly less than p
 *   G1 point      128 B = x || y                   (y^2 = x^3 + 4 over Fp)
 *   G2 point      256 B = x.c0 || x.c1 || y.c0 || y.c1
 *                  i.e. REAL component first, which is the opposite of the
 *                  BN254 precompiles' imaginary-first order in bn254.cpp
 *   infinity       all zero bytes
 *
 * Deliberately NOT using blst_p1_deserialize / blst_p2_deserialize even though
 * they look like a fit. Two reasons: they read the top three bits of the first
 * byte as compression/infinity/sign flags, which is not what EIP-2537 means by
 * those bits; and blst's uncompressed G2 is x.c1 || x.c0 || y.c1 || y.c0, the
 * IMAGINARY component first, the opposite of EIP-2537. Assembling the affine
 * structs from blst_fp_from_bendian keeps the byte order explicit and local, at
 * the price of doing the range check here (blst_fp_from_bendian does not).
 *
 * Subgroup (correct-order) checks apply to MSM and PAIRING inputs. G1ADD and
 * G2ADD check only that the point is on the curve — EIP-2537 deliberately
 * omits the order check there, and the oracle's "two subgroup points" and
 * "point not on the curve" cases pin both halves of that.
 */
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

/* A heap array without the C++ runtime: Lean executables link this file without
 * libstdc++, so no std::vector / operator new here (std::__throw_length_error would
 * be undefined at link time on Linux). Allocation failure aborts, as bad_alloc did. */
template <class T> struct HeapArr {
    T *p;
    explicit HeapArr(size_t k) : p((T *) malloc(k ? k * sizeof(T) : 1)) { if (!p) abort(); }
    ~HeapArr() { free(p); }
    HeapArr(const HeapArr &) = delete;
    HeapArr &operator=(const HeapArr &) = delete;
    T &operator[](size_t i) { return p[i]; }
    T *data() { return p; }
};
#include "blst.h"
#ifndef EITA_NO_LEAN_WRAPPER
#include <lean/lean.h>

#endif

/* p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624
 *     1eabfffeb153ffffb9feffffffffaaab  (big-endian, 48 bytes) */
static const uint8_t BLS_P[48] = {
    0x1a,0x01,0x11,0xea,0x39,0x7f,0xe6,0x9a,0x4b,0x1b,0xa7,0xb6,
    0x43,0x4b,0xac,0xd7,0x64,0x77,0x4b,0x84,0xf3,0x85,0x12,0xbf,
    0x67,0x30,0xd2,0xa0,0xf6,0xb0,0xf6,0x24,0x1e,0xab,0xff,0xfe,
    0xb1,0x53,0xff,0xff,0xb9,0xfe,0xff,0xff,0xff,0xff,0xaa,0xab,
};

enum {
    FP_BYTES = 64, FP_PAD = 16, FP_VAL = 48,
    G1_BYTES = 128, G2_BYTES = 256,
    G1ADD_IN = 256, G2ADD_IN = 512,
    G1MSM_PAIR = 160, G2MSM_PAIR = 288, PAIRING_PAIR = 384,
    SCALAR_BYTES = 32, SCALAR_BITS = 256,
};

/* Returns 1 iff the 48-byte big-endian value is strictly less than p. */
static int fp_lt_p(const uint8_t *be) {
    for (int i = 0; i < FP_VAL; i++) {
        if (be[i] < BLS_P[i]) return 1;
        if (be[i] > BLS_P[i]) return 0;
    }
    return 0;   /* equal to p is NOT a valid field element */
}

/* Decode one 64-byte EIP-2537 field element. Returns 1 on success. */
static int fp_from_be(blst_fp *out, const uint8_t *src) {
    for (int i = 0; i < FP_PAD; i++)
        if (src[i] != 0) return 0;            /* top padding must be zero */
    if (!fp_lt_p(src + FP_PAD)) return 0;
    blst_fp_from_bendian(out, src + FP_PAD);
    return 1;
}

static void fp_to_be(uint8_t *dst, const blst_fp *x) {
    memset(dst, 0, FP_PAD);
    blst_bendian_from_fp(dst + FP_PAD, x);
}

static int is_zero_bytes(const uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) if (p[i]) return 0;
    return 1;
}

/* Parse a 128-byte G1 point. CHECK_ORDER adds the subgroup check.
 * blst's affine infinity is x = y = 0, which is exactly EIP-2537's all-zeros,
 * but the on-curve predicate is only meaningful off infinity so it is skipped
 * there deliberately. */
static int g1_from_be(blst_p1_affine *out, const uint8_t *src, int check_order) {
    memset(out, 0, sizeof *out);
    if (is_zero_bytes(src, G1_BYTES)) return 1;             /* infinity */
    if (!fp_from_be(&out->x, src)) return 0;
    if (!fp_from_be(&out->y, src + FP_BYTES)) return 0;
    if (!blst_p1_affine_on_curve(out)) return 0;
    if (check_order && !blst_p1_affine_in_g1(out)) return 0;
    return 1;
}

/* Parse a 256-byte G2 point: x.c0, x.c1, y.c0, y.c1 (real component first).
 * blst_fp2 documents fp[0] as the real part, so the mapping is direct. */
static int g2_from_be(blst_p2_affine *out, const uint8_t *src, int check_order) {
    memset(out, 0, sizeof *out);
    if (is_zero_bytes(src, G2_BYTES)) return 1;             /* infinity */
    if (!fp_from_be(&out->x.fp[0], src + 0 * FP_BYTES)) return 0;
    if (!fp_from_be(&out->x.fp[1], src + 1 * FP_BYTES)) return 0;
    if (!fp_from_be(&out->y.fp[0], src + 2 * FP_BYTES)) return 0;
    if (!fp_from_be(&out->y.fp[1], src + 3 * FP_BYTES)) return 0;
    if (!blst_p2_affine_on_curve(out)) return 0;
    if (check_order && !blst_p2_affine_in_g2(out)) return 0;
    return 1;
}

static void g1_to_be(uint8_t *dst, const blst_p1 *g) {
    memset(dst, 0, G1_BYTES);
    if (blst_p1_is_inf(g)) return;                  /* infinity = all zeros */
    blst_p1_affine aff;
    blst_p1_to_affine(&aff, g);
    fp_to_be(dst, &aff.x);
    fp_to_be(dst + FP_BYTES, &aff.y);
}

static void g2_to_be(uint8_t *dst, const blst_p2 *g) {
    memset(dst, 0, G2_BYTES);
    if (blst_p2_is_inf(g)) return;
    blst_p2_affine aff;
    blst_p2_to_affine(&aff, g);
    fp_to_be(dst + 0 * FP_BYTES, &aff.x.fp[0]);
    fp_to_be(dst + 1 * FP_BYTES, &aff.x.fp[1]);
    fp_to_be(dst + 2 * FP_BYTES, &aff.y.fp[0]);
    fp_to_be(dst + 3 * FP_BYTES, &aff.y.fp[1]);
}

/* The group operations the precompiles below are made of, shared with the Lean oracle
 * (lean_bls_oracle_*, Evm.Crypto.Bls12381.native), so the Lean replay runs the same blst
 * calls as production. [k]O = O is handled here: blst's mult is not defined on infinity.
 * SCALAR is 32 bytes big-endian; no reduction mod r is needed or permitted to change the
 * result for a point of order r. */
static void g1_mul(blst_p1 *out, const blst_p1_affine *a, const uint8_t *scalar_be) {
    memset(out, 0, sizeof *out);                         /* identity */
    if (blst_p1_affine_is_inf(a)) return;
    blst_scalar s;
    blst_scalar_from_bendian(&s, scalar_be);
    blst_p1 pa;
    blst_p1_from_affine(&pa, a);
    blst_p1_mult(out, &pa, s.b, SCALAR_BITS);
}

static void g2_mul(blst_p2 *out, const blst_p2_affine *a, const uint8_t *scalar_be) {
    memset(out, 0, sizeof *out);
    if (blst_p2_affine_is_inf(a)) return;
    blst_scalar s;
    blst_scalar_from_bendian(&s, scalar_be);
    blst_p2 pa;
    blst_p2_from_affine(&pa, a);
    blst_p2_mult(out, &pa, s.b, SCALAR_BITS);
}

/* Whether prod e(Q_i, P_i) = 1. e(O, Q) = e(P, O) = 1, and blst's miller loop is not
 * defined on infinity, so those pairs contribute the identity and are skipped. */
static int pairing_is_one(const blst_p1_affine *g1, const blst_p2_affine *g2, size_t k) {
    blst_fp12 acc = *blst_fp12_one();
    for (size_t i = 0; i < k; i++) {
        if (blst_p1_affine_is_inf(&g1[i]) || blst_p2_affine_is_inf(&g2[i])) continue;
        blst_fp12 e;
        blst_miller_loop(&e, &g2[i], &g1[i]);
        blst_fp12_mul(&acc, &acc, &e);
    }
    blst_final_exp(&acc, &acc);
    return blst_fp12_is_one(&acc) ? 1 : 0;
}

extern "C" {

int eita_bls_g1add(const uint8_t *in, size_t len, uint8_t *out) {
    if (len != G1ADD_IN) return 0;
    blst_p1_affine a, b;
    /* no subgroup check: EIP-2537 requires only that both points be on-curve */
    if (!g1_from_be(&a, in, 0) || !g1_from_be(&b, in + G1_BYTES, 0)) return 0;
    blst_p1 pa, r;
    blst_p1_from_affine(&pa, &a);
    blst_p1 pb;
    blst_p1_from_affine(&pb, &b);
    blst_p1_add_or_double(&r, &pa, &pb);   /* handles a == b and infinity */
    g1_to_be(out, &r);
    return 1;
}

int eita_bls_g2add(const uint8_t *in, size_t len, uint8_t *out) {
    if (len != G2ADD_IN) return 0;
    blst_p2_affine a, b;
    if (!g2_from_be(&a, in, 0) || !g2_from_be(&b, in + G2_BYTES, 0)) return 0;
    blst_p2 pa, pb, r;
    blst_p2_from_affine(&pa, &a);
    blst_p2_from_affine(&pb, &b);
    blst_p2_add_or_double(&r, &pa, &pb);
    g2_to_be(out, &r);
    return 1;
}

int eita_bls_g1msm(const uint8_t *in, size_t len, uint8_t *out) {
    if (len == 0 || len % G1MSM_PAIR != 0) return 0;
    size_t k = len / G1MSM_PAIR;
    /* Parse everything before computing: a later invalid pair must reject the
     * whole call, not return a partial sum. */
    HeapArr<blst_p1_affine> pts(k);
    for (size_t i = 0; i < k; i++)
        if (!g1_from_be(&pts[i], in + i * G1MSM_PAIR, 1)) return 0;   /* subgroup required */
    blst_p1 acc;
    memset(&acc, 0, sizeof acc);                         /* identity */
    for (size_t i = 0; i < k; i++) {
        blst_p1 term;
        g1_mul(&term, &pts[i], in + i * G1MSM_PAIR + G1_BYTES);
        blst_p1_add_or_double(&acc, &acc, &term);
    }
    g1_to_be(out, &acc);
    return 1;
}

int eita_bls_g2msm(const uint8_t *in, size_t len, uint8_t *out) {
    if (len == 0 || len % G2MSM_PAIR != 0) return 0;
    size_t k = len / G2MSM_PAIR;
    HeapArr<blst_p2_affine> pts(k);
    for (size_t i = 0; i < k; i++)
        if (!g2_from_be(&pts[i], in + i * G2MSM_PAIR, 1)) return 0;
    blst_p2 acc;
    memset(&acc, 0, sizeof acc);
    for (size_t i = 0; i < k; i++) {
        blst_p2 term;
        g2_mul(&term, &pts[i], in + i * G2MSM_PAIR + G2_BYTES);
        blst_p2_add_or_double(&acc, &acc, &term);
    }
    g2_to_be(out, &acc);
    return 1;
}

int eita_bls_pairing(const uint8_t *in, size_t len, uint8_t *out) {
    /* An EMPTY input fails here, where EIP-197's BN254 pairing treats it as the
     * empty product and returns 1. Confirmed against the chain. */
    if (len == 0 || len % PAIRING_PAIR != 0) return 0;
    size_t k = len / PAIRING_PAIR;
    HeapArr<blst_p1_affine> g1(k);
    HeapArr<blst_p2_affine> g2(k);
    for (size_t i = 0; i < k; i++) {
        const uint8_t *p = in + i * PAIRING_PAIR;
        if (!g1_from_be(&g1[i], p, 1)) return 0;         /* subgroup required */
        if (!g2_from_be(&g2[i], p + G1_BYTES, 1)) return 0;
    }
    memset(out, 0, SCALAR_BYTES);
    out[SCALAR_BYTES - 1] = (uint8_t) pairing_is_one(g1.data(), g2.data(), k);
    return 1;
}

int eita_bls_map_fp_to_g1(const uint8_t *in, size_t len, uint8_t *out) {
    if (len != FP_BYTES) return 0;
    blst_fp u;
    if (!fp_from_be(&u, in)) return 0;
    blst_p1 g;
    blst_map_to_g1(&g, &u, NULL);   /* SSWU + isogeny + clear cofactor */
    g1_to_be(out, &g);
    return 1;
}

int eita_bls_map_fp2_to_g2(const uint8_t *in, size_t len, uint8_t *out) {
    if (len != 2 * FP_BYTES) return 0;
    blst_fp2 u;
    if (!fp_from_be(&u.fp[0], in)) return 0;
    if (!fp_from_be(&u.fp[1], in + FP_BYTES)) return 0;
    blst_p2 g;
    blst_map_to_g2(&g, &u, NULL);
    g2_to_be(out, &g);
    return 1;
}

#ifndef EITA_NO_LEAN_WRAPPER
/* Lean-object wrappers: empty ByteArray signals failure, matching bn254.cpp. */
#define EITA_BLS_LEAN_WRAP(NAME, FN, OUTLEN)                                   \
    LEAN_EXPORT lean_obj_res NAME(b_lean_obj_arg input) {                      \
        uint8_t buf[OUTLEN];                                                   \
        if (!FN(lean_sarray_cptr(input), lean_sarray_size(input), buf))         \
            return lean_alloc_sarray(1, 0, 0);                                 \
        lean_obj_res o = lean_alloc_sarray(1, OUTLEN, OUTLEN);                  \
        memcpy(lean_sarray_cptr(o), buf, OUTLEN);                              \
        return o;                                                              \
    }
EITA_BLS_LEAN_WRAP(lean_bls_g1add,         eita_bls_g1add,         128)
EITA_BLS_LEAN_WRAP(lean_bls_g1msm,         eita_bls_g1msm,         128)
EITA_BLS_LEAN_WRAP(lean_bls_g2add,         eita_bls_g2add,         256)
EITA_BLS_LEAN_WRAP(lean_bls_g2msm,         eita_bls_g2msm,         256)
EITA_BLS_LEAN_WRAP(lean_bls_pairing,       eita_bls_pairing,        32)
EITA_BLS_LEAN_WRAP(lean_bls_map_fp_to_g1,  eita_bls_map_fp_to_g1,  128)
EITA_BLS_LEAN_WRAP(lean_bls_map_fp2_to_g2, eita_bls_map_fp2_to_g2, 256)
#undef EITA_BLS_LEAN_WRAP

/* The oracle of Evm.Crypto.Bls12381 (`native`): the group operations alone, over
 * EIP-2537 encodings the Lean wrapper has already validated (range, curve, subgroup).
 * Each is total: an argument that does not parse (never passed) is treated as the
 * point at infinity. */
static lean_obj_res bytes_out(const uint8_t *buf, size_t n) {
    lean_obj_res o = lean_alloc_sarray(1, n, n);
    memcpy(lean_sarray_cptr(o), buf, n);
    return o;
}
static void g1_arg(blst_p1_affine *a, b_lean_obj_arg x) {
    if (lean_sarray_size(x) != G1_BYTES || !g1_from_be(a, lean_sarray_cptr(x), 0))
        memset(a, 0, sizeof *a);
}
static void g2_arg(blst_p2_affine *a, b_lean_obj_arg x) {
    if (lean_sarray_size(x) != G2_BYTES || !g2_from_be(a, lean_sarray_cptr(x), 0))
        memset(a, 0, sizeof *a);
}
static void scalar_arg(uint8_t s[SCALAR_BYTES], b_lean_obj_arg x) {
    memset(s, 0, SCALAR_BYTES);
    if (lean_sarray_size(x) == SCALAR_BYTES) memcpy(s, lean_sarray_cptr(x), SCALAR_BYTES);
}

LEAN_EXPORT lean_obj_res lean_bls_oracle_g1_add(b_lean_obj_arg a, b_lean_obj_arg b) {
    blst_p1_affine x, y;
    g1_arg(&x, a); g1_arg(&y, b);
    blst_p1 px, py, r;
    blst_p1_from_affine(&px, &x);
    blst_p1_from_affine(&py, &y);
    blst_p1_add_or_double(&r, &px, &py);                 /* as eita_bls_g1add */
    uint8_t out[G1_BYTES];
    g1_to_be(out, &r);
    return bytes_out(out, G1_BYTES);
}
LEAN_EXPORT lean_obj_res lean_bls_oracle_g1_mul(b_lean_obj_arg a, b_lean_obj_arg s) {
    blst_p1_affine x;
    uint8_t sc[SCALAR_BYTES];
    g1_arg(&x, a); scalar_arg(sc, s);
    blst_p1 r;
    g1_mul(&r, &x, sc);                                  /* as eita_bls_g1msm */
    uint8_t out[G1_BYTES];
    g1_to_be(out, &r);
    return bytes_out(out, G1_BYTES);
}
LEAN_EXPORT uint8_t lean_bls_oracle_g1_in_g1(b_lean_obj_arg a) {
    blst_p1_affine x;
    g1_arg(&x, a);
    return blst_p1_affine_in_g1(&x) ? 1 : 0;              /* as g1_from_be's order check */
}
LEAN_EXPORT lean_obj_res lean_bls_oracle_g2_add(b_lean_obj_arg a, b_lean_obj_arg b) {
    blst_p2_affine x, y;
    g2_arg(&x, a); g2_arg(&y, b);
    blst_p2 px, py, r;
    blst_p2_from_affine(&px, &x);
    blst_p2_from_affine(&py, &y);
    blst_p2_add_or_double(&r, &px, &py);
    uint8_t out[G2_BYTES];
    g2_to_be(out, &r);
    return bytes_out(out, G2_BYTES);
}
LEAN_EXPORT lean_obj_res lean_bls_oracle_g2_mul(b_lean_obj_arg a, b_lean_obj_arg s) {
    blst_p2_affine x;
    uint8_t sc[SCALAR_BYTES];
    g2_arg(&x, a); scalar_arg(sc, s);
    blst_p2 r;
    g2_mul(&r, &x, sc);
    uint8_t out[G2_BYTES];
    g2_to_be(out, &r);
    return bytes_out(out, G2_BYTES);
}
LEAN_EXPORT uint8_t lean_bls_oracle_g2_in_g2(b_lean_obj_arg a) {
    blst_p2_affine x;
    g2_arg(&x, a);
    return blst_p2_affine_in_g2(&x) ? 1 : 0;
}
LEAN_EXPORT lean_obj_res lean_bls_oracle_map_fp_to_g1(b_lean_obj_arg u) {
    uint8_t out[G1_BYTES];
    if (!eita_bls_map_fp_to_g1(lean_sarray_cptr(u), lean_sarray_size(u), out))
        memset(out, 0, G1_BYTES);
    return bytes_out(out, G1_BYTES);
}
LEAN_EXPORT lean_obj_res lean_bls_oracle_map_fp2_to_g2(b_lean_obj_arg u) {
    uint8_t out[G2_BYTES];
    if (!eita_bls_map_fp2_to_g2(lean_sarray_cptr(u), lean_sarray_size(u), out))
        memset(out, 0, G2_BYTES);
    return bytes_out(out, G2_BYTES);
}
LEAN_EXPORT uint8_t lean_bls_oracle_pairing_check(b_lean_obj_arg pairs) {
    size_t len = lean_sarray_size(pairs);
    if (len % PAIRING_PAIR != 0) return 0;
    size_t k = len / PAIRING_PAIR;
    const uint8_t *in = lean_sarray_cptr(pairs);
    HeapArr<blst_p1_affine> g1(k);
    HeapArr<blst_p2_affine> g2(k);
    for (size_t i = 0; i < k; i++) {
        if (!g1_from_be(&g1[i], in + i * PAIRING_PAIR, 0)) memset(&g1[i], 0, sizeof g1[i]);
        if (!g2_from_be(&g2[i], in + i * PAIRING_PAIR + G1_BYTES, 0)) memset(&g2[i], 0, sizeof g2[i]);
    }
    return (uint8_t) pairing_is_one(g1.data(), g2.data(), k);   /* as eita_bls_pairing */
}
#endif

} /* extern "C" */
