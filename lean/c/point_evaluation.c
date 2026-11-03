/*
 * point_evaluation.c — the EIP-4844 point-evaluation precompile (0x0a, Cancun+),
 * over vendor/blst (the same pinned library as the EIP-2537 precompiles).
 *
 * The spec is EELS, clause for clause:
 *   forks/cancun/vm/precompiled_contracts/point_evaluation.py (unchanged in
 *   prague and osaka; amsterdam renames `evm.message.data` to `evm.call_data`)
 *     44-45   len(data) != 192                          -> KZGProofError
 *     47-51   versioned_hash | z | y | commitment | proof  (32|32|32|48|48)
 *     54      charge PRECOMPILE_POINT_EVALUATION = 50000 (gas lives in
 *             Evm.CL.GasEmit.pointEvaluationGas, charged by the caller)
 *     55-56   kzg_commitment_to_versioned_hash(commitment) != versioned_hash
 *                                                       -> KZGProofError
 *     59-65   verify_kzg_proof raises or returns False  -> KZGProofError
 *     69-72   output = U256(4096).to_be_bytes32() ++ U256(BLS_MODULUS).to_be_bytes32()
 *   crypto/kzg.py
 *     65-74   versioned hash = 0x01 ++ sha256(commitment)[1:]
 *     77-85   validate_kzg_g1: the canonical infinity c0 00.. is accepted;
 *             anything else must be a valid compressed G1 point in the subgroup
 *             (py_ecc KeyValidate: decompress, not infinity, subgroup check)
 *     96-104  bytes_to_bls_field: big-endian, must be < BLS_MODULUS
 *     152-176 verify_kzg_proof_impl: e(C - [y]G1, -G2) * e(proof, [s]G2 - [z]G2) == 1
 *
 * Every failure is an exceptional halt in EELS (KZGProofError), so the caller
 * consumes the whole forwarded pool; there is no "success with empty output".
 *
 * The blst calls mirror c-kzg-4844 v2.1.1 verify_kzg_proof (src/eip4844/eip4844.c
 * verify_kzg_proof_impl, src/common/utils.c pairings_verify, src/common/ec.c
 * g1_mul/g1_sub, src/common/bytes.c validate_kzg_g1) — the library geth, reth and
 * the EELS test filler use — so the only trusted-setup point verification needs
 * is embedded below instead of vendoring c-kzg and its 4096-point setup loader.
 *
 * KZG_SETUP_G2_MONOMIAL_1 = [s]G2, the second G2 monomial point of the mainnet KZG
 * ceremony. Source: EELS crypto/kzg.py line 62 (KZG_SETUP_G2_MONOMIAL_1); equal to
 * line 4100 (g2_monomial[1]) of c-kzg-4844 v2.1.1 src/trusted_setup.txt
 * (sha256 d39b9f2d047cc9dca2de58f264b6a09448ccd34db967881a6713eacacf0f26b7).
 * Line 4099 of that file (g2_monomial[0]) is the standard generator blst_p2_generator().
 *
 * Tests: c/test_point_evaluation.c over the c-kzg-4844 verify_kzg_proof vectors
 * (lean/c/testdata/kzg-verify-proof-vectors.txt) — `make -C c test_point_evaluation`.
 */

#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include "blst.h"
#ifndef EITA_NO_LEAN_WRAPPER
#include <lean/lean.h>
#endif

void sha256_hash(const uint8_t *in, size_t n, uint8_t out[32]);   /* sha256.c */

static const uint8_t KZG_SETUP_G2_MONOMIAL_1[96] = {
    0xb5,0xbf,0xd7,0xdd,0x8c,0xde,0xb1,0x28,0x84,0x3b,0xc2,0x87,0x23,0x0a,0xf3,0x89,
    0x26,0x18,0x70,0x75,0xcb,0xfb,0xef,0xa8,0x10,0x09,0xa2,0xce,0x61,0x5a,0xc5,0x3d,
    0x29,0x14,0xe5,0x87,0x0c,0xb4,0x52,0xd2,0xaf,0xaa,0xab,0x24,0xf3,0x49,0x9f,0x72,
    0x18,0x5c,0xbf,0xee,0x53,0x49,0x27,0x14,0x73,0x44,0x29,0xb7,0xb3,0x86,0x08,0xe2,
    0x39,0x26,0xc9,0x11,0xcc,0xec,0xea,0xc9,0xa3,0x68,0x51,0x47,0x7b,0xa4,0xc6,0x0b,
    0x08,0x70,0x41,0xde,0x62,0x10,0x00,0xed,0xc9,0x8e,0xda,0xda,0x20,0xc1,0xde,0xf2,
};

/* EELS point_evaluation.py 27-28: FIELD_ELEMENTS_PER_BLOB, BLS_MODULUS (big-endian). */
static const uint8_t SUCCESS_OUTPUT[64] = {
    0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0x10,0x00,
    0x73,0xed,0xa7,0x53,0x29,0x9d,0x7d,0x48,0x33,0x39,0xd8,0x08,0x09,0xa1,0xd8,0x05,
    0x53,0xbd,0xa4,0x02,0xff,0xfe,0x5b,0xfe,0xff,0xff,0xff,0xff,0x00,0x00,0x00,0x01,
};

/* kzg.py 77-85 validate_kzg_g1 (+ pubkey_to_G1): 1 and OUT set, or 0. */
static int g1_from_bytes(blst_p1 *out, const uint8_t b[48]) {
    blst_p1_affine a;
    if (blst_p1_uncompress(&a, b) != BLST_SUCCESS) return 0;   /* only c0 00.. decodes to infinity */
    if (!blst_p1_affine_is_inf(&a) && !blst_p1_affine_in_g1(&a)) return 0;
    blst_p1_from_affine(out, &a);
    return 1;
}

/* kzg.py 96-104 bytes_to_bls_field: 1 and OUT set when b < BLS_MODULUS, else 0. */
static int fr_from_bytes(blst_scalar *out, const uint8_t b[32]) {
    blst_scalar_from_bendian(out, b);
    return blst_scalar_fr_check(out) ? 1 : 0;
}

/* kzg.py 127-176 verify_kzg_proof: 1 valid, 0 a well-formed proof that does not
   verify, -1 malformed input (EELS raises; the precompile treats both alike). */
int eita_kzg_verify_proof(const uint8_t commitment[48], const uint8_t z_bytes[32],
                          const uint8_t y_bytes[32], const uint8_t proof_bytes[48]) {
    blst_p1 c, proof, y_g1, p_minus_y;
    blst_p2 s_g2, z_g2, x_minus_z;
    blst_p2_affine s_aff;
    blst_scalar z, y;
    if (!g1_from_bytes(&c, commitment) || !fr_from_bytes(&z, z_bytes) ||
        !fr_from_bytes(&y, y_bytes) || !g1_from_bytes(&proof, proof_bytes))
        return -1;
    if (blst_p2_uncompress(&s_aff, KZG_SETUP_G2_MONOMIAL_1) != BLST_SUCCESS) return -1;
    blst_p2_from_affine(&s_g2, &s_aff);

    /* X - z = [s]G2 - [z]G2 ;  P - y = C - [y]G1   (255 = bits of a field element) */
    blst_p2_mult(&z_g2, blst_p2_generator(), z.b, 255);
    blst_p2_cneg(&z_g2, 1);
    blst_p2_add_or_double(&x_minus_z, &s_g2, &z_g2);
    blst_p1_mult(&y_g1, blst_p1_generator(), y.b, 255);
    blst_p1_cneg(&y_g1, 1);
    blst_p1_add_or_double(&p_minus_y, &c, &y_g1);

    /* e(P - y, -G2) * e(proof, X - z) == 1 */
    blst_p1_affine a1, b1;
    blst_p2_affine a2, b2;
    blst_fp12 l0, l1, gt;
    blst_p1_cneg(&p_minus_y, 1);
    blst_p1_to_affine(&a1, &p_minus_y);
    blst_p1_to_affine(&b1, &proof);
    blst_p2_to_affine(&a2, blst_p2_generator());
    blst_p2_to_affine(&b2, &x_minus_z);
    blst_miller_loop(&l0, &a2, &a1);
    blst_miller_loop(&l1, &b2, &b1);
    blst_fp12_mul(&gt, &l0, &l1);
    blst_final_exp(&gt, &gt);
    return blst_fp12_is_one(&gt) ? 1 : 0;
}

/* point_evaluation.py 32-72 minus the gas charge: 1 with OUT = 64 bytes on success,
   0 on any KZGProofError (wrong length, versioned-hash mismatch, bad proof). */
int eita_point_evaluation(const uint8_t *in, uint64_t inlen, uint8_t out[64]) {
    uint8_t h[32];
    if (inlen != 192) return 0;
    sha256_hash(in + 96, 48, h);
    h[0] = 0x01;                                    /* VERSIONED_HASH_VERSION_KZG */
    if (memcmp(h, in, 32) != 0) return 0;
    if (eita_kzg_verify_proof(in + 96, in + 32, in + 64, in + 144) != 1) return 0;
    memcpy(out, SUCCESS_OUTPUT, 64);
    return 1;
}

#ifndef EITA_NO_LEAN_WRAPPER
/* Lean: the 64-byte output on success, empty on failure (Evm.Crypto.Kzg). */
LEAN_EXPORT lean_obj_res lean_point_evaluation(b_lean_obj_arg input) {
    uint8_t buf[64];
    if (!eita_point_evaluation(lean_sarray_cptr(input), lean_sarray_size(input), buf))
        return lean_alloc_sarray(1, 0, 0);
    lean_obj_res o = lean_alloc_sarray(1, 64, 64);
    memcpy(lean_sarray_cptr(o), buf, 64);
    return o;
}
#endif
