/*
 * p256verify.c — RIP-7212 secp256r1 (NIST P-256) signature verify.
 *
 * Links against OpenSSL libcrypto. Uses the deprecated low-level EC
 * API (EC_KEY / ECDSA_do_verify) because EVP_PKEY for raw ECDSA
 * verification requires juggling parameter sets that the low-level
 * API exposes directly. We pin the OpenSSL deprecation off via
 * OPENSSL_API_COMPAT so future libcrypto bumps keep building.
 *
 * Input layout (160 bytes, RIP-7212):
 *   bytes   0..32  : message hash (the keccak-256 of the message,
 *                    interpreted as a 32-byte BE integer)
 *   bytes  32..64  : r (32-byte BE)
 *   bytes  64..96  : s (32-byte BE)
 *   bytes  96..128 : qx (public key x, 32-byte BE)
 *   bytes 128..160 : qy (public key y, 32-byte BE)
 *
 * Returns: 1 (valid) or 0 (invalid / malformed / verify failed).
 *
 * Lean side packages the 5 × U256 into the 160-byte buffer; this
 * routine is purely "does (r,s) verify under (qx,qy) for msgHash".
 */

#define OPENSSL_API_COMPAT 0x10100000L
#include <stdint.h>
#include <string.h>
#include <stddef.h>
#include <openssl/bn.h>
#include <openssl/ec.h>
#include <openssl/ecdsa.h>
#include <openssl/obj_mac.h>
#ifndef EITA_NO_LEAN_WRAPPER
#include <lean/lean.h>
#endif

/* Cache the EC_GROUP for NIST P-256. Constructed lazily on first
 * call; freed never (process-lifetime). */
static EC_GROUP *get_p256_group(void) {
    static EC_GROUP *g = NULL;
    if (!g) {
        g = EC_GROUP_new_by_curve_name(NID_X9_62_prime256v1);
    }
    return g;
}

/* Plain-C entry (libeita / the CL replay): SRC is the 160-byte EIP-7951 input
 * `msgHash || r || s || qx || qy`; returns 1 iff the signature verifies. The
 * range checks EELS spells out (0 < r,s < n; qx,qy < p; (qx,qy) ≠ (0,0); on curve)
 * are enforced by OpenSSL: set_affine_coordinates / is_on_curve reject bad
 * points, ECDSA_do_verify rejects r,s outside [1, n-1]. */
int eita_p256_verify_raw(const uint8_t *src) {

    EC_GROUP *group = get_p256_group();
    if (!group) return 0;

    /* Parse r, s, qx, qy as 32-byte big-endian unsigned ints. */
    BIGNUM *r  = BN_bin2bn(src +  32, 32, NULL);
    BIGNUM *s  = BN_bin2bn(src +  64, 32, NULL);
    BIGNUM *qx = BN_bin2bn(src +  96, 32, NULL);
    BIGNUM *qy = BN_bin2bn(src + 128, 32, NULL);
    if (!r || !s || !qx || !qy) {
        BN_free(r); BN_free(s); BN_free(qx); BN_free(qy);
        return 0;
    }

    /* Build the EC_POINT for the public key (qx, qy). */
    EC_POINT *pub = EC_POINT_new(group);
    if (!pub) {
        BN_free(r); BN_free(s); BN_free(qx); BN_free(qy);
        return 0;
    }
    int ok_point = EC_POINT_set_affine_coordinates(group, pub, qx, qy, NULL);
    BN_free(qx); BN_free(qy);
    if (!ok_point) {
        EC_POINT_free(pub); BN_free(r); BN_free(s);
        return 0;
    }
    if (!EC_POINT_is_on_curve(group, pub, NULL)) {
        EC_POINT_free(pub); BN_free(r); BN_free(s);
        return 0;
    }

    /* Build the EC_KEY for verification. */
    EC_KEY *key = EC_KEY_new();
    if (!key) {
        EC_POINT_free(pub); BN_free(r); BN_free(s);
        return 0;
    }
    if (!EC_KEY_set_group(key, group)) {
        EC_KEY_free(key); EC_POINT_free(pub); BN_free(r); BN_free(s);
        return 0;
    }
    if (!EC_KEY_set_public_key(key, pub)) {
        EC_KEY_free(key); EC_POINT_free(pub); BN_free(r); BN_free(s);
        return 0;
    }
    EC_POINT_free(pub);

    /* Build the ECDSA_SIG. ECDSA_SIG_set0 takes ownership of r,s
     * — don't free them after this point. */
    ECDSA_SIG *sig = ECDSA_SIG_new();
    if (!sig) {
        EC_KEY_free(key); BN_free(r); BN_free(s);
        return 0;
    }
    if (!ECDSA_SIG_set0(sig, r, s)) {
        ECDSA_SIG_free(sig); EC_KEY_free(key); BN_free(r); BN_free(s);
        return 0;
    }
    /* r,s now owned by sig — don't double-free below. */

    /* Verify: 1 = valid, 0 = invalid, -1 = error. */
    int rv = ECDSA_do_verify(src, 32, sig, key);
    ECDSA_SIG_free(sig);
    EC_KEY_free(key);
    return (rv == 1) ? 1 : 0;
}

#ifndef EITA_NO_LEAN_WRAPPER
LEAN_EXPORT uint8_t lean_p256_verify(b_lean_obj_arg input) {
    if (lean_sarray_size(input) != 160) return 0;
    return (uint8_t) eita_p256_verify_raw(lean_sarray_cptr(input));
}
#endif
