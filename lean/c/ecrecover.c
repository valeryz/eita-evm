/*
 * ecrecover.c — ECDSA public-key recovery on secp256k1, EVM-style.
 *
 * Links against libsecp256k1 (Bitcoin Core's library). Combines that
 * with Keccak-256 (from keccak.c) to derive the 20-byte Ethereum
 * address of the signer.
 *
 * Input layout (128 bytes, EVM ABI):
 *   bytes  0..32  : message hash (32 bytes)
 *   bytes 32..64  : v as a 32-byte big-endian integer (must be 27 or 28)
 *   bytes 64..96  : r (32 bytes)
 *   bytes 96..128 : s (32 bytes)
 *
 * Output: 32 bytes, left-zero-padded 20-byte address. On any failure
 * (bad v, malformed signature, recovery failure) the result is an
 * empty ByteArray, which the caller interprets as "invalid signature"
 * per EELS.
 */

#include <stdint.h>
#include <string.h>
#include <stddef.h>
#include <secp256k1.h>
#include <secp256k1_recovery.h>
#ifndef EITA_NO_LEAN_WRAPPER
#include <lean/lean.h>
#endif

extern void keccak256(const uint8_t *in, size_t len, uint8_t out[32]);

static secp256k1_context *get_ctx(void) {
    static secp256k1_context *ctx = NULL;
    if (!ctx) {
        ctx = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
    }
    return ctx;
}

/* Plain-C entry point: input must be exactly 128 bytes (msg ‖ v ‖ r ‖ s).
   Writes 32 bytes to OUT (left-zero-padded address) and returns 1 on
   success, or 0 on any validation failure (caller treats 0 as "empty
   output" per EELS). */
int eita_ecrecover(const uint8_t *src, size_t len, uint8_t out[32]) {
    if (len != 128) return 0;

    /* v must be 27 or 28; rest of the 32-byte v slot must be zero. */
    for (size_t i = 32; i < 63; i++) {
        if (src[i] != 0) return 0;
    }
    uint8_t v = src[63];
    if (v != 27 && v != 28) return 0;
    int recid = v - 27;

    /* r ‖ s (compact 64-byte signature). */
    uint8_t sig_bytes[64];
    memcpy(sig_bytes, src + 64, 64);

    secp256k1_context *ctx = get_ctx();

    secp256k1_ecdsa_recoverable_signature rec_sig;
    if (!secp256k1_ecdsa_recoverable_signature_parse_compact(
            ctx, &rec_sig, sig_bytes, recid)) {
        return 0;
    }

    secp256k1_pubkey pubkey;
    if (!secp256k1_ecdsa_recover(ctx, &pubkey, &rec_sig, src)) {
        return 0;
    }

    /* Serialize uncompressed: 0x04 ‖ X ‖ Y, 65 bytes. */
    uint8_t pubkey_bytes[65];
    size_t pubkey_len = sizeof(pubkey_bytes);
    secp256k1_ec_pubkey_serialize(
        ctx, pubkey_bytes, &pubkey_len, &pubkey, SECP256K1_EC_UNCOMPRESSED);

    /* Address = keccak256(X ‖ Y)[12:32], left-zero-padded to 32 bytes. */
    uint8_t hash[32];
    keccak256(pubkey_bytes + 1, 64, hash);

    memset(out, 0, 12);
    memcpy(out + 12, hash + 12, 20);
    return 1;
}

#ifndef EITA_NO_LEAN_WRAPPER
LEAN_EXPORT lean_obj_res lean_ecrecover(b_lean_obj_arg input) {
    if (lean_sarray_size(input) != 128) {
        return lean_alloc_sarray(1, 0, 0);
    }
    const uint8_t *src = lean_sarray_cptr(input);
    uint8_t out_buf[32];
    if (!eita_ecrecover(src, 128, out_buf)) {
        return lean_alloc_sarray(1, 0, 0);
    }
    lean_obj_res out = lean_alloc_sarray(1, 32, 32);
    memcpy(lean_sarray_cptr(out), out_buf, 32);
    return out;
}
#endif
