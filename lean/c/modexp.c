/*
 * modexp.c — EIP-198 MODEXP precompile (0x05).
 *
 * Computes base^exp mod modulus using OpenSSL's BN_mod_exp for the
 * arbitrary-precision arithmetic. EIP-198 input layout (big-endian):
 *
 *   bytes  0.. 32 : base_size  (u256)
 *   bytes 32.. 64 : exp_size   (u256)
 *   bytes 64.. 96 : mod_size   (u256)
 *   bytes 96..96+base_size      : base
 *   then exp_size bytes         : exponent
 *   then mod_size bytes         : modulus
 *
 * Output: mod_size bytes of (base^exp) mod modulus, big-endian, left-zero
 * padded. If modulus == 0, output is mod_size zero bytes (matches EELS).
 *
 * Per EIP-2565, gas is `max(200, complexity * iterations / 3)`; that math
 * is done by the caller (run-precompile), not here.
 *
 * Two backends, by modulus size: GMP's mpz_powm up to 64 bytes, OpenSSL's
 * BN_mod_exp above. On x300 (Zen 3) mpz_powm is 2.0x faster at 32 bytes and
 * 1.1x at 64; BN_mod_exp is faster from 128 bytes (GMP 0.85x at 128, 0.73x at
 * 256 and 512). Mainnet 25,000,001..25,030,000: 877,642 of 877,694 calls are
 * 32/32/32 (base/exp/mod sizes). GMP is LGPL: linked dynamically (libgmp10).
 * c/test_modexp.c checks the two backends agree.
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <openssl/bn.h>
#include <gmp.h>
#ifndef EITA_NO_LEAN_WRAPPER
#include <lean/lean.h>
#endif

/* Read big-endian u256 from src. Returns UINT64_MAX if any high byte is
 * set (caller should treat as OOG-sized). */
static uint64_t be_u256_to_u64(const uint8_t *src) {
    for (size_t i = 0; i < 24; i++) {
        if (src[i] != 0) return UINT64_MAX;
    }
    uint64_t v = 0;
    for (size_t i = 24; i < 32; i++) v = (v << 8) | src[i];
    return v;
}

/* Copy `len` bytes starting at `off` in the input body into `dst`, padding
 * with zeros if the source range runs past `body_avail`. */
static void slice_padded(const uint8_t *body, size_t body_avail,
                          size_t off, size_t len, uint8_t *dst) {
    memset(dst, 0, len);
    if (off >= body_avail) return;
    size_t copy = body_avail - off < len ? body_avail - off : len;
    memcpy(dst, body + off, copy);
}

/* Returns 1 on success, 0 on malformed input. OUT must be at least
 * mod_size bytes. *OUT_LEN is written with mod_size on success. */
int eita_modexp(const uint8_t *src, size_t src_len,
                uint8_t *out, size_t *out_len) {
    uint8_t hdr[96] = {0};
    size_t hdr_copy = src_len < 96 ? src_len : 96;
    memcpy(hdr, src, hdr_copy);
    uint64_t base_sz = be_u256_to_u64(hdr);
    uint64_t exp_sz  = be_u256_to_u64(hdr + 32);
    uint64_t mod_sz  = be_u256_to_u64(hdr + 64);

    if (base_sz == 0 && mod_sz == 0) {
        *out_len = 0;
        return 1;
    }
    /* Defensive cap; caller's gas accounting should make oversized inputs
     * impossible to reach here. */
    if (base_sz > (1u << 20) || exp_sz > (1u << 20) || mod_sz > (1u << 20)) {
        return 0;
    }

    const uint8_t *body = src + 96;
    size_t body_avail = src_len > 96 ? src_len - 96 : 0;

    uint8_t *bbuf = (uint8_t *)malloc(base_sz ? base_sz : 1);
    uint8_t *ebuf = (uint8_t *)malloc(exp_sz  ? exp_sz  : 1);
    uint8_t *mbuf = (uint8_t *)malloc(mod_sz  ? mod_sz  : 1);
    if (!bbuf || !ebuf || !mbuf) { free(bbuf); free(ebuf); free(mbuf); return 0; }
    slice_padded(body, body_avail, 0,                 base_sz, bbuf);
    slice_padded(body, body_avail, base_sz,           exp_sz,  ebuf);
    slice_padded(body, body_avail, base_sz + exp_sz,  mod_sz,  mbuf);

    *out_len = mod_sz;
    memset(out, 0, mod_sz);

    if (mod_sz <= 64) {
        mpz_t b, e, m, r;
        mpz_inits(b, e, m, r, NULL);
        mpz_import(b, base_sz, 1, 1, 1, 0, bbuf);
        mpz_import(e, exp_sz, 1, 1, 1, 0, ebuf);
        mpz_import(m, mod_sz, 1, 1, 1, 0, mbuf);
        free(bbuf); free(ebuf); free(mbuf);
        if (mpz_sgn(m) != 0) {                  /* EELS: x mod 0 = 0 */
            mpz_powm(r, b, e, m);
            size_t rlen = (mpz_sizeinbase(r, 2) + 7) / 8;
            if (mpz_sgn(r) != 0 && rlen <= mod_sz) mpz_export(out + mod_sz - rlen, NULL, 1, 1, 1, 0, r);
        }
        mpz_clears(b, e, m, r, NULL);
        return 1;
    }

    BIGNUM *bn_base = BN_bin2bn(bbuf, base_sz, NULL);
    BIGNUM *bn_exp  = BN_bin2bn(ebuf, exp_sz,  NULL);
    BIGNUM *bn_mod  = BN_bin2bn(mbuf, mod_sz,  NULL);
    free(bbuf); free(ebuf); free(mbuf);
    BIGNUM *bn_res  = BN_new();
    BN_CTX *ctx     = BN_CTX_new();
    int ok = 0;
    if (bn_base && bn_exp && bn_mod && bn_res && ctx) {
        if (BN_is_zero(bn_mod)) {
            /* EELS: x mod 0 = 0. */
            ok = 1;
        } else {
            ok = BN_mod_exp(bn_res, bn_base, bn_exp, bn_mod, ctx);
            if (ok) {
                int rlen = BN_num_bytes(bn_res);
                if ((size_t)rlen <= mod_sz) {
                    BN_bn2bin(bn_res, out + mod_sz - rlen);
                }
            }
        }
    }
    BN_free(bn_base); BN_free(bn_exp); BN_free(bn_mod); BN_free(bn_res);
    BN_CTX_free(ctx);
    return ok;
}
