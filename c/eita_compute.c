/*
 * eita_compute.c — pure-compute helpers for ARM64 opcodes whose body
 * would be too long to inline in handler assembly (256-bit MUL/DIV,
 * shifts, EXP, etc.).
 *
 * Each helper has a stable C ABI:
 *
 *   void eita_op(u256 *result, const u256 *a, [const u256 *b, ...]);
 *
 * The ARM64 handler loads operand pointers, BL's the helper, then
 * reads the result back into its TOS register set.
 *
 * Pure functions: no callbacks, no allocation, no side effects on the
 * EvmState. Just compute. Compile with -O2 (set in build script).
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "evm_state.h"

typedef u256_t u256;

/* ---- Utilities --------------------------------------------------------- */

static inline int u256_is_zero(const u256 *x) {
    return (x->limb[0] | x->limb[1] | x->limb[2] | x->limb[3]) == 0;
}

static inline void u256_zero(u256 *x) {
    x->limb[0] = x->limb[1] = x->limb[2] = x->limb[3] = 0;
}

static inline void u256_shl_inplace(u256 *x, int n) {
    /* In-place left shift; n in [0, 256). For n >= 256, caller must zero. */
    if (n == 0) return;
    int wshift = n / 64;
    int bshift = n % 64;
    if (wshift > 0) {
        for (int i = 3; i >= 0; i--) {
            x->limb[i] = (i - wshift >= 0) ? x->limb[i - wshift] : 0;
        }
    }
    if (bshift) {
        uint64_t carry = 0;
        for (int i = 0; i < 4; i++) {
            uint64_t next_carry = x->limb[i] >> (64 - bshift);
            x->limb[i] = (x->limb[i] << bshift) | carry;
            carry = next_carry;
        }
    }
}

static inline void u256_shr_inplace(u256 *x, int n) {
    if (n == 0) return;
    int wshift = n / 64;
    int bshift = n % 64;
    if (wshift > 0) {
        for (int i = 0; i < 4; i++) {
            x->limb[i] = (i + wshift < 4) ? x->limb[i + wshift] : 0;
        }
    }
    if (bshift) {
        uint64_t carry = 0;
        for (int i = 3; i >= 0; i--) {
            uint64_t next_carry = x->limb[i] << (64 - bshift);
            x->limb[i] = (x->limb[i] >> bshift) | carry;
            carry = next_carry;
        }
    }
}

/* ---- Shifts ------------------------------------------------------------ */

/* SHL: shift = top, val = nos. result = val << shift; for shift >= 256, 0. */
void eita_helper_shl(u256 *result, const u256 *shift, const u256 *val) {
    /* If shift has any bits beyond limb[0] or limb[0] >= 256, result = 0. */
    if (shift->limb[1] | shift->limb[2] | shift->limb[3] || shift->limb[0] >= 256) {
        u256_zero(result);
        return;
    }
    *result = *val;
    u256_shl_inplace(result, (int)shift->limb[0]);
}

/* SHR: result = val >> shift; for shift >= 256, 0. */
void eita_helper_shr(u256 *result, const u256 *shift, const u256 *val) {
    if (shift->limb[1] | shift->limb[2] | shift->limb[3] || shift->limb[0] >= 256) {
        u256_zero(result);
        return;
    }
    *result = *val;
    u256_shr_inplace(result, (int)shift->limb[0]);
}

/* SAR: arithmetic right shift. For shift >= 256: 0 if val positive,
 * all-ones if val negative. */
void eita_helper_sar(u256 *result, const u256 *shift, const u256 *val) {
    int is_neg = (val->limb[3] >> 63) & 1;
    if (shift->limb[1] | shift->limb[2] | shift->limb[3] || shift->limb[0] >= 256) {
        if (is_neg) {
            result->limb[0] = result->limb[1] = result->limb[2] = result->limb[3] = ~(uint64_t)0;
        } else {
            u256_zero(result);
        }
        return;
    }
    int n = (int)shift->limb[0];
    *result = *val;
    u256_shr_inplace(result, n);
    if (is_neg) {
        /* OR in the sign-extending high bits. */
        uint64_t mask_fill = ~(uint64_t)0;
        int rem = 256 - n;
        int top_word = rem / 64;
        int top_bit = rem % 64;
        for (int i = 3; i > top_word; i--) result->limb[i] = mask_fill;
        if (top_word >= 0 && top_word < 4) {
            /* Fill bits [top_bit..63] of top_word with the sign. At top_bit==0
             * this must fill the WHOLE word: ~((1<<0)-1) = ~0 = all-ones. The
             * old (top_bit==0)?0 special-case produced ~(0-1)=0 → no fill, so
             * SAR by a multiple of 64 (64/128/192) of a negative value left the
             * top fill-word zeroed. (Latent: SAR is Constantinople+, 0x1d.) */
            uint64_t mask = (uint64_t)1 << top_bit;
            result->limb[top_word] |= ~(mask - 1);
        }
    }
}

/* ---- BYTE -------------------------------------------------------------- */

/* BYTE: extract i-th byte (counting from high end). i >= 32 → 0. */
void eita_helper_byte(u256 *result, const u256 *i, const u256 *x) {
    if (i->limb[1] | i->limb[2] | i->limb[3] || i->limb[0] >= 32) {
        u256_zero(result);
        return;
    }
    int idx = (int)i->limb[0];
    int shift = (31 - idx) * 8;
    int word = shift / 64;
    int word_shift = shift % 64;
    uint64_t b = (x->limb[word] >> word_shift) & 0xff;
    u256_zero(result);
    result->limb[0] = b;
}

/* ---- SIGNEXTEND -------------------------------------------------------- */

/* SIGNEXTEND b x: extend bit (8*b+7) through high bits; b >= 31 → x. */
void eita_helper_signextend(u256 *result, const u256 *b, const u256 *x) {
    if (b->limb[1] | b->limb[2] | b->limb[3] || b->limb[0] >= 31) {
        *result = *x;
        return;
    }
    int bn = (int)b->limb[0];
    int bit_idx = 8 * bn + 7;
    int word = bit_idx / 64;
    int bit_in_word = bit_idx % 64;
    /* Sign bit value */
    int sign = (x->limb[word] >> bit_in_word) & 1;
    /* Mask covering bits [0..bit_idx]; OR with all-ones above if sign=1 */
    *result = *x;
    /* Clear high bits above bit_idx. */
    if (bit_in_word == 63) {
        for (int i = word + 1; i < 4; i++) result->limb[i] = 0;
    } else {
        uint64_t mask = ((uint64_t)1 << (bit_in_word + 1)) - 1;
        result->limb[word] &= mask;
        for (int i = word + 1; i < 4; i++) result->limb[i] = 0;
    }
    if (sign) {
        /* Fill bits above bit_idx with 1 */
        if (bit_in_word == 63) {
            for (int i = word + 1; i < 4; i++) result->limb[i] = ~(uint64_t)0;
        } else {
            uint64_t mask = ((uint64_t)1 << (bit_in_word + 1)) - 1;
            result->limb[word] |= ~mask;
            for (int i = word + 1; i < 4; i++) result->limb[i] = ~(uint64_t)0;
        }
    }
}

/* ---- MUL --------------------------------------------------------------- */

/* MUL: result = a * b mod 2^256. Long-multiplication with proper carry. */
void eita_helper_mul(u256 *result, const u256 *a, const u256 *b) {
    uint64_t r[4] = {0, 0, 0, 0};
    for (int i = 0; i < 4; i++) {
        if (a->limb[i] == 0) continue;
        uint64_t carry = 0;
        for (int j = 0; i + j < 4; j++) {
            __uint128_t t = (__uint128_t)a->limb[i] * b->limb[j]
                          + r[i + j] + carry;
            r[i + j] = (uint64_t)t;
            carry = (uint64_t)(t >> 64);
        }
    }
    result->limb[0] = r[0];
    result->limb[1] = r[1];
    result->limb[2] = r[2];
    result->limb[3] = r[3];
}

/* ---- Word-wise division (Knuth TAOCP vol. 2, 4.3.1, Algorithm D) -------
 * The one reduction behind DIV, MOD, SDIV, SMOD, ADDMOD and MULMOD: an m-limb dividend
 * (4; 5 for ADDMOD's 257-bit sum; 8 for MULMOD's 512-bit product) by a 4-limb divisor,
 * one 64-bit limb of quotient per step instead of one bit. Limbs little-endian; every
 * index below is bounded by m <= 8 and n <= 4 (un has m+1 <= 9 limbs). */

#define UDIV_MAX_LIMBS 8

/* 2-by-1 limb division by a normalized d (top bit set) with the reciprocal
 * floor((2^128 - 1) / d) - 2^64, the one 128-bit division per udivrem call (Möller &
 * Granlund, IEEE TC 2011, Algorithm 4): two multiplications and two rare corrections. */
static inline uint64_t reciprocal_2by1(uint64_t d) {
    return (uint64_t)(((((__uint128_t)~d) << 64) | ~(uint64_t)0) / d);
}

/* (u1:u0) / d for u1 < d (quotient fits one limb); *rem = the remainder. */
static inline uint64_t div_2by1(uint64_t u1, uint64_t u0, uint64_t d, uint64_t v,
                                uint64_t *rem) {
    __uint128_t q = (__uint128_t)v * u1 + ((((__uint128_t)u1) << 64) | u0);
    uint64_t q1 = (uint64_t)(q >> 64) + 1, q0 = (uint64_t)q;
    uint64_t r = u0 - q1 * d;
    if (r > q0) { q1--; r += d; }
    if (r >= d) { q1++; r -= d; }
    *rem = r;
    return q1;
}

/* r[0..3] = u mod v and, if q, q[0..3] = u / v (q only for m <= 4: DIV); v = 0 gives
 * 0 for both (the EVM rule). 1 <= m <= UDIV_MAX_LIMBS. Works on local copies and
 * writes q and r last, so they may alias u or v. */
static void udivrem(uint64_t q[4], uint64_t r[4], const uint64_t *u, int m,
                    const uint64_t v[4]) {
    uint64_t qt[UDIV_MAX_LIMBS] = {0}, rt[4] = {0};
    int n = 4;
    while (n > 0 && v[n - 1] == 0) n--;
    if (n == 0) goto out;
    while (m > 0 && u[m - 1] == 0) m--;
    int lt = m < n;                                  /* u < v: quotient 0, remainder u */
    for (int i = m - 1; !lt && m == n && i >= 0; i--) {
        if (u[i] != v[i]) { lt = u[i] < v[i]; break; }
    }
    if (lt) {
        for (int i = 0; i < 4; i++) rt[i] = i < m ? u[i] : 0;
        goto out;
    }
    /* D1: normalize so the divisor's top bit is set. s in [0,63]; the s == 0
     * case must not shift by 64 (undefined), hence the masked carry-ins. */
    int s = __builtin_clzll(v[n - 1]);
    uint64_t mask = s ? ~(uint64_t)0 : 0;            /* zero the carry-in when s == 0 */
    int rs = (64 - s) & 63;
    uint64_t vn[4], un[UDIV_MAX_LIMBS + 1];
    for (int i = n - 1; i > 0; i--) vn[i] = (v[i] << s) | ((v[i - 1] >> rs) & mask);
    vn[0] = v[0] << s;
    un[m] = (u[m - 1] >> rs) & mask;
    for (int i = m - 1; i > 0; i--) un[i] = (u[i] << s) | ((u[i - 1] >> rs) & mask);
    un[0] = u[0] << s;
    if (n == 1) {                                    /* short division: one 2-by-1 per limb */
        uint64_t rem = un[m];                        /* < vn[0]: the bits shifted out */
        uint64_t inv = reciprocal_2by1(vn[0]);
        for (int i = m - 1; i >= 0; i--) qt[i] = div_2by1(rem, un[i], vn[0], inv, &rem);
        rt[0] = rem >> s;
        goto out;
    }
    uint64_t vtop = vn[n - 1], vnext = vn[n - 2], inv = reciprocal_2by1(vtop);
    for (int j = m - n; j >= 0; j--) {
        /* D3: estimate qhat = (un[j+n]:un[j+n-1]) / vtop; un[j+n] <= vtop. */
        uint64_t qhat, rhat;
        int rhat_big = 0;                            /* rhat >= 2^64: test below is moot */
        if (un[j + n] >= vtop) {                     /* == vtop: estimate is base-1 */
            qhat = ~(uint64_t)0;
            uint64_t t = un[j + n - 1] + vtop;       /* rhat = un[j+n-1] + vtop */
            rhat_big = t < vtop;
            rhat = t;
        } else {
            qhat = div_2by1(un[j + n], un[j + n - 1], vtop, inv, &rhat);
        }
        while (!rhat_big &&
               (__uint128_t)qhat * vnext > (((__uint128_t)rhat << 64) | un[j + n - 2])) {
            qhat--;
            uint64_t t = rhat + vtop;
            rhat_big = t < rhat;
            rhat = t;
        }
        /* D4: un[j..j+n] -= qhat * vn. */
        uint64_t borrow = 0, carry = 0;
        for (int i = 0; i < n; i++) {
            __uint128_t p = (__uint128_t)qhat * vn[i] + carry;
            carry = (uint64_t)(p >> 64);
            uint64_t plo = (uint64_t)p, x = un[i + j];
            uint64_t t = x - plo;
            uint64_t b1 = x < plo;
            un[i + j] = t - borrow;
            borrow = b1 | (t < borrow);
        }
        uint64_t x = un[j + n];
        uint64_t t = x - carry;
        uint64_t b1 = x < carry;
        un[j + n] = t - borrow;
        borrow = b1 | (t < borrow);
        /* D5/D6: qhat was one too large (rare): add vn back. */
        if (borrow) {
            qhat--;
            uint64_t c = 0;
            for (int i = 0; i < n; i++) {
                __uint128_t sum = (__uint128_t)un[i + j] + vn[i] + c;
                un[i + j] = (uint64_t)sum;
                c = (uint64_t)(sum >> 64);
            }
            un[j + n] += c;                          /* the carry out is discarded */
        }
        qt[j] = qhat;
    }
    /* D8: denormalize the remainder (n limbs, < v). */
    for (int i = 0; i < n; i++) rt[i] = (un[i] >> s) | ((un[i + 1] << rs) & mask);
out:
    if (q) for (int i = 0; i < 4; i++) q[i] = qt[i];
    for (int i = 0; i < 4; i++) r[i] = rt[i];
}

/* ---- DIV / MOD / SDIV / SMOD (zero divisor: 0) ------------------------- */

void eita_helper_div(u256 *result, const u256 *a, const u256 *b) {
    uint64_t r[4];
    udivrem(result->limb, r, a->limb, 4, b->limb);
}

void eita_helper_mod(u256 *result, const u256 *a, const u256 *b) {
    udivrem(NULL, result->limb, a->limb, 4, b->limb);
}

/* SDIV / SMOD: DIV / MOD of the magnitudes (two's complement), so b = 0 gives 0.
 * SDIV truncates toward 0; MIN / -1 = MIN (|MIN| = 2^255, negated back to MIN).
 * SMOD takes the dividend's sign. */
static void u256_negate(u256 *x) {                   /* ~x + 1 */
    uint64_t c = 1;
    for (int i = 0; i < 4; i++) { uint64_t t = ~x->limb[i] + c; c = c && t == 0; x->limb[i] = t; }
}

static int u256_abs(u256 *out, const u256 *x) {      /* returns the sign bit */
    int neg = (int)(x->limb[3] >> 63);
    *out = *x;
    if (neg) u256_negate(out);
    return neg;
}

void eita_helper_sdiv(u256 *result, const u256 *a, const u256 *b) {
    u256 aa, bb;
    int neg = u256_abs(&aa, a) ^ u256_abs(&bb, b);
    eita_helper_div(result, &aa, &bb);
    if (neg) u256_negate(result);
}

void eita_helper_smod(u256 *result, const u256 *a, const u256 *b) {
    u256 aa, bb;
    int neg = u256_abs(&aa, a);
    u256_abs(&bb, b);
    eita_helper_mod(result, &aa, &bb);
    if (neg) u256_negate(result);
}

/* ---- ADDMOD / MULMOD (n = 0: 0) -------------------------------------- */

/* ADDMOD: (a + b) mod n over the full 257-bit sum (no 2^256 wrap). */
void eita_helper_addmod(u256 *result, const u256 *a, const u256 *b, const u256 *n) {
    uint64_t s[5];
    uint64_t carry = 0;
    for (int i = 0; i < 4; i++) {
        __uint128_t t = (__uint128_t)a->limb[i] + b->limb[i] + carry;
        s[i] = (uint64_t)t;
        carry = (uint64_t)(t >> 64);
    }
    s[4] = carry;
    udivrem(NULL, result->limb, s, 5, n->limb);
}

/* MULMOD: (a * b) mod n over the full 512-bit product. */
void eita_helper_mulmod(u256 *result, const u256 *a, const u256 *b, const u256 *n) {
    uint64_t prod[8] = {0};
    for (int i = 0; i < 4; i++) {
        uint64_t carry = 0;
        for (int j = 0; j < 4; j++) {
            __uint128_t t = (__uint128_t)a->limb[i] * b->limb[j]
                          + prod[i + j] + carry;
            prod[i + j] = (uint64_t)t;
            carry = (uint64_t)(t >> 64);
        }
        prod[i + 4] = carry;
    }
    udivrem(NULL, result->limb, prod, 8, n->limb);
}

/* ---- Buffer copies / CALLDATALOAD ------------------------------------- */

/* CALLDATALOAD: read 32 bytes BE from calldata[off..off+32], zero-pad. */
void eita_helper_calldataload(u256 *result, EvmState *state, const u256 *off) {
    const uint8_t *cd = state->calldata;
    uint64_t size = state->calldata_size;
    /* CALLDATALOAD offset is a full u256. If any HIGH limb is set the true
     * offset is >= 2^64 > calldata_size, so the whole 32-byte window lies
     * past the end and reads as zero. Using only limb[0] would wrap a huge
     * offset (e.g. old-Solidity ABI junk pointer ~2^208) down to a small
     * in-bounds index and return real calldata as garbage — mainnet block
     * 549413 tx2 (Gav-Wood Wallet) decoded a bogus bytes length that way and
     * OOG'd on a phantom CALLDATACOPY. (Cf. codecopy-u256-src-overflow.) */
    if (off->limb[1] != 0 || off->limb[2] != 0 || off->limb[3] != 0) {
        result->limb[0] = result->limb[1] = result->limb[2] = result->limb[3] = 0;
        return;
    }
    uint64_t offN = off->limb[0];
    uint8_t buf[32];
    /* In bounds iff offN + i < size, compared without forming offN + i: near 2^64 that sum
     * wraps to a small index (CALLDATALOAD(2^64-1) read calldata[0..30] into bytes 1..31). */
    for (int i = 0; i < 32; i++)
        buf[i] = (offN < size && (uint64_t)i < size - offN) ? cd[offN + i] : 0;
    /* BE bytes → LE limbs. */
    for (int limb = 0; limb < 4; limb++) {
        uint64_t v = 0;
        for (int byte = 0; byte < 8; byte++) {
            v = (v << 8) | buf[(3 - limb) * 8 + byte];
        }
        result->limb[limb] = v;
    }
}

/* Generic copy: copy from source buffer to memory[dst..dst+len], zero-pad past source end. */
static void copy_into_memory(EvmState *state, uint64_t dst, uint64_t src,
                              uint64_t len, const uint8_t *source, uint64_t source_size,
                              int src_overflow) {
    uint8_t *mem = state->memory;
    /* A zero-length copy touches no memory and must NOT expand it (EELS:
     * memory expansion is over [dst, dst+len), empty when len==0). Skipping
     * the update also avoids corrupting memory_size when len==0 but dst is a
     * huge u256 whose low limb is large — the assembly fast-path skips its
     * cap check for len==0, so this guard is the only thing standing between
     * a junk `CODECOPY(huge_dst, *, 0)` and an out-of-bounds memory_size. */
    if (len == 0) return;
    /* Expand memory if needed via host-allocated buffer (caller pre-allocated). */
    uint64_t end = dst + len;
    if (state->memory_size < end) state->memory_size = end;
    if (state->mp < end) state->mp = end;
    /* If the u256 source offset exceeds 2^64 (i.e. any high limb set), the
     * entire source range is past source_size — produce zeros. Otherwise the
     * low limb is the byte offset. */
    if (src_overflow) {
        for (uint64_t i = 0; i < len; i++) mem[dst + i] = 0;
        return;
    }
    /* In bounds iff src + i < source_size, compared without forming src + i: near 2^64 that
     * sum wraps to a small index — CALLDATACOPY / CODECOPY from 2^64-1 copied the buffer's
     * first bytes where EELS buffer_read gives zeros (ethereum/tests stMemoryTest
     * bufferSrcOffset d22 / d46: the copied word is stored, so the gas and state differ). */
    for (uint64_t i = 0; i < len; i++) {
        uint8_t b = (src < source_size && i < source_size - src) ? source[src + i] : 0;
        mem[dst + i] = b;
    }
}

/* CALLDATACOPY: copy calldata[src..src+len] to memory[dst..dst+len]. */
void eita_helper_calldatacopy(EvmState *state, const u256 *dst,
                               const u256 *src, const u256 *len) {
    int src_overflow = (src->limb[1] | src->limb[2] | src->limb[3]) != 0;
    copy_into_memory(state, dst->limb[0], src->limb[0], len->limb[0],
                     state->calldata, state->calldata_size, src_overflow);
}

/* CODECOPY: copy code[src..src+len] to memory[dst..dst+len]. */
void eita_helper_codecopy(EvmState *state, const u256 *dst,
                           const u256 *src, const u256 *len) {
    int src_overflow = (src->limb[1] | src->limb[2] | src->limb[3]) != 0;
    copy_into_memory(state, dst->limb[0], src->limb[0], len->limb[0],
                     state->code, state->code_size, src_overflow);
}

/* RETURNDATACOPY: like CALLDATACOPY but errors if src + len > returndata_size.
 * For now, we just zero-pad past end (host validates bounds at the spec layer).
 * Audit fixtures stage len so this is always in-bounds. */
void eita_helper_returndatacopy(EvmState *state, const u256 *dst,
                                 const u256 *src, const u256 *len) {
    int src_overflow = (src->limb[1] | src->limb[2] | src->limb[3]) != 0;
    copy_into_memory(state, dst->limb[0], src->limb[0], len->limb[0],
                     state->returndata, state->returndata_size, src_overflow);
}

/* After CALL/STATICCALL/etc returns, copy returndata to caller's
 * memory[out_off..out_off+min(out_len, returndata_size)] per spec.
 * Memory beyond returndata_size stays untouched. Called by the CALL-family
 * handlers between the cb_call invocation and pushing the success flag. */
void eita_helper_returndata_to_mem(EvmState *state, uint64_t out_off,
                                    uint64_t out_len) {
    uint64_t copy_len = out_len < state->returndata_size
                            ? out_len
                            : state->returndata_size;
    if (copy_len == 0) return;
    /* Ensure memory is large enough; the caller already paid memexp gas. */
    uint64_t need = out_off + copy_len;
    if (need > state->memory_size) {
        return;  /* Should never happen if memexp gas was charged. */
    }
    for (uint64_t i = 0; i < copy_len; i++) {
        state->memory[out_off + i] = state->returndata[i];
    }
}

/* KECCAK256: hash memory[off..off+len], place 32-byte BE digest in result. */
extern void eita_keccak256(const uint8_t *input, size_t inlen, uint8_t output[32]);

/* A 64-byte KECCAK256 is nearly always a Solidity mapping slot, keccak(key ‖ slot), and the
 * same one recurs: on mainnet (blocks 25.0M+) 89 % of KECCAK256 inputs are 64 bytes and a
 * 256-entry direct-mapped memo answers 47 % of them. A memo entry holds the whole input and
 * its digest, so a hit is the hash of exactly these bytes: a pure function memoised, no
 * invalidation. Per thread (whichever thread runs the interpreter). */
#define KMEMO_BITS 8
typedef struct { uint8_t in[64]; uint8_t out[32]; uint8_t full; } KMemo;
static _Thread_local KMemo kmemo[1 << KMEMO_BITS];
static void keccak64_memo(const uint8_t *in, uint8_t out[32]) {
    uint64_t h = 0;
    for (int i = 0; i < 64; i += 8) { uint64_t w; memcpy(&w, in + i, 8); h = (h ^ w) * 0x9E3779B97F4A7C15ull; }
    KMemo *e = &kmemo[(h >> 32) & ((1u << KMEMO_BITS) - 1)];
    if (e->full && memcmp(e->in, in, 64) == 0) { memcpy(out, e->out, 32); return; }
    eita_keccak256(in, 64, out);
    memcpy(e->in, in, 64); memcpy(e->out, out, 32); e->full = 1;
}

void eita_helper_keccak256(EvmState *state, const u256 *off,
                            const u256 *len, u256 *result) {
    uint64_t offN = off->limb[0];
    uint64_t lenN = len->limb[0];
    /* A zero-length KECCAK256 hashes the empty string and touches no memory;
     * it must NOT expand memory. The assembly fast-path skips its cap check
     * when len==0, so guarding here prevents memory_size/mp from being set to
     * a huge `off` low-limb (e.g. KECCAK256(huge_off, 0)). */
    if (lenN > 0) {
        uint64_t end = offN + lenN;
        if (state->memory_size < end) state->memory_size = end;
        if (state->mp < end) state->mp = end;
    }
    uint8_t digest[32];
    if (lenN == 64) keccak64_memo(state->memory + offN, digest);
    else eita_keccak256(state->memory + offN, (size_t)lenN, digest);
    /* digest is BE 32 bytes → LE u256 limbs */
    for (int limb = 0; limb < 4; limb++) {
        uint64_t v = 0;
        for (int b = 0; b < 8; b++) {
            v = (v << 8) | digest[(3 - limb) * 8 + b];
        }
        result->limb[limb] = v;
    }
}

/* MCOPY: memory-to-memory copy. Use temp buffer for overlap safety. */
void eita_helper_mcopy(EvmState *state, const u256 *dst,
                       const u256 *src, const u256 *len) {
    uint64_t d = dst->limb[0], s = src->limb[0], l = len->limb[0];
    uint8_t *mem = state->memory;
    /* A zero-length MCOPY touches no memory and must NOT expand it. The
     * assembly fast-path skips its cap check when len==0, so guarding here
     * prevents memory_size/mp from being set to a huge dst/src low-limb. */
    if (l == 0) return;
    uint64_t end = (d > s ? d : s) + l;
    if (state->memory_size < end) state->memory_size = end;
    if (state->mp < end) state->mp = end;
    /* Use temporary buffer for overlap safety (up to 1024 bytes inline). */
    if (l <= 4096) {
        uint8_t tmp[4096];
        for (uint64_t i = 0; i < l; i++) tmp[i] = mem[s + i];
        for (uint64_t i = 0; i < l; i++) mem[d + i] = tmp[i];
    } else {
        /* Slow path: forward or backward depending on overlap direction. */
        if (d < s) {
            for (uint64_t i = 0; i < l; i++) mem[d + i] = mem[s + i];
        } else {
            for (uint64_t i = l; i > 0; i--) mem[d + i - 1] = mem[s + i - 1];
        }
    }
}

/* ---- Valid-JUMPDEST map --------------------------------------------------
 *
 * out[pc] = 1 iff code[pc] is the JUMPDEST opcode (0x5b) and pc is not inside a
 * PUSH1..PUSH32 immediate; every other byte 0. EELS `get_valid_jump_destinations`
 * (vm/runtime.py: skip `push_data_size = op - PUSH1 + 1` bytes after a PUSH), the
 * Lean spec's `Runtime.jumpDestBitmap`. The host builds it once per frame next to
 * the frame's code copy and points EvmState.jumpdests (#136) at it; the JUMP/JUMPI
 * handlers test the map byte after their bounds check. `out` has `len` bytes. */
void eita_jumpdest_map(const uint8_t *code, uint64_t len, uint8_t *out) {
    memset(out, 0, (size_t)len);
    for (uint64_t pc = 0; pc < len; ) {
        uint8_t op = code[pc];
        if (op == 0x5b) out[pc] = 1;
        pc += (op >= 0x60 && op <= 0x7f) ? (uint64_t)(op - 0x60) + 2 : 1;
    }
}

/* ---- High-level wrapper for the Lean replay harness -------------------
 *
 * eita_run_program: take bytecode + gas, allocate a fresh EvmState +
 * stack/memory/arena, dispatch through eita_run, write back the result.
 *
 * The caller owns the output buffer; we malloc up to `output_cap` bytes
 * and write the actual size to `*output_len`. On revert / OOG / halt,
 * we still write the state into the outparams.
 *
 * Returns 1 on RETURN, 0 on REVERT / abnormal halt. */

extern void eita_run(EvmState *state);

int eita_run_program(const uint8_t *code, uint64_t code_len,
                     uint64_t initial_gas,
                     uint8_t *output_buf, uint64_t output_cap,
                     uint64_t *output_len,
                     uint64_t *gas_left) {
    if (output_len) *output_len = 0;
    if (gas_left)   *gas_left   = 0;

    EvmState *state = (EvmState *)calloc(1, sizeof(EvmState));
    u256_t   *stack = (u256_t *)calloc(1024, sizeof(u256_t));
    uint8_t  *mem   = (uint8_t *)calloc(64 * 1024, 1);
    /* Pad the code with 64 zero bytes so PUSH-N read-past-end is safe; the
     * valid-JUMPDEST map follows the pad (the replay's frame slot layout). */
    uint8_t  *code_copy = (uint8_t *)calloc(code_len + 64 + code_len, 1);
    if (code && code_len) memcpy(code_copy, code, code_len);
    eita_jumpdest_map(code_copy, code_len, code_copy + code_len + 64);

    state->gas_left    = initial_gas;
    state->sp          = 0;
    state->stack       = stack;
    state->memory      = mem;
    state->memory_cap  = 64 * 1024;
    state->code        = code_copy;
    state->code_size   = code_len;
    state->jumpdests   = code_copy + code_len + 64;

    eita_run(state);

    int success = (state->halted && !state->reverted) ? 1 : 0;
    if (state->output && state->output_size && output_buf) {
        uint64_t n = state->output_size < output_cap ? state->output_size : output_cap;
        memcpy(output_buf, state->output, n);
        if (output_len) *output_len = n;
    }
    if (gas_left) *gas_left = state->gas_left;

    free(state);
    free(stack);
    free(mem);
    free(code_copy);
    return success;
}

/* ---- EXP --------------------------------------------------------------- */

/* EXP: result = base^e mod 2^256. Square-and-multiply.
 * Variable gas: caller handles. */
void eita_helper_exp(u256 *result, const u256 *base, const u256 *e) {
    u256 r = {{1, 0, 0, 0}};
    u256 b = *base;
    u256 e_copy = *e;
    while (!u256_is_zero(&e_copy)) {
        if (e_copy.limb[0] & 1) {
            u256 tmp;
            eita_helper_mul(&tmp, &r, &b);
            r = tmp;
        }
        u256 tmp_b;
        eita_helper_mul(&tmp_b, &b, &b);
        b = tmp_b;
        u256_shr_inplace(&e_copy, 1);
    }
    *result = r;
}

/* ---- JIT icache maintenance (#249 Linux JIT bring-up) ------------------ *
 * Flush the instruction cache for a freshly-written JIT chunk. The replay
 * arena writes machine bytes through a RW alias and executes them through a
 * RX alias of the same physical pages; on ARM64 the I-cache must be made
 * coherent with the D-cache writes before execution. __builtin___clear_cache
 * lowers to the correct `dc cvau` / `ic ivau` / `dsb`/`isb` sequence on both
 * arm64 macOS and Linux, so this is one portable entry the SBCL loader calls
 * regardless of platform (replaces the macOS-only sys_icache_invalidate). */
void eita_clear_icache(void *addr, uint64_t len) {
    char *p = (char *)addr;
    __builtin___clear_cache(p, p + len);
}
