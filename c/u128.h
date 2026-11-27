/* c/u128.h — the 128-bit primitives the 256-bit arithmetic is built from.
 *
 * `eita_compute.c` used `__uint128_t` directly, which a 32-bit target does not
 * have (rv32: see c/rv32/README.md). This isolates the eight places that
 * needed it into five primitives with two implementations:
 *
 *   - on a 64-bit compiler, each is the `__uint128_t` expression it replaces,
 *     inline, so the host's generated code and its speed are unchanged;
 *   - otherwise (or with -DEITA_NO_INT128, which is how the differential tests
 *     exercise this path on the host) each is built from 32x32->64 products.
 *
 * `eita_udiv128by64` is the only division, and the only routine here with
 * preconditions: the divisor must be normalized (top bit set) and the high
 * dividend word must be below it, which is what `reciprocal_2by1`'s caller
 * guarantees. It is Hacker's Delight 9-3 `divlu` — the classic two-digit
 * Knuth D over 32-bit halves — and `test_compute` checks it against GMP over
 * millions of cases on both paths, which is the point of keeping both.
 */
#ifndef EITA_U128_H
#define EITA_U128_H
#include <stdint.h>

#if defined(__SIZEOF_INT128__) && !defined(EITA_NO_INT128)
#define EITA_HAS_INT128 1
#endif

/** A 128-bit value as two limbs. */
typedef struct { uint64_t lo, hi; } eita_u128;

/** `a * b`, full 128-bit product. */
static inline eita_u128 eita_mul64(uint64_t a, uint64_t b) {
#if defined(EITA_HAS_INT128)
    __uint128_t p = (__uint128_t)a * b;
    eita_u128 r = { (uint64_t)p, (uint64_t)(p >> 64) };
    return r;
#else
    /* Four 32x32->64 products. The middle column cannot overflow: the two
       32-bit halves plus a 32-bit carry are at most 2^33, well inside 64. */
    uint64_t al = (uint32_t)a, ah = a >> 32;
    uint64_t bl = (uint32_t)b, bh = b >> 32;
    uint64_t ll = al * bl, lh = al * bh, hl = ah * bl, hh = ah * bh;
    uint64_t mid = (ll >> 32) + (uint32_t)lh + (uint32_t)hl;
    eita_u128 r;
    r.lo = (uint64_t)(uint32_t)ll | (mid << 32);
    r.hi = hh + (lh >> 32) + (hl >> 32) + (mid >> 32);
    return r;
#endif
}

/** `a + b` over 128 bits (wrapping, which no caller here reaches). */
static inline eita_u128 eita_u128_add(eita_u128 a, eita_u128 b) {
    eita_u128 r;
    r.lo = a.lo + b.lo;
    r.hi = a.hi + b.hi + (r.lo < a.lo);
    return r;
}

/** `a + b` with a 64-bit addend. */
static inline eita_u128 eita_u128_add64(eita_u128 a, uint64_t b) {
    eita_u128 r;
    r.lo = a.lo + b;
    r.hi = a.hi + (r.lo < b);
    return r;
}

/** `hi:lo` as a 128-bit value. */
static inline eita_u128 eita_u128_of(uint64_t hi, uint64_t lo) {
    eita_u128 r = { lo, hi };
    return r;
}

/** `a > b`, unsigned. */
static inline int eita_u128_gt(eita_u128 a, eita_u128 b) {
    return a.hi > b.hi || (a.hi == b.hi && a.lo > b.lo);
}

/** `(u1:u0) / d`, for a NORMALIZED `d` (top bit set) and `u1 < d`, so the
    quotient is one limb. */
static inline uint64_t eita_udiv128by64(uint64_t u1, uint64_t u0, uint64_t d) {
#if defined(EITA_HAS_INT128)
    return (uint64_t)(((((__uint128_t)u1) << 64) | u0) / d);
#else
    const uint64_t b = (uint64_t)1 << 32;
    uint64_t dn1 = d >> 32, dn0 = (uint32_t)d;
    uint64_t un1 = u0 >> 32, un0 = (uint32_t)u0;
    uint64_t q1, q0, rhat, un21;

    q1 = u1 / dn1;
    rhat = u1 - q1 * dn1;
    while (q1 >= b || q1 * dn0 > b * rhat + un1) {
        q1--; rhat += dn1;
        if (rhat >= b) break;
    }
    un21 = u1 * b + un1 - q1 * d;

    q0 = un21 / dn1;
    rhat = un21 - q0 * dn1;
    while (q0 >= b || q0 * dn0 > b * rhat + un0) {
        q0--; rhat += dn1;
        if (rhat >= b) break;
    }
    return q1 * b + q0;
#endif
}

#endif /* EITA_U128_H */
