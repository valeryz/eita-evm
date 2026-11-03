/* test_compute.c — eita_compute.c's arithmetic helpers against GMP. They are trusted-base
 * C that every tier and backend calls, so a tier diff cannot see their bugs. The EVM
 * definitions, written out in GMP (sa = a as two's complement):
 *   DIV / MOD a b   unsigned a / b, a mod b; b = 0 gives 0
 *   SDIV / SMOD a b trunc(sa / sb), sign(sa) * (|sa| mod |sb|), mod 2^256; b = 0 gives 0
 *   ADDMOD / MULMOD (a + b) mod n, (a * b) mod n without the 2^256 wrap; n = 0 gives 0
 *   SAR s v         floor(sv / 2^min(s, 256)) mod 2^256 (#258: s a multiple of 64)
 * The first six share one word-wise division (udivrem, Knuth algorithm D). Inputs, from
 * the seed: (1) N random cases per helper, each operand a random width 1..256, an edge
 * constant, a limb pattern of 0 / 1 / 2^63 / 2^64-1 / random words (Knuth D's rare
 * branches) or a negation; (2) every divisor bit length 1..256 (every limb count and
 * normalization shift) in four shapes, and every SAR shift 0..257 of every edge constant;
 * (3) every pair of edge constants (0..3, 2^k-1, 2^k, 2^k+1, -2^k, MIN+1, full words).
 * Results go through exactly-32-byte heap buffers, so ASan flags a write outside them
 * (the bf4c773 MULMOD bug), and are recomputed with the result aliasing each operand.
 * Then the buffer reads (CALLDATALOAD / CALLDATACOPY / CODECOPY, section 4) against EELS
 * buffer_read at the u64 wrap. make test_compute (ASan + UBSan; in `make test`). Args: [N, default 1000000] [seed] */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include "evm_state.h"

typedef u256_t u256;
typedef void (*fn2)(u256 *, const u256 *, const u256 *);
typedef void (*fn3)(u256 *, const u256 *, const u256 *, const u256 *);
void eita_helper_div(u256 *, const u256 *, const u256 *);
void eita_helper_mod(u256 *, const u256 *, const u256 *);
void eita_helper_sdiv(u256 *, const u256 *, const u256 *);
void eita_helper_smod(u256 *, const u256 *, const u256 *);
void eita_helper_sar(u256 *, const u256 *, const u256 *);
void eita_helper_addmod(u256 *, const u256 *, const u256 *, const u256 *);
void eita_helper_mulmod(u256 *, const u256 *, const u256 *, const u256 *);
void eita_helper_calldataload(u256 *, EvmState *, const u256 *);
void eita_helper_calldatacopy(EvmState *, const u256 *, const u256 *, const u256 *);
void eita_helper_codecopy(EvmState *, const u256 *, const u256 *, const u256 *);

/* eita_compute.c references these for helpers this test never calls. */
void eita_keccak256(const uint8_t *in, size_t n, uint8_t out[32]) { (void)in; (void)n; (void)out; }
void eita_run(EvmState *state) { (void)state; }

enum { DIV, MOD, SDIV, SMOD, SAR, ADDMOD, MULMOD, NOPS };
static const char *names[NOPS] = { "DIV", "MOD", "SDIV", "SMOD", "SAR", "ADDMOD", "MULMOD" };
static const fn2 bin[SAR + 1] = { eita_helper_div, eita_helper_mod, eita_helper_sdiv,
                                  eita_helper_smod, eita_helper_sar };
static long counts[NOPS], fails;

static uint64_t rng_state;                          /* splitmix64 */
static uint64_t rnd(void) {
    uint64_t z = (rng_state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static void u_set(u256 *x, uint64_t v) { memset(x, 0, sizeof *x); x->limb[0] = v; }
static void u_pow2(u256 *x, int k) { u_set(x, 0); x->limb[k / 64] = (uint64_t)1 << (k % 64); }
static void u_neg(u256 *x) {
    uint64_t c = 1;
    for (int i = 0; i < 4; i++) { uint64_t t = ~x->limb[i] + c; c = c && t == 0; x->limb[i] = t; }
}
static void u_add(u256 *x, int64_t d) {             /* x += d, d in {-1, +1} */
    for (int i = 0; i < 4; i++) { uint64_t o = x->limb[i]; x->limb[i] += (uint64_t)d;
                                  if (d > 0 ? x->limb[i] != 0 : o != 0) break; }
}
static void u_width(u256 *x, int w) {               /* random, exactly w bits (1..256) */
    for (int i = 0; i < 4; i++) {
        int lo = i * 64;
        x->limb[i] = w <= lo ? 0 : w < lo + 64 ? rnd() & (((uint64_t)1 << (w - lo)) - 1) : rnd();
    }
    x->limb[(w - 1) / 64] |= (uint64_t)1 << ((w - 1) % 64);
}

static u256 edges[1100];
static int n_edges;
static void edge_add(const u256 *x) {
    for (int i = 0; i < n_edges; i++) if (!memcmp(&edges[i], x, sizeof *x)) return;
    edges[n_edges++] = *x;
}
static void build_edges(void) {
    u256 x;
    for (int v = 0; v <= 3; v++) { u_set(&x, (uint64_t)v); edge_add(&x); }
    for (int k = 1; k < 256; k++)
        for (int d = -1; d <= 1; d++) { u_pow2(&x, k); if (d) u_add(&x, d); edge_add(&x); }
    for (int k = 0; k < 256; k++) { u_pow2(&x, k); u_neg(&x); edge_add(&x); }      /* -2^k */
    u_set(&x, 2); u_neg(&x); edge_add(&x);                                           /* -2 */
    u_pow2(&x, 255); u_add(&x, 1); edge_add(&x);                                     /* MIN+1 */
    for (int i = 0; i < 4; i++) { u_set(&x, 0); x.limb[i] = ~(uint64_t)0; edge_add(&x); }
}

static void u_pattern(u256 *x) {                    /* hostile limbs, random top limb */
    static const uint64_t w[] = { 0, 1, 2, 0x7fffffffffffffffULL, 0x8000000000000000ULL,
                                  0x8000000000000001ULL, 0xfffffffffffffffeULL,
                                  0xffffffffffffffffULL, 0xffffffffULL, 0xffffffff00000000ULL };
    int top = (int)(rnd() % 4);
    for (int i = 0; i < 4; i++) x->limb[i] = i > top ? 0 : (rnd() & 3) == 0 ? rnd() : w[rnd() % 10];
}
static void u_random(u256 *x) {
    switch (rnd() % 8) {
    case 0: case 1: case 2: u_width(x, 1 + (int)(rnd() % 256)); break;
    case 3: *x = edges[rnd() % (uint64_t)n_edges]; break;
    case 4: u_pattern(x); break;
    case 5: u_width(x, 1 + (int)(rnd() % 256)); u_neg(x); break;
    case 6: u_width(x, 1 + (int)(rnd() % 64)); break;
    default: u_pattern(x); u_neg(x); break;
    }
}

/* ---- GMP reference -------------------------------------------------------- */
static mpz_t M256, M255;
static void to_mpz(mpz_t z, const u256 *x, int sgn) {
    mpz_import(z, 4, -1, 8, 0, 0, x->limb);
    if (sgn && mpz_cmp(z, M255) >= 0) mpz_sub(z, z, M256);
}
static void ref(int op, u256 *out, const u256 *a, const u256 *b, const u256 *n) {
    mpz_t A, B, R; mpz_inits(A, B, R, NULL);
    to_mpz(A, a, op == SDIV || op == SMOD);
    to_mpz(B, op >= ADDMOD ? n : b, op == SDIV || op == SMOD || op == SAR);
    if (op == SAR) {                                 /* a = shift, b = value */
        int big = (a->limb[1] | a->limb[2] | a->limb[3]) || a->limb[0] >= 256;
        mpz_fdiv_q_2exp(R, B, big ? 256 : a->limb[0]);
    } else if (mpz_sgn(B) == 0) mpz_set_ui(R, 0);
    else switch (op) {
    case DIV: case SDIV: mpz_tdiv_q(R, A, B); break;
    case MOD: case SMOD: mpz_tdiv_r(R, A, B); break;
    case ADDMOD: to_mpz(R, b, 0); mpz_add(R, A, R); mpz_mod(R, R, B); break;
    case MULMOD: to_mpz(R, b, 0); mpz_mul(R, A, R); mpz_mod(R, R, B); break;
    }
    mpz_mod(R, R, M256);
    memset(out, 0, sizeof *out); mpz_export(out->limb, NULL, -1, 8, 0, 0, R);
    mpz_clears(A, B, R, NULL);
}

static void call(int op, u256 *r, const u256 *a, const u256 *b, const u256 *n) {
    if (op <= SAR) bin[op](r, a, b);
    else (op == ADDMOD ? (fn3)eita_helper_addmod : (fn3)eita_helper_mulmod)(r, a, b, n);
}

static void check(int op, const u256 *a, const u256 *b, const u256 *n) {
    u256 want, *in[3], *r = malloc(sizeof(u256));
    ref(op, &want, a, b, n);
    for (int k = 0; k < 3; k++) in[k] = malloc(sizeof(u256));
    *in[0] = *a; *in[1] = *b; *in[2] = *n;
    memset(r, 0xa5, sizeof *r);
    call(op, r, in[0], in[1], in[2]);
    int bad = memcmp(r, &want, sizeof want) || memcmp(in[0], a, 32) || memcmp(in[1], b, 32)
              || memcmp(in[2], n, 32);
    for (int k = 0; k < (op >= ADDMOD ? 3 : 2) && !bad; k++) {   /* result aliases operand k */
        *in[0] = *a; *in[1] = *b; *in[2] = *n;
        call(op, in[k], in[0], in[1], in[2]);
        bad = memcmp(in[k], &want, sizeof want) != 0;
    }
    free(r); for (int k = 0; k < 3; k++) free(in[k]);
    counts[op]++;
    if (bad && fails++ < 20) {
        const u256 *v[4] = { a, b, n, &want };
        fprintf(stderr, "FAIL %s", names[op]);
        for (int k = 0; k < 4; k++)
            fprintf(stderr, " %s=0x%016llx%016llx%016llx%016llx", k == 3 ? "want" : (const char *[]){"a", "b", "n"}[k],
                    (unsigned long long)v[k]->limb[3], (unsigned long long)v[k]->limb[2],
                    (unsigned long long)v[k]->limb[1], (unsigned long long)v[k]->limb[0]);
        fprintf(stderr, "\n");
    }
}

/* 4. Buffer reads — CALLDATALOAD, CALLDATACOPY, CODECOPY: byte j of the result is buf[start + j]
 * when start + j < size in unbounded arithmetic, else 0 (EELS buffer_read). Every start offset
 * near a size and near 2^64 (where start + j wraps a u64), past 2^64, and huge; every length
 * 0..40 into a 64-byte memory that must change only in [0, len). */
static long buf_cases, buf_fails;
static uint8_t buf_ref(const uint8_t *buf, uint64_t size, const u256 *start, uint64_t j) {
    if (start->limb[1] | start->limb[2] | start->limb[3]) return 0;
    return (unsigned __int128)start->limb[0] + j < size ? buf[start->limb[0] + j] : 0;
}
static void buf_fail(const char *what, uint64_t size, const u256 *start, uint64_t len) {
    if (buf_fails++ < 20)
        fprintf(stderr, "FAIL %s size=%llu start=0x%016llx%016llx%016llx%016llx len=%llu\n", what,
                (unsigned long long)size, (unsigned long long)start->limb[3], (unsigned long long)start->limb[2],
                (unsigned long long)start->limb[1], (unsigned long long)start->limb[0], (unsigned long long)len);
}
static void check_buffers(void) {
    static const uint64_t sizes[] = { 0, 1, 31, 32, 33, 100 };
    uint8_t src[100], mem[64];
    for (int i = 0; i < 100; i++) src[i] = (uint8_t)(i + 1);       /* no zero byte */
    for (int si = 0; si < 6; si++) {
        uint64_t size = sizes[si];
        u256 starts[128]; int ns = 0;
        for (uint64_t k = 0; k <= size + 2; k++) u_set(&starts[ns++], k);
        for (uint64_t k = 1; k <= 33; k += 8) u_set(&starts[ns++], (uint64_t)0 - k);   /* 2^64 - k */
        u_set(&starts[ns++], (uint64_t)1 << 63);
        u_pow2(&starts[ns++], 64); u_pow2(&starts[ns++], 255);
        u_set(&starts[ns], 1); starts[ns++].limb[3] = 1;                                   /* 2^192 + 1 */
        for (int t = 0; t < ns; t++) {
            EvmState st; memset(&st, 0, sizeof st);
            st.calldata = src; st.calldata_size = size; st.code = src; st.code_size = size;
            u256 r; eita_helper_calldataload(&r, &st, &starts[t]);
            int bad = 0;
            for (int j = 0; j < 32; j++)                               /* byte j is BE: limb 3 - j/8 */
                bad |= (uint8_t)(r.limb[3 - j / 8] >> (8 * (7 - j % 8))) != buf_ref(src, size, &starts[t], (uint64_t)j);
            buf_cases++; if (bad) buf_fail("CALLDATALOAD", size, &starts[t], 32);
            for (uint64_t len = 0; len <= 40; len++)
                for (int which = 0; which < 2; which++) {
                    u256 dst, l; u_set(&dst, 0); u_set(&l, len);
                    memset(mem, 0xa5, sizeof mem);
                    st.memory = mem; st.memory_size = st.mp = st.memory_cap = sizeof mem;
                    (which ? eita_helper_codecopy : eita_helper_calldatacopy)(&st, &dst, &starts[t], &l);
                    bad = 0;
                    for (uint64_t j = 0; j < sizeof mem; j++)
                        bad |= mem[j] != (j < len ? buf_ref(src, size, &starts[t], j) : 0xa5);
                    buf_cases++; if (bad) buf_fail(which ? "CODECOPY" : "CALLDATACOPY", size, &starts[t], len);
                }
        }
    }
    printf("buffers %9ld cases, %ld failures\n", buf_cases, buf_fails);
}

int main(int argc, char **argv) {
    long N = argc > 1 ? atol(argv[1]) : 1000000;
    rng_state = argc > 2 ? strtoull(argv[2], NULL, 0) : 0x5eedd17d0ULL;
    mpz_inits(M256, M255, NULL);
    mpz_ui_pow_ui(M256, 2, 256); mpz_ui_pow_ui(M255, 2, 255);
    build_edges();
    for (long i = 0; i < N; i++) {                               /* 1. random */
        u256 a, b, n; u_random(&a); u_random(&b); u_random(&n);
        u256 sh = a;
        if (rnd() & 3) u_set(&sh, rnd() % 300);                  /* SAR: mostly in-range shifts */
        for (int op = 0; op < NOPS; op++) check(op, op == SAR ? &sh : &a, &b, &n);
    }
    for (int w = 1; w <= 256; w++)                               /* 2. divisor sweep */
        for (int shape = 0; shape < 4; shape++) {
            u256 d, nd;
            if (shape == 0) u_pow2(&d, w - 1);
            else if (shape == 1) { u_set(&d, 0);                                   /* 2^w - 1 */
                                   for (int k = 0; k < w; k++) d.limb[k / 64] |= (uint64_t)1 << (k % 64); }
            else u_width(&d, w);
            nd = d; u_neg(&nd);
            for (int j = 0; j < 400; j++) {
                u256 a, b;
                if (j < 40) { a = edges[rnd() % (uint64_t)n_edges]; b = edges[rnd() % (uint64_t)n_edges]; }
                else if (j < 120) { u_pattern(&a); u_pattern(&b); }
                else { u_width(&a, 1 + (int)(rnd() % 256)); u_width(&b, 1 + (int)(rnd() % 256)); }
                for (int op = DIV; op <= SMOD; op++) check(op, &a, &d, &d);
                check(SDIV, &a, &nd, &nd); check(SMOD, &a, &nd, &nd);
                check(ADDMOD, &a, &b, &d); check(MULMOD, &a, &b, &d);
            }
        }
    for (int s = 0; s <= 257; s++)
        for (int i = 0; i < n_edges; i++) { u256 sh; u_set(&sh, (uint64_t)s); check(SAR, &sh, &edges[i], &edges[i]); }
    for (int i = 0; i < n_edges; i++)                            /* 3. edge pairs */
        for (int j = 0; j < n_edges; j++) {
            for (int op = DIV; op <= SAR; op++) check(op, &edges[i], &edges[j], &edges[j]);
            const u256 *n = &edges[rnd() % (uint64_t)n_edges];
            check(ADDMOD, &edges[i], &edges[j], n); check(MULMOD, &edges[i], &edges[j], n);
        }
    long total = 0;
    for (int op = 0; op < NOPS; op++) { printf("%-7s %9ld cases\n", names[op], counts[op]); total += counts[op]; }
    printf("total   %9ld cases, %d edge constants, %ld failures\n", total, n_edges, fails);
    check_buffers();
    return fails != 0 || buf_fails != 0;
}
