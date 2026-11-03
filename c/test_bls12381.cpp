/*
 * test_bls12381.cpp — EIP-2537 conformance test against the chain's own answers.
 *
 * Reads lean/c/testdata/bls12381-vectors.json (inputs with CANONICAL outputs:
 * four captured from the execution of Arc block 21 142 242 tx 34, the rest
 * answered by eth_call against the same chain) and checks every one of the
 * seven precompiles. A vector marked "ok" must return 1 with byte-identical
 * output; a vector marked "fail" must return 0.
 *
 * Also exercises what used to be the cross-curve hazard. BLS12-381 now runs on
 * blst, which has no global curve state, and mcl is pinned to BN254, so a BLS
 * call between two BN254 calls cannot disturb the BN254 result and cannot
 * trigger a re-init. The test asserts both: the BN254 answer is unchanged, and
 * mcl has been initialised exactly once no matter how the calls interleave.
 *
 *   make -C c test_bls12381
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <string>
#include <vector>

#include "../lean/c/mcl_curve.h"

extern "C" {
int eita_bls_g1add(const uint8_t *, size_t, uint8_t *);
int eita_bls_g1msm(const uint8_t *, size_t, uint8_t *);
int eita_bls_g2add(const uint8_t *, size_t, uint8_t *);
int eita_bls_g2msm(const uint8_t *, size_t, uint8_t *);
int eita_bls_pairing(const uint8_t *, size_t, uint8_t *);
int eita_bls_map_fp_to_g1(const uint8_t *, size_t, uint8_t *);
int eita_bls_map_fp2_to_g2(const uint8_t *, size_t, uint8_t *);
int eita_bn254_add(const uint8_t *, size_t, uint8_t *);
}

/* ---- the smallest JSON reader that can read this one generated file ------- */

static std::string slurp(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "cannot open %s\n", path); exit(2); }
    std::string s;
    char buf[65536];
    size_t n;
    while ((n = fread(buf, 1, sizeof buf, f)) > 0) s.append(buf, n);
    fclose(f);
    return s;
}

/* Value of "key": either a quoted string (returned without quotes, `is_null`
 * false) or the literal null (`is_null` true). Aborts if the key is absent, so
 * a format change is loud rather than silently skipping vectors. */
static std::string field(const std::string &obj, const char *key, bool *is_null) {
    std::string pat = std::string("\"") + key + "\"";
    size_t k = obj.find(pat);
    if (k == std::string::npos) { fprintf(stderr, "vector missing key %s\n", key); exit(2); }
    size_t c = obj.find(':', k + pat.size());
    size_t i = c + 1;
    while (i < obj.size() && (obj[i] == ' ' || obj[i] == '\n' || obj[i] == '\t')) i++;
    if (obj.compare(i, 4, "null") == 0) { if (is_null) *is_null = true; return ""; }
    if (obj[i] != '"') { fprintf(stderr, "key %s is neither string nor null\n", key); exit(2); }
    size_t j = i + 1;
    std::string out;
    while (j < obj.size() && obj[j] != '"') {
        if (obj[j] == '\\' && j + 1 < obj.size()) j++;
        out.push_back(obj[j++]);
    }
    if (is_null) *is_null = false;
    return out;
}

static std::vector<uint8_t> unhex(const std::string &s) {
    size_t i = (s.size() >= 2 && s[0] == '0' && s[1] == 'x') ? 2 : 0;
    std::vector<uint8_t> out;
    for (; i + 1 < s.size(); i += 2) {
        auto nib = [](char ch) -> int {
            if (ch >= '0' && ch <= '9') return ch - '0';
            if (ch >= 'a' && ch <= 'f') return ch - 'a' + 10;
            if (ch >= 'A' && ch <= 'F') return ch - 'A' + 10;
            return -1;
        };
        int hi = nib(s[i]), lo = nib(s[i + 1]);
        if (hi < 0 || lo < 0) { fprintf(stderr, "bad hex in vector\n"); exit(2); }
        out.push_back((uint8_t)((hi << 4) | lo));
    }
    return out;
}

/* Split the "vectors" array into its top-level {...} objects. */
static std::vector<std::string> vectors_of(const std::string &doc) {
    size_t k = doc.find("\"vectors\"");
    if (k == std::string::npos) { fprintf(stderr, "no \"vectors\" array\n"); exit(2); }
    size_t i = doc.find('[', k);
    std::vector<std::string> out;
    int depth = 0;
    size_t start = 0;
    bool in_str = false;
    for (size_t p = i; p < doc.size(); p++) {
        char ch = doc[p];
        if (in_str) {
            if (ch == '\\') p++;
            else if (ch == '"') in_str = false;
            continue;
        }
        if (ch == '"') { in_str = true; continue; }
        if (ch == '{') { if (depth++ == 0) start = p; }
        else if (ch == '}') { if (--depth == 0) out.push_back(doc.substr(start, p - start + 1)); }
        else if (ch == ']' && depth == 0) break;
    }
    return out;
}

/* ---- dispatch -------------------------------------------------------------- */

typedef int (*bls_fn)(const uint8_t *, size_t, uint8_t *);

struct Op { const char *name; bls_fn fn; size_t outlen; };

static const Op OPS[] = {
    {"G1ADD",         eita_bls_g1add,         128},
    {"G1MSM",         eita_bls_g1msm,         128},
    {"G2ADD",         eita_bls_g2add,         256},
    {"G2MSM",         eita_bls_g2msm,         256},
    {"PAIRING_CHECK", eita_bls_pairing,        32},
    {"MAP_FP_TO_G1",  eita_bls_map_fp_to_g1,  128},
    {"MAP_FP2_TO_G2", eita_bls_map_fp2_to_g2, 256},
};

static const Op *find_op(const std::string &name) {
    for (const Op &o : OPS) if (name == o.name) return &o;
    return nullptr;
}

static void hexdump(const uint8_t *p, size_t n, size_t max = 32) {
    for (size_t i = 0; i < n && i < max; i++) printf("%02x", p[i]);
    if (n > max) printf("...(%zuB)", n);
}

/* ---- the BN254 anchor used to detect cross-curve corruption --------------- */

/* G = (1, 2) on alt_bn128. If a BLS call leaves mcl on the wrong curve, these
 * coordinates reduce modulo the wrong prime and the doubling changes (or the
 * point is rejected outright). */
static int bn254_double_g(uint8_t out[64]) {
    uint8_t in[128];
    memset(in, 0, sizeof in);
    in[31] = 1; in[63] = 2;      /* (1,2) */
    in[95] = 1; in[127] = 2;     /* (1,2) */
    return eita_bn254_add(in, sizeof in, out);
}

int main(int argc, char **argv) {
    const char *path = argc > 1 ? argv[1] : "../lean/c/testdata/bls12381-vectors.json";
    std::string doc = slurp(path);
    std::vector<std::string> vs = vectors_of(doc);
    printf("oracle: %s (%zu vectors)\n\n", path, vs.size());

    int pass = 0, fail = 0, idx = 0;
    for (const std::string &v : vs) {
        bool null_out = false;
        std::string op = field(v, "op", nullptr);
        std::string expect = field(v, "expect", nullptr);
        std::vector<uint8_t> in = unhex(field(v, "input", nullptr));
        std::string out_s = field(v, "output", &null_out);
        std::vector<uint8_t> want = null_out ? std::vector<uint8_t>() : unhex(out_s);

        const Op *o = find_op(op);
        if (!o) { printf("%2d %-14s SKIP (unknown op)\n", idx++, op.c_str()); fail++; continue; }

        std::vector<uint8_t> got(o->outlen, 0xcd);
        int rc = o->fn(in.data(), in.size(), got.data());

        bool ok;
        const char *why = "";
        if (expect == "fail") {
            ok = (rc == 0);
            why = ok ? "" : "expected failure, got success";
        } else if (rc != 1) {
            ok = false; why = "expected success, got failure";
        } else if (want.size() != o->outlen) {
            ok = false; why = "oracle output length disagrees with the op";
        } else if (memcmp(got.data(), want.data(), o->outlen) != 0) {
            ok = false; why = "output differs from the canonical answer";
        } else {
            ok = true;
        }

        printf("%2d %-14s %5zuB expect=%-4s %s", idx++, op.c_str(), in.size(), expect.c_str(),
               ok ? "PASS" : "FAIL");
        if (!ok) {
            printf("  (%s)", why);
            if (expect == "ok" && rc == 1) {
                printf("\n      want "); hexdump(want.data(), want.size());
                printf("\n      got  "); hexdump(got.data(), got.size());
            }
        }
        printf("\n");
        ok ? pass++ : fail++;
    }

    printf("\nvectors: %d passed, %d failed, %zu total\n", pass, fail, vs.size());

    /* ---- cross-curve interleaving ---------------------------------------- */
    printf("\ncross-curve hazard (mcl pinned to BN254, BLS on blst):\n");
    uint8_t bn_before[64], bn_after[64];
    int rc1 = bn254_double_g(bn_before);
    /* a BLS call in between, which switches mcl's global curve */
    uint8_t scratch[128];
    uint8_t fp_one[64];
    memset(fp_one, 0, sizeof fp_one);
    fp_one[63] = 1;
    int rcb = eita_bls_map_fp_to_g1(fp_one, sizeof fp_one, scratch);
    int rc2 = bn254_double_g(bn_after);
    bool stable = rc1 == 1 && rc2 == 1 && memcmp(bn_before, bn_after, 64) == 0;
    printf("  bn254 ECADD(G,G) -> BLS map -> bn254 ECADD(G,G) identical: %s%s\n",
           stable ? "PASS" : "FAIL", rcb == 1 ? "" : " (BLS call itself failed)");
    if (!stable) {
        printf("    before "); hexdump(bn_before, 64); printf("\n");
        printf("    after  "); hexdump(bn_after, 64); printf("\n");
        fail++;
    } else {
        pass++;
    }

    /* ---- what a switch costs --------------------------------------------- */
    const int N = 200;
    struct timespec t0, t1;
    unsigned long sw0 = eita_mcl_curve_switches();
    (void)sw0;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < N; i++) { bn254_double_g(bn_after); eita_bls_map_fp_to_g1(fp_one, 64, scratch); }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double alt_us = ((t1.tv_sec - t0.tv_sec) * 1e6 + (t1.tv_nsec - t0.tv_nsec) / 1e3) / N;
    unsigned long switches_alt = eita_mcl_curve_switches() - sw0;
    /* The guarantee, not just the timing: pinning mcl means one init, ever. */
    unsigned long inits_total = eita_mcl_curve_switches();
    printf("  mcl initialisations after %d interleaved pairs: %lu (expected 1): %s\n",
           N, inits_total, inits_total == 1 ? "PASS" : "FAIL");
    if (inits_total != 1) fail++; else pass++;

    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < N; i++) eita_bls_map_fp_to_g1(fp_one, 64, scratch);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double same_us = ((t1.tv_sec - t0.tv_sec) * 1e6 + (t1.tv_nsec - t0.tv_nsec) / 1e3) / N;

    /* A 2-pair PAIRING_CHECK (vector 3, the one the seed tx actually ran) is the
     * most expensive thing EIP-2537 prices, at 102 900 gas. Timing it gives the
     * switch overhead a scale: if a switch costs about as much as a pairing then
     * gas already covers that order of work, and the exposure is only to cheap
     * ops (a 375-gas G1ADD) being used to force switches. */
    double pair_us = 0.0;
    for (const std::string &v : vs) {
        if (field(v, "op", nullptr) != "PAIRING_CHECK" || field(v, "expect", nullptr) != "ok") continue;
        std::vector<uint8_t> in = unhex(field(v, "input", nullptr));
        if (in.size() != 768) continue;
        uint8_t o32[32];
        const int M = 50;
        clock_gettime(CLOCK_MONOTONIC, &t0);
        for (int i = 0; i < M; i++) eita_bls_pairing(in.data(), in.size(), o32);
        clock_gettime(CLOCK_MONOTONIC, &t1);
        pair_us = ((t1.tv_sec - t0.tv_sec) * 1e6 + (t1.tv_nsec - t0.tv_nsec) / 1e3) / M;
        break;
    }

    printf("\ncost:\n");
    printf("  one bn254-add + one BLS map, interleaved:          %8.1f us/iter (%lu new mcl inits)\n",
           alt_us, switches_alt);
    printf("  one BLS map alone:                                 %8.1f us/iter\n", same_us);
    printf("  interleaving overhead (was 2781.7 us on mcl):       %8.1f us\n",
           alt_us - same_us);
    printf("  2-pair PAIRING_CHECK (102900 gas), for scale:      %8.1f us\n", pair_us);

    printf("\n%s\n", fail == 0 ? "ALL PASS" : "FAILURES PRESENT");
    return fail == 0 ? 0 : 1;
}
