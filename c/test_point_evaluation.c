/* EIP-4844 point evaluation (lean/c/point_evaluation.c) against the c-kzg-4844
 * verify_kzg_proof vectors (lean/c/testdata/kzg-verify-proof-vectors.txt):
 *   1. eita_kzg_verify_proof gives the vector's exact verdict (valid / invalid / error);
 *      a field of the wrong length must be an error case (the precompile's fixed
 *      192-byte layout rejects it before any curve code runs);
 *   2. eita_point_evaluation on the 192-byte input with the correct versioned hash
 *      succeeds exactly on the valid cases and returns 4096 ++ BLS_MODULUS; with one
 *      versioned-hash bit flipped, or a byte short, it fails. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

int eita_kzg_verify_proof(const uint8_t c[48], const uint8_t z[32], const uint8_t y[32], const uint8_t p[48]);
int eita_point_evaluation(const uint8_t *in, uint64_t inlen, uint8_t out[64]);
void sha256_hash(const uint8_t *in, size_t n, uint8_t out[32]);

static int unhex(const char *s, uint8_t *out, size_t want) {
    if (strlen(s) != 2 * want) return 0;
    for (size_t i = 0; i < want; i++) {
        unsigned v;
        if (sscanf(s + 2 * i, "%2x", &v) != 1) return 0;
        out[i] = (uint8_t)v;
    }
    return 1;
}

int main(int argc, char **argv) {
    FILE *f = fopen(argc > 1 ? argv[1] : "../lean/c/testdata/kzg-verify-proof-vectors.txt", "r");
    if (!f) { perror("vectors"); return 2; }
    char line[1024], name[256], cs[256], zs[256], ys[256], ps[256], exp[8];
    int n = 0, bad = 0, ok_cases = 0;
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#') continue;
        if (sscanf(line, "%255s %255s %255s %255s %255s %7s", name, cs, zs, ys, ps, exp) != 6) continue;
        n++;
        uint8_t in[192], out[64];
        int lens_ok = unhex(cs, in + 96, 48) & unhex(zs, in + 32, 32) &
                      unhex(ys, in + 64, 32) & unhex(ps, in + 144, 48);
        int want = exp[0] == '1' ? 1 : exp[0] == '0' ? 0 : -1;
        if (!lens_ok) {
            if (want != -1) { printf("FAIL %s: malformed field but expected %s\n", name, exp); bad++; }
            continue;
        }
        int got = eita_kzg_verify_proof(in + 96, in + 32, in + 64, in + 144);
        if (got != want) { printf("FAIL %s: verify %d, expected %d\n", name, got, want); bad++; }
        sha256_hash(in + 96, 48, in);
        in[0] = 0x01;
        int pe = eita_point_evaluation(in, 192, out);
        if (pe != (want == 1)) { printf("FAIL %s: precompile %d\n", name, pe); bad++; }
        if (pe && !(out[30] == 0x10 && out[31] == 0 && out[32] == 0x73 && out[63] == 1)) {
            printf("FAIL %s: output\n", name); bad++;
        }
        if (want == 1) {
            ok_cases++;
            in[5] ^= 1;
            if (eita_point_evaluation(in, 192, out)) { printf("FAIL %s: hash flip accepted\n", name); bad++; }
            in[5] ^= 1;
            if (eita_point_evaluation(in, 191, out)) { printf("FAIL %s: 191 bytes accepted\n", name); bad++; }
        }
    }
    fclose(f);
    printf("point evaluation: %d vectors (%d valid), %d failures\n", n, ok_cases, bad);
    return bad || n == 0;
}
