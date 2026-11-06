/* test_modexp.c — eita_modexp (lean/c/modexp.c: GMP up to 64-byte moduli, OpenSSL above)
 * against OpenSSL's BN_mod_exp on the same EIP-198 input: random base/exp/mod sizes across
 * the 64-byte backend boundary, modulus 0 / 1 / even / all-ones / leading zero bytes, exponent
 * 0 / 1, base above the modulus, truncated input (zero-padded), and the EIP-198 examples.
 * make test_modexp. Args: [N, default 200000] [seed] */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <openssl/bn.h>

int eita_modexp(const uint8_t *src, size_t src_len, uint8_t *out, size_t *out_len);

static uint64_t rs;
static uint64_t rnd(void) { uint64_t z = (rs += 0x9e3779b97f4a7c15ULL); z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
                            z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL; return z ^ (z >> 31); }
static long fails, cases;

static void put_size(uint8_t *h, uint64_t v) { memset(h, 0, 32); for (int i = 0; i < 8; i++) h[31 - i] = (uint8_t)(v >> (8 * i)); }

/* reference: the input as EIP-198 reads it (zero-padded), through BN_mod_exp */
static void reference(const uint8_t *src, size_t len, size_t bs, size_t es, size_t ms, uint8_t *out) {
  uint8_t *body = calloc(bs + es + ms + 1, 1);
  if (len > 96) memcpy(body, src + 96, len - 96 < bs + es + ms ? len - 96 : bs + es + ms);
  BIGNUM *b = BN_bin2bn(body, (int)bs, NULL), *e = BN_bin2bn(body + bs, (int)es, NULL),
         *m = BN_bin2bn(body + bs + es, (int)ms, NULL), *r = BN_new();
  BN_CTX *c = BN_CTX_new();
  memset(out, 0, ms);
  if (!BN_is_zero(m)) { BN_mod_exp(r, b, e, m, c); int n = BN_num_bytes(r); BN_bn2bin(r, out + ms - n); }
  BN_free(b); BN_free(e); BN_free(m); BN_free(r); BN_CTX_free(c); free(body);
}

static void check(size_t bs, size_t es, size_t ms, int shape, int truncate) {
  size_t full = 96 + bs + es + ms;
  uint8_t *src = malloc(full + 1), *got = malloc(ms + 1), *want = malloc(ms + 1);
  put_size(src, bs); put_size(src + 32, es); put_size(src + 64, ms);
  uint8_t *b = src + 96, *e = b + bs, *m = e + es;
  for (size_t i = 0; i < bs + es + ms; i++) b[i] = (uint8_t)rnd();
  switch (shape) {
  case 1: memset(m, 0, ms); break;                                  /* modulus 0 */
  case 2: memset(m, 0, ms); if (ms) m[ms - 1] = 1; break;           /* modulus 1 */
  case 3: if (ms) m[ms - 1] &= 0xfe; break;                         /* even */
  case 4: memset(m, 0xff, ms); break;                               /* all ones */
  case 5: if (ms > 2) { m[0] = 0; m[1] = 0; } break;                /* leading zero bytes */
  case 6: memset(e, 0, es); break;                                  /* exponent 0 */
  case 7: memset(e, 0, es); if (es) e[es - 1] = 1; break;           /* exponent 1 */
  case 8: memset(b, 0, bs); break;                                  /* base 0 */
  }
  size_t len = truncate ? 96 + (size_t)(rnd() % (bs + es + ms + 1)) : full;
  size_t ol = 0;
  int ok = eita_modexp(src, len, got, &ol);
  reference(src, len, bs, es, ms, want);
  cases++;
  if (!ok || ol != ms || memcmp(got, want, ms)) {
    if (fails++ < 10) printf("FAIL bs=%zu es=%zu ms=%zu shape=%d len=%zu ok=%d ol=%zu\n", bs, es, ms, shape, len, ok, ol);
  }
  free(src); free(got); free(want);
}

int main(int argc, char **argv) {
  long N = argc > 1 ? atol(argv[1]) : 200000;
  rs = argc > 2 ? strtoull(argv[2], NULL, 0) : 0x6d6f64657870ULL;
  for (long i = 0; i < N; i++) {
    size_t ms = (size_t)(rnd() % 71), bs = (size_t)(rnd() % 81), es = (size_t)(rnd() % 81);
    if (rnd() % 3 == 0) { bs = 32; es = 32; ms = 32; }              /* the mainnet shape */
    check(bs, es, ms, (int)(rnd() % 9), rnd() % 8 == 0);
  }
  /* EIP-198 examples: 3^(2^256 - 2^32 - 978) mod (2^256 - 2^32 - 977) = 1; a zero modulus gives 0 */
  uint8_t in[96 + 1 + 32 + 32] = {0}, out[32]; size_t ol;
  put_size(in, 1); put_size(in + 32, 32); put_size(in + 64, 32);
  in[96] = 3;
  /* modulus p = 2^256 - 2^32 - 977 = ff..ff fffffffe fffffc2f; exponent p - 1 = ff..ff fffffffe fffffc2e */
  memset(in + 129, 0xff, 32); in[129 + 27] = 0xfe; in[129 + 30] = 0xfc; in[129 + 31] = 0x2f;
  memset(in + 97, 0xff, 32);  in[97 + 27] = 0xfe;  in[97 + 30] = 0xfc;  in[97 + 31] = 0x2e;
  int ok = eita_modexp(in, sizeof in, out, &ol);
  int one = ok && ol == 32 && out[31] == 1; for (int i = 0; i < 31; i++) one &= out[i] == 0;
  printf("EIP-198 example 1 (3^(p-1) mod p = 1): %s\n", one ? "ok" : "FAIL"); if (!one) fails++;
  put_size(in + 64, 0); ok = eita_modexp(in, 96 + 1 + 32, out, &ol);
  printf("EIP-198 example 2 (zero modulus: empty output): %s\n", ok && ol == 0 ? "ok" : "FAIL"); if (!(ok && ol == 0)) fails++;
  printf("modexp: %ld cases, %ld failures\n", cases, fails);
  return fails != 0;
}
