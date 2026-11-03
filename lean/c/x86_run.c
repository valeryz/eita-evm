/*
 * x86_run.c — execution harness for X86Asm output (stage 4 of #238), and a
 * minimal loader for the helper-call family.
 *
 * Usage: x86_run <hex-bytes> [arg0 [arg1]] [N=V | N=@M | ?N | !sym:off ...]
 *   arg0/arg1 are decimal u64s, or `@N` meaning "the address of element N of
 *   the harness's u64 array" (element i holds 1000 + i by default). `N=V`
 *   presets element N to V before the call (`N=@M` presets it to the ADDRESS
 *   of element M, for pointer-valued slots); `?N` prints element N after it.
 *   `N=!sym` presets element N to the ADDRESS of helper `sym` (a callback
 *   table entry). `!sym:off` is an abs64 relocation: the 8-byte slot at byte `off` of the
 *   image is filled with the address of `sym` from the helper table below —
 *   what the real loader does with dlsym — before the image is made
 *   executable. A leading underscore on `sym` is ignored (Mach-O spelling).
 *   The bytes are mapped RW, patched, flipped to RX, and called as
 *   uint64_t f(uint64_t rdi, uint64_t rsi); the output is the result followed
 *   by each `?N` readback, space-separated, in decimal.
 *
 * The helper table binds the REAL helpers: c/eita_compute.c is compiled into
 * this harness (the portable C the handlers call on every target), so a
 * derived MUL/DIV/… handler is exercised against the same code it will call
 * in the arena.
 *
 * Built with `clang -arch x86_64` (macOS, run under Rosetta 2) or plain clang
 * (Linux x86-64) by scripts/verify-x86-run.sh.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include "evm_state.h"

typedef u256_t u256;
void eita_helper_mul(u256 *, const u256 *, const u256 *);
void eita_helper_div(u256 *, const u256 *, const u256 *);
void eita_helper_sdiv(u256 *, const u256 *, const u256 *);
void eita_helper_mod(u256 *, const u256 *, const u256 *);
void eita_helper_smod(u256 *, const u256 *, const u256 *);
void eita_helper_shl(u256 *, const u256 *, const u256 *);
void eita_helper_shr(u256 *, const u256 *, const u256 *);
void eita_helper_sar(u256 *, const u256 *, const u256 *);
void eita_helper_byte(u256 *, const u256 *, const u256 *);
void eita_helper_signextend(u256 *, const u256 *, const u256 *);
void eita_helper_addmod(u256 *, const u256 *, const u256 *, const u256 *);
void eita_helper_mulmod(u256 *, const u256 *, const u256 *, const u256 *);

/* A host callback stub for the cb-slot handlers (SLOAD shape): writes a value
 * derived from the key into the scratch and returns the gas to charge. The
 * real callbacks live in the SBCL host; this one lets the call SEQUENCE run. */
static uint64_t eita_test_cb_sload(void *ctx, void *field, const uint64_t *top, uint64_t *scratch) {
  (void)ctx; (void)field;
  scratch[0] = 0xC0FFEEull + top[0]; scratch[1] = 0; scratch[2] = 0; scratch[3] = 0;
  return 42;
}
/* TLOAD's direct callback (`cbDirect _eita_ts_tload`): same shape, no gas return. */
static void eita_ts_tload(void *ctx, void *field, const uint64_t *top, uint64_t *scratch) {
  (void)ctx; (void)field;
  scratch[0] = 0xBEEFull + top[0]; scratch[1] = 0; scratch[2] = 0; scratch[3] = 0;
}

/* eita_compute.c references these; the compute helpers under test do not call them. */
void eita_keccak256(const uint8_t *in, size_t n, uint8_t out[32]) { (void)in; (void)n; (void)out; }
void eita_run(EvmState *state) { (void)state; }

static const struct { const char *name; void *fn; } helpers[] = {
  {"eita_helper_mul", (void *)eita_helper_mul},   {"eita_helper_div", (void *)eita_helper_div},
  {"eita_helper_sdiv", (void *)eita_helper_sdiv}, {"eita_helper_mod", (void *)eita_helper_mod},
  {"eita_helper_smod", (void *)eita_helper_smod}, {"eita_helper_shl", (void *)eita_helper_shl},
  {"eita_helper_shr", (void *)eita_helper_shr},   {"eita_helper_sar", (void *)eita_helper_sar},
  {"eita_helper_byte", (void *)eita_helper_byte}, {"eita_helper_signextend", (void *)eita_helper_signextend},
  {"eita_helper_addmod", (void *)eita_helper_addmod}, {"eita_helper_mulmod", (void *)eita_helper_mulmod},
  {"eita_test_cb_sload", (void *)eita_test_cb_sload}, {"eita_ts_tload", (void *)eita_ts_tload},
};

static uint64_t arr[256];   /* 2 KB: a full-size EvmState image, a stack, memory and code */

static uint64_t parse_arg(const char *s) {
  if (s[0] == '@') return (uint64_t)(uintptr_t)&arr[strtoull(s + 1, NULL, 10) % 256];
  return strtoull(s, NULL, 10);
}

static void *lookup(const char *sym) {
  if (sym[0] == '_') sym++;
  for (size_t i = 0; i < sizeof helpers / sizeof helpers[0]; i++)
    if (strcmp(helpers[i].name, sym) == 0) return helpers[i].fn;
  fprintf(stderr, "unknown symbol %s\n", sym);
  exit(2);
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: x86_run <hex> [args...]\n"); return 2; }
  for (int i = 0; i < 256; i++) arr[i] = 1000 + i;
  const char *hex = argv[1];
  size_t n = strlen(hex) / 2;
  size_t sz = (n + 4095) & ~(size_t)4095; if (!sz) sz = 4096;
  unsigned char *m = mmap(0, sz, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
  if (m == MAP_FAILED) { perror("mmap"); return 2; }
  for (size_t i = 0; i < n; i++) {
    unsigned v; if (sscanf(hex + 2 * i, "%2x", &v) != 1) { fprintf(stderr, "bad hex\n"); return 2; }
    m[i] = (unsigned char)v;
  }
  uint64_t a0 = argc > 2 ? parse_arg(argv[2]) : 0;
  uint64_t a1 = argc > 3 ? parse_arg(argv[3]) : 0;
  for (int i = 4; i < argc; i++) {
    unsigned long long k, v;
    char sym[128];
    if (argv[i][0] == '!' && sscanf(argv[i] + 1, "%127[^:]:%llu", sym, &v) == 2 && v + 8 <= n) {
      uint64_t addr = (uint64_t)(uintptr_t)lookup(sym);
      memcpy(m + v, &addr, 8);
    } else if (sscanf(argv[i], "%llu=!%127s", &k, sym) == 2 && k < 256) {
      arr[k] = (uint64_t)(uintptr_t)lookup(sym);           /* a function-pointer slot */
    } else if (sscanf(argv[i], "%llu=@%llu", &k, &v) == 2 && k < 256 && v < 256) {
      arr[k] = (uint64_t)(uintptr_t)&arr[v];
    } else if (sscanf(argv[i], "%llu=%llu", &k, &v) == 2 && k < 256) {
      arr[k] = v;
    }
  }
  if (mprotect(m, sz, PROT_READ | PROT_EXEC)) { perror("mprotect"); return 2; }
  uint64_t (*f)(uint64_t, uint64_t) = (uint64_t (*)(uint64_t, uint64_t))m;
  printf("%llu", (unsigned long long)f(a0, a1));
  for (int i = 4; i < argc; i++)
    if (argv[i][0] == '?') printf(" %llu", (unsigned long long)arr[strtoull(argv[i] + 1, NULL, 10)]);
  printf("\n");
  return 0;
}
