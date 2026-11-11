/* c/rv32/shim.c — the freestanding C runtime the engine needs on rv32.
 *
 * Memory moves are implemented here (the compiler emits calls to memcpy and
 * memset for struct assignment and initialisation, so they must exist as real
 * symbols). Allocation, abort and logging are the HOST's: the engine's C owns
 * no heap and no console, which is what lets the same sources sit inside a
 * Xous application that already has both. See README.md.
 */
#include <string.h>
#include <stdlib.h>
#include <stdio.h>


/* Every definition here is WEAK. A freestanding consumer gets these; a
 * consumer that already has a C runtime — a Xous application built with Rust
 * `std`, which exports `abort` and brings its own allocator — overrides them,
 * and the link does not collide. That is how the same shim serves both. */
#define EITA_SHIM __attribute__((weak))

/* --- provided by the firmware ------------------------------------------- */
void *eita_rv32_malloc(size_t n);
void *eita_rv32_realloc(void *p, size_t n);
void  eita_rv32_free(void *p);
void  eita_rv32_abort(const char *why) __attribute__((noreturn));
void  eita_rv32_log(const char *msg);

/* --- memory ------------------------------------------------------------- */
EITA_SHIM void *memcpy(void *dst, const void *src, size_t n) {
    unsigned char *d = dst; const unsigned char *s = src;
    for (size_t i = 0; i < n; i++) d[i] = s[i];
    return dst;
}

EITA_SHIM void *memmove(void *dst, const void *src, size_t n) {
    unsigned char *d = dst; const unsigned char *s = src;
    if (d < s) { for (size_t i = 0; i < n; i++) d[i] = s[i]; }
    else { for (size_t i = n; i > 0; i--) d[i - 1] = s[i - 1]; }
    return dst;
}

EITA_SHIM void *memset(void *dst, int c, size_t n) {
    unsigned char *d = dst;
    for (size_t i = 0; i < n; i++) d[i] = (unsigned char)c;
    return dst;
}

EITA_SHIM int memcmp(const void *a, const void *b, size_t n) {
    const unsigned char *x = a, *y = b;
    for (size_t i = 0; i < n; i++) if (x[i] != y[i]) return (int)x[i] - (int)y[i];
    return 0;
}

/* --- allocation: the host's ---------------------------------------------- */
EITA_SHIM void *malloc(size_t n) { return eita_rv32_malloc(n); }
EITA_SHIM void  free(void *p) { eita_rv32_free(p); }
EITA_SHIM void *realloc(void *p, size_t n) { return eita_rv32_realloc(p, n); }

EITA_SHIM void *calloc(size_t n, size_t sz) {
    size_t total = n * sz;
    if (sz != 0 && total / sz != n) return 0;      /* overflow: no allocation */
    void *p = eita_rv32_malloc(total);
    if (p) memset(p, 0, total);
    return p;
}

/* --- the loud stops ------------------------------------------------------ */
EITA_SHIM void abort(void) { eita_rv32_abort("eita: abort"); }

/* `stderr` is a token: nothing reads it, the hook decides where text goes. */
struct EitaRv32File { int unused; };
static struct EitaRv32File eita_rv32_stderr_obj;
EITA_SHIM FILE *stderr = &eita_rv32_stderr_obj;

EITA_SHIM int fputs(const char *s, FILE *stream) { (void)stream; eita_rv32_log(s); return 0; }

/* Does NOT format — logs the format string and drops the arguments. Every call
   site is an abort path where the string names the failure. */
EITA_SHIM int fprintf(FILE *stream, const char *fmt, ...) {
    (void)stream; eita_rv32_log(fmt); return 0;
}
