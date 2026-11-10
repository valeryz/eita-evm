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

/* --- provided by the firmware ------------------------------------------- */
void *eita_rv32_malloc(size_t n);
void *eita_rv32_realloc(void *p, size_t n);
void  eita_rv32_free(void *p);
void  eita_rv32_abort(const char *why) __attribute__((noreturn));
void  eita_rv32_log(const char *msg);

/* --- memory ------------------------------------------------------------- */
void *memcpy(void *dst, const void *src, size_t n) {
    unsigned char *d = dst; const unsigned char *s = src;
    for (size_t i = 0; i < n; i++) d[i] = s[i];
    return dst;
}

void *memmove(void *dst, const void *src, size_t n) {
    unsigned char *d = dst; const unsigned char *s = src;
    if (d < s) { for (size_t i = 0; i < n; i++) d[i] = s[i]; }
    else { for (size_t i = n; i > 0; i--) d[i - 1] = s[i - 1]; }
    return dst;
}

void *memset(void *dst, int c, size_t n) {
    unsigned char *d = dst;
    for (size_t i = 0; i < n; i++) d[i] = (unsigned char)c;
    return dst;
}

int memcmp(const void *a, const void *b, size_t n) {
    const unsigned char *x = a, *y = b;
    for (size_t i = 0; i < n; i++) if (x[i] != y[i]) return (int)x[i] - (int)y[i];
    return 0;
}

/* --- allocation: the host's ---------------------------------------------- */
void *malloc(size_t n) { return eita_rv32_malloc(n); }
void  free(void *p) { eita_rv32_free(p); }
void *realloc(void *p, size_t n) { return eita_rv32_realloc(p, n); }

void *calloc(size_t n, size_t sz) {
    size_t total = n * sz;
    if (sz != 0 && total / sz != n) return 0;      /* overflow: no allocation */
    void *p = eita_rv32_malloc(total);
    if (p) memset(p, 0, total);
    return p;
}

/* --- the loud stops ------------------------------------------------------ */
void abort(void) { eita_rv32_abort("eita: abort"); }

/* `stderr` is a token: nothing reads it, the hook decides where text goes. */
struct EitaRv32File { int unused; };
static struct EitaRv32File eita_rv32_stderr_obj;
FILE *stderr = &eita_rv32_stderr_obj;

int fputs(const char *s, FILE *stream) { (void)stream; eita_rv32_log(s); return 0; }

/* Does NOT format — logs the format string and drops the arguments. Every call
   site is an abort path where the string names the failure. */
int fprintf(FILE *stream, const char *fmt, ...) {
    (void)stream; eita_rv32_log(fmt); return 0;
}
