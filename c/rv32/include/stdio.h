/* stdio.h — the abort-path logging only; `fprintf` does NOT format, it logs
   its format string (../README.md says why). */
#ifndef EITA_RV32_STDIO_H
#define EITA_RV32_STDIO_H
#ifndef NULL
#define NULL ((void *)0)
#endif
typedef struct EitaRv32File FILE;
extern FILE *stderr;
int fputs(const char *s, FILE *stream);
int fprintf(FILE *stream, const char *fmt, ...);
#endif
