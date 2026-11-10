/* stdlib.h — allocation forwarded to the host's allocator (../README.md). */
#ifndef EITA_RV32_STDLIB_H
#define EITA_RV32_STDLIB_H
typedef __SIZE_TYPE__ size_t;
#ifndef NULL
#define NULL ((void *)0)
#endif
void *malloc(size_t n);
void *calloc(size_t n, size_t sz);
void *realloc(void *p, size_t n);
void  free(void *p);
void  abort(void) __attribute__((noreturn));
#endif
