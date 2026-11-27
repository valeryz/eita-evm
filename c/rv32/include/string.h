/* string.h — the freestanding subset the engine uses (see ../README.md). */
#ifndef EITA_RV32_STRING_H
#define EITA_RV32_STRING_H
typedef __SIZE_TYPE__ size_t;
#ifndef NULL
#define NULL ((void *)0)
#endif
void *memcpy(void *dst, const void *src, size_t n);
void *memmove(void *dst, const void *src, size_t n);
void *memset(void *dst, int c, size_t n);
int   memcmp(const void *a, const void *b, size_t n);
#endif
