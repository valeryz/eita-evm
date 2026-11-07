/* world_slots.c — the world's storage slots (world_slots.h; docs/native-storage.md). */
#include "world_slots.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef WS_DIR_MIN
#define WS_DIR_MIN 256   /* the first directory size (the CBMC harness makes it small) */
#endif

/* Zeroed memory or abort. A macro, so that each allocation is its own call site with its
   element type in the size expression: CBMC tells heap objects apart by allocation site
   and types them from `n * sizeof(T)` (cbmc/world_slots_harness.c). n * size cannot
   overflow: n <= 2^41 (a directory, WS_MAX_CAP for a table), size <= 64. */
static void *ws_zeroed(void *p, uint64_t bytes) {
  if (!p) { fputs("eita_ws: out of memory\n", stderr); abort(); }
  memset(p, 0, bytes);
  return p;
}
#define ws_alloc(n, size) ws_zeroed(malloc((n) * (size)), (n) * (size))

/* The Lisp table's hash (slots-hash): ((k0 * golden) + k1) >> 17, masked. */
static inline uint64_t ws_hash(uint64_t k0, uint64_t k1, uint64_t mask) {
  return ((k0 * UINT64_C(0x9E3779B97F4A7C15) + k1) >> 17) & mask;
}

static ws_slots *ws_slots_new(uint64_t cap) {
  ws_slots *t = ws_alloc(1, sizeof *t);
  t->cap = cap;
  t->words = ws_alloc(cap, 8 * sizeof(uint64_t));
  t->state = ws_alloc(cap, 1);
  return t;
}

static void ws_slots_free(ws_slots *t) {
  if (!t) return;
  free(t->words); free(t->state); free(t);
}

ws_world *eita_ws_new(void) {
  static uint64_t serial;
  ws_world *w = ws_alloc(1, sizeof(ws_world));
  w->serial = ++serial;
  return w;
}

void eita_ws_free(ws_world *w) {
  if (!w) return;
  for (uint64_t i = 0; i < w->n; i++) ws_slots_free(w->acct[i]);
  free(w->acct); free(w);
}

ws_slots *eita_ws_table(const ws_world *w, uint64_t id) {
  return id < w->n ? w->acct[id] : NULL;
}

ws_slots *eita_ws_touch(ws_world *w, uint64_t id) {
  if (id >= w->n) {
    if (id >= (UINT64_C(1) << 40)) { fputs("eita_ws: account id out of range\n", stderr); abort(); }
    uint64_t n = w->n ? 2 * w->n : WS_DIR_MIN;
    while (n <= id) n *= 2;
    ws_slots **a = ws_alloc(n, sizeof *a);
    if (w->n) memcpy(a, w->acct, w->n * sizeof *a);
    free(w->acct);
    w->acct = a; w->n = n;
  }
  if (!w->acct[id]) w->acct[id] = ws_slots_new(4);
  return w->acct[id];
}

int64_t eita_ws_probe(const ws_slots *t, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3) {
  uint64_t mask = t->cap - 1, i = ws_hash(k0, k1, mask);
  int64_t tomb = -1;
  /* Terminates: used < cap (the 3/4 rule), so an empty entry is on every probe path. */
  for (;;) {
    uint8_t st = t->state[i];
    if (st == 0) return -1 - (tomb >= 0 ? tomb : (int64_t)i);
    if (st == 2) { if (tomb < 0) tomb = (int64_t)i; }
    else {
      const uint64_t *e = t->words + 8 * i;
      if (e[0] == k0 && e[1] == k1 && e[2] == k2 && e[3] == k3) return (int64_t)i;
    }
    i = (i + 1) & mask;
  }
}

const uint64_t *eita_ws_get(const ws_world *w, uint64_t id,
                            uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3) {
  const ws_slots *t = eita_ws_table(w, id);
  if (!t) return NULL;
  int64_t i = eita_ws_probe(t, k0, k1, k2, k3);
  return i < 0 ? NULL : t->words + 8 * (uint64_t)i + 4;
}

/* KEY := VALUE in T, which has room (used + 1 < cap). */
static void ws_place(ws_slots *t, const uint64_t *k, const uint64_t *v) {
  int64_t i = eita_ws_probe(t, k[0], k[1], k[2], k[3]);
  if (i < 0) {
    i = -1 - i;
    if (t->state[i] == 0) t->used++;
    t->state[i] = 1;
    t->count++;
    uint64_t *e = t->words + 8 * (uint64_t)i;
    e[0] = k[0]; e[1] = k[1]; e[2] = k[2]; e[3] = k[3];
  }
  uint64_t *e = t->words + 8 * (uint64_t)i + 4;
  e[0] = v[0]; e[1] = v[1]; e[2] = v[2]; e[3] = v[3];
}

/* The Lisp table's growth (slots-grow): double when over half the entries are present,
   else rehash at the same size (tombstones only). Entries are re-placed in table order;
   none can need a second growth (count <= 3/8 of the new capacity, or <= 1/2 of the same). */
static void ws_grow(ws_slots *t) {
  uint64_t old_cap = t->cap, cap = 2 * t->count > old_cap ? 2 * old_cap : old_cap;
  uint64_t *old_w = t->words; uint8_t *old_s = t->state;
  if (cap > WS_MAX_CAP) { fputs("eita_ws: table too large\n", stderr); abort(); }
  t->cap = cap; t->count = 0; t->used = 0;
  t->words = ws_alloc(cap, 8 * sizeof(uint64_t));
  t->state = ws_alloc(cap, 1);
  for (uint64_t i = 0; i < old_cap; i++)
    if (old_s[i] == 1) ws_place(t, old_w + 8 * i, old_w + 8 * i + 4);
  free(old_w); free(old_s);
}

static void ws_insert(ws_slots *t, const uint64_t *k, const uint64_t *v) {
  if (4 * (t->used + 1) >= 3 * t->cap) ws_grow(t);
  ws_place(t, k, v);
}

void eita_ws_put(ws_world *w, uint64_t id, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3,
                 uint64_t v0, uint64_t v1, uint64_t v2, uint64_t v3) {
  const uint64_t k[4] = {k0, k1, k2, k3}, v[4] = {v0, v1, v2, v3};
  ws_insert(eita_ws_touch(w, id), k, v);
}

void eita_ws_remove(ws_world *w, uint64_t id, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3) {
  ws_slots *t = eita_ws_touch(w, id);
  int64_t i = eita_ws_probe(t, k0, k1, k2, k3);
  if (i >= 0) { t->state[i] = 2; t->count--; }
}

void eita_ws_drop(ws_world *w, uint64_t id) {
  if (id < w->n) { ws_slots_free(w->acct[id]); w->acct[id] = NULL; }
}

void eita_ws_copy(ws_world *dst, uint64_t id, const ws_slots *src) {
  eita_ws_drop(dst, id);
  if (!src) return;
  ws_slots *t = eita_ws_touch(dst, id);
  free(t->words); free(t->state);
  *t = *src;
  t->words = ws_alloc(src->cap, 8 * sizeof(uint64_t));
  t->state = ws_alloc(src->cap, 1);
  memcpy(t->words, src->words, src->cap * 8 * sizeof(uint64_t));
  memcpy(t->state, src->state, src->cap);
}

void eita_ws_map(const ws_world *w, uint64_t id,
                 void (*fn)(const uint64_t *key, const uint64_t *val, void *ctx), void *ctx) {
  const ws_slots *t = eita_ws_table(w, id);
  if (!t) return;
  for (uint64_t i = 0; i < t->cap; i++)
    if (t->state[i] == 1) fn(t->words + 8 * i, t->words + 8 * i + 4, ctx);
}
