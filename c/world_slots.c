/* world_slots.c — the world's storage slots (world_slots.h; docs/native-storage.md), glue over
 * the Velvet-emitted table in world_slots_emit.c.
 *
 * Every table decision is in world_slots_emit.c (generated, do not edit), printed from Velvet
 * methods proved for every capacity against the slot-table model (lean/Evm/CL/WorldSlotsModel.lean;
 * the proofs live in Eita's separate velvet-slots package, to be published): the probe and its
 * insertion index, place, the load test, the growth rule, the rehash, remove, the walk step, the
 * 4-entry fresh table, the directory size rule, the array copy, and both abort conditions
 * (WS_MAX_CAP, the 2^40 id limit). This file is the trusted glue (docs/trusted-surface.md), mirrored
 * in that package's world-level proofs: it unpacks a ws_slots into the emitted functions' arguments
 * and stores their results back, frees the arrays a grow replaced (the emitted functions never
 * free), keeps the directory's pointer array (allocate, copy the old pointers, free), and calls the
 * map callback. ws_place / ws_grow stay statics for the CBMC harness (cbmc/world_slots_harness.c).
 * Core's copy is byte-identical to the package's; the package's drift check diffs the two.
 */
#include "world_slots.h"
#include "world_slots_emit.c"

#ifndef WS_DIR_MIN
#define WS_DIR_MIN 256   /* the first directory size (the CBMC harness makes it small) */
#endif

/* Zeroed memory or abort; a macro so that each allocation is its own call site with its
   element type in the size expression (CBMC types heap objects by site and `n * sizeof(T)`). */
#define ws_alloc(n, size) vv_zeroed(malloc((n) * (size)), (n) * (size))

/* T's fields := an emitted function's results; free the arrays they replaced. */
static void ws_set(ws_slots *t, uint64_t cap, uint64_t *words, uint8_t *state, uint64_t count,
                   uint64_t used) {
  if (words != t->words) free(t->words);
  if (state != t->state) free(t->state);
  t->cap = cap; t->words = words; t->state = state; t->count = count; t->used = used;
}

static ws_slots *ws_slots_new(void) {
  ws_slots *t = ws_alloc(1, sizeof *t);
  struct ret_vv_fresh r = vv_fresh();
  t->cap = r.f0; t->words = r.f1; t->state = r.f2;
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
  uint64_t n = vv_dirGrow(w->n, id, WS_DIR_MIN);   /* aborts past the id limit */
  if (n != w->n) {
    ws_slots **a = ws_alloc(n, sizeof *a);
    if (w->n) memcpy(a, w->acct, w->n * sizeof *a);
    free(w->acct);
    w->acct = a; w->n = n;
  }
  if (!w->acct[id]) w->acct[id] = ws_slots_new();
  return w->acct[id];
}

int64_t eita_ws_probe(const ws_slots *t, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3) {
  struct ret_vv_find r = vv_find(t->cap, t->words, t->state, k0, k1, k2, k3);
  return r.f0 ? (int64_t)r.f1 : -1 - (int64_t)r.f1;
}

const uint64_t *eita_ws_get(const ws_world *w, uint64_t id,
                            uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3) {
  const ws_slots *t = eita_ws_table(w, id);
  if (!t) return NULL;
  struct ret_vv_lookup r = vv_lookup(t->cap, t->words, t->state, t->count, t->used, k0, k1, k2, k3);
  return r.f0 ? t->words + 8 * r.f1 + 4 : NULL;
}

/* KEY := VALUE in T, which has room (used + 1 < cap). (ws_place and ws_grow are put's two halves,
   kept as functions for the CBMC harness, which proves them one by one.) */
__attribute__((unused)) static void ws_place(ws_slots *t, const uint64_t *k, const uint64_t *v) {
  struct ret_vv_place r = vv_place(t->cap, t->words, t->state, t->count, t->used,
                                   k[0], k[1], k[2], k[3], v[0], v[1], v[2], v[3]);
  ws_set(t, t->cap, r.f0, r.f1, r.f2, r.f3);
}

/* The rehash a put does when the load test fails. */
__attribute__((unused)) static void ws_grow(ws_slots *t) {
  struct ret_vv_grow r = vv_grow(t->cap, t->words, t->state, t->count, t->used, WS_MAX_CAP);
  ws_set(t, r.f0, r.f1, r.f2, r.f3, r.f4);
}

void eita_ws_put(ws_world *w, uint64_t id, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3,
                 uint64_t v0, uint64_t v1, uint64_t v2, uint64_t v3) {
  ws_slots *t = eita_ws_touch(w, id);
  struct ret_vv_put r = vv_put(t->cap, t->words, t->state, t->count, t->used,
                               k0, k1, k2, k3, v0, v1, v2, v3, WS_MAX_CAP);
  ws_set(t, r.f0, r.f1, r.f2, r.f3, r.f4);
}

void eita_ws_remove(ws_world *w, uint64_t id, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3) {
  ws_slots *t = eita_ws_touch(w, id);
  struct ret_vv_remove r = vv_remove(t->cap, t->words, t->state, t->count, k0, k1, k2, k3);
  ws_set(t, t->cap, t->words, r.f0, r.f1, t->used);
}

void eita_ws_drop(ws_world *w, uint64_t id) {
  if (id < w->n) { ws_slots_free(w->acct[id]); w->acct[id] = NULL; }
}

void eita_ws_copy(ws_world *dst, uint64_t id, const ws_slots *src) {
  eita_ws_drop(dst, id);
  if (!src) return;
  ws_slots *t = eita_ws_touch(dst, id);
  struct ret_vv_copyArrs r = vv_copyArrs(src->cap, src->words, src->state);
  ws_set(t, src->cap, r.f0, r.f1, src->count, src->used);
}

void eita_ws_map(const ws_world *w, uint64_t id,
                 void (*fn)(const uint64_t *key, const uint64_t *val, void *ctx), void *ctx) {
  const ws_slots *t = eita_ws_table(w, id);
  if (!t) return;
  for (uint64_t i = vv_next(t->cap, t->state, 0); i < t->cap; i = vv_next(t->cap, t->state, i + 1))
    fn(t->words + 8 * i, t->words + 8 * i + 4, ctx);
}
