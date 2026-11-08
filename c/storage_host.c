/* storage_host.c — SLOAD and SSTORE (storage_host.h). */
#include "storage_host.h"
#include <string.h>
#include <stdio.h>
#include <stdlib.h>

eita_sh eita_sh_g;

static void cache_check(eita_sh *h) {
  if (h->cache_serial != h->ws->serial) { memset(h->cache, 0, sizeof h->cache); h->cache_serial = h->ws->serial; }
}

/* Bind the frame account and the key for the effect: the account's id from the cache, or
   learned from Lisp (and cached) the first time the address is seen under this world. */
static void bind(eita_sh *h, void *ctx, const u256_t *addr, const u256_t *slot) {
  if (!h->ws) { fputs("eita_sh: SLOAD/SSTORE with no world\n", stderr); abort(); }
  /* the address as read-addr reads it: the low 160 bits */
  uint64_t a0 = addr->limb[0], a1 = addr->limb[1], a2 = addr->limb[2] & 0xFFFFFFFFu;
  h->ar = ctx;
  h->addr.limb[0] = a0; h->addr.limb[1] = a1; h->addr.limb[2] = a2; h->addr.limb[3] = 0;
  h->key = *slot;
  h->watched = 0;
  for (uint64_t w = 0; w < h->watch_n; w++)
    if (h->watch[w].limb[0] == a0 && h->watch[w].limb[1] == a1 && h->watch[w].limb[2] == a2) h->watched = 1;
  cache_check(h);
  const uint64_t i = a0 % EITA_SH_CACHE;
  if (!(h->cache[i].id1 && h->cache[i].a0 == a0 && h->cache[i].a1 == a1 && h->cache[i].a2 == a2)) {
    h->learns++;
    uint64_t id = h->learn(&h->addr);              /* interning may not move this world */
    cache_check(h);
    h->cache[i].a0 = a0; h->cache[i].a1 = a1; h->cache[i].a2 = a2; h->cache[i].id1 = id + 1;
  }
  h->id = h->cache[i].id1 - 1;
}

static const uint64_t zero4[4];

void eita_sh_fault(eita_sh *h) {
  const uint64_t *k = h->key.limb;
  h->slot = eita_ws_get(h->ws, h->id, k[0], k[1], k[2], k[3]);
  if (!h->slot && (h->flags & EITA_SH_LAZY)) {
    h->faults++;
    h->fault(&h->addr, &h->key);
    h->slot = eita_ws_get(h->ws, h->id, k[0], k[1], k[2], k[3]);
  }
  if (h->flags & EITA_SH_OBSERVE) eita_sh_touch(h->id, &h->addr, &h->key, h->slot ? h->slot : zero4);
}

void eita_sh_touch(uint64_t id, const u256_t *addr, const u256_t *key, const uint64_t *val) {
  eita_sh *h = &eita_sh_g;
  if (!h->touch_seen) h->touch_seen = eita_ws_new();
  if (eita_ws_get(h->touch_seen, id, key->limb[0], key->limb[1], key->limb[2], key->limb[3])) return;
  eita_ws_put(h->touch_seen, id, key->limb[0], key->limb[1], key->limb[2], key->limb[3], 1, 0, 0, 0);
  if (h->touch_n == h->touch_cap) {
    uint64_t cap = h->touch_cap ? 2 * h->touch_cap : 256;
    struct eita_touch *l = realloc(h->touch_log, cap * sizeof *l);
    if (!l) { fputs("eita_sh: out of memory\n", stderr); abort(); }
    h->touch_log = l; h->touch_cap = cap;
  }
  struct eita_touch *t = &h->touch_log[h->touch_n++];
  t->addr = *addr; t->key = *key;
  limb_copy(t->val.limb, val);
}

void eita_sh_touch_l(uint64_t id, uint64_t a0, uint64_t a1, uint64_t a2, uint64_t k0, uint64_t k1,
                     uint64_t k2, uint64_t k3, uint64_t v0, uint64_t v1, uint64_t v2, uint64_t v3) {
  const u256_t a = {{a0, a1, a2, 0}}, k = {{k0, k1, k2, k3}};
  const uint64_t v[4] = {v0, v1, v2, v3};
  eita_sh_touch(id, &a, &k, v);
}

void eita_sh_touch_reset(void) {
  eita_sh *h = &eita_sh_g;
  if (h->touch_n) { eita_ws_free(h->touch_seen); h->touch_seen = 0; h->touch_n = 0; }
}

uint64_t eita_sh_watch(uint64_t a0, uint64_t a1, uint64_t a2) {
  eita_sh *h = &eita_sh_g;
  if (h->watch_n == EITA_SH_WATCH) return 0;
  h->watch[h->watch_n].limb[0] = a0; h->watch[h->watch_n].limb[1] = a1;
  h->watch[h->watch_n].limb[2] = a2; h->watch[h->watch_n].limb[3] = 0;
  h->watch_n++;
  return 1;
}
void eita_sh_watch_clear(void) { eita_sh_g.watch_n = 0; }

uint64_t eita_sh_touch_count(void) { return eita_sh_g.touch_n; }
const struct eita_touch *eita_sh_touch_at(uint64_t i) { return &eita_sh_g.touch_log[i]; }

static int lookup(eita_sh *h, const u256_t *addr, uint64_t *id) {
  uint64_t a0 = addr->limb[0], a1 = addr->limb[1], a2 = addr->limb[2] & 0xFFFFFFFFu;
  const uint64_t i = a0 % EITA_SH_CACHE;
  if (!(h->cache[i].id1 && h->cache[i].a0 == a0 && h->cache[i].a1 == a1 && h->cache[i].a2 == a2)) return 0;
  *id = h->cache[i].id1 - 1;
  return 1;
}

void eita_sh_revert_storage(TxArena *ar, uint64_t target) {
  eita_sh *h = &eita_sh_g;
  if ((h->flags & EITA_SH_VIEW) || !h->ws) return;
  cache_check(h);
  for (uint64_t n = ar->journal_count; n > target; n--) {
    JournalEntry *j = &ar->journal_data[n - 1];
    uint64_t id;
    if (j->entry_type == 10) return;
    if (j->entry_type != 0 || !lookup(h, &j->addr, &id)) continue;
    const uint64_t *k = j->key.limb, *v = j->old_val.limb;
    if (!h->keep_zero && limb_is_zero(v)) eita_ws_remove(h->ws, id, k[0], k[1], k[2], k[3]);
    else eita_ws_put(h->ws, id, k[0], k[1], k[2], k[3], v[0], v[1], v[2], v[3]);
    j->entry_type = EITA_J_SSTORE_DONE;
  }
}

uint64_t eita_cb_sload(void *ctx, const u256_t *addr, const u256_t *slot, u256_t *out) {
  eita_sh *h = &eita_sh_g;
  bind(h, ctx, addr, slot);
  h->sloads++;
  uint64_t g = eita_spec_sload_effect(h, out->limb);
  if ((h->flags & EITA_SH_VIEW) || h->watched) h->hook(0, &h->addr, &h->key, out, &h->cur);
  return g;
}

uint64_t eita_cb_sstore(void *ctx, const u256_t *addr, const u256_t *slot, const u256_t *val) {
  eita_sh *h = &eita_sh_g;
  bind(h, ctx, addr, slot);
  h->val = *val;
  h->sstores++;
  uint64_t g = eita_spec_sstore_effect(h);
  if ((h->flags & EITA_SH_VIEW) || h->watched ||
      ((h->flags & EITA_SH_DIRTY) && !limb_eq(h->val.limb, h->cur.limb)))
    h->hook(1, &h->addr, &h->key, &h->val, &h->cur);
  return g;
}

uint64_t eita_sh_sstore_gas(eita_sh *h, const uint64_t *orig, const uint64_t *cur, const uint64_t *nv, int cold) {
  uint64_t out[2], refund = (uint64_t)h->ts->refund_counter;
  eita_spec_sstore_plan(h->fork, out, refund, (const u256_t *)orig, (const u256_t *)cur, (const u256_t *)nv,
                        cold ? 1 : 0);
  int64_t d = (int64_t)(out[1] - refund);      /* as the Lisp: (- new-refund (ts-refund)) */
  if (d != 0) eita_ts_refund_add(h->ts, h->ar, d);
  return out[0];
}

void eita_sh_set_storage(eita_sh *h, const uint64_t *w) {
  /* the journal entry first (journal-push!'s layout): the old value is the slot's current
     one, read before the write can move the table */
  JournalEntry *j = &h->ar->journal_data[h->ar->journal_count++];
  j->entry_type = 0;
  j->addr = h->addr; j->key = h->key;
  limb_copy(j->old_val.limb, h->cur.limb);
  if (!h->keep_zero && limb_is_zero(w))           /* world-storage-set: a full world drops zeros */
    eita_ws_remove(h->ws, h->id, h->key.limb[0], h->key.limb[1], h->key.limb[2], h->key.limb[3]);
  else
    eita_ws_put(h->ws, h->id, h->key.limb[0], h->key.limb[1], h->key.limb[2], h->key.limb[3],
                w[0], w[1], w[2], w[3]);
}
