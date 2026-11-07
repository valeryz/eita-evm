/*
 * storage_host.h — the native SLOAD path's host (docs/native-storage.md, owner note 6 step 3).
 *
 * The native SLOAD and SSTORE callbacks (eita_cb_sload / eita_cb_sstore, in the callbacks
 * vtable's slots 0 and 1) run the effects EMITTED from the effect IR (c/generated/storage_effect.c, lean/Evm/CL/EffectC.lean)
 * against the native slot tables (world_slots.h) and the native per-tx state (tx_state.h),
 * and falls back to the Lisp callback (the Lisp printing of the same term, with the
 * fault-in and the hooks) when:
 *   - the fast path is off (h->enabled: bit 0 SLOAD, bit 1 SSTORE; both off under an
 *     observer, the read stream, the differential's reference tier, EITA_NATIVE_STORAGE=0;
 *     SSTORE off while the incremental root checker tracks dirty slots), or
 *   - the frame's account has no id in the cache yet (the Lisp path fills it), or
 *   - the slot is not in the native table (a miss: the emitted effect returns
 *     EITA_SH_MISS before any effect, and the Lisp effect runs it whole).
 * One writer: the replay thread. Lisp sets ws / fork / enabled at every frame entry
 * (src/evm/interp.lisp run-frame) by plain stores into eita_sh_g.
 */
#ifndef EITA_STORAGE_HOST_H
#define EITA_STORAGE_HOST_H
#include <stdint.h>
#include "world_slots.h"
#include "tx_state.h"
#include "generated/limb_ops.h"

#define EITA_SH_MISS UINT64_MAX
#define EITA_SH_CACHE 64
#define EITA_SH_WATCH 16

typedef uint64_t (*eita_sh_sload_fn)(void *ctx, const u256_t *addr, const u256_t *slot, u256_t *out);
typedef uint64_t (*eita_sh_sstore_fn)(void *ctx, const u256_t *addr, const u256_t *slot, const u256_t *val);

typedef struct eita_sh {
  /* set by Lisp (offsets 0..40, src/evm/storage-host.lisp) */
  ws_world *ws;                 /*  0: the current world's slot tables */
  TxState *ts;                  /*  8 */
  uint64_t fork;                /* 16: Fork.ord */
  uint64_t enabled;             /* 24: bit 0 SLOAD, bit 1 SSTORE */
  eita_sh_sload_fn lisp_sload;  /* 32: the Lisp callbacks (the slow paths) */
  uint64_t hits, misses;        /* 40, 48: SLOAD */
  eita_sh_sstore_fn lisp_sstore;/* 56 */
  uint64_t sstore_hits, sstore_misses;  /* 64, 72 */
  uint64_t keep_zero;           /* 80: *keep-zero-slots*: a slot set to 0 stays present */
  /* the observers' first-touch log (bit 2 of enabled: an observer is installed): every slot
     the tx touches, once, in first-touch order, with its value then; one owner for the
     native and the Lisp paths (eita_sh_touch), read at tx end (do-storage-changes) */
  ws_world *touch_seen;
  struct eita_touch { u256_t addr, key, val; } *touch_log;
  uint64_t touch_n, touch_cap;
  /* the watch filter (tier (b)): accounts whose every SLOAD/SSTORE takes the Lisp path,
     where *storage-access-hook* sees it; empty in normal runs */
  uint64_t watch_n;
  u256_t watch[EITA_SH_WATCH];
  /* per call */
  TxArena *ar;
  uint64_t id;
  u256_t addr, key, val;
  const uint64_t *slot;
  /* the frame accounts' ids: (address -> id + 1), valid while cache_serial == ws->serial */
  uint64_t cache_serial;
  struct { uint64_t a0, a1, a2, id1; } cache[EITA_SH_CACHE];
} eita_sh;

extern eita_sh eita_sh_g;

/* The primitives the emitted effect calls (EffectC's table). */
void eita_sh_touch(uint64_t id, const u256_t *addr, const u256_t *key, const uint64_t *val);
static inline int eita_sh_hit(eita_sh *h) {
  h->slot = eita_ws_get(h->ws, h->id, h->key.limb[0], h->key.limb[1], h->key.limb[2], h->key.limb[3]);
  if (h->slot && (h->enabled & 4)) eita_sh_touch(h->id, &h->addr, &h->key, h->slot);   /* fault-slot!'s */
  return h->slot != 0;
}
static inline void eita_sh_sload(const eita_sh *h, uint64_t *x) { limb_copy(x, h->slot); }
static inline int eita_sh_access_slot(eita_sh *h) {
  return eita_ts_access_slot(h->ts, h->ar, &h->addr, &h->key) == 1;   /* 1: newly warmed = cold */
}
static inline void eita_sh_orig_record(eita_sh *h, const uint64_t *cur) {
  eita_ts_orig_record(h->ts, &h->addr, &h->key, (const u256_t *)cur);
}

static inline void eita_sh_orig_get(const eita_sh *h, const uint64_t *cur, uint64_t *out) {
  eita_ts_orig_get(h->ts, &h->addr, &h->key, (const u256_t *)cur, (u256_t *)out);
}
/* The fork's SSTORE schedule (emitted dispatch): sets the refund counter (journaled) and
   returns the cost. */
uint64_t eita_sh_sstore_gas(eita_sh *h, const uint64_t *orig, const uint64_t *cur, const uint64_t *nv, int cold);
/* (self, key) := W, journaled (type 0, the old value: the slot's current one). */
void eita_sh_set_storage(eita_sh *h, const uint64_t *w);

uint64_t eita_spec_sload_effect(eita_sh *h, uint64_t *out);   /* emitted */
uint64_t eita_spec_sstore_effect(eita_sh *h);                 /* emitted */
void eita_spec_sstore_plan(uint64_t fork, uint64_t *out, uint64_t refund, const u256_t *orig,
                           const u256_t *cur, const u256_t *nv, uint64_t cold);   /* emitted */
/* A revert's SSTORE entries, natively: from ARENA's newest entry down to TARGET, every type-0
   entry of an account with a known id is restored into the slot table (as the Lisp restore:
   world-storage-set of the old value) and retyped EITA_J_SSTORE_DONE, which the host loop and
   eita_ts_revert skip. Stops at the first un-create entry (type 10: it drops the account's
   whole table, so the entries below it must be replayed after it, in order: by the host). */
#define EITA_J_SSTORE_DONE 255
/* The first-touch log: Lisp's entry (scalars), its reset at tx start, its length and entries. */
void eita_sh_touch_l(uint64_t id, uint64_t a0, uint64_t a1, uint64_t a2, uint64_t k0, uint64_t k1,
                     uint64_t k2, uint64_t k3, uint64_t v0, uint64_t v1, uint64_t v2, uint64_t v3);
void eita_sh_touch_reset(void);
/* The watch filter: add an account (an address: 160 bits; 0 when full), or empty it. */
uint64_t eita_sh_watch(uint64_t a0, uint64_t a1, uint64_t a2);
void eita_sh_watch_clear(void);
uint64_t eita_sh_touch_count(void);
const struct eita_touch *eita_sh_touch_at(uint64_t i);
void eita_sh_revert_storage(TxArena *ar, uint64_t target);
uint64_t eita_cb_sload(void *ctx, const u256_t *addr, const u256_t *slot, u256_t *out);
uint64_t eita_cb_sstore(void *ctx, const u256_t *addr, const u256_t *slot, const u256_t *val);
/* The Lisp path, after its SLOAD of ADDR (an address: 160 bits), records ADDR's id. */
void eita_sh_cache_put(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t id);
#endif
