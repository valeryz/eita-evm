/*
 * storage_host.h — the native SLOAD path's host (docs/native-storage.md, owner note 6 step 3).
 *
 * The native SLOAD callback (eita_cb_sload, in the callbacks vtable's SLOAD slot) runs the
 * effect EMITTED from the effect IR (c/generated/storage_effect.c, lean/Evm/CL/EffectC.lean)
 * against the native slot tables (world_slots.h) and the native per-tx state (tx_state.h),
 * and falls back to the Lisp callback (the Lisp printing of the same term, with the
 * fault-in and the hooks) when:
 *   - the fast path is off (h->enabled = 0: an observer, the read stream, the differential's
 *     reference tier, EITA_NATIVE_STORAGE=0), or
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

typedef uint64_t (*eita_sh_sload_fn)(void *ctx, const u256_t *addr, const u256_t *slot, u256_t *out);

typedef struct eita_sh {
  /* set by Lisp (offsets 0..40, src/evm/storage-host.lisp) */
  ws_world *ws;                 /*  0: the current world's slot tables */
  TxState *ts;                  /*  8 */
  uint64_t fork;                /* 16: Fork.ord */
  uint64_t enabled;             /* 24 */
  eita_sh_sload_fn lisp_sload;  /* 32: the Lisp callback (the slow path) */
  uint64_t hits, misses;        /* 40, 48 */
  /* per call */
  TxArena *ar;
  uint64_t id;
  u256_t addr, key;
  const uint64_t *slot;
  /* the frame accounts' ids: (address -> id + 1), valid while cache_serial == ws->serial */
  uint64_t cache_serial;
  struct { uint64_t a0, a1, a2, id1; } cache[EITA_SH_CACHE];
} eita_sh;

extern eita_sh eita_sh_g;

/* The primitives the emitted effect calls (EffectC's table). */
static inline int eita_sh_hit(eita_sh *h) {
  h->slot = eita_ws_get(h->ws, h->id, h->key.limb[0], h->key.limb[1], h->key.limb[2], h->key.limb[3]);
  return h->slot != 0;
}
static inline void eita_sh_sload(const eita_sh *h, uint64_t *x) { limb_copy(x, h->slot); }
static inline int eita_sh_access_slot(eita_sh *h) {
  return eita_ts_access_slot(h->ts, h->ar, &h->addr, &h->key) == 1;   /* 1: newly warmed = cold */
}
static inline void eita_sh_orig_record(eita_sh *h, const uint64_t *cur) {
  eita_ts_orig_record(h->ts, &h->addr, &h->key, (const u256_t *)cur);
}

uint64_t eita_spec_sload_effect(eita_sh *h, uint64_t *out);   /* emitted */
uint64_t eita_cb_sload(void *ctx, const u256_t *addr, const u256_t *slot, u256_t *out);
/* The Lisp path, after its SLOAD of ADDR (an address: 160 bits), records ADDR's id. */
void eita_sh_cache_put(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t id);
#endif
