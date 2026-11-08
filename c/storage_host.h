/*
 * storage_host.h — SLOAD and SSTORE (docs/native-storage.md, owner note 6 and its addendum 2).
 *
 * The callbacks vtable's slots 0 and 1 are eita_cb_sload / eita_cb_sstore, the one execution
 * path of the two opcodes: they run the effects EMITTED from the effect IR
 * (c/generated/storage_effect.c, lean/Evm/CL/EffectC.lean) against the native slot tables
 * (world_slots.h) and the native per-tx state (tx_state.h). Lisp is called only for data and
 * for observation, never to run an effect:
 *   - learn: the frame account's id, the first time an address is seen under a world (the
 *     address -> id cache, keyed by the world's serial);
 *   - fault: a key absent from the native table of a lazy world (flags bit 3: a fault hook is
 *     installed) is loaded through the world's fault hook, then read again (absent = zero);
 *   - hook: after the effect, one call per access when the read stream is on (bit 4: the
 *     storage view), for a watched account (the watch filter), and for an SSTORE that changed
 *     its slot while the incremental root checker tracks dirty slots (bit 5).
 * Bit 2: an observer is installed (the first-touch log). One writer: the replay thread. Lisp
 * sets ws / ts / fork / flags at every frame entry (storage-host-sync!) by plain stores into
 * eita_sh_g; the three Lisp callbacks once (calls.lisp alloc-callbacks).
 */
#ifndef EITA_STORAGE_HOST_H
#define EITA_STORAGE_HOST_H
#include <stdint.h>
#include "world_slots.h"
#include "tx_state.h"
#include "generated/limb_ops.h"

#define EITA_SH_CACHE 64
#define EITA_SH_WATCH 16

#define EITA_SH_OBSERVE 4      /* flags: an observer: enter first touches in the log */
#define EITA_SH_LAZY 8         /* a fault hook is installed: absent keys are faulted */
#define EITA_SH_VIEW 16        /* the read stream: hook every access; the revert is Lisp's */
#define EITA_SH_DIRTY 32       /* the root checker's dirty set: hook every changing SSTORE */

typedef uint64_t (*eita_sh_learn_fn)(const u256_t *addr);                  /* -> the id */
typedef void (*eita_sh_fault_fn)(const u256_t *addr, const u256_t *key);
typedef void (*eita_sh_hook_fn)(uint64_t op, const u256_t *addr, const u256_t *key,
                                const u256_t *val, const u256_t *cur);    /* op 0 SLOAD, 1 SSTORE */

typedef struct eita_sh {
  /* set by Lisp (offsets 0..88, src/evm/callbacks.lisp) */
  ws_world *ws;                 /*  0: the current world's slot tables */
  TxState *ts;                  /*  8 */
  uint64_t fork;                /* 16: Fork.ord */
  uint64_t flags;               /* 24: EITA_SH_* */
  eita_sh_learn_fn learn;       /* 32 */
  uint64_t sloads, faults;      /* 40, 48: SLOADs run; keys faulted in through Lisp */
  eita_sh_fault_fn fault;       /* 56 */
  uint64_t sstores, learns;     /* 64, 72: SSTOREs run; account ids learned from Lisp */
  uint64_t keep_zero;           /* 80: *keep-zero-slots*: a slot set to 0 stays present */
  eita_sh_hook_fn hook;         /* 88 */
  /* the observers' first-touch log (EITA_SH_OBSERVE: an observer is installed): every slot
     the tx touches, once, in first-touch order, with its value then; one owner for the
     native and the Lisp paths (eita_sh_touch), read at tx end (do-storage-changes) */
  ws_world *touch_seen;
  struct eita_touch { u256_t addr, key, val; } *touch_log;
  uint64_t touch_n, touch_cap;
  /* the watch filter (tier (b)): accounts whose every SLOAD/SSTORE calls the hook, where
     *storage-access-hook* sees it; empty in normal runs */
  uint64_t watch_n;
  u256_t watch[EITA_SH_WATCH];
  /* per call */
  TxArena *ar;
  uint64_t id, watched;
  u256_t addr, key, val, cur;   /* cur: the slot's value before the effect */
  const uint64_t *slot;         /* the key's entry, or 0 when absent (the value is zero) */
  /* the frame accounts' ids: (address -> id + 1), valid while cache_serial == ws->serial */
  uint64_t cache_serial;
  struct { uint64_t a0, a1, a2, id1; } cache[EITA_SH_CACHE];
} eita_sh;

extern eita_sh eita_sh_g;

/* The primitives the emitted effect calls (EffectC's table). */
void eita_sh_touch(uint64_t id, const u256_t *addr, const u256_t *key, const uint64_t *val);
/* faultSlot: the key's entry, faulted in first when absent from a lazy world; the first
   touch enters the observers' log (with the value then: zero when absent). */
void eita_sh_fault(eita_sh *h);
static inline void eita_sh_sload(eita_sh *h, uint64_t *x) {
  if (h->slot) limb_copy(x, h->slot); else x[0] = x[1] = x[2] = x[3] = 0;
  limb_copy(h->cur.limb, x);
}
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
/* (self, key) := W, journaled (type 0, the old value: the slot's current one, h->cur). */
void eita_sh_set_storage(eita_sh *h, const uint64_t *w);

uint64_t eita_spec_sload_effect(eita_sh *h, uint64_t *out);   /* emitted */
uint64_t eita_spec_sstore_effect(eita_sh *h);                 /* emitted */
void eita_spec_sstore_plan(uint64_t fork, uint64_t *out, uint64_t refund, const u256_t *orig,
                           const u256_t *cur, const u256_t *nv, uint64_t cold);   /* emitted */
/* A revert's SSTORE entries, natively: from ARENA's newest entry down to TARGET, every type-0
   entry of an account with a known id is restored into the slot table (as the Lisp restore:
   world-storage-set of the old value) and retyped EITA_J_SSTORE_DONE, which the host loop and
   eita_ts_revert skip. Stops at the first un-create entry (type 10: it drops the account's
   whole table, so the entries below it must be replayed after it, in order: by the host).
   Not while the read stream is on (EITA_SH_VIEW): the Lisp restore streams each write. */
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
#endif
