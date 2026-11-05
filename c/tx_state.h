/*
 * tx_state.h — native per-transaction transient state (Slice 3).
 *
 * Holds the EIP-2929 accessed sets, EIP-1153 transient storage, the
 * EIP-3529 refund counter, the EIP-6780 created-this-tx set, and the
 * EIP-2200 original-value snapshot — everything the Lisp host used to
 * keep in per-tx hash tables and that opcode handlers had to reach via
 * CFFI callbacks. One TxState is shared by every frame in a tx; the
 * world maps (storage/balance/code) stay host-owned.
 *
 * ## Tables
 *
 * Open addressing with linear probing, power-of-2 capacities, sized by
 * the host from the tx gas ceiling (every insert is gas-bounded, so a
 * correctly sized table cannot fill; inserts abort() if it ever does).
 * Occupancy is an epoch tag, not a bit: `entry.epoch == ts->epoch`
 * means live, anything else is empty. Per-tx reset is then O(1) —
 * bump ts->epoch — instead of a multi-MiB memset. Epoch 0 is reserved
 * (fresh tables are zeroed; ts->epoch starts at 1).
 *
 * ## Journaling and revert
 *
 * Per EELS, all of this state is scoped to the current call frame: a
 * reverting frame must restore the accessed sets, transient storage,
 * refund counter, and created set to their values at frame entry.
 * Every mutation therefore appends a JournalEntry (tx_arena.h) and
 * eita_ts_revert() replays entries in REVERSE order back to a saved
 * journal_count.
 *
 * Reverse-order removal is deletion-safe for linear probing without
 * tombstones: a key only probes past slots that were occupied when it
 * was inserted, so any key probing past slot S was inserted after the
 * key living at S. Reverting in reverse insertion order removes the
 * later key first — by the time S is cleared, no surviving key's probe
 * chain crosses it.
 *
 * The original-value snapshot is NOT journaled: "original" means the
 * value at tx start, which a revert does not change; a first-touch
 * record made inside a reverted frame remains correct.
 *
 * ## JournalEntry.entry_type registry (extends tx_arena.h)
 *
 *   0  sstore        host-replayed: restore world storage old_val
 *   1  tstore_old    native: restore tstorage[addr,key] = old_val
 *   2  balance       host-replayed: restore world balance
 *   3  selfdestruct  host-replayed
 *   4  access_addr   native: un-warm accessed_addrs slot
 *   5  access_slot   native: un-warm accessed_slots slot
 *   6  tstore_new    native: remove freshly inserted tstorage entry
 *   7  refund_set    native: refund_counter = (int64_t)old_val.limb[0]
 *   8  created_new   native: remove freshly inserted created entry
 *
 * For the native removal types (4/5/6/8) the table slot index is
 * stashed in old_val.limb[0]; addr/key keep the logical key for
 * debugging. eita_ts_revert handles the native types and skips the
 * host types — the host replays those over the same slice (in the
 * same reverse order) BEFORE calling eita_ts_revert, which rewinds
 * journal_count last.
 */

#ifndef EITA_TX_STATE_H
#define EITA_TX_STATE_H

#include <stdint.h>
#include <stddef.h>
#include "evm_state.h"
#include "tx_arena.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
    EITA_J_SSTORE       = 0,
    EITA_J_TSTORE_OLD   = 1,
    EITA_J_BALANCE      = 2,
    EITA_J_SELFDESTRUCT = 3,
    EITA_J_ACCESS_ADDR  = 4,
    EITA_J_ACCESS_SLOT  = 5,
    EITA_J_TSTORE_NEW   = 6,
    EITA_J_REFUND_SET   = 7,
    EITA_J_CREATED_NEW  = 8,
};

/* Set member keyed by one u256 (address). 40 bytes. */
typedef struct {
    uint64_t epoch;
    u256_t   key;
} TsAddrEntry;

/* Set member keyed by (address, slot). 72 bytes. */
typedef struct {
    uint64_t epoch;
    u256_t   addr;
    u256_t   key;
} TsSlotEntry;

/* Map entry (address, slot) -> value. 104 bytes. */
typedef struct {
    uint64_t epoch;
    u256_t   addr;
    u256_t   key;
    u256_t   val;
} TsKvEntry;

_Static_assert(sizeof(TsAddrEntry) == 40,  "TsAddrEntry size");
_Static_assert(sizeof(TsSlotEntry) == 72,  "TsSlotEntry size");
_Static_assert(sizeof(TsKvEntry)   == 104, "TsKvEntry size");

/* Counters first so handlers can reach them with one small-offset load.
 * Masks are capacity-1 (capacities are powers of two). */
typedef struct TxState {
    int64_t      refund_counter;  /* offset   0 */
    uint64_t     epoch;           /* offset   8 */
    uint64_t     addr_mask;       /* offset  16 */
    uint64_t     slot_mask;       /* offset  24 */
    uint64_t     tstore_mask;     /* offset  32 */
    uint64_t     created_mask;    /* offset  40 */
    uint64_t     orig_mask;       /* offset  48 */
    TsAddrEntry *accessed_addrs;  /* offset  56 */
    TsSlotEntry *accessed_slots;  /* offset  64 */
    TsKvEntry   *tstorage;        /* offset  72 */
    TsAddrEntry *created;         /* offset  80 */
    TsKvEntry   *originals;       /* offset  88 */
    uint64_t     addr_count;      /* offset  96 */
    uint64_t     slot_count;      /* offset 104 */
    uint64_t     tstore_count;    /* offset 112 */
    uint64_t     created_count;   /* offset 120 */
    uint64_t     orig_count;      /* offset 128 */
} TxState;                        /* 136 bytes */

_Static_assert(sizeof(TxState) == 136, "TxState must be 136 bytes");
_Static_assert(offsetof(TxState, refund_counter) == 0,   "TxState.refund_counter offset");
_Static_assert(offsetof(TxState, epoch)          == 8,   "TxState.epoch offset");
_Static_assert(offsetof(TxState, addr_mask)      == 16,  "TxState.addr_mask offset");
_Static_assert(offsetof(TxState, accessed_addrs) == 56,  "TxState.accessed_addrs offset");
_Static_assert(offsetof(TxState, accessed_slots) == 64,  "TxState.accessed_slots offset");
_Static_assert(offsetof(TxState, tstorage)       == 72,  "TxState.tstorage offset");
_Static_assert(offsetof(TxState, created)        == 80,  "TxState.created offset");
_Static_assert(offsetof(TxState, originals)      == 88,  "TxState.originals offset");

/* O(1) per-tx reset: bump the epoch, zero the counters. Table memory is
 * untouched (stale epochs read as empty). */
void eita_ts_reset(TxState *ts);

/* EIP-2929. Return 1 if cold (first access this frame-tree, insert +
 * journal), 0 if warm. */
uint64_t eita_ts_access_addr(TxState *ts, TxArena *ar, const u256_t *addr);
void eita_ts_access_addrs(TxState *ts, TxArena *ar, const u256_t *addrs, uint64_t n);
uint64_t eita_ts_access_slot(TxState *ts, TxArena *ar,
                             const u256_t *addr, const u256_t *slot);

/* EIP-1153. tload writes 0 to *out when absent. tstore journals the
 * old value (or the fresh insert) before overwriting. */
void eita_ts_tload (const TxState *ts, const u256_t *addr,
                    const u256_t *slot, u256_t *out);
void eita_ts_tstore(TxState *ts, TxArena *ar, const u256_t *addr,
                    const u256_t *slot, const u256_t *val);

/* EIP-3529 refund counter. Journals the PRE-delta value (absolute
 * restore on revert). delta may be negative. */
void eita_ts_refund_add(TxState *ts, TxArena *ar, int64_t delta);

/* EIP-6780 created-this-tx set. insert returns 1 if newly inserted
 * (journaled), 0 if already present. */
uint64_t eita_ts_created_insert(TxState *ts, TxArena *ar, const u256_t *addr);
uint64_t eita_ts_created_p(const TxState *ts, const u256_t *addr);

/* EIP-2200 original (tx-start) values. record is first-touch-only and
 * NOT journaled; get writes the recorded original, or *cur when the
 * slot has no record (i.e. current == original). */
void eita_ts_orig_record(TxState *ts, const u256_t *addr,
                         const u256_t *slot, const u256_t *cur);
void eita_ts_orig_get(const TxState *ts, const u256_t *addr,
                      const u256_t *slot, const u256_t *cur, u256_t *out);

/* Replay native journal entries (types 1/4/5/6/7/8) in reverse from
 * ar->journal_count down to target_count, then rewind journal_count to
 * target_count. Host-replayed types (0/2/3) are skipped — the host
 * must process those over the same slice BEFORE calling this. */
void eita_ts_revert(TxState *ts, TxArena *ar, uint64_t target_count);

#ifdef __cplusplus
}
#endif

#endif /* EITA_TX_STATE_H */
