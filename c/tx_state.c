/* tx_state.c — see tx_state.h for the design notes. */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "tx_state.h"

/* Fibonacci hashing over the xor-fold of the limbs. Linear probing
 * only needs the high bits spread; one multiply does it. */
static inline uint64_t hash_u256(const u256_t *a) {
    uint64_t x = a->limb[0] ^ a->limb[1] ^ a->limb[2] ^ a->limb[3];
    x *= 0x9E3779B97F4A7C15ull;
    return x ^ (x >> 32);
}

static inline uint64_t hash_pair(const u256_t *a, const u256_t *k) {
    uint64_t x = a->limb[0] ^ a->limb[1] ^ a->limb[2] ^ a->limb[3]
               ^ (k->limb[0] * 0xC2B2AE3D27D4EB4Full)
               ^ k->limb[1] ^ k->limb[2] ^ k->limb[3];
    x *= 0x9E3779B97F4A7C15ull;
    return x ^ (x >> 32);
}

static inline int u256_eq(const u256_t *a, const u256_t *b) {
    return a->limb[0] == b->limb[0] && a->limb[1] == b->limb[1]
        && a->limb[2] == b->limb[2] && a->limb[3] == b->limb[3];
}

static void die(const char *what) {
    fprintf(stderr, "tx_state: %s — table sized below the gas bound?\n", what);
    abort();
}

static JournalEntry *jpush(TxArena *ar) {
    if (ar->journal_cap && ar->journal_count >= ar->journal_cap)
        die("journal overflow");
    return &ar->journal_data[ar->journal_count++];
}

void eita_ts_reset(TxState *ts) {
    ts->refund_counter = 0;
    ts->epoch++;
    ts->addr_count = ts->slot_count = ts->tstore_count = 0;
    ts->created_count = ts->orig_count = 0;
}

/* --- addr-keyed set probe (accessed_addrs, created) --- */

static TsAddrEntry *addr_probe(TsAddrEntry *tbl, uint64_t mask, uint64_t epoch,
                               const u256_t *key) {
    for (uint64_t i = hash_u256(key) & mask; ; i = (i + 1) & mask) {
        TsAddrEntry *e = &tbl[i];
        if (e->epoch != epoch || u256_eq(&e->key, key)) return e;
    }
}

static uint64_t addr_set_insert(TxState *ts, TxArena *ar,
                                TsAddrEntry *tbl, uint64_t mask,
                                uint64_t *count, uint64_t jtype,
                                const u256_t *key) {
    TsAddrEntry *e = addr_probe(tbl, mask, ts->epoch, key);
    if (e->epoch == ts->epoch) return 0;            /* warm / present */
    if (++*count * 2 > mask + 1) die("set overflow");
    e->epoch = ts->epoch;
    e->key = *key;
    JournalEntry *j = jpush(ar);
    j->entry_type = jtype;
    j->addr = *key;
    memset(&j->key, 0, sizeof j->key);
    memset(&j->old_val, 0, sizeof j->old_val);
    j->old_val.limb[0] = (uint64_t)(e - tbl);
    return 1;
}

uint64_t eita_ts_access_addr(TxState *ts, TxArena *ar, const u256_t *addr) {
    return addr_set_insert(ts, ar, ts->accessed_addrs, ts->addr_mask,
                           &ts->addr_count, EITA_J_ACCESS_ADDR, addr);
}

/* N addresses warmed in order, one crossing for the tx seed's precompiles (warm-tx-seed!). */
void eita_ts_access_addrs(TxState *ts, TxArena *ar, const u256_t *addrs, uint64_t n) {
    for (uint64_t i = 0; i < n; i++) eita_ts_access_addr(ts, ar, &addrs[i]);
}

uint64_t eita_ts_created_insert(TxState *ts, TxArena *ar, const u256_t *addr) {
    return addr_set_insert(ts, ar, ts->created, ts->created_mask,
                           &ts->created_count, EITA_J_CREATED_NEW, addr);
}

uint64_t eita_ts_created_p(const TxState *ts, const u256_t *addr) {
    TsAddrEntry *e = addr_probe(ts->created, ts->created_mask, ts->epoch, addr);
    return e->epoch == ts->epoch;
}

/* --- (addr, slot)-keyed set (accessed_slots) --- */

static TsSlotEntry *slot_probe(TsSlotEntry *tbl, uint64_t mask, uint64_t epoch,
                               const u256_t *addr, const u256_t *key) {
    for (uint64_t i = hash_pair(addr, key) & mask; ; i = (i + 1) & mask) {
        TsSlotEntry *e = &tbl[i];
        if (e->epoch != epoch ||
            (u256_eq(&e->addr, addr) && u256_eq(&e->key, key))) return e;
    }
}

uint64_t eita_ts_access_slot(TxState *ts, TxArena *ar,
                             const u256_t *addr, const u256_t *slot) {
    TsSlotEntry *e = slot_probe(ts->accessed_slots, ts->slot_mask, ts->epoch,
                                addr, slot);
    if (e->epoch == ts->epoch) return 0;
    if (++ts->slot_count * 2 > ts->slot_mask + 1) die("slot set overflow");
    e->epoch = ts->epoch;
    e->addr = *addr;
    e->key = *slot;
    JournalEntry *j = jpush(ar);
    j->entry_type = EITA_J_ACCESS_SLOT;
    j->addr = *addr;
    j->key = *slot;
    memset(&j->old_val, 0, sizeof j->old_val);
    j->old_val.limb[0] = (uint64_t)(e - ts->accessed_slots);
    return 1;
}

/* --- (addr, slot) -> value maps (tstorage, originals) --- */

static TsKvEntry *kv_probe(TsKvEntry *tbl, uint64_t mask, uint64_t epoch,
                           const u256_t *addr, const u256_t *key) {
    for (uint64_t i = hash_pair(addr, key) & mask; ; i = (i + 1) & mask) {
        TsKvEntry *e = &tbl[i];
        if (e->epoch != epoch ||
            (u256_eq(&e->addr, addr) && u256_eq(&e->key, key))) return e;
    }
}

void eita_ts_tload(const TxState *ts, const u256_t *addr,
                   const u256_t *slot, u256_t *out) {
    TsKvEntry *e = kv_probe(ts->tstorage, ts->tstore_mask, ts->epoch,
                            addr, slot);
    if (e->epoch == ts->epoch) *out = e->val;
    else memset(out, 0, sizeof *out);
}

void eita_ts_tstore(TxState *ts, TxArena *ar, const u256_t *addr,
                    const u256_t *slot, const u256_t *val) {
    TsKvEntry *e = kv_probe(ts->tstorage, ts->tstore_mask, ts->epoch,
                            addr, slot);
    JournalEntry *j = jpush(ar);
    j->addr = *addr;
    j->key = *slot;
    if (e->epoch == ts->epoch) {
        j->entry_type = EITA_J_TSTORE_OLD;
        j->old_val = e->val;
    } else {
        if (++ts->tstore_count * 2 > ts->tstore_mask + 1)
            die("tstorage overflow");
        j->entry_type = EITA_J_TSTORE_NEW;
        memset(&j->old_val, 0, sizeof j->old_val);
        j->old_val.limb[0] = (uint64_t)(e - ts->tstorage);
        e->epoch = ts->epoch;
        e->addr = *addr;
        e->key = *slot;
    }
    e->val = *val;
}

void eita_ts_orig_record(TxState *ts, const u256_t *addr,
                         const u256_t *slot, const u256_t *cur) {
    TsKvEntry *e = kv_probe(ts->originals, ts->orig_mask, ts->epoch,
                            addr, slot);
    if (e->epoch == ts->epoch) return;              /* already snapshotted */
    if (++ts->orig_count * 2 > ts->orig_mask + 1) die("originals overflow");
    e->epoch = ts->epoch;
    e->addr = *addr;
    e->key = *slot;
    e->val = *cur;
}

void eita_ts_orig_get(const TxState *ts, const u256_t *addr,
                      const u256_t *slot, const u256_t *cur, u256_t *out) {
    TsKvEntry *e = kv_probe(ts->originals, ts->orig_mask, ts->epoch,
                            addr, slot);
    *out = (e->epoch == ts->epoch) ? e->val : *cur;
}

/* --- refund counter --- */

void eita_ts_refund_add(TxState *ts, TxArena *ar, int64_t delta) {
    JournalEntry *j = jpush(ar);
    j->entry_type = EITA_J_REFUND_SET;
    memset(&j->addr, 0, sizeof j->addr);
    memset(&j->key, 0, sizeof j->key);
    memset(&j->old_val, 0, sizeof j->old_val);
    j->old_val.limb[0] = (uint64_t)ts->refund_counter;
    ts->refund_counter += delta;
}

/* --- revert --- */

void eita_ts_revert(TxState *ts, TxArena *ar, uint64_t target_count) {
    for (uint64_t n = ar->journal_count; n > target_count; n--) {
        JournalEntry *j = &ar->journal_data[n - 1];
        uint64_t idx = j->old_val.limb[0];
        switch (j->entry_type) {
        case EITA_J_TSTORE_OLD: {
            TsKvEntry *e = kv_probe(ts->tstorage, ts->tstore_mask, ts->epoch,
                                    &j->addr, &j->key);
            /* entry must be live: it was updated, never removed, and
             * any later insert journaled after it is already undone */
            e->val = j->old_val;
            break;
        }
        case EITA_J_ACCESS_ADDR:
            ts->accessed_addrs[idx].epoch = 0;
            ts->addr_count--;
            break;
        case EITA_J_ACCESS_SLOT:
            ts->accessed_slots[idx].epoch = 0;
            ts->slot_count--;
            break;
        case EITA_J_TSTORE_NEW:
            ts->tstorage[idx].epoch = 0;
            ts->tstore_count--;
            break;
        case EITA_J_REFUND_SET:
            ts->refund_counter = (int64_t)j->old_val.limb[0];
            break;
        case EITA_J_CREATED_NEW:
            ts->created[idx].epoch = 0;
            ts->created_count--;
            break;
        default:                /* 0/2/3: host-replayed, skip */
            break;
        }
    }
    ar->journal_count = target_count;
}
