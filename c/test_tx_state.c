/* test_tx_state.c — unit test for the native per-tx state tables.
 *
 * Build + run: make test  (see Makefile)
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "tx_state.h"

static int failures = 0;

#define CHECK(cond, ...) do { \
    if (!(cond)) { failures++; printf("FAIL %s:%d  ", __FILE__, __LINE__); \
                   printf(__VA_ARGS__); printf("\n"); } } while (0)

static u256_t u(uint64_t a, uint64_t b, uint64_t c, uint64_t d) {
    u256_t v = {{a, b, c, d}};
    return v;
}

static uint64_t rng_state = 0x123456789ABCDEFull;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}

static TxState *make_ts(uint64_t cap) {
    TxState *ts = calloc(1, sizeof *ts);
    ts->epoch = 1;
    ts->addr_mask = ts->slot_mask = ts->tstore_mask = cap - 1;
    ts->created_mask = ts->orig_mask = cap - 1;
    ts->accessed_addrs = calloc(cap, sizeof(TsAddrEntry));
    ts->accessed_slots = calloc(cap, sizeof(TsSlotEntry));
    ts->tstorage       = calloc(cap, sizeof(TsKvEntry));
    ts->created        = calloc(cap, sizeof(TsAddrEntry));
    ts->originals      = calloc(cap, sizeof(TsKvEntry));
    return ts;
}

static TxArena *make_arena(uint64_t cap) {
    TxArena *ar = calloc(1, sizeof *ar);
    ar->journal_data = calloc(cap, sizeof(JournalEntry));
    ar->journal_cap = cap;
    return ar;
}

int main(void) {
    TxState *ts = make_ts(1 << 14);
    TxArena *ar = make_arena(1 << 16);

    /* --- cold/warm address --- */
    u256_t a1 = u(0xAAAA, 0, 0, 0), a2 = u(0xBBBB, 1, 2, 3);
    u256_t zero_addr = u(0, 0, 0, 0);
    CHECK(eita_ts_access_addr(ts, ar, &a1) == 1, "a1 first access is cold");
    CHECK(eita_ts_access_addr(ts, ar, &a1) == 0, "a1 second access is warm");
    CHECK(eita_ts_access_addr(ts, ar, &a2) == 1, "a2 cold");
    CHECK(eita_ts_access_addr(ts, ar, &zero_addr) == 1,
          "address 0 is a valid key (cold)");
    CHECK(eita_ts_access_addr(ts, ar, &zero_addr) == 0, "address 0 warm");

    /* --- cold/warm slot, keyed by (addr, slot) --- */
    u256_t s1 = u(7, 0, 0, 0);
    CHECK(eita_ts_access_slot(ts, ar, &a1, &s1) == 1, "(a1,s1) cold");
    CHECK(eita_ts_access_slot(ts, ar, &a1, &s1) == 0, "(a1,s1) warm");
    CHECK(eita_ts_access_slot(ts, ar, &a2, &s1) == 1,
          "same slot under different addr is cold");

    /* --- transient storage, per-address keying (EIP-1153) --- */
    u256_t v1 = u(111, 0, 0, 0), v2 = u(222, 0, 0, 0), got;
    eita_ts_tload(ts, &a1, &s1, &got);
    CHECK(got.limb[0] == 0 && got.limb[3] == 0, "tload default 0");
    eita_ts_tstore(ts, ar, &a1, &s1, &v1);
    eita_ts_tstore(ts, ar, &a2, &s1, &v2);
    eita_ts_tload(ts, &a1, &s1, &got);
    CHECK(got.limb[0] == 111, "tload a1 sees a1's value");
    eita_ts_tload(ts, &a2, &s1, &got);
    CHECK(got.limb[0] == 222, "tload a2 sees a2's value (addr-keyed)");

    /* --- refund counter --- */
    eita_ts_refund_add(ts, ar, 4800);
    eita_ts_refund_add(ts, ar, -2800);
    CHECK(ts->refund_counter == 2000, "refund add/sub");

    /* --- created set --- */
    CHECK(eita_ts_created_insert(ts, ar, &a1) == 1, "created insert new");
    CHECK(eita_ts_created_insert(ts, ar, &a1) == 0, "created insert dup");
    CHECK(eita_ts_created_p(ts, &a1) == 1, "created_p present");
    CHECK(eita_ts_created_p(ts, &a2) == 0, "created_p absent");

    /* --- originals: first-touch wins, absent reads as current --- */
    u256_t cur1 = u(10, 0, 0, 0), cur2 = u(20, 0, 0, 0);
    eita_ts_orig_record(ts, &a1, &s1, &cur1);
    eita_ts_orig_record(ts, &a1, &s1, &cur2);    /* ignored */
    eita_ts_orig_get(ts, &a1, &s1, &cur2, &got);
    CHECK(got.limb[0] == 10, "original is first-touch value");
    eita_ts_orig_get(ts, &a2, &s1, &cur2, &got);
    CHECK(got.limb[0] == 20, "absent original falls back to current");

    /* --- frame revert --- */
    uint64_t snap = ar->journal_count;
    int64_t refund_snap = ts->refund_counter;
    u256_t a3 = u(0xCCCC, 0, 0, 0), v3 = u(333, 0, 0, 0);
    CHECK(eita_ts_access_addr(ts, ar, &a3) == 1, "a3 cold in sub-frame");
    eita_ts_access_slot(ts, ar, &a3, &s1);
    eita_ts_tstore(ts, ar, &a1, &s1, &v3);       /* update: 111 -> 333 */
    eita_ts_tstore(ts, ar, &a3, &s1, &v3);       /* fresh insert */
    eita_ts_refund_add(ts, ar, 19900);
    eita_ts_created_insert(ts, ar, &a3);
    eita_ts_revert(ts, ar, snap);
    CHECK(ar->journal_count == snap, "journal rewound");
    CHECK(eita_ts_access_addr(ts, ar, &a3) == 1, "a3 cold again after revert");
    eita_ts_revert(ts, ar, snap);                /* undo the probe insert */
    eita_ts_tload(ts, &a1, &s1, &got);
    CHECK(got.limb[0] == 111, "tstore update reverted to old value");
    eita_ts_tload(ts, &a3, &s1, &got);
    CHECK(got.limb[0] == 0, "fresh tstore insert removed");
    CHECK(ts->refund_counter == refund_snap, "refund restored");
    CHECK(eita_ts_created_p(ts, &a3) == 0, "created insert reverted");
    CHECK(eita_ts_access_addr(ts, ar, &a1) == 0, "pre-snapshot a1 still warm");
    eita_ts_tload(ts, &a2, &s1, &got);
    CHECK(got.limb[0] == 222, "pre-snapshot tstore intact");

    /* --- probe-chain integrity under bulk revert ---
     * Insert N keys, snapshot, insert N more, revert: every pre-snapshot
     * key must still be warm, every post-snapshot key cold. Exercises
     * reverse-order deletion across colliding probe chains. */
    enum { N = 2000 };
    u256_t keys[2 * N];
    for (int i = 0; i < 2 * N; i++)
        keys[i] = u(rnd(), rnd() & 0xFF, 0, 0);
    for (int i = 0; i < N; i++)
        CHECK(eita_ts_access_addr(ts, ar, &keys[i]) == 1, "bulk pre cold %d", i);
    uint64_t snap2 = ar->journal_count;
    for (int i = N; i < 2 * N; i++)
        CHECK(eita_ts_access_addr(ts, ar, &keys[i]) == 1, "bulk post cold %d", i);
    eita_ts_revert(ts, ar, snap2);
    for (int i = 0; i < N; i++) {
        uint64_t cold = eita_ts_access_addr(ts, ar, &keys[i]);
        CHECK(cold == 0, "pre-snapshot key %d went cold after revert", i);
    }
    eita_ts_revert(ts, ar, snap2);
    for (int i = N; i < 2 * N; i++) {
        uint64_t cold = eita_ts_access_addr(ts, ar, &keys[i]);
        CHECK(cold == 1, "post-snapshot key %d still warm after revert", i);
    }
    eita_ts_revert(ts, ar, snap2);

    /* --- nested revert: inner frame reverts, outer frame reverts --- */
    uint64_t outer = ar->journal_count;
    eita_ts_tstore(ts, ar, &a1, &s1, &v2);       /* outer writes 222 */
    uint64_t inner = ar->journal_count;
    eita_ts_tstore(ts, ar, &a1, &s1, &v3);       /* inner writes 333 */
    eita_ts_revert(ts, ar, inner);
    eita_ts_tload(ts, &a1, &s1, &got);
    CHECK(got.limb[0] == 222, "inner revert restores outer's write");
    eita_ts_revert(ts, ar, outer);
    eita_ts_tload(ts, &a1, &s1, &got);
    CHECK(got.limb[0] == 111, "outer revert restores original");

    /* --- O(1) epoch reset --- */
    eita_ts_reset(ts);
    ar->journal_count = 0;
    CHECK(eita_ts_access_addr(ts, ar, &a1) == 1, "a1 cold after tx reset");
    eita_ts_tload(ts, &a1, &s1, &got);
    CHECK(got.limb[0] == 0, "tstorage cleared by reset");
    CHECK(eita_ts_created_p(ts, &a1) == 0, "created cleared by reset");
    eita_ts_orig_get(ts, &a1, &s1, &cur2, &got);
    CHECK(got.limb[0] == 20, "originals cleared by reset");
    CHECK(ts->refund_counter == 0, "refund cleared by reset");

    if (failures) {
        printf("test_tx_state: %d FAILURES\n", failures);
        return 1;
    }
    printf("test_tx_state: all checks passed\n");
    return 0;
}
