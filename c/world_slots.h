/*
 * world_slots.h — the world's storage slots, natively (docs/native-storage.md).
 *
 * The one copy of every loaded storage slot: (account id, slot key) -> value, keys and
 * values as four 64-bit limbs (least significant first). A ws_world belongs to one
 * account table (src/state/world.lisp: ids are per table; a frozen layer keeps its
 * table and so its slots) and holds, per account id, one open-addressed ws_slots table.
 *
 * Per-account tables, not one world-wide table: a wipe (SELFDESTRUCT, a failed CREATE)
 * and an account's slot walk (the root checker, a journaled wipe, a layer write) cost the
 * account's own slots, not the world's; and the hash, probe and growth rules are the Lisp
 * table's they replace, so an account's slots are walked in the same order as before
 * (the journal of a wipe, the fact log and the layer files are unchanged).
 *
 * A slot table: linear probing, a power-of-two capacity, at most 3/4 used (present +
 * tombstones). An entry is 8 limbs (key 0..3, value 4..7) and a state byte (0 empty,
 * 1 full, 2 tombstone). A present key may hold 0 (a lazy world keeps faulted zeros).
 *
 * Threads: one writer (the replay thread on the hot table); a frozen table is read-only
 * and may be read by several threads. Allocation failure aborts.
 *
 * Contracts (the Lean model: lean/Evm/CL/WorldSlotsModel.lean, a finite map
 * (id, key) -> value plus the set of ids that have a table; checked by
 * c/test_world_slots.c and the CBMC harness c/cbmc/world_slots_harness.c):
 */
#ifndef EITA_WORLD_SLOTS_H
#define EITA_WORLD_SLOTS_H
#include <stdint.h>

typedef struct ws_slots {
  uint64_t count;   /* present keys */
  uint64_t used;    /* present + tombstones */
  uint64_t cap;     /* a power of two, >= 4 */
  uint64_t *words;  /* cap x 8 limbs */
  uint8_t *state;   /* cap bytes */
} ws_slots;         /* field offsets 0, 8, 16, 24, 32: read by the Lisp walk (world.lisp) */

typedef struct ws_world {
  uint64_t n;       /* ids below n have a directory entry */
  ws_slots **acct;  /* n entries, NULL: no table */
  uint64_t serial;  /* unique per ws_world made (an address may be reused after a free) */
} ws_world;

#define WS_MAX_CAP (UINT64_C(1) << 40)

ws_world *eita_ws_new(void);
/* Frees every table and W. */
void eita_ws_free(ws_world *w);
/* ID's table, or NULL. */
ws_slots *eita_ws_table(const ws_world *w, uint64_t id);
/* ID's table, created empty when it has none. */
ws_slots *eita_ws_touch(ws_world *w, uint64_t id);
/* Index of KEY's entry in T, or -1 - (the insertion index: the first tombstone on the
   probe path, else the empty entry that ends it). */
int64_t eita_ws_probe(const ws_slots *t, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3);
/* The value limbs of (ID, KEY), or NULL when absent. */
const uint64_t *eita_ws_get(const ws_world *w, uint64_t id,
                            uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3);
/* (ID, KEY) := VALUE (ID's table created when it has none). */
void eita_ws_put(ws_world *w, uint64_t id, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3,
                 uint64_t v0, uint64_t v1, uint64_t v2, uint64_t v3);
/* (ID, KEY) absent (ID's table created when it has none). */
void eita_ws_remove(ws_world *w, uint64_t id, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3);
/* ID has no table (every key of ID absent). */
void eita_ws_drop(ws_world *w, uint64_t id);
/* ID's table in DST := a copy of SRC's entries (SRC may be NULL: ID has no table). */
void eita_ws_copy(ws_world *dst, uint64_t id, const ws_slots *src);
/* FN(key, value, ctx) for every present key of ID, in table order. */
void eita_ws_map(const ws_world *w, uint64_t id,
                 void (*fn)(const uint64_t *key, const uint64_t *val, void *ctx), void *ctx);
#endif
