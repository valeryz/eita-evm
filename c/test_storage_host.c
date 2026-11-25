/* test_storage_host.c — the native revert (eita_sh_revert_storage) is complete on its own, as
   a C-only host needs: SSTOREs through eita_cb_sstore to three accounts whose addresses
   collide in the 64-entry address -> id cache, so at the revert the cache holds only the last
   one; the revert alone must restore every slot, retype every type-0 entry and return their
   count. Also: it stops at an un-create entry (type 10), leaving the entries below it. */
#include "storage_host.h"
#include <stdio.h>
#include <stdlib.h>

static int failures;
#define CHECK(c, ...) do { if (!(c)) { failures++; fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); } } while (0)

/* The host's address -> id table: the authority the cache fronts. */
static u256_t known[8];
static uint64_t nknown, learn_calls;
static uint64_t learn(const u256_t *a) {
  learn_calls++;
  for (uint64_t i = 0; i < nknown; i++)
    if (known[i].limb[0] == a->limb[0] && known[i].limb[1] == a->limb[1] && known[i].limb[2] == a->limb[2]) return i;
  known[nknown] = *a;
  return nknown++;
}

static TxState *make_ts(uint64_t cap) {
  TxState *ts = calloc(1, sizeof *ts);
  ts->epoch = 1;
  ts->addr_mask = ts->slot_mask = ts->tstore_mask = ts->created_mask = ts->orig_mask = cap - 1;
  ts->accessed_addrs = calloc(cap, sizeof(TsAddrEntry));
  ts->accessed_slots = calloc(cap, sizeof(TsSlotEntry));
  ts->tstorage = calloc(cap, sizeof(TsKvEntry));
  ts->created = calloc(cap, sizeof(TsAddrEntry));
  ts->originals = calloc(cap, sizeof(TsKvEntry));
  return ts;
}

static u256_t w(uint64_t x) { u256_t r = {{x, 0, 0, 0}}; return r; }
static uint64_t slot_val(ws_world *ws, uint64_t id, uint64_t k, int *present) {
  const uint64_t *v = eita_ws_get(ws, id, k, 0, 0, 0);
  *present = v != 0;
  return v ? v[0] : 0;
}
static uint64_t count_type(const TxArena *ar, uint64_t from, uint64_t type) {
  uint64_t c = 0;
  for (uint64_t n = from; n < ar->journal_count; n++) c += ar->journal_data[n].entry_type == type;
  return c;
}

int main(void) {
  ws_world *ws = eita_ws_new();
  TxState *ts = make_ts(1 << 10);
  TxArena *ar = calloc(1, sizeof *ar);
  ar->journal_cap = 1 << 10;
  ar->journal_data = calloc(ar->journal_cap, sizeof(JournalEntry));
  eita_sh *h = &eita_sh_g;
  h->ws = ws; h->ts = ts; h->fork = 11; h->flags = 0; h->learn = learn;

  /* A, B, C: equal low limb mod 64, so one cache entry. The SSTOREs name A with a bit set
     above its 160 (not part of the address, as read-addr reads it). */
  const u256_t A = {{5, 0, 0, 0}}, B = {{5 + 64, 7, 0, 0}}, C = {{5 + 128, 0, 0, 0}};
  const u256_t Ahi = {{5, 0, 0x100000000ull, 0}};
  const uint64_t a = learn(&A), b = learn(&B), c = learn(&C);
  eita_ws_put(ws, a, 1, 0, 0, 0, 11, 0, 0, 0);
  eita_ws_put(ws, b, 1, 0, 0, 0, 22, 0, 0, 0);
  eita_ws_put(ws, c, 1, 0, 0, 0, 33, 0, 0, 0);
  learn_calls = 0;

  /* the frame: interleaved SSTOREs, C last, so the cache holds C at the revert */
  const uint64_t mark = ar->journal_count;
  const struct { const u256_t *addr; uint64_t k, v; } ops[] = {
    {&Ahi, 1, 111}, {&B, 1, 222}, {&A, 2, 333}, {&B, 1, 0}, {&C, 1, 444}, {&Ahi, 1, 1111}, {&B, 2, 555}, {&C, 2, 666},
  };
  for (unsigned i = 0; i < sizeof ops / sizeof ops[0]; i++) {
    u256_t k = w(ops[i].k), v = w(ops[i].v);
    eita_cb_sstore(ar, ops[i].addr, &k, &v);
  }
  const uint64_t stores = count_type(ar, mark, 0);
  CHECK(stores == 8, "8 SSTORE entries, got %llu", (unsigned long long)stores);
  CHECK(learn_calls == 8, "every SSTORE missed the shared cache entry: %llu learns", (unsigned long long)learn_calls);

  uint64_t restored = eita_sh_revert_storage(ar, mark);
  CHECK(restored == stores, "restored %llu of %llu", (unsigned long long)restored, (unsigned long long)stores);
  CHECK(count_type(ar, mark, 0) == 0, "a type-0 entry left for a second pass");
  CHECK(count_type(ar, mark, EITA_J_SSTORE_DONE) == stores, "every SSTORE entry retyped");
  int p;
  CHECK(slot_val(ws, a, 1, &p) == 11 && p, "A[1] restored");
  CHECK(slot_val(ws, b, 1, &p) == 22 && p, "B[1] restored");
  CHECK(slot_val(ws, c, 1, &p) == 33 && p, "C[1] restored");
  slot_val(ws, a, 2, &p); CHECK(!p, "A[2] absent again");
  slot_val(ws, b, 2, &p); CHECK(!p, "B[2] absent again");
  slot_val(ws, c, 2, &p); CHECK(!p, "C[2] absent again");
  CHECK(nknown == 3, "the revert learned no new account");
  eita_ts_revert(ts, ar, mark);
  CHECK(ar->journal_count == mark, "journal rewound");

  /* an un-create entry stops the native pass: the entries below it are the host's */
  u256_t k1 = w(1), v = w(7);
  eita_cb_sstore(ar, &A, &k1, &v);
  JournalEntry *u = &ar->journal_data[ar->journal_count++];
  u->entry_type = 10; u->addr = B;
  eita_cb_sstore(ar, &B, &k1, &v);
  eita_cb_sstore(ar, &C, &k1, &v);
  restored = eita_sh_revert_storage(ar, mark);
  CHECK(restored == 2, "above the un-create: 2 restored, got %llu", (unsigned long long)restored);
  CHECK(slot_val(ws, a, 1, &p) == 7, "below the un-create: A[1] left for the host");
  CHECK(slot_val(ws, b, 1, &p) == 22 && slot_val(ws, c, 1, &p) == 33, "above the un-create: restored");
  CHECK(count_type(ar, mark, 0) == 1, "below the un-create: A's entry still type 0");

  if (failures) { fprintf(stderr, "test_storage_host: %d failures\n", failures); return 1; }
  puts("test_storage_host: OK");
  return 0;
}
