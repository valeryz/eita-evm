/* world_slots_harness.c — CBMC proof harness of the native slot tables (../world_slots.c).
 *
 * Inductive form: an ARBITRARY slot table of capacity CAP (4 or 8) that satisfies the
 * table invariant, one operation OP with arbitrary key and value (0 get, 1 place = a put
 * into a table with room, 2 remove, 3 grow = the rehash a put does when the load test
 * fails; eita_ws_put is touch + grow-if-full + place, so 1 and 3 cover it), then:
 *   - memory safety (bounds, pointers, frees, leaks, signed overflow, conversions);
 *   - the invariant again, and the load: 4 used <= 3 cap after every op, and after a grow
 *     room for the put's one place (4 (used + 1) <= 3 cap);
 *   - the finite-map model (lean/Evm/CL/WorldSlotsModel.lean): for an arbitrary key q, the
 *     table's contents found by a plain SCAN (no hashing) are the model's after the op.
 * Since every table the code builds starts empty (which satisfies the invariant) and each
 * op preserves it, this covers every reachable table of these sizes, not only short op
 * sequences. The invariant:
 *   count = #full, used = #full + #tombstones, used < cap, cap a power of two;
 *   no two full entries hold one key;
 *   a full entry at j with key k: no EMPTY entry between hash(k) and j (cyclically), so a
 *   probe from hash(k) reaches it.
 * Keys come from a small domain whose low limbs collide (equal hash, long probe chains).
 * directory_growth checks the per-account directory (growth, independence of accounts,
 * drop, copy) with concrete ids. Run by run.sh (one CBMC run per OP, CAP and, for grow,
 * present count COUNT, which makes the new capacity concrete). Shaped for CBMC: the table
 * header is static and keys pass by value (strong updates, no aliasing), loops over
 * concrete indices are branch-free, and world_slots.c allocates per call site.
 */
#include "../world_slots.c"   /* the static ws_place / ws_grow are proved one by one */
#include <stdlib.h>

#ifndef CAP
#define CAP 4
#endif
uint64_t nondet_u64(void);
unsigned nondet_unsigned(void);
uint8_t nondet_u8(void);
_Bool nondet_bool(void);

typedef struct { uint64_t l[4]; } key;   /* keys by value: pointer arguments would alias */
static key key_at(const ws_slots *t, uint64_t i) {
  key k = {{t->words[8 * i], t->words[8 * i + 1], t->words[8 * i + 2], t->words[8 * i + 3]}};
  return k;
}
static int eqk(key a, key b) {
  return a.l[0] == b.l[0] && a.l[1] == b.l[1] && a.l[2] == b.l[2] && a.l[3] == b.l[3];
}
static uint64_t hash_of(uint64_t k0, uint64_t k1, uint64_t mask) {   /* world_slots.c's ws_hash */
  return ((k0 * UINT64_C(0x9E3779B97F4A7C15) + k1) >> 17) & mask;
}
static key any_key(void) {
  key k = {{nondet_u64(), nondet_u64(), nondet_bool(), nondet_bool() ? ~UINT64_C(0) : 0}};
  __CPROVER_assume(k.l[0] < 4 && k.l[1] < 2);
  return k;
}
/* The scan lookup: the index of a full entry holding K, or -1 (no hashing involved).
   Branch-free over concrete indices, like the invariant: early returns inside loops make
   CBMC's path guards grow with every iteration. */
static int64_t scan(const ws_slots *t, key k) {
  int64_t r = -1;
  for (uint64_t i = 0; i < t->cap; i++)
    r = (t->state[i] == 1 && eqk(key_at(t, i), k)) ? (int64_t)i : r;
  return r;
}
static int invariant(const ws_slots *t) {
  uint64_t full = 0, used = 0, mask = t->cap - 1;
  int ok = t->cap != 0 && (t->cap & mask) == 0;
  for (uint64_t j = 0; j < t->cap; j++) {
    uint8_t s = t->state[j];
    key k = key_at(t, j);
    uint64_t h = hash_of(k.l[0], k.l[1], mask);
    ok &= s <= 2;
    used += s != 0;
    full += s == 1;
    for (uint64_t i = 0; i < t->cap; i++) {
      /* no second full entry with j's key */
      ok &= !(s == 1 && i > j && t->state[i] == 1 && eqk(key_at(t, i), k));
      /* every entry on the probe path hash(k) .. j-1 is non-empty */
      ok &= !(s == 1 && ((i - h) & mask) < ((j - h) & mask) && t->state[i] == 0);
    }
  }
  return ok && full == t->count && used == t->used && used < t->cap;
}

static void directory_growth(void) {
  ws_world *w = eita_ws_new();
  eita_ws_put(w, 0, 1, 0, 0, 0, 10, 0, 0, 0);
  eita_ws_put(w, 3, 2, 0, 0, 0, 20, 0, 0, 0);       /* the directory grows past id 0's */
  eita_ws_put(w, 2, 3, 0, 0, 0, 30, 0, 0, 0);
  const uint64_t *a = eita_ws_get(w, 0, 1, 0, 0, 0), *b = eita_ws_get(w, 3, 2, 0, 0, 0),
                 *c = eita_ws_get(w, 2, 3, 0, 0, 0);
  __CPROVER_assert(a && *a == 10 && b && *b == 20 && c && *c == 30, "directory growth keeps tables");
  __CPROVER_assert(eita_ws_table(w, 7) == 0 && eita_ws_table(w, 1000) == 0, "no table past the directory");
  eita_ws_remove(w, 3, 1, 0, 0, 0);                   /* id 3's write does not reach id 0 */
  eita_ws_drop(w, 2);
  a = eita_ws_get(w, 0, 1, 0, 0, 0);
  __CPROVER_assert(a && *a == 10 && eita_ws_get(w, 3, 2, 0, 0, 0) && !eita_ws_table(w, 2), "accounts are independent");
  ws_world *d = eita_ws_new();                        /* copy: same contents, own arrays */
  eita_ws_copy(d, 3, eita_ws_table(w, 3));
  b = eita_ws_get(d, 3, 2, 0, 0, 0);
  __CPROVER_assert(b && *b == 20 && eita_ws_table(d, 3)->words != eita_ws_table(w, 3)->words, "copy");
  eita_ws_free(d);
  eita_ws_free(w);
}

int main(void) {
#ifndef NODIR
  directory_growth();
#endif

  /* an arbitrary table of capacity CAP satisfying the invariant, as account 0's */
  /* built directly (as eita_ws_touch would, at capacity CAP): nothing allocated and freed
     here, so no dead object joins the pointers' value sets */
  static ws_world W; static ws_slots T; static ws_slots *DIR[1];   /* static: CBMC updates */
  ws_world *w = &W; ws_slots *t = &T;                             /* their fields strongly */
  w->n = 1; w->acct = DIR; DIR[0] = t;
#ifdef COUNT
  t->cap = CAP; t->count = COUNT; t->used = nondet_u64();   /* concrete: grow's new capacity is */
#else
  t->cap = CAP; t->count = nondet_u64(); t->used = nondet_u64();
#endif
  t->words = malloc(CAP * 8 * sizeof(uint64_t)); t->state = malloc(CAP);
  __CPROVER_assume(t->words && t->state);
  for (int i = 0; i < CAP; i++) {
    t->state[i] = nondet_u8();
    key r = any_key();
    for (int l = 0; l < 4; l++) t->words[8 * i + l] = r.l[l];
    t->words[8 * i + 4] = nondet_u64(); t->words[8 * i + 5] = 0;   /* values: two free limbs */
    t->words[8 * i + 6] = nondet_u64(); t->words[8 * i + 7] = 0;
  }
  __CPROVER_assume(invariant(t));
  __CPROVER_assume(4 * t->used <= 3 * t->cap);       /* the load the inserts keep */

  uint64_t v0 = nondet_u64(), v2 = nondet_u64();
  key k = any_key(), q = any_key();
  /* the model's answer for q before the op */
  int64_t qi = scan(t, q);
  int q_was = qi >= 0;
  uint64_t q_v0 = q_was ? t->words[8 * qi + 4] : 0, q_v2 = q_was ? t->words[8 * qi + 6] : 0;
  int64_t ki = scan(t, k);

#ifndef OP
#define OP 0                         /* 0 get, 1 place (put), 2 remove, 3 grow: one per run */
#endif
  const unsigned op = OP;
  if (op == 0) {                                      /* get = the scan's answer */
    const uint64_t *g = eita_ws_get(w, 0, k.l[0], k.l[1], k.l[2], k.l[3]);
    __CPROVER_assert((g == 0) == (ki < 0), "get: present = model");
    __CPROVER_assert(g == 0 || (g[0] == t->words[8 * ki + 4] && g[2] == t->words[8 * ki + 6] && g[1] == 0 && g[3] == 0),
                     "get: value = model");
  } else if (op == 1) {                              /* put = touch; grow when full; place */
    __CPROVER_assume(4 * (t->used + 1) <= 3 * t->cap); /* place: room (what insert's load test or a grow leaves) */
    const uint64_t kk[4] = {k.l[0], k.l[1], k.l[2], k.l[3]}, vv[4] = {v0, 0, v2, 0};
    ws_place(t, kk, vv);
  } else if (op == 2) {
    eita_ws_remove(w, 0, k.l[0], k.l[1], k.l[2], k.l[3]);
  } else {                                            /* grow: when a put finds the table full */
    __CPROVER_assume(4 * (t->used + 1) >= 3 * t->cap);
    ws_grow(t);
  }
  t = eita_ws_table(w, 0);                            /* a put may have grown it */
  __CPROVER_assert(t != 0, "the table stays");
  __CPROVER_assert(invariant(t), "invariant kept");
  if (op == 3) __CPROVER_assert(4 * (t->used + 1) <= 3 * t->cap, "grow: room for the put");
  else __CPROVER_assert(4 * t->used <= 3 * t->cap, "load kept");
  int64_t ki2 = scan(t, k), qi2 = scan(t, q);
  if (op == 1) __CPROVER_assert(ki2 >= 0 && t->words[8 * ki2 + 4] == v0 && t->words[8 * ki2 + 6] == v2, "put: key holds value");
  if (op == 2) __CPROVER_assert(ki2 < 0, "remove: key absent");
  if (op == 0 || op == 3 || !eqk(q, k))                /* get and grow change no key */
    __CPROVER_assert((qi2 >= 0) == q_was && (!q_was || (t->words[8 * qi2 + 4] == q_v0 && t->words[8 * qi2 + 6] == q_v2)),
                     "other keys unchanged");
  free(t->words); free(t->state);                    /* (the header is static) */
  return 0;
}
