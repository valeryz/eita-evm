/* test_world_slots.c — world_slots.c against a reference finite map (the Lean model's
   semantics: lean/Evm/CL/WorldSlotsModel.lean), randomized: put / overwrite / remove /
   drop / copy / revert-in-reverse, colliding keys, growth. With an argument: replay a trace
   of the Lean model itself (lake exe worldSlotsVectors) and check its answers. Built with
   ASan + UBSan. */
#include "world_slots.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NID 40
#define MAXE 200000

typedef struct { uint64_t id, k[4], v[4]; } ent;   /* the model: a list of present keys */
static ent model[MAXE]; static int nmodel;
static int has_table[NID];

static uint64_t rs = 88172645463325252ull;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int mfind(uint64_t id, const uint64_t *k) {
  for (int i = 0; i < nmodel; i++)
    if (model[i].id == id && !memcmp(model[i].k, k, sizeof model[i].k)) return i;
  return -1;
}
static void mput(uint64_t id, const uint64_t *k, const uint64_t *v) {
  has_table[id] = 1;
  int i = mfind(id, k);
  if (i < 0) { i = nmodel++; model[i].id = id; memcpy(model[i].k, k, 32); }
  memcpy(model[i].v, v, 32);
}
static void mremove(uint64_t id, const uint64_t *k) {
  has_table[id] = 1;
  int i = mfind(id, k);
  if (i >= 0) model[i] = model[--nmodel];
}
static void mdrop(uint64_t id) {
  has_table[id] = 0;
  for (int i = 0; i < nmodel;) if (model[i].id == id) model[i] = model[--nmodel]; else i++;
}

/* Keys from a small pool, built to collide: equal k0/k1 (same hash) with other k2/k3. */
static void rkey(uint64_t *k) {
  uint64_t r = rnd() % 600;
  k[0] = r % 7 == 0 ? 0 : (r % 50); k[1] = r % 3 == 0 ? 0 : (r % 11); k[2] = r / 50; k[3] = r % 5 == 1 ? ~0ull : 0;
}
static void rval(uint64_t *v) {
  for (int i = 0; i < 4; i++) v[i] = rnd() % 4 == 0 ? 0 : rnd();
  if (rnd() % 5 == 0) memset(v, 0, 32);
}

static int failures;
#define CHECK(c, ...) do { if (!(c)) { if (failures++ < 20) { fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); } } } while (0)

struct walk { uint64_t id; int seen; };
static void walk_fn(const uint64_t *k, const uint64_t *v, void *ctx) {
  struct walk *w = ctx;
  int i = mfind(w->id, k);
  CHECK(i >= 0 && !memcmp(model[i].v, v, 32), "map: id %lu yields a key the model lacks", w->id);
  w->seen++;
}

static void check_all(ws_world *w) {
  for (uint64_t id = 0; id < NID; id++) {
    ws_slots *t = eita_ws_table(w, id);
    CHECK(!!t == has_table[id], "table existence of id %lu", id);
    int n = 0;
    for (int i = 0; i < nmodel; i++) if (model[i].id == id) n++;
    if (t) {
      CHECK(t->count == (uint64_t)n, "count id %lu: %lu vs %d", id, t->count, n);
      CHECK((t->cap & (t->cap - 1)) == 0 && t->used < t->cap && 4 * t->used <= 3 * t->cap, "cap/load id %lu: cap %lu used %lu count %lu", id, t->cap, t->used, t->count);
    }
    struct walk wk = {id, 0};
    eita_ws_map(w, id, walk_fn, &wk);
    CHECK(wk.seen == n, "map id %lu saw %d of %d", id, wk.seen, n);
  }
  for (int i = 0; i < nmodel; i++) {
    const uint64_t *v = eita_ws_get(w, model[i].id, model[i].k[0], model[i].k[1], model[i].k[2], model[i].k[3]);
    CHECK(v && !memcmp(v, model[i].v, 32), "get of a present key");
  }
}

/* Replay a Lean model trace (lake exe worldSlotsVectors): every G and H answer must be the
   model's. */
static int replay(const char *path) {
  FILE *f = fopen(path, "r");
  if (!f) { perror(path); return 1; }
  ws_world *w = eita_ws_new();
  char op; unsigned long id; uint64_t k[4], v[4]; long n = 0, answers = 0;
  while (fscanf(f, " %c %lu", &op, &id) == 2) {
    n++;
    if (op == 'P' || op == 'R' || op == 'G')
      if (fscanf(f, "%lx %lx %lx %lx", &k[0], &k[1], &k[2], &k[3]) != 4) break;
    if (op == 'P') {
      if (fscanf(f, "%lx %lx %lx %lx", &v[0], &v[1], &v[2], &v[3]) != 4) break;
      eita_ws_put(w, id, k[0], k[1], k[2], k[3], v[0], v[1], v[2], v[3]);
    } else if (op == 'R') eita_ws_remove(w, id, k[0], k[1], k[2], k[3]);
    else if (op == 'D') eita_ws_drop(w, id);
    else if (op == 'G' || op == 'H') {
      int present;
      if (fscanf(f, " = %d", &present) != 1) break;
      answers++;
      if (op == 'H') { CHECK(!!eita_ws_table(w, id) == present, "line %ld: H %lu", n, id); continue; }
      const uint64_t *g = eita_ws_get(w, id, k[0], k[1], k[2], k[3]);
      if (present) {
        if (fscanf(f, "%lx %lx %lx %lx", &v[0], &v[1], &v[2], &v[3]) != 4) break;
        CHECK(g && !memcmp(g, v, 32), "line %ld: G %lu present", n, id);
      } else CHECK(g == NULL, "line %ld: G %lu absent", n, id);
    }
  }
  int bad = !feof(f);
  CHECK(!bad, "%s: unreadable at op %ld", path, n);
  fclose(f); eita_ws_free(w);
  printf("test_world_slots: %ld model ops, %ld answers checked, %d failures\n", n, answers, failures);
  return failures != 0;
}

int main(int argc, char **argv) {
  if (argc > 1) return replay(argv[1]);
  ws_world *w = eita_ws_new();
  long ops = 0;
  for (int round = 0; round < 60; round++) {
    /* a frame: random ops journaled as (id, key, was-present, old value), then maybe reverted */
    static struct { uint64_t id, k[4], v[4]; int present; } jr[4096];
    int nj = 0, revert = rnd() % 3 == 0;
    for (int op = 0; op < 4000; op++, ops++) {
      uint64_t id = rnd() % NID, k[4], v[4];
      rkey(k); rval(v);
      int r = rnd() % 100;
      if (r < 85) {                               /* put (60) or remove (25), journaled */
        int i = mfind(id, k);
        jr[nj].id = id; memcpy(jr[nj].k, k, 32); jr[nj].present = i >= 0;
        if (i >= 0) memcpy(jr[nj].v, model[i].v, 32);
        nj++;
        if (r < 60) { eita_ws_put(w, id, k[0], k[1], k[2], k[3], v[0], v[1], v[2], v[3]); mput(id, k, v); }
        else { eita_ws_remove(w, id, k[0], k[1], k[2], k[3]); mremove(id, k); }
      } else if (r < 97) {                         /* get, absent or present */
        const uint64_t *g = eita_ws_get(w, id, k[0], k[1], k[2], k[3]);
        int i = mfind(id, k);
        CHECK(i < 0 ? g == NULL : (g && !memcmp(g, model[i].v, 32)), "get id %lu", id);
      } else if (!revert && r < 99) {              /* drop (a wipe, outside a reverted frame) */
        eita_ws_drop(w, id); mdrop(id);
      } else if (!revert) {                        /* copy into a second world and back */
        ws_world *c = eita_ws_new();
        eita_ws_copy(c, id, eita_ws_table(w, id));
        eita_ws_copy(w, id, eita_ws_table(c, id));
        eita_ws_free(c);
      }
    }
    if (revert)                                    /* restore in reverse journal order */
      for (int j = nj - 1; j >= 0; j--) {
        uint64_t *k = jr[j].k, *v = jr[j].v;
        if (jr[j].present) { eita_ws_put(w, jr[j].id, k[0], k[1], k[2], k[3], v[0], v[1], v[2], v[3]); mput(jr[j].id, k, v); }
        else { eita_ws_remove(w, jr[j].id, k[0], k[1], k[2], k[3]); mremove(jr[j].id, k); }
      }
    check_all(w);
  }
  /* one large table: growth through many doublings, then remove all */
  for (uint64_t i = 0; i < 100000; i++) eita_ws_put(w, NID + 1, i * 0x10001, i >> 3, i, 0, i, 0, 0, 1);
  CHECK(eita_ws_table(w, NID + 1)->count == 100000, "large count");
  for (uint64_t i = 0; i < 100000; i++) {
    const uint64_t *v = eita_ws_get(w, NID + 1, i * 0x10001, i >> 3, i, 0);
    CHECK(v && v[0] == i && v[3] == 1, "large get %lu", i);
  }
  for (uint64_t i = 0; i < 100000; i++) eita_ws_remove(w, NID + 1, i * 0x10001, i >> 3, i, 0);
  CHECK(eita_ws_table(w, NID + 1)->count == 0, "large remove");
  eita_ws_free(w);
  printf("test_world_slots: %ld random ops + 300000 bulk, %d failures\n", ops, failures);
  return failures != 0;
}
