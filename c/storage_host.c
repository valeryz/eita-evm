/* storage_host.c — the native SLOAD callback (storage_host.h). */
#include "storage_host.h"
#include <string.h>

eita_sh eita_sh_g;

static void cache_check(eita_sh *h) {
  if (h->cache_serial != h->ws->serial) { memset(h->cache, 0, sizeof h->cache); h->cache_serial = h->ws->serial; }
}

void eita_sh_cache_put(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t id) {
  eita_sh *h = &eita_sh_g;
  if (!h->ws) return;
  cache_check(h);
  h->cache[a0 % EITA_SH_CACHE].a0 = a0;
  h->cache[a0 % EITA_SH_CACHE].a1 = a1;
  h->cache[a0 % EITA_SH_CACHE].a2 = a2;
  h->cache[a0 % EITA_SH_CACHE].id1 = id + 1;
}

uint64_t eita_cb_sload(void *ctx, const u256_t *addr, const u256_t *slot, u256_t *out) {
  eita_sh *h = &eita_sh_g;
  if (h->enabled && h->ws) {
    /* the address as the Lisp callback reads it (read-addr): the low 160 bits */
    uint64_t a0 = addr->limb[0], a1 = addr->limb[1], a2 = addr->limb[2] & 0xFFFFFFFFu;
    cache_check(h);
    const uint64_t i = a0 % EITA_SH_CACHE;
    if (h->cache[i].id1 && h->cache[i].a0 == a0 && h->cache[i].a1 == a1 && h->cache[i].a2 == a2) {
      h->ar = ctx;
      h->id = h->cache[i].id1 - 1;
      h->addr.limb[0] = a0; h->addr.limb[1] = a1; h->addr.limb[2] = a2; h->addr.limb[3] = 0;
      h->key = *slot;
      uint64_t g = eita_spec_sload_effect(h, out->limb);
      if (g != EITA_SH_MISS) { h->hits++; return g; }
    }
  }
  h->misses++;
  return h->lisp_sload(ctx, addr, slot, out);
}
