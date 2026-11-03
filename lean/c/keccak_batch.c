/*
 * keccak_batch.c — batched Keccak-256 (#237 MPT).
 *
 * One FFI crossing hashes N inputs, killing the per-hash CFFI overhead that
 * dominated the trie profile (~640 ns/hash, almost all marshaling). Inputs are
 * PACKED into one buffer + an offsets/lengths table so the CL side does a single
 * marshaling pass. Uses the FEAT_SHA3 permutation (eita_keccak256_sha3).
 *
 * Hashing is independent across inputs (trie key-hashes, and all dirty nodes
 * within one trie level), so a batch can also be split across threads — see
 * eita_keccak256_batch_par.
 */
#include <stdint.h>
#include <stddef.h>
#include <pthread.h>

/* From keccak_sha3.c (FEAT_SHA3-accelerated, bit-identical to portable). */
void eita_keccak256_sha3(const uint8_t *in, size_t len, uint8_t out[32]);

/* Hash count inputs: input i = data[offs[i] .. offs[i]+lens[i]); out i = outs+32*i. */
/* Explicitly exported: the library is built with -fvisibility=hidden so that its
 * private copy of eita_keccak256_sha3 CANNOT collide with libeita's. Both libraries
 * used to export that symbol, so which keccak the replay bound to depended on dlopen
 * order — perturbing it made the replay hash with the wrong copy and silently compute
 * a wrong base fee. */
__attribute__((visibility("default")))
void eita_keccak256_batch(const uint8_t *data, const uint64_t *offs,
                          const uint64_t *lens, uint8_t *outs, uint64_t count) {
    for (uint64_t i = 0; i < count; i++)
        eita_keccak256_sha3(data + offs[i], (size_t)lens[i], outs + i * 32);
}

/* Parallel variant: split the batch across `nthreads` worker threads. Each
   worker hashes a contiguous slice (independent — no shared state). */
struct slice { const uint8_t *data; const uint64_t *offs; const uint64_t *lens;
               uint8_t *outs; uint64_t lo, hi; };

static void *worker(void *arg) {
    struct slice *s = (struct slice *)arg;
    for (uint64_t i = s->lo; i < s->hi; i++)
        eita_keccak256_sha3(s->data + s->offs[i], (size_t)s->lens[i], s->outs + i * 32);
    return 0;
}

__attribute__((visibility("default")))
void eita_keccak256_batch_par(const uint8_t *data, const uint64_t *offs,
                              const uint64_t *lens, uint8_t *outs,
                              uint64_t count, uint32_t nthreads) {
    if (nthreads < 2 || count < 2 * nthreads) {
        eita_keccak256_batch(data, offs, lens, outs, count);
        return;
    }
    if (nthreads > 64) nthreads = 64;
    pthread_t th[64];
    struct slice sl[64];
    uint64_t per = count / nthreads;
    for (uint32_t t = 0; t < nthreads; t++) {
        sl[t].data = data; sl[t].offs = offs; sl[t].lens = lens; sl[t].outs = outs;
        sl[t].lo = t * per;
        sl[t].hi = (t == nthreads - 1) ? count : (t + 1) * per;
        pthread_create(&th[t], 0, worker, &sl[t]);
    }
    for (uint32_t t = 0; t < nthreads; t++) pthread_join(th[t], 0);
}
