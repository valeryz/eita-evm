/*
 * tx_arena.h — bump-allocated tx-level arena for journal entries, log
 * records, output buffers, and frame slots.
 *
 * Lives in memory pointed to by `EvmState.cb_ctx` (offset 504 in
 * evm_state.h). Native handlers that need to record per-tx side
 * effects (SSTORE/TSTORE journaling, LOG-N record append) bump
 * pointers into the appropriate region without calling out — no
 * malloc, no syscall, no Lisp GC interaction.
 *
 * Reset at tx start by clearing journal_count and log_count (the
 * regions are reused). Host owns allocation of the arena and the
 * data regions; native code only bumps.
 *
 * ## Layout discipline
 *
 * - All bump counters are u64 at known offsets at the start of the
 *   struct so handlers can `ldr x_count, [x_arena, #N]` cheaply.
 * - All data region pointers follow the counters.
 * - Entry types are fixed-size for arithmetic addressing
 *   (`entry_ptr = base + count * SIZE_OF_ENTRY`).
 */

#ifndef EITA_TX_ARENA_H
#define EITA_TX_ARENA_H

#include <stdint.h>
#include <stddef.h>
#include "evm_state.h"

#ifdef __cplusplus
extern "C" {
#endif

/* =========================================================================
 * JournalEntry — recorded on SSTORE / TSTORE / SELFDESTRUCT / balance
 * change. The host replays these on REVERT.
 *
 *   entry_type: 0 = sstore, 1 = tstore, 2 = balance, 3 = selfdestruct, ...
 *   addr      : 32B — contract whose state was mutated
 *   key       : 32B — slot (for sstore/tstore) or unused
 *   old_val   : 32B — value to restore on REVERT
 *
 * 104 bytes total. Fits two per cache line (rounded up).
 * ========================================================================= */

typedef struct {
    uint64_t entry_type;  /* offset   0 */
    u256_t   addr;        /* offset   8 */
    u256_t   key;         /* offset  40 */
    u256_t   old_val;     /* offset  72 */
} JournalEntry;

_Static_assert(sizeof(JournalEntry) == 104, "JournalEntry must be 104 bytes");
_Static_assert(offsetof(JournalEntry, entry_type) == 0,   "JournalEntry.entry_type offset");
_Static_assert(offsetof(JournalEntry, addr)       == 8,   "JournalEntry.addr offset");
_Static_assert(offsetof(JournalEntry, key)        == 40,  "JournalEntry.key offset");
_Static_assert(offsetof(JournalEntry, old_val)    == 72,  "JournalEntry.old_val offset");

/* =========================================================================
 * LogEntry — recorded on LOG-N. Variable-length data field; we store the
 * length and a pointer into a separate log-data region.
 *
 *   self_addr  : 32B — emitting contract
 *   n_topics   : u8  — 0..4
 *   topics[4]  : up to 4 × 32B (unused slots zeroed)
 *   data_ptr   : u64 — pointer into log_data region
 *   data_len   : u64 — bytes
 *
 * 176 bytes. Aligned to 8.
 * ========================================================================= */

typedef struct {
    u256_t   self_addr;     /* offset  0 */
    uint8_t  n_topics;      /* offset 32 */
    uint8_t  pad[7];        /* offset 33..39 — align */
    u256_t   topics[4];     /* offset 40 (4 × 32 = 128 bytes) */
    uint64_t data_ptr;      /* offset 168 */
    uint64_t data_len;      /* offset 176 */
} LogEntry;

_Static_assert(sizeof(LogEntry) == 184, "LogEntry must be 184 bytes");
_Static_assert(offsetof(LogEntry, self_addr) == 0,   "LogEntry.self_addr offset");
_Static_assert(offsetof(LogEntry, n_topics)  == 32,  "LogEntry.n_topics offset");
_Static_assert(offsetof(LogEntry, topics)    == 40,  "LogEntry.topics offset");
_Static_assert(offsetof(LogEntry, data_ptr)  == 168, "LogEntry.data_ptr offset");
_Static_assert(offsetof(LogEntry, data_len)  == 176, "LogEntry.data_len offset");

/* =========================================================================
 * TxArena — counters + region pointers. Field order is chosen so the
 * counters (read+written by handlers) all sit in the first cache line.
 *
 *   journal_count    u64 — number of entries currently in journal
 *   log_count        u64 — number of log records currently in logs
 *   journal_data     ptr — base of journal entry array
 *   log_data         ptr — base of log entry array
 *   log_blob_ptr     ptr — current bump pointer in log-data blob region
 *   journal_cap      u64 — capacity (for bounds check on debug builds)
 *   log_cap          u64 — capacity
 *   log_blob_cap     u64 — capacity of log-data blob region
 *   tx_state         ptr — per-tx TxState tables (tx_state.h); shared by
 *                          every frame arena of the tx
 *
 * 72 bytes.
 * ========================================================================= */

struct TxState;

typedef struct {
    uint64_t        journal_count;    /* offset  0 */
    uint64_t        log_count;        /* offset  8 */
    JournalEntry   *journal_data;     /* offset 16 */
    LogEntry       *log_data;         /* offset 24 */
    uint8_t        *log_blob_ptr;     /* offset 32 */
    uint64_t        journal_cap;      /* offset 40 */
    uint64_t        log_cap;          /* offset 48 */
    uint64_t        log_blob_cap;     /* offset 56 */
    struct TxState *tx_state;         /* offset 64 */
} TxArena;

_Static_assert(sizeof(TxArena) == 72, "TxArena must be 72 bytes");
_Static_assert(offsetof(TxArena, journal_count) == 0,  "TxArena.journal_count offset");
_Static_assert(offsetof(TxArena, log_count)     == 8,  "TxArena.log_count offset");
_Static_assert(offsetof(TxArena, journal_data)  == 16, "TxArena.journal_data offset");
_Static_assert(offsetof(TxArena, log_data)      == 24, "TxArena.log_data offset");
_Static_assert(offsetof(TxArena, log_blob_ptr)  == 32, "TxArena.log_blob_ptr offset");
_Static_assert(offsetof(TxArena, journal_cap)   == 40, "TxArena.journal_cap offset");
_Static_assert(offsetof(TxArena, log_cap)       == 48, "TxArena.log_cap offset");
_Static_assert(offsetof(TxArena, log_blob_cap)  == 56, "TxArena.log_blob_cap offset");
_Static_assert(offsetof(TxArena, tx_state)      == 64, "TxArena.tx_state offset");

/* Reset arena counters at start of a new tx (data regions stay allocated;
 * old entries simply get overwritten). Called by the host, never by the
 * threaded interpreter. */
static inline void tx_arena_reset(TxArena *a) {
    a->journal_count = 0;
    a->log_count = 0;
    if (a->log_data) a->log_blob_ptr = (uint8_t *)a->log_data + sizeof(LogEntry) * a->log_cap;
}

#ifdef __cplusplus
}
#endif

#endif /* EITA_TX_ARENA_H */
