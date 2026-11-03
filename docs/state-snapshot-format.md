# Eita State Snapshot Format (v1)

Design for the immutable on-disk state tier of the honest-client direction
(#267 redirection, 2026-07-13). A snapshot is the **point-in-time flat state
after block N**, written at a checkpoint, never mutated. Together with the
in-RAM delta (the existing world hashtables) it replaces "hold the whole chain
in RAM" — and replaces MDBX, which we rejected: deterministic-fold recovery
(rewind to checkpoint + redrive the ledger) removes any need for a
transactional KV store. What remains is exactly this: sorted, fixed-width,
mmap-friendly flat files.

**Design point:** ≤ 1 disk read per cold point lookup; pure sequential I/O for
scans (checkpoint merge, #237 root check); zero decode (fixed layouts, no
protobuf/varint — we control both writer and reader).

## Goals / non-goals

Goals: point lookup by `addr` and `(addr, slot)` (the fault-hook miss path);
full ordered iteration (checkpoint writer, state-root check, `dump-state-root`
class of users); crash-safety by immutability + atomic publish; bootstrap by
conversion from reth/erigon/geth flat state; one format across chains
(mainnet, Base, OP, World).

Non-goals (v1): history (a snapshot is one block's state; older snapshots are
retained or GC'd wholesale); intra-file mutation; MPT nodes (State-not-MPT —
#237 recomputes the root from the flat state when honesty demands it);
compression (deferred to v2: addr-prefix grouping, zstd cold blocks, layered
deltas).

## Directory layout

```
snap-<chainid>-<block>/
  MANIFEST.sexp
  accounts.dat      sorted by addr;          96 B records
  storage.dat       sorted by (addr, slot);  88 B records
  code.dat          sorted by codehash;      variable-length, 8-aligned
  code.idx          sorted (codehash, off);  40 B entries
```

Atomic publish: write into `.tmp-snap-<chainid>-<block>/`, fsync every file,
`rename(2)` the directory. A snapshot directory either exists completely or
not at all. Readers mmap the `.dat` files read-only; immutability makes
concurrent readers trivially safe and lets N processes share one snapshot
(page cache dedups).

## Byte conventions

Everything is **big-endian**, one rule, no exceptions. Keys sort by `memcmp`,
which is then numeric order; u256 values are EVM-natural byte order (what RLP,
keccak preimages, and #237 want — no swapping at the trust-sensitive edge).
Records are 8-byte aligned. Each `.dat`/`.idx` file opens with a 4096-byte
header (page-aligned data start):

```
off  size  field
0    8     magic   "EITASNAP"
8    4     version u32 = 1
12   4     table   u32  (1=accounts 2=storage 3=code 6=code-idx; 4/5 retired, see below)
16   8     count   u64  record count (code.dat: blob count)
24   8     chainid u64
32   8     block   u64
40   4     recsize u32  (0 for variable-length code.dat)
44   4     stride  u32  (retired accounts/storage idx: K; else 0)
48   ...   zero padding to 4096
```

## Record layouts

### accounts.dat — 96 B, sorted by addr

```
off  size  field
0    20    addr
20   4     flags      bit0 = EXISTS_EMPTY (see semantics); rest 0
24   8     nonce      u64
32   32    balance    u256
64   32    codehash   keccak256(code); keccak256("") = c5d24601... for codeless
```

### storage.dat — 88 B, sorted by (addr, slot) as one 52-byte memcmp key

```
0    20    addr
20   32    slot
52   32    value      u256, never zero (see semantics)
84   4     pad        zero
```

### code.dat — variable, sorted by codehash

```
0    32    codehash
32   4     len        u32
36   len   bytes
...  pad   zero to 8-byte alignment
```

### Index files

`code.idx`: explicit 40 B entries `codehash(32) | offset(8)` since code
records are variable-length; derivable from `code.dat`.

**Retired (2026-10-28):** `accounts.idx` / `storage.idx` (table 4/5, the key of
every `K`th record, `K = stride`, manifest `:idx-stride`). The fence below
replaced them; new snapshots and layers no longer contain them. An older
snapshot that does keeps working unchanged: its manifest lists them, so
`snap-sealed-p` and `snap-verify` check them and its content hash (computed
over the manifest's file list) is what it always was; the reader never maps
them. A new snapshot's file list has four files, so its content hash differs
from what the old writer would have produced for the same state. Recovery and
GC work on whole directories and manifests, so both kinds are picked and
deleted alike, and a stack may mix them (an old base under new layers).

### Lookup algorithm and cost

```
lookup(key):                           (src/state/snapshot.lisp `lower-bound`)
  fence node: the key's next R bits → bucket [A[p], A[p+1])      (RAM)
  bucket over 512 records → its child node, keyed by the bits after
    the bucket's common prefix (a big contract's slots: the slot)
  binary-search the bucket            (~7 probes in ~11 KiB; ≤ 512 records)
```

The **fence** of `accounts.dat` and of `storage.dat` is an in-memory radix
index built when the snapshot is opened (one pass over the keys, one more over
each big bucket), aiming at 64–128 records per bucket, 4 bytes per bucket. At
4.9M (21.9M accounts, 35.8M slots) it is 5.7 MB and builds in 0.8 s from the
page cache; at 150M / 550M about 80 MB and 11 s. The replay opens a compacted
base on the compactor thread, so the build never runs on the replay thread
after resume; the root checker builds one for its base only under layers (a
plain base check only scans). Measured on the replay's own lookups at 4.9M:
accounts 0.92 → 0.49 µs, slots 1.04 → 0.57 µs, a slot run's start 2.5 →
0.95 µs. The cost left is the cold record's page: one miss, where the window
search took about ten.

## Semantics (the part that must match the trie)

These rules make snapshot contents bijective with trie contents, which is what
lets #237 gate honesty:

- **S1 — inclusion:** an account record exists **iff** the account is in the
  trie: non-empty (nonce>0 ∨ balance>0 ∨ code≠ε) **or** empty-but-present, in
  which case `EXISTS_EMPTY` is set. This is exactly `dump-state-root`'s
  inclusion rule and the `world-accounts` existence set (EIP-161, #271).
  Absent record ⇒ account does not exist.
- **S2 — storage:** a slot record exists **iff** value ≠ 0. Absent ⇒ 0.
  (Matches `world-storage-set`'s remhash-on-zero and trie semantics.)
- **S3 — code integrity:** every `codehash` in accounts.dat other than
  keccak256("") has exactly one code.dat record. Code is content-addressed and
  deduplicated.
- **S4 — sortedness:** each table strictly ascending by its memcmp key
  (no duplicate keys).
- **S5 — orphan slots forbidden:** every distinct `addr` in storage.dat has an
  accounts.dat record. Note the EIP-161 subtlety (#271): emptiness ignores
  storage, so an account can be storage-bearing yet "empty" (nonce=0,
  balance=0, no code). If such an account is in the trie, S1 still demands a
  record, and only `EXISTS_EMPTY` can witness it — the writer/importer must
  set the flag rather than drop the account, or its slots would be orphaned
  and the recomputed root would drift.

## MANIFEST.sexp

```lisp
(:version 1
 :chain-id 8453 :chain "base"
 :block 31900000
 :state-root  "0x…"          ; canonical header stateRoot at :block
 :root-checked t             ; set ONLY after #237 verifies it from these files
 :counts (:accounts N :slots N :codes N)
 :sha256 (("accounts.dat" "…") ("storage.dat" "…") ("code.dat" "…") ("code.idx" "…"))
 :provenance "imported reth-1.3/mdbx @ block …"  ; or "eita checkpoint of snap-…"
 :created "2026-07-13T…")
```

`:root-checked nil` snapshots are quarantined: usable for experiments, never
as the base of a run that claims honesty. The root check (#237) recomputes the
MPT root from a full scan and compares to `:state-root`; `sha256` (we already
have `lean/c/sha256.c`) covers at-rest integrity, the root covers semantic
integrity — different failure classes, keep both.

## Integration with the engine (audited seam, 2026-07-13)

The read-miss seam already exists and is proven by the lazy-RPC Base backend:
`*fault-account-hook*` / `*fault-slot-hook*` (src/evm/ ~L1069) fire at
14 choke points before world-table access. The snapshot backend is the same
shape with the RPC swapped for the file:

```lisp
snap-fault-account(addr):                 ;; mirrors base-fault-account
  unless faulted(addr):
    rec ← eita_snap_account(addr)         ;; C helper, mmap bsearch
    when rec: install balance/nonce/code into world tables
              (EXISTS_EMPTY ⇒ world-accounts insert)
    mark faulted(addr)                    ;; absent is cached too

snap-fault-slot(addr, slot): analogous via eita_snap_slot.
```

**Tier semantics** (who is authoritative):

- `faulted(x)` set ⇒ **RAM is authoritative** for x — including authoritative
  absence (selfdestruct/EIP-161 sweep leave remhash'd tables + faulted bit =
  a tombstone; the snapshot value is dead).
- Not faulted ⇒ snapshot is authoritative; any access must go through the
  fault first. Grow-only mode gets this from the 14 choke points today;
  **eviction mode requires the accessor-ization refactor first** (121 direct
  gethash sites would silently read evicted-as-zero — the audited precondition).
- `dirty(x)`: written since the last checkpoint (derivable from the journal's
  committed writes). **Evictable iff faulted ∧ ¬dirty.** Dirty entries pin
  until the next checkpoint persists them.

**Checkpoint writer** = one sequential merge: scan old snapshot ⋈ sorted dirty
set → new snapshot directory (then dirty set clears, eviction candidates
unpin). The same merged iterator feeds #237's root computation —
`dump-state-root`'s walk + inclusion rule generalizes into it. Write cost is
sequential (~150 GB ≈ minutes on NVMe, mainnet-scale; Base ~10× less);
frequency is a knob since recovery = last snapshot + redrive.

**C reader API** (new `c/snapshot.c`, linked into libeita; plain C, callable
from the Lisp fault hooks and later from Lean via the usual wrapper split):

```c
typedef struct { uint8_t flags; uint64_t nonce;
                 uint8_t balance[32], codehash[32]; } EitaSnapAccount;
int  eita_snap_open   (const char *dir);                       /* handle ≥0 */
int  eita_snap_account(int h, const uint8_t addr[20], EitaSnapAccount *out);
int  eita_snap_slot   (int h, const uint8_t addr[20],
                       const uint8_t slot[32], uint8_t val[32]);   /* 1/0 */
int64_t eita_snap_code(int h, const uint8_t hash[32], const uint8_t **p);
/* ordered full scans for merge / root check: */
int  eita_snap_iter_accounts(int h, ...cursor...);
int  eita_snap_iter_storage (int h, ...cursor...);
void eita_snap_close  (int h);
```

## Bootstrap (import from other clients)

reth and erigon keep current flat state in MDBX already sorted by our keys
(`PlainState`: addr → account, addr‖incarnation‖slot → value), so import is a
streaming walk emitting `.dat` files in order — no sort pass, no trie
traversal. geth's `geth snapshot dump` is an alternative source. The imported
snapshot is untrusted until #237 verifies `:state-root` against the canonical
header — that check **is** the honesty boundary; nothing downstream trusts a
snapshot without `:root-checked t`.

## Trust surface & validation plan

`c/snapshot.c` (reader), the checkpoint writer, and the importer are
unverified code adjacent to consensus state — treated like the other host
seams (minimal, explicit, tested before load-bearing):

1. **Round-trip property tests:** random worlds → write → read back
   (point lookups + full scan) → structurally equal; S1–S5 checked.
2. **A/B replay:** Base lazy replay from a snapshot vs from per-slot RPC over
   the same block range — bit-exact gas/state gates (the same methodology that
   validated #269/#270).
3. **Root gate:** #237 at import and at every checkpoint. A root mismatch
   quarantines the snapshot, never "warns".
4. Lean involvement starts where it pays: the merge iterator's semantics
   (snapshot ⋈ delta = post-state) once eviction lands, and the projection
   theorem (`OpportunityState = Project(SerialExecution)`) sits above this
   layer untouched.

## Sizing (order of magnitude, mid-2026)

| chain | accounts | slots | accounts.dat | storage.dat | code | total |
|---|---|---|---|---|---|---|
| mainnet | ~320 M | ~1.4 B | ~31 GB | ~123 GB | ~5 GB | ~160 GB |
| Base | ~40 M | ~180 M | ~4 GB | ~16 GB | ~1 GB | ~21 GB |

Plus one retained previous snapshot during checkpoint transitions (2× peak
disk). vvv1's 40 GB handles a Base-class chain only; mainnet needs the
big-NVMe box (full_chain_aws).

## Deferred to v2 (explicitly out)

Addr-prefix grouping in storage.dat (per-contract headers, ~20 B/slot saved);
layered delta snapshots (LSM-lite) if full-merge checkpoints prove too
frequent; zstd for cold blocks; shared-code table across chain instances of
the same L2 stack.

## Layers (2026-10-26)

A delta layer `layer-P-N/` (`docs/layered-snapshots.md`) uses this format for what blocks
P+1..N changed, over a base and the layers below it: every mentioned address has an account
record with its fields (flags bit 0 = the existence mark, bit 2 = WIPED: the storage below
is gone), slot records may be 0 (a tombstone), `code.dat` holds only codes not already
below, and the manifest adds `:kind :layer :parent P`. A manifest without `:kind` is a base.

