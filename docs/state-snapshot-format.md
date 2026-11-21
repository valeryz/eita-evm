# Eita State Snapshot Format (v1; v2 specified below)

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
after resume; the root checker builds them for its layers only (it scans the
base: a layered address takes the base records the scan is at). Measured on
the replay's own lookups at 4.9M: accounts 0.92 → 0.49 µs, slots 1.04 →
0.57 µs, a slot run's start 2.5 → 0.95 µs. The cost left is the cold record's page:
one miss, where the window search took about ten.

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

## Deferred (explicitly out of v1 and v2)

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

## v2: hashed key order and the frontier (specified 2026-11-21, not yet built)

v2 sorts every record by the key the state trie uses, `keccak(addr)` and `keccak(slot)`.
A trie's leaves under one nibble prefix are then one contiguous range of the file, which
is what a per-block state root needs: a root worker in the replay's process keeps the
**frontier** (the reference of every subtrie at a fixed depth) and rebuilds only the
subtries a block's writes dirty, from those ranges. v2 replaces the anchor root-check child
process, its bucket files, the fence pass at open and minor compaction. Bases and layers
share the format. The engine reads v2 only; v1 is read only by the converter (below).

What is written first, before any code (spec first):

| | where | status |
|---|---|---|
| the frontier algorithm | `lean/Evm/Trie/Frontier.lean` | locality (F1) and the update (F2) proved; decomposition (L2), emission (L1′), the two levels (L4) and the worker's refinement gap (R) stated, `sorry` |
| `compose-range` | `lean/Evm/Persist/Layered.lean` Part E | proved (`viewRange_slot`, `viewRange_acct`) |
| the frontier component in recovery and GC | `Layered.lean` Part D (`Comp.frontier`) | proved (`gc_keeps_resume_components`); `recoveryVectors` emits it |
| the root worker's protocol | `verify/protocols/EitaVeil/RootWorker.lean` | safe: inductive invariant, kernel-checked VCs |
| the stack under P2–P3, with the worker as a reader | `verify/protocols/EitaVeil/CompactionV2.lean` | safe: inductive invariant, kernel-checked VCs |

The models cite the code they describe as `@planned` (`verify/protocols/CheckCode.lean`
lists each name with the section below that specifies it); the check fails once the code
exists, so each citation becomes `@code` in the PR that writes it.

### v2 files

| file | sorted by | record | table id | change from v1 |
|---|---|---|---:|---|
| `accounts.dat` | `hkey = keccak(addr)` | 128 B | 1 | key; +32 B |
| `storage.dat` | `haddr ‖ hslot` (one 64-byte memcmp key) | 96 B | 2 | key; the raw slot is dropped |
| `code.dat`, `code.idx` | codehash | as v1 | 3, 6 | none |
| `accounts.fnc`, `storage.fnc` | — | the persisted fence | 7, 8 | new |
| `MANIFEST.sexp` | — | `:version 2 :key-order :hashed` | — | version, both fences listed |

The 4,096-byte header is v1's with `version` = 2. Byte order (big-endian, memcmp) and the
atomic publish (`.tmp-…/`, every file fsynced, `rename(2)`, the parent fsynced) are
unchanged. The manifest's file list includes the fences, so the content hash covers them.

### v2 records and semantics

```
accounts.dat (128 B)                          storage.dat (96 B)
 off size                                      off size
  0   32  hkey      keccak(addr)                 0   32  haddr   keccak(addr)
 32   20  addr      kept for exports, metrics   32   32  hslot   keccak(slot)
                    and the fault path's check  64   32  value   u256; never 0 in a base,
 52    4  flags     bit0 EXISTS_EMPTY / mark                     0 = a tombstone in a layer
                    bit2 WIPED (layers)
 56    8  nonce     u64
 64   32  balance   u256
 96   32  codehash
```

S1 (inclusion), S2 (no zero slot in a base) and S3 (code integrity) are unchanged. S4: each
table strictly ascending by `hkey`, or by `(haddr, hslot)`. S5: every `haddr` of
`storage.dat` has an `accounts.dat` record with that `hkey`. The raw slot number leaves the
snapshot: it is in every `storage_diff` row of the fact log already. Lookups by raw slot
(the execution fault, `view-slot`) hash the slot first (~0.5 µs). Two consequences:

* **`storage-wipe-journaled!` becomes a journaled WIPED flag.** EELS `destroy_storage` at a
  creation onto an address with storage cannot enumerate cold slots by raw key any more;
  the cold tier already reads 0 under a set flag (`snap-fault-slot`, as after a
  SELFDESTRUCT), RAM slots are still journaled one by one, and observers get one
  `storage_wipe` event instead of a row per cold slot. The effect contract (= EELS
  `destroy_storage` on the view) is unchanged.
* A raw-slot export of a whole contract comes from the fact log, not the snapshot.

Sizes, Ethereum at 26.33M (432.4M accounts, 1.69B slots): `accounts.dat` 55.3 GB,
`storage.dat` 162.2 GB, fences ≈ 0.13 GB; about 230 GB in all (v1: 193–206 GB). Arc at
2.96M accounts and 76M slots: about 10.1 GB.

### v2 index: the persisted fence

The fence is v1's radix index (`fence-node`: buckets of 64–128 records, a child node for a
bucket over 512 records, keyed by the bits after its common prefix), unchanged: it does not
depend on the key. Hashed account keys are uniform and get no children (432M records: r =
22, 16 MB); storage keeps children where a contract is large (by `hslot` bits). The
**writer builds it** in its pass (the top level fills as records are emitted, a child right
after its bucket closes, from the page cache) and persists it:

```
<name>.fnc: the 4,096-byte header (table 7 or 8), then the nodes, root first:
  node:  bit u32 · r u32 · nkids u32 · a[2^r + 1] u32 · nkids × (bucket u32 · child-offset u64)
```

Opening a snapshot maps its fence: the open-time fence build, its thread and `snap-open`'s
`:background`/`:scan` modes go.

### v2 layers

A layer keeps v1's layer rules (every mentioned address has its account record with its
fields: FieldsCover; WIPED; tombstones; `:kind :layer :parent P`) over hashed keys. It also
gets, at open:

* the address Bloom filter, keyed by `hkey` (its bits are uniform: no rehash);
* an **account-prefix bitmap** of 16^D bits (2 MB at D = 6, 8 KB at D = 4), from
  `accounts.dat`: does this layer hold anything in account bucket p, with no I/O. The worker
  asks it for every dirty bucket through every disk layer.

### v2 compose-range

`compose-range (sources lo hi)` is the one merge primitive: a k-way merge, over a key range,
of the sources' ascending runs, newest first (the worker's delta, then the layers, then the
base). On equal keys the newest source wins; a slot run stops at the first source whose
account record there is WIPED; tombstones are dropped when the base is included; the caller
applies S1 to accounts. It is Lean's `composeRuns` (`Persist/Layered.lean` Part E), proved to
be the stack's lookup on the range (`viewRange_slot`, `viewRange_acct`). It replaces
`compose-address`, `map-touched-addresses` and their `:base-at` plumbing.

| caller | range | sources |
|---|---|---|
| an execution fault (`view-account`, `view-slot`) | one key | the layers, the base |
| the worker, account bucket p | `[p·0…, (p+1)·0…)` over `hkey` | delta, disk layers, base |
| the worker, storage bucket q of contract c | `[haddr_c ‖ q·0…, …)` | delta, disk layers, base |
| major compaction, the full-pass root, the converter | everything | the layers, the base |

### The frontier (frontier-N/)

**One depth rule for every trie**: a trie of n leaves has frontier depth `d(n) =
round(log16(n / 32))`, and 0 when n < 128 (rebuilt whole). That gives D = 6 for Ethereum's
account trie (about 26 accounts a bucket), D = 4 on Arc, and per contract its own `d_c`. A
region keeps its depth until `|log16(n / 32) − d| > 0.75` (hysteresis); a promotion happens
at n > 256.

**DenseAbove(d)**: every prefix shorter than d with keys under it is a branch with two or
more children (Lean `DenseAbove`). It is checked at run time on every dense branch the
worker recomputes; when it fails, that trie is rebuilt whole in the same block and re-laid at
a lower depth (Lean `Trie1.root`'s fallback). Every entry is a 32-byte keccak (a subtrie at
depth ≤ 6 over 32-byte keys encodes to at least 33 bytes); thirty-two zero bytes mean no
keys under the prefix; a short (inline) encoding is a hard error.

`frontier-N/` is a component of anchor N, written by the root worker:

| file | content | layout |
|---|---|---|
| `accounts.frt` | levels D…1 of the account trie, bottom level first | 4 KB header; level D at offset 0, page-aligned, then D−1, …, 1. The entry for prefix q at level k is at `off[k] + 32·q` |
| `storage.dir` | one 64-byte record per contract with a region, sorted by `haddr`: `haddr 32 · d u8 · flags u8 · pad 6 · n_c u64 · offset u64 · pad 8` | resident |
| `storage.frt` | one region per contract: levels d_c…1, bottom first, as `accounts.frt` | a region with d ≥ 2 starts on a 4 KiB boundary; d = 1 regions are 512 B, 512-aligned, eight to a page |
| `roots.dat` | `haddr 32 · storage root 32`, sorted, one record per account with storage | an account bucket's records are contiguous |
| `roots.idx` | 2^20 × u32: the first `roots.dat` record of each top-20-bit prefix | resident |
| `MANIFEST.sexp` | `:version 2 :kind :frontier :block N :state-root R :t 32 :hysteresis 0.75 :account-depth D :counts (:accounts n :storage n :regions k)`, the files with sizes and FNV, `:content-hash` | |

Ethereum: 5.15 GB per anchor (`accounts.frt` 0.57 GB, `storage.frt` 2.75 GB, `roots.dat`
1.8 GB); Arc under 0.2 GB. The bottom level first keeps every level of 8 KiB or more
page-aligned with no padding; a dirty bucket's entry and its 15 siblings (512 B) share one
page.

Who touches it: the worker writes it (at every anchor; the converter once) and is its only
reader; execution never reads it. Major compaction checks it entry by entry at its base
block; a resume self-checks its dense levels against the root.

### The frontier checkpoint

At anchor N, at its block boundary N, the worker freezes its overlay (lookups go new
overlay, frozen overlay, file), copies the account region (~0.1 s, its one pause), and a
background thread merges `frontier-A/` with the frozen overlay into `.tmp-frontier-N/` (one
sequential pass), fsyncs it, renames it and fsyncs the parent. Two rules (found by the
RootWorker model):

* the worker **publishes frontier-N only after verdict(N) passed**, and reports
  "frontier-N published for (N, hash)" to the replay thread;
* it **swaps to frontier-N only once N is below the reorg floor** (settled): until then it
  keeps mapping `frontier-A/` under the frozen overlay, so a rollback below N never unmaps
  the frontier it reads. At the swap it drops the frozen overlay and unpins `frontier-A/`.

Cost: 5.15 GB written per Ethereum anchor (every ~1.4 days at the tip; 11–21 MB/s at
catch-up's 25–45 blocks/s).

### The root worker

One coordinator and a pool of `root-check-threads` (half the hardware threads, at most 16).
No new environment toggle: at the tip (`at-tip-p`) the interval is one block; in catch-up a
constant 256, cut at every anchor and at the switch to the tip.

```lisp
(root-worker-start! frontier-dir composition block)  ; resume, genesis, after conversion
(root-verdict n hash &key wait-ms)    ; → (values :valid | :invalid | :pending  computed-root)
(root-worker-view! base disk-layers)  ; replay thread, under *stack-lock*: a layer publish or a swap
(root-worker-checkpoint! n)           ; anchor N
(root-worker-drop-above! f)           ; called by rollback-to! only
(root-worker-stop!)
```

Verdicts are keyed by (number, hash): a verdict computed for an abandoned branch never
answers for the new branch's block of the same number.

What it holds (Ethereum, *est.*): the account region (levels D…1, 0.57 GB, RAM); the
mapped `frontier-A/` (23 MB resident); the overlay of storage-frontier entries, roots and
directory changes since its checkpoint (≤ 0.28 GB at 10,000 blocks); the delta, the leaves
written since its newest disk layer by hashed key with their last-write block (≤ 0.15 GB at
2,500 blocks); the undo log of the reorg window (10 MB at 64 blocks); the current interval's
write sets (≤ 35 MB). About 1.0 GB steady, +0.6 GB for seconds at a checkpoint.

### The root worker's input

The per-block **write set** on the event stream (subscriber `root`, bounded in blocks and
bytes), net over the block, at its boundary, over every `tx-end` summary of the block (user
transactions and the pre/post-block pseudo-transactions alike): per account `addr` and its
post nonce, balance, codehash, **existence mark** and **wiped**; per slot `addr`, `slot` and
post value; the header's `stateRoot` and hash. `do-account-changes`
(`evm/observe-tx.lisp`) gains the two missing kinds (existence-only changes: an EIP-161
deletion, the pre-Spurious mark; storage wipes: a pre-Cancun SELFDESTRUCT and the creation
wipe), and so does the fact log (`account_diff` and a `storage_wipe` row): one summary, two
consumers. A key missing from the write set shows as a root mismatch at that block. The
worker hashes the keys in batch on its pool.

### One block

1. **Ingest**: hash the keys, fold them into the delta (recording undo), collect the dirty
   contracts and dirty account buckets.
2. **Storage**, contracts in parallel. A wipe drops the contract's region (rebuilt as new
   from the slots written after it). No region (n_c < 128): compose the contract's range,
   stream it into the stack trie (`st-push`/`st-finish`, Lean `Trie.Stack`), take its root,
   count n_c, and promote past n > 256 (the same pass emits the region: Lean
   `buildFrontier`). A region at d_c: per dirty bucket compose `[haddr_c ‖ q]`, build the
   subtrie at depth d_c into the overlay (Lean `stepFrontier`: F1/F2), count Δn while
   merging, recompute the distinct dirty dense parents upward (Lean `refAt`; a clean
   parent keeps its reference, `refAt_step_clean`), checking DenseAbove. A giant contract's
   buckets spread over the pool. Write `roots[haddr_c]` into the overlay (n_c = 0 removes
   it).
3. **Accounts**, buckets in parallel, over the buckets of the written accounts and of every
   contract whose root changed: skip the disk layers whose prefix bitmap is clear, compose
   the bucket, apply S1 (storage present iff a root), build the leaves with their roots
   (overlay, then `roots.dat`), the subtrie at depth D, then levels D−1…1 and the root.
4. **Verdict**: compare with the header root, publish `(n, hash, root, ok)`. At the tip a
   mismatch stops the chain at the source block (during the shadow period: an alert and
   "unverified", re-seeded at the next anchor). In catch-up a mismatched interval is
   bisected: undo to its start, re-run it block by block from the kept write sets.
5. **Undo bookkeeping**: records below the reorg floor are dropped.

Backpressure: at the tip the queue holds two blocks (N + 1 executes while N's root
computes); in catch-up the subscriber folds the next interval while the pool computes the
current one, and the stream's bounded pipe blocks the replay only when both are full.
Layout changes (a promotion, a re-lay past the hysteresis, a demotion after a DenseAbove
failure, the account trie's D on a growing chain) are a background rebuild of one region: pin
the view at block M, stream the composed range with frontier emission, keep the old region
current meanwhile, then recompute the buckets dirtied since M and swap. Correctness never
waits on a rebuild (DenseAbove's fallback is the whole rebuild in the same block).

### The root worker's view

The worker adopts a disk layer, or a compacted base, at its first block boundary at or past
it: it reads base and disk layers once under `*stack-lock*` (as `live-components` does),
pins them, then trims the delta entries whose last write is at or below the new layer. It
never reads a RAM layer. GC (`live-components`) and `close-retired!` wait for its pin, as for
the writer and the compactor: a retired snap the worker pins stays mapped until it adopts
the next view (CompactionV2).

### Reorgs: drop-above!

`rollback-to!` is the one owner; it calls `(root-worker-drop-above! f)`, which waits for the
worker's block boundary, then discards the queued write sets above F, pops the undo log
above F (frontier entries, roots, regions, delta, counts), forgets the verdicts and
checkpoint reports above F, aborts a checkpoint above F and deletes a published, unanchored
`frontier-N/` above F (else the new branch's checkpoint at N would rename onto the abandoned
branch's directory). A fork below the reorg floor is refused. Under P3 every disk layer is at
or below the floor, so the worker's view never rolls back (RootWorker: after `drop-above! F`
the worker's consumed blocks are exactly the chain up to its block).

### Layers under v2: the RAM window

* **The window** (`reorg-window`: 64 on Ethereum, 0 on Arc) holds one frozen RAM layer per
  block. A rollback inside it drops only RAM layers: the writer and the compactor work at or
  below the floor, so `rollback-to!` neither drains the writer nor joins the compactor.
* **Settling**: a block leaving the window is folded into the one open **settled RAM
  layer** (Lean `compose` on the RAM tables, newest wins; it keeps FieldsCover,
  `fieldsCover_compose`).
* **Disk layers**: the settled layer is handed to the writer at the next **quarter-anchor
  point** (or earlier by the state budget) and written as one disk layer: four disk layers
  per anchor at the tip, the worker's delta bounded by 2,500 blocks, ~50 MB of RAM layers in
  the window.
* **Minor compaction is deleted** (`minor-run`, `+max-layers+`, the `:minor` job).
* Major compaction fires at base/8 bytes or at **32 disk layers**.

### Compaction to a verified anchor

1. Pick the newest verified anchor A whose layers are all on disk (under P3 it is below the
   floor).
2. Merge the base and the layers up to A into `.tmp-snap-A/` with `compose-range`: one
   sequential write, fences emitted.
3. **The root in the same pass**: every 1/256 of the key space the writer completes, a pool
   thread reads that range back from the page cache, streams each contract's storage into its
   root (a giant contract splits by `hslot` nibble), then its accounts' subtrie;
   `split-root` combines the 256 subtries. The emitted frontier entries are compared with
   `frontier-A/` entry by entry (same D and d_c).
4. Root = the header root at A **and** every entry equal: fsync, rename, append the line
   `(A … "sA.h+fA.h")`, swap at once. Otherwise discard the tmp directory and stop loudly.

There is no pending compacted base: `*compacting-base*`, `*base-check-due*`,
`discard-compacting-base!` and the swap's refusal path go, and with them the reorg below a
pending base (`CompactionDeepReorg`).

### Anchors

Anchors, quarter points and compaction bases sit on fact-log shard ends (N ≡ 999 mod 1000).
Anchor N is appended, as one fsynced line `(N expected computed t "sB.h+l…-N.h+fN.h")`,
only after all three components are sealed and the verdict passed:

```
 fact-log shard ending at N sealed     (durable before the layer)
 layer-P-N/ published                  (the writer, once N is settled)
 verdict (N, hash) = header root       (the worker, in RAM)
 frontier-N/ published                 (the worker's checkpoint, reported for (N, hash))
 anchors.sexp: the line N              ◀ N is a resume point
```

That replaces spawning, polling and collecting the root-check child.

### Crash consistency

| crash between | on disk | resume |
|---|---|---|
| a layer write, mid-way | `.tmp-layer-*` | removed at startup; the previous anchor A |
| layer N published, frontier-N not | sealed layer N, no line | anchor A |
| frontier-N published, line not appended | `frontier-N/`, named by no point | anchor A; GC deletes it |
| a torn anchor line | a partial last line | skipped (I1); anchor A |
| a compaction, mid-way | `.tmp-snap-*` | removed; the old base |
| `snap-A/` published, line not appended | a base named by no verified line | the old composition; GC per the rule |
| any crash | the worker's RAM state (overlay, delta, undo) | the replay and the worker restart at A with `frontier-A/`: no recompute |

### Recovery and GC

A point's components are `(:base B)`, `(:layer P N)` and `(:frontier N)` (Lean
`Comp.frontier`); the composition string appends `+fN.<hash>`. An anchored point needs all
its components sealed; GC keeps what kept points name, so it keeps their frontiers
(`gc_keeps_resume_components`), never deletes a frontier above the newest anchor (in flight)
and pins the worker's current frontier and its checkpoint's output (RootWorker). Retained
anchors hard-link `frontier-N/` too. A resume from anchor A maps `frontier-A/`, reads the
account region and starts; a background self-check recomputes the account region's dense
levels from level D (~4 s) against the header root at A and every region's top against
`roots.dat` (~18 s of CPU); the bottom entries are covered by the files' FNV
(`EITA_RESUME_VERIFY`). A resume from an unanchored point (a bisect layer) runs the nearest
`frontier-A/` below it plus the layers above as one catch-up interval. Frontiers are not
uploaded with GCS anchors: a restore recomputes them (a full pass).

### The converter (v1 → v2)

It generalizes `root.lisp`'s pass 1: read a verified v1 composition (with the merge-join of
its layers), compose, apply S1, hash `addr` and `slot`, write v2 records into 4,096 bucket
files by the top 12 bits of `hkey` / `haddr` (contracts over 1M slots into per-contract
sub-buckets by `hslot`'s top byte), sort each bucket in RAM (~55 MB) and write
`accounts.dat` / `storage.dat` with fences, then run the full-pass root over the result,
emitting `frontier-N/` at d(n) for every trie. Root = the header root at N, or the output is
discarded. Then publish `snap-N/` (v2) and `frontier-N/` and append the anchor line. Ethereum
on x300: ~417–634 GB read, ~452 GB written, 1–1.5 h unconstrained or 2–3 h under nice 19 /
ionice -c3; Arc: minutes. After the shadow period on both chains the v1 reader is deleted.

### What is proved, modelled and checked

* **Proved** (Lean, standard axioms): F1 `prefixed_update`/`subRef_update`; F2
  `frontierOK_update`/`frontierOK_step`, `refAt_congr`/`refAt_step_clean`, `assemble_congr`;
  L1′'s completeness `buildFrontier_complete`; F3 `viewRange_slot`/`viewRange_acct`; F4
  `gc_keeps_resume_components` (and the Part D lemmas over the new constructor).
* **Stated, `sorry`** (visible in `scripts/generated/verification-stats.md`):
  `patricialise_assemble` (L2), `build_emits_frontier` (L1′), `stateRoot_two_levels` (L4),
  `layered_frontier_root_eq` (R, the worker's refinement gap). `Trie1.root_step` (one trie's
  incremental root = the root of its post-state) is proved from F2 and L2, and carries L2's
  `sorry`. L2, L1′ and L4 wait on the total trie spec (`patricialise`, `nodeRef` and RLP are
  `partial def`s today) and on the order independence of `rootBytes`.
* **Modelled** (Veil, safe): `RootWorker` (verdicts exact and keyed by block; `drop-above!`
  restores the worker's state; no frontier before its verdict; the worker never maps a
  deleted frontier; the anchor line names a canonical frontier) and `CompactionV2` (the
  stack's composition and liveness under the window, settling, the writer, compaction to a
  verified anchor, GC, `close-retired!` and rollback at any depth, with the worker as a
  reader).
* **Checked at run time** where a step is not proved: the header root every block (every
  interval, bisected), DenseAbove on every recomputed dense branch, 32-byte references, the
  compaction's in-pass root and its entry-by-entry frontier comparison, the resume
  self-check.
