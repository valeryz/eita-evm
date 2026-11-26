# Eita state snapshot format

The persisted state of a replay: immutable, sorted, fixed-width files that a process maps
read-only, laid out so that one block's state root can be recomputed from the subtries its
writes touch.

**Status.** This document specifies format version 2. A chain replayed from genesis runs on
the legacy version 1 ([Appendix A](#appendix-a-legacy-format-v1)); a chain started from an
import (§10, "Import from reth") runs on version 2: its base, its layers, their compaction and
the anchors' root check (docs/layered-snapshots.md, "A stack over a version 2 base"). The
frontier and the root worker (§7, §8) are not built yet: a version 2 stack is root-checked at
anchors, as a version 1 stack is. `eita convert-snapshot` turns a verified v1 state into a
root-checked v2 base and its anchor (§10, "The converter"); it does not write the first
frontier yet. Once the chains on v1 have moved, v1 is read only by the converter. Lean definitions and
proofs, and the Veil models of the protocols, exist for the whole of v2 (§11). The Veil models
cite the code they describe with `@planned` where that code is not yet written
(`verify/protocols/CheckCode.lean` maps each such name to the section below that specifies it).

Contents: [1 Concepts](#1-concepts) · [2 Directory layout](#2-directory-layout) ·
[3 Files and records](#3-files-and-records) · [4 Semantics](#4-semantics) ·
[5 Layers](#5-layers) · [6 Composition](#6-composition) · [7 The frontier](#7-the-frontier) ·
[8 The root worker](#8-the-root-worker) · [9 Compaction and anchors](#9-compaction-and-anchors) ·
[10 Crash consistency, recovery and GC](#10-crash-consistency-recovery-and-gc) ·
[11 What is proved, modelled and checked](#11-what-is-proved-modelled-and-checked) ·
[Appendix A](#appendix-a-legacy-format-v1)

## 1. Concepts

| term | meaning |
|---|---|
| **snapshot**, **base** (`snap-B/`) | the complete flat state after block B: every account, every non-zero slot, every code |
| **layer** (`layer-P-N/`) | what blocks P+1..N changed, over the base and the layers below it; same file format |
| **stack** | one base under an ordered list of layers, oldest first; reading it gives the state at its top block |
| **RAM layer** | a layer held in the replay's heap (frozen, read-only), not yet written to disk |
| **composition** | the names and content hashes of a stack's components, e.g. `s4900000.4659a9fe…+l4900000-4902000.2b53b206…+f4902000.…` |
| **hashed key** | `hkey = keccak(addr)` for an account, `hslot = keccak(slot)` for a slot: the keys the state trie is built on |
| **frontier** (`frontier-N/`) | the reference (32-byte hash) of every subtrie at a fixed nibble depth, for the account trie and each large storage trie, at block N |
| **root worker** | the thread pool in the replay's process that recomputes the state root of every block from the frontier and the block's writes |
| **write set** | one block's net writes: per account its post fields, per slot its post value (§8, "The write set") |
| **reorg window**, **floor** | the newest `reorg-window` blocks (64 on Ethereum, 0 on Arc) may be rolled back; the floor is the oldest block outside the window |
| **anchor** | a block N at which the stack's state root matched the header and the composition is durably recorded in `anchors.sexp`; a resume point |
| **quarter point** | a block a quarter of the anchor interval apart: where a disk layer is written |
| **verdict** | the root worker's result for a block: (number, hash, computed root, match or not) |

Byte order is big-endian throughout; keys compare by `memcmp`, which is then numeric order.

## 2. Directory layout

```
<state-dir>/
  anchors.sexp                 one line per verified anchor: (N expected computed ok composition)
  snap-B/                      a base
  layer-P-N/                   a layer: blocks P+1..N
  frontier-N/                  the frontier at anchor N
  .tmp-…/                      work in progress; removed at startup

snap-B/, layer-P-N/            frontier-N/
  MANIFEST.sexp                  MANIFEST.sexp
  accounts.dat   accounts.fnc    accounts.frt
  storage.dat    storage.fnc     storage.dir   storage.frt
  code.dat       code.idx        roots.dat     roots.idx
```

Every directory is **published atomically**: written as `.tmp-<name>/`, every file fsynced,
`rename(2)` to its name, the parent directory fsynced. A published directory is never
modified; it is complete or absent. Readers map the files read-only, so any number of threads
and processes can share one.

The stack, read newest first:

```
   RAM layers (window)    blocks F+1..T   frozen in the heap, one per block
   settled RAM layer      blocks Q+1..F   blocks that left the window, folded together
   disk layers            layer-…-Q/ …    one per quarter point
   base                   snap-B/
```

## 3. Files and records

### File header

Every file except `MANIFEST.sexp` opens with a 4,096-byte header, so its data starts page
aligned:

```
off  size  field
0    8     magic    "EITASNAP"
8    4     version  u32 = 2
12   4     table    u32: 1 accounts, 2 storage, 3 code, 6 code-idx, 7 accounts fence, 8 storage fence
16   8     count    u64: records (code.dat: blobs)
24   8     chainid  u64
32   8     block    u64
40   4     recsize  u32 (0 for variable-length files)
44   4     stride   u32 = 0
48   …     zero to 4096
```

### accounts.dat and storage.dat

Records are 8-byte aligned and sorted by their key.

```
accounts.dat: 128 B, sorted by hkey          storage.dat: 96 B, sorted by (haddr, hslot)
 off size                                     off size
  0   32  hkey      keccak(addr)                0   32  haddr   keccak(addr)
 32   20  addr      the address itself         32   32  hslot   keccak(slot)
 52    4  flags     bit 0 EXISTS (§4)          64   32  value   u256
                    bit 2 WIPED (layers, §5)
 56    8  nonce     u64
 64   32  balance   u256
 96   32  codehash  keccak(code); keccak("") for no code
```

The address stays in the account record for exports and metrics and for the execution
fault's check. The raw slot number is not stored: the fact log's `storage_diff` rows carry it,
and a lookup by raw slot (`view-slot`, the execution fault) hashes it first. An imported base
(§10, "Import from reth") may not know an address: its field is then 20 zero bytes, which
the address 0x00…00 itself never has with its own `hkey`; the record a layer writes for that
account, once the replay touches it, carries the address. The replay never reads the field
(it faults an account by the address the EVM touched); it is for exports and metrics, which
must treat zero as unknown.

### code.dat and code.idx

`code.dat` holds one record per distinct code, sorted by codehash:
`codehash 32 · len u32 · bytes · zero padding to 8`. `code.idx` holds one 40-byte entry per
record, `codehash 32 · offset u64`, in the same order.

### The persisted fence (accounts.fnc, storage.fnc)

The fence is a radix index over a sorted file's keys. A node reads the key's next `r` bits
at bit offset `bit` and maps them to a bucket `[a[p], a[p+1])` of records; a bucket over 512
records has a child node keyed by the bits after the bucket's common prefix. Buckets aim at
64–128 records. A lookup is one node walk in RAM, then a binary search of at most 512 records
(about seven probes in 11 KiB): one page miss for a cold record.

Hashed account keys are uniform, so the account fence has no children (432M records: `r` =
22, 16 MB). The storage fence keeps children where a contract is large (split by `hslot`
bits). The writer builds the fence in its pass and persists it: the top level as records are
emitted (at the radix its caller's estimate of the record count gives, reduced at the end to
the one the actual count gives), then a child for each bucket over 512 records from the
records just written. After a low estimate it builds the whole fence from the records
written. Either way the fence is the one the records determine, so the content hash does not
depend on the estimate.

```
<name>.fnc: the header (table 7 or 8, count = nodes), then the nodes, root first, each
followed by its children's subtrees in bucket order:
  node:  bit u32 · r u32 · nkids u32 · a[2^r + 1] u32 · nkids × (bucket u32 · child-offset u64)
  child-offset: the child's node, in bytes from the end of the header
```

An empty table has a fence file with no nodes. Opening a snapshot reads its fences (a copy of
the file into memory); nothing is built at open.

### MANIFEST.sexp

```lisp
(:version 2 :key-order :hashed
 :chain-id 1 :block 26330000
 :state-root "0x…"                   ; the header's stateRoot at :block
 :kind :layer :parent 26329000       ; layers only; a manifest without :kind is a base
 :counts (:accounts n :slots n :codes n)
 :files (("accounts.dat" size fnv) ("accounts.fnc" size fnv) …)   ; sorted by name
 :provenance "…" :created "…"
 :root-checked t                     ; an import whose recomputed root matched (§10)
 :content-hash "…")                  ; FNV-1a 64 over the files' names, sizes and hashes
```

The content hash is what a composition names, so it covers every file, the fences included.

**Sizes** (estimates). Ethereum at 432.4M accounts and 1.69B slots: `accounts.dat` 55.3 GB,
`storage.dat` 162.2 GB, fences about 0.13 GB, about 230 GB in all. Arc at 2.96M accounts and
76M slots: about 10.1 GB.

## 4. Semantics

These rules make a base's contents correspond one to one with the state trie's leaves:

- **S1, inclusion.** An account record exists iff the account is in the trie: non-empty
  (nonce > 0, balance > 0 or code), or empty but present, in which case `EXISTS` is set.
  Emptiness ignores storage (EIP-161), so an empty account can hold storage; it is then in the
  trie, and `EXISTS` is what keeps its record. No record means the account does not exist.
- **S2, storage.** A base holds a slot record iff its value is non-zero; no record reads 0.
- **S3, code.** Every codehash other than `keccak("")` in `accounts.dat` has exactly one
  `code.dat` record. Code is content-addressed and stored once per stack.
- **S4, order.** Each table is strictly ascending by its key: `hkey`, `(haddr, hslot)`,
  codehash.
- **S5, no orphan slots.** Every `haddr` in `storage.dat` has an account record with that
  `hkey`.

Under S4 every subtrie of the state trie (a nibble prefix of the hashed key) is one contiguous
range of `accounts.dat`, and every subtrie of a contract's storage trie one contiguous range of
`storage.dat`. The frontier (§7) rests on that.

**Storage wipe.** When a contract is created on an address that already has storage (EELS
`destroy_storage`), or destroyed before Cancun, the cold slots cannot be enumerated by raw key.
The wipe is a WIPED flag on the address, set by the creation and cleared by its revert (bit 1
of journal entry 10): the cold tier reads 0 under it (`snap-fault-slot`), and slots in RAM are
journaled one by one. Observers see the slots the transaction touched, as for SELFDESTRUCT. The
effect equals EELS `destroy_storage` on the view. Both formats wipe this way.

## 5. Layers

### Layer records

A layer uses the base format with these differences:

- **FieldsCover.** Every address the layer mentions has an account record with all its
  fields (the writer takes an untouched address's fields from the stack below). Flags: bit 0 is
  the existence mark of the replay's RAM (`world-accounts`), bit 2 WIPED: the address's storage
  below this layer is gone. A deleted account is the record (0, 0, empty code, no mark).
- A slot record may hold 0: a **tombstone** that hides the value below.
- `code.dat` holds only codes the stack below does not hold.
- The manifest adds `:kind :layer :parent P`; `:state-root` is the header root at N.

At open a layer gets two in-memory filters, built from `accounts.dat`:

- an address **Bloom filter** keyed by `hkey` (k = 3, 16 bits per address; `hkey` is already
  uniform);
- an **account-prefix bitmap** of 16^D bits (2 MB at D = 6, 8 KB at D = 4; D from §7): does
  the layer hold any account under prefix p. The root worker asks it for every dirty bucket.

### The RAM reorg window

- **The window** holds one frozen RAM layer per block. A rollback inside it drops RAM layers
  only. The writer and the compactor work at or below the floor, so `rollback-to!` neither
  waits for the writer nor joins the compactor. A rollback below the floor is refused.
- **Settling.** A block leaving the window is folded into the one open **settled RAM layer**
  (Lean `compose` on the RAM tables, newest wins; it keeps FieldsCover, `fieldsCover_compose`).
- **Disk layers.** At the next quarter point (earlier if the state budget is exceeded) the
  settled layer goes to the writer and becomes one disk layer: four per anchor interval at the
  tip. The worker's delta (§8) then spans at most about 2,500 blocks, and the window's RAM
  layers about 50 MB.
- **Major compaction** (§9) runs when the layers outweigh an eighth of the base or reach 32
  disk layers. There is no other compaction.

## 6. Composition

`compose-range` is the one merge primitive: a k-way merge of the sources' ascending runs over
a key range `[lo, hi)`, newest first (the worker's delta, then the layers, then the base).
`snap-run` gives a source's run of the range through its fence.

- On equal keys the newest source wins.
- A storage run stops at the first source whose account record for that address is WIPED.
- Tombstones are dropped when the base is among the sources.
- The caller applies S1 to accounts.

It is Lean's `composeRuns` (`lean/Evm/Persist/Layered.lean`, Part E), proved equal to the
stack's lookup on the range (`viewRange_slot`, `viewRange_acct`).

| caller | range | sources |
|---|---|---|
| an execution fault (`view-account`, `view-slot`) | one key | the layers, the base |
| the worker, account bucket p | `[p·0…, (p+1)·0…)` over `hkey` | delta, disk layers, base |
| the worker, storage bucket q of contract c | `[haddr_c ‖ q·0…, haddr_c ‖ (q+1)·0…)` | delta, disk layers, base |
| major compaction, the full-pass root, the converter | everything | the layers, the base |

## 7. The frontier

```
 depth 0          root                          recomputed every block
                 /    \
 1..D-1      dense branches (DenseAbove)        recomputed where dirty
               /  |  \
 D        r_0 … r_q … r_{16^D-1}                the frontier: one 32-byte ref per prefix
             |
          leaves under prefix q                 one contiguous range of accounts.dat
                                                (§4), rebuilt when the block wrote under q
```

### Depth and DenseAbove

**One depth rule for every trie.** A trie of n leaves has frontier depth
`d(n) = round(log16(n / 32))`, and none (it is rebuilt whole) when n < 128. That gives D = 6
for Ethereum's account trie (about 26 accounts a bucket), D = 4 on Arc, and per contract its
own `d_c`. A trie keeps its depth until `|log16(n / 32) − d| > 0.75` (hysteresis); a storage
trie gets a frontier once n > 256.

**DenseAbove(d)**: every prefix shorter than d with keys under it is a branch with two or more
children (Lean `DenseAbove`). Then the levels above the frontier are determined by the frontier
entries alone. The worker checks DenseAbove on every dense branch it recomputes; when it fails,
that trie is rebuilt whole in the same block and re-laid at a lower depth (Lean `Trie1.root`'s
fallback).

Every entry is a 32-byte keccak (a subtrie at depth ≤ 6 over 32-byte keys encodes to at least
33 bytes, so it is never inlined); 32 zero bytes mean no keys under the prefix; a short
encoding is a hard error.

### The frontier files

| file | content | layout |
|---|---|---|
| `accounts.frt` | levels D…1 of the account trie, bottom level first | the header; level D at offset 0, page-aligned, then D−1, …, 1; the entry for prefix q at level k is at `off[k] + 32·q` |
| `storage.dir` | one 64-byte record per contract with a frontier, sorted by `haddr`: `haddr 32 · d u8 · flags u8 · pad 6 · n_c u64 · offset u64 · pad 8` | resident in RAM |
| `storage.frt` | one region per contract: levels d_c…1, bottom first, as `accounts.frt` | a region with d ≥ 2 starts on a 4 KiB boundary; d = 1 regions are 512 B, 512-aligned, eight to a page |
| `roots.dat` | `haddr 32 · storage root 32`, sorted, one record per account with storage | an account bucket's records are contiguous |
| `roots.idx` | 2^20 × u32: the first `roots.dat` record of each top-20-bit prefix | resident in RAM |
| `MANIFEST.sexp` | `:version 2 :kind :frontier :block N :state-root R :t 32 :hysteresis 0.75 :account-depth D :counts (:accounts n :storage n :regions k)`, the files with sizes and FNV, `:content-hash` | |

Bottom level first keeps every level of 8 KiB or more page-aligned without padding; a dirty
bucket's entry and its 15 siblings (512 B) share one page. Size per anchor: Ethereum 5.15 GB
(`accounts.frt` 0.57 GB, `storage.frt` 2.75 GB, `roots.dat` 1.8 GB), Arc under 0.2 GB.

The root worker writes `frontier-N/` (at every anchor; the converter is to write the first) and is
its only reader; execution never reads it. Major compaction checks it entry by entry at its
base block (§9); a resume self-checks its dense levels against the root (§10).

### The frontier checkpoint

At anchor N, at block boundary N, the worker freezes its overlay (lookups then go: new
overlay, frozen overlay, file), copies the account region (about 0.1 s, its one pause), and a
background thread merges `frontier-A/` (the previous anchor's) with the frozen overlay into
`.tmp-frontier-N/` in one sequential pass, fsyncs it, renames it and fsyncs the parent.

- The worker **publishes `frontier-N/` only after verdict(N) passed**, and reports
  "frontier-N published for (N, hash)" to the replay thread.
- It **swaps to `frontier-N/` only once N is below the floor**. Until then it keeps mapping
  `frontier-A/` under the frozen overlay, so a rollback below N never unmaps the frontier it
  reads. At the swap it drops the frozen overlay and unpins `frontier-A/`.

Cost: 5.15 GB written per Ethereum anchor.

## 8. The root worker

One coordinator and a pool of `root-check-threads` (half the hardware threads, at most 16).
At the tip (`at-tip-p`) it computes a root every block; in catch-up every 256 blocks, with an
interval cut at every anchor and at the switch to the tip.

### The root worker's interface

```lisp
(root-worker-start! frontier-dir composition block)  ; at resume, at genesis, after conversion
(root-verdict n hash &key wait-ms)    ; → (values :valid | :invalid | :pending  computed-root)
(root-worker-view! base disk-layers)  ; replay thread, under *stack-lock*: a layer publish or a swap
(root-worker-checkpoint! n)           ; anchor N
(root-worker-drop-above! f)           ; called by rollback-to! only
(root-worker-stop!)
```

Verdicts are keyed by (number, hash): a verdict computed on an abandoned branch never answers
for the new branch's block of the same number.

Memory (Ethereum, estimates): the account region (levels D…1, 0.57 GB); the mapped
`frontier-A/` (23 MB resident); the overlay of storage-frontier entries, roots and directory
changes since the checkpoint (≤ 0.28 GB over 10,000 blocks); the **delta**, the leaves written
since the newest disk layer, by hashed key with their last-write block (≤ 0.15 GB over 2,500
blocks); the undo log of the reorg window (10 MB over 64 blocks); the current interval's write
sets (≤ 35 MB). About 1.0 GB steady, 0.6 GB more for seconds at a checkpoint.

### The write set

The per-block write set goes on the event stream (subscriber `root`, bounded in blocks and
bytes). It is net over the block, emitted at its boundary over every `tx-end` summary of the
block (user transactions and the pre- and post-block system steps alike):

- per account: `addr`, post nonce, balance, codehash, **existence mark** and **wiped**;
- per slot: `addr`, `slot`, post value;
- the header's `stateRoot` and hash.

`do-account-changes` (`src/evm/observe-tx.lisp`) produces it, and the same summary feeds the
fact log (`account_diff`, `storage_wipe`): one summary, two consumers. This includes
existence-only changes (an EIP-161 deletion, the pre-Spurious-Dragon mark) and storage wipes. A
key missing from the write set shows as a root mismatch at that block. The worker hashes the
keys in batch on its pool.

### One block

1. **Ingest.** Hash the keys, fold them into the delta (recording undo), collect the dirty
   contracts and the dirty account buckets.
2. **Storage**, contracts in parallel. A wipe drops the contract's region (rebuilt from the
   slots written after it).
   - *No frontier* (n_c < 128): compose the contract's range, stream it into the stack trie
     (`st-push`/`st-finish`, Lean `Trie.Stack`), take its root, count n_c; past n > 256 the
     same pass emits a frontier (Lean `buildFrontier`).
   - *A frontier at d_c*: per dirty bucket compose `[haddr_c ‖ q]`, build the subtrie into
     the overlay (Lean `stepFrontier`), count Δn while merging, recompute the distinct dirty
     dense parents upward (Lean `refAt`; a clean parent keeps its reference,
     `refAt_step_clean`), checking DenseAbove. A large contract's buckets spread over the pool.
   - Write `roots[haddr_c]` into the overlay (n_c = 0 removes it).
3. **Accounts**, buckets in parallel, over the buckets of the written accounts and of every
   contract whose root changed: skip the disk layers whose prefix bitmap is clear, compose the
   bucket, apply S1 (storage present iff a root), build the leaves with their storage roots
   (overlay, then `roots.dat`), the subtrie at depth D, then levels D−1…1 and the root.
4. **Verdict.** Compare with the header root and publish `(n, hash, root, ok)`. At the tip a
   mismatch stops the chain at that block. In catch-up a mismatched interval is bisected: undo
   to its start and re-run it block by block from the kept write sets. In shadow mode (beside
   the legacy anchor root check, Appendix A) a mismatch raises an alert and marks the chain
   unverified, and the worker re-seeds at the next anchor.
5. **Undo bookkeeping.** Records below the floor are dropped.

**Backpressure.** At the tip the queue holds two blocks (N + 1 executes while N's root
computes). In catch-up the subscriber folds the next interval while the pool computes the
current one; the stream's bounded pipe blocks the replay only when both are full.

**Layout changes** (a new storage frontier, a re-lay past the hysteresis, a lower depth after a
DenseAbove failure, the account depth D of a growing chain) are a background rebuild of one
region: pin the view at block M, stream the composed range with frontier emission, keep the old
region current meanwhile, then recompute the buckets dirtied since M and swap. Correctness never
waits on a rebuild: DenseAbove's fallback is the whole rebuild in the same block.

### The root worker's view

The worker adopts a new disk layer, or a compacted base, at its first block boundary at or past
it: it reads the base and the disk layers once under `*stack-lock*` (as `live-components`
does), pins them, then trims the delta entries whose last write is at or below the new layer.
It never reads a RAM layer. GC (`live-components`) and `close-retired!` respect its pin as they
do the writer's and the compactor's: a retired snapshot the worker pins stays mapped until it
adopts the next view.

### Reorgs: drop-above!

`rollback-to!` is the one owner of a rollback. It calls `(root-worker-drop-above! f)`, which
waits for the worker's block boundary, then:

- discards the queued write sets above F;
- pops the undo log above F (frontier entries, roots, regions, delta, counts);
- forgets the verdicts and checkpoint reports above F;
- aborts a checkpoint above F and deletes a published, unanchored `frontier-N/` above F (else
  the new branch's checkpoint at N would rename onto the abandoned branch's directory).

A fork below the floor is refused. Every disk layer is at or below the floor, so the worker's
view never rolls back.

## 9. Compaction and anchors

### Compaction to a verified anchor

1. Pick the newest verified anchor A whose layers are all on disk (it is below the floor).
2. Merge the base and the layers up to A into `.tmp-snap-A/` with `compose-range`: one
   sequential write, fences emitted.
3. **The root in the same pass.** Each time the writer completes 1/256 of the key space, a pool
   thread reads that range back from the page cache, streams each contract's storage into its
   root (a large contract splits by `hslot` nibble), then the accounts' subtrie; `split-root`
   combines the 256 subtries. The emitted frontier entries are compared with `frontier-A/`
   entry by entry (same D and d_c).
4. If the root equals the header root at A **and** every entry matches: fsync, rename, append
   the anchor line `(A … "sA.h+fA.h")`, and swap the new base in at once. Otherwise discard the
   tmp directory and stop with an error.

The new base is verified before it is published, so no unverified base ever waits in the stack.

### Anchors

Anchors, quarter points and compaction bases fall on fact-log shard ends (N ≡ 999 mod 1000).
The anchor line for N, `(N expected computed ok "sB.h+l…-N.h+fN.h")`, is appended as one fsynced
line only after all of these hold:

```
 fact-log shard ending at N sealed     (durable before the layer)
 layer-P-N/ published                  (the writer, once N is below the floor)
 verdict (N, hash) = header root       (the worker, in RAM)
 frontier-N/ published                 (the worker's checkpoint, reported for (N, hash))
 anchors.sexp: the line for N          ◀ N is a resume point
```

## 10. Crash consistency, recovery and GC

### Crash consistency

A crash at any point leaves the directories of §2 complete or absent; startup removes `.tmp-*`.
A is the newest anchor with a line.

| crash between | on disk | resume from |
|---|---|---|
| a layer write, mid-way | `.tmp-layer-*` | A |
| layer N published, `frontier-N/` not | layer N, no line | A |
| `frontier-N/` published, line not appended | `frontier-N/`, named by no line | A; GC deletes it |
| a torn anchor line | a partial last line | A (the torn line is skipped) |
| a compaction, mid-way | `.tmp-snap-*` | the old base |
| `snap-A/` published, line not appended | a base named by no verified line | the old composition; GC applies the rule below |
| any point | the worker's RAM state (overlay, delta, undo) is lost | A, with `frontier-A/`: nothing recomputed |

### Recovery

A point's components are `(:base B)`, `(:layer P N)` and `(:frontier N)` (Lean
`Comp.frontier`); the composition string ends `+fN.<hash>`. An anchored point needs all its
components sealed. The resume point is the newest anchored point whose components are sealed
(Lean `resumePoint`, mirrored by `src/state/recovery.lisp`).

A resume from anchor A maps `frontier-A/`, reads the account region and starts. A background
self-check recomputes the account region's dense levels from level D (about 4 s) against the
header root at A, and every region's top against `roots.dat` (about 18 s of CPU); the bottom
entries are covered by the files' FNV hashes (`EITA_RESUME_VERIFY` re-hashes them). A resume
from an unanchored point (a quarter-point layer, as in a bisection) starts from the nearest
`frontier-A/` below it and runs the layers above as one catch-up interval. Offsite copies of an
anchor do not include its frontier: a restore recomputes it in one full pass.

### Garbage collection

GC keeps what kept points name, so it keeps their frontiers (`gc_keeps_resume_components`). It
never deletes a frontier above the newest anchor (it may be in flight), and it pins the worker's
current frontier, the worker's view and its checkpoint's output. Retained anchors hard-link
`frontier-N/` as they do their other components.

### Import from reth

A chain can start from another client's state instead of from genesis. reth keeps the current
state in its hashed tables, `HashedAccounts` (keccak(addr) to account) and `HashedStorages`
(keccak(addr), keccak(slot) to value); its "storage v2" layout, the one Base's published
snapshots use, keeps no other current state (it writes no plain-address tables). Those tables
are already in this format's key order, so the import is one forward walk of each, with no sort
and no trie:

```
eita-reth-export --datadir DIR --chain-id N | eita import-reth --state STATE-DIR -
```

- `rust/reth-export` opens the reth datadir read-only, takes the block H the state belongs to
  (the Finish stage checkpoint, or its `partial_state_trie` when the state lags), its header's
  hash and `stateRoot`, and streams the records: per account its slots, then the account, then
  every code. The account records carry no address (above). It checks S2, S3 and S5 and
  re-hashes every code. It refuses a database whose state is persisted only partly past some
  block (the Finish checkpoint's `partial_state_trie`, left by a node stopped mid-persistence):
  starting the node on it once, without a consensus client, unwinds it to a consistent block.
  Its reth crates are pinned to the revision Base's node is built from; `cargo build --release`
  in `rust/reth-export` takes about 2 GB of target directory and 7 minutes with 4 jobs (Zen 3).
- `eita import-reth` (`src/state/import.lisp`) feeds the records through the v2 writer (S2, S4,
  S5, fences in the same pass) into `.tmp-snap-H/`, re-hashes every code, then recomputes the
  state root from the written records (`snapshot-root`: a stack trie over each 16th of the key
  space, every storage root first, no key hashing, no sort, two stack tries per thread). reth's
  trie tables and stored roots are never read.
- **The root gate.** Only when that root equals header H's `stateRoot` does the manifest gain
  `:root-checked t` and the directory become `snap-H/`. On a mismatch it stays in
  `.tmp-snap-H/`, which nothing reads, and the command exits 1.
- **Replaying from it.** `eita replay --state STATE-DIR --resume H --from H+1 …` runs on the
  base: it is not yet an anchor, so the replay checks its root once more before the first
  block and records the anchor, and the stack above it is version 2
  (docs/layered-snapshots.md, "A stack over a version 2 base").

### The converter (v1 to v2)

A chain replayed from genesis has a version 1 stack (Appendix A). The converter turns the state
at one of its anchors into a version 2 base, root-checked, with its anchor line, so the chain
continues on version 2 from there:

```
eita convert-snapshot --from V1-STATE-DIR --to V2-STATE-DIR [--tmp DIR] [--threads N] [--block N]
eita replay --chain C --state V2-STATE-DIR --resume N …
```

`src/state/convert.lisp`. The input is the composition of the newest passed anchor of
`V1-STATE-DIR` (or the one at `--block N`) whose components are all sealed; each component's
manifest must hash to the content hash the anchor recorded. The input is only read.

1. **Partition.** Chunks of 4,096 base accounts run in parallel, as the version 1 root check
   reads them: the addresses the layers mention are merged in, each composed over the base
   (`compose-range` over its layer and base slot runs: newest wins, tombstones dropped, stopped
   at a wipe), and S1 decides which accounts remain. Every address and slot is hashed (keccak
   in batches, from the mappings) and written as a version 2 record into one of 4,096 bucket
   files, by the top 12 bits of `hkey` / `haddr`, in `--tmp` (default `V2-STATE-DIR`). An
   account's slots are contiguous in their bucket. A storage of over 1M slots goes to 256
   files of its own, by the top byte of `hslot`.
2. **Sort and write.** Bucket by bucket in key order, a pool of `--threads` sorts buckets in RAM
   (the accounts by `hkey`; the slot runs by `haddr`, each by `hslot`), at most `--threads` + 2
   ahead of the writer. The version 2 writer (the one an import and a layer use) checks S2, S4
   and S5 and builds the fences in the same pass; a large storage's 256 files are sorted and
   written one at a time where its account falls. Codes are copied (the code files have the
   same format in both versions). Each bucket file is deleted once read.
3. **The root gate.** `snapshot-root` recomputes the state root from the written records. Only
   if it equals the header root at N (the top component's `:state-root`) does the manifest
   gain `:root-checked t`, the directory become `snap-N/` and the line `(N expected computed T
   hash)` go into `V2-STATE-DIR/anchors.sexp`; a replay then resumes from N without checking
   again. On a mismatch the output stays in `.tmp-snap-N/` (nothing reads it; a replay deletes
   it at startup) and the command exits 1.

Memory: the bucket write buffers (8,192 × 32 KiB), a chunk's records per thread, and the
sort window (about 55 MB a bucket on Ethereum). Disk in `--tmp`: about the size of the version
2 base, transient. Measured (x300, Zen 3, NVMe, `nice 19`, `ionice -c3`, 4 threads, 6 GB
heap, beside the production replays): Arc at 33,030,144 (a version 1 base and 13 layers, 11.7 GB;
3.7M accounts and 102M slots composed, one storage of 34.6M slots) in 16 min: partition 5.6
min, sort and write 6.7 min, codes and fences 2.2 min, root 1.3 min; peak RSS 5.7 GB; the root
matched the header's, and a replay of the next 32,768 blocks over it passed all eight anchors
(the last equal to the production replay's).
Ethereum at 26.33M (430M accounts, 1.69B slots), from a slice (every 64th chunk of the base:
6.7M accounts, 18.4M slots, 2.4 GB of buckets, in 177 s: partition 81 s, sort and write 74 s,
root 18 s, 3.0 GB peak RSS) scaled by bytes (×91): about 4.5–6 h, 217 GB of buckets in `--tmp`
at the end of the partition, a 230 GB base, under 6 GB of heap.

Not yet: the converter does not write `frontier-N/` (§7). The full pass that would emit it
is `snapshot-root`'s, whose stack tries close every subtrie at the frontier depth as they go;
emitting them needs the frontier file writer of §7, which the root worker will own. Until
then a converted chain is root-checked at anchors, as any version 2 stack is.

## 11. What is proved, modelled and checked

Lean labels: F1–F3 are the frontier's proved lemmas, L1′, L2 and L4 its stated ones, R the
statement that connects the worker to the trie spec (`lean/Evm/Trie/Frontier.lean`).

- **Proved** (Lean, standard axioms only):
  - F1, locality: `prefixed_update`, `subRef_update` (a clean prefix's subtrie is unchanged);
  - F2, the frontier update: `frontierOK_update`, `frontierOK_step`, `refAt_congr`,
    `refAt_step_clean`, `assemble_congr`;
  - L1′'s completeness: `buildFrontier_complete` (the streaming build emits every prefix);
  - F3, `compose-range`: `viewRange_slot`, `viewRange_acct` (`Persist/Layered.lean` Part E);
  - recovery with frontiers: `gc_keeps_resume_components` and the Part D lemmas over
    `Comp.frontier`.
- **Stated, `sorry`** (listed in `scripts/generated/verification-stats.md`):
  `patricialise_assemble` (L2, decomposition), `build_emits_frontier` (L1′, soundness),
  `stateRoot_two_levels` (L4, the account trie over the storage roots),
  `layered_frontier_root_eq` (R: the worker's step over the composed stack yields the fork's
  `stateRootBytes`). `Trie1.root_step` (one trie's incremental root equals the root of its
  post-state) is proved from F2 and L2 and carries L2's `sorry`. L2, L1′ and L4 wait on the
  total trie spec (`patricialise`, `nodeRef` and RLP are `partial def`s) and on the order
  independence of `rootBytes`.
- **Modelled** (Veil, safe; `verify/protocols/`):
  - `RootWorker`: verdicts are exact and keyed by block; `drop-above!` restores the worker's
    state; no frontier is published before its verdict; the worker never maps a deleted
    frontier; the anchor line names a canonical frontier;
  - `CompactionV2`: the stack's composition and liveness under the window, settling, the
    writer, compaction to a verified anchor, GC, `close-retired!` and rollback at any depth,
    with the worker as a reader.
- **Checked at run time** where a step is not proved: the header root every block (every
  catch-up interval, bisected on mismatch), DenseAbove on every recomputed dense branch,
  32-byte references, the compaction's in-pass root and its entry-by-entry frontier
  comparison, the resume self-check.

## Appendix A. Legacy format (v1)

The format the engine reads and writes until conversion (`src/state/snapshot.lisp`).
Differences from v2:

- **Key order: raw.** `accounts.dat` (96 B: `addr 20 · flags 4 · nonce 8 · balance 32 ·
  codehash 32`) is sorted by `addr`; `storage.dat` (88 B: `addr 20 · slot 32 · value 32 ·
  pad 4`) by `(addr, slot)`. Header `version` = 1; S1–S5 hold over these keys. Layer flags and
  tombstones are as in §5.
- **No persisted fence.** The fence (`fence-node`, as in §3) is built in memory when a
  snapshot is opened, on a background thread for a resumed base (lookups binary-search the file
  until it is published). Manifests list no `.fnc` files and say `:version 1` without
  `:key-order`. Snapshots that still contain `accounts.idx` / `storage.idx` (tables 4 and 5, a
  sampled index) remain valid: their manifests list those files, so sealing and verification
  check them and the content hash covers them; the reader does not map them.
- **No frontier.** The state root is checked at anchors, not every block: `src/state/root.lisp`
  runs as a separate process over the base and the layers (`docs/layered-snapshots.md`), and a
  compacted base is root-checked after it is written, before it replaces the old one.
- **Minor compaction.** Over 16 disk layers, a run of eight is composed into one
  (`docs/layered-snapshots.md`).
