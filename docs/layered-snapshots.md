# Layered snapshots

*Replaces the full-merge anchor and the hot-budget early checkpoint (2026-10-26).
Lean: `lean/Evm/Persist/Layered.lean`. Code: `src/state/snapshot.lisp` (format, reader,
composers), `src/state/snapshot-world.lisp` (the replay's stack, writer, compactor, rollback),
`src/state/anchors.lisp` (anchors, root checks), `src/state/root.lisp` (the
checker over a stack), `src/state/recovery.lisp` (resume point, GC).*

## 1. What changed

Before: at every anchor the replay stopped, merged its hot set into a new full snapshot
(a sequential copy of the whole state: 19–21 s at Ethereum 4.9M, 3–8 min at Arc 10M+;
21–26 % of production wall time) and dropped the hot set; a hot set over
`EITA_HOT_BUDGET_MB` forced the same merge early.

Now the persisted state is a **base** snapshot (today's format, `snap-B/`) under an
ordered stack of immutable **delta layers** (`layer-P-N/`: what blocks P+1..N changed).

| tier | where | what |
|---|---|---|
| hot | heap | everything touched since the last freeze, faulted on first touch |
| frozen | heap, read-only | hot sets frozen at a layer point, queued for the writer (at most 4) |
| layers | `layer-P-N/`, mmapped | written by a background thread, oldest first |
| base | `snap-B/`, mmapped | the full state at B |

* A **layer point** freezes the hot set: the world's tables become the newest frozen layer
  and the replay continues on empty ones. O(1): measured 0.0–4.7 ms against 19–21 s.
  Layer points: every anchor; a quarter of the anchor interval (resume and bisect points:
  8,192 blocks on Arc); the state budget (`EITA_HOT_BUDGET_MB`, below); and, within the
  chain's reorg depth of the head, every block.
* The **state budget** (`EITA_HOT_BUDGET_MB`; unset, a quarter of the heap) bounds what the
  state's tables hold in memory, heap and native slot tables together (`acct-table-bytes`,
  measured from the tables, not from the heap). Two uses, one number: the live hot set is
  frozen early when it passes the budget (checked every 1,000 blocks, only while no frozen
  layer waits for the writer); and the tables of layers already written are dropped, with
  a full GC, once they hold a quarter of it (`collect-written!`, logged as
  `[layers] dropped N written hot sets`). The second is what bounds memory at the tip,
  where every block is a layer. It used to count the layers' bytes on disk (a quarter of
  the nursery), but a block's table holds about three times its layer's bytes, a third of
  it native (Ethereum 25M: 0.27 MB on disk, 0.5 MB heap + 0.28 MB native per block), so
  1.8 GB piled up between collections at a 10 GB heap, twice that at 20 GB.
* The **writer** thread turns a frozen layer into `layer-P-N/` and swaps it into the stack.
* An **anchor** queues a root check of the stack at its block. `state/root.lisp` reads the
  base plus the layers (no merged snapshot is written) with half the hardware threads, at
  most 16 (it shares the box with the replay: all 30 on GCP contended with it); a passed
  check appends the stack's **composition** to `anchors.sexp`, which is what a resume
  loads.
* The **compactor** thread folds layers: *minor* — over 16 layers on disk, eight
  consecutive layers within a factor of eight of each other in bytes (the cheapest such
  run) into one, so a composition waits for peers before it is rewritten (size-tiered:
  a block is rewritten about log₈ of its depth); *major* — the layers up to a boundary
  into a new base, once the layers outweigh an eighth of the base. A compacted base is root-checked as a plain snapshot before it
  replaces the old base. Neither touches the newest `reorg-depth` blocks or crosses a
  pending anchor.
* A **reorg** (at the tip, a block whose parent is not our previous block) finds the fork
  point, drops every layer above the newest boundary at or below it, pulls the fact log
  back to that boundary and re-executes (`reorg!`, `rollback-chain!`, `rollback-to!`).
  Reorg depth is a chain-spec field: 64 by default (two Ethereum epochs), 0 on Arc (BFT
  finality: a discontinuity stays a fault).
* **Recovery** is unchanged in shape: the resume point is the newest verified block whose
  recorded composition is sealed; GC deletes what no kept point is made of. The replay runs
  that one rule (`prune-dumps!` → `recovery.lisp`'s `run-gc`) at startup, after every root
  check and after every minor compaction, so retired and previous-life layers do not pile
  up until the next anchor (77 directories in the production trial).

## 2. Formats

**A layer** is a snapshot-format directory (`docs/state-snapshot-format.md`), the same six
files, holding only the addresses the layer mentions:

* `accounts.dat`: one 96-byte record per mentioned address, always with the fields (the
  writer takes an unfaulted address's fields from the stack below — *FieldsCover*). Flags:
  bit 0 = the RAM existence mark (`world-accounts`), bit 2 = WIPED (the address's storage
  below this layer is gone). A deleted account is the record (0, 0, empty code, no mark).
* `storage.dat`: 88-byte slot records; value 0 is a tombstone.
* `code.dat`: codes the stack below does not hold.
* `MANIFEST.sexp`: as a base, plus `:kind :layer :parent P`; `:state-root` is the header
  root at its block (what a check of the stack at N, or a base compacted to N, expects).

A per-layer **Bloom filter** over its addresses (k = 3, 16 bits per address) is built at
open, so a lookup for an address a layer does not mention costs three bit tests.

**A composition** is written in an anchor line's hash field, oldest first:
`s4900000.4659a9fe4981dc3e+l4900000-4902000.2b53b206b9fa6058` (a base, then layers, each
with its content hash). A lone base keeps the v1 form, its bare hash: every anchor written
before layers is a composition, and `snap-N/` from before layers are bases.

## 3. Reading the stack

`eita-snap:view-account` / `view-slot` (one reader for disk layers and the replay's frozen
RAM layers, which answer through `*foreign-layer*`): an account comes from the newest layer
that mentions it, else the base; a slot from the newest layer that sets it, 0 at the first
layer that wiped its account, else the base. The account is then materialized by the
writer's inclusion rule S1 (`s1-included-p`): present iff non-empty, with storage, or
marked; its flag is then `empty`. Faults go through these (`snap-fault-account`,
`snap-fault-slot`, `snap-cold-storage-map`).

`compose-address` folds one address through a run of layers (and optionally the base) on
raw records — a k-way merge of their slot runs, newest wins, stopping at a wipe — and serves
minor compaction (zeros kept), major compaction and the layered root check (state: zeros
dropped, S1 applied by the merge writer, `merge-account :raw-slots`).

The root check (`state/root.lisp <base> <layer>...`) keeps its streaming structure:
chunks of 4,096 base accounts in parallel; each chunk's address range picks up the layer
addresses in it (`map-touched-addresses`), and an address any layer mentions is composed
over the base before its storage root is built — except a giant base storage (over 1M
slots): only its layers are composed (tombstones kept), and `giant-root` lays them over the
base's records in place while it builds that storage's trie with every thread (split by the
hashed keys' top byte; 6 B per slot off the heap). Measured at 4.9M (22M accounts, 36M slots,
up to 13 layers): 18.3–20.5 s, the plain check of the same state 18.7–21.6 s.

## 4. Invariants

1. **FieldsCover**: a layer record carries the fields of every address whose storage it
   touches or wipes (the writer enforces it). Without it a base, which stores materialized
   records, would not compose with later layers (`mat_apply_mat`).
2. **Durability order**: the fact log's checkpoint at N (its `.at-N` prefixes) is durable
   before layer N is published — the writer waits for the encoder's acknowledgement
   (`factlog-checkpoint!` no longer blocks the replay). A layer is written in
   `.tmp-layer-P-N/`, every file fsynced, renamed into place, the parent fsynced.
3. **Boundaries**: anchors are layer boundaries, and stay so: minor compaction never
   composes past a queued anchor; major compaction stops below the oldest one (a base at
   a queued anchor's block removed that boundary before the anchor's own check, which
   then never ran: the replay hung at the end of a bounded run, and at the tip no later
   anchor would have been checked — found by the twin, seed 22). The anchor
   being checked may be composed over: the checker reads the files it was given, which GC
   pins until the verdict names them (I8).
4. **Compositions are exact**: a resume loads the components its anchor names and checks
   each one against the recorded content hash (I3): its manifest (each file's name, size
   and FNV) must hash to it and every file have its recorded size. The bytes are not
   re-read: the root check read exactly these files, a component is immutable once
   published, and the next anchor's root check reads every byte again
   (`EITA_RESUME_VERIFY=1` re-hashes them first: 206 GB of Ethereum base, about 14 min at
   250 MB/s). The fences are built on a thread of their own while the replay runs (lookups
   binary-search until then): another 190 GB read. A point without an anchored
   composition (a bisect layer, a copied snapshot) has its bytes re-hashed and is
   root-checked before anything runs on it.
5. **One point per block** in recovery: the first sealed of its anchored compositions
   (passed checks, fewest components first), the base alone, the widest layer chain.
6. **Reorg window**: compaction and tip-anchor checks stay `reorg-depth` behind the
   newest block, so a rollback within it only ever drops whole layers.
7. **No snap is unmapped under a reader**: swapped-out snaps are closed by the replay
   thread only while neither background thread is running.
8. **GC never deletes under the replay**: the replay's GC pins its live stack, the
   composition the root check in flight reads, and a compaction's output (a restarted
   replay rewrites layers its previous life left, under the same names; a GC between the
   rename-aside and the publish once deleted live layers — found by the twin; a GC after a
   minor compaction would otherwise delete the layers a running check was handed). It does not run while a compacted base waits for its check.
9. **A root checker lives only as long as its replay**: spawned with `--parent <pid>`, it
   exits within a second once that process is no longer its parent (polls `getppid`:
   Linux and macOS), releasing its heap (16 GB in production) and threads. Its scratch
   (`.root-N-PID/`) and its output files (deleted before each spawn: fresh inodes) are
   its own, so a replacement replay never shares them with a dying checker of the
   previous life; startup removes stale `.root-*/` and `state-*.rootout`.

## 5. What is proved, what is assumed

`lean/Evm/Persist/Layered.lean` (standard axioms only, no `sorry`):

| theorem | statement |
|---|---|
| `lookupAcct_eq`, `lookupSlot_eq` | lookup through the stack = lookup in the merged state |
| `apply_compose`, `applyAll_composeAll`, `compose_run_view` | composing a run of layers (minor compaction) leaves the view unchanged |
| `mat_idem`, `mat_apply_mat` | S1 is idempotent and commutes with a covered layer |
| `compact_view`, `compaction_correct` | a base compacted from base + layers, under the remaining layers, reads as the whole stack |
| `stack_view` | correct layers over the canonical base read as the canonical state at the top: the state after a freeze, and after a resume from any layer |
| `rollback_view` | dropping the newest layers of a correct stack reads as the canonical state at the new top |
| `fieldsCover_compose`, `fieldsCover_composeAll` | composition keeps FieldsCover |
| `gcSubset_preserves_resume`, `gcFiles_preserves_resume`, `resume_components_sealed` | GC over layered files — any part of the GC set: the replay pins its live stack — never moves the resume point; the resume point's components are sealed |

Recovery Part 1 (`resumePoint`, `gcSet`) is reused over the points; `src/state/recovery.lisp`
mirrors `dumpsOf`/`keepFiles`/`gcFiles` and is checked against `lake exe recoveryVectors`
(40,000 vectors, half of them layered).

Assumed (hypotheses, not theorems): the writer implements its contract (`LayerOK`: the
layer it writes turns the canonical state at its parent into the one at its block); the
merge writer implements `mat ∘ apply` (`CompactOK`); keccak collision resistance (a
matching root means a matching state); the replay is a function of the blocks (a reorg
re-execution reproduces the canonical branch). Checked on the implementation by
`tests/layers.lisp` (random states: lookups, minor and major compaction and the
layered root check against a model of `mat ∘ applyAll`; a mutant that ignores wipes fails
172 checks in 20 rounds) and the gates below.

## 6. Gates (2026-10-26)

* **(b) facts and roots**, Ethereum 4,900,001–4,910,000 resumed from `snap-4900000`, anchors
  every 2,000 (layers every 500): decoded rows of all seven kinds identical to the
  full-merge run and `committed` equal; all five anchors root OK over base + layers (one
  minor compaction on the way: eight layers into `layer-4900000-4904000`).
* **(c) resume from a mid-stack point**: from the anchor at 4,906,000 (base + a composed
  layer + four layers) and from the unverified layer 4,907,500 (root-checked at resume):
  rows of 4,900,001–4,910,000 identical, every later anchor OK.
* **(d) reorg**: 4,900,001–4,900,300, a layer per block above 4,900,150; after 4,900,290 a
  rollback to 4,900,270 (20 layers dropped) and blocks 4,900,271–290 again: fact rows and
  row files byte-identical to the straight run; anchors 4,900,100/200/300 root OK in both.
* **(e) cost**, same segment (`PROF blocks-wall`, run-block only, interp, Mac M-series):

  | run | wall | µs/tx | anchor pause |
  |---|---:|---:|---:|
  | no anchors, no layers | 49.1 s | 24.1 | — |
  | full-merge anchors every 2,000 (before) | 241.5 s | 118.5 | 18.6–20.6 s × 5 |
  | layered anchors every 2,000, layers every 500 | 70.2 s | 34.4 | ≤ 4.7 ms |
  | layers every 1,000 (budget), no root checks | 58.2 s | 28.6 | ≤ 0.1 ms |
  | layered code, no layer in the segment | 49.4 s | 24.2 | — |

  The remaining cost over no anchors is the five 12-thread root checks running beside the
  replay on the same cores (about 6 µs/tx) and re-faulting after each freeze (about
  4 µs/tx). Peak memory footprint 3.76 GB (full merge: 3.06 GB; no anchors 3.80 GB); with
  budget freezes every 1,000 blocks, 2.93 GB. Heap use is bounded by the budget plus the
  frozen layers the writer has not finished (at most four: its queue blocks the replay
  beyond that). A budget check while a frozen layer is still queued is skipped: the heap
  then holds that layer too, and a freeze would cut a small layer (and pay a full GC) for
  memory the writer is about to release — the production trial's stutter, a 1,000-block
  layer and a full GC at every check while the writer lagged. Layer size at
  4.9M: about 11 MB per 500 blocks, against a 5.0 GB snapshot.
* **(a) fault injection**: the fault-injection twin (an operator test, not in this repository) on an arm64 Ubuntu 24.04 VM (OrbStack,
  SBCL 2.5.2 built from source as on x86-64 Linux), Arc 1–30,000 from genesis, anchors every 600
  (layers every 150; seven major compactions in the reference): see §8 for the trial
  results. The twin's I1 compares (block, verdict) of scheduled anchors only — a
  composition, and the blocks compactions pick, depend on background timing.
* **(f)** the Arc regression blocks: 14/14 PASS, and every block's fact rows equal to the
  pre-change tree's (3,991 rows); `scripts/verify-host-emit.sh` passes.

* **(g) minor compaction's rule** (2026-10-27, after the production-scale trial: minor never
  fired there, major's base/8 came first). Kept, with a new rule: its role is the tip,
  where a chain with a reorg window freezes a layer per block (Ethereum: 64), and without
  minor those layers would pile up until major — thousands of mmapped layers, six files
  each, at a 100 GB base. On Arc (reorg depth 0) and on bounded historical runs major
  bounds the stack first and minor rarely runs; that is the intended outcome, not dead
  code. The old rule (eight consecutive layers of one log₈-span level, else the oldest
  eight past 32) starved when budget freezes cut quarter points into alternating levels.
  A policy model (instantaneous compaction, compositions 0.85-0.95 of their inputs, layer
  sizes from the 4.9M segment: about 22 KB per block, 11 MB per 500 blocks) over three
  rules — old; the fewest-bytes run of eight, any sizes; the fewest-bytes run of eight
  within a factor of eight (adopted):

  | scenario | max layers (old / any / adopted) | minor bytes written per layer byte |
  |---|---|---|
  | 4.9M, layers every 500, 5 GB base | 16 / 16 / 16 | 0.96 / 0.77 / 0.77 |
  | Arc, 8,192-block layers cut by budget freezes (3,000 + 3,000 + 2,192) | 16 / 16 / 18 | 1.14 / 1.66 / 1.20 |
  | alternating levels (8,192, 3,000, 5,192), 200 GB base | **32** / 16 / 18 | 3.58 / 1.69 / 1.31 |
  | tip, a 1 MB layer per block, window 64, 100 GB base | 94 / 71 / 89 | 3.28 / **18.9** / 3.85 |
  | catch-up layers, then the tip | 95 / 71 / 88 | 3.02 / 18.7 / 3.42 |

  "Any sizes" fixes the starvation but at the tip composes each big composition with
  seven one-block layers again and again (quadratic); the adopted rule fixes the
  starvation and keeps the tip's write amplification within 0.6 of the old rule's. At the
  tip the count is dominated by the 64 per-block layers the reorg window keeps.
  Exercised: the 2,000-anchor segment (one minor, `layer-4901000-4905000`, rows identical,
  five roots OK) and the reorg gate (seven minors over per-block layers, rows identical).

* **(h) the heap after a freeze** (2026-10-28, after four production deaths of
  `HEAP-EXHAUSTED-ERROR` at 33-50 % heap use, Ethereum 13.4-14.0M, 52 GB heap, 26 GB
  budget). The live set is small: the hot set of a 62,500-block layer is 3.4-3.9M
  accounts, 17-19M slots, 3.0-3.5 GB in the heap; codes and their JUMPDEST maps 0.7-1.1
  GB. But a written layer's frozen hot set was only freed when SBCL next collected the
  generation it had been promoted to (gens 3-5 have a minimum average age), so the dead
  hot sets piled up: post-GC usage 0.1 → 20.5 GB over 300k blocks against a live hot
  set ≤ 3.5 GB, interleaved with live pages. SBCL's large allocations search only
  upward from the highest page any allocation reached since the last GC (`gc_alloc_large`
  from `max_alloc_start_page`); with a 4 GB nursery that hint swept 40-90 % of the heap
  per cycle, and once the free tail above the old data was gone (49 GB → 163 MB) a
  35 MB receipts buffer found no run above it: the trial on the production composition
  (13.75M, same settings, `results/heap-20261028`) died at 14,283,600 in the chunk decoder
  with 42 % of the heap allocated and 64 free runs of 32-256 MB below the hint, as
  production did. Now the replay thread drops the written layers' tables and runs a full
  GC once they add up to a quarter of the nursery (`collect-written!`): 1.3-4 s per layer
  point at this scale. Same blocks with a 16 GB heap and a 5 GB budget: dynamic usage
  ≤ 5.4 GB, RSS anon 6.6 GB through the 14.0M anchor and a major compaction; GC 4.9 % of
  wall against 4.3 % before.

## 7. Deployment and migration

Nothing to convert. Existing `snap-N/` are bases; existing anchor lines are compositions of
one base. The first anchor after the upgrade records a stack over the newest verified
snapshot.

1. Ship the code (bundle → checkout, as today). `EITA_CHECKPOINT_EVERY` stays 32,768:
   anchors keep their cadence; layers come every 8,192 blocks for free.
2. Restart from the newest verified snapshot (recovery.lisp decides, as before). The first
   freezes write `layer-*/` beside it; GC keeps the base until a newer verified base exists.
3. `EITA_HOT_BUDGET_MB` keeps its meaning (a memory bound) and is now cheap; it can be set
   lower (e.g. 1,500) on 30 GB boxes.
4. Offsite (an operator's copy job, not in this repository): uploads each verified anchor's components, each
   once (`SNAPSHOT_KEEP` newest anchors kept): the history becomes a base plus deltas.
5. **Park only after three deaths without progress.** Progress is the fact log's
   `committed` frontier passing the furthest any earlier life got — not the resume point,
   which with long anchor intervals stays put while each life gets further (the old rule,
   "three deaths from the same resume point", parked runs that were advancing between
   crashes). One supervisor (an operator's, not in this repository) does this for every chain
   (`PARK_AFTER`, default 3); an input outage (exit 75) is not a death.
6. Rolling the code back needs no conversion either: a pre-layer build sees only `snap-N/`
   and the anchors naming a lone base (bare hash), so it resumes from the newest verified
   base — the initial snapshot or the last major compaction — and re-executes from there.

## 8. Fault-injection results

Arm64 Ubuntu 24.04 VM (OrbStack, 12 cores, SBCL 2.5.2 from source, libmcl/blst built there,
the fsjournal `LD_PRELOAD` shim), Arc 1–30,000 from genesis, `--every 600`: anchors every
600 blocks, layers every 150, a major compaction (base root-checked, swapped, old base
collected) whenever the layers outweigh an eighth of the young base — seven in the
reference run (69 s).

* Seeds 1–20, up to 20 faults each cycling replay / checker / all / power, `--aim 0.15`:
  **20/20 PASS, 112 faults**; every trial's fact log identical to the reference, `R`
  monotone and never `refuse`, and every trial ends at the reference's resume point
  (30,000). Power losses rewound up to 2.7M journaled operations (5,406 files torn, 13,625
  directory entries undone) in one fault.
* Seeds 21–26, power losses only (up to 8 each): **6/6 PASS, 32 power losses**, each
  rewinding up to 1.3M journaled operations, resume points 0 → 7,200 under them, final
  resume point 30,000 every time.
* The first batch found a liveness bug the old checks could not see: after a restart the
  replay rewrites, under the same names, layers its previous life left; a GC between the
  rename-aside and the publish took those layers for unreferenced and deleted the replay's
  own live stack, and every later anchor of that run failed to check (`R` stuck at 22,800
  of 30,000, while the facts stayed identical). Fixed: the replay's GC pins its live stack
  and a compaction's output (`live-components`; Lean `gcSubset_preserves_resume`), and the
  twin now also requires the final resume point to equal the reference's, unless a checker
  was killed in the last run (its anchor stays unverified by design, I6).

* **The trial follow-ups (2026-10-27)**, same VM setup (Ubuntu 24.04, SBCL 2.5.2), Arc
  1–30,000, `--every 600`. On the final code: replay and checker kills only, seeds 22–28,
  **7/7 PASS, 140 faults** (98 replay, 42 checker); all four kinds, seeds 29–34, **6/6
  PASS, 33 faults**; every trial's fact log identical, final resume point 30,000, no root
  checker or replay left running after any trial. Before the last fix, seed 22 hung: a
  major compaction to the block of a queued anchor took that anchor's boundary out of the
  stack (§4 I3); with it, 13 more seeds passed (79 faults).

* **The production-scale re-trial (2026-10-27)**, a cloud VM beside the live replay
  (10 cores by `taskset`, `nice 5`; heap 52 GB, hot budget 26 GB, checker heap 16 GB), Ethereum
  11,750,001–12,250,000 from the verified production `snap-11750000` (116M accounts, 405M
  slots, 46 GB), anchors every 250,000, layers every 62,500. Straight run: anchors 12.0M and
  12.25M and the compacted base 12,062,500 (one major compaction of 5 layers) root OK; 45.1
  blocks/s, 553 Mgas/s over the 500k blocks against the production replay's 436 / 502 Mgas/s on
  the same blocks (its 12.0M full-merge anchor paused it 1,642 s; a freeze here is 0.0 ms).
  Layers 1.1–1.34 GB, written in 36–55 s; the major compaction wrote the 46 GB base in 7 min;
  every root check over the stack (base + up to 5 layers) 531–582 s, with 5 checker threads
  (half the 10 cores the replay may use), slowing the replay ~10 % while it runs. Root-check
  lag: the verdict lands 31k–45k blocks behind the replay, never more than one anchor queued,
  at most 5 layers. Peak RSS: replay 55 GB (anon 25 GB, the rest mmapped base pages), checker
  14 GB (anon 7 GB); disk peak 162 GB (two bases during the compaction's check). Crash run:
  kill -9 of the replay right after a freeze, mid layer write, mid root check (12.0M), mid
  major compaction and right after a freeze above the compacted base, and the root checker
  alone mid the 12.25M check; every life resumed through recovery (11.75M, 12.0M, then the
  compacted base 12,062,500), stale `.tmp-layer`/`.tmp-snap` removed at startup, no checker
  survived its replay, the killed check reported (`could NOT RUN … UNVERIFIED`, the bounded
  run ended rc 0), the compacted base and every layer re-made with the straight run's content
  hashes, and the fact log identical to the straight run's over all 500,000 blocks (footer
  content hashes of all seven tables, 1.1 billion rows).

## 9. Next: incremental MPT over layers (step F)

Designed for, not built. A layer can carry the trie's dirty-path node hashes: each layer
persists the branch nodes its writes changed (keyed by path), the base persists the full
node set once; a per-block root then hashes only the dirty paths of the hot set, reading
sibling hashes newest layer first, exactly like account lookups. Compaction folds node sets
like slot runs (newest wins). `mpt-live.lisp` would seed from the base's node file instead
of a full in-heap world.

## 10. Open

* The twin exercises major compactions but not minor ones (Arc's early state is small);
  minor compaction is covered by the 4.9M segment, the reorg gate and `test-layers.lisp`
  (composition; the selection rule by the model in §6 g).
* Root checks can fall far behind a fast replay (at production scale they do not: §8, the
  re-trial, 31k–45k blocks behind with a 250,000-block interval): in the twin (3,000 Arc blocks/s, a check
  every 600 blocks, ~2 s each) the queue lags ~20,000 blocks, its oldest anchor fences
  compaction, and the stack reaches ~180 layers. In production a check (minutes) finishes
  well within an anchor interval (32,768 blocks); a catch-up at very high block rates
  would see the same lag.
* Metric subscribers have no rollback: a reorg with one attached stops the run (loud).
* Layers record faulted-but-unchanged keys too (the hot set does not track dirtiness), so a
  layer is larger than the strict delta.
