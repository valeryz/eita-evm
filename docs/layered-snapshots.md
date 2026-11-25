# Layered snapshots

The replay's persisted state is a **base** snapshot under an ordered stack of immutable
**delta layers**. Freezing the replay's in-memory changes into a layer is O(1); a background
thread writes it; compaction folds layers; recovery resumes from the newest verified stack.

Lean: `lean/Evm/Persist/Layered.lean`. Code: `src/state/snapshot.lisp` (format, reader,
composers), `src/state/snapshot-world.lisp` (the replay's stack, writer, compactor, rollback),
`src/state/anchors.lisp` (anchors, root checks), `src/state/root.lisp` (the root checker over a
stack), `src/state/recovery.lisp` (resume point, GC). File format and the terms used here:
[state-snapshot-format.md](state-snapshot-format.md); this document describes the running
system, whose files are that document's legacy format (its Appendix A).

## 1. The stack

| tier | where | what |
|---|---|---|
| hot | heap | everything touched since the last freeze, faulted in on first touch |
| frozen | heap, read-only | hot sets frozen at a layer point, queued for the writer (at most 4) |
| layers | `layer-P-N/`, mapped | what blocks P+1..N changed; written by a background thread |
| base | `snap-B/`, mapped | the full state at B |

```
 replay thread ──freeze──▶ frozen RAM layers ──writer──▶ layer-P-N/ ─┐
      │                                                              ├─ compactor ─▶ layer / snap-M/
      └─ reads: hot ▸ frozen ▸ layers (newest first) ▸ base ◀────────┘
 anchor N ──▶ root check of base + layers at N ──pass──▶ anchors.sexp: (N … composition)
```

- **Layer point.** A freeze makes the world's tables the newest frozen layer and continues on
  empty ones: O(1), 0.0–4.7 ms measured. Layer points: every anchor; every quarter of the anchor
  interval (resume and bisect points); the state budget (below); and every block within the
  chain's reorg depth of the head.
- **State budget** (`EITA_HOT_BUDGET_MB`, default 3,000) bounds the memory the state's tables
  hold, heap and native slot tables together (`acct-table-bytes`, measured from the tables: a
  block's tables hold about three times its layer's bytes on disk, a third of that native). One
  number, two uses: the live hot set is frozen early when it exceeds the budget (checked every
  1,000 blocks, only while no frozen layer waits for the writer: a freeze then would cut a small
  layer for memory the writer is about to release); and the tables of layers already written
  are dropped, with a full GC, once they hold a quarter of the budget (`collect-written!`,
  logged as `[layers] dropped N written hot sets`). The second bounds memory at the tip, where
  every block is a layer. The full GC matters: a written layer's tables are otherwise freed only
  when SBCL next collects the generation they were promoted to, so dead hot sets accumulate
  between live pages until a large allocation finds no free run. The GC policy itself is
  `src/chains/driver.lisp`'s.
- **Writer.** A thread turns the oldest frozen layer into `layer-P-N/` and swaps it into the
  stack.
- **Anchor.** An anchor queues a root check of the stack at its block. `src/state/root.lisp`
  reads the base and the layers (no merged snapshot is written) with half the hardware threads,
  at most 16, beside the replay. A passed check appends the stack's **composition** to
  `anchors.sexp`; a resume loads it. The anchor interval comes from the chain; `EITA_CHECKPOINT_EVERY`
  overrides it.
- **Compactor.** A thread folds layers. *Minor*: over 16 layers on disk, a run of eight
  consecutive layers within a factor of eight of each other in bytes (the run with the fewest
  bytes) is composed into one, so a composition waits for peers before it is rewritten (a block
  is rewritten about log₈ of its depth times); with no such run and over 32 layers, the
  fewest-bytes run of eight whatever its sizes. *Major*: the layers up to a boundary into a new
  base, once the layers outweigh an eighth of the base; the compacted base is root-checked as a
  plain snapshot before it replaces the old base. Neither touches the newest `reorg-depth`
  blocks or crosses a pending anchor. Minor compaction serves the tip, where a chain with a
  reorg window freezes a layer per block; on a chain without one (Arc) and in catch-up, major
  compaction bounds the stack first.
- **Reorg.** At the tip, a block whose parent is not the previous block starts a reorg: find the
  fork point, drop every layer above the newest boundary at or below it, pull the fact log back
  to that boundary and re-execute (`rollback-chain!`, which calls `rollback-to!`; the program
  that follows the chain head chooses the fork point). Reorg depth is
  a chain-spec field: 64 by default (two Ethereum epochs), 0 on Arc (BFT finality: a
  discontinuity is a fault).
- **Recovery.** The resume point is the newest verified block whose recorded composition is
  sealed; GC deletes what no kept point is made of. The replay runs that rule
  (`prune-dumps!` → `recovery.lisp`'s `run-gc`) at startup, after every root check and after
  every minor compaction.

## 2. Formats

**A layer** is a snapshot directory holding only the addresses the layer mentions:

- `accounts.dat`: one record per mentioned address, always with its fields (the writer takes an
  untouched address's fields from the stack below: *FieldsCover*). Flags: bit 0 = the RAM
  existence mark (`world-accounts`), bit 2 = WIPED (the address's storage below this layer is
  gone). A deleted account is the record (0, 0, empty code, no mark).
- `storage.dat`: slot records; value 0 is a tombstone.
- `code.dat`: codes the stack below does not hold.
- `MANIFEST.sexp`: as a base's, plus `:kind :layer :parent P`; `:state-root` is the header root
  at its block (what a check of the stack at N, or a base compacted to N, expects).

Each layer gets a **Bloom filter** over its addresses at open (k = 3, 16 bits per address), so a
lookup for an address the layer does not mention costs three bit tests.

**A composition** is written in an anchor line's hash field, oldest first:
`s4900000.4659a9fe4981dc3e+l4900000-4902000.2b53b206b9fa6058` (a base, then layers, each with its
content hash). A lone base is written as its bare hash.

## 3. Reading the stack

`eita.state.snapshot:view-account` / `view-slot` read disk layers and the replay's frozen RAM layers alike
(RAM layers answer through `*foreign-layer*`): an account comes from the newest layer that
mentions it, else the base; a slot from the newest layer that sets it, 0 at the first layer that
wiped its account, else the base. The account is then materialized by the inclusion rule S1
(`s1-included-p`): present iff non-empty, with storage, or marked. Faults go through these
(`snap-fault-account`, `snap-fault-slot`, `snap-cold-storage-map`).

`compose-range` is the one merge of sorted record runs over a key range: a k-way merge, newest
wins, stopping at a source that wiped the account (Lean `composeRuns`,
`docs/state-snapshot-format.md` §6). `compose-address` gives it one address's slot runs through a
run of layers (optionally with the base), on raw records. It serves minor compaction (zeros kept),
major compaction and the root check (zeros dropped, S1 applied by the merge writer,
`merge-account :raw-slots`).

**The root check** (`state/root.lisp <base> <layer>...`) streams: chunks of 4,096 base accounts
in parallel; each chunk's address range picks up the layer addresses in it (`compose-range`
over the layers' account records), and an address any layer mentions is composed over the base records
the scan is at (`:base-at`, a merge-join; the base is read once, without its fence). A base
storage of over 1M slots is the exception: only its layers are composed (tombstones kept), and
`giant-root` lays them over the base's records in place while it builds that storage's trie
with every thread (split by the hashed keys' top byte; 6 B a slot off the heap). Ethereum at
4.9M (22M accounts, 36M slots, up to 13 layers): 18.3–20.5 s.

## 4. Invariants

1. **FieldsCover**: a layer record carries the fields of every address whose storage it touches
   or wipes (the writer enforces it). A base stores materialized records, so without it a base
   would not compose with later layers (`mat_apply_mat`).
2. **Durability order**: the fact log's checkpoint at N (its `.at-N` prefixes) is durable before
   layer N is published; the writer waits for the encoder's acknowledgement. A layer is written
   in `.tmp-layer-P-N/`, every file fsynced, renamed into place, the parent fsynced.
3. **Boundaries**: anchors are layer boundaries and stay so. Minor compaction never composes past
   a queued anchor; major compaction stops below the oldest one (a base at a queued anchor's
   block would remove the boundary that anchor's check needs). The anchor being checked may be
   composed over: the checker reads the files it was given, which GC pins until the verdict
   names them (invariant 8).
4. **Compositions are exact**: a resume loads the components its anchor names and checks each
   against the recorded content hash: its manifest (each file's name, size and FNV) must hash to
   it and every file must have its recorded size. The bytes are not re-read: the root check read
   exactly these files, a component is immutable once published, and the next anchor's check
   reads every byte again (`EITA_RESUME_VERIFY=1` re-hashes them first: for a 206 GB Ethereum
   base about 14 min at 250 MB/s). The fences are built on their own thread while the replay
   runs (lookups binary-search until then). A point without an anchored composition (a bisect
   layer, a copied snapshot) has its bytes re-hashed and is root-checked before anything runs on
   it.
5. **One point per block** in recovery: the first sealed of its anchored compositions (passed
   checks, fewest components first), then the base alone, then the widest layer chain.
6. **Reorg window**: compaction and tip-anchor checks stay `reorg-depth` behind the newest
   block, so a rollback within it only drops whole layers.
7. **No snapshot is unmapped under a reader**: swapped-out snapshots are closed by the replay
   thread only while neither background thread runs.
8. **GC never deletes under the replay**: the replay's GC pins its live stack, the composition
   the root check in flight reads, and a compaction's output. A restarted replay rewrites layers
   its previous life left under the same names, so without the pin a GC between the
   rename-aside and the publish would delete live layers. GC does not run while a compacted base
   waits for its check.
9. **A root checker lives only as long as its replay**: spawned with `--parent <pid>`, it exits
   within a second once that process is no longer its parent (it polls `getppid`, on Linux and
   macOS), releasing its heap and threads. Its scratch (`.root-N-PID/`) and its output files
   (deleted before each spawn: fresh inodes) are its own, so a replacement replay never shares
   them with a dying checker; startup removes stale `.root-*/` and `state-*.rootout`.

The concurrent protocols behind invariants 3, 6, 7 and 8 are modelled in Veil
(`verify/protocols/`: `LayerGcFixed`, `Compaction`, `CompactionDeepReorg`).

## 5. What is proved, what is assumed

`lean/Evm/Persist/Layered.lean` (standard axioms only):

| theorem | statement |
|---|---|
| `lookupAcct_eq`, `lookupSlot_eq` | lookup through the stack = lookup in the merged state |
| `apply_compose`, `applyAll_composeAll`, `compose_run_view` | composing a run of layers (minor compaction) leaves the view unchanged |
| `mat_idem`, `mat_apply_mat` | S1 is idempotent and commutes with a covered layer |
| `compact_view`, `compaction_correct` | a base compacted from base + layers, under the remaining layers, reads as the whole stack |
| `stack_view` | correct layers over the canonical base read as the canonical state at the top: after a freeze, and after a resume from any layer |
| `rollback_view` | dropping the newest layers of a correct stack reads as the canonical state at the new top |
| `fieldsCover_compose`, `fieldsCover_composeAll` | composition keeps FieldsCover |
| `gcSubset_preserves_resume`, `gcFiles_preserves_resume`, `resume_components_sealed` | GC over layered files (any part of the GC set: the replay pins its live stack) never moves the resume point; the resume point's components are sealed |

Recovery Part 1 (`resumePoint`, `gcSet`) is reused over the points; `src/state/recovery.lisp`
mirrors `dumpsOf`/`keepFiles`/`gcFiles` and is checked against `lake exe recoveryVectors`
(40,000 vectors, half of them layered).

Assumed (hypotheses, not theorems): the writer implements its contract (`LayerOK`: the layer it
writes turns the canonical state at its parent into the one at its block); the merge writer
implements `mat ∘ apply` (`CompactOK`); keccak collision resistance (a matching root means a
matching state); the replay is a function of the blocks (a reorg re-execution reproduces the
canonical branch).

## 6. Validation

- **Property tests** (`tests/layers.lisp`): random states; lookups, minor and major compaction
  and the layered root check against a model of `mat ∘ applyAll`. A mutant that ignores wipes
  fails 172 checks in 20 rounds.
- **Facts and roots**, Ethereum 4,900,001–4,910,000 from `snap-4900000`, anchors every 2,000,
  layers every 500: decoded rows of all seven fact kinds identical to a run without layers,
  `committed` equal, every anchor root OK over base + layers (with one minor compaction).
- **Resume from a mid-stack point**: from the anchor at 4,906,000 (base, a composed layer, four
  layers) and from the unverified layer at 4,907,500 (root-checked at resume): rows identical,
  every later anchor OK.
- **Reorg**: blocks 4,900,001–4,900,300 with a layer per block above 4,900,150; after 4,900,290
  a rollback to 4,900,270 (20 layers dropped) and re-execution: fact rows and row files
  byte-identical to the straight run, anchors root OK.
- **Cost**, same segment (run-block only, interpreter, M-series Mac):

  | run | wall | µs/tx | anchor pause |
  |---|---:|---:|---:|
  | no anchors, no layers | 49.1 s | 24.1 | — |
  | anchors every 2,000, layers every 500 | 70.2 s | 34.4 | ≤ 4.7 ms |
  | layers every 1,000 (budget), no root checks | 58.2 s | 28.6 | ≤ 0.1 ms |

  The difference over no anchors is the root checks sharing the cores (about 6 µs/tx) and
  re-faulting after each freeze (about 4 µs/tx). Layer size at 4.9M: about 11 MB per 500 blocks,
  against a 5.0 GB base.
- **Scale**, Ethereum 11,750,001–12,250,000 from a verified `snap-11750000` (116M accounts, 405M
  slots, 46 GB), anchors every 250,000, layers every 62,500, on 10 cores: 45.1 blocks/s; every
  anchor and the compacted base root OK; layers 1.1–1.34 GB, written in 36–55 s; a major
  compaction wrote the 46 GB base in 7 min; root checks over base + up to 5 layers took 531–582 s
  and finished 31k–45k blocks behind the replay. A crash run (kill -9 of the replay after a
  freeze, mid layer write, mid root check, mid major compaction, and of the checker alone)
  resumed through recovery every time, re-made every layer and the compacted base with the
  straight run's content hashes, and produced a fact log identical over all 500,000 blocks (1.1
  billion rows).
- **Fault injection** (an operator harness, not in this repository: an arm64 Linux VM, Arc
  1–30,000 from genesis, anchors every 600, layers every 150, seven major compactions in the
  reference): replay and checker kills, 7 seeds, 140 faults; replay, checker, both and power
  loss (an fsjournal `LD_PRELOAD` shim that rewinds unsynced operations), 6 seeds, 33 faults.
  Every trial's fact log is identical to the reference's and every trial ends at the reference's
  resume point (30,000), with no checker or replay left running.
- **Memory**: with a 16 GB heap and a 5 GB budget, Ethereum 13.75M–14.0M through an anchor and a
  major compaction keeps dynamic usage ≤ 5.4 GB and anonymous RSS 6.6 GB; GC is 4.9 % of wall.

## 7. Next: snapshot v2 and the per-block root

Specified in [state-snapshot-format.md](state-snapshot-format.md): records sorted by hashed
key, a frontier of subtrie references per anchor (`frontier-N/`), a root worker that checks
every block's root in the replay's process, the RAM reorg window with quarter-point disk layers
in place of minor compaction, and compaction to a verified anchor with the root computed in its
pass. Lean: `lean/Evm/Trie/Frontier.lean`, `Persist/Layered.lean` Part E; Veil: `RootWorker`,
`CompactionV2`.

## 8. Open

- The fault-injection harness exercises major compactions but not minor ones (Arc's early state
  is small); minor compaction is covered by the Ethereum segments and `tests/layers.lisp`.
- Root checks can fall far behind a very fast replay: at 3,000 blocks/s with a check every 600
  blocks (about 2 s each) the queue lags about 20,000 blocks, its oldest anchor holds back
  compaction, and the stack reaches about 180 layers. With a 32,768-block interval a check
  (minutes) finishes well within the interval.
- Metric subscribers have no rollback: a reorg with one attached stops the run.
- Layers record faulted-but-unchanged keys too (the hot set does not track dirtiness), so a
  layer is larger than the strict delta.
