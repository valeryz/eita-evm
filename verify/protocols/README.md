# verify/protocols — Veil models of the state layer's concurrent protocols

Each model is a transition system in [Veil](https://github.com/verse-lab/veil) (Lean 4): one
action per step of the code it abstracts, each action naming that code with `@code` (a defun,
or a step marked `; @veil defun/step` on its line in the Lisp). Three kinds:

- a **FIXED** model describes the running code and is proved safe;
- an **OLD** model describes an earlier version of the code and reproduces its bug as a
  reachable violation, so the property the FIXED model proves is known to be the one that
  failed;
- a **DESIGN** model describes code that is specified but not yet written, and is proved safe
  against the specification ([`docs/state-snapshot-format.md`](../../docs/state-snapshot-format.md)).

| model | kind (code described): what it establishes | result |
|---|---|---|
| `LayerGcFixed` | fixed (current): GC never deletes a layer under its writer: `live-components` reads `*base*` and `*layers*` once under `*stack-lock*` | safe: inductive invariant, IC3 certificate (`ic3_safe`) |
| `LayerGcOld` | old (0a9f2c0): with only the stack's snapshots pinned, GC deletes a frozen layer's directory under its writer ("rename: No such file") | violation; kernel-checked counterexample (`ic3_unsafe`) |
| `LayerGcSwapped` | old (807f8f5 with its two reads swapped, hypothetical): two unlocked reads of `*layers*` are safe only in one order: `append` must read the RAM layers first | violation in 10 steps |
| `Compaction` | fixed (current): the stack's protocol: freeze!, the writer, minor and major compaction and their swaps, the background root check, GC, `close-retired!`, `collect-written!`, `rollback-to!`, the resumed base's background fence; forks within `reorg-window` of the highest block run | safe: inductive invariant (11 clauses), every VC a kernel-checked lean-smt proof; 996,705 states model-checked |
| `CompactionDeepReorg` | fixed (current): the same properties for forks at any depth, including below a compacted base whose root check is due or running (`rollback-to!` kills the check and discards the base) | safe: the same inductive invariant, kernel-checked lean-smt proofs; 1,252,665 states model-checked; the old violation's 14-step prefix is `sat` and now ends with the base discarded |
| `CompactionDeepReorgOld` | old (f1d29c6): without that guard, `compaction-swap!` installs a base of the abandoned branch after a reorg below it | violation in 17 steps (model checker; `sat trace` by cvc5) |
| `CompactionV2` | design (planned): snapshot v2's stack: the RAM reorg window, the settled RAM layer and its quarter-point disk layer, the writer, major compaction to a verified anchor with the root in its pass and an immediate swap, GC and `close-retired!` with the root worker's pins, rollback at any requested depth (refused below the floor) | safe: inductive invariant (7 clauses), every VC a kernel-checked lean-smt proof (1,020 theorems); 75,609 states model-checked; four mutants (the worker's pin ignored by `close-retired!` or by GC, the floor guard dropped, a window layer settled above the floor) each a violation |
| `RootWorker` | design (planned): the per-block root worker: write-set ingest, a block's verdict keyed by (number, hash), `drop-above!` against `rollback-to!`, the undo window, the frontier checkpoint (freeze, publish, swap), the anchor line, GC of frontier directories | safe: inductive invariant (4 clauses), kernel-checked lean-smt proofs (602 theorems); 10,780 states model-checked; four mutants (no deletion of an abandoned frontier, a swap before N settles, queued write sets kept across a rollback, GC above the newest anchor) each a violation |

"Code described": *current* is the code at this commit (checked by `CheckCode.lean`); a commit
hash is the version an OLD model describes (its citations are checked with `git show`);
*planned* is code a DESIGN model describes before it exists. `CompactionV2` replaces
`Compaction` and `CompactionDeepReorg` when the v2 stack code lands.

**Design models and `@planned`.** A DESIGN model's changed steps cite `@planned` names.
`CheckCode.lean` lists each with the section of `docs/state-snapshot-format.md` that specifies
it, checks that the section exists, and fails once the defun (or marker) appears in the code, so
the citation becomes `@code` in the change that writes it.

**Rules the design models require.** `RootWorker` is safe only with two rules, both part of the
specification: the worker swaps to a new `frontier-N/` only once N is below the reorg floor
(until then it reads `frontier-A/` under its frozen overlay), and `drop-above! F` deletes a
published, unanchored frontier above F. Without the second, after a reorg below N the new
branch's checkpoint renames onto the abandoned branch's `frontier-N/`; without the first, that
deletion would unmap the frontier the worker reads. GC also never deletes a frontier above the
newest anchor (it may be in flight).

The three LayerGc models share `EitaVeil/LayerGc.lean`, the three Compaction models
`EitaVeil/CompactionParts.lean`: commands (Lean macros) each variant splices into its
`veil module`; a variant's own file holds only what differs (the pin, the rollback, the swap
without a layer at M, the invariant's use and the checks).

## The caller's fork bound (Compaction)

`Compaction`'s `rollback` keeps the fork point at or above `fin`, a block once `reorg-window`
behind the replay (every compaction stays at or below it). Core does not choose fork points:
the program that calls `rollback-chain!` does, and `Compaction` assumes it never forks below
`reorg-window` under the highest block it has run. A caller that searches for the fork
point no deeper than that meets it. Safety does not
rest on the bound: `CompactionDeepReorg` proves the same properties for forks at any depth.

### Compaction: what is modelled

Sorts `blk` (a total order) and `comp` (a RAM layer, a layer snap or a base; fresh ones are
allocated by freezes and compactions). Each component holds the deltas of blocks `lo < k ≤ hi`.
Actors, one atomic step per action: the replay thread (freeze!, a fault's lock-free walk of the
list it read, compaction-step!'s start and take, root-check spawn and collection with
compaction-swap!, prune-dumps! = live-components then run-gc, close-retired!, collect-written!,
rollback-to! with its kill of a root check and discard of a pending base above T), the layer
writer (take, write, publish, open, swap), the compactor (write-composed, publish, open), the
`eita check-root` process (runs, exits), the resumed base's fence thread (build, publish).
Properties: the stack covers every block up to the newest freeze exactly once (against a
ghost owner per block set by what each step means to do), nothing above it, only
canonical-chain deltas, one base, every snap in it on disk and mapped; no snap-close of a
component a thread may read (stack, a fault's list, the writer's BELOW, a compaction's inputs,
a fence being built); GC/rollback never delete a stack component, a compaction's output, the
compacted base waiting for its check, the writer's layer, or a dir a root check reads whose
verdict will count; RAM tables never cut while reachable; a fence pointer only to a built
fence; a compaction's run still in the stack at its swap; no writer/compactor rename/open
failure.

**The deep-reorg guard (CompactionDeepReorg vs CompactionDeepReorgOld).** Once
compaction-step! has taken a major result, `*compactor-job*` is NIL while `*compacting-base*`
and `*base-check-due*` wait for the base's root check. A rollback below the base's block M must
therefore act on the pending base itself: `rollback-to!` kills a root check above T and
discards a pending base above T (`discard-compacting-base!`), and `compaction-swap!` refuses a
base with no layer at M. Without these (`CompactionDeepReorgOld`), the rollback either leaves
`*compacting-base*` set for good (no compaction starts, GC stops, `finish-anchors!` never
returns), or lets the check pass later against the base's own manifest root, and
`compaction-swap!` installs snap-M of the abandoned branch under the kept layers. Two reorgs in a
row, each within `reorg-window` of the block being run, can reach below M.

### Atomicity and memory-ordering assumptions (Compaction)

- `*layers*`/`*base*`: every publication under `*stack-lock*` with `(barrier (:write))` before
  the store (an ordering check); faults read the list once and load through it
  (address-dependent, ordered on ARM64). `*base*` changes only on the replay thread, so a
  fault's two reads (`view-* *layers* *base*`) see one stack.
- The fence: built, then `(barrier (:write))`, then the pointer (`snap-open/publish`): the
  model's f_build before f_pub; `snap-close` joins the fence thread before unmapping.
- `*writer-busy*` is set in the same critical section that reads BELOW (`write-layer!/take`)
  and cleared in the one that swaps (`write-layer!/swap`); `close-retired!` and
  `writer-idle-p` read it without the lock. Seeing T is ordered by the lock (every retiring
  swap takes it after the writer's read). Seeing NIL then unmapping relies on the writer's
  loads from BELOW being done before its `*writer-busy* NIL` store is visible: ARM64 allows a
  later store to pass earlier loads, and only a lock acquire sits between them; in the code
  the file syscalls of merge-finish and snap-publish (fsync, rename) separate them. Assumed,
  not modelled.
- `*compactor*` is cleared only after `join-thread` (`compaction-step!/join`), which
  synchronizes; the compactor's result and error are read after it.
- Replay-thread steps are atomic with respect to each other; with respect to the writer,
  compactor and fence thread each touches shared state in one critical section (freeze!, the
  minor splice, compaction-swap!, live-components' read), or runs with them stopped
  (rollback-to!: writer drained, compactor joined). rollback-to! kills a check above T and
  discards a pending base above T before it publishes the kept stack and deletes the dropped
  layers: one step (the Old variant: rollback-chain! killed it after the deletions, harmless
  because its verdict is dropped).
- Abstractions: GC may delete any unpinned component (`gc-files` not modelled); `rm -rf` of
  one directory is one step; the minor-run size tiers, the pending-anchor fence and the anchor
  queue are not modelled (they decide which runs and checks happen, not their safety); only the
  initial base fences in the background (every resumed component takes the same path).

## Running

Toolchain: core's (`lean-toolchain` links to `../../lean/lean-toolchain`). Veil is pinned in
`lakefile.toml` and every dependency in `lake-manifest.json` by full commit SHA. Core's `lean/`
package does not depend on this one.

    scripts/verify-protocols.sh             # the code check, then all eight models, one at a time
    scripts/verify-protocols.sh --quick     # the code check and the six models under 10 GB
    scripts/verify-protocols.sh LayerGcFixed  # the code check and one model

Cost on a 64 GB M-series Mac (one model at a time, peak RSS of the process tree):

| model | wall | peak RSS | in `--quick` |
|---|---|---|---|
| LayerGcFixed | 1.5 min | 4.2 GB | yes |
| LayerGcSwapped | 0.3 min | 2.9 GB | yes |
| CompactionDeepReorgOld | 2.1 min | 5.7 GB | yes |
| Compaction | 5.8 min | 9.1 GB | yes |
| CompactionV2 | 3.6 min | 6.5 GB | yes |
| RootWorker | 1.0 min | 3.1 GB | yes |
| LayerGcOld | 3.7 min | 6.6 GB | no (its `ic3_unsafe` certificate is the slow part) |
| CompactionDeepReorg | — | > 32 GB | no: exceeds the default cap in its 1,252,665-state model check; run it with a higher `EITA_PROTOCOLS_MAX_GB` |

`lake build` here builds only the shared parts and the code check (`EitaVeil.Code`,
`EitaVeil.LayerGc`, `EitaVeil.CompactionParts`); the script elaborates each model with `lake
env lean --load-dynlib=<cvc5 FFI>` (`lake build` would load it too, but holds every message to
the end), under a memory cap on the whole process tree (`EITA_PROTOCOLS_MAX_GB`, default 32),
and prints each model's wall time and peak RSS. A model passes when it elaborates without an
error, prints its expected result (a FIXED model: no violation, its `ic3_safe` axioms or the
VC theorems' axioms; an OLD model: the violation, its traces), and every axiom list printed is
`propext, Classical.choice, Quot.sound`.

## The code check

    cd verify/protocols && lake env lean --run CheckCode.lean     # seconds; the script runs it first

`EitaVeil/Code.lean` reads the cited Lisp (a small reader: lists, atoms, strings; comments
skipped) and checks every `@code` citation of `EitaVeil/*.lean`:

- `@code freeze!`: exactly one `(defun freeze! …)` in the cited files;
- `@code freeze!/push`: a `; @veil freeze!/push` marker on the cited line, inside
  `(defun freeze! …)`; every marker is cited by some model (no orphans);
- `@code snapshot-world.lisp@0a9f2c0:315`: historical code an OLD model describes; a row of
  `CheckCode.lean` gives the fragment that line holds at that commit (`git show`).

Then the orderings the proofs rest on (structural checks over the forms, `CheckCode.lean`):
`live-components` reads `*layers*` and `*base*` exactly once, inside `(with-mutex
(*stack-lock*))`; every `(setf … *layers* …)` in snapshot-world.lisp directly follows
`(sb-thread:barrier (:write))`; so does every `(setf (snap-…-fence s) …)` in `snap-open`;
`snap-close` joins the fence thread before it unmaps; `close-retired!` closes only under `(not
*writer-busy*)` and `(null *compactor*)`; `write-layer!` sets `*writer-busy*` in the critical
section that reads `stack-below` and clears it in the one that swaps; `rollback-to!` drains the
writer and joins the compactor before it publishes the shortened stack, and after its
below-the-base error kills a root check above T, then discards a pending base above T, then
publishes the kept stack and deletes the dropped layers (`rollback-chain!` kills no check
itself); `compaction-swap!` refuses unless a layer at M is in the stack, before it installs.

Markers survive edits that only move code. A change to a marked line, or a moved, renamed or
deleted step, is in sight of its marker: update the model and the marker together, and re-run
the model.

## Trust

- Safety of a FIXED model: `#updr certify` produces `ic3_safe` (reachable ⇒ property, for
  every instantiation of the sorts), kernel-checked, axioms `propext, Classical.choice,
  Quot.sound` only. `#check_invariants` runs with `veil.smt.trust false`: each solver
  answer is reconstructed by lean-smt into a proof term (no trusted cvc5).
- Compaction, CompactionDeepReorg, CompactionV2 and RootWorker have no `ic3_safe`: `#updr`'s
  search finds Compaction's invariant inductive at frame 1 (30 solver calls, 243 s), but
  building the certificate's kernel term exceeds 35 GB of memory. Their safety
  rests instead on `#check_invariants` under `veil.smt.trust false`: initiation and every
  action's consecution of all their clauses, each a lean-smt proof term that `#gen_theorems` adds
  as a theorem (kernel-checked; `report_axioms` prints their axioms). That is the same
  statement ic3_safe packages (inductive invariant ⇒ every reachable state is safe), minus the
  one closing lemma. The pinned Veil's certificate also cannot re-pose an `if` whose condition
  has a `¬` or `≠` (`assumption` fails on `a ≠ b` against `distinctN [a, b]`): the models
  write such conditions as `r x = false` or as assignments, which keeps the certificate
  possible on a larger machine.
- An OLD model's violation: `#updr (expect := unsafe) certify` gives `ic3_unsafe` (LayerGcOld),
  a kernel-checked counterexample at the model's sort sizes (evaluation, no solver in the
  proof); otherwise it rests on the next item.
- `sat trace` / `unsat trace` and the bounded `#model_check` rest on cvc5 1.3.2 and Veil's
  explicit-state checker respectively (not kernel-checked).
- What no tool checks: that an action is a faithful abstraction of the cited code (the code
  check only keeps the citations current), the atomicity each action assumes, and
  memory-model effects: the models are sequentially consistent; the ARM64 publication order
  of `*layers*` is the write barriers' (argued in the message of commit 28a9f4f), not modelled.

## Next models, in priority order

1. Fact-log sealing and resume: the writer's `.sealed.tmp` → sealed rename, the `committed`
   marker, kill at any step, `recovery resume`.
2. Decoder → replay → verifier pipeline: the block decoder thread, the replay, the root
   check, and their queues and back-pressure.
