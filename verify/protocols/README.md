# verify/protocols — Veil models of the state layer's concurrent protocols

Each model is a transition system in [Veil](https://github.com/verse-lab/veil) (Lean 4): one
action per step of the code it abstracts, each action naming that code with `@code` (a defun,
or a step marked `; @veil defun/step` on its line in the Lisp). An OLD model reproduces a bug
as a reachable violation; a FIXED model of the same protocol is proved safe.
`CompactionDeepReorgOld` is a finding of the models themselves (no stress loop saw it): the
fixed code is `CompactionDeepReorg` (any fork depth) and `Compaction` (forks bounded by the
caller).

| model | code | result |
|---|---|---|
| `LayerGcOld` | 0a9f2c0: `live-components` pins only the stack's snaps | violation (GC deletes a layer under its writer, "rename: No such file"); kernel-checked counterexample |
| `LayerGcSwapped` | 807f8f5's two reads of `*layers*` in the other order (hypothetical) | violation in 10 steps: 807f8f5 was safe only because `append` reads the RAM layers first |
| `LayerGcFixed` | now (28a9f4f): one read of `*base*`/`*layers*` under `*stack-lock*` | safe: inductive invariant, IC3 certificate |
| `Compaction` | now (674e575): freeze!, the writer, minor/major compaction and their swaps, the background root check, GC, `close-retired!`, `collect-written!`, `rollback-to!`, the resumed base's background fence; forks within `reorg-window` of the highest block run | safe: inductive invariant (11 clauses), every VC a kernel-checked lean-smt proof; 996,705 states model-checked |
| `CompactionDeepReorg` | now, forks at any depth: below a compacted base whose root check is due or running (`rollback-to!` kills the check and discards the base) | safe: the same inductive invariant, kernel-checked lean-smt proofs; 1,252,665 states model-checked; the old violation's 14-step prefix `sat` (the rollback discards the base); last full run before the move into core (2026-11-09): it now exceeds the 32 GB cap here, see the cost table |
| `CompactionDeepReorgOld` | `rollback-to!` and `compaction-swap!` as at f1d29c6 (the rest as now), forks at any depth | violation in 17 steps (model checker; `sat trace` by cvc5): `compaction-swap!` installs a base of the abandoned branch (finding, fixed in 674e575) |

The three LayerGc models share `EitaVeil/LayerGc.lean`, the three Compaction models
`EitaVeil/CompactionParts.lean`: commands (Lean macros) each variant splices into its
`veil module`; a variant's own file holds only what differs (the pin, the rollback, the swap
without a layer at M, the invariant's use and the checks).

## The caller's fork bound (Compaction)

`Compaction`'s `rollback` keeps the fork point at or above `fin`, a block once `reorg-window`
behind the replay (every compaction stays at or below it). Core does not choose fork points:
the program that calls `rollback-chain!` does, and `Compaction` assumes it never forks below
`reorg-window` under the highest block it has run. Eita's node meets that (its `reorg!`
searches down to `reorg-fork-floor`; the node's own code check verifies it). Safety does not
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

**Finding (CompactionDeepReorgOld), fixed in 674e575.** At f1d29c6 `rollback-to!` refused a
fork below a *running* compaction (`*compactor-job*`), but once compaction-step! had taken a
major result the job was NIL and `*compacting-base*` / `*base-check-due*` waited for the
base's root check, unguarded. A rollback below its block M then either killed that check (in
`rollback-chain!`) and left `*compacting-base*` set for good (no compaction starts, GC stops,
`finish-anchors!` never returns), or, the check still due behind an anchor check, let it pass
later against the base's own manifest root, and `compaction-swap!` found no layer at M and
installed snap-M of the abandoned branch under the kept layers. Eita's node then bounded the
fork by `reorg-window` below the block being run, so two reorgs in a row could reach below M.
Fixed: `rollback-to!` kills a root check above T and discards a pending base above T
(`discard-compacting-base!`); `compaction-swap!` refuses a base with no layer at M.

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

    scripts/verify-protocols.sh             # the code check, then all six models, one at a time
    scripts/verify-protocols.sh --quick     # the code check and the four models under 10 GB
    scripts/verify-protocols.sh LayerGcFixed  # the code check and one model

Cost on a 64 GB M-series Mac (2026-11-12, one model at a time, peak RSS of the process tree):

| model | wall | peak RSS | in `--quick` |
|---|---|---|---|
| LayerGcFixed | 1.5 min | 4.2 GB | yes |
| LayerGcSwapped | 0.3 min | 2.9 GB | yes |
| CompactionDeepReorgOld | 2.1 min | 5.7 GB | yes |
| Compaction | 5.8 min | 9.1 GB | yes |
| LayerGcOld | 3.7 min | 6.6 GB | no (its `ic3_unsafe` certificate is the slow part) |
| CompactionDeepReorg | — | > 32 GB | no: stopped at the cap in its 1,252,665-state model check (earlier runs: 7.6 min, 21 GB) |

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
- Compaction and CompactionDeepReorg have no `ic3_safe`: `#updr`'s search finds Compaction's
  invariant inductive at frame 1 (30 solver calls, 243 s), but building the certificate's
  kernel term ran past 35 GB of memory in 15 min on a 64 GB Mac and was stopped. Their safety
  rests instead on `#check_invariants` under `veil.smt.trust false`: initiation and every
  action's consecution of all 11 clauses, each a lean-smt proof term that `#gen_theorems` adds
  as a theorem (kernel-checked; `report_axioms` prints their axioms). That is the same
  statement ic3_safe packages (inductive invariant ⇒ every reachable state is safe), minus the
  one closing lemma. Veil 22cbf1a's certificate also cannot re-pose an `if` whose condition
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
  of `*layers*` is the write barriers', argued in 28a9f4f's commit message, not modelled.

## Next models, in priority order

1. Fact-log sealing and resume: the writer's `.sealed.tmp` → sealed rename, the `committed`
   marker, kill at any step, `recovery resume`.
2. Decoder → replay → verifier pipeline: the block decoder thread, the replay, the root
   check, and their queues and back-pressure.
