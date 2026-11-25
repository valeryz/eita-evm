module

public import EitaVeil.CompactionParts

/-! # The per-block root worker: verdicts, `drop-above!`, the frontier checkpoint, anchors (snapshot v2, planned): safe

The design model of the root worker (`docs/state-snapshot-format.md`, "The root worker"),
written before its code: its steps cite `@planned` names (`CheckCode.lean` lists them, and
fails once one exists in the code, so the citation becomes `@code` with the code's PR).

Sorts `blk` (block numbers, a total order) and `ws` (a block as executed: number and hash,
with its write set). `canon w`: `w` is on the replay's chain. Threads: the replay thread
(execution, `rollback-to!`, the anchor line, GC), the worker's coordinator (ingest, a
block's root, the checkpoint's freeze and swap) and the checkpoint writer (frontier-N/).

What is checked:
* a verdict is published only for a block whose write set the worker consumed, computed from
  exactly its chain (`verdict_exact`), keyed by the block (number and hash), and forgotten when
  a rollback drops the block;
* `drop-above! F` (called by `rollback-to!` only) restores the worker's state at F: no
  consumed block above F without an undo record (`no_hazard`), and the consumed set is again
  the chain up to the worker's block (`worker_exact`);
* no frontier-N published before verdict(N) passed, and every frontier directory holds a
  verified block's state (`frontier_verified`); the worker never maps a deleted frontier; the
  anchor line names a canonical, verified block's frontier (`anchor_good`); no rename onto an
  existing frontier directory.

Two rules of the design the model requires: (1) the worker swaps to frontier-N only
once N is below the reorg floor (settled; until then it keeps reading frontier-A under its
frozen overlay), and (2) `drop-above! F` deletes a published, unanchored frontier above F (and
aborts a checkpoint above F). Without (2) a reorg below N leaves the abandoned branch's
frontier-N, and the new branch's checkpoint at N renames onto it; without (1) that deletion
would unmap the worker's current frontier.

Abstractions: the anchor cadence and the frontier contents are not modelled (a checkpoint may
start at any consumed block above the current frontier); a published verdict stands for a
computed root equal to the header's (a mismatch stops the chain); GC may delete any frontier
directory at or below the newest anchor that is not pinned (`gc-files`' rule over the kept
anchors is proved in `lean/Evm/Persist/Layered.lean`).
-/

veil module RootWorker

type blk
instantiate ord : TotalOrder blk
open TotalOrder
type ws

enum CPC = { CIdle, CRun }
enum KPC = { KIdle, KWrite, KPub }
enum GPC = { GIdle, GDel }

immutable individual h0 : blk             -- the resume anchor's block
immutable individual w0 : ws              -- its block

function num : ws → blk
relation fresh : ws → Bool                -- not executed yet
relation canon : ws → Bool                -- on the replay's chain
relation queued : ws → Bool               -- its write set on the stream, not consumed
relation cons : ws → Bool                 -- consumed: folded into the worker's state
relation undo : ws → Bool                 -- its undo record is kept (reorg window)
relation vpub : ws → Bool                 -- its verdict is published
relation vgood : ws → Bool                -- ghost: computed from exactly its chain
relation krep : ws → Bool                 -- the worker reported "frontier-(num w) published for w"
individual etop : blk                     -- the replay's newest block
individual wtop : blk                     -- the worker's block
individual floor : blk                    -- the reorg floor (no fork below it)
individual cpc : CPC                      -- the coordinator computing a block's root
individual cw : ws
individual kpc : KPC                      -- the checkpoint
individual kw : ws
relation fdisk : blk → Bool               -- frontier-N/ exists (sealed)
function fbr : blk → ws                   -- ghost: whose state frontier-N/ holds
individual fcur : blk                     -- the frontier the worker maps
relation anch : blk → Bool                -- anchors.sexp has a line for N
individual atop : blk                     -- the newest anchor
individual gpc : GPC
relation fpin : blk → Bool                -- GC's pins

individual bad_undo : Bool                -- drop-above! met a consumed block with no undo record
individual bad_map : Bool                 -- a frontier the worker maps or writes was deleted
individual ferr : Bool                    -- rename onto an existing frontier-N/

#gen_state

assumption [h0_least] ∀ b, le h0 b

after_init {
  num X := h0
  fresh X := X ≠ w0
  canon X := X = w0
  queued X := false
  cons X := X = w0
  undo X := false
  vpub X := X = w0
  vgood X := X = w0
  krep X := X = w0
  etop := h0
  wtop := h0
  floor := h0
  cpc := CIdle
  cw := w0
  kpc := KIdle
  kw := w0
  fdisk N := N = h0
  fbr N := w0
  fcur := h0
  anch N := N = h0
  atop := h0
  gpc := GIdle
  fpin N := false
  bad_undo := false
  bad_map := false
  ferr := false
}

/-! ## Replay thread: a block executes; its write set goes on the stream (@planned emit-write-set) -/
action exec (w : ws) (n : blk) {
  require gpc = GIdle
  require fresh w
  require le etop n ∧ etop ≠ n
  fresh w := false
  num w := n
  canon w := true
  queued w := true
  etop := n
}

/-! ## The chain: the reorg floor advances (reorg-window below the replay) -/
action advance_floor (x : blk) {
  require le floor x ∧ le x etop ∧ le x wtop
  floor := x
}

/-! ## Coordinator: ingest the oldest write set (@planned root-worker-ingest) -/
action consume (w : ws) {
  require cpc = CIdle
  require queued w
  require ∀ v, queued v → le (num w) (num v)
  queued w := false
  cons w := true
  undo w := true
  wtop := num w
}

/-! ## Coordinator: a block's root on the pool, then its verdict (n, hash) (@planned root-worker-block) -/
action v_start (w : ws) {
  require cpc = CIdle
  require cons w ∧ num w = wtop
  cw := w
  cpc := CRun
}
action v_pub {                             -- @planned root-verdict
  require cpc = CRun
  vpub cw := true
  if (∀ v, cons v → canon v ∧ le (num v) (num cw)) ∧
     (∀ v, (canon v ∧ fresh v = false ∧ le (num v) (num cw)) → cons v) then
    vgood cw := true
  else
    vgood cw := false
  cpc := CIdle
}

/-! ## Coordinator: undo records older than the reorg floor are dropped -/
action u_trim (w : ws) {
  require le (num w) floor
  undo w := false
}

/-! ## Coordinator: the frontier checkpoint at anchor N (@planned root-worker-checkpoint!) -/
action ck_start (w : ws) {                 -- freeze the overlay at the block boundary N
  require cpc = CIdle ∧ kpc = KIdle
  require cons w ∧ num w = wtop
  require le fcur (num w) ∧ fcur ≠ num w
  kw := w
  kpc := KWrite
}
action ck_pub {                            -- @planned root-worker-checkpoint!/publish fsync, rename, fsync the parent
  require kpc = KWrite
  require vpub kw                          -- verdict(N) passed first
  if fdisk (num kw) then
    ferr := true
  else
    fdisk (num kw) := true
    fbr (num kw) := kw
    krep kw := true
  kpc := KPub
}
action ck_swap {                           -- @planned root-worker-checkpoint!/swap at a block boundary, N settled
  require kpc = KPub ∧ cpc = CIdle
  require le (num kw) floor
  fcur := num kw
  kpc := KIdle
}

/-! ## Replay thread: the anchor line, after layer N, frontier-N and verdict(N) (@planned anchor-line!) -/
action anchor (w : ws) {
  require gpc = GIdle
  require canon w ∧ le (num w) floor       -- layer-P-N/ is written once N is settled
  require krep w                           -- the worker's report: frontier-N published for (N, hash)
  require le atop (num w) ∧ atop ≠ num w
  anch (num w) := true
  atop := num w
}

/-! ## Replay thread: rollback-to! F, which calls drop-above! F (@planned root-worker-drop-above!) -/
action rollback (f : blk) {
  require gpc = GIdle
  require le floor f ∧ le f etop           -- a fork below the floor is refused
  require cpc = CIdle                      -- the worker stops at its next block boundary
  -- the replay drops the blocks above F
  canon X := decide $ canon X ∧ le (num X) f
  etop := f
  -- drop-above! F: the queued write sets above F
  queued X := decide $ queued X ∧ le (num X) f
  -- the undo log above F (every record kept)
  if ∃ w, cons w ∧ ¬ le (num w) f ∧ undo w = false then bad_undo := true
  cons X := decide $ cons X ∧ le (num X) f
  undo X := decide $ undo X ∧ le (num X) f
  wtop := if le wtop f then wtop else f
  -- the verdicts above F
  vpub X := decide $ vpub X ∧ le (num X) f
  krep X := decide $ krep X ∧ le (num X) f
  -- a checkpoint above F is aborted, and a published, unanchored frontier above F deleted
  kpc := if le (num kw) f then kpc else KIdle
  if ¬ le fcur f then bad_map := true
  fdisk N := decide $ fdisk N ∧ (le N f ∨ anch N)
}

/-! ## Replay thread: GC of frontier directories (@planned live-components/worker, run-gc) -/
action g_pin {                             -- under *stack-lock*: the worker's current frontier and its checkpoint's
  require gpc = GIdle
  fpin N := decide $ N = fcur ∨ (kpc ≠ KIdle ∧ N = num kw)
  gpc := GDel
}
action g_delete (n : blk) {
  require gpc = GDel
  require fdisk n ∧ fpin n = false
  require le n atop                        -- nothing above the newest anchor: in flight
  if n = fcur ∨ (kpc ≠ KIdle ∧ n = num kw) then bad_map := true
  fdisk n := false
}
action g_done {
  require gpc = GDel
  fpin N := false
  gpc := GIdle
}

-- a verdict is computed from exactly its block's chain
safety [verdict_exact] vpub X → vgood X
-- the worker's state is its chain up to its block (drop-above! restores it)
safety [worker_exact] cons X → canon X ∧ le (num X) wtop
-- every frontier directory holds a verified block's state; the anchor line names a canonical one
safety [frontier_verified] fdisk N → num (fbr N) = N ∧ vgood (fbr N)
safety [anchor_good] anch N → canon (fbr N) ∧ num (fbr N) = N
safety [no_hazard] bad_undo = false ∧ bad_map = false ∧ ferr = false ∧ fdisk fcur

-- the inductive invariant behind the safety properties
-- executed blocks: one per number on the chain, all of them consumed or queued in order
invariant [blocks]
    (fresh X → X ≠ w0 ∧ ¬ canon X ∧ ¬ queued X ∧ ¬ cons X ∧ ¬ undo X ∧ ¬ vpub X ∧ ¬ krep X) ∧
    (¬ fresh w0 ∧ canon w0 ∧ cons w0 ∧ num w0 = h0 ∧ vgood w0 ∧ ¬ fresh cw ∧ ¬ fresh kw) ∧
    (canon X → le (num X) etop) ∧
    (canon X ∧ canon Y ∧ num X = num Y → X = Y) ∧
    (le floor wtop ∧ le wtop etop)
-- the worker: its state is exactly the chain up to wtop; the rest of the chain is queued above it
invariant [worker]
    (queued X → canon X ∧ ¬ cons X ∧ ¬ le (num X) wtop) ∧
    (canon X ∧ ¬ cons X → queued X) ∧
    (canon X ∧ le (num X) wtop → cons X) ∧
    (cons X ∧ ¬ le (num X) floor → undo X) ∧
    (cpc = CRun → cons cw ∧ num cw = wtop) ∧
    (vpub X → cons X)
-- the checkpoint and the frontier directories
invariant [frontier]
    (kpc ≠ KIdle → cons kw ∧ ¬ le (num kw) fcur ∧ le (num kw) wtop) ∧
    (kpc = KPub → fdisk (num kw) ∧ fbr (num kw) = kw ∧ krep kw) ∧
    (fdisk N ∧ ¬ le N fcur → kpc = KPub ∧ N = num kw) ∧
    (le fcur floor) ∧
    (krep X → canon X ∧ vgood X ∧ fbr (num X) = X ∧ (le (num X) fcur ∨ (kpc = KPub ∧ X = kw))) ∧
    (le atop fcur ∨ (kpc = KPub ∧ atop = num kw)) ∧
    (anch N → le N atop ∧ le N floor ∧ krep (fbr N) ∧ num (fbr N) = N) ∧
    (anch atop) ∧
    (fdisk N → fresh (fbr N) = false)
-- GC between its pin and its deletions
invariant [gc]
    gpc = GDel → (fpin fcur ∨ ¬ le fcur atop) ∧ (kpc ≠ KIdle → fpin (num kw) ∨ ¬ le (num kw) atop)

-- #check_invariants reconstructs lean-smt proofs instead of trusting cvc5's unsat
set_option veil.smt.trust false

#gen_spec

set_option veil.violationIsError false in
#model_check { blk := Fin 3, ws := Fin 3 } { h0 := 0, w0 := 0 }

-- every action preserves the invariant (and init establishes it): each VC a lean-smt proof
-- term, added as a theorem and kernel-checked by #gen_theorems
#check_invariants
#gen_theorems
report_axioms "RootWorker"

end RootWorker
