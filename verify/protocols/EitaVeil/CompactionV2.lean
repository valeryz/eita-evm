module

public import EitaVeil.CompactionParts

/-! # The layer stack under snapshot v2's reorg window and anchored compaction (planned): safe

The design model of the stack under snapshot v2 (`docs/state-snapshot-format.md`, "The RAM
reorg window" and "Compaction to a verified anchor"), written before its code: steps that change cite
`@planned` names (`CheckCode.lean` lists them and fails once one exists in the code). It
replaces `Compaction` / `CompactionDeepReorg` when the code lands; until then those describe
the running code.

What changed from `Compaction`:
* **The RAM reorg window.** Every block freezes a RAM layer (`freeze`); a block leaving the
  window (at or below `fin`) is folded into the one open **settled RAM layer** (`settle`,
  Lean `compose`); at a quarter point the settled layer goes to the writer (`qpoint`), which
  writes it as one disk layer. There is no minor compaction.
* **Compaction to a verified anchor.** Major compaction merges the base and the disk layers
  up to a verified anchor A (`vfy`), computes the root in the same pass and swaps the new base
  in at once (`take_major`): no pending base, no root-check process, no `*compacting-base*`.
* **Persisted fences.** Opening a snap maps its fence: no fence thread.
* **The root worker reads the stack.** It adopts base + disk layers under `*stack-lock*` and
  pins them (`wv_adopt`); GC and `close-retired!` wait for its pin, as for the writer and the
  compactor (I7 gains an actor); it never reads a RAM layer.
* **Rollback at any depth, refused below the floor.** `rollback-to!` drops only window RAM
  layers: the writer and the compactor work at or below `fin`, so it neither drains the writer
  nor joins the compactor, and no pending base exists to discard.

Sorts, components and threads as in `Compaction` (`EitaVeil/CompactionParts.lean`), without
the root-check process and the fence thread, with the root worker. Properties: those of
`Compaction` (`stack_composes`, `stack_live`, `no_hazard`) plus: the worker never reads an
unmapped snap and GC never deletes one it pins; a rollback never removes a settled or disk
component; the compaction's in-pass root never mismatches (its inputs are canonical).
-/

veil module CompactionV2

set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 1000000

type blk
instantiate ord : TotalOrder blk
open TotalOrder
type comp

enum WPC = { WIdle, WRead, WPub, WOpen, WSwap, WFail }
enum CPC = { CNone, CRead, CPub, COpen, CDone }
enum GPC = { GIdle, GDel }
enum DPC = { DIdle, DIn }

immutable individual h0 : blk           -- the base's block at the start: the least block
immutable individual c0 : comp          -- that base

relation fresh : comp → Bool
function lo : comp → blk
function hi : comp → blk
relation isbase : comp → Bool
relation ram : comp → Bool              -- a RAM layer (window or settled)
relation settled : comp → Bool          -- the settled RAM layer, open or handed to the writer
relation tables : comp → Bool
relation instack : comp → Bool
relation valid : comp → Bool
relation disk : comp → Bool
relation mapped : comp → Bool
relation retired : comp → Bool
relation written : comp → Bool
relation queued : comp → Bool
function owner : blk → comp             -- ghost
individual top : blk
individual fin : blk                    -- the reorg floor: no fork below it
individual slive : Bool                 -- a settled layer is open
individual sl : comp                    -- ... that one
relation vfy : blk → Bool               -- a verified anchor's block (its anchor line)

individual wpc : WPC
individual wl : comp
relation wbelow : comp → Bool
individual cpc : CPC                    -- the compactor (*compactor* non-NIL = cpc ≠ CNone)
individual cout : comp
individual cz : comp                    -- ghost: the layer at M
relation crd : comp → Bool
individual gpc : GPC
relation pinned : comp → Bool
individual dpc : DPC
relation rset : comp → Bool
relation rram : comp → Bool
relation wvpin : comp → Bool            -- the root worker's view (base and disk layers it pinned)

individual bad_unmap : Bool
individual bad_delete : Bool
individual bad_tables : Bool
individual bad_read : Bool
individual bad_swap : Bool
individual bad_wread : Bool             -- the worker read an unmapped snap
individual bad_drop : Bool              -- a rollback removed a settled or disk component
individual werr : Bool
individual cerr : Bool                  -- the in-pass root mismatched (a non-canonical input)

#gen_state

assumption [h0_least] ∀ b, le h0 b

after_init {
  fresh C := C ≠ c0
  lo C := h0
  hi C := h0
  isbase C := C = c0
  ram C := false
  settled C := false
  tables C := false
  instack C := C = c0
  valid C := true
  disk C := C = c0
  mapped C := C = c0      -- the persisted fence is mapped with it
  retired C := false
  written C := false
  queued C := false
  owner K := c0
  top := h0
  fin := h0
  slive := false
  sl := c0
  vfy B := B = h0
  wpc := WIdle
  wl := c0
  wbelow C := false
  cpc := CNone
  cout := c0
  cz := c0
  crd C := false
  gpc := GIdle
  pinned C := false
  dpc := DIdle
  rset C := false
  rram C := false
  wvpin C := false
  bad_unmap := false
  bad_delete := false
  bad_tables := false
  bad_read := false
  bad_swap := false
  bad_wread := false
  bad_drop := false
  werr := false
  cerr := false
}

/-! ## Replay thread: every block freezes a RAM layer of the window (@code freeze!) -/
action freeze (l : comp) (n : blk) {
  require gpc = GIdle ∧ dpc = DIdle
  require fresh l
  require le top n ∧ top ≠ n
  fresh l := false
  lo l := top
  hi l := n
  isbase l := false
  ram l := true
  settled l := false
  tables l := true
  valid l := true
  disk l := false
  mapped l := false
  retired l := false
  written l := false
  queued l := false
  instack l := true
  owner K := if le K n ∧ ¬ le K top then l else owner K
  top := n
}

/-! ## Replay thread: the oldest window layer leaves the window (@planned settle!) -/
action settle (l : comp) {
  require gpc = GIdle ∧ dpc = DIdle
  require instack l ∧ ram l ∧ settled l = false ∧ le (hi l) fin
  require ∀ c, (instack c ∧ ram c ∧ settled c = false ∧ c ≠ l) → le (hi l) (lo c)
  if slive then
    -- Lean `compose` into the open settled layer's tables (newest wins); l's tables are dropped
    hi sl := hi l
    owner K := if le K (hi l) ∧ ¬ le K (lo l) then sl else owner K
    instack l := false
    ram l := false
    tables l := false
  else
    settled l := true
    sl := l
    slive := true
}

/-! ## Replay thread: a quarter-anchor point hands the settled layer to the writer (@planned settle!/quarter) -/
action qpoint {
  require gpc = GIdle ∧ dpc = DIdle
  require slive
  queued sl := true                       -- @code freeze!/pipe pipe-put
  slive := false
}

/-! ## The layer writer: @code writer-loop → @code write-layer! -/
action w_take (l : comp) {               -- @code write-layer!/take *writer-busy*, stack-below under the lock
  require wpc = WIdle
  require queued l
  require ∀ c, (instack c ∧ ram c) → le (hi l) (hi c)    -- the pipe is oldest first
  queued l := false
  wl := l
  wbelow C := decide $ instack C ∧ C ≠ l ∧ le (hi C) (lo l)
  if ∃ c, instack c ∧ c ≠ l ∧ le (hi c) (lo l) ∧ ram c then werr := true  -- @code write-layer!/ram-below
  wpc := WRead
}
action w_read {                          -- @code write-layer!/write → @code write-ram-tables
  require wpc = WRead
  if tables wl = false then bad_tables := true
  if ∃ c, wbelow c ∧ mapped c = false then bad_read := true
  wpc := WPub
}
action w_pub {                           -- @code write-ram-tables/publish → @code snap-publish (fence written in the pass)
  require wpc = WPub
  disk wl := true
  wpc := WOpen
}
action w_open {                          -- @code write-ram-tables/open (snap-open: maps the fence)
  require wpc = WOpen
  if disk wl then
    mapped wl := true
    wpc := WSwap
  else
    werr := true
    wpc := WFail
}
action w_swap {                          -- @code write-layer!/swap (substitute snap l *layers*) under the lock
  require wpc = WSwap
  ram wl := false
  settled wl := false
  written wl := true
  wbelow C := false
  wpc := WIdle
}

/-! ## Replay thread: a fault reads the stack without the lock (@code snap-fault-account/view, @code snap-fault-slot/view) -/
action d_begin {
  require gpc = GIdle ∧ dpc = DIdle
  rset C := instack C
  rram C := decide $ instack C ∧ ram C
  dpc := DIn
}
action d_read (c : comp) {
  require dpc = DIn ∧ rset c
  if rram c ∧ tables c = false then bad_read := true
  if rram c = false ∧ mapped c = false then bad_read := true
}
action d_end {
  require dpc = DIn
  rset C := false
  rram C := false
  dpc := DIdle
}

/-! ## The root worker: its view, adopted at a block boundary under *stack-lock* (@planned root-worker-view!) -/
action wv_adopt {
  wvpin C := decide $ instack C ∧ ram C = false
}
action wv_read (c : comp) {              -- a bucket's compose-range over its view
  require wvpin c
  if mapped c = false then bad_wread := true
}

/-! ## The anchor line: a verified, canonical disk layer at N (RootWorker: layer, frontier, verdict) (@planned anchor-line!) -/
action anchor (z : comp) {
  require gpc = GIdle ∧ dpc = DIdle
  require instack z ∧ ram z = false ∧ isbase z = false ∧ valid z ∧ le (hi z) fin
  vfy (hi z) := true
}

/-! ## Replay thread: major compaction to a verified anchor (@code compaction-step!/major) -/
action start_major (z o : comp) {
  require gpc = GIdle ∧ dpc = DIdle
  require cpc = CNone
  require fresh o
  require instack z ∧ isbase z = false ∧ ram z = false ∧ vfy (hi z)
  require ∀ c, (instack c ∧ le (hi c) (hi z)) → ram c = false
  crd C := decide $ instack C ∧ le (hi C) (hi z)
  fresh o := false
  lo o := h0
  hi o := hi z
  isbase o := true
  ram o := false
  settled o := false
  tables o := false
  instack o := false
  if ∀ c, (instack c ∧ le (hi c) (hi z)) → valid c then
    valid o := true
  else
    valid o := false
  disk o := false
  mapped o := false
  retired o := false
  written o := false
  queued o := false
  cout := o
  cz := z
  cpc := CRead
}

/-! ## The compactor thread (@code start-compaction!/thread) -/
action c_read {                          -- @code start-compaction!/compose compose-range over the inputs
  require cpc = CRead
  if ∃ c, crd c ∧ mapped c = false then bad_read := true
  cpc := CPub
}
action c_pub {                           -- @planned start-compaction!/root the in-pass root = header at A, then publish
  require cpc = CPub
  if valid cout = false then cerr := true
  disk cout := true
  cpc := COpen
}
action c_open {                          -- @code start-compaction!/open snap-open; the thread ends
  require cpc = COpen
  if disk cout then
    mapped cout := true
    cpc := CDone
  else
    cerr := true
}

/-! ## Replay thread: the swap, at once (@code compaction-swap!) -/
action take_major {                      -- @code compaction-step!/join, then @code compaction-swap!/install
  require gpc = GIdle ∧ dpc = DIdle
  require cpc = CDone
  if ∃ c, crd c ∧ instack c = false then bad_swap := true
  retired C := decide $ retired C ∨ (instack C ∧ (isbase C ∨ le (hi C) (hi cout)))
  instack C := decide $ (instack C ∧ ¬ (isbase C ∨ le (hi C) (hi cout))) ∨ C = cout
  owner K := if le K (hi cout) then cout else owner K
  crd C := false
  cpc := CNone
}

/-! ## Replay thread: @code prune-dumps! → @code live-components → @code run-gc -/
action g_pin {                           -- @code live-components/read; @planned live-components/worker the worker's pins
  require gpc = GIdle ∧ dpc = DIdle
  pinned C := decide $ instack C ∨ (cpc ≠ CNone ∧ C = cout) ∨ wvpin C
  gpc := GDel
}
action g_delete (c : comp) {             -- @code run-gc/rm any unpinned component
  require gpc = GDel
  require disk c ∧ pinned c = false
  bad_delete := decide $ bad_delete ∨ instack c ∨ (cpc ≠ CNone ∧ c = cout) ∨ (wpc ≠ WIdle ∧ c = wl) ∨ wvpin c
  disk c := false
}
action g_done {
  require gpc = GDel
  pinned C := false
  gpc := GIdle
}

/-! ## Replay thread: @code close-retired! (waits for the worker's pin), @code collect-written! -/
action close_retired {
  require gpc = GIdle ∧ dpc = DIdle
  require wpc = WIdle ∧ cpc = CNone      -- @code close-retired!/guard
  if ∃ c, retired c ∧ (instack c ∨ crd c ∨ wbelow c) then bad_unmap := true
  mapped C := decide $ mapped C ∧ ¬ (retired C ∧ wvpin C = false)   -- @planned close-retired!/worker
  retired C := decide $ retired C ∧ wvpin C
}
action collect_written {
  require gpc = GIdle ∧ dpc = DIdle
  if ∃ c, written c ∧ ((instack c ∧ ram c) ∨ (wpc ≠ WIdle ∧ wl = c)) then bad_tables := true
  tables C := decide $ tables C ∧ written C = false
  written C := false
}

/-! ## The chain: the reorg floor advances -/
action advance_fin (x : blk) {
  require le fin x
  fin := x
}

/-! ## Replay thread: a reorg forked after B, at any depth: refused below the floor; else only
window layers drop (@code rollback-to!) -/
action rollback (b t : blk) {
  require gpc = GIdle ∧ dpc = DIdle
  require le fin b                                                    -- @planned rollback-to!/floor else refused
  require (∃ c, instack c ∧ hi c = t) ∧ le t b
  require ∀ c, (instack c ∧ le (hi c) b) → le (hi c) t
  if ∃ c, instack c ∧ ¬ le (hi c) t ∧ (ram c = false ∨ settled c) then bad_drop := true
  tables C := decide $ tables C ∧ ¬ (instack C ∧ ¬ le (hi C) t)
  ram C := decide $ ram C ∧ ¬ (instack C ∧ ¬ le (hi C) t)
  instack C := decide $ instack C ∧ le (hi C) t   -- @code rollback-to!/publish
  valid C := decide $ valid C ∧ le (hi C) b
  top := t
}

safety [stack_composes]
    (instack C ∧ instack D ∧ ¬ le K (lo C) ∧ le K (hi C) ∧ ¬ le K (lo D) ∧ le K (hi D) → C = D) ∧
    (¬ le K h0 ∧ le K top → instack (owner K) ∧ ¬ le K (lo (owner K)) ∧ le K (hi (owner K))) ∧
    (instack C → le (hi C) top) ∧
    (instack C ∧ isbase C ∧ instack D ∧ isbase D → C = D)
safety [stack_live]
    (instack C → valid C) ∧
    (instack C ∧ ram C = false → disk C ∧ mapped C)
safety [no_hazard]
    bad_unmap = false ∧ bad_delete = false ∧ bad_tables = false ∧ bad_read = false ∧
    bad_swap = false ∧ bad_wread = false ∧ bad_drop = false ∧ werr = false ∧ cerr = false

-- the inductive invariant behind the safety properties
-- allocation and shape
invariant [alloc]
    (fresh C → ¬ instack C ∧ ¬ queued C ∧ ¬ retired C ∧ ¬ written C ∧ ¬ crd C ∧ ¬ wbelow C ∧ ¬ rset C ∧ ¬ disk C ∧ ¬ mapped C ∧ ¬ ram C ∧ ¬ settled C ∧ ¬ wvpin C) ∧
    (¬ fresh wl ∧ ¬ fresh cout ∧ ¬ fresh cz ∧ ¬ fresh sl) ∧
    (isbase C → lo C = h0) ∧
    (¬ fresh C ∧ ¬ isbase C → le (lo C) (hi C) ∧ lo C ≠ hi C) ∧
    (retired C → ¬ instack C ∧ ¬ ram C)
-- the RAM layers: the window on top, then the settled layers, then the snaps; only the window above the floor
invariant [layers]
    (instack C ∧ ram C → tables C ∧ ¬ written C ∧ ¬ isbase C) ∧
    (ram C → instack C) ∧
    (settled C → ram C) ∧
    (queued C → instack C ∧ settled C ∧ ¬ written C) ∧
    (slive → instack sl ∧ settled sl ∧ ¬ queued sl ∧ ¬ (wpc ≠ WIdle ∧ wl = sl)) ∧
    (settled C ∧ ¬ (slive ∧ C = sl) → queued C ∨ (wpc ≠ WIdle ∧ wl = C)) ∧
    (instack C ∧ ram C ∧ ¬ settled C ∧ instack D ∧ (¬ ram D ∨ settled D) → le (hi D) (lo C)) ∧
    (instack C ∧ settled C ∧ instack D ∧ ¬ ram D → le (hi D) (lo C)) ∧
    (slive ∧ instack C ∧ settled C ∧ C ≠ sl → le (hi C) (lo sl)) ∧
    (instack C ∧ (¬ ram C ∨ settled C) → le (hi C) fin)
-- the writer: the oldest RAM layer, a settled one
invariant [writer]
    (wpc ≠ WIdle → instack wl ∧ ram wl ∧ settled wl ∧ ¬ queued wl) ∧
    (wpc ≠ WIdle ∧ instack C ∧ ram C ∧ C ≠ wl → le (hi wl) (lo C)) ∧
    ((wpc = WOpen ∨ wpc = WSwap) → disk wl) ∧
    (wpc = WSwap → mapped wl) ∧
    (wpc ≠ WFail) ∧
    (wbelow C → wpc ≠ WIdle ∧ mapped C ∧ (instack C ∨ retired C) ∧ ¬ ram C)
-- the compactor: every stack component up to M is an input, all of them snaps at or below the floor
invariant [compactor]
    (crd C → cpc ≠ CNone ∧ instack C ∧ ¬ ram C ∧ le (hi C) (hi cout)) ∧
    (cpc ≠ CNone → ¬ instack cout ∧ ¬ retired cout ∧ ¬ ram cout ∧ ¬ settled cout ∧ ¬ queued cout ∧ ¬ written cout ∧ ¬ crd cout ∧ ¬ wvpin cout ∧ ¬ wbelow cout ∧ ¬ rset cout ∧ isbase cout ∧ valid cout ∧ le (hi cout) fin ∧ instack cz ∧ crd cz ∧ ¬ isbase cz ∧ hi cz = hi cout) ∧
    (cpc ≠ CNone ∧ instack C ∧ le (hi C) (hi cout) → crd C) ∧
    ((cpc = COpen ∨ cpc = CDone) → disk cout) ∧
    (cpc = CDone → mapped cout)
-- GC between its pin and its deletions
invariant [gc_pins]
    (gpc = GDel → (instack C → pinned C) ∧ ((cpc ≠ CNone ∧ C = cout) → pinned C) ∧ (wvpin C → pinned C))
-- a fault walking the list it read
invariant [fault]
    (dpc = DIn ∧ rset C → (rram C → tables C) ∧ (¬ rram C → mapped C)) ∧
    (dpc = DIdle → ¬ rset C)
-- the root worker's view: snaps, kept mapped and on disk while it pins them
invariant [worker]
    (wvpin C → disk C ∧ mapped C ∧ ¬ ram C ∧ (instack C ∨ retired C))

set_option veil.smt.trust false

#gen_spec

set_option veil.violationIsError false in
#model_check { blk := Fin 3, comp := Fin 4 } { h0 := 0, c0 := 0 }

-- every action preserves the invariant (and init establishes it): each VC a lean-smt proof
-- term, added as a theorem and kernel-checked by #gen_theorems
#check_invariants
#gen_theorems
report_axioms "CompactionV2"

end CompactionV2
