module

public import Veil

/-! # The layer stack under freezes, the writer, compaction, root checks, GC and rollback:
the parts the three variants share

`Compaction` (forks bounded), `CompactionDeepReorg` (forks at any depth) and
`CompactionDeepReorgOld` (the code before the fix) are one model; this file holds what they
share, as commands each variant splices into its `veil module` (macros, hygiene off: the
names are the module's own). The variants' own files hold `rollback`, the swap without a
layer at M, the invariant's use and the checks.

Code: `src/state/snapshot-world.lisp`, `src/state/anchors.lisp`, `src/state/snapshot.lisp`
(`snap-open`/`snap-close`), `src/state/recovery.lisp` (`run-gc`), `src/chains/driver.lisp`
(`rollback-chain!`). The `@code` citations name a defun, or a step in one marked
`; @veil defun/step` on its line; `CheckCode.lean` checks them against the code.

A component `c` (sort `comp`) is a frozen RAM layer, a layer snap layer-P-N/ or a base
snap-N/: it holds the delta of blocks `lo c` < k ≤ `hi c` (a base: `h0` < k ≤ `hi c`).
The RAM layer and the snap that replaces it in `*layers*` are one component (`ram` says
which). `instack c`: in `*base*` or `*layers*`; `top`: the newest frozen block (the hot set
is above it and not modelled). `owner k` (ghost): the component that should hold block k's
delta, set by what each step means to do (the freeze of k, the compaction covering k), never
by how the code splices the list; `valid c`: c's delta is of the canonical chain (a rollback
to the fork point b invalidates every component with a block above b).

Threads: the replay thread (freeze!, the stack's lock-free reads, compaction-step!, the root
check's spawn and collection, prune-dumps!/live-components, close-retired!, collect-written!,
rollback-to!; one step at a time), the layer writer, the compactor, the `eita check-root`
process, and the resumed base's fence thread. Each action is one atomic step of one thread.
-/

open Veil

public section

-- the macros splice commands into the variant's module: its names, not fresh ones
set_option hygiene false

/-- The sorts, the state and its initial value. -/
macro "compaction_state" : command => `(
type blk
instantiate ord : TotalOrder blk
open TotalOrder
type comp

enum WPC = { WIdle, WRead, WPub, WOpen, WSwap, WFail }
enum CPC = { CNone, CRead, CPub, COpen, CDone, CFail }
enum JOB = { JNone, JMinor, JMajor }
enum RPC = { RNone, RRun, RExit }
enum GPC = { GIdle, GDel }
enum DPC = { DIdle, DIn }

immutable individual h0 : blk           -- the base's block at the start: the least block
immutable individual c0 : comp          -- that base

relation fresh : comp → Bool            -- never allocated (a fresh one per freeze / compaction)
function lo : comp → blk
function hi : comp → blk
relation isbase : comp → Bool
relation ram : comp → Bool              -- a RAM-LAYER, not yet replaced by its snap
relation tables : comp → Bool           -- (ram-layer-accts l) non-NIL
relation instack : comp → Bool
relation valid : comp → Bool
relation disk : comp → Bool             -- its directory exists
relation mapped : comp → Bool           -- an open snap (its files mmapped)
relation fencing : comp → Bool          -- snap-open :background's fence thread running
relation fbuilt : comp → Bool           -- the fence's contents written
relation fpub : comp → Bool             -- (snap-acct-fence s) published
relation retired : comp → Bool          -- in *retired*
relation written : comp → Bool          -- in *written*
relation queued : comp → Bool           -- in *writer-pipe*
function owner : blk → comp             -- ghost
individual top : blk
individual fin : blk                    -- the chain's finality: no fork after a block below it

individual wpc : WPC                    -- the writer; *writer-busy* = wpc ≠ WIdle
individual wl : comp
relation wbelow : comp → Bool           -- write-layer!'s BELOW and BASE
individual cpc : CPC                    -- the compactor; *compactor* non-NIL = cpc ≠ CNone
individual cjob : JOB                   -- *compactor-job*
individual cout : comp                  -- its output (and *compacting-base*)
individual ca : comp                    -- ghost: the run's oldest layer (minor)
individual cz : comp                    -- ghost: the run's newest layer, the layer at M
relation crd : comp → Bool              -- the job's inputs (run, and base for :major)
individual cbase : Bool                 -- *compacting-base* non-NIL
individual due : Bool                   -- *base-check-due*
individual rpc : RPC                    -- *pending-root* non-NIL = rpc ≠ RNone
individual rbase : Bool                 -- its kind is :base
individual rblk : blk
relation rcr : comp → Bool              -- its composition (the dirs the checker reads)
individual gpc : GPC                    -- prune-dumps!: live-components then run-gc
relation pinned : comp → Bool
individual dpc : DPC                    -- a fault walking the stack (view-account &c.)
relation rset : comp → Bool             -- the *layers*/*base* it read
relation rram : comp → Bool             -- ... and which of them were RAM layers then

individual bad_unmap : Bool             -- snap-close of a component a thread may read
individual bad_delete : Bool            -- GC/rollback removed the dir of a live component
individual bad_rc : Bool                -- a dir deleted under a root check whose verdict counts
individual bad_tables : Bool            -- a RAM layer's tables dropped while reachable
individual bad_read : Bool              -- a read of an unmapped snap / a cut RAM layer
individual bad_fence : Bool             -- a lookup through a fence not yet built
individual bad_swap : Bool              -- a compaction's run no longer in the stack at its swap
individual werr : Bool                  -- *writer-error* (rename/open: No such file)
individual cerr : Bool                  -- *compactor-error*

#gen_state

assumption [h0_least] ∀ b, le h0 b

after_init {
  fresh C := C ≠ c0
  lo C := h0
  hi C := h0
  isbase C := C = c0
  ram C := false
  tables C := false
  instack C := C = c0
  valid C := true
  disk C := C = c0
  mapped C := C = c0
  fencing C := C = c0     -- resume-stack! → open-composition: snap-open :fence :background
  fbuilt C := false
  fpub C := false
  retired C := false
  written C := false
  queued C := false
  owner K := c0
  top := h0
  fin := h0
  wpc := WIdle
  wl := c0
  wbelow C := false
  cpc := CNone
  cjob := JNone
  cout := c0
  ca := c0
  cz := c0
  crd C := false
  cbase := false
  due := false
  rpc := RNone
  rbase := false
  rblk := h0
  rcr C := false
  gpc := GIdle
  pinned C := false
  dpc := DIdle
  rset C := false
  rram C := false
  bad_unmap := false
  bad_delete := false
  bad_rc := false
  bad_tables := false
  bad_read := false
  bad_fence := false
  bad_swap := false
  werr := false
  cerr := false
})

/-- Every thread's steps up to a passed `:base` check with a layer at M in the stack. -/
macro "compaction_threads" : command => `(
/-! ## Replay thread: @code freeze! -/
action freeze (l : comp) (n : blk) {
  require gpc = GIdle ∧ dpc = DIdle
  require fresh l
  require le top n ∧ top ≠ n
  fresh l := false                        -- @code freeze!/make make-ram-layer :parent (stack-top-block)
  lo l := top
  hi l := n
  isbase l := false
  ram l := true
  tables l := true
  valid l := true
  disk l := false
  mapped l := false
  fencing l := false
  fbuilt l := false
  fpub l := false
  retired l := false
  written l := false
  instack l := true                      -- @code freeze!/push (cons l *layers*) under *stack-lock*
  queued l := true                       -- @code freeze!/pipe pipe-put
  owner K := if le K n ∧ ¬ le K top then l else owner K
  top := n
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
action w_read {                          -- @code write-layer!/write → @code write-ram-tables: its tables, BELOW's snaps
  require wpc = WRead
  if tables wl = false then bad_tables := true
  if ∃ c, wbelow c ∧ ¬ mapped c then bad_read := true
  wpc := WPub
}
action w_pub {                           -- @code write-ram-tables/publish → @code snap-publish
  require wpc = WPub
  disk wl := true
  wpc := WOpen
}
action w_open {                          -- @code write-ram-tables/open (snap-open final)
  require wpc = WOpen
  if disk wl then
    mapped wl := true
    wpc := WSwap
  else
    werr := true
    wpc := WFail
}
action w_swap {                          -- @code write-layer!/swap (substitute snap l *layers*) under the lock; *written*
  require wpc = WSwap
  ram wl := false
  written wl := true
  wbelow C := false
  wpc := WIdle
}

/-! ## Replay thread: a fault reads the stack without the lock (@code snap-fault-account/view,
@code snap-fault-account/code, @code snap-fault-slot/view, @code snap-cold-storage-map/view) -/
action d_begin {
  require gpc = GIdle ∧ dpc = DIdle
  rset C := instack C
  rram C := decide $ instack C ∧ ram C
  dpc := DIn
}
action d_read (c : comp) {               -- eita.state.snapshot::view-* over the list it read
  require dpc = DIn ∧ rset c
  if rram c ∧ tables c = false then bad_read := true
  if rram c = false ∧ mapped c = false then bad_read := true
  if rram c = false ∧ fpub c ∧ fbuilt c = false then bad_fence := true
}
action d_end {
  require dpc = DIn
  rset C := false
  rram C := false
  dpc := DIdle
}

/-! ## The resumed base's fence thread: @code snap-open/background → @code snap-open/fences -/
action f_build (c : comp) {              -- @code snap-open/build build-fence over the mappings
  require fencing c ∧ ¬ fbuilt c
  if mapped c = false then bad_read := true
  fbuilt c := true
}
action f_pub (c : comp) {                -- @code snap-open/publish barrier, then the pointer; the thread ends
  require fencing c ∧ fbuilt c
  fpub c := true
  fencing c := false
}

/-! ## Replay thread: @code compaction-step! starts a job (→ @code start-compaction!) -/
action start_minor (a z o : comp) {      -- @code compaction-step!/minor (run: @code compaction-step!/minor-run, oldest disk layers ≤ horizon)
  require gpc = GIdle ∧ dpc = DIdle
  require cpc = CNone ∧ ¬ cbase          -- @code compaction-step!/guard
  require fresh o
  require instack a ∧ instack z ∧ ¬ isbase a ∧ ¬ isbase z ∧ le (hi a) (hi z)
  require le (hi z) fin                  -- @code compaction-step!/horizon horizon = n - (reorg-window)
  require ∀ c, (instack c ∧ ¬ le (hi c) (lo a) ∧ le (hi c) (hi z)) → ¬ ram c   -- @code compaction-step!/disk disk layers
  crd C := decide $ instack C ∧ ¬ le (hi C) (lo a) ∧ le (hi C) (hi z)
  fresh o := false
  lo o := lo a
  hi o := hi z
  isbase o := false
  ram o := false
  tables o := false
  instack o := false
  if ∀ c, (instack c ∧ ¬ le (hi c) (lo a) ∧ le (hi c) (hi z)) → valid c then
    valid o := true
  else
    valid o := false
  disk o := false
  mapped o := false
  fencing o := false
  fbuilt o := false
  fpub o := false
  retired o := false
  written o := false
  queued o := false
  cout := o
  ca := a
  cz := z
  cjob := JMinor                         -- @code start-compaction!/job *compactor-job*
  cpc := CRead
}
action start_major (z o : comp) {        -- @code compaction-step!/major (run: @code compaction-step!/major-run, every disk layer up to the horizon)
  require gpc = GIdle ∧ dpc = DIdle
  require cpc = CNone ∧ ¬ cbase          -- @code compaction-step!/guard
  require fresh o
  require instack z ∧ ¬ isbase z ∧ ¬ ram z
  require le (hi z) fin                  -- @code compaction-step!/major-run horizon
  require ∀ c, (instack c ∧ le (hi c) (hi z)) → ¬ ram c
  crd C := decide $ instack C ∧ le (hi C) (hi z)  -- the run and @code start-compaction!/base base
  fresh o := false
  lo o := h0
  hi o := hi z
  isbase o := true
  ram o := false
  tables o := false
  instack o := false
  if ∀ c, (instack c ∧ le (hi c) (hi z)) → valid c then
    valid o := true
  else
    valid o := false
  disk o := false
  mapped o := false
  fencing o := false
  fbuilt o := false
  fpub o := false
  retired o := false
  written o := false
  queued o := false
  cout := o
  cz := z
  cjob := JMajor
  cpc := CRead
}

/-! ## The compactor thread (@code start-compaction!/thread) -/
action c_read {                          -- @code start-compaction!/compose write-composed over the run (and base)
  require cpc = CRead
  if ∃ c, crd c ∧ ¬ mapped c then bad_read := true
  cpc := CPub
}
action c_pub {                           -- @code start-compaction!/publish snap-publish
  require cpc = CPub
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
    cpc := CFail
}

/-! ## Replay thread: compaction-step! takes the result (@code compaction-step!/take) -/
action take_minor {                      -- @code compaction-step!/splice the splice under the lock, then @code compaction-step!/retire
  require gpc = GIdle ∧ dpc = DIdle
  require cpc = CDone ∧ cjob = JMinor    -- @code compaction-step!/join joined; *compactor-job* NIL
  if ∃ c, crd c ∧ ¬ instack c then bad_swap := true
  instack C := decide $ (instack C ∧ ¬ crd C) ∨ C = cout
  retired C := decide $ retired C ∨ crd C
  owner K := if ¬ le K (lo cout) ∧ le K (hi cout) then cout else owner K
  crd C := false
  cjob := JNone
  cpc := CNone
}
action take_major {                      -- @code compaction-step!/cbase *compacting-base*; @code root-check-poll!/compact spawn it
  require gpc = GIdle ∧ dpc = DIdle
  require cpc = CDone ∧ cjob = JMajor
  crd C := false
  cjob := JNone
  cpc := CNone
  cbase := true
  if rpc = RNone then
    rbase := true
    rblk := hi cout
    rcr C := C = cout
    rpc := RRun
  else
    due := true
}

/-! ## Root checks: @code spawn-root-check! from @code root-check-poll!/idle -/
action spawn_base {                      -- @code root-check-poll!/base-due a compacted base waiting (*base-check-due*)
  require gpc = GIdle ∧ dpc = DIdle
  require rpc = RNone ∧ due
  due := false
  rbase := true
  rblk := hi cout
  rcr C := C = cout
  rpc := RRun
}
action spawn_stack (a : blk) {           -- @code root-check-poll!/anchor an anchor: @code root-check-poll!/compose (@code stack-composition a), @code root-check-poll!/spawn-stack
  require gpc = GIdle ∧ dpc = DIdle
  require rpc = RNone ∧ ¬ due
  require ∃ c, instack c ∧ hi c = a
  require ∀ c, (instack c ∧ le (hi c) a) → ¬ ram c
  rbase := false
  rblk := a
  rcr C := decide $ instack C ∧ le (hi C) a
  rpc := RRun
}
action rc_exit {                         -- the `eita check-root` process exits
  require rpc = RRun
  rpc := RExit
}
-- @code root-check-finish!, a computed root that matches. A :stack check of a
-- component off the canonical chain mismatches (@code root-check-finish!/mismatch, the run stops): not a pass.
-- A :base check compares with the compacted base's own manifest root (@code root-check-poll!/manifest-root): it passes.
action rc_pass_stack {
  require gpc = GIdle ∧ dpc = DIdle
  require rpc = RExit ∧ ¬ rbase
  require ∀ c, rcr c → valid c
  rcr C := false
  rpc := RNone
}
-- @code root-check-finish!/swap → @code compaction-swap!: gone = *base* + (member m *layers*)
action rc_pass_base_member {             -- a layer at M is in the stack
  require gpc = GIdle ∧ dpc = DIdle
  require rpc = RExit ∧ rbase
  require ∃ d, instack d ∧ ¬ isbase d ∧ hi d = hi cout
  retired C := decide $ retired C ∨ (instack C ∧ (isbase C ∨ le (hi C) (hi cout)))  -- @code compaction-swap!/gone, @code compaction-swap!/retire
  instack C := decide $ (instack C ∧ ¬ (isbase C ∨ le (hi C) (hi cout))) ∨ C = cout  -- @code compaction-swap!/keep, @code compaction-swap!/install
  owner K := if le K (hi cout) then cout else owner K
  cbase := false                         -- @code compaction-swap!/done
  rcr C := false
  rbase := false
  rpc := RNone
})

/-- The fixed `compaction-swap!` without a layer at M: refused, the base discarded. -/
macro "compaction_swap_refused" : command => `(
action rc_pass_base_nomember {           -- @code compaction-swap!/refuse no layer at M in the stack: REFUSED, discarded (@code compaction-swap!/discard → @code discard-compacting-base!/close, @code discard-compacting-base!/rm)
  require gpc = GIdle ∧ dpc = DIdle
  require rpc = RExit ∧ rbase
  require ∀ d, (instack d ∧ ¬ isbase d) → hi d ≠ hi cout
  require ¬ fencing cout                 -- snap-close joins the fence thread (@code snap-close/join)
  if instack cout ∨ crd cout then bad_unmap := true
  mapped cout := false
  disk cout := false
  cbase := false
  due := false
  rcr C := false
  rbase := false
  rpc := RNone
})

/-- Root checks that could not run, GC, close-retired!, collect-written!, finality. -/
macro "compaction_gc" : command => `(
action rc_norun_stack {                  -- @code root-check-finish!/norun could NOT RUN (no anchors line)
  require gpc = GIdle ∧ dpc = DIdle
  require rpc = RExit ∧ ¬ rbase
  rcr C := false
  rpc := RNone
}
action rc_norun_base {                   -- @code root-check-finish!/norun-base a :base one closes *compacting-base*
  require gpc = GIdle ∧ dpc = DIdle
  require rpc = RExit ∧ rbase
  require ¬ fencing cout                 -- snap-close joins the fence thread (@code snap-close/join)
  if instack cout ∨ crd cout then bad_unmap := true
  mapped cout := false
  cbase := false
  rcr C := false
  rbase := false
  rpc := RNone
}

/-! ## Replay thread: @code prune-dumps! → @code live-components → @code run-gc -/
action g_pin {                           -- @code prune-dumps!/not-compacting not while *compacting-base*; @code live-components/read
  require gpc = GIdle ∧ dpc = DIdle
  require ¬ cbase
  pinned C := decide $ instack C ∨ (rpc ≠ RNone ∧ rcr C) ∨ (cjob ≠ JNone ∧ C = cout)  -- the stack, @code live-components/pending, @code live-components/job
  gpc := GDel
}
action g_delete (c : comp) {             -- @code run-gc/scan, @code run-gc/victims: rm -rf (@code run-gc/rm) any unpinned component
  require gpc = GDel
  require disk c ∧ ¬ pinned c
  bad_delete := decide $ bad_delete ∨ instack c ∨ ((cjob ≠ JNone ∨ cbase) ∧ c = cout) ∨ (wpc ≠ WIdle ∧ c = wl)
  bad_rc := decide $ bad_rc ∨ (rpc ≠ RNone ∧ rcr c)
  disk c := false
}
action g_done {
  require gpc = GDel
  pinned C := false
  gpc := GIdle
}

/-! ## Replay thread: @code close-retired!, @code collect-written! -/
action close_retired {
  require gpc = GIdle ∧ dpc = DIdle
  require wpc = WIdle ∧ cpc = CNone      -- @code close-retired!/guard (not *writer-busy*) (null *compactor*)
  require ∀ c, retired c → ¬ fencing c   -- @code close-retired!/close snap-close joins the fence thread (@code snap-close/join)
  if ∃ c, retired c ∧ (instack c ∨ crd c ∨ wbelow c) then bad_unmap := true
  mapped C := decide $ mapped C ∧ ¬ retired C
  retired C := false
}
action collect_written {                 -- @code collect-written!/take (shiftf *written*) under the lock; @code collect-written!/cut cut the tables
  require gpc = GIdle ∧ dpc = DIdle
  if ∃ c, written c ∧ ((instack c ∧ ram c) ∨ (wpc ≠ WIdle ∧ wl = c)) then bad_tables := true
  tables C := decide $ tables C ∧ ¬ written C
  written C := false
}

/-! ## The chain: finality advances (@code reorg-window/depth) -/
action advance_fin (x : blk) {
  require le fin x
  fin := x
}
)

/-- The fixed `rollback-to!`; `window` bounds the fork point (`True`: any depth). -/
macro "compaction_rollback" window:term : command => `(
/-! ## Replay thread: a reorg forked after B — @code rollback-to!, called by @code rollback-chain!/rollback
(which resumes at T+1, @code rollback-chain!/resume) -/
action rollback (b t : blk) {
  require gpc = GIdle ∧ dpc = DIdle
  require wpc = WIdle ∧ ∀ c, ¬ (instack c ∧ ram c) ∧ ¬ queued c     -- @code rollback-to!/drain writer-drain!
  require cpc = CNone ∨ cpc = CDone                                   -- @code rollback-to!/join join the compactor
  require ¬ (cjob ≠ JNone ∧ ¬ le (hi cout) b)                         -- @code rollback-to!/job-guard else error
  require ∀ c, (instack c ∧ isbase c) → le (hi c) b                   -- @code rollback-to!/base-guard else error
  require $window                                                     -- the fork bound: the variant's
  require (∃ c, instack c ∧ hi c = t) ∧ le t b                        -- @code rollback-to!/keep T (@code rollback-to!/top)
  require ∀ c, (instack c ∧ le (hi c) b) → le (hi c) t
  require ∀ c, (instack c ∧ ¬ le (hi c) t) → ¬ fencing c             -- @code rollback-to!/close snap-close joins
  if ∃ c, instack c ∧ ¬ le (hi c) t ∧ ((crd c ∧ cpc ≠ CDone) ∨ wbelow c ∨ rset c) then bad_unmap := true
  if ∃ c, instack c ∧ ¬ le (hi c) t ∧ (cjob ≠ JNone ∨ cbase) ∧ c = cout then bad_delete := true
  -- @code rollback-to!/kill @code kill-root-check!: a check above T is killed first, its
  -- verdict dropped (a :base one of a pending base above T among them: its block is M)
  rcr C := decide $ rcr C ∧ (rpc = RNone ∨ le rblk t)
  rbase := decide $ rbase ∧ (rpc = RNone ∨ le rblk t)
  rpc := if le rblk t then rpc else RNone
  -- @code rollback-to!/discard @code discard-compacting-base!: a pending base above T is closed, deleted
  -- and forgotten (@code discard-compacting-base!/forget) with its due check (@code discard-compacting-base!/due);
  -- at or below T it stays (its layer at M is kept)
  if cbase ∧ ¬ le (hi cout) t ∧ ((rpc ≠ RNone ∧ rcr cout) ∨ fencing cout ∨ crd cout ∨ rset cout) then bad_unmap := true
  disk C := decide $ disk C ∧ ¬ (cbase ∧ C = cout ∧ ¬ le (hi cout) t)
  mapped C := decide $ mapped C ∧ ¬ (cbase ∧ C = cout ∧ ¬ le (hi cout) t)
  due := decide $ due ∧ le (hi cout) t
  cbase := decide $ cbase ∧ le (hi cout) t
  -- @code rollback-to!/publish the kept stack; @code rollback-to!/rm rm -rf of the dropped layers (a check still running is at or below T)
  if ∃ c, instack c ∧ ¬ le (hi c) t ∧ rpc ≠ RNone ∧ rcr c then bad_rc := true
  disk C := decide $ disk C ∧ ¬ (instack C ∧ ¬ le (hi C) t)
  mapped C := decide $ mapped C ∧ ¬ (instack C ∧ ¬ le (hi C) t)
  instack C := decide $ instack C ∧ le (hi C) t  -- @code rollback-to!/publish
  valid C := decide $ valid C ∧ le (hi C) b  -- blocks after B are abandoned
  top := t
}
)

/-- The safety properties. -/
macro "compaction_safety" : command => `(
-- the stack composes to the replay's committed state: every block up to the newest freeze in
-- exactly one component, that block's owner (stack_owner), nothing above it, one base
safety [stack_composes]
    (instack C ∧ instack D ∧ ¬ le K (lo C) ∧ le K (hi C) ∧ ¬ le K (lo D) ∧ le K (hi D) → C = D) ∧
    (¬ le K h0 ∧ le K top → instack (owner K) ∧ ¬ le K (lo (owner K)) ∧ le K (hi (owner K))) ∧
    (instack C → le (hi C) top) ∧
    (instack C ∧ isbase C ∧ instack D ∧ isbase D → C = D)
-- only canonical-chain deltas; every snap in the stack on disk and mapped
safety [stack_live]
    (instack C → valid C) ∧
    (instack C ∧ ¬ ram C → disk C ∧ mapped C)
-- no thread unmaps, deletes, cuts or reads what another still uses; no rename/open failure
safety [no_hazard]
    bad_unmap = false ∧ bad_delete = false ∧ bad_rc = false ∧ bad_tables = false ∧ bad_read = false ∧
    bad_fence = false ∧ bad_swap = false ∧ werr = false ∧ cerr = false)

/-- The inductive invariant behind the safety properties (the fixed variants). -/
macro "compaction_invariant" : command => `(
-- the inductive invariant behind the safety properties
-- allocation and shape (unused_idle, ptrs_used, base_lo, layer_span, retired_out)
invariant [alloc]
    (fresh C → ¬ instack C ∧ ¬ queued C ∧ ¬ retired C ∧ ¬ written C ∧ ¬ crd C ∧ ¬ rcr C ∧ ¬ wbelow C ∧ ¬ rset C ∧ ¬ fencing C ∧ ¬ disk C ∧ ¬ mapped C ∧ ¬ ram C) ∧
    (¬ fresh wl ∧ ¬ fresh cout ∧ ¬ fresh ca ∧ ¬ fresh cz) ∧
    (isbase C → lo C = h0) ∧
    (¬ fresh C ∧ ¬ isbase C → le (lo C) (hi C) ∧ lo C ≠ hi C) ∧
    (retired C → ¬ instack C ∧ ¬ ram C)
-- the writer: RAM layers are the newest, written oldest first (queued_ram, ram_writer, ram_instack, ram_newest, wl_active, wl_oldest, wl_disk, wl_mapped, no_wfail, wbelow_live)
invariant [writer]
    (queued C → instack C ∧ ram C ∧ ¬ written C) ∧
    (instack C ∧ ram C → tables C ∧ ¬ written C ∧ ¬ isbase C ∧ (queued C ∨ (wpc ≠ WIdle ∧ wl = C))) ∧
    (ram C → instack C) ∧
    (instack C ∧ ram C ∧ instack D ∧ ¬ ram D → le (hi D) (lo C)) ∧
    (wpc ≠ WIdle → instack wl ∧ ram wl ∧ ¬ queued wl) ∧
    (wpc ≠ WIdle ∧ instack C ∧ ram C ∧ C ≠ wl → le (hi wl) (lo C)) ∧
    ((wpc = WOpen ∨ wpc = WSwap) → disk wl) ∧
    (wpc = WSwap → mapped wl) ∧
    (wpc ≠ WFail) ∧
    (wbelow C → wpc ≠ WIdle ∧ mapped C ∧ (instack C ∨ retired C) ∧ ¬ ram C)
-- the compactor (job_pc, no_cfail, crd_job, cout_job, cout_disk, cout_mapped, minor_job, minor_run, minor_crd, major_job, cbase_cout)
invariant [compactor]
    (cjob = JNone ↔ cpc = CNone) ∧
    (cpc ≠ CFail) ∧
    (crd C → cjob ≠ JNone ∧ instack C ∧ ¬ ram C ∧ le (hi C) (hi cout)) ∧
    (cjob ≠ JNone → ¬ instack cout ∧ ¬ retired cout ∧ ¬ ram cout ∧ ¬ queued cout ∧ ¬ written cout ∧ ¬ crd cout ∧ ¬ fencing cout ∧ valid cout ∧ le (hi cout) fin ∧ instack cz ∧ crd cz ∧ ¬ isbase cz ∧ hi cz = hi cout) ∧
    ((cpc = COpen ∨ cpc = CDone) → disk cout) ∧
    (cpc = CDone → mapped cout) ∧
    (cjob = JMinor → crd ca ∧ lo ca = lo cout ∧ ¬ isbase ca ∧ ¬ isbase cout) ∧
    (cjob = JMinor ∧ instack C ∧ ¬ le (hi C) (lo cout) ∧ le (hi C) (hi cout) → crd C) ∧
    (cjob = JMinor ∧ crd C → ¬ le (hi C) (lo cout)) ∧
    (cjob = JMajor → isbase cout) ∧
    (cbase → cjob = JNone ∧ isbase cout ∧ ¬ instack cout ∧ ¬ retired cout ∧ ¬ ram cout ∧ ¬ queued cout ∧ ¬ written cout ∧ ¬ fencing cout ∧ disk cout ∧ mapped cout ∧ valid cout ∧ le (hi cout) fin ∧ instack cz ∧ ¬ isbase cz ∧ ¬ ram cz ∧ hi cz = hi cout)
-- root checks (rc_none, rc_stack, rc_stack_not_cout, rc_base, due_cbase)
invariant [root_check]
    (rpc = RNone → ¬ rcr C) ∧
    (rpc ≠ RNone ∧ ¬ rbase ∧ rcr C → le (hi C) rblk) ∧
    (rpc ≠ RNone ∧ ¬ rbase ∧ (cjob ≠ JNone ∨ cbase) → ¬ rcr cout) ∧
    (rpc ≠ RNone ∧ rbase → cbase ∧ ¬ due ∧ rblk = hi cout ∧ (rcr C → C = cout)) ∧
    (due → cbase ∧ ¬ (rpc ≠ RNone ∧ rbase))
-- GC between its pin and its deletions (the replay thread is in run-gc) (gdel_pins)
invariant [gc_pins]
    (gpc = GDel → ¬ cbase ∧ (instack C → pinned C) ∧ ((rpc ≠ RNone ∧ rcr C) → pinned C) ∧ ((cjob ≠ JNone ∧ C = cout) → pinned C))
-- a fault walking the list it read (reader, reader_idle)
invariant [fault]
    (dpc = DIn ∧ rset C → (rram C → tables C) ∧ (¬ rram C → mapped C)) ∧
    (dpc = DIdle → ¬ rset C)
-- the fence thread (fence_order, fencing_mapped)
invariant [fence]
    (fpub C → fbuilt C) ∧
    (fencing C → mapped C)
)

/-- Every theorem `#gen_theorems` added to module `m`, and the axioms they rest on (expected:
propext, Classical.choice, Quot.sound; `sorryAx` would mean a VC was trusted, not proved). -/
macro "report_axioms" m:str : command => `(
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let thms := env.constants.map₂.toList.filterMap fun (n, ci) =>
    if (Name.mkSimple $m).isPrefixOf n && ci matches .thmInfo _ then some n else none
  let mut ax : Array Name := #[]
  for n in thms do
    for a in (← liftCoreM (Lean.collectAxioms n)) do
      unless ax.contains a do ax := ax.push a
  logInfo m!"{thms.length} theorems; axioms: {ax}"
)

end
