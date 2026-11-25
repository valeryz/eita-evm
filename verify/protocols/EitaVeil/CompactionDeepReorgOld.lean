module

public import EitaVeil.CompactionParts

/-! # The layer stack under freezes, the writer, compaction, root checks, GC and rollback — rollback-to! and compaction-swap! as at core f1d29c6, any fork depth: violation

The shared model is `EitaVeil/CompactionParts.lean`, with rollback-to! and compaction-swap! as
at core f1d29c6 (below), no bound on the fork depth. rollback-to!'s guard
(@code snapshot-world.lisp@f1d29c6:504) covered only a RUNNING compaction (*compactor-job*);
once compaction-step! has taken a major result (@code compaction-step!/cbase) the job is NIL
and *compacting-base* / *base-check-due* wait, unguarded. A rollback below its block M then
(a) killed its root check if running (@code driver.lisp@f1d29c6:231), leaving
*compacting-base* set for good: no compaction starts (@code compaction-step!/guard) and GC
stops (@code prune-dumps!/not-compacting); or (b) when the check was still due, spawned it
later: it passes against the base's own manifest root (@code root-check-poll!/manifest-root)
and compaction-swap! installed a base of the abandoned branch under the kept layers
((member m *layers*) NIL, @code snapshot-world.lisp@f1d29c6:472).
How a caller got there: Eita's node then searched the fork within `reorg-window` of the block
being run, not of the highest block run; right after a rollback that block is just above the
fork point, so a second reorg could fork up to `reorg-window` below the first one's fork
point: below a compacted base M that the first left valid (M ≤ the horizon ≤ that fork point).
-/

veil module CompactionDeepReorgOld

set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 1000000

compaction_state
compaction_threads

action rc_pass_base_nomember {           -- @code snapshot-world.lisp@f1d29c6:472 / @code snapshot-world.lisp@f1d29c6:473 (member m *layers*) is NIL: gone = (*base*), keep = *layers*
  require gpc = GIdle ∧ dpc = DIdle
  require rpc = RExit ∧ rbase
  require ∀ d, (instack d ∧ ¬ isbase d) → hi d ≠ hi cout
  retired C := decide $ retired C ∨ (instack C ∧ isbase C)
  instack C := decide $ (instack C ∧ ¬ isbase C) ∨ C = cout
  owner K := if le K (hi cout) then cout else owner K
  cbase := false
  rcr C := false
  rbase := false
  rpc := RNone
}

compaction_gc

/-! ## Replay thread: a reorg forked after B — rollback-to! (@code snapshot-world.lisp@f1d29c6:496),
then rollback-chain! (@code driver.lisp@f1d29c6:224, @code driver.lisp@f1d29c6:228): the OLD code, no guard for a pending base -/
action rollback (b t : blk) {
  require gpc = GIdle ∧ dpc = DIdle
  require wpc = WIdle ∧ ∀ c, ¬ (instack c ∧ ram c) ∧ ¬ queued c     -- @code snapshot-world.lisp@f1d29c6:500 writer-drain!
  require cpc = CNone ∨ cpc = CDone                                   -- @code snapshot-world.lisp@f1d29c6:503 join the compactor
  require ¬ (cjob ≠ JNone ∧ ¬ le (hi cout) b)                         -- @code snapshot-world.lisp@f1d29c6:504 else error
  require ∀ c, (instack c ∧ isbase c) → le (hi c) b                   -- @code snapshot-world.lisp@f1d29c6:510 else error
  -- (no finality assumption: a fork may reach below a compacted base still being checked)
  require (∃ c, instack c ∧ hi c = t) ∧ le t b                        -- @code snapshot-world.lisp@f1d29c6:507 T (@code snapshot-world.lisp@f1d29c6:509)
  require ∀ c, (instack c ∧ le (hi c) b) → le (hi c) t
  require ∀ c, (instack c ∧ ¬ le (hi c) t) → ¬ fencing c             -- @code snapshot-world.lisp@f1d29c6:514 snap-close joins
  if ∃ c, instack c ∧ ¬ le (hi c) t ∧ ((crd c ∧ cpc ≠ CDone) ∨ wbelow c ∨ rset c) then bad_unmap := true
  if ∃ c, instack c ∧ ¬ le (hi c) t ∧ (cjob ≠ JNone ∨ cbase) ∧ c = cout then bad_delete := true
  -- @code snapshot-world.lisp@f1d29c6:515 rm -rf before rollback-chain! kills a check above T (its verdict is dropped)
  if ∃ c, instack c ∧ ¬ le (hi c) t ∧ rpc ≠ RNone ∧ rcr c ∧ le rblk t then bad_rc := true
  disk C := decide $ disk C ∧ ¬ (instack C ∧ ¬ le (hi C) t)
  mapped C := decide $ mapped C ∧ ¬ (instack C ∧ ¬ le (hi C) t)
  instack C := decide $ instack C ∧ le (hi C) t  -- @code snapshot-world.lisp@f1d29c6:512
  valid C := decide $ valid C ∧ le (hi C) b  -- blocks after B are abandoned
  -- @code driver.lisp@f1d29c6:231 a check above T is killed (@code driver.lisp@f1d29c6:232), its verdict dropped (@code driver.lisp@f1d29c6:234); *compacting-base* stays
  rcr C := decide $ rcr C ∧ (rpc = RNone ∨ le rblk t)
  rbase := decide $ rbase ∧ (rpc = RNone ∨ le rblk t)
  rpc := if le rblk t then rpc else RNone
  top := t
}

compaction_safety

#gen_spec

-- (Veil 22cbf1a's IC3 certificate cannot re-pose a transition whose `if` condition has a `¬`
-- or `≠` (`assumption` fails on `a ≠ b` against `distinctN [a, b]`): such a condition is
-- written `r x = false`, or the `if` as assignments (g_delete, rollback's kill))
set_option veil.violationIsError false in
#model_check { blk := Fin 3, comp := Fin 4 } { h0 := 0, c0 := 0 }

-- (b): the base check due behind an anchor check, a rollback below M, then the swap
sat trace [deep_reorg_swap] {
  freeze
  w_take
  w_read
  w_pub
  w_open
  w_swap
  advance_fin
  spawn_stack
  start_major
  c_read
  c_pub
  c_open
  take_major
  rollback
  spawn_base
  rc_exit
  rc_pass_base_nomember
  assert (∃ c, instack c ∧ ¬ valid c)
}

end CompactionDeepReorgOld
