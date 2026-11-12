module

public import EitaVeil.CompactionParts

/-! # The layer stack under freezes, the writer, compaction, root checks, GC and rollback — a fork at any depth, below a compacted base waiting for its check (core 674e575): safe

The shared model is `EitaVeil/CompactionParts.lean`, with no bound on the fork depth: a fork
may reach below a compacted base whose root check is due or running (Eita's node once
measured `reorg-window` from the block being run, and two reorgs in a row added up).
rollback-to! kills a root check above its T (@code rollback-to!/kill) and discards a pending
base above T (@code rollback-to!/discard, @code discard-compacting-base!): its check never
passes later, compaction (@code compaction-step!/guard) and GC (@code prune-dumps!/not-compacting)
resume; compaction-swap! refuses a base with no layer at M (@code compaction-swap!/refuse).
A running compaction is still refused below its run (@code rollback-to!/job-guard).
CompactionDeepReorgOld is the code before the fix.
-/

veil module CompactionDeepReorg

set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 1000000

compaction_state
compaction_threads
compaction_swap_refused
compaction_gc
compaction_rollback True           -- no finality assumption: a fork may reach below a compacted base still being checked
compaction_safety
compaction_invariant

-- #check_invariants reconstructs lean-smt proofs instead of trusting cvc5's unsat (read when
-- the spec is generated: set here, not at the command)
set_option veil.smt.trust false

#gen_spec

-- (Veil 22cbf1a's IC3 certificate cannot re-pose a transition whose `if` condition has a `¬`
-- or `≠` (`assumption` fails on `a ≠ b` against `distinctN [a, b]`): such a condition is
-- written `r x = false`, or the `if` as assignments (g_delete, rollback's kill))
set_option veil.violationIsError false in
#model_check { blk := Fin 3, comp := Fin 4 } { h0 := 0, c0 := 0 }

-- every action preserves the invariant (and init establishes it): each VC proved by a
-- lean-smt proof term (veil.smt.trust false, no trusted cvc5), added as a theorem and
-- kernel-checked by #gen_theorems (see Compaction for why not `#updr certify`)
#check_invariants
#gen_theorems
report_axioms "CompactionDeepReorg"

-- the old violation's prefix is reachable: a rollback below a pending base, which it discards
-- (the fixed rollback's encoding needs more than the default 200000 heartbeats)
set_option maxHeartbeats 4000000
sat trace [deep_reorg_discards] {
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
  assert (cbase = false ∧ due = false ∧ ∀ c, instack c → valid c)
}
-- (the swap that followed it: no `unsat trace` — its encoding exceeds simp's step limit; the
-- inductive invariant above already excludes it: cbase → a layer at M is in the stack)

end CompactionDeepReorg
