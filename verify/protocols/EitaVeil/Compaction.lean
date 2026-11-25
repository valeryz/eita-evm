module

public import EitaVeil.CompactionParts

/-! # The layer stack under freezes, the writer, compaction, root checks, GC and rollback — forks within reorg-window of the highest block run (core 674e575): safe

The shared model is `EitaVeil/CompactionParts.lean`. Here `rollback` keeps the fork point at
or above `fin`, a block once `reorg-window` (@code reorg-window) behind the replay: every
compaction stays at or below it (@code compaction-step!/horizon). That bound is the caller's:
whoever calls `rollback-chain!` (core's driver does not choose fork points) never forks below
`reorg-window` under the highest block it has run. Eita's node bounds its `reorg!` this way
(its `reorg-fork-floor`, checked by the node's code check). Safety does not depend on it:
CompactionDeepReorg proves the same properties for forks at any depth.
-/

veil module Compaction

set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 1000000

compaction_state
compaction_threads
compaction_swap_refused
compaction_gc
compaction_rollback (le fin b)     -- no fork below fin (the caller's bound)
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
-- kernel-checked by #gen_theorems. Not `#updr certify`: its search finds the invariant
-- inductive at frame 1 (243 s, 30 solver calls), but the certificate's kernel term outgrows
-- a 64 GB machine (> 35 GB, > 15 min), see README.
#check_invariants
#gen_theorems
report_axioms "Compaction"

end Compaction
