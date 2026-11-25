module

public import EitaVeil.LayerGc

/-! # State GC vs the layer writer — FIXED live-components: one locked read (core 28a9f4f)

`live-components` reads `*base*` and `*layers*` once, under `*stack-lock*`, and pins both the
RAM layers and the snaps of that one read: atomic with respect to the writer's swap (also
under the lock). Safe: an inductive invariant and an IC3 certificate. The shared state,
writer and GC are in `EitaVeil/LayerGc.lean`.
-/

veil module LayerGcFixed

layer_gc_writer
layer_gc_start GPin1

action g_pin {                    -- @code live-components/read (the one read of *layers*, under *stack-lock*)
  require gpc = GPin1
  pinned L := pinned L ∨ ram L ∨ snap L   -- @code live-components/ram the RAM layers and @code live-components/snaps the snaps, of that one read
  gpc := GDel
}

layer_gc_delete

-- the inductive invariant behind the three safety properties
invariant [queued_in_ram] (wpc L = WQueued ∨ wpc L = WWriting ∨ wpc L = WProbedYes ∨ wpc L = WProbedNo ∨ wpc L = WRenamed ∨ wpc L = WOpened) → ram L ∧ ¬ snap L
invariant [none_out] wpc L = WNone → ¬ ram L ∧ ¬ snap L
invariant [done_snap] wpc L = WDone → snap L ∧ ¬ ram L
invariant [never_failed] wpc L ≠ WFailed
invariant [probed_yes_disk] wpc L = WProbedYes → disk L
invariant [probed_no_gone] wpc L = WProbedNo → ¬ disk L
invariant [published_disk] (wpc L = WRenamed ∨ wpc L = WOpened) → disk L
invariant [pindel] gpc = GDel → (ram L ∨ snap L) → pinned L

-- #check_invariants reconstructs lean-smt proofs instead of trusting cvc5's unsat
set_option veil.smt.trust false

#gen_spec

set_option veil.violationIsError false in
#model_check { layer := Fin 2 } { }

#check_invariants

set_option veil.synthesizer.timings true in
#updr certify
#gen_theorems
#print axioms ic3_safe
#check @ic3_safe

end LayerGcFixed
