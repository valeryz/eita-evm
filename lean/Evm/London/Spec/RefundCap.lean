/-
  Evm.London.Spec.RefundCap — EIP-3529 refund-cap reduction.

  EELS reference: `forks/london/fork.py` `process_transaction`. The
  end-of-tx refund computation changes from

    refund = min(refund_counter, gas_used // 2)     # Frontier..Berlin

  to

    refund = min(refund_counter, gas_used // 5)     # London+

  EIP-3529 also drops the SSTORE-clear refund from 15000 to 4800,
  and removes the SELFDESTRUCT refund entirely. The 4800 / 0 changes
  are tracked in `London/Spec/StorageStep.lean` (TODO; not in this
  drop) and `London/Spec/Selfdestruct.lean` respectively. This file
  is just the cap.

  ## What's encoded vs glossed

  * Encoded: the formula `min(counter, gasUsed / 5)`.
  * Encoded: the cap divisor itself (5 vs Berlin's 2) as a
    parametric `refundCapDivisor`.
  * Glossed: the surrounding `processTransaction` plumbing — where
    `gasUsed` comes from, how `refund_counter` is accumulated, how
    `gas_used - refund` is multiplied by effective gas price to
    determine the refund wei. All those pieces are in
    `London/Spec/FeeMarket.lean` / the inherited Byzantium
    processTransaction.
-/

import Evm.Forks

namespace Evm.London.Spec

/-- EIP-3529 max-refund denominator. Frontier through Berlin used
    `2`; London drops to `5`. -/
def refundCapDivisor : Nat := 5

/-- The pre-London (Frontier..Berlin) max-refund denominator, kept
    here as a named constant so the forward / reverse fork conditions
    can be stated. The implementations live as literal `/ 2` in
    `Frontier.Fork`, `Byzantium.Fork`, `Berlin.Fork`. -/
def preLondonRefundCapDivisor : Nat := 2

/-- `IsRefundCapped gasUsed refundCounter refund` — the
    end-of-transaction refund computation. EELS:
    `refund = min(refund_counter, gas_used // 5)`. -/
def IsRefundCapped (gasUsed refundCounter refund : Nat) : Prop :=
  refund = min refundCounter (gasUsed / refundCapDivisor)

/-! ## Fork-conditional value (iff form)

    The EIP-3529 divisor change is the *only* fork-conditional
    behavioural delta on the refund cap. We state it as a single
    iff:

      `divisorAt f = 5  ↔  f ≥ London`

    Anything else (the actual divisor at a non-London fork is 2;
    the numbers themselves; monotonicity of `gasUsed/d`) is a
    consequence of this one biconditional, so we don't restate. -/

/-- The fork-parametric refund-cap divisor. -/
def divisorAt (f : Evm.Fork) : Nat :=
  if f.atLeast .london then refundCapDivisor else preLondonRefundCapDivisor

/-- EIP-3529 activation: divisor is the post-London value iff the
    fork is London or later. -/
theorem divisor_iff_london (f : Evm.Fork) :
    divisorAt f = refundCapDivisor ↔ f.atLeast .london := by
  unfold divisorAt
  split <;> simp_all <;> decide

/-! ## Properties -/

/-- The capped refund never exceeds the counter. -/
theorem refund_le_counter
    (gasUsed refundCounter refund : Nat)
    (h : IsRefundCapped gasUsed refundCounter refund) :
    refund ≤ refundCounter := by
  rw [h]
  exact Nat.min_le_left _ _

/-- The capped refund never exceeds `gasUsed / 5`. -/
theorem refund_le_one_fifth
    (gasUsed refundCounter refund : Nat)
    (h : IsRefundCapped gasUsed refundCounter refund) :
    refund ≤ gasUsed / refundCapDivisor := by
  rw [h]
  exact Nat.min_le_right _ _

/-- Equivalent statement of the cap as an upper bound on the refund's
    contribution to the *gas effectively used* by the tx. After
    refund, `gasUsed' = gasUsed - refund ≥ gasUsed * 4/5`. -/
theorem effective_gas_used_lower_bound
    (gasUsed refundCounter refund : Nat)
    (h : IsRefundCapped gasUsed refundCounter refund) :
    gasUsed - refund ≥ gasUsed - gasUsed / refundCapDivisor := by
  have hr : refund ≤ gasUsed / refundCapDivisor :=
    refund_le_one_fifth gasUsed refundCounter refund h
  exact Nat.sub_le_sub_left hr gasUsed

end Evm.London.Spec
