/-
  Evm.London.Spec.BaseFee — EIP-1559 base-fee formula.

  EELS reference: `forks/london/fork.py` `calculate_base_fee_per_gas`.
  Approximate body (paraphrased from the Python):

  ```
  parent_gas_target = parent_gas_limit // ELASTICITY_MULTIPLIER  # =2
  if parent_gas_used == parent_gas_target:
      return parent_base_fee_per_gas
  elif parent_gas_used > parent_gas_target:
      delta = parent_gas_used - parent_gas_target
      return parent_base_fee_per_gas + max(
          parent_base_fee_per_gas * delta //
              parent_gas_target //
              BASE_FEE_MAX_CHANGE_DENOMINATOR,                   # =8
          1)
  else:
      delta = parent_gas_target - parent_gas_used
      return parent_base_fee_per_gas - (
          parent_base_fee_per_gas * delta //
              parent_gas_target //
              BASE_FEE_MAX_CHANGE_DENOMINATOR)
  ```

  Constants (EIP-1559 §"Specification"):
    * `ELASTICITY_MULTIPLIER             = 2`
    * `BASE_FEE_MAX_CHANGE_DENOMINATOR   = 8`
    * `INITIAL_BASE_FEE                  = 10⁹` (genesis of London;
                                                 not used here)

  The formula's behavior:
    * gas_used == target  → base fee unchanged.
    * gas_used > target   → base fee rises, at most by 1/8 per block.
      The `max(…, 1)` clause ensures a min increment of 1 wei when
      the percentage increment would round to zero (otherwise tiny
      blocks with `gas_used = target + 1` would never raise the fee).
    * gas_used < target   → base fee falls, at most by 1/8 per block.
      No `max(…, 1)` here — the fee CAN stay flat under tiny
      decrements (intentional; the floor is just bounded by zero).

  ## What's encoded vs glossed

  * Encoded: the three-branch formula above, faithfully — including
    the `max(…, 1)` floor on the up branch.
  * Encoded: the floor-division order (`* delta // target //
    DENOM`). This matters: `a * b // c // d ≠ a * b // (c * d)` for
    arbitrary `a, b, c, d` due to truncation order. EELS chains the
    divisions left-to-right; we mirror.
  * Glossed: the *header validity* check that the new base fee
    equals the formula's output. That's the job of the London
    block-validation relation (`forks/london/fork.py`
    `validate_header`) — out of scope for this file.
  * Glossed: the genesis-base-fee bootstrap (block 12,965,000 is
    seeded with `INITIAL_BASE_FEE = 10⁹` by definition).

  EELS line citations are best-effort; the file has been refactored
  since this spec was last reviewed against an exact revision. The
  formula above is the EIP-1559 final spec and matches every
  implementation we've cross-checked.
-/

namespace Evm.London.Spec

/-- EIP-1559 `BASE_FEE_MAX_CHANGE_DENOMINATOR`. -/
def baseFeeMaxChangeDenominator : Nat := 8

/-- EIP-1559 `ELASTICITY_MULTIPLIER`. The block gas target is
    `gasLimit / 2`; the gas limit is the absolute ceiling. -/
def elasticityMultiplier : Nat := 2

/-- EIP-1559 `INITIAL_BASE_FEE` at the London fork block. Exposed as
    a constant; the genesis seed lives in `London/Fork.lean` once
    that fork's apply-block plumbs it. -/
def initialBaseFee : Nat := 1_000_000_000

/-- The base-fee formula. Pure function of three Nats; the predicate
    form is `IsCalculatedBaseFee` below. EELS:
    `calculate_base_fee_per_gas(
       block_gas_limit,        -- = parent_gas_limit
       parent_gas_limit,
       parent_gas_used,
       parent_base_fee_per_gas)`
    In London (no gas-limit transitions inside this formula at this
    fork), the first two are equal, so we simplify the signature to
    `(parent_gas_used, parent_gas_target, parent_base_fee)` per the
    brief. The caller computes `parent_gas_target = parent_gas_limit
    / elasticityMultiplier` outside this function. -/
def calculateBaseFeePerGas
    (parentGasUsed parentGasTarget parentBaseFee : Nat) : Nat :=
  if parentGasUsed = parentGasTarget then
    parentBaseFee
  else if parentGasUsed > parentGasTarget then
    let delta := parentGasUsed - parentGasTarget
    let raw   := parentBaseFee * delta / parentGasTarget / baseFeeMaxChangeDenominator
    parentBaseFee + max raw 1
  else
    -- parentGasUsed < parentGasTarget
    let delta := parentGasTarget - parentGasUsed
    let raw   := parentBaseFee * delta / parentGasTarget / baseFeeMaxChangeDenominator
    -- `Nat.sub` saturates at 0 — fine, the formula never goes below
    -- zero because the down-step is at most 1/8 of the current fee.
    parentBaseFee - raw

/-- The function-relation pair. `IsCalculatedBaseFee p_used p_tgt p_bf
    f` holds iff `f` is the base fee for the current block given the
    parent's `(gas_used, gas_target, base_fee)`. -/
def IsCalculatedBaseFee
    (parentGasUsed parentGasTarget parentBaseFee : Nat) (f : Nat) : Prop :=
  f = calculateBaseFeePerGas parentGasUsed parentGasTarget parentBaseFee

/-! ## Properties

    The formula has two structural properties worth pinning down for
    refinement: it's a total function (well-defined for all inputs
    with target ≥ 1) and is monotone in `parentBaseFee` (no
    surprises). The hard property — "base fee changes by at most
    1/8 per block" — is a consequence of the `* delta / target /
    DENOM` chain, but proving the bound requires a non-trivial
    division lemma. We defer. -/

/-- The formula evaluates deterministically. (Trivially true since
    `calculateBaseFeePerGas` is a `def`, but the lemma makes the
    relation's functionality explicit.) -/
theorem baseFee_deterministic
    (parentGasUsed parentGasTarget parentBaseFee f₁ f₂ : Nat)
    (h₁ : IsCalculatedBaseFee parentGasUsed parentGasTarget parentBaseFee f₁)
    (h₂ : IsCalculatedBaseFee parentGasUsed parentGasTarget parentBaseFee f₂) :
    f₁ = f₂ := h₁.trans h₂.symm

/-- When `parent_gas_used == parent_gas_target`, the base fee is
    unchanged. Sanity-check of the equality branch. -/
theorem baseFee_at_target_unchanged
    (target parentBaseFee : Nat) :
    calculateBaseFeePerGas target target parentBaseFee = parentBaseFee := by
  simp [calculateBaseFeePerGas]

end Evm.London.Spec
