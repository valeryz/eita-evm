/-
  Evm.London.Spec.FeeMarket — EIP-1559 effective gas price + burn.

  EELS reference: `forks/london/fork.py` `process_transaction`
  (around the upfront-cost / coinbase-credit block). The relevant
  EELS lines compute:

  ```
  if isinstance(tx, FeeMarketTransaction):
      priority_fee_per_gas = min(
          tx.max_priority_fee_per_gas,
          tx.max_fee_per_gas - block_env.base_fee_per_gas)
      effective_gas_price = priority_fee_per_gas + block_env.base_fee_per_gas
  else:
      # legacy / type-1 (access-list) tx
      priority_fee_per_gas = tx.gas_price - block_env.base_fee_per_gas
      effective_gas_price = tx.gas_price
  …
  blob_gas_fee = 0  # London proper
  total_gas_used = gas_used + (refund applied)
  ...
  coinbase_credit_wei = total_gas_used * priority_fee_per_gas
  state.add_balance(block_env.coinbase, coinbase_credit_wei)
  # NB: state.add_balance(coinbase, gas_used * base_fee_per_gas)  is NOT done;
  # the base-fee portion is BURNED — it leaves the sender, never lands.
  ```

  The two consequential facts:

    (A) The coinbase credit equals
            `gasUsed * priorityFeePerGas`
        and NOT `gasUsed * effectiveGasPrice`. The base-fee portion
        is BURNED — i.e., subtracted from the sender's upfront
        payment but credited to no account (mass leaves the
        execution-layer money supply).
    (B) `effectiveGasPrice = baseFee + priorityFee`, and
        `priorityFee = min(maxPriority, maxFee - baseFee)`. For the
        legacy / access-list cases, `effectiveGasPrice = tx.gasPrice`
        directly; `priorityFee = tx.gasPrice - baseFee` (only valid
        when `tx.gasPrice ≥ baseFee`, which is a tx validity
        precondition checked elsewhere).

  ## What's encoded vs glossed in this file

  * Encoded: the `effectivePrice` and `priorityFee` formulas as
    pure functions of `(maxFee, maxPriority, baseFee)`.
  * Encoded: the coinbase-credit relation
    `IsCoinbaseCredit gasUsed priorityFee credit`.
  * Encoded: the burn relation
    `IsBaseFeeBurnt gasUsed baseFee burntWei` — declared distinct
    from the coinbase credit to make the two-flows nature of the
    EIP-1559 fee market a first-class spec object.
  * Encoded: the sender-deduction invariant
    `IsTxFeeDebit sender gasUsed effectivePrice debited` — the
    sender pays `gasUsed * effectivePrice`, which equals
    `(coinbaseCredit + burnt)`. We state and prove the conservation
    lemma.
  * Glossed: the LEGACY/type-1 tx path is collapsed by the
    convention `priorityFee = gasPrice - baseFee, effectivePrice =
    gasPrice`. The relation here lives at the
    `(effectivePrice, priorityFee)` interface, not the tx-type
    interface; the caller picks the input pair according to tx
    type and feeds it in.
  * Glossed: the up-front cost check `senderBalance ≥ maxFee *
    gasLimit + value` — that's tx-validity, not the post-execution
    fee distribution.
  * Glossed: the refund cap interaction. `gasUsed` here is the
    POST-REFUND value (`gasUsed - refund`), so the refund logic
    composes BEFORE this spec. See `RefundCap.lean`.
-/

import Evm.BaseTypes

namespace Evm.London.Spec

/-! ## Effective price + priority fee (Type-2 / EIP-1559 path)

    For a type-2 transaction with `maxFee` and `maxPriority`:
      priorityFee   = min(maxPriority, maxFee - baseFee)
      effectivePrice = baseFee + priorityFee
                     = min(maxFee, baseFee + maxPriority)

    The two formulations are equivalent (provable from
    `baseFee ≤ maxFee` tx-validity). We use the second form (per
    brief) since it doesn't require Nat-subtraction safety. -/

/-- EIP-1559 effective gas price for a type-2 tx. EELS form:
    `min(maxFee, baseFee + maxPriority)`. -/
def effectivePrice (maxFee maxPriority baseFee : Nat) : Nat :=
  min maxFee (baseFee + maxPriority)

/-- EIP-1559 priority fee for a type-2 tx. EELS form:
    `effectivePrice - baseFee`. Saturates at 0 (which means: when
    `effectivePrice < baseFee`, this would underflow on signed math;
    in practice, tx validity ensures `maxFee ≥ baseFee`, so
    `effectivePrice ≥ baseFee` and the subtraction is safe). -/
def priorityFee (maxFee maxPriority baseFee : Nat) : Nat :=
  effectivePrice maxFee maxPriority baseFee - baseFee

/-! ## Burn / credit split

    The sender pays `gasUsed * effectivePrice`. That payment splits
    into two streams:
      * `gasUsed * baseFee` — BURNT (no recipient).
      * `gasUsed * priorityFee` — credited to the block coinbase. -/

/-- `IsCoinbaseCredit gasUsed priorityFee credit` — the coinbase's
    EIP-1559 credit for a single tx. Note the multiplier is
    `priorityFee`, NOT `effectivePrice`. -/
def IsCoinbaseCredit (gasUsed priorityFeePerGas credit : Nat) : Prop :=
  credit = gasUsed * priorityFeePerGas

/-- `IsBaseFeeBurnt gasUsed baseFee burnt` — the wei the network
    eliminates per tx. Equal to `gasUsed * baseFee`. The post-state
    contains no balance increase by this amount anywhere; it is
    deducted from the sender as part of the upfront cost and never
    re-deposited. -/
def IsBaseFeeBurnt (gasUsed baseFee burnt : Nat) : Prop :=
  burnt = gasUsed * baseFee

/-- `IsTxFeeDebit gasUsed effectivePrice debited` — the wei deducted
    from the sender (per-tx fee portion only; the `value` field
    transfers separately). Equals `gasUsed * effectivePrice`. -/
def IsTxFeeDebit (gasUsed effectivePricePerGas debited : Nat) : Prop :=
  debited = gasUsed * effectivePricePerGas

/-! ## Conservation theorem

    The two output streams (coinbase credit + burn) must add up to
    the single input stream (sender debit). This is the on-paper
    statement of "EIP-1559 doesn't create money, it destroys some of
    what the sender paid". -/

/-- For a type-2 tx with valid `(maxFee, maxPriority, baseFee)` (i.e.
    `effectivePrice = baseFee + priorityFee` exactly), the sender's
    debit equals the coinbase credit plus the burnt amount.

    Statement:
      `gasUsed * effectivePrice = gasUsed * priorityFee + gasUsed * baseFee`
    which holds whenever `effectivePrice = baseFee + priorityFee`. -/
theorem fee_conservation
    (gasUsed maxFee maxPriority baseFee : Nat)
    (hValid : maxFee ≥ baseFee) :
    gasUsed * effectivePrice maxFee maxPriority baseFee =
      gasUsed * priorityFee maxFee maxPriority baseFee +
      gasUsed * baseFee := by
  -- priorityFee = effectivePrice - baseFee  (by def)
  -- and  effectivePrice ≥ baseFee  (under hValid, since
  -- min maxFee (baseFee + maxPriority) ≥ baseFee).
  have h1 : baseFee ≤ effectivePrice maxFee maxPriority baseFee := by
    unfold effectivePrice
    apply Nat.le_min.mpr
    exact ⟨hValid, Nat.le_add_right baseFee maxPriority⟩
  -- Now effectivePrice = priorityFee + baseFee.
  have h2 : effectivePrice maxFee maxPriority baseFee =
            priorityFee maxFee maxPriority baseFee + baseFee := by
    unfold priorityFee
    exact (Nat.sub_add_cancel h1).symm
  rw [h2, Nat.mul_add]

/-! ## Legacy / type-1 tx path

    For legacy and type-1 (access-list) transactions, EELS does
      `priority_fee_per_gas = tx.gas_price - block_env.base_fee_per_gas`
      `effective_gas_price  = tx.gas_price`
    The same conservation theorem applies (since
    `tx.gas_price = (tx.gas_price - baseFee) + baseFee` under the
    `tx.gas_price ≥ baseFee` tx-validity precondition). We provide
    a convenience constructor that exposes the same
    `(effectivePrice, priorityFee)` pair from a legacy `gasPrice`. -/

/-- Legacy / type-1 tx-level helper: derive the EIP-1559 fee pair
    from the monolithic `gasPrice`. Requires `gasPrice ≥ baseFee`
    (tx validity); under that precondition, the conservation
    theorem `fee_conservation_legacy` below holds. -/
def legacyFeePair (gasPrice baseFee : Nat) : Nat × Nat :=
  (gasPrice, gasPrice - baseFee)

/-- Conservation for legacy/type-1 tx. -/
theorem fee_conservation_legacy
    (gasUsed gasPrice baseFee : Nat)
    (hValid : gasPrice ≥ baseFee) :
    gasUsed * gasPrice =
      gasUsed * (gasPrice - baseFee) + gasUsed * baseFee := by
  rw [← Nat.mul_add, Nat.sub_add_cancel hValid]

end Evm.London.Spec
