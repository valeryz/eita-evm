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
  * Encoded: the end-of-tx settlement `IsFeeSettlement` — the sender's
    refund of the unused gas, the coinbase's priority-fee credit, no other
    balance move (the base-fee share is burnt) — and the conservation
    lemma `fee_conservation` (debit = credit + burn).
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
import Evm.Frontier.State

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

/-! ## The end-of-tx settlement (burn / credit split)

    The sender paid `gas_limit · effective_price` up front. At the end it
    gets back the unused gas at the effective price, the coinbase gets the
    priority fee on the gas used, and the base fee on the gas used is
    credited to nobody: it is BURNT (`fee_conservation` below). -/

/-- `IsFeeSettlement sender coinbase gasLimit gasUsed price baseFee pre post` — the
    balance changes of EELS `forks/london/fork.py::process_transaction` 813-835:
    `create_ether(sender, tx_gas_left · effective_gas_price)` with `tx_gas_left =
    tx.gas − tx_gas_used_after_refund`, then the coinbase's balance `+= tx_gas_used ·
    priority_fee_per_gas` (`priority_fee_per_gas = effective_gas_price − base_fee`); no
    other balance moves (the base-fee share is burnt). Replaces the separate
    `IsCoinbaseCredit` / `IsBaseFeeBurnt` / `IsTxFeeDebit` number equations, which no
    implementation computed as such. -/
def IsFeeSettlement (sender coinbase : Evm.Address)
    (gasLimit gasUsed effectivePrice baseFee : Nat) (pre post : Evm.Frontier.State) : Prop :=
  let refunded :=
    pre.addBalance sender (Evm.U256.ofNat ((gasLimit - gasUsed) * effectivePrice))
  (post.getAccount coinbase).balance
      = (refunded.getAccount coinbase).balance
          + Evm.U256.ofNat (gasUsed * (effectivePrice - baseFee)) ∧
  ∀ a, a ≠ coinbase → (post.getAccount a).balance = (refunded.getAccount a).balance

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
