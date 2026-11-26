/-
  Evm.Avalanche.Charging — Coreth post-Apricot & Helicon/SAE transaction gas and fee rules.

  Source: avalanchego d38de7e0
    graft/coreth/core/state_transition.go  TransitionDb / refundGas (refunds disabled;
                                           whole fee credited to coinbase 0x0100..0000)
    vms/saevm/saexec / libevm              StateTransition.afterGasRefund with
                                           MinimumGasConsumption (λ = 2: ceil(limit / 2))
-/

import Evm.Avalanche.Forks

namespace Evm.Avalanche.Charging

/-- SAE minimum gas consumption divisor (`saeparams.Lambda = 2`). -/
def saeLambda : Nat := 2

/-- Minimum gas charged under Helicon/SAE: `ceil(gasLimit / 2)`. -/
def saeGasFloor (gasLimit : Nat) : Nat := (gasLimit + 1) / saeLambda

/-- Coreth disables EVM gas refunds (`refund = 0`). Under Helicon/SAE, charged gas is
    `max (spent + predicateGas) (ceil(gasLimit / 2))`; pre-Helicon it is `spent + predicateGas`. -/
def txGasUsed (f : AvaxFork) (spent predicateGas gasLimit : Nat) : Nat :=
  let totalSpent := spent + predicateGas
  if f.saeActive then max totalSpent (saeGasFloor gasLimit) else totalSpent

/-- Unused gas returned to the sender at the effective gas price. -/
def unusedGas (gasLimit charged : Nat) : Nat := gasLimit - charged

/-- Fee credited to coinbase (`0x0100..0000`): the whole charged gas at `egp` (no burn split). -/
def coinbaseFee (charged egp : Nat) : Nat := charged * egp

/-- Unused gas refund credited back to the sender. -/
def senderRefund (gasLimit charged egp : Nat) : Nat := unusedGas gasLimit charged * egp

/-- Effective gas price for a dynamic-fee (EIP-1559) transaction. -/
def dynamicEgp (maxFee maxPriority baseFee : Nat) : Nat :=
  min maxFee (baseFee + maxPriority)

theorem saeGasFloor_le_limit (gasLimit : Nat) :
    saeGasFloor gasLimit ≤ gasLimit := by
  unfold saeGasFloor saeLambda; omega

theorem two_mul_saeGasFloor_ge (gasLimit : Nat) :
    2 * saeGasFloor gasLimit ≥ gasLimit := by
  unfold saeGasFloor saeLambda; omega

theorem txGasUsed_ge_spent (f : AvaxFork) (spent predicateGas gasLimit : Nat) :
    txGasUsed f spent predicateGas gasLimit ≥ spent + predicateGas := by
  simp only [txGasUsed]
  split <;> omega

theorem txGasUsed_ge_sae_floor (spent predicateGas gasLimit : Nat) :
    2 * txGasUsed .helicon spent predicateGas gasLimit ≥ gasLimit := by
  simp [txGasUsed, saeGasFloor, saeLambda, AvaxFork.saeActive, AvaxFork.atLeast, AvaxFork.ord]
  omega

theorem txGasUsed_le_limit (f : AvaxFork) (spent predicateGas gasLimit : Nat)
    (h : spent + predicateGas ≤ gasLimit) :
    txGasUsed f spent predicateGas gasLimit ≤ gasLimit := by
  simp only [txGasUsed, saeGasFloor, saeLambda]
  split <;> omega

/-- Exact wei conservation: sender refund + coinbase fee = upfront gasLimit * egp. -/
theorem fee_conservation (gasLimit charged egp : Nat) (h : charged ≤ gasLimit) :
    senderRefund gasLimit charged egp + coinbaseFee charged egp = gasLimit * egp := by
  unfold senderRefund coinbaseFee unusedGas
  rw [← Nat.add_mul, Nat.sub_add_cancel h]

/-- Soundness of recovering an SAE block's executed base fee from a dynamic-fee receipt
    whose effective gas price fell strictly below its fee cap. -/
theorem sae_executed_base_fee_sound (maxFee tip baseFee : Nat)
    (h : dynamicEgp maxFee tip baseFee < maxFee) :
    dynamicEgp maxFee tip baseFee - tip = baseFee := by
  unfold dynamicEgp at *
  omega

end Evm.Avalanche.Charging
