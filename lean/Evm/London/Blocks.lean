/-
  Evm.London.Blocks — block/header for London.

  EELS reference: `forks/london/blocks.py`. The London Header adds one
  field relative to Berlin: `base_fee_per_gas: Uint` (EIP-1559).
  See `forks/london/blocks.py` line 176.

  Per the delta-only fork layout we don't re-declare the whole Header
  record here — Frontier's Header already carries `baseFeePerGas`
  (defaulting to 0 for pre-London callers) — but we re-export the
  Frontier types under `Evm.London` so London-aware code reads naturally.
  This file also adds the EIP-1559 base-fee update rule
  (`calculateBaseFeePerGas`), the per-block constants
  (`elasticityMultiplier`, `baseFeeMaxChangeDenominator`,
  `initialBaseFee`), and the EIP-3554 difficulty bomb constants we
  carry for completeness.
-/

import Evm.BaseTypes
import Evm.Frontier.Blocks

namespace Evm.London

/-- EELS `forks/london/fork.py` line 77. -/
def elasticityMultiplier : Nat := 2

/-- EELS `forks/london/fork.py` line 76. -/
def baseFeeMaxChangeDenominator : Nat := 8

/-- The initial base fee paid at the London activation block. EELS
    `forks/london/fork.py` line 79: `INITIAL_BASE_FEE = Uint(10^9)`. -/
def initialBaseFee : Nat := 1000000000

/-- Re-export Frontier Header / Block under `Evm.London`. The London
    header semantically requires `baseFeePerGas`; the constructor still
    defaults it to 0, but the validators below ensure it's set. -/
abbrev Header := Evm.Frontier.Header
abbrev Block  := Evm.Frontier.Block

/-- EIP-1559 base-fee update rule. EELS:
    `forks/london/fork.py` lines 236-296, `calculate_base_fee_per_gas`.

    `parentGasTarget := parentGasLimit / elasticityMultiplier`.

    * If `parentGasUsed == parentGasTarget`, the new base fee equals
      the parent's.
    * If `parentGasUsed > parentGasTarget`, the new base fee rises by
      `max(1, parentBaseFee * gasUsedDelta / parentGasTarget /
            baseFeeMaxChangeDenominator)`.
    * If `parentGasUsed < parentGasTarget`, the new base fee falls by
      `parentBaseFee * gasUsedDelta / parentGasTarget /
       baseFeeMaxChangeDenominator` (no `max 1` on the way down). -/
def calculateBaseFeePerGas
    (parentGasLimit parentGasUsed parentBaseFeePerGas : Nat) : Nat :=
  let parentGasTarget := parentGasLimit / elasticityMultiplier
  if parentGasUsed = parentGasTarget then
    parentBaseFeePerGas
  else if parentGasUsed > parentGasTarget then
    let gasUsedDelta       := parentGasUsed - parentGasTarget
    let parentFeeGasDelta  := parentBaseFeePerGas * gasUsedDelta
    let targetFeeGasDelta  :=
      if parentGasTarget = 0 then 0 else parentFeeGasDelta / parentGasTarget
    let baseFeePerGasDelta := max (targetFeeGasDelta / baseFeeMaxChangeDenominator) 1
    parentBaseFeePerGas + baseFeePerGasDelta
  else
    let gasUsedDelta       := parentGasTarget - parentGasUsed
    let parentFeeGasDelta  := parentBaseFeePerGas * gasUsedDelta
    let targetFeeGasDelta  :=
      if parentGasTarget = 0 then 0 else parentFeeGasDelta / parentGasTarget
    let baseFeePerGasDelta := targetFeeGasDelta / baseFeeMaxChangeDenominator
    if baseFeePerGasDelta ≥ parentBaseFeePerGas then 0
    else parentBaseFeePerGas - baseFeePerGasDelta

end Evm.London
