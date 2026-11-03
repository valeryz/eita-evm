/-
  Evm.Optimism.Bedrock.Spec.L1Block — the L1Block predeploy and the
  block-prologue system call.

  Source: optimism-monorepo `packages/contracts-bedrock/src/L2/L1Block.sol`.

  Every L2 block's first transaction is a deposited tx that calls
  the L1Block predeploy with the current L1 attributes (the L1 block
  number, L1 block hash, L1 timestamp, L1 base fee, sequence number
  within the L1 epoch, batcher hash, plus Ecotone-added blob base
  fee and scalars). The setters mutate predeploy storage; subsequent
  contract reads (e.g. `block.basefee` of L1 via L1Block.basefee()) hit
  this storage.

  Predeploy address: 0x4200000000000000000000000000000000000015.

  Setter selector evolves by fork:
    Bedrock:  setL1BlockValues(uint64 number, uint64 timestamp,
                               uint256 basefee, bytes32 hash,
                               uint64 sequenceNumber, bytes32 batcherHash,
                               uint256 l1FeeOverhead, uint256 l1FeeScalar)
    Ecotone:  setL1BlockValuesEcotone() — packed calldata, 144 bytes
    Isthmus:  setL1BlockValuesIsthmus()  — extends Ecotone packing
              with new operator-fee fields (gas scalar + flat fee)

  Caller of the system call: 0xDeaDDEaDDeAdDeAdDEAdDEaddeAddEAdDEAd0001
  (the "depositor account"). The deposited-tx envelope carries `from =
  depositor`, so message origin is set to this canonical address.
-/

import Evm.BaseTypes
import Evm.Optimism.Forks

namespace Evm.Optimism.Bedrock.Spec

/-- The L1Block predeploy address. Fixed across all OP forks. -/
def l1BlockPredeploy : Evm.Address := Evm.Address.ofNat 0x4200000000000000000000000000000000000015

/-- The system-call caller used for the block-prologue deposited tx. -/
def depositorAccount : Evm.Address :=
  Evm.Address.ofNat 0xdeaddeaddeaddeaddeaddeaddeaddeaddead0001

/-- ABI selector for each fork's L1-attributes setter. The fork-
    selector is fork-conditional; the predeploy contract dispatches
    on selector and runs different storage layouts. -/
def setL1BlockValuesSelector (f : Evm.Optimism.OpFork) : UInt32 :=
  if f.atLeast .isthmus  then 0x098999be   -- setL1BlockValuesIsthmus()
  else if f.atLeast .ecotone then 0x440a5e20   -- setL1BlockValuesEcotone()
  else                            0x015d8eb9   -- setL1BlockValues(...)

/-- Forward & reverse: the Isthmus selector is only chosen at
    Isthmus+. Catches accidental fork-gate flips. -/
theorem isthmus_selector_iff_isthmus (f : Evm.Optimism.OpFork) :
    setL1BlockValuesSelector f = 0x098999be ↔ f.atLeast .isthmus := by
  unfold setL1BlockValuesSelector
  cases f <;> decide

/-- Ecotone selector is in effect at Ecotone, Fjord, Granite,
    Holocene — and *not* at Isthmus (which has its own selector). -/
theorem ecotone_selector_iff_ecotone_to_holocene (f : Evm.Optimism.OpFork) :
    setL1BlockValuesSelector f = 0x440a5e20 ↔
      (f.atLeast .ecotone ∧ ¬ f.atLeast .isthmus) := by
  unfold setL1BlockValuesSelector
  cases f <;> decide

end Evm.Optimism.Bedrock.Spec
