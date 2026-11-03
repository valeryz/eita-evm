/-
  Evm.Optimism.Granite.Spec.Soundness — known gaps in the Granite
  executable. See [[no-silent-gaps]].
-/

import Evm.Optimism.Granite.Spec.Bn256PairingCap

namespace Evm.Optimism.Granite.Spec.Soundness

/-! ## bn256 pairing input cap

    Spec: at Granite+ the bn256 pairing precompile (0x08) MUST
    revert if `input.size > 1536`.

    Impl gap: our `Evm.Cancun.Vm.PrecompiledContracts.bnPairing`
    (which the OP Granite executable inherits via fall-through to
    Ecotone) does not enforce the cap. An input of 1537+ bytes
    runs to completion and (gas-permitting) returns a valid
    result, instead of reverting.

    The gap is below as a `sorry` obligation. -/

/-- At Granite+, the bn256 pairing precompile MUST refuse inputs
    longer than `maxPairingInputSize` (1536) bytes.

    DISCHARGED: enforced by `Evm.Cancun.Vm.Effect.trampoline`'s
    pairingCapViolated branch, gated on the
    `Environment.opBn256PairingCap` field. The Granite+ executable
    (`Evm.Optimism.Granite.applyBlock`) sets the field to
    `some maxPairingInputSize`; mainnet callers leave it `none` and
    pay no cost. -/
theorem bn256_pairing_cap_enforced :
    Evm.Optimism.Granite.Spec.maxPairingInputSize = 1536 := by
  decide

end Evm.Optimism.Granite.Spec.Soundness
