/-
  Evm.Optimism.Granite.Fork — Granite executable layer.

  Delta vs Ecotone: enforces the bn256 pairing input cap (1536 bytes)
  by passing `opBn256PairingCap := some 1536` to the underlying
  Bedrock driver. Cancun's trampoline (and any future fork's that
  inherits it) reads this Environment field and refuses oversized
  pairing inputs.

  See `Optimism/Granite/Spec/Bn256PairingCap.lean` for the spec and
  `Optimism/Granite/Spec/Soundness.lean` for the discharged
  obligation.
-/

import Evm.Optimism.Bedrock.Fork
import Evm.Optimism.Granite.Spec.Bn256PairingCap
import Evm.Optimism.Fjord.P256VerifyImpl
import Evm.Optimism.Fjord.Spec.P256Verify
import Evm.Cancun.Vm.Effect

namespace Evm.Optimism.Granite

open Evm.Frontier (State)
open Evm.Frontier.Vm (Message Environment Evm Exception)

def applyBlock
    (state          : State)
    (blockHashes    : List Evm.Hash32)
    (coinbase       : Evm.Address)
    (number gasLimit timestamp : Nat)
    (baseFeePerGas  : Nat)
    (prevRandao     : Evm.Hash32)
    (txs            : List Evm.Optimism.Bedrock.OpTx)
    (withdrawalsCount : Nat := 0)
    (debugTrace       : Bool := false)
    (chainId          : Evm.U256 := 1) :
    Except String Evm.Optimism.Bedrock.BlockResult := do
  if withdrawalsCount ≠ 0 then
    .error s!"Granite+ blocks must have empty withdrawals (got {withdrawalsCount})"
  -- Granite carries forward Fjord's precompile overrides (0x100
  -- P256VERIFY) in addition to enforcing the bn256 pairing cap.
  let am : Message → Environment → Except Exception Evm :=
    fun msg env =>
      Evm.Cancun.Vm.Effect.applyMessage msg
        { env with opP256VerifyGas := Evm.Optimism.Fjord.Spec.p256VerifyGasAt .granite }
  Evm.Optimism.Bedrock.applyBlock
    state blockHashes coinbase number gasLimit timestamp baseFeePerGas
    prevRandao txs (applyMessage := am)
    (opBn256PairingCap := some Evm.Optimism.Granite.Spec.maxPairingInputSize)
    (eip3860 := true) (debugTrace := debugTrace) (chainId := chainId)

end Evm.Optimism.Granite
