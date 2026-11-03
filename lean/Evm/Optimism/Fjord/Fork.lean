/-
  Evm.Optimism.Fjord.Fork — Fjord executable layer.

  Delta vs Ecotone: routes 0x100 → RIP-7212 P256VERIFY via the
  Environment's precompile-overrides list.

  Wire:
    1. `Bedrock.applyBlock` already takes an `applyMessage` parameter
       that we use to inject env-level configuration.
    2. We pre-seed `env.opP256VerifyGas := p256VerifyGasAt .fjord`
       on the applyMessage adapter; the Cancun trampoline's callLike
       branch consults the list before treating a target as an EOA.
    3. The cryptographic primitive (`isValidP256Signature`) is
       declared `opaque` in `Optimism/Fjord/P256VerifyImpl.lean`. That
       opaque is the explicit trust boundary — replace its body with
       a real impl (FFI / pure Lean) to fully discharge the chain.

  See `Optimism/Fjord/Spec/Soundness.lean` for the discharged
  obligation.
-/

import Evm.Optimism.Bedrock.Fork
import Evm.Optimism.Fjord.P256VerifyImpl
import Evm.Optimism.Fjord.Spec.P256Verify
import Evm.Cancun.Vm.Effect

namespace Evm.Optimism.Fjord

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
    .error s!"Fjord+ blocks must have empty withdrawals (got {withdrawalsCount})"
  -- Cancun applyMessage + Fjord precompile override + Granite cap
  -- (Granite ≥ Fjord ordering: although Fjord predates Granite, Base
  -- mainnet's actual Fjord blocks aren't replayed via this driver
  -- in isolation — they go through `Replay.Dispatch.applyBlockFor`).
  let am : Message → Environment → Except Exception Evm :=
    fun msg env =>
      Evm.Cancun.Vm.Effect.applyMessage msg
        { env with opP256VerifyGas := Evm.Optimism.Fjord.Spec.p256VerifyGasAt .fjord }
  Evm.Optimism.Bedrock.applyBlock
    state blockHashes coinbase number gasLimit timestamp baseFeePerGas
    prevRandao txs (applyMessage := am) (eip3860 := true)
    (debugTrace := debugTrace) (chainId := chainId)

end Evm.Optimism.Fjord
