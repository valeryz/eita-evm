/-
  Evm.Optimism.Canyon.Fork — Canyon executable layer.

  Delta vs Bedrock:
    * EVM is Shanghai (PUSH0 / EIP-3651 warm coinbase / EIP-3860
      init-code cap+surcharge), so the supplied `applyMessage` is
      `Evm.Shanghai.Vm.Effect.applyMessage`.
    * `withdrawals` field is REQUIRED to be empty on OP. We validate
      that at the entry of `applyBlock` and then ignore it.

  Block driver delegates straight through to Bedrock.applyBlock —
  no other shape change.
-/

import Evm.Optimism.Bedrock.Fork
import Evm.Shanghai.Vm.Effect

namespace Evm.Optimism.Canyon

open Evm.Frontier (State)
open Evm.Frontier.Vm (Message Environment Evm Exception)

/-- Canyon block driver.

    `withdrawalsCount` is the length of the block's withdrawals
    list. EIP-4895 mandates it be present-but-empty on OP from
    Canyon onwards. -/
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
    .error s!"Canyon+ blocks must have empty withdrawals (got {withdrawalsCount})"
  Evm.Optimism.Bedrock.applyBlock
    state blockHashes coinbase number gasLimit timestamp baseFeePerGas
    prevRandao txs (applyMessage := Evm.Shanghai.Vm.Effect.applyMessage)
    (eip3860 := true) (debugTrace := debugTrace) (chainId := chainId)

end Evm.Optimism.Canyon
