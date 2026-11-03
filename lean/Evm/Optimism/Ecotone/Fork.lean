/-
  Evm.Optimism.Ecotone.Fork — Ecotone executable layer.

  Delta vs Canyon:
    * EVM is Cancun (EIP-1153 TLOAD/TSTORE, EIP-5656 MCOPY,
      EIP-6780 SELFDESTRUCT, EIP-4844 BLOBHASH / BLOBBASEFEE in
      opcode space — though L2 blobs themselves aren't a thing).
    * L1Block.setL1BlockValuesEcotone selector + 144-byte packed
      calldata layout (handled by the EVM execution of the
      L1Block predeploy when the prologue tx runs; not a fork
      concern at the EL driver level).

  Block driver delegates to Bedrock.applyBlock with the Cancun
  applyMessage.
-/

import Evm.Optimism.Bedrock.Fork
import Evm.Cancun.Vm.Effect

namespace Evm.Optimism.Ecotone

open Evm.Frontier (State)

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
    .error s!"Ecotone+ blocks must have empty withdrawals (got {withdrawalsCount})"
  Evm.Optimism.Bedrock.applyBlock
    state blockHashes coinbase number gasLimit timestamp baseFeePerGas
    prevRandao txs (applyMessage := Evm.Cancun.Vm.Effect.applyMessage)
    (eip3860 := true) (debugTrace := debugTrace) (chainId := chainId)

end Evm.Optimism.Ecotone
