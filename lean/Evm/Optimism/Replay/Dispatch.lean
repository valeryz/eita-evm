/-
  Evm.Optimism.Replay.Dispatch — fork-dispatched block driver.

  Picks the right `<OpFork>.applyBlock` based on the block's
  timestamp (resolved via `Evm.Optimism.OpFork.baseMainnetAt`).

  Bedrock blocks land in `Bedrock.applyBlock` directly. Canyon /
  Ecotone / Isthmus get their own modules. Fjord / Granite /
  Holocene currently delegate to Ecotone — they don't yet have
  dedicated Fork.lean executables since their deltas are confined
  to (a) precompile additions (Fjord), (b) input-cap (Granite), or
  (c) extraData parsing (Holocene). All three can be wired in by
  parameterising Ecotone.applyBlock when needed.
-/

import Evm.Optimism.Forks
import Evm.Optimism.Bedrock.Fork
import Evm.Optimism.Canyon.Fork
import Evm.Optimism.Ecotone.Fork
import Evm.Optimism.Fjord.Fork
import Evm.Optimism.Granite.Fork
import Evm.Optimism.Isthmus.Fork
import Evm.Optimism.Azul.Fork

namespace Evm.Optimism.Replay

open Evm.Frontier (State)
open Evm.Optimism (OpFork)

/-- Dispatch by OP fork. Picks the right `applyBlock`. -/
def applyBlockFor
    (f : OpFork)
    (state          : State)
    (blockHashes    : List Evm.Hash32)
    (coinbase       : Evm.Address)
    (number gasLimit timestamp : Nat)
    (baseFeePerGas  : Nat)
    (prevRandao     : Evm.Hash32)
    (txs            : List Evm.Optimism.Bedrock.OpTx)
    (operatorParams : Evm.Optimism.Isthmus.Spec.OperatorFeeParams :=
                      { scalar := 0, constant := 0 })
    (withdrawalsCount : Nat := 0)
    (debugTrace       : Bool := false)
    (chainId          : Evm.U256 := 1) :
    Except String Evm.Optimism.Bedrock.BlockResult :=
  match f with
  | .bedrock =>
    Evm.Optimism.Bedrock.applyBlock state blockHashes coinbase number
      gasLimit timestamp baseFeePerGas prevRandao txs
      (debugTrace := debugTrace) (chainId := chainId)
  | .canyon =>
    Evm.Optimism.Canyon.applyBlock state blockHashes coinbase number
      gasLimit timestamp baseFeePerGas prevRandao txs withdrawalsCount
      (debugTrace := debugTrace) (chainId := chainId)
  | .ecotone =>
    Evm.Optimism.Ecotone.applyBlock state blockHashes coinbase number
      gasLimit timestamp baseFeePerGas prevRandao txs withdrawalsCount
      (debugTrace := debugTrace) (chainId := chainId)
  | .fjord =>
    Evm.Optimism.Fjord.applyBlock state blockHashes coinbase number
      gasLimit timestamp baseFeePerGas prevRandao txs withdrawalsCount
      (debugTrace := debugTrace) (chainId := chainId)
  | .granite | .holocene =>
    Evm.Optimism.Granite.applyBlock state blockHashes coinbase number
      gasLimit timestamp baseFeePerGas prevRandao txs withdrawalsCount
      (debugTrace := debugTrace) (chainId := chainId)
  | .isthmus =>
    Evm.Optimism.Isthmus.applyBlock state blockHashes coinbase number
      gasLimit timestamp baseFeePerGas prevRandao txs operatorParams
      withdrawalsCount (debugTrace := debugTrace) (chainId := chainId)
  | .jovian =>
    -- This Lean block driver has none of Jovian's rules (the operator-fee fix, the DA
    -- footprint, the precompile input limits, the minimum base fee): it refuses the
    -- fork rather than run it as Isthmus. The CL replay takes them from the spec
    -- modules (`Replay.Emit.operatorFeeExpr`).
    .error "Jovian: the Lean block driver does not implement Jovian's rules"
  | .beryl | .cobalt | .denim =>
    .error "Beryl, Cobalt, Denim: Base's rules after Azul are not specified here"
  | .azul =>
    Evm.Optimism.Azul.applyBlock state blockHashes coinbase number
      gasLimit timestamp baseFeePerGas prevRandao txs operatorParams
      withdrawalsCount (debugTrace := debugTrace) (chainId := chainId)

end Evm.Optimism.Replay
