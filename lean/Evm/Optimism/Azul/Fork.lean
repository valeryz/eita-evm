/-
  Evm.Optimism.Azul.Fork — Base-mainnet-only post-Isthmus fork that
  activates Osaka execution-layer semantics ahead of the broader
  Superchain.

  Activated: 2026-05-28 18:00:00 UTC (timestamp 1779991200) on Base
  mainnet (chain id 8453). Source of truth: `base/base` repo,
  `crates/common/chains/src/config.rs::MAINNET.azul_timestamp =
  Some(1_779_991_200)`. Announcement:
  https://blog.base.dev/introducing-base-azul.

  Crucially: OP Mainnet did NOT activate Osaka semantics with the
  Superchain's Upgrade 17 (Jovian, 2025-12-02); per Optimism
  governance, "We will NOT be activating Osaka (the execution layer
  component of the Fusaka hardfork) on L2 with this upgrade."
  Reference: https://gov.optimism.io/t/upgrade-17-jovian-hardfork-and-fusaka-readiness/10400.
  So Azul is a BASE-SPECIFIC delta, NOT shared with the rest of the
  Superchain.

  Delta on Isthmus:
    * EIP-7883: MODEXP gas reprice. Berlin's `max(200, mult*iter/3)`
      becomes Osaka's `max(500, mult*iter)`. multComplexity is also
      changed to `max(16, 2*ceil(max(B,M)/8)²)` for inputs > 32 bytes.
      Implemented in `Evm.Osaka.Vm.PrecompiledContracts.modexp7883`.
    * EIP-7823: MODEXP input-size cap (≤ 1024 bytes per operand).
      Enforced inside the same impl.

  Everything else inherits from Isthmus directly (EVM is still
  Prague, EIP-7702 still active, fee-vault routing unchanged, etc.).

  This module is the seam where the EIP-7883 precompile swap happens.
-/

import Evm.Optimism.Isthmus.Fork
import Evm.Osaka.Vm.PrecompiledContracts

namespace Evm.Optimism.Azul

open Evm.Frontier.Vm (Message Environment Evm Exception)
open Evm.Frontier (State)

/-- Azul precompile table: Isthmus's lookup with 0x05 swapped to
    Osaka's EIP-7883 MODEXP. Every other precompile address falls
    through to the inherited Isthmus (Cancun-default) table. -/
def azulPrecompiles
    (addr : Evm.Address) :
    Option Evm.Frontier.Vm.PrecompiledContracts.Precompile :=
  if addr = Evm.Address.ofNat 0x05 then
    some Evm.Osaka.Vm.PrecompiledContracts.modexp7883
  else
    Evm.Optimism.Isthmus.isthmusPrecompiles addr

/-- Azul applyMessage adapter: Prague semantics + Azul precompile
    table (which swaps in Osaka MODEXP at 0x05). -/
private def azulApplyMessage : Message → Environment → Except Exception Evm := fun msg env =>
  let pstate : Evm.Prague.State := { inner := env.state }
  let (result, _newPstate) :=
    Evm.Prague.Vm.Effect.applyMessage msg env pstate
      (precompileLookup := azulPrecompiles)
  result

/-- Run an Azul block. Same shape as Isthmus.applyBlock, but uses
    Azul's precompile table (with EIP-7883 active at 0x05). All
    other behaviour — operator fee, EIP-7702 set-code txs, withdrawal
    rules — inherits from Isthmus. -/
def applyBlock
    (state            : State)
    (blockHashes      : List Evm.Hash32)
    (coinbase         : Evm.Address)
    (number gasLimit timestamp : Nat)
    (baseFeePerGas    : Nat)
    (prevRandao       : Evm.Hash32)
    (txs              : List Evm.Optimism.Bedrock.OpTx)
    (operatorParams   : Evm.Optimism.Isthmus.Spec.OperatorFeeParams :=
                          { scalar := 0, constant := 0 })
    (withdrawalsCount : Nat := 0)
    (debugTrace       : Bool := false)
    (chainId          : Evm.U256 := 1) :
    Except String Evm.Optimism.Bedrock.BlockResult := do
  if withdrawalsCount ≠ 0 then
    .error s!"Azul blocks must have empty withdrawals (got {withdrawalsCount})"
  let rec go (st : Evm.Frontier.State) (gasAcc : Nat)
             (logsAcc : List Evm.Frontier.Vm.Log)
             (xs : List Evm.Optimism.Bedrock.OpTx) :
      Except String Evm.Optimism.Bedrock.BlockResult :=
    match xs with
    | [] => .ok { state := st, gasUsed := gasAcc, logs := logsAcc }
    | Evm.Optimism.Bedrock.OpTx.deposited dtx :: rest => do
      let am : Message → Environment → Except Exception Evm :=
        fun msg env =>
          azulApplyMessage msg
            { env with
                opBn256PairingCap   := some Evm.Optimism.Granite.Spec.maxPairingInputSize
                opP256VerifyGas     := Evm.Optimism.Fjord.Spec.p256VerifyGasAt .azul
                pragueDelegation    := true
                debugTrace          := debugTrace }
      let r ← Evm.Optimism.Bedrock.processDepositedTx st blockHashes
                coinbase number gasLimit timestamp baseFeePerGas
                prevRandao dtx am
      go r.state (gasAcc + r.gasUsed) (logsAcc ++ r.logs) rest
    | Evm.Optimism.Bedrock.OpTx.userWithAuths u auths :: rest => do
      let am : Message → Environment → Except Exception Evm :=
        fun msg env =>
          azulApplyMessage msg
            { env with
                opBn256PairingCap   := some Evm.Optimism.Granite.Spec.maxPairingInputSize
                opP256VerifyGas     := Evm.Optimism.Fjord.Spec.p256VerifyGasAt .azul
                pragueDelegation    := true
                debugTrace          := debugTrace }
      let authIntrinsic := auths.length * 25000
      let r ← Evm.Optimism.Bedrock.processUserTx st blockHashes
                coinbase number gasLimit timestamp baseFeePerGas
                prevRandao u am (eip3860 := true) (chainId := chainId)
                (eip7623 := true) (authIntrinsic := authIntrinsic)
                (auths := auths)
      let opFee := Evm.Optimism.Isthmus.Spec.operatorFeeWei operatorParams r.gasUsed
      let stateWithOpFee :=
        if opFee = 0 then r.state
        else r.state.addBalance Evm.Optimism.Isthmus.Spec.operatorFeeVault (Evm.U256.ofNat opFee)
      go stateWithOpFee (gasAcc + r.gasUsed) (logsAcc ++ r.logs) rest
    | Evm.Optimism.Bedrock.OpTx.user u :: rest => do
      let am : Message → Environment → Except Exception Evm :=
        fun msg env =>
          azulApplyMessage msg
            { env with
                opBn256PairingCap   := some Evm.Optimism.Granite.Spec.maxPairingInputSize
                opP256VerifyGas     := Evm.Optimism.Fjord.Spec.p256VerifyGasAt .azul
                pragueDelegation    := true
                debugTrace          := debugTrace }
      let r ← Evm.Optimism.Bedrock.processUserTx st blockHashes
                coinbase number gasLimit timestamp baseFeePerGas
                prevRandao u am (eip3860 := true) (chainId := chainId)
                (eip7623 := true)
      let opFee := Evm.Optimism.Isthmus.Spec.operatorFeeWei operatorParams r.gasUsed
      let stateWithOpFee :=
        if opFee = 0 then r.state
        else r.state.addBalance Evm.Optimism.Isthmus.Spec.operatorFeeVault (Evm.U256.ofNat opFee)
      go stateWithOpFee (gasAcc + r.gasUsed) (logsAcc ++ r.logs) rest
  go state 0 [] txs

end Evm.Optimism.Azul
