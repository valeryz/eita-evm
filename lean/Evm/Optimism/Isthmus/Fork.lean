/-
  Evm.Optimism.Isthmus.Fork — Isthmus executable layer.

  Delta vs Ecotone:
    * EVM is Prague (EIP-2537 BLS, EIP-2935 historical hashes,
      EIP-7702 set-code txs, EIP-7623 calldata floor, EIP-7685
      requests root). The supplied `applyMessage` is
      `Evm.Prague.Vm.Effect.applyMessage`.
    * Operator fee component added on every user tx, routed to
      `OperatorFeeVault` (0x42…1B). The scalar + constant are read
      from L1Block predeploy storage (populated by the prologue
      `setL1BlockValuesIsthmus` call); the caller passes them in
      via `operatorFeeParams`.
    * Block-level invariant: `header.withdrawalsRoot` must equal
      the L2ToL1MessagePasser predeploy's storage trie root. We
      DON'T check that here (the trie root computation is non-
      trivial and lives in the matcher); we'll validate it at the
      Replay layer when state-root assertion is wired.

  The operator fee is charged ON TOP of the EVM gas fee + L1 data
  fee. We bolt it onto each user tx by inflating the L1FeeVault
  credit and the upfront-cost computation. To stay surgical, this
  module wraps `processUserTx` with one extra credit pass after
  the underlying driver returns.
-/

import Evm.Optimism.Bedrock.Fork
import Evm.Optimism.Isthmus.Spec.PragueInheritance
import Evm.Optimism.Granite.Spec.Bn256PairingCap
import Evm.Optimism.Fjord.P256VerifyImpl
import Evm.Optimism.Fjord.Spec.P256Verify
import Evm.Cancun.Vm.Effect
import Evm.Cancun.Vm.PrecompiledContracts
import Evm.Prague.Vm.Effect
import Evm.Prague.State
import Evm.Prague.Fork
import Evm.Prague.Transactions
import Evm.Osaka.Vm.PrecompiledContracts

namespace Evm.Optimism.Isthmus

open Evm.Frontier.Vm (Message Environment Evm Exception)

/-! ## Prague applyMessage adapter

    Prague's `applyMessage` has signature
        `Message → Environment → Prague.State → Except Exception Evm × Prague.State`
    because it threads `Prague.State` for EIP-7702 delegation lookups,
    transient storage, EIP-2929 warm-cold tracking, EIP-6780
    createdAccounts, etc.

    The OP driver in `Bedrock.applyBlock` expects the Cancun-shape
    signature `Message → Environment → Except Exception Evm`. We
    adapt by wrapping `env.state` (a `Frontier.State`) in a fresh
    `Prague.State` per call.

    SOUNDNESS GAP (explicit, see
    `Optimism/Isthmus/Spec/Soundness.lean`): the per-call wrap
    discards Prague.State BETWEEN top-level message calls. Inside a
    single message tree the state is threaded correctly (Prague's
    own recursion takes care of that), but cross-message:
      * EIP-7702 delegations created by one set-code tx are not
        visible to a later set-code tx in the same block;
      * EIP-1153 transient storage works (single tx) but a future
        cross-tx leak couldn't be caught by this adapter.

    Both are visible as `sorry` obligations in the spec module. -/

/-- Isthmus precompile table: Cancun's Prague-inherited registry,
    unchanged. Upstream op-geth's `PrecompiledContractsIsthmus` has
    `bigModExp{eip2565: true}` — Berlin's formula, NOT Osaka's
    EIP-7883. EIP-7883 lands on Base via the Base-specific Azul
    fork (see `Optimism/Azul/Fork.lean`); OP Mainnet hasn't activated
    Osaka semantics yet (Jovian explicitly deferred them). -/
def isthmusPrecompiles
    (addr : Evm.Address) :
    Option Evm.Frontier.Vm.PrecompiledContracts.Precompile :=
  Evm.Cancun.Vm.PrecompiledContracts.lookup addr

private def isthmusApplyMessage : Message → Environment → Except Exception Evm := fun msg env =>
  -- Wrap env.state in a fresh Prague.State. inner = env.state; the
  -- four post-Frontier scratch maps are empty at message entry.
  let pstate : Evm.Prague.State := { inner := env.state }
  let (result, _newPstate) :=
    Evm.Prague.Vm.Effect.applyMessage msg env pstate
      (precompileLookup := isthmusPrecompiles)
  -- The new Prague.State delta is discarded; only the Evm result
  -- (which already carries env.state mutations) propagates.
  result

open Evm.Frontier (State)
open Evm.Optimism.Isthmus.Spec (OperatorFeeParams operatorFeeWei operatorFeeVault)

/-- Run an Isthmus block. Same shape as `Ecotone.applyBlock` plus
    the operator-fee credit (applied to OperatorFeeVault). The
    actual operator-fee scalars live in `params.l1Block.operator*`
    — see the Isthmus L1Block predeploy storage layout.

    For an Isthmus-era block, pass `operatorParams` populated from
    the L1Block storage at the START of the block (i.e. as it would
    be AFTER the prologue tx runs — most easily, just read the
    pre-state's slot since the prologue overwrites with the same
    values). -/
def applyBlock
    (state            : State)
    (blockHashes      : List Evm.Hash32)
    (coinbase         : Evm.Address)
    (number gasLimit timestamp : Nat)
    (baseFeePerGas    : Nat)
    (prevRandao       : Evm.Hash32)
    (txs              : List Evm.Optimism.Bedrock.OpTx)
    (operatorParams   : OperatorFeeParams := { scalar := 0, constant := 0 })
    (withdrawalsCount : Nat := 0)
    (debugTrace       : Bool := false)
    (chainId          : Evm.U256 := 1) :
    Except String Evm.Optimism.Bedrock.BlockResult := do
  if withdrawalsCount ≠ 0 then
    .error s!"Isthmus blocks must have empty withdrawals (got {withdrawalsCount})"
  -- Drive the tx loop ourselves so we can apply the operator fee
  -- PER USER TX (vs. a block-bulk approximation that mis-credits when
  -- gas distribution is uneven across txs).
  let rec go (st : Evm.Frontier.State) (gasAcc : Nat)
             (logsAcc : List Evm.Frontier.Vm.Log)
             (xs : List Evm.Optimism.Bedrock.OpTx) :
      Except String Evm.Optimism.Bedrock.BlockResult :=
    match xs with
    | [] => .ok { state := st, gasUsed := gasAcc, logs := logsAcc }
    | Evm.Optimism.Bedrock.OpTx.deposited dtx :: rest => do
      let am : Message → Environment → Except Exception Evm :=
        fun msg env =>
          isthmusApplyMessage msg
            { env with
                opBn256PairingCap   := some Evm.Optimism.Granite.Spec.maxPairingInputSize
                opP256VerifyGas     := Evm.Optimism.Fjord.Spec.p256VerifyGasAt .isthmus
                pragueDelegation    := true
                debugTrace          := debugTrace }
      let r ← Evm.Optimism.Bedrock.processDepositedTx st blockHashes
                coinbase number gasLimit timestamp baseFeePerGas
                prevRandao dtx am
      go r.state (gasAcc + r.gasUsed) (logsAcc ++ r.logs) rest
    | Evm.Optimism.Bedrock.OpTx.userWithAuths u auths :: rest => do
      -- EIP-7702 set-code tx: processUserTx bumps the sender nonce
      -- FIRST and then applies the authorization list (matters when
      -- sender == authority — common pattern).
      let am : Message → Environment → Except Exception Evm :=
        fun msg env =>
          isthmusApplyMessage msg
            { env with
                opBn256PairingCap   := some Evm.Optimism.Granite.Spec.maxPairingInputSize
                opP256VerifyGas     := Evm.Optimism.Fjord.Spec.p256VerifyGasAt .isthmus
                pragueDelegation    := true
                debugTrace          := debugTrace }
      -- EIP-7702 intrinsic surcharge: PER_EMPTY_ACCOUNT_COST (= 25000)
      -- per authorization, charged upfront. Each authorization whose
      -- authority pre-existed earns a (25000 - 12500) = 12500 refund
      -- via the refund counter inside `applyAuthorizations`, subject
      -- to EIP-3529's gasUsed/5 cap. Matches go-ethereum
      -- `core/state_transition.go::IntrinsicGas`:
      --   gas += len(authList) * params.CallNewAccountGas
      let authIntrinsic := auths.length * 25000
      let r ← Evm.Optimism.Bedrock.processUserTx st blockHashes
                coinbase number gasLimit timestamp baseFeePerGas
                prevRandao u am (eip3860 := true) (chainId := chainId)
                (eip7623 := true) (authIntrinsic := authIntrinsic)
                (auths := auths)
      let opFee := operatorFeeWei operatorParams r.gasUsed
      let stateWithOpFee :=
        if opFee = 0 then r.state
        else r.state.addBalance operatorFeeVault (Evm.U256.ofNat opFee)
      go stateWithOpFee (gasAcc + r.gasUsed) (logsAcc ++ r.logs) rest
    | Evm.Optimism.Bedrock.OpTx.user u :: rest => do
      -- Wrap pragueApplyMessage to seed all OP env-level config.
      let am : Message → Environment → Except Exception Evm :=
        fun msg env =>
          isthmusApplyMessage msg
            { env with
                opBn256PairingCap   := some Evm.Optimism.Granite.Spec.maxPairingInputSize
                opP256VerifyGas     := Evm.Optimism.Fjord.Spec.p256VerifyGasAt .isthmus
                pragueDelegation    := true
                debugTrace          := debugTrace }
      let r ← Evm.Optimism.Bedrock.processUserTx st blockHashes
                coinbase number gasLimit timestamp baseFeePerGas
                prevRandao u am (eip3860 := true) (chainId := chainId)
                (eip7623 := true)
      -- Operator-fee credit, per-tx, using THIS tx's gasUsed.
      let opFee := operatorFeeWei operatorParams r.gasUsed
      let stateWithOpFee :=
        if opFee = 0 then r.state
        else r.state.addBalance operatorFeeVault (Evm.U256.ofNat opFee)
      go stateWithOpFee (gasAcc + r.gasUsed) (logsAcc ++ r.logs) rest
  go state 0 [] txs

end Evm.Optimism.Isthmus
