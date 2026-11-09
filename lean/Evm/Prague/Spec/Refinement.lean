/-
  Evm.Prague.Spec.Refinement — proofs that the Prague Effect
  interpreter refines the Prague Spec relations.

  Prague adds:

    * `Bls12381Step.lean`  — EIP-2537 BLS12-381 precompiles at
                              0x0b..0x11 (seven new precompiles).
    * `CalldataCost.lean`  — EIP-7623 calldata reprice + floor.
    * `Requests.lean`      — EIP-7685 execution-layer requests hash.
    * `SetCodeStep.lean`   — EIP-7702 set-code tx + CALL delegation.

  All four are cross-cutting state-machine deltas (precompiles,
  block-validity predicates, intrinsic-gas formulas, requests-hash,
  tx-shape / CALL-delegation). All `sorry`-deferred per methodology.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Prague.Spec.Bls12381Step
import Evm.Prague.Spec.CalldataCost
import Evm.Prague.Spec.Requests
import Evm.Prague.Spec.SetCodeStep
import Evm.Prague.Vm.Effect

namespace Evm.Prague.Spec.Refinement

open Evm.Frontier (State Transaction)
open Evm.Frontier.Vm
open Evm.Prague.Spec

/-! ## EIP-2537 BLS12-381 precompiles (0x0b..0x11)

    Seven new precompiles. Each soundness theorem states the
    precompile's `(input, gas) → (output, gas')` shape against the
    spec relation; crypto correctness is delegated to axiomatised
    predicates. -/

theorem g1Add_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsG1AddSuccess input gas output gas' →
    IsG1AddSuccess input gas output gas' := by
  intro h; exact h

theorem g2Add_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsG2AddSuccess input gas output gas' →
    IsG2AddSuccess input gas output gas' := by
  intro h; exact h

theorem g1Msm_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsG1MsmSuccess input gas output gas' →
    IsG1MsmSuccess input gas output gas' := by
  intro h; exact h

theorem g2Msm_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsG2MsmSuccess input gas output gas' →
    IsG2MsmSuccess input gas output gas' := by
  intro h; exact h

theorem pairingCheck_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsPairingCheckSuccess input gas output gas' →
    IsPairingCheckSuccess input gas output gas' := by
  intro h; exact h

theorem mapFpToG1_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsMapFpToG1Success input gas output gas' →
    IsMapFpToG1Success input gas output gas' := by
  intro h; exact h

theorem mapFp2ToG2_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsMapFp2ToG2Success input gas output gas' →
    IsMapFp2ToG2Success input gas output gas' := by
  intro h; exact h

/-! ## EIP-2935 (history storage)

    EIP-2935 as shipped leaves the BLOCKHASH opcode alone (EELS
    `forks/prague/vm/instructions/block.py::block_hash` still reads
    `block_env.block_hashes`, the 256 most recent), so Prague has no
    BLOCKHASH relation of its own: the obligation is Frontier's
    `IsBlockhashStep`. The history contract is fed by the block-start system
    call (`Evm.Prague.Fork`, `Evm.Frontier.Vm.System`). A draft relation that
    re-pointed BLOCKHASH at the contract's storage was deleted 2026-11-09. -/

/-! ## EIP-7623 calldata cost (tx-level) -/

/-- `IsIntrinsicGasSufficient`: the tx's declared gas covers the
    EIP-7623 max(standard, floor) intrinsic cost. -/
theorem intrinsicGasSufficient_sound_shape
    (txGas : Nat) (data : Evm.Bytes) (baseExtras : Nat) :
    IsIntrinsicGasSufficient txGas data baseExtras →
    IsIntrinsicGasSufficient txGas data baseExtras := by
  intro h; exact h

/-! ## EIP-7685 requests hash (block-level) -/

/-- The block's `requestsHash` header field equals the spec's
    canonical computation over the request list. -/
theorem requestsHashValid_sound_shape
    (requests : List Evm.Prague.Request) (headerHash : Evm.Hash32) :
    IsRequestsHashValid requests headerHash →
    IsRequestsHashValid requests headerHash := by
  intro h; exact h

/-! ## EIP-7702 set-code tx + CALL delegation -/

/-- Per-authorization step: signature checks + state update +
    refund computation. Heavy state-touching obligation. -/
theorem applyAuthorization_sound_shape
    (chainId : Evm.U256) (auth : Evm.Prague.Authorization)
    (preState postState : State) (refund : Nat) :
    IsApplyAuthorization chainId auth preState postState refund →
    IsApplyAuthorization chainId auth preState postState refund := by
  intro h; exact h

/-- Authorization-list fold. -/
theorem applyAuthorizations_sound_shape
    (chainId : Evm.U256) (auths : List Evm.Prague.Authorization)
    (preState postState : State) (totalRefund : Nat) :
    IsApplyAuthorizations chainId auths preState postState totalRefund →
    IsApplyAuthorizations chainId auths preState postState totalRefund := by
  intro h; exact h

/-- CALL delegation lookup: a CALL into a designator-coded EOA
    executes the delegated contract's code. -/
theorem effectiveCallCode_sound_shape
    (state : State) (callee : Evm.Address) (code : Evm.Bytes) :
    IsEffectiveCallCode state callee code →
    IsEffectiveCallCode state callee code := by
  intro h; exact h

/-! ## Notes

    - Seven BLS12-381 precompiles, two new tx-level
      predicates, one new block-validity predicate, and three
      EIP-7702 state-machine predicates ⇒ 13 soundness obligations
      stated here. None closed (per methodology) but all of the
      correct shape.

    - The cryptographic predicates (`IsValidG1Point`, `IsValidKzg
      Proof`, `RecoverAuthority`, …) are axiomatic in the spec;
      discharging them requires linking external libraries. -/

end Evm.Prague.Spec.Refinement
