/-
  Evm.Shanghai.Spec.Refinement — proofs that the Shanghai Effect
  interpreter refines the Shanghai Spec relations.

  Shanghai adds:

    * `Push0Step.lean`     — EIP-3855 0x5f PUSH0.
    * `InitcodeCap.lean`   — EIP-3860 init-code size cap + per-word
                               surcharge (CREATE/CREATE2/tx-CREATE).
    * `WarmCoinbase.lean`  — EIP-3651 pre-warmed coinbase.

  PUSH0 is a NullaryPushStep over the constant 0; the rest are
  cross-cutting state-machine deltas. All `sorry`-deferred per
  methodology.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Byzantium.Spec.Refinement
import Evm.Shanghai.Spec.Push0Step
import Evm.Shanghai.Spec.InitcodeCap
import Evm.Shanghai.Spec.WarmCoinbase
import Evm.Shanghai.Vm.Effect
import Evm.Frontier.Vm.Tx

namespace Evm.Shanghai.Spec.Refinement

open Evm.Frontier (State)
open Evm.Frontier.Vm
open Evm.Shanghai.Spec

/-! ## EIP-3855 PUSH0 (0x5f) -/

/-- PUSH0 (`doPush0`, the 0x5f arm of `Shanghai.Vm.Effect.step1`) is a nullary push of 0
    at `GAS_BASE`. EELS `forks/shanghai/vm/instructions/stack.py::push_n` (48-) with
    `num_bytes = 0`. -/
theorem push0_sound (evm evm' : Evm) :
    Evm.Shanghai.Vm.Effect.doPush0 evm = .continue evm' →
    IsPush0Step evm evm' := by
  unfold Evm.Shanghai.Vm.Effect.doPush0 Evm.Shanghai.Vm.Effect.push0Cost
  exact Evm.Byzantium.Spec.Refinement.stepNullaryPush_sound Gas.base (fun _ => 0) evm evm'

/-! ## EIP-3860 init-code cap + per-word surcharge -/

/-- EIP-3860 at the tx: a creating tx the tx layer accepts at Shanghai+ (`k ≥ 15`) has
    init code within `MAX_INIT_CODE_SIZE`. EELS `forks/shanghai/fork.py::
    validate_transaction` (`if tx.to == Bytes0(b"") and len(tx.data) > MAX_INIT_CODE_SIZE:
    raise InvalidTransaction`). -/
theorem initcodeWithinCap_tx_sound (k : Nat) (benv : Environment) (st : State)
    (sender : Evm.Address) (tx : Evm.Frontier.Vm.Tx.Tx) :
    Evm.Frontier.Vm.Tx.invalid k benv st sender tx = none → k ≥ 15 → tx.to = none →
    InitcodeWithinCap tx.data.size := by
  intro h hk hto
  have hr := Evm.Frontier.Vm.Tx.rules_false_of_valid h
    (decide (k ≥ 15 ∧ tx.to.isNone ∧ tx.data.size > Evm.Frontier.Vm.Create.maxInitCodeSize),
      "init code size") (by simp [Evm.Frontier.Vm.Tx.rules])
  simp [hk, hto] at hr
  unfold InitcodeWithinCap maxInitCodeSize
  simpa [Evm.Frontier.Vm.Create.maxInitCodeSize] using hr

/-- EIP-3860 at CREATE / CREATE2: when `Create.start` (EELS `generic_create`) gets past the
    charge under the EIP-3860 rules, the init code is within the cap. EELS
    `forks/shanghai/vm/instructions/system.py::create` (`if memory_size >
    MAX_INIT_CODE_SIZE: raise OutOfGasError`). -/
theorem initcodeWithinCap_create_sound (r : Evm.Frontier.Vm.Create.Rules) (evm : Evm)
    (value : Evm.U256) (initCode : Evm.Bytes) (newAddr : Evm.Address) (base : Nat) :
    Evm.Frontier.Vm.Create.start r evm value initCode newAddr base ≠ .halt →
    r.eip3860 = true → InitcodeWithinCap initCode.size := by
  intro h h3
  unfold Evm.Frontier.Vm.Create.start at h
  unfold InitcodeWithinCap maxInitCodeSize
  by_cases hc : initCode.size > Evm.Frontier.Vm.Create.maxInitCodeSize
  · exfalso; apply h
    by_cases hg : evm.gasLeft < base
    · simp [hg]
    · simp [hg, h3, hc]
  · simpa [Evm.Frontier.Vm.Create.maxInitCodeSize] using hc

/-! EIP-4895 withdrawals: `Evm.Frontier.Vm.Block.processWithdrawals`, derived as
    `Evm.CL.EffectBlock` (`Evm.CL.EffectBlockProof.credits_refines`). -/

/-! ## EIP-3651 warm coinbase -/

/-- `Tx.ins` folds keep every element already collected and add every new one. -/
theorem mem_foldl_ins (l acc : List Evm.Address) (a : Evm.Address) :
    a ∈ acc ∨ a ∈ l → a ∈ l.foldl Evm.Frontier.Vm.Tx.ins acc := by
  induction l generalizing acc with
  | nil => intro h; simpa using h
  | cons x xs ih =>
    intro h
    apply ih
    unfold Evm.Frontier.Vm.Tx.ins
    rcases h with h | h
    · left; split <;> simp [h]
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · left; split <;> simp_all
      · right; exact h

/-- EIP-3651: at Shanghai+ (`k ≥ 15`) the message starts with the coinbase warm.
    EELS `forks/shanghai/fork.py::process_transaction` 566
    (`access_list_addresses.add(block_env.coinbase)`). -/
theorem warmCoinbaseInit_sound (k : Nat) (benv : Environment) (st : State)
    (sender : Evm.Address) (tx : Evm.Frontier.Vm.Tx.Tx) :
    k ≥ 15 →
    IsWarmCoinbaseInit benv.coinbase (Evm.Frontier.Vm.Tx.env0 k benv st sender tx) := by
  intro hk
  unfold IsWarmCoinbaseInit WarmCoinbase Evm.Frontier.Vm.Tx.env0
    Evm.Frontier.Vm.Tx.accessedSeed
  simp only [show k ≥ 10 from by omega, ite_true, List.contains_iff_mem]
  apply mem_foldl_ins
  right
  simp [Evm.Frontier.Vm.Tx.seedAddrs, hk]

/-! ## Notes

    - PUSH0 was the simplest opcode addition since Frontier; its
      refinement is a single-line shape-lemma invocation pending the
      `runNullaryPush_sound` plumbing.

    - The Shanghai `Effect.step1` for CREATE / CREATE2 should
      enforce `InitcodeWithinCap` and charge `initCodeCost` BEFORE
      yielding to the trampoline; the joint refinement against the
      EIP-3860 spec lives at the CREATE/CREATE2 dispatch.

    - Withdrawals are not transactions: their refinement is a fold,
      not a step relation. -/

end Evm.Shanghai.Spec.Refinement
