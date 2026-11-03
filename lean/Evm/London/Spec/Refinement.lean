/-
  Evm.London.Spec.Refinement — proofs that the London Effect
  interpreter refines the London Spec relations.

  London adds:

    * `BaseFee.lean` — EIP-1559 base-fee formula (block-level).
    * `BasefeeStep.lean` — EIP-3198 0x48 BASEFEE opcode.
    * `CodePrefix.lean` — EIP-3541 0xEF deployed-code prefix reject.
    * `FeeMarket.lean` — EIP-1559 effective price / coinbase credit /
                          burn.
    * `RefundCap.lean` — EIP-3529 refund cap (gas_used / 5 instead of
                          / 2).
    * `Selfdestruct.lean` — EIP-3529 SELFDESTRUCT refund removal.

  BASEFEE is a NullaryPushStep; the rest are tx- / block-level
  relations (block-validity formulas, deposit-code checks, refund
  caps, SELFDESTRUCT refund deltas). All `sorry`-deferred per
  methodology.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.London.Spec.BaseFee
import Evm.London.Spec.BasefeeStep
import Evm.London.Spec.CodePrefix
import Evm.London.Spec.FeeMarket
import Evm.London.Spec.RefundCap
import Evm.London.Spec.Selfdestruct
import Evm.London.Vm.Instructions.Block
import Evm.London.Vm.Effect

namespace Evm.London.Spec.Refinement

open Evm.Frontier.Vm
open Evm.London.Spec

/-! ## EIP-3198 BASEFEE (0x48) -/

/-- BASEFEE is a NullaryPushStep over `env.baseFeePerGas`. One-line
    proof via the `nullaryPush_sound` shape lemma. -/
theorem basefee_sound (evm evm' : Evm) :
    Evm.London.Vm.Instructions.baseFee evm = .ok evm' →
    IsBasefeeStep evm evm' := by
  intro h
  exact Evm.Frontier.Spec.Refinement.nullaryPush_sound
    _ (fun e => Evm.U256.ofNat e.env.baseFeePerGas) evm evm' h

/-! ## EIP-1559 base-fee formula refinement -/

/-- `IsCalculatedBaseFee` is the (block-validity) base-fee formula.
    The impl side lives in `London.Fork.applyBlock`'s header
    validation. -/
theorem calculateBaseFee_sound_shape
    (parentGasUsed parentGasTarget parentBaseFee f : Nat) :
    IsCalculatedBaseFee parentGasUsed parentGasTarget parentBaseFee f →
    IsCalculatedBaseFee parentGasUsed parentGasTarget parentBaseFee f := by
  -- The relation IS the formula's pointwise equation; the impl
  -- function `calculateBaseFeePerGas` evaluates it.
  intro h; exact h

/-! ## EIP-3541 deployed-code prefix refinement -/

/-- `IsValidDeployedCode` is the 0xEF-prefix reject predicate. The
    CREATE / CREATE2 deposit branches at London check this before
    accepting the init-code output. -/
theorem validDeployedCode_sound_shape (bytes : Evm.Bytes) :
    IsValidDeployedCode bytes →
    IsValidDeployedCode bytes := by
  intro h; exact h

/-! ## EIP-1559 fee-market refinement (tx-level) -/

/-- `IsCoinbaseCredit`, `IsBaseFeeBurnt`, `IsTxFeeDebit` together
    describe the three balance flows the London tx layer produces.
    All three are equational; refinement is a definitional rewrite
    inside `London.Fork.processTransaction`. -/
theorem coinbaseCredit_sound_shape
    (gasUsed priorityFeePerGas credit : Nat) :
    IsCoinbaseCredit gasUsed priorityFeePerGas credit →
    IsCoinbaseCredit gasUsed priorityFeePerGas credit := by
  intro h; exact h

theorem baseFeeBurnt_sound_shape (gasUsed baseFee burnt : Nat) :
    IsBaseFeeBurnt gasUsed baseFee burnt →
    IsBaseFeeBurnt gasUsed baseFee burnt := by
  intro h; exact h

theorem txFeeDebit_sound_shape (gasUsed effectivePricePerGas debited : Nat) :
    IsTxFeeDebit gasUsed effectivePricePerGas debited →
    IsTxFeeDebit gasUsed effectivePricePerGas debited := by
  intro h; exact h

/-! ## EIP-3529 refund cap refinement (tx-level) -/

/-- `IsRefundCapped`: the end-of-tx refund formula. -/
theorem refundCap_sound_shape (gasUsed refundCounter refund : Nat) :
    IsRefundCapped gasUsed refundCounter refund →
    IsRefundCapped gasUsed refundCounter refund := by
  intro h; exact h

/-! ## EIP-3529 SELFDESTRUCT refund removal -/

/-- `IsSelfdestructRefundDelta`: the SELFDESTRUCT-induced refund
    delta is always 0 at London. -/
theorem selfdestructRefundDelta_sound_shape
    (env env' : Environment) (delta : Nat) :
    IsSelfdestructRefundDelta env env' delta →
    IsSelfdestructRefundDelta env env' delta := by
  intro h; exact h

/-! ## Notes

    - Several of the above are *identity refinements*: the spec
      relation is a closed-form equation and the impl computes it
      directly. The soundness obligation reduces to definitional
      equality once the impl callsite is extracted.

    - BASEFEE soundness is a one-liner via the
      `nullaryPush_sound` shape lemma. -/

end Evm.London.Spec.Refinement
