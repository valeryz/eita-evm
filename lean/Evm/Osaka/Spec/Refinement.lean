/-
  Evm.Osaka.Spec.Refinement — proofs that the Osaka Effect interpreter
  refines the Osaka Spec relations.

  Osaka adds:

    * `ClzStep.lean`        — EIP-7939 0x1e CLZ (count leading zeros).
    * `GasCap.lean`         — EIP-7825 tx-gas cap + EIP-7892 blob count.
    * `ModexpGas.lean`      — EIP-7823 + EIP-7883 MODEXP delta.
    * `P256VerifyStep.lean` — EIP-7951 P256VERIFY precompile (0x100).

  CLZ is a unary op (closes via `runUnary_sound` once the impl
  exposes a Handler-shaped `Instructions.clz`); the rest are
  tx-validity / precompile relations. All deferred per methodology.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Osaka.Spec.ClzStep
import Mathlib.Data.Nat.Size
import Evm.Osaka.Spec.GasCap
import Evm.Osaka.Spec.ModexpGas
import Evm.Osaka.Spec.P256VerifyStep
import Evm.Osaka.Vm.Effect
import Evm.Frontier.Vm.Tx

namespace Evm.Osaka.Spec.Refinement

open Evm.Frontier.Vm
open Evm.Osaka.Spec

/-! ## EIP-7939 CLZ (0x1e) -/

/-- The implementation's shift loop counts `Nat.size`. -/
theorem bitLengthAux_eq (n acc : Nat) :
    Evm.Osaka.Vm.Effect.bitLengthAux n acc = acc + Nat.size n := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    rcases n with _ | m
    · simp [Evm.Osaka.Vm.Effect.bitLengthAux]
    · rw [Evm.Osaka.Vm.Effect.bitLengthAux, ih _ (by rw [Nat.shiftRight_one]; omega)]
      have h := Nat.size_bit (b := (m+1).testBit 0) (n := (m+1) >>> 1)
        (by rw [Nat.bit_testBit_zero_shiftRight_one]; omega)
      rw [Nat.bit_testBit_zero_shiftRight_one] at h
      rw [h]; simp only [Nat.succ_eq_add_one] at *; omega

/-- The implementation's CLZ word function is EELS's `256 - bit_length`. -/
theorem clzU256_eq (x : Evm.U256) :
    Evm.Osaka.Vm.Effect.clzU256 x = Evm.Osaka.Spec.clzU256 x := by
  unfold Evm.Osaka.Vm.Effect.clzU256 Evm.Osaka.Spec.clzU256
  rw [bitLengthAux_eq, Nat.zero_add]

/-- 0x1E CLZ refines `IsClzStep`: pop `x`, charge `GAS_LOW` (`OPCODE_CLZ`), push
    `256 - bit_length(x)`. EELS `forks/osaka/vm/instructions/bitwise.py::
    count_leading_zeros` 248-274. Stated on `doClz`, the handler Osaka's `step1`
    dispatches 0x1E to. -/
theorem clz_sound (evm evm' : Evm) :
    Evm.Osaka.Vm.Effect.doClz evm = .continue evm' →
    IsClzStep evm evm' := by
  intro h
  unfold Evm.Osaka.Vm.Effect.doClz at h
  split at h
  · exact absurd h (by simp)
  · rename_i x rest hp
    split at h
    · exact absurd h (by simp)
    · rename_i g hg
      split at h
      · exact absurd h (by simp)
      · rename_i s hs
        obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
        obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
        obtain ⟨hlt, rfl⟩ := (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hs
        simp only [Evm.Byzantium.Vm.Effect.StepResult.continue.injEq] at h
        subst h
        refine ⟨x, rest, hStack, hlt, hle, ?_⟩
        rw [clzU256_eq]

/-! ## EIP-7825 / EIP-7892 tx validity caps -/

/-- EIP-7825: an Osaka+ (`k ≥ 18`) tx the tx layer accepts declares at most
    `TX_MAX_GAS_LIMIT` gas. EELS `forks/osaka/transactions.py::validate_transaction` 585
    (`if tx.gas > TX_MAX_GAS_LIMIT: raise TransactionGasLimitExceededError`). -/
theorem validTxGasCap_sound (k : Nat) (benv : Environment) (st : Evm.Frontier.State)
    (sender : Evm.Address) (t : Evm.Prague.Transaction) :
    Evm.Frontier.Vm.Tx.invalid k benv st sender (Evm.Frontier.Vm.Tx.ofPrague t) = none →
    k ≥ 18 → IsValidTxGasCap t := by
  intro h hk
  have hr := Evm.Frontier.Vm.Tx.rules_false_of_valid h
    (decide (k ≥ 18 ∧ (Evm.Frontier.Vm.Tx.ofPrague t).gas > 16777216),
      "gas above TX_MAX_GAS_LIMIT") (by simp [Evm.Frontier.Vm.Tx.rules])
  simp only [hk, true_and, decide_eq_false_iff_not, Nat.not_lt] at hr
  unfold IsValidTxGasCap txMaxGasLimit
  cases t <;> simpa [Evm.Frontier.Vm.Tx.ofPrague, Evm.Prague.Transaction.gasLimit] using hr

/-- EIP-7594 / EIP-7892 per-tx blob cap: an Osaka+ tx the tx layer accepts carries at most
    `BLOB_COUNT_LIMIT` (6) blobs. EELS `forks/osaka/fork.py::check_transaction` 510
    (`if blob_count > BLOB_COUNT_LIMIT: raise BlobCountExceededError`). -/
theorem validBlobCount_sound (k : Nat) (benv : Environment) (st : Evm.Frontier.State)
    (sender : Evm.Address) (t : Evm.Prague.Transaction) :
    Evm.Frontier.Vm.Tx.invalid k benv st sender (Evm.Frontier.Vm.Tx.ofPrague t) = none →
    k ≥ 18 → IsValidBlobCount t := by
  intro h hk
  have hr := Evm.Frontier.Vm.Tx.rules_false_of_valid h
    (decide ((Evm.Frontier.Vm.Tx.ofPrague t).type = 3 ∧ k ≥ 18 ∧
      (Evm.Frontier.Vm.Tx.ofPrague t).blobHashes.length > 6), "too many blobs")
    (by simp [Evm.Frontier.Vm.Tx.rules])
  unfold IsValidBlobCount blobCountLimit
  cases t <;> simp_all [Evm.Frontier.Vm.Tx.ofPrague, Evm.Prague.Transaction.blobCount]

/-! ## EIP-7823 + EIP-7883 MODEXP delta -/

/-- EIP-7823: a successful Osaka MODEXP (`modexp7883`, the 0x05 entry of
    `Call.precompiles` from Osaka) read operand lengths of at most 1024 bytes each. EELS
    `forks/osaka/vm/precompiled_contracts/modexp.py` 32-40 (`if base_length > U256(1024):
    raise ExceptionalHalt`, same for exp / modulus); the lengths are the input's first
    three 32-byte words. -/
theorem validModexpInput_sound (input : Evm.Bytes) (gas : Nat) (out : Evm.Bytes × Nat)
    (baseLen expLen modLen : Nat)
    (hb : Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input 0 32 = baseLen)
    (he : Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input 32 32 = expLen)
    (hm : Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input 64 32 = modLen) :
    Evm.Osaka.Vm.PrecompiledContracts.modexp7883 input gas = .ok out →
    IsValidModexpInput baseLen expLen modLen := by
  intro h
  subst hb he hm
  unfold Evm.Osaka.Vm.PrecompiledContracts.modexp7883 at h
  unfold IsValidModexpInput maxModexpOperandLen
  simp only at h
  split at h
  · simp at h
  · rename_i hc
    simp only [Evm.Osaka.Vm.PrecompiledContracts.maxModexpOperandLen] at hc
    omega

/-! ## EIP-7951 P256VERIFY precompile (0x100) -/

/-- P256VERIFY precompile success / failure both encoded in
    `IsP256VerifyStep verify input gas output gasOut`. The crypto
    verifier `verify` is a `Bytes → Bool` external parameter; the
    spec captures the gas / output-shape obligations. OPEN on purpose: the Lean
    precompile is a stub that rejects every signature
    (`Evm.Osaka.Vm.PrecompiledContracts.p256verify_stub_rejects`); a proof against it
    would certify the stub. Closes when Lean has SECP256R1 verification. -/
theorem p256Verify_sound_shape
    (verify : Evm.Bytes → Bool)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gasOut : Nat) :
    IsP256VerifyStep verify input gas output gasOut →
    IsP256VerifyStep verify input gas output gasOut := by
  intro h; exact h

/-! ## Notes

    - ModexpGas.lean exposes formulas (`modexpComplexity`,
      `modexpExpLengthPart`, `modexpGasFinal`) but no `IsXxx`
      predicate — they're consumed by an EIP-7883 MODEXP refinement
      that lives wherever the Osaka MODEXP impl lands. We state no
      theorem here; the file's content is constants + helpers.

    - The P256VERIFY impl currently stubs the cryptographic
      verifier (returns empty output; `p256verify_stub_rejects`).
      Its obligation stays open rather than being proved with
      `verify _ = false`. -/

end Evm.Osaka.Spec.Refinement
