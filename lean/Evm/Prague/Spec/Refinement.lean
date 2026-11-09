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
  tx-shape / CALL-delegation).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Prague.Spec.Bls12381Step
import Evm.Prague.Spec.CalldataCost
import Evm.Prague.Spec.Requests
import Evm.Prague.Spec.SetCodeStep
import Evm.Prague.Vm.Effect
import Evm.CL.GasEmitPrague
import Evm.Frontier.Vm.Tx

namespace Evm.Prague.Spec.Refinement

open Evm.Frontier (State Transaction)
open Evm.Frontier.Vm
open Evm.Prague.Spec

/-! ## EIP-2537 BLS12-381 precompiles (0x0b..0x11)

    Each precompile `bls*With o` refines its EELS relation for EVERY oracle `o` (success
    and failure both); the replay's instance is `Evm.Crypto.Bls12381.native` (blst). -/

/-! ### The seven wrappers -/

/-- `blsG1AddWith` refines `IsG1AddSuccess` for every oracle `o`. -/
theorem g1Add_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    Evm.Prague.Vm.PrecompiledContracts.blsG1AddWith o input gas = .ok (output, gas') →
    IsG1AddSuccess o input gas output gas' := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsG1AddWith at h
  unfold IsG1AddSuccess
  have e0 : g1PointSize = 128 := rfl
  have e1 : gasG1Add = Evm.Prague.Vm.PrecompiledContracts.gasG1Add := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size ≠ 256
  · simp only [c1, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte, reduceCtorEq] at h
  simp only [c1, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte] at h
  by_cases c2 : gas < Evm.Prague.Vm.PrecompiledContracts.gasG1Add
  · simp only [c2, ↓reduceIte, reduceCtorEq] at h
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.g1Decode input 0 with
  | none => simp only [ha, reduceCtorEq] at h
  | some a =>
    cases hb : Evm.Crypto.Bls12381.g1Decode input 128 with
    | none => simp only [ha, hb, reduceCtorEq] at h
    | some b =>
      simp only [ha, hb, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, by omega, a, b, rfl, rfl, rfl, rfl⟩

/-- `blsG1AddWith`'s exceptional halts are exactly `IsG1AddFailure`, for every oracle `o`. -/
theorem g1Add_failure_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (e : Evm.Frontier.Vm.Exception) :
    Evm.Prague.Vm.PrecompiledContracts.blsG1AddWith o input gas = .error e →
    IsG1AddFailure input gas := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsG1AddWith at h
  unfold IsG1AddFailure
  have e0 : g1PointSize = 128 := rfl
  have e1 : gasG1Add = Evm.Prague.Vm.PrecompiledContracts.gasG1Add := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size ≠ 256
  · omega
  simp only [c1, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte] at h
  by_cases c2 : gas < Evm.Prague.Vm.PrecompiledContracts.gasG1Add
  · exact Or.inr (Or.inl c2)
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.g1Decode input 0 with
  | none => exact Or.inr (Or.inr (Or.inl rfl))
  | some a =>
    cases hb : Evm.Crypto.Bls12381.g1Decode input 128 with
    | none => exact Or.inr (Or.inr (Or.inr rfl))
    | some b => simp only [ha, hb, reduceCtorEq] at h

/-- `blsG2AddWith` refines `IsG2AddSuccess` for every oracle `o`. -/
theorem g2Add_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    Evm.Prague.Vm.PrecompiledContracts.blsG2AddWith o input gas = .ok (output, gas') →
    IsG2AddSuccess o input gas output gas' := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsG2AddWith at h
  unfold IsG2AddSuccess
  have e0 : g2PointSize = 256 := rfl
  have e1 : gasG2Add = Evm.Prague.Vm.PrecompiledContracts.gasG2Add := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size ≠ 512
  · simp only [c1, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte, reduceCtorEq] at h
  simp only [c1, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte] at h
  by_cases c2 : gas < Evm.Prague.Vm.PrecompiledContracts.gasG2Add
  · simp only [c2, ↓reduceIte, reduceCtorEq] at h
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.g2Decode input 0 with
  | none => simp only [ha, reduceCtorEq] at h
  | some a =>
    cases hb : Evm.Crypto.Bls12381.g2Decode input 256 with
    | none => simp only [ha, hb, reduceCtorEq] at h
    | some b =>
      simp only [ha, hb, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, by omega, a, b, rfl, rfl, rfl, rfl⟩

/-- `blsG2AddWith`'s exceptional halts are exactly `IsG2AddFailure`, for every oracle `o`. -/
theorem g2Add_failure_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (e : Evm.Frontier.Vm.Exception) :
    Evm.Prague.Vm.PrecompiledContracts.blsG2AddWith o input gas = .error e →
    IsG2AddFailure input gas := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsG2AddWith at h
  unfold IsG2AddFailure
  have e0 : g2PointSize = 256 := rfl
  have e1 : gasG2Add = Evm.Prague.Vm.PrecompiledContracts.gasG2Add := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size ≠ 512
  · omega
  simp only [c1, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte] at h
  by_cases c2 : gas < Evm.Prague.Vm.PrecompiledContracts.gasG2Add
  · exact Or.inr (Or.inl c2)
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.g2Decode input 0 with
  | none => exact Or.inr (Or.inr (Or.inl rfl))
  | some a =>
    cases hb : Evm.Crypto.Bls12381.g2Decode input 256 with
    | none => exact Or.inr (Or.inr (Or.inr rfl))
    | some b => simp only [ha, hb, reduceCtorEq] at h

/-- `blsG1MsmWith` refines `IsG1MsmSuccess` for every oracle `o`. -/
theorem g1Msm_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    Evm.Prague.Vm.PrecompiledContracts.blsG1MsmWith o input gas = .ok (output, gas') →
    IsG1MsmSuccess o input gas output gas' := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsG1MsmWith at h
  unfold IsG1MsmSuccess
  have e0 : g1MsmGas (input.size / g1MsmPairSize) = Evm.CL.GasEmit.blsG1MsmGas input.size := rfl
  have e1 : g1MsmPairSize = 160 := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size = 0 ∨ input.size % 160 ≠ 0
  · simp only [c1, ↓reduceIte, reduceCtorEq] at h
  simp only [c1, ↓reduceIte] at h
  by_cases c2 : gas < Evm.CL.GasEmit.blsG1MsmGas input.size
  · simp only [c2, ↓reduceIte, reduceCtorEq] at h
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.g1MsmPairs o input (input.size / 160) with
  | none => simp only [ha, reduceCtorEq] at h
  | some a =>
    simp only [ha, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega, by omega, a, rfl, rfl, rfl⟩

/-- `blsG1MsmWith`'s exceptional halts are exactly `IsG1MsmFailure`, for every oracle `o`. -/
theorem g1Msm_failure_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (e : Evm.Frontier.Vm.Exception) :
    Evm.Prague.Vm.PrecompiledContracts.blsG1MsmWith o input gas = .error e →
    IsG1MsmFailure o input gas := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsG1MsmWith at h
  unfold IsG1MsmFailure
  have e0 : g1MsmGas (input.size / g1MsmPairSize) = Evm.CL.GasEmit.blsG1MsmGas input.size := rfl
  have e1 : g1MsmPairSize = 160 := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size = 0 ∨ input.size % 160 ≠ 0
  · omega
  simp only [c1, ↓reduceIte] at h
  by_cases c2 : gas < Evm.CL.GasEmit.blsG1MsmGas input.size
  · exact Or.inr (Or.inr (Or.inl c2))
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.g1MsmPairs o input (input.size / 160) with
  | none => exact Or.inr (Or.inr (Or.inr rfl))
  | some a => simp only [ha, reduceCtorEq] at h

/-- `blsG2MsmWith` refines `IsG2MsmSuccess` for every oracle `o`. -/
theorem g2Msm_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    Evm.Prague.Vm.PrecompiledContracts.blsG2MsmWith o input gas = .ok (output, gas') →
    IsG2MsmSuccess o input gas output gas' := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsG2MsmWith at h
  unfold IsG2MsmSuccess
  have e0 : g2MsmGas (input.size / g2MsmPairSize) = Evm.CL.GasEmit.blsG2MsmGas input.size := rfl
  have e1 : g2MsmPairSize = 288 := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size = 0 ∨ input.size % 288 ≠ 0
  · simp only [c1, ↓reduceIte, reduceCtorEq] at h
  simp only [c1, ↓reduceIte] at h
  by_cases c2 : gas < Evm.CL.GasEmit.blsG2MsmGas input.size
  · simp only [c2, ↓reduceIte, reduceCtorEq] at h
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.g2MsmPairs o input (input.size / 288) with
  | none => simp only [ha, reduceCtorEq] at h
  | some a =>
    simp only [ha, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega, by omega, a, rfl, rfl, rfl⟩

/-- `blsG2MsmWith`'s exceptional halts are exactly `IsG2MsmFailure`, for every oracle `o`. -/
theorem g2Msm_failure_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (e : Evm.Frontier.Vm.Exception) :
    Evm.Prague.Vm.PrecompiledContracts.blsG2MsmWith o input gas = .error e →
    IsG2MsmFailure o input gas := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsG2MsmWith at h
  unfold IsG2MsmFailure
  have e0 : g2MsmGas (input.size / g2MsmPairSize) = Evm.CL.GasEmit.blsG2MsmGas input.size := rfl
  have e1 : g2MsmPairSize = 288 := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size = 0 ∨ input.size % 288 ≠ 0
  · omega
  simp only [c1, ↓reduceIte] at h
  by_cases c2 : gas < Evm.CL.GasEmit.blsG2MsmGas input.size
  · exact Or.inr (Or.inr (Or.inl c2))
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.g2MsmPairs o input (input.size / 288) with
  | none => exact Or.inr (Or.inr (Or.inr rfl))
  | some a => simp only [ha, reduceCtorEq] at h

/-- `blsPairingWith` refines `IsPairingCheckSuccess` for every oracle `o`. -/
theorem pairingCheck_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    Evm.Prague.Vm.PrecompiledContracts.blsPairingWith o input gas = .ok (output, gas') →
    IsPairingCheckSuccess o input gas output gas' := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsPairingWith at h
  unfold IsPairingCheckSuccess
  have e0 : pairingGas (input.size / pairingPairSize) = Evm.Prague.Vm.PrecompiledContracts.gasPairingBase + input.size / 384 * Evm.Prague.Vm.PrecompiledContracts.gasPairingPair := rfl
  have e1 : pairingPairSize = 384 := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size = 0 ∨ input.size % 384 ≠ 0
  · simp only [c1, ↓reduceIte, reduceCtorEq] at h
  simp only [c1, ↓reduceIte] at h
  by_cases c2 : gas < Evm.Prague.Vm.PrecompiledContracts.gasPairingBase + input.size / 384 * Evm.Prague.Vm.PrecompiledContracts.gasPairingPair
  · simp only [c2, ↓reduceIte, reduceCtorEq] at h
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.pairingPairs o input (input.size / 384) with
  | none => simp only [ha, reduceCtorEq] at h
  | some a =>
    simp only [ha, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega, by omega, a, rfl, rfl, rfl⟩

/-- `blsPairingWith`'s exceptional halts are exactly `IsPairingCheckFailure`, for every oracle `o`. -/
theorem pairingCheck_failure_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (e : Evm.Frontier.Vm.Exception) :
    Evm.Prague.Vm.PrecompiledContracts.blsPairingWith o input gas = .error e →
    IsPairingCheckFailure o input gas := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsPairingWith at h
  unfold IsPairingCheckFailure
  have e0 : pairingGas (input.size / pairingPairSize) = Evm.Prague.Vm.PrecompiledContracts.gasPairingBase + input.size / 384 * Evm.Prague.Vm.PrecompiledContracts.gasPairingPair := rfl
  have e1 : pairingPairSize = 384 := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size = 0 ∨ input.size % 384 ≠ 0
  · omega
  simp only [c1, ↓reduceIte] at h
  by_cases c2 : gas < Evm.Prague.Vm.PrecompiledContracts.gasPairingBase + input.size / 384 * Evm.Prague.Vm.PrecompiledContracts.gasPairingPair
  · exact Or.inr (Or.inr (Or.inl c2))
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.pairingPairs o input (input.size / 384) with
  | none => exact Or.inr (Or.inr (Or.inr rfl))
  | some a => simp only [ha, reduceCtorEq] at h

/-- `blsMapFpToG1With` refines `IsMapFpToG1Success` for every oracle `o`. -/
theorem mapFpToG1_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    Evm.Prague.Vm.PrecompiledContracts.blsMapFpToG1With o input gas = .ok (output, gas') →
    IsMapFpToG1Success o input gas output gas' := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsMapFpToG1With at h
  unfold IsMapFpToG1Success
  have e0 : fpSize = 64 := rfl
  have e1 : gasMapFpToG1 = Evm.Prague.Vm.PrecompiledContracts.gasMapFpToG1 := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size ≠ 64
  · simp only [c1, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte, reduceCtorEq] at h
  simp only [c1, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte] at h
  by_cases c2 : gas < Evm.Prague.Vm.PrecompiledContracts.gasMapFpToG1
  · simp only [c2, ↓reduceIte, reduceCtorEq] at h
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.fpDecode input 0 with
  | none => simp only [ha, reduceCtorEq] at h
  | some a =>
    simp only [ha, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega, a, rfl, rfl, rfl⟩

/-- `blsMapFpToG1With`'s exceptional halts are exactly `IsMapFpToG1Failure`, for every oracle `o`. -/
theorem mapFpToG1_failure_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (e : Evm.Frontier.Vm.Exception) :
    Evm.Prague.Vm.PrecompiledContracts.blsMapFpToG1With o input gas = .error e →
    IsMapFpToG1Failure input gas := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsMapFpToG1With at h
  unfold IsMapFpToG1Failure
  have e0 : fpSize = 64 := rfl
  have e1 : gasMapFpToG1 = Evm.Prague.Vm.PrecompiledContracts.gasMapFpToG1 := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size ≠ 64
  · omega
  simp only [c1, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte] at h
  by_cases c2 : gas < Evm.Prague.Vm.PrecompiledContracts.gasMapFpToG1
  · exact Or.inr (Or.inl c2)
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.fpDecode input 0 with
  | none => exact Or.inr (Or.inr rfl)
  | some a => simp only [ha, reduceCtorEq] at h

/-- `blsMapFp2ToG2With` refines `IsMapFp2ToG2Success` for every oracle `o`. -/
theorem mapFp2ToG2_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    Evm.Prague.Vm.PrecompiledContracts.blsMapFp2ToG2With o input gas = .ok (output, gas') →
    IsMapFp2ToG2Success o input gas output gas' := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsMapFp2ToG2With at h
  unfold IsMapFp2ToG2Success
  have e0 : fp2Size = 128 := rfl
  have e1 : gasMapFp2ToG2 = Evm.Prague.Vm.PrecompiledContracts.gasMapFp2ToG2 := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size ≠ 128
  · simp only [c1, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte, reduceCtorEq] at h
  simp only [c1, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte] at h
  by_cases c2 : gas < Evm.Prague.Vm.PrecompiledContracts.gasMapFp2ToG2
  · simp only [c2, ↓reduceIte, reduceCtorEq] at h
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.fp2Decode input 0 with
  | none => simp only [ha, reduceCtorEq] at h
  | some a =>
    simp only [ha, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega, a, rfl, rfl, rfl⟩

/-- `blsMapFp2ToG2With`'s exceptional halts are exactly `IsMapFp2ToG2Failure`, for every oracle `o`. -/
theorem mapFp2ToG2_failure_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (e : Evm.Frontier.Vm.Exception) :
    Evm.Prague.Vm.PrecompiledContracts.blsMapFp2ToG2With o input gas = .error e →
    IsMapFp2ToG2Failure input gas := by
  intro h
  unfold Evm.Prague.Vm.PrecompiledContracts.blsMapFp2ToG2With at h
  unfold IsMapFp2ToG2Failure
  have e0 : fp2Size = 128 := rfl
  have e1 : gasMapFp2ToG2 = Evm.Prague.Vm.PrecompiledContracts.gasMapFp2ToG2 := rfl
  try dsimp only
  rw [e0, e1]
  by_cases c1 : input.size ≠ 128
  · omega
  simp only [c1, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte] at h
  by_cases c2 : gas < Evm.Prague.Vm.PrecompiledContracts.gasMapFp2ToG2
  · exact Or.inr (Or.inl c2)
  simp only [c2, ↓reduceIte] at h
  cases ha : Evm.Crypto.Bls12381.fp2Decode input 0 with
  | none => exact Or.inr (Or.inr rfl)
  | some a => simp only [ha, reduceCtorEq] at h

/-! ## EIP-2935 (history storage)

    EIP-2935 as shipped leaves the BLOCKHASH opcode alone (EELS
    `forks/prague/vm/instructions/block.py::block_hash` still reads
    `block_env.block_hashes`, the 256 most recent), so Prague has no
    BLOCKHASH relation of its own: the obligation is Frontier's
    `IsBlockhashStep`. The history contract is fed by the block-start system
    call (`Evm.Prague.Fork`, `Evm.Frontier.Vm.System`). A draft relation that
    re-pointed BLOCKHASH at the contract's storage was deleted 2026-11-09. -/

/-! ## EIP-7623 calldata cost (tx-level) -/

/-- EIP-7623 (+ EIP-7702's per-authorization cost): a Prague+ (`k ≥ 17`) tx the tx
    layer accepts (`Tx.invalid = none`) declares at least `max(regular,
    calldata_floor)`, with the regular cost's extras read off the tx (creation,
    access list, authorizations). EELS `forks/prague/transactions.py::
    validate_transaction` 578-579 and `calculate_intrinsic_cost` 594-660. The
    implementation's costs are the emitted `GasEmit` formulas, equal to the spec's
    by `Evm.CL.GasEmitPrague`. -/
theorem intrinsicGasSufficient_sound (k : Nat) (hk : 17 ≤ k) (benv : Environment)
    (st : Evm.Frontier.State) (sender : Evm.Address) (tx : Evm.Frontier.Vm.Tx.Tx)
    (extras : Nat)
    (hx : extras = baseExtras tx.to.isNone tx.data.size tx.accessList.length
      (tx.accessList.map (·.2.length)).sum tx.auths.length) :
    Evm.Frontier.Vm.Tx.invalid k benv st sender tx = none →
    IsIntrinsicGasSufficient tx.gas tx.data extras := by
  intro h
  subst hx
  have hr := Evm.Frontier.Vm.Tx.rules_false_of_valid h
    (decide (max (Evm.Frontier.Vm.Tx.intrinsic k tx) (Evm.Frontier.Vm.Tx.floor k tx) > tx.gas),
      "intrinsic gas") (by simp [Evm.Frontier.Vm.Tx.rules])
  simp only [decide_eq_false_iff_not, Nat.not_lt] at hr
  have hf : (Evm.Frontier.Vm.Tx.gasEnv k tx) "fork-ord" = k := by
    simp [Evm.Frontier.Vm.Tx.gasEnv]
  have hfl := Evm.CL.GasEmitPrague.calldataFloor_eq_spec (Evm.Frontier.Vm.Tx.gasEnv k tx)
    (by rw [hf]; exact hk)
  have hz : (Evm.Frontier.Vm.Tx.gasEnv k tx) "zero-bytes" =
      Evm.Frontier.Vm.Tx.zeroBytes tx.data := by simp [Evm.Frontier.Vm.Tx.gasEnv]
  have hnz : (Evm.Frontier.Vm.Tx.gasEnv k tx) "nonzero-bytes" =
      tx.data.size - Evm.Frontier.Vm.Tx.zeroBytes tx.data := by
    simp [Evm.Frontier.Vm.Tx.gasEnv]
  have hdl : (Evm.Frontier.Vm.Tx.gasEnv k tx) "data-len" = tx.data.size := by
    simp [Evm.Frontier.Vm.Tx.gasEnv]
  have hal : (Evm.Frontier.Vm.Tx.gasEnv k tx) "al-addrs" = tx.accessList.length := by
    simp [Evm.Frontier.Vm.Tx.gasEnv]
  have hak : (Evm.Frontier.Vm.Tx.gasEnv k tx) "al-keys" =
      (tx.accessList.map (·.2.length)).sum := by simp [Evm.Frontier.Vm.Tx.gasEnv]
  rw [hz, hnz] at hfl
  unfold IsIntrinsicGasSufficient countBytes intrinsicCost
  simp only [Evm.Frontier.Vm.Tx.intrinsic, Evm.Frontier.Vm.Tx.floor, hfl, hz, hnz,
    show k ≥ 17 from hk, ite_true] at hr
  show tx.gas ≥ max (standardCost (Evm.Frontier.Vm.Tx.zeroBytes tx.data)
      (tx.data.size - Evm.Frontier.Vm.Tx.zeroBytes tx.data) _) _
  cases hc : tx.to.isNone
  · have hci : (Evm.Frontier.Vm.Tx.gasEnv k tx) "is-create" = 0 := by
      simp [Evm.Frontier.Vm.Tx.gasEnv, hc]
    rw [Evm.CL.GasEmitPrague.intrinsicCall_eq_spec _ (by rw [hf]; exact hk) hci, hz, hnz,
      hal, hak] at hr
    unfold baseExtras
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add, authPerEmptyAccount]
    simp only [standardCost, floorCost, tokens, txBaseCost, txDataTokenStandard,
      txDataTokenFloor, tokensPerNonZero, Evm.Frontier.Vm.Tx.zeroBytes] at hr hfl ⊢
    omega
  · have hci : (Evm.Frontier.Vm.Tx.gasEnv k tx) "is-create" = 1 := by
      simp [Evm.Frontier.Vm.Tx.gasEnv, hc]
    rw [Evm.CL.GasEmitPrague.intrinsicCreate_eq_spec _ (by rw [hf]; exact hk) hci, hz, hnz,
      hal, hak, hdl] at hr
    unfold baseExtras
    simp only [ite_true, authPerEmptyAccount, txCreateCost, initCodeWordCost]
    simp only [standardCost, floorCost, tokens, txBaseCost, txDataTokenStandard,
      txDataTokenFloor, tokensPerNonZero, Evm.Frontier.Vm.Tx.zeroBytes] at hr hfl ⊢
    omega

/-! ## EIP-7685 requests hash (block-level) -/

/-- EIP-7685: the implementation's commitment over the request lists `applyBlock`
    builds (`ofOutput` of the deposit data and of each predeploy's output, in type
    order) is EELS's `compute_requests_hash` over EELS's `requests_from_execution`.
    So `applyBlock`'s check `computeRequestsHash (dreqs ++ wreqs ++ creqs) =
    header.requestsHash` is `IsRequestsHashValid`. EELS `forks/prague/requests.py::
    compute_requests_hash` 289-308, `forks/prague/fork.py::
    process_general_purpose_requests` 767-810 and the header check 245, 263.

    (Implementation gap, visible: `Prague.harvestDepositRequests` is a stub
    returning `[]` — EIP-6110 deposit parsing from receipt logs is not
    implemented at the `Prague.applyBlock` layer, whose body runs no
    transactions; this theorem covers any deposit data `d`.) -/
theorem requestsHashValid_sound (d w c : Evm.Bytes) (requests : List Evm.Bytes)
    (headerHash : Evm.Hash32) (hreq : requests = requestsFromExecution d w c) :
    Evm.Prague.Requests.computeRequestsHash
        (Evm.Prague.Requests.ofOutput 0 d ++ Evm.Prague.Requests.ofOutput 1 w ++
          Evm.Prague.Requests.ofOutput 2 c) = headerHash →
    IsRequestsHashValid requests headerHash := by
  intro h
  subst h hreq
  unfold IsRequestsHashValid requestsFromExecution Evm.Prague.Requests.ofOutput
  by_cases hd : d.size = 0 <;> by_cases hw : w.size = 0 <;> by_cases hc : c.size = 0 <;>
    simp only [hd, hw, hc, ite_true, ite_false, List.nil_append, List.append_nil,
      List.cons_append] <;> rfl

/-! ## EIP-7702 set-code tx + CALL delegation -/

/-- The implementation's designator parser is the spec's recogniser and address
    extraction (EELS `get_delegated_code_address`: `Address(code[3:])` exactly when
    `is_valid_delegation(code)`). -/
theorem parseDelegation_eq (c : Evm.Bytes) :
    Evm.Prague.State.parseDelegation c =
      if isDelegationDesignator c then some (parseDelegated c) else none := by
  unfold Evm.Prague.State.parseDelegation isDelegationDesignator parseDelegated
  by_cases h0 : c.size = 23
  · by_cases h1 : c.get! 0 = 0xef <;> by_cases h2 : c.get! 1 = 0x01 <;>
      by_cases h3 : c.get! 2 = 0x00 <;>
      simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, ite_true,
        ite_false, decide_true, decide_false, Bool.and_true, Bool.and_false] <;> try rfl
    simp only [Evm.Bytes.sliceZeroPad, Std.Legacy.Range.forIn_eq_forIn_range', h0]
    rfl
  · simp [h0]

/-- One EIP-7702 authorization: the implementation `Tx.authorize` (over the tx
    environment, with the same `recover` oracle) refines `IsApplyAuthorization` —
    the prechecks, the authority warmed, its code and nonce checks, then the 12500
    refund when it exists, the code, the nonce. EELS `forks/prague/vm/
    eoa_delegation.py::validate_authorization` 155-189, `recover_authority` 77-128,
    `set_delegation` 192-237. -/
theorem applyAuthorization_sound (chainId : Evm.U256)
    (recover : Evm.Prague.Authorization → Option Evm.Address)
    (env env' : Environment) (auth : Evm.Prague.Authorization) :
    Evm.Frontier.Vm.Tx.authorize chainId recover env auth = env' →
    IsApplyAuthorization chainId recover auth env env' := by
  intro h
  subst h
  unfold Evm.Frontier.Vm.Tx.authorize IsApplyAuthorization
  have hN : Evm.Frontier.Vm.Tx.secp256k1n = secp256k1n := rfl
  rw [hN]
  by_cases hpre : AuthPrechecks chainId auth
  · rw [if_neg (not_not_intro hpre)]
    obtain ⟨hc, hn, hy, hr0, hrN, hs0, hsN⟩ := hpre
    rw [if_neg (not_not_intro hc), if_neg (by omega),
      if_neg (not_not_intro ⟨hy, hr0, hrN, hs0, hsN⟩)]
    cases hr : recover auth with
    | none => rfl
    | some au =>
      simp only [Evm.Frontier.Vm.Call.warm]
      have hpd := parseDelegation_eq (env.state.getAccount au).code
      by_cases hw : env.accessedAddresses.contains au = true
      · simp only [hw, ite_true]
        by_cases hd : isDelegationDesignator (env.state.getAccount au).code = true
        · simp only [hpd, hd, ite_true, Option.isNone_some, Bool.false_eq_true, and_false,
            false_or]
          by_cases hno : (env.state.getAccount au).nonce = auth.nonce.toNat <;>
            simp only [hno, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              or_false, or_true, false_or, and_false, and_true] <;>
            by_cases hsz : (env.state.getAccount au).code.size = 0 <;>
            simp only [hsz, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              true_and, false_and, or_false, false_or] <;>
            first | rfl | trivial | (exfalso; simp_all [isDelegationDesignator])
        · simp only [hpd, hd, Bool.false_eq_true, ite_false, Option.isNone_none, and_true]
          by_cases hno : (env.state.getAccount au).nonce = auth.nonce.toNat <;>
            simp only [hno, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              or_false, or_true, false_or, and_false, and_true] <;>
            by_cases hsz : (env.state.getAccount au).code.size = 0 <;>
            simp only [hsz, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              true_and, false_and, or_false, false_or] <;>
            first | rfl | trivial | (exfalso; simp_all [isDelegationDesignator])
      · simp only [hw, Bool.false_eq_true, ite_false]
        by_cases hd : isDelegationDesignator (env.state.getAccount au).code = true
        · simp only [hpd, hd, ite_true, Option.isNone_some, Bool.false_eq_true, and_false,
            false_or]
          by_cases hno : (env.state.getAccount au).nonce = auth.nonce.toNat <;>
            simp only [hno, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              or_false, or_true, false_or, and_false, and_true] <;>
            by_cases hsz : (env.state.getAccount au).code.size = 0 <;>
            simp only [hsz, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              true_and, false_and, or_false, false_or] <;>
            first | rfl | trivial | (exfalso; simp_all [isDelegationDesignator])
        · simp only [hpd, hd, Bool.false_eq_true, ite_false, Option.isNone_none, and_true]
          by_cases hno : (env.state.getAccount au).nonce = auth.nonce.toNat <;>
            simp only [hno, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              or_false, or_true, false_or, and_false, and_true] <;>
            by_cases hsz : (env.state.getAccount au).code.size = 0 <;>
            simp only [hsz, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              true_and, false_and, or_false, false_or] <;>
            first | rfl | trivial | (exfalso; simp_all [isDelegationDesignator])
  · rw [if_pos hpre]
    by_cases hc : auth.chainId = chainId ∨ auth.chainId = 0
    · rw [if_neg (not_not_intro hc)]
      by_cases hn : auth.nonce.toNat ≥ 2 ^ 64 - 1
      · rw [if_pos hn]
      · rw [if_neg hn]
        have hsig : ¬ (auth.yParity.toNat ≤ 1 ∧ 0 < auth.r.toNat ∧ auth.r.toNat < secp256k1n ∧
            0 < auth.s.toNat ∧ auth.s.toNat ≤ secp256k1n / 2) := fun hs =>
          hpre ⟨hc, by omega, hs⟩
        rw [if_pos hsig]
    · rw [if_pos hc]

/-- The authorization list (`Tx.message`'s `tx.auths.foldl (authorize …)`) refines
    `IsApplyAuthorizations`, by induction from `applyAuthorization_sound`. EELS
    `set_delegation` 209-228 (the loop). -/
theorem applyAuthorizations_sound (chainId : Evm.U256)
    (recover : Evm.Prague.Authorization → Option Evm.Address)
    (auths : List Evm.Prague.Authorization) (env env' : Environment) :
    auths.foldl (Evm.Frontier.Vm.Tx.authorize chainId recover) env = env' →
    IsApplyAuthorizations chainId recover auths env env' := by
  induction auths generalizing env with
  | nil => intro h; exact h.symm
  | cons a rest ih =>
    intro h
    exact ⟨_, applyAuthorization_sound chainId recover env _ a rfl, ih _ h⟩

/-- CALL delegation (EIP-7702, Prague: `pragueDelegation` on): the code a CALL into
    `to` runs (`Call.codeOf`) is the delegate's when `to`'s code is a designator,
    else `to`'s own. EELS `forks/prague/vm/instructions/system.py::generic_call` via
    `vm/eoa_delegation.py::get_delegated_code_address` (`access_delegation`). -/
theorem effectiveCallCode_sound (env : Environment) (to : Evm.Address)
    (hP : env.pragueDelegation = true) :
    IsEffectiveCallCode env.state to (Evm.Frontier.Vm.Call.codeOf env to) := by
  unfold IsEffectiveCallCode Evm.Frontier.Vm.Call.codeOf Evm.Frontier.Vm.Call.delegate
  dsimp only
  simp only [hP, ite_true, parseDelegation_eq]
  by_cases hd : isDelegationDesignator (env.state.getAccount to).code = true
  · simp only [hd, ite_true]
  · simp only [hd, Bool.false_eq_true, ite_false]

/-! ## Notes

    - The BLS12-381 crypto (group law, subgroup test, map-to-curve, pairing) is an
      oracle parameter of the relations, not an axiom; its assumed meaning is
      `Evm.Crypto.Contracts`. -/

end Evm.Prague.Spec.Refinement
