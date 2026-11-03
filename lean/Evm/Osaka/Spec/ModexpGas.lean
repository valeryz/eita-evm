/-
  Evm.Osaka.Spec.ModexpGas — EIP-7823 + EIP-7883 MODEXP precompile
  delta over Prague.

  EELS reference: `forks/osaka/vm/precompiled_contracts/modexp.py`.
  Diff against Prague's modexp.py (chunked for readability):

    EIP-7823 (input size cap, lines 32-41):
        if base_length > U256(1024):
            raise ExceptionalHalt("Mod-exp base length is too large")
        if exp_length > U256(1024):
            raise ExceptionalHalt("Mod-exp exponent length is too large")
        if modulus_length > U256(1024):
            raise ExceptionalHalt("Mod-exp modulus length is too large")

    EIP-7883 (gas formula, lines 88-175):
        # Prague:   return words ** 2
        # Osaka:    complexity = 16
        #           if max_length > 32:
        #               complexity = 2 * words ** 2
        ...
        # Prague:   length_part = 8 * (exp_length - 32)
        # Osaka:    length_part = 16 * (exp_length - 32)
        ...
        # Prague:   cost //= GQUADDIVISOR;  return max(200, cost)
        # Osaka:    return max(500, cost)        (no division)

  Per the SPEC-METHODOLOGY: a precompile gas formula change is a
  relation on `(base_len, exp_len, mod_len, exp_head) → gas`. We give
  it a separate file from the new opcodes; refinement will be wired
  when Prague-level MODEXP is implemented (currently both Prague and
  Osaka stub the MODEXP body — see `Prague/Vm/PrecompiledContracts.lean`
  line 187).
-/

import Evm.BaseTypes
import Evm.Osaka.Vm.PrecompiledContracts

namespace Evm.Osaka.Spec

/-! ## EIP-7823 input-size cap -/

/-- EELS `MAX_OPERAND_LEN` (implicit; first appears in Osaka). -/
def maxModexpOperandLen : Nat := 1024

/-- EIP-7823 input-validity predicate. -/
def IsValidModexpInput (baseLen expLen modLen : Nat) : Prop :=
  baseLen ≤ maxModexpOperandLen ∧
  expLen  ≤ maxModexpOperandLen ∧
  modLen  ≤ maxModexpOperandLen

/-! ## EIP-7883 gas formula -/

/-- EELS `forks/osaka/vm/precompiled_contracts/modexp.py::complexity`.

    `max_length = max(base_length, modulus_length)`,
    `words = ceil(max_length / 8)`. Then:

      complexity = 16
      if max_length > 32:
          complexity = 2 * words ** 2

    Pre-Osaka: `return words ** 2`. -/
def modexpComplexity (maxLen : Nat) : Nat :=
  let words := (maxLen + 7) / 8
  if maxLen > 32 then 2 * words * words else 16

/-- EELS `forks/osaka/vm/precompiled_contracts/modexp.py::iter_count`
    fragment for the `exp_length > 32` branch.

    Pre-Osaka: `length_part = 8 * (exp_length - 32)`.
    Osaka:     `length_part = 16 * (exp_length - 32)`. -/
def modexpExpLengthPart (expLen : Nat) : Nat :=
  if expLen ≤ 32 then 0 else 16 * (expLen - 32)

/-- EELS `forks/osaka/vm/precompiled_contracts/modexp.py` final return:

      return max(500, cost)

    Pre-Osaka: `cost //= GQUADDIVISOR; return max(200, cost)`. -/
def modexpGasFinal (cost : Nat) : Nat := max 500 cost

/-! ## Spec constants match the implementation

    These theorems pin the constants used by
    `Evm.Osaka.Vm.PrecompiledContracts.modexp7883` against the spec
    above. They're `rfl`-discharged today — the value is to enforce
    that any future drift on either side fails the build. -/

theorem modexp_input_cap_eq :
    maxModexpOperandLen
      = Evm.Osaka.Vm.PrecompiledContracts.maxModexpOperandLen := rfl

theorem modexp_floor_eq :
    Evm.Osaka.Vm.PrecompiledContracts.osakaModexpFloor = 500 := rfl

theorem modexp_exp_length_multiplier_eq :
    Evm.Osaka.Vm.PrecompiledContracts.osakaExpLengthMul = 16 := rfl

theorem modexp_complexity_base_eq :
    Evm.Osaka.Vm.PrecompiledContracts.osakaQuadBase = 16 := rfl

/-- `multComplexity7883` matches `modexpComplexity` when given the
    parsed `max(baseLen, modLen)`. Both branch the same way on
    `maxLen ≤ 32` and otherwise compute `2 * ceil(maxLen/8)^2`. -/
theorem modexp_complexity_impl_matches_spec
    (baseLen modLen : Nat) :
    Evm.Osaka.Vm.PrecompiledContracts.multComplexity7883 baseLen modLen
      = modexpComplexity (max baseLen modLen) := by
  unfold Evm.Osaka.Vm.PrecompiledContracts.multComplexity7883
         modexpComplexity Evm.Osaka.Vm.PrecompiledContracts.osakaQuadBase
         Evm.Berlin.Vm.PrecompiledContracts.multComplexity2565
  by_cases h : max baseLen modLen ≤ 32
  · simp [h, Nat.not_lt.mpr h]
  · have h' : 32 < max baseLen modLen := Nat.lt_of_not_le h
    simp [h, h', Nat.mul_assoc]

end Evm.Osaka.Spec
