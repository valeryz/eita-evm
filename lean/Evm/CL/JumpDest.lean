/-
  Evm.CL.JumpDest — JUMP / JUMPI destination validation: width, bounds and the
  valid-JUMPDEST map.

  `jumpBody` / `jumpiBody` validate the destination in three steps, and
  `jumpValidate` / `jumpiCheck` denote all three, so each is a theorem below:

   1. **Width.** The destination is a u256 in x6-x9. A destination of 2^64 + k
      whose LOW limb lands on a real JUMPDEST must not jump to k: the spec
      (`Frontier…jump`: `dest.toNat`, then `isValidJumpDest`) halts exceptionally,
      since `dest.toNat` is ≥ 2^64, hence ≥ code_size. Both ops fold x7-x9 and
      branch to `_eita_invalid_jump` before the bounds compare. (JUMPI's CONDITION
      is likewise folded over all four limbs.)
   2. **Bounds.** The low limb is compared with `code_size`.
   3. **Valid-JUMPDEST map.** The spec's `valid_jump_destinations` (EELS
      `vm/runtime.py`, `Runtime.validJumpDests` here) skips PUSH immediates, so a
      0x5b that is PUSH data is not a destination. The host builds a
      valid-JUMPDEST map per frame (`eita_jumpdest_map`, EvmState #136,
      `Mach.jumpDest`) and the ops test the map byte, never `code[dest]`. A
      creation tx with init code (mainnet 5,800,596 tx 117)

      68 5b60aa60006000a100   PUSH9 0x5b60aa60006000a100
      60 01                   PUSH1 1
      56                      JUMP            ; offset 1 is the 0x5b inside the PUSH9

      halts on mainnet with all its gas; a code-byte test would jump to 1 and run
      the immediate as code (LOG1, STOP; 54,466 gas).

  Fixtures do not exercise step 1: `stMemoryStressTest/JUMP_Bounds2` and
  `JUMPI_Bounds` jump to 0xffffffff, 2^64-1, 2^128-1 and 2^176-1 — every one of
  which has a huge LOW limb too, so a truncated compare rejects them for the
  right reason by accident. The dangerous shape is a SMALL low limb with a
  nonzero high limb; random fixtures miss single-limb differences because they
  are rare by chance. The two wrong forms (truncating, byte-testing) are stated
  below as counterexamples, so neither check can be dropped as redundant.
-/

import Evm.CL.AsmCore
import Evm.Frontier.Vm.Runtime

namespace Evm.CL.JumpDest

open Evm.CL.AsmCore

/-- A destination that fits u64. -/
def narrow (a : AsmCore.U256) : Prop := a.l1 = 0 ∧ a.l2 = 0 ∧ a.l3 = 0

/-! ## JUMP -/

/-- A narrow, in-bounds destination the map marks is taken at its low limb. -/
theorem jump_valid_dest_taken (m : Mach) (cost : Nat)
    (hsp : 1 ≤ m.sp) (hg : cost ≤ m.gas) (hn : narrow m.tos)
    (hb : m.tos.l0 < m.codeSize) (hj : m.jumpDest m.tos.l0 = true) :
    ((jumpBody cost).denote m).pcReg = m.tos.l0 := by
  obtain ⟨h1, h2, h3⟩ := hn
  simp [Prog.denote, jumpBody, Op.denote, Nat.not_lt.2 hsp, Nat.not_lt.2 hg,
        h1, h2, h3, hb, hj]

/-- **A destination that does not fit u64 is invalid, not truncated.** -/
theorem jump_wide_traps (m : Mach) (cost : Nat)
    (hsp : 1 ≤ m.sp) (hw : ¬ narrow m.tos) :
    ((jumpBody cost).denote m).trap = true := by
  have hw' : ¬ (m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0 ∧ m.tos.l0 < m.codeSize ∧ m.jumpDest m.tos.l0 = true) := fun ⟨h1, h2, h3, _, _⟩ => hw ⟨h1, h2, h3⟩
  by_cases hgc : m.gas < cost <;>
    simp [Prog.denote, jumpBody, Op.denote, Nat.not_lt.2 hsp, hw', hgc]

/-- **A destination the map does not mark is invalid, whatever byte the code holds
    there** — this is the jump into PUSH data. -/
theorem jump_unmapped_dest_traps (m : Mach) (cost : Nat)
    (hsp : 1 ≤ m.sp) (hj : m.jumpDest m.tos.l0 = false) :
    ((jumpBody cost).denote m).trap = true := by
  have hw' : ¬ (m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0 ∧ m.tos.l0 < m.codeSize ∧ m.jumpDest m.tos.l0 = true) := fun ⟨_, _, _, _, h⟩ => by simp [hj] at h
  by_cases hgc : m.gas < cost <;>
    simp [Prog.denote, jumpBody, Op.denote, Nat.not_lt.2 hsp, hw', hgc]

/-- **A destination at or past the end of the code is invalid.** -/
theorem jump_out_of_bounds_traps (m : Mach) (cost : Nat)
    (hsp : 1 ≤ m.sp) (hb : m.codeSize ≤ m.tos.l0) :
    ((jumpBody cost).denote m).trap = true := by
  have hw' : ¬ (m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0 ∧ m.tos.l0 < m.codeSize ∧ m.jumpDest m.tos.l0 = true) := fun ⟨_, _, _, h, _⟩ => absurd h (Nat.not_lt.2 hb)
  by_cases hgc : m.gas < cost <;>
    simp [Prog.denote, jumpBody, Op.denote, Nat.not_lt.2 hsp, hw', hgc]

/-- The destination is NOT read modulo 2^64: `2^64 + 5` traps, and does not
    become a jump to 5. This is the exact divergence the emit had. -/
example :
    let dest : AsmCore.U256 := { l0 := 5, l1 := 1, l2 := 0, l3 := 0 }
    ¬ narrow dest := by
  simp [narrow]

/-! ## JUMPI -/

/-- A zero condition falls through: no pc change, whatever the destination —
    including a wide or unmapped one, which must NOT trap when the branch is not
    taken (the spec charges and continues at pc+1). -/
theorem jumpi_zero_cond_falls_through (m : Mach)
    (hc : m.nos.l0 = 0 ∧ m.nos.l1 = 0 ∧ m.nos.l2 = 0 ∧ m.nos.l3 = 0) :
    ((Op.jumpiCheck).denote m).pcReg = m.pcReg
      ∧ ((Op.jumpiCheck).denote m).trap = m.trap := by
  obtain ⟨c0, c1, c2, c3⟩ := hc
  simp [Op.denote, c0, c1, c2, c3]

/-- A nonzero condition with a valid destination takes it. -/
theorem jumpi_taken_valid (m : Mach)
    (hc : ¬ (m.nos.l0 = 0 ∧ m.nos.l1 = 0 ∧ m.nos.l2 = 0 ∧ m.nos.l3 = 0))
    (hn : narrow m.tos) (hb : m.tos.l0 < m.codeSize) (hj : m.jumpDest m.tos.l0 = true) :
    ((Op.jumpiCheck).denote m).pcReg = m.tos.l0 := by
  obtain ⟨h1, h2, h3⟩ := hn
  simp [Op.denote, hc, h1, h2, h3, hb, hj]

/-- **A nonzero condition with a wide destination is invalid.** -/
theorem jumpi_taken_wide_traps (m : Mach)
    (hc : ¬ (m.nos.l0 = 0 ∧ m.nos.l1 = 0 ∧ m.nos.l2 = 0 ∧ m.nos.l3 = 0))
    (hw : ¬ narrow m.tos) :
    ((Op.jumpiCheck).denote m).trap = true := by
  have hw' : ¬ (m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0 ∧ m.tos.l0 < m.codeSize ∧ m.jumpDest m.tos.l0 = true) := fun ⟨h1, h2, h3, _, _⟩ => hw ⟨h1, h2, h3⟩
  simp [Op.denote, hc, hw']

/-- **A nonzero condition with an unmapped destination is invalid** — JUMPI into
    PUSH data, the `jumpi` d14 fixture case. -/
theorem jumpi_taken_unmapped_traps (m : Mach)
    (hc : ¬ (m.nos.l0 = 0 ∧ m.nos.l1 = 0 ∧ m.nos.l2 = 0 ∧ m.nos.l3 = 0))
    (hj : m.jumpDest m.tos.l0 = false) :
    ((Op.jumpiCheck).denote m).trap = true := by
  have hw' : ¬ (m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0 ∧ m.tos.l0 < m.codeSize ∧ m.jumpDest m.tos.l0 = true) := fun ⟨_, _, _, _, h⟩ => by simp [hj] at h
  simp [Op.denote, hc, hw']

/-- The condition is folded over ALL FOUR limbs, so a condition whose low limb
    is zero but whose high limb is not still takes the branch — the mirror of
    the destination's width check. -/
theorem jumpi_high_limb_cond_is_nonzero (m : Mach)
    (hcl : m.nos.l0 = 0) (hch : m.nos.l1 = 1) (hn : narrow m.tos)
    (hb : m.tos.l0 < m.codeSize) (hj : m.jumpDest m.tos.l0 = true) :
    ((Op.jumpiCheck).denote m).pcReg = m.tos.l0 := by
  obtain ⟨h1, h2, h3⟩ := hn
  simp [Op.denote, hcl, hch, h1, h2, h3, hb, hj]

/-! ## Two wrong forms, as counterexamples

The truncating form sets `pc := tos.l0` unconditionally; the byte-testing form
tests the code byte. Both are stated here so neither check can be dropped as
redundant. -/

/-- A machine with a given destination and code, the rest inert. The map is the
    spec's (`Runtime.jumpDestBitmap` of the code), which is the host's contract
    for EvmState #136. -/
def machFor (dest : AsmCore.U256) (code : ByteArray) : Mach :=
  { gas := 100, sp := 1, pcReg := 0, tos := dest, nos := AsmCore.U256.ofScalar 0,
    mem := fun _ => AsmCore.U256.ofScalar 0, stateMem := fun _ => 0,
    helperFn := fun _ a _ => a, helperFn3 := fun _ a _ _ => a,
    cbGas := 0, cbResult := AsmCore.U256.ofScalar 0,
    evmMem := fun _ => AsmCore.U256.ofScalar 0, memSize := 0, memCap := 0,
    acc := 0, scratch := 0,
    code := fun pc => (code.get! pc).toNat, codeSize := code.size,
    jumpDest := fun pc => (Evm.Frontier.Vm.Runtime.jumpDestBitmap code).get! pc == 1,
    isStatic := false, oog := false, trap := false, ret := false, halted := false }

/-- The truncating form: jump to the low limb. -/
def jumpValidateTruncating (m : Mach) : Mach := { m with pcReg := m.tos.l0 }

/-- On `2^64 + 5` the two disagree: the truncating form jumps to 5, `jumpValidate`
    traps. Low limb 5, high limb 1 — the shape no fixture in the corpus has,
    because `JUMP_Bounds2` and `JUMPI_Bounds` all use huge low limbs. -/
theorem truncating_form_is_wrong :
    ∃ (m : Mach),
      (jumpValidateTruncating m).pcReg = 5 ∧
      ((Op.jumpValidate).denote m).trap = true := by
  refine ⟨machFor { l0 := 5, l1 := 1, l2 := 0, l3 := 0 } .empty, ?_, ?_⟩
  · rfl
  · simp [Op.denote, machFor]

/-- The byte-testing form: width, bounds, then `code[dest] = 0x5b`. -/
def jumpValidateByteTest (m : Mach) : Mach :=
  if m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0 ∧ m.tos.l0 < m.codeSize
     ∧ m.code m.tos.l0 = 0x5b
  then { m with pcReg := m.tos.l0 } else { m with trap := true }

/-- The init code of mainnet 5,800,596 tx 117
    (0x3666640316df11865abd1352f4c0b4c5126f8ac1d858ef2a0c6e744a4865bca2):
    `PUSH9 0x5b60aa60006000a100; PUSH1 1; JUMP`. -/
def tx117InitCode : ByteArray :=
  ⟨#[0x68, 0x5b, 0x60, 0xaa, 0x60, 0x00, 0x60, 0x00, 0xa1, 0x00, 0x60, 0x01, 0x56]⟩

/-- Offset 1 holds the JUMPDEST byte… -/
theorem tx117_byte1_is_0x5b : tx117InitCode.get! 1 = 0x5b := by native_decide

/-- …and the spec has no valid destination in that code at all: the 0x5b is the
    first byte of the PUSH9 immediate. -/
theorem tx117_has_no_jumpdests :
    Evm.Frontier.Vm.Runtime.validJumpDests tx117InitCode = [] := by native_decide

/-- **The byte test is wrong on the mainnet witness**: it jumps to 1 and runs
    on; the map test traps. -/
theorem byte_test_is_wrong :
    ∃ (m : Mach),
      (jumpValidateByteTest m).pcReg = 1 ∧ (jumpValidateByteTest m).trap = false ∧
      ((Op.jumpValidate).denote m).trap = true := by
  refine ⟨machFor (AsmCore.U256.ofScalar 1) tx117InitCode, ?_, ?_, ?_⟩ <;> native_decide

end Evm.CL.JumpDest
