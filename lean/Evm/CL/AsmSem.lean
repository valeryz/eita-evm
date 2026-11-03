/-
  Evm.CL.AsmSem — a machine semantics for `AInstr` programs WITH control flow.

  `Op.denote` gives the straight-line handler bodies their meaning at the level
  of the EVM machine (`Mach`: gas, TOS/NOS, memory). The gas routines
  (`_eita_sstore_gas_*`, `_eita_call_gas*`) are not straight-line: they are
  `tst`/`csel`/`cbz`/`cbnz`/`b` trees over 64-bit registers, and until now the
  correspondence between the `AInstr` program and the plan function it was
  proven against (`SstoreGasDenote`, `CallGasDenote`) was by inspection plus
  the SBCL differential audits. This module is the missing joint:

    * `RM` — a register file `Reg → BitVec 64`, NZCV flags, 64-bit words at
      64-bit byte addresses;
    * `step` — the data instructions, as the ARMv8 ARM defines them (flags
      from `subs`/`adds`/`tst`, the condition codes, `csel`/`cset`);
    * `exec` — a loop-free program: `ret` stops, numeric `Nf` labels resolve
      FORWARD to `label N` (the assembler's rule), directives are no-ops, an
      instruction outside the subset is `none`.

  The theorems in `ARM64.CallGasSem` / `ARM64.SstoreGasSem` then say: running
  the emitted program from the symbol stores exactly the plan's numbers. With
  `plan_eq_spec` and friends that closes program → plan → spec.
-/

import Evm.CL.AsmCore
import Std.Tactic.BVDecide

namespace Evm.CL.AsmSem

open Evm.CL.AsmCore

structure Flags where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  deriving Repr, DecidableEq

/-- The register machine. -/
structure RM where
  regs  : Reg → BitVec 64
  flags : Flags
  mem   : BitVec 64 → BitVec 64

def RM.set (m : RM) (r : Reg) (v : BitVec 64) : RM :=
  { m with regs := fun r' => if r' = r then v else m.regs r' }

def RM.withFlags (m : RM) (f : Flags) : RM := { m with flags := f }

def RM.store (m : RM) (a v : BitVec 64) : RM :=
  { m with mem := fun a' => if a' = a then v else m.mem a' }

@[simp] theorem set_regs (m : RM) (r : Reg) (v : BitVec 64) (r' : Reg) :
    (m.set r v).regs r' = if r' = r then v else m.regs r' := rfl
@[simp] theorem set_flags (m : RM) (r : Reg) (v : BitVec 64) : (m.set r v).flags = m.flags := rfl
@[simp] theorem set_mem (m : RM) (r : Reg) (v : BitVec 64) : (m.set r v).mem = m.mem := rfl
@[simp] theorem withFlags_regs (m : RM) (f : Flags) : (m.withFlags f).regs = m.regs := rfl
@[simp] theorem withFlags_flags (m : RM) (f : Flags) : (m.withFlags f).flags = f := rfl
@[simp] theorem withFlags_mem (m : RM) (f : Flags) : (m.withFlags f).mem = m.mem := rfl
@[simp] theorem store_regs (m : RM) (a v : BitVec 64) : (m.store a v).regs = m.regs := rfl
@[simp] theorem store_flags (m : RM) (a v : BitVec 64) : (m.store a v).flags = m.flags := rfl
@[simp] theorem store_mem (m : RM) (a v a' : BitVec 64) :
    (m.store a v).mem a' = if a' = a then v else m.mem a' := rfl

/-! ## Flags and conditions (ARMv8 ARM, C6.2) -/

/-- `subs`/`cmp`: C is the NOT-borrow (`b ≤ a` unsigned), V the signed overflow. -/
def subFlags (a b : BitVec 64) : Flags :=
  let r := a - b
  { n := r.msb, z := r = 0, c := b ≤ a, v := (a.msb != b.msb) && (r.msb != a.msb) }

/-- `adds`: C is the unsigned carry out. -/
def addFlags (a b : BitVec 64) : Flags :=
  let r := a + b
  { n := r.msb, z := r = 0, c := decide (a.toNat + b.toNat ≥ 2^64),
    v := (a.msb == b.msb) && (r.msb != a.msb) }

/-- `tst`/`ands`: N and Z from the result, C and V cleared. -/
def logicFlags (r : BitVec 64) : Flags := { n := r.msb, z := r = 0, c := false, v := false }

def bcHolds : BCond → Flags → Bool
  | .eq, f => f.z
  | .ne, f => !f.z
  | .lo, f => !f.c
  | .hs, f => f.c
  | .hi, f => f.c && !f.z
  | .ls, f => !(f.c && !f.z)
  | .lt, f => f.n != f.v

def scHolds : SetCond → Flags → Bool
  | .eq, f => f.z
  | .lo, f => !f.c
  | .lt, f => f.n != f.v

/-- What `cset` materialises. -/
def b2v (b : Bool) : BitVec 64 := if b then 1 else 0

/-! ## The data instructions -/

def step (m : RM) : AInstr → Option RM
  | .subImm d a i   => some (m.set d (m.regs a - BitVec.ofNat 64 i))
  | .addImm d a i   => some (m.set d (m.regs a + BitVec.ofNat 64 i))
  | .movImm d i     => some (m.set d (BitVec.ofNat 64 i))
  | .movzImm d i    => some (m.set d (BitVec.ofNat 64 i))
  | .movImmW d i    => some (m.set d (BitVec.ofNat 64 i))
  | .movkImm d i hw =>
      some (m.set d ((m.regs d &&& ~~~(BitVec.ofNat 64 0xffff <<< (16 * hw)))
                     ||| (BitVec.ofNat 64 i <<< (16 * hw))))
  | .movReg d a     => some (m.set d (m.regs a))
  | .orr3 d a b     => some (m.set d (m.regs a ||| m.regs b))
  | .and3 d a b     => some (m.set d (m.regs a &&& m.regs b))
  | .eor3 d a b     => some (m.set d (m.regs a ^^^ m.regs b))
  | .eorImm1 d a    => some (m.set d (m.regs a ^^^ 1))
  | .andImmHex d a i => some (m.set d (m.regs a &&& BitVec.ofNat 64 i))
  | .mvn d a        => some (m.set d (~~~ m.regs a))
  | .addReg d a b   => some (m.set d (m.regs a + m.regs b))
  | .subReg d a b   => some (m.set d (m.regs a - m.regs b))
  | .mulReg d a b   => some (m.set d (m.regs a * m.regs b))
  | .lsrImm d a sh  => some (m.set d (m.regs a >>> sh))
  | .lslImm d a sh  => some (m.set d (m.regs a <<< sh))
  | .addLsr d a b sh => some (m.set d (m.regs a + (m.regs b >>> sh)))
  | .addLsl d a b sh => some (m.set d (m.regs a + (m.regs b <<< sh)))
  | .addLsl5 d a b  => some (m.set d (m.regs a + (m.regs b <<< 5)))
  | .adds d a b     => some ((m.set d (m.regs a + m.regs b)).withFlags (addFlags (m.regs a) (m.regs b)))
  | .addsImm d a i  => some ((m.set d (m.regs a + BitVec.ofNat 64 i)).withFlags
                               (addFlags (m.regs a) (BitVec.ofNat 64 i)))
  | .subsReg d a b  => some ((m.set d (m.regs a - m.regs b)).withFlags (subFlags (m.regs a) (m.regs b)))
  | .subsImm d a i  => some ((m.set d (m.regs a - BitVec.ofNat 64 i)).withFlags
                               (subFlags (m.regs a) (BitVec.ofNat 64 i)))
  | .subsZr a b     => some (m.withFlags (subFlags (m.regs a) (m.regs b)))
  | .cmpReg a b     => some (m.withFlags (subFlags (m.regs a) (m.regs b)))
  | .cmpImm a i     => some (m.withFlags (subFlags (m.regs a) (BitVec.ofNat 64 i)))
  | .cmpImmWHex a i => some (m.withFlags (subFlags (m.regs a) (BitVec.ofNat 64 i)))
  | .tstImm r i     => some (m.withFlags (logicFlags (m.regs r &&& BitVec.ofNat 64 i)))
  | .csel d a b c   => some (m.set d (if bcHolds c m.flags then m.regs a else m.regs b))
  | .cselZrA d b c  => some (m.set d (if bcHolds c m.flags then 0 else m.regs b))
  | .cselZrB d a c  => some (m.set d (if bcHolds c m.flags then m.regs a else 0))
  | .cselHi d a b   => some (m.set d (if bcHolds .hi m.flags then m.regs a else m.regs b))
  | .cselNe d a b   => some (m.set d (if bcHolds .ne m.flags then m.regs a else m.regs b))
  | .csinvEqZr d a  => some (m.set d (if m.flags.z then m.regs a else ~~~(0 : BitVec 64)))
  | .cset d c       => some (m.set d (b2v (scHolds c m.flags)))
  | .ldrOff d b o   => some (m.set d (m.mem (m.regs b + BitVec.ofNat 64 o)))
  | .ldrBase d b    => some (m.set d (m.mem (m.regs b)))
  | .ldpOff r1 r2 b o =>
      let a := m.regs b
      some ((m.set r1 (m.mem (a + BitVec.ofNat 64 o))).set r2 (m.mem (a + BitVec.ofNat 64 (o + 8))))
  | .strOff s b o   => some (m.store (m.regs b + BitVec.ofNat 64 o) (m.regs s))
  | .strBase s b    => some (m.store (m.regs b) (m.regs s))
  | .strZr b o      => some (m.store (m.regs b + BitVec.ofNat 64 o) 0)
  | .stpOff r1 r2 b o =>
      let a := m.regs b
      some ((m.store (a + BitVec.ofNat 64 o) (m.regs r1)).store (a + BitVec.ofNat 64 (o + 8)) (m.regs r2))
  -- directives: nothing happens
  | .blank | .global _ | .p2align2 | .p2align3 | .symLabel _ | .textSection | .dataSection
  | .commentLine _ => some m
  | _ => none

/-! ## Programs: forward local labels, `ret` stops -/

/-- Drop up to the `label N` that a `Nf` reference names. -/
def skipTo (lbl : String) : List AInstr → List AInstr
  | [] => []
  | (.label t) :: rest => if lbl == t ++ "f" then (.label t) :: rest else skipTo lbl rest
  | _ :: rest => skipTo lbl rest

theorem skipTo_length_le (lbl : String) (xs : List AInstr) : (skipTo lbl xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [skipTo]
  | cons x rest ih =>
    cases x <;> simp only [skipTo] <;> try (exact Nat.le_succ_of_le ih)
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le ih

/-- Execute to the first `ret`. `none` = fell off the end, branched to a
    missing label, or met an instruction outside the modelled subset. -/
def exec : List AInstr → RM → Option RM
  | [], _ => none
  | i :: rest, m =>
    match i with
    | .ret        => some m
    | .label _    => exec rest m
    | .bLbl l     => exec (skipTo l rest) m
    | .cbzLbl r l => if m.regs r = 0 then exec (skipTo l rest) m else exec rest m
    | .cbnzLbl r l => if m.regs r = 0 then exec rest m else exec (skipTo l rest) m
    | .cbzWLbl r l => if m.regs r &&& 0xffffffff = 0 then exec (skipTo l rest) m else exec rest m
    | .cbnzWLbl r l => if m.regs r &&& 0xffffffff = 0 then exec rest m else exec (skipTo l rest) m
    | .bcLbl c l  => if bcHolds c m.flags then exec (skipTo l rest) m else exec rest m
    | .blsLbl l   => if bcHolds .ls m.flags then exec (skipTo l rest) m else exec rest m
    | i' =>
      match step m i' with
      | some m' => exec rest m'
      | none => none
termination_by p => p.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Nat.lt_succ_self _
    | exact Nat.lt_succ_of_le (skipTo_length_le _ _)

/-- The program from a symbol: everything from `sym:` on. -/
def entry (sym : String) : List AInstr → List AInstr
  | [] => []
  | (.symLabel s) :: rest => if s == sym then (.symLabel s) :: rest else entry sym rest
  | _ :: rest => entry sym rest

/-! ## Simp support -/

@[simp] theorem exec_nil (m : RM) : exec [] m = none := by simp [exec]

@[simp] theorem b2v_true : b2v true = 1#64 := rfl
@[simp] theorem b2v_false : b2v false = 0#64 := rfl
@[simp] theorem b2v_eq_zero (b : Bool) : (b2v b = 0#64) ↔ b = false := by cases b <;> simp [b2v]
@[simp] theorem b2v_xor_one (b : Bool) : b2v b ^^^ 1#64 = b2v (!b) := by cases b <;> simp [b2v]
@[simp] theorem b2v_and (a b : Bool) : b2v a &&& b2v b = b2v (a && b) := by
  cases a <;> cases b <;> simp [b2v]
@[simp] theorem b2v_msb (b : Bool) : (b2v b).msb = false := by cases b <;> simp [b2v]
@[simp] theorem b2v_sub_zero (b : Bool) : b2v b - 0#64 = b2v b := by simp

/-- `cmp r, #0 ; <eq>` on a predicate register. -/
@[simp] theorem subFlags_b2v_zero_z (b : Bool) : (subFlags (b2v b) 0#64).z = !b := by
  cases b <;> simp [subFlags, b2v]
@[simp] theorem subFlags_b2v_zero_n (b : Bool) : (subFlags (b2v b) 0#64).n = false := by
  cases b <;> simp [subFlags, b2v]
@[simp] theorem subFlags_b2v_zero_v (b : Bool) : (subFlags (b2v b) 0#64).v = false := by
  cases b <;> simp [subFlags, b2v]

@[simp] theorem add8_ne_self (a : BitVec 64) : (a + 8#64 = a) ↔ False := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp at this; omega
  · intro h; exact h.elim
@[simp] theorem self_ne_add8 (a : BitVec 64) : (a = a + 8#64) ↔ False := by
  rw [eq_comm]; exact add8_ne_self a
@[simp] theorem add16_ne_add8 (a : BitVec 64) : (a + 16#64 = a + 8#64) ↔ False := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp at this; omega
  · intro h; exact h.elim
@[simp] theorem add16_ne_self (a : BitVec 64) : (a + 16#64 = a) ↔ False := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp at this; omega
  · intro h; exact h.elim

/-- `lsr x, #6` as the division omega understands (the 63/64 cap). -/
theorem ushiftRight_six (x : BitVec 64) : x >>> 6 = BitVec.ofNat 64 (x.toNat / 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have : x.toNat / 2^6 < 2^64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
  rw [Nat.mod_eq_of_lt (by simpa using this)]

/-- `mov r, #v` is one `movz` when `v < 2^16` — every gas constant is. -/
theorem movImmInstrs_small (r : Reg) (v : Nat) (h : v < 65536) :
    movImmInstrs r v = [AInstr.movzImm r v] := by
  have h1 : (v >>> 16) % 65536 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]; have : v / 2^16 = 0 := Nat.div_eq_of_lt h; simp [this]
  have h2 : (v >>> 32) % 65536 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]; have : v / 2^32 = 0 := Nat.div_eq_of_lt (by omega); simp [this]
  have h3 : (v >>> 48) % 65536 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]; have : v / 2^48 = 0 := Nat.div_eq_of_lt (by omega); simp [this]
  simp [movImmInstrs, List.range_succ, h1, h2, h3, Nat.mod_eq_of_lt h]


/-! ## Entry: a routine's program is a suffix of the whole file -/

/-- `movz`/`movk` only: no symbol label hides in a `mov #imm`. -/
@[simp] theorem symLabel_not_mem_movImmInstrs (t : String) (r : Reg) (v : Nat) :
    (AInstr.symLabel t ∈ movImmInstrs r v) ↔ False := by
  simp only [movImmInstrs, List.mem_cons, List.mem_filterMap, List.mem_range, iff_false,
             not_or, reduceCtorEq, not_false_eq_true, true_and, not_exists, not_and]
  intro i _ h
  split at h <;> simp_all

/-- Skipping a prefix that does not carry the symbol. -/
theorem entry_append_left (s : String) (A B : List AInstr)
    (h : ∀ t, AInstr.symLabel t ∈ A → t ≠ s) : entry s (A ++ B) = entry s B := by
  induction A with
  | nil => rfl
  | cons x rest ih =>
    have ih' := ih (fun t ht => h t (List.mem_cons_of_mem x ht))
    cases x <;> simp only [List.cons_append, entry, ih']
    rename_i t
    have : t ≠ s := h t (List.mem_cons_self ..)
    simp [this]

end Evm.CL.AsmSem
