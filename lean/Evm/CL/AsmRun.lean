/-
  Evm.CL.AsmRun — a FRAGMENT semantics for `AInstr`, for the chunk JIT.

  `AsmSem` runs a routine to its `ret` over a word-cell memory, which is all
  the gas routines need. The chunk pieces (`ARM64.JIT.emitRegionFlushT`, the
  `ChunkGas` gadgets) need more:

   * they are fragments — a flush falls off its end into the next piece; a
     fault symbol (`b _eita_oog`) leaves the frame; a helper call
     (`bl _eita_helper_mul`) returns;
   * they address bytes — `strb` for MSTORE8, `str` at any constant MSTORE
     offset — so the memory is a byte map and a 64-bit access is eight bytes;
   * they use the stack pointer (the scratch frame of 32-byte slots) and the
     carry chain (`adcs`/`sbcs`) the u256 cores are built from.

  Register-only instructions are delegated to `AsmSem.step` through a view
  with a dummy memory, so there is ONE semantics for `adds`, `csel`, `cset`,
  `cmp`, …; this module adds the memory, sp, byte, reverse and carry forms,
  and the control forms (`Outcome`). Helpers (`_eita_helper_*`) are an oracle
  `Helpers`: the value they write, the junk they leave in caller-saved
  registers and below sp. A theorem over all oracles whose values satisfy
  `Helpers.Spec` is a theorem about the real C helpers under exactly the trust
  the DSL already places in them (`Mach.helperFn`).
-/

import Evm.CL.AsmSem
import Evm.IR.SymExpr
import Std.Tactic.BVDecide

namespace Evm.CL.AsmRun

open Evm.CL.AsmCore Evm.CL.AsmSem
open Evm.IR.SymExpr (eval)

/-! ## Byte memory -/

abbrev Mem := BitVec 64 → BitVec 8

def st8 (mem : Mem) (a : BitVec 64) (v : BitVec 8) : Mem :=
  fun x => if x = a then v else mem x

/-- `a + k`, always spelled `BitVec.ofNat 64 k` so that address terms match
    syntactically across definitions and lemmas (a bare numeral is a different
    literal). -/
abbrev off (a : BitVec 64) (k : Nat) : BitVec 64 := a + BitVec.ofNat 64 k

/-- A little-endian 64-bit word at byte address `a`. -/
def ld64 (mem : Mem) (a : BitVec 64) : BitVec 64 :=
  mem (off a 7) ++ mem (off a 6) ++ mem (off a 5) ++ mem (off a 4) ++
  mem (off a 3) ++ mem (off a 2) ++ mem (off a 1) ++ mem a

def st64 (mem : Mem) (a : BitVec 64) (v : BitVec 64) : Mem :=
  st8 (st8 (st8 (st8 (st8 (st8 (st8 (st8 mem a (v.extractLsb' 0 8))
    (off a 1) (v.extractLsb' 8 8)) (off a 2) (v.extractLsb' 16 8)) (off a 3) (v.extractLsb' 24 8))
    (off a 4) (v.extractLsb' 32 8)) (off a 5) (v.extractLsb' 40 8)) (off a 6) (v.extractLsb' 48 8))
    (off a 7) (v.extractLsb' 56 8)

/-- A u256 as four little-endian limbs (`ldp` order). -/
def ld256 (mem : Mem) (a : BitVec 64) : Evm.U256 :=
  ld64 mem (off a 24) ++ ld64 mem (off a 16) ++ ld64 mem (off a 8) ++ ld64 mem a

def st256 (mem : Mem) (a : BitVec 64) (v : Evm.U256) : Mem :=
  st64 (st64 (st64 (st64 mem a (v.extractLsb' 0 64)) (off a 8) (v.extractLsb' 64 64))
    (off a 16) (v.extractLsb' 128 64)) (off a 24) (v.extractLsb' 192 64)

/-- `rev`: byte reverse. -/
def rev64 (v : BitVec 64) : BitVec 64 :=
  v.extractLsb' 0 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 24 8 ++
  v.extractLsb' 32 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 56 8

/-! ## The machine -/

structure RS where
  regs  : Reg → BitVec 64
  sp    : BitVec 64
  flags : Flags
  mem   : Mem

def RS.set (s : RS) (r : Reg) (v : BitVec 64) : RS :=
  { s with regs := fun r' => if r' = r then v else s.regs r' }
def RS.withFlags (s : RS) (f : Flags) : RS := { s with flags := f }
def RS.store64 (s : RS) (a v : BitVec 64) : RS := { s with mem := st64 s.mem a v }
def RS.store8 (s : RS) (a : BitVec 64) (v : BitVec 8) : RS := { s with mem := st8 s.mem a v }
def RS.withSp (s : RS) (p : BitVec 64) : RS := { s with sp := p }

/-- The register-only view `AsmSem.step` runs on. -/
def toRM (s : RS) : RM := { regs := s.regs, flags := s.flags, mem := fun _ => 0 }

@[simp] theorem set_regs (s : RS) (r : Reg) (v : BitVec 64) (r' : Reg) :
    (s.set r v).regs r' = if r' = r then v else s.regs r' := rfl
@[simp] theorem set_sp (s : RS) (r : Reg) (v : BitVec 64) : (s.set r v).sp = s.sp := rfl
@[simp] theorem set_flags (s : RS) (r : Reg) (v : BitVec 64) : (s.set r v).flags = s.flags := rfl
@[simp] theorem set_mem (s : RS) (r : Reg) (v : BitVec 64) : (s.set r v).mem = s.mem := rfl
@[simp] theorem withFlags_regs (s : RS) (f : Flags) : (s.withFlags f).regs = s.regs := rfl
@[simp] theorem withFlags_sp (s : RS) (f : Flags) : (s.withFlags f).sp = s.sp := rfl
@[simp] theorem withFlags_flags (s : RS) (f : Flags) : (s.withFlags f).flags = f := rfl
@[simp] theorem withFlags_mem (s : RS) (f : Flags) : (s.withFlags f).mem = s.mem := rfl
@[simp] theorem store64_regs (s : RS) (a v : BitVec 64) : (s.store64 a v).regs = s.regs := rfl
@[simp] theorem store64_sp (s : RS) (a v : BitVec 64) : (s.store64 a v).sp = s.sp := rfl
@[simp] theorem store64_flags (s : RS) (a v : BitVec 64) : (s.store64 a v).flags = s.flags := rfl
@[simp] theorem store64_mem (s : RS) (a v : BitVec 64) : (s.store64 a v).mem = st64 s.mem a v := rfl
@[simp] theorem store8_regs (s : RS) (a : BitVec 64) (v : BitVec 8) : (s.store8 a v).regs = s.regs := rfl
@[simp] theorem store8_sp (s : RS) (a : BitVec 64) (v : BitVec 8) : (s.store8 a v).sp = s.sp := rfl
@[simp] theorem store8_flags (s : RS) (a : BitVec 64) (v : BitVec 8) : (s.store8 a v).flags = s.flags := rfl
@[simp] theorem store8_mem (s : RS) (a : BitVec 64) (v : BitVec 8) : (s.store8 a v).mem = st8 s.mem a v := rfl
@[simp] theorem withSp_regs (s : RS) (p : BitVec 64) : (s.withSp p).regs = s.regs := rfl
@[simp] theorem withSp_sp (s : RS) (p : BitVec 64) : (s.withSp p).sp = p := rfl
@[simp] theorem withSp_flags (s : RS) (p : BitVec 64) : (s.withSp p).flags = s.flags := rfl
@[simp] theorem withSp_mem (s : RS) (p : BitVec 64) : (s.withSp p).mem = s.mem := rfl
@[simp] theorem toRM_regs (s : RS) : (toRM s).regs = s.regs := rfl

theorem set_set_same (s : RS) (r : Reg) (a b : BitVec 64) : (s.set r a).set r b = s.set r b := by
  simp only [RS.set]; congr 1; funext r'; split <;> rfl

theorem set_eq_self (s : RS) (r : Reg) (v : BitVec 64) (h : s.regs r = v) : s.set r v = s := by
  obtain ⟨regs, sp, flags, mem⟩ := s
  simp only [RS.set]
  congr 1
  funext r'
  split
  · subst r'; exact h.symm
  · rfl
@[simp] theorem toRM_flags (s : RS) : (toRM s).flags = s.flags := rfl

/-! ## The carry chain (ARMv8 ARM: AddWithCarry) -/

def bit (b : Bool) : BitVec 65 := if b then 1 else 0

/-- `a + b + c`: the 64-bit result and the flags, from the 65-bit sum. -/
def addc (a b : BitVec 64) (c : Bool) : BitVec 64 × Flags :=
  let r65 := a.zeroExtend 65 + b.zeroExtend 65 + bit c
  let r := r65.truncate 64
  (r, { n := r.msb, z := r = 0, c := r65.msb, v := (a.msb == b.msb) && (r.msb != a.msb) })

/-- `a - b - ¬c` = `a + ¬b + c`: C is the no-borrow (`b + ¬c ≤ a`). -/
def subc (a b : BitVec 64) (c : Bool) : BitVec 64 × Flags :=
  let r := if c then a - b else a - b - 1
  (r, { n := r.msb, z := r = 0,
        c := BitVec.ule (b.zeroExtend 65 + bit (!c)) (a.zeroExtend 65),
        v := (a.msb != b.msb) && (r.msb != a.msb) })

/-! ## The step -/

def step (s : RS) : AInstr → Option RS
  -- memory
  | .ldrOff d b o   => some (s.set d (ld64 s.mem (s.regs b + BitVec.ofNat 64 o)))
  | .ldrBase d b    => some (s.set d (ld64 s.mem (s.regs b)))
  | .ldpOff r1 r2 b o =>
      let a := s.regs b
      some ((s.set r1 (ld64 s.mem (a + BitVec.ofNat 64 o))).set r2
              (ld64 s.mem (a + BitVec.ofNat 64 (o + 8))))
  | .strOff src b o => some (s.store64 (s.regs b + BitVec.ofNat 64 o) (s.regs src))
  | .strBase src b  => some (s.store64 (s.regs b) (s.regs src))
  | .strZr b o      => some (s.store64 (s.regs b + BitVec.ofNat 64 o) 0)
  | .stpOff r1 r2 b o =>
      let a := s.regs b
      some ((s.store64 (a + BitVec.ofNat 64 o) (s.regs r1)).store64
              (a + BitVec.ofNat 64 (o + 8)) (s.regs r2))
  | .strbOff src b o => some (s.store8 (s.regs b + BitVec.ofNat 64 o) ((s.regs src).extractLsb' 0 8))
  | .strbBase src b  => some (s.store8 (s.regs b) ((s.regs src).extractLsb' 0 8))
  | .strbReg src b i => some (s.store8 (s.regs b + s.regs i) ((s.regs src).extractLsb' 0 8))
  | .ldrbOff d b o  => some (s.set d ((s.mem (s.regs b + BitVec.ofNat 64 o)).zeroExtend 64))
  | .ldrbReg d b i  => some (s.set d ((s.mem (s.regs b + s.regs i)).zeroExtend 64))
  | .rev d a        => some (s.set d (rev64 (s.regs a)))
  -- the stack pointer
  | .addSp d n      => some (s.set d (s.sp + BitVec.ofNat 64 n))
  | .addSpReg r     => some (s.set r (s.sp + s.regs r))
  | .spSub n        => some (s.withSp (s.sp - BitVec.ofNat 64 n))
  | .spAdd n        => some (s.withSp (s.sp + BitVec.ofNat 64 n))
  | .spSubReg r     => some (s.withSp (s.sp - s.regs r))
  | .spAddReg r     => some (s.withSp (s.sp + s.regs r))
  | .stpFpLr        =>
      let p := s.sp - BitVec.ofNat 64 16
      some (((s.store64 p (s.regs .x29)).store64 (off p 8) (s.regs .x30)).withSp p)
  | .ldpFpLr        =>
      some (((s.set .x29 (ld64 s.mem s.sp)).set .x30 (ld64 s.mem (off s.sp 8))).withSp (off s.sp 16))
  -- the carry chain
  | .adcs d a b     => let (r, f) := addc (s.regs a) (s.regs b) s.flags.c; some ((s.set d r).withFlags f)
  | .adc d a b      => some (s.set d (addc (s.regs a) (s.regs b) s.flags.c).1)
  | .sbcs d a b     => let (r, f) := subc (s.regs a) (s.regs b) s.flags.c; some ((s.set d r).withFlags f)
  | .sbc d a b      => some (s.set d (subc (s.regs a) (s.regs b) s.flags.c).1)
  | .sbcsZr a b     => some (s.withFlags (subc (s.regs a) (s.regs b) s.flags.c).2)
  -- everything register-only: ONE semantics, `AsmSem.step`
  | i => (AsmSem.step (toRM s) i).map (fun rm => { s with regs := rm.regs, flags := rm.flags })

/-! ## Helpers: the oracle -/

/-- The C helpers' boundary. `fn2`/`fn3` are their values; `clob`, `flg`,
    `junk` are whatever they leave in the caller-saved registers, the flags
    and the memory below sp. -/
structure Helpers where
  fn2  : String → Evm.U256 → Evm.U256 → Evm.U256
  fn3  : String → Evm.U256 → Evm.U256 → Evm.U256 → Evm.U256
  clob : String → RS → Reg → BitVec 64
  flg  : String → RS → Flags
  junk : String → RS → BitVec 64 → BitVec 8
  /-- the argument registers a call stages: out, a, b, c (AAPCS64 x0-x3 on
      ARM64; the x86-64 frame names x3, x2, x1, x14, whose homes are the SysV
      rdi, rsi, rdx, rcx) -/
  conv : Reg × Reg × Reg × Reg

/-- AAPCS64: x0 out, x1-x3 the arguments. -/
def armConv : Reg × Reg × Reg × Reg := (.x0, .x1, .x2, .x3)

/-- AAPCS64 caller-saved: x0-x17 and the link register. -/
def callerSaved : Reg → Bool
  | .x0 | .x1 | .x2 | .x3 | .x4 | .x5 | .x6 | .x7 | .x8 | .x9 | .x10 | .x11 | .x12 | .x13
  | .x14 | .x15 | .x16 | .x17 | .x30 => true
  | _ => false

def ternary (h : String) : Bool := h == "_eita_helper_addmod" || h == "_eita_helper_mulmod"

/-- How far below sp a helper's own frames may reach (64 KiB; the compute
    helpers use a few hundred bytes). -/
def helperStack : Nat := 65536

/-- `x` is in the helper's stack window `[sp - helperStack, sp)`. -/
def belowSp (sp x : BitVec 64) : Bool :=
  BitVec.ult x sp && BitVec.ule (sp - BitVec.ofNat 64 helperStack) x

/-- `bl h` with (out, a, b[, n]) in x0-x3: the result lands at `out`; the
    caller-saved registers, the flags and the bytes in the helper's stack
    window below sp are the oracle's. -/
def callHelper (H : Helpers) (h : String) (s : RS) : RS :=
  let out := s.regs H.conv.1
  let a := ld256 s.mem (s.regs H.conv.2.1)
  let b := ld256 s.mem (s.regs H.conv.2.2.1)
  let v := if ternary h then H.fn3 h a b (ld256 s.mem (s.regs H.conv.2.2.2)) else H.fn2 h a b
  let below : Mem := fun x => if belowSp s.sp x then H.junk h s x else s.mem x
  { regs := fun r => if callerSaved r then H.clob h s r else s.regs r,
    sp := s.sp, flags := H.flg h s, mem := st256 below out v }

/-- What the real helpers compute (`c/eita_compute.c`, the DSL's
    `Mach.helperFn`): the `Expr.eval` arms. -/
structure Helpers.Spec (H : Helpers) : Prop where
  mul : ∀ a b, H.fn2 "_eita_helper_mul" a b = a * b
  div : ∀ a b, H.fn2 "_eita_helper_div" a b = if b = 0 then 0 else BitVec.udiv a b
  sdiv : ∀ a b, H.fn2 "_eita_helper_sdiv" a b = if b = 0 then 0 else BitVec.sdiv a b
  mod_ : ∀ a b, H.fn2 "_eita_helper_mod" a b = if b = 0 then 0 else BitVec.umod a b
  smod_ : ∀ a b, H.fn2 "_eita_helper_smod" a b = if b = 0 then 0 else BitVec.srem a b
  addmod : ∀ a b n, H.fn3 "_eita_helper_addmod" a b n =
    if n = 0 then 0 else Evm.U256.ofNat ((a.toNat + b.toNat) % n.toNat)
  mulmod : ∀ a b n, H.fn3 "_eita_helper_mulmod" a b n =
    if n = 0 then 0 else Evm.U256.ofNat ((a.toNat * b.toNat) % n.toNat)
  signextend : ∀ a b, H.fn2 "_eita_helper_signextend" a b = Evm.Frontier.Vm.Instructions.signExtend a b
  byte_ : ∀ i x, H.fn2 "_eita_helper_byte" i x = eval (.byte_ (.const i) (.const x)) []
  shl : ∀ sh x, H.fn2 "_eita_helper_shl" sh x = eval (.shl_ (.const sh) (.const x)) []
  shr : ∀ sh x, H.fn2 "_eita_helper_shr" sh x = eval (.shr_ (.const sh) (.const x)) []
  sar : ∀ sh x, H.fn2 "_eita_helper_sar" sh x = eval (.sar_ (.const sh) (.const x)) []

/-! ## Labels: named (`Lj_3_1`) or GNU numeric forward (`8f` → `8`) -/

/-- Drop up to the label a reference names: an exact name, or `N` for `Nf`. -/
def skipTo (lbl : String) : List AInstr → List AInstr
  | [] => []
  | (.label t) :: rest => if lbl == t || lbl == t ++ "f" then (.label t) :: rest else skipTo lbl rest
  | _ :: rest => skipTo lbl rest

theorem skipTo_length_le (lbl : String) (xs : List AInstr) : (skipTo lbl xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [skipTo]
  | cons x rest ih =>
    cases x <;> simp only [skipTo] <;> try (exact Nat.le_succ_of_le ih)
    split
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le ih

/-! ## Fragments -/

inductive Outcome where
  /-- fell off the fragment's end -/
  | done  (s : RS)
  /-- `ret` -/
  | ret   (s : RS)
  /-- a far branch to a fault symbol: the frame exits there -/
  | fault (sym : String) (s : RS)
  /-- an instruction outside the subset. (A branch to a label the fragment does not
      contain is NOT stuck: `skipTo` returns `[]` and the run ends `done` at the branch —
      a fragment that is not `closed` must say where such a label lives.) -/
  | stuck

/-- The control forms, classified once. -/
inductive Ctrl where
  | ret
  | label
  | jump (l : String)
  | cond (taken : RS → Bool) (l : String)
  | far  (sym : String)
  /-- a conditional far exit (x86-64 `jcc` to a trampoline) -/
  | condFar (taken : RS → Bool) (sym : String)
  | call (h : String)

def ctrl : AInstr → Option Ctrl
  | .ret          => some .ret
  | .label _      => some .label
  | .bLbl l       => some (.jump l)
  | .cbzLbl r l   => some (.cond (fun s => decide (s.regs r = 0)) l)
  | .cbnzLbl r l  => some (.cond (fun s => decide (s.regs r ≠ 0)) l)
  | .cbzWLbl r l  => some (.cond (fun s => decide (s.regs r &&& 0xffffffff = 0)) l)
  | .cbnzWLbl r l => some (.cond (fun s => decide (s.regs r &&& 0xffffffff ≠ 0)) l)
  | .bcLbl c l    => some (.cond (fun s => bcHolds c s.flags) l)
  | .blsLbl l     => some (.cond (fun s => bcHolds .ls s.flags) l)
  | .bFar sym     => some (.far sym)
  | .bTramp sym   => some (.far sym)
  | .bcTramp c sym => some (.condFar (fun s => bcHolds c s.flags) sym)
  | .blFar h      => some (.call h)
  | .blSym h      => some (.call h)
  -- the handler bodies' exits to an external symbol (the fault stubs, B7a)
  | .bSym c sym   => some (.condFar (fun s => bcHolds c s.flags) sym)
  | .bSymU sym    => some (.far sym)
  | .cbnzSym r sym => some (.condFar (fun s => decide (s.regs r ≠ 0)) sym)
  | .cbnzSymW r sym => some (.condFar (fun s => decide (s.regs r &&& 0xffffffff ≠ 0)) sym)
  | .cbnzOog r    => some (.condFar (fun s => decide (s.regs r ≠ 0)) "_eita_oog")
  | .bcsOog       => some (.condFar (fun s => bcHolds .hs s.flags) "_eita_oog")
  | .bhiOog       => some (.condFar (fun s => bcHolds .hi s.flags) "_eita_oog")
  | .bloOog       => some (.condFar (fun s => bcHolds .lo s.flags) "_eita_oog")
  | _             => none

def run (H : Helpers) : List AInstr → RS → Outcome
  | [], s => .done s
  | i :: rest, s =>
    match ctrl i with
    | some .ret          => .ret s
    | some .label        => run H rest s
    | some (.jump l)     => run H (skipTo l rest) s
    | some (.cond c l)   => if c s then run H (skipTo l rest) s else run H rest s
    | some (.far sym)    => .fault sym s
    | some (.condFar c sym) => if c s then .fault sym s else run H rest s
    | some (.call h)     => run H rest (callHelper H h s)
    | none =>
      match step s i with
      | some s' => run H rest s'
      | none => .stuck
termination_by p => p.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Nat.lt_succ_self _
    | exact Nat.lt_succ_of_le (skipTo_length_le _ _)

@[simp] theorem run_nil (H : Helpers) (s : RS) : run H [] s = .done s := by simp [run]

/-- One data instruction. -/
theorem run_cons_step (H : Helpers) (i : AInstr) (rest : List AInstr) (s s' : RS)
    (hc : ctrl i = none) (hs : step s i = some s') : run H (i :: rest) s = run H rest s' := by
  simp [run, hc, hs]

theorem run_cons_label (H : Helpers) (l : String) (rest : List AInstr) (s : RS) :
    run H (.label l :: rest) s = run H rest s := by simp [run, ctrl]

theorem run_cons_bFar (H : Helpers) (sym : String) (rest : List AInstr) (s : RS) :
    run H (.bFar sym :: rest) s = .fault sym s := by simp [run, ctrl]

/-- A conditional exit to an external symbol. -/
theorem run_cons_condFar (H : Helpers) (i : AInstr) (c : RS → Bool) (sym : String) (rest : List AInstr) (s : RS)
    (hc : ctrl i = some (.condFar c sym)) :
    run H (i :: rest) s = if c s then .fault sym s else run H rest s := by
  simp [run, hc]

theorem run_cons_bcLbl (H : Helpers) (c : BCond) (l : String) (rest : List AInstr) (s : RS) :
    run H (.bcLbl c l :: rest) s =
      if bcHolds c s.flags then run H (skipTo l rest) s else run H rest s := by simp [run, ctrl]

/-! ### The data steps, one lemma each (all `rfl`: the delegation is definitional) -/

@[simp] theorem step_movzImm (s : RS) (r : Reg) (i : Nat) :
    step s (.movzImm r i) = some (s.set r (BitVec.ofNat 64 i)) := rfl
@[simp] theorem step_movImm (s : RS) (r : Reg) (i : Nat) :
    step s (.movImm r i) = some (s.set r (BitVec.ofNat 64 i)) := rfl
@[simp] theorem step_movkImm (s : RS) (r : Reg) (i hw : Nat) :
    step s (.movkImm r i hw) =
      some (s.set r ((s.regs r &&& ~~~(BitVec.ofNat 64 0xffff <<< (16 * hw))) ||| (BitVec.ofNat 64 i <<< (16 * hw)))) := rfl
@[simp] theorem step_subsImm (s : RS) (d a : Reg) (i : Nat) :
    step s (.subsImm d a i) =
      some ((s.set d (s.regs a - BitVec.ofNat 64 i)).withFlags (subFlags (s.regs a) (BitVec.ofNat 64 i))) := rfl
@[simp] theorem step_subsReg (s : RS) (d a b : Reg) :
    step s (.subsReg d a b) =
      some ((s.set d (s.regs a - s.regs b)).withFlags (subFlags (s.regs a) (s.regs b))) := rfl
@[simp] theorem step_addReg (s : RS) (d a b : Reg) :
    step s (.addReg d a b) = some (s.set d (s.regs a + s.regs b)) := rfl
@[simp] theorem step_subImm (s : RS) (d a : Reg) (i : Nat) :
    step s (.subImm d a i) = some (s.set d (s.regs a - BitVec.ofNat 64 i)) := rfl
@[simp] theorem step_addImm (s : RS) (d a : Reg) (i : Nat) :
    step s (.addImm d a i) = some (s.set d (s.regs a + BitVec.ofNat 64 i)) := rfl
@[simp] theorem step_cmpImm (s : RS) (a : Reg) (i : Nat) :
    step s (.cmpImm a i) = some (s.withFlags (subFlags (s.regs a) (BitVec.ofNat 64 i))) := rfl
@[simp] theorem step_cmpReg (s : RS) (a b : Reg) :
    step s (.cmpReg a b) = some (s.withFlags (subFlags (s.regs a) (s.regs b))) := rfl

@[simp] theorem step_adds (s : RS) (d a b : Reg) :
    step s (.adds d a b) = some ((s.set d (s.regs a + s.regs b)).withFlags (addFlags (s.regs a) (s.regs b))) := rfl
@[simp] theorem step_adcs (s : RS) (d a b : Reg) :
    step s (.adcs d a b) =
      some ((s.set d (addc (s.regs a) (s.regs b) s.flags.c).1).withFlags (addc (s.regs a) (s.regs b) s.flags.c).2) := rfl
@[simp] theorem step_adc (s : RS) (d a b : Reg) :
    step s (.adc d a b) = some (s.set d (addc (s.regs a) (s.regs b) s.flags.c).1) := rfl
@[simp] theorem step_sbcs (s : RS) (d a b : Reg) :
    step s (.sbcs d a b) =
      some ((s.set d (subc (s.regs a) (s.regs b) s.flags.c).1).withFlags (subc (s.regs a) (s.regs b) s.flags.c).2) := rfl
@[simp] theorem step_sbc (s : RS) (d a b : Reg) :
    step s (.sbc d a b) = some (s.set d (subc (s.regs a) (s.regs b) s.flags.c).1) := rfl
@[simp] theorem step_subsZr (s : RS) (a b : Reg) :
    step s (.subsZr a b) = some (s.withFlags (subFlags (s.regs a) (s.regs b))) := rfl
@[simp] theorem step_sbcsZr (s : RS) (a b : Reg) :
    step s (.sbcsZr a b) = some (s.withFlags (subc (s.regs a) (s.regs b) s.flags.c).2) := rfl
@[simp] theorem step_cset (s : RS) (d : Reg) (c : SetCond) :
    step s (.cset d c) = some (s.set d (b2v (scHolds c s.flags))) := rfl
@[simp] theorem step_and3 (s : RS) (d a b : Reg) : step s (.and3 d a b) = some (s.set d (s.regs a &&& s.regs b)) := rfl
@[simp] theorem step_orr3 (s : RS) (d a b : Reg) : step s (.orr3 d a b) = some (s.set d (s.regs a ||| s.regs b)) := rfl
@[simp] theorem step_eor3 (s : RS) (d a b : Reg) : step s (.eor3 d a b) = some (s.set d (s.regs a ^^^ s.regs b)) := rfl
@[simp] theorem step_mvn (s : RS) (d a : Reg) : step s (.mvn d a) = some (s.set d (~~~ s.regs a)) := rfl
@[simp] theorem step_movReg (s : RS) (d a : Reg) : step s (.movReg d a) = some (s.set d (s.regs a)) := rfl
@[simp] theorem step_lsrImm (s : RS) (d a : Reg) (sh : Nat) : step s (.lsrImm d a sh) = some (s.set d (s.regs a >>> sh)) := rfl
@[simp] theorem step_lslImm (s : RS) (d a : Reg) (sh : Nat) : step s (.lslImm d a sh) = some (s.set d (s.regs a <<< sh)) := rfl
@[simp] theorem step_mulReg (s : RS) (d a b : Reg) : step s (.mulReg d a b) = some (s.set d (s.regs a * s.regs b)) := rfl
@[simp] theorem step_addLsr (s : RS) (d a b : Reg) (sh : Nat) :
    step s (.addLsr d a b sh) = some (s.set d (s.regs a + (s.regs b >>> sh))) := rfl
@[simp] theorem step_addLsl (s : RS) (d a b : Reg) (sh : Nat) :
    step s (.addLsl d a b sh) = some (s.set d (s.regs a + (s.regs b <<< sh))) := rfl
@[simp] theorem step_addLsl5 (s : RS) (d a b : Reg) :
    step s (.addLsl5 d a b) = some (s.set d (s.regs a + (s.regs b <<< 5))) := rfl
@[simp] theorem step_subReg (s : RS) (d a b : Reg) : step s (.subReg d a b) = some (s.set d (s.regs a - s.regs b)) := rfl
@[simp] theorem step_cselHi (s : RS) (d a b : Reg) :
    step s (.cselHi d a b) = some (s.set d (if bcHolds .hi s.flags then s.regs a else s.regs b)) := rfl

@[simp] theorem step_addSp (s : RS) (d : Reg) (n : Nat) :
    step s (.addSp d n) = some (s.set d (s.sp + BitVec.ofNat 64 n)) := rfl
@[simp] theorem step_addSpReg (s : RS) (r : Reg) :
    step s (.addSpReg r) = some (s.set r (s.sp + s.regs r)) := rfl
@[simp] theorem step_spSub (s : RS) (n : Nat) : step s (.spSub n) = some (s.withSp (s.sp - BitVec.ofNat 64 n)) := rfl
@[simp] theorem step_spAdd (s : RS) (n : Nat) : step s (.spAdd n) = some (s.withSp (s.sp + BitVec.ofNat 64 n)) := rfl
@[simp] theorem step_spSubReg (s : RS) (r : Reg) : step s (.spSubReg r) = some (s.withSp (s.sp - s.regs r)) := rfl
@[simp] theorem step_spAddReg (s : RS) (r : Reg) : step s (.spAddReg r) = some (s.withSp (s.sp + s.regs r)) := rfl
@[simp] theorem step_ldrOff (s : RS) (d b : Reg) (o : Nat) :
    step s (.ldrOff d b o) = some (s.set d (ld64 s.mem (s.regs b + BitVec.ofNat 64 o))) := rfl
@[simp] theorem step_ldpOff (s : RS) (r1 r2 b : Reg) (o : Nat) :
    step s (.ldpOff r1 r2 b o) =
      some ((s.set r1 (ld64 s.mem (s.regs b + BitVec.ofNat 64 o))).set r2
              (ld64 s.mem (s.regs b + BitVec.ofNat 64 (o + 8)))) := rfl
@[simp] theorem step_strOff (s : RS) (src b : Reg) (o : Nat) :
    step s (.strOff src b o) = some (s.store64 (s.regs b + BitVec.ofNat 64 o) (s.regs src)) := rfl
@[simp] theorem step_strBase (s : RS) (src b : Reg) :
    step s (.strBase src b) = some (s.store64 (s.regs b) (s.regs src)) := rfl
@[simp] theorem step_stpOff (s : RS) (r1 r2 b : Reg) (o : Nat) :
    step s (.stpOff r1 r2 b o) =
      some ((s.store64 (s.regs b + BitVec.ofNat 64 o) (s.regs r1)).store64
              (s.regs b + BitVec.ofNat 64 (o + 8)) (s.regs r2)) := rfl
@[simp] theorem step_strbBase (s : RS) (src b : Reg) :
    step s (.strbBase src b) = some (s.store8 (s.regs b) ((s.regs src).extractLsb' 0 8)) := rfl
@[simp] theorem step_rev (s : RS) (d a : Reg) : step s (.rev d a) = some (s.set d (rev64 (s.regs a))) := rfl
@[simp] theorem step_stpFpLr (s : RS) :
    step s .stpFpLr =
      some (((s.store64 (s.sp - BitVec.ofNat 64 16) (s.regs .x29)).store64
               (off (s.sp - BitVec.ofNat 64 16) 8) (s.regs .x30)).withSp (s.sp - BitVec.ofNat 64 16)) := rfl
@[simp] theorem step_ldpFpLr (s : RS) :
    step s .ldpFpLr =
      some (((s.set .x29 (ld64 s.mem s.sp)).set .x30 (ld64 s.mem (off s.sp 8))).withSp (off s.sp 16)) := rfl

@[simp] theorem ctrl_adds (d a b : Reg) : ctrl (.adds d a b) = none := rfl
@[simp] theorem ctrl_adcs (d a b : Reg) : ctrl (.adcs d a b) = none := rfl
@[simp] theorem ctrl_adc (d a b : Reg) : ctrl (.adc d a b) = none := rfl
@[simp] theorem ctrl_sbcs (d a b : Reg) : ctrl (.sbcs d a b) = none := rfl
@[simp] theorem ctrl_sbc (d a b : Reg) : ctrl (.sbc d a b) = none := rfl
@[simp] theorem ctrl_subsZr (a b : Reg) : ctrl (.subsZr a b) = none := rfl
@[simp] theorem ctrl_sbcsZr (a b : Reg) : ctrl (.sbcsZr a b) = none := rfl
@[simp] theorem ctrl_cset (d : Reg) (c : SetCond) : ctrl (.cset d c) = none := rfl
@[simp] theorem ctrl_and3 (d a b : Reg) : ctrl (.and3 d a b) = none := rfl
@[simp] theorem ctrl_orr3 (d a b : Reg) : ctrl (.orr3 d a b) = none := rfl
@[simp] theorem ctrl_eor3 (d a b : Reg) : ctrl (.eor3 d a b) = none := rfl
@[simp] theorem ctrl_mvn (d a : Reg) : ctrl (.mvn d a) = none := rfl
@[simp] theorem ctrl_movReg (d a : Reg) : ctrl (.movReg d a) = none := rfl
@[simp] theorem ctrl_lsrImm (d a : Reg) (sh : Nat) : ctrl (.lsrImm d a sh) = none := rfl
@[simp] theorem ctrl_lslImm (d a : Reg) (sh : Nat) : ctrl (.lslImm d a sh) = none := rfl
@[simp] theorem ctrl_mulReg (d a b : Reg) : ctrl (.mulReg d a b) = none := rfl
@[simp] theorem ctrl_addLsr (d a b : Reg) (sh : Nat) : ctrl (.addLsr d a b sh) = none := rfl
@[simp] theorem ctrl_addLsl (d a b : Reg) (sh : Nat) : ctrl (.addLsl d a b sh) = none := rfl
@[simp] theorem ctrl_addLsl5 (d a b : Reg) : ctrl (.addLsl5 d a b) = none := rfl
@[simp] theorem ctrl_subReg (d a b : Reg) : ctrl (.subReg d a b) = none := rfl
@[simp] theorem ctrl_cselHi (d a b : Reg) : ctrl (.cselHi d a b) = none := rfl
@[simp] theorem ctrl_ldrOff (d b : Reg) (o : Nat) : ctrl (.ldrOff d b o) = none := rfl
@[simp] theorem ctrl_ldrBase (d b : Reg) : ctrl (.ldrBase d b) = none := rfl
@[simp] theorem ctrl_ldpOff (r1 r2 b : Reg) (o : Nat) : ctrl (.ldpOff r1 r2 b o) = none := rfl
@[simp] theorem ctrl_strOff (src b : Reg) (o : Nat) : ctrl (.strOff src b o) = none := rfl
@[simp] theorem ctrl_strBase (src b : Reg) : ctrl (.strBase src b) = none := rfl
@[simp] theorem ctrl_stpOff (r1 r2 b : Reg) (o : Nat) : ctrl (.stpOff r1 r2 b o) = none := rfl
@[simp] theorem ctrl_strbBase (src b : Reg) : ctrl (.strbBase src b) = none := rfl
@[simp] theorem ctrl_rev (d a : Reg) : ctrl (.rev d a) = none := rfl
@[simp] theorem ctrl_addSp (d : Reg) (n : Nat) : ctrl (.addSp d n) = none := rfl
@[simp] theorem ctrl_spSub (n : Nat) : ctrl (.spSub n) = none := rfl
@[simp] theorem ctrl_spAdd (n : Nat) : ctrl (.spAdd n) = none := rfl
@[simp] theorem ctrl_stpFpLr : ctrl .stpFpLr = none := rfl
@[simp] theorem ctrl_spSubReg (r : Reg) : ctrl (.spSubReg r) = none := rfl
@[simp] theorem ctrl_spAddReg (r : Reg) : ctrl (.spAddReg r) = none := rfl
@[simp] theorem ctrl_addSpReg (r : Reg) : ctrl (.addSpReg r) = none := rfl
@[simp] theorem ctrl_strbOff (src b : Reg) (o : Nat) : ctrl (.strbOff src b o) = none := rfl
@[simp] theorem ctrl_ldpFpLr : ctrl .ldpFpLr = none := rfl

/-- `run` over a data instruction, as simp uses it. -/
@[simp] theorem run_cons_data (H : Helpers) (i : AInstr) (rest : List AInstr) (s : RS) (hc : ctrl i = none) :
    run H (i :: rest) s = match step s i with | some s' => run H rest s' | none => .stuck := by
  simp [run, hc]

@[simp] theorem ctrl_movzImm (r : Reg) (i : Nat) : ctrl (.movzImm r i) = none := rfl
@[simp] theorem ctrl_movImm (r : Reg) (i : Nat) : ctrl (.movImm r i) = none := rfl
@[simp] theorem ctrl_movkImm (r : Reg) (i hw : Nat) : ctrl (.movkImm r i hw) = none := rfl
@[simp] theorem ctrl_subsImm (d a : Reg) (i : Nat) : ctrl (.subsImm d a i) = none := rfl
@[simp] theorem ctrl_subsReg (d a b : Reg) : ctrl (.subsReg d a b) = none := rfl
@[simp] theorem ctrl_addReg (d a b : Reg) : ctrl (.addReg d a b) = none := rfl
@[simp] theorem ctrl_subImm (d a : Reg) (i : Nat) : ctrl (.subImm d a i) = none := rfl
@[simp] theorem ctrl_addImm (d a : Reg) (i : Nat) : ctrl (.addImm d a i) = none := rfl
@[simp] theorem ctrl_cmpImm (a : Reg) (i : Nat) : ctrl (.cmpImm a i) = none := rfl
@[simp] theorem ctrl_cmpReg (a b : Reg) : ctrl (.cmpReg a b) = none := rfl

/-- The label a control instruction references, if any. -/
def refLabel (i : AInstr) : Option String :=
  match ctrl i with
  | some (.jump l) | some (.cond _ l) => some l
  | _ => none

/-- A closed fragment: every forward reference finds its label inside the
    fragment, so appending more code cannot capture it. -/
def closed : List AInstr → Prop
  | [] => True
  | i :: rest => (∀ l, refLabel i = some l → skipTo l rest ≠ []) ∧ closed rest

theorem skipTo_append_of_found (l : String) (xs ys : List AInstr) (h : skipTo l xs ≠ []) :
    skipTo l (xs ++ ys) = skipTo l xs ++ ys := by
  induction xs with
  | nil => exact absurd rfl h
  | cons x rest ih =>
    cases x with
    | label t =>
      simp only [List.cons_append, skipTo]
      split
      · simp
      · simp only [skipTo] at h; rw [ite_eq_right (by assumption)] at h; exact ih h
    | _ => simp only [List.cons_append, skipTo] at h ⊢; exact ih h

/-- `skipTo` returns a suffix. -/
theorem skipTo_suffix (l : String) (xs : List AInstr) : (skipTo l xs).IsSuffix xs := by
  induction xs with
  | nil => simp [skipTo]
  | cons x rest ih =>
    cases x with
    | label t =>
      simp only [skipTo]
      split
      · exact List.suffix_refl _
      · exact ih.trans (List.suffix_cons _ _)
    | _ => simp only [skipTo]; exact ih.trans (List.suffix_cons _ _)

theorem closed_suffix {xs ys : List AInstr} (h : closed ys) (hs : xs.IsSuffix ys) : closed xs := by
  obtain ⟨pre, rfl⟩ := hs
  induction pre with
  | nil => simpa using h
  | cons a pre ih => exact ih h.2

/-- A fragment then more: `done` continues into the rest. -/
theorem run_append (H : Helpers) (p q : List AInstr) (s : RS) (hc : closed p) :
    run H (p ++ q) s =
      match run H p s with
      | .done s' => run H q s'
      | .ret s' => .ret s'
      | .fault sym s' => .fault sym s'
      | .stuck => .stuck := by
  induction p, s using run.induct H with
  | case1 s => simp
  | case2 i rest s hi => simp [run, hi]
  | case3 i rest s hi ih => simp only [List.cons_append, run, hi]; exact ih hc.2
  | case4 i rest s l hi ih =>
    simp only [List.cons_append, run, hi]
    rw [skipTo_append_of_found l rest q (hc.1 l (by simp [refLabel, hi]))]
    exact ih (closed_suffix hc.2 (skipTo_suffix l rest))
  | case5 i rest s c l hi ht ih =>
    simp only [List.cons_append, run, hi, ite_eq_left ht]
    rw [skipTo_append_of_found l rest q (hc.1 l (by simp [refLabel, hi]))]
    exact ih (closed_suffix hc.2 (skipTo_suffix l rest))
  | case6 i rest s c l hi ht ih =>
    simp only [List.cons_append, run, hi, ite_eq_right ht]; exact ih hc.2
  | case7 i rest s sym hi => simp [run, hi]
  | case8 i rest s c sym hi ht => simp [run, hi, ht]
  | case9 i rest s c sym hi ht ih => simp only [List.cons_append, run, hi, ite_eq_right ht]; exact ih hc.2
  | case10 i rest s h hi ih => simp only [List.cons_append, run, hi]; exact ih hc.2
  | case11 i rest s hi s' hs ih => simp only [List.cons_append, run, hi, hs]; exact ih hc.2
  | case12 i rest s hi hs => simp [hi, hs]

end Evm.CL.AsmRun
