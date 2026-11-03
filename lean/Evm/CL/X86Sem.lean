/-
  Evm.CL.X86Sem — an x86-64 machine semantics for the instructions
  `X86Items.x86Items` produces, and the LOWERING SIMULATION: running the
  lowering of an `AInstr` on the x86-64 machine tracks `AsmRun.step` on the
  ARM-flavoured machine, under a relation indexed by

    * the LIVE set `L` — the registers whose x86 homes hold their values
      (several `Reg`s share a home: x1/x15 → rdx, x2/x17 → rsi, x3/x4/x16 →
      rdi; `X86Alias.no_alias_hazards` is the static check that no two are
      live together, this is the semantic counterpart), and
    * the flag PROVENANCE — after a `sub`-type instruction x86's CF is the
      borrow, ARM's C the no-borrow; after an `add`-type both are the carry.
      The lowering of a condition (`bcondXc`) is correct under `sub`/`logic`
      provenance for every condition, and under `add` provenance only for
      the carry-consuming forms (`adc`, `bcsOog`). The relation says which
      is in force, so a mis-lowered consumer cannot be proven.

  NOS (x10-x13) has no x86 register: it is read from
  `[r12 + r13 - (64 - 8l)]`; a NOS register is "live" when that word holds
  its value. Memory is byte-addressed little-endian on both sides
  (`AsmRun.Mem`), so stores relate directly.
-/

import Evm.CL.AsmRun
import Evm.CL.X86Items
import Evm.CL.X86JIT

namespace Evm.CL.X86Sem

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.X86Encode Evm.CL.X86Items

/-! ## The machine -/

structure XFlags where
  cf : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving Repr, DecidableEq

structure XS where
  regs  : XReg → BitVec 64
  flags : XFlags
  mem   : AsmRun.Mem

def XS.set (x : XS) (r : XReg) (v : BitVec 64) : XS :=
  { x with regs := fun r' => if r' = r then v else x.regs r' }
def XS.withFlags (x : XS) (f : XFlags) : XS := { x with flags := f }
def XS.store64 (x : XS) (a v : BitVec 64) : XS := { x with mem := st64 x.mem a v }
def XS.store8 (x : XS) (a : BitVec 64) (v : BitVec 8) : XS := { x with mem := st8 x.mem a v }

@[simp] theorem XS.set_regs (x : XS) (r : XReg) (v : BitVec 64) (r' : XReg) :
    (x.set r v).regs r' = if r' = r then v else x.regs r' := rfl
@[simp] theorem XS.set_flags (x : XS) (r : XReg) (v : BitVec 64) : (x.set r v).flags = x.flags := rfl
@[simp] theorem XS.set_mem (x : XS) (r : XReg) (v : BitVec 64) : (x.set r v).mem = x.mem := rfl
@[simp] theorem XS.withFlags_regs (x : XS) (f : XFlags) : (x.withFlags f).regs = x.regs := rfl
@[simp] theorem XS.withFlags_flags (x : XS) (f : XFlags) : (x.withFlags f).flags = f := rfl
@[simp] theorem XS.withFlags_mem (x : XS) (f : XFlags) : (x.withFlags f).mem = x.mem := rfl
@[simp] theorem XS.store64_regs (x : XS) (a v : BitVec 64) : (x.store64 a v).regs = x.regs := rfl
@[simp] theorem XS.store64_flags (x : XS) (a v : BitVec 64) : (x.store64 a v).flags = x.flags := rfl
@[simp] theorem XS.store64_mem (x : XS) (a v : BitVec 64) : (x.store64 a v).mem = st64 x.mem a v := rfl
@[simp] theorem XS.store8_regs (x : XS) (a : BitVec 64) (v : BitVec 8) : (x.store8 a v).regs = x.regs := rfl
@[simp] theorem XS.store8_flags (x : XS) (a : BitVec 64) (v : BitVec 8) : (x.store8 a v).flags = x.flags := rfl
@[simp] theorem XS.store8_mem (x : XS) (a : BitVec 64) (v : BitVec 8) : (x.store8 a v).mem = st8 x.mem a v := rfl

/-- The effective address of a memory operand. -/
def ea (x : XS) (m : X86Encode.Mem) : BitVec 64 :=
  x.regs m.base + (match m.index with | some i => x.regs i * BitVec.ofNat 64 m.scale | none => 0) +
    BitVec.ofInt 64 m.disp

/-- Condition codes (Intel SDM, Appendix B). Parity is not modelled (never
    emitted); it is given a fixed value to keep the function total. -/
def xcHolds : XCond → XFlags → Bool
  | .o, f => f.of   | .no, f => !f.of
  | .b, f => f.cf   | .ae, f => !f.cf
  | .e, f => f.zf   | .ne, f => !f.zf
  | .be, f => f.cf || f.zf | .a, f => !(f.cf || f.zf)
  | .s, f => f.sf   | .ns, f => !f.sf
  | .p, _ => false  | .np, _ => true
  | .l, f => f.sf != f.of | .ge, f => f.sf == f.of
  | .le, f => f.zf || (f.sf != f.of) | .g, f => !f.zf && (f.sf == f.of)

/-- `sub`/`cmp`: CF is the borrow. -/
def subXF (a b : BitVec 64) : XFlags :=
  let r := a - b
  { cf := decide (a.toNat < b.toNat), zf := r = 0, sf := r.msb, of := (a.msb != b.msb) && (r.msb != a.msb) }

/-- `add`: CF is the carry. -/
def addXF (a b : BitVec 64) : XFlags :=
  let r := a + b
  { cf := decide (a.toNat + b.toNat ≥ 2 ^ 64), zf := r = 0, sf := r.msb, of := (a.msb == b.msb) && (r.msb != a.msb) }

/-- `adc`: `a + b + CF`, CF the carry out (the 65-bit sum's top bit). -/
def adcXF (a b : BitVec 64) (c : Bool) : XFlags :=
  let r := a + b + (if c then 1 else 0)
  { cf := (a.zeroExtend 65 + b.zeroExtend 65 + bit c).msb, zf := r = 0, sf := r.msb,
    of := (a.msb == b.msb) && (r.msb != a.msb) }

/-- `sbb`: `a - b - CF`, CF the borrow out (`a < b + CF` in 65 bits). -/
def sbbXF (a b : BitVec 64) (c : Bool) : XFlags :=
  let r := a - b - (if c then 1 else 0)
  { cf := !BitVec.ule (b.zeroExtend 65 + bit c) (a.zeroExtend 65), zf := r = 0, sf := r.msb,
    of := (a.msb != b.msb) && (r.msb != a.msb) }

/-- `and`/`or`/`xor`/`test`: CF = OF = 0. -/
def logicXF (r : BitVec 64) : XFlags := { cf := false, zf := r = 0, sf := r.msb, of := false }

/-- The value and flags of a two-operand ALU op. `cmp` writes no register. -/
def alu (o : AluOp) (a b : BitVec 64) (cf : Bool) : BitVec 64 × XFlags :=
  match o with
  | .add  => (a + b, addXF a b)
  | .sub  => (a - b, subXF a b)
  | .cmp  => (a, subXF a b)
  | .adc  => (a + b + (if cf then 1 else 0), adcXF a b cf)
  | .sbb  => (a - b - (if cf then 1 else 0), sbbXF a b cf)
  | .and_ => (a &&& b, logicXF (a &&& b))
  | .or_  => (a ||| b, logicXF (a ||| b))
  | .xor_ => (a ^^^ b, logicXF (a ^^^ b))

def aluR (x : XS) (o : AluOp) (d : XReg) (b : BitVec 64) : XS :=
  let (v, f) := alu o (x.regs d) b x.flags.cf
  match o with
  | .cmp => x.withFlags f
  | _    => (x.set d v).withFlags f

/-- Flags after a shift or `imul`: defined by the SDM only in part, never
    consumed by any emitted program (`X86FlagProv`). Modelled as an opaque
    function so that nothing can be proven about them. -/
@[irreducible] def clobXF (f : XFlags) (v : BitVec 64) : XFlags :=
  { cf := false, zf := v = 0, sf := v.msb, of := f.of }

def xstep (x : XS) : XInsn → Option XS
  | .movRR d s      => some (x.set d (x.regs s))
  | .movRM d m      => some (x.set d (ld64 x.mem (ea x m)))
  | .movMR m s      => some (x.store64 (ea x m) (x.regs s))
  | .movRI d i      => some (x.set d (BitVec.ofInt 64 i))
  | .aluRR o d s    => some (aluR x o d (x.regs s))
  | .aluRM o d m    => some (aluR x o d (ld64 x.mem (ea x m)))
  | .aluMR o m s    =>
      let a := ea x m
      let (v, f) := alu o (ld64 x.mem a) (x.regs s) x.flags.cf
      match o with
      | .cmp => some (x.withFlags f)
      | _    => some ((x.store64 a v).withFlags f)
  | .aluRI o d i    => some (aluR x o d (BitVec.ofInt 64 i))
  | .aluMI o m i    =>
      let a := ea x m
      let (v, f) := alu o (ld64 x.mem a) (BitVec.ofInt 64 i) x.flags.cf
      match o with
      | .cmp => some (x.withFlags f)
      | _    => some ((x.store64 a v).withFlags f)
  | .shiftRI o d n  =>
      let v := match o with
        | .shl => x.regs d <<< n | .shr => x.regs d >>> n | .sar => BitVec.sshiftRight (x.regs d) n
      some ((x.set d v).withFlags (clobXF x.flags v))
  | .imulRR d s     => some ((x.set d (x.regs d * x.regs s)).withFlags (clobXF x.flags (x.regs d * x.regs s)))
  | .lea d m        => some (x.set d (ea x m))
  | .cmovRR c d s   => some (if xcHolds c x.flags then x.set d (x.regs s) else x)
  | .bswap r        => some (x.set r (rev64 (x.regs r)))
  | .notR r         => some (x.set r (~~~ x.regs r))
  | .setcc c r      => some (x.set r ((x.regs r &&& ~~~(0xff : BitVec 64)) ||| (if xcHolds c x.flags then 1 else 0)))
  | .movzxB d s     => some (x.set d ((x.regs s).extractLsb' 0 8 |>.zeroExtend 64))
  | .movzxBM d m    => some (x.set d ((x.mem (ea x m)).zeroExtend 64))
  | .movMR8 m s     => some (x.store8 (ea x m) ((x.regs s).extractLsb' 0 8))
  | .movMI m i      => some (x.store64 (ea x m) (BitVec.ofInt 64 i))
  | .testRI r i     => some (x.withFlags (logicXF (x.regs r &&& BitVec.ofInt 64 i)))
  | .cmpRI32 r i    => some (x.withFlags (subXF ((x.regs r).extractLsb' 0 32 |>.zeroExtend 64) (BitVec.ofInt 64 i)))
  | _ => none

/-- Straight-line items: instructions only (labels and branches: `X86Run`). -/
def xsteps (x : XS) : List XItem → Option XS
  | [] => some x
  | .I i :: rest => match xstep x i with | some x' => xsteps x' rest | none => none
  | _ :: _ => none

@[simp] theorem xsteps_nil (x : XS) : xsteps x [] = some x := rfl
theorem xsteps_cons (x x' : XS) (i : XInsn) (rest : List XItem) (h : xstep x i = some x') :
    xsteps x (.I i :: rest) = xsteps x' rest := by simp [xsteps, h]

/-! ## The relation -/

/-- Flag provenance: which instruction kind last wrote the flags. -/
inductive Prov where
  | sub | add | logic | unknown
  deriving DecidableEq, Repr

def nosReg : Nat → Reg
  | 0 => .x10 | 1 => .x11 | 2 => .x12 | _ => .x13

/-- The x86 value of an ARM register: its home, or the NOS word in memory. -/
def valOf (x : XS) (r : Reg) : Option (BitVec 64) :=
  match xreg? r, nosLimb r with
  | some xr, _ => some (x.regs xr)
  | none, some l => some (ld64 x.mem (ea x (nosMemX l)))
  | none, none => none

/-- The flags agree, under a provenance. -/
def FlagsRel : Prov → Flags → XFlags → Prop
  | .sub, f, xf => xf.cf = !f.c ∧ xf.zf = f.z ∧ xf.sf = f.n ∧ xf.of = f.v
  | .add, f, xf => xf.cf = f.c ∧ xf.zf = f.z ∧ xf.sf = f.n ∧ xf.of = f.v
  | .logic, f, xf => xf.cf = false ∧ f.c = false ∧ xf.zf = f.z ∧ xf.sf = f.n ∧ xf.of = false ∧ f.v = false
  | .unknown, _, _ => True

/-- The simulation relation: every live register's x86 value is its ARM
    value, rsp is sp, memory is memory, flags per the provenance. -/
structure Rel (L : List Reg) (p : Prov) (s : RS) (x : XS) : Prop where
  regs  : ∀ r ∈ L, valOf x r = some (s.regs r)
  sp    : x.regs .rsp = s.sp
  mem   : x.mem = s.mem
  flags : FlagsRel p s.flags x.flags

/-! ## Conditions -/

/-- Every lowered condition is right under `sub` provenance. -/
theorem cond_sub (c : BCond) (f : Flags) (xf : XFlags) (h : FlagsRel .sub f xf) :
    xcHolds (bcondXc c) xf = bcHolds c f := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases c <;> simp [bcondXc, xcHolds, bcHolds, h1, h2, h3, h4]

/-- Under `add` provenance only the equality and signed conditions agree
    (x86's CF is the carry, ARM's `lo` is the carry CLEAR). -/
theorem cond_add_eq (f : Flags) (xf : XFlags) (h : FlagsRel .add f xf) :
    xcHolds .e xf = bcHolds .eq f ∧ xcHolds .ne xf = bcHolds .ne f ∧ xcHolds .l xf = bcHolds .lt f := by
  obtain ⟨_, h2, h3, h4⟩ := h
  simp [xcHolds, bcHolds, h2, h3, h4]

/-- Under `logic` provenance likewise: `tst` clears C on ARM, so `lo` HOLDS
    there while x86's `b` (CF) does not — the carry conditions after a `tst`
    would be mis-lowered, and are therefore not provable here. -/
theorem cond_logic_eq (f : Flags) (xf : XFlags) (h : FlagsRel .logic f xf) :
    xcHolds .e xf = bcHolds .eq f ∧ xcHolds .ne xf = bcHolds .ne f ∧ xcHolds .l xf = bcHolds .lt f := by
  obtain ⟨_, _, h2, h3, h4, h4'⟩ := h
  simp [xcHolds, bcHolds, h2, h3, h4, h4']

/-- The negated condition is the negation. -/
theorem nbcond_eq (c : BCond) (xf : XFlags) : xcHolds (nbcondXc c) xf = !xcHolds (bcondXc c) xf := by
  cases c <;> simp only [nbcondXc, bcondXc, xcHolds] <;>
    first | rfl | (cases xf.sf <;> cases xf.of <;> rfl) | (cases xf.cf <;> cases xf.zf <;> rfl)

/-- `cset`'s conditions. -/
theorem setcond_sub (c : SetCond) (f : Flags) (xf : XFlags) (h : FlagsRel .sub f xf) :
    xcHolds (setcondXc c) xf = scHolds c f := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases c <;> simp [setcondXc, xcHolds, scHolds, h1, h2, h3, h4]

theorem setcond_logic_eq (f : Flags) (xf : XFlags) (h : FlagsRel .logic f xf) :
    xcHolds (setcondXc .eq) xf = scHolds .eq f ∧ xcHolds (setcondXc .lt) xf = scHolds .lt f := by
  obtain ⟨_, _, h2, h3, h4, h4'⟩ := h
  simp [setcondXc, xcHolds, scHolds, h2, h3, h4, h4']

/-! ## Flags: the ARM and x86 computations agree -/

theorem subXF_rel (a b : BitVec 64) : FlagsRel .sub (subFlags a b) (subXF a b) := by
  refine ⟨?_, rfl, rfl, rfl⟩
  show decide (a.toNat < b.toNat) = !decide (b ≤ a)
  simp only [BitVec.le_def]
  by_cases h : b.toNat ≤ a.toNat <;> simp [h] <;> omega

theorem addXF_rel (a b : BitVec 64) : FlagsRel .add (addFlags a b) (addXF a b) := ⟨rfl, rfl, rfl, rfl⟩

theorem logicXF_rel (r : BitVec 64) : FlagsRel .logic (logicFlags r) (logicXF r) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `adcs` (ARM, `addc` with carry in C) against `adc` with CF = C. -/
theorem adc_rel (a b : BitVec 64) (c : Bool) :
    (addc a b c).1 = a + b + (if c then 1 else 0) ∧ FlagsRel .add (addc a b c).2 (adcXF a b c) := by
  have hr : (a.zeroExtend 65 + b.zeroExtend 65 + bit c).truncate 64 = a + b + (if c then 1 else 0) := by
    cases c <;> simp [bit] <;> bv_decide
  refine ⟨hr, rfl, ?_, ?_, ?_⟩ <;> simp only [adcXF, addc] <;> rw [hr]

/-- `sbcs` (ARM, `subc`: `a - b - ¬C`) against `sbb` with CF = ¬C. -/
theorem sbb_rel (a b : BitVec 64) (c : Bool) :
    (subc a b c).1 = a - b - (if !c then 1 else 0) ∧ FlagsRel .sub (subc a b c).2 (sbbXF a b (!c)) := by
  have hr : (if c then a - b else a - b - 1) = a - b - (if !c then 1 else 0) := by cases c <;> simp
  refine ⟨hr, rfl, ?_, ?_, ?_⟩ <;> simp only [sbbXF, subc] <;> rw [hr]

/-! ## Liveness bookkeeping -/

/-- Two different registers with one home. -/
def aliasedH (a b : Reg) : Bool :=
  a != b && (match xreg? a, xreg? b with | some x, some y => x == y | _, _ => false)

def isNos (r : Reg) : Bool := (nosLimb r).isSome

/-- What a write to `d` invalidates: its aliases, and (when `d`'s home is the
    NOS base or index register) the NOS words. -/
def clobbers (d r : Reg) : Bool :=
  aliasedH d r || (isNos r && (xreg? d == some .r12 || xreg? d == some .r13))

/-- The live set after a register write. -/
def upd (L : List Reg) (d : Reg) : List Reg := d :: L.filter (fun r => !clobbers d r)

/-- The live set after a memory store: the NOS words are no longer trusted. -/
def updStore (L : List Reg) : List Reg := L.filter (fun r => !isNos r)

theorem valOf_reg (x : XS) (r : Reg) (xr : XReg) (h : xreg? r = some xr) : valOf x r = some (x.regs xr) := by
  simp [valOf, h]

theorem valOf_nos (x : XS) (r : Reg) (l : Nat) (h : xreg? r = none) (hl : nosLimb r = some l) :
    valOf x r = some (ld64 x.mem (ea x (nosMemX l))) := by
  simp [valOf, h, hl]

theorem Rel.val {L : List Reg} {p : Prov} {s : RS} {x : XS} (hR : Rel L p s x) (r : Reg) (hr : r ∈ L) (xr : XReg)
    (h : xreg? r = some xr) : x.regs xr = s.regs r := by
  have := hR.regs r hr; rw [valOf_reg x r xr h] at this; exact Option.some.inj this

theorem nosLimb_some_xreg_none (r : Reg) (l : Nat) (h : nosLimb r = some l) : xreg? r = none := by
  cases r <;> simp_all [nosLimb, xreg?]

theorem nosLimb_lt (r : Reg) (l : Nat) (h : nosLimb r = some l) : l < 4 := by
  cases r <;> simp_all [nosLimb] <;> omega

theorem Rel.valNos {L : List Reg} {p : Prov} {s : RS} {x : XS} (hR : Rel L p s x) (r : Reg) (hr : r ∈ L) (l : Nat)
    (h : nosLimb r = some l) : ld64 x.mem (ea x (nosMemX l)) = s.regs r := by
  have := hR.regs r hr; rw [valOf_nos x r l (nosLimb_some_xreg_none r l h) h] at this; exact Option.some.inj this

/-- The x86 value of an operand register, however it is homed. -/
def opVal (x : XS) (r : Reg) : BitVec 64 := (valOf x r).getD 0

theorem Rel.opVal {L : List Reg} {p : Prov} {s : RS} {x : XS} (hR : Rel L p s x) (r : Reg) (hr : r ∈ L) :
    opVal x r = s.regs r := by
  simp [X86Sem.opVal, hR.regs r hr]

/-- `aluFrom o d src` reads `opVal x src`, when `src` has a home or is NOS. -/
theorem aluFrom_step (x : XS) (o : AluOp) (d : XReg) (src : Reg) (hsrc : (valOf x src).isSome) :
    ∃ i, aluFrom o d src = .I i ∧ xstep x i = some (aluR x o d (opVal x src)) := by
  unfold aluFrom
  cases h1 : xreg? src with
  | some xr => exact ⟨_, rfl, by simp [xstep, opVal, valOf, h1]⟩
  | none =>
    cases h2 : nosLimb src with
    | some l => exact ⟨_, rfl, by simp [xstep, opVal, valOf, h1, h2]⟩
    | none => simp [valOf, h1, h2] at hsrc

theorem movFrom_step (x : XS) (d : XReg) (src : Reg) (hsrc : (valOf x src).isSome) :
    ∃ i, movFrom d src = .I i ∧ xstep x i = some (x.set d (opVal x src)) := by
  unfold movFrom
  cases h1 : xreg? src with
  | some xr => exact ⟨_, rfl, by simp [xstep, opVal, valOf, h1]⟩
  | none =>
    cases h2 : nosLimb src with
    | some l => exact ⟨_, rfl, by simp [xstep, opVal, valOf, h1, h2]⟩
    | none => simp [valOf, h1, h2] at hsrc

theorem Rel.isSome {L : List Reg} {p : Prov} {s : RS} {x : XS} (hR : Rel L p s x) (r : Reg) (hr : r ∈ L) :
    (valOf x r).isSome := by rw [hR.regs r hr]; rfl

/-! ## The relation through one write -/

/-- `ea` of a NOS word does not move when the written home is neither r12 nor r13. -/
theorem ea_nos_set (x : XS) (xd : XReg) (v : BitVec 64) (l : Nat) (h12 : xd ≠ .r12) (h13 : xd ≠ .r13) :
    ea (x.set xd v) (nosMemX l) = ea x (nosMemX l) := by
  simp [ea, nosMemX, XS.set, h12.symm, h13.symm]

theorem valOf_set (x : XS) (d r : Reg) (xd : XReg) (hd : xreg? d = some xd) (v : BitVec 64)
    (hc : clobbers d r = false) (hne : r ≠ d) : valOf (x.set xd v) r = valOf x r := by
  simp only [clobbers, aliasedH, isNos, Bool.or_eq_false_iff, Bool.and_eq_false_iff, bne_eq_false_iff_eq,
             Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hc
  obtain ⟨h1, h2⟩ := hc
  unfold valOf
  cases hr : xreg? r with
  | some xr =>
    have hne' : xr ≠ xd := by
      intro e; subst e
      rcases h1 with h1 | h1
      · exact hne h1.symm
      · rw [hd, hr] at h1; simp at h1
    simp [XS.set, hne']
  | none =>
    cases hl : nosLimb r with
    | some l =>
      rcases h2 with h2 | h2
      · rw [hl] at h2; simp at h2
      · simp only [beq_eq_false_iff_ne, ne_eq] at h2
        rw [hd] at h2
        have h12 : xd ≠ .r12 := fun e => h2.1 (by rw [e])
        have h13 : xd ≠ .r13 := fun e => h2.2 (by rw [e])
        simp only [XS.set_mem]
        rw [ea_nos_set x xd v l h12 h13]
    | none => rfl

/-- A register write on both sides. -/
theorem Rel.setReg {L : List Reg} {p : Prov} {s : RS} {x : XS} (hR : Rel L p s x) (d : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (v : BitVec 64) (hsp : xd ≠ .rsp) :
    Rel (upd L d) p (s.set d v) (x.set xd v) := by
  refine ⟨?_, ?_, hR.mem, hR.flags⟩
  · intro r hr
    simp only [upd, List.mem_cons, List.mem_filter, Bool.not_eq_true'] at hr
    rcases hr with rfl | ⟨hr, hc⟩
    · rw [valOf_reg _ _ _ hd]; simp [XS.set, RS.set]
    · by_cases hne : r = d
      · subst hne; rw [valOf_reg _ _ _ hd]; simp [XS.set, RS.set]
      · rw [valOf_set x d r xd hd v hc hne, hR.regs r hr]; simp [RS.set, hne]
  · simp [XS.set, hsp.symm]; exact hR.sp

/-- Flags on both sides. -/
theorem Rel.setFlags {L : List Reg} {p : Prov} {s : RS} {x : XS} (hR : Rel L p s x) (p' : Prov)
    (f : Flags) (xf : XFlags) (h : FlagsRel p' f xf) : Rel L p' (s.withFlags f) (x.withFlags xf) :=
  ⟨fun r hr => by simpa [valOf, ea, XS.withFlags] using hR.regs r hr, hR.sp, hR.mem, h⟩

/-- Forgetting the provenance. -/
theorem Rel.forget {L : List Reg} {p : Prov} {s : RS} {x : XS} (hR : Rel L p s x) (xf : XFlags) :
    Rel L .unknown s (x.withFlags xf) :=
  ⟨fun r hr => by simpa [valOf, ea, XS.withFlags] using hR.regs r hr, hR.sp, hR.mem, trivial⟩

theorem Rel.mono {L L' : List Reg} {p : Prov} {s : RS} {x : XS} (hR : Rel L p s x) (h : ∀ r ∈ L', r ∈ L) :
    Rel L' p s x := ⟨fun r hr => hR.regs r (h r hr), hR.sp, hR.mem, hR.flags⟩

theorem mem_upd_self (L : List Reg) (d : Reg) : d ∈ upd L d := by simp [upd]
theorem mem_upd_of_mem (L : List Reg) (d r : Reg) (hr : r ∈ L) (hc : clobbers d r = false) : r ∈ upd L d := by
  simp [upd, hr, hc]

/-- A write to a home that is not rsp. -/
theorem home_ne_rsp (d : Reg) (xd : XReg) (h : xreg? d = some xd) : xd ≠ .rsp := by
  intro e; subst e; cases d <;> simp [xreg?] at h

theorem ofInt_ofNat (i : Nat) : BitVec.ofInt 64 (Int.ofNat i) = BitVec.ofNat 64 i := by
  rfl

/-! ## The simulation, instruction by instruction

    Each lemma: from `Rel L p s x`, with the instruction's sources live and
    its aliasing side conditions, the lowering runs to a state related to the
    ARM step, at the updated live set and the new provenance. -/

/-- The state after an ARM `set`-only step, as the lemmas state it. -/
theorem xsteps_single (x x' : XS) (i : XInsn) (h : xstep x i = some x') : xsteps x [.I i] = some x' := by
  simp [xsteps, h]

theorem sim_movImm (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (i : Nat) :
    ∃ x', xsteps x (x86Items (.movImm d i)) = some x' ∧ Rel (upd L d) p (s.set d (BitVec.ofNat 64 i)) x' := by
  refine ⟨x.set (dst d) (BitVec.ofInt 64 (Int.ofNat i)), xsteps_single _ _ _ rfl, ?_⟩
  have := hR.setReg d xd hd (BitVec.ofNat 64 i) (home_ne_rsp d xd hd)
  simpa [dst, hd, ofInt_ofNat] using this

theorem sim_movzImm (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (i : Nat) :
    ∃ x', xsteps x (x86Items (.movzImm d i)) = some x' ∧ Rel (upd L d) p (s.set d (BitVec.ofNat 64 i)) x' := by
  refine ⟨x.set (dst d) (BitVec.ofInt 64 (Int.ofNat i)), xsteps_single _ _ _ rfl, ?_⟩
  have := hR.setReg d xd hd (BitVec.ofNat 64 i) (home_ne_rsp d xd hd)
  simpa [dst, hd, ofInt_ofNat] using this

theorem sim_movReg (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) :
    ∃ x', xsteps x (x86Items (.movReg d a)) = some x' ∧ Rel (upd L d) p (s.set d (s.regs a)) x' := by
  obtain ⟨i, hi, hstep⟩ := movFrom_step x (dst d) a (hR.isSome a ha)
  refine ⟨_, by simp only [x86Items, hi]; exact xsteps_single _ _ _ hstep, ?_⟩
  rw [hR.opVal a ha]
  have := hR.setReg d xd hd (s.regs a) (home_ne_rsp d xd hd)
  simpa [dst, hd] using this

/-- `twoOp o d a b comm` at the x86 side, for a register-destination op. -/
theorem twoOp_run (x : XS) (o : AluOp) (d a b : Reg) (comm : Bool) (xd : XReg) (hd : xreg? d = some xd)
    (ha : (valOf x a).isSome) (hb : (valOf x b).isSome)
    (hside : d = a ∨ (d = b ∧ comm = true) ∨ (d ≠ b ∧ clobbers d b = false)) :
    ∃ x', xsteps x (twoOp o d a b comm) = some x' ∧
      ((d = a ∧ x' = aluR x o xd (opVal x b)) ∨
       (d ≠ a ∧ d = b ∧ comm = true ∧ x' = aluR x o xd (opVal x a)) ∨
       (d ≠ a ∧ d ≠ b ∧ x' = aluR (x.set xd (opVal x a)) o xd (opVal x b))) := by
  unfold twoOp
  by_cases hda : d = a
  · subst hda
    obtain ⟨i, hi, hstep⟩ := aluFrom_step x o (dst d) b hb
    refine ⟨aluR x o (dst d) (opVal x b), ?_, Or.inl ⟨rfl, by simp [dst, hd]⟩⟩
    simp only [beq_self_eq_true, ite_true, hi]; exact xsteps_single _ _ _ hstep
  · rw [if_neg (by simp [hda])]
    by_cases hdb : d = b
    · rcases hside with h | ⟨_, hc⟩ | ⟨h, _⟩
      · exact absurd h hda
      · subst hdb
        obtain ⟨i, hi, hstep⟩ := aluFrom_step x o (dst d) a ha
        refine ⟨aluR x o (dst d) (opVal x a), ?_, Or.inr (Or.inl ⟨hda, rfl, hc, by simp [dst, hd]⟩)⟩
        simp only [beq_self_eq_true, hc, Bool.and_true, ite_true, hi]; exact xsteps_single _ _ _ hstep
      · exact absurd hdb h
    · rw [if_neg (by simp [hdb]), if_neg (by simp [hdb])]
      obtain ⟨i1, hi1, hstep1⟩ := movFrom_step x (dst d) a ha
      have hb' : (valOf (x.set (dst d) (opVal x a)) b).isSome := by
        rcases hside with h | ⟨h, _⟩ | ⟨_, hc⟩
        · exact absurd h hda
        · exact absurd h hdb
        · rw [dst, hd, Option.getD_some, valOf_set x d b xd hd _ hc (Ne.symm hdb)]; exact hb
      obtain ⟨i2, hi2, hstep2⟩ := aluFrom_step (x.set (dst d) (opVal x a)) o (dst d) b hb'
      refine ⟨_, by rw [hi1, hi2, xsteps_cons _ _ _ _ hstep1]; exact xsteps_single _ _ _ hstep2,
              Or.inr (Or.inr ⟨hda, hdb, ?_⟩)⟩
      rcases hside with h | ⟨h, _⟩ | ⟨_, hc⟩
      · exact absurd h hda
      · exact absurd h hdb
      · have : opVal (x.set (dst d) (opVal x a)) b = opVal x b := by
          simp only [opVal, dst, hd, Option.getD_some]
          rw [valOf_set x d b xd hd _ hc (Ne.symm hdb)]
        rw [this]; simp [dst, hd]

/-- The ALU result on a register destination, when both operands are live. -/
theorem aluR_set (x : XS) (o : AluOp) (xd : XReg) (b : BitVec 64) (ho : o ≠ .cmp) :
    aluR x o xd b = (x.set xd (alu o (x.regs xd) b x.flags.cf).1).withFlags (alu o (x.regs xd) b x.flags.cf).2 := by
  unfold aluR
  cases o <;> simp_all

theorem aluR_cmp (x : XS) (xd : XReg) (b : BitVec 64) : aluR x .cmp xd b = x.withFlags (subXF (x.regs xd) b) := by
  simp [aluR, alu]

/-- A binary register op without flags on the ARM side (`addReg`, `subReg`,
    `and3`, `orr3`, `eor3`): the x86 flags become unknown. -/
theorem sim_twoOp_noflags (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x)
    (o : AluOp) (ho : o ≠ .cmp) (comm : Bool) (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ a b cf, (alu o a b cf).1 = f a b) (hcomm : comm = true → ∀ a b, f a b = f b a)
    (d a b : Reg) (xd : XReg) (hd : xreg? d = some xd) (ha : a ∈ L) (hb : b ∈ L)
    (hside : d = a ∨ (d = b ∧ comm = true) ∨ (d ≠ b ∧ clobbers d b = false)) :
    ∃ x', xsteps x (twoOp o d a b comm) = some x' ∧ Rel (upd L d) .unknown (s.set d (f (s.regs a) (s.regs b))) x' := by
  obtain ⟨x', hx', hcase⟩ := twoOp_run x o d a b comm xd hd (hR.isSome a ha) (hR.isSome b hb) hside
  refine ⟨x', hx', ?_⟩
  have hva := hR.opVal a ha
  have hvb := hR.opVal b hb
  rcases hcase with ⟨hda, rfl⟩ | ⟨_, hdb, hc, rfl⟩ | ⟨_, _, rfl⟩
  · rw [aluR_set _ _ _ _ ho, hf, hvb, hR.val d (hda ▸ ha) xd hd, hda]
    exact (hR.setReg a xd (hda ▸ hd) _ (home_ne_rsp _ _ hd)).forget _
  · rw [aluR_set _ _ _ _ ho, hf, hva, hR.val d (hdb ▸ hb) xd hd, hdb, hcomm hc]
    exact (hR.setReg b xd (hdb ▸ hd) _ (home_ne_rsp _ _ hd)).forget _
  · rw [aluR_set _ _ _ _ ho, hf, hvb]
    simp only [XS.set_regs, ite_true, hva]
    have h1 := hR.setReg d xd hd (s.regs a) (home_ne_rsp d xd hd)
    have h2 := h1.setReg d xd hd (f (s.regs a) (s.regs b)) (home_ne_rsp d xd hd)
    rw [AsmRun.set_set_same] at h2
    refine (h2.mono (fun r hr => ?_)).forget _
    simp only [upd, List.mem_cons, List.mem_filter, Bool.not_eq_true'] at hr ⊢
    rcases hr with rfl | ⟨hr, hc⟩
    · left; rfl
    · right; exact ⟨Or.inr ⟨hr, hc⟩, hc⟩


/-! ### Register ALU forms -/

theorem sim_addReg (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a b : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) (hb : b ∈ L) (hside : d = a ∨ d = b ∨ clobbers d b = false) :
    ∃ x', xsteps x (x86Items (.addReg d a b)) = some x' ∧ Rel (upd L d) .unknown (s.set d (s.regs a + s.regs b)) x' := by
  apply sim_twoOp_noflags L p s x hR .add (by decide) true (· + ·) (fun _ _ _ => rfl) (fun _ a b => BitVec.add_comm a b) d a b xd hd ha hb
  rcases hside with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, rfl⟩)
  · by_cases hdb : d = b
    · exact Or.inr (Or.inl ⟨hdb, rfl⟩)
    · exact Or.inr (Or.inr ⟨hdb, h⟩)

theorem sim_orr3 (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a b : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) (hb : b ∈ L) (hside : d = a ∨ d = b ∨ clobbers d b = false) :
    ∃ x', xsteps x (x86Items (.orr3 d a b)) = some x' ∧ Rel (upd L d) .unknown (s.set d (s.regs a ||| s.regs b)) x' := by
  apply sim_twoOp_noflags L p s x hR .or_ (by decide) true (· ||| ·) (fun _ _ _ => rfl) (fun _ a b => BitVec.or_comm a b) d a b xd hd ha hb
  rcases hside with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, rfl⟩)
  · by_cases hdb : d = b
    · exact Or.inr (Or.inl ⟨hdb, rfl⟩)
    · exact Or.inr (Or.inr ⟨hdb, h⟩)

theorem sim_and3 (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a b : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) (hb : b ∈ L) (hside : d = a ∨ d = b ∨ clobbers d b = false) :
    ∃ x', xsteps x (x86Items (.and3 d a b)) = some x' ∧ Rel (upd L d) .unknown (s.set d (s.regs a &&& s.regs b)) x' := by
  apply sim_twoOp_noflags L p s x hR .and_ (by decide) true (· &&& ·) (fun _ _ _ => rfl) (fun _ a b => BitVec.and_comm a b) d a b xd hd ha hb
  rcases hside with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, rfl⟩)
  · by_cases hdb : d = b
    · exact Or.inr (Or.inl ⟨hdb, rfl⟩)
    · exact Or.inr (Or.inr ⟨hdb, h⟩)

theorem sim_eor3 (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a b : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) (hb : b ∈ L) (hside : d = a ∨ d = b ∨ clobbers d b = false) :
    ∃ x', xsteps x (x86Items (.eor3 d a b)) = some x' ∧ Rel (upd L d) .unknown (s.set d (s.regs a ^^^ s.regs b)) x' := by
  apply sim_twoOp_noflags L p s x hR .xor_ (by decide) true (· ^^^ ·) (fun _ _ _ => rfl) (fun _ a b => BitVec.xor_comm a b) d a b xd hd ha hb
  rcases hside with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, rfl⟩)
  · by_cases hdb : d = b
    · exact Or.inr (Or.inl ⟨hdb, rfl⟩)
    · exact Or.inr (Or.inr ⟨hdb, h⟩)

/-- `subReg`: not commutative, so `d = b` is unlowered (`twoOp … false`). -/
theorem sim_subReg (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a b : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) (hb : b ∈ L) (hside : d = a ∨ (d ≠ b ∧ clobbers d b = false)) :
    ∃ x', xsteps x (x86Items (.subReg d a b)) = some x' ∧ Rel (upd L d) .unknown (s.set d (s.regs a - s.regs b)) x' := by
  apply sim_twoOp_noflags L p s x hR .sub (by decide) false (· - ·) (fun _ _ _ => rfl) (fun h => by cases h) d a b xd hd ha hb
  rcases hside with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-- A binary op WITH flags on the ARM side (`adds`, `subsReg`): the x86 flags
    track them under the op's provenance. -/
theorem sim_twoOp_flags (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x)
    (o : AluOp) (ho : o ≠ .cmp) (comm : Bool) (p' : Prov) (f : BitVec 64 → BitVec 64 → BitVec 64)
    (fl : BitVec 64 → BitVec 64 → Flags)
    (hf : ∀ a b cf, (alu o a b cf).1 = f a b) (hfl : ∀ a b cf, FlagsRel p' (fl a b) (alu o a b cf).2)
    (hcomm : comm = true → ∀ a b, f a b = f b a ∧ fl a b = fl b a)
    (d a b : Reg) (xd : XReg) (hd : xreg? d = some xd) (ha : a ∈ L) (hb : b ∈ L)
    (hside : d = a ∨ (d = b ∧ comm = true) ∨ (d ≠ b ∧ clobbers d b = false)) :
    ∃ x', xsteps x (twoOp o d a b comm) = some x' ∧
      Rel (upd L d) p' ((s.set d (f (s.regs a) (s.regs b))).withFlags (fl (s.regs a) (s.regs b))) x' := by
  obtain ⟨x', hx', hcase⟩ := twoOp_run x o d a b comm xd hd (hR.isSome a ha) (hR.isSome b hb) hside
  refine ⟨x', hx', ?_⟩
  have hva := hR.opVal a ha
  have hvb := hR.opVal b hb
  rcases hcase with ⟨hda, rfl⟩ | ⟨_, hdb, hc, rfl⟩ | ⟨_, _, rfl⟩
  · rw [aluR_set _ _ _ _ ho, hf, hvb, hR.val d (hda ▸ ha) xd hd, hda]
    exact (hR.setReg a xd (hda ▸ hd) _ (home_ne_rsp _ _ hd)).setFlags p' _ _ (hfl _ _ _)
  · rw [aluR_set _ _ _ _ ho, hf, hva, hR.val d (hdb ▸ hb) xd hd, hdb, (hcomm hc _ _).1, (hcomm hc _ _).2]
    exact (hR.setReg b xd (hdb ▸ hd) _ (home_ne_rsp _ _ hd)).setFlags p' _ _ (hfl _ _ _)
  · rw [aluR_set _ _ _ _ ho, hf, hvb]
    simp only [XS.set_regs, ite_true, hva]
    have h1 := hR.setReg d xd hd (s.regs a) (home_ne_rsp d xd hd)
    have h2 := h1.setReg d xd hd (f (s.regs a) (s.regs b)) (home_ne_rsp d xd hd)
    rw [AsmRun.set_set_same] at h2
    refine (h2.mono (fun r hr => ?_)).setFlags p' _ _ (hfl _ _ _)
    simp only [upd, List.mem_cons, List.mem_filter, Bool.not_eq_true'] at hr ⊢
    rcases hr with rfl | ⟨hr, hc⟩
    · left; rfl
    · right; exact ⟨Or.inr ⟨hr, hc⟩, hc⟩

theorem sim_adds (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a b : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) (hb : b ∈ L) (hside : d = a ∨ d = b ∨ clobbers d b = false) :
    ∃ x', xsteps x (x86Items (.adds d a b)) = some x' ∧
      Rel (upd L d) .add ((s.set d (s.regs a + s.regs b)).withFlags (addFlags (s.regs a) (s.regs b))) x' := by
  apply sim_twoOp_flags L p s x hR .add (by decide) true .add (· + ·) addFlags (fun _ _ _ => rfl)
    (fun a b _ => addXF_rel a b)
    (fun _ a b => ⟨BitVec.add_comm a b, by
      simp only [addFlags, BitVec.add_comm a b]
      cases ha : a.msb <;> cases hb : b.msb <;> simp [Nat.add_comm]⟩) d a b xd hd ha hb
  rcases hside with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, rfl⟩)
  · by_cases hdb : d = b
    · exact Or.inr (Or.inl ⟨hdb, rfl⟩)
    · exact Or.inr (Or.inr ⟨hdb, h⟩)

theorem sim_subsReg (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a b : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) (hb : b ∈ L) (hside : d = a ∨ (d ≠ b ∧ clobbers d b = false)) :
    ∃ x', xsteps x (x86Items (.subsReg d a b)) = some x' ∧
      Rel (upd L d) .sub ((s.set d (s.regs a - s.regs b)).withFlags (subFlags (s.regs a) (s.regs b))) x' := by
  apply sim_twoOp_flags L p s x hR .sub (by decide) false .sub (· - ·) subFlags (fun _ _ _ => rfl)
    (fun a b _ => subXF_rel a b) (fun h => by cases h) d a b xd hd ha hb
  rcases hside with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-- `adcs`: `adc` consumes CF, which is the ARM carry under `add` provenance. -/
theorem sim_adcs (L : List Reg) (s : RS) (x : XS) (hR : Rel L .add s x) (d a b : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) (hb : b ∈ L) (hside : d = a ∨ d = b ∨ clobbers d b = false) :
    ∃ x', xsteps x (x86Items (.adcs d a b)) = some x' ∧
      Rel (upd L d) .add ((s.set d (addc (s.regs a) (s.regs b) s.flags.c).1).withFlags
        (addc (s.regs a) (s.regs b) s.flags.c).2) x' := by
  have hcf : x.flags.cf = s.flags.c := hR.flags.1
  obtain ⟨x', hx', hcase⟩ := twoOp_run x .adc d a b true xd hd (hR.isSome a ha) (hR.isSome b hb)
    (by rcases hside with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h, rfl⟩)
        · by_cases hdb : d = b
          · exact Or.inr (Or.inl ⟨hdb, rfl⟩)
          · exact Or.inr (Or.inr ⟨hdb, h⟩))
  refine ⟨x', by simpa [x86Items] using hx', ?_⟩
  have hva := hR.opVal a ha
  have hvb := hR.opVal b hb
  have key : ∀ (u v : BitVec 64), FlagsRel .add (addc u v s.flags.c).2 (adcXF u v s.flags.c) ∧
      (alu .adc u v s.flags.c).1 = (addc u v s.flags.c).1 := fun u v =>
    ⟨(adc_rel u v s.flags.c).2, by simp only [alu]; exact (adc_rel u v s.flags.c).1.symm⟩
  have hcomm : ∀ u v, addc u v s.flags.c = addc v u s.flags.c := by
    intro u v; simp only [addc]; rw [BitVec.add_comm (u.zeroExtend 65)]
    congr 1; cases u.msb <;> cases v.msb <;> simp
  rcases hcase with ⟨hda, rfl⟩ | ⟨_, hdb, _, rfl⟩ | ⟨_, _, rfl⟩
  · rw [aluR_set _ _ _ _ (by decide), hvb, hR.val d (hda ▸ ha) xd hd, hcf, hda, (key _ _).2]
    exact (hR.setReg a xd (hda ▸ hd) _ (home_ne_rsp _ _ hd)).setFlags .add _ _ (by simp only [alu]; exact (key _ _).1)
  · rw [aluR_set _ _ _ _ (by decide), hva, hR.val d (hdb ▸ hb) xd hd, hcf, hdb, (key _ _).2,
        hcomm (s.regs a) (s.regs b)]
    exact (hR.setReg b xd (hdb ▸ hd) _ (home_ne_rsp _ _ hd)).setFlags .add _ _ (by simp only [alu]; exact (key _ _).1)
  · rw [aluR_set _ _ _ _ (by decide), hvb]
    simp only [XS.set_regs, XS.set_flags, ite_true, hva, hcf, (key _ _).2]
    have h1 := hR.setReg d xd hd (s.regs a) (home_ne_rsp d xd hd)
    have h2 := h1.setReg d xd hd (addc (s.regs a) (s.regs b) s.flags.c).1 (home_ne_rsp d xd hd)
    rw [AsmRun.set_set_same] at h2
    refine (h2.mono (fun r hr => ?_)).setFlags .add _ _ (by simp only [alu]; exact (key _ _).1)
    simp only [upd, List.mem_cons, List.mem_filter, Bool.not_eq_true'] at hr ⊢
    rcases hr with rfl | ⟨hr, hc⟩
    · left; rfl
    · right; exact ⟨Or.inr ⟨hr, hc⟩, hc⟩

/-- `sbcs`: `sbb` consumes CF, which is the ARM NOT-carry under `sub` provenance. -/
theorem sim_sbcs (L : List Reg) (s : RS) (x : XS) (hR : Rel L .sub s x) (d a b : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) (hb : b ∈ L) (hside : d = a ∨ (d ≠ b ∧ clobbers d b = false)) :
    ∃ x', xsteps x (x86Items (.sbcs d a b)) = some x' ∧
      Rel (upd L d) .sub ((s.set d (subc (s.regs a) (s.regs b) s.flags.c).1).withFlags
        (subc (s.regs a) (s.regs b) s.flags.c).2) x' := by
  have hcf : x.flags.cf = !s.flags.c := hR.flags.1
  obtain ⟨x', hx', hcase⟩ := twoOp_run x .sbb d a b false xd hd (hR.isSome a ha) (hR.isSome b hb)
    (by rcases hside with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h))
  refine ⟨x', by simpa [x86Items] using hx', ?_⟩
  have hva := hR.opVal a ha
  have hvb := hR.opVal b hb
  have key : ∀ (u v : BitVec 64), FlagsRel .sub (subc u v s.flags.c).2 (sbbXF u v (!s.flags.c)) ∧
      (alu .sbb u v (!s.flags.c)).1 = (subc u v s.flags.c).1 := fun u v =>
    ⟨(sbb_rel u v s.flags.c).2, by simp only [alu]; exact (sbb_rel u v s.flags.c).1.symm⟩
  rcases hcase with ⟨hda, rfl⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, rfl⟩
  · rw [aluR_set _ _ _ _ (by decide), hvb, hR.val d (hda ▸ ha) xd hd, hcf, hda, (key _ _).2]
    exact (hR.setReg a xd (hda ▸ hd) _ (home_ne_rsp _ _ hd)).setFlags .sub _ _ (by simp only [alu]; exact (key _ _).1)
  · cases hc
  · rw [aluR_set _ _ _ _ (by decide), hvb]
    simp only [XS.set_regs, XS.set_flags, ite_true, hva, hcf, (key _ _).2]
    have h1 := hR.setReg d xd hd (s.regs a) (home_ne_rsp d xd hd)
    have h2 := h1.setReg d xd hd (subc (s.regs a) (s.regs b) s.flags.c).1 (home_ne_rsp d xd hd)
    rw [AsmRun.set_set_same] at h2
    refine (h2.mono (fun r hr => ?_)).setFlags .sub _ _ (by simp only [alu]; exact (key _ _).1)
    simp only [upd, List.mem_cons, List.mem_filter, Bool.not_eq_true'] at hr ⊢
    rcases hr with rfl | ⟨hr, hc⟩
    · left; rfl
    · right; exact ⟨Or.inr ⟨hr, hc⟩, hc⟩


theorem home_ne_of_not_clobbers (d b : Reg) (xd xb : XReg) (hd : xreg? d = some xd) (hb : xreg? b = some xb)
    (hne : d ≠ b) (hc : clobbers d b = false) : xb ≠ xd := by
  intro e; subst e
  simp [clobbers, aliasedH, hd, hb, hne] at hc

theorem ofInt_zero : BitVec.ofInt 64 0 = 0 := by
  rw [show (0 : Int) = Int.ofNat 0 from rfl, ofInt_ofNat]; rfl

/-! ### Immediates, compares, the carry-chain tail -/

/-- `subsImm d a i`: `sub d, i` (or `mov d, a ; sub d, i`), `sub` provenance. -/
theorem sim_subsImm (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a : Reg) (xd xa : XReg)
    (hd : xreg? d = some xd) (ha' : xreg? a = some xa) (ha : a ∈ L) (i : Nat) :
    ∃ x', xsteps x (x86Items (.subsImm d a i)) = some x' ∧
      Rel (upd L d) .sub ((s.set d (s.regs a - BitVec.ofNat 64 i)).withFlags (subFlags (s.regs a) (BitVec.ofNat 64 i))) x' := by
  have hva := hR.val a ha xa ha'
  by_cases hda : d = a
  · simp only [x86Items, hda, beq_self_eq_true, ite_true]
    refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
    simp only [aluR, alu, dst, ha', Option.getD_some, hva, ofInt_ofNat]
    exact (hR.setReg a xa ha' _ (home_ne_rsp _ _ ha')).setFlags .sub _ _ (subXF_rel _ _)
  · refine ⟨_, by simp only [x86Items, beq_iff_eq, hda, ite_false]
                  rw [xsteps_cons _ _ _ _ rfl]; exact xsteps_single _ _ _ rfl, ?_⟩
    simp only [aluR, alu, dst, hd, ha', Option.getD_some, XS.set_regs, ite_true, hva, ofInt_ofNat]
    have h1 := hR.setReg d xd hd (s.regs a) (home_ne_rsp d xd hd)
    have h2 := h1.setReg d xd hd (s.regs a - BitVec.ofNat 64 i) (home_ne_rsp d xd hd)
    rw [AsmRun.set_set_same] at h2
    refine (h2.mono (fun r hr => ?_)).setFlags .sub _ _ (subXF_rel _ _)
    simp only [upd, List.mem_cons, List.mem_filter, Bool.not_eq_true'] at hr ⊢
    rcases hr with rfl | ⟨hr, hc⟩
    · left; rfl
    · right; exact ⟨Or.inr ⟨hr, hc⟩, hc⟩

/-- `cmpImm a i`, `sub` provenance; nothing else changes. -/
theorem sim_cmpImm (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (a : Reg) (xa : XReg)
    (ha' : xreg? a = some xa) (ha : a ∈ L) (i : Nat) :
    ∃ x', xsteps x (x86Items (.cmpImm a i)) = some x' ∧
      Rel L .sub (s.withFlags (subFlags (s.regs a) (BitVec.ofNat 64 i))) x' := by
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [aluR, alu, dst, ha', Option.getD_some, hR.val a ha xa ha', ofInt_ofNat]
  exact hR.setFlags .sub _ _ (subXF_rel _ _)

theorem sim_cmpImmWHex (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (a : Reg) (xa : XReg)
    (ha' : xreg? a = some xa) (ha : a ∈ L) (i : Nat) :
    ∃ x', xsteps x (x86Items (.cmpImmWHex a i)) = some x' ∧
      Rel L .sub (s.withFlags (subFlags (s.regs a) (BitVec.ofNat 64 i))) x' := by
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [aluR, alu, dst, ha', Option.getD_some, hR.val a ha xa ha', ofInt_ofNat]
  exact hR.setFlags .sub _ _ (subXF_rel _ _)

/-- `cmpReg a b` with `a` in a register (the NOS-left form is `aluMR`, below). -/
theorem sim_cmpReg (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (a b : Reg) (xa : XReg)
    (ha' : xreg? a = some xa) (ha : a ∈ L) (hb : b ∈ L) :
    ∃ x', xsteps x (x86Items (.cmpReg a b)) = some x' ∧
      Rel L .sub (s.withFlags (subFlags (s.regs a) (s.regs b))) x' := by
  obtain ⟨i, hi, hstep⟩ := aluFrom_step x .cmp xa b (hR.isSome b hb)
  refine ⟨_, by simp only [x86Items, ha']; rw [hi]; exact xsteps_single _ _ _ hstep, ?_⟩
  rw [aluR_cmp, hR.opVal b hb, hR.val a ha xa ha']
  exact hR.setFlags .sub _ _ (subXF_rel _ _)

theorem sim_cmpReg_nos (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (a b : Reg) (la : Nat) (xb : XReg)
    (ha' : nosLimb a = some la) (hb' : xreg? b = some xb) (ha : a ∈ L) (hb : b ∈ L) :
    ∃ x', xsteps x (x86Items (.cmpReg a b)) = some x' ∧
      Rel L .sub (s.withFlags (subFlags (s.regs a) (s.regs b))) x' := by
  have hxa := nosLimb_some_xreg_none a la ha'
  refine ⟨_, by simp only [x86Items, hxa, ha', hb']; exact xsteps_single _ _ _ rfl, ?_⟩
  simp only [hR.valNos a ha la ha', hR.val b hb xb hb']
  exact hR.setFlags .sub _ _ (subXF_rel _ _)

theorem sim_subsZr (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (a b : Reg) (xa : XReg)
    (ha' : xreg? a = some xa) (ha : a ∈ L) (hb : b ∈ L) :
    ∃ x', xsteps x (x86Items (.subsZr a b)) = some x' ∧
      Rel L .sub (s.withFlags (subFlags (s.regs a) (s.regs b))) x' := by
  obtain ⟨i, hi, hstep⟩ := aluFrom_step x .cmp xa b (hR.isSome b hb)
  refine ⟨_, by simp only [x86Items, cmpFrom, ha']; rw [hi]; exact xsteps_single _ _ _ hstep, ?_⟩
  rw [aluR_cmp, hR.opVal b hb, hR.val a ha xa ha']
  exact hR.setFlags .sub _ _ (subXF_rel _ _)

theorem valOf_withFlags (x : XS) (f : XFlags) (r : Reg) : valOf (x.withFlags f) r = valOf x r := by
  cases hr : xreg? r <;> cases hl : nosLimb r <;> simp [valOf, ea, hr, hl]

/-- The live set minus a scratch register and everything it clobbers. -/
def kill (L : List Reg) (d : Reg) : List Reg := L.filter (fun r => !clobbers d r && r != d)

theorem mem_kill {L : List Reg} {d r : Reg} (h : r ∈ kill L d) : r ∈ L ∧ clobbers d r = false ∧ r ≠ d := by
  simp only [kill, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- `sbcsZr a b`: `mov rcx, a ; sbb rcx, b` — x14 (rcx) is scratch and leaves the live set. -/
theorem sim_sbcsZr (L : List Reg) (s : RS) (x : XS) (hR : Rel L .sub s x) (a b : Reg) (ha : a ∈ L) (hb : b ∈ L)
    (hb14 : b ≠ .x14) :
    ∃ x', xsteps x (x86Items (.sbcsZr a b)) = some x' ∧
      Rel (kill L .x14) .sub (s.withFlags (subc (s.regs a) (s.regs b) s.flags.c).2) x' := by
  have hcf : x.flags.cf = !s.flags.c := hR.flags.1
  obtain ⟨i1, hi1, hstep1⟩ := movFrom_step x .rcx a (hR.isSome a ha)
  have h14 : xreg? .x14 = some .rcx := rfl
  have hc : clobbers .x14 b = false := by
    cases b <;> first | exact absurd rfl hb14 | rfl
  have hb' : (valOf (x.set .rcx (opVal x a)) b).isSome := by
    rw [valOf_set x .x14 b .rcx h14 _ hc hb14]; exact hR.isSome b hb
  obtain ⟨i2, hi2, hstep2⟩ := aluFrom_step (x.set .rcx (opVal x a)) .sbb .rcx b hb'
  refine ⟨_, by simp only [x86Items]; rw [hi1, hi2, xsteps_cons _ _ _ _ hstep1]; exact xsteps_single _ _ _ hstep2, ?_⟩
  have hvb : opVal (x.set .rcx (opVal x a)) b = s.regs b := by
    simp only [opVal]; rw [valOf_set x .x14 b .rcx h14 _ hc hb14, hR.regs b hb]; rfl
  rw [aluR_set _ _ _ _ (by decide), hvb]
  simp only [XS.set_regs, XS.set_flags, ite_true, hR.opVal a ha, hcf, alu]
  have key := sbb_rel (s.regs a) (s.regs b) s.flags.c
  refine ⟨fun r hr => ?_, by simpa using hR.sp, by simpa using hR.mem, key.2⟩
  obtain ⟨hrL, hc', hne⟩ := mem_kill hr
  rw [valOf_withFlags, valOf_set _ _ r .rcx h14 _ hc' hne, valOf_set _ _ r .rcx h14 _ hc' hne, hR.regs r hrL]
  rfl

/-! ### Shifts, multiply, shift-and-add -/

theorem sim_lsrImm (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a : Reg) (xd xa : XReg)
    (hd : xreg? d = some xd) (ha' : xreg? a = some xa) (ha : a ∈ L) (sh : Nat) :
    ∃ x', xsteps x (x86Items (.lsrImm d a sh)) = some x' ∧ Rel (upd L d) .unknown (s.set d (s.regs a >>> sh)) x' := by
  have hva := hR.val a ha xa ha'
  by_cases hda : d = a
  · simp only [x86Items, hda, beq_self_eq_true, ite_true]
    refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
    simp only [dst, ha', Option.getD_some, hva]
    exact (hR.setReg a xa ha' _ (home_ne_rsp _ _ ha')).forget _
  · simp only [x86Items, beq_iff_eq, hda, ite_false]
    refine ⟨_, by rw [xsteps_cons _ _ _ _ rfl]; exact xsteps_single _ _ _ rfl, ?_⟩
    simp only [dst, hd, ha', Option.getD_some, XS.set_regs, ite_true, hva]
    have h1 := hR.setReg d xd hd (s.regs a) (home_ne_rsp d xd hd)
    have h2 := h1.setReg d xd hd (s.regs a >>> sh) (home_ne_rsp d xd hd)
    rw [AsmRun.set_set_same] at h2
    refine (h2.mono (fun r hr => ?_)).forget _
    simp only [upd, List.mem_cons, List.mem_filter, Bool.not_eq_true'] at hr ⊢
    rcases hr with rfl | ⟨hr, hc⟩
    · left; rfl
    · right; exact ⟨Or.inr ⟨hr, hc⟩, hc⟩

theorem sim_lslImm (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a : Reg) (xd xa : XReg)
    (hd : xreg? d = some xd) (ha' : xreg? a = some xa) (ha : a ∈ L) (sh : Nat) :
    ∃ x', xsteps x (x86Items (.lslImm d a sh)) = some x' ∧ Rel (upd L d) .unknown (s.set d (s.regs a <<< sh)) x' := by
  have hva := hR.val a ha xa ha'
  by_cases hda : d = a
  · simp only [x86Items, hda, beq_self_eq_true, ite_true]
    refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
    simp only [dst, ha', Option.getD_some, hva]
    exact (hR.setReg a xa ha' _ (home_ne_rsp _ _ ha')).forget _
  · simp only [x86Items, beq_iff_eq, hda, ite_false]
    refine ⟨_, by rw [xsteps_cons _ _ _ _ rfl]; exact xsteps_single _ _ _ rfl, ?_⟩
    simp only [dst, hd, ha', Option.getD_some, XS.set_regs, ite_true, hva]
    have h1 := hR.setReg d xd hd (s.regs a) (home_ne_rsp d xd hd)
    have h2 := h1.setReg d xd hd (s.regs a <<< sh) (home_ne_rsp d xd hd)
    rw [AsmRun.set_set_same] at h2
    refine (h2.mono (fun r hr => ?_)).forget _
    simp only [upd, List.mem_cons, List.mem_filter, Bool.not_eq_true'] at hr ⊢
    rcases hr with rfl | ⟨hr, hc⟩
    · left; rfl
    · right; exact ⟨Or.inr ⟨hr, hc⟩, hc⟩

theorem upd_upd_sub (L : List Reg) (d r : Reg) (hr : r ∈ upd L d) : r ∈ upd (upd L d) d := by
  simp only [upd, List.mem_cons, List.mem_filter, Bool.not_eq_true'] at hr ⊢
  rcases hr with rfl | ⟨hr, hc⟩
  · left; rfl
  · right; exact ⟨Or.inr ⟨hr, hc⟩, hc⟩

theorem sim_mulReg (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a b : Reg) (xd xa xb : XReg)
    (hd : xreg? d = some xd) (ha' : xreg? a = some xa) (hb' : xreg? b = some xb) (ha : a ∈ L) (hb : b ∈ L)
    (hside : d = a ∨ d = b ∨ clobbers d b = false) :
    ∃ x', xsteps x (x86Items (.mulReg d a b)) = some x' ∧ Rel (upd L d) .unknown (s.set d (s.regs a * s.regs b)) x' := by
  have hva := hR.val a ha xa ha'
  have hvb := hR.val b hb xb hb'
  by_cases hda : d = a
  · subst hda
    have hx : xa = xd := by rw [ha'] at hd; exact Option.some.inj hd
    subst hx
    simp only [x86Items, beq_self_eq_true, ite_true, dst, ha', hb', Option.getD_some]
    refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
    simp only [hva, hvb]
    exact (hR.setReg d xa ha' _ (home_ne_rsp _ _ ha')).forget _
  · by_cases hdb : d = b
    · subst hdb
      have hx : xb = xd := by rw [hb'] at hd; exact Option.some.inj hd
      subst hx
      simp only [x86Items, dst, ha', hb', Option.getD_some]
      rw [if_neg (by simpa using hda), if_pos (by simp)]
      refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
      simp only [hva, hvb, BitVec.mul_comm (s.regs d)]
      exact (hR.setReg d xb hb' _ (home_ne_rsp _ _ hb')).forget _
    · have hc : clobbers d b = false := by
        rcases hside with h | h | h
        · exact absurd h hda
        · exact absurd h hdb
        · exact h
      have hxb : xb ≠ xd := home_ne_of_not_clobbers d b xd xb hd hb' hdb hc
      simp only [x86Items, dst, hd, ha', hb', Option.getD_some]
      rw [if_neg (by simpa using hda), if_neg (by simpa using hdb)]
      refine ⟨_, by rw [xsteps_cons _ _ _ _ rfl]; exact xsteps_single _ _ _ rfl, ?_⟩
      simp only [XS.set_regs, ite_true, if_neg hxb, hva, hvb]
      have h1 := hR.setReg d xd hd (s.regs a) (home_ne_rsp d xd hd)
      have h2 := h1.setReg d xd hd (s.regs a * s.regs b) (home_ne_rsp d xd hd)
      rw [AsmRun.set_set_same] at h2
      exact (h2.mono (upd_upd_sub L d)).forget _

/-- `lea`'s scaled index is the shift, for the four encodable scales. -/
theorem shl_eq_mul_scale (b : BitVec 64) (sh : Nat) (hsh : sh ≤ 3) :
    b * BitVec.ofNat 64 (2 ^ sh) = b <<< sh := by
  rcases (show sh = 0 ∨ sh = 1 ∨ sh = 2 ∨ sh = 3 by omega) with rfl | rfl | rfl | rfl <;> bv_decide

theorem sim_addLsl_lea (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a b : Reg) (xd xa xb : XReg)
    (hd : xreg? d = some xd) (ha' : xreg? a = some xa) (hb' : xreg? b = some xb) (ha : a ∈ L) (hb : b ∈ L)
    (sh : Nat) (hsh : sh ≤ 3) :
    ∃ x', xsteps x (x86Items (.addLsl d a b sh)) = some x' ∧
      Rel (upd L d) p (s.set d (s.regs a + (s.regs b <<< sh))) x' := by
  simp only [x86Items, hsh, ite_true]
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [dst, hd, ha', hb', Option.getD_some, ea, hR.val a ha xa ha', hR.val b hb xb hb',
             shl_eq_mul_scale _ _ hsh, ofInt_zero]
  have hz : ∀ v : BitVec 64, v + 0 = v := fun v => by simp
  rw [hz]
  exact hR.setReg d xd hd _ (home_ne_rsp d xd hd)

/-- `shiftThenAdd o xd sh a` from a state where xd holds `v`: `(v op sh) + a`. -/
theorem shiftThenAdd_run (x : XS) (o : ShiftOp) (xd : XReg) (sh : Nat) (a : Reg) (ha : (valOf x a).isSome)
    (hxa : ∀ xa, xreg? a = some xa → xa ≠ xd) (hnos : ∀ l, nosLimb a = some l → xd ≠ .r12 ∧ xd ≠ .r13) :
    let v := match o with
      | .shl => x.regs xd <<< sh | .shr => x.regs xd >>> sh | .sar => BitVec.sshiftRight (x.regs xd) sh
    ∃ x', xsteps x (shiftThenAdd o xd sh a) = some x' ∧
      x' = aluR ((x.set xd v).withFlags (clobXF x.flags v)) .add xd (opVal x a) := by
  intro v
  have hva : opVal ((x.set xd v).withFlags (clobXF x.flags v)) a = opVal x a := by
    simp only [opVal]
    cases hr : xreg? a with
    | some xa =>
      rw [valOf_withFlags, valOf_reg _ _ _ hr, valOf_reg _ _ _ hr]; simp [XS.set, hxa xa hr]
    | none =>
      cases hl : nosLimb a with
      | some l =>
        rw [valOf_withFlags, valOf_nos _ _ _ hr hl, valOf_nos _ _ _ hr hl]
        rw [ea_nos_set _ _ _ _ (hnos l hl).1 (hnos l hl).2]; rfl
      | none => simp [valOf, hr, hl] at ha
  obtain ⟨i, hi, hstep⟩ := aluFrom_step ((x.set xd v).withFlags (clobXF x.flags v)) .add xd a
    (by rw [valOf_withFlags, show valOf (x.set xd v) a = valOf x a from ?_]; exact ha
        simp only [valOf]
        cases hr : xreg? a with
        | some xa => simp [XS.set, hxa xa hr]
        | none =>
          cases hl : nosLimb a with
          | some l => simp only [XS.set_mem]; rw [ea_nos_set _ _ _ _ (hnos l hl).1 (hnos l hl).2]
          | none => rfl)
  rw [hva] at hstep
  refine ⟨_, ?_, rfl⟩
  simp only [shiftThenAdd]
  rw [hi]
  have hshift : xstep x (.shiftRI o xd sh) = some ((x.set xd v).withFlags (clobXF x.flags v)) := by
    cases o <;> rfl
  rw [xsteps_cons _ _ _ _ hshift]
  exact xsteps_single _ _ _ hstep

/-! ### Selects -/

/-- The three-way `cmov` lowering shared by `csel`, `cselHi`, `cselNe`:
    `d = b`: `cmov<c> d, a`; `d = a`: `cmov<¬c> d, b`; else `mov d, b ; cmov<c> d, a`. -/
theorem sim_cmovsel (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a b : Reg) (xd xa xb : XReg)
    (hd : xreg? d = some xd) (ha' : xreg? a = some xa) (hb' : xreg? b = some xb) (ha : a ∈ L) (hb : b ∈ L)
    (cond : Bool) (ct cn : XCond) (hct : xcHolds ct x.flags = cond) (hcn : xcHolds cn x.flags = !cond)
    (items : List XItem)
    (hitems : items = (if d == b then [.I (.cmovRR ct xd xa)]
                       else if d == a then [.I (.cmovRR cn xd xb)]
                       else [.I (.movRR xd xb), .I (.cmovRR ct xd xa)]))
    (hside : d = a ∨ d = b ∨ clobbers d a = false) :
    ∃ x', xsteps x items = some x' ∧ Rel (upd L d) p (s.set d (if cond then s.regs a else s.regs b)) x' := by
  have hva := hR.val a ha xa ha'
  have hvb := hR.val b hb xb hb'
  subst hitems
  by_cases hdb : d = b
  · subst hdb
    have hx : xb = xd := by rw [hb'] at hd; exact Option.some.inj hd
    subst hx
    simp only [beq_self_eq_true, ite_true]
    refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
    simp only [hct]
    cases cond with
    | true =>
      try simp only [ite_true, hva]
      exact hR.setReg d xb hb' _ (home_ne_rsp _ _ hb')
    | false =>
      try simp only [Bool.false_eq_true, ite_false]
      rw [AsmRun.set_eq_self _ _ _ rfl]
      exact hR.mono (fun r hr => by
        simp only [upd, List.mem_cons, List.mem_filter] at hr
        rcases hr with rfl | ⟨hr, _⟩
        · exact hb
        · exact hr)
  · by_cases hda : d = a
    · subst hda
      have hx : xa = xd := by rw [ha'] at hd; exact Option.some.inj hd
      subst hx
      rw [if_neg (by simpa using hdb), if_pos (by simp)]
      refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
      simp only [hcn]
      cases cond with
      | true =>
        try simp only [Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
        rw [AsmRun.set_eq_self _ _ _ rfl]
        exact hR.mono (fun r hr => by
          simp only [upd, List.mem_cons, List.mem_filter] at hr
          rcases hr with rfl | ⟨hr, _⟩
          · exact ha
          · exact hr)
      | false =>
        try simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false, hvb]
        exact hR.setReg d xa ha' _ (home_ne_rsp _ _ ha')
    · have hc : clobbers d a = false := by
        rcases hside with h | h | h
        · exact absurd h hda
        · exact absurd h hdb
        · exact h
      have hxa : xa ≠ xd := home_ne_of_not_clobbers d a xd xa hd ha' hda hc
      rw [if_neg (by simpa using hdb), if_neg (by simpa using hda)]
      refine ⟨_, by rw [xsteps_cons _ _ _ _ rfl]; exact xsteps_single _ _ _ rfl, ?_⟩
      simp only [XS.set_flags, hct, XS.set_regs, if_neg hxa, hvb, hva]
      have h1 := hR.setReg d xd hd (s.regs b) (home_ne_rsp d xd hd)
      cases cond with
      | true =>
        try simp only [ite_true]
        have h2 := h1.setReg d xd hd (s.regs a) (home_ne_rsp d xd hd)
        rw [AsmRun.set_set_same] at h2
        exact h2.mono (upd_upd_sub L d)
      | false =>
        try simp only [Bool.false_eq_true, ite_false]
        exact h1

theorem sim_cselHi (L : List Reg) (s : RS) (x : XS) (hR : Rel L .sub s x) (d a b : Reg) (xd xa xb : XReg)
    (hd : xreg? d = some xd) (ha' : xreg? a = some xa) (hb' : xreg? b = some xb) (ha : a ∈ L) (hb : b ∈ L)
    (hside : d = a ∨ d = b ∨ clobbers d a = false) :
    ∃ x', xsteps x (x86Items (.cselHi d a b)) = some x' ∧
      Rel (upd L d) .sub (s.set d (if bcHolds .hi s.flags then s.regs a else s.regs b)) x' := by
  apply sim_cmovsel L .sub s x hR d a b xd xa xb hd ha' hb' ha hb (bcHolds .hi s.flags) .a .be
    (by have := cond_sub .hi s.flags x.flags hR.flags; simpa [bcondXc] using this)
    (by have := cond_sub .hi s.flags x.flags hR.flags; rw [← this]; simp [bcondXc, xcHolds])
    _ ?_ hside
  simp only [x86Items, dst, hd, ha', hb', Option.getD_some]

theorem sim_csel (L : List Reg) (s : RS) (x : XS) (hR : Rel L .sub s x) (d a b : Reg) (c : BCond) (xd xa xb : XReg)
    (hd : xreg? d = some xd) (ha' : xreg? a = some xa) (hb' : xreg? b = some xb) (ha : a ∈ L) (hb : b ∈ L)
    (hside : d = a ∨ d = b ∨ clobbers d a = false) :
    ∃ x', xsteps x (x86Items (.csel d a b c)) = some x' ∧
      Rel (upd L d) .sub (s.set d (if bcHolds c s.flags then s.regs a else s.regs b)) x' := by
  apply sim_cmovsel L .sub s x hR d a b xd xa xb hd ha' hb' ha hb (bcHolds c s.flags) (bcondXc c) (nbcondXc c)
    (cond_sub c s.flags x.flags hR.flags)
    (by rw [nbcond_eq, cond_sub c s.flags x.flags hR.flags])
    _ ?_ hside
  simp only [x86Items, dst, hd, ha', hb', Option.getD_some]

/-! ### `cset`, `tst`, `rev`, `mvn` -/

theorem setcc_movzx (v : BitVec 64) (b : Bool) :
    ((((v &&& ~~~(0xff : BitVec 64)) ||| (if b then 1 else 0)).extractLsb' 0 8).zeroExtend 64) = b2v b := by
  cases b <;> simp [b2v] <;> bv_decide

theorem sim_cset (L : List Reg) (s : RS) (x : XS) (hR : Rel L .sub s x) (d : Reg) (c : SetCond) (xd : XReg)
    (hd : xreg? d = some xd) :
    ∃ x', xsteps x (x86Items (.cset d c)) = some x' ∧ Rel (upd L d) .sub (s.set d (b2v (scHolds c s.flags))) x' := by
  simp only [x86Items, dst, hd, Option.getD_some]
  refine ⟨_, by rw [xsteps_cons _ _ _ _ rfl]; exact xsteps_single _ _ _ rfl, ?_⟩
  simp only [XS.set_regs, ite_true, setcond_sub c s.flags x.flags hR.flags, setcc_movzx]
  have h1 := hR.setReg d xd hd ((x.regs xd &&& ~~~(0xff : BitVec 64)) ||| (if scHolds c s.flags then 1 else 0))
    (home_ne_rsp d xd hd)
  have h2 := h1.setReg d xd hd (b2v (scHolds c s.flags)) (home_ne_rsp d xd hd)
  rw [AsmRun.set_set_same] at h2
  exact h2.mono (upd_upd_sub L d)

theorem sim_tstImm (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (r : Reg) (xr : XReg)
    (hr' : xreg? r = some xr) (hr : r ∈ L) (i : Nat) :
    ∃ x', xsteps x (x86Items (.tstImm r i)) = some x' ∧
      Rel L .logic (s.withFlags (logicFlags (s.regs r &&& BitVec.ofNat 64 i))) x' := by
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [dst, hr', Option.getD_some, hR.val r hr xr hr', ofInt_ofNat]
  exact hR.setFlags .logic _ _ (logicXF_rel _)

theorem sim_rev (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) :
    ∃ x', xsteps x (x86Items (.rev d a)) = some x' ∧ Rel (upd L d) p (s.set d (rev64 (s.regs a))) x' := by
  by_cases hda : d = a
  · subst hda
    simp only [x86Items, beq_self_eq_true, ite_true, dst, hd, Option.getD_some]
    refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
    rw [hR.val d ha xd hd]
    exact hR.setReg d xd hd _ (home_ne_rsp d xd hd)
  · simp only [x86Items, beq_iff_eq, hda, ite_false]
    obtain ⟨i, hi, hstep⟩ := movFrom_step x (dst d) a (hR.isSome a ha)
    refine ⟨_, by rw [hi, xsteps_cons _ _ _ _ hstep]; exact xsteps_single _ _ _ rfl, ?_⟩
    simp only [dst, hd, Option.getD_some, XS.set_regs, ite_true, hR.opVal a ha]
    have h1 := hR.setReg d xd hd (s.regs a) (home_ne_rsp d xd hd)
    have h2 := h1.setReg d xd hd (rev64 (s.regs a)) (home_ne_rsp d xd hd)
    rw [AsmRun.set_set_same] at h2
    exact h2.mono (upd_upd_sub L d)

theorem sim_mvn (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) :
    ∃ x', xsteps x (x86Items (.mvn d a)) = some x' ∧ Rel (upd L d) p (s.set d (~~~ s.regs a)) x' := by
  by_cases hda : d = a
  · subst hda
    simp only [x86Items, beq_self_eq_true, ite_true, dst, hd, Option.getD_some]
    refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
    rw [hR.val d ha xd hd]
    exact hR.setReg d xd hd _ (home_ne_rsp d xd hd)
  · simp only [x86Items, beq_iff_eq, hda, ite_false]
    obtain ⟨i, hi, hstep⟩ := movFrom_step x (dst d) a (hR.isSome a ha)
    refine ⟨_, by rw [hi, xsteps_cons _ _ _ _ hstep]; exact xsteps_single _ _ _ rfl, ?_⟩
    simp only [dst, hd, Option.getD_some, XS.set_regs, ite_true, hR.opVal a ha]
    have h1 := hR.setReg d xd hd (s.regs a) (home_ne_rsp d xd hd)
    have h2 := h1.setReg d xd hd (~~~ s.regs a) (home_ne_rsp d xd hd)
    rw [AsmRun.set_set_same] at h2
    exact h2.mono (upd_upd_sub L d)

/-! ### Memory and the stack pointer -/

theorem ea_disp (x : XS) (b : XReg) (o : Nat) :
    ea x { base := b, disp := Int.ofNat o } = x.regs b + BitVec.ofNat 64 o := by
  simp [ea]

theorem ea_base (x : XS) (b : XReg) : ea x { base := b } = x.regs b := by simp [ea]

theorem ea_index (x : XS) (b i : XReg) : ea x { base := b, index := some i } = x.regs b + x.regs i := by
  simp [ea]

theorem valOf_store64 (x : XS) (a v : BitVec 64) (r : Reg) (hr : xreg? r = some xr) :
    valOf (x.store64 a v) r = valOf x r := by simp [valOf, hr, XS.store64]
theorem valOf_store8 (x : XS) (a : BitVec 64) (v : BitVec 8) (r : Reg) (hr : xreg? r = some xr) :
    valOf (x.store8 a v) r = valOf x r := by simp [valOf, hr, XS.store8]

theorem Rel.store64 {L : List Reg} {p : Prov} {s : RS} {x : XS} (hR : Rel L p s x) (a v : BitVec 64) :
    Rel (updStore L) p (s.store64 a v) (x.store64 a v) := by
  refine ⟨?_, by simpa using hR.sp, by simp [hR.mem], by simpa using hR.flags⟩
  intro r hr
  simp only [updStore, List.mem_filter, Bool.not_eq_true', isNos, Option.isSome_eq_false_iff,
             Option.isNone_iff_eq_none] at hr
  cases hx : xreg? r with
  | some xr => rw [valOf_store64 _ _ _ _ hx, hR.regs r hr.1]; rfl
  | none => have := hR.regs r hr.1; simp [valOf, hx, hr.2] at this

theorem Rel.store8 {L : List Reg} {p : Prov} {s : RS} {x : XS} (hR : Rel L p s x) (a : BitVec 64) (v : BitVec 8) :
    Rel (updStore L) p (s.store8 a v) (x.store8 a v) := by
  refine ⟨?_, by simpa using hR.sp, by simp [hR.mem], by simpa using hR.flags⟩
  intro r hr
  simp only [updStore, List.mem_filter, Bool.not_eq_true', isNos, Option.isSome_eq_false_iff,
             Option.isNone_iff_eq_none] at hr
  cases hx : xreg? r with
  | some xr => rw [valOf_store8 _ _ _ _ hx, hR.regs r hr.1]; rfl
  | none => have := hR.regs r hr.1; simp [valOf, hx, hr.2] at this

theorem sim_ldrOff (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d b : Reg) (xd xb : XReg)
    (hd : xreg? d = some xd) (hb' : xreg? b = some xb) (hb : b ∈ L) (o : Nat) :
    ∃ x', xsteps x (x86Items (.ldrOff d b o)) = some x' ∧
      Rel (upd L d) p (s.set d (ld64 s.mem (s.regs b + BitVec.ofNat 64 o))) x' := by
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [dst, hd, hb', Option.getD_some, ea_disp, hR.val b hb xb hb', hR.mem]
  exact hR.setReg d xd hd _ (home_ne_rsp d xd hd)

theorem sim_ldrBase (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d b : Reg) (xd xb : XReg)
    (hd : xreg? d = some xd) (hb' : xreg? b = some xb) (hb : b ∈ L) :
    ∃ x', xsteps x (x86Items (.ldrBase d b)) = some x' ∧ Rel (upd L d) p (s.set d (ld64 s.mem (s.regs b))) x' := by
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [dst, hd, hb', Option.getD_some, ea_base, hR.val b hb xb hb', hR.mem]
  exact hR.setReg d xd hd _ (home_ne_rsp d xd hd)

theorem sim_ldpOff (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (r1 r2 b : Reg) (x1 x2 xb : XReg)
    (h1 : xreg? r1 = some x1) (h2 : xreg? r2 = some x2) (hb' : xreg? b = some xb) (hb : b ∈ L) (o : Nat)
    (hc : clobbers r1 b = false) (hne : r1 ≠ b) :
    ∃ x', xsteps x (x86Items (.ldpOff r1 r2 b o)) = some x' ∧
      Rel (upd (upd L r1) r2) p
        ((s.set r1 (ld64 s.mem (s.regs b + BitVec.ofNat 64 o))).set r2
          (ld64 s.mem (s.regs b + BitVec.ofNat 64 (o + 8)))) x' := by
  simp only [x86Items, dst, h1, h2, hb', Option.getD_some]
  refine ⟨_, by rw [xsteps_cons _ _ _ _ rfl]; exact xsteps_single _ _ _ rfl, ?_⟩
  have hvb := hR.val b hb xb hb'
  have hx1 : xb ≠ x1 := home_ne_of_not_clobbers r1 b x1 xb h1 hb' hne hc
  have hA := hR.setReg r1 x1 h1 (ld64 s.mem (s.regs b + BitVec.ofNat 64 o)) (home_ne_rsp _ _ h1)
  have hB := Rel.setReg hA r2 x2 h2 (ld64 s.mem (s.regs b + BitVec.ofNat 64 (o + 8))) (home_ne_rsp _ _ h2)
  simp only [ea_disp, XS.set_regs, XS.set_mem, if_neg hx1, hvb, hR.mem]
  exact hB

theorem sim_strOff (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (src b : Reg) (xs xb : XReg)
    (hs' : xreg? src = some xs) (hb' : xreg? b = some xb) (hs : src ∈ L) (hb : b ∈ L) (o : Nat) :
    ∃ x', xsteps x (x86Items (.strOff src b o)) = some x' ∧
      Rel (updStore L) p (s.store64 (s.regs b + BitVec.ofNat 64 o) (s.regs src)) x' := by
  have hn : nosLimb src = none := by cases src <;> simp_all [nosLimb, xreg?]
  simp only [x86Items, hn, dst, hs', hb', Option.getD_some]
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [ea_disp, hR.val b hb xb hb', hR.val src hs xs hs']
  exact hR.store64 _ _

theorem sim_stpOff (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (r1 r2 b : Reg) (x1 x2 xb : XReg)
    (h1 : xreg? r1 = some x1) (h2 : xreg? r2 = some x2) (hb' : xreg? b = some xb)
    (hr1 : r1 ∈ L) (hr2 : r2 ∈ L) (hb : b ∈ L) (o : Nat) :
    ∃ x', xsteps x (x86Items (.stpOff r1 r2 b o)) = some x' ∧
      Rel (updStore L) p ((s.store64 (s.regs b + BitVec.ofNat 64 o) (s.regs r1)).store64
        (s.regs b + BitVec.ofNat 64 (o + 8)) (s.regs r2)) x' := by
  have hn1 : nosLimb r1 = none := by cases r1 <;> simp_all [nosLimb, xreg?]
  have hn2 : nosLimb r2 = none := by cases r2 <;> simp_all [nosLimb, xreg?]
  simp only [x86Items, hn1, hn2, dst, h1, h2, hb', Option.getD_some, List.cons_append, List.nil_append]
  refine ⟨_, by rw [xsteps_cons _ _ _ _ rfl]; exact xsteps_single _ _ _ rfl, ?_⟩
  simp only [ea_disp, XS.store64_regs, hR.val b hb xb hb', hR.val r1 hr1 x1 h1, hR.val r2 hr2 x2 h2]
  have hA := hR.store64 (s.regs b + BitVec.ofNat 64 o) (s.regs r1)
  have hB := hA.store64 (s.regs b + BitVec.ofNat 64 (o + 8)) (s.regs r2)
  exact hB.mono (fun r hr => by simp only [updStore, List.mem_filter] at hr ⊢; exact ⟨⟨hr.1, hr.2⟩, hr.2⟩)

theorem sim_strbOff (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (src b : Reg) (xs xb : XReg)
    (hs' : xreg? src = some xs) (hb' : xreg? b = some xb) (hs : src ∈ L) (hb : b ∈ L) (o : Nat) :
    ∃ x', xsteps x (x86Items (.strbOff src b o)) = some x' ∧
      Rel (updStore L) p (s.store8 (s.regs b + BitVec.ofNat 64 o) ((s.regs src).extractLsb' 0 8)) x' := by
  simp only [x86Items, dst, hs', hb', Option.getD_some]
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [ea_disp, hR.val b hb xb hb', hR.val src hs xs hs']
  exact hR.store8 _ _

theorem sim_strZr (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (b : Reg) (xb : XReg)
    (hb' : xreg? b = some xb) (hb : b ∈ L) (o : Nat) :
    ∃ x', xsteps x (x86Items (.strZr b o)) = some x' ∧
      Rel (updStore L) p (s.store64 (s.regs b + BitVec.ofNat 64 o) 0) x' := by
  simp only [x86Items, dst, hb', Option.getD_some]
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [ea_disp, hR.val b hb xb hb', ofInt_zero]
  exact hR.store64 _ _

theorem sim_ldrbOff (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d b : Reg) (xd xb : XReg)
    (hd : xreg? d = some xd) (hb' : xreg? b = some xb) (hb : b ∈ L) (o : Nat) :
    ∃ x', xsteps x (x86Items (.ldrbOff d b o)) = some x' ∧
      Rel (upd L d) p (s.set d ((s.mem (s.regs b + BitVec.ofNat 64 o)).zeroExtend 64)) x' := by
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [dst, hd, hb', Option.getD_some, ea_disp, hR.val b hb xb hb', hR.mem]
  exact hR.setReg d xd hd _ (home_ne_rsp d xd hd)

theorem sim_ldrbReg (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d b i : Reg) (xd xb xi : XReg)
    (hd : xreg? d = some xd) (hb' : xreg? b = some xb) (hi' : xreg? i = some xi) (hb : b ∈ L) (hi : i ∈ L) :
    ∃ x', xsteps x (x86Items (.ldrbReg d b i)) = some x' ∧
      Rel (upd L d) p (s.set d ((s.mem (s.regs b + s.regs i)).zeroExtend 64)) x' := by
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [dst, hd, hb', hi', Option.getD_some, ea_index, hR.val b hb xb hb', hR.val i hi xi hi', hR.mem]
  exact hR.setReg d xd hd _ (home_ne_rsp d xd hd)

/-- rsp is no register's home, so writing it keeps every live value. -/
theorem valOf_set_rsp (x : XS) (v : BitVec 64) (r : Reg) : valOf (x.set .rsp v) r = valOf x r := by
  cases hr : xreg? r with
  | some xr => have := home_ne_rsp r xr hr; simp [valOf, hr, XS.set, this]
  | none =>
    cases hl : nosLimb r with
    | some l => simp [valOf, hr, hl, ea, nosMemX, XS.set]
    | none => simp [valOf, hr, hl]

theorem Rel.setSp {L : List Reg} {p : Prov} {s : RS} {x : XS} (hR : Rel L p s x) (v : BitVec 64) :
    Rel L p (s.withSp v) (x.set .rsp v) :=
  ⟨fun r hr => by rw [valOf_set_rsp, hR.regs r hr]; rfl, by simp [XS.set], by simpa using hR.mem,
   by simpa using hR.flags⟩

theorem sim_addSp (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (n : Nat) :
    ∃ x', xsteps x (x86Items (.addSp d n)) = some x' ∧ Rel (upd L d) p (s.set d (s.sp + BitVec.ofNat 64 n)) x' := by
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [dst, hd, Option.getD_some, ea_disp, hR.sp]
  exact hR.setReg d xd hd _ (home_ne_rsp d xd hd)

theorem sim_spSub (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (n : Nat) :
    ∃ x', xsteps x (x86Items (.spSub n)) = some x' ∧ Rel L .unknown (s.withSp (s.sp - BitVec.ofNat 64 n)) x' := by
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [aluR, alu, hR.sp, ofInt_ofNat]
  exact (hR.setSp _).forget _

theorem sim_spAdd (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (n : Nat) :
    ∃ x', xsteps x (x86Items (.spAdd n)) = some x' ∧ Rel L .unknown (s.withSp (s.sp + BitVec.ofNat 64 n)) x' := by
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [aluR, alu, hR.sp, ofInt_ofNat]
  exact (hR.setSp _).forget _

/-! ## Control: fragments with local labels, fault exits, helper calls -/

/-- The x86 helper boundary: the C helpers' values (shared with the ARM model),
    and what a call leaves in the caller-saved registers, the flags and the
    memory below rsp. SysV: out = rdi, a = rsi, b = rdx, c = rcx. -/
structure XHelpers where
  fns  : Helpers
  clob : String → XS → XReg → BitVec 64
  flg  : String → XS → XFlags
  junk : String → XS → BitVec 64 → BitVec 8
  /-- the helper a `CallRip` slot is bound to by the loader (`Lsym_<h>` ↦ `h`) -/
  sym  : String → String

/-- SysV caller-saved. -/
def xCallerSaved : XReg → Bool
  | .rax | .rcx | .rdx | .rsi | .rdi | .r8 | .r9 | .r10 | .r11 => true
  | _ => false

def xcall (HX : XHelpers) (slot : String) (x : XS) : XS :=
  let h := HX.sym slot
  let out := x.regs .rdi
  let a := ld256 x.mem (x.regs .rsi)
  let b := ld256 x.mem (x.regs .rdx)
  let v := if ternary h then HX.fns.fn3 h a b (ld256 x.mem (x.regs .rcx)) else HX.fns.fn2 h a b
  let below : AsmRun.Mem := fun y => if belowSp (x.regs .rsp) y then HX.junk h x y else x.mem y
  { regs := fun r => if xCallerSaved r then HX.clob h x r else x.regs r,
    flags := HX.flg h x, mem := st256 below out v }

inductive XOutcome where
  /-- fell off the fragment's end -/
  | done (x : XS)
  /-- `ret` -/
  | ret  (x : XS)
  /-- control left the fragment: to a fault symbol (`JccSym`/`JmpSym`) or to
      a label the fragment does not define (a trampoline, `Lx_oog`) -/
  | exit (target : String) (x : XS)
  /-- an instruction outside the modelled subset -/
  | stuck

/-- Forward local labels, the assembler's rule (`Nf` names the next `N`). -/
def xskipTo (lbl : String) : List XItem → Option (List XItem)
  | [] => none
  | (.L t) :: rest => if lbl == t || lbl == t ++ "f" then some ((.L t) :: rest) else xskipTo lbl rest
  | _ :: rest => xskipTo lbl rest

theorem xskipTo_length_le (lbl : String) (xs : List XItem) (ys : List XItem) (h : xskipTo lbl xs = some ys) :
    ys.length ≤ xs.length := by
  induction xs with
  | nil => simp [xskipTo] at h
  | cons x rest ih =>
    cases x <;> simp only [xskipTo] at h <;> try (exact Nat.le_succ_of_le (ih h))
    split at h
    · cases h; exact Nat.le_refl _
    · exact Nat.le_succ_of_le (ih h)

def xrun (HX : XHelpers) : List XItem → XS → XOutcome
  | [], x => .done x
  | it :: rest, x =>
    match it with
    | .L _          => xrun HX rest x
    | .Jmp l        => match _h : xskipTo l rest with
                       | some r => xrun HX r x
                       | none => .exit l x
    | .Jcc c l      => if xcHolds c x.flags then
                         (match _h : xskipTo l rest with
                          | some r => xrun HX r x
                          | none => .exit l x)
                       else xrun HX rest x
    | .JccSym c sym => if xcHolds c x.flags then .exit sym x else xrun HX rest x
    | .JmpSym sym   => .exit sym x
    | .CallRip slot => xrun HX rest (xcall HX slot x)
    | .I .ret       => .ret x
    | .I i          => match xstep x i with
                       | some x' => xrun HX rest x'
                       | none => .stuck
    | _             => .stuck
termination_by p => p.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Nat.lt_succ_self _
    | exact Nat.lt_succ_of_le (xskipTo_length_le _ _ _ ‹xskipTo _ _ = some _›)

@[simp] theorem xrun_nil (HX : XHelpers) (x : XS) : xrun HX [] x = .done x := by simp [xrun]

theorem xrun_cons_I (HX : XHelpers) (i : XInsn) (hi : i ≠ .ret) (rest : List XItem) (x x' : XS)
    (h : xstep x i = some x') : xrun HX (.I i :: rest) x = xrun HX rest x' := by
  cases i <;> simp [xrun, h] at *

theorem xrun_cons_L (HX : XHelpers) (l : String) (rest : List XItem) (x : XS) :
    xrun HX (.L l :: rest) x = xrun HX rest x := by simp [xrun]

theorem xrun_cons_Jcc_not (HX : XHelpers) (c : XCond) (l : String) (rest : List XItem) (x : XS)
    (hc : xcHolds c x.flags = false) : xrun HX (.Jcc c l :: rest) x = xrun HX rest x := by
  simp [xrun, hc]

theorem xrun_cons_Jcc_exit (HX : XHelpers) (c : XCond) (l : String) (rest : List XItem) (x : XS)
    (hc : xcHolds c x.flags = true) (hs : xskipTo l rest = none) : xrun HX (.Jcc c l :: rest) x = .exit l x := by
  simp only [xrun, hc, if_true]; split <;> simp_all

theorem xrun_cons_Jcc_skip (HX : XHelpers) (c : XCond) (l : String) (rest r : List XItem) (x : XS)
    (hc : xcHolds c x.flags = true) (hs : xskipTo l rest = some r) : xrun HX (.Jcc c l :: rest) x = xrun HX r x := by
  simp only [xrun, hc, if_true]; split <;> simp_all

theorem xrun_cons_Jmp_exit (HX : XHelpers) (l : String) (rest : List XItem) (x : XS)
    (hs : xskipTo l rest = none) : xrun HX (.Jmp l :: rest) x = .exit l x := by
  simp only [xrun]; split <;> simp_all

theorem xrun_cons_Jmp_skip (HX : XHelpers) (l : String) (rest r : List XItem) (x : XS)
    (hs : xskipTo l rest = some r) : xrun HX (.Jmp l :: rest) x = xrun HX r x := by
  simp only [xrun]; split <;> simp_all

theorem xrun_cons_JccSym (HX : XHelpers) (c : XCond) (sym : String) (rest : List XItem) (x : XS) :
    xrun HX (.JccSym c sym :: rest) x = if xcHolds c x.flags then .exit sym x else xrun HX rest x := by
  simp [xrun]

theorem xrun_cons_CallRip (HX : XHelpers) (slot : String) (rest : List XItem) (x : XS) :
    xrun HX (.CallRip slot :: rest) x = xrun HX rest (xcall HX slot x) := by simp [xrun]

theorem xrun_cons_ret (HX : XHelpers) (rest : List XItem) (x : XS) : xrun HX (.I .ret :: rest) x = .ret x := by
  simp [xrun]

/-- Straight-line prefixes compose with `xsteps`. -/
theorem xrun_xsteps (HX : XHelpers) : ∀ (its : List XItem) (rest : List XItem) (x x' : XS),
    (∀ i ∈ its, ∀ j, i = .I j → j ≠ .ret) → xsteps x its = some x' → xrun HX (its ++ rest) x = xrun HX rest x'
  | [], rest, x, x', _, h => by simp [xsteps] at h; subst h; rfl
  | .I i :: its, rest, x, x', hnr, h => by
    simp only [xsteps] at h
    split at h
    · rename_i x1 hx1
      rw [List.cons_append, xrun_cons_I HX i (hnr _ (by simp) i rfl) _ _ _ hx1]
      exact xrun_xsteps HX its rest x1 x' (fun i hi => hnr i (by simp [hi])) h
    · cases h
  | .L _ :: _, _, _, _, _, h => by simp [xsteps] at h
  | .Jcc _ _ :: _, _, _, _, _, h => by simp [xsteps] at h
  | .Jmp _ :: _, _, _, _, _, h => by simp [xsteps] at h
  | .JccSym _ _ :: _, _, _, _, _, h => by simp [xsteps] at h
  | .JmpSym _ :: _, _, _, _, _, h => by simp [xsteps] at h
  | .LeaRip _ _ :: _, _, _, _, _, h => by simp [xsteps] at h
  | .LeaRipSym _ _ :: _, _, _, _, _, h => by simp [xsteps] at h
  | .QuadOff _ :: _, _, _, _, _, h => by simp [xsteps] at h
  | .Call _ :: _, _, _, _, _, h => by simp [xsteps] at h
  | .CallRip _ :: _, _, _, _, _, h => by simp [xsteps] at h
  | .QuadSym _ :: _, _, _, _, _, h => by simp [xsteps] at h
  | .unlowered _ :: _, _, _, _, _, h => by simp [xsteps] at h

/-! ### `addImm`/`subImm`: in place (flags clobbered), NOS source, or `lea` -/

theorem sim_addImm_lea (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a : Reg) (xd xa : XReg)
    (hd : xreg? d = some xd) (ha' : xreg? a = some xa) (ha : a ∈ L) (hda : d ≠ a) (i : Nat) :
    ∃ x', xsteps x (x86Items (.addImm d a i)) = some x' ∧ Rel (upd L d) p (s.set d (s.regs a + BitVec.ofNat 64 i)) x' := by
  have hn : nosLimb a = none := by cases a <;> simp_all [nosLimb, xreg?]
  simp only [x86Items, hn, dst, hd, ha', Option.getD_some]
  rw [if_neg (by simpa using hda)]
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [ea_disp, hR.val a ha xa ha']
  exact hR.setReg d xd hd _ (home_ne_rsp d xd hd)

theorem sim_addImm_inplace (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (hdL : d ∈ L) (i : Nat) :
    ∃ x', xsteps x (x86Items (.addImm d d i)) = some x' ∧
      Rel (upd L d) .unknown (s.set d (s.regs d + BitVec.ofNat 64 i)) x' := by
  simp only [x86Items, beq_self_eq_true, ite_true, dst, hd, Option.getD_some]
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [aluR, alu, hR.val d hdL xd hd, ofInt_ofNat]
  exact (hR.setReg d xd hd _ (home_ne_rsp d xd hd)).forget _

theorem sim_addImm_nos (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a : Reg) (xd : XReg) (la : Nat)
    (hd : xreg? d = some xd) (ha' : nosLimb a = some la) (ha : a ∈ L) (i : Nat) :
    ∃ x', xsteps x (x86Items (.addImm d a i)) = some x' ∧
      Rel (upd L d) .unknown (s.set d (s.regs a + BitVec.ofNat 64 i)) x' := by
  have hxa := nosLimb_some_xreg_none a la ha'
  have hda : d ≠ a := by intro e; subst e; rw [hd] at hxa; cases hxa
  simp only [x86Items, ha', dst, hd, Option.getD_some]
  rw [if_neg (by simpa using hda)]
  refine ⟨_, by rw [xsteps_cons _ _ _ _ rfl]; exact xsteps_single _ _ _ rfl, ?_⟩
  simp only [aluR, alu, XS.set_regs, ite_true, hR.valNos a ha la ha', ofInt_ofNat]
  have h1 := hR.setReg d xd hd (s.regs a) (home_ne_rsp d xd hd)
  have h2 := h1.setReg d xd hd (s.regs a + BitVec.ofNat 64 i) (home_ne_rsp d xd hd)
  rw [AsmRun.set_set_same] at h2
  exact (h2.mono (upd_upd_sub L d)).forget _

theorem ofInt_neg_ofNat (i : Nat) : BitVec.ofInt 64 (-(Int.ofNat i)) = -BitVec.ofNat 64 i := by
  rw [BitVec.ofInt_neg, ofInt_ofNat]

theorem sim_subImm_lea (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a : Reg) (xd xa : XReg)
    (hd : xreg? d = some xd) (ha' : xreg? a = some xa) (ha : a ∈ L) (hda : d ≠ a) (i : Nat) :
    ∃ x', xsteps x (x86Items (.subImm d a i)) = some x' ∧ Rel (upd L d) p (s.set d (s.regs a - BitVec.ofNat 64 i)) x' := by
  simp only [x86Items, dst, hd, ha', Option.getD_some]
  rw [if_neg (by simpa using hda)]
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  have hz : ∀ v : BitVec 64, v + 0 = v := fun v => by simp
  simp only [ea, hR.val a ha xa ha', ofInt_neg_ofNat, hz, ← BitVec.sub_eq_add_neg]
  exact hR.setReg d xd hd _ (home_ne_rsp d xd hd)

theorem sim_subImm_inplace (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (hdL : d ∈ L) (i : Nat) :
    ∃ x', xsteps x (x86Items (.subImm d d i)) = some x' ∧
      Rel (upd L d) .unknown (s.set d (s.regs d - BitVec.ofNat 64 i)) x' := by
  simp only [x86Items, beq_self_eq_true, ite_true, dst, hd, Option.getD_some]
  refine ⟨_, xsteps_single _ _ _ rfl, ?_⟩
  simp only [aluR, alu, hR.val d hdL xd hd, ofInt_ofNat]
  exact (hR.setReg d xd hd _ (home_ne_rsp d xd hd)).forget _

/-! ### NOS-source stores: through the scratch temporary -/

/-- The scratch temporary is one of rax/rcx/rdx/rsi, never the base's home. -/
theorem nosStoreTemp_ne_base (b : Reg) (xb : XReg) (hb : xreg? b = some xb) : nosStoreTempX b none ≠ xb := by
  simp only [nosStoreTempX, dst, hb, Option.getD_some, Option.map_none, Option.getD_none, List.append_nil]
  cases xb <;> decide

/-- A write to a temporary home: the registers homed there leave the live set. -/
def killHome (L : List Reg) (t : XReg) : List Reg := L.filter (fun r => xreg? r != some t && !isNos r)

theorem Rel.setTemp {L : List Reg} {p : Prov} {s : RS} {x : XS} (hR : Rel L p s x) (t : XReg) (v : BitVec 64)
    (ht : t ≠ .rsp) : Rel (killHome L t) p s (x.set t v) := by
  refine ⟨?_, by simp [XS.set, ht.symm]; exact hR.sp, by simpa using hR.mem, by simpa using hR.flags⟩
  intro r hr
  simp only [killHome, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', isNos,
             Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hr
  obtain ⟨hrL, hne, hnos⟩ := hr
  cases hx : xreg? r with
  | some xr =>
    have hxr : xr ≠ t := by intro e; subst e; exact hne hx
    rw [valOf_reg _ _ _ hx, ← hR.regs r hrL, valOf_reg _ _ _ hx]
    simp [XS.set, hxr]
  | none => have := hR.regs r hrL; simp [valOf, hx, hnos] at this

theorem sim_strOff_nos (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (src b : Reg) (ls : Nat)
    (xb : XReg) (hs' : nosLimb src = some ls) (hb' : xreg? b = some xb) (hs : src ∈ L) (hb : b ∈ L) (o : Nat) :
    ∃ x', xsteps x (x86Items (.strOff src b o)) = some x' ∧
      Rel (updStore (killHome L (nosStoreTempX b none))) p (s.store64 (s.regs b + BitVec.ofNat 64 o) (s.regs src)) x' := by
  have hv := hR.valNos src hs ls hs'
  have ht := nosStoreTemp_ne_base b xb hb'
  simp only [x86Items, hs', dst, hb', Option.getD_some]
  refine ⟨_, by rw [xsteps_cons _ _ _ _ rfl]; exact xsteps_single _ _ _ rfl, ?_⟩
  have htsp : nosStoreTempX b none ≠ .rsp := by
    simp only [nosStoreTempX, dst, hb', Option.getD_some, Option.map_none, Option.getD_none, List.append_nil]
    cases xb <;> decide
  have hA := hR.setTemp (nosStoreTempX b none) (ld64 x.mem (ea x (nosMemX ls))) htsp
  have hB := hA.store64 (s.regs b + BitVec.ofNat 64 o) (s.regs src)
  simp only [ea_disp, XS.set_regs, ite_true, if_neg (Ne.symm ht), hR.val b hb xb hb', hv] at hB ⊢
  exact hB

/-! ### Helper calls: `blSym` under the x86-64 convention -/

/-- The x86-64 frame's helper convention (`X86JIT.x86Flush.helperArgs`). -/
def x86Conv : Reg × Reg × Reg × Reg := (.x3, .x2, .x1, .x14)

/-- The callee-saved ARM registers (`FlushSem.keep`): x19-x28. -/
def calleeKept : Reg → Bool
  | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 | .x28 => true
  | _ => false

/-- The live set after a call: the kept registers that have a home. -/
def killCall (L : List Reg) : List Reg := L.filter (fun r => calleeKept r && !isNos r)

theorem keep_home_calleeSaved (r : Reg) (xr : XReg) (hk : calleeKept r = true) (hx : xreg? r = some xr) :
    xCallerSaved xr = false := by
  cases r <;> simp [calleeKept] at hk <;> cases hx <;> rfl

theorem keep_not_callerSaved' (r : Reg) (hk : calleeKept r = true) : callerSaved r = false := by
  cases r <;> simp_all [calleeKept, callerSaved]

/-- `blSym h` against `call [rip + Lsym_h]`: the out pointer and the arguments
    are read through the x86 convention, the result lands at the same place,
    the junk below sp agrees (the oracles describe one C helper), the kept
    registers survive on both sides. -/
theorem sim_blSym (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (H : Helpers) (HX : XHelpers)
    (h slot : String) (hfns : HX.fns = H) (hconv : H.conv = x86Conv) (hslot : HX.sym slot = h)
    (h3 : Reg.x3 ∈ L) (h2 : Reg.x2 ∈ L) (h1 : Reg.x1 ∈ L) (h14 : ternary h = true → Reg.x14 ∈ L)
    (hjunk : ∀ y, HX.junk h x y = H.junk h s y) :
    Rel (killCall L) .unknown (callHelper H h s) (xcall HX slot x) := by
  have e3 := hR.val .x3 h3 .rdi rfl
  have e2 := hR.val .x2 h2 .rsi rfl
  have e1 := hR.val .x1 h1 .rdx rfl
  refine ⟨?_, ?_, ?_, trivial⟩
  · intro r hr
    simp only [killCall, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', isNos, Option.isSome_eq_false_iff,
               Option.isNone_iff_eq_none] at hr
    obtain ⟨hrL, hk, hnos⟩ := hr
    cases hx : xreg? r with
    | some xr =>
      have hv := hR.val r hrL xr hx
      rw [valOf_reg _ _ _ hx]
      simp only [xcall, keep_home_calleeSaved r xr hk hx, callHelper, keep_not_callerSaved' r hk,
                 Bool.false_eq_true, ite_false, hv]
    | none => have := hR.regs r hrL; simp [valOf, hx, hnos] at this
  · simp only [xcall, callHelper, xCallerSaved]; exact hR.sp
  · by_cases ht : ternary h = true
    · have e14 := hR.val .x14 (h14 ht) .rcx rfl
      simp only [xcall, callHelper, hslot, hfns, hconv, x86Conv, hR.mem, hR.sp, e3, e2, e1, e14]
      congr 1
      funext y
      simp [hjunk y]
    · simp only [xcall, callHelper, hslot, hfns, hconv, x86Conv, hR.mem, hR.sp, e3, e2, e1, ht, Bool.false_eq_true,
                 ite_false]
      congr 1
      funext y
      simp [hjunk y]

/-! ## The x86-64 gas gadgets, under the x86-64 machine

    `X86JIT.gasX86` lowered (`lowerX`): `sub r15, n` sets CF on borrow and
    `jb Lx_oog` leaves the fragment to the OOG trampoline exactly when the
    denotation halts — the x86 twin of `ARM64.ChunkGasSem.ginstr_run`, proven
    directly on the x86 semantics rather than through the ARM flag model. -/

open Evm.CL.ARM64.ChunkGas Evm.CL.X86JIT Evm.CL.OpInstrs in
theorem lowerX_charge (n : Nat) (lbl : String) :
    lowerX (gasX86 (.charge n lbl)) = [.I (.aluRI .sub .r15 (Int.ofNat n)), .Jcc .b "Lx_oog"] := by
  simp [lowerX, gasX86, spScale, OpInstrs.dest?, OpInstrs.isNos, x86Items, dst, xreg?, bcondXc, AsmCore.trampLabel]

open Evm.CL.ARM64.ChunkGas Evm.CL.X86JIT Evm.CL.OpInstrs in
theorem lowerX_handBack (rem : Nat) :
    lowerX (gasX86 (.handBack rem)) = [.I (.movRI .rdx (Int.ofNat rem)), .I (.aluRR .add .r15 .rdx)] := by
  simp [lowerX, gasX86, spScale, OpInstrs.dest?, OpInstrs.isNos, x86Items, dst, xreg?, twoOp, aluFrom]

open Evm.CL.ARM64.ChunkGas Evm.CL.X86JIT Evm.CL.OpInstrs in
theorem lowerX_retake (rem : Nat) (lbl : String) :
    lowerX (gasX86 (.retake rem lbl)) =
      [.I (.movRI .rdx (Int.ofNat rem)), .I (.aluRR .sub .r15 .rdx), .Jcc .b "Lx_oog"] := by
  simp [lowerX, gasX86, spScale, OpInstrs.dest?, OpInstrs.isNos, x86Items, dst, xreg?, twoOp, aluFrom, bcondXc, AsmCore.trampLabel]

/-- The gas register on x86-64 is r15. -/
def xgas (x : XS) : Nat := (x.regs .r15).toNat

theorem toNat_ofNat64 (k : Nat) (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ret_ne_aluRI (o : AluOp) (d : XReg) (i : Int) : XInsn.aluRI o d i ≠ .ret := by intro h; cases h
theorem ret_ne_aluRR (o : AluOp) (d s : XReg) : XInsn.aluRR o d s ≠ .ret := by intro h; cases h
theorem ret_ne_movRI (d : XReg) (i : Int) : XInsn.movRI d i ≠ .ret := by intro h; cases h

open Evm.CL.ARM64.ChunkGas Evm.CL.X86JIT in
/-- `charge`: `sub r15, n ; jb Lx_oog`. With `Lx_oog` not a label of the
    continuation (the OOG trampoline lives in the chunk tail), the fragment
    exits to it exactly when `n > gas` — `GInstr.denote`'s halt. -/
theorem charge_x86 (HX : XHelpers) (n : Nat) (hn : n < 2 ^ 64) (lbl : String) (rest : List XItem) (x : XS) :
    (n ≤ xgas x → ∃ x', xrun HX (lowerX (gasX86 (.charge n lbl)) ++ rest) x = xrun HX rest x' ∧
        xgas x' = xgas x - n ∧ x'.regs .rsp = x.regs .rsp ∧ x'.mem = x.mem ∧
        (∀ r, r ≠ .r15 → x'.regs r = x.regs r)) ∧
    (¬ n ≤ xgas x → xskipTo "Lx_oog" rest = none →
        ∃ x', xrun HX (lowerX (gasX86 (.charge n lbl)) ++ rest) x = .exit "Lx_oog" x') := by
  rw [lowerX_charge, List.cons_append, List.singleton_append,
      xrun_cons_I HX _ (ret_ne_aluRI _ _ _) _ _ _ rfl]
  simp only [aluR, alu]
  have hflag : xcHolds .b ((x.set .r15 (x.regs .r15 - BitVec.ofInt 64 (Int.ofNat n))).withFlags
      (subXF (x.regs .r15) (BitVec.ofInt 64 (Int.ofNat n)))).flags = decide (xgas x < n) := by
    simp [xcHolds, subXF, toNat_ofNat64 n hn, xgas]
  constructor
  · intro hle
    rw [xrun_cons_Jcc_not _ _ _ _ _ (by rw [hflag]; simp; omega)]
    refine ⟨_, rfl, ?_, by simp, by simp, ?_⟩
    · simp only [xgas, XS.set_regs, XS.withFlags_regs, ite_true, ofInt_ofNat]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat64 n hn]; exact hle), toNat_ofNat64 n hn]
    · intro r h15; simp [h15]
  · intro hlt hskip
    rw [xrun_cons_Jcc_exit _ _ _ _ _ (by rw [hflag]; simp; omega) hskip]
    exact ⟨_, rfl⟩

open Evm.CL.ARM64.ChunkGas Evm.CL.X86JIT in
/-- `handBack`: `mov rdx, rem ; add r15, rdx`. -/
theorem handBack_x86 (HX : XHelpers) (rem : Nat) (rest : List XItem) (x : XS) (hw : xgas x + rem < 2 ^ 64) :
    ∃ x', xrun HX (lowerX (gasX86 (.handBack rem)) ++ rest) x = xrun HX rest x' ∧
      xgas x' = xgas x + rem ∧ x'.regs .rsp = x.regs .rsp ∧ x'.mem = x.mem ∧
      (∀ r, r ≠ .r15 → r ≠ .rdx → x'.regs r = x.regs r) := by
  have hrem : rem < 2 ^ 64 := by unfold xgas at hw; omega
  rw [lowerX_handBack, List.cons_append, List.singleton_append,
      xrun_cons_I HX _ (ret_ne_movRI _ _) _ _ _ rfl, xrun_cons_I HX _ (ret_ne_aluRR _ _ _) _ _ _ rfl]
  simp only [aluR, alu]
  refine ⟨_, rfl, ?_, by simp, by simp, ?_⟩
  · simp only [xgas, XS.set_regs, XS.withFlags_regs, ite_true, reduceCtorEq, ite_false, ofInt_ofNat]
    rw [BitVec.toNat_add, toNat_ofNat64 rem hrem, Nat.mod_eq_of_lt (by unfold xgas at hw; omega)]
  · intro r h15 hdx; simp [h15, hdx]

open Evm.CL.ARM64.ChunkGas Evm.CL.X86JIT in
/-- `retake`: `mov rdx, rem ; sub r15, rdx ; jb lbl` — checked, like `charge`. -/
theorem retake_x86 (HX : XHelpers) (rem : Nat) (hn : rem < 2 ^ 64) (lbl : String) (rest : List XItem) (x : XS) :
    (rem ≤ xgas x → ∃ x', xrun HX (lowerX (gasX86 (.retake rem lbl)) ++ rest) x = xrun HX rest x' ∧
        xgas x' = xgas x - rem ∧ x'.regs .rsp = x.regs .rsp ∧ x'.mem = x.mem ∧
        (∀ r, r ≠ .r15 → r ≠ .rdx → x'.regs r = x.regs r)) ∧
    (¬ rem ≤ xgas x → xskipTo "Lx_oog" rest = none →
        ∃ x', xrun HX (lowerX (gasX86 (.retake rem lbl)) ++ rest) x = .exit "Lx_oog" x') := by
  rw [lowerX_retake, List.cons_append, List.cons_append, List.singleton_append,
      xrun_cons_I HX _ (ret_ne_movRI _ _) _ _ _ rfl, xrun_cons_I HX _ (ret_ne_aluRR _ _ _) _ _ _ rfl]
  simp only [aluR, alu, XS.set_regs, ite_true, reduceCtorEq, ite_false, ofInt_ofNat]
  have hflag : xcHolds .b (((x.set .rdx (BitVec.ofNat 64 rem)).set .r15 (x.regs .r15 - BitVec.ofNat 64 rem)).withFlags
      (subXF (x.regs .r15) (BitVec.ofNat 64 rem))).flags = decide (xgas x < rem) := by
    simp [xcHolds, subXF, toNat_ofNat64 rem hn, xgas]
  constructor
  · intro hle
    rw [xrun_cons_Jcc_not _ _ _ _ _ (by rw [hflag]; simp; omega)]
    refine ⟨_, rfl, ?_, by simp, by simp, ?_⟩
    · simp only [xgas, XS.set_regs, XS.withFlags_regs, ite_true]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat64 rem hn]; exact hle), toNat_ofNat64 rem hn]
    · intro r h15 hdx; simp [h15, hdx]
  · intro hlt hskip
    rw [xrun_cons_Jcc_exit _ _ _ _ _ (by rw [hflag]; simp; omega) hskip]
    exact ⟨_, rfl⟩

/-! ### The flagless carry forms and the shift-right-then-add -/

/-- `adc d, a, b` (ARM, flags untouched): the x86 `adc` sets them, so the
    provenance is forgotten. -/
theorem sim_adc (L : List Reg) (s : RS) (x : XS) (hR : Rel L .add s x) (d a b : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) (hb : b ∈ L) (hside : d = a ∨ d = b ∨ clobbers d b = false) :
    ∃ x', xsteps x (x86Items (.adc d a b)) = some x' ∧
      Rel (upd L d) .unknown (s.set d (addc (s.regs a) (s.regs b) s.flags.c).1) x' := by
  obtain ⟨x', hx', hR'⟩ := sim_adcs L s x hR d a b xd hd ha hb hside
  refine ⟨x', by simpa [x86Items] using hx', ?_⟩
  have h := hR'.forget x'.flags
  have e : x'.withFlags x'.flags = x' := by cases x'; rfl
  rw [e] at h
  exact ⟨fun r hr => by simpa [valOf, ea, AsmRun.RS.withFlags] using h.regs r hr, h.sp, h.mem, trivial⟩

theorem sim_sbc (L : List Reg) (s : RS) (x : XS) (hR : Rel L .sub s x) (d a b : Reg) (xd : XReg)
    (hd : xreg? d = some xd) (ha : a ∈ L) (hb : b ∈ L) (hside : d = a ∨ (d ≠ b ∧ clobbers d b = false)) :
    ∃ x', xsteps x (x86Items (.sbc d a b)) = some x' ∧
      Rel (upd L d) .unknown (s.set d (subc (s.regs a) (s.regs b) s.flags.c).1) x' := by
  obtain ⟨x', hx', hR'⟩ := sim_sbcs L s x hR d a b xd hd ha hb hside
  refine ⟨x', by simpa [x86Items] using hx', ?_⟩
  have h := hR'.forget x'.flags
  have e : x'.withFlags x'.flags = x' := by cases x'; rfl
  rw [e] at h
  exact ⟨fun r hr => by simpa [valOf, ea, AsmRun.RS.withFlags] using h.regs r hr, h.sp, h.mem, trivial⟩

/-- `addLsr d a d sh` (the accumulating form): `shr d, sh ; add d, a`. -/
theorem sim_addLsr_acc (L : List Reg) (p : Prov) (s : RS) (x : XS) (hR : Rel L p s x) (d a : Reg) (xd xa : XReg)
    (hd : xreg? d = some xd) (ha' : xreg? a = some xa) (hne : xa ≠ xd) (ha : a ∈ L) (hdL : d ∈ L) (sh : Nat) :
    ∃ x', xsteps x (x86Items (.addLsr d a d sh)) = some x' ∧
      Rel (upd L d) .unknown (s.set d (s.regs a + (s.regs d >>> sh))) x' := by
  simp only [x86Items, beq_self_eq_true, ite_true]
  obtain ⟨x', hx', hx'eq⟩ := shiftThenAdd_run x .shr (dst d) sh a (hR.isSome a ha)
    (fun xa' hxa' => by rw [ha'] at hxa'; cases hxa'; simpa [dst, hd] using hne)
    (fun l hl => by exfalso; cases a <;> simp [nosLimb] at hl <;> simp [xreg?] at ha')
  refine ⟨x', hx', ?_⟩
  rw [hx'eq, aluR_set _ _ _ _ (by decide)]
  simp only [dst, hd, Option.getD_some, XS.withFlags_regs, XS.set_regs, ite_true, alu, hR.opVal a ha,
             hR.val d hdL xd hd]
  rw [BitVec.add_comm (s.regs d >>> sh)]
  have h1 := hR.setReg d xd hd (s.regs d >>> sh) (home_ne_rsp d xd hd)
  have h2 := (h1.forget (clobXF x.flags (s.regs d >>> sh))).setReg d xd hd (s.regs a + (s.regs d >>> sh))
    (home_ne_rsp d xd hd)
  rw [AsmRun.set_set_same] at h2
  refine (h2.mono (fun r hr => ?_)).forget _
  simp only [upd, List.mem_cons, List.mem_filter, Bool.not_eq_true'] at hr ⊢
  rcases hr with rfl | ⟨hr, hc⟩
  · left; rfl
  · right; exact ⟨Or.inr ⟨hr, hc⟩, hc⟩

end Evm.CL.X86Sem
