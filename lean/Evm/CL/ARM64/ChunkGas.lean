/-
  Evm.CL.ARM64.ChunkGas — the chunk's gas accounting, with a denotation.

  Stage 1 of #238 (docs/x86-64-backend.md): the ~660 lines of raw mnemonic
  strings in the emitters have no denotation, so nothing about them can be
  proved and nothing can be derived for a second target. This module closes
  that gap for the piece that cost the most: the JIT chunk's gas accounting.

  A chunk is a straight-line block, so its head pre-charges the WHOLE block's
  static gas in one `subs`. Two ops read gas mid-chunk (`observesGas`: GAS and
  SSTORE), and for those the pre-charge of strictly-later ops is handed BACK
  before the handler and taken again after, so the handler sees the gas the
  spec says it should. Three gadgets, then:

      charge n lbl     subs x22,x22,#n   (or movz/movk x14 + subs) + OOG branch
      handBack rem     movz/movk x15     + add  x22,x22,x15
      retake rem lbl   movz/movk x15     + subs x22,x22,x15 + OOG branch

  Each was hand-written twice — once as text for the clang path, once as
  `Item`s for the in-process encoder — and `retake` was written with a bare
  `sub`, with no borrow check. That is the whole of the second JIT bug: the
  handler charges its dynamic cost against the COMPENSATED pool, so a cost `c`
  with `gas < c ≤ gas + rem` passes the handler's own check and leaves the
  re-take to wrap the u64 gas register just under 2^64. The frame then ran on
  with ~1.8e19 gas instead of halting (Arc 12 881 017 tx 24).

  `compensation_refines` below is the theorem that was missing: with a CHECKED
  re-take the hand-back pair is transparent — the chunk charges exactly what
  per-op charging would. `compensation_unchecked_is_wrong` exhibits the bug as a
  counterexample rather than a comment, and the unchecked form is not a `GInstr`
  at all, so no emitter can produce it.
-/

import Evm.CL.AsmEncode
import Evm.CL.ARM64

namespace Evm.CL.ARM64.ChunkGas

open Evm.CL.AsmEncode Evm.CL.AsmEncode.Insn Evm.CL.AsmEncode.Item

/-- 2^64: the gas register is a u64, and that is the whole point here. -/
def W : Nat := 18446744073709551616

/-- The only machine state the gas gadgets touch. `halted` is the frame exiting
    through `_eita_oog`, which does not return. -/
structure GMach where
  gas    : Nat
  halted : Bool
  deriving DecidableEq, Repr

/-- Out of gas: the stub halts the frame; the register value is then dead. -/
def oog : GMach := { gas := 0, halted := true }

/-- The gas gadgets. Note what is ABSENT: there is no unchecked subtraction
    constructor, so neither emitter can produce one (cf. `AsmCore`, where the
    MSIZE bug is likewise not representable). -/
inductive GInstr where
  /-- Chunk head: take `n` for the whole block, branch to `_eita_oog` on borrow.
      `lbl` is the local label the carry-set branch skips to. Scratch: x14. -/
  | charge   (n : Nat) (lbl : String)
  /-- Give `rem` back before a handler that READS gas. Scratch: x15. -/
  | handBack (rem : Nat)
  /-- Take `rem` again afterwards. MUST be checked — see the module header.
      Scratch: x15. -/
  | retake   (rem : Nat) (lbl : String)
  deriving DecidableEq, Repr

/-- `subs` + a carry-set branch is exactly "unsigned no borrow", i.e. `n ≤ gas`. -/
def GInstr.denote : GInstr → GMach → GMach
  | .charge n _,   m => if n ≤ m.gas then { m with gas := m.gas - n } else oog
  | .handBack rem, m => { m with gas := m.gas + rem }
  | .retake rem _, m => if rem ≤ m.gas then { m with gas := m.gas - rem } else oog

/-- What a bare `sub x22, x22, x15` does: wrap, silently. Deliberately NOT a
    `GInstr` — it exists only to be refuted below. -/
def retakeUnchecked (rem : Nat) (m : GMach) : GMach :=
  { m with gas := (m.gas + W - rem % W) % W }

/-! ## The emitter — one definition per gadget -/

/-- The gadget as `AInstr` (stage 4s): the one body the text and the bytes are both
    lowered from. -/
def GInstr.instrs : GInstr → List Evm.CL.AsmCore.AInstr
  | .charge n lbl =>
      (if n ≤ 4095 then [.subsImm .x22 .x22 n]
       else Evm.CL.AsmCore.movImmInstrs .x14 n ++ [.subsReg .x22 .x22 .x14]) ++
      [.bcLbl .hs lbl, .bFar "_eita_oog", .label lbl]
  | .handBack rem => Evm.CL.AsmCore.movImmInstrs .x15 rem ++ [.addReg .x22 .x22 .x15]
  | .retake rem lbl =>
      Evm.CL.AsmCore.movImmInstrs .x15 rem ++
      [.subsReg .x22 .x22 .x15, .bcLbl .hs lbl, .bFar "_eita_oog", .label lbl]

/-! ## Per-op charging, and the refinement -/

/-- Charging each op's cost in turn — what the interpreter tier does, and the
    specification the chunk's single pre-charge has to refine. -/
def chargeEach : List Nat → GMach → GMach
  | [],      m => m
  | c :: cs, m => chargeEach cs ((GInstr.charge c "").denote m)

@[simp] theorem chargeEach_nil (m : GMach) : chargeEach [] m = m := rfl

theorem chargeEach_cons (c : Nat) (cs : List Nat) (m : GMach) :
    chargeEach (c :: cs) m = chargeEach cs ((GInstr.charge c "").denote m) := rfl

/-- Once halted with an empty pool, nothing further changes. -/
theorem chargeEach_oog (cs : List Nat) : chargeEach cs oog = oog := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [chargeEach_cons]
    by_cases h : c ≤ (0 : Nat)
    · have : c = 0 := Nat.le_zero.mp h
      simp [GInstr.denote, oog, this] at *
      exact ih
    · simp [GInstr.denote, oog, h]
      exact ih

/-- Enough gas for the whole list: the pool drops by the sum and nothing halts. -/
theorem chargeEach_of_le (cs : List Nat) (m : GMach) (h : cs.sum ≤ m.gas) :
    chargeEach cs m = { m with gas := m.gas - cs.sum } := by
  induction cs generalizing m with
  | nil => simp
  | cons c cs ih =>
    have hc : c ≤ m.gas := by
      have : c ≤ cs.sum + c := Nat.le_add_left _ _
      simp [List.sum_cons] at h; omega
    rw [chargeEach_cons]
    simp only [GInstr.denote, hc, ite_true]
    have h' : cs.sum ≤ m.gas - c := by simp [List.sum_cons] at h; omega
    rw [ih _ h']
    simp [List.sum_cons]
    omega

/-- Not enough for the whole list: it halts, wherever the prefix runs out. -/
theorem chargeEach_of_gt (cs : List Nat) (m : GMach) (h : m.gas < cs.sum) :
    chargeEach cs m = oog := by
  induction cs generalizing m with
  | nil => simp at h
  | cons c cs ih =>
    rw [chargeEach_cons]
    by_cases hc : c ≤ m.gas
    · simp only [GInstr.denote, hc, ite_true]
      simp only [List.sum_cons] at h
      exact ih _ (show m.gas - c < cs.sum by omega)
    · simp only [GInstr.denote, hc, ite_false]
      exact chargeEach_oog cs

/-- **The chunk head is exactly per-op charging.** One `subs` of the block's
    total gas is observationally equal to charging every op in turn — including
    when it runs out, because a straight-line block executes all of its ops. -/
theorem precharge_refines_perOp (cs : List Nat) (m : GMach) :
    (GInstr.charge cs.sum "L").denote m = chargeEach cs m := by
  by_cases h : cs.sum ≤ m.gas
  · rw [chargeEach_of_le cs m h]; simp [GInstr.denote, h]
  · rw [chargeEach_of_gt cs m (by omega)]; simp [GInstr.denote, h]

/-! ## The hand-back pair -/

/-- With nothing in between, hand-back then re-take is the identity. -/
theorem handBack_retake_id (rem : Nat) (m : GMach) :
    (GInstr.retake rem "L").denote ((GInstr.handBack rem).denote m) = m := by
  simp [GInstr.denote]

/-- **The theorem the bug violated.** A handler that reads gas runs against the
    COMPENSATED pool and charges `c` against it; taking `rem` back afterwards
    must leave exactly what charging `c` from the uncompensated pool would.

    The interesting case is `m.gas < c ≤ m.gas + rem`: the handler's own check
    passes (it sees `gas + rem`), so the halt can only come from the re-take —
    which is why that subtraction has to be checked. -/
theorem compensation_refines (rem c : Nat) (m : GMach) :
    (GInstr.retake rem "Lr").denote
        ((GInstr.charge c "Lc").denote ((GInstr.handBack rem).denote m))
      = (GInstr.charge c "Lc").denote m := by
  by_cases hc : c ≤ m.gas
  · have h1 : c ≤ m.gas + rem := by omega
    have h2 : rem ≤ m.gas + rem - c := by omega
    simp [GInstr.denote, hc, h1, h2]
    omega
  · by_cases h1 : c ≤ m.gas + rem
    · have h2 : ¬ (rem ≤ m.gas + rem - c) := by omega
      simp [GInstr.denote, hc, h1, h2]
    · by_cases hr : rem ≤ (0 : Nat)
      · have : rem = 0 := Nat.le_zero.mp hr
        simp [GInstr.denote, oog, hc, this]
      · simp [GInstr.denote, oog, hc, h1, hr]

/-- **And the bug is real.** With a bare `sub` the pair is NOT transparent: the
    numbers are the shape of Arc 12 881 017 tx 24 — a chunk entered with little
    gas, two SSTOREs, a 100-gas charge that the compensated pool could absorb.
    The checked form halts; the unchecked one wraps the u64 register to just
    under 2^64 and the frame runs on.

    `2^63 ≤ gas` is exactly the condition `run-jit-frame` now checks at the
    seam, so the runtime guard and this theorem are watching for the same
    thing. -/
theorem compensation_unchecked_is_wrong :
    ∃ (rem c : Nat) (m : GMach),
      retakeUnchecked rem ((GInstr.charge c "Lc").denote ((GInstr.handBack rem).denote m))
        ≠ (GInstr.charge c "Lc").denote m := by
  refine ⟨1000, 100, { gas := 23, halted := false }, ?_⟩
  native_decide

/-- Spelled out: the wrapped pool is astronomically large and not halted. -/
example :
    (retakeUnchecked 1000
      ((GInstr.charge 100 "Lc").denote ((GInstr.handBack 1000).denote { gas := 23, halted := false })))
      = { gas := 18446744073709551539, halted := false } := by native_decide
/-- …which is above 2^63, i.e. what the seam's guard rejects. -/
example : 9223372036854775808 ≤
    (retakeUnchecked 1000
      ((GInstr.charge 100 "Lc").denote
        ((GInstr.handBack 1000).denote { gas := 23, halted := false }))).gas := by native_decide
/-- The checked form halts on the same inputs. -/
example :
    (GInstr.retake 1000 "Lr").denote
      ((GInstr.charge 100 "Lc").denote ((GInstr.handBack 1000).denote { gas := 23, halted := false }))
      = oog := by native_decide

/-! ## Why the hand-back cannot itself overflow

`handBack` adds to the gas register, and the model is ℕ. In the machine it is a
u64, so transparency also needs `gas + rem < 2^64`. That holds structurally:
`rem` is a sub-sum of the chunk's static gas, `gas` is bounded by the block gas
limit at frame entry, and both are far below 2^63. Stated as a lemma so the
assumption is visible rather than implicit. -/
theorem handBack_no_overflow (rem : Nat) (m : GMach)
    (hg : m.gas < 2 ^ 32) (hr : rem < 2 ^ 32) :
    ((GInstr.handBack rem).denote m).gas < W := by
  simp only [GInstr.denote, W]
  omega

end Evm.CL.ARM64.ChunkGas
