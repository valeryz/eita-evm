import Evm.CL.WordOps

/-! # CL/LimbC — the native storage path's limb primitives, defined once, proved, emitted to C

The native SLOAD/SSTORE path (docs/native-storage.md) moves and compares 256-bit values as four
64-bit limbs, least significant first (`Evm.CL.WordOps.Limbs`). Its primitives are written here
as a small deep embedding — limb expressions `L`, conditions `B`, limb assignments `A` — with a
meaning (`eval`, `exec`) and a C printer (`toC`). Each primitive is proved equal to its 256-bit
operation, through `WordOps` (`eq_ofBV`, `isZero_ofBV`); `lake exe emitLimbC` prints
`c/generated/limb_ops.h` from the same terms, and `scripts/verify-host-emit.sh` checks the
committed file for drift. So the C is what the theorems are about, not a transcription.

| C (`c/generated/limb_ops.h`) | term | theorem |
|---|---|---|
| `limb_eq(a, b)` | `eqB` | `eqB_spec`: `a = b` |
| `limb_is_zero(a)` | `isZeroB` | `isZeroB_spec`: `a = 0` |
| `limb_copy(d, a)` | `copyA` | `copyA_spec`: `d := a` |
| `limb_zero(d)` | `zeroA` | `zeroA_spec`: `d := 0` |
-/

namespace Evm.CL.LimbC

open Evm.CL.WordOps

/-- A limb: of the input word `a` or `b` (C: `a[i]`, `b[i]`), zero, or an OR of two. -/
inductive L where
  | a (i : Fin 4)
  | b (i : Fin 4)
  | zero
  | or (x y : L)

/-- A condition on limbs (C: an `int`, 1 or 0). -/
inductive B where
  | eq (x y : L)
  | isZero (x : L)
  | and (p q : B)

def limb (w : Limbs) : Fin 4 → BitVec 64
  | 0 => w.l0 | 1 => w.l1 | 2 => w.l2 | 3 => w.l3

def L.eval (x y : Limbs) : L → BitVec 64
  | .a i => limb x i
  | .b i => limb y i
  | .zero => 0
  | .or p q => p.eval x y ||| q.eval x y

def B.eval (x y : Limbs) : B → Bool
  | .eq p q => p.eval x y == q.eval x y
  | .isZero p => p.eval x y == 0
  | .and p q => p.eval x y && q.eval x y

/-- An assignment of the four result limbs (C: `d[0] = …; … d[3] = …;`). -/
structure A where
  r0 : L
  r1 : L
  r2 : L
  r3 : L

def A.exec (x y : Limbs) (s : A) : Limbs := ⟨s.r0.eval x y, s.r1.eval x y, s.r2.eval x y, s.r3.eval x y⟩

/-! ## The primitives -/

def eqB : B :=
  .and (.and (.and (.eq (.a 0) (.b 0)) (.eq (.a 1) (.b 1))) (.eq (.a 2) (.b 2))) (.eq (.a 3) (.b 3))

def isZeroB : B := .isZero (.or (.or (.or (.a 0) (.a 1)) (.a 2)) (.a 3))

def copyA : A := ⟨.a 0, .a 1, .a 2, .a 3⟩

def zeroA : A := ⟨.zero, .zero, .zero, .zero⟩

/-! ## Each is its 256-bit operation -/

theorem eqB_eval (x y : Limbs) : eqB.eval x y = WordOps.eq x y := by
  simp [eqB, B.eval, L.eval, limb, WordOps.eq, Bool.and_assoc]

theorem eqB_spec (x y : BitVec 256) : eqB.eval (Limbs.ofBV x) (Limbs.ofBV y) = decide (x = y) := by
  rw [eqB_eval, eq_ofBV]

theorem isZeroB_eval (x y : Limbs) : isZeroB.eval x y = WordOps.isZero x := by
  simp [isZeroB, B.eval, L.eval, limb, WordOps.isZero]

theorem isZeroB_spec (x y : BitVec 256) : isZeroB.eval (Limbs.ofBV x) (Limbs.ofBV y) = decide (x = 0) := by
  rw [isZeroB_eval, isZero_ofBV]

theorem copyA_spec (x y : BitVec 256) : (copyA.exec (Limbs.ofBV x) (Limbs.ofBV y)).toBV = x := by
  have : copyA.exec (Limbs.ofBV x) (Limbs.ofBV y) = Limbs.ofBV x := by
    simp [copyA, A.exec, L.eval, limb]
  rw [this, toBV_ofBV]

theorem zeroA_spec (x y : BitVec 256) : (zeroA.exec (Limbs.ofBV x) (Limbs.ofBV y)).toBV = 0 := by
  simp only [zeroA, A.exec, L.eval, Limbs.toBV]; bv_decide

/-! ## The C printer -/

def L.toC : L → String
  | .a i => s!"a[{i.val}]"
  | .b i => s!"b[{i.val}]"
  | .zero => "0"
  | .or p q => s!"({p.toC} | {q.toC})"

def B.toC : B → String
  | .eq p q => s!"({p.toC} == {q.toC})"
  | .isZero p => s!"({p.toC} == 0)"
  | .and p q => s!"({p.toC} & {q.toC})"

def A.toC (s : A) : String :=
  s!"d[0] = {s.r0.toC}; d[1] = {s.r1.toC}; d[2] = {s.r2.toC}; d[3] = {s.r3.toC};"

/-- `c/generated/limb_ops.h`. -/
def header : String :=
  "/* c/generated/limb_ops.h — EMITTED by `lake exe emitLimbC` from lean/Evm/CL/LimbC.lean; do not edit.\n" ++
  "   Each function is the C printing of a term proved equal to its 256-bit operation there\n" ++
  "   (eqB_spec, isZeroB_spec, copyA_spec, zeroA_spec). Limbs: four uint64_t, least significant first. */\n" ++
  "#ifndef EITA_LIMB_OPS_H\n#define EITA_LIMB_OPS_H\n#include <stdint.h>\n\n" ++
  s!"static inline int limb_eq(const uint64_t *a, const uint64_t *b) \{ return {eqB.toC}; }\n" ++
  s!"static inline int limb_is_zero(const uint64_t *a) \{ return {isZeroB.toC}; }\n" ++
  s!"static inline void limb_copy(uint64_t *d, const uint64_t *a) \{ {copyA.toC} }\n" ++
  s!"static inline void limb_zero(uint64_t *d) \{ {zeroA.toC} }\n" ++
  "#endif\n"

end Evm.CL.LimbC
