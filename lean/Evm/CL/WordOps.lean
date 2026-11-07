import Evm.BaseTypes
import Std.Tactic.BVDecide

/-! # CL/WordOps — the host's word operations on four 64-bit limbs

The effect layer's CL (src/generated/host.lisp and the storage view) moves, stores and
compares 256-bit values as OPAQUE WORDS: four (unsigned-byte 64) limbs, least significant
first, never a Lisp integer (src/core/u256.lisp, "Opaque words"). The EffectIR printer
(`Evm.CL.EffectIR`) prints the IR's word comparisons as these operations; their meaning
in the IR (`WExp.eval`, `BExp.eval`) is on `Evm.U256` (`BitVec 256`).

Each operation is defined here limb by limb, exactly as the Lisp computes it (the same
limb order, the same carry/borrow chain, each limb step `adcCmp` / `sbbCmp` — two wrapping
operations and their compares, `adcCmp_eq` / `sbbCmp_eq`), and proved equal to the integer
operation it stands for:

| Lisp (u256.lisp) | here | theorem |
|---|---|---|
| `word=` | `eq` | `eq_ofBV`: `x = y` |
| `word-zerop` | `isZero` | `isZero_ofBV`: `x = 0` |
| `word<` | `lt` (the borrow out of `a − b`) | `lt_ofBV`: `x.toNat < y.toNat` |
| `word+!` | `add` (the carry chain) | `add_ofBV`: `x + y` mod 2^256, carry `2^256 ≤ x + y` |
| `word-!` | `sub` (the borrow chain) | `sub_ofBV`: `x − y` mod 2^256, no borrow `y ≤ x` |
| `word-set!`, `word-limbs` | `ofBV` / `toBV` | `toBV_ofBV` |

From core def68c3 (branch perf-opaque). On this branch the operations the native storage path
needs are EMITTED to C from a deep embedding of these definitions (`Evm.CL.LimbC`), not
transcribed. -/

namespace Evm.CL.WordOps

/-- A word as the host holds it: four 64-bit limbs, `l0` least significant. -/
structure Limbs where
  l0 : BitVec 64
  l1 : BitVec 64
  l2 : BitVec 64
  l3 : BitVec 64

/-- The 256-bit value of the limbs. -/
def Limbs.toBV (a : Limbs) : BitVec 256 := a.l3 ++ a.l2 ++ a.l1 ++ a.l0

/-- The limbs of a 256-bit value (what `word-limbs` reads, `word-set!` writes). -/
def Limbs.ofBV (x : BitVec 256) : Limbs :=
  ⟨x.extractLsb' 0 64, x.extractLsb' 64 64, x.extractLsb' 128 64, x.extractLsb' 192 64⟩

theorem toBV_ofBV (x : BitVec 256) : (Limbs.ofBV x).toBV = x := by
  simp only [Limbs.ofBV, Limbs.toBV]; bv_decide

/-- A limb add with carry: the 64-bit sum and the carry out (of the 65-bit sum). -/
def adc (a b : BitVec 64) (c : Bool) : BitVec 64 × Bool :=
  let s : BitVec 65 := a.zeroExtend 65 + b.zeroExtend 65 + (BitVec.ofBool c).zeroExtend 65
  (s.extractLsb' 0 64, s.msb)

/-- A limb subtract with borrow (`c` = no borrow in): `a − b − (1 − c)` mod 2^64, and
    whether it did NOT borrow. -/
def sbb (a b : BitVec 64) (c : Bool) : BitVec 64 × Bool :=
  let bin : BitVec 65 := if c then 0 else 1
  (a - b - (if c then 0 else 1), !(a.zeroExtend 65 < b.zeroExtend 65 + bin))

/-- One limb step as the Lisp computes it (`adc` in src/core/u256.lisp, portable: two wrapping
    adds and their compares — SBCL's digit primitives are not on every target). -/
def adcCmp (a b : BitVec 64) (c : Bool) : BitVec 64 × Bool :=
  let s1 := a + (if c then 1 else 0)
  let s := s1 + b
  (s, decide (s1 < a) || decide (s < s1))

/-- …and `sbb`: two wrapping subtracts and their compares (`c` = no borrow in). -/
def sbbCmp (a b : BitVec 64) (c : Bool) : BitVec 64 × Bool :=
  let bin : BitVec 64 := if c then 0 else 1
  let d1 := a - bin
  (d1 - b, !(decide (a < bin) || decide (d1 < b)))

/-- The Lisp's limb steps compute the carry and the borrow of the 65-bit operation. -/
theorem adcCmp_eq (a b : BitVec 64) (c : Bool) : adcCmp a b c = adc a b c := by
  cases c <;> simp only [adcCmp, adc, Prod.mk.injEq, BitVec.ofBool] <;> constructor <;> bv_decide

theorem sbbCmp_eq (a b : BitVec 64) (c : Bool) : sbbCmp a b c = sbb a b c := by
  cases c <;> simp only [sbbCmp, sbb, Prod.mk.injEq] <;> constructor <;> bv_decide

/-- `word=`: limb-wise equality. -/
def eq (a b : Limbs) : Bool := a.l0 == b.l0 && a.l1 == b.l1 && a.l2 == b.l2 && a.l3 == b.l3

/-- `word-zerop`: the OR of the limbs is zero. -/
def isZero (a : Limbs) : Bool := (a.l0 ||| a.l1 ||| a.l2 ||| a.l3) == 0

/-- `word-!`: the borrow chain, lowest limb first, no borrow in; the limbs and the final
    no-borrow flag. -/
def sub (a b : Limbs) : Limbs × Bool :=
  let (r0, c0) := sbb a.l0 b.l0 true
  let (r1, c1) := sbb a.l1 b.l1 c0
  let (r2, c2) := sbb a.l2 b.l2 c1
  let (r3, c3) := sbb a.l3 b.l3 c2
  (⟨r0, r1, r2, r3⟩, c3)

/-- `word<`: the chain borrowed. -/
def lt (a b : Limbs) : Bool := !(sub a b).2

/-- `word+!`: the carry chain, no carry in; the limbs and the carry out. -/
def add (a b : Limbs) : Limbs × Bool :=
  let (r0, c0) := adc a.l0 b.l0 false
  let (r1, c1) := adc a.l1 b.l1 c0
  let (r2, c2) := adc a.l2 b.l2 c1
  let (r3, c3) := adc a.l3 b.l3 c2
  (⟨r0, r1, r2, r3⟩, c3)

/-! ## Each operation is the integer operation -/

theorem eq_ofBV (x y : BitVec 256) : eq (Limbs.ofBV x) (Limbs.ofBV y) = decide (x = y) := by
  simp only [eq, Limbs.ofBV]; bv_decide

theorem isZero_ofBV (x : BitVec 256) : isZero (Limbs.ofBV x) = decide (x = 0) := by
  simp only [isZero, Limbs.ofBV]; bv_decide

theorem sub_ofBV (x y : BitVec 256) :
    (sub (Limbs.ofBV x) (Limbs.ofBV y)).1.toBV = x - y ∧
    (sub (Limbs.ofBV x) (Limbs.ofBV y)).2 = decide (y ≤ x) := by
  simp only [sub, sbb, Limbs.ofBV, Limbs.toBV]
  constructor <;> bv_decide

theorem lt_ofBV (x y : BitVec 256) : lt (Limbs.ofBV x) (Limbs.ofBV y) = decide (x.toNat < y.toNat) := by
  have h := (sub_ofBV x y).2
  simp only [lt, h]
  by_cases hxy : x.toNat < y.toNat
  · have : ¬ y ≤ x := by rw [BitVec.le_def]; omega
    simp [this, hxy]
  · have : y ≤ x := by rw [BitVec.le_def]; omega
    simp [this, hxy]

theorem add_ofBV (x y : BitVec 256) :
    (add (Limbs.ofBV x) (Limbs.ofBV y)).1.toBV = x + y ∧
    (add (Limbs.ofBV x) (Limbs.ofBV y)).2 = decide (x + y < x) := by
  simp only [add, adc, Limbs.ofBV, Limbs.toBV]
  constructor <;> bv_decide

/-- The carry out is the integer overflow: `x + y ≥ 2^256`. -/
theorem add_carry_iff (x y : BitVec 256) :
    (x + y < x) ↔ 2 ^ 256 ≤ x.toNat + y.toNat := by
  rw [BitVec.lt_def, BitVec.toNat_add]
  have hx := x.isLt; have hy := y.isLt
  generalize x.toNat = a at *; generalize y.toNat = b at *
  generalize hM : (2 : Nat) ^ 256 = M at *
  have hM0 : 0 < M := by omega
  by_cases h : M ≤ a + b
  · have : (a + b) % M = a + b - M := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [this]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-! ## The EffectIR's word comparisons, as printed

`BExp.weq` means `decide (a = b)` and prints `word=`; `BExp.pos` means `decide (w ≠ 0)`
and prints `(not (word-zerop …))`'s complement `plusp` on integers; `BExp.wlt` means
`decide (a.toNat < b.toNat)` and prints `word<`. On the limbs the host holds: -/

theorem weq_is_eq (a b : Evm.U256) : decide (a = b) = eq (Limbs.ofBV a) (Limbs.ofBV b) :=
  (eq_ofBV a b).symm

theorem pos_is_not_isZero (w : Evm.U256) : decide (w ≠ 0) = !isZero (Limbs.ofBV w) := by
  rw [isZero_ofBV]; by_cases h : w = 0 <;> simp [h]

theorem wlt_is_lt (a b : Evm.U256) :
    decide (a.toNat < b.toNat) = lt (Limbs.ofBV a) (Limbs.ofBV b) :=
  (lt_ofBV a b).symm

end Evm.CL.WordOps
