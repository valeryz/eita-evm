import Slots.Mem
import Slots.CPrint
/-! The printer's rejections (run: `lake env lean PrinterNeg.lean`; each `#emit_c` must fail
with the message shown). -/

method bang (a : Array UInt64) (i : Nat) returns (r : UInt64)
  requires i < a.size
  ensures True
do
  return a[i]!
prove_correct bang by velvet_vcgen [bang] with finish

method bangSet (a : Array UInt64) (i : Nat) returns (r : Array UInt64)
  requires i < a.size
  ensures True
do
  return a.set! i 0
prove_correct bangSet by velvet_vcgen [bangSet] with finish

method oobAllowed (a : Array UInt64) (i : Nat) returns (r : UInt64)
  requires i < a.size
  signals True
  ensures True
do
  let x ← rd a i
  return x
prove_correct oobAllowed by velvet_vcgen [oobAllowed] with finish

method useAfterSet (a : Array UInt64) returns (r : Array UInt64 × UInt64)
  requires 1 < a.size
  ensures True
do
  let b ← wr a 0 7
  let x ← rd a 1
  return (b, x)
prove_correct useAfterSet by velvet_vcgen [useAfterSet] with finish

/-- error: C printer: `a[i]!` is not accepted (unchecked index); use `a[i]'h` under `if h : i < a.size` (Slots/Mem.lean `rd`) -/
#guard_msgs in #emit_c "/dev/null" [bang]
/-- error: C printer: `a.set! i v` is not accepted (unchecked index); use `a.set i v h` (Slots/Mem.lean `wr`) -/
#guard_msgs in #emit_c "/dev/null" [bangSet]
/-- error: C printer: an `oob` bound check in a method whose contract allows failure (the else branch is not proved dead) -/
#guard_msgs in #emit_c "/dev/null" [oobAllowed]
/-- error: C printer: array a used after it was consumed (not linear) -/
#guard_msgs in #emit_c "/dev/null" [useAfterSet]
