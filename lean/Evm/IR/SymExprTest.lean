/-
  Evm.IR.SymExprTest — sanity checks for `Expr.eval`.

  These tests hand-construct the symbolic exit stack of the
  `FullMath.mulDiv` entry chunk and evaluate it on concrete
  `(a, b, denom)` inputs, comparing against a direct Lean
  implementation of the same arithmetic.

  This is the seed of the differential test harness. Once we
  have a Lean port of the symbolic compiler, we'll feed it
  `muldiv.bin` and compare the auto-generated Expr against
  the bytecode interpreter.
-/

import Evm.IR.SymExpr

namespace Evm.IR.SymExpr.Test

open Evm Evm.IR.SymExpr

/-- Build `prod1 = (mm - prod0) - (mm < prod0)` symbolically,
    in exactly the shape the CL interpreter produces for the
    entry chunk of mulDiv. Stack convention at chunk entry:
    `stackAt 0 = denom, stackAt 1 = b, stackAt 2 = a`. -/
def prod1Expr : Expr :=
  let a    := Expr.stackAt 2
  let b    := Expr.stackAt 1
  let mask : U256 := U256.ofNat ((1 <<< 256) - 1)  -- 2^256 - 1
  let mm   := Expr.mulmod b a (Expr.const mask)
  let p0   := Expr.mul b a
  Expr.sub (Expr.sub mm p0) (Expr.lt mm p0)

/-- Direct Lean reference: prod1 from the Solidity algorithm. -/
def prod1Ref (a b : U256) : U256 :=
  let mask : U256 := U256.ofNat ((1 <<< 256) - 1)
  let mm := U256.ofNat ((b.toNat * a.toNat) % mask.toNat)
  let p0 := b * a
  (mm - p0) - (if mm < p0 then 1 else 0)

/-- Run the symbolic eval and the direct reference; assert equality. -/
def testProd1 (a b denom : U256) : IO Unit := do
  let es : List U256 := [denom, b, a]
  let sym := eval prod1Expr es
  let ref := prod1Ref a b
  if sym = ref then
    IO.println s!"  prod1 OK: a={a.toNat}, b={b.toNat} -> {sym.toNat}"
  else
    IO.eprintln s!"  prod1 MISMATCH: sym={sym.toNat}, ref={ref.toNat}"

/-- prod0 = a * b (with overflow wrapped to U256). Symbolic shape. -/
def prod0Expr : Expr :=
  Expr.mul (Expr.stackAt 1) (Expr.stackAt 2)

def testProd0 (a b denom : U256) : IO Unit := do
  let es : List U256 := [denom, b, a]
  let sym := eval prod0Expr es
  let ref := b * a
  if sym = ref then
    IO.println s!"  prod0 OK: {sym.toNat}"
  else
    IO.eprintln s!"  prod0 MISMATCH: sym={sym.toNat}, ref={ref.toNat}"

/-- Suite of inputs covering: small values, overflow, prod1=0 case. -/
def main : IO Unit := do
  let cases : List (U256 × U256 × U256) :=
    [ (10, 20, 7)                                  -- small, prod1 = 0
    , (100, 200, 13)
    , (U256.ofNat (1 <<< 200), U256.ofNat (1 <<< 200), 1) -- overflow case
    , (0, 12345, 99)                                -- a = 0
    , (1, 1, 0)                                     -- denom = 0 (revert case)
    ]
  IO.println "=== SymExpr.eval differential tests ==="
  for (a, b, denom) in cases do
    IO.println s!"input: a={a.toNat}, b={b.toNat}, denom={denom.toNat}"
    testProd0 a b denom
    testProd1 a b denom

end Evm.IR.SymExpr.Test
