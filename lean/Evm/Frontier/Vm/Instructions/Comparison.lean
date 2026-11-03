/-
  Evm.Frontier.Vm.Instructions.Comparison — opcodes 0x10..0x15.

  EELS reference: ethereum/frontier/vm/instructions/comparison.py.

  All comparison opcodes cost `GAS_VERY_LOW` (3) and push `1` for true /
  `0` for false. `LT`/`GT` are unsigned; `SLT`/`SGT` are signed (two's
  complement).
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions

namespace Evm.Frontier.Vm.Instructions

open Evm.Frontier.Vm

/- The boolean-result lambdas below are written in the same if-form
   as the spec's `IsLtStep`/… abbrevs (Evm.Frontier.Spec.Step), so
   the refinement `*_complete` lemmas hold definitionally. -/

/-- 0x10 LT (unsigned) -/
def lt : Handler := runBinary Gas.veryLow fun a b => if a < b then 1 else 0

/-- 0x11 GT (unsigned) -/
def gt : Handler := runBinary Gas.veryLow fun a b => if a > b then 1 else 0

/-- 0x12 SLT (signed) -/
def slt : Handler := runBinary Gas.veryLow fun a b => if BitVec.slt a b then 1 else 0

/-- 0x13 SGT (signed) -/
def sgt : Handler := runBinary Gas.veryLow fun a b => if BitVec.slt b a then 1 else 0

/-- 0x14 EQ -/
def eq : Handler := runBinary Gas.veryLow fun a b => if a = b then 1 else 0

/-- 0x15 ISZERO -/
def iszero : Handler := runUnary Gas.veryLow fun a => if a = 0 then 1 else 0

end Evm.Frontier.Vm.Instructions
