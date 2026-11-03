/-
  Evm.Osaka.Spec.ClzStep — EIP-7939 CLZ (0x1E).

  EELS reference: `forks/osaka/vm/instructions/bitwise.py`
  `count_leading_zeros` (lines ~85-115); gas constant
  `OPCODE_CLZ = LOW` in `forks/osaka/vm/gas.py` (line 196).

  Pops one U256 `x`, pushes `256 - bit_length(x)`. Equivalently: the
  number of leading zero bits in `x` interpreted as a 256-bit integer.
  Special case: `CLZ(0) = 256`.

  Gas: `Gas.low` (= 5).

  Per the SPEC-METHODOLOGY: a single new opcode introduced at Osaka;
  inherits unchanged by Amsterdam and beyond, so the relation lives
  here only.

  The relation reuses the `IsUnaryStep` shape from
  `Evm.Frontier.Spec.StepShapes`, with `op = clzU256`. The
  implementation in `Evm.Osaka.Vm.Effect.doClz` computes the same
  function (`Evm.Osaka.Vm.Effect.clzU256`); both encode the standard
  bit-length-by-shift loop.
-/

import Evm.Frontier.Spec.StepShapes
import Evm.Osaka.Vm.Effect

namespace Evm.Osaka.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (IsUnaryStep)

/-- Count leading zero bits in a 256-bit word. Lifts the loop in
    `Evm.Osaka.Vm.Effect.clzU256`. `CLZ(0) = 256` by the empty-loop
    base case (no bits set ⇒ `bit_length = 0`). -/
def clzU256 : Evm.U256 → Evm.U256 := Evm.Osaka.Vm.Effect.clzU256

/-- 0x1E CLZ. EELS `count_leading_zeros`; gas tier LOW. -/
abbrev IsClzStep : Evm → Evm → Prop :=
  IsUnaryStep clzU256 Gas.low

end Evm.Osaka.Spec
