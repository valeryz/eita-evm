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
  `Evm.Frontier.Spec.StepShapes`, with `op = clzU256` stated through
  `Nat.size` (Python's `bit_length`). The implementation
  (`Evm.Osaka.Vm.Effect.clzU256`, a shift loop) is proved equal in
  `Evm.Osaka.Spec.Refinement.clzU256_eq`.
-/

import Evm.Frontier.Spec.StepShapes
import Mathlib.Data.Nat.Size

namespace Evm.Osaka.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (IsUnaryStep)

/-- Count leading zero bits in a 256-bit word: `256 - bit_length(x)`, with
    `bit_length` Python's `int.bit_length` — the least `k` with `x < 2^k`, i.e.
    Mathlib's `Nat.size`. EELS `forks/osaka/vm/instructions/bitwise.py::
    count_leading_zeros` 268-269 (`bit_length = U256(x.bit_length())`;
    `result = U256(256) - bit_length`). Restated 2026-11-09: this used to be the
    implementation's own shift loop (`Evm.Osaka.Vm.Effect.clzU256`), so the
    refinement was circular. -/
def clzU256 (x : Evm.U256) : Evm.U256 := Evm.U256.ofNat (256 - Nat.size x.toNat)

/-- 0x1E CLZ. EELS `count_leading_zeros`; gas tier LOW. -/
abbrev IsClzStep : Evm → Evm → Prop :=
  IsUnaryStep clzU256 Gas.low

end Evm.Osaka.Spec
