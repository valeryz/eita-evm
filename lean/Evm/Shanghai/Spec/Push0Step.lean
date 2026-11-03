/-
  Evm.Shanghai.Spec.Push0Step — EIP-3855 PUSH0 step relation.

  EELS reference: `forks/shanghai/vm/instructions/stack.py` `push0`
  (gas in `forks/shanghai/vm/gas.py` constant `BASE = 2`).

  PUSH0 (0x5f) is the simplest opcode in the EVM: it pushes the
  constant `0` onto the stack, charges `BASE = 2` gas, and advances
  `pc` by one. It is structurally a `IsNullaryPushStep` over the
  constant-zero value extractor — i.e. exactly the "push something
  derived from the frame" shape, just with a frame-independent value.

  Implementation reference: `Evm.Shanghai.Vm.Effect.doPush0`.

  Inheritance: PUSH0 is introduced at Shanghai and unchanged at
  Cancun / Prague / later forks — they all import this file directly.
-/

import Evm.Frontier.Spec.StepShapes

namespace Evm.Shanghai.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (IsNullaryPushStep)

/-- 0x5f PUSH0. Charges `Gas.base = 2`, pushes a literal `0 : U256`,
    advances pc by 1. Stack depth bound is the usual `< 1024`.

    Note we cast through `IsNullaryPushStep` with a constant value
    extractor `fun _ => 0`. The result is identical to a hand-written
    `∃ rest, … ∧ evm' = { stack := 0 :: evm.stack, … }` but reuses the
    well-tested shape lemma. -/
abbrev IsPush0Step : Evm → Evm → Prop :=
  IsNullaryPushStep (fun _ => (0 : Evm.U256)) Gas.base

end Evm.Shanghai.Spec
