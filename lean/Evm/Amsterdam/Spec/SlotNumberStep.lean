/-
  Evm.Amsterdam.Spec.SlotNumberStep — EIP-7732 SLOTNUM (0x4B).

  EELS reference:
    * `forks/amsterdam/vm/instructions/block.py::slot_number` (lines
      ~120-150). The opcode pushes `evm.message.block_env.slot_number`,
      a `U64` plumbed from `Header.slot_number` via the
      `BlockEnvironment` constructed in
      `forks/amsterdam/fork.py::execute_block`.
    * Gas: `OPCODE_SLOTNUM = BASE` (= 2) in
      `forks/amsterdam/vm/gas.py`.

  Per the SPEC-METHODOLOGY: an environment-lookup opcode of the
  PREVRANDAO / TIMESTAMP family. Uses the `IsNullaryPushStep` shape
  with the value-extractor `env → env.slotNumber`.

  Plumbing: `Frontier.Vm.Environment.slotNumber` (Nat). Default 0;
  the Amsterdam fork driver populates it from
  `Header.slot_number`. Pre-Amsterdam interpreters never read it, so
  the field is invisible there.
-/

import Evm.Frontier.Spec.StepShapes

namespace Evm.Amsterdam.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (IsNullaryPushStep)

/-- 0x4B SLOTNUM. Pushes `env.slotNumber`. Gas BASE (=2). -/
abbrev IsSlotNumberStep : Evm → Evm → Prop :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.env.slotNumber) Gas.base

end Evm.Amsterdam.Spec
