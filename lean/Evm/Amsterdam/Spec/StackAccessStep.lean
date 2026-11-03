/-
  Evm.Amsterdam.Spec.StackAccessStep — EIP-8024 DUPN / SWAPN / EXCHANGE.

  EELS reference:
    * `forks/amsterdam/vm/instructions/stack.py::dupn`   (0xE6)
    * `forks/amsterdam/vm/instructions/stack.py::swapn`  (0xE7)
    * `forks/amsterdam/vm/instructions/stack.py::exchange` (0xE8)
    * Gas constants: `OPCODE_DUPN / OPCODE_SWAPN / OPCODE_EXCHANGE
      = VERY_LOW` in `forks/amsterdam/vm/gas.py`.
    * Dispatch addition: `forks/amsterdam/vm/instructions/__init__.py`
      lines 191-195 and 360-362.

  Each opcode reads a single immediate byte (the byte at `pc + 1`).
  The pc therefore advances by 2.

  Decode rules (EELS `decode_single` / `decode_pair`):
    * DUPN  : `item_number = imm + 1`. Duplicate item at depth
              `item_number` (= 1-indexed from top). New stack length is
              old + 1.
    * SWAPN : `n = imm`. Swap top (position 1) with position `n + 1`.
              Stack length unchanged.
    * EXCHANGE : `n = imm >> 4`, `m = imm & 0x0f`. Swap items at
              positions `n + 1` and `m + 1`. Stack length unchanged.

  Per the SPEC-METHODOLOGY: new opcodes get their own relations here;
  the implementation in `Evm/Amsterdam/Vm/Effect.lean` (`doDupN`,
  `doSwapN`, `doExchange`) is the refinement target.
-/

import Evm.Frontier.Vm

namespace Evm.Amsterdam.Spec

open Evm.Frontier.Vm

/-- Read the immediate byte following the opcode at `pc`. Out-of-code
    reads pad to zero (EELS uses `buffer_read(evm.code, U256(pc+1),
    U256(1))[0]`). -/
def immediateByte (code : Evm.Bytes) (pc : Nat) : Nat :=
  let p := pc + 1
  if p < code.size then (code.get! p).toNat else 0

/-- 0xE6 DUPN. Pre: stack has at least `imm + 1` items. Post: that
    item is duplicated on top; gas charged VERY_LOW; pc advances by 2. -/
def IsDupNStep (evm evm' : Evm) : Prop :=
  let imm := immediateByte evm.message.code evm.pc
  let n   := imm + 1
  ∃ v,
    evm.stack[n - 1]? = some v ∧
    evm.stack.length < stackLimit ∧
    evm.gasLeft ≥ Gas.veryLow ∧
    evm' = { evm with
      stack   := v :: evm.stack,
      gasLeft := evm.gasLeft - Gas.veryLow,
      pc      := evm.pc + 2 }

/-- 0xE7 SWAPN. Pre: stack has top + at least `imm` items beneath.
    Post: top swapped with position `imm + 1` (0-indexed: `rest[imm]`). -/
def IsSwapNStep (evm evm' : Evm) : Prop :=
  let imm := immediateByte evm.message.code evm.pc
  ∃ top other rest,
    evm.stack = top :: rest ∧
    rest[imm]? = some other ∧
    evm.gasLeft ≥ Gas.veryLow ∧
    evm' = { evm with
      stack   := other :: rest.set imm top,
      gasLeft := evm.gasLeft - Gas.veryLow,
      pc      := evm.pc + 2 }

/-- 0xE8 EXCHANGE. Pre: stack has at least `max(n, m) + 1` items with
    `n = imm >> 4` and `m = imm & 0x0f`. Post: items at positions
    `n + 1` and `m + 1` (0-indexed: indices `n` and `m`) are swapped. -/
def IsExchangeStep (evm evm' : Evm) : Prop :=
  let imm := immediateByte evm.message.code evm.pc
  let n   := imm >>> 4
  let m   := imm &&& 0x0f
  ∃ vn vm,
    evm.stack[n]? = some vn ∧
    evm.stack[m]? = some vm ∧
    evm.gasLeft ≥ Gas.veryLow ∧
    evm' = { evm with
      stack   := (evm.stack.set n vm).set m vn,
      gasLeft := evm.gasLeft - Gas.veryLow,
      pc      := evm.pc + 2 }

end Evm.Amsterdam.Spec
