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

  Decode rules (EELS `forks/amsterdam/vm/stack.py::decode_single` 25-53 /
  `decode_pair` 56-91):
    * DUPN  : `n = decode_single(imm)` (17..235; bytes 91..127 invalid).
              Duplicate the `n`-th item from the top (1-indexed).
    * SWAPN : `n = decode_single(imm)`. Swap top (position 1) with
              position `n + 1`.
    * EXCHANGE : `(n, m) = decode_pair(imm)` (bytes 82..127 invalid).
              Swap items at positions `n + 1` and `m + 1`.
  An invalid immediate is EELS `InvalidParameter`, an exceptional halt:
  no step relation holds.

  2026-11-09: these relations used the pre-index-shifting draft
  (`imm + 1`, `imm`, nibbles); corrected to EELS amsterdam (spec-fidelity
  fix, together with the implementation).

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

/-- EELS `decode_single`: invalid for 91..127, else `(x + 145) mod 256`. -/
def decodeSingle (x : Nat) : Option Nat :=
  if 90 < x ∧ x < 128 then none else some ((x + 145) % 256)

/-- EELS `decode_pair`: invalid for 82..127; else `k = x xor 143`, `q, r = divmod(k, 16)`,
    `(q + 1, r + 1)` when `q < r`, otherwise `(r + 1, 29 - q)`. -/
def decodePair (x : Nat) : Option (Nat × Nat) :=
  if 81 < x ∧ x < 128 then none
  else
    let k := x ^^^ 143
    if k / 16 < k % 16 then some (k / 16 + 1, k % 16 + 1)
    else some (k % 16 + 1, 29 - k / 16)

/-- 0xE6 DUPN. The immediate decodes to `n`; the stack has an `n`-th item
    from the top (1-indexed, `stack[n - 1]`), which is pushed; VERY_LOW; pc += 2. -/
def IsDupNStep (evm evm' : Evm) : Prop :=
  ∃ n v,
    decodeSingle (immediateByte evm.message.code evm.pc) = some n ∧
    evm.stack[n - 1]? = some v ∧
    evm.stack.length < stackLimit ∧
    evm.gasLeft ≥ Gas.veryLow ∧
    evm' = { evm with
      stack   := v :: evm.stack,
      gasLeft := evm.gasLeft - Gas.veryLow,
      pc      := evm.pc + 2 }

/-- 0xE7 SWAPN. The immediate decodes to `n`; the top swaps with position
    `n + 1` (`stack[n]`, i.e. `rest[n - 1]` below the top). -/
def IsSwapNStep (evm evm' : Evm) : Prop :=
  ∃ n top other rest,
    decodeSingle (immediateByte evm.message.code evm.pc) = some n ∧
    evm.stack = top :: rest ∧
    rest[n - 1]? = some other ∧
    evm.gasLeft ≥ Gas.veryLow ∧
    evm' = { evm with
      stack   := other :: rest.set (n - 1) top,
      gasLeft := evm.gasLeft - Gas.veryLow,
      pc      := evm.pc + 2 }

/-- 0xE8 EXCHANGE. The immediate decodes to `(n, m)`; positions `n + 1`
    and `m + 1` (indices `n`, `m`) are swapped. -/
def IsExchangeStep (evm evm' : Evm) : Prop :=
  ∃ n m vn vm,
    decodePair (immediateByte evm.message.code evm.pc) = some (n, m) ∧
    evm.stack[n]? = some vn ∧
    evm.stack[m]? = some vm ∧
    evm.gasLeft ≥ Gas.veryLow ∧
    evm' = { evm with
      stack   := (evm.stack.set n vm).set m vn,
      gasLeft := evm.gasLeft - Gas.veryLow,
      pc      := evm.pc + 2 }

end Evm.Amsterdam.Spec
