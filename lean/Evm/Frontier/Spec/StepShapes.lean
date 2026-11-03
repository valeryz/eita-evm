/-
  Evm.Frontier.Spec.StepShapes — parametric step-relation shapes
  for the simple opcode families.

  Goal: collapse the dozens of nearly-identical `IsXxxStep`
  structures (one per arithmetic / bitwise / comparison opcode)
  into a single parametric `def` per stack-arity. Each opcode then
  declares itself via a one-liner:

      abbrev IsAddStep := IsBinaryStep (· + ·) Gas.veryLow
      abbrev IsMulStep := IsBinaryStep (· * ·) Gas.low
      ...

  The body of each shape is *property-flavored* — preconditions on
  the input frame, an equational post-condition on `evm'`. The
  equation `evm' = { evm with ... }` simultaneously specifies all
  post-state fields AND all the frame conditions (anything not
  mentioned in the `with` is copied verbatim).

  Three shapes cover ~95% of pure-stack opcodes:
    - `IsUnaryStep   op gas` — pops 1, pushes 1
    - `IsBinaryStep  op gas` — pops 2, pushes 1
    - `IsTernaryStep op gas` — pops 3, pushes 1

  Stack-only operations (PUSH-N, POP, DUP-n, SWAP-n) and
  control-flow (JUMP, JUMPI, PC) have their own shapes since their
  effect on the stack and pc is non-uniform.
-/

import Evm.Frontier.Vm
import Evm.Frontier.Vm.Exceptions

namespace Evm.Frontier.Spec

open Evm.Frontier.Vm

/-! ## Unary, binary, ternary pure-stack ops

    These cover ADD, MUL, SUB, DIV, SDIV, MOD, SMOD, EXP, SIGNEXTEND,
    LT, GT, SLT, SGT, EQ, ISZERO, AND, OR, XOR, NOT, BYTE, ADDMOD,
    MULMOD, KECCAK256 (last reads memory, so it's NOT a pure-stack
    op — keep it separate). -/

/-- Pop 1, apply `op`, push result. Charge `gas`. Advance pc by 1.
    Everything else (memory, env, halted, …) unchanged. -/
def IsUnaryStep (op : Evm.U256 → Evm.U256) (gas : Gas.Gas)
                (evm evm' : Evm) : Prop :=
  ∃ a rest,
    evm.stack = a :: rest ∧
    rest.length < stackLimit ∧
    evm.gasLeft ≥ gas ∧
    evm' = { evm with
      stack   := (op a) :: rest,
      gasLeft := evm.gasLeft - gas,
      pc      := evm.pc + 1 }

/-- Pop 2, apply `op`, push result. Charge `gas`. Advance pc by 1. -/
def IsBinaryStep (op : Evm.U256 → Evm.U256 → Evm.U256) (gas : Gas.Gas)
                 (evm evm' : Evm) : Prop :=
  ∃ a b rest,
    evm.stack = a :: b :: rest ∧
    rest.length < stackLimit ∧
    evm.gasLeft ≥ gas ∧
    evm' = { evm with
      stack   := (op a b) :: rest,
      gasLeft := evm.gasLeft - gas,
      pc      := evm.pc + 1 }

/-- Pop 3, apply `op`, push result. Charge `gas`. Advance pc by 1. -/
def IsTernaryStep (op : Evm.U256 → Evm.U256 → Evm.U256 → Evm.U256)
                  (gas : Gas.Gas) (evm evm' : Evm) : Prop :=
  ∃ a b c rest,
    evm.stack = a :: b :: c :: rest ∧
    rest.length < stackLimit ∧
    evm.gasLeft ≥ gas ∧
    evm' = { evm with
      stack   := (op a b c) :: rest,
      gasLeft := evm.gasLeft - gas,
      pc      := evm.pc + 1 }

/-! ## Stack-shape ops

    POP, DUP-n, SWAP-n have non-uniform stack effects so they get
    their own shapes. Same property-flavored equational form. -/

/-- POP — discard top. -/
def IsPopStep (gas : Gas.Gas) (evm evm' : Evm) : Prop :=
  ∃ a rest,
    evm.stack = a :: rest ∧
    evm.gasLeft ≥ gas ∧
    evm' = { evm with
      stack   := rest,
      gasLeft := evm.gasLeft - gas,
      pc      := evm.pc + 1 }

/-- DUP-n: duplicate the item at depth `n-1` (so DUP1 duplicates
    the top). Need stack to have at least `n` elements; new stack
    has length one greater. -/
def IsDupStep (n : Nat) (gas : Gas.Gas) (evm evm' : Evm) : Prop :=
  ∃ v,
    n > 0 ∧
    n ≤ 16 ∧
    evm.stack[n - 1]? = some v ∧
    evm.stack.length < stackLimit ∧
    evm.gasLeft ≥ gas ∧
    evm' = { evm with
      stack   := v :: evm.stack,
      gasLeft := evm.gasLeft - gas,
      pc      := evm.pc + 1 }

/-- SWAP-n: swap the top with the item at depth `n`. Length
    unchanged. -/
def IsSwapStep (n : Nat) (gas : Gas.Gas) (evm evm' : Evm) : Prop :=
  ∃ top other rest,
    evm.stack = top :: rest ∧
    rest[n - 1]? = some other ∧
    evm.gasLeft ≥ gas ∧
    evm' = { evm with
      stack   := other :: rest.set (n - 1) top,
      gasLeft := evm.gasLeft - gas,
      pc      := evm.pc + 1 }

/-! ## Constant / environment lookups

    ADDRESS, ORIGIN, CALLER, CALLVALUE, CALLDATASIZE, CODESIZE,
    GASPRICE, COINBASE, TIMESTAMP, NUMBER, DIFFICULTY, GASLIMIT,
    PC, MSIZE, GAS — all push one value derived from the current
    frame. The value-extraction function abstracts the difference
    between them. -/

/-- Push a value derived from the current frame; no stack input. -/
def IsNullaryPushStep (value : Evm → Evm.U256) (gas : Gas.Gas)
                      (evm evm' : Evm) : Prop :=
  evm.stack.length < stackLimit ∧
  evm.gasLeft ≥ gas ∧
  evm' = { evm with
    stack   := (value evm) :: evm.stack,
    gasLeft := evm.gasLeft - gas,
    pc      := evm.pc + 1 }

/-! ## PUSH-N (read N bytes from code, push as integer)

    Different from `IsNullaryPushStep` because the pushed value
    depends on `evm.code[pc+1 .. pc+1+n]` (with zero-padding past
    the end of code) and pc advances by `n + 1`. -/

/-- Read the next `n` bytes after `pc` as a big-endian integer,
    zero-padding past the end of code. This is EELS `push_n`
    clause-by-clause (frontier/vm/instructions/stack.py):
    `buffer_read(evm.code, pc + 1, n)` is `sliceZeroPad`, and
    `U256.from_be_bytes` is `ofBytesBE`. -/
def pushImmediate (code : Evm.Bytes) (pc n : Nat) : Evm.U256 :=
  Evm.U256.ofBytesBE (Evm.Bytes.sliceZeroPad code (pc + 1) n)

def IsPushStep (n : Nat) (gas : Gas.Gas) (evm evm' : Evm) : Prop :=
  evm.stack.length < stackLimit ∧
  evm.gasLeft ≥ gas ∧
  evm' = { evm with
    stack   := (pushImmediate evm.message.code evm.pc n) :: evm.stack,
    gasLeft := evm.gasLeft - gas,
    pc      := evm.pc + n + 1 }

end Evm.Frontier.Spec
