/-
  Evm.Frontier.Vm.Stack — operand stack.

  EELS reference: ethereum/frontier/vm/stack.py. The 1024-item limit is
  fork-invariant; the data structure is duplicated per fork only because
  EELS chooses to keep each fork self-contained.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions

namespace Evm.Frontier.Vm

def stackLimit : Nat := 1024

/-- Operand stack. Top of stack is the head of the list. -/
abbrev Stack : Type := List Evm.U256

namespace Stack

def empty : Stack := []

def push (s : Stack) (x : Evm.U256) : Except Exception Stack :=
  if s.length ≥ stackLimit then .error .stackOverflow
  else .ok (x :: s)

def pop : Stack → Except Exception (Evm.U256 × Stack)
  | []      => .error .stackUnderflow
  | x :: xs => .ok (x, xs)

/-- Pop two items, returning `(top, second-from-top, rest)`. -/
def pop2 (s : Stack) : Except Exception (Evm.U256 × Evm.U256 × Stack) := do
  let (a, s) ← pop s
  let (b, s) ← pop s
  return (a, b, s)

/-- Pop three items. -/
def pop3 (s : Stack) : Except Exception (Evm.U256 × Evm.U256 × Evm.U256 × Stack) := do
  let (a, s) ← pop s
  let (b, s) ← pop s
  let (c, s) ← pop s
  return (a, b, c, s)

/-- Peek at depth `n` (0 = top). -/
def peek (s : Stack) (n : Nat) : Except Exception Evm.U256 :=
  match s[n]? with
  | some v => .ok v
  | none   => .error .stackUnderflow

/-- Replace the item at depth `n` (0 = top). Underflow if missing. -/
def setAt (s : Stack) (n : Nat) (v : Evm.U256) : Except Exception Stack :=
  if n < s.length then .ok (s.set n v)
  else .error .stackUnderflow

/-- DUP-n: duplicate the item at depth `n-1` (so DUP1 duplicates the top). -/
def dup (s : Stack) (n : Nat) : Except Exception Stack := do
  let v ← peek s (n - 1)
  push s v

/-- SWAP-n: swap the top with the item at depth `n`. -/
def swap (s : Stack) (n : Nat) : Except Exception Stack := do
  match s with
  | [] => .error .stackUnderflow
  | top :: rest =>
    match rest[n - 1]? with
    | some other => .ok (other :: rest.set (n - 1) top)
    | none       => .error .stackUnderflow

end Stack

end Evm.Frontier.Vm
