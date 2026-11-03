/-
  Evm.Frontier.Vm.Runtime — code-level helpers (jumpdest analysis).

  EELS reference: ethereum/frontier/vm/runtime.py. Walks the code linearly,
  treating PUSH1..PUSH32 immediates as data so that 0x5b bytes inside them
  do not register as JUMPDESTs.
-/

import Evm.BaseTypes

namespace Evm.Frontier.Vm.Runtime

/-- The set of program-counter positions in `code` that are valid jump
    destinations (i.e. the position of a `JUMPDEST` opcode 0x5b that is
    not located inside a PUSH immediate). -/
partial def validJumpDests (code : Evm.Bytes) : List Nat := Id.run do
  let mut out : List Nat := []
  let mut pc : Nat := 0
  while pc < code.size do
    let op := code.get! pc
    if op = 0x5b then
      out := out ++ [pc]
      pc := pc + 1
    else if op ≥ 0x60 ∧ op ≤ 0x7f then
      -- PUSH1..PUSH32 — skip the immediate.
      let n := (op.toNat - 0x60) + 1
      pc := pc + 1 + n
    else
      pc := pc + 1
  pure out

/-- O(1)-lookup bitmap form of `validJumpDests`: byte `i` is `1` iff
    `i` is a valid JUMPDEST position. Build once per frame and consult
    via `bitmapHas` for jump validation. -/
partial def jumpDestBitmap (code : Evm.Bytes) : Evm.Bytes := Id.run do
  let mut out : Evm.Bytes := ByteArray.mk (Array.replicate code.size (0 : UInt8))
  let mut pc : Nat := 0
  while pc < code.size do
    let op := code.get! pc
    if op = 0x5b then
      out := out.set! pc 1
      pc := pc + 1
    else if op ≥ 0x60 ∧ op ≤ 0x7f then
      let n := (op.toNat - 0x60) + 1
      pc := pc + 1 + n
    else
      pc := pc + 1
  pure out

/-- O(1) bitmap query. -/
def bitmapHas (bm : Evm.Bytes) (pos : Nat) : Bool :=
  pos < bm.size ∧ bm.get! pos = (1 : UInt8)

/-- Slow path retained for callers that still pass raw code. Prefer
    `bitmapHas` against a precomputed `jumpDestBitmap` from
    `Evm.jumpDests`. -/
def isJumpDest (code : Evm.Bytes) (pos : Nat) : Bool :=
  (validJumpDests code).contains pos

end Evm.Frontier.Vm.Runtime
