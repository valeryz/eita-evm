/-
  Evm.Frontier.Vm.Instructions.ControlFlow — opcodes 0x00, 0x56, 0x57,
  0x58, 0x5a, 0x5b.

  EELS reference: ethereum/frontier/vm/instructions/control_flow.py.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Runtime
import Evm.Frontier.Vm.Instructions

namespace Evm.Frontier.Vm.Instructions

open Evm.Frontier.Vm

/-- 0x00 STOP: halt the current frame with no output. -/
def stop : Handler := fun evm =>
  return { evm with halted := true }

/-- O(1) jump-validity check: prefer the cached `evm.jumpDests`
    bitmap (populated by `Evm.fresh`); fall back to a linear scan
    for legacy code paths that construct an `Evm` without populating
    the cache.

    Public because the IR terminator semantics (`IR.execTerm`) and
    the spec relations (`IsJumpStep` / `IsJumpiStep`) reference this
    exact check, so handler/IR/spec agreement on jump validity is
    definitional. Bitmap-vs-scan agreement (`jumpDestBitmap` vs
    `validJumpDests`) is a separate, currently-unproven obligation;
    all three layers share whichever answer this function gives. -/
def isValidJumpDest (evm : Evm) (pos : Nat) : Bool :=
  if evm.jumpDests.size = 0
  then Runtime.isJumpDest evm.message.code pos
  else Runtime.bitmapHas evm.jumpDests pos

/-- 0x56 JUMP: pop a destination; transfer control if it is a JUMPDEST. -/
def jump : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.mid
  let (dest, s) ← Stack.pop evm.stack
  let destN := dest.toNat
  if isValidJumpDest evm destN then
    return { evm with gasLeft := gasLeft, stack := s, pc := destN }
  else
    .error .invalidJumpDest

/-- 0x57 JUMPI: pop dest then condition; jump iff condition ≠ 0. -/
def jumpi : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.high
  let (dest, cond, s) ← Stack.pop2 evm.stack
  if cond = (0 : Evm.U256) then
    return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }
  else
    let destN := dest.toNat
    if isValidJumpDest evm destN then
      return { evm with gasLeft := gasLeft, stack := s, pc := destN }
    else
      .error .invalidJumpDest

/-- 0x58 PC -/
def pc : Handler :=
  runNullaryPush Gas.base (fun evm => Evm.U256.ofNat evm.pc)

/-- 0x5a GAS: push the gas remaining *after* this instruction's own
    `GAS_BASE` charge. The value lambda reads the pre-charge frame, so
    it subtracts the charge itself; when the charge succeeds this is
    exactly the post-charge `gasLeft`. -/
def gas : Handler :=
  runNullaryPush Gas.base (fun evm => Evm.U256.ofNat (evm.gasLeft - Gas.base))

/-- 0x5b JUMPDEST: no-op (only its existence at this position matters). -/
def jumpdest : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.jumpDest
  return { evm with gasLeft := gasLeft, pc := evm.pc + 1 }

end Evm.Frontier.Vm.Instructions
