/-
  Evm.SpuriousDragon.Vm.Interpreter — EIP-161 + EIP-170 dispatcher and
  recursive handlers.

  Deltas vs Tangerine Whistle:

  * **EIP-161 "state-clearing":** account-existence becomes
    `is_dead := !exists ∨ isEmpty`. The CALL family's `NEW_ACCOUNT`
    charge gains a value gate: `value > 0 ∧ is_dead(callee)`.
    Similarly SELFDESTRUCT's `NEW_ACCOUNT` charge is gated on actual
    value transfer.
  * **EIP-170 max deployed code size:** if the bytes returned by an
    init-code (CREATE-opcode or CREATE-tx) exceed 24 576 bytes, the
    CREATE fails. (Frontier/Homestead/TW have no such limit; in
    practice they cap on the deposit gas cost instead.)
  * **EIP-160 EXP byte cost** lives in the non-recursive
    `Vm/Instructions.lean`; the dispatcher just points 0x0a at SD's
    `exp` rather than Frontier's.

  Everything else (63/64 rule, repriced base costs, mining rewards)
  carries forward from TW.
-/

import Evm.BaseTypes
import Evm.Frontier.State
import Evm.Frontier.Utils.Address
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Interpreter  -- for defaultFuel
import Evm.Frontier.Vm.Instructions
import Evm.Frontier.Vm.Instructions.Arithmetic
import Evm.Frontier.Vm.Instructions.Comparison
import Evm.Frontier.Vm.Instructions.Bitwise
import Evm.Frontier.Vm.Instructions.Stack
import Evm.Frontier.Vm.Instructions.Memory
import Evm.Frontier.Vm.Instructions.Storage
import Evm.Frontier.Vm.Instructions.ControlFlow
import Evm.Frontier.Vm.Instructions.Environment
import Evm.Frontier.Vm.Instructions.Block
import Evm.Frontier.Vm.Instructions.Keccak
import Evm.Frontier.Vm.Instructions.Log
import Evm.Frontier.Vm.Instructions.System
import Evm.Frontier.Vm.PrecompiledContracts
import Evm.TangerineWhistle.Vm.Gas
import Evm.TangerineWhistle.Vm.Instructions
import Evm.SpuriousDragon.Vm.Gas
import Evm.SpuriousDragon.Vm.Instructions

namespace Evm.SpuriousDragon.Vm

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

def maxCallDepth : Nat := 1024

private def addrToU256 (a : Evm.Address) : Evm.U256 := Evm.U256.ofNat a.toNat
private def u256ToAddr (x : Evm.U256) : Evm.Address := Evm.Address.ofNat x.toNat

/-- EIP-161 "is_dead": account is absent OR present-but-empty
    (nonce=0, balance=0, code empty). -/
private def isDead (state : Evm.Frontier.State) (addr : Evm.Address) : Bool :=
  if state.accountExists addr then (state.getAccount addr).isEmpty
  else true

private def pop7 (s : Stack) :
    Except Exception (Evm.U256 × Evm.U256 × Evm.U256 × Evm.U256 ×
                      Evm.U256 × Evm.U256 × Evm.U256 × Stack) := do
  let (a, s) ← Stack.pop s
  let (b, s) ← Stack.pop s
  let (c, s) ← Stack.pop s
  let (d, s) ← Stack.pop s
  let (e, s) ← Stack.pop s
  let (f, s) ← Stack.pop s
  let (g, s) ← Stack.pop s
  return (a, b, c, d, e, f, g, s)

private def pop6 (s : Stack) :
    Except Exception (Evm.U256 × Evm.U256 × Evm.U256 × Evm.U256 ×
                      Evm.U256 × Evm.U256 × Stack) := do
  let (a, s) ← Stack.pop s
  let (b, s) ← Stack.pop s
  let (c, s) ← Stack.pop s
  let (d, s) ← Stack.pop s
  let (e, s) ← Stack.pop s
  let (f, s) ← Stack.pop s
  return (a, b, c, d, e, f, s)

private def mergeChild (parent child : Evm) : Evm :=
  { parent with env := child.env }

/-- Add an address to the EIP-161 touched set if not already present.
    The end-of-tx sweep in `Evm.SpuriousDragon.sweepEmptyAccounts`
    deletes touched accounts that are still empty. -/
def touchAddr (env : Environment) (a : Evm.Address) : Environment :=
  if env.touched.contains a then env
  else { env with touched := env.touched ++ [a] }

private def capForward (requested available : Nat) : Nat :=
  min requested (available - available / 64)

/-- 0xff SELFDESTRUCT — EIP-150 base 5000; EIP-161 NEW_ACCOUNT gated
    on actual value transfer (balance > 0 AND beneficiary is_dead).
    Non-recursive — outside the fuel-bounded mutual block. -/
def selfdestruct : Handler := fun evm => do
  -- EIP-214 (Byzantium+): SELFDESTRUCT is forbidden in static context.
  if evm.message.isStatic then
    .error .writeInStaticContext
  let (beneficiaryW, _) ← Stack.pop evm.stack
  let beneficiary := u256ToAddr beneficiaryW
  let self        := evm.message.currentTarget
  let balance     := evm.env.state.getBalance self

  let newAccountCost : Nat :=
    if balance ≠ (0 : Evm.U256) ∧ isDead evm.env.state beneficiary then
      Gas.newAccount else 0
  let gasLeft ← Gas.charge evm.gasLeft
    (Evm.TangerineWhistle.Vm.Gas.selfDestruct + newAccountCost)

  let st :=
    if balance = (0 : Evm.U256) ∧ ¬ evm.env.state.accountExists beneficiary then
      evm.env.state
    else
      evm.env.state.addBalance beneficiary balance
  let st := st.setAccount self { (st.getAccount self) with balance := 0 }
  let firstTime := ¬ evm.env.selfDestructSet.contains self
  let refund := if firstTime then Gas.selfDestructRefund else 0
  -- EIP-161: SELFDESTRUCT touches the beneficiary (and `self`, which
  -- is queued for deletion below so the sweep won't see it anyway).
  let envTouched := touchAddr evm.env beneficiary
  return { evm with
    gasLeft := gasLeft,
    env := { envTouched with
      state := st,
      selfDestructSet :=
        if firstTime then evm.env.selfDestructSet ++ [self]
        else evm.env.selfDestructSet,
      refundCounter := evm.env.refundCounter + refund },
    halted := true }

mutual

def dispatch (fuel : Nat) (op : UInt8) : Handler :=
  match op.toNat with
  | 0x00 => stop
  | 0x01 => add
  | 0x02 => mul
  | 0x03 => sub
  | 0x04 => div
  | 0x05 => sdiv
  | 0x06 => mod_
  | 0x07 => smod_
  | 0x08 => addmod
  | 0x09 => mulmod
  | 0x0a => Evm.SpuriousDragon.Vm.Instructions.exp  -- EIP-160
  | 0x0b => signextend
  | 0x10 => lt
  | 0x11 => gt
  | 0x12 => slt
  | 0x13 => sgt
  | 0x14 => eq
  | 0x15 => iszero
  | 0x16 => and_
  | 0x17 => or_
  | 0x18 => xor_
  | 0x19 => not_
  | 0x1a => byte
  | 0x20 => keccak256
  | 0x30 => address
  | 0x31 => Evm.TangerineWhistle.Vm.Instructions.balance        -- EIP-150
  | 0x32 => origin
  | 0x33 => caller
  | 0x34 => callvalue
  | 0x35 => calldataload
  | 0x36 => calldatasize
  | 0x37 => calldatacopy
  | 0x38 => codesize
  | 0x39 => codecopy
  | 0x3a => gasprice
  | 0x3b => Evm.TangerineWhistle.Vm.Instructions.extcodesize    -- EIP-150
  | 0x3c => Evm.TangerineWhistle.Vm.Instructions.extcodecopy    -- EIP-150
  | 0x40 => blockhash
  | 0x41 => coinbase
  | 0x42 => timestamp
  | 0x43 => number
  | 0x44 => difficulty
  | 0x45 => gaslimit
  | 0x50 => Instructions.pop
  | 0x51 => mload
  | 0x52 => mstore
  | 0x53 => mstore8
  | 0x54 => Evm.TangerineWhistle.Vm.Instructions.sload          -- EIP-150
  | 0x55 => sstore
  | 0x56 => jump
  | 0x57 => jumpi
  | 0x58 => pc
  | 0x59 => msize
  | 0x5a => gas
  | 0x5b => jumpdest
  | 0xf0 => create fuel
  | 0xf1 => call fuel
  | 0xf2 => callcode fuel
  | 0xf3 => return_
  | 0xf4 => delegatecall fuel
  | 0xff => selfdestruct
  | n =>
    if      0x60 ≤ n ∧ n ≤ 0x7f then push (n - 0x5f)
    else if 0x80 ≤ n ∧ n ≤ 0x8f then dup  (n - 0x7f)
    else if 0x90 ≤ n ∧ n ≤ 0x9f then swap (n - 0x8f)
    else if 0xa0 ≤ n ∧ n ≤ 0xa4 then log  (n - 0xa0)
    else fun _ => .error (.invalidOpcode op)
termination_by (fuel, 2)

def step (fuel : Nat) (evm : Evm) : Except Exception Evm :=
  if evm.halted then return evm
  else if evm.pc ≥ evm.message.code.size then
    return { evm with halted := true }
  else
    dispatch fuel (evm.message.code.get! evm.pc) evm
termination_by (fuel, 3)

def runFrame : Nat → Evm → Except Exception Evm
  | 0,      _   => .error .fuelExhausted
  | fuel+1, evm => do
    let evm' ← step fuel evm
    if evm'.halted then return evm'
    runFrame fuel evm'
termination_by f _ => (f, 0)

/-- 0xf1 CALL — EIP-150 + EIP-161. NEW_ACCOUNT charged iff
    `value > 0 ∧ is_dead(callee)`. -/
def call : Nat → Handler
  | 0      => fun _   => .error .fuelExhausted
  | fuel+1 => fun evm => do
  let (gasArg, addrW, value, argsOff, argsLen, retOff, retLen, s) ← pop7 evm.stack
  let callee := u256ToAddr addrW
  let argsOffN := argsOff.toNat
  let argsLenN := argsLen.toNat
  let retOffN  := retOff.toNat
  let retLenN  := retLen.toNat
  let (gasLeft, mem) ← chargeMemory evm.gasLeft evm.memory argsOffN argsLenN
  let (gasLeft, mem) ← chargeMemory gasLeft mem retOffN retLenN
  let valueCost      : Nat := if value = (0 : Evm.U256) then 0 else Gas.callValue
  let newAccountCost : Nat :=
    if value ≠ (0 : Evm.U256) ∧ isDead evm.env.state callee then Gas.newAccount else 0
  let gasLeft ←
    Gas.charge gasLeft
      (Evm.TangerineWhistle.Vm.Gas.call + valueCost + newAccountCost)
  let gasForwardRaw := capForward gasArg.toNat gasLeft
  let gasLeft       := gasLeft - gasForwardRaw
  let gasForward    := gasForwardRaw +
                       (if value = (0 : Evm.U256) then 0 else Gas.callStipend)
  let caller        := evm.message.currentTarget
  let callerBalance := evm.env.state.getBalance caller
  let failFast :=
    evm.message.depth ≥ maxCallDepth ∨
    (value ≠ (0 : Evm.U256) ∧ callerBalance.toNat < value.toNat)
  if failFast then
    let s ← Stack.push s 0
    return { evm with
      gasLeft := gasLeft + gasForward, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
  let stateAfterTransfer :=
    if value = (0 : Evm.U256) then evm.env.state
    else (evm.env.state.subBalance caller value).addBalance callee value
  -- EIP-161: a CALL touches its recipient (state-changing operation).
  let envChild := touchAddr { evm.env with state := stateAfterTransfer } callee
  let input := Evm.Bytes.sliceZeroPad mem argsOffN argsLenN
  let runResult : Except Exception (Evm.Bytes × Nat × Evm) :=
    match Evm.Frontier.Vm.PrecompiledContracts.lookup callee with
    | some precompile =>
      match precompile input gasForward with
      | .ok (output, gasLeftSub) =>
        .ok (output, gasLeftSub,
             { gasLeft := gasLeftSub
               message := { caller := caller, target := some callee,
                            currentTarget := callee, value := value,
                            data := input, code := Evm.Bytes.empty,
                            gas := gasForward, depth := evm.message.depth + 1 }
               env := envChild
               halted := true, output := output })
      | .error e => .error e
    | none =>
      let calleeAccount := evm.env.state.getAccount callee
      let subMsg : Message :=
        { caller := caller, target := some callee, currentTarget := callee,
          value := value, data := input, code := calleeAccount.code,
          gas := gasForward, depth := evm.message.depth + 1 }
      let subEvm := Evm.fresh subMsg envChild
      (runFrame fuel subEvm).map fun s => (s.output, s.gasLeft, s)
  match runResult with
  | .ok (output, gasLeftSub, subEvm) =>
    let writeLen := min retLenN output.size
    let mem := Memory.write mem retOffN (Evm.Bytes.sliceZeroPad output 0 writeLen)
    let merged := mergeChild evm subEvm
    let s ← Stack.push s 1
    return { merged with
      gasLeft := gasLeft + gasLeftSub, memory := mem, stack := s,
      returnData := output, pc := evm.pc + 1 }
  | .error _ =>
    let s ← Stack.push s 0
    return { evm with
      gasLeft := gasLeft, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
termination_by f => (f, 1)

def callcode : Nat → Handler
  | 0      => fun _   => .error .fuelExhausted
  | fuel+1 => fun evm => do
  let (gasArg, addrW, value, argsOff, argsLen, retOff, retLen, s) ← pop7 evm.stack
  let codeFrom := u256ToAddr addrW
  let argsOffN := argsOff.toNat
  let argsLenN := argsLen.toNat
  let retOffN  := retOff.toNat
  let retLenN  := retLen.toNat
  let (gasLeft, mem) ← chargeMemory evm.gasLeft evm.memory argsOffN argsLenN
  let (gasLeft, mem) ← chargeMemory gasLeft mem retOffN retLenN
  let valueCost : Nat := if value = (0 : Evm.U256) then 0 else Gas.callValue
  let gasLeft ← Gas.charge gasLeft (Evm.TangerineWhistle.Vm.Gas.call + valueCost)
  let gasForwardRaw := capForward gasArg.toNat gasLeft
  let gasLeft       := gasLeft - gasForwardRaw
  let gasForward    := gasForwardRaw +
                       (if value = (0 : Evm.U256) then 0 else Gas.callStipend)
  let caller        := evm.message.currentTarget
  let callerBalance := evm.env.state.getBalance caller
  let failFast :=
    evm.message.depth ≥ maxCallDepth ∨
    (value ≠ (0 : Evm.U256) ∧ callerBalance.toNat < value.toNat)
  if failFast then
    let s ← Stack.push s 0
    return { evm with
      gasLeft := gasLeft + gasForward, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
  let input := Evm.Bytes.sliceZeroPad mem argsOffN argsLenN
  let calleeAccount := evm.env.state.getAccount codeFrom
  -- EIP-161: CALLCODE runs in the caller's context; per EELS the
  -- touched address is `to`, which for CALLCODE is the caller (already
  -- touched by the tx). The code-source is NOT touched.
  let runResult : Except Exception (Evm.Bytes × Nat × Evm) :=
    match Evm.Frontier.Vm.PrecompiledContracts.lookup codeFrom with
    | some precompile =>
      match precompile input gasForward with
      | .ok (output, gasLeftSub) =>
        .ok (output, gasLeftSub,
             { gasLeft := gasLeftSub
               message := { caller := caller, target := some codeFrom,
                            currentTarget := caller, value := value,
                            data := input, code := Evm.Bytes.empty,
                            gas := gasForward, depth := evm.message.depth + 1 }
               env := evm.env, halted := true, output := output })
      | .error e => .error e
    | none =>
      let subMsg : Message :=
        { caller := caller, target := some codeFrom, currentTarget := caller,
          value := value, data := input, code := calleeAccount.code,
          gas := gasForward, depth := evm.message.depth + 1 }
      let subEvm := Evm.fresh subMsg evm.env
      (runFrame fuel subEvm).map fun s => (s.output, s.gasLeft, s)
  match runResult with
  | .ok (output, gasLeftSub, subEvm) =>
    let writeLen := min retLenN output.size
    let mem := Memory.write mem retOffN (Evm.Bytes.sliceZeroPad output 0 writeLen)
    let merged := mergeChild evm subEvm
    let s ← Stack.push s 1
    return { merged with
      gasLeft := gasLeft + gasLeftSub, memory := mem, stack := s,
      returnData := output, pc := evm.pc + 1 }
  | .error _ =>
    let s ← Stack.push s 0
    return { evm with
      gasLeft := gasLeft, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
termination_by f => (f, 1)

def delegatecall : Nat → Handler
  | 0      => fun _   => .error .fuelExhausted
  | fuel+1 => fun evm => do
  let (gasArg, addrW, argsOff, argsLen, retOff, retLen, s) ← pop6 evm.stack
  let codeFrom := u256ToAddr addrW
  let argsOffN := argsOff.toNat
  let argsLenN := argsLen.toNat
  let retOffN  := retOff.toNat
  let retLenN  := retLen.toNat
  let (gasLeft, mem) ← chargeMemory evm.gasLeft evm.memory argsOffN argsLenN
  let (gasLeft, mem) ← chargeMemory gasLeft mem retOffN retLenN
  let gasLeft ← Gas.charge gasLeft Evm.TangerineWhistle.Vm.Gas.call
  let gasForward := capForward gasArg.toNat gasLeft
  let gasLeft    := gasLeft - gasForward
  if evm.message.depth ≥ maxCallDepth then
    let s ← Stack.push s 0
    return { evm with
      gasLeft := gasLeft + gasForward, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
  let input := Evm.Bytes.sliceZeroPad mem argsOffN argsLenN
  let calleeAccount := evm.env.state.getAccount codeFrom
  -- EIP-161: DELEGATECALL runs in current context; per EELS the touched
  -- address is `to`, which for DELEGATECALL is the current contract
  -- (already touched). The code-source is NOT touched.
  let runResult : Except Exception (Evm.Bytes × Nat × Evm) :=
    match Evm.Frontier.Vm.PrecompiledContracts.lookup codeFrom with
    | some precompile =>
      match precompile input gasForward with
      | .ok (output, gasLeftSub) =>
        .ok (output, gasLeftSub,
             { gasLeft := gasLeftSub
               message := { caller := evm.message.caller,
                            target := some codeFrom,
                            currentTarget := evm.message.currentTarget,
                            value := evm.message.value,
                            data := input, code := Evm.Bytes.empty,
                            gas := gasForward, depth := evm.message.depth + 1 }
               env := evm.env, halted := true, output := output })
      | .error e => .error e
    | none =>
      let subMsg : Message :=
        { caller := evm.message.caller
          target := some codeFrom
          currentTarget := evm.message.currentTarget
          value := evm.message.value
          data := input
          code := calleeAccount.code
          gas := gasForward
          depth := evm.message.depth + 1 }
      let subEvm := Evm.fresh subMsg evm.env
      (runFrame fuel subEvm).map fun s => (s.output, s.gasLeft, s)
  match runResult with
  | .ok (output, gasLeftSub, subEvm) =>
    let writeLen := min retLenN output.size
    let mem := Memory.write mem retOffN (Evm.Bytes.sliceZeroPad output 0 writeLen)
    let merged := mergeChild evm subEvm
    let s ← Stack.push s 1
    return { merged with
      gasLeft := gasLeft + gasLeftSub, memory := mem, stack := s,
      returnData := output, pc := evm.pc + 1 }
  | .error _ =>
    let s ← Stack.push s 0
    return { evm with
      gasLeft := gasLeft, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
termination_by f => (f, 1)

/-- 0xf0 CREATE — EIP-150 63/64 + EIP-170 max code size check. -/
def create : Nat → Handler
  | 0      => fun _   => .error .fuelExhausted
  | fuel+1 => fun evm => do
  let (value, offset, len, s) ← Stack.pop3 evm.stack
  let offN := offset.toNat
  let lenN := len.toNat
  let (gasLeft, mem) ← chargeMemory evm.gasLeft evm.memory offN lenN
  let gasLeft ← Gas.charge gasLeft Gas.create
  let sender := evm.message.currentTarget
  let senderAcc := evm.env.state.getAccount sender
  let failFast :=
    evm.message.depth ≥ maxCallDepth ∨
    senderAcc.balance.toNat < value.toNat
  if failFast then
    let s ← Stack.push s 0
    return { evm with
      gasLeft := gasLeft, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
  let newAddr := Evm.Frontier.Utils.computeContractAddress sender senderAcc.nonce
  let initCode := Evm.Bytes.sliceZeroPad mem offN lenN
  let collision := evm.env.state.getAccount newAddr
  let gasRetained := gasLeft / 64
  if collision.nonce > 0 ∨ collision.code.size > 0 then
    let s ← Stack.push s 0
    let stateBumped := evm.env.state.setAccount sender
      { senderAcc with nonce := senderAcc.nonce + 1 }
    return { evm with
      env := { evm.env with state := stateBumped },
      gasLeft := gasRetained, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
  let gasForward := gasLeft - gasRetained
  let gasLeft    := gasRetained
  let stateAfterSetup :=
    let st := evm.env.state
    let st := st.setAccount sender { senderAcc with
      nonce := senderAcc.nonce + 1,
      balance := senderAcc.balance - value }
    let dest := st.getAccount newAddr
    -- EIP-161 part 2: a newly-created account starts at nonce 1, so
    -- an init code that returns nothing doesn't leave behind an
    -- "empty" account which would then be swept at end-of-tx.
    st.setAccount newAddr { dest with balance := dest.balance + value, nonce := 1 }
  -- EIP-161: CREATE touches the newly-created address.
  let envChild := touchAddr { evm.env with state := stateAfterSetup } newAddr
  let subMsg : Message :=
    { caller := sender, target := some newAddr, currentTarget := newAddr,
      value := value, data := Evm.Bytes.empty, code := initCode,
      gas := gasForward, depth := evm.message.depth + 1 }
  let subEvm := Evm.fresh subMsg envChild
  match runFrame fuel subEvm with
  | .ok subEvm =>
    let codeBytes := subEvm.output
    -- EIP-170: enforce max deployed code size.
    if codeBytes.size > Evm.SpuriousDragon.Vm.Gas.maxCodeSize then
      let s ← Stack.push s 0
      return { evm with
        gasLeft := gasLeft, memory := mem, stack := s,
        returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
    let depositCost := Gas.codeDeposit * codeBytes.size
    if subEvm.gasLeft < depositCost then
      let s ← Stack.push s 0
      return { evm with
        gasLeft := gasLeft, memory := mem, stack := s,
        returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
    else
      let st := subEvm.env.state.setAccount newAddr
                  { (subEvm.env.state.getAccount newAddr) with code := codeBytes }
      let merged := mergeChild evm
        { subEvm with env := { subEvm.env with state := st } }
      let s ← Stack.push s (addrToU256 newAddr)
      return { merged with
        gasLeft := gasLeft + (subEvm.gasLeft - depositCost), memory := mem,
        stack := s, returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
  | .error _ =>
    let stateAfterNonceBump :=
      evm.env.state.setAccount sender { senderAcc with
        nonce := senderAcc.nonce + 1 }
    let s ← Stack.push s 0
    return { evm with
      env := { evm.env with state := stateAfterNonceBump },
      gasLeft := gasLeft, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
termination_by f => (f, 1)

end -- mutual

/-- Default fuel ceiling — see `Evm.Frontier.Vm.defaultFuel`. -/
def defaultFuel : Nat := Evm.Frontier.Vm.defaultFuel

def applyMessage (msg : Message) (env : Environment) : Except Exception Evm :=
  runFrame defaultFuel (Evm.fresh msg env)

end Evm.SpuriousDragon.Vm
