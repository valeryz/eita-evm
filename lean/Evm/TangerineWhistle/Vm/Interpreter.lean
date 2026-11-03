/-
  Evm.TangerineWhistle.Vm.Interpreter — EIP-150 dispatcher + recursive
  handlers (CALL, CALLCODE, DELEGATECALL, CREATE, SELFDESTRUCT).

  Major behavioural change from Homestead:

  * **63/64 forwarded-gas rule.** For the CALL family, the gas argument
    is silently capped at `(remaining - remaining/64)`. There is no
    "pre-pay full gasArg and OOG if insufficient" — it's now physically
    impossible to over-request. CREATE forwards `(remaining - remaining/64)`
    of its post-base gas to the init code rather than all of it.

  * **Repriced base costs** from `Evm.TangerineWhistle.Vm.Gas`.

  * **SELFDESTRUCT now costs 5000** plus a `GAS_NEW_ACCOUNT` (25000)
    surcharge if the beneficiary doesn't already exist.

  Every opcode handler not listed in `dispatch` here is reused as-is
  from `Evm.Frontier.Vm.Instructions.*` — TW only mutates the ones
  EIP-150 actually touches.
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

namespace Evm.TangerineWhistle.Vm

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

def maxCallDepth : Nat := 1024

private def addrToU256 (a : Evm.Address) : Evm.U256 := Evm.U256.ofNat a.toNat
private def u256ToAddr (x : Evm.U256) : Evm.Address := Evm.Address.ofNat x.toNat

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

/-- The EIP-150 63/64-of-remaining cap on forwarded gas. -/
private def capForward (requested available : Nat) : Nat :=
  min requested (available - available / 64)

/-- 0xff SELFDESTRUCT — EIP-150: base 5000, plus `GAS_NEW_ACCOUNT`
    (25000) if the beneficiary doesn't already exist in state.
    Non-recursive — outside the fuel-bounded mutual block. -/
def selfdestruct : Handler := fun evm => do
  -- EIP-214 (Byzantium+): SELFDESTRUCT is forbidden in static context.
  if evm.message.isStatic then
    .error .writeInStaticContext
  let (beneficiaryW, _) ← Stack.pop evm.stack
  let beneficiary := u256ToAddr beneficiaryW
  let self        := evm.message.currentTarget

  let newAccountCost : Nat :=
    if evm.env.state.accountExists beneficiary then 0 else Gas.newAccount
  let gasLeft ← Gas.charge evm.gasLeft
    (Evm.TangerineWhistle.Vm.Gas.selfDestruct + newAccountCost)

  let balance := evm.env.state.getBalance self
  let st := evm.env.state.addBalance beneficiary balance
  let st := st.setAccount self { (st.getAccount self) with balance := 0 }
  let firstTime := ¬ evm.env.selfDestructSet.contains self
  let refund := if firstTime then Gas.selfDestructRefund else 0
  return { evm with
    gasLeft := gasLeft,
    env := { evm.env with
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
  | 0x0a => Instructions.exp
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
  -- EIP-150 deltas:
  | 0x31 => Evm.TangerineWhistle.Vm.Instructions.balance
  | 0x32 => origin
  | 0x33 => caller
  | 0x34 => callvalue
  | 0x35 => calldataload
  | 0x36 => calldatasize
  | 0x37 => calldatacopy
  | 0x38 => codesize
  | 0x39 => codecopy
  | 0x3a => gasprice
  | 0x3b => Evm.TangerineWhistle.Vm.Instructions.extcodesize
  | 0x3c => Evm.TangerineWhistle.Vm.Instructions.extcodecopy
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
  | 0x54 => Evm.TangerineWhistle.Vm.Instructions.sload
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

/-- 0xf1 CALL — EIP-150: base 700, 63/64-of-remaining forwarded-gas cap. -/
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
    if evm.env.state.accountExists callee then 0 else Gas.newAccount
  let gasLeft ←
    Gas.charge gasLeft
      (Evm.TangerineWhistle.Vm.Gas.call + valueCost + newAccountCost)

  -- 63/64 cap (replaces Homestead's gasArg pre-payment).
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

  -- Pre-EIP-158: a CALL to a non-existent address creates that
  -- account in state regardless of value (geth `exec()` in
  -- core/execution.go: every CALL goes through CreateAccount when
  -- !Exist). That makes a second CALL to the same address see it as
  -- existing and not re-charge NEW_ACCOUNT — the case that produced
  -- the `tx_e1c174e2_d0g0v0_EIP150` over-charge.
  let stateTouched :=
    if evm.env.state.accountExists callee then evm.env.state
    else evm.env.state.setAccount callee Evm.Frontier.Account.empty
  let stateAfterTransfer :=
    if value = (0 : Evm.U256) then stateTouched
    else (stateTouched.subBalance caller value).addBalance callee value
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
               env := { evm.env with state := stateAfterTransfer }
               halted := true, output := output })
      | .error e => .error e
    | none =>
      let calleeAccount := evm.env.state.getAccount callee
      let subMsg : Message :=
        { caller := caller, target := some callee, currentTarget := callee,
          value := value, data := input, code := calleeAccount.code,
          gas := gasForward, depth := evm.message.depth + 1 }
      let subEvm := Evm.fresh subMsg { evm.env with state := stateAfterTransfer }
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

/-- 0xf2 CALLCODE — EIP-150: base 700, 63/64 cap. Storage owner stays
    the caller. -/
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

/-- 0xf4 DELEGATECALL — EIP-150: base 700, 63/64 cap, no value transfer. -/
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

/-- 0xf0 CREATE — EIP-150: forward only 63/64 of post-base gas to the
    init code (rather than all of it). EIP-2's deposit-failure-reverts
    rule still applies, since that's a Homestead change. -/
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
  -- EIP-150: even on collision, the caller retains its 1/64 of the
  -- post-base gas (the forwarded 63/64 is consumed, as if a sub-frame
  -- had OOG'd immediately). The sender's nonce is bumped regardless
  -- (per EELS: collision is still "an attempted creation").
  let gasRetained := gasLeft / 64
  if collision.nonce > 0 ∨ collision.code.size > 0 then
    let s ← Stack.push s 0
    let stateBumped := evm.env.state.setAccount sender
      { senderAcc with nonce := senderAcc.nonce + 1 }
    return { evm with
      env := { evm.env with state := stateBumped },
      gasLeft := gasRetained, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }

  -- EIP-150: forward 63/64 of remaining (not all).
  let gasForward := gasLeft - gasRetained
  let gasLeft    := gasRetained

  let stateAfterSetup :=
    let st := evm.env.state
    let st := st.setAccount sender { senderAcc with
      nonce := senderAcc.nonce + 1,
      balance := senderAcc.balance - value }
    let dest := st.getAccount newAddr
    st.setAccount newAddr { dest with balance := dest.balance + value }
  let subMsg : Message :=
    { caller := sender, target := some newAddr, currentTarget := newAddr,
      value := value, data := Evm.Bytes.empty, code := initCode,
      gas := gasForward, depth := evm.message.depth + 1 }
  let subEvm := Evm.fresh subMsg { evm.env with state := stateAfterSetup }
  match runFrame fuel subEvm with
  | .ok subEvm =>
    let codeBytes := subEvm.output
    let depositCost := Gas.codeDeposit * codeBytes.size
    if subEvm.gasLeft < depositCost then
      -- EIP-2: revert (carried forward from Homestead).
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

end Evm.TangerineWhistle.Vm
