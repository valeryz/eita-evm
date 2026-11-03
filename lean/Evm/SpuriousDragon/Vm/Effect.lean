/-
  Evm.SpuriousDragon.Vm.Effect — yield-based execution for SD.

  Deltas from TW:
    * EIP-160: EXP byte cost 10 → 50.
    * EIP-161: state-clearing. CALL/SELFDESTRUCT NEW_ACCOUNT becomes
      value-gated (`value > 0 ∧ isDead(callee)`). Touched-set
      tracking via `touchAddr` in env.
    * EIP-170: 24576-byte max deployed-code size.

  Carries TW's EIP-150 deltas (63/64 forward, repriced bases).

  Original Frontier doc:

  Migration from the recursive mutual block (#5) to a trampoline-based
  interpreter. First-pass scope: yields only for the recursive opcodes
  (CALL / CALLCODE / CREATE). Everything else uses the existing total
  handlers via `liftPure`. Storage/balance/log yields are architectural
  groundwork for Block-STM (#6); they're not required for functional
  equivalence with the existing interpreter, so deferred.

  The win in this drop:
    * `runFrame` has zero recursion across frames.
    * Sub-frame execution lives in the trampoline, structurally separate
      from opcode dispatch.
    * Termination is local: `runFrame`'s fuel bounds steps within one
      frame; `trampoline`'s fuel bounds the call-depth × per-frame-steps
      product, which is bounded by gas budget × 1024 in real execution.

  The trampoline + `applyMessage` here are intended to drop in as a
  replacement for `Frontier.Vm.applyMessage`.
-/

import Evm.Frontier.Vm
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
import Evm.Frontier.Vm.Interpreter   -- for selfdestruct + addrToU256/u256ToAddr-style helpers
import Evm.Frontier.Utils.Address
import Evm.TangerineWhistle.Vm.Gas
import Evm.TangerineWhistle.Vm.Instructions
import Evm.TangerineWhistle.Vm.Effect      -- for the pure EIP-150 callGasPlan
import Evm.SpuriousDragon.Vm.Gas
import Evm.SpuriousDragon.Vm.Instructions
import Evm.SpuriousDragon.Vm.Interpreter   -- for SD selfdestruct + touchAddr

namespace Evm.SpuriousDragon.Vm.Effect

open Evm.Frontier (Account)
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions
-- Call gas at SD is TW's (EIP-161 only narrows the new-account FLAG to
-- `value ≠ 0 ∧ dead`, decided at the call site), so bind TW's plan.
open Evm.TangerineWhistle.Vm.Effect (callGasPlan)

/-! ## Local helpers (mirror Interpreter.lean's privates) -/

private def addrToU256 (a : Evm.Address) : Evm.U256 :=
  Evm.U256.ofNat a.toNat

private def u256ToAddr (x : Evm.U256) : Evm.Address :=
  Evm.Address.ofNat x.toNat

def maxCallDepth : Nat := 1024

/-- EIP-161 "is_dead": account is absent OR present-but-empty. -/
private def isDead (state : Evm.Frontier.State) (addr : Evm.Address) : Bool :=
  if state.accountExists addr then (state.getAccount addr).isEmpty
  else true

/-! ## Yield effects -/

/-- Tag for the call-family kind, used by resume to push the right
    success/failure indicator and merge state correctly. Homestead
    adds `delegatecall` (EIP-7). -/
inductive CallKind where
  | call
  | callcode
  | delegatecall
  deriving Inhabited, DecidableEq

/-- A point in execution where the frame needs to coordinate with the
    world. First-pass scope: only the recursive opcodes yield. -/
inductive YieldEffect where
  /-- CALL family (`Evm.Frontier.Vm.Call`): the child's message, the address whose
      precompile runs (`none` when EIP-7702 disabled precompiles), the child's world, the
      caller's gas and memory after the charge, the output range, the caller's stack and
      pc. -/
  | callLike     (kind : CallKind) (subMsg : Message) (code : Option Evm.Address)
                 (stateForSub : Evm.Frontier.State)
                 (gasLeftPostCharge : Nat) (mem : Memory)
                 (retOff retLen : Nat) (stack : Stack)
                 (pc : Nat)
  /-- CREATE: sub-frame runs init code with `stateForSub` (value
      transfer already applied). -/
  | createLike   (subMsg : Message) (newAddr : Evm.Address)
                 (stateForSub : Evm.Frontier.State)
                 (gasLeftPostCharge : Nat) (mem : Memory)
                 (stack : Stack) (pc : Nat) (sender : Evm.Address)
                 (senderAccNonce : Nat) (value : Evm.U256)

  -- State yields (atomic state operations) — see Frontier.Vm.Effect.
  | sload          (slot : Evm.U256)
  | sstore         (key : Evm.U256) (value : Evm.U256)
  | balance        (addr : Evm.Address)
  | extcodesize    (addr : Evm.Address)
  | extcodecopy    (addr : Evm.Address) (memOff codeOff size : Nat)
  | blockhash      (n : Nat)
  | logEmit        (record : Log)
  | selfdestruct   (beneficiary : Evm.Address)
  deriving Inhabited

/-! ## Per-opcode dispatch -/

inductive StepResult where
  | continue    (frame : Evm)
  | yield       (frame : Evm) (eff : YieldEffect)
  | halt        (frame : Evm) (output : Evm.Bytes)
  | error       (frame : Evm) (e : Exception)
  deriving Inhabited

inductive Step where
  | yield  (frame : Evm) (eff : YieldEffect)
  | halt   (frame : Evm) (output : Evm.Bytes)
  | error  (frame : Evm) (e : Exception)
  deriving Inhabited

/-- Lift a total handler into a StepResult. -/
def liftPure (h : Handler) (evm : Evm) : StepResult :=
  match h evm with
  | .ok evm'   =>
    if evm'.halted then .halt evm' evm'.output else .continue evm'
  | .error e   => .error evm e

/-! ## Pop helpers (mirror Interpreter's `pop7`) -/

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

/-! ## CALL / CALLCODE / CREATE — yield variants -/

/-- 0xf1 CALL (EELS `call`) — `Evm.Frontier.Vm.Call.opcode` at this fork's rules: the pops, the static
    check, the memory charge, then `Call.start`; the child's run and its end are the
    `.callLike` arm (`Call.resume`). -/
def doCall (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Call.opcode (Evm.Frontier.Vm.Call.Rules.ofOrd 4) .call evm (.error evm) .continue
    (fun p m c st ro rl => .yield p (.callLike .call m c st p.gasLeft p.memory ro rl p.stack p.pc))

/-- 0xf2 CALLCODE (EELS `callcode`) — `Evm.Frontier.Vm.Call.opcode` at this fork's rules: the pops, the static
    check, the memory charge, then `Call.start`; the child's run and its end are the
    `.callLike` arm (`Call.resume`). -/
def doCallcode (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Call.opcode (Evm.Frontier.Vm.Call.Rules.ofOrd 4) .callcode evm (.error evm) .continue
    (fun p m c st ro rl => .yield p (.callLike .callcode m c st p.gasLeft p.memory ro rl p.stack p.pc))

/-- 0xf4 DELEGATECALL (EELS `delegatecall`, EIP-7) — `Evm.Frontier.Vm.Call.opcode` at this fork's rules: the pops, the static
    check, the memory charge, then `Call.start`; the child's run and its end are the
    `.callLike` arm (`Call.resume`). -/
def doDelegatecall (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Call.opcode (Evm.Frontier.Vm.Call.Rules.ofOrd 4) .delegatecall evm (.error evm) .continue
    (fun p m c st ro rl => .yield p (.callLike .delegatecall m c st p.gasLeft p.memory ro rl p.stack p.pc))

/-- 0xf0 CREATE — deploy a new contract. -/
def doCreate (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Create.opcode (Evm.Frontier.Vm.Create.Rules.ofOrd 4) false false evm (.error evm) .continue
    (fun p m st snd n v => .yield p (.createLike m m.currentTarget st p.gasLeft p.memory p.stack p.pc snd n v))

/-! ## State-yielding handlers (mirror Frontier.Vm.Effect) -/

def doSload (evm : Evm) : StepResult :=
  match Gas.charge evm.gasLeft Evm.TangerineWhistle.Vm.Gas.sLoad with
  | .error e => .error evm e
  | .ok gasLeft =>
    match Stack.pop evm.stack with
    | .error e => .error evm e
    | .ok (key, s) => .yield { evm with gasLeft := gasLeft, stack := s } (.sload key)

def doSstore (evm : Evm) : StepResult :=
  if evm.message.isStatic then .error evm .writeInStaticContext
  else
  match Stack.pop2 evm.stack with
  | .error e => .error evm e
  | .ok (key, value, s) => .yield { evm with stack := s } (.sstore key value)

def doBalance (evm : Evm) : StepResult :=
  match Gas.charge evm.gasLeft Evm.TangerineWhistle.Vm.Gas.balance with
  | .error e => .error evm e
  | .ok gasLeft =>
    match Stack.pop evm.stack with
    | .error e => .error evm e
    | .ok (addrW, s) =>
      .yield { evm with gasLeft := gasLeft, stack := s } (.balance (u256ToAddr addrW))

def doExtcodesize (evm : Evm) : StepResult :=
  match Gas.charge evm.gasLeft Evm.TangerineWhistle.Vm.Gas.extCode with
  | .error e => .error evm e
  | .ok gasLeft =>
    match Stack.pop evm.stack with
    | .error e => .error evm e
    | .ok (addrW, s) =>
      .yield { evm with gasLeft := gasLeft, stack := s } (.extcodesize (u256ToAddr addrW))

def doExtcodecopy (evm : Evm) : StepResult :=
  match Stack.pop evm.stack with
  | .error e => .error evm e
  | .ok (addrW, s) =>
  match Stack.pop3 s with
  | .error e => .error evm e
  | .ok (memOff, codeOff, size, s) =>
  let memOffN := memOff.toNat
  let sizeN   := size.toNat
  match chargeMemory evm.gasLeft evm.memory memOffN sizeN with
  | .error e => .error evm e
  | .ok (gasLeft, mem) =>
  let copyCost := Evm.TangerineWhistle.Vm.Gas.extCode + Gas.copy * ((sizeN + 31) / 32)
  match Gas.charge gasLeft copyCost with
  | .error e => .error evm e
  | .ok gasLeft =>
    .yield { evm with gasLeft := gasLeft, memory := mem, stack := s }
           (.extcodecopy (u256ToAddr addrW) memOffN codeOff.toNat sizeN)

def doBlockhash (evm : Evm) : StepResult :=
  match Gas.charge evm.gasLeft Gas.blockHash with
  | .error e => .error evm e
  | .ok gasLeft =>
    match Stack.pop evm.stack with
    | .error e => .error evm e
    | .ok (n, s) =>
      .yield { evm with gasLeft := gasLeft, stack := s } (.blockhash n.toNat)

private def popTopicsAux (s : Stack) : Nat → Except Exception (List Evm.U256 × Stack)
  | 0     => return ([], s)
  | k + 1 => do
    let (t, s')   ← Stack.pop s
    let (ts, s'') ← popTopicsAux s' k
    return (t :: ts, s'')

def doLog (n : Nat) (evm : Evm) : StepResult :=
  if evm.message.isStatic then .error evm .writeInStaticContext
  else
  match Stack.pop2 evm.stack with
  | .error e => .error evm e
  | .ok (offset, len, s) =>
  match popTopicsAux s n with
  | .error e => .error evm e
  | .ok (topics, s) =>
    let off := offset.toNat
    let lenN := len.toNat
    let cost := Gas.log + Gas.logTopic * n + Gas.logData * lenN
    match Gas.charge evm.gasLeft cost with
    | .error e => .error evm e
    | .ok gasLeft =>
    match chargeMemory gasLeft evm.memory off lenN with
    | .error e => .error evm e
    | .ok (gasLeft, mem) =>
      let entry : Log :=
        { address := evm.message.currentTarget, topics := topics,
          data := Memory.read mem off lenN }
      .yield { evm with gasLeft := gasLeft, memory := mem, stack := s } (.logEmit entry)

def doSelfdestruct (evm : Evm) : StepResult :=
  if evm.message.isStatic then .error evm .writeInStaticContext
  else
  match Stack.pop evm.stack with
  | .error e => .error evm e
  | .ok (beneficiaryW, _) =>
    .yield evm (.selfdestruct (u256ToAddr beneficiaryW))

private def resumeSload (frame : Evm) (value : Evm.U256) : Except Exception Evm := do
  let s ← Stack.push frame.stack value
  return { frame with stack := s, pc := frame.pc + 1 }

private def resumeSstore (frame : Evm) (value oldValue : Evm.U256) : Except Exception Evm := do
  let cost := if oldValue = (0 : Evm.U256) ∧ value ≠ (0 : Evm.U256) then Gas.sSet else Gas.sReset
  let gasLeft ← Gas.charge frame.gasLeft cost
  let refundDelta : Nat :=
    if oldValue ≠ (0 : Evm.U256) ∧ value = (0 : Evm.U256) then Gas.sClearRefund else 0
  return { frame with
    gasLeft := gasLeft,
    env := { frame.env with refundCounter := frame.env.refundCounter + refundDelta },
    pc := frame.pc + 1 }

private def resumeBalance (frame : Evm) (bal : Evm.U256) : Except Exception Evm := do
  let s ← Stack.push frame.stack bal
  return { frame with stack := s, pc := frame.pc + 1 }

private def resumeExtcodesize (frame : Evm) (size : Nat) : Except Exception Evm := do
  let s ← Stack.push frame.stack (Evm.U256.ofNat size)
  return { frame with stack := s, pc := frame.pc + 1 }

private def resumeExtcodecopy (frame : Evm) : Except Exception Evm := do
  return { frame with pc := frame.pc + 1 }

private def resumeBlockhash (frame : Evm) (h : Evm.Hash32) : Except Exception Evm := do
  let s ← Stack.push frame.stack h
  return { frame with stack := s, pc := frame.pc + 1 }

private def resumeLog (frame : Evm) : Except Exception Evm := do
  return { frame with pc := frame.pc + 1 }

private def resumeSelfdestruct (frame : Evm) : Except Exception Evm := do
  return { frame with halted := true }

/-! ## Single-step dispatch -/


/-- Read one opcode and produce its `StepResult`. Mirrors the dispatch
    table in `Interpreter.lean`, but the recursive opcodes produce
    `.yield` instead of recursing into `runFrame`. -/
def step1 (evm : Evm) : StepResult :=
  if evm.halted then .halt evm evm.output
  else if evm.pc ≥ evm.message.code.size then
    .halt { evm with halted := true } evm.output
  else
    let op := evm.message.code.get! evm.pc
    match op.toNat with
    | 0x00 => .halt { evm with halted := true } evm.output
    | 0x01 => liftPure Instructions.add evm
    | 0x02 => liftPure Instructions.mul evm
    | 0x03 => liftPure Instructions.sub evm
    | 0x04 => liftPure Instructions.div evm
    | 0x05 => liftPure Instructions.sdiv evm
    | 0x06 => liftPure Instructions.mod_ evm
    | 0x07 => liftPure Instructions.smod_ evm
    | 0x08 => liftPure Instructions.addmod evm
    | 0x09 => liftPure Instructions.mulmod evm
    | 0x0a => liftPure Evm.SpuriousDragon.Vm.Instructions.exp evm  -- EIP-160
    | 0x0b => liftPure Instructions.signextend evm
    | 0x10 => liftPure Instructions.lt evm
    | 0x11 => liftPure Instructions.gt evm
    | 0x12 => liftPure Instructions.slt evm
    | 0x13 => liftPure Instructions.sgt evm
    | 0x14 => liftPure Instructions.eq evm
    | 0x15 => liftPure Instructions.iszero evm
    | 0x16 => liftPure Instructions.and_ evm
    | 0x17 => liftPure Instructions.or_ evm
    | 0x18 => liftPure Instructions.xor_ evm
    | 0x19 => liftPure Instructions.not_ evm
    | 0x1a => liftPure Instructions.byte evm
    | 0x20 => liftPure Instructions.keccak256 evm
    | 0x30 => liftPure Instructions.address evm
    | 0x31 => doBalance evm    -- EIP-150
    | 0x32 => liftPure Instructions.origin evm
    | 0x33 => liftPure Instructions.caller evm
    | 0x34 => liftPure Instructions.callvalue evm
    | 0x35 => liftPure Instructions.calldataload evm
    | 0x36 => liftPure Instructions.calldatasize evm
    | 0x37 => liftPure Instructions.calldatacopy evm
    | 0x38 => liftPure Instructions.codesize evm
    | 0x39 => liftPure Instructions.codecopy evm
    | 0x3a => liftPure Instructions.gasprice evm
    | 0x3b => doExtcodesize evm  -- EIP-150
    | 0x3c => doExtcodecopy evm  -- EIP-150
    | 0x40 => doBlockhash evm
    | 0x41 => liftPure Instructions.coinbase evm
    | 0x42 => liftPure Instructions.timestamp evm
    | 0x43 => liftPure Instructions.number evm
    | 0x44 => liftPure Instructions.difficulty evm
    | 0x45 => liftPure Instructions.gaslimit evm
    | 0x50 => liftPure Instructions.pop evm
    | 0x51 => liftPure Instructions.mload evm
    | 0x52 => liftPure Instructions.mstore evm
    | 0x53 => liftPure Instructions.mstore8 evm
    | 0x54 => doSload evm        -- EIP-150
    | 0x55 => doSstore evm
    | 0x56 => liftPure Instructions.jump evm
    | 0x57 => liftPure Instructions.jumpi evm
    | 0x58 => liftPure Instructions.pc evm
    | 0x59 => liftPure Instructions.msize evm
    | 0x5a => liftPure Instructions.gas evm
    | 0x5b => liftPure Instructions.jumpdest evm
    | 0xf0 => doCreate evm
    | 0xf1 => doCall evm
    | 0xf2 => doCallcode evm
    | 0xf3 => liftPure Instructions.return_ evm
    | 0xf4 => doDelegatecall evm   -- EIP-7
    | 0xff => liftPure _root_.Evm.SpuriousDragon.Vm.selfdestruct evm         -- EIP-161
    | n =>
      if      0x60 ≤ n ∧ n ≤ 0x7f then liftPure (Instructions.push (n - 0x5f)) evm
      else if 0x80 ≤ n ∧ n ≤ 0x8f then liftPure (Instructions.dup  (n - 0x7f)) evm
      else if 0x90 ≤ n ∧ n ≤ 0x9f then liftPure (Instructions.swap (n - 0x8f)) evm
      else if 0xa0 ≤ n ∧ n ≤ 0xa4 then doLog (n - 0xa0) evm
      else .error evm (.invalidOpcode op)

/-! ## Run-until-yield -/

/-- Step the current frame repeatedly until it yields, halts, or errors.
    `fuel` bounds the number of single-opcode steps within this frame —
    it does not span sub-frames. -/
def runFrame : Nat → Evm → Step
  | 0,      evm => .error evm .outOfGas
  | fuel+1, evm =>
    match step1 evm with
    | .continue evm'      => runFrame fuel evm'
    | .yield evm' eff     => .yield evm' eff
    | .halt evm' output   => .halt evm' output
    | .error evm' e       => .error evm' e

/-! ## Trampoline -/

/-- Merge a successful sub-frame back into the parent. -/
private def mergeChild (parent child : Evm) : Evm :=
  { parent with env := child.env }

/-- Process ONE yield: spawn the sub-frame (via the supplied
    `runSub` callback) or perform the state operation, run the
    matching resume function, and return the parent's
    continuation frame. Total — same extraction rationale as
    Frontier's `handleYield`: the IR trampoline binds it instead
    of re-encoding, and Spec-layer theorems can quantify over
    it. -/
def handleYield (frame : Evm) (eff : YieldEffect)
    (runSub : Evm → Except Exception Evm) : Except Exception Evm :=
  match eff with
  | .callLike _ subMsg code stateForSub _ _ retOff retLen _ _ =>
    -- EELS generic_call's end, process_message, execute_code, incorporate_child_*
    -- (Evm.Frontier.Vm.Call.resume / runChild).
    Evm.Frontier.Vm.Call.resume (Evm.Frontier.Vm.Call.Rules.ofOrd 4) frame subMsg.currentTarget
      retOff retLen
      (Evm.Frontier.Vm.Call.runChild (fun _ => Evm.Frontier.Vm.Call.precompiles 4) frame subMsg code stateForSub runSub)
  | .createLike subMsg newAddr stateForSub _ _ _ _ _ _ _ =>
    -- EELS process_create_message + incorporate_child_* (Evm.Frontier.Vm.Create.resume).
    Evm.Frontier.Vm.Create.resume (Evm.Frontier.Vm.Create.Rules.ofOrd 4) frame newAddr
      (runSub (Evm.Frontier.Vm.Create.child frame subMsg stateForSub))


  -- State yields (mirror Frontier.Vm.Effect)
  | .sload key =>
    let v := frame.env.state.getStorage frame.message.currentTarget key
    resumeSload frame v
  | .sstore key value =>
    let addr := frame.message.currentTarget
    let oldValue := frame.env.state.getStorage addr key
    let stateAfter := frame.env.state.setStorage addr key value
    let frameWithWrite := { frame with env := { frame.env with state := stateAfter } }
    resumeSstore frameWithWrite value oldValue
  | .balance addr =>
    let bal := frame.env.state.getBalance addr
    resumeBalance frame bal
  | .extcodesize addr =>
    let code := (frame.env.state.getAccount addr).code
    resumeExtcodesize frame code.size
  | .extcodecopy addr memOff codeOff size =>
    let code := (frame.env.state.getAccount addr).code
    let bytes := Evm.Bytes.sliceZeroPad code codeOff size
    let mem' := Memory.write frame.memory memOff bytes
    let frameWithCopy := { frame with memory := mem' }
    resumeExtcodecopy frameWithCopy
  | .blockhash n =>
    let curN := frame.env.number
    let h : Evm.Hash32 :=
      if n ≥ curN ∨ curN - n > 256 then 0
      else
        let len := frame.env.blockHashes.length
        let idx := len - (curN - n)
        frame.env.blockHashes[idx]?.getD 0
    resumeBlockhash frame h
  | .logEmit entry =>
    let frameWithLog :=
      { frame with env := { frame.env with logs := frame.env.logs ++ [entry] } }
    resumeLog frameWithLog
  | .selfdestruct beneficiary =>
    let self := frame.message.currentTarget
    let balance := frame.env.state.getBalance self
    let st  := frame.env.state.addBalance beneficiary balance
    let st  := st.setAccount self { (st.getAccount self) with balance := 0 }
    let firstTime := ¬ frame.env.selfDestructSet.contains self
    let refund    := if firstTime then Gas.selfDestructRefund else 0
    let frameAfter :=
      { frame with
        env := { frame.env with
          state := st,
          selfDestructSet :=
            if firstTime then frame.env.selfDestructSet ++ [self]
            else frame.env.selfDestructSet,
          refundCounter := frame.env.refundCounter + refund } }
    resumeSelfdestruct frameAfter

/-- The trampoline: orchestrates `runFrame`, handles each yield via
    `handleYield` (spawning sub-frames by recursively trampolining
    them), until the top frame halts or errors. -/
partial def trampoline (evm : Evm) : Except Exception Evm :=
  match runFrame (1 <<< 24) evm with
  | .halt finalEvm _ => .ok finalEvm
  | .error _ e       => .error e
  | .yield frame eff =>
    match handleYield frame eff trampoline with
    | .ok cont => trampoline cont
    | .error e => .error e

/-- Top-level entry: build a fresh frame and trampoline it to halt. -/
def applyMessage (msg : Message) (env : Environment) :
    Except Exception Evm :=
  trampoline (Evm.fresh msg env)

end Evm.SpuriousDragon.Vm.Effect
