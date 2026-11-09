/-
  Evm.Frontier.Vm.Effect — yield-based execution model.

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
import Evm.Frontier.Vm.Create
import Evm.Frontier.Vm.Call

namespace Evm.Frontier.Vm.Effect

open Evm.Frontier (Account)
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

/-! ## Local helpers (mirror Interpreter.lean's privates) -/

def addrToU256 (a : Evm.Address) : Evm.U256 :=
  Evm.U256.ofNat a.toNat

def u256ToAddr (x : Evm.U256) : Evm.Address :=
  Evm.Address.ofNat x.toNat

def maxCallDepth : Nat := 1024

/-! ## Yield effects -/

/-- Tag for the call-family kind, used by resume to push the right
    success/failure indicator and merge state correctly. -/
inductive CallKind where
  | call
  | callcode
  deriving Inhabited, DecidableEq

/-- A point in execution where the frame needs to coordinate with the
    world. Two flavours: structural yields (CALL/CREATE that spawn
    sub-frames) and state yields (SLOAD/SSTORE/etc. that read or
    write the world's state). The trampoline is the single point
    where state is touched. -/
inductive YieldEffect where
  -- Structural yields (sub-frame setup)
  /-- CALL family (`Evm.Frontier.Vm.Call`): the child's message, the address whose
      precompile runs (`none` when EIP-7702 disabled precompiles), the child's world, the
      caller's gas and memory after the charge, the output range, the caller's stack and
      pc. -/
  | callLike     (kind : CallKind) (subMsg : Message) (code : Option Evm.Address)
                 (stateForSub : Evm.Frontier.State)
                 (gasLeftPostCharge : Nat) (mem : Memory)
                 (retOff retLen : Nat) (stack : Stack)
                 (pc : Nat)
  | createLike   (subMsg : Message) (newAddr : Evm.Address)
                 (stateForSub : Evm.Frontier.State)
                 (gasLeftPostCharge : Nat) (mem : Memory)
                 (stack : Stack) (pc : Nat) (sender : Evm.Address)
                 (senderAccNonce : Nat) (value : Evm.U256)

  -- State yields (atomic state operations)
  /-- SLOAD: read storage slot of `evm.message.currentTarget`. -/
  | sload          (slot : Evm.U256)
  /-- SSTORE: write `value` to `evm.message.currentTarget[key]`.
      Trampoline performs the write and also returns the
      pre-write value via `Response.sstoreOld` so the resume
      step can compute Frontier's refund schedule. -/
  | sstore         (key : Evm.U256) (value : Evm.U256)
  /-- BALANCE: read balance of `addr`. -/
  | balance        (addr : Evm.Address)
  /-- EXTCODESIZE: read deployed-code size of `addr`. -/
  | extcodesize    (addr : Evm.Address)
  /-- EXTCODECOPY: copy a slice of `addr`'s code into memory.
      Trampoline performs the copy and acks. -/
  | extcodecopy    (addr : Evm.Address) (memOff codeOff size : Nat)
  /-- BLOCKHASH: read hash of block `n` from `env.blockHashes`. -/
  | blockhash      (n : Nat)
  /-- LOG: emit a log record. Trampoline appends to `env.logs`. -/
  | logEmit        (record : Log)
  /-- SELFDESTRUCT: queue `evm.message.currentTarget` for deletion,
      transfer its balance to `beneficiary`. Trampoline performs
      the state side-effects and acks. -/
  | selfdestruct   (beneficiary : Evm.Address)
  deriving Inhabited

/-- State yields are resolved in place from the frame's own `env`
    (`handleYield` never consults its `runSub` callback for them);
    structural yields and SELFDESTRUCT spawn sub-frames / end the
    frame and stay with the trampoline. -/
def YieldEffect.isState : YieldEffect → Bool
  | .sload _ | .sstore _ _ | .balance _ | .extcodesize _
  | .extcodecopy _ _ _ _ | .blockhash _ | .logEmit _ => true
  | _ => false

/-- Environment's response to a yield. First-order sum (not
    dependently indexed by `YieldEffect`) so pattern-matching in
    `resume` stays plain. -/
inductive YieldResponse where
  /-- For SLOAD / BALANCE: a 256-bit value. -/
  | u256        (v : Evm.U256)
  /-- For EXTCODESIZE: a Nat. -/
  | nat         (n : Nat)
  /-- For BLOCKHASH: a 32-byte hash. -/
  | hash        (h : Evm.Hash32)
  /-- For EXTCODECOPY / LOG / SELFDESTRUCT: acknowledgment, no payload. -/
  | ack
  /-- For SSTORE: the pre-write value, needed to compute cost / refund. -/
  | sstoreOld   (oldValue : Evm.U256)
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

def pop7 (s : Stack) :
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

/-! ## CALL / CALLCODE / CREATE — yield variants -/

/-- 0xf1 CALL (EELS `call`) — `Evm.Frontier.Vm.Call.opcode` at this fork's rules: the pops, the static
    check, the memory charge, then `Call.start`; the child's run and its end are the
    `.callLike` arm (`Call.resume`). -/
def doCall (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Call.opcode (Evm.Frontier.Vm.Call.Rules.ofOrd 0) .call evm (.error evm) .continue
    (fun p m c st ro rl => .yield p (.callLike .call m c st p.gasLeft p.memory ro rl p.stack p.pc))

/-- 0xf2 CALLCODE (EELS `callcode`) — `Evm.Frontier.Vm.Call.opcode` at this fork's rules: the pops, the static
    check, the memory charge, then `Call.start`; the child's run and its end are the
    `.callLike` arm (`Call.resume`). -/
def doCallcode (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Call.opcode (Evm.Frontier.Vm.Call.Rules.ofOrd 0) .callcode evm (.error evm) .continue
    (fun p m c st ro rl => .yield p (.callLike .callcode m c st p.gasLeft p.memory ro rl p.stack p.pc))

/-- 0xf0 CREATE — deploy a new contract.

    EELS reference: `create` in `forks/frontier/vm/instructions/system.py`
    (line 44). Three exit paths in EELS:

      a. **fail-fast** (line 85): `balance < endowment ∨ nonce overflow
         ∨ depth+1 > limit` — push 0, refund `create_message_gas`
         (the gas that would have been forwarded).
      b. **address collision** (line 92): contract address already has
         code/nonce/storage — bump sender's nonce, push 0, and the
         forwarded gas is LOST (EELS moved `gas_left` into
         `create_message_gas` before the branch and never refunds it
         here, so the parent continues with 0 gas).
      c. **happy path** (line 97): bump sender nonce, build child
         message, call `process_create_message`, merge result via
         `incorporate_child_on_{success,error}`.

    `process_create_message` (interpreter.py line 138) wraps the
    sub-frame run with snapshot/restore; on success it charges
    `200 * #bytes` for code deposit (Frontier: if charge fails,
    output is zeroed but gas is preserved and tx succeeds with
    empty code; Homestead onward reverts).

    Lean structure: every fork's CREATE/CREATE2 is `Evm.Frontier.Vm.Create.opcode`
    (the clauses above, by fork rules) up to the yield point; the `.createLike` arm of
    `handleYield` is `Create.resume`, the post-sub-frame merge. -/
def doCreate (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Create.opcode (Evm.Frontier.Vm.Create.Rules.ofOrd 0) false false evm (.error evm) .continue
    (fun p m st snd n v => .yield p (.createLike m m.currentTarget st p.gasLeft p.memory p.stack p.pc snd n v))

/-! ## State-yielding handlers

    These replace the previous `liftPure Instructions.<op>` entries
    in `step1`. The frame at yield has already charged gas and
    popped args; the trampoline reads/writes state and resumes via
    the corresponding `resume*` function. -/

/-- 0x54 SLOAD — charge gas, pop slot, yield with the slot. -/
def doSload (evm : Evm) : StepResult :=
  match Gas.charge evm.gasLeft Gas.sLoad with
  | .error e => .error evm e
  | .ok gasLeft =>
    match Stack.pop evm.stack with
    | .error e => .error evm e
    | .ok (key, s) =>
      .yield { evm with gasLeft := gasLeft, stack := s } (.sload key)

/-- 0x55 SSTORE — pop both args, yield. Gas cost is determined
    after the response carries the pre-write value. -/
def doSstore (evm : Evm) : StepResult :=
  if evm.message.isStatic then .error evm .writeInStaticContext
  else
  match Stack.pop2 evm.stack with
  | .error e => .error evm e
  | .ok (key, value, s) =>
    .yield { evm with stack := s } (.sstore key value)

/-- 0x31 BALANCE — charge gas, pop addr, yield. -/
def doBalance (evm : Evm) : StepResult :=
  match Gas.charge evm.gasLeft Gas.balance with
  | .error e => .error evm e
  | .ok gasLeft =>
    match Stack.pop evm.stack with
    | .error e => .error evm e
    | .ok (addrW, s) =>
      .yield { evm with gasLeft := gasLeft, stack := s }
             (.balance (u256ToAddr addrW))

/-- 0x3b EXTCODESIZE — charge gas, pop addr, yield. -/
def doExtcodesize (evm : Evm) : StepResult :=
  match Gas.charge evm.gasLeft Gas.extCode with
  | .error e => .error evm e
  | .ok gasLeft =>
    match Stack.pop evm.stack with
    | .error e => .error evm e
    | .ok (addrW, s) =>
      .yield { evm with gasLeft := gasLeft, stack := s }
             (.extcodesize (u256ToAddr addrW))

/-- 0x3c EXTCODECOPY — pops 4, charges gas + memory expansion + copy,
    yields with the work the trampoline must do. -/
def doExtcodecopy (evm : Evm) : StepResult :=
  match Stack.pop evm.stack with
  | .error e => .error evm e
  | .ok (addrW, s) =>
  match Stack.pop3 s with
  | .error e => .error evm e
  | .ok (memOff, codeOff, size, s) =>
  let memOffN  := memOff.toNat
  let sizeN    := size.toNat
  match chargeMemory evm.gasLeft evm.memory memOffN sizeN with
  | .error e => .error evm e
  | .ok (gasLeft, mem) =>
  let copyCost := Gas.extCode + Gas.copy * ((sizeN + 31) / 32)
  match Gas.charge gasLeft copyCost with
  | .error e => .error evm e
  | .ok gasLeft =>
    .yield { evm with gasLeft := gasLeft, memory := mem, stack := s }
           (.extcodecopy (u256ToAddr addrW) memOffN codeOff.toNat sizeN)

/-- 0x40 BLOCKHASH — charge gas, pop n, yield. -/
def doBlockhash (evm : Evm) : StepResult :=
  match Gas.charge evm.gasLeft Gas.blockHash with
  | .error e => .error evm e
  | .ok gasLeft =>
    match Stack.pop evm.stack with
    | .error e => .error evm e
    | .ok (n, s) =>
      .yield { evm with gasLeft := gasLeft, stack := s }
             (.blockhash n.toNat)

/-- 0xa0..0xa4 LOG0..LOG4 — yields a Log record. -/
def popTopicsAux (s : Stack) : Nat → Except Exception (List Evm.U256 × Stack)
  | 0       => return ([], s)
  | k + 1 => do
    let (t, s')  ← Stack.pop s
    let (ts, s'') ← popTopicsAux s' k
    return (t :: ts, s'')

def doLog (n : Nat) (evm : Evm) : StepResult :=
  if evm.message.isStatic then
    .error evm .writeInStaticContext
  else
  match Stack.pop2 evm.stack with
  | .error e => .error evm e
  | .ok (offset, len, s) =>
  match popTopicsAux s n with
  | .error e => .error evm e
  | .ok (topics, s) =>
    let off  := offset.toNat
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
      .yield { evm with gasLeft := gasLeft, memory := mem, stack := s }
             (.logEmit entry)

/-- 0xff SELFDESTRUCT — yield with beneficiary; trampoline applies
    the balance transfer, queues for deletion, and updates refund.

    EELS reference: `selfdestruct` in
    `forks/frontier/vm/instructions/system.py` line 345. The full
    semantics live in the trampoline handler (search for
    `.selfdestruct` near the trampoline's match clauses). EELS
    sequence (matched by Lean's handler):

      1. Pop beneficiary (masked to 20 bytes).
      2. Charge `GasCosts.ZERO` (line 372).
      3. Refund `REFUND_SELF_DESTRUCT` iff `originator` not already in
         `accounts_to_delete` chain (EELS lines 363-370 walk parents;
         Lean reads from the shared-env `selfDestructSet` which is
         already merged across the call chain — see the comment in
         `REPLAY.md` about the per-frame→shared-env refactor).
      4. Transfer originator's balance to beneficiary (line 383).
      5. Zero originator's balance (line 391) — must come AFTER (4)
         so beneficiary=self ends up at 0, not 2×balance.
      6. Add originator to `accounts_to_delete` (line 394).
      7. Halt the frame (line 397).

    The `isStatic` guard here belongs to Byzantium (EIP-214), which
    Frontier never raises on — kept as a no-op cost so the same
    code is the Byzantium delta. -/
def doSelfdestruct (evm : Evm) : StepResult :=
  if evm.message.isStatic then
    .error evm .writeInStaticContext
  else
  match Stack.pop evm.stack with
  | .error e => .error evm e
  | .ok (beneficiaryW, _) =>
    .yield evm (.selfdestruct (u256ToAddr beneficiaryW))

/-! ## Resume functions for state yields

    Public (not `private`): these are the per-terminator /
    per-state-yield semantic units the IR trampoline binds to and the
    Spec-layer refinement theorems quantify over. -/

def resumeSload (frame : Evm) (value : Evm.U256) :
    Except Exception Evm := do
  let s ← Stack.push frame.stack value
  return { frame with stack := s, pc := frame.pc + 1 }

def resumeSstore (frame : Evm) (value oldValue : Evm.U256) :
    Except Exception Evm := do
  let cost := if oldValue = (0 : Evm.U256) ∧ value ≠ (0 : Evm.U256)
              then Gas.sSet else Gas.sReset
  let gasLeft ← Gas.charge frame.gasLeft cost
  let refundDelta : Nat :=
    if oldValue ≠ (0 : Evm.U256) ∧ value = (0 : Evm.U256) then
      Gas.sClearRefund
    else 0
  return { frame with
    gasLeft := gasLeft,
    env := { frame.env with
      refundCounter := frame.env.refundCounter + refundDelta },
    pc := frame.pc + 1 }

def resumeBalance (frame : Evm) (bal : Evm.U256) :
    Except Exception Evm := do
  let s ← Stack.push frame.stack bal
  return { frame with stack := s, pc := frame.pc + 1 }

def resumeExtcodesize (frame : Evm) (size : Nat) :
    Except Exception Evm := do
  let s ← Stack.push frame.stack (Evm.U256.ofNat size)
  return { frame with stack := s, pc := frame.pc + 1 }

/-- EXTCODECOPY's resume is just pc-advance; the trampoline already
    wrote the code bytes into the frame's memory at yield time. -/
def resumeExtcodecopy (frame : Evm) : Except Exception Evm := do
  return { frame with pc := frame.pc + 1 }

def resumeBlockhash (frame : Evm) (h : Evm.Hash32) :
    Except Exception Evm := do
  -- Hash32 is BitVec 256, the same width as U256.
  let s ← Stack.push frame.stack h
  return { frame with stack := s, pc := frame.pc + 1 }

/-- LOG / SELFDESTRUCT resume: just advance pc. SELFDESTRUCT also
    halts. -/
def resumeLog (frame : Evm) : Except Exception Evm := do
  return { frame with pc := frame.pc + 1 }

def resumeSelfdestruct (frame : Evm) : Except Exception Evm := do
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
    | 0x0a => liftPure Instructions.exp evm
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
    | 0x31 => doBalance evm
    | 0x32 => liftPure Instructions.origin evm
    | 0x33 => liftPure Instructions.caller evm
    | 0x34 => liftPure Instructions.callvalue evm
    | 0x35 => liftPure Instructions.calldataload evm
    | 0x36 => liftPure Instructions.calldatasize evm
    | 0x37 => liftPure Instructions.calldatacopy evm
    | 0x38 => liftPure Instructions.codesize evm
    | 0x39 => liftPure Instructions.codecopy evm
    | 0x3a => liftPure Instructions.gasprice evm
    | 0x3b => doExtcodesize evm
    | 0x3c => doExtcodecopy evm
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
    | 0x54 => doSload evm
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
    | 0xff => liftPure Evm.Frontier.Vm.selfdestruct evm
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
def mergeChild (parent child : Evm) : Evm :=
  { parent with env := child.env }

/-- Process ONE yield: spawn the sub-frame (via the supplied
    `runSub` callback) or perform the state operation, run the
    matching resume function, and return the parent's continuation
    frame.

    This is the trampoline's entire per-yield semantics as a TOTAL
    function — `trampoline` below is just the recursive knot tied
    around it. Extracted so that (a) the IR trampoline
    (`Evm.IR.Trampoline`) binds the SAME definition rather than
    re-encoding the math, and (b) Spec-layer refinement theorems can
    quantify over it (a `partial def` is opaque to the kernel; this
    isn't). -/
def handleYield (frame : Evm) (eff : YieldEffect)
    (runSub : Evm → Except Exception Evm) : Except Exception Evm :=
  match eff with
  | .callLike _ subMsg code stateForSub _ _ retOff retLen _ _ =>
    -- EELS generic_call's end, process_message, execute_code, incorporate_child_*
    -- (Evm.Frontier.Vm.Call.resume / runChild).
    Evm.Frontier.Vm.Call.resume (Evm.Frontier.Vm.Call.Rules.ofOrd 0) frame subMsg.currentTarget
      retOff retLen
      (Evm.Frontier.Vm.Call.runChild (fun _ => Evm.Frontier.Vm.Call.precompiles 0) frame subMsg code stateForSub runSub)
  | .createLike subMsg newAddr stateForSub _ _ _ _ _ _ _ =>
    -- EELS process_create_message + incorporate_child_* (Evm.Frontier.Vm.Create.resume).
    Evm.Frontier.Vm.Create.resume (Evm.Frontier.Vm.Create.Rules.ofOrd 0) frame newAddr
      (runSub (Evm.Frontier.Vm.Create.child frame subMsg stateForSub))

  -- State yields: consult / mutate `frame.env.state`, build the
  -- response, resume.
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
    -- Indexing mirrors `Instructions.blockhash`: blockHashes has
    -- the last 256 ancestor hashes; idx = len - (current - n).
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
    -- EELS `selfdestruct` (forks/frontier/vm/instructions/system.py
    -- lines 383-391):
    --   set_balance(beneficiary, beneficiary_bal + originator_bal)
    --   set_balance(originator, 0)
    -- Order matters when beneficiary == originator (otherwise the
    -- self-transfer wouldn't end at 0). `addBalance` is `+=` so
    -- the result matches EELS' explicit set-to-sum form.
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

/-- `runFrame` with state-yield resolution folded in. Structural
    yields (CALL/CREATE/SELFDESTRUCT) still surface as `.yield` for
    the trampoline, but state yields (SLOAD/BALANCE/…) are resolved
    on the spot by the SAME `handleYield` the trampoline uses — for
    those the `runSub` callback is unreachable, so it errors loudly.
    One fuel tick per opcode, yield-resuming or not.

    This is the run the IR chunk-soundness theorems quantify over:
    a chunk may contain state ops mid-stream, which `runFrame`
    alone would stop at. By construction `runFrameR` computes
    exactly the `runFrame`-then-`handleYield`-then-resume
    composition the trampoline performs for state yields. -/
def runFrameR : Nat → Evm → Step
  | 0,      evm => .error evm .outOfGas
  | fuel+1, evm =>
    match step1 evm with
    | .continue evm'      => runFrameR fuel evm'
    | .yield frame eff    =>
      if eff.isState then
        match handleYield frame eff (fun _ => .error .outOfGas) with
        | .ok cont => runFrameR fuel cont
        | .error e => .error frame e
      else .yield frame eff
    | .halt evm' output   => .halt evm' output
    | .error evm' e       => .error evm' e

/-- The trampoline: orchestrates `runFrame`, handles each yield via
    `handleYield` (spawning sub-frames by recursively trampolining
    them), until the top frame halts or errors.

    Fuel: `evm.gasLeft + 1` steps per `runFrame` (every fork's trampoline and
    `IR.runProgram` alike). A step that continues charges at least 1 gas, so the frame
    halts, errors or yields before the fuel is gone. Until 2026-11-09 the fuel was a fixed
    `2^24`, which a London+ frame (block gas limits above 2^24) could exhaust: a spurious
    out-of-gas. -/
partial def trampoline (evm : Evm) : Except Exception Evm :=
  match runFrame (evm.gasLeft + 1) evm with
  | .halt finalEvm _ => .ok finalEvm
  | .error _ e       => .error e
  | .yield frame eff =>
    match handleYield frame eff trampoline with
    | .ok cont => trampoline cont
    | .error e => .error e

/-- Top-level entry: build a fresh frame and trampoline it to halt.

    EELS reference: `process_message` in
    `forks/frontier/vm/interpreter.py` line 181. Unlike EELS, this
    function does NOT do `touch_account` or `move_ether` — those are
    the caller's responsibility:

      * `Fork.processTransaction` (CALL branch) and `doCall` /
        `doCallcode` in `Effect.lean` do the touch + value transfer
        on the state they pass in via `env.state` / `Message.code`.
      * The depth limit check (EELS line 197) is enforced by callers
        via `failFast` rather than checked here. (For tx-level entry
        the depth is always 0 so the check is trivially true.)
      * Snapshot / rollback (EELS lines 219 / 244) is implicit:
        Lean's resume functions either adopt `subEvm.env` (success)
        or discard it (failure) — pure functional state, no
        in-place mutation. -/
def applyMessage (msg : Message) (env : Environment) :
    Except Exception Evm :=
  trampoline (Evm.fresh msg env)

end Evm.Frontier.Vm.Effect
