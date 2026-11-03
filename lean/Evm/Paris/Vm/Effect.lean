/-
  Evm.Paris.Vm.Effect — yield-based execution for Paris (the Merge).

  EELS reference: ethereum/forks/paris/vm/instructions/block.py
  (function `prev_randao`, line 168). The only EVM-level delta from
  Byzantium / London is EIP-4399:

    * 0x44 DIFFICULTY is renamed PREVRANDAO. The opcode number is
      unchanged; the gas cost is unchanged (base = 2); the value
      pushed is now `block_env.prev_randao` (a Hash32 from the
      consensus layer) reinterpreted as a U256.

  Every other opcode behaves exactly as in Byzantium, so we delegate
  to `Evm.Byzantium.Vm.Effect.step1` for the entire dispatch table
  and only intercept 0x44.

  EELS Paris does not introduce any new opcodes; its `vm/instructions/`
  is structurally identical to London / Berlin / Byzantium except
  for the rename of `difficulty` → `prev_randao` in the dispatch
  table at `forks/paris/vm/instructions/__init__.py`.

  The trampoline is identical in shape to Byzantium's but pinned to
  Paris's `step1` so PREVRANDAO is honoured in every sub-frame.
-/

import Evm.Byzantium.Vm.Effect
import Evm.London.Vm.Effect
import Evm.Istanbul.Vm.PrecompiledContracts

namespace Evm.Paris.Vm.Effect

open Evm.Frontier (Account)
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions
open Evm.Byzantium.Vm.Effect (StepResult Step CallKind YieldEffect liftPure)

/-- EIP-4399 PREVRANDAO (0x44, formerly DIFFICULTY). Gas cost = base = 2.
    EELS `forks/paris/vm/instructions/block.py` `prev_randao`, line 168.

    Semantics: push `env.prevRandao` (a `Hash32`, interpreted as a
    big-endian U256) onto the stack. EELS does
    `U256.from_be_bytes(evm.message.block_env.prev_randao)`; here
    `Hash32 = U256 = BitVec 256`, so the reinterpretation is a no-op. -/
def prevRandao : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.base
  let s ← Stack.push evm.stack evm.env.prevRandao
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- Single-step dispatch for Paris. Intercepts 0x44 (PREVRANDAO) and
    falls through to Byzantium for everything else (the Merge does not
    introduce or remove any EVM opcodes). -/
def step1 (evm : Evm) : StepResult :=
  if evm.halted then .halt evm evm.output
  else if evm.pc ≥ evm.message.code.size then
    .halt { evm with halted := true } evm.output
  else
    let op := evm.message.code.get! evm.pc
    match op.toNat with
    | 0x44 => liftPure prevRandao evm    -- EIP-4399
    -- Fall through to LONDON (not Byzantium) — Paris inherits
    -- Berlin's EIP-2929 warm/cold opcode pricing and London's
    -- EIP-3198 BASEFEE / EIP-3529 refund-and-SELFDESTRUCT deltas.
    -- The previous Byzantium fall-through silently skipped all of
    -- those, which is why Shanghai/Cancun SSTOREs were under-charged
    -- by EIP-2929's 2100-gas cold surcharge.
    | _    => Evm.London.Vm.Effect.step1 evm

/-- Run-until-yield loop, identical in shape to Byzantium's but pinned
    to Paris's `step1`. -/
def runFrame : Nat → Evm → Step
  | 0,      evm => .error evm .outOfGas
  | fuel+1, evm =>
    match step1 evm with
    | .continue evm'      => runFrame fuel evm'
    | .yield evm' eff     => .yield evm' eff
    | .halt evm' output   => .halt evm' output
    | .error evm' e       => .error evm' e

/-- Merge a successful sub-frame back into the parent. -/
private def mergeChild (parent child : Evm) : Evm :=
  { parent with env := child.env }

private def addrToU256 (a : Evm.Address) : Evm.U256 :=
  Evm.U256.ofNat a.toNat

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
    Evm.Frontier.Vm.Call.resume (Evm.Frontier.Vm.Call.Rules.ofOrd 14) frame subMsg.currentTarget
      retOff retLen
      (Evm.Frontier.Vm.Call.runChild (fun _ => Evm.Frontier.Vm.Call.precompiles 14) frame subMsg code stateForSub runSub)
  | .createLike subMsg newAddr stateForSub _ _ _ _ _ _ _ =>
    -- EELS process_create_message + incorporate_child_* (Evm.Frontier.Vm.Create.resume).
    Evm.Frontier.Vm.Create.resume (Evm.Frontier.Vm.Create.Rules.ofOrd 14) frame newAddr
      (runSub (Evm.Frontier.Vm.Create.child frame subMsg stateForSub))
  | .sload key =>
    let v := frame.env.state.getStorage frame.message.currentTarget key
    match Stack.push frame.stack v with
    | .error e => .error e
    | .ok s => .ok { frame with stack := s, pc := frame.pc + 1 }
  | .sstore key value =>
    let addr := frame.message.currentTarget
    let oldValue := frame.env.state.getStorage addr key
    let cost := if oldValue = (0 : Evm.U256) ∧ value ≠ (0 : Evm.U256) then Gas.sSet else Gas.sReset
    match Gas.charge frame.gasLeft cost with
    | .error e => .error e
    | .ok gasLeft =>
      let refundDelta : Nat :=
        if oldValue ≠ (0 : Evm.U256) ∧ value = (0 : Evm.U256) then Gas.sClearRefund else 0
      let stateAfter := frame.env.state.setStorage addr key value
      .ok
        { frame with
          gasLeft := gasLeft,
          env := { frame.env with
            state := stateAfter,
            refundCounter := frame.env.refundCounter + refundDelta },
          pc := frame.pc + 1 }
  | .balance addr =>
    let bal := frame.env.state.getBalance addr
    match Stack.push frame.stack bal with
    | .error e => .error e
    | .ok s => .ok { frame with stack := s, pc := frame.pc + 1 }
  | .extcodesize addr =>
    let code := (frame.env.state.getAccount addr).code
    match Stack.push frame.stack (Evm.U256.ofNat code.size) with
    | .error e => .error e
    | .ok s => .ok { frame with stack := s, pc := frame.pc + 1 }
  | .extcodecopy addr memOff codeOff size =>
    let code := (frame.env.state.getAccount addr).code
    let bytes := Evm.Bytes.sliceZeroPad code codeOff size
    let mem' := Memory.write frame.memory memOff bytes
    .ok { frame with memory := mem', pc := frame.pc + 1 }
  | .blockhash n =>
    let curN := frame.env.number
    let h : Evm.Hash32 :=
      if n ≥ curN ∨ curN - n > 256 then 0
      else
        let len := frame.env.blockHashes.length
        let idx := len - (curN - n)
        frame.env.blockHashes[idx]?.getD 0
    match Stack.push frame.stack h with
    | .error e => .error e
    | .ok s => .ok { frame with stack := s, pc := frame.pc + 1 }
  | .logEmit entry =>
    .ok
      { frame with
        env := { frame.env with logs := frame.env.logs ++ [entry] },
        pc := frame.pc + 1 }
  | .selfdestruct beneficiary =>
    let self := frame.message.currentTarget
    let balance := frame.env.state.getBalance self
    let st  := frame.env.state.addBalance beneficiary balance
    let st  := st.setAccount self { (st.getAccount self) with balance := 0 }
    let firstTime := ¬ frame.env.selfDestructSet.contains self
    -- EIP-3529 (London+, inherited by Paris): SELFDESTRUCT 24000
    -- refund removed.
    let refund : Nat := 0
    let _ := firstTime
    .ok
      { frame with
        halted := true,
        env := { frame.env with
          state := st,
          selfDestructSet :=
            if firstTime then frame.env.selfDestructSet ++ [self]
            else frame.env.selfDestructSet,
          refundCounter := frame.env.refundCounter + refund } }

/-- The trampoline mirrors Byzantium's exactly (yields discharged
    via `handleYield` above); the only reason we re-emit it here is
    so that sub-frame recursion lands in `Paris.Vm.Effect.runFrame`
    (and therefore Paris's `step1` with PREVRANDAO) rather than
    Byzantium's. EELS does the same: each fork's `vm/interpreter.py`
    re-implements `process_message` against its own opcode
    dispatch. -/
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

end Evm.Paris.Vm.Effect
