/-
  Evm.Constantinople.Vm.Effect — yield-based execution for Constantinople.

  Strict Paris-style delta on Byzantium. Constantinople adds five
  opcodes (SHL/SHR/SAR/EXTCODEHASH/CREATE2) plus rewrites SSTORE per
  EIP-1283. All five new opcodes and the SSTORE rewrite are pure-or-
  near-pure handlers that live in `Evm.Constantinople.Vm.Instructions`;
  this module only adds the dispatch in `step1` and the one new yield
  generator `doCreate2`. Everything else falls through to
  `Evm.Byzantium.Vm.Effect.step1`.

  EELS reference: `forks/constantinople/vm/instructions/__init__.py`
  for the dispatch additions; per-opcode references in the respective
  Constantinople `Instructions` files.

  EIPs introduced:
    * EIP-145 (SHL 0x1b / SHR 0x1c / SAR 0x1d) — pure bitwise ops.
    * EIP-1014 (CREATE2 0xf5) — new yield, address from salt + keccak.
    * EIP-1052 (EXTCODEHASH 0x3f) — synchronous state probe.
    * EIP-1283 (SSTORE 0x55, net metering) — reads `originalState` from
      `Environment`. Petersburg overrides 0x55 back to Byzantium's
      simpler schedule.
    * EIP-1234 (block reward 3 → 2 ETH) — handled in `Fork.lean`,
      not here.

  Pattern note: the trampoline body below is a direct copy of
  Byzantium's, bound to *this* fork's `runFrame` so that sub-frame
  recursion uses Constantinople's `step1`. EELS does the same — each
  fork's `vm/interpreter.py` re-emits `process_message` against its
  own dispatch table. (A future refactor could parameterise the
  trampoline by `step1`; current Lean `partial def` ergonomics make
  this awkward.)
-/

import Evm.Byzantium.Vm.Effect
import Evm.Constantinople.Vm.Gas
import Evm.Constantinople.Vm.Instructions.Bitwise
import Evm.Constantinople.Vm.Instructions.Environment
import Evm.Constantinople.Vm.Instructions.Storage
import Evm.Constantinople.Utils.Address

namespace Evm.Constantinople.Vm.Effect

open Evm.Frontier (Account)
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions
open Evm.Byzantium.Vm.Effect (StepResult Step CallKind YieldEffect liftPure
                                addrToU256 u256ToAddr mergeChild)
-- `Evm.Byzantium.Vm.Effect.maxCallDepth` collides with
-- `Evm.Frontier.Vm.Effect.maxCallDepth` (both are `def`s of `1024`).
-- Qualify at use sites with `Byzantium.Vm.Effect.maxCallDepth`.

/-! ## New yield generator -/

/-- 0xf5 CREATE2 — like CREATE but with a salt-derived address.

    EELS reference: `forks/constantinople/vm/instructions/system.py`
    `create2` (the EIP-1014 implementation), gas formula in
    `vm/gas.py` (G_create + keccak-per-word over initcode).

    Reuses the `.createLike` yield variant — sub-frame execution,
    collision handling, and code-deposit are identical to CREATE
    once the address has been computed. -/
def doCreate2 (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Create.opcode (Evm.Frontier.Vm.Create.Rules.ofOrd 6) true true evm (.error evm) .continue
    (fun p m st snd n v => .yield p (.createLike m m.currentTarget st p.gasLeft p.memory p.stack p.pc snd n v))

/-! ## Step dispatch -/

/-- Single-step dispatch for Constantinople. Intercepts the five new
    opcode slots and the SSTORE rewrite; everything else falls through
    to Byzantium's `step1`. -/
def step1 (evm : Evm) : StepResult :=
  if evm.halted then .halt evm evm.output
  else if evm.pc ≥ evm.message.code.size then
    .halt { evm with halted := true } evm.output
  else
    let op := evm.message.code.get! evm.pc
    match op.toNat with
    | 0x1b => liftPure Evm.Constantinople.Vm.Instructions.shl evm           -- EIP-145
    | 0x1c => liftPure Evm.Constantinople.Vm.Instructions.shr evm           -- EIP-145
    | 0x1d => liftPure Evm.Constantinople.Vm.Instructions.sar evm           -- EIP-145
    | 0x3f => liftPure Evm.Constantinople.Vm.Instructions.extcodehash evm   -- EIP-1052
    | 0x55 => liftPure Evm.Constantinople.Vm.Instructions.sstore evm        -- EIP-1283
    | 0xf5 => doCreate2 evm                                                 -- EIP-1014
    | _    => Evm.Byzantium.Vm.Effect.step1 evm

def runFrame : Nat → Evm → Step
  | 0,      evm => .error evm .outOfGas
  | fuel+1, evm =>
    match step1 evm with
    | .continue evm'      => runFrame fuel evm'
    | .yield evm' eff     => .yield evm' eff
    | .halt evm' output   => .halt evm' output
    | .error evm' e       => .error evm' e

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
    Evm.Frontier.Vm.Call.resume (Evm.Frontier.Vm.Call.Rules.ofOrd 6) frame subMsg.currentTarget
      retOff retLen
      (Evm.Frontier.Vm.Call.runChild (fun _ => Evm.Frontier.Vm.Call.precompiles 6) frame subMsg code stateForSub runSub)
  | .createLike subMsg newAddr stateForSub _ _ _ _ _ _ _ =>
    -- EELS process_create_message + incorporate_child_* (Evm.Frontier.Vm.Create.resume).
    Evm.Frontier.Vm.Create.resume (Evm.Frontier.Vm.Create.Rules.ofOrd 6) frame newAddr
      (runSub (Evm.Frontier.Vm.Create.child frame subMsg stateForSub))
  | .sload key =>
    let v := frame.env.state.getStorage frame.message.currentTarget key
    match Stack.push frame.stack v with
    | .error e => .error e
    | .ok s => .ok { frame with stack := s, pc := frame.pc + 1 }
  | .sstore key value =>
    -- Constantinople intercepts 0x55 in `step1` as a pure handler
    -- (EIP-1283 net metering), so this arm is dead code on this fork.
    -- Kept structurally because the yield variant is shared across
    -- forks; pre-Constantinople ops that still yield .sstore land here.
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
    let refund    := if firstTime then Gas.selfDestructRefund else 0
    .ok
      { frame with
        halted := true,
        env := { frame.env with
          state := st,
          selfDestructSet :=
            if firstTime then frame.env.selfDestructSet ++ [self]
            else frame.env.selfDestructSet,
          refundCounter := frame.env.refundCounter + refund } }

/-- Trampoline — yield discharge (`handleYield` above) identical to
    Byzantium's, pinned to this fork's `runFrame` so sub-frame
    recursion uses Constantinople's `step1` (and therefore the new
    opcodes + EIP-1283 SSTORE). -/
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

end Evm.Constantinople.Vm.Effect
