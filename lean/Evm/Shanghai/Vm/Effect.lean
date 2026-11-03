/-
  Evm.Shanghai.Vm.Effect — yield-based execution for Shanghai.

  Strict delta on Paris. Three opcode-layer changes:
    * EIP-3855 PUSH0 (0x5f) — new opcode, 2 gas, pushes 0.
    * EIP-3860 init-code size cap + 2-gas/word surcharge — applies to
      CREATE (0xf0) and CREATE2 (0xf5). Tx-level CREATE intrinsic
      gets the same surcharge in `Fork.lean`.
    * EIP-3651 warm COINBASE — tx-level only (in `Fork.lean`,
      `processTransaction` seeds the touched set with coinbase).
    * EIP-4895 withdrawals — block-level only (in `Fork.lean`'s
      `applyBlock`, processed after txs).

  All other opcodes inherit from Paris (which itself just renames
  DIFFICULTY → PREVRANDAO at 0x44).

  EELS reference: `forks/shanghai/vm/instructions/__init__.py` for
  the dispatch additions; per-opcode references at definition sites.
-/

import Evm.Paris.Vm.Effect
import Evm.Petersburg.Utils.Address

namespace Evm.Shanghai.Vm.Effect

open Evm.Frontier (Account)
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions
open Evm.Byzantium.Vm.Effect (StepResult Step CallKind YieldEffect liftPure
                                addrToU256 u256ToAddr mergeChild)
-- See note in Constantinople/Vm/Effect.lean.

/-! ## EIP-3855 helpers (EIP-3860 lives in `Evm.Frontier.Vm.Create`) -/

/-- EIP-3855 PUSH0 gas: BASE = 2. EELS `forks/shanghai/vm/gas.py` 141. -/
def push0Cost : Nat := Gas.base

/-! ## EIP-3855 PUSH0 -/

def doPush0 (evm : Evm) : StepResult :=
  match Gas.charge evm.gasLeft push0Cost with
  | .error e => .error evm e
  | .ok gasLeft =>
    match Stack.push evm.stack (0 : Evm.U256) with
    | .error e => .error evm e
    | .ok s    => .continue { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-! ## EIP-3860 CREATE / CREATE2 -/

/-- 0xf0 CREATE with the EIP-3860 size cap + per-word surcharge. -/
def doCreate (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Create.opcode (Evm.Frontier.Vm.Create.Rules.ofOrd 15) true false evm (.error evm) .continue
    (fun p m st snd n v => .yield p (.createLike m m.currentTarget st p.gasLeft p.memory p.stack p.pc snd n v))

/-- 0xf5 CREATE2 with EIP-3860 size cap + per-word surcharge. -/
def doCreate2 (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Create.opcode (Evm.Frontier.Vm.Create.Rules.ofOrd 15) true true evm (.error evm) .continue
    (fun p m st snd n v => .yield p (.createLike m m.currentTarget st p.gasLeft p.memory p.stack p.pc snd n v))

/-! ## Step dispatch -/

def step1 (evm : Evm) : StepResult :=
  if evm.halted then .halt evm evm.output
  else if evm.pc ≥ evm.message.code.size then
    .halt { evm with halted := true } evm.output
  else
    let op := evm.message.code.get! evm.pc
    match op.toNat with
    | 0x5f => doPush0 evm                       -- EIP-3855
    | 0xf0 => doCreate evm                      -- EIP-3860 cap+surcharge
    | 0xf5 => doCreate2 evm                     -- EIP-3860 cap+surcharge
    | _    => Evm.Paris.Vm.Effect.step1 evm

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
    Evm.Frontier.Vm.Call.resume (Evm.Frontier.Vm.Call.Rules.ofOrd 15) frame subMsg.currentTarget
      retOff retLen
      (Evm.Frontier.Vm.Call.runChild (fun _ => Evm.Frontier.Vm.Call.precompiles 15) frame subMsg code stateForSub runSub)
  | .createLike subMsg newAddr stateForSub _ _ _ _ _ _ _ =>
    -- EELS process_create_message + incorporate_child_* (Evm.Frontier.Vm.Create.resume).
    Evm.Frontier.Vm.Create.resume (Evm.Frontier.Vm.Create.Rules.ofOrd 15) frame newAddr
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
    -- EIP-3529 (London+, inherited): SELFDESTRUCT 24000 refund removed.
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

/-- Trampoline — yields discharged via `handleYield` above (identical
    body to Paris's), bound to Shanghai's `runFrame` so sub-frames
    see PUSH0 + EIP-3860 CREATEs. -/
partial def trampoline (evm : Evm) : Except Exception Evm :=
  match runFrame (1 <<< 24) evm with
  | .halt finalEvm _ => .ok finalEvm
  | .error _ e       => .error e
  | .yield frame eff =>
    match handleYield frame eff trampoline with
    | .ok cont => trampoline cont
    | .error e => .error e

def applyMessage (msg : Message) (env : Environment) :
    Except Exception Evm :=
  trampoline (Evm.fresh msg env)

end Evm.Shanghai.Vm.Effect
