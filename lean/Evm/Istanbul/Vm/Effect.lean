/-
  Evm.Istanbul.Vm.Effect — yield-based execution for Istanbul.

  Strict delta on Petersburg. Istanbul adds two opcodes (CHAINID,
  SELFBALANCE), re-prices three (SLOAD/BALANCE/EXTCODEHASH per
  EIP-1884), rewrites SSTORE per EIP-2200, and registers BLAKE2F
  (EIP-152) at precompile address 0x09.

  EELS reference: `forks/istanbul/vm/instructions/__init__.py` for
  the dispatch additions; per-opcode references in
  `Evm.Istanbul.Vm.Instructions.*`.

  EIPs introduced:
    * EIP-152  BLAKE2F precompile (0x09)
    * EIP-1108 bn256 re-pricing (gas only; affects precompile costs)
    * EIP-1344 CHAINID opcode (0x46)
    * EIP-1884 SLOAD 200→800, BALANCE 400→700, EXTCODEHASH 400→700;
               SELFBALANCE opcode (0x47)
    * EIP-2028 calldata gas non-zero 68→16 (intrinsic; in Fork.lean)
    * EIP-2200 net SSTORE metering (revised from EIP-1283)

  All the gas-affecting opcodes are routed through pure (or
  pre-charge-then-yield) handlers in Step1, so the inherited
  Petersburg trampoline doesn't need to know about the new prices.
  Precompile lookup in the trampoline uses Istanbul's table.
-/

import Evm.Petersburg.Vm.Effect
import Evm.Istanbul.Vm.Gas
import Evm.Istanbul.Vm.Instructions.Block
import Evm.Istanbul.Vm.Instructions.Environment
import Evm.Istanbul.Vm.Instructions.Storage
import Evm.Istanbul.Vm.PrecompiledContracts

namespace Evm.Istanbul.Vm.Effect

open Evm.Frontier (Account)
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions
open Evm.Byzantium.Vm.Effect (StepResult Step CallKind YieldEffect liftPure
                                addrToU256 u256ToAddr mergeChild)
-- See note in Constantinople/Vm/Effect.lean. Istanbul doesn't define
-- new yield generators that need `maxCallDepth`, but pull in if added.

/-- 0x31 BALANCE at EIP-1884 pricing (400 → 700). Implemented inline
    as a pure handler so we don't need to re-thread Istanbul gas
    through the trampoline's `.balance` arm. -/
def doBalance : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Evm.Istanbul.Vm.Gas.balance
  let (addrW, s) ← Stack.pop evm.stack
  let addr := u256ToAddr addrW
  let bal := evm.env.state.getBalance addr
  let s ← Stack.push s bal
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- Single-step dispatch for Istanbul. Intercepts the new + re-priced
    opcodes; everything else falls through to Petersburg. -/
def step1 (evm : Evm) : StepResult :=
  if evm.halted then .halt evm evm.output
  else if evm.pc ≥ evm.message.code.size then
    .halt { evm with halted := true } evm.output
  else
    let op := evm.message.code.get! evm.pc
    match op.toNat with
    | 0x31 => liftPure doBalance evm                                        -- EIP-1884
    | 0x3f => liftPure Evm.Istanbul.Vm.Instructions.extcodehash evm         -- EIP-1884
    | 0x46 => liftPure Evm.Istanbul.Vm.Instructions.chainid evm             -- EIP-1344
    | 0x47 => liftPure Evm.Istanbul.Vm.Instructions.selfbalance evm         -- EIP-1884
    | 0x54 => liftPure Evm.Istanbul.Vm.Instructions.sload evm               -- EIP-1884
    | 0x55 => liftPure Evm.Istanbul.Vm.Instructions.sstore evm              -- EIP-2200
    | _    => Evm.Petersburg.Vm.Effect.step1 evm

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
    Evm.Frontier.Vm.Call.resume (Evm.Frontier.Vm.Call.Rules.ofOrd 8) frame subMsg.currentTarget
      retOff retLen
      (Evm.Frontier.Vm.Call.runChild (fun _ => Evm.Frontier.Vm.Call.precompiles 8) frame subMsg code stateForSub runSub)
  | .createLike subMsg newAddr stateForSub _ _ _ _ _ _ _ =>
    -- EELS process_create_message + incorporate_child_* (Evm.Frontier.Vm.Create.resume).
    Evm.Frontier.Vm.Create.resume (Evm.Frontier.Vm.Create.Rules.ofOrd 8) frame newAddr
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

/-- Trampoline — yield discharge (`handleYield` above) same as
    Petersburg's, but the precompile lookup uses Istanbul's table
    (which adds BLAKE2F at 0x09). The `.sload`, `.balance`, and
    `.sstore` yield arms are dead code at Istanbul because step1
    routes those opcodes through pure handlers above. -/
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

end Evm.Istanbul.Vm.Effect
