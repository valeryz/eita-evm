/-
  Evm.London.Vm.Effect — yield-based execution for London.

  Strict delta on Berlin. London introduces one new opcode and three
  refund-side changes:

    * EIP-3198 BASEFEE (0x48) — pure handler, pushes `block.baseFeePerGas`,
      charges GAS_BASE = 2. Implemented in `Evm.London.Vm.Instructions.baseFee`.
    * EIP-3529 SSTORE clear refund 15000 → 4800. We re-emit SSTORE as a
      London-specific pure handler using a London-tuned EIP-2200 schedule.
      EELS `forks/london/vm/gas.py` line 62 + `vm/instructions/storage.py`
      lines 99-159.
    * EIP-3529 SELFDESTRUCT refund 24000 → 0. We re-emit SELFDESTRUCT
      with the refund-add line dropped. EELS `forks/london/vm/
      instructions/system.py:selfdestruct` lines 470-532.
    * EIP-3541 reject 0xEF-prefix code on deploy — CREATE / CREATE2
      and tx-CREATE refuse the deposit. We intercept the
      `.createLike` success arm in the trampoline. EELS
      `forks/london/vm/interpreter.py:process_create_message` lines
      188-209. The tx-level CREATE rejection lives in `London.Fork`.
    * EIP-3554 difficulty bomb delay — not modelled (we don't model
      the bomb).
    * Max-refund ratio 1/2 → 1/5 — tx-level, applied in
      `London.Fork.processTransaction`.

  Berlin (EIP-2929 warm/cold) is inherited unchanged via the
  fall-through to `Berlin.Vm.Effect.step1`. Berlin already pre-warms
  the new CREATE/CREATE2 address; London adds the EIP-3541 check on
  top in the trampoline.
-/

import Evm.Berlin.Vm.Effect
import Evm.Berlin.Vm.Instructions.Storage
import Evm.London.Vm.Gas
import Evm.London.Vm.Instructions.Block

namespace Evm.London.Vm.Effect

open Evm.Frontier (Account)
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions
open Evm.Byzantium.Vm.Effect (StepResult Step CallKind YieldEffect liftPure
                                addrToU256 u256ToAddr mergeChild)
-- See Constantinople note: qualify `Byzantium.Vm.Effect.maxCallDepth`
-- at use sites to avoid the Frontier-vs-Byzantium ambiguity.

private def isDead (state : Evm.Frontier.State) (addr : Evm.Address) : Bool :=
  if state.accountExists addr then (state.getAccount addr).isEmpty
  else true

/-! ## EIP-3529 SSTORE schedule

    The EIP-2200 dirty-map logic is unchanged from Berlin; the only
    delta is `SSTORE_CLEARS_SCHEDULE = 4800` (was 15000). We re-emit
    the schedule here rather than parameterise Berlin's because the
    refund constant shows up in two arms of the net-metering table
    (the "clear" arm and the "back to original from non-zero" arm).
    EELS `forks/london/vm/gas.py` line 62. -/

/-- EIP-2200 net-gas-metering with EIP-3529's lower clears refund.
    Mirrors `Berlin.Vm.Instructions.Storage.eip2200` with the single
    `sstoreClearsRefund = 4800` substitution. -/
def eip2200London (original current new_ : Evm.U256) : Nat × Nat × Nat :=
  let sstoreSet   := Berlin.Vm.Instructions.Storage.sstoreSet
  let sstoreReset := Berlin.Vm.Instructions.Storage.sstoreReset
  let clearsRef   := London.Vm.Gas.sStoreClearRefund  -- 4800 (was 15000)
  if new_ = current then
    (Berlin.Vm.Gas.warmAccess, 0, 0)
  else if current = original then
    if original = (0 : Evm.U256) then
      (sstoreSet, 0, 0)
    else
      let refundAdd := if new_ = (0 : Evm.U256) then clearsRef else 0
      (sstoreReset, refundAdd, 0)
  else
    let cost := Berlin.Vm.Gas.warmAccess
    let (addClear, subClear) : Nat × Nat :=
      if original ≠ (0 : Evm.U256) then
        if      current = (0 : Evm.U256) then (0, clearsRef)
        else if new_    = (0 : Evm.U256) then (clearsRef, 0)
        else (0, 0)
      else (0, 0)
    let addReset : Nat :=
      if new_ = original then
        if original = (0 : Evm.U256) then
          sstoreSet   - Berlin.Vm.Gas.warmAccess
        else
          sstoreReset - Berlin.Vm.Gas.warmAccess
      else 0
    (cost, addClear + addReset, subClear)

/-- Pure London SSTORE gas + refund: `(cost, newRefundCounter)`.
    Berlin's `sstoreGas` shape with `eip2200London` swapped in. -/
def sstoreGas (refund : Nat) (isCold : Bool)
    (original current new_ : Evm.U256) : Nat × Nat :=
  let (c, addR, subR) := eip2200London original current new_
  let surcharge := if isCold then Berlin.Vm.Gas.sstoreColdSurcharge else 0
  let r1 := refund + addR
  (c + surcharge, if r1 < subR then 0 else r1 - subR)

/-- 0x55 SSTORE — London (EIP-3529 refund). Pure handler in step1
    (no yield). Same shape as `Berlin.Vm.Effect.doSstorePure` with
    `eip2200London` swapped in. -/
def doSstoreLondon : Handler := fun evm => do
  if evm.message.isStatic then
    .error .writeInStaticContext
  let (key, value, s) ← Stack.pop2 evm.stack
  -- EIP-2200 sentry, kept by EIP-3529: refuse to run on ≤ 2300
  -- (GAS_CALL_STIPEND) gas left. EELS `forks/london/vm/instructions/
  -- storage.py:sstore`.
  if evm.gasLeft ≤ Gas.callStipend then
    .error .outOfGas
  let addr     := evm.message.currentTarget
  let current  := evm.env.state.getStorage addr key
  let original := Berlin.Vm.Effect.getOriginal evm.env addr key current
  let envOrig  := Berlin.Vm.Effect.cacheOriginal evm.env addr key original
  let isCold   := ¬ Berlin.Vm.Effect.isSlotWarm envOrig addr key
  let (envWarm, _) := Berlin.Vm.Effect.warmSlot envOrig addr key
  let (cost, refundCounter) :=
    sstoreGas envWarm.refundCounter isCold original current value
  let gasLeft ← Gas.charge evm.gasLeft cost
  let stateAfter := evm.env.state.setStorage addr key value
  return { evm with
    gasLeft := gasLeft, stack := s,
    env := { envWarm with state := stateAfter, refundCounter := refundCounter },
    pc := evm.pc + 1 }

/-- 0xff SELFDESTRUCT — London (EIP-3529: refund removed). Pure
    handler; same shape as `Berlin.Vm.Effect.doSelfdestructPure`
    with the `selfDestructRefund` add line dropped. EELS
    `forks/london/vm/instructions/system.py:selfdestruct` lines
    470-532 — no `refund_counter` mutation. -/
def doSelfdestructLondon : Handler := fun evm => do
  if evm.message.isStatic then
    .error .writeInStaticContext
  let (beneficiaryW, _) ← Stack.pop evm.stack
  let beneficiary := u256ToAddr beneficiaryW
  let isCold := ¬ Berlin.Vm.Effect.isAddrWarm evm.env beneficiary
  let self := evm.message.currentTarget
  let balance := evm.env.state.getBalance self
  let newAccountCost : Nat :=
    if balance ≠ (0 : Evm.U256) ∧ isDead evm.env.state beneficiary then
      Gas.newAccount else 0
  let coldSurcharge : Nat :=
    if isCold then Berlin.Vm.Gas.coldAccountAccess else 0
  let gasLeft ← Gas.charge evm.gasLeft
    (Evm.TangerineWhistle.Vm.Gas.selfDestruct + newAccountCost + coldSurcharge)
  let (envWarm, _) := Berlin.Vm.Effect.warmAddr evm.env beneficiary
  -- EELS (berlin|london)/vm/instructions/system.py selfdestruct: the beneficiary is
  -- credited, then `if account_exists_and_is_empty(beneficiary): touched_accounts.add`.
  -- Written in the SpuriousDragon form (`SpuriousDragon.Vm.selfdestruct`, Cancun's
  -- `selfdestructEIP6780`): no zero credit to an ABSENT beneficiary, touch it — the
  -- end-of-tx sweep then leaves the state EELS leaves. Until 2026-10-26 this handler
  -- credited unconditionally and never touched, so a 0-wei SELFDESTRUCT to an absent
  -- account left an empty account the sweep never saw (found deriving cb-selfdestruct,
  -- Evm.CL.EffectSelfdestruct; the CL was right).
  let st := if balance = (0 : Evm.U256) ∧ ¬ envWarm.state.accountExists beneficiary
            then envWarm.state else envWarm.state.addBalance beneficiary balance
  let st := st.setAccount self { (st.getAccount self) with balance := 0 }
  let firstTime := ¬ envWarm.selfDestructSet.contains self
  -- EIP-3529: NO refund counter mutation (was `+= selfDestructRefund`).
  let envTouched := _root_.Evm.SpuriousDragon.Vm.touchAddr envWarm beneficiary
  return { evm with
    gasLeft := gasLeft,
    halted := true,
    env := { envTouched with
      state := st,
      selfDestructSet :=
        if firstTime then envWarm.selfDestructSet ++ [self]
        else envWarm.selfDestructSet } }

/-! ## Step dispatch -/

def step1 (evm : Evm) : StepResult :=
  if evm.halted then .halt evm evm.output
  else if evm.pc ≥ evm.message.code.size then
    .halt { evm with halted := true } evm.output
  else
    let op := evm.message.code.get! evm.pc
    match op.toNat with
    | 0x48 => liftPure _root_.Evm.London.Vm.Instructions.baseFee evm  -- EIP-3198
    | 0x55 => liftPure doSstoreLondon evm                             -- EIP-3529 SSTORE refund
    | 0xff => liftPure doSelfdestructLondon evm                       -- EIP-3529 SELFDESTRUCT refund
    | _    => Evm.Berlin.Vm.Effect.step1 evm

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
    Evm.Frontier.Vm.Call.resume (Evm.Frontier.Vm.Call.Rules.ofOrd 11) frame subMsg.currentTarget
      retOff retLen
      (Evm.Frontier.Vm.Call.runChild (fun _ => Evm.Frontier.Vm.Call.precompiles 11) frame subMsg code stateForSub runSub)
  | .createLike subMsg newAddr stateForSub _ _ _ _ _ _ _ =>
    -- EELS process_create_message + incorporate_child_* (Evm.Frontier.Vm.Create.resume).
    Evm.Frontier.Vm.Create.resume (Evm.Frontier.Vm.Create.Rules.ofOrd 11) frame newAddr
      (runSub (Evm.Frontier.Vm.Create.child frame subMsg stateForSub))
  | .sload key =>
    -- Dead arm: SLOAD intercepted in Berlin.step1.
    let v := frame.env.state.getStorage frame.message.currentTarget key
    match Stack.push frame.stack v with
    | .error e => .error e
    | .ok s => .ok { frame with stack := s, pc := frame.pc + 1 }
  | .sstore key value =>
    -- Dead arm: SSTORE intercepted above.
    let addr := frame.message.currentTarget
    let stateAfter := frame.env.state.setStorage addr key value
    .ok { frame with
      env := { frame.env with state := stateAfter }, pc := frame.pc + 1 }
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
  | .selfdestruct _beneficiary =>
    -- Dead arm: SELFDESTRUCT intercepted above.
    .ok { frame with halted := true }

/-- Trampoline — yield discharge (`handleYield` above) mirrors
    Berlin's, with the `.createLike` success arm extended to perform
    the EIP-3541 0xEF code-prefix check. EELS
    `forks/london/vm/interpreter.py:process_create_message`. -/
partial def trampoline (evm : Evm) : Except Exception Evm :=
  match runFrame (evm.gasLeft + 1) evm with
  | .halt finalEvm _ => .ok finalEvm
  | .error _ e       => .error e
  | .yield frame eff =>
    match handleYield frame eff trampoline with
    | .ok cont => trampoline cont
    | .error e => .error e

def applyMessage (msg : Message) (env : Environment) :
    Except Exception Evm :=
  trampoline (Evm.fresh msg env)

end Evm.London.Vm.Effect
