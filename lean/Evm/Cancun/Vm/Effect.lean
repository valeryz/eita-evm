/-
  Evm.Cancun.Vm.Effect — yield-based execution for Cancun.

  Strict delta on Shanghai. Cancun introduces five new opcodes plus
  the EIP-6780 SELFDESTRUCT semantic change:

    * EIP-1153 transient storage (TLOAD 0x5c, TSTORE 0x5d) — pure
      env-mutating handlers, dispatched via `liftPure`.
    * EIP-5656 MCOPY 0x5e — pure memory-mutating handler.
    * EIP-4844 BLOBHASH 0x49 — pure stack push reading tx-scope env.
    * EIP-7516 BLOBBASEFEE 0x4a — pure stack push reading block env.
    * EIP-6780 SELFDESTRUCT (0xff) — same-tx-only full destroy.
      Wired by tracking `env.createdAccounts` (populated at CREATE
      resume) and by re-implementing the SELFDESTRUCT yield handler
      in the trampoline (`selfdestructEIP6780` below). EELS:
      `forks/cancun/vm/instructions/system.py:selfdestruct`.

  All other opcodes — including PUSH0 (EIP-3855), EIP-3860 CREATE/
  CREATE2 size caps, the Paris PREVRANDAO rename, and the Byzantium
  call/create infrastructure — inherit from Shanghai's `step1`.

  The trampoline body mirrors Shanghai's (CREATE's merge is every fork's
  `Evm.Frontier.Vm.Create.resume`; the child it runs, `Create.child`, carries the
  `createdAccounts` mark EIP-6780 reads), with one change:
    * `.selfdestruct` branch dispatches through `selfdestructEIP6780`
      (replacing Shanghai's flat destroy with the same-tx test).

  EELS reference: `forks/cancun/vm/interpreter.py:process_message_call`
  for the top-level frame structure, `forks/cancun/vm/instructions/
  __init__.py:op_implementation` for the dispatch table.
-/

import Evm.Shanghai.Vm.Effect
import Evm.Cancun.State
import Evm.Cancun.Vm.Gas
import Evm.Cancun.Vm.Instructions
import Evm.Cancun.Vm.PrecompiledContracts
import Evm.Crypto.P256Verify

namespace Evm.Cancun.Vm.Effect

open Evm.Frontier (Account)
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions
open Evm.Byzantium.Vm.Effect (StepResult Step CallKind YieldEffect liftPure
                                addrToU256 u256ToAddr mergeChild)
-- See note in Constantinople/Vm/Effect.lean: `Byzantium.Vm.Effect.maxCallDepth`
-- collides with `Frontier.Vm.Effect.maxCallDepth`; qualify at use sites.

private def u256ToAddrL (x : Evm.U256) : Evm.Address := Evm.Address.ofNat x.toNat

/-! ## EIP-6780 SELFDESTRUCT

    The dispatch produces a SELFDESTRUCT yield exactly like Byzantium
    (we re-use Byzantium's `.selfdestruct` yield variant). The
    trampoline branch below is where the EIP-6780 conditional kicks in:

      if currentTarget ∈ env.createdAccounts:
          # Same-tx CREATE → full destroy (Byzantium semantics).
      else:
          # Pre-existing account → ONLY transfer balance to beneficiary.
          # Don't queue for delete, don't change refund counter.

    EELS `forks/cancun/vm/instructions/system.py:selfdestruct` lines
    ~50-100. The "transfer balance" step uses the SD touch+addBalance
    pair so that the beneficiary's EIP-161 isDead invariant stays
    correct (a value=0 SELFDESTRUCT to a fresh address must NOT
    create a ghost account). -/
def selfdestructEIP6780 (frame : Evm) (beneficiary : Evm.Address) :
    Except Exception Evm := do
  if frame.message.isStatic then
    .error .writeInStaticContext
  let self     := frame.message.currentTarget
  let state    := frame.env.state
  let balance  := state.getBalance self

  let createdThisTx := Evm.Cancun.State.wasCreatedThisTx frame.env self
  let firstTimeSet  := ¬ frame.env.selfDestructSet.contains self

  -- EIP-6780 self-as-beneficiary: when the contract is NOT being
  -- destroyed (i.e. wasn't created in this tx), SELFDESTRUCT(self) is
  -- a no-op for the balance (transfer-to-self preserves it). Only the
  -- legacy delete-branch burns self-balance — EELS implements this by
  -- zeroing originator AFTER the transfer, so when self == beneficiary
  -- the transfer-back leaves the balance intact in the no-delete arm.
  let stateZeroed :=
    if ¬ createdThisTx ∧ beneficiary = self then
      state
    else
      let stateAfterTransfer :=
        if balance = (0 : Evm.U256) ∧ ¬ state.accountExists beneficiary then
          state
        else
          state.addBalance beneficiary balance
      stateAfterTransfer.setAccount self
        { (stateAfterTransfer.getAccount self) with balance := 0 }

  let envAfter : Environment :=
    if createdThisTx then
      -- Full destroy: queue for end-of-tx delete (matches Byzantium).
      -- EIP-3529 (London+, inherited by Cancun) REMOVED the
      -- SELFDESTRUCT 24000 refund — `refund` stays 0 regardless
      -- of firstTimeSet.
      let refund : Nat := 0
      let envTouched := _root_.Evm.SpuriousDragon.Vm.touchAddr frame.env beneficiary
      { envTouched with
          state := stateZeroed
          selfDestructSet :=
            if firstTimeSet then frame.env.selfDestructSet ++ [self]
            else frame.env.selfDestructSet
          refundCounter := frame.env.refundCounter + refund }
    else
      -- EIP-6780: balance moved, account stays. NO refund, NO
      -- selfDestructSet add. (EIP-3529 already cut SELFDESTRUCT_REFUND
      -- to 0 at London; EIP-6780 just confirms it.)
      let envTouched := _root_.Evm.SpuriousDragon.Vm.touchAddr frame.env beneficiary
      { envTouched with state := stateZeroed }

  return { frame with env := envAfter, halted := true }

/-- 0xff SELFDESTRUCT — Cancun (EIP-6780): emit a `.selfdestruct`
    yield; the trampoline arm below routes through
    `selfdestructEIP6780` rather than the inherited flat-destroy
    logic. EELS: `forks/cancun/vm/instructions/system.py:selfdestruct`.

    Gas charging mirrors Berlin's `doSelfdestructPure`:
      selfDestruct (5000) + cold-account-access (2600 if
      beneficiary cold) + newAccount (25000 if balance>0 ∧
      beneficiary dead, EIP-161). Without this, the previous
      code went straight to the yield and refunded 7600+ gas
      the spec charges — visible as `simpleSuicide_Cancun`
      sender balance 10000 too high. -/
def doSelfdestruct (evm : Evm) : StepResult :=
  if evm.message.isStatic then .error evm .writeInStaticContext
  else
    match Stack.pop evm.stack with
    | .error e => .error evm e
    | .ok (beneficiaryW, s) =>
      let beneficiary := u256ToAddrL beneficiaryW
      let self := evm.message.currentTarget
      let balance := evm.env.state.getBalance self
      let beneficiaryDead :=
        if evm.env.state.accountExists beneficiary
        then (evm.env.state.getAccount beneficiary).isEmpty
        else true
      let newAccountCost : Nat :=
        if balance ≠ (0 : Evm.U256) ∧ beneficiaryDead then
          Evm.Frontier.Vm.Gas.newAccount else 0
      let isCold :=
        ¬ evm.env.accessedAddresses.contains beneficiary
      let coldSurcharge : Nat :=
        if isCold then Evm.Berlin.Vm.Gas.coldAccountAccess else 0
      let totalCost :=
        Evm.TangerineWhistle.Vm.Gas.selfDestruct +
        newAccountCost + coldSurcharge
      match Evm.Frontier.Vm.Gas.charge evm.gasLeft totalCost with
      | .error e => .error evm e
      | .ok gasLeft =>
        let warmed : List Evm.Address :=
          if isCold then evm.env.accessedAddresses ++ [beneficiary]
          else evm.env.accessedAddresses
        let envWarm :=
          { evm.env with accessedAddresses := warmed }
        .yield
          { evm with gasLeft := gasLeft, stack := s, env := envWarm }
          (.selfdestruct beneficiary)

/-! ## Step dispatch

    Cancun intercepts five new opcodes plus SELFDESTRUCT, falls
    through to Shanghai for everything else. -/
def step1 (evm : Evm) : StepResult :=
  if evm.halted then .halt evm evm.output
  else if evm.pc ≥ evm.message.code.size then
    .halt { evm with halted := true } evm.output
  else
    let op := evm.message.code.get! evm.pc
    match op.toNat with
    | 0x49 => liftPure Evm.Cancun.Vm.Instructions.blobhash evm       -- EIP-4844
    | 0x4a => liftPure Evm.Cancun.Vm.Instructions.blobbasefee evm    -- EIP-7516
    | 0x5c => liftPure Evm.Cancun.Vm.Instructions.tload  evm         -- EIP-1153
    | 0x5d => liftPure Evm.Cancun.Vm.Instructions.tstore evm         -- EIP-1153
    | 0x5e => liftPure Evm.Cancun.Vm.Instructions.mcopy  evm         -- EIP-5656
    | 0xff => doSelfdestruct evm                                     -- EIP-6780
    | _    => Evm.Shanghai.Vm.Effect.step1 evm

/-- Trace-friendly format: one tab-separated line per opcode step.
    Matches the layout `BaseReplay` produces from op-geth's
    `structLogTracer` JSON so we can `diff` the two files. -/
private def formatTraceLine (evm : Evm) : String :=
  let pc := evm.pc
  let op : UInt8 := if pc < evm.message.code.size then evm.message.code.get! pc else 0
  let gas := evm.gasLeft
  let depth := evm.message.depth
  let stkLen := evm.stack.length
  let top0 : String :=
    match evm.stack with
    | x :: _ => s!"{x.toNat}"
    | _ => "-"
  let top1 : String :=
    match evm.stack with
    | _ :: x :: _ => s!"{x.toNat}"
    | _ => "-"
  let memBytes := evm.memory.size
  s!"TRACE\tpc={pc}\top=0x{Nat.toDigits 16 op.toNat |> String.ofList}\tgas={gas}\tdepth={depth}\tstk={stkLen}\tst0={top0}\tst1={top1}\tmem={memBytes}"

def runFrame : Nat → Evm → Step
  | 0,      evm => .error evm .outOfGas
  | fuel+1, evm =>
    -- Optional per-step trace. The `dbgTrace`'s return value MUST
    -- be threaded into the `evm` we pass to step1, otherwise
    -- Lean's compiler elides the call as dead code and no trace
    -- ever fires.
    let evm :=
      if evm.env.debugTrace then dbgTrace (formatTraceLine evm) (fun _ => evm) else evm
    match step1 evm with
    | .continue evm'      => runFrame fuel evm'
    | .yield evm' eff     => .yield evm' eff
    | .halt evm' output   => .halt evm' output
    | .error evm' e       => .error evm' e


/-- The OP-Stack rules on the precompile table (both flags are off on Ethereum, so the
    table is the fork's): Fjord's RIP-7212 P256VERIFY at 0x100 at the fork's gas
    (`env.opP256VerifyGas`), Granite's bn256 pairing input cap (`opBn256PairingCap`,
    op-geth `bn256PairingGranite`: a longer input fails, consuming the gas). -/
def opPrecompiles
    (lookup : Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (env : Environment) (a : Evm.Address) :
    Option Evm.Frontier.Vm.PrecompiledContracts.Precompile :=
  let rest := (lookup a).map fun p input gas =>
    let capped : Bool := match env.opBn256PairingCap with
      | some cap => decide (input.size > cap)
      | none => false
    if decide (a = Evm.Address.ofNat 0x08) && capped then .error .outOfGas else p input gas
  match env.opP256VerifyGas with
  | some g => if a = Evm.Address.ofNat 0x0100 then some (Evm.Crypto.p256VerifyWith g) else rest
  | none => rest

/-- Process ONE yield: spawn the sub-frame (via the supplied
    `runSub` callback) or perform the state operation, run the
    matching resume function, and return the parent's
    continuation frame. Total — same extraction rationale as
    Frontier's `handleYield`: the IR trampoline binds it instead
    of re-encoding, and Spec-layer theorems can quantify over
    it. -/
def handleYield
    (precompileLookup : Evm.Address →
        Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (frame : Evm) (eff : YieldEffect)
    (runSub : Evm → Except Exception Evm) : Except Exception Evm :=
  match eff with
  | .callLike _ subMsg code stateForSub _ _ retOff retLen _ _ =>
    -- EELS generic_call's end, process_message, execute_code, incorporate_child_*
    -- (Evm.Frontier.Vm.Call.resume / runChild).
    Evm.Frontier.Vm.Call.resume (Evm.Frontier.Vm.Call.Rules.ofOrd 16) frame subMsg.currentTarget
      retOff retLen
      (Evm.Frontier.Vm.Call.runChild (opPrecompiles precompileLookup) frame subMsg code stateForSub runSub)
  | .createLike subMsg newAddr stateForSub _ _ _ _ _ _ _ =>
    -- EELS process_create_message + incorporate_child_* (Evm.Frontier.Vm.Create.resume).
    Evm.Frontier.Vm.Create.resume (Evm.Frontier.Vm.Create.Rules.ofOrd 16) frame newAddr
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
    -- EIP-6780 dispatch — see `selfdestructEIP6780` above.
    selfdestructEIP6780 frame beneficiary

/-- Trampoline — yields discharged via `handleYield` above
    (Shanghai's body with one Cancun tweak):
      * `.selfdestruct` arm dispatches through `selfdestructEIP6780`.

    The `precompileLookup` parameter is supplied by the fork
    driver (the block-number-based dispatch happens THERE, then
    the chosen fork passes ITS precompile table down here). This
    keeps the trampoline a pure interpreter loop with no knowledge
    of which fork's precompiles are in scope. Default is Cancun's
    table for convenience at vanilla-Cancun call sites; Prague,
    Osaka, and OP Isthmus each supply their own. -/
partial def trampoline
    (precompileLookup : Evm.Address →
        Option Evm.Frontier.Vm.PrecompiledContracts.Precompile :=
      Evm.Cancun.Vm.PrecompiledContracts.lookup)
    (evm : Evm) : Except Exception Evm :=
  match runFrame (evm.gasLeft + 1) evm with
  | .halt finalEvm _ => .ok finalEvm
  | .error _ e       => .error e
  | .yield frame eff =>
    match handleYield precompileLookup frame eff (trampoline precompileLookup) with
    | .ok cont => trampoline precompileLookup cont
    | .error e => .error e

/-- Vanilla Cancun applyMessage: uses Cancun's precompile table.
    Preserved with the original `Message → Environment → ...`
    signature so existing call sites (mainnet, Bedrock..Ecotone)
    can pass it as a function value without change. -/
def applyMessage (msg : Message) (env : Environment) :
    Except Exception Evm :=
  trampoline Evm.Cancun.Vm.PrecompiledContracts.lookup (Evm.fresh msg env)

/-- Generic applyMessage parameterised on the precompile table.
    Fork drivers that need to override the table (e.g. OP Isthmus
    cherry-picking Osaka's EIP-7883 MODEXP) call this directly. -/
def applyMessageWith
    (precompileLookup : Evm.Address →
        Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (msg : Message) (env : Environment) :
    Except Exception Evm :=
  trampoline precompileLookup (Evm.fresh msg env)

end Evm.Cancun.Vm.Effect
