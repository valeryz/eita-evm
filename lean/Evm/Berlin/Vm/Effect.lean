/-
  Evm.Berlin.Vm.Effect — yield-based execution for Berlin.

  Strict delta on Istanbul. Berlin rewrites the gas schedule for every
  state-access opcode (EIP-2929 warm/cold) and lifts SSTORE to a
  cold-aware EIP-2200 net-gas-metering schedule:

    * EIP-2929 warm/cold pricing for SLOAD, BALANCE, EXTCODESIZE,
      EXTCODECOPY, EXTCODEHASH, CALL family, SELFDESTRUCT beneficiary.
      Tracked via `accessedAddresses` / `accessedStorageKeys` on
      `Environment` — populated for the duration of one transaction
      (NOT one frame). EELS `forks/berlin/vm/gas.py` lines 40-65.
    * EIP-2200 SSTORE net-gas-metering with the dirty-map predicate,
      with the EIP-2929 cold surcharge folded on top. EELS
      `forks/berlin/vm/instructions/storage.py:sstore`. The schedule
      lives in `Evm.Berlin.Vm.Instructions.Storage.cost`.
    * EIP-2718/EIP-2930 access lists: pre-warming is the caller's
      responsibility (see `Berlin.processTransaction`); this module
      assumes `accessedAddresses` / `accessedStorageKeys` are pre-
      populated correctly at frame entry.

  Slim-pattern note. Berlin opts the EIP-2929-specific opcodes into
  pure / pre-charge handlers so the inherited Istanbul trampoline body
  (which itself mirrors Byzantium's) suffices unchanged. The trade-off
  is that the per-tx warm-set propagation across REVERT / call-error
  boundaries collapses to the conservative "keep parent's warm set"
  behaviour — the EELS-faithful "propagate child's warm set even on
  REVERT" requires structural changes to the call resume path that
  are deferred to a follow-up. The replay corpus does not exercise the
  difference, but a future addition exercising EIP-2929 across nested
  REVERT must revisit this.

  All non-state-access opcodes (arithmetic, bitwise, push/dup/swap,
  jump, mem, log, etc.) fall through to Istanbul's `step1`.
-/

import Evm.Istanbul.Vm.Effect
import Evm.Berlin.Vm.Gas
import Evm.Berlin.Vm.Instructions.Storage

namespace Evm.Berlin.Vm.Effect

open Evm.Frontier (Account)
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions
open Evm.Byzantium.Vm.Effect (StepResult Step CallKind YieldEffect liftPure
                                addrToU256 u256ToAddr mergeChild)
-- `Evm.Byzantium.Vm.Effect.maxCallDepth` collides with
-- `Evm.Frontier.Vm.Effect.maxCallDepth`; qualify at use sites.

/-! ## EIP-2929 warm-set helpers (the per-tx warm sets live on `Environment`). -/

/-- Is `addr` already in the warm set for this transaction? -/
def isAddrWarm (env : Environment) (addr : Evm.Address) : Bool :=
  env.accessedAddresses.contains addr

/-- Is `(addr, slot)` already in the warm set for this transaction? -/
def isSlotWarm (env : Environment) (addr : Evm.Address) (slot : Evm.U256) : Bool :=
  env.accessedStorageKeys.contains (addr, slot)

/-- Add `addr` to the warm set if absent. Returns `(env', isCold)` —
    `isCold` is what callers need to pick warm-vs-cold pricing. -/
def warmAddr (env : Environment) (addr : Evm.Address) : Environment × Bool :=
  if env.accessedAddresses.contains addr then (env, false)
  else ({ env with accessedAddresses := env.accessedAddresses ++ [addr] }, true)

/-- Add `(addr, slot)` to the warm-slots set if absent. -/
def warmSlot (env : Environment) (addr : Evm.Address) (slot : Evm.U256) :
    Environment × Bool :=
  if env.accessedStorageKeys.contains (addr, slot) then (env, false)
  else ({ env with accessedStorageKeys :=
                     env.accessedStorageKeys ++ [(addr, slot)] }, true)

/-- Look up the cached "original at start of tx" value for a slot; if
    not yet cached, return the supplied fallback (typically the current
    value, which then becomes the original on first SSTORE). -/
def getOriginal (env : Environment) (addr : Evm.Address) (slot : Evm.U256)
    (fallback : Evm.U256) : Evm.U256 :=
  match env.storageOriginals.find? (fun (k, _) => k = (addr, slot)) with
  | some (_, v) => v
  | none        => fallback

/-- Cache `original` for `(addr, slot)` if not already present. -/
def cacheOriginal (env : Environment) (addr : Evm.Address) (slot : Evm.U256)
    (original : Evm.U256) : Environment :=
  if env.storageOriginals.any (fun (k, _) => k = (addr, slot)) then env
  else { env with storageOriginals :=
                    env.storageOriginals ++ [((addr, slot), original)] }

/-- Pre-warmed precompile addresses at Berlin (per EIP-2929, addresses
    `0x01..0x09` are warm at tx start). -/
def precompileAddresses : List Evm.Address :=
  (List.range 9).map (fun i => Evm.Address.ofNat (i + 1))

/-! ## Helpers -/

private def isDead (state : Evm.Frontier.State) (addr : Evm.Address) : Bool :=
  if state.accountExists addr then (state.getAccount addr).isEmpty
  else true

/-! ## EIP-2929 pure handlers — SLOAD / SSTORE done in step1.

    Both ops read storage / cache originals / mark slots warm and
    (for SSTORE) compute the EIP-2200 / EIP-2929 cost + refund delta
    directly in `step1`, then continue. No yield is emitted — this
    avoids needing to extend Byzantium's `YieldEffect` with an
    `isCold` flag. EELS:
      * `forks/berlin/vm/instructions/storage.py:sload`
      * `forks/berlin/vm/instructions/storage.py:sstore`
    -/

/-- 0x54 SLOAD with EIP-2929 cold/warm pricing. -/
def doSloadPure : Handler := fun evm => do
  let (key, s) ← Stack.pop evm.stack
  let addr := evm.message.currentTarget
  let isCold := ¬ isSlotWarm evm.env addr key
  let cost := if isCold then Berlin.Vm.Gas.coldSload else Berlin.Vm.Gas.warmAccess
  let gasLeft ← Gas.charge evm.gasLeft cost
  let value := evm.env.state.getStorage addr key
  let (envWarm, _) := warmSlot evm.env addr key
  let envCached := cacheOriginal envWarm addr key value
  let s ← Stack.push s value
  return { evm with gasLeft := gasLeft, env := envCached, stack := s, pc := evm.pc + 1 }

/-- 0x55 SSTORE with EIP-2200 + EIP-2929 cost + refund accounting. -/
def doSstorePure : Handler := fun evm => do
  if evm.message.isStatic then
    .error .writeInStaticContext
  let (key, value, s) ← Stack.pop2 evm.stack
  -- EIP-2200 sentry, kept by EIP-2929: refuse to run on ≤ 2300
  -- (GAS_CALL_STIPEND) gas left. EELS `forks/berlin/vm/instructions/
  -- storage.py:sstore` — the check sits between the pops and the
  -- original/current reads.
  if evm.gasLeft ≤ Gas.callStipend then
    .error .outOfGas
  let addr     := evm.message.currentTarget
  let current  := evm.env.state.getStorage addr key
  let original := getOriginal evm.env addr key current
  let envOrig  := cacheOriginal evm.env addr key original
  let isCold   := ¬ isSlotWarm envOrig addr key
  let (envWarm, _) := warmSlot envOrig addr key
  let (cost, refundCounter) :=
    Berlin.Vm.Instructions.Storage.sstoreGas envWarm.refundCounter
      isCold original current value
  let gasLeft ← Gas.charge evm.gasLeft cost
  let stateAfter := evm.env.state.setStorage addr key value
  return { evm with
    gasLeft := gasLeft, stack := s,
    env := { envWarm with state := stateAfter, refundCounter := refundCounter },
    pc := evm.pc + 1 }

/-! ## EIP-7702 delegated access helper

    When the callee's account holds a 23-byte `0xef0100||addr`
    designator AND the Prague-era delegation flag is set on the
    env, the CALL family must charge an additional EIP-2929
    cold/warm access for `addr` (the delegated implementation
    contract) BEFORE computing the 63/64 forward. Returns the
    cost in gas and the env updated with `addr` warmed; both
    fall through unchanged when delegation doesn't apply. -/
/-! ## EIP-2929 account-access opcodes — pure handlers. -/

/-- 0x31 BALANCE with EIP-2929 cold/warm pricing. -/
def doBalancePure : Handler := fun evm => do
  let (addrW, s) ← Stack.pop evm.stack
  let addr := u256ToAddr addrW
  let isCold := ¬ isAddrWarm evm.env addr
  let cost := if isCold then Berlin.Vm.Gas.coldAccountAccess else Berlin.Vm.Gas.warmAccess
  let gasLeft ← Gas.charge evm.gasLeft cost
  let bal := evm.env.state.getBalance addr
  let (envWarm, _) := warmAddr evm.env addr
  let s ← Stack.push s bal
  return { evm with gasLeft := gasLeft, env := envWarm, stack := s, pc := evm.pc + 1 }

/-- 0x3b EXTCODESIZE with EIP-2929 cold/warm pricing. -/
def doExtcodesizePure : Handler := fun evm => do
  let (addrW, s) ← Stack.pop evm.stack
  let addr := u256ToAddr addrW
  let isCold := ¬ isAddrWarm evm.env addr
  let cost := if isCold then Berlin.Vm.Gas.coldAccountAccess else Berlin.Vm.Gas.warmAccess
  let gasLeft ← Gas.charge evm.gasLeft cost
  let code := (evm.env.state.getAccount addr).code
  let (envWarm, _) := warmAddr evm.env addr
  let s ← Stack.push s (Evm.U256.ofNat code.size)
  return { evm with gasLeft := gasLeft, env := envWarm, stack := s, pc := evm.pc + 1 }

/-- 0x3c EXTCODECOPY with EIP-2929 cold/warm pricing. -/
def doExtcodecopyPure : Handler := fun evm => do
  let (addrW, s) ← Stack.pop evm.stack
  let (memOff, codeOff, size, s) ← Stack.pop3 s
  let memOffN := memOff.toNat
  let sizeN   := size.toNat
  let (gasLeft, mem) ← chargeMemory evm.gasLeft evm.memory memOffN sizeN
  let addr := u256ToAddr addrW
  let isCold := ¬ isAddrWarm evm.env addr
  let baseCost := if isCold then Berlin.Vm.Gas.coldAccountAccess else Berlin.Vm.Gas.warmAccess
  let copyCost := baseCost + Gas.copy * ((sizeN + 31) / 32)
  let gasLeft ← Gas.charge gasLeft copyCost
  let (envWarm, _) := warmAddr evm.env addr
  let code := (evm.env.state.getAccount addr).code
  let bytes := Evm.Bytes.sliceZeroPad code codeOff.toNat sizeN
  let mem := Memory.write mem memOffN bytes
  return { evm with gasLeft := gasLeft, env := envWarm, memory := mem, stack := s,
                    pc := evm.pc + 1 }

/-- 0x3f EXTCODEHASH with EIP-2929 cold/warm pricing.
    EELS `forks/berlin/vm/instructions/environment.py:extcodehash`. -/
def doExtcodehashPure : Handler := fun evm => do
  let (addrW, s) ← Stack.pop evm.stack
  let addr := u256ToAddr addrW
  let isCold := ¬ isAddrWarm evm.env addr
  let cost := if isCold then Berlin.Vm.Gas.coldAccountAccess else Berlin.Vm.Gas.warmAccess
  let gasLeft ← Gas.charge evm.gasLeft cost
  let (envWarm, _) := warmAddr evm.env addr
  let exists' := evm.env.state.accountExists addr
  let acc := evm.env.state.getAccount addr
  let codehash : Evm.U256 :=
    if ¬ exists' ∨ acc.isEmpty then 0
    else Evm.Crypto.keccak256 acc.code
  let s ← Stack.push s codehash
  return { evm with gasLeft := gasLeft, env := envWarm, stack := s, pc := evm.pc + 1 }

/-- 0xf1 CALL (EELS `call`) — `Evm.Frontier.Vm.Call.opcode` at this fork's rules: the pops, the static
    check, the memory charge, then `Call.start`; the child's run and its end are the
    `.callLike` arm (`Call.resume`). -/
def doCall (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Call.opcode (Evm.Frontier.Vm.Call.Rules.ofOrd 10) .call evm (.error evm) .continue
    (fun p m c st ro rl => .yield p (.callLike .call m c st p.gasLeft p.memory ro rl p.stack p.pc))

/-- 0xf2 CALLCODE (EELS `callcode`) — `Evm.Frontier.Vm.Call.opcode` at this fork's rules: the pops, the static
    check, the memory charge, then `Call.start`; the child's run and its end are the
    `.callLike` arm (`Call.resume`). -/
def doCallcode (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Call.opcode (Evm.Frontier.Vm.Call.Rules.ofOrd 10) .callcode evm (.error evm) .continue
    (fun p m c st ro rl => .yield p (.callLike .callcode m c st p.gasLeft p.memory ro rl p.stack p.pc))

/-- 0xf4 DELEGATECALL (EELS `delegatecall`, EIP-7) — `Evm.Frontier.Vm.Call.opcode` at this fork's rules: the pops, the static
    check, the memory charge, then `Call.start`; the child's run and its end are the
    `.callLike` arm (`Call.resume`). -/
def doDelegatecall (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Call.opcode (Evm.Frontier.Vm.Call.Rules.ofOrd 10) .delegatecall evm (.error evm) .continue
    (fun p m c st ro rl => .yield p (.callLike .delegatecall m c st p.gasLeft p.memory ro rl p.stack p.pc))

/-- 0xfa STATICCALL (EELS `staticcall`, EIP-214) — `Evm.Frontier.Vm.Call.opcode` at this fork's rules: the pops, the static
    check, the memory charge, then `Call.start`; the child's run and its end are the
    `.callLike` arm (`Call.resume`). -/
def doStaticcall (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Call.opcode (Evm.Frontier.Vm.Call.Rules.ofOrd 10) .staticcall evm (.error evm) .continue
    (fun p m c st ro rl => .yield p (.callLike .staticcall m c st p.gasLeft p.memory ro rl p.stack p.pc))

/-- 0xf0 CREATE — Berlin variant. Per EIP-2929 the new address is
    pre-warmed. EELS `forks/berlin/vm/instructions/system.py:create`. -/
def doCreate (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Create.opcode (Evm.Frontier.Vm.Create.Rules.ofOrd 10) true false evm (.error evm) .continue
    (fun p m st snd n v => .yield p (.createLike m m.currentTarget st p.gasLeft p.memory p.stack p.pc snd n v))

/-- 0xf5 CREATE2 with EIP-2929 pre-warm. EELS
    `forks/berlin/vm/instructions/system.py:create2`. -/
def doCreate2 (evm : Evm) : StepResult :=
  Evm.Frontier.Vm.Create.opcode (Evm.Frontier.Vm.Create.Rules.ofOrd 10) true true evm (.error evm) .continue
    (fun p m st snd n v => .yield p (.createLike m m.currentTarget st p.gasLeft p.memory p.stack p.pc snd n v))

/-- 0xff SELFDESTRUCT — Berlin pure handler. EIP-2929 cold beneficiary
    surcharge of `+2600`, on top of TW's `5000` base and (when value-
    transferring to a dead account) SD's `25000` NEW_ACCOUNT. The actual
    state changes happen here (rather than via yield): transfer the
    self balance to the beneficiary, queue self for end-of-tx delete,
    add refund. EELS `forks/berlin/vm/instructions/system.py:selfdestruct`. -/
def doSelfdestructPure : Handler := fun evm => do
  if evm.message.isStatic then
    .error .writeInStaticContext
  let (beneficiaryW, _) ← Stack.pop evm.stack
  let beneficiary := u256ToAddr beneficiaryW
  let isCold := ¬ isAddrWarm evm.env beneficiary
  let self := evm.message.currentTarget
  let balance := evm.env.state.getBalance self
  let newAccountCost : Nat :=
    if balance ≠ (0 : Evm.U256) ∧ isDead evm.env.state beneficiary then
      Gas.newAccount else 0
  let coldSurcharge : Nat :=
    if isCold then Berlin.Vm.Gas.coldAccountAccess else 0
  let gasLeft ← Gas.charge evm.gasLeft
    (Evm.TangerineWhistle.Vm.Gas.selfDestruct + newAccountCost + coldSurcharge)
  let (envWarm, _) := warmAddr evm.env beneficiary
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
  let refund    := if firstTime then Gas.selfDestructRefund else 0
  let envTouched := _root_.Evm.SpuriousDragon.Vm.touchAddr envWarm beneficiary
  return { evm with
    gasLeft := gasLeft,
    halted := true,
    env := { envTouched with
      state := st,
      selfDestructSet :=
        if firstTime then envWarm.selfDestructSet ++ [self]
        else envWarm.selfDestructSet,
      refundCounter := envWarm.refundCounter + refund } }

/-! ## Step dispatch -/

def step1 (evm : Evm) : StepResult :=
  if evm.halted then .halt evm evm.output
  else if evm.pc ≥ evm.message.code.size then
    .halt { evm with halted := true } evm.output
  else
    let op := evm.message.code.get! evm.pc
    match op.toNat with
    | 0x31 => liftPure doBalancePure evm                                    -- EIP-2929
    | 0x3b => liftPure doExtcodesizePure evm                                -- EIP-2929
    | 0x3c => liftPure doExtcodecopyPure evm                                -- EIP-2929
    | 0x3f => liftPure doExtcodehashPure evm                                -- EIP-2929 + EIP-1052
    | 0x54 => liftPure doSloadPure evm                                      -- EIP-2929
    | 0x55 => liftPure doSstorePure evm                                     -- EIP-2200 + EIP-2929
    | 0xf0 => doCreate evm                                                  -- EIP-2929 pre-warm
    | 0xf1 => doCall evm                                                    -- EIP-2929
    | 0xf2 => doCallcode evm                                                -- EIP-2929
    | 0xf4 => doDelegatecall evm                                            -- EIP-2929
    | 0xf5 => doCreate2 evm                                                 -- EIP-2929 pre-warm
    | 0xfa => doStaticcall evm                                              -- EIP-2929
    | 0xff => liftPure doSelfdestructPure evm                               -- EIP-2929
    | _    => Evm.Istanbul.Vm.Effect.step1 evm

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
    Evm.Frontier.Vm.Call.resume (Evm.Frontier.Vm.Call.Rules.ofOrd 10) frame subMsg.currentTarget
      retOff retLen
      (Evm.Frontier.Vm.Call.runChild (fun _ => Evm.Frontier.Vm.Call.precompiles 10) frame subMsg code stateForSub runSub)
  | .createLike subMsg newAddr stateForSub _ _ _ _ _ _ _ =>
    -- EELS process_create_message + incorporate_child_* (Evm.Frontier.Vm.Create.resume).
    Evm.Frontier.Vm.Create.resume (Evm.Frontier.Vm.Create.Rules.ofOrd 10) frame newAddr
      (runSub (Evm.Frontier.Vm.Create.child frame subMsg stateForSub))
  | .sload key =>
    -- Dead arm at Berlin: SLOAD is intercepted in step1.
    let v := frame.env.state.getStorage frame.message.currentTarget key
    match Stack.push frame.stack v with
    | .error e => .error e
    | .ok s => .ok { frame with stack := s, pc := frame.pc + 1 }
  | .sstore key value =>
    -- Dead arm at Berlin: SSTORE is intercepted in step1.
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
    -- Dead arm at Berlin: SELFDESTRUCT is intercepted in step1.
    .ok { frame with halted := true }

/-- Trampoline — yield discharge (`handleYield` above) identical to
    Istanbul's (which is Byzantium's). The `.sload`, `.sstore`,
    `.balance`, `.extcodesize`, `.extcodecopy`, and `.selfdestruct`
    arms are dead code at Berlin because `step1` routes those opcodes
    through pure handlers above. -/
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

end Evm.Berlin.Vm.Effect
