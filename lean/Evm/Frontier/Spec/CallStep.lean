/-
  Evm.Frontier.Spec.CallStep — CALL / CALLCODE entry-level spec.

  CALL has three distinct exit paths *before* the sub-frame
  actually runs, and they have to be specced independently:

    1. **failFast (depth)** — `depth ≥ 1024`. Pushes 0, refunds
       the forwarded gas, advances pc. No sub-frame.
    2. **failFast (balance)** — `value > 0 ∧ caller balance < value`.
       Same effect as (1).
    3. **success → sub-frame setup** — pre-charges gas, touches the
       callee (pre-EIP-158), transfers value to a *separate*
       `stateForSub`, builds the sub-frame Message, hands off.

  This file specs path (1), (2), and the entry phase of (3). The
  full whole-frame spec (post-sub-execution merge) requires
  `IsSubExecution` and is the next layer up; deferred.

  The relation is FORK-SPECIFIC because:
    - Frontier: full gasArg pre-paid; pre-EIP-158 touch on
      no-value calls.
    - Homestead: same as Frontier.
    - Tangerine Whistle: 63/64 cap on forwarded gas; pre-EIP-158
      touch.
    - Spurious Dragon: 63/64 cap; EIP-161 value-gated NEW_ACCOUNT;
      no touch on value-0 calls.

  This file declares the Frontier version. Other forks should
  declare their own `IsCallEntry` with their gas/touch semantics.
-/

import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions.Memory   -- chargeMemory helper

namespace Evm.Frontier.Spec

open Evm.Frontier (Account)
open Evm.Frontier.Vm

/-- The 7-tuple of operands CALL pops, in pop order (top first). -/
structure CallArgs where
  gasArg   : Evm.U256
  callee   : Evm.Address     -- post u256→address conversion
  value    : Evm.U256
  argsOff  : Nat
  argsLen  : Nat
  retOff   : Nat
  retLen   : Nat

/-- Re-state CallArgs in raw stack form. The address word is MASKED
    to 160 bits (EELS `to_address`), so the relations below quantify
    the raw `addrW` — the masking is lossy, a CALL with high-bit
    garbage in the address word is valid EVM. -/
def CallArgs.fromStack (gasArg addrW value : Evm.U256)
                       (argsOff argsLen retOff retLen : Evm.U256) :
                       CallArgs :=
  { gasArg, callee := Evm.Address.ofNat addrW.toNat, value,
    argsOff := argsOff.toNat, argsLen := argsLen.toNat,
    retOff  := retOff.toNat,  retLen  := retLen.toNat }

/-! ## Pre-condition: the call's gas-and-memory bookkeeping

    Memory must accommodate `[argsOff, argsOff+argsLen)` AND
    `[retOff, retOff+retLen)`. EELS `calculate_gas_extend_memory`
    (gas.py) processes the extension list SEQUENTIALLY and SKIPS
    `size == 0` entries entirely — a CALL with `argsLen = 0` and a
    huge `argsOff` charges nothing for the args range. The
    sequential charges telescope to one expansion because the
    memory cost function is monotone
    (`memoryExpansionCost_trans`, CallRefinement.lean). -/

/-- Memory words after accommodating the args range then the ret
    range, zero-size ranges skipped. -/
def Frontier.callPostMemWords (args : CallArgs) (preMemWords : Nat) : Nat :=
  let w1 := if args.argsLen = 0 then preMemWords
            else max preMemWords ((args.argsOff + args.argsLen + 31) / 32)
  if args.retLen = 0 then w1
  else max w1 ((args.retOff + args.retLen + 31) / 32)

/-- The expanded parent memory. EELS extends memory BEFORE the
    depth/balance fail-fast checks (`extend_memory` precedes the
    `sender_balance < value` branch in system.py `call`), so the
    fail-fast post-states below carry the expansion too. -/
def Frontier.callExpandMemory (args : CallArgs) (mem : Memory) : Memory :=
  let m1 := if args.argsLen = 0 then mem
            else Memory.extend mem (args.argsOff + args.argsLen)
  if args.retLen = 0 then m1
  else Memory.extend m1 (args.retOff + args.retLen)

/-- The total non-forwarded gas cost of a Frontier CALL given its
    args and the current memory's pre-call words. Captures EELS:
      `base + valueCost + newAccountCost + memoryExpansion`
    where `newAccountCost` is 0 if callee is in state, else 25000
    (Frontier; EIP-161 changes this at SD). -/
def Frontier.callBaseGas (args : CallArgs) (preState : Evm.Frontier.State)
                          (preMemWords : Nat) : Nat :=
  let memCost := Gas.memoryExpansionCost preMemWords
                   (Frontier.callPostMemWords args preMemWords)
  let valueCost := if args.value = (0 : Evm.U256) then 0 else Gas.callValue
  let newAccountCost :=
    if preState.accountExists args.callee then 0 else Gas.newAccount
  Gas.call + valueCost + newAccountCost + memCost

/-- Forwarded gas: full `gasArg` + stipend if value > 0.
    (Frontier rule; EIP-150 changes this at TW.) -/
def Frontier.callForwardGas (args : CallArgs) : Nat :=
  args.gasArg.toNat +
    (if args.value = (0 : Evm.U256) then 0 else Gas.callStipend)

/-! ## Entry-level relations -/

/-- `IsCallFailFastDepth evm evm'`: depth limit hit. Push 0,
    refund the forwarded gas, advance pc. State unchanged — but
    memory IS expanded (EELS extends before the depth check). -/
def IsCallFailFastDepth (evm evm' : Evm) : Prop :=
  ∃ (gasW addrW valueW argsOffW argsLenW retOffW retLenW : Evm.U256)
    (rest : Stack),
    evm.stack = gasW :: addrW :: valueW :: argsOffW :: argsLenW ::
                retOffW :: retLenW :: rest ∧
    let args := CallArgs.fromStack gasW addrW valueW
                  argsOffW argsLenW retOffW retLenW
    evm.message.depth ≥ 1024 ∧
    rest.length < stackLimit ∧
    let baseGas := Frontier.callBaseGas args evm.env.state
                     (Memory.words evm.memory)
    let fwdGas  := args.gasArg.toNat
    evm.gasLeft ≥ baseGas + fwdGas ∧
    -- Post: gas refunded (sub-frame never ran), state unchanged,
    -- 0 pushed, memory expanded, pc advanced, returnData cleared.
    evm' = { evm with
      stack       := 0 :: rest,
      memory      := Frontier.callExpandMemory args evm.memory,
      gasLeft     := evm.gasLeft - baseGas - fwdGas + Frontier.callForwardGas args,
      returnData  := Evm.Bytes.empty,
      pc          := evm.pc + 1 }

/-- `IsCallFailFastBalance evm evm'`: value > 0 and caller cannot
    pay. Same post-effect as depth-fail-fast. -/
def IsCallFailFastBalance (evm evm' : Evm) : Prop :=
  ∃ (gasW addrW valueW argsOffW argsLenW retOffW retLenW : Evm.U256)
    (rest : Stack),
    evm.stack = gasW :: addrW :: valueW :: argsOffW :: argsLenW ::
                retOffW :: retLenW :: rest ∧
    let args := CallArgs.fromStack gasW addrW valueW
                  argsOffW argsLenW retOffW retLenW
    args.value ≠ (0 : Evm.U256) ∧
    (evm.env.state.getBalance evm.message.currentTarget).toNat < args.value.toNat ∧
    rest.length < stackLimit ∧
    let baseGas := Frontier.callBaseGas args evm.env.state
                     (Memory.words evm.memory)
    let fwdGas  := args.gasArg.toNat
    evm.gasLeft ≥ baseGas + fwdGas ∧
    evm' = { evm with
      stack       := 0 :: rest,
      memory      := Frontier.callExpandMemory args evm.memory,
      gasLeft     := evm.gasLeft - baseGas - fwdGas + Frontier.callForwardGas args,
      returnData  := Evm.Bytes.empty,
      pc          := evm.pc + 1 }

/-- A pending sub-frame: the data structure the parent prepares
    for the sub-execution. Implementation-neutral — doesn't say
    HOW the sub-frame runs, only what it should be initialized
    with. Used as the existential witness in `IsCallEntrySuccess`. -/
structure SubFrameSetup where
  subMsg     : Message
  subState   : Evm.Frontier.State   -- world the sub-frame sees
                                    -- (with value transfer + touch applied)
  parentSnapshot : Evm              -- parent state at the moment of yield;
                                    -- on sub-frame failure, this is what gets restored
  retOff : Nat
  retLen : Nat
  deriving Inhabited

/-- `IsCallEntrySuccess evm setup`: the parent passes its
    pre-checks, all gas charges succeed, and `setup` is exactly
    what the parent must prepare for the sub-frame. Everything is
    pinned: the sub-message (including calldata sliced from the
    EXPANDED memory and the callee's code as seen in `subState`),
    the value-transferred sub-state, and the full parent snapshot
    (gas pre-paid, memory expanded, 7 args popped, pc still at the
    CALL — it advances at merge, see `IsCallMerge`). -/
def IsCallEntrySuccess (evm : Evm) (setup : SubFrameSetup) : Prop :=
  ∃ (gasW addrW valueW argsOffW argsLenW retOffW retLenW : Evm.U256)
    (rest : Stack),
    evm.stack = gasW :: addrW :: valueW :: argsOffW :: argsLenW ::
                retOffW :: retLenW :: rest ∧
    let args := CallArgs.fromStack gasW addrW valueW
                  argsOffW argsLenW retOffW retLenW
    -- Pre: not failFast.
    evm.message.depth < 1024 ∧
    (args.value = (0 : Evm.U256) ∨
     (evm.env.state.getBalance evm.message.currentTarget).toNat ≥ args.value.toNat) ∧
    let baseGas := Frontier.callBaseGas args evm.env.state
                     (Memory.words evm.memory)
    let fwdGas  := args.gasArg.toNat
    evm.gasLeft ≥ baseGas + fwdGas ∧
    let memExpanded := Frontier.callExpandMemory args evm.memory
    -- Pre-EIP-158 touch + value transfer; what subState must be:
    let touched :=
      if evm.env.state.accountExists args.callee then evm.env.state
      else evm.env.state.setAccount args.callee Account.empty
    setup.subState =
      (if args.value = (0 : Evm.U256) then touched
       else (touched.subBalance evm.message.currentTarget args.value).addBalance
              args.callee args.value) ∧
    setup.subMsg = { caller := evm.message.currentTarget,
                     target := some args.callee,
                     currentTarget := args.callee,
                     value := args.value,
                     data := Memory.read memExpanded args.argsOff args.argsLen,
                     code := (setup.subState.getAccount args.callee).code,
                     gas := Frontier.callForwardGas args,
                     depth := evm.message.depth + 1 } ∧
    setup.retOff = args.retOff ∧
    setup.retLen = args.retLen ∧
    setup.parentSnapshot = { evm with
      gasLeft := evm.gasLeft - baseGas - fwdGas,
      memory  := memExpanded,
      stack   := rest }

/-! ## CALLCODE (0xf2) variants

    EELS `callcode` (system.py line 285): identical to `call` except
    the sub-frame executes in the CALLER's storage context
    (`current_target = evm.message.current_target`) and value stays
    in the caller — no inter-account transfer, no touch (the caller
    already exists by virtue of running code), and NO new-account
    cost (the popped address is only a code source, never a created
    account). Memory-expansion ordering and the depth/balance
    fail-fast are exactly CALL's. -/

/-- CALLCODE's non-forwarded gas: like `callBaseGas` but with no
    new-account component — `calculate_message_call_gas` is invoked
    by EELS `callcode` without the `GAS_NEW_ACCOUNT` term. -/
def Frontier.callcodeBaseGas (args : CallArgs) (preMemWords : Nat) : Nat :=
  let memCost := Gas.memoryExpansionCost preMemWords
                   (Frontier.callPostMemWords args preMemWords)
  let valueCost := if args.value = (0 : Evm.U256) then 0 else Gas.callValue
  Gas.call + valueCost + memCost

/-- CALLCODE depth fail-fast. Same shape as `IsCallFailFastDepth`,
    CALLCODE gas formula. -/
def IsCallcodeFailFastDepth (evm evm' : Evm) : Prop :=
  ∃ (gasW addrW valueW argsOffW argsLenW retOffW retLenW : Evm.U256)
    (rest : Stack),
    evm.stack = gasW :: addrW :: valueW :: argsOffW :: argsLenW ::
                retOffW :: retLenW :: rest ∧
    let args := CallArgs.fromStack gasW addrW valueW
                  argsOffW argsLenW retOffW retLenW
    evm.message.depth ≥ 1024 ∧
    rest.length < stackLimit ∧
    let baseGas := Frontier.callcodeBaseGas args (Memory.words evm.memory)
    let fwdGas  := args.gasArg.toNat
    evm.gasLeft ≥ baseGas + fwdGas ∧
    evm' = { evm with
      stack       := 0 :: rest,
      memory      := Frontier.callExpandMemory args evm.memory,
      gasLeft     := evm.gasLeft - baseGas - fwdGas + Frontier.callForwardGas args,
      returnData  := Evm.Bytes.empty,
      pc          := evm.pc + 1 }

/-- CALLCODE balance fail-fast. The balance checked is the CALLER's
    (`current_target`) — same account as CALL since both spend from
    the running frame. -/
def IsCallcodeFailFastBalance (evm evm' : Evm) : Prop :=
  ∃ (gasW addrW valueW argsOffW argsLenW retOffW retLenW : Evm.U256)
    (rest : Stack),
    evm.stack = gasW :: addrW :: valueW :: argsOffW :: argsLenW ::
                retOffW :: retLenW :: rest ∧
    let args := CallArgs.fromStack gasW addrW valueW
                  argsOffW argsLenW retOffW retLenW
    args.value ≠ (0 : Evm.U256) ∧
    (evm.env.state.getBalance evm.message.currentTarget).toNat < args.value.toNat ∧
    rest.length < stackLimit ∧
    let baseGas := Frontier.callcodeBaseGas args (Memory.words evm.memory)
    let fwdGas  := args.gasArg.toNat
    evm.gasLeft ≥ baseGas + fwdGas ∧
    evm' = { evm with
      stack       := 0 :: rest,
      memory      := Frontier.callExpandMemory args evm.memory,
      gasLeft     := evm.gasLeft - baseGas - fwdGas + Frontier.callForwardGas args,
      returnData  := Evm.Bytes.empty,
      pc          := evm.pc + 1 }

/-- CALLCODE entry success. Differs from `IsCallEntrySuccess` in:
    `subState` is the caller's state UNCHANGED (no touch, no
    transfer — value stays in the caller, who is also the recipient),
    `currentTarget` stays the caller, and the code comes from the
    popped address as seen in the CURRENT state. -/
def IsCallcodeEntrySuccess (evm : Evm) (setup : SubFrameSetup) : Prop :=
  ∃ (gasW addrW valueW argsOffW argsLenW retOffW retLenW : Evm.U256)
    (rest : Stack),
    evm.stack = gasW :: addrW :: valueW :: argsOffW :: argsLenW ::
                retOffW :: retLenW :: rest ∧
    let args := CallArgs.fromStack gasW addrW valueW
                  argsOffW argsLenW retOffW retLenW
    evm.message.depth < 1024 ∧
    (args.value = (0 : Evm.U256) ∨
     (evm.env.state.getBalance evm.message.currentTarget).toNat ≥ args.value.toNat) ∧
    let baseGas := Frontier.callcodeBaseGas args (Memory.words evm.memory)
    let fwdGas  := args.gasArg.toNat
    evm.gasLeft ≥ baseGas + fwdGas ∧
    let memExpanded := Frontier.callExpandMemory args evm.memory
    setup.subState = evm.env.state ∧
    setup.subMsg = { caller := evm.message.currentTarget,
                     target := some args.callee,
                     currentTarget := evm.message.currentTarget,
                     value := args.value,
                     data := Memory.read memExpanded args.argsOff args.argsLen,
                     code := (evm.env.state.getAccount args.callee).code,
                     gas := Frontier.callForwardGas args,
                     depth := evm.message.depth + 1 } ∧
    setup.retOff = args.retOff ∧
    setup.retLen = args.retLen ∧
    setup.parentSnapshot = { evm with
      gasLeft := evm.gasLeft - baseGas - fwdGas,
      memory  := memExpanded,
      stack   := rest }

/-! ## Notes

    - Each of the three relations above describes ONE entry path.
      The complete spec at the entry level is the disjunction:
      "any successful step of CALL satisfies one of these."

    - The post-state in (1) and (2) is fully determined; the spec
      pins down `evm'` exactly. The post-state in (3) is a
      `SubFrameSetup` parameter — the spec admits any setup whose
      fields agree with the computed expected values.

    - `Frontier.callBaseGas` and `Frontier.callForwardGas` are
      spec-level mathematical definitions of the gas formula.
      They appear in this file because gas costs are part of the
      semantics, not the implementation strategy.

    - The rest of the CALL spec lives in `FrameRun.lean`
      (`IsCallMerge`, the mutual `IsFrameRun`/`IsCallFrame`).
      Refinement against `Effect.doCall` and the trampoline's
      resume functions is in `CallRefinement.lean`.

    - CALL (0xf1) and CALLCODE (0xf2) each get their own relation
      family above; they share `CallArgs`, the memory-expansion
      definitions, and `callForwardGas`, and differ in the base-gas
      formula and the sub-frame's state/currentTarget. -/

end Evm.Frontier.Spec
