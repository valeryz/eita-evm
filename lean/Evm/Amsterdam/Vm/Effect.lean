/-
  Evm.Amsterdam.Vm.Effect — yield-based execution for Amsterdam.

  EELS reference: `forks/amsterdam/vm/instructions/__init__.py`
  (dispatch additions) and the per-opcode files cited below.

  Delta on Osaka at the EVM dispatcher:

    * 0x4B SLOTNUM — push `block_env.slot_number` (EELS
      `forks/amsterdam/vm/instructions/block.py::slot_number`).
      Gas: BASE (=2) per `gas.py::OPCODE_SLOTNUM`.
    * 0xE6 DUPN — duplicate item at depth `imm + 1` (one-byte immediate).
      Gas: VERY_LOW. EELS `forks/amsterdam/vm/instructions/stack.py::dupn`.
    * 0xE7 SWAPN — swap top with item at depth `imm + 1`.
      Gas: VERY_LOW. EELS `stack.py::swapn`.
    * 0xE8 EXCHANGE — swap items at depths `n+1` and `m+1`, with `n` /
      `m` decoded from the immediate byte as `(imm >> 4, imm & 0x0f)`.
      Gas: VERY_LOW. EELS `stack.py::exchange`.

  All four new opcodes (and CLZ from Osaka, PUSH0/EIP-3860 from
  Shanghai, PREVRANDAO from Paris) need to be reachable inside every
  sub-frame, so we re-emit the full trampoline pinned to Amsterdam's
  `runFrame` — same trick used in every previous fork's `Vm/Effect.lean`.

  The EIP-7928 block-access-list, EIP-7981 calldata-floor re-pricing,
  and the EIP-7732 ERC-20-style auto-Transfer-log emission do NOT
  affect single-step EVM dispatch and so are not handled here. The
  TODO-bearing block-or-tx-level wrapper in `Amsterdam/Fork.lean` calls
  them out.
-/

import Evm.BaseTypes
import Evm.Osaka.Vm.Effect

namespace Evm.Amsterdam.Vm.Effect

open Evm.Frontier.Vm
open Evm.Byzantium.Vm.Effect (StepResult Step CallKind YieldEffect liftPure
                                addrToU256 u256ToAddr maxCallDepth mergeChild)

/-! ## EIP-7732 SLOTNUM (0x4B) -/

/-- 0x4B SLOTNUM. Gas BASE (= 2). EELS
    `forks/amsterdam/vm/instructions/block.py::slot_number`. -/
def doSlotNumber (evm : Evm) : StepResult :=
  match Gas.charge evm.gasLeft Gas.base with
  | .error e => .error evm e
  | .ok gasLeft =>
    match Stack.push evm.stack (Evm.U256.ofNat evm.env.slotNumber) with
    | .error e => .error evm e
    | .ok s    => .continue { evm with gasLeft := gasLeft, stack := s,
                                        pc := evm.pc + 1 }

/-! ## EIP-8024 stack-access instructions -/

/-- Read the immediate byte following the opcode at `pc`, with
    out-of-code reads padded to zero (matches the EELS pattern using
    `buffer_read(evm.code, U256(evm.pc + 1), U256(1))`). -/
private def immByte (evm : Evm) : Nat :=
  let p := evm.pc + 1
  if p < evm.message.code.size then (evm.message.code.get! p).toNat else 0

/-- 0xE6 DUPN. EELS `forks/amsterdam/vm/instructions/stack.py::dupn`.
    `item_number = imm + 1`. Push stack[-(imm+1)] (= n-th from top,
    1-indexed). Gas VERY_LOW. PC advances by 2 (1 opcode + 1 imm). -/
def doDupN (evm : Evm) : StepResult :=
  let imm := immByte evm
  let n := imm + 1
  match evm.stack[n - 1]? with
  | none => .error evm .stackUnderflow
  | some v =>
    match Gas.charge evm.gasLeft Gas.veryLow with
    | .error e => .error evm e
    | .ok gasLeft =>
      match Stack.push evm.stack v with
      | .error e => .error evm e
      | .ok s    => .continue { evm with gasLeft := gasLeft, stack := s,
                                          pc := evm.pc + 2 }

/-- 0xE7 SWAPN. EELS `stack.py::swapn`. SWAPN with decoded value `n`
    swaps top (position 1) with position `n+1`. -/
def doSwapN (evm : Evm) : StepResult :=
  let imm := immByte evm
  let n := imm
  match evm.stack with
  | [] => .error evm .stackUnderflow
  | top :: rest =>
    match rest[n]? with
    | none       => .error evm .stackUnderflow
    | some other =>
      match Gas.charge evm.gasLeft Gas.veryLow with
      | .error e => .error evm e
      | .ok gasLeft =>
        .continue { evm with
          gasLeft := gasLeft,
          stack   := other :: rest.set n top,
          pc      := evm.pc + 2 }

/-- 0xE8 EXCHANGE. EELS `stack.py::exchange`. The immediate byte is
    decoded into `(n, m)` (high nibble, low nibble); the opcode swaps
    items at positions `n+1` and `m+1` (1-indexed; position 1 = top).
    `depth = max(n, m) + 1` items must be on the stack. -/
def doExchange (evm : Evm) : StepResult :=
  let imm := immByte evm
  let n := imm >>> 4
  let m := imm &&& 0x0f
  let depth := (max n m) + 1
  if depth > evm.stack.length then
    .error evm .stackUnderflow
  else
    -- Convert to 0-indexed list positions: position k → index (k-1).
    let i := n
    let j := m
    match evm.stack[i]?, evm.stack[j]? with
    | some vi, some vj =>
      match Gas.charge evm.gasLeft Gas.veryLow with
      | .error e => .error evm e
      | .ok gasLeft =>
        let s1 := evm.stack.set i vj
        let s2 := s1.set j vi
        .continue { evm with gasLeft := gasLeft, stack := s2,
                              pc := evm.pc + 2 }
    | _, _ => .error evm .stackUnderflow

/-! ## Step dispatch -/

def step1 (evm : Evm) : StepResult :=
  if evm.halted then .halt evm evm.output
  else if evm.pc ≥ evm.message.code.size then
    .halt { evm with halted := true } evm.output
  else
    let op := evm.message.code.get! evm.pc
    match op.toNat with
    | 0x4b => doSlotNumber evm           -- SLOTNUM
    | 0xe6 => doDupN evm                 -- DUPN
    | 0xe7 => doSwapN evm                -- SWAPN
    | 0xe8 => doExchange evm             -- EXCHANGE
    | _    => Evm.Osaka.Vm.Effect.step1 evm

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
    Evm.Frontier.Vm.Call.resume (Evm.Frontier.Vm.Call.Rules.ofOrd 21) frame subMsg.currentTarget
      retOff retLen
      (Evm.Frontier.Vm.Call.runChild (fun _ => Evm.Frontier.Vm.Call.precompiles 21) frame subMsg code stateForSub runSub)
  | .createLike subMsg newAddr stateForSub _ _ _ _ _ _ _ =>
    -- EELS process_create_message + incorporate_child_* (Evm.Frontier.Vm.Create.resume).
    Evm.Frontier.Vm.Create.resume (Evm.Frontier.Vm.Create.Rules.ofOrd 21) frame newAddr
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
    -- EIP-6780, unchanged since Cancun (EELS amsterdam/vm/instructions/system.py selfdestruct
    -- = cancun's): the Cancun effect. Until 2026-10-26 this arm was the FRONTIER form —
    -- every SELFDESTRUCT queued for deletion with a 24000 refund — so the spec's Osaka
    -- SELFDESTRUCT (reached through Cancun's `doSelfdestruct` yield, `step1` 0xff) deleted
    -- pre-existing contracts and refunded gas EIP-3529 removed. Found deriving
    -- cb-selfdestruct from the spec (Evm.CL.EffectSelfdestruct); the CL was right.
    Evm.Cancun.Vm.Effect.selfdestructEIP6780 frame beneficiary

/-- Trampoline — yield discharge (`handleYield` above) same as
    Osaka's, pinned to Amsterdam's `runFrame` so sub-frames see
    SLOTNUM/DUPN/SWAPN/EXCHANGE/CLZ. -/
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

end Evm.Amsterdam.Vm.Effect
