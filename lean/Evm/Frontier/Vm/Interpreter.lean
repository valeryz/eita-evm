/-
  Evm.Frontier.Vm.Interpreter — opcode dispatcher, fetch-execute loop, and
  the recursive system opcodes (CALL, CREATE, CALLCODE, SELFDESTRUCT).

  EELS reference: ethereum/frontier/vm/interpreter.py and the recursive
  handlers in ethereum/frontier/vm/instructions/system.py.

  The recursive handlers live here (not in `Instructions/System.lean`)
  because they form a mutual cycle with the dispatcher: CALL/CREATE/
  CALLCODE invoke `runFrame` on a fresh sub-frame, which in turn calls
  `dispatch`, which maps 0xf0..0xf2 back to them.

  State semantics: `State` is a value (not a reference), so a sub-call
  that fails simply doesn't propagate its modified `env.state` back to
  the caller — there is no separate snapshot/rollback step. On success
  the caller adopts the sub-frame's `env.state`, accumulated logs,
  refunds, and self-destruct set.

  Frontier specifics:
    * No 63/64 gas-forwarding rule (introduced by TangerineWhistle).
    * `CALL_VALUE` = 9000, stipend = 2300 when value > 0.
    * `NEW_ACCOUNT` = 25000 charged when the callee account is empty.
    * `CREATE` base = 32000; code deposit = 200 per byte; on out-of-gas
      during deposit the contract is left as an empty account at its
      computed address (Frontier behaviour — changed at Homestead via
      EIP-2 to revert the creation entirely).
    * `SELFDESTRUCT` cost = 0; refund = 24000 the first time per tx.
-/

import Evm.BaseTypes
import Evm.Frontier.State
import Evm.Frontier.Utils.Address
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

namespace Evm.Frontier.Vm

open Evm.Frontier.Vm.Instructions
open Evm.Frontier (State)

/-- The hard cap on call-frame nesting depth. -/
def maxCallDepth : Nat := 1024

private def addrToU256 (a : Evm.Address) : Evm.U256 :=
  Evm.U256.ofNat a.toNat

private def u256ToAddr (x : Evm.U256) : Evm.Address :=
  Evm.Address.ofNat x.toNat

/-- Pop seven `U256`s from the stack: `(a, b, c, d, e, f, g, rest)` with
    `a` having been on top. Used by CALL / CALLCODE. -/
private def pop7 (s : Stack) :
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

/-- Merge the side-effects accumulated in a successful sub-frame back
    into the parent. Because `state`, `logs`, `refundCounter`, and
    `selfDestructSet` all live on `Environment`, taking the child's env
    is enough — no concatenation needed. -/
private def mergeChild (parent child : Evm) : Evm :=
  { parent with env := child.env }

/-- 0xff SELFDESTRUCT / SUICIDE — transfer the contract's balance to
    `beneficiary` and mark the contract for deletion. The "first time
    per (account, tx)" refund check consults `env.selfDestructSet`,
    which is now tx-wide (not per-frame) — so repeated SELFDESTRUCTs
    of the same address from different sub-calls don't double-count.

    Non-recursive — lives outside the fuel-bounded mutual block. -/
def selfdestruct : Handler := fun evm => do
  -- EIP-214 (Byzantium+): SELFDESTRUCT is forbidden in static context.
  if evm.message.isStatic then
    .error .writeInStaticContext
  let (beneficiaryW, _) ← Stack.pop evm.stack
  let beneficiary := u256ToAddr beneficiaryW
  let self        := evm.message.currentTarget
  let balance     := evm.env.state.getBalance self

  -- EELS Frontier: the beneficiary is always credited (even on zero
  -- transfer), which creates the account in state if absent. This is
  -- the pre-EIP-161 behaviour; from Spurious Dragon on, the empty
  -- beneficiary check applies.
  let st  := evm.env.state.addBalance beneficiary balance
  let st  := st.setAccount self { (st.getAccount self) with balance := 0 }

  let firstTime := ¬ evm.env.selfDestructSet.contains self
  let refund    := if firstTime then Gas.selfDestructRefund else 0

  return { evm with
    env := { evm.env with
      state := st,
      selfDestructSet :=
        if firstTime then evm.env.selfDestructSet ++ [self]
        else evm.env.selfDestructSet,
      refundCounter := evm.env.refundCounter + refund },
    halted := true }

mutual

/-- Dispatch one opcode byte to its handler. Most cases delegate to a
    handler defined in `Instructions/*.lean`; the recursive system ops
    use the locally-defined `call`/`create`/`callcode`. The `fuel`
    parameter is threaded only to the recursive opcodes. -/
def dispatch (fuel : Nat) (op : UInt8) : Handler :=
  match op.toNat with
  | 0x00 => stop
  | 0x01 => add
  | 0x02 => mul
  | 0x03 => sub
  | 0x04 => div
  | 0x05 => sdiv
  | 0x06 => mod_
  | 0x07 => smod_
  | 0x08 => addmod
  | 0x09 => mulmod
  | 0x0a => Instructions.exp
  | 0x0b => signextend
  | 0x10 => lt
  | 0x11 => gt
  | 0x12 => slt
  | 0x13 => sgt
  | 0x14 => eq
  | 0x15 => iszero
  | 0x16 => and_
  | 0x17 => or_
  | 0x18 => xor_
  | 0x19 => not_
  | 0x1a => byte
  | 0x20 => keccak256
  | 0x30 => address
  | 0x31 => balance
  | 0x32 => origin
  | 0x33 => caller
  | 0x34 => callvalue
  | 0x35 => calldataload
  | 0x36 => calldatasize
  | 0x37 => calldatacopy
  | 0x38 => codesize
  | 0x39 => codecopy
  | 0x3a => gasprice
  | 0x3b => extcodesize
  | 0x3c => extcodecopy
  | 0x40 => blockhash
  | 0x41 => coinbase
  | 0x42 => timestamp
  | 0x43 => number
  | 0x44 => difficulty
  | 0x45 => gaslimit
  | 0x50 => Instructions.pop
  | 0x51 => mload
  | 0x52 => mstore
  | 0x53 => mstore8
  | 0x54 => sload
  | 0x55 => sstore
  | 0x56 => jump
  | 0x57 => jumpi
  | 0x58 => pc
  | 0x59 => msize
  | 0x5a => gas
  | 0x5b => jumpdest
  | 0xf0 => create fuel
  | 0xf1 => call fuel
  | 0xf2 => callcode fuel
  | 0xf3 => return_
  | 0xff => selfdestruct
  | n =>
    if      0x60 ≤ n ∧ n ≤ 0x7f then push (n - 0x5f)
    else if 0x80 ≤ n ∧ n ≤ 0x8f then dup  (n - 0x7f)
    else if 0x90 ≤ n ∧ n ≤ 0x9f then swap (n - 0x8f)
    else if 0xa0 ≤ n ∧ n ≤ 0xa4 then log  (n - 0xa0)
    else fun _ => .error (.invalidOpcode op)
termination_by (fuel, 2)

/-- Single instruction step. Reading past the end of code is an implicit
    STOP (matches EELS). -/
def step (fuel : Nat) (evm : Evm) : Except Exception Evm :=
  if evm.halted then return evm
  else if evm.pc ≥ evm.message.code.size then
    return { evm with halted := true }
  else
    dispatch fuel (evm.message.code.get! evm.pc) evm
termination_by (fuel, 3)

/-- Run the current frame until it halts (or raises an exception). The
    `fuel` parameter is a modelling counter, not part of EVM semantics:
    it bounds the recursion so the function is provably total. Each
    step uses one fuel unit; CALL / CREATE pass `fuel - 1` to the
    sub-frame. -/
def runFrame : Nat → Evm → Except Exception Evm
  | 0,      _   => .error .fuelExhausted
  | fuel+1, evm => do
    let evm' ← step fuel evm
    if evm'.halted then return evm'
    runFrame fuel evm'
termination_by f _ => (f, 0)

/-- 0xf1 CALL — invokes another account. -/
def call : Nat → Handler
  | 0      => fun _   => .error .fuelExhausted
  | fuel+1 => fun evm => do
  let (gasArg, addrW, value, argsOff, argsLen, retOff, retLen, s) ← pop7 evm.stack
  let callee := u256ToAddr addrW
  let argsOffN := argsOff.toNat
  let argsLenN := argsLen.toNat
  let retOffN  := retOff.toNat
  let retLenN  := retLen.toNat

  -- Memory expansion to cover both input and output regions.
  let (gasLeft, mem) ← chargeMemory evm.gasLeft evm.memory argsOffN argsLenN
  let (gasLeft, mem) ← chargeMemory gasLeft mem retOffN retLenN

  -- Frontier extra costs.
  let valueCost      : Nat := if value = (0 : Evm.U256) then 0 else Gas.callValue
  let calleeAccount  := evm.env.state.getAccount callee
  -- NEW_ACCOUNT is charged when the callee is absent from the state
  -- map (Frontier semantics; EELS calls this !account_exists). An
  -- account that exists with zero fields does NOT trigger the charge.
  let newAccountCost : Nat :=
    if evm.env.state.accountExists callee then 0 else Gas.newAccount
  let extraGas       := Gas.call + valueCost + newAccountCost
  let gasLeft ← Gas.charge gasLeft extraGas

  -- Frontier: the full requested `gasArg` is pre-paid from the caller's
  -- remaining gas. If the caller cannot cover it, the frame OOGs (the
  -- behaviour EIP-150 / TangerineWhistle changed: at-and-after that
  -- fork, gasArg is silently capped at 63/64 of remaining).
  let gasLeft ← Gas.charge gasLeft gasArg.toNat
  let gasForward := gasArg.toNat +
                    (if value = (0 : Evm.U256) then 0 else Gas.callStipend)

  -- Depth and balance checks: failure pushes 0 without consuming
  -- the forwarded gas.
  let caller        := evm.message.currentTarget
  let callerBalance := evm.env.state.getBalance caller
  let failFast :=
    evm.message.depth ≥ maxCallDepth ∨
    (value ≠ (0 : Evm.U256) ∧ callerBalance.toNat < value.toNat)
  if failFast then
    let s ← Stack.push s 0
    return { evm with
      gasLeft := gasLeft + gasForward, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }

  -- Pre-EIP-158 "touch" semantics: every CALL to a non-existent
  -- callee creates the account in state, regardless of value. This
  -- is how geth's `exec()` works at this fork (see
  -- core/execution.go), and the reason a repeated value-0 CALL to
  -- the same fresh address doesn't double-charge NEW_ACCOUNT.
  let stateTouched :=
    if evm.env.state.accountExists callee then evm.env.state
    else evm.env.state.setAccount callee Account.empty
  let stateAfterTransfer :=
    if value = (0 : Evm.U256) then stateTouched
    else (stateTouched.subBalance caller value).addBalance callee value

  let input := Evm.Bytes.sliceZeroPad mem argsOffN argsLenN

  -- Dispatch to precompile or to the regular bytecode interpreter.
  let runResult : Except Exception (Evm.Bytes × Nat × Evm) :=
    match PrecompiledContracts.lookup callee with
    | some precompile =>
      match precompile input gasForward with
      | .ok (output, gasLeftSub) =>
        .ok (output, gasLeftSub,
             -- Synthesise a halted sub-frame purely to carry state
             -- through the same merge path as a normal sub-call.
             { gasLeft := gasLeftSub
               message := { caller := caller, target := some callee,
                            currentTarget := callee, value := value,
                            data := input, code := Evm.Bytes.empty,
                            gas := gasForward, depth := evm.message.depth + 1 }
               env := { evm.env with state := stateAfterTransfer }
               halted := true, output := output })
      | .error e => .error e
    | none =>
      let subMsg : Message :=
        { caller := caller, target := some callee, currentTarget := callee,
          value := value, data := input, code := calleeAccount.code,
          gas := gasForward, depth := evm.message.depth + 1 }
      let subEvm := Evm.fresh subMsg { evm.env with state := stateAfterTransfer }
      (runFrame fuel subEvm).map fun s => (s.output, s.gasLeft, s)

  match runResult with
  | .ok (output, gasLeftSub, subEvm) =>
    -- Write output to memory[retOff:retOff+min(retLen, output.size)].
    let writeLen := min retLenN output.size
    let mem := Memory.write mem retOffN (Evm.Bytes.sliceZeroPad output 0 writeLen)
    let merged := mergeChild evm subEvm
    let s ← Stack.push s 1
    return { merged with
      gasLeft := gasLeft + gasLeftSub, memory := mem, stack := s,
      returnData := output, pc := evm.pc + 1 }
  | .error _ =>
    -- Failure: don't merge state; forwarded gas is lost.
    let s ← Stack.push s 0
    return { evm with
      gasLeft := gasLeft, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
termination_by f => (f, 1)

/-- 0xf2 CALLCODE — like CALL but the sub-frame uses the caller's
    storage and balance. The target's code is what runs. -/
def callcode : Nat → Handler
  | 0      => fun _   => .error .fuelExhausted
  | fuel+1 => fun evm => do
  let (gasArg, addrW, value, argsOff, argsLen, retOff, retLen, s) ← pop7 evm.stack
  let codeFrom := u256ToAddr addrW
  let argsOffN := argsOff.toNat
  let argsLenN := argsLen.toNat
  let retOffN  := retOff.toNat
  let retLenN  := retLen.toNat

  let (gasLeft, mem) ← chargeMemory evm.gasLeft evm.memory argsOffN argsLenN
  let (gasLeft, mem) ← chargeMemory gasLeft mem retOffN retLenN

  let valueCost : Nat := if value = (0 : Evm.U256) then 0 else Gas.callValue
  -- CALLCODE: no NEW_ACCOUNT cost (we're calling into the caller's account).
  let extraGas := Gas.call + valueCost
  let gasLeft ← Gas.charge gasLeft extraGas

  -- Pre-EIP-150 gas pre-payment, like CALL above.
  let gasLeft ← Gas.charge gasLeft gasArg.toNat
  let gasForward := gasArg.toNat +
                    (if value = (0 : Evm.U256) then 0 else Gas.callStipend)

  let caller        := evm.message.currentTarget
  let callerBalance := evm.env.state.getBalance caller
  let failFast :=
    evm.message.depth ≥ maxCallDepth ∨
    (value ≠ (0 : Evm.U256) ∧ callerBalance.toNat < value.toNat)
  if failFast then
    let s ← Stack.push s 0
    return { evm with
      gasLeft := gasLeft + gasForward, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }

  let input := Evm.Bytes.sliceZeroPad mem argsOffN argsLenN
  let calleeAccount := evm.env.state.getAccount codeFrom

  let runResult : Except Exception (Evm.Bytes × Nat × Evm) :=
    match PrecompiledContracts.lookup codeFrom with
    | some precompile =>
      match precompile input gasForward with
      | .ok (output, gasLeftSub) =>
        .ok (output, gasLeftSub,
             { gasLeft := gasLeftSub
               message := { caller := caller, target := some codeFrom,
                            currentTarget := caller, value := value,
                            data := input, code := Evm.Bytes.empty,
                            gas := gasForward, depth := evm.message.depth + 1 }
               env := evm.env, halted := true, output := output })
      | .error e => .error e
    | none =>
      let subMsg : Message :=
        { caller := caller, target := some codeFrom, currentTarget := caller,
          value := value, data := input, code := calleeAccount.code,
          gas := gasForward, depth := evm.message.depth + 1 }
      let subEvm := Evm.fresh subMsg evm.env
      (runFrame fuel subEvm).map fun s => (s.output, s.gasLeft, s)

  match runResult with
  | .ok (output, gasLeftSub, subEvm) =>
    let writeLen := min retLenN output.size
    let mem := Memory.write mem retOffN (Evm.Bytes.sliceZeroPad output 0 writeLen)
    let merged := mergeChild evm subEvm
    let s ← Stack.push s 1
    return { merged with
      gasLeft := gasLeft + gasLeftSub, memory := mem, stack := s,
      returnData := output, pc := evm.pc + 1 }
  | .error _ =>
    let s ← Stack.push s 0
    return { evm with
      gasLeft := gasLeft, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
termination_by f => (f, 1)

/-- 0xf0 CREATE — deploy a new contract. -/
def create : Nat → Handler
  | 0      => fun _   => .error .fuelExhausted
  | fuel+1 => fun evm => do
  let (value, offset, len, s) ← Stack.pop3 evm.stack
  let offN := offset.toNat
  let lenN := len.toNat
  let (gasLeft, mem) ← chargeMemory evm.gasLeft evm.memory offN lenN
  let gasLeft ← Gas.charge gasLeft Gas.create

  let sender := evm.message.currentTarget
  let senderAcc := evm.env.state.getAccount sender

  let failFast :=
    evm.message.depth ≥ maxCallDepth ∨
    senderAcc.balance.toNat < value.toNat
  if failFast then
    let s ← Stack.push s 0
    return { evm with
      gasLeft := gasLeft, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }

  -- Derive contract address from pre-increment nonce, then bump nonce.
  let newAddr := Utils.computeContractAddress sender senderAcc.nonce
  let initCode := Evm.Bytes.sliceZeroPad mem offN lenN

  -- Address-collision check: if `newAddr` already has nonzero nonce or
  -- non-empty code, the CREATE opcode fails (push 0) without running
  -- the init code. The forwarded gas — i.e. everything the caller had
  -- left after the 32000 base — is consumed (it was conceptually set
  -- aside for a sub-frame that never ran), so the caller's `gasLeft`
  -- becomes 0 here. The sender's nonce is bumped (per EELS); on
  -- Frontier the caller subsequently OOGs and the bump tx-reverts.
  let collision := evm.env.state.getAccount newAddr
  if collision.nonce > 0 ∨ collision.code.size > 0 then
    let s ← Stack.push s 0
    let stateBumped := evm.env.state.setAccount sender
      { senderAcc with nonce := senderAcc.nonce + 1 }
    return { evm with
      env := { evm.env with state := stateBumped },
      gasLeft := 0, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }

  -- Frontier: forwarded gas is all of evm.gasLeft after CREATE base.
  let gasForward := gasLeft
  let gasLeft    := 0

  let stateAfterSetup :=
    let st := evm.env.state
    let st := st.setAccount sender { senderAcc with
      nonce := senderAcc.nonce + 1,
      balance := senderAcc.balance - value }
    let dest := st.getAccount newAddr
    st.setAccount newAddr { dest with balance := dest.balance + value }

  let subMsg : Message :=
    { caller := sender, target := some newAddr, currentTarget := newAddr,
      value := value, data := Evm.Bytes.empty, code := initCode,
      gas := gasForward, depth := evm.message.depth + 1 }
  let subEvm := Evm.fresh subMsg { evm.env with state := stateAfterSetup }

  match runFrame fuel subEvm with
  | .ok subEvm =>
    -- Charge 200 gas per byte of deployed code; Frontier behaviour on
    -- insufficient gas is to leave the new contract with empty code
    -- but keep the balance transfer (changed at Homestead, EIP-2).
    let codeBytes := subEvm.output
    let depositCost := Gas.codeDeposit * codeBytes.size
    let (finalState, refundedGas) :=
      if subEvm.gasLeft < depositCost then
        (subEvm.env.state, 0)  -- empty code, gas all consumed
      else
        let st := subEvm.env.state.setAccount newAddr
                    { (subEvm.env.state.getAccount newAddr) with code := codeBytes }
        (st, subEvm.gasLeft - depositCost)
    let merged := mergeChild evm { subEvm with env := { subEvm.env with state := finalState } }
    let s ← Stack.push s (addrToU256 newAddr)
    return { merged with
      gasLeft := gasLeft + refundedGas, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
  | .error _ =>
    -- Init code failed. Per Frontier: revert the balance transfer but
    -- KEEP the sender's nonce bump.
    let stateAfterNonceBump :=
      evm.env.state.setAccount sender { senderAcc with
        nonce := senderAcc.nonce + 1 }
    let s ← Stack.push s 0
    return { evm with
      env := { evm.env with state := stateAfterNonceBump },
      gasLeft := gasLeft, memory := mem, stack := s,
      returnData := Evm.Bytes.empty, pc := evm.pc + 1 }
termination_by f => (f, 1)

end -- mutual

/-- Default fuel ceiling for top-level entry points. Sized to be well
    in excess of anything a single Ethereum block can drive: the gas
    limit is ~30M and the cheapest opcode is 1 gas, so a generous
    upper bound on per-block step count is ~30M; this leaves several
    orders of magnitude of headroom. Only the totality story depends
    on `runFrame`'s fuel — at runtime we never exhaust it. -/
def defaultFuel : Nat := 1 <<< 30

/-- Convenience: run a `Message` against `env` to completion. -/
def applyMessage (msg : Message) (env : Environment) : Except Exception Evm :=
  runFrame defaultFuel (Evm.fresh msg env)

end Evm.Frontier.Vm
