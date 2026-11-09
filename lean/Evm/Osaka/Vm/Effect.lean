/-
  Evm.Osaka.Vm.Effect — yield-based execution for the Osaka (Fusaka)
  fork.

  EELS reference: `forks/osaka/vm/instructions/__init__.py` (dispatch
  table) and `forks/osaka/vm/instructions/bitwise.py::count_leading_zeros`
  (the lone new opcode at the EVM layer).

  Delta on Prague at the EVM dispatcher level:

    * EIP-7939: CLZ (0x1E) — count-leading-zeros. Pops one U256, pushes
      `256 - bit_length(x)` (so CLZ(0) = 256). Gas: LOW (= 5).
      EELS: `forks/osaka/vm/instructions/bitwise.py` `count_leading_zeros`
      (lines 90-115); gas constant
      `GasCosts.OPCODE_CLZ = LOW` in `forks/osaka/vm/gas.py` line 196.

  All other opcodes inherit from Prague — i.e. from the existing
  Byzantium-shape interpreter that Prague delegates to. We intercept
  only 0x1E and fall through everywhere else.

  Prague's `Vm.Effect.applyMessage` routes through
  `Evm.Byzantium.Vm.Effect.applyMessage` (see the comment in
  `Evm/Prague/Vm/Effect.lean`); we mirror the same pattern but install
  Osaka's `step1` (which intercepts CLZ) by piggybacking on the
  pre-existing trampolines. Concretely: since Prague chains all the way
  down to Byzantium's `step1`, we install Osaka by wrapping Byzantium's
  trampoline with a CLZ pre-check at the message entry — there is no
  fork-local dispatcher above Byzantium yet, so the cleanest place is
  a thin wrapper that:

    1. If the first byte at `pc` is CLZ, executes CLZ directly.
    2. Otherwise hands off to `Byzantium.Vm.Effect.applyMessage`.

  This is _not_ the right shape for a code that uses CLZ in the middle
  of a frame (the inner Byzantium dispatcher would error with
  `.invalidOpcode` on 0x1E); the proper fix is a full Osaka `runFrame`
  that intercepts 0x1E per-step. That's the shape this module follows.

  The trampoline is identical to Byzantium's modulo the bound `step1`.
-/

import Evm.BaseTypes
import Evm.Byzantium.Vm.Effect
import Evm.Cancun.Vm.Effect
import Evm.Prague.Vm.Effect

namespace Evm.Osaka.Vm.Effect

open Evm.Frontier.Vm
open Evm.Byzantium.Vm.Effect (StepResult Step CallKind YieldEffect liftPure
                                addrToU256 u256ToAddr maxCallDepth mergeChild)

/-! ## EIP-7939 CLZ -/

/-- Count the number of one-prefix bits needed to encode a Nat: the
    smallest `k` such that `n < 2^k`. `bitLengthAux n 0`. Tail-recursive
    on `n / 2`. Equivalent to Python's `int.bit_length()`. -/
private def bitLengthAux : Nat → Nat → Nat
  | 0,        acc => acc
  | n@(_+1),  acc => bitLengthAux (n >>> 1) (acc + 1)

/-- Count leading zero bits of a 256-bit word. EELS reference:
    `ethereum_types.numeric.U256.bit_length` (computes the smallest `k`
    such that `x < 2^k`; equivalently the position of the highest set
    bit, with `bit_length(0) = 0`). CLZ pushes `256 - bit_length(x)`,
    so CLZ(0) = 256 and CLZ(top-bit-set) = 0. -/
def clzU256 (x : Evm.U256) : Evm.U256 :=
  Evm.U256.ofNat (256 - bitLengthAux x.toNat 0)

/-- 0x1E CLZ. EELS `forks/osaka/vm/instructions/bitwise.py`
    `count_leading_zeros` (line ~90); gas = LOW (`OPCODE_CLZ` in
    `forks/osaka/vm/gas.py`). Stack: pops one value, pushes
    `256 - bit_length(x)`. -/
def doClz (evm : Evm) : StepResult :=
  match Stack.pop evm.stack with
  | .error e => .error evm e
  | .ok (x, rest) =>
    match Gas.charge evm.gasLeft Gas.low with
    | .error e => .error evm e
    | .ok gasLeft =>
      match Stack.push rest (clzU256 x) with
      | .error e => .error evm e
      | .ok s    => .continue { evm with gasLeft := gasLeft, stack := s,
                                          pc := evm.pc + 1 }

/-! ## Step dispatch -/

/-- Osaka single-step. Intercepts EIP-7939 CLZ (0x1E); everything else
    falls through to Paris → Byzantium. Prague has no pre-existing
    `step1` of its own (its `Vm/Effect.lean` is a thin delegation
    wrapper into Byzantium); Shanghai's `step1` currently has an
    independent build issue (`maxCallDepth` ambiguity from
    `open Evm.Frontier.Vm`). We therefore chain through Paris's
    `step1` so this file is self-contained, and explicitly mark
    PUSH0 (EIP-3855) and the EIP-3860 CREATE/CREATE2 surcharges as
    TODOs reachable from Osaka frames once the predecessor chain is
    repaired. -/
def step1 (evm : Evm) : StepResult :=
  if evm.halted then .halt evm evm.output
  else if evm.pc ≥ evm.message.code.size then
    .halt { evm with halted := true } evm.output
  else
    let op := evm.message.code.get! evm.pc
    match op.toNat with
    | 0x1e => doClz evm                          -- EIP-7939
    -- Fall through to Cancun's step1 (gives PUSH0/EIP-3860 via Shanghai,
    -- PREVRANDAO via Paris, EIP-2929 warm/cold via Berlin, EIP-2200 SSTORE
    -- via Istanbul, etc.). Prague-specific EIP-7702 delegation is handled
    -- at the message level in `Evm.Prague.Vm.Effect.applyMessage`, not at
    -- the opcode level, so step1 fall-through bypasses it (matches EELS:
    -- delegation resolution is a `prepare_message`-time rewrite).
    | _    => _root_.Evm.Cancun.Vm.Effect.step1 evm

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
    Evm.Frontier.Vm.Call.resume (Evm.Frontier.Vm.Call.Rules.ofOrd 18) frame subMsg.currentTarget
      retOff retLen
      (Evm.Frontier.Vm.Call.runChild (fun _ => Evm.Frontier.Vm.Call.precompiles 18) frame subMsg code stateForSub runSub)
  | .createLike subMsg newAddr stateForSub _ _ _ _ _ _ _ =>
    -- EELS process_create_message + incorporate_child_* (Evm.Frontier.Vm.Create.resume).
    Evm.Frontier.Vm.Create.resume (Evm.Frontier.Vm.Create.Rules.ofOrd 18) frame newAddr
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
    -- EIP-6780, unchanged since Cancun (EELS osaka/vm/instructions/system.py selfdestruct
    -- = cancun's): the Cancun effect. Until 2026-10-26 this arm was the FRONTIER form —
    -- every SELFDESTRUCT queued for deletion with a 24000 refund — so the spec's Osaka
    -- SELFDESTRUCT (reached through Cancun's `doSelfdestruct` yield, `step1` 0xff) deleted
    -- pre-existing contracts and refunded gas EIP-3529 removed. Found deriving
    -- cb-selfdestruct from the spec (Evm.CL.EffectSelfdestruct); the CL was right.
    Evm.Cancun.Vm.Effect.selfdestructEIP6780 frame beneficiary

/-- Trampoline — yield discharge (`handleYield` above) same as
    Shanghai's. Bound to Osaka's `runFrame` so sub-frames also see
    CLZ. -/
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

end Evm.Osaka.Vm.Effect
