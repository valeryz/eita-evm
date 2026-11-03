/-
  Evm.Frontier.Spec.FrameRun — whole-frame execution + CALL merge.

  Closes the gap left by `CallStep.lean` (which only specs the
  CALL entry phase). A full CALL relation requires three pieces:

    1. `IsCallEntrySuccess` — already in CallStep.lean.
    2. `IsFrameRun` — "this is a valid execution of a full frame
       from start to halt". Recursive: a frame can do a CALL,
       which is itself a `IsCallFrame`.
    3. `IsCallMerge` — given the sub-frame's halted state, what's
       the parent's resumed state.

  The recursion is via mutual inductive: `IsFrameRun` references
  `IsCallFrame`, which references `IsFrameRun` for the sub-frame.
  Lean's structural-recursion checker accepts the inductive
  family because each constructor produces a smaller proof tree
  (no constructor produces a `IsFrameRun` from a `IsFrameRun` of
  the same `evm`).

  Status: the SHAPE of the relations is locked in. Several
  constructors carry `sorry`-typed bodies as placeholders for the
  per-opcode step relations (IsAddStep, IsMulStep, …) that aren't
  yet woven into the IsAnyStep dispatcher. This file establishes
  the framework; filling in IsAnyStep is a follow-up that takes a
  step-by-step pass through the dispatch table.
-/

import Evm.Frontier.Spec.Step
import Evm.Frontier.Spec.MemStep
import Evm.Frontier.Spec.StorageStep
import Evm.Frontier.Spec.StateStep
import Evm.Frontier.Spec.CallStep
import Evm.Frontier.Spec.SelfdestructStep
import Evm.Frontier.Vm.Instructions.ControlFlow

namespace Evm.Frontier.Spec

open Evm.Frontier.Vm

/-! ## Halt cause

    A halted frame is in one of five states. `IsCallMerge`
    dispatches on this because each case merges differently:
    - `stop` / `runOff`: state from sub-frame is merged into parent,
      output is empty, parent gets gas refund.
    - `return`: state merged, output preserved, gas refunded.
    - `revert`: state NOT merged (parent reverts to its snapshot),
      output preserved, gas refunded.
    - `selfdestruct`: state merged, contract queued for deletion.
    - `exception`: sub-frame raised (OOG / stack fault / invalid op).
      State NOT merged, no output, and — Frontier-specifically — no
      gas refund: an erroring frame consumed everything (no REVERT
      until Byzantium), so EELS `incorporate_child_on_error`'s
      `gas_left += child.gas_left` is a no-op. -/

inductive HaltCause where
  | stop
  | return_ (output : Evm.Bytes)
  | revert_ (output : Evm.Bytes)
  | selfdestruct (beneficiary : Evm.Address)
  | exception
  deriving Inhabited

/-! ## Halting opcodes: STOP (0x00), RETURN (0xf3)

    EELS `stop` (frontier/vm/instructions/control_flow.py): charge
    nothing, `evm.running = False`, `evm.pc += 1`.

    STATED DIVERGENCE: this spec pins the halted frame's pc at
    STOP's own pc (no `+ 1`), matching the executable
    (`Effect.step1`) and the IR's `endPc` convention. The pc of a
    halted frame is unobservable at the frame boundary — call
    merges (`IsCallMerge`) read only gas, output, and state — so
    the divergence cannot change any observable result; it is
    surfaced here rather than silently absorbed. -/

def IsStopStep (evm evm' : Evm) : Prop :=
  evm' = { evm with halted := true }

/-- RETURN — EELS `return_` (frontier/vm/instructions/system.py):
    pop offset and size, charge `GAS_ZERO (= 0) + memory expansion`,
    expand memory, set output to the memory slice, halt, pc += 1. -/
def IsReturnStep (evm evm' : Evm) : Prop :=
  ∃ offset length rest,
    evm.stack = offset :: length :: rest ∧
    let off := offset.toNat
    let len := length.toNat
    let totalGas := memExpansionGas evm.memory off len
    evm.gasLeft ≥ totalGas ∧
    let mem' := memAfterExpand evm.memory off len
    evm' = { evm with
      stack   := rest,
      memory  := mem',
      gasLeft := evm.gasLeft - totalGas,
      output  := Memory.read mem' off len,
      halted  := true,
      pc      := evm.pc + 1 }

/-! ## Control-flow steps: JUMP (0x56), JUMPI (0x57)

    EELS `jump` / `jumpi` (frontier/vm/instructions/control_flow.py):
    charge GAS_MID / GAS_HIGH, pop destination (and condition), and
    transfer control iff the destination is a valid JUMPDEST.

    Jump validity is expressed via the executable's own
    `Instructions.isValidJumpDest` (cached-bitmap check with
    linear-scan fallback) rather than the ground-truth
    `Runtime.isJumpDest` scan, so handler/IR/spec agree
    definitionally. The bitmap-correctness obligation
    (`jumpDestBitmap` agrees with `validJumpDests`) is deliberately
    OUTSIDE these relations — see the note on `isValidJumpDest`. -/

def IsJumpStep (evm evm' : Evm) : Prop :=
  ∃ dest rest,
    evm.stack = dest :: rest ∧
    evm.gasLeft ≥ Gas.mid ∧
    Instructions.isValidJumpDest evm dest.toNat = true ∧
    evm' = { evm with gasLeft := evm.gasLeft - Gas.mid,
                      stack := rest, pc := dest.toNat }

def IsJumpiStep (evm evm' : Evm) : Prop :=
  ∃ dest cond rest,
    evm.stack = dest :: cond :: rest ∧
    evm.gasLeft ≥ Gas.high ∧
    ((cond = 0 ∧
      evm' = { evm with gasLeft := evm.gasLeft - Gas.high,
                        stack := rest, pc := evm.pc + 1 }) ∨
     (cond ≠ 0 ∧
      Instructions.isValidJumpDest evm dest.toNat = true ∧
      evm' = { evm with gasLeft := evm.gasLeft - Gas.high,
                        stack := rest, pc := dest.toNat }))

/-! ## Per-opcode step dispatch (placeholder)

    `IsAnyStep` should case-split on `code[pc]` and delegate to the
    appropriate `IsXxxStep` relation. Filling this in is the
    natural follow-up; for now it's `False` for unhandled opcodes
    (so a frame trace that hits one of them is unprovable, which
    is the safe default).

    Wiring: each branch is `IsAddStep evm evm'` etc. The relation
    fires when `evm.message.code[evm.pc]?.toNat == 0x01`, etc. -/

def IsAnyStep (evm evm' : Evm) : Prop :=
  match evm.message.code[evm.pc]? with
  | none => evm' = { evm with halted := true }  -- ran off end of code
  | some op =>
    match op.toNat with
    | 0x00 => IsStopStep evm evm'
    | 0x01 => IsAddStep evm evm'
    | 0x02 => IsMulStep evm evm'
    | 0x03 => IsSubStep evm evm'
    | 0x04 => IsDivStep evm evm'
    | 0x05 => IsSdivStep evm evm'
    | 0x06 => IsModStep evm evm'
    | 0x07 => IsSmodStep evm evm'
    | 0x08 => IsAddmodStep evm evm'
    | 0x09 => IsMulmodStep evm evm'
    | 0x0a => IsExpStep evm evm'
    | 0x0b => IsSignextendStep evm evm'
    | 0x10 => IsLtStep evm evm'
    | 0x11 => IsGtStep evm evm'
    | 0x12 => IsSltStep evm evm'
    | 0x13 => IsSgtStep evm evm'
    | 0x14 => IsEqStep evm evm'
    | 0x15 => IsIszeroStep evm evm'
    | 0x16 => IsAndStep evm evm'
    | 0x17 => IsOrStep  evm evm'
    | 0x18 => IsXorStep evm evm'
    | 0x19 => IsNotStep evm evm'
    | 0x1a => IsByteStep evm evm'
    | 0x20 => IsKeccak256Step evm evm'
    | 0x30 => IsAddressStep evm evm'
    | 0x31 => IsBalanceStep evm evm'
    | 0x32 => IsOriginStep evm evm'
    | 0x33 => IsCallerStep evm evm'
    | 0x34 => IsCallvalueStep evm evm'
    | 0x35 => IsCalldataloadStep evm evm'
    | 0x36 => IsCalldatasizeStep evm evm'
    | 0x37 => IsCalldatacopyStep evm evm'
    | 0x38 => IsCodesizeStep evm evm'
    | 0x39 => IsCodecopyStep evm evm'
    | 0x3a => IsGaspriceStep evm evm'
    | 0x3b => IsExtcodesizeStep evm evm'
    | 0x3c => IsExtcodecopyStep evm evm'
    | 0x40 => IsBlockhashStep evm evm'
    | 0x41 => IsCoinbaseStep evm evm'
    | 0x42 => IsTimestampStep evm evm'
    | 0x43 => IsNumberStep evm evm'
    | 0x44 => IsDifficultyStep evm evm'
    | 0x45 => IsGaslimitStep evm evm'
    | 0x50 => IsPopStep Gas.base evm evm'
    | 0x51 => IsMloadStep   evm evm'
    | 0x52 => IsMstoreStep  evm evm'
    | 0x53 => IsMstore8Step evm evm'
    | 0x54 => IsSloadStep   evm evm'
    | 0x55 => IsSstoreStep  evm evm'
    | 0x56 => IsJumpStep  evm evm'
    | 0x57 => IsJumpiStep evm evm'
    | 0x58 => IsPcStep evm evm'
    | 0x59 => IsMsizeStep evm evm'
    | 0x5a => IsGasStep evm evm'
    | 0x5b => IsJumpdestStep evm evm'
    | 0xf3 => IsReturnStep evm evm'
    | 0xff => IsSelfdestructStep evm evm'
    | n =>
      -- PUSH1 (0x60) … PUSH32 (0x7f)
      if 0x60 ≤ n ∧ n ≤ 0x7f then IsPushStep (n - 0x5f) Gas.veryLow evm evm'
      -- DUP1 (0x80) … DUP16 (0x8f)
      else if 0x80 ≤ n ∧ n ≤ 0x8f then IsDupStep (n - 0x7f) Gas.veryLow evm evm'
      -- SWAP1 (0x90) … SWAP16 (0x9f)
      else if 0x90 ≤ n ∧ n ≤ 0x9f then IsSwapStep (n - 0x8f) Gas.veryLow evm evm'
      -- LOG0 (0xa0) … LOG4 (0xa4)
      else if 0xa0 ≤ n ∧ n ≤ 0xa4 then IsLogStep (n - 0xa0) evm evm'
      else False  -- TODO: REVERT (Byzantium+), CALL family, CREATE.

/-! ## CALL merge — sub-frame's halt cause determines parent's resume -/

def IsCallMerge (parent : Evm) (setup : SubFrameSetup) (subFinal : Evm)
                 (cause : HaltCause) (parent' : Evm) : Prop :=
  match cause with
  | .return_ output =>
    let writeLen := min setup.retLen output.size
    let mem := Memory.write parent.memory setup.retOff
                 (Evm.Bytes.sliceZeroPad output 0 writeLen)
    parent' = { setup.parentSnapshot with
      stack       := (1 : Evm.U256) :: setup.parentSnapshot.stack,
      memory      := mem,
      gasLeft     := setup.parentSnapshot.gasLeft + subFinal.gasLeft,
      env         := subFinal.env,
      returnData  := output,
      pc          := setup.parentSnapshot.pc + 1 }
  | .stop =>
    parent' = { setup.parentSnapshot with
      stack       := (1 : Evm.U256) :: setup.parentSnapshot.stack,
      gasLeft     := setup.parentSnapshot.gasLeft + subFinal.gasLeft,
      env         := subFinal.env,
      returnData  := Evm.Bytes.empty,
      pc          := setup.parentSnapshot.pc + 1 }
  | .revert_ output =>
    let writeLen := min setup.retLen output.size
    let mem := Memory.write parent.memory setup.retOff
                 (Evm.Bytes.sliceZeroPad output 0 writeLen)
    parent' = { setup.parentSnapshot with
      stack       := (0 : Evm.U256) :: setup.parentSnapshot.stack,
      memory      := mem,
      gasLeft     := setup.parentSnapshot.gasLeft + subFinal.gasLeft,
      returnData  := output,
      pc          := setup.parentSnapshot.pc + 1 }
  | .exception =>
    -- Frontier: erroring sub-frame has gas_left = 0, so the parent
    -- keeps exactly its snapshot gas (the forwarded gas is lost).
    -- State and memory unchanged; 0 pushed; returnData cleared.
    parent' = { setup.parentSnapshot with
      stack       := (0 : Evm.U256) :: setup.parentSnapshot.stack,
      returnData  := Evm.Bytes.empty,
      pc          := setup.parentSnapshot.pc + 1 }
  | .selfdestruct _ =>
    parent' = { setup.parentSnapshot with
      stack       := (1 : Evm.U256) :: setup.parentSnapshot.stack,
      gasLeft     := setup.parentSnapshot.gasLeft + subFinal.gasLeft,
      env         := subFinal.env,
      returnData  := Evm.Bytes.empty,
      pc          := setup.parentSnapshot.pc + 1 }

/-! ## Frame-run relation — mutually recursive with IsCallFrame

    `IsFrameRun evm cause evm'`: starting from `evm`, executing
    the frame to its halt produces `evm'` (the final frame state)
    and the `cause` of halt.

    Constructors:
    - `halted`: evm is already halted; trivial reflexive case.
    - `step`: take any valid one-step transition, then continue.
    - `callStep`: the current opcode is CALL; embed an
      `IsCallFrame` and continue with the resumed parent.
-/

mutual

inductive IsFrameRun : Evm → HaltCause → Evm → Prop where
  /-- Already halted: zero-step trace, return same frame with cause. -/
  | done (evm : Evm) (cause : HaltCause) :
      evm.halted = true →
      -- The cause must be consistent with how evm reached its
      -- halted state. The spec doesn't enforce this constructively
      -- (it's an invariant earned by following the rules); a
      -- well-formed trace will only use this constructor when
      -- the cause matches.
      IsFrameRun evm cause evm

  /-- Take one non-recursive opcode step, then continue. The step
      relation is `IsAnyStep` (defined below). -/
  | step (evm evm_mid evm' : Evm) (cause : HaltCause) :
      IsAnyStep evm evm_mid →
      IsFrameRun evm_mid cause evm' →
      IsFrameRun evm cause evm'

  /-- Take a recursive CALL step, then continue. `IsCallFrame`
      handles entry + sub-execution + merge in one go; the result
      is the parent frame's post-CALL state. -/
  | callStep (evm evm_mid evm' : Evm) (cause : HaltCause) :
      IsCallFrame evm evm_mid →
      IsFrameRun evm_mid cause evm' →
      IsFrameRun evm cause evm'

/-- The whole-CALL relation. Captures entry, sub-execution, and
    merge. -/
inductive IsCallFrame : Evm → Evm → Prop where
  /-- Sub-frame ran to completion. The parent's resumed state
      depends on the sub-frame's halt cause via `IsCallMerge`.
      `subEntry` is required to be the fresh sub-frame derived
      from `setup`; the equation is a premise rather than baked
      into the constructor. -/
  | spawn (parent parent' : Evm) (setup : SubFrameSetup)
          (subEntry subFinal : Evm) (cause : HaltCause) :
      IsCallEntrySuccess parent setup →
      subEntry = (Evm.fresh setup.subMsg
                  { parent.env with state := setup.subState }) →
      IsFrameRun subEntry cause subFinal →
      IsCallMerge parent setup subFinal cause parent' →
      IsCallFrame parent parent'

  /-- Pre-execution failFast on depth — no sub-frame spawned. -/
  | failFastDepth (evm evm' : Evm) :
      IsCallFailFastDepth evm evm' →
      IsCallFrame evm evm'

  /-- Pre-execution failFast on balance — no sub-frame spawned. -/
  | failFastBalance (evm evm' : Evm) :
      IsCallFailFastBalance evm evm' →
      IsCallFrame evm evm'

end

/-! ## Notes

    - The mutual induction terminates structurally: each
      constructor produces a `IsFrameRun` / `IsCallFrame` proof
      from STRICTLY SMALLER sub-proofs. Lean accepts the
      definition as well-founded.

    - The relation is INTENTIONALLY non-deterministic about the
      sub-frame's execution path — a frame can go through many
      valid traces depending on internal choices. Any of them
      satisfies `IsFrameRun`, and `IsCallFrame.spawn` admits any
      such trace as the sub-frame's behaviour. The IMPLEMENTATION
      must pick one valid trace and stick with it; the SPEC
      accepts any.

    - `IsAnyStep`'s dispatch table is incomplete (missing REVERT,
      JUMP, JUMPI, DUP-n, SWAP-n, environment lookups, LOG-n,
      CREATE, SELFDESTRUCT). Filling it is the natural follow-up;
      for now any frame trace that hits one of those opcodes is
      unprovable, which is the safe default — refinement against
      the executable will fail at the missing opcode, surfacing
      the gap.

    - `IsCallMerge` is the most subtle relation in the spec. The
      five branches each capture a different semantic of CALL's
      return path. Refinement against `Effect.trampoline`'s
      `resumeCallOk` / `resumeCallErr` / `resumeCallRevert` will
      verify each branch corresponds to the right executable
      arm. -/

end Evm.Frontier.Spec
