/-
  Evm.IR.Trampoline — per-terminator dispatch for CALL / CREATE /
  SELFDESTRUCT and the other chunk terminators.

  The trampoline is what binds the per-chunk story together: when a
  chunk's terminator is `.call` / `.create`, the trampoline does the
  gas math (EIP-150 cap, value-fee, stipend), builds the sub-frame,
  runs it, processes the result (gas refund, output copy, success
  push), and resumes the parent.

  Same principle as `Evm.IR.Dispatch` (Phase 2a): the IR terminator's
  semantics IS the corresponding Effect-layer function — no second
  encoding of the math. The bugs that produced the 25% GST failure
  rate in the previous push were ALL hand-encoded trampoline math
  (cb_call / cb_create / cb_selfdestruct in src/evm/calls.lisp
  drifting from spec). Binding instead of re-encoding makes that
  drift unrepresentable; the per-terminator soundness theorems are
  correspondingly definitional (`rfl`), and the SUBSTANTIVE proof
  obligations live where they belong:

    * `Effect.doCall` / `doCallcode` / `doCreate` vs the Spec
      relations (`IsCallFailFast*`, `IsCallEntrySuccess`) — see
      `Evm.Frontier.Spec.CallRefinement`.
    * `Effect.resumeCall*` / `Create.resume` vs `IsCallMerge` —
      same file.
    * `Effect.handleYield` ties yield → resume; the IR trampoline
      re-exports it (`runYield`), so anything proven about
      `handleYield` covers the IR side verbatim.

  The recursion knot (`runSub`) stays a parameter — the design doc's
  `hSub` hypothesis: sub-frame execution refines its own spec; with
  that assumed, the wrapper math here is verified.

  Per-fork dispatch (#223): five fork modules define their own
  `StepResult` inductive (Frontier, Homestead, TangerineWhistle,
  SpuriousDragon, Byzantium — each adding `CallKind` constructors);
  Constantinople onward reuse Byzantium's. `StepResultOf` maps each
  fork to its family's type, and `Terminator.stepHandler` binds, per
  fork, exactly the Effect function that fork's own `step1` binds —
  including the Berlin EIP-2929 and Shanghai EIP-3860 overrides and
  Cancun's EIP-6780 yield-based SELFDESTRUCT.
-/

import Evm.IR.Types
import Evm.Forks
import Evm.Frontier.Vm.Effect
import Evm.Homestead.Vm.Effect
import Evm.TangerineWhistle.Vm.Effect
import Evm.SpuriousDragon.Vm.Effect
import Evm.Byzantium.Vm.Effect
import Evm.Byzantium.Vm.Instructions.System
import Evm.Constantinople.Vm.Effect
import Evm.Petersburg.Vm.Effect
import Evm.Istanbul.Vm.Effect
import Evm.Berlin.Vm.Effect
import Evm.London.Vm.Effect
import Evm.Paris.Vm.Effect
import Evm.Shanghai.Vm.Effect
import Evm.Cancun.Vm.Effect
import Evm.Osaka.Vm.Effect
import Evm.Amsterdam.Vm.Effect

namespace Evm.IR.Trampoline

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions
open Evm.Frontier.Vm.Effect (StepResult YieldEffect)

/-! ## The per-fork StepResult family

    `Evm` / `Exception` / `Handler` are the single shared Frontier
    types across every fork module; only the Effect-layer inductives
    (`StepResult` / `YieldEffect` / `CallKind`) are redefined when a
    fork adds a `CallKind` constructor. -/

/-- The `StepResult` type a fork's Effect layer produces. Forks that
    do not redefine it map to their family head (Byzantium for
    everything ≥ byzantium, Homestead for daoFork). -/
def StepResultOf : Evm.Fork → Type
  | .frontier => Evm.Frontier.Vm.Effect.StepResult
  | .homestead | .daoFork => Evm.Homestead.Vm.Effect.StepResult
  | .tangerineWhistle => Evm.TangerineWhistle.Vm.Effect.StepResult
  | .spuriousDragon => Evm.SpuriousDragon.Vm.Effect.StepResult
  | _ => Evm.Byzantium.Vm.Effect.StepResult

/-- The `Step` type a fork's Effect layer produces — same family map
    as `StepResultOf`. A `Step` is a `StepResult` minus `.continue`:
    the shape a whole program run ends in. -/
def StepOf : Evm.Fork → Type
  | .frontier => Evm.Frontier.Vm.Effect.Step
  | .homestead | .daoFork => Evm.Homestead.Vm.Effect.Step
  | .tangerineWhistle => Evm.TangerineWhistle.Vm.Effect.Step
  | .spuriousDragon => Evm.SpuriousDragon.Vm.Effect.Step
  | _ => Evm.Byzantium.Vm.Effect.Step

/-- The `YieldEffect` type a fork's Effect layer yields — same family
    map as `StepResultOf`. -/
def YieldEffectOf : Evm.Fork → Type
  | .frontier => Evm.Frontier.Vm.Effect.YieldEffect
  | .homestead | .daoFork => Evm.Homestead.Vm.Effect.YieldEffect
  | .tangerineWhistle => Evm.TangerineWhistle.Vm.Effect.YieldEffect
  | .spuriousDragon => Evm.SpuriousDragon.Vm.Effect.YieldEffect
  | _ => Evm.Byzantium.Vm.Effect.YieldEffect

/-! Fork-indexed plumbing for the family: the chunk runner
    (`Evm.IR.Execute`) is generic in the fork, so it cannot name a
    family's constructors directly — these helpers dispatch on the
    fork and apply the family's own constructor / `liftPure`. Every
    arm is a literal fork constructor so the matcher iota-reduces and
    the Frontier-pinned `rfl` soundness proofs keep holding
    definitionally. -/

/-- Fork-indexed `liftPure`: lift a total `Handler` (shared Frontier
    type) into the fork's own `StepResult` — each arm IS that
    family's `liftPure`. -/
def StepResultOf.liftPure :
    (fork : Evm.Fork) → Handler → Evm → StepResultOf fork
  | .frontier         => Evm.Frontier.Vm.Effect.liftPure
  | .homestead        => Evm.Homestead.Vm.Effect.liftPure
  | .daoFork          => Evm.Homestead.Vm.Effect.liftPure
  | .tangerineWhistle => Evm.TangerineWhistle.Vm.Effect.liftPure
  | .spuriousDragon   => Evm.SpuriousDragon.Vm.Effect.liftPure
  | .byzantium        => Evm.Byzantium.Vm.Effect.liftPure
  | .constantinople   => Evm.Byzantium.Vm.Effect.liftPure
  | .petersburg       => Evm.Byzantium.Vm.Effect.liftPure
  | .istanbul         => Evm.Byzantium.Vm.Effect.liftPure
  | .muirGlacier      => Evm.Byzantium.Vm.Effect.liftPure
  | .berlin           => Evm.Byzantium.Vm.Effect.liftPure
  | .london           => Evm.Byzantium.Vm.Effect.liftPure
  | .arrowGlacier     => Evm.Byzantium.Vm.Effect.liftPure
  | .grayGlacier      => Evm.Byzantium.Vm.Effect.liftPure
  | .paris            => Evm.Byzantium.Vm.Effect.liftPure
  | .shanghai         => Evm.Byzantium.Vm.Effect.liftPure
  | .cancun           => Evm.Byzantium.Vm.Effect.liftPure
  | .prague           => Evm.Byzantium.Vm.Effect.liftPure
  | .osaka            => Evm.Byzantium.Vm.Effect.liftPure
  | .bpo1             => Evm.Byzantium.Vm.Effect.liftPure
  | .bpo2             => Evm.Byzantium.Vm.Effect.liftPure
  | .amsterdam        => Evm.Byzantium.Vm.Effect.liftPure

/-- Fork-indexed `.error` constructor for `StepResultOf`. -/
def StepResultOf.error :
    (fork : Evm.Fork) → Evm → Exception → StepResultOf fork
  | .frontier         => Evm.Frontier.Vm.Effect.StepResult.error
  | .homestead        => Evm.Homestead.Vm.Effect.StepResult.error
  | .daoFork          => Evm.Homestead.Vm.Effect.StepResult.error
  | .tangerineWhistle => Evm.TangerineWhistle.Vm.Effect.StepResult.error
  | .spuriousDragon   => Evm.SpuriousDragon.Vm.Effect.StepResult.error
  | .byzantium        => Evm.Byzantium.Vm.Effect.StepResult.error
  | .constantinople   => Evm.Byzantium.Vm.Effect.StepResult.error
  | .petersburg       => Evm.Byzantium.Vm.Effect.StepResult.error
  | .istanbul         => Evm.Byzantium.Vm.Effect.StepResult.error
  | .muirGlacier      => Evm.Byzantium.Vm.Effect.StepResult.error
  | .berlin           => Evm.Byzantium.Vm.Effect.StepResult.error
  | .london           => Evm.Byzantium.Vm.Effect.StepResult.error
  | .arrowGlacier     => Evm.Byzantium.Vm.Effect.StepResult.error
  | .grayGlacier      => Evm.Byzantium.Vm.Effect.StepResult.error
  | .paris            => Evm.Byzantium.Vm.Effect.StepResult.error
  | .shanghai         => Evm.Byzantium.Vm.Effect.StepResult.error
  | .cancun           => Evm.Byzantium.Vm.Effect.StepResult.error
  | .prague           => Evm.Byzantium.Vm.Effect.StepResult.error
  | .osaka            => Evm.Byzantium.Vm.Effect.StepResult.error
  | .bpo1             => Evm.Byzantium.Vm.Effect.StepResult.error
  | .bpo2             => Evm.Byzantium.Vm.Effect.StepResult.error
  | .amsterdam        => Evm.Byzantium.Vm.Effect.StepResult.error

/-- Fork-indexed `.error` constructor for `StepOf`. -/
def StepOf.error :
    (fork : Evm.Fork) → Evm → Exception → StepOf fork
  | .frontier         => Evm.Frontier.Vm.Effect.Step.error
  | .homestead        => Evm.Homestead.Vm.Effect.Step.error
  | .daoFork          => Evm.Homestead.Vm.Effect.Step.error
  | .tangerineWhistle => Evm.TangerineWhistle.Vm.Effect.Step.error
  | .spuriousDragon   => Evm.SpuriousDragon.Vm.Effect.Step.error
  | .byzantium        => Evm.Byzantium.Vm.Effect.Step.error
  | .constantinople   => Evm.Byzantium.Vm.Effect.Step.error
  | .petersburg       => Evm.Byzantium.Vm.Effect.Step.error
  | .istanbul         => Evm.Byzantium.Vm.Effect.Step.error
  | .muirGlacier      => Evm.Byzantium.Vm.Effect.Step.error
  | .berlin           => Evm.Byzantium.Vm.Effect.Step.error
  | .london           => Evm.Byzantium.Vm.Effect.Step.error
  | .arrowGlacier     => Evm.Byzantium.Vm.Effect.Step.error
  | .grayGlacier      => Evm.Byzantium.Vm.Effect.Step.error
  | .paris            => Evm.Byzantium.Vm.Effect.Step.error
  | .shanghai         => Evm.Byzantium.Vm.Effect.Step.error
  | .cancun           => Evm.Byzantium.Vm.Effect.Step.error
  | .prague           => Evm.Byzantium.Vm.Effect.Step.error
  | .osaka            => Evm.Byzantium.Vm.Effect.Step.error
  | .bpo1             => Evm.Byzantium.Vm.Effect.Step.error
  | .bpo2             => Evm.Byzantium.Vm.Effect.Step.error
  | .amsterdam        => Evm.Byzantium.Vm.Effect.Step.error

/-- Case split for one family: a `StepResult` is either a `.continue`
    (the program runner loops) or one of the three `Step`-shaped
    outcomes, which embed into `Step` unchanged. -/
private def casesFrontier {motive : Type} :
    Evm.Frontier.Vm.Effect.StepResult → (Evm → motive) →
    (Evm.Frontier.Vm.Effect.Step → motive) → motive
  | .continue f,   onCont, _      => onCont f
  | .yield f eff,  _,      onStep => onStep (.yield f eff)
  | .halt f o,     _,      onStep => onStep (.halt f o)
  | .error f e,    _,      onStep => onStep (.error f e)

private def casesHomestead {motive : Type} :
    Evm.Homestead.Vm.Effect.StepResult → (Evm → motive) →
    (Evm.Homestead.Vm.Effect.Step → motive) → motive
  | .continue f,   onCont, _      => onCont f
  | .yield f eff,  _,      onStep => onStep (.yield f eff)
  | .halt f o,     _,      onStep => onStep (.halt f o)
  | .error f e,    _,      onStep => onStep (.error f e)

private def casesTangerine {motive : Type} :
    Evm.TangerineWhistle.Vm.Effect.StepResult → (Evm → motive) →
    (Evm.TangerineWhistle.Vm.Effect.Step → motive) → motive
  | .continue f,   onCont, _      => onCont f
  | .yield f eff,  _,      onStep => onStep (.yield f eff)
  | .halt f o,     _,      onStep => onStep (.halt f o)
  | .error f e,    _,      onStep => onStep (.error f e)

private def casesSpurious {motive : Type} :
    Evm.SpuriousDragon.Vm.Effect.StepResult → (Evm → motive) →
    (Evm.SpuriousDragon.Vm.Effect.Step → motive) → motive
  | .continue f,   onCont, _      => onCont f
  | .yield f eff,  _,      onStep => onStep (.yield f eff)
  | .halt f o,     _,      onStep => onStep (.halt f o)
  | .error f e,    _,      onStep => onStep (.error f e)

private def casesByz {motive : Type} :
    Evm.Byzantium.Vm.Effect.StepResult → (Evm → motive) →
    (Evm.Byzantium.Vm.Effect.Step → motive) → motive
  | .continue f,   onCont, _      => onCont f
  | .yield f eff,  _,      onStep => onStep (.yield f eff)
  | .halt f o,     _,      onStep => onStep (.halt f o)
  | .error f e,    _,      onStep => onStep (.error f e)

/-- Fork-indexed case split over `StepResultOf`: `.continue` goes to
    `onCont` (the program runner loops); `.yield` / `.halt` /
    `.error` embed into the fork's `StepOf` and go to `onStep`. -/
def StepResultOf.cases {motive : Type} :
    (fork : Evm.Fork) → StepResultOf fork →
    (Evm → motive) → (StepOf fork → motive) → motive
  | .frontier         => casesFrontier
  | .homestead        => casesHomestead
  | .daoFork          => casesHomestead
  | .tangerineWhistle => casesTangerine
  | .spuriousDragon   => casesSpurious
  | .byzantium        => casesByz
  | .constantinople   => casesByz
  | .petersburg       => casesByz
  | .istanbul         => casesByz
  | .muirGlacier      => casesByz
  | .berlin           => casesByz
  | .london           => casesByz
  | .arrowGlacier     => casesByz
  | .grayGlacier      => casesByz
  | .paris            => casesByz
  | .shanghai         => casesByz
  | .cancun           => casesByz
  | .prague           => casesByz
  | .osaka            => casesByz
  | .bpo1             => casesByz
  | .bpo2             => casesByz
  | .amsterdam        => casesByz

private def casesStepFrontier {motive : Type} :
    Evm.Frontier.Vm.Effect.Step →
    (Evm → Evm.Frontier.Vm.Effect.YieldEffect → motive) →
    (Evm → Evm.Bytes → motive) → (Evm → Exception → motive) → motive
  | .yield f eff, onYield, _, _ => onYield f eff
  | .halt f o,    _, onHalt, _  => onHalt f o
  | .error f e,   _, _, onError => onError f e

private def casesStepHomestead {motive : Type} :
    Evm.Homestead.Vm.Effect.Step →
    (Evm → Evm.Homestead.Vm.Effect.YieldEffect → motive) →
    (Evm → Evm.Bytes → motive) → (Evm → Exception → motive) → motive
  | .yield f eff, onYield, _, _ => onYield f eff
  | .halt f o,    _, onHalt, _  => onHalt f o
  | .error f e,   _, _, onError => onError f e

private def casesStepTangerine {motive : Type} :
    Evm.TangerineWhistle.Vm.Effect.Step →
    (Evm → Evm.TangerineWhistle.Vm.Effect.YieldEffect → motive) →
    (Evm → Evm.Bytes → motive) → (Evm → Exception → motive) → motive
  | .yield f eff, onYield, _, _ => onYield f eff
  | .halt f o,    _, onHalt, _  => onHalt f o
  | .error f e,   _, _, onError => onError f e

private def casesStepSpurious {motive : Type} :
    Evm.SpuriousDragon.Vm.Effect.Step →
    (Evm → Evm.SpuriousDragon.Vm.Effect.YieldEffect → motive) →
    (Evm → Evm.Bytes → motive) → (Evm → Exception → motive) → motive
  | .yield f eff, onYield, _, _ => onYield f eff
  | .halt f o,    _, onHalt, _  => onHalt f o
  | .error f e,   _, _, onError => onError f e

private def casesStepByz {motive : Type} :
    Evm.Byzantium.Vm.Effect.Step →
    (Evm → Evm.Byzantium.Vm.Effect.YieldEffect → motive) →
    (Evm → Evm.Bytes → motive) → (Evm → Exception → motive) → motive
  | .yield f eff, onYield, _, _ => onYield f eff
  | .halt f o,    _, onHalt, _  => onHalt f o
  | .error f e,   _, _, onError => onError f e

/-- Fork-indexed case split over `StepOf` (constructor order:
    yield / halt / error). The program-level trampoline folds a whole
    run's outcome through this. -/
def StepOf.cases {motive : Type} :
    (fork : Evm.Fork) → StepOf fork →
    (Evm → YieldEffectOf fork → motive) →
    (Evm → Evm.Bytes → motive) → (Evm → Exception → motive) → motive
  | .frontier         => casesStepFrontier
  | .homestead        => casesStepHomestead
  | .daoFork          => casesStepHomestead
  | .tangerineWhistle => casesStepTangerine
  | .spuriousDragon   => casesStepSpurious
  | .byzantium        => casesStepByz
  | .constantinople   => casesStepByz
  | .petersburg       => casesStepByz
  | .istanbul         => casesStepByz
  | .muirGlacier      => casesStepByz
  | .berlin           => casesStepByz
  | .london           => casesStepByz
  | .arrowGlacier     => casesStepByz
  | .grayGlacier      => casesStepByz
  | .paris            => casesStepByz
  | .shanghai         => casesStepByz
  | .cancun           => casesStepByz
  | .prague           => casesStepByz
  | .osaka            => casesStepByz
  | .bpo1             => casesStepByz
  | .bpo2             => casesStepByz
  | .amsterdam        => casesStepByz

/-! ## Terminator dispatch — frame-yielding (trampoline) terminators

    These return a `StepResult` producer: the Effect-layer function
    that pops args, charges gas, and either fail-fasts (`.continue`)
    or yields a sub-frame request (`.yield`). Each family helper
    binds exactly what the corresponding fork's `step1` binds. -/

/-- Frontier family: CALL / CALLCODE / CREATE only. -/
def stepHandlerFrontier :
    Terminator → Option (Evm → Evm.Frontier.Vm.Effect.StepResult)
  | .call .call     => some Evm.Frontier.Vm.Effect.doCall
  | .call .callcode => some Evm.Frontier.Vm.Effect.doCallcode
  | .create .create => some Evm.Frontier.Vm.Effect.doCreate
  | _ => none

/-- Homestead family (EIP-7 adds DELEGATECALL). Also covers daoFork
    (no VM changes). -/
def stepHandlerHomestead :
    Terminator → Option (Evm → Evm.Homestead.Vm.Effect.StepResult)
  | .call .call         => some Evm.Homestead.Vm.Effect.doCall
  | .call .callcode     => some Evm.Homestead.Vm.Effect.doCallcode
  | .call .delegatecall => some Evm.Homestead.Vm.Effect.doDelegatecall
  | .create .create     => some Evm.Homestead.Vm.Effect.doCreate
  | _ => none

/-- TangerineWhistle family (EIP-150 63/64 cap + repricing). -/
def stepHandlerTangerine :
    Terminator → Option (Evm → Evm.TangerineWhistle.Vm.Effect.StepResult)
  | .call .call         => some Evm.TangerineWhistle.Vm.Effect.doCall
  | .call .callcode     => some Evm.TangerineWhistle.Vm.Effect.doCallcode
  | .call .delegatecall => some Evm.TangerineWhistle.Vm.Effect.doDelegatecall
  | .create .create     => some Evm.TangerineWhistle.Vm.Effect.doCreate
  | _ => none

/-- SpuriousDragon family (EIP-161 dead-account rules). -/
def stepHandlerSpurious :
    Terminator → Option (Evm → Evm.SpuriousDragon.Vm.Effect.StepResult)
  | .call .call         => some Evm.SpuriousDragon.Vm.Effect.doCall
  | .call .callcode     => some Evm.SpuriousDragon.Vm.Effect.doCallcode
  | .call .delegatecall => some Evm.SpuriousDragon.Vm.Effect.doDelegatecall
  | .create .create     => some Evm.SpuriousDragon.Vm.Effect.doCreate
  | _ => none

/-- Byzantium family — every fork ≥ byzantium shares Byzantium's
    `StepResult`. Within the family the bound function follows the
    fork's own `step1`: Berlin (EIP-2929) overrides the whole call /
    create set, Shanghai (EIP-3860) overrides the creates, Cancun
    (EIP-6780) turns SELFDESTRUCT into a structural yield. CREATE2 is
    gated on its introducing fork (Constantinople). -/
def stepHandlerByzFamily (fork : Evm.Fork) :
    Terminator → Option (Evm → Evm.Byzantium.Vm.Effect.StepResult)
  | .call .call =>
      some (if fork.atLeast .berlin then Evm.Berlin.Vm.Effect.doCall
            else Evm.Byzantium.Vm.Effect.doCall)
  | .call .callcode =>
      some (if fork.atLeast .berlin then Evm.Berlin.Vm.Effect.doCallcode
            else Evm.Byzantium.Vm.Effect.doCallcode)
  | .call .delegatecall =>
      some (if fork.atLeast .berlin then Evm.Berlin.Vm.Effect.doDelegatecall
            else Evm.Byzantium.Vm.Effect.doDelegatecall)
  | .call .staticcall =>
      some (if fork.atLeast .berlin then Evm.Berlin.Vm.Effect.doStaticcall
            else Evm.Byzantium.Vm.Effect.doStaticcall)
  | .create .create =>
      some (if fork.atLeast .shanghai then Evm.Shanghai.Vm.Effect.doCreate
            else if fork.atLeast .berlin then Evm.Berlin.Vm.Effect.doCreate
            else Evm.Byzantium.Vm.Effect.doCreate)
  | .create .create2 =>
      if fork.atLeast .constantinople then
        some (if fork.atLeast .shanghai then Evm.Shanghai.Vm.Effect.doCreate2
              else if fork.atLeast .berlin then Evm.Berlin.Vm.Effect.doCreate2
              else Evm.Constantinople.Vm.Effect.doCreate2)
      else none
  -- EIP-6780 (Cancun): SELFDESTRUCT becomes a `.selfdestruct` yield
  -- discharged by the fork trampoline's `selfdestructEIP6780` arm;
  -- pre-Cancun it is a plain Handler — see `Terminator.handler`.
  | .selfdestruct =>
      if fork.atLeast .cancun then some Evm.Cancun.Vm.Effect.doSelfdestruct
      else none
  | _ => none

/-- Per-terminator step dispatch for the yielding terminators. The
    return type is the FORK'S OWN `StepResult` (`StepResultOf`), so
    each fork binds its own tested Effect functions. `none` =
    terminator not legal on this fork (the chunk runner treats it as
    invalid) or handled on the plain-`Handler` track. -/
def Terminator.stepHandler :
    (fork : Evm.Fork) → Terminator → Option (Evm → StepResultOf fork)
  | .frontier         => stepHandlerFrontier
  | .homestead        => stepHandlerHomestead
  | .daoFork          => stepHandlerHomestead
  | .tangerineWhistle => stepHandlerTangerine
  | .spuriousDragon   => stepHandlerSpurious
  | .byzantium        => stepHandlerByzFamily .byzantium
  | .constantinople   => stepHandlerByzFamily .constantinople
  | .petersburg       => stepHandlerByzFamily .petersburg
  | .istanbul         => stepHandlerByzFamily .istanbul
  | .muirGlacier      => stepHandlerByzFamily .muirGlacier
  | .berlin           => stepHandlerByzFamily .berlin
  | .london           => stepHandlerByzFamily .london
  | .arrowGlacier     => stepHandlerByzFamily .arrowGlacier
  | .grayGlacier      => stepHandlerByzFamily .grayGlacier
  | .paris            => stepHandlerByzFamily .paris
  | .shanghai         => stepHandlerByzFamily .shanghai
  | .cancun           => stepHandlerByzFamily .cancun
  | .prague           => stepHandlerByzFamily .prague
  | .osaka            => stepHandlerByzFamily .osaka
  | .bpo1             => stepHandlerByzFamily .bpo1
  | .bpo2             => stepHandlerByzFamily .bpo2
  | .amsterdam        => stepHandlerByzFamily .amsterdam

/-! ## Terminator dispatch — frame-ending / control-flow terminators

    These have plain `Handler` semantics (no sub-frame), so they bind
    to the same `Instructions.*` handlers the tested Lean VM runs. -/

/-- Per-terminator handler dispatch for non-yielding terminators. -/
def Terminator.handler (fork : Evm.Fork) : Terminator → Option Handler
  | .stop         => some Instructions.stop
  | .endOfCode    => some Instructions.stop   -- implicit STOP past code end
  | .ret          => some Instructions.return_
  | .revert       =>                          -- Byzantium+ (EIP-140)
      if fork.atLeast .byzantium then some Evm.Byzantium.Vm.Instructions.revert
      else none
  | .jump _       => some Instructions.jump
  | .jumpDynamic  => some Instructions.jump
  | .jumpi _      => some Instructions.jumpi
  | .jumpiDynamic => some Instructions.jumpi
  -- SELFDESTRUCT: each fork's step1 lifts a total Handler pre-Cancun
  -- (NOT the yield-based `doSelfdestruct` Block-STM groundwork):
  -- Frontier's through SpuriousDragon's repriced/EIP-161 variants,
  -- Berlin's EIP-2929 cold-beneficiary one, London's EIP-3529
  -- no-refund one. Cancun+ yields instead — see `stepHandler`.
  | .selfdestruct =>
      if fork.atLeast .cancun then none       -- EIP-6780: yield track
      else if fork.atLeast .london then
        some Evm.London.Vm.Effect.doSelfdestructLondon
      else if fork.atLeast .berlin then
        some Evm.Berlin.Vm.Effect.doSelfdestructPure
      else if fork.atLeast .spuriousDragon then
        some Evm.SpuriousDragon.Vm.selfdestruct
      else if fork.atLeast .tangerineWhistle then
        some Evm.TangerineWhistle.Vm.selfdestruct
      else some Evm.Frontier.Vm.selfdestruct
  | _ => none

/-! ## Yield discharge

    The IR trampoline's yield processing IS the fork's own
    `handleYield` — one definition per fork, shared with that fork's
    `trampoline` knot. `runSub` is the recursion parameter (the
    design doc's `hSub` seam): the IR chunk runner passes its own
    sub-frame executor; each fork's `trampoline` passes itself.
    Forks without their own Effect layer bind their VM predecessor's
    (daoFork → Homestead, muirGlacier → Istanbul, the gas-only
    glaciers → London); Prague routes into Cancun's interpreter with
    EIP-7702 delegation pre-resolved in account code
    (`Prague.applyMessage`), so its per-yield semantics IS Cancun's. -/

abbrev runYield := Effect.handleYield

/-- Fork-indexed yield discharge: each arm IS that fork's
    `handleYield`. Cancun-family arms pin the `precompileLookup`
    parameter to the fork's table (`Call.precompiles`: Prague adds EIP-2537). -/
def runYieldOf :
    (fork : Evm.Fork) → Evm → YieldEffectOf fork →
    (Evm → Except Exception Evm) → Except Exception Evm
  | .frontier         => Evm.Frontier.Vm.Effect.handleYield
  | .homestead        => Evm.Homestead.Vm.Effect.handleYield
  | .daoFork          => Evm.Homestead.Vm.Effect.handleYield
  | .tangerineWhistle => Evm.TangerineWhistle.Vm.Effect.handleYield
  | .spuriousDragon   => Evm.SpuriousDragon.Vm.Effect.handleYield
  | .byzantium        => Evm.Byzantium.Vm.Effect.handleYield
  | .constantinople   => Evm.Constantinople.Vm.Effect.handleYield
  | .petersburg       => Evm.Petersburg.Vm.Effect.handleYield
  | .istanbul         => Evm.Istanbul.Vm.Effect.handleYield
  | .muirGlacier      => Evm.Istanbul.Vm.Effect.handleYield
  | .berlin           => Evm.Berlin.Vm.Effect.handleYield
  | .london           => Evm.London.Vm.Effect.handleYield
  | .arrowGlacier     => Evm.London.Vm.Effect.handleYield
  | .grayGlacier      => Evm.London.Vm.Effect.handleYield
  | .paris            => Evm.Paris.Vm.Effect.handleYield
  | .shanghai         => Evm.Shanghai.Vm.Effect.handleYield
  | .cancun           =>
      Evm.Cancun.Vm.Effect.handleYield Evm.Cancun.Vm.PrecompiledContracts.lookup
  | .prague           =>
      Evm.Cancun.Vm.Effect.handleYield (Evm.Frontier.Vm.Call.precompiles 17)
  | .osaka            => Evm.Osaka.Vm.Effect.handleYield
  | .bpo1             => Evm.Osaka.Vm.Effect.handleYield
  | .bpo2             => Evm.Osaka.Vm.Effect.handleYield
  | .amsterdam        => Evm.Amsterdam.Vm.Effect.handleYield

/-- Fork-indexed sub-frame runner: each arm IS that fork's
    `trampoline` — the tested Effect interpreter the IR program
    runner hands its yielded sub-frames to. -/
def trampolineOf : Evm.Fork → Evm → Except Exception Evm
  | .frontier         => Evm.Frontier.Vm.Effect.trampoline
  | .homestead        => Evm.Homestead.Vm.Effect.trampoline
  | .daoFork          => Evm.Homestead.Vm.Effect.trampoline
  | .tangerineWhistle => Evm.TangerineWhistle.Vm.Effect.trampoline
  | .spuriousDragon   => Evm.SpuriousDragon.Vm.Effect.trampoline
  | .byzantium        => Evm.Byzantium.Vm.Effect.trampoline
  | .constantinople   => Evm.Constantinople.Vm.Effect.trampoline
  | .petersburg       => Evm.Petersburg.Vm.Effect.trampoline
  | .istanbul         => Evm.Istanbul.Vm.Effect.trampoline
  | .muirGlacier      => Evm.Istanbul.Vm.Effect.trampoline
  | .berlin           => Evm.Berlin.Vm.Effect.trampoline
  | .london           => Evm.London.Vm.Effect.trampoline
  | .arrowGlacier     => Evm.London.Vm.Effect.trampoline
  | .grayGlacier      => Evm.London.Vm.Effect.trampoline
  | .paris            => Evm.Paris.Vm.Effect.trampoline
  | .shanghai         => Evm.Shanghai.Vm.Effect.trampoline
  | .cancun           =>
      Evm.Cancun.Vm.Effect.trampoline Evm.Cancun.Vm.PrecompiledContracts.lookup
  | .prague           =>
      Evm.Cancun.Vm.Effect.trampoline (Evm.Frontier.Vm.Call.precompiles 17)
  | .osaka            => Evm.Osaka.Vm.Effect.trampoline
  | .bpo1             => Evm.Osaka.Vm.Effect.trampoline
  | .bpo2             => Evm.Osaka.Vm.Effect.trampoline
  | .amsterdam        => Evm.Amsterdam.Vm.Effect.trampoline

/-! ## Per-terminator soundness theorems

    Definitional, by the binding-not-reencoding principle — same
    shape as the `_dispatch_sound` family in `Evm.IR.Dispatch`.
    Grep-discoverable as `_terminator_sound`. -/

theorem call_terminator_sound :
    Terminator.stepHandler .frontier (.call .call) = some Effect.doCall := rfl

theorem callcode_terminator_sound :
    Terminator.stepHandler .frontier (.call .callcode) = some Effect.doCallcode := rfl

theorem create_terminator_sound :
    Terminator.stepHandler .frontier (.create .create) = some Effect.doCreate := rfl

theorem selfdestruct_terminator_sound :
    Terminator.handler .frontier .selfdestruct = some Evm.Frontier.Vm.selfdestruct := rfl

theorem stop_terminator_sound :
    Terminator.handler .frontier .stop = some Instructions.stop := rfl

theorem endOfCode_terminator_sound :
    Terminator.handler .frontier .endOfCode = some Instructions.stop := rfl

theorem ret_terminator_sound :
    Terminator.handler .frontier .ret = some Instructions.return_ := rfl

theorem jump_terminator_sound (dest : Nat) :
    Terminator.handler .frontier (.jump dest) = some Instructions.jump := rfl

theorem jumpDynamic_terminator_sound :
    Terminator.handler .frontier .jumpDynamic = some Instructions.jump := rfl

theorem jumpi_terminator_sound (dest : Nat) :
    Terminator.handler .frontier (.jumpi dest) = some Instructions.jumpi := rfl

theorem jumpiDynamic_terminator_sound :
    Terminator.handler .frontier .jumpiDynamic = some Instructions.jumpi := rfl

/-- The IR trampoline's yield discharge is the Effect layer's,
    definitionally. Anything proven about `Effect.handleYield`
    (e.g. the `IsCallMerge` refinement in
    `Evm.Frontier.Spec.CallRefinement`) covers the IR trampoline. -/
theorem runYield_is_handleYield :
    runYield = Effect.handleYield := rfl

/-- Per-fork yield discharge is each fork's own `handleYield`,
    definitionally — spot checks across the families. -/
theorem runYieldOf_frontier_is_handleYield :
    runYieldOf .frontier = Effect.handleYield := rfl

theorem runYieldOf_homestead_is_handleYield :
    runYieldOf .homestead = Evm.Homestead.Vm.Effect.handleYield := rfl

theorem runYieldOf_byzantium_is_handleYield :
    runYieldOf .byzantium = Evm.Byzantium.Vm.Effect.handleYield := rfl

theorem runYieldOf_berlin_is_handleYield :
    runYieldOf .berlin = Evm.Berlin.Vm.Effect.handleYield := rfl

theorem runYieldOf_cancun_is_handleYield :
    runYieldOf .cancun
      = Evm.Cancun.Vm.Effect.handleYield
          Evm.Cancun.Vm.PrecompiledContracts.lookup := rfl

theorem runYieldOf_muirGlacier_is_istanbul :
    runYieldOf .muirGlacier = Evm.Istanbul.Vm.Effect.handleYield := rfl

/-! ## Per-fork bindings — introducing forks and overrides

    Each is `rfl` against the fork's own `step1` choice. These flip
    the former `_unwired` theorems: DELEGATECALL / STATICCALL /
    CREATE2 now bind their introducing fork's Effect function. -/

theorem delegatecall_terminator_sound :
    Terminator.stepHandler .homestead (.call .delegatecall)
      = some Evm.Homestead.Vm.Effect.doDelegatecall := rfl

theorem staticcall_terminator_sound :
    Terminator.stepHandler .byzantium (.call .staticcall)
      = some Evm.Byzantium.Vm.Effect.doStaticcall := rfl

theorem create2_terminator_sound :
    Terminator.stepHandler .constantinople (.create .create2)
      = some Evm.Constantinople.Vm.Effect.doCreate2 := rfl

theorem revert_terminator_sound :
    Terminator.handler .byzantium .revert
      = some Evm.Byzantium.Vm.Instructions.revert := rfl

theorem call_tangerine_sound :
    Terminator.stepHandler .tangerineWhistle (.call .call)
      = some Evm.TangerineWhistle.Vm.Effect.doCall := rfl

theorem call_berlin_sound :
    Terminator.stepHandler .berlin (.call .call)
      = some Evm.Berlin.Vm.Effect.doCall := rfl

theorem create_shanghai_sound :
    Terminator.stepHandler .shanghai (.create .create)
      = some Evm.Shanghai.Vm.Effect.doCreate := rfl

theorem create2_cancun_sound :
    Terminator.stepHandler .cancun (.create .create2)
      = some Evm.Shanghai.Vm.Effect.doCreate2 := rfl

theorem selfdestruct_cancun_sound :
    Terminator.stepHandler .cancun .selfdestruct
      = some Evm.Cancun.Vm.Effect.doSelfdestruct := rfl

theorem selfdestruct_london_sound :
    Terminator.handler .london .selfdestruct
      = some Evm.London.Vm.Effect.doSelfdestructLondon := rfl

theorem selfdestruct_cancun_handler_none :
    Terminator.handler .cancun .selfdestruct = none := rfl

/-! ## Invalidity spot-checks — pre-gate terminators are `none` -/

theorem delegatecall_invalid_frontier :
    Terminator.stepHandler .frontier (.call .delegatecall) = none := rfl

theorem staticcall_invalid_frontier :
    Terminator.stepHandler .frontier (.call .staticcall) = none := rfl

theorem create2_invalid_frontier :
    Terminator.stepHandler .frontier (.create .create2) = none := rfl

theorem create2_invalid_byzantium :
    Terminator.stepHandler .byzantium (.create .create2) = none := rfl

theorem staticcall_invalid_homestead :
    Terminator.stepHandler .homestead (.call .staticcall) = none := rfl

theorem revert_invalid_frontier :
    Terminator.handler .frontier .revert = none := rfl

end Evm.IR.Trampoline
