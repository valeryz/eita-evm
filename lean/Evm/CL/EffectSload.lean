import Evm.CL.EffectIR
import Evm.TangerineWhistle.Vm.Instructions
import Evm.Berlin.Vm.Effect

/-! # CL/EffectSload — `cb-sload`, derived (docs/effect-layer-derivation.md §4.5)

The SLOAD host callback as one `EffectIR` term for every fork, proved in
`Evm.CL.EffectSloadProof` (`sload_refines`) against the handler the IR binds
(`Evm.IR.Dispatch.Op.handler f .sload`), and emitted as `spec-sload-effect`.

**What is the callback's part.** The native SLOAD handler pops the key, calls the callback,
charges the gas it returns and pushes the word it returns. The callback: load the slot, read
it, warm it (EIP-2929, Berlin+), record its original value at first touch (the cache the
SSTORE schedules read — `EffectSstore`; the spec keeps one from Berlin), return the value,
and charge the fork's price: 50 (Frontier), 200 (EIP-150), 800 (EIP-1884), 2100 cold / 100
warm (EIP-2929) — the spec's own constants. -/

namespace Evm.CL.EffectSload

open Evm.CL.EffectIR

abbrev self : AExp := .var "self"
abbrev key  : WExp := .var "key"

/-- The fork's SLOAD price; `cold` is the warm-up's answer (false before Berlin). -/
def gas : GExp :=
  .ite (.forkGe 10)
    (.ite (.var "cold") (.lit Evm.Berlin.Vm.Gas.coldSload) (.lit Evm.Berlin.Vm.Gas.warmAccess))
    (.ite (.forkGe 8) (.lit Evm.Istanbul.Vm.Gas.sLoad)
      (.ite (.forkGe 3) (.lit Evm.TangerineWhistle.Vm.Gas.sLoad) (.lit Evm.Frontier.Vm.Gas.sLoad)))

/-- The callback. Inputs `self` (the executing account), `key`; returns the gas and the
    slot's value. -/
def term : Stmt :=
  .seq (.faultSlot self key) <|
  .letW "value" (.sload self key) <|
  .warmSlot (.forkGe 10) self key "cold" <|                    -- EIP-2929 (Berlin+)
  .seq (.origRecord self key (.var "value")) <|               -- original = first touch
  .seq (.ret (.var "value")) <|
  .charge gas

end Evm.CL.EffectSload
