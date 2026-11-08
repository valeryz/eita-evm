import Evm.CL.EffectIR

/-! # CL/EffectSstore — `cb-sstore`, derived (docs/effect-layer-derivation.md §7.3)

The SSTORE host callback as one `EffectIR` term for every fork, proved in
`Evm.CL.EffectSstoreProof` (`sstore_refines`) against the handler the IR binds
(`Evm.IR.Dispatch.Op.handler f .sstore`), and emitted as `spec-sstore-effect`.

**What is the callback's part.** The native SSTORE handler pops the key and the new
value, raises EIP-214's static violation (Byzantium+), applies the EIP-2200/EIP-1706
sentry (Istanbul+: out of gas when gas left ≤ 2300, before anything is read), calls the
callback, charges what it returns. The callback: load the slot, read it, warm it (EIP-2929,
Berlin+), record its original value at first touch, run the fork's schedule
(`sstorePlan`: EIP-1283 at Constantinople, EIP-2200 at Istanbul, EIP-2929 at Berlin,
EIP-3529 from London, the legacy 20000/5000/15000 otherwise) — it sets the refund counter
and the gas — and write the slot when the value changes (journaled). -/

namespace Evm.CL.EffectSstore

open Evm.CL.EffectIR

abbrev self : AExp := .var "self"
abbrev key  : WExp := .var "key"
abbrev new  : WExp := .var "new"
abbrev cur  : WExp := .var "current"
abbrev orig : WExp := .var "original"

/-- The callback. Inputs `self` (the executing account), `key`, `new`; returns the gas. -/
def term : Stmt :=
  .seq (.faultSlot self key) <|
  .letW "current" (.sload self key) <|
  .warmSlot (.forkGe 10) self key "cold" <|                    -- EIP-2929 (Berlin+)
  .seq (.origRecord self key cur) <|                           -- original = first touch
  .letW "original" (.orig self key cur) <|
  .seq (.sstoreGas orig cur new (.var "cold")) <|
  .ite (.not (.weq new cur)) (.setStorage self key new) .skip

end Evm.CL.EffectSstore
