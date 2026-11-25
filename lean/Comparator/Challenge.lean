/-
# The pinned statements (the Lean comparator's challenge)

Reviewer: the owner (Valeriy Zamaraiev). This file is the human-reviewed record of what
Eita's headline theorems say. A change to any statement here, to the theorem list in
`comparator.json` / `comparator-native.json`, or to either file's `permitted_axioms`, needs
the owner's review: `scripts/verify-comparator.sh` fails when this file's hash differs from
`scripts/generated/comparator-challenge.sha256`, and CODEOWNERS routes the file to the owner.

Each `Pinned.<name>` below restates, word for word, the theorem `<name>` of the same
namespace, with `sorry` as its proof. `Comparator/Solution.lean` proves each `Pinned.<name>`
by the real theorem, with the real theorem's own type. `lake comparator` (Lean's built-in
judge, `scripts/verify-comparator.sh`) then establishes, in a sandbox, that

* every real theorem still proves exactly the statement written here (kernel terms equal,
  every constant the statement mentions identical in both environments),
* no proof uses `sorry` or an axiom outside the config's `permitted_axioms`,
* the kernel accepts the whole proof closure.

What it does not establish: that the definitions these statements mention mean what their
names say. They are imported from `Evm.*` and judged by reading them (the statement is only
as strong as `Refines`, `IsFrameRun`, `IsClzStep`, ...).

Two sets, two configs:
* `comparator.json` — the standard axioms only (propext, Quot.sound, Classical.choice).
* `comparator-native.json` — the theorems whose proofs use `native_decide` / `bv_decide`
  (the compiled evaluator is trusted): the standard axioms plus each auxiliary axiom by name.
-/
import Evm.Parallel.BlockSTM
import Evm.IR.Soundness
import Evm.CL.EffectBlockProof
import Evm.CL.EffectCallProof
import Evm.CL.EffectCreateProof
import Evm.CL.EffectSloadProof
import Evm.CL.EffectSstoreProof
import Evm.CL.EffectSelfdestructProof
import Evm.CL.EffectSettleProof
import Evm.CL.EffectSystemProof
import Evm.CL.EffectEndTxProof
import Evm.CL.EffectTxProof
import Evm.CL.CacheSound
import Evm.CL.X86CacheSound
import Evm.CL.ARM64.Interp
import Evm.CL.ARM64.CallGasSem
import Evm.CL.ARM64.SstoreGasSem
import Evm.CL.MemExpandSpec
import Evm.CL.OpSem
import Evm.Istanbul.Spec.Refinement
import Evm.Prague.Spec.Refinement
import Evm.Osaka.Spec.Refinement
import Evm.Cancun.Spec.Refinement
import Evm.Amsterdam.Spec.Refinement

/-! ## Block-STM: a validated schedule commits the sequential result; an unvalidated one need not -/
namespace Evm.Parallel.BlockSTM

theorem Pinned.blockSTM_refines_seq
    (txs : List Tx) (σ : Storage) (view : Nat → Storage)
    (wf : ∀ t ∈ txs, t.WellFormed)
    (valid : ScheduleValidFrom view σ 0 txs) :
    commitFold txs σ view = seqExec txs σ := sorry

theorem Pinned.unvalidated_schedule_diverges :
    ∃ (txs : List Tx) (σ : Storage) (badview : Nat → Storage),
      commitFold txs σ badview ≠ seqExec txs σ := sorry

end Evm.Parallel.BlockSTM

/-! ## The IR compiler: a compiled chunk's run is a frame run of the spec -/
namespace Evm.IR.Soundness
open Evm.Frontier.Vm

theorem Pinned.compile_sound_vs_effect
    (code : Evm.Bytes) (chunk : Chunk) (evm evm' : Evm)
    (hcc : evm.message.code = code)
    (hpc : evm.pc = 0)
    (hHalt : evm.halted = false)
    (hcompile : IR.compile .frontier code = .ok chunk)
    (hexec : IR.execute chunk evm = .ok evm')
    (hHalted : evm'.halted = true) :
    ∃ fuel, Effect.runFrameR fuel evm = .halt evm' evm'.output := sorry

theorem Pinned.compile_sound_vs_spec
    (code : Evm.Bytes) (chunk : Chunk) (evm evm' : Evm)
    (hcc : evm.message.code = code)
    (hpc : evm.pc = 0)
    (hHalt : evm.halted = false)
    (hcompile : IR.compile .frontier code = .ok chunk)
    (hexec : IR.execute chunk evm = .ok evm')
    (hHalted : evm'.halted = true) :
    ∃ cause, Evm.Frontier.Spec.IsFrameRun evm cause evm' := sorry

theorem Pinned.compileProgram_sound_vs_spec (fuel : Nat) (code : Evm.Bytes)
    (prog : Program) (evm evm' : Evm)
    (hcompile : IR.compileProgram .frontier code = .ok prog)
    (hcc : evm.message.code = code) (hHalt : evm.halted = false)
    (hrun : IR.executeProgram fuel prog evm = .ok evm') :
    ∃ cause, Evm.Frontier.Spec.IsFrameRun evm cause evm' := sorry

end Evm.IR.Soundness

/-! ## The effect layer: each host effect program refines its EELS-shaped spec, every fork -/
namespace Evm.CL.EffectBlockProof
open Evm.CL.EffectIR Evm.CL.EffectBlock
open Evm.Frontier (State)

theorem Pinned.credits_refines (k : Nat) (cb : Evm.Address) (number : Nat)
    (ommers ws : List (Evm.Address × Nat)) (h : HState) :
    credits.run (ctxB k cb number ommers ws) h
      = { h with state := Evm.Frontier.Vm.Block.postBlock k h.state cb number ommers ws } := sorry

end Evm.CL.EffectBlockProof

namespace Evm.CL.EffectCall
open Evm.CL.EffectIR
open Evm.CL.EffectCreate (envOf Agree toRes agree_ofEnv warm_eq ofEnv_gas ofEnv_out ofEnv_rdata)
open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Environment Evm Stack Exception Message Memory)
open Evm.Frontier.Vm.Call

theorem Pinned.call_refines (k : Nat) (n : Native)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hpmono : ∀ a p i g o g', pre (env2S k n) a = some p → p i g = .ok (o, g') → g' ≤ g)
    (hlen : n.frame.stack.length < Evm.Frontier.Vm.stackLimit) :
    Refines n.frame n.retOff n.retLen (Evm.Frontier.Vm.Call.run (Rules.ofOrd k) pre n runSub)
      (term.run (ctxOf k n pre runSub) (HState.ofEnv n.frame.env)) := sorry

end Evm.CL.EffectCall

namespace Evm.CL.EffectCreate
open Evm.CL.EffectIR
open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Environment Evm Stack Exception Message)
open Evm.Frontier.Vm.Create

theorem Pinned.create_refines (k : Nat) (evm : Evm) (value : Evm.U256) (initCode : Evm.Bytes)
    (newAddr : Evm.Address) (base : Nat) (runSub : Evm → Except Exception Evm)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hlen : evm.stack.length < Evm.Frontier.Vm.stackLimit) :
    Refines evm (Evm.Frontier.Vm.Create.run (Rules.ofOrd k) evm value initCode newAddr base runSub)
      (term.run (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env)) := sorry

end Evm.CL.EffectCreate

namespace Evm.CL.EffectSload
open Evm.CL.EffectIR
open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Environment Evm Stack Exception)
open Evm.CL.EffectSettle (SAgree)
open Evm.CL.EffectSstore (Agree charge_cases)

theorem Pinned.sload_refines (f : Evm.Fork) (evm : Evm) (key : Evm.U256) (rest : List Evm.U256)
    (hstack : evm.stack = key :: rest) (hlen : rest.length < Evm.Frontier.Vm.stackLimit) :
    Refines f.ord (specSload f evm) evm.gasLeft rest
      (term.run (ctxOf f.ord evm.message.currentTarget key) (HState.ofEnv evm.env)) := sorry

end Evm.CL.EffectSload

namespace Evm.CL.EffectSstore
open Evm.CL.EffectIR
open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Environment Evm Stack Exception)
open Evm.CL.EffectSettle (SAgree)

theorem Pinned.sstore_refines (f : Evm.Fork) (evm : Evm) (key new : Evm.U256) (rest : List Evm.U256)
    (hstack : evm.stack = key :: new :: rest) (hstatic : evm.message.isStatic = false)
    (hsentry : f.ord ≥ 8 → 2300 < evm.gasLeft)
    (horig : (f.ord = 6 ∨ f.ord = 8 ∨ f.ord = 9) →
      getOrig (putOrig evm.env.storageOriginals evm.message.currentTarget key
                (evm.env.state.getStorage evm.message.currentTarget key))
              evm.message.currentTarget key (evm.env.state.getStorage evm.message.currentTarget key)
        = evm.env.originalState.getStorage evm.message.currentTarget key) :
    Refines f.ord (specSstore f evm) evm.gasLeft
      (term.run (ctxOf f.ord evm.message.currentTarget key new) (HState.ofEnv evm.env)) := sorry

end Evm.CL.EffectSstore

namespace Evm.CL.EffectSelfdestruct
open Evm.CL.EffectIR
open Evm.Frontier.Vm (Environment Evm)
open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Stack Exception)

theorem Pinned.selfdestruct_refines (f : Evm.Fork) (evm : Evm) (bW : Evm.U256) (rest : List Evm.U256)
    (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (hself : evm.env.state.accountExists evm.message.currentTarget = true) :
    Refines (specSelfdestruct f evm) evm.gasLeft f.ord (runOn f.ord evm (Evm.Address.ofNat bW.toNat)) := sorry

end Evm.CL.EffectSelfdestruct

namespace Evm.CL.EffectSettle
open Evm.CL.EffectIR
open Evm.Frontier (State Account)

theorem Pinned.settle_refines (k : Nat) (h : HState) (sender coinbase : Evm.Address) (gl gu egp bf : Nat)
    (hgu : gu ≤ gl) (hbf : bf ≤ egp)
    (hsender : h.state.accountExists sender = true) (hwf : WF h.state)
    (hnowrap : ((h.state.addBalance sender (BitVec.ofNat 256 ((gl - gu) * egp))).getAccount coinbase).balance
                 + BitVec.ofNat 256 (gu * (egp - bf)) = 0 → BitVec.ofNat 256 (gu * (egp - bf)) = 0) :
    let R := settle.run (ctxOf k sender coinbase gl gu egp bf) h
    SAgree (specSettle k h.state sender coinbase ((gl - gu) * egp) (gu * (egp - bf))) R.state ∧
      R.destroyed = h.destroyed ∧ R.touched = h.touched ∧ R.accessed = h.accessed ∧
      R.created = h.created ∧ R.refund = h.refund ∧ R.gas = h.gas ∧ R.facts = h.facts := sorry

end Evm.CL.EffectSettle

namespace Evm.CL.EffectSystem
open Evm.CL.EffectIR
open Evm.Frontier (State)
open Evm.Frontier.Vm (Environment Evm Exception)
open Evm.Frontier.Vm.Tx (Tx Out callTail)
open Evm.Frontier.Vm.System
open Evm.CL.EffectTx (h0 MBound callPath_run callOracle delegS_run cDel cDel_bool ins_eq)

theorem Pinned.system_refines (k : Nat) (benv : Environment) (st : State) (r : Rule) (tgt : Evm.Address)
    (data : Evm.Bytes)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm) (checked : Bool)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hpmono : ∀ a p i g o g', pre (e2S k benv st r tgt) a = some p → p i g = .ok (o, g') → g' ≤ g)
    (hcode : checked = true → (st.getAccount tgt).code.size ≠ 0) :
    let R := term.run (ctxSys k benv st r tgt data pre runSub checked) (h0 st)
    let o := message k benv st r tgt data pre runSub
    R.rej = 0 ∧ R.state = o.env.state ∧ R.destroyed = o.env.selfDestructSet ∧ R.touched = o.env.touched ∧
      R.refund = o.env.refundCounter ∧ R.gas + o.gasLeft = systemGas ∧
      R.out = (if o.success then Evm.U256.ofNat 1 else 0) := sorry

end Evm.CL.EffectSystem

namespace Evm.CL.EffectEndTx
open Evm.CL.EffectIR
open Evm.Frontier (State Account)
open Evm.CL.EffectSettle (SAgree WF)

theorem Pinned.endTx_refines (k : Nat) (h : HState) (hwf : WF h.state) :
    let R := endTx.run (ctxOf k) h
    SAgree (specEndTx k h.state h.destroyed h.touched) R.state ∧
      R.destroyed = h.destroyed ∧ R.touched = h.touched ∧ R.accessed = h.accessed ∧
      R.created = h.created ∧ R.refund = h.refund ∧ R.gas = h.gas ∧ R.facts = h.facts := sorry

end Evm.CL.EffectEndTx

namespace Evm.CL.EffectTx
open Evm.CL.EffectIR
open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Environment Evm Exception Message)
open Evm.Frontier.Vm.Tx
open Evm.CL.EffectSettle (SAgree WF)

theorem Pinned.tx_refines (k : Nat) (benv : Environment) (st : State) (sdr : Evm.Address) (tx : Tx)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm) (recover : Evm.Prague.Authorization → Option Evm.Address)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hpmono : ∀ a p i g o g', pre (e2S k benv st sdr tx recover) a = some p → p i g = .ok (o, g') → g' ≤ g)
    (hv : invalid k benv st sdr tx = none) :
    let R := term.run (ctxTx k benv st sdr tx pre runSub recover) (h0 st)
    let o := message k benv st sdr tx pre runSub recover
    R.rej = 0 ∧ R.state = o.env.state ∧ R.destroyed = o.env.selfDestructSet ∧ R.touched = o.env.touched ∧
      R.refund = o.env.refundCounter ∧ R.gas + o.gasLeft = tx.gas - intrinsic k tx ∧
      R.out = (if o.success then Evm.U256.ofNat 1 else 0) := sorry

theorem Pinned.apply_tx_refines (k : Nat) (benv : Environment) (st : State) (sdr : Evm.Address) (tx : Tx)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm) (recover : Evm.Prague.Authorization → Option Evm.Address)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hpmono : ∀ a p i g o g', pre (e2S k benv st sdr tx recover) a = some p → p i g = .ok (o, g') → g' ≤ g)
    (hv : invalid k benv st sdr tx = none)
    (hsender : (message k benv st sdr tx pre runSub recover).env.state.accountExists sdr = true)
    (hwf : WF (message k benv st sdr tx pre runSub recover).env.state)
    (hnowrap : let o := message k benv st sdr tx pre runSub recover
               let gu := gasUsed k tx o
               let p := egp benv.baseFeePerGas tx
               ((o.env.state.addBalance sdr (BitVec.ofNat 256 ((tx.gas - gu) * p))).getAccount benv.coinbase).balance
                 + BitVec.ofNat 256 (gu * (p - benv.baseFeePerGas)) = 0 →
               BitVec.ofNat 256 (gu * (p - benv.baseFeePerGas)) = 0) :
    let R := term.run (ctxTx k benv st sdr tx pre runSub recover) (h0 st)
    let gu := Evm.CL.GasEmit.txGasUsed.eval (fun y =>
      if y = "gas-used" then intrinsic k tx + R.gas else if y = "refund-counter" then R.refund else gasEnv k tx y)
    let p := egp benv.baseFeePerGas tx
    let S := EffectSettle.settle.run (EffectSettle.ctxOf k sdr benv.coinbase tx.gas gu p benv.baseFeePerGas) R
    let E := EffectEndTx.endTx.run (EffectEndTx.ctxOf k) S
    R.rej = 0 ∧ ∃ r, run k benv st sdr tx pre runSub recover = .ok r ∧
      SAgree r.state E.state ∧ r.gasUsed = gu ∧ (r.success = true ↔ R.out = Evm.U256.ofNat 1) := sorry

end Evm.CL.EffectTx

/-! ## The stack-top register cache: the static check's verdict is sound (ARM64, x86-64) -/
namespace Evm.CL.CacheSound
open Evm.CL.AsmCore Evm.CL.OpInstrs Evm.CL.AsmRun
open Evm.CL.AsmSem (subFlags bcHolds)

theorem Pinned.cacheIncoherent_sound (is : List AInstr) (h : cacheIncoherent is = []) (m₀ : RS)
    (hsp : 0 ≤ sp₀ m₀ ∧ sp₀ m₀ ≤ 1024) (hc : Coherent m₀) (hsep : Sep is m₀) :
    ∀ j m, Reach is m₀ j m → is[j]? = some .brCont → Coherent m := sorry

end Evm.CL.CacheSound

namespace Evm.CL.X86CacheSound
open Evm.CL.AsmRun Evm.CL.X86Encode Evm.CL.X86Items Evm.CL.X86Cache
open Evm.CL.X86Sem (XS XFlags xstep xcHolds subXF aluR xskipTo xCallerSaved ea)

theorem Pinned.xcacheIncoherent_sound (its : List XItem) (h : xcacheIncoherent its = []) (x₀ : XS)
    (hsp : SpOk x₀) (hc : XCoherent x₀) (hsep : Sep its x₀) :
    ∀ i rest x, XReach its x₀ (.I i :: rest) x → isExit i = true → XCoherent x := sorry

/-! native set: the verdict over the shipped handlers is computed by `native_decide` -/
section Handlers
open Evm.CL.AsmCore Evm.CL.X86Interp Evm.CL.ARM64.Interp

theorem Pinned.x86_handler_runs_cache_coherent :
    ∀ h ∈ handlerList, ∀ its ∈ [progItems (handlerInstrs h.2.1 h.2.2), threadedItems (handlerInstrs h.2.1 h.2.2)],
    ∀ x₀ : Evm.CL.X86Sem.XS, SpOk x₀ → XCoherent x₀ → Sep its x₀ →
    ∀ i rest x, XReach its x₀ (.I i :: rest) x → isExit i = true → XCoherent x := sorry

end Handlers
end Evm.CL.X86CacheSound

namespace Evm.CL.ARM64.Interp
open Evm.IR
open Evm.CL.AsmCore Evm.CL.OpInstrs Evm.CL.CacheSound in
/-- native set (`native_decide` over the shipped handler bodies). -/
theorem Pinned.handler_runs_cache_coherent :
    ∀ p ∈ (handlerProgs (fun _ => 0)).map (·.2) ++ variantProgs.map (·.2.2),
    ∀ m₀ : Evm.CL.AsmRun.RS, 0 ≤ sp₀ m₀ ∧ sp₀ m₀ ≤ 1024 → Coherent m₀ → Sep (bodyInstrs p) m₀ →
    ∀ j m, Reach (bodyInstrs p) m₀ j m → (bodyInstrs p)[j]? = some .brCont → Coherent m := sorry

end Evm.CL.ARM64.Interp

/-! ## Gas routines run as ARM64 machine code compute the spec's plan (native set) -/
/- The two modules below do not import Mathlib, so their `2^64` elaborates with core's
   `instPowNat`; here Mathlib's `Monoid.Pow` would be found instead and the kernel terms would
   differ. `a ^ᴺ b` spells core's instance (a macro: it adds no constant to the statement). -/
local macro:75 a:term:76 " ^ᴺ " b:term:75 : term =>
  `(@HPow.hPow Nat Nat Nat (@instHPow Nat Nat instPowNat) $a $b)

namespace Evm.CL.ARM64.CallGasSem
open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.ARM64

theorem Pinned.frontier_sem (m : RM) (isCold cv cn : Bool) (gasArg : Nat)
    (h1 : m.regs .x1 = flagsWord isCold cv cn) (h3 : m.regs .x3 = BitVec.ofNat 64 gasArg) :
    (exec (entry "_eita_call_gas_frontier" CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (CallGasDenote.planFrontier cv cn gasArg).charge,
              BitVec.ofNat 64 (CallGasDenote.planFrontier cv cn gasArg).forward,
              BitVec.ofNat 64 (CallGasDenote.planFrontier cv cn gasArg).stipend) := sorry

theorem Pinned.tangerine_sem (m : RM) (isCold cv cn : Bool) (gasArg avail : Nat)
    (h1 : m.regs .x1 = flagsWord isCold cv cn) (h3 : m.regs .x3 = BitVec.ofNat 64 gasArg)
    (h4 : m.regs .x4 = BitVec.ofNat 64 avail) (hg : gasArg < 2 ^ᴺ 64) (ha : avail < 2 ^ᴺ 64) :
    (exec (entry "_eita_call_gas_tangerine" CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (CallGasDenote.planTangerine cv cn gasArg avail).charge,
              BitVec.ofNat 64 (CallGasDenote.planTangerine cv cn gasArg avail).forward,
              BitVec.ofNat 64 (CallGasDenote.planTangerine cv cn gasArg avail).stipend) := sorry

theorem Pinned.berlin_sem (m : RM) (isCold cv cn : Bool) (delegated gasArg avail : Nat)
    (h1 : m.regs .x1 = flagsWord isCold cv cn) (h2 : m.regs .x2 = BitVec.ofNat 64 delegated)
    (h3 : m.regs .x3 = BitVec.ofNat 64 gasArg) (h4 : m.regs .x4 = BitVec.ofNat 64 avail)
    (hd : delegated + 2600 + 9000 + 25000 < 2 ^ᴺ 64) (hg : gasArg < 2 ^ᴺ 64) (ha : avail < 2 ^ᴺ 64) :
    (exec (entry "_eita_call_gas" CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (CallGasDenote.plan isCold cv cn delegated gasArg avail).charge,
              BitVec.ofNat 64 (CallGasDenote.plan isCold cv cn delegated gasArg avail).forward,
              BitVec.ofNat 64 (CallGasDenote.plan isCold cv cn delegated gasArg avail).stipend) := sorry

end Evm.CL.ARM64.CallGasSem

namespace Evm.CL.ARM64.SstoreGasSem
open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.ARM64 Evm.CL.ARM64.PredFold

theorem Pinned.legacy_sem (m : RM) (rest : List AInstr) (r : BitVec 64) (c n : Evm.U256)
    (h1 : m.regs .x1 = r) (_hr : r.toNat + 65536 < 2 ^ᴺ 63)
    (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (exec (entry "_eita_sstore_gas_legacy" (SstoreGas.legacyA ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (SstoreGasDenote.planLegacy r.toNat (pz c) (pz n)).1,
              BitVec.ofNat 64 (SstoreGasDenote.planLegacy r.toNat (pz c) (pz n)).2) := sorry

theorem Pinned.berlin_sem (m : RM) (rest : List AInstr) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h1 : m.regs .x1 = r) (hr : r.toNat + 65536 < 2 ^ᴺ 63) (h5 : m.regs .x5 = b2v cold)
    (ho : loads m .x2 o) (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (exec (entry "_eita_sstore_gas_berlin" (SstoreGas.eip2929A "berlin" SstoreGasDenote.berlinConsts ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (SstoreGasDenote.plan2929 SstoreGasDenote.berlinConsts r.toNat cold (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).1,
              BitVec.ofNat 64 (SstoreGasDenote.plan2929 SstoreGasDenote.berlinConsts r.toNat cold (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).2) := sorry

theorem Pinned.london_sem (m : RM) (rest : List AInstr) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h1 : m.regs .x1 = r) (hr : r.toNat + 65536 < 2 ^ᴺ 63) (h5 : m.regs .x5 = b2v cold)
    (ho : loads m .x2 o) (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (exec (entry "_eita_sstore_gas_london" (SstoreGas.eip2929A "london" SstoreGasDenote.londonConsts ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (SstoreGasDenote.plan2929 SstoreGasDenote.londonConsts r.toNat cold (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).1,
              BitVec.ofNat 64 (SstoreGasDenote.plan2929 SstoreGasDenote.londonConsts r.toNat cold (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).2) := sorry

end Evm.CL.ARM64.SstoreGasSem

/-! ## Op semantics: the shipped instruction sequences against `Op.denote` -/
namespace Evm.CL.AsmCore
open Evm.Frontier.Vm

theorem Pinned.memExpand_acc_refines (m : Mach) (hcap : ¬ m.memCap < m.scratch) :
    (Op.denote .memExpand m).acc =
      m.acc + Gas.memoryExpansionCost (m.memSize / 32) ((m.scratch + 31) / 32) := sorry

end Evm.CL.AsmCore

namespace Evm.CL.OpSem
open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun
open Evm.CL.ARM64.MemCommitSem (toNat_ofNat64 words_bv oldWords_bv
  aligned_bv mcost_bv mcost_mono wordsOf wordsOf_le mcost ecost msAt capAt run_cons_blsLbl)

theorem Pinned.jumpValidate_sem (H : Helpers) (m : Mach) (s : RS) (v : JumpView m s) (ht : m.trap = false) :
    (∃ s', run H (Op.toAInstrs .jumpValidate) s = .done s' ∧
       (Op.denote .jumpValidate m).trap = false ∧
       s'.regs .x21 = BitVec.ofNat 64 (Op.denote .jumpValidate m).pcReg) ∨
    (∃ s', run H (Op.toAInstrs .jumpValidate) s = .fault "_eita_invalid_jump" s' ∧
       (Op.denote .jumpValidate m).trap = true) := sorry

theorem Pinned.jumpiCheck_sem (H : Helpers) (m : Mach) (s : RS) (v : JumpiView m s) (ht : m.trap = false) :
    (nosZero m → ∃ s', run H (Op.toAInstrs .jumpiCheck) s = .done s' ∧
       Op.denote .jumpiCheck m = m ∧ s'.regs .x21 = s.regs .x21) ∧
    (¬ nosZero m →
      (∃ s', run H (Op.toAInstrs .jumpiCheck) s = .done s' ∧
         (Op.denote .jumpiCheck m).trap = false ∧
         s'.regs .x21 = BitVec.ofNat 64 (Op.denote .jumpiCheck m).pcReg) ∨
      (∃ s', run H (Op.toAInstrs .jumpiCheck) s = .fault "_eita_invalid_jump" s' ∧
         (Op.denote .jumpiCheck m).trap = true)) := sorry

theorem Pinned.memExpandIfLen_sem (H : Helpers) (tag : String) (m : Mach) (s : RS) (v : MemView m s)
    (hoog : m.oog = false)
    (hL : (s!".Lro{tag}1" == s!".Lro{tag}0" || s!".Lro{tag}1" == s!".Lro{tag}0" ++ "f") = false) :
    (∃ s', run H (Op.toAInstrs (.memExpandIfLen tag)) s = .done s' ∧
       (Op.denote (.memExpandIfLen tag) m).oog = false ∧
       s'.regs .x22 = BitVec.ofNat 64 (Op.denote (.memExpandIfLen tag) m).gas ∧
       msAt s'.mem (s.regs .x20) = BitVec.ofNat 64 (Op.denote (.memExpandIfLen tag) m).memSize) ∨
    (∃ s', run H (Op.toAInstrs (.memExpandIfLen tag)) s = .fault "_eita_oog" s' ∧
       (Op.denote (.memExpandIfLen tag) m).oog = true) := sorry

end Evm.CL.OpSem

/-! ## Precompile wrappers: sound for any crypto oracle -/
namespace Evm.Istanbul.Spec.Refinement
open Evm.Frontier.Vm
open Evm.Istanbul.Spec

theorem Pinned.blake2f_sound
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gasLeft : Nat) :
    Evm.Istanbul.Vm.PrecompiledContracts.blake2f input gas = .ok (output, gasLeft) →
    IsBlake2fStep input gas output gasLeft := sorry

end Evm.Istanbul.Spec.Refinement

namespace Evm.Prague.Spec.Refinement
open Evm.Frontier (State Transaction)
open Evm.Frontier.Vm
open Evm.Prague.Spec

theorem Pinned.g1Add_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    Evm.Prague.Vm.PrecompiledContracts.blsG1AddWith o input gas = .ok (output, gas') →
    IsG1AddSuccess o input gas output gas' := sorry

theorem Pinned.g1Msm_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    Evm.Prague.Vm.PrecompiledContracts.blsG1MsmWith o input gas = .ok (output, gas') →
    IsG1MsmSuccess o input gas output gas' := sorry

theorem Pinned.pairingCheck_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    Evm.Prague.Vm.PrecompiledContracts.blsPairingWith o input gas = .ok (output, gas') →
    IsPairingCheckSuccess o input gas output gas' := sorry

theorem Pinned.mapFp2ToG2_sound (o : Evm.Crypto.Bls12381.Oracle)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    Evm.Prague.Vm.PrecompiledContracts.blsMapFp2ToG2With o input gas = .ok (output, gas') →
    IsMapFp2ToG2Success o input gas output gas' := sorry

end Evm.Prague.Spec.Refinement

namespace Evm.Osaka.Spec.Refinement
open Evm.Frontier.Vm
open Evm.Osaka.Spec

theorem Pinned.p256Verify_sound
    (verify : Nat → Nat → Nat → Nat → Nat → Bool)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gasOut : Nat) :
    Evm.Crypto.p256VerifyWithOracle verify Evm.Osaka.Vm.PrecompiledContracts.gasP256Verify
      input gas = .ok (output, gasOut) →
    IsP256VerifyStep verify input gas output gasOut := sorry

/-! ## Opcodes of the recent forks: the implementation step is the spec relation -/
theorem Pinned.clz_sound (evm evm' : Evm) :
    Evm.Osaka.Vm.Effect.doClz evm = .continue evm' →
    IsClzStep evm evm' := sorry

end Evm.Osaka.Spec.Refinement

namespace Evm.Cancun.Spec.Refinement
open Evm.Frontier (State)
open Evm.Frontier.Vm
open Evm.Cancun.Spec

theorem Pinned.tstore_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.tstore evm = .ok evm' → IsTstoreStep evm evm' := sorry

theorem Pinned.mcopy_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.mcopy evm = .ok evm' →
    IsMcopyStep evm evm' := sorry

theorem Pinned.blobhash_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.blobhash evm = .ok evm' → IsBlobhashStep evm evm' := sorry

end Evm.Cancun.Spec.Refinement

namespace Evm.Amsterdam.Spec.Refinement
open Evm.Frontier.Vm
open Evm.Amsterdam.Spec

theorem Pinned.exchange_sound (evm evm' : Evm) :
    Evm.Amsterdam.Vm.Effect.doExchange evm = .continue evm' →
    IsExchangeStep evm evm' := sorry

end Evm.Amsterdam.Spec.Refinement
