/-
  AxiomAudit — print the axiom closure of the headline theorems.

  scripts/verify-axioms.sh runs this file, diffs the output against the
  committed scripts/generated/axiom-audit.txt, and hard-fails on any
  drift or on a trust_smt reappearance (SMT-solver discharge via the
  since-removed loom dependency). Regenerate after an intended change:

    (cd lean && lake env lean AxiomAudit.lean | sed 's/^info: //' \
      | grep -v '^extern rule OK' | grep -v '^extern inventory OK' \
      > ../scripts/generated/axiom-audit.txt)

  Coverage (per review on PR #44): every effect-layer `*_refines`
  entry point, every emitted `*_eq_spec` / `*_is_spec` theorem, plus
  the IR-pipeline and BlockSTM headlines. A new axiom (or a
  native_decide, whose `._native.native_decide.ax_…` shows up here) must land in the
  committed baseline deliberately, with eyes on it. -/

import Evm.IR.Soundness
import Evm.IR.SymExpr
import Evm.CL.EffectBlockProof
import Evm.CL.EffectCallProof
import Evm.CL.EffectCreateProof
import Evm.CL.EffectEndTxProof
import Evm.CL.EffectSelfdestructProof
import Evm.CL.EffectSettleProof
import Evm.CL.EffectSloadProof
import Evm.CL.EffectSstoreProof
import Evm.CL.EffectSystemProof
import Evm.CL.EffectTxProof
import Evm.CL.MemExpandSpec
import Evm.CL.GasEmitLondon
import Evm.CL.GasEmitCancun
import Evm.CL.GasEmitPrague
import Evm.CL.RepriceEmit
import Evm.CL.Flags
import Evm.CL.ForkEmit
import Evm.CL.HeaderEmit
import Evm.CL.BlobEnv
import Evm.CL.HostEmit
import Evm.Arc.Spec.BlockSystem
import Evm.CL.ARM64.SstoreGasDenote
import Evm.CL.ARM64.MemCommitSem
import Evm.CL.ARM64.CallGasDenote
import Evm.Parallel.BlockSTM
import Evm.CL.CacheSound
import Evm.CL.ARM64.Interp
import Evm.CL.X86CacheSound
-- the rest of the modules that use native_decide (the extern rule, at the end)
import Evm.CL.Boundary
import Evm.CL.DispatchTable
import Evm.CL.Fetch
import Evm.CL.JumpDest
import Evm.CL.Relax
import Evm.CL.StackOps
import Evm.CL.StaticGuard
import Evm.CL.X86Alias
import Evm.CL.X86Asm
import Evm.CL.X86Dispatch
import Evm.CL.X86Encode
import Evm.CL.X86FlagProv
import Evm.CL.X86Handler
import Evm.CL.X86Interp
import Evm.CL.X86Items
import Evm.CL.X86JIT
import Evm.CL.X86Run
import Evm.CL.ARM64.SstoreGasSem
-- the precompile wrappers over a crypto oracle (Phase F) and the oracle contracts
import Evm.Istanbul.Spec.Refinement
import Evm.Prague.Spec.Refinement
import Evm.Osaka.Spec.Refinement
import Evm.Crypto.Contracts
-- every module that declares an @[extern] (the extern inventory, at the end)
import Evm.Crypto.Hash
import Evm.Crypto.Sha256
import Evm.Crypto.Ripemd160
import Evm.Crypto.EcRecover
import Evm.Crypto.Bn254
import Evm.Crypto.P256Verify
import Evm.Crypto.Bls12381
import Evm.Cancun.Vm.PrecompiledContracts

-- IR pipeline: compiled chunks ⇔ executable and ⇔ spec relations.
#print axioms Evm.IR.Soundness.compile_sound_vs_effect
#print axioms Evm.IR.Soundness.compile_sound_vs_spec
#print axioms Evm.IR.Soundness.compileProgram_sound_vs_spec

-- Symbolic partial evaluation (chunk-local constant folding).
#print axioms Evm.IR.SymExpr.symStep_sound

-- Effect layer: derived callbacks refine every fork's spec (one entry
-- point per effect proof, plus the *_binding companions where present).
#print axioms Evm.CL.EffectBlockProof.credits_refines
#print axioms Evm.CL.EffectCall.call_refines
#print axioms Evm.CL.EffectCall.call_spec_refines
#print axioms Evm.CL.EffectCall.afterPlan_refines
#print axioms Evm.CL.EffectCall.finish_refines
#print axioms Evm.CL.EffectCreate.create_refines
#print axioms Evm.CL.EffectCreate.create_spec_refines
#print axioms Evm.CL.EffectCreate.finish_refines
#print axioms Evm.CL.EffectEndTx.endTx_refines
#print axioms Evm.CL.EffectSelfdestruct.selfdestruct_refines
#print axioms Evm.CL.EffectSettle.settle_refines
#print axioms Evm.CL.EffectSload.sload_refines
#print axioms Evm.CL.EffectSstore.sstore_refines
#print axioms Evm.CL.EffectSstore.tail_refines
#print axioms Evm.CL.EffectSystem.system_refines
#print axioms Evm.CL.EffectSystem.checked_refines
#print axioms Evm.CL.EffectTx.apply_tx_refines
#print axioms Evm.CL.EffectTx.tx_refines
#print axioms Evm.CL.AsmCore.memExpand_acc_refines

-- Emitted gas formulas == fork specs (per fork / per formula).
#print axioms Evm.CL.GasEmitLondon.initialBaseFee_eq_spec
#print axioms Evm.CL.GasEmitLondon.nextBaseFee_eq_spec
#print axioms Evm.CL.GasEmitCancun.blobBaseFee_eq_spec
#print axioms Evm.CL.GasEmitCancun.maxBlobGasPerBlock_eq_spec
#print axioms Evm.CL.GasEmitCancun.nextExcessBlobGas_eq_spec
#print axioms Evm.CL.GasEmitCancun.txMaxGasLimit_eq_spec
#print axioms Evm.CL.GasEmitPrague.calldataFloor_eq_spec
#print axioms Evm.CL.GasEmitPrague.intrinsicCall_eq_spec
#print axioms Evm.CL.GasEmitPrague.intrinsicCreate_eq_spec
#print axioms Evm.CL.GasEmitPrague.txGasUsed_eq_spec
#print axioms Evm.CL.HeaderEmit.blockDifficulty_eq_spec
#print axioms Evm.CL.HeaderEmit.headerViolation_eq_spec
#print axioms Evm.CL.Flags.charge_is_spec
#print axioms Evm.CL.ForkEmit.mainnetForkOrd_eq_spec
#print axioms Evm.CL.BlobEnv.blobbasefee_is_spec
#print axioms Evm.CL.BlobEnv.blobhash_is_spec
#print axioms Evm.CL.HostEmit.createCollision_eq_spec

-- The re-costing tool's prices == Osaka's schedule / EIP-8037/8038 (EELS 636b5f1); the
-- EIP-8037 gas meter's facts.
#print axioms Evm.CL.RepriceEmit.osakaSstore_eq_spec
#print axioms Evm.CL.RepriceEmit.amsSstore_eq_spec
#print axioms Evm.CL.RepriceEmit.osakaCallCharge_eq_spec
#print axioms Evm.CL.RepriceEmit.amsCall_eq_spec
#print axioms Evm.CL.RepriceEmit.amsTxGasUsed_eq_spec
#print axioms Evm.Amsterdam.Vm.Gas.credit_after_charge
#print axioms Evm.Amsterdam.Vm.Gas.allocate_split

-- Arc host spec + ARM64 semantics-of-gas lemmas.
#print axioms Evm.Arc.Spec.BlockSystem.nextBaseFeeExpr_eq_spec
#print axioms Evm.Arc.Spec.BlockSystem.smoothedGasUsedExpr_eq_spec
#print axioms Evm.CL.ARM64.SstoreGasDenote.legacy_eq_spec
#print axioms Evm.CL.ARM64.SstoreGasDenote.eip1283_eq_spec
#print axioms Evm.CL.ARM64.SstoreGasDenote.eip2200_eq_spec
#print axioms Evm.CL.ARM64.SstoreGasDenote.berlin_eq_spec
#print axioms Evm.CL.ARM64.SstoreGasDenote.london_eq_spec
#print axioms Evm.CL.ARM64.MemCommitSem.ecost_eq_spec
#print axioms Evm.CL.ARM64.MemCommitSem.mcost_eq_spec
#print axioms Evm.CL.ARM64.CallGasDenote.planFrontier_eq_spec
#print axioms Evm.CL.ARM64.CallGasDenote.planTangerine_eq_spec
#print axioms Evm.CL.ARM64.CallGasDenote.plan_eq_spec

-- Parallel execution refines sequential.
#print axioms Evm.Parallel.BlockSTM.blockSTM_refines_seq

-- The stack-cache check is sound against the AsmRun semantics (no native_decide), and
-- so every handler body's runs keep the cache (via the native_decide verdict).
#print axioms Evm.CL.CacheSound.cacheIncoherent_sound
#print axioms Evm.CL.ARM64.Interp.handler_runs_cache_coherent
-- …and on x86-64, over the lowered bodies and `X86Sem.xstep` (also for `xrun`).
#print axioms Evm.CL.X86CacheSound.xcacheIncoherent_sound
#print axioms Evm.CL.X86CacheSound.xrun_ret_coherent
#print axioms Evm.CL.X86CacheSound.x86_handler_runs_cache_coherent

-- Precompile wrappers = EELS for every crypto oracle (no axiom beyond Lean's three).
#print axioms Evm.Istanbul.Spec.Refinement.blake2f_sound
#print axioms Evm.Istanbul.Spec.Refinement.blake2f_failure_sound
#print axioms Evm.Prague.Spec.Refinement.g1Add_sound
#print axioms Evm.Prague.Spec.Refinement.g1Msm_sound
#print axioms Evm.Prague.Spec.Refinement.g2Add_sound
#print axioms Evm.Prague.Spec.Refinement.g2Msm_sound
#print axioms Evm.Prague.Spec.Refinement.pairingCheck_sound
#print axioms Evm.Prague.Spec.Refinement.mapFpToG1_sound
#print axioms Evm.Prague.Spec.Refinement.mapFp2ToG2_sound
#print axioms Evm.Prague.Spec.Refinement.pairingCheck_failure_sound
#print axioms Evm.Osaka.Spec.Refinement.p256Verify_sound
#print axioms Evm.Osaka.Spec.Refinement.p256Verify_failure_sound
#print axioms Evm.Crypto.Contracts.Bls12381.g1MsmSum_contract

/-! ## native_decide never runs an `@[extern]` / `@[implemented_by]` of ours

`native_decide` proves `p` by running the compiled `decide p` (v4.29: an
auxiliary axiom `<thm>._native.native_decide.ax_…` stating `decide p = true`;
older: `Lean.ofReduceBool`). If that code reaches one of the spec's
`@[extern]`s (keccak, sha256, bn254, p256, …: C) or an `@[implemented_by]`
(a different Lean function), the theorem is about that implementation, not the
definition it names. For every such axiom / `ofReduceBool` proof in an `Evm.*`
module: walk the constants the evaluated term reaches — through definition and
opaque values, instances, matchers and `_unsafe_rec` bodies, not proofs and
types (never executed), and only through `Evm.*` constants (Lean core, Batteries
and Mathlib cannot reach ours) — and fail on any `@[extern]` / `@[implemented_by]`
there, naming the theorem and the path. Every `Evm/**.lean` file that uses
native_decide must be imported above (checked), else its theorems go unseen.
`externAllowed` takes a reasoned exception: (theorem, constant, why). -/

namespace AxiomAudit.ExternRule
open Lean

/-- (theorem, constant it may run, why). Keyed by theorem: a new proof reaching the same
    constant fails until it is reviewed and listed. -/
def externAllowed : List (Name × Name × String) :=
  -- The JIT emitters' corpus gates (2026-11-08, the rule's first run): each runs the
  -- emitter over the fixture corpus as emitJIT itself runs it -- dagSlots through its
  -- pointer-memoized `dagSlotsImpl` (the reference is never executed: structural dedup is
  -- 2^k on DUP-shared trees), and the IR fold (dynCosts -> regionStep -> foldStep ->
  -- execOp) through the C Keccak for a constant-input KECCAK256. They gate the shipped
  -- emitter's output on the corpus (text identity, lowering, relocations, register
  -- aliasing, flag provenance); no proof uses them (docs and comments only), so they say
  -- nothing about the reference dagSlots or keccak256 that a lemma could build on.
  let gates := [``Evm.CL.ARM64.JIT.chunk_text_derived, ``Evm.CL.X86FlagProv.no_flag_provenance_hazards,
                ``Evm.CL.X86JIT.x86_chunks_lower, ``Evm.CL.X86JIT.x86_chunks_no_alias,
                ``Evm.CL.X86JIT.x86_chunks_only_abs64]
  gates.flatMap fun t =>
    [(t, ``Evm.CL.ARM64.JIT.dagSlots, "emitter corpus gate: emitJIT's own dagSlotsImpl"),
     (t, ``Evm.Crypto.keccak256Bytes, "emitter corpus gate: the IR fold's constant KECCAK256, emitJIT's own C Keccak")]

def ours (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => env.header.moduleNames[i.toNat]!.getRoot == `Evm
  | none => false

def isNativeAux (n : Name) : Bool :=
  n.components.any (· == `native_decide) && n.components.any (· == `_native)

def flagged (env : Environment) (c : Name) : Option String :=
  if isExtern env c then some "@[extern]"
  else (Compiler.implementedByAttr.getParam? env c).map (s!"@[implemented_by {·}]")

/-- What running `c` may run: its value (definitions, opaques), its compiled `_unsafe_rec`. -/
def execDeps (env : Environment) (c : Name) : Array Name :=
  let v := match env.find? c with
    | some (.defnInfo d) => d.value.getUsedConstants
    | some (.opaqueInfo d) => d.value.getUsedConstants
    | _ => #[]
  if env.contains (c ++ `_unsafe_rec) then v.push (c ++ `_unsafe_rec) else v

/-- Every flagged constant reachable from `start`, each with one path to it. -/
partial def reach (env : Environment) (start : Array Name) : Array (List Name × String) :=
  go (start.toList.map fun c => (c, [c])) {} #[]
where
  go : List (Name × List Name) → NameSet → Array (List Name × String) → Array (List Name × String)
  | [], _, acc => acc
  | (c, path) :: rest, seen, acc =>
    if seen.contains c || !ours env c then go rest seen acc
    else match flagged env c with
      | some why => go rest (seen.insert c) (acc.push (path.reverse, why))
      | none => go ((execDeps env c).toList.map (fun d => (d, d :: path)) ++ rest) (seen.insert c) acc

/-- `Evm/**.lean` files that use native_decide, as module names. -/
partial def nativeModules (dir : System.FilePath) (mod : Name) : IO (Array Name) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← nativeModules e.path (mod ++ .mkSimple e.fileName))
    else if e.path.extension == some "lean" then
      if ((← IO.FS.readFile e.path).splitOn "native_decide").length > 1 then
        out := out.push (mod ++ .mkSimple (e.path.fileStem.getD e.fileName))
  return out

end AxiomAudit.ExternRule

open Lean Elab Command AxiomAudit.ExternRule in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let missing := (← nativeModules "Evm" `Evm).filter (env.getModuleIdx? · |>.isNone)
  unless missing.isEmpty do
    throwError "extern rule: these modules use native_decide but AxiomAudit.lean does not import them: {missing.qsort Name.lt}"
  let mut checked := 0
  let mut bad : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless ours env n do continue
    let start? : Option (Name × Array Name) := match ci with
      | .axiomInfo a => if isNativeAux n then some (n.getPrefix.getPrefix.getPrefix, a.type.getUsedConstants) else none
      -- Lean ≥ v4.3x: `Lean.ofReduceBool` is gone; native_decide only produces the aux axiom above
      | _ => none
    let some (thm, start) := start? | continue
    checked := checked + 1
    for (path, why) in reach env start do
      unless externAllowed.any (fun (t, c, _) => t == thm && c == path.getLast!) do
        bad := bad.push s!"  {thm}: runs {path.getLast!} {why} via {path}"
  if bad.isEmpty then
    IO.eprintln s!"extern rule OK: {checked} native_decide / ofReduceBool proofs in Evm.*, none runs an Evm @[extern] / @[implemented_by] (allowed: {externAllowed.length} reviewed (theorem, constant) pairs)"
  else
    throwError "extern rule: {bad.size} native_decide proofs run an @[extern] / @[implemented_by]:\n{"\n".intercalate (bad.qsort (· < ·)).toList}"

/-! ## The extern inventory: every `@[extern]` in `Evm.*`, enumerated

Each `@[extern]` constant is C the Lean semantics trusts (the replay runs it; no proof
looks inside it). The list below is the complete set, each with the code and library it
binds and its role; a new `@[extern]` in any `Evm/**.lean` file fails this check until it
is listed here (and in docs/trusted-surface.md). Every file declaring one must be imported
above (checked). Oracle externs (BLS12-381, P-256) instantiate an oracle parameter: the
wrapper theorems hold for every oracle, so these bind only what the replay computes. -/

namespace AxiomAudit.ExternInventory
open Lean

def blst := "blst v0.3.17 (vendor/blst) via lean/c/bls12381.cpp"

/-- (constant, what it trusts). -/
def trusted : List (Name × String) :=
  [ (``Evm.Crypto.keccak256Bytes, "Keccak-256, own C (lean/c/keccak.c)"),
    (``Evm.Crypto.sha256, "SHA2-256, own C (lean/c/sha256.c)"),
    (``Evm.Crypto.ripemd160, "RIPEMD-160, own C (lean/c/ripemd160.c)"),
    (``Evm.Crypto.ecrecoverRaw, "secp256k1 recovery, libsecp256k1 v0.8.0 (vendor/secp256k1) via lean/c/ecrecover.c"),
    (``Evm.Crypto.bn254Add, "alt_bn128 add, mcl via lean/c/bn254.cpp"),
    (``Evm.Crypto.bn254Mul, "alt_bn128 mul, mcl via lean/c/bn254.cpp"),
    (``Evm.Crypto.bn254Pairing, "alt_bn128 pairing, mcl via lean/c/bn254.cpp"),
    (``Evm.Cancun.Vm.PrecompiledContracts.pointEvaluationRaw,
      "EIP-4844 point evaluation, blst v0.3.17 via lean/c/point_evaluation.c"),
    -- 2026-11-09 (Phase F): the P-256 and BLS12-381 oracle instances
    (``Evm.Crypto.verifyRaw,
      "P-256 oracle (Evm.Crypto.isValidP256Signature): OpenSSL libcrypto ECDSA_do_verify via lean/c/p256verify.c"),
    (``Evm.Crypto.Bls12381.g1AddRaw, s!"BLS12-381 oracle (native.g1Add): {blst}"),
    (``Evm.Crypto.Bls12381.g1MulRaw, s!"BLS12-381 oracle (native.g1Mul): {blst}"),
    (``Evm.Crypto.Bls12381.g1InG1Raw, s!"BLS12-381 oracle (native.g1InSubgroup): {blst}"),
    (``Evm.Crypto.Bls12381.g2AddRaw, s!"BLS12-381 oracle (native.g2Add): {blst}"),
    (``Evm.Crypto.Bls12381.g2MulRaw, s!"BLS12-381 oracle (native.g2Mul): {blst}"),
    (``Evm.Crypto.Bls12381.g2InG2Raw, s!"BLS12-381 oracle (native.g2InSubgroup): {blst}"),
    (``Evm.Crypto.Bls12381.mapFpToG1Raw, s!"BLS12-381 oracle (native.mapFpToG1): {blst}"),
    (``Evm.Crypto.Bls12381.mapFp2ToG2Raw, s!"BLS12-381 oracle (native.mapFp2ToG2): {blst}"),
    (``Evm.Crypto.Bls12381.pairingCheckRaw, s!"BLS12-381 oracle (native.pairingCheck): {blst}") ]

/-- `Evm/**.lean` files with an `@[extern` attribute line, as module names. -/
partial def externModules (dir : System.FilePath) (mod : Name) : IO (Array Name) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← externModules e.path (mod ++ .mkSimple e.fileName))
    else if e.path.extension == some "lean" then
      let lines := (← IO.FS.readFile e.path).splitOn "\n"
      if lines.any (·.trimAscii.startsWith "@[extern") then
        out := out.push (mod ++ .mkSimple (e.path.fileStem.getD e.fileName))
  return out

end AxiomAudit.ExternInventory

open Lean Elab Command AxiomAudit.ExternRule AxiomAudit.ExternInventory in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let missing := (← externModules "Evm" `Evm).filter (env.getModuleIdx? · |>.isNone)
  unless missing.isEmpty do
    throwError "extern inventory: these modules declare an @[extern] but AxiomAudit.lean does not import them: {missing.qsort Name.lt}"
  let found := env.constants.map₁.toList.filterMap fun (n, _) =>
    if ours env n && isExtern env n && !n.isInternal then some n else none
  let unlisted := found.filter fun n => !trusted.any (·.1 == n)
  let stale := trusted.filter fun (n, _) => !found.contains n
  unless unlisted.isEmpty && stale.isEmpty do
    throwError "extern inventory: unlisted @[extern]s {unlisted.toArray.qsort Name.lt}; listed but absent {stale.map (·.1)}"
  IO.eprintln s!"extern inventory OK: {found.length} @[extern] constants in Evm.*, each enumerated with the library it trusts"
