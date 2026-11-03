/-
  AxiomAudit — print the axiom closure of the headline theorems.

  scripts/verify-axioms.sh runs this file, diffs the output against the
  committed scripts/generated/axiom-audit.txt, and hard-fails on any
  drift or on a trust_smt reappearance (SMT-solver discharge via the
  since-removed loom dependency). Regenerate after an intended change:

    (cd lean && lake env lean AxiomAudit.lean | sed 's/^info: //' \
      > ../scripts/generated/axiom-audit.txt)

  Coverage (per review on PR #44): every effect-layer `*_refines`
  entry point, every emitted `*_eq_spec` / `*_is_spec` theorem, plus
  the IR-pipeline and BlockSTM headlines. A new axiom (or a
  native_decide, whose ofReduceBool shows up here) must land in the
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
