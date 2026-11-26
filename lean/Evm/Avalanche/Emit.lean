/-
  Evm.Avalanche.Emit — emitted Avalanche C-Chain rules (`Evm.CL.GasEmit.Expr`), each proved
  equal to its Lean specification in `Evm.Avalanche.*`.

  Emitted into `src/generated/host.lisp` by `lean/EmitHostCL.lean`:
    spec-avax-mainnet-fork-ord (ts)              = (AvaxFork.mainnetAt ts).ord
    spec-avax-fuji-fork-ord (ts)                 = (AvaxFork.fujiAt ts).ord
    spec-avax-eth-analog-ord (avax-fork)         = (AvaxFork.ethereumAnalog f).ord
    spec-avax-p256-active (avax-fork)            = 1 iff p256Active else 0
    spec-avax-sae-active (avax-fork)             = 1 iff saeActive else 0
    spec-avax-extradata-offset (avax-fork)       = extraDataResultsOffset f
    spec-avax-sae-gas-floor (gas-limit)          = Charging.saeGasFloor gasLimit
    spec-avax-tx-gas-used (avax-fork spent pred-gas gas-limit)
                                                 = Charging.txGasUsed f spent predGas gasLimit
    spec-avax-warp-blockchain-id-gas ()          = Warp.getBlockchainIdGas
    spec-avax-warp-send-gas (arg-len)            = Warp.sendWarpGas argLen
    spec-avax-warp-read-gas (num-keys)           = Warp.readWarpGas numKeys
    spec-avax-warp-predicate-gas (num-keys num-signers)
                                                 = Warp.predicateGas numKeys numSigners
    spec-avax-atomic-tx-gas (unsigned-bytes num-sigs)
                                                 = Atomic.atomicTxGas unsignedBytes numSigs
    spec-avax-gasclock-target (target-exp)       = GasClock.targetOfExponent targetExp
    spec-avax-gasclock-min-price (min-price-exp) = GasClock.minPriceOfExponent minPriceExp
    spec-avax-gasclock-price-at (excess target)  = (Params.mk target 0).priceAt excess
    spec-avax-gasclock-base-fee (excess target min-price)
                                                 = max (priceAt excess target) minPrice
-/

import Evm.CL.GasEmit
import Evm.Avalanche.Forks
import Evm.Avalanche.Charging
import Evm.Avalanche.GasClock
import Evm.Avalanche.Warp
import Evm.Avalanche.Atomic

namespace Evm.Avalanche.Emit

open Evm.CL.GasEmit (Expr Env mkEnv)
open Evm.Avalanche (AvaxFork)

private def v (x : String) : Expr := .var x
private def n (k : Nat) : Expr := .lit k

private def geChain (x : String) : List (Nat × Nat) → Nat → Expr
  | [], d => .lit d
  | (k, o) :: r, d => .ite (.var x) (.lit k) (geChain x r d) (.lit o)

/-! ## Fork schedule -/

def mainnetForkOrdExpr : Expr :=
  geChain "ts"
    [ (AvaxFork.mainnetHeliconTime, 4)
    , (AvaxFork.mainnetGraniteTime, 3)
    , (AvaxFork.mainnetFortunaTime, 2)
    , (AvaxFork.mainnetEtnaTime, 1) ] 0

set_option backward.isDefEq.respectTransparency false in
theorem mainnetForkOrdExpr_eq_spec (ρ : Env) :
    mainnetForkOrdExpr.eval ρ = (AvaxFork.mainnetAt (ρ "ts")).ord := by
  simp only [mainnetForkOrdExpr, geChain, Expr.eval, AvaxFork.mainnetAt]
  simp only [apply_ite (f := AvaxFork.ord)]
  simp only [AvaxFork.ord]
  generalize AvaxFork.mainnetHeliconTime = k4 at *
  generalize AvaxFork.mainnetGraniteTime = k3 at *
  generalize AvaxFork.mainnetFortunaTime = k2 at *
  generalize AvaxFork.mainnetEtnaTime    = k1 at *
  simp only [ge_iff_le, ← Nat.not_lt, ite_not]

def fujiForkOrdExpr : Expr :=
  geChain "ts"
    [ (AvaxFork.fujiHeliconTime, 4)
    , (AvaxFork.fujiGraniteTime, 3)
    , (AvaxFork.fujiFortunaTime, 2)
    , (AvaxFork.fujiEtnaTime, 1) ] 0

set_option backward.isDefEq.respectTransparency false in
theorem fujiForkOrdExpr_eq_spec (ρ : Env) :
    fujiForkOrdExpr.eval ρ = (AvaxFork.fujiAt (ρ "ts")).ord := by
  simp only [fujiForkOrdExpr, geChain, Expr.eval, AvaxFork.fujiAt]
  simp only [apply_ite (f := AvaxFork.ord)]
  simp only [AvaxFork.ord]
  generalize AvaxFork.fujiHeliconTime = k4 at *
  generalize AvaxFork.fujiGraniteTime = k3 at *
  generalize AvaxFork.fujiFortunaTime = k2 at *
  generalize AvaxFork.fujiEtnaTime    = k1 at *
  simp only [ge_iff_le, ← Nat.not_lt, ite_not]

def ethAnalogOrdExpr : Expr :=
  .ite (v "avax-fork") (n 1) (n 15) (n 16)

theorem ethAnalogOrdExpr_eq_spec (f : AvaxFork) :
    ethAnalogOrdExpr.eval (mkEnv [("avax-fork", f.ord)]) = (AvaxFork.ethereumAnalog f).ord := by
  cases f <;> decide

def p256ActiveExpr : Expr :=
  .ite (v "avax-fork") (n 3) (n 0) (n 1)

theorem p256ActiveExpr_eq_spec (f : AvaxFork) :
    p256ActiveExpr.eval (mkEnv [("avax-fork", f.ord)]) = if f.p256Active then 1 else 0 := by
  cases f <;> decide

def saeActiveExpr : Expr :=
  .ite (v "avax-fork") (n 4) (n 0) (n 1)

theorem saeActiveExpr_eq_spec (f : AvaxFork) :
    saeActiveExpr.eval (mkEnv [("avax-fork", f.ord)]) = if f.saeActive then 1 else 0 := by
  cases f <;> decide

def extraDataOffsetExpr : Expr :=
  .ite (v "avax-fork") (n 2) (n 80) (.ite (v "avax-fork") (n 4) (n 24) (n 0))

theorem extraDataOffsetExpr_eq_spec (f : AvaxFork) :
    extraDataOffsetExpr.eval (mkEnv [("avax-fork", f.ord)]) = f.extraDataResultsOffset := by
  cases f <;> decide

/-! ## Coreth & SAE charging -/

def saeGasFloorExpr : Expr :=
  .fdiv (.add (v "gas-limit") (n 1)) (n Charging.saeLambda)

theorem saeGasFloorExpr_eq_spec (ρ : Env) :
    saeGasFloorExpr.eval ρ = Charging.saeGasFloor (ρ "gas-limit") := by
  rfl

def txGasUsedExpr : Expr :=
  let totalSpent := .add (v "spent") (v "pred-gas")
  .ite (v "avax-fork") (n 4) totalSpent (.emax totalSpent saeGasFloorExpr)

theorem txGasUsedExpr_eq_spec (f : AvaxFork) (spent predGas gasLimit : Nat) :
    txGasUsedExpr.eval (mkEnv [("avax-fork", f.ord), ("spent", spent), ("pred-gas", predGas), ("gas-limit", gasLimit)])
      = Charging.txGasUsed f spent predGas gasLimit := by
  cases f <;> simp [txGasUsedExpr, saeGasFloorExpr, v, n, Charging.txGasUsed, Charging.saeGasFloor,
                    AvaxFork.saeActive, AvaxFork.atLeast, AvaxFork.ord, Expr.eval, mkEnv]

/-! ## Warp Messenger gas -/

def warpBlockchainIdGasExpr : Expr := n Warp.getBlockchainIdGas
def warpSendGasExpr         : Expr := .add (n Warp.sendGas) (.mul (n Warp.sendPerByteGas) (v "arg-len"))
def warpReadGasExpr         : Expr := .add (n Warp.verifiedReadGas) (.mul (n Warp.perKeyGas) (v "num-keys"))
def warpPredicateGasExpr    : Expr :=
  .add (.add (n Warp.verifyGas) (.mul (n Warp.perKeyGas) (v "num-keys")))
       (.mul (n Warp.perSignerGas) (v "num-signers"))

theorem warpBlockchainIdGasExpr_eq_spec (ρ : Env) :
    warpBlockchainIdGasExpr.eval ρ = Warp.getBlockchainIdGas := rfl

theorem warpSendGasExpr_eq_spec (ρ : Env) :
    warpSendGasExpr.eval ρ = Warp.sendWarpGas (ρ "arg-len") := rfl

theorem warpReadGasExpr_eq_spec (ρ : Env) :
    warpReadGasExpr.eval ρ = Warp.readWarpGas (ρ "num-keys") := rfl

theorem warpPredicateGasExpr_eq_spec (ρ : Env) :
    warpPredicateGasExpr.eval ρ = Warp.predicateGas (ρ "num-keys") (ρ "num-signers") := rfl

/-! ## Atomic tx gas -/

def atomicTxGasExpr : Expr :=
  .add (.add (.lit (Atomic.atomicIntrinsicGas + Atomic.codecVersionBytes)) (v "unsigned-bytes"))
       (.mul (n Atomic.atomicGasPerSig) (v "num-sigs"))

theorem atomicTxGasExpr_eq_spec (ρ : Env) :
    atomicTxGasExpr.eval ρ = Atomic.atomicTxGas (ρ "unsigned-bytes") (ρ "num-sigs") := by
  simp [atomicTxGasExpr, v, n, Atomic.atomicTxGas, Expr.eval]

/-! ## SAE GasClock pricing -/

def gasClockTargetExpr : Expr :=
  .emax (n 1)
    (.emin
      (.emin (.fakeExp (n GasClock.minTarget) (v "target-exp") (n GasClock.targetConversion))
             (n GasClock.maxU64))
      (n (GasClock.maxU64 / GasClock.targetToRate)))

theorem gasClockTargetExpr_eq_spec (ρ : Env) :
    gasClockTargetExpr.eval ρ = GasClock.targetOfExponent (ρ "target-exp") := by
  simp [gasClockTargetExpr, v, n, GasClock.targetOfExponent, GasClock.satFakeExp, GasClock.satU64,
        GasClock.targetConversion, Expr.eval]

def gasClockMinPriceExpr : Expr :=
  .emin (.fakeExp (n 1) (v "min-price-exp") (n GasClock.minPriceConversion)) (n GasClock.maxU64)

theorem gasClockMinPriceExpr_eq_spec (ρ : Env) :
    gasClockMinPriceExpr.eval ρ = GasClock.minPriceOfExponent (ρ "min-price-exp") := by
  simp [gasClockMinPriceExpr, v, n, GasClock.minPriceOfExponent, GasClock.satFakeExp, GasClock.satU64,
        GasClock.minPriceConversion, Expr.eval]

def gasClockPriceAtExpr : Expr :=
  let scaling := .emin (.mul (v "target") (n GasClock.targetToExcessScaling)) (n GasClock.maxU64)
  .ite scaling (n 1) (n 0)
    (.emin (.fakeExp (n 1) (v "excess") scaling) (n GasClock.maxU64))

theorem gasClockPriceAtExpr_eq_spec (ρ : Env) :
    gasClockPriceAtExpr.eval ρ = (GasClock.Params.mk (ρ "target") 0).priceAt (ρ "excess") := by
  simp only [gasClockPriceAtExpr, v, n, GasClock.Params.priceAt, GasClock.Params.scaling,
             GasClock.satFakeExp, GasClock.satU64, Expr.eval]
  by_cases h0 : min (ρ "target" * GasClock.targetToExcessScaling) GasClock.maxU64 = 0
  · simp [h0]
  · have hge : ¬ (min (ρ "target" * GasClock.targetToExcessScaling) GasClock.maxU64 < 1) := by omega
    simp [h0, hge]

def gasClockBaseFeeExpr : Expr :=
  .emax gasClockPriceAtExpr (v "min-price")

theorem gasClockBaseFeeExpr_eq_spec (ρ : Env) :
    gasClockBaseFeeExpr.eval ρ =
      max ((GasClock.Params.mk (ρ "target") (ρ "min-price")).priceAt (ρ "excess")) (ρ "min-price") := by
  simp only [gasClockBaseFeeExpr, Expr.eval]
  rw [gasClockPriceAtExpr_eq_spec]
  rfl

end Evm.Avalanche.Emit
