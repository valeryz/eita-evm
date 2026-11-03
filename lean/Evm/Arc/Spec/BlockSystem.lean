/-
  Evm.Arc.Spec.BlockSystem — Arc's per-block system state (beyond the txs).

  Source: circlefin/arc-node@6e76402
    crates/evm/src/executor.rs            apply_pre_execution_changes (EIP-2935 call),
                                          apply_post_block_writes / compute_gas_values
    crates/execution-config/src/gas_fee.rs determine_ema_parent_gas_used,
                                          arc_calc_next_block_base_fee
    crates/execution-config/src/chainspec.rs BASE_FEE_CONFIG_MAINNET (L336),
                                          resolve_calc_params, clamp_absolute
    crates/precompiles/src/system_accounting.rs  ring-buffer slot + packing

  Every block: (1) the EIP-2935 history contract is called with the parent hash;
  (2) after the txs, `storeGasValues(n, {gasUsed, gasUsedSmoothed, nextBaseFee})`
  writes one word into SystemAccounting's 64-slot ring buffer. `nextBaseFee` is
  ALSO what the client validates the header's `extra_data` against, and it is the
  next block's `baseFeePerGas` — so the math below is checkable against headers.

  Mainnet genesis headers (rpc.mainnet.arc.io):
    block 0: baseFee 1 000 000 000, gasUsed 0, gasLimit 30 000 000, extraData empty
    block 1: baseFee   980 000 000, extraData 0x00000004a817c800 (= 20 gwei)
    block 2: baseFee 20 000 000 000
  At block 0 `feeParams()` is unavailable (ProtocolConfig not yet initialised) →
  chainspec defaults, no ProtocolConfig clamp → 1 gwei − 2 % = 0.98 gwei. From
  block 1 `feeParams()` succeeds with minBaseFee = 20 gwei → clamp → 20 gwei.
-/

import Evm.CL.GasEmit
import Evm.Frontier.Vm.System
import Evm.Arc.Spec.NativeCoin

namespace Evm.Arc.Spec.BlockSystem

def alphaMax : Nat := 100
def fpScale  : Nat := 10000

/-- EMA of the parent's smoothed gas used with this block's raw gas used
    (gas_fee.rs:23). `none` when α > 100 (the executor then uses the raw value). -/
def emaGasUsed (smoothedParent raw alpha : Nat) : Option Nat :=
  if alpha ≤ alphaMax then some (((alphaMax - alpha) * smoothedParent + alpha * raw) / alphaMax)
  else none

/-- arc_calc_next_block_base_fee (gas_fee.rs:69): fixed-point EIP-1559.
    target = limit·inv/10000, denominator = target·10000/k; +max(1, Δ) above
    target, −Δ below, unchanged at target or when a divisor degenerates. -/
def nextBaseFee (gasUsed gasLimit baseFee kRate invElasticity : Nat) : Nat :=
  let target := gasLimit * invElasticity / fpScale
  if target = 0 ∨ kRate = 0 then baseFee
  else
    let denominator := target * fpScale / kRate
    if denominator = 0 then baseFee
    else if gasUsed = target then baseFee
    else if gasUsed > target then baseFee + max 1 (baseFee * (gasUsed - target) / denominator)
    else baseFee - baseFee * (target - gasUsed) / denominator

/-- Mainnet BaseFeeConfig defaults (chainspec.rs:336): alpha 20, kRate 200,
    inverseElasticity 5000; absolute bounds [1, 20 000 gwei]. -/
def mainnetAlpha : Nat := 20
def mainnetKRate : Nat := 200
def mainnetInvElasticity : Nat := 5000
def mainnetAbsMin : Nat := 1
def mainnetAbsMax : Nat := 20000000000000

/-- ProtocolConfig clamp (protocol_config.rs:82): no-op for a nonsensical range. -/
def boundedBaseFee (minFee maxFee fee : Nat) : Nat :=
  if maxFee = 0 ∨ maxFee < minFee then fee else max minFee (min maxFee fee)

/-- Block 0 → 1 (defaults, no ProtocolConfig clamp): 1 gwei − 2 % = 0.98 gwei. -/
example : nextBaseFee 0 30000000 1000000000 mainnetKRate mainnetInvElasticity = 980000000 := by decide
/-- Block 1 → 2: the raw value is clamped up to ProtocolConfig's 20 gwei floor. -/
example : boundedBaseFee 20000000000 20000000000000
    (nextBaseFee 0 30000000 980000000 mainnetKRate mainnetInvElasticity) = 20000000000 := by decide
/-- Block 2 → 3: 20 gwei − 2 % clamps straight back to 20 gwei. -/
example : boundedBaseFee 20000000000 20000000000000
    (nextBaseFee 0 30000000 20000000000 mainnetKRate mainnetInvElasticity) = 20000000000 := by decide
/-- EMA with α = 20: 80 % parent, 20 % raw. -/
example : emaGasUsed 1000000 2000000 mainnetAlpha = some 1200000 := by decide
example : emaGasUsed 0 0 101 = none := by decide

/-! ## compute_gas_values (executor.rs:291-348)

The whole post-block computation: bounded parameter resolution (chainspec.rs:157,
228-246), the EMA, the next base fee, ProtocolConfig's clamp when `feeParams()` answered,
and the chainspec's absolute clamp (chainspec.rs:249). -/

/-- `BoundedParam` (chainspec.rs:150-164). -/
structure BoundedParam where
  lo : Nat
  default : Nat
  hi : Nat

/-- `BoundedParam::resolve`: the on-chain value if within [lo, hi], else the default;
    `resolve_calc_params` uses the defaults when `feeParams()` failed (`none`). -/
def BoundedParam.resolve (p : BoundedParam) : Option Nat → Nat
  | some v => if p.lo ≤ v ∧ v ≤ p.hi then v else p.default
  | none   => p.default

/-- BASE_FEE_CONFIG_MAINNET (chainspec.rs:336-342). -/
def mainnetAlphaBounds : BoundedParam := ⟨1, mainnetAlpha, 100⟩
def mainnetKRateBounds : BoundedParam := ⟨1, mainnetKRate, 1000⟩
def mainnetInvElasticityBounds : BoundedParam := ⟨1, mainnetInvElasticity, 9000⟩

/-- `clamp_absolute` (chainspec.rs:249). -/
def clampAbsolute (fee : Nat) : Nat := max mainnetAbsMin (min mainnetAbsMax fee)

/-- `IProtocolConfig::FeeParams` as the executor reads it. -/
structure FeeParams where
  alpha : Nat
  kRate : Nat
  invElasticity : Nat
  minBaseFee : Nat
  maxBaseFee : Nat

/-- `compute_gas_values` (executor.rs:291-348): `(gasUsedSmoothed, nextBaseFee)`. -/
def computeGasValues (gasUsed gasLimit baseFee parentSmoothed : Nat) (fp : Option FeeParams) : Nat × Nat :=
  let alpha := mainnetAlphaBounds.resolve (fp.map (·.alpha))
  let kRate := mainnetKRateBounds.resolve (fp.map (·.kRate))
  let inv   := mainnetInvElasticityBounds.resolve (fp.map (·.invElasticity))
  let smoothed := (emaGasUsed parentSmoothed gasUsed alpha).getD gasUsed
  let raw := nextBaseFee smoothed gasLimit baseFee kRate inv
  let clamped := match fp with
    | some p => boundedBaseFee p.minBaseFee p.maxBaseFee raw
    | none   => raw
  (smoothed, clampAbsolute clamped)

/-- Mainnet blocks 0 → 1 → 2 (header extra_data 0x…3a699d00 = 0.98 gwei, then 20 gwei). -/
example : (computeGasValues 0 30000000 1000000000 0 none).2 = 980000000 := by decide
example : (computeGasValues 0 30000000 980000000 0
    (some ⟨20, 200, 5000, 20000000000, 20000000000000⟩)).2 = 20000000000 := by decide

/-! ### The same computation as emitted formulas (src/generated/host.lisp)

Inputs: `gas-used`, `gas-limit`, `base-fee`, `smoothed-parent`, `have-params` (0/1:
did `feeParams()` answer), and the raw `alpha`, `k-rate`, `inv-elasticity`, `min-fee`,
`max-fee` it returned. The theorems below prove each emitted formula equal to
`computeGasValues` for every input. -/

open Evm.CL.GasEmit (Expr Env)

private def v (x : String) : Expr := .var x
private def n (k : Nat) : Expr := .lit k

/-- `resolve` of the input `x` against `p`, defaults unless `have-params`. -/
def resolveExpr (p : BoundedParam) (x : String) : Expr :=
  .ite (n 0) (v "have-params")
    (.ite (v x) (n p.lo) (n p.default) (.ite (n p.hi) (v x) (n p.default) (v x)))
    (n p.default)

/-- `determine_ema_parent_gas_used(..).unwrap_or(gas_used)` over `alpha`. -/
def emaExpr : Expr :=
  .ite (n alphaMax) (v "alpha") (v "gas-used")
    (.fdiv (.add (.mul (.sub (n alphaMax) (v "alpha")) (v "smoothed-parent")) (.mul (v "alpha") (v "gas-used")))
           (n alphaMax))

/-- `arc_calc_next_block_base_fee(smoothed, gas-limit, base-fee, k-rate, inv-elasticity)`.
    Divisions by `den` sit only in branches where `den > 0` (CL `if` is lazy). -/
def nextFeeExpr : Expr :=
  let target : Expr := .fdiv (.mul (v "gas-limit") (v "inv-elasticity")) (n fpScale)
  let den : Expr := .fdiv (.mul target (n fpScale)) (v "k-rate")
  let base := v "base-fee"
  let su := v "smoothed"
  .ite (n 0) target
    (.ite (n 0) (v "k-rate")
      (.ite (n 0) den
        (.ite su target
          (.sub base (.fdiv (.mul base (.sub target su)) den))
          (.ite target su (.add base (.emax (n 1) (.fdiv (.mul base (.sub su target)) den))) base))
        base)
      base)
    base

/-- `determine_bounded_base_fee(fp, fee)` over `min-fee`, `max-fee`. -/
def boundedExpr : Expr :=
  .ite (n 0) (v "max-fee")
    (.ite (v "max-fee") (v "min-fee") (v "fee") (.emax (v "min-fee") (.emin (v "max-fee") (v "fee"))))
    (v "fee")

/-- Emitted `spec-arc-smoothed-gas-used`. -/
def smoothedGasUsedExpr : Expr := emaExpr.subst "alpha" (resolveExpr mainnetAlphaBounds "alpha")

/-- Emitted `spec-arc-next-base-fee`. -/
def nextBaseFeeExpr : Expr :=
  -- substitute the resolved parameters first and the smoothed gas last, so each piece
  -- is evaluated over the caller's inputs
  let raw : Expr := ((nextFeeExpr.subst "k-rate" (resolveExpr mainnetKRateBounds "k-rate")).subst
                       "inv-elasticity" (resolveExpr mainnetInvElasticityBounds "inv-elasticity")).subst
                       "smoothed" smoothedGasUsedExpr
  let clamped : Expr := .ite (n 0) (v "have-params") (boundedExpr.subst "fee" raw) raw
  .emax (n mainnetAbsMin) (.emin (n mainnetAbsMax) clamped)

/-- The fee params the environment describes. -/
def envParams (ρ : Env) : Option FeeParams :=
  if 0 < ρ "have-params" then
    some ⟨ρ "alpha", ρ "k-rate", ρ "inv-elasticity", ρ "min-fee", ρ "max-fee"⟩
  else none

theorem resolveExpr_eval (p : BoundedParam) (x : String) (ρ : Env) :
    (resolveExpr p x).eval ρ =
      p.resolve (if 0 < ρ "have-params" then some (ρ x) else none) := by
  unfold resolveExpr v n
  by_cases h : 0 < ρ "have-params"
  · by_cases h1 : ρ x < p.lo <;> by_cases h2 : p.hi < ρ x <;>
      simp [Expr.eval, BoundedParam.resolve, h, h1, h2] <;> omega
  · simp [Expr.eval, BoundedParam.resolve, h]

theorem emaExpr_eval (ρ : Env) :
    emaExpr.eval ρ = (emaGasUsed (ρ "smoothed-parent") (ρ "gas-used") (ρ "alpha")).getD (ρ "gas-used") := by
  unfold emaExpr v n emaGasUsed
  by_cases h : ρ "alpha" ≤ alphaMax
  · have h' : ¬ alphaMax < ρ "alpha" := by omega
    simp [Expr.eval, h, h']
  · have h' : alphaMax < ρ "alpha" := by omega
    simp [Expr.eval, h, h']

theorem nextFeeExpr_eval (ρ : Env) :
    nextFeeExpr.eval ρ = nextBaseFee (ρ "smoothed") (ρ "gas-limit") (ρ "base-fee") (ρ "k-rate") (ρ "inv-elasticity") := by
  unfold nextFeeExpr v n nextBaseFee
  simp only [Expr.eval]
  generalize ρ "gas-limit" * ρ "inv-elasticity" / fpScale = T
  generalize ρ "k-rate" = K
  generalize ρ "smoothed" = S
  generalize ρ "base-fee" = B
  by_cases hT : T = 0
  · simp [hT]
  by_cases hK : K = 0
  · simp [hK]
  have hT' : 0 < T := Nat.pos_of_ne_zero hT
  have hK' : 0 < K := Nat.pos_of_ne_zero hK
  generalize T * fpScale / K = D
  by_cases hD : D = 0
  · simp [hT, hK, hT', hK', hD]
  have hD' : 0 < D := Nat.pos_of_ne_zero hD
  by_cases h1 : S < T
  · have h3 : S ≠ T := by omega
    have h4 : ¬ S > T := by omega
    simp [hT, hK, hT', hK', hD, hD', h1, h3, h4]
  · by_cases h2 : T < S
    · have h3 : S ≠ T := by omega
      have h4 : S > T := by omega
      simp [hT, hK, hT', hK', hD, hD', h1, h2, h3]
    · have h3 : S = T := by omega
      simp [hT, hK, hT', hK', hD, hD', h3]

theorem boundedExpr_eval (ρ : Env) :
    boundedExpr.eval ρ = boundedBaseFee (ρ "min-fee") (ρ "max-fee") (ρ "fee") := by
  unfold boundedExpr v n boundedBaseFee
  by_cases hm : ρ "max-fee" = 0
  · simp [Expr.eval, hm]
  · have hm' : 0 < ρ "max-fee" := Nat.pos_of_ne_zero hm
    by_cases hl : ρ "max-fee" < ρ "min-fee" <;> simp [Expr.eval, hm, hm', hl]

/-- The emitted smoothed gas used IS `compute_gas_values`' first component. -/
theorem smoothedGasUsedExpr_eq_spec (ρ : Env) :
    smoothedGasUsedExpr.eval ρ =
      (computeGasValues (ρ "gas-used") (ρ "gas-limit") (ρ "base-fee") (ρ "smoothed-parent") (envParams ρ)).1 := by
  unfold smoothedGasUsedExpr computeGasValues envParams
  rw [Expr.eval_subst, emaExpr_eval]
  by_cases h : 0 < ρ "have-params" <;> simp [resolveExpr_eval, h]

/-- The emitted next base fee IS `compute_gas_values`' second component. -/
theorem nextBaseFeeExpr_eq_spec (ρ : Env) :
    nextBaseFeeExpr.eval ρ =
      (computeGasValues (ρ "gas-used") (ρ "gas-limit") (ρ "base-fee") (ρ "smoothed-parent") (envParams ρ)).2 := by
  unfold nextBaseFeeExpr
  by_cases h : 0 < ρ "have-params" <;>
    simp [Expr.eval, v, n, h, Expr.eval_subst, boundedExpr_eval, nextFeeExpr_eval, resolveExpr_eval,
      smoothedGasUsedExpr_eq_spec, computeGasValues, envParams, clampAbsolute]

/-- Ring-buffer packing (system_accounting.rs:220): word = nextBaseFee·2¹²⁸ + smoothed·2⁶⁴ + gasUsed. -/
def packGasValues (gasUsed smoothed nextFee : Nat) : Nat :=
  nextFee * 2 ^ 128 + smoothed * 2 ^ 64 + gasUsed
example : packGasValues 5 7 9 = 9 * 2 ^ 128 + 7 * 2 ^ 64 + 5 := by decide

/-! ## System calls (arc-node: revm's `run_system_call`)

Arc's system calls — the EIP-2935 history write (executor.rs:377-378, alloy-evm
`transact_blockhashes_contract_call`) and `ProtocolConfig.feeParams()` (executor.rs:229,
protocol_config.rs:108-114) — go through `ArcEvm::transact_system_call` (evm.rs:1557-1597):
before Zero7 revm's `system_call_with_caller` (evm.rs:1572-1574), from Zero7
`ArcEvmHandler::run_system_call` after loading NativeCoinControl (evm.rs:1576-1589). Both
are revm-handler 18.1.0 `run_system_call` (handler.rs:123-141): `execution` only — no
validation, no `pre_execution` (so no warm-up of the caller, the coinbase or an access
list), no `post_execution` (no refund, no reward). The first frame loads the target and its
EIP-7702 delegate (execution.rs:20-35), which warms them; the value-0 transfer touches only
the target (revm-context 16.0.1 journal/inner.rs:447-449, the caller is never loaded). The
precompile addresses a tx's `pre_execution` warmed stay warm in the block's journal
(inner.rs:160 clears only the coinbase and the access list), so a post-block call after a
block with transactions sees them warm; the pre-block call runs on a fresh EVM and does not.
GASPRICE is 0 (`TxEnv::new_system_tx_with_caller`, system_call.rs:56-68: no gas price). The
EIP-2935 result is committed (alloy-evm `apply_blockhashes_contract_call`, `db.commit`)
through revm's state: selfdestructed accounts destroyed, touched empty accounts cleared
(EIP-161) — the end of tx (`Tx.endTx`). `feeParams()` is never committed
(protocol_config.rs:99-133 reads the output only); it is a view call and writes nothing, so
the replay, which keeps its world, agrees.

This differs from EELS (`Evm.Frontier.Vm.System.eels`: nothing warm, GASPRICE the base fee,
nothing destroyed or swept) in the warm target, NativeCoinControl, the post-block
precompiles, GASPRICE and the end. None of it moves state on the contracts Arc calls (the
history contract and ProtocolConfig read and write their own storage only); the gas a system
call uses is charged to no one. -/

/-- The addresses an Arc system call starts warm with: the target, NativeCoinControl from
    Zero7, the fork's precompiles after a block's transactions. -/
def systemSeed (k : Nat) (target : Evm.Address) (zero7 precompilesWarm : Bool) : List Evm.Address :=
  [target] ++ (if zero7 then [Evm.Arc.Spec.NativeCoin.nativeCoinControlAddress] else []) ++
    (if precompilesWarm then Evm.Frontier.Vm.Tx.precompileAddrs k else [])

/-- Arc's system-call rule. -/
def systemRule (k : Nat) (target : Evm.Address) (zero7 precompilesWarm : Bool) :
    Evm.Frontier.Vm.System.Rule :=
  { seed := systemSeed k target zero7 precompilesWarm, gasPrice := 0 }

/-- Arc's world after a system call: the message's, then revm's commit (the accounts_to_delete
    and the EIP-161 sweep). -/
def systemEnd (k : Nat) (o : Evm.Frontier.Vm.Tx.Out) : Evm.Frontier.State :=
  Evm.Frontier.Vm.Tx.endTx k o.env.state o.env.selfDestructSet o.env.touched

end Evm.Arc.Spec.BlockSystem
