/-
  Evm.Optimism.Replay.Emit — the OP-Stack rules the Lisp replay runs, as emitted formulas
  (`Evm.CL.GasEmit.Expr`, `src/generated/host.lisp` via EmitHostCL), each proved equal to
  its spec function here:

    spec-op-base-fork-ord (ts)          = (OpFork.baseMainnetAt ts).ord
    spec-op-eth-analog-ord (op-fork)    = (OpFork.ethereumAnalog f).ord
    spec-op-l1-fee (op-fork zeroes ones flz l1-base-fee overhead scalar blob-base-fee
                    base-fee-scalar blob-base-fee-scalar)
                                        = Replay.l1FeeWei f params tx flz, for a tx with
                                          `zeroes` zero and `ones` non-zero bytes
    spec-op-operator-fee (op-fork gas scalar constant)
                                        = Isthmus/Jovian operator fee (op-geth
                                          `NewOperatorCostFunc`)
    spec-op-da-size-scaled (flz)        = Fjord.estimatedSizeScaled
    spec-op-deposit-fails (op-fork gas-limit intrinsic floor value balance data-len create)
                                        = Bedrock.Spec.depositFails (a failed deposit)

  What stays the Lisp seam: the byte counts and the FastLZ length of the tx's EIP-2718
  encoding (`spec-flz-compress-len`, emitted from `Fjord.Spec.FastLz`), and the L1Block
  predeploy storage reads (`L1Block.lean`: slots 1, 3, 5, 6, 7, 8).
-/

import Evm.CL.GasEmit
import Evm.Optimism.Forks
import Evm.Optimism.Replay.L1Fee
import Evm.Optimism.Isthmus.Spec.PragueInheritance
import Evm.Optimism.Bedrock.Spec.DepositReceipt
import Evm.Optimism.Fjord.Spec.FastLz

namespace Evm.Optimism.Replay.Emit

open Evm.CL.GasEmit (Expr Env mkEnv)
open Evm.Optimism (OpFork)

private def v (x : String) : Expr := .var x
private def n (k : Nat) : Expr := .lit k

/-! ## The fork schedule -/

/-- `if v ≥ k₁ then o₁ else …` (as `Evm.CL.ForkEmit.geChain`). -/
def geChain (x : String) : List (Nat × Nat) → Nat → Expr
  | [], d => .lit d
  | (k, o) :: r, d => .ite (.var x) (.lit k) (geChain x r d) (.lit o)

/-- `OpFork.baseMainnetAt` as an ordinal. -/
def baseForkOrdExpr : Expr :=
  geChain "ts" [(1779991200, 8), (1764691201, 7), (1746806401, 6), (1736445601, 5),
                (1726070401, 4), (1720627201, 3), (1710374401, 2), (1704992401, 1)] 0

set_option backward.isDefEq.respectTransparency false in
theorem baseForkOrdExpr_eq_spec (ρ : Env) :
    baseForkOrdExpr.eval ρ = (OpFork.baseMainnetAt (ρ "ts")).ord := by
  simp only [baseForkOrdExpr, geChain, Expr.eval, OpFork.baseMainnetAt]
  simp only [apply_ite (f := OpFork.ord)]
  simp only [OpFork.ord]
  -- the activations as variables (deciding `ts < 1779991200` by reduction would unfold
  -- the literal: the Nat-literal whnf trap)
  generalize (1779991200 : Nat) = k8 at *
  generalize (1764691201 : Nat) = k7 at *
  generalize (1746806401 : Nat) = k6 at *
  generalize (1736445601 : Nat) = k5 at *
  generalize (1726070401 : Nat) = k4 at *
  generalize (1720627201 : Nat) = k3 at *
  generalize (1710374401 : Nat) = k2 at *
  generalize (1704992401 : Nat) = k1 at *
  simp only [ge_iff_le, ← Nat.not_lt, ite_not]

/-- `OpFork.ethereumAnalog` as an ordinal (`Evm.Fork.ord`), over the OP ordinal. -/
def ethAnalogOrdExpr : Expr :=
  geChain "op-fork" [(8, 18), (6, 17), (2, 16), (1, 15)] 11

theorem ethAnalogOrdExpr_eq_spec (f : OpFork) :
    ethAnalogOrdExpr.eval (mkEnv [("op-fork", f.ord)]) = (OpFork.ethereumAnalog f).ord := by
  cases f <;> decide

/-! ## The L1 data fee -/

/-- `Bedrock.Spec.calldataGas` of a tx with `zeroes` zero and `ones` non-zero bytes. -/
def calldataGasExpr : Expr := .add (.mul (n 4) (v "zeroes")) (.mul (n 16) (v "ones"))

/-- `Ecotone.Spec.l1FeeScaled`. -/
def l1FeeScaledExpr : Expr :=
  .add (.mul (.mul (n 16) (v "l1-base-fee")) (v "base-fee-scalar"))
       (.mul (v "blob-base-fee") (v "blob-base-fee-scalar"))

/-- `Fjord.Spec.estimatedSizeScaled` (the clamp makes the truncated subtraction exact). -/
def daSizeScaledExpr : Expr :=
  .emax (n Evm.Optimism.Fjord.Spec.minTxSizeScaled) (.sub (.mul (n 836500) (v "flz")) (n 42585600))

/-- `Replay.l1FeeWei`: the Ecotone fields set (some of blob base fee, the two scalars
    non-zero) selects Fjord from OP ordinal 3 and Ecotone from 2; else the Bedrock formula. -/
def l1FeeExpr : Expr :=
  let bedrock : Expr := .fdiv (.mul (.mul (.add calldataGasExpr (v "overhead")) (v "l1-base-fee")) (v "scalar"))
                              (n 1000000)
  let ecotone : Expr := .fdiv (.mul calldataGasExpr l1FeeScaledExpr) (n 16000000)
  let fjord : Expr := .fdiv (.mul daSizeScaledExpr l1FeeScaledExpr) (n 1000000000000)
  .ite (n 0) (.add (v "blob-base-fee") (.add (v "base-fee-scalar") (v "blob-base-fee-scalar")))
    (.ite (v "op-fork") (n 2) bedrock (.ite (v "op-fork") (n 3) ecotone fjord))
    bedrock

private theorem clampNat (x : Nat) :
    (if (-42585600 + 836500 * (x : Int)) < 0 then 0 else (-42585600 + 836500 * (x : Int)).toNat)
      = 836500 * x - 42585600 := by
  split <;> omega

/-- `estimatedSizeScaled` in `Nat`: the clamp makes the truncated subtraction exact. -/
theorem estimatedSizeScaled_nat (x : Nat) :
    Evm.Optimism.Fjord.Spec.estimatedSizeScaled x
      = max Evm.Optimism.Fjord.Spec.minTxSizeScaled (836500 * x - 42585600) := by
  unfold Evm.Optimism.Fjord.Spec.estimatedSizeScaled Evm.Optimism.Fjord.Spec.interceptScaled
    Evm.Optimism.Fjord.Spec.fastlzCoefScaled
  simp only
  rw [clampNat]

theorem daSizeScaledExpr_eq_spec (ρ : Env) :
    daSizeScaledExpr.eval ρ = Evm.Optimism.Fjord.Spec.estimatedSizeScaled (ρ "flz") := by
  rw [estimatedSizeScaled_nat]; rfl

/-- The L1 fee from counts and the FastLZ length (the shape the Lisp seam supplies). -/
def l1FeeWeiCounts (f : OpFork) (p : L1FeeParams) (zeroes ones flz : Nat) : Nat :=
  let cg := 4 * zeroes + 16 * ones
  let ecotoneSet := !Evm.Optimism.Ecotone.Spec.firstEcotoneBlock
    p.l1BlobBaseFee p.baseFeeScalar p.blobBaseFeeScalar
  if f.atLeast .fjord && ecotoneSet then
    Evm.Optimism.Fjord.Spec.l1FeeWei flz p.l1BaseFee p.l1BlobBaseFee p.baseFeeScalar p.blobBaseFeeScalar
  else if f.atLeast .ecotone && ecotoneSet then
    Evm.Optimism.Ecotone.Spec.l1FeeWei cg p.l1BaseFee p.l1BlobBaseFee p.baseFeeScalar p.blobBaseFeeScalar
  else
    (cg + p.l1FeeOverhead) * p.l1BaseFee * p.l1FeeScalar / Evm.Optimism.Bedrock.Spec.feeScalarDenominator

/-- The counts the seam takes from the tx's bytes. -/
def zeroCount (b : Evm.Bytes) : Nat := b.toList.countP (· = 0)
def nonZeroCount (b : Evm.Bytes) : Nat := b.toList.countP (· ≠ 0)

private theorem calldataGas_foldl (l : List UInt8) (acc : Nat) :
    l.foldl (fun acc b => acc + (if b = 0 then Evm.Optimism.Bedrock.Spec.l1GasPerZeroByte
                                 else Evm.Optimism.Bedrock.Spec.l1GasPerNonZeroByte)) acc
      = acc + 4 * l.countP (· = 0) + 16 * l.countP (· ≠ 0) := by
  induction l generalizing acc with
  | nil => simp
  | cons b t ih =>
    rw [List.foldl_cons, ih]
    by_cases h : b = 0 <;>
      simp [h, Evm.Optimism.Bedrock.Spec.l1GasPerZeroByte,
        Evm.Optimism.Bedrock.Spec.l1GasPerNonZeroByte] <;> omega

theorem calldataGas_counts (b : Evm.Bytes) :
    Evm.Optimism.Bedrock.Spec.calldataGas b = 4 * zeroCount b + 16 * nonZeroCount b := by
  unfold Evm.Optimism.Bedrock.Spec.calldataGas zeroCount nonZeroCount
  rw [calldataGas_foldl]; omega

/-- **The counts form is the spec**: `l1FeeWei` on the tx's bytes. -/
theorem l1FeeWei_eq_counts (f : OpFork) (p : L1FeeParams) (b : Evm.Bytes) (flz : Nat) :
    l1FeeWei f p b flz = l1FeeWeiCounts f p (zeroCount b) (nonZeroCount b) flz := by
  unfold l1FeeWei l1FeeWeiCounts Evm.Optimism.Bedrock.Spec.l1FeeWei
  simp only [calldataGas_counts]

/-- The environment the emitted formula reads for fork `f`, params `p`, counts and length. -/
def l1Env (f : OpFork) (p : L1FeeParams) (zeroes ones flz : Nat) : Env :=
  mkEnv [("op-fork", f.ord), ("zeroes", zeroes), ("ones", ones), ("flz", flz),
         ("l1-base-fee", p.l1BaseFee), ("overhead", p.l1FeeOverhead), ("scalar", p.l1FeeScalar),
         ("blob-base-fee", p.l1BlobBaseFee), ("base-fee-scalar", p.baseFeeScalar),
         ("blob-base-fee-scalar", p.blobBaseFeeScalar)]

set_option backward.isDefEq.respectTransparency false in
/-- **The emitted `spec-op-l1-fee` is the spec**, for every fork and input. -/
theorem l1FeeExpr_eq_spec (f : OpFork) (p : L1FeeParams) (zeroes ones flz : Nat) :
    l1FeeExpr.eval (l1Env f p zeroes ones flz) = l1FeeWeiCounts f p zeroes ones flz := by
  have hda := daSizeScaledExpr_eq_spec (l1Env f p zeroes ones flz)
  simp only [l1FeeExpr, l1FeeWeiCounts, Expr.eval] at hda ⊢
  rw [hda]
  simp only [l1Env, mkEnv, List.find?, n, v, calldataGasExpr, l1FeeScaledExpr, Expr.eval,
    Evm.Optimism.Ecotone.Spec.firstEcotoneBlock,
    Evm.Optimism.Fjord.Spec.l1FeeWei, Evm.Optimism.Ecotone.Spec.l1FeeWei,
    Evm.Optimism.Ecotone.Spec.l1FeeScaled, Evm.Optimism.Ecotone.Spec.ecotoneDivisor,
    Evm.Optimism.Fjord.Spec.fjordDivisor, Evm.Optimism.Bedrock.Spec.feeScalarDenominator,
    OpFork.atLeast, Option.elim]
  cases f <;> simp [OpFork.ord] <;>
    by_cases h : p.l1BlobBaseFee = 0 <;> by_cases h1 : p.baseFeeScalar = 0 <;>
      by_cases h2 : p.blobBaseFeeScalar = 0 <;> simp [h, h1, h2] <;> omega

/-! ## A Fjord vector, end to end

Base block 17,000,000, the legacy tx `0xc5ad60b2…c7df70` (283 bytes signed): op-geth's FastLZ
length is 242, its receipt's `l1Fee` 14113415242 wei at `l1GasPrice = 2432047535`,
`l1BlobBaseFee = 1`, scalars 2269 / 1055762. The Lean FastLZ, the fee spec and the emitted
formula agree with it. (`tests/op-l1-fee.lisp` checks 72 such txs, Bedrock to Azul, on
the emitted CL.) -/

/-- The tx's signed EIP-2718 bytes (keccak = its hash). -/
def base17000000tx : Array UInt8 := #[
  0xf9, 0x01, 0x18, 0x81, 0xe9, 0x83, 0x8d, 0xdc, 0x79, 0x83, 0x03, 0x73, 0x2d, 0x94, 0x19, 0xce,
  0xea, 0xd7, 0x10, 0x56, 0x07, 0xcd, 0x44, 0x4f, 0x5a, 0xd1, 0x0d, 0xd5, 0x13, 0x56, 0x43, 0x60,
  0x95, 0xa1, 0x87, 0x01, 0x1b, 0xc3, 0x29, 0x2b, 0x80, 0x00, 0xb8, 0xaa, 0x83, 0xbd, 0x37, 0xf9,
  0x00, 0x00, 0x00, 0x03, 0x07, 0x01, 0x1b, 0xc3, 0x29, 0x2b, 0x80, 0x00, 0x03, 0x0e, 0xa6, 0x07,
  0x0c, 0xcc, 0xcc, 0x00, 0x01, 0xfb, 0x21, 0x39, 0x33, 0x15, 0x32, 0xe3, 0xee, 0x59, 0x77, 0x7f,
  0xbb, 0xcb, 0x14, 0xaf, 0x67, 0x4f, 0x3f, 0xd6, 0x71, 0x00, 0x00, 0x00, 0x01, 0x5f, 0x1a, 0x99,
  0x37, 0x82, 0x0d, 0xb5, 0x6e, 0x7a, 0xeb, 0x48, 0xaa, 0xbf, 0x63, 0x7f, 0xdc, 0x6a, 0x21, 0x80,
  0xf0, 0x00, 0x00, 0x00, 0x00, 0x03, 0x01, 0x02, 0x03, 0x00, 0x04, 0x01, 0x01, 0x02, 0x0a, 0x00,
  0x01, 0x01, 0x02, 0x01, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf6, 0xc0, 0xa3, 0x74, 0xa4, 0x83, 0x10, 0x1e, 0x04, 0xef,
  0x5f, 0x7a, 0xc9, 0xbd, 0x15, 0xd9, 0x14, 0x2b, 0xac, 0x95, 0x42, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x82, 0x42, 0x2e, 0xa0, 0x71, 0x2f, 0x2f, 0xf3, 0xfb, 0xcf,
  0x88, 0xb6, 0x68, 0x51, 0x13, 0x4c, 0x40, 0x69, 0x7d, 0x18, 0x03, 0x29, 0xa3, 0x09, 0x88, 0xcc,
  0x02, 0x6b, 0xbf, 0xa5, 0x07, 0x9e, 0x5f, 0x12, 0x44, 0x88, 0xa0, 0x4a, 0x68, 0x8f, 0x12, 0x1f,
  0x3a, 0xf0, 0x4c, 0x71, 0x50, 0x8e, 0x25, 0x2e, 0x32, 0xf0, 0x93, 0x79, 0x88, 0x45, 0x8e, 0xa3,
  0xcd, 0xfc, 0x35, 0x56, 0x96, 0x95, 0xfa, 0xef, 0x90, 0x91, 0x53]

theorem base_17000000_fjord :
    Evm.Optimism.Fjord.Spec.flzCompressLen base17000000tx = 242 ∧
    l1FeeWei .fjord { l1BaseFee := 2432047535, l1BlobBaseFee := 1,
                       baseFeeScalar := 2269, blobBaseFeeScalar := 1055762 }
      ⟨base17000000tx⟩ 242 = 14113415242 := by
  decide +kernel

/-! ## The operator fee (Isthmus; Jovian's fix) -/

/-- op-geth `NewOperatorCostFunc` (rollup_cost.go:215-289): 0 before Isthmus;
    Isthmus `gas * scalar / 1e6 + constant`; Jovian ("operator fee fix")
    `gas * scalar * 100 + constant`. The params come from L1Block slot 8 (scalar: bytes
    [20:24), constant: bytes [24:32)); an all-zero slot charges 0 — what both formulas give. -/
def operatorFeeWei (f : OpFork) (gas scalar constant : Nat) : Nat :=
  if f.atLeast .jovian then gas * scalar * 100 + constant
  else if f.atLeast .isthmus then gas * scalar / 1000000 + constant
  else 0

def operatorFeeExpr : Expr :=
  .ite (v "op-fork") (n 6) (n 0)
    (.ite (v "op-fork") (n 7)
      (.add (.fdiv (.mul (v "gas") (v "scalar")) (n 1000000)) (v "constant"))
      (.add (.mul (.mul (v "gas") (v "scalar")) (n 100)) (v "constant")))

theorem operatorFeeExpr_eq_spec (f : OpFork) (gas scalar constant : Nat) :
    operatorFeeExpr.eval (mkEnv [("op-fork", f.ord), ("gas", gas), ("scalar", scalar),
                                 ("constant", constant)])
      = operatorFeeWei f gas scalar constant := by
  cases f <;> simp [operatorFeeExpr, operatorFeeWei, Expr.eval, mkEnv, List.find?, n, v,
    OpFork.ord, OpFork.atLeast]

/-- The Isthmus formula is `Isthmus.Spec.operatorFeeWei` (PragueInheritance). -/
theorem operatorFeeWei_isthmus (gas scalar constant : Nat) :
    operatorFeeWei .isthmus gas scalar constant
      = Evm.Optimism.Isthmus.Spec.operatorFeeWei ⟨scalar, constant⟩ gas := by
  simp [operatorFeeWei, Evm.Optimism.Isthmus.Spec.operatorFeeWei, OpFork.atLeast, OpFork.ord,
    Nat.mul_comm]

/-! ## A failed deposit -/

/-- `Bedrock.Spec.depositFails` (`create` 0/1): 1 when the deposit fails. -/
def depositFailsExpr : Expr :=
  .ite (v "gas-limit") (v "intrinsic") (n 1) <|
  .ite (v "gas-limit") (v "floor") (n 1) <|
  .ite (v "balance") (v "value") (n 1) <|
  .ite (n 0) (v "create") (.ite (v "op-fork") (n 1) (n 0) (.ite (n 49152) (v "data-len") (n 1) (n 0))) (n 0)

theorem depositFailsExpr_eq_spec (f : OpFork) (gasLimit intrinsic floor value balance dataLen : Nat)
    (create : Bool) :
    depositFailsExpr.eval (mkEnv [("op-fork", f.ord), ("gas-limit", gasLimit), ("intrinsic", intrinsic),
                                  ("floor", floor), ("value", value), ("balance", balance),
                                  ("data-len", dataLen), ("create", if create then 1 else 0)])
      = if Evm.Optimism.Bedrock.Spec.depositFails f gasLimit intrinsic floor value balance dataLen create
        then 1 else 0 := by
  unfold depositFailsExpr Evm.Optimism.Bedrock.Spec.depositFails
  cases create <;> cases f <;>
    simp [Expr.eval, mkEnv, List.find?, n, v, OpFork.ord, OpFork.atLeast] <;>
    by_cases h1 : gasLimit < intrinsic <;> by_cases h2 : gasLimit < floor <;>
      by_cases h3 : balance < value <;> simp [h1, h2, h3]

end Evm.Optimism.Replay.Emit
