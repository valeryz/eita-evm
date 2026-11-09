import Evm.CL.GasEmit
import Evm.Osaka.Spec.BlobSchedule
import Evm.Osaka.Spec.GasCap

/-! # Evm.CL.GasEmitCancun — the emitted blob fee market is the fork-typed spec's

`Evm.CL.GasEmit.blobBaseFee` is what the host computes once per block (the emitted
`spec-blob-base-fee`): it prices every type-3 tx's blob fee and is the value every frame's
BLOBBASEFEE pushes (EvmState #568). `nextExcessBlobGas` (a clause of `spec-header-violation`,
`Evm.CL.HeaderEmit`) and `maxBlobGasPerBlock` (`spec-max-blob-gas-per-block`) are header gates. The spec side is
`Evm.Osaka.Spec.BlobSchedule`: one schedule (`blobParamsAt` — Cancun, Prague/Osaka, BPO1,
BPO2) and EELS `calculate_blob_gas_price` / `calculate_excess_blob_gas` (with EIP-7918's
reserve-price clause from Osaka) over it. This file proves the emitted terms the same
functions of the fork and the parent fields, so the executable can neither price one
schedule's blobs on another's curve (which the hand-written Cancun-only formula did until
2026-10-25) nor skip EIP-7918. Same pattern as `GasEmitParis` / `GasEmitShanghai`. -/

namespace Evm.CL.GasEmitCancun

open Evm.CL.GasEmit
open Evm.Osaka.Spec (blobParamsAt blobParamsCancun blobParamsPrague blobParamsBpo1 blobParamsBpo2)

/-- Every `bySchedule` selector reads the fork's schedule entry. -/
private theorem bySchedule_eq (ρ : Env) (f : Evm.Fork) (hf : ρ "fork-ord" = f.ord)
    (c p b1 b2 : Nat) (g : Evm.Osaka.Spec.BlobParams → Nat)
    (hc : g blobParamsCancun = c) (hp : g blobParamsPrague = p)
    (h1 : g blobParamsBpo1 = b1) (h2 : g blobParamsBpo2 = b2) :
    (bySchedule c p b1 b2).eval ρ = g (blobParamsAt f) := by
  simp only [bySchedule, fork, Expr.eval, hf, blobParamsAt, Evm.Fork.atLeast]
  cases f <;> simp [Evm.Fork.ord, hc, hp, h1, h2]

/-- **The emitted blob base fee is the spec's** for every fork `f` (as the host's `fork-ord`)
    and excess: `calculateBlobGasPriceAt f excess` (EELS `calculate_blob_gas_price` with the
    fork's `BLOB_BASE_FEE_UPDATE_FRACTION`). -/
theorem blobBaseFee_eq_spec (ρ : Env) (f : Evm.Fork) (e : Nat)
    (hf : ρ "fork-ord" = f.ord) (he : ρ "excess-blob-gas" = e) :
    blobBaseFee.eval ρ = Evm.Osaka.Spec.calculateBlobGasPriceAt f e := by
  simp only [blobBaseFee, blobBaseFeeUpdateFraction, Expr.eval, he,
             Evm.Osaka.Spec.calculateBlobGasPriceAt, Evm.Cancun.Spec.minBaseFeePerBlobGas]
  rw [bySchedule_eq ρ f hf 3338477 5007716 8346193 11684671 (·.fraction) rfl rfl rfl rfl]

/-- Below BPO1 the fee is Prague's statement of it (`Evm.Prague.Spec.calculateBlobGasPriceAt`). -/
theorem blobBaseFee_eq_prague (ρ : Env) (f : Evm.Fork) (e : Nat) (h : ¬ f.atLeast .bpo1)
    (hf : ρ "fork-ord" = f.ord) (he : ρ "excess-blob-gas" = e) :
    blobBaseFee.eval ρ = Evm.Prague.Spec.calculateBlobGasPriceAt f e := by
  rw [blobBaseFee_eq_spec ρ f e hf he, Evm.Osaka.Spec.calculateBlobGasPriceAt_eq_prague f h]

/-- Corollary at Cancun: the emitted fee is the Cancun spec's `calculateBlobGasPrice`. -/
theorem blobBaseFee_cancun (ρ : Env) (e : Nat)
    (hf : ρ "fork-ord" = 16) (he : ρ "excess-blob-gas" = e) :
    blobBaseFee.eval ρ = Evm.Cancun.Spec.calculateBlobGasPrice e := by
  rw [blobBaseFee_eq_prague ρ .cancun e (by decide) hf he,
      Evm.Prague.Spec.calculateBlobGasPriceAt_cancun]

/-- The four curves differ (each later one is slower), so the schedule selection is
    load-bearing: one BPO2 fraction of excess prices at 33 / 10 / 4 / 2 on the Cancun /
    Prague-Osaka / BPO1 / BPO2 curves. -/
theorem fraction_change_is_observable :
    Evm.Osaka.Spec.calculateBlobGasPriceAt .cancun 11684671 = 33 ∧
    Evm.Osaka.Spec.calculateBlobGasPriceAt .prague 11684671 = 10 ∧
    Evm.Osaka.Spec.calculateBlobGasPriceAt .osaka  11684671 = 10 ∧
    Evm.Osaka.Spec.calculateBlobGasPriceAt .bpo1   11684671 = 4 ∧
    Evm.Osaka.Spec.calculateBlobGasPriceAt .bpo2   11684671 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

set_option backward.isDefEq.respectTransparency false in
/-- **The emitted excess-blob-gas update is the fork-typed spec's** (EELS
    `calculate_excess_blob_gas` with the fork's schedule entry and, from Osaka, EIP-7918's
    reserve-price clause): for every fork and parent header. -/
theorem nextExcessBlobGas_eq_spec (ρ : Env) (f : Evm.Fork) (pe pu pb : Nat)
    (hf : ρ "fork-ord" = f.ord) (he : ρ "parent-excess-blob-gas" = pe)
    (hu : ρ "parent-blob-gas-used" = pu) (hb : ρ "parent-base-fee" = pb) :
    nextExcessBlobGas.eval ρ = Evm.Osaka.Spec.calculateExcessBlobGasAt f pe pu pb := by
  have ht := bySchedule_eq ρ f hf 393216 786432 1310720 1835008
    (fun p => p.target * Evm.Cancun.Spec.gasPerBlob) rfl rfl rfl rfl
  have hm := bySchedule_eq ρ f hf 6 9 15 21 (·.max) rfl rfl rfl rfl
  have hd := bySchedule_eq ρ f hf 3 3 5 7 (fun p => p.max - p.target) rfl rfl rfl rfl
  have hr := bySchedule_eq ρ f hf 3338477 5007716 8346193 11684671 (·.fraction) rfl rfl rfl rfl
  simp only [nextExcessBlobGas, parentBlobGas, parentExcessBlobGas, parentBlobGasUsed,
             parentBaseFee, blobTargetGasPerBlock, blobScheduleMax, blobScheduleDelta,
             blobBaseFeeUpdateFraction, fork, Expr.eval, he, hu, hb, hf] at *
  rw [ht, hm, hd, hr]
  simp only [Evm.Osaka.Spec.calculateExcessBlobGasAt, Evm.Osaka.Spec.calculateBlobGasPriceAt,
             Evm.Osaka.Spec.blobBaseCost, Evm.Cancun.Spec.gasPerBlob,
             Evm.Cancun.Spec.minBaseFeePerBlobGas, Evm.Fork.atLeast]
  cases f <;> simp [Evm.Fork.ord]

/-- Before Osaka the update is Prague's (`Evm.Prague.Spec.calculateExcessBlobGasAt`): no
    reserve-price clause, the parent base fee is not read. -/
theorem nextExcessBlobGas_eq_prague (ρ : Env) (f : Evm.Fork) (pe pu pb : Nat)
    (h : ¬ f.atLeast .osaka)
    (hf : ρ "fork-ord" = f.ord) (he : ρ "parent-excess-blob-gas" = pe)
    (hu : ρ "parent-blob-gas-used" = pu) (hb : ρ "parent-base-fee" = pb) :
    nextExcessBlobGas.eval ρ = Evm.Prague.Spec.calculateExcessBlobGasAt f pe pu := by
  rw [nextExcessBlobGas_eq_spec ρ f pe pu pb hf he hu hb,
      Evm.Osaka.Spec.calculateExcessBlobGasAt_eq_prague f h]

/-- **The emitted blob-gas cap is the spec's** `MAX_BLOB_GAS_PER_BLOCK` for every fork. -/
theorem maxBlobGasPerBlock_eq_spec (ρ : Env) (f : Evm.Fork) (hf : ρ "fork-ord" = f.ord) :
    maxBlobGasPerBlock.eval ρ = Evm.Osaka.Spec.maxBlobGasPerBlockAt f := by
  simp only [maxBlobGasPerBlock, Evm.Osaka.Spec.maxBlobGasPerBlockAt]
  rw [bySchedule_eq ρ f hf 786432 1179648 1966080 2752512
        (fun p => p.max * Evm.Cancun.Spec.gasPerBlob) rfl rfl rfl rfl]

/-- EIP-7825: the emitted cap is `Evm.Osaka.Spec.txMaxGasLimit`. -/
theorem txMaxGasLimit_eq_spec (ρ : Env) : txMaxGasLimit.eval ρ = Evm.Osaka.Spec.txMaxGasLimit := by
  rfl

/-- The reserve-price clause is observable: the same parent (at target, excess 0) yields
    excess 0 at Prague and 262144 at Osaka under a 1-gwei base fee. -/
theorem eip7918_is_observable :
    Evm.Osaka.Spec.calculateExcessBlobGasAt .prague 0 786432 1000000000 = 0 ∧
    Evm.Osaka.Spec.calculateExcessBlobGasAt .osaka  0 786432 1000000000 = 262144 := by
  constructor <;> native_decide

end Evm.CL.GasEmitCancun
