/-
  Evm.Osaka.Spec.BlobSchedule — the blob fee market from Osaka on: EIP-7918 (blob base fee
  bounded by execution cost) and the EIP-7892 blob-parameter-only schedule (BPO1, BPO2).

  EELS references (execution-specs `src/ethereum/forks/`):

  * `osaka/vm/gas.py` `GasCosts` (lines 95-101):
        PER_BLOB                      = U64(2**17)
        BLOB_SCHEDULE_TARGET          = U64(6)
        BLOB_TARGET_GAS_PER_BLOCK     = PER_BLOB * BLOB_SCHEDULE_TARGET
        BLOB_BASE_COST                = Uint(2**13)
        BLOB_SCHEDULE_MAX             = U64(9)
        BLOB_MIN_GASPRICE             = Uint(1)
        BLOB_BASE_FEE_UPDATE_FRACTION = Uint(5007716)
    Osaka keeps Prague's (EIP-7691) target / max / fraction.
  * `bpo1/vm/gas.py` lines 96-101: TARGET 10, MAX 15, FRACTION 8346193.
    `bpo2/vm/gas.py` lines 96-101: TARGET 14, MAX 21, FRACTION 11684671.
    These are the only differences between `osaka`, `bpo1` and `bpo2` (`diff` of the gas
    modules; `fork.py` is identical). geth's `params/chainspecs/mainnet.json` `blobSchedule`
    carries the same four entries (cancun 3/6/3338477, prague 6/9/5007716, bpo1 10/15/8346193,
    bpo2 14/21/11684671; no `osaka` entry: it inherits prague).
  * `osaka/vm/gas.py` `calculate_excess_blob_gas` (lines 398-441), EIP-7918:

        parent_blob_gas = excess_blob_gas + blob_gas_used
        if parent_blob_gas < GasCosts.BLOB_TARGET_GAS_PER_BLOCK:
            return U64(0)

        target_blob_gas_price = Uint(GasCosts.PER_BLOB)
        target_blob_gas_price *= calculate_blob_gas_price(excess_blob_gas)

        base_blob_tx_price = GasCosts.BLOB_BASE_COST * base_fee_per_gas
        if base_blob_tx_price > target_blob_gas_price:
            blob_schedule_delta = (
                GasCosts.BLOB_SCHEDULE_MAX - GasCosts.BLOB_SCHEDULE_TARGET
            )
            return (
                excess_blob_gas
                + blob_gas_used * blob_schedule_delta // GasCosts.BLOB_SCHEDULE_MAX
            )

        return parent_blob_gas - GasCosts.BLOB_TARGET_GAS_PER_BLOCK

    where `excess_blob_gas`, `blob_gas_used`, `base_fee_per_gas` are the PARENT header's
    (lines 418-424) and `calculate_blob_gas_price` is the validating block's fork's
    (its `BLOB_BASE_FEE_UPDATE_FRACTION`). Prague's function (`prague/vm/gas.py` 392-425)
    is the same without the reserve-price branch.
  * `osaka/fork.py` line 103: `MAX_BLOB_GAS_PER_BLOCK = BLOB_SCHEDULE_MAX * PER_BLOB`;
    `check_transaction` line 469-476 rejects a tx whose blob gas exceeds what is left of
    it, so a valid block has `blob_gas_used ≤ MAX_BLOB_GAS_PER_BLOCK`.

  One owner: `blobParamsAt` is THE schedule. `Evm.Prague.Spec.BlobSchedule`'s fork-typed
  functions remain Prague's own statement of the market and are proved to agree with this
  file below BPO1 (`blobParamsAt_fraction_eq_prague` etc.); the emitted host formulas
  (`Evm.CL.GasEmit.blobBaseFee`, `nextExcessBlobGas`, `maxBlobGasPerBlock`) are proved
  equal to THIS file's functions for every fork in `Evm.CL.GasEmitCancun`.
-/

import Evm.Prague.Spec.BlobSchedule

namespace Evm.Osaka.Spec

open Evm.Cancun.Spec (gasPerBlob fakeExponential minBaseFeePerBlobGas)

/-- One blob-schedule entry: EELS `BLOB_SCHEDULE_TARGET`, `BLOB_SCHEDULE_MAX` (blobs) and
    `BLOB_BASE_FEE_UPDATE_FRACTION`; geth's `blobSchedule.{target,max,baseFeeUpdateFraction}`. -/
structure BlobParams where
  target   : Nat
  max      : Nat
  fraction : Nat
  deriving Repr, DecidableEq

/-- `cancun/vm/gas.py`: 3 / 6 / 3338477. -/
def blobParamsCancun : BlobParams := ⟨3, 6, 3338477⟩
/-- `prague/vm/gas.py` (EIP-7691): 6 / 9 / 5007716. Osaka keeps it (`osaka/vm/gas.py`). -/
def blobParamsPrague : BlobParams := ⟨6, 9, 5007716⟩
/-- `bpo1/vm/gas.py`: 10 / 15 / 8346193. -/
def blobParamsBpo1 : BlobParams := ⟨10, 15, 8346193⟩
/-- `bpo2/vm/gas.py`: 14 / 21 / 11684671. -/
def blobParamsBpo2 : BlobParams := ⟨14, 21, 11684671⟩

/-- The blob schedule in force at fork `f` (EIP-7892: later entries supersede). -/
def blobParamsAt (f : Evm.Fork) : BlobParams :=
  if f.atLeast .bpo2 then blobParamsBpo2
  else if f.atLeast .bpo1 then blobParamsBpo1
  else if f.atLeast .prague then blobParamsPrague
  else blobParamsCancun

/-- `BLOB_BASE_COST = 2^13` (EIP-7918, `osaka/vm/gas.py` line 98). -/
def blobBaseCost : Nat := 2 ^ 13

/-- `BLOB_TARGET_GAS_PER_BLOCK = PER_BLOB · BLOB_SCHEDULE_TARGET` at fork `f`. -/
def targetBlobGasPerBlockAt (f : Evm.Fork) : Nat := (blobParamsAt f).target * gasPerBlob

/-- `MAX_BLOB_GAS_PER_BLOCK = BLOB_SCHEDULE_MAX · PER_BLOB` at fork `f` (`osaka/fork.py` 103). -/
def maxBlobGasPerBlockAt (f : Evm.Fork) : Nat := (blobParamsAt f).max * gasPerBlob

/-- `calculate_blob_gas_price` at fork `f`: `taylor_exponential(BLOB_MIN_GASPRICE, excess,
    fraction(f))` (`osaka/vm/gas.py` 462-481). -/
def calculateBlobGasPriceAt (f : Evm.Fork) (excessBlobGas : Nat) : Nat :=
  fakeExponential minBaseFeePerBlobGas excessBlobGas (blobParamsAt f).fraction

/-- `calculate_excess_blob_gas` at fork `f` from the parent header's `excess_blob_gas`,
    `blob_gas_used` and `base_fee_per_gas` (0/0/0 for a parent without the fields, lines
    416-418): the EIP-7918 clause quoted in the module note from Osaka on, Prague's
    `max(0, parent_excess + parent_used − target)` before. -/
def calculateExcessBlobGasAt (f : Evm.Fork) (parentExcess parentUsed parentBaseFee : Nat) : Nat :=
  let p := blobParamsAt f
  let target := p.target * gasPerBlob
  let sum := parentExcess + parentUsed
  if sum < target then 0
  else if f.atLeast .osaka ∧
          gasPerBlob * calculateBlobGasPriceAt f parentExcess < blobBaseCost * parentBaseFee then
    parentExcess + parentUsed * (p.max - p.target) / p.max
  else sum - target

/-! ## Agreement with the Prague-level statement below BPO1 / Osaka -/

theorem blobParamsAt_fraction_eq_prague (f : Evm.Fork) (h : ¬ f.atLeast .bpo1) :
    (blobParamsAt f).fraction = Evm.Prague.Spec.blobBaseFeeUpdateFractionAt f := by
  cases f <;> simp_all [blobParamsAt, Evm.Fork.atLeast, Evm.Fork.ord,
    Evm.Prague.Spec.blobBaseFeeUpdateFractionAt, blobParamsCancun, blobParamsPrague,
    Evm.Prague.Spec.blobBaseFeeUpdateFraction, Evm.Cancun.Spec.blobBaseFeeUpdateFraction]

theorem targetBlobGasPerBlockAt_eq_prague (f : Evm.Fork) (h : ¬ f.atLeast .bpo1) :
    targetBlobGasPerBlockAt f = Evm.Prague.Spec.targetBlobGasPerBlockAt f := by
  cases f <;> simp_all [targetBlobGasPerBlockAt, blobParamsAt, Evm.Fork.atLeast, Evm.Fork.ord,
    Evm.Prague.Spec.targetBlobGasPerBlockAt, blobParamsCancun, blobParamsPrague,
    Evm.Prague.Spec.targetBlobGasPerBlock, Evm.Cancun.Spec.targetBlobGasPerBlock,
    Evm.Cancun.Spec.gasPerBlob]

theorem calculateBlobGasPriceAt_eq_prague (f : Evm.Fork) (h : ¬ f.atLeast .bpo1) (e : Nat) :
    calculateBlobGasPriceAt f e = Evm.Prague.Spec.calculateBlobGasPriceAt f e := by
  simp [calculateBlobGasPriceAt, Evm.Prague.Spec.calculateBlobGasPriceAt,
        blobParamsAt_fraction_eq_prague f h]

/-- Before Osaka there is no reserve-price clause: the update is Prague's. -/
theorem calculateExcessBlobGasAt_eq_prague (f : Evm.Fork) (h : ¬ f.atLeast .osaka)
    (pe pu pb : Nat) :
    calculateExcessBlobGasAt f pe pu pb = Evm.Prague.Spec.calculateExcessBlobGasAt f pe pu := by
  have h1 : ¬ f.atLeast .bpo1 := by
    cases f <;> simp_all [Evm.Fork.atLeast, Evm.Fork.ord]
  have hb : f.atLeast .osaka = false := by simpa using h
  have ht := targetBlobGasPerBlockAt_eq_prague f h1
  simp only [calculateExcessBlobGasAt, Evm.Prague.Spec.calculateExcessBlobGasAt, hb,
             Bool.false_eq_true, false_and, if_false]
  -- the schedule's target is Prague's below BPO1 (no numerals are compared here: the
  -- `targetBlobGasPerBlockAt` fold is definitional)
  rw [show (blobParamsAt f).target * gasPerBlob = targetBlobGasPerBlockAt f from rfl, ht]

/-! ## Vectors (EELS numbers, `native_decide`) -/

-- the four entries are distinct and observable in the price: one BPO2 fraction of excess
-- prices at ⌊e^(11684671/3338477)⌋ = 33 on Cancun's curve, ⌊e^(11684671/5007716)⌋ = 10 on
-- Prague's/Osaka's, ⌊e^(11684671/8346193)⌋ = 4 on BPO1's, ⌊e^1⌋ = 2 on BPO2's.
example : calculateBlobGasPriceAt .cancun 11684671 = 33 := by native_decide
example : calculateBlobGasPriceAt .osaka  11684671 = 10 := by native_decide
example : calculateBlobGasPriceAt .bpo1   11684671 = 4  := by native_decide
example : calculateBlobGasPriceAt .bpo2   11684671 = 2  := by native_decide

-- EIP-7918 at Osaka: a parent at the 6-blob target with excess 0 (blob price 1 wei) and a
-- base fee of 1 gwei: 8192·1e9 > 131072·1, so the excess GROWS by used·3/9 = 262144
-- instead of staying at 0; at a base fee of 16 wei (8192·16 = 131072, not >) it stays 0.
example : calculateExcessBlobGasAt .osaka 0 786432 1000000000 = 262144 := by native_decide
example : calculateExcessBlobGasAt .osaka 0 786432 16 = 0 := by native_decide
example : calculateExcessBlobGasAt .prague 0 786432 1000000000 = 0 := by native_decide
-- below target the reserve clause never fires (the target check comes first)
example : calculateExcessBlobGasAt .bpo2 100 0 1000000000 = 0 := by native_decide
-- BPO2: 21 blobs on an empty excess at a tiny base fee: 21·131072 − 14·131072 = 917504;
-- at 1 gwei the reserve clause: 0 + 2752512·7/21 = 917504 too (max − target = max/3).
example : calculateExcessBlobGasAt .bpo2 0 2752512 1 = 917504 := by native_decide
example : calculateExcessBlobGasAt .bpo2 0 2752512 1000000000 = 917504 := by native_decide
example : maxBlobGasPerBlockAt .cancun = 786432 := by native_decide
example : maxBlobGasPerBlockAt .prague = 1179648 := by native_decide
example : maxBlobGasPerBlockAt .osaka  = 1179648 := by native_decide
example : maxBlobGasPerBlockAt .bpo1   = 1966080 := by native_decide
example : maxBlobGasPerBlockAt .bpo2   = 2752512 := by native_decide

end Evm.Osaka.Spec
