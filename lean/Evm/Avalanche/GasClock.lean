/-
  Evm.Avalanche.GasClock — ACP-194 Streaming Asynchronous Execution (SAE) gas clock.

  Source: avalanchego d38de7e0
    vms/saevm/gastime/gastime.go    Time, BeforeBlock, AfterBlock, BaseFee, TargetToRate
    vms/saevm/cchain/hooks.go       GasConfigAfter, SettledGasTime, TargetToExcessScaling
    vms/components/gas/gas.go       CalculatePrice (EIP-4844 fake_exponential, u64-saturating)
    vms/components/gas/dynamic.go   TargetExponent, PriceExponent

  The clock tracks time in charged gas at `rate = 2 * target` gas/second and maintains a
  gas `excess`. The base fee is `max minPrice (fakeExp(1, excess, 87 * target))`.
-/

import Evm.Cancun.Spec.BlobTx

namespace Evm.Avalanche.GasClock

def maxU64                : Nat := 18446744073709551615   -- 2^64 - 1
def targetToRate          : Nat := 2
def targetToExcessScaling : Nat := 87
def minTarget             : Nat := 1000000
def targetConversion      : Nat := 33554432               -- 2^25
def minPriceConversion    : Nat := 415828534307635077     -- MaxUint64 / ln(MaxUint64)
def nanosecondsPerSec     : Nat := 1000000000

/-- Saturate a `Nat` to `u64::MAX`. -/
def satU64 (x : Nat) : Nat := min x maxU64

/-- Saturating EIP-4844 `fake_exponential`, matching avalanchego `gas.CalculatePrice`:
    returns 0 when `denom = 0`, else `min maxU64 (fakeExponential factor numer denom)`. -/
def satFakeExp (factor numer denom : Nat) : Nat :=
  if denom = 0 then 0 else satU64 (Evm.Cancun.Spec.fakeExponential factor numer denom)

/-- Target gas per second derived from a header's `targetExponent` (`GasConfigAfter`),
    clamped to `[1, maxU64 / 2]`. -/
def targetOfExponent (targetExp : Nat) : Nat :=
  let raw := satFakeExp minTarget targetExp targetConversion
  max 1 (min raw (maxU64 / targetToRate))

/-- Minimum gas price derived from a header's `minPriceExponent` (`GasConfigAfter`). -/
def minPriceOfExponent (minPriceExp : Nat) : Nat :=
  satFakeExp 1 minPriceExp minPriceConversion

/-- Gas clock parameters after a block (`GasConfigAfter`). -/
structure Params where
  target   : Nat
  minPrice : Nat
  deriving Repr, DecidableEq, Inhabited

namespace Params

def ofExponents (targetExp minPriceExp : Nat) : Params :=
  ⟨targetOfExponent targetExp, minPriceOfExponent minPriceExp⟩

/-- Clock rate in gas per second (`2 * target`). -/
def rate (p : Params) : Nat := p.target * targetToRate

/-- Excess scaling denominator `K = 87 * target`, saturating at `u64::MAX`. -/
def scaling (p : Params) : Nat := satU64 (p.target * targetToExcessScaling)

/-- Exponential price at `excess`: `fakeExp(1, excess, K)`. -/
def priceAt (p : Params) (excess : Nat) : Nat :=
  satFakeExp 1 excess p.scaling

end Params

/-- SAE gas clock state (`gastime.Time`). -/
structure Clock where
  seconds  : Nat
  fraction : Nat
  excess   : Nat
  params   : Params
  deriving Repr, DecidableEq, Inhabited

/-- Base fee of a block starting at clock state `c` (`Time.BaseFee`). -/
def baseFee (c : Clock) : Nat :=
  max (c.params.priceAt c.excess) c.params.minPrice

/-- Ceiling division `ceil(a / b)` (0 when `b = 0`). -/
def divCeil (a b : Nat) : Nat :=
  if b = 0 then 0 else (a + b - 1) / b

/-- Whether `(toSec, toFrac)` is strictly ahead of `(curSec, curFrac)`. -/
private def isAhead (toSec toFrac curSec curFrac : Nat) : Bool :=
  if toSec = curSec then toFrac > curFrac else toSec > curSec

/-- Decay excess across `(skippedSec, skippedFrac)` at target `t` and rate `r`. -/
private def decayExcess (excess skippedSec skippedFrac t r : Nat) : Nat :=
  (excess - skippedSec * t) - (skippedFrac * t) / r

private theorem decayExcess_le (excess skippedSec skippedFrac t r : Nat) :
    decayExcess excess skippedSec skippedFrac t r ≤ excess :=
  Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)

/-- Advance the clock to consensus wall time `(blockSec, blockNs)` if the clock is behind it,
    decaying `excess` by unused target gas (`Time.BeforeBlock`, prior to minimum-excess floor). -/
def beforeBlockRaw (c : Clock) (blockSec blockNs : Nat) : Clock :=
  let r := c.params.rate
  let t := c.params.target
  if r = 0 then c
  else
    let intoSec := divCeil (blockNs * r) nanosecondsPerSec
    let toSec := satU64 (blockSec + intoSec / r)
    let toFrac := intoSec % r
    if !isAhead toSec toFrac c.seconds c.fraction then c
    else
      let rawSkippedSec := toSec - c.seconds
      let skipped :=
        if c.fraction > toFrac then
          (rawSkippedSec - 1, r - (c.fraction - toFrac))
        else
          (rawSkippedSec, toFrac - c.fraction)
      { c with seconds := toSec, fraction := toFrac,
               excess := decayExcess c.excess skipped.1 skipped.2 t r }

/-- Advance the clock by `charged` gas and switch to `nextParams` (`Time.AfterBlock`). -/
def afterBlock (c : Clock) (charged : Nat) (nextParams : Params) : Clock :=
  let r := c.params.rate
  let t := c.params.target
  if r = 0 then { c with params := nextParams }
  else
    let frac1 := c.fraction + charged
    let sec1 := c.seconds + frac1 / r
    let rem1 := frac1 % r
    let exc1 := satU64 (c.excess + (charged * (r - t)) / r)
    let oldK := c.params.scaling
    let newK := nextParams.scaling
    let exc2 := if oldK = 0 then exc1 else satU64 (divCeil (exc1 * newK) oldK)
    let nr := nextParams.rate
    let frac2 := divCeil (rem1 * nr) r
    let (sec2, rem2) := if nr > 0 && frac2 ≥ nr then (sec1 + 1, frac2 - nr) else (sec1, frac2)
    { seconds := sec2, fraction := rem2, excess := exc2, params := nextParams }

theorem targetOfExponent_pos (e : Nat) : targetOfExponent e ≥ 1 := by
  unfold targetOfExponent
  exact Nat.le_max_left _ _

theorem rate_ge_two (te me : Nat) : (Params.ofExponents te me).rate ≥ 2 := by
  simp only [Params.rate, Params.ofExponents, targetToRate]
  have h := targetOfExponent_pos te
  omega

theorem baseFee_ge_minPrice (c : Clock) : baseFee c ≥ c.params.minPrice := by
  unfold baseFee; exact Nat.le_max_right _ _

theorem beforeBlockRaw_excess_le (c : Clock) (sec ns : Nat) :
    (beforeBlockRaw c sec ns).excess ≤ c.excess := by
  unfold beforeBlockRaw
  dsimp only
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · exact decayExcess_le _ _ _ _ _

end Evm.Avalanche.GasClock
