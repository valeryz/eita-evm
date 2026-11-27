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

/-! ## Fuel-sufficiency & early-saturation proofs for `fakeExponential`

    `Evm.Cancun.Spec.fakeExponential` runs 1,024 iterations of the EIP-4844 integer
    Taylor loop, whereas the runtime Lisp `spec-fake-exponential` runs to convergence
    (stopping early when `output ≥ cap * denom`). We prove:
      1. `fakeExpLoopCap_eq`: stopping early at `output ≥ cap * denom` preserves
         `min cap (output / denom)` identically.
      2. `satFakeExp_fuel_sufficient`: for every GasClock parameter range
         (`1 ≤ factor ≤ minTarget`, `1 ≤ denom ≤ maxU64`, any `numer : Nat`),
         1,024 iterations always suffice — for `numer ≥ 128 * denom` the sum saturates
         above `maxU64 * denom` by step 65, and for `numer < 128 * denom` the Taylor
         term underflows to `0` by step 628. -/

/-- Explicit fuel-parameterized EIP-4844 Taylor loop (identical to `fakeExponential.loop`). -/
def fakeExpLoop (numer denom : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, output, _, _ => output
  | fuel + 1, output, accum, i =>
    if accum = 0 then output
    else fakeExpLoop numer denom fuel (output + accum) ((accum * numer) / (denom * i)) (i + 1)

/-- Capped variant matching the runtime Lisp `spec-fake-exponential` with `&optional cap`. -/
def fakeExpLoopCap (cap numer denom : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, output, _, _ => output
  | fuel + 1, output, accum, i =>
    if accum = 0 ∨ output ≥ cap * denom then output
    else fakeExpLoopCap cap numer denom fuel (output + accum) ((accum * numer) / (denom * i)) (i + 1)

private theorem fakeExponential_loop_eq (numer denom fuel output accum i : Nat) :
    Evm.Cancun.Spec.fakeExponential.loop numer denom fuel output accum i =
      fakeExpLoop numer denom fuel output accum i := by
  induction fuel generalizing output accum i with
  | zero => rfl
  | succ fuel ih =>
    unfold Evm.Cancun.Spec.fakeExponential.loop fakeExpLoop
    split
    · rfl
    · exact ih _ _ _

theorem fakeExponential_eq_loop (factor numer denom : Nat) :
    Evm.Cancun.Spec.fakeExponential factor numer denom =
      fakeExpLoop numer denom 1024 0 (factor * denom) 1 / denom := by
  unfold Evm.Cancun.Spec.fakeExponential
  rw [fakeExponential_loop_eq]

private theorem fakeExpLoop_mono (numer denom fuel output accum i : Nat) :
    output ≤ fakeExpLoop numer denom fuel output accum i := by
  induction fuel generalizing output accum i with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    unfold fakeExpLoop
    split
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_add_right _ _) (ih _ _ _)

/-- Stopping `fakeExpLoop` early once `output ≥ cap * denom` preserves `min cap (output / denom)`. -/
theorem fakeExpLoopCap_eq (cap numer denom fuel output accum i : Nat) (hd : 0 < denom) :
    min cap (fakeExpLoopCap cap numer denom fuel output accum i / denom) =
    min cap (fakeExpLoop numer denom fuel output accum i / denom) := by
  induction fuel generalizing output accum i with
  | zero => rfl
  | succ fuel ih =>
    unfold fakeExpLoopCap fakeExpLoop
    by_cases ha : accum = 0
    · simp [ha]
    · by_cases hc : output ≥ cap * denom
      · have h1 : cap ≤ output / denom := (Nat.le_div_iff_mul_le hd).2 hc
        have h2 : output ≤ fakeExpLoop numer denom fuel (output + accum) ((accum * numer) / (denom * i)) (i + 1) :=
          Nat.le_trans (Nat.le_add_right _ _) (fakeExpLoop_mono _ _ _ _ _ _)
        have h3 : cap ≤ fakeExpLoop numer denom fuel (output + accum) ((accum * numer) / (denom * i)) (i + 1) / denom :=
          (Nat.le_div_iff_mul_le hd).2 (Nat.le_trans hc h2)
        simp [ha, hc, Nat.min_eq_left h1, Nat.min_eq_left h3]
      · simp [ha, hc]
        exact ih _ _ _

/-- Single step of the Taylor loop as a state transition `(output, accum, i)`. -/
private def fakeExpStep (numer denom : Nat) (st : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let (output, accum, i) := st
  if accum = 0 then (output, 0, i)
  else (output + accum, (accum * numer) / (denom * i), i + 1)

private def fakeExpSteps (numer denom : Nat) : Nat → Nat × Nat × Nat → Nat × Nat × Nat
  | 0, st => st
  | k + 1, st => fakeExpSteps numer denom k (fakeExpStep numer denom st)

private theorem fakeExpLoop_eq_steps (numer denom fuel output accum i : Nat) :
    fakeExpLoop numer denom fuel output accum i =
      (fakeExpSteps numer denom fuel (output, accum, i)).1 := by
  induction fuel generalizing output accum i with
  | zero => rfl
  | succ fuel ih =>
    unfold fakeExpLoop fakeExpSteps fakeExpStep
    by_cases ha : accum = 0
    · subst ha
      have hzero : ∀ k o j, (fakeExpSteps numer denom k (o, 0, j)).1 = o := by
        intro k
        induction k with
        | zero => intro _ _; rfl
        | succ k ihk => intro o j; simp [fakeExpSteps, fakeExpStep, ihk]
      simp [hzero]
    · simp [ha, ih]

private theorem fakeExpSteps_add (numer denom a b : Nat) (st : Nat × Nat × Nat) :
    fakeExpSteps numer denom (a + b) st =
      fakeExpSteps numer denom b (fakeExpSteps numer denom a st) := by
  induction a generalizing st with
  | zero => simp [fakeExpSteps]
  | succ a ih =>
    rw [Nat.succ_add]
    exact ih (fakeExpStep numer denom st)

private theorem fakeExpSteps_zero_accum (numer denom k output i : Nat) :
    fakeExpSteps numer denom k (output, 0, i) = (output, 0, i) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [fakeExpSteps, fakeExpStep] using ih

private theorem fakeExpSteps_output_le (numer denom k : Nat) (st : Nat × Nat × Nat) :
    st.1 ≤ (fakeExpSteps numer denom k st).1 := by
  induction k generalizing st with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    rcases st with ⟨o, a, i⟩
    simp only [fakeExpSteps, fakeExpStep]
    split
    · exact ih (o, 0, i)
    · exact Nat.le_trans (Nat.le_add_right o a) (ih (o + a, a * numer / (denom * i), i + 1))

/-- When `numer ≥ 128 * denom`, `accum` at least doubles at every step for `1 ≤ i ≤ 64`. -/
private theorem fakeExpSteps_double
    (numer denom : Nat) (hd : 0 < denom) (hbig : 128 * denom ≤ numer)
    (k output accum i a0 : Nat)
    (hi1 : 1 ≤ i) (hik : i + k ≤ 65) (ha0 : 0 < a0) (ha : a0 ≤ accum) :
    let st := fakeExpSteps numer denom k (output, accum, i)
    2 ^ k * a0 ≤ st.2.1 ∧ st.2.2 = i + k := by
  induction k generalizing output accum i a0 with
  | zero =>
    simp [fakeExpSteps, ha]
  | succ k ih =>
    have hpos : accum ≠ 0 := by omega
    have hdi_pos : 0 < denom * i := Nat.mul_pos hd (by omega)
    have hmul : (2 * accum) * (denom * i) ≤ accum * numer := by
      have hi64 : 2 * i ≤ 128 := by omega
      calc (2 * accum) * (denom * i)
          = accum * ((2 * i) * denom) := by ac_rfl
        _ ≤ accum * (128 * denom) := Nat.mul_le_mul_left accum (Nat.mul_le_mul_right denom hi64)
        _ ≤ accum * numer := Nat.mul_le_mul_left accum hbig
    have hstep : 2 * a0 ≤ (accum * numer) / (denom * i) :=
      Nat.le_trans (Nat.mul_le_mul_left 2 ha) ((Nat.le_div_iff_mul_le hdi_pos).2 hmul)
    have hrec := ih (output + accum) ((accum * numer) / (denom * i)) (i + 1) (2 * a0)
      (by omega) (by omega) (by omega) hstep
    simp only [fakeExpSteps, fakeExpStep, hpos, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · have hpow : 2 ^ (k + 1) * a0 = 2 ^ k * (2 * a0) := by
        rw [Nat.pow_succ]; ac_rfl
      rw [hpow]; exact hrec.1
    · omega

/-- When `numer < 128 * denom`, each step starting at `i` with `128 ≤ m * i` grows `accum` by at most `m`. -/
private theorem fakeExpSteps_mul_bound
    (numer denom m : Nat) (_hd : 0 < denom) (hsmall : numer < 128 * denom)
    (k output accum i B : Nat) (hi : 1 ≤ i) (hm : 128 ≤ m * i) (hB : accum ≤ B) :
    let st := fakeExpSteps numer denom k (output, accum, i)
    st.2.1 ≤ m ^ k * B ∧ (st.2.1 = 0 ∨ st.2.2 = i + k) := by
  induction k generalizing output accum i B with
  | zero =>
    simp [fakeExpSteps, hB]
  | succ k ih =>
    simp only [fakeExpSteps, fakeExpStep]
    by_cases ha : accum = 0
    · subst ha
      simp only [↓reduceIte, fakeExpSteps_zero_accum]
      exact ⟨Nat.zero_le _, Or.inl trivial⟩
    · simp only [ha, ↓reduceIte]
      have hmul : accum * numer ≤ (denom * i) * (m * accum) := by
        calc accum * numer
            ≤ accum * (128 * denom) := Nat.mul_le_mul_left accum (Nat.le_of_lt hsmall)
          _ ≤ accum * ((m * i) * denom) := Nat.mul_le_mul_left accum (Nat.mul_le_mul_right denom hm)
          _ = (denom * i) * (m * accum) := by ac_rfl
      have hnext : (accum * numer) / (denom * i) ≤ m * B :=
        Nat.le_trans (Nat.div_le_of_le_mul hmul)
          (Nat.mul_le_mul_left m hB)
      have hm' : 128 ≤ m * (i + 1) := Nat.le_trans hm (Nat.mul_le_mul_left m (Nat.le_succ i))
      have hrec := ih (output + accum) ((accum * numer) / (denom * i)) (i + 1) (m * B)
        (by omega) hm' hnext
      refine ⟨?_, ?_⟩
      · have hpow : m ^ (k + 1) * B = m ^ k * (m * B) := by
          rw [Nat.pow_succ]; ac_rfl
        rw [hpow]; exact hrec.1
      · rcases hrec.2 with hz | hj
        · exact Or.inl hz
        · exact Or.inr (by omega)

/-- Once `i ≥ 256` and `numer < 128 * denom`, each step strictly halves `accum` below the next power of 2. -/
private theorem fakeExpSteps_halve_zero
    (numer denom : Nat) (_hd : 0 < denom) (hsmall : numer < 128 * denom)
    (n output accum i : Nat) (hi : 256 ≤ i) (ha : accum < 2 ^ n) :
    (fakeExpSteps numer denom n (output, accum, i)).2.1 = 0 := by
  induction n generalizing output accum i with
  | zero =>
    simp only [Nat.pow_zero] at ha
    have : accum = 0 := by omega
    simp [fakeExpSteps, this]
  | succ n ih =>
    simp only [fakeExpSteps, fakeExpStep]
    by_cases h0 : accum = 0
    · subst h0
      simp only [↓reduceIte, fakeExpSteps_zero_accum]
    · simp only [h0, ↓reduceIte]
      have hlt : accum * numer < (denom * i) * 2 ^ n := by
        have h1 : accum * numer < 2 ^ (n + 1) * (128 * denom) := by
          have ha1 : accum < 2 ^ (n + 1) := ha
          have hn1 : numer < 128 * denom := hsmall
          calc accum * numer
              < accum * (128 * denom) := Nat.mul_lt_mul_of_pos_left hn1 (by omega)
            _ ≤ 2 ^ (n + 1) * (128 * denom) := Nat.mul_le_mul_right _ (Nat.le_of_lt ha1)
        have h2 : 2 ^ (n + 1) * (128 * denom) = (denom * 256) * 2 ^ n := by
          rw [Nat.pow_succ]
          have : 2 * 128 = 256 := rfl
          calc 2 ^ n * 2 * (128 * denom)
              = (denom * (2 * 128)) * 2 ^ n := by ac_rfl
            _ = (denom * 256) * 2 ^ n := by rw [this]
        have h3 : (denom * 256) * 2 ^ n ≤ (denom * i) * 2 ^ n :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left denom hi)
        exact Nat.lt_of_lt_of_le (h2 ▸ h1) h3
      have hnext : (accum * numer) / (denom * i) < 2 ^ n := Nat.div_lt_of_lt_mul hlt
      exact ih (output + accum) ((accum * numer) / (denom * i)) (i + 1) (by omega) hnext

/-- When `128 * denom ≤ numer`, any `fuel ≥ 65` already saturates `satU64 (fakeExpLoop ... / denom)` to `maxU64`. -/
theorem satFakeExp_saturates_of_big
    (factor numer denom fuel : Nat)
    (hf1 : 1 ≤ factor) (hd1 : 1 ≤ denom) (hbig : 128 * denom ≤ numer) (hfuel : 65 ≤ fuel) :
    satU64 (fakeExpLoop numer denom fuel 0 (factor * denom) 1 / denom) = maxU64 := by
  have hd : 0 < denom := by omega
  rw [fakeExpLoop_eq_steps]
  have h64 := fakeExpSteps_double numer denom hd hbig 64 0 (factor * denom) 1 (factor * denom)
    (by omega) (by omega) (Nat.mul_pos (by omega) hd) (Nat.le_refl _)
  have ha64 : 2 ^ 64 * denom ≤ (fakeExpSteps numer denom 64 (0, factor * denom, 1)).2.1 :=
    Nat.le_trans (Nat.mul_le_mul_left (2 ^ 64) (by simpa using Nat.mul_le_mul_right denom hf1)) h64.1
  have ha64_ne : (fakeExpSteps numer denom 64 (0, factor * denom, 1)).2.1 ≠ 0 := by
    have : 0 < 2 ^ 64 * denom := Nat.mul_pos (by decide) hd
    omega
  have h65_out : maxU64 * denom ≤ (fakeExpSteps numer denom 65 (0, factor * denom, 1)).1 := by
    have hsplit : (65 : Nat) = 64 + 1 := rfl
    rw [hsplit, fakeExpSteps_add]
    generalize hst : fakeExpSteps numer denom 64 (0, factor * denom, 1) = st64 at ha64 ha64_ne ⊢
    rcases st64 with ⟨o64, a64, i64⟩
    simp only at ha64 ha64_ne
    simp only [fakeExpSteps, fakeExpStep, ha64_ne, ↓reduceIte]
    have hmax : maxU64 ≤ 2 ^ 64 := by decide
    calc maxU64 * denom
        ≤ 2 ^ 64 * denom := Nat.mul_le_mul_right denom hmax
      _ ≤ a64 := ha64
      _ ≤ o64 + a64 := Nat.le_add_left _ _
  have hsplit : fuel = 65 + (fuel - 65) := by omega
  rw [hsplit, fakeExpSteps_add]
  have hle : maxU64 * denom ≤ (fakeExpSteps numer denom (fuel - 65)
      (fakeExpSteps numer denom 65 (0, factor * denom, 1))).1 :=
    Nat.le_trans h65_out (fakeExpSteps_output_le _ _ _ _)
  have hdiv : maxU64 ≤ (fakeExpSteps numer denom (fuel - 65)
      (fakeExpSteps numer denom 65 (0, factor * denom, 1))).1 / denom :=
    (Nat.le_div_iff_mul_le hd).2 hle
  exact Nat.min_eq_right hdiv

/-- Core fuel-sufficiency theorem: for every GasClock parameter combination
    (`1 ≤ factor ≤ minTarget`, `1 ≤ denom ≤ maxU64`, arbitrary `numer`),
    running `fakeExpLoop` beyond 1,024 iterations never changes the u64-saturated result. -/
theorem satFakeExp_fuel_sufficient
    (factor numer denom extra : Nat)
    (hf1 : 1 ≤ factor) (hf2 : factor ≤ minTarget)
    (hd1 : 1 ≤ denom) (hd2 : denom ≤ maxU64) :
    satU64 (fakeExpLoop numer denom (1024 + extra) 0 (factor * denom) 1 / denom) =
    satU64 (fakeExpLoop numer denom 1024 0 (factor * denom) 1 / denom) := by
  have hd : 0 < denom := by omega
  by_cases hbig : 128 * denom ≤ numer
  · -- Case 1: numer ≥ 128 * denom → saturates past maxU64 * denom by step 65 ≤ 1024
    rw [satFakeExp_saturates_of_big factor numer denom (1024 + extra) hf1 hd1 hbig (by omega),
        satFakeExp_saturates_of_big factor numer denom 1024 hf1 hd1 hbig (by omega)]
  · -- Case 2: numer < 128 * denom → accum reaches 0 by step 628 ≤ 1024
    rw [fakeExpLoop_eq_steps, fakeExpLoop_eq_steps]
    have hsmall : numer < 128 * denom := by omega
    have h0 : factor * denom ≤ 2 ^ 84 - 1 := by
      have hm : minTarget * maxU64 ≤ 2 ^ 84 - 1 := by decide
      exact Nat.le_trans (Nat.mul_le_mul hf2 hd2) hm
    have s1 := fakeExpSteps_mul_bound numer denom 128 hd hsmall 16 0 (factor * denom) 1 (2 ^ 84 - 1)
      (by omega) (by omega) h0
    have h628 : (fakeExpSteps numer denom 628 (0, factor * denom, 1)).2.1 = 0 := by
      have hchain : (628 : Nat) = 16 + (16 + (32 + (64 + (128 + 372)))) := rfl
      rw [hchain, fakeExpSteps_add]
      generalize hst1 : fakeExpSteps numer denom 16 (0, factor * denom, 1) = st1 at s1 ⊢
      rcases st1 with ⟨o1, a1, i1⟩
      simp only at s1
      rcases s1.2 with hz1 | hi1
      · subst hz1; simp [fakeExpSteps_zero_accum]
      · subst hi1
        rw [fakeExpSteps_add]
        have s2 := fakeExpSteps_mul_bound numer denom 8 hd hsmall 16 o1 a1 17 (128 ^ 16 * (2 ^ 84 - 1))
          (by omega) (by omega) s1.1
        generalize hst2 : fakeExpSteps numer denom 16 (o1, a1, 17) = st2 at s2 ⊢
        rcases st2 with ⟨o2, a2, i2⟩
        simp only at s2
        rcases s2.2 with hz2 | hi2
        · subst hz2; simp [fakeExpSteps_zero_accum]
        · subst hi2
          rw [fakeExpSteps_add]
          have s3 := fakeExpSteps_mul_bound numer denom 4 hd hsmall 32 o2 a2 33
            (8 ^ 16 * (128 ^ 16 * (2 ^ 84 - 1))) (by omega) (by omega) s2.1
          generalize hst3 : fakeExpSteps numer denom 32 (o2, a2, 33) = st3 at s3 ⊢
          rcases st3 with ⟨o3, a3, i3⟩
          simp only at s3
          rcases s3.2 with hz3 | hi3
          · subst hz3; simp [fakeExpSteps_zero_accum]
          · subst hi3
            rw [fakeExpSteps_add]
            have s4 := fakeExpSteps_mul_bound numer denom 2 hd hsmall 64 o3 a3 65
              (4 ^ 32 * (8 ^ 16 * (128 ^ 16 * (2 ^ 84 - 1)))) (by omega) (by omega) s3.1
            generalize hst4 : fakeExpSteps numer denom 64 (o3, a3, 65) = st4 at s4 ⊢
            rcases st4 with ⟨o4, a4, i4⟩
            simp only at s4
            rcases s4.2 with hz4 | hi4
            · subst hz4; simp [fakeExpSteps_zero_accum]
            · subst hi4
              rw [fakeExpSteps_add]
              have s5 := fakeExpSteps_mul_bound numer denom 1 hd hsmall 128 o4 a4 129
                (2 ^ 64 * (4 ^ 32 * (8 ^ 16 * (128 ^ 16 * (2 ^ 84 - 1))))) (by omega) (by omega) s4.1
              generalize hst5 : fakeExpSteps numer denom 128 (o4, a4, 129) = st5 at s5 ⊢
              rcases st5 with ⟨o5, a5, i5⟩
              simp only at s5
              rcases s5.2 with hz5 | hi5
              · subst hz5; simp [fakeExpSteps_zero_accum]
              · subst hi5
                have ha5 : a5 < 2 ^ 372 := by
                  have hlt84 : 2 ^ 84 - 1 < 2 ^ 84 := Nat.sub_lt (Nat.pow_pos (by omega)) (by omega)
                  have hpow128 : (128 : Nat) ^ 16 = 2 ^ 112 := by
                    have : (128 : Nat) = 2 ^ 7 := rfl
                    rw [this, ← Nat.pow_mul]
                  have hpow8 : (8 : Nat) ^ 16 = 2 ^ 48 := by
                    have : (8 : Nat) = 2 ^ 3 := rfl
                    rw [this, ← Nat.pow_mul]
                  have hpow4 : (4 : Nat) ^ 32 = 2 ^ 64 := by
                    have : (4 : Nat) = 2 ^ 2 := rfl
                    rw [this, ← Nat.pow_mul]
                  have hpeak : 1 ^ 128 * (2 ^ 64 * (4 ^ 32 * (8 ^ 16 * (128 ^ 16 * (2 ^ 84 - 1))))) < 2 ^ 372 := by
                    rw [Nat.one_pow, Nat.one_mul, hpow128, hpow8, hpow4]
                    have hstep : 2 ^ 64 * (2 ^ 64 * (2 ^ 48 * (2 ^ 112 * (2 ^ 84 - 1)))) <
                                 2 ^ 64 * (2 ^ 64 * (2 ^ 48 * (2 ^ 112 * 2 ^ 84))) := by
                      repeat apply Nat.mul_lt_mul_of_pos_left _ (Nat.pow_pos (by omega))
                      exact hlt84
                    have hsum : 2 ^ 64 * (2 ^ 64 * (2 ^ 48 * (2 ^ 112 * 2 ^ 84))) = 2 ^ 372 := by
                      rw [← Nat.pow_add, show (112 : Nat) + 84 = 196 from rfl,
                          ← Nat.pow_add, show (48 : Nat) + 196 = 244 from rfl,
                          ← Nat.pow_add, show (64 : Nat) + 244 = 308 from rfl,
                          ← Nat.pow_add]
                    exact hsum ▸ hstep
                  exact Nat.lt_of_le_of_lt s5.1 hpeak
                exact fakeExpSteps_halve_zero numer denom hd hsmall 372 o5 a5 (129 + 128) (by omega) ha5
    have hconst : ∀ k, 628 ≤ k →
        (fakeExpSteps numer denom k (0, factor * denom, 1)).1 =
        (fakeExpSteps numer denom 628 (0, factor * denom, 1)).1 := by
      intro k hk
      have hsplit : k = 628 + (k - 628) := by omega
      rw [hsplit, fakeExpSteps_add]
      generalize hst : fakeExpSteps numer denom 628 (0, factor * denom, 1) = st at h628 ⊢
      rcases st with ⟨o, a, i⟩
      simp only at h628
      subst h628
      rw [fakeExpSteps_zero_accum]
    rw [hconst (1024 + extra) (by omega), hconst 1024 (by omega)]

/-- Corollary: `targetOfExponent` is independent of fuel beyond 1,024. -/
theorem targetOfExponent_fuel_sufficient (targetExp extra : Nat) :
    satU64 (fakeExpLoop targetExp targetConversion (1024 + extra) 0 (minTarget * targetConversion) 1 / targetConversion) =
    satFakeExp minTarget targetExp targetConversion := by
  have h := satFakeExp_fuel_sufficient minTarget targetExp targetConversion extra
    (by decide) (Nat.le_refl _) (by decide) (by decide)
  rw [h]; unfold satFakeExp; simp [targetConversion, fakeExponential_eq_loop]

/-- Corollary: `minPriceOfExponent` is independent of fuel beyond 1,024. -/
theorem minPriceOfExponent_fuel_sufficient (minPriceExp extra : Nat) :
    satU64 (fakeExpLoop minPriceExp minPriceConversion (1024 + extra) 0 (1 * minPriceConversion) 1 / minPriceConversion) =
    satFakeExp 1 minPriceExp minPriceConversion := by
  have h := satFakeExp_fuel_sufficient 1 minPriceExp minPriceConversion extra
    (Nat.le_refl _) (by decide) (by decide) (by decide)
  rw [h]; unfold satFakeExp; simp [minPriceConversion, fakeExponential_eq_loop]

/-- Corollary: `Params.priceAt` is independent of fuel beyond 1,024 for any positive target. -/
theorem priceAt_fuel_sufficient (p : Params) (excess extra : Nat) (ht : 0 < p.target) :
    satU64 (fakeExpLoop excess p.scaling (1024 + extra) 0 (1 * p.scaling) 1 / p.scaling) =
    p.priceAt excess := by
  have hsc1 : 1 ≤ p.scaling := by
    unfold Params.scaling satU64 targetToExcessScaling maxU64
    omega
  have hsc2 : p.scaling ≤ maxU64 := Nat.min_le_right _ _
  have h := satFakeExp_fuel_sufficient 1 excess p.scaling extra
    (Nat.le_refl _) (by decide) hsc1 hsc2
  rw [h]; unfold Params.priceAt satFakeExp
  have hne : p.scaling ≠ 0 := by omega
  simp [hne, fakeExponential_eq_loop]

/-! ## Extreme-range comparison vectors (Lean kernel proofs, cross-checked in `tests/avalanche.lisp`) -/

example : targetOfExponent 0 = 1000000 := rfl
example : targetOfExponent maxU64 = 9223372036854775807 := by
  unfold targetOfExponent satFakeExp
  simp only [show targetConversion ≠ 0 by decide, ↓reduceIte, fakeExponential_eq_loop]
  rw [satFakeExp_saturates_of_big minTarget maxU64 targetConversion 1024 (by decide) (by decide) (by decide) (by decide)]
  decide
example : minPriceOfExponent 0 = 1 := rfl
example : minPriceOfExponent 415828534307635077 = 2 := rfl
example : minPriceOfExponent (2 * minPriceConversion) = 7 := rfl
example : minPriceOfExponent (128 * minPriceConversion) = maxU64 := by
  unfold minPriceOfExponent satFakeExp
  simp only [show minPriceConversion ≠ 0 by decide, ↓reduceIte, fakeExponential_eq_loop]
  exact satFakeExp_saturates_of_big 1 (128 * minPriceConversion) minPriceConversion 1024
    (by decide) (by decide) (Nat.le_refl _) (by decide)
example : (Params.ofExponents 0 0).priceAt 0 = 1 := rfl
example : (Params.ofExponents 0 0).priceAt maxU64 = maxU64 := by
  unfold Params.priceAt satFakeExp
  have hsc : (Params.ofExponents 0 0).scaling = 87000000 := rfl
  simp only [hsc, show (87000000 : Nat) ≠ 0 by decide, ↓reduceIte, fakeExponential_eq_loop]
  exact satFakeExp_saturates_of_big 1 maxU64 87000000 1024 (by decide) (by decide) (by decide) (by decide)
example : (Params.ofExponents 0 0).priceAt 12000000000 = maxU64 := by
  unfold Params.priceAt satFakeExp
  have hsc : (Params.ofExponents 0 0).scaling = 87000000 := rfl
  simp only [hsc, show (87000000 : Nat) ≠ 0 by decide, ↓reduceIte, fakeExponential_eq_loop]
  exact satFakeExp_saturates_of_big 1 12000000000 87000000 1024 (by decide) (by decide) (by decide) (by decide)

end Evm.Avalanche.GasClock
