import Evm.CL.GasEmit
import Evm.CL.GasEmitLondon
import Evm.CL.GasEmitCancun
import Evm.Frontier.Spec.HeaderValidity

/-! # Evm.CL.HeaderEmit — `validate_header`, emitted to the host's header gate

`headerViolation` is the `Expr` term the host evaluates for every block (and every ommer)
against its parent header: 0 when the header is valid, else the code
(`Evm.Frontier.Spec.HeaderValidity.Violation.code`) of the FIRST clause of EELS
`validate_header` that raises, for the block's fork. `headerViolation_eq_spec` proves it
equal to `Evm.Frontier.Spec.HeaderValidity.validateHeader` for every fork; the parts are
proved separately: `blockDifficulty` = `calculateBlockDifficulty` before Paris (the signed
`max(…, -99)` clamp done in Nat, the bomb's Python floor division on a possibly negative
number), the gas-limit window = `check_gas_limit`, and the base fee / excess blob gas through
`Evm.CL.GasEmitLondon` / `Evm.CL.GasEmitCancun`.

Inputs (`Env` names): the header's `number timestamp gas-limit gas-used extra-len difficulty
nonce base-fee excess-blob-gas`; the parent's `parent-number parent-timestamp
parent-gas-limit parent-gas-used parent-difficulty parent-base-fee parent-excess-blob-gas
parent-blob-gas-used`; the flags (1/0) `extra-is-dao ommers-empty parent-has-ommers
london-fork-block`; `fork-ord`. A field the fork's header lacks is 0 (the host refuses a
header whose fields do not match its fork before it asks). -/

namespace Evm.CL.HeaderEmit

open Evm.CL.GasEmit
open Evm.Frontier.Spec.HeaderValidity

def v (x : String) : Expr := .var x
/-- `if a ≠ b then t else e`. -/
def ifNe (a b t e : Expr) : Expr := .ite a b t (.ite b a t e)
/-- `if a ≤ b then t else e`. -/
def ifLe (a b t e : Expr) : Expr := .ite b a e t
/-- `if flag then t else e` for a 1/0 flag. -/
def ifSet (x : String) (t e : Expr) : Expr := .ite (.lit 0) (v x) t e
/-- `if fork-ord < k then t else e`. -/
def forkBelow (k : Nat) (t e : Expr) : Expr := .ite fork (.lit k) t e

/-- `if not check_gas_limit(gas_limit, parent_gas_limit) then t else e`. -/
def ifGasLimitBad (t e : Expr) : Expr :=
  let gl := v "gas-limit"
  let pgl := v "parent-gas-limit"
  let delta := Expr.fdiv pgl (.lit 1024)
  .ite gl (.add pgl delta) (ifLe gl (.sub pgl delta) t (.ite gl (.lit 5000) t e)) t

/-- The bomb delay of the fork (`BOMB_DELAY_BLOCKS`; 0 before Byzantium). -/
def bombDelayE : Expr :=
  forkBelow 5 (.lit 0) (forkBelow 6 (.lit 3000000) (forkBelow 9 (.lit 5000000)
    (forkBelow 11 (.lit 9000000) (forkBelow 12 (.lit 9700000) (forkBelow 13 (.lit 10700000) (.lit 11400000))))))

def pdiff : Expr := v "parent-difficulty"
def tsDelta : Expr := .sub (v "timestamp") (v "parent-timestamp")

/-- EIP-2 / EIP-100: `parent + parent // 2048 * max(c - (ts - pts) // k, -99)`, in Nat: up
    by `(c - q)` steps when `q < c`, else down by `min(q - c, 99)` steps. -/
def adjusted (c : Expr) (k : Nat) : Expr :=
  let q := Expr.fdiv tsDelta (.lit k)
  let step := Expr.fdiv pdiff (.lit 2048)
  .ite q c (.add pdiff (.mul step (.sub c q))) (.sub pdiff (.mul step (.emin (.sub q c) (.lit 99))))

/-- `calculate_block_difficulty` (before Paris). -/
def blockDifficulty : Expr :=
  let frontierD := Expr.ite (v "timestamp") (.add (v "parent-timestamp") (.lit 13))
    (.add pdiff (.fdiv pdiff (.lit 2048))) (.sub pdiff (.fdiv pdiff (.lit 2048)))
  let base := forkBelow 1 frontierD
    (forkBelow 5 (adjusted (.lit 1) 10) (adjusted (ifSet "parent-has-ommers" (.lit 2) (.lit 1)) 9))
  let periods := Expr.fdiv (.sub (v "number") bombDelayE) (.lit 100000)
  .emax (.add base (.ite periods (.lit 2) (.lit 0) (.pow2 (.sub periods (.lit 2))))) (.lit 131072)

/-- The `validate_header` violation code (0 = valid), clause order as EELS. -/
def headerViolation : Expr :=
  let num := v "number"; let ts := v "timestamp"; let gl := v "gas-limit"; let gu := v "gas-used"
  let c (x : Violation) : Expr := .lit x.code
  let difficultyRule (e : Expr) : Expr := ifNe (v "difficulty") blockDifficulty (c .difficulty) e
  let preLondon :=
    Expr.ite gl gu (c .gasUsedAboveLimit)
    (ifLe ts (v "parent-timestamp") (c .timestamp)
    (ifNe num (.add (v "parent-number") (.lit 1)) (c .number)
    (ifGasLimitBad (c .gasLimit)
    (.ite (.lit 32) (v "extra-len") (c .extraData)
    (difficultyRule
    -- dao_fork: 1,920,000 <= number < 1,920,010 needs extra_data = b"dao-hard-fork"
    (ifNe fork (.lit 2) (.lit 0)
      (.ite num (.lit daoForkBlock) (.lit 0)
        (.ite num (.lit (daoForkBlock + 10)) (ifSet "extra-is-dao" (.lit 0) (c .daoExtraData)) (.lit 0)))))))))
  let rest :=
    ifLe ts (v "parent-timestamp") (c .timestamp)
    (ifNe num (.add (v "parent-number") (.lit 1)) (c .number)
    (.ite (.lit 32) (v "extra-len") (c .extraData)
    (forkBelow 14 (difficultyRule (.lit 0))
    (ifNe (v "difficulty") (.lit 0) (c .difficulty)
    (ifNe (v "nonce") (.lit 0) (c .nonce)
    (ifSet "ommers-empty" (.lit 0) (c .ommersHash)))))))
  -- london on: the base fee (calculate_base_fee_per_gas checks the gas limit first); on the
  -- London fork block INITIAL_BASE_FEE and no gas-limit check. Each continuation appears once
  -- (an Expr has no sharing): the two conditions are 1/0 terms.
  let forkBlock := forkBelow 12 (ifSet "london-fork-block" (.lit 1) (.lit 0)) (.lit 0)
  let gasLimitBad := ifGasLimitBad (.lit 1) (.lit 0)
  let afterExcess :=
    Expr.ite gl gu (c .gasUsedAboveLimit)
    (.ite (.lit 0) (.mul gasLimitBad (.sub (.lit 1) forkBlock)) (c .gasLimit)
    (ifNe (v "base-fee") (.ite (.lit 0) forkBlock initialBaseFee nextBaseFee) (c .baseFee) rest))
  forkBelow 11 preLondon
    (.ite (.lit 0) (forkBelow 16 (.lit 0) (ifNe (v "excess-blob-gas") nextExcessBlobGas (.lit 1) (.lit 0)))
      (c .excessBlobGas) afterExcess)

/-! ## The emitted term is the spec -/

theorem ifGasLimitBad_eval (ρ : Env) (t e : Expr) :
    (ifGasLimitBad t e).eval ρ
      = if checkGasLimit (ρ "gas-limit") (ρ "parent-gas-limit") then e.eval ρ else t.eval ρ := by
  simp only [ifGasLimitBad, ifLe, v, Expr.eval, checkGasLimit, limitAdjustmentFactor, limitMinimum]
  by_cases h1 : ρ "gas-limit" < ρ "parent-gas-limit" + ρ "parent-gas-limit" / 1024
  · by_cases h2 : ρ "parent-gas-limit" - ρ "parent-gas-limit" / 1024 < ρ "gas-limit"
    · have h1' : ¬ ρ "gas-limit" ≥ ρ "parent-gas-limit" + ρ "parent-gas-limit" / 1024 := by omega
      have h2' : ¬ ρ "gas-limit" ≤ ρ "parent-gas-limit" - ρ "parent-gas-limit" / 1024 := by omega
      by_cases h3 : ρ "gas-limit" < 5000 <;> simp [h1, h2, h3, h1', h2']
    · have h1' : ¬ ρ "gas-limit" ≥ ρ "parent-gas-limit" + ρ "parent-gas-limit" / 1024 := by omega
      have : ρ "gas-limit" ≤ ρ "parent-gas-limit" - ρ "parent-gas-limit" / 1024 := by omega
      simp [h1, h2, h1', this]
  · have : ρ "gas-limit" ≥ ρ "parent-gas-limit" + ρ "parent-gas-limit" / 1024 := by omega
    simp [h1, this]

theorem bombDelayE_eval (ρ : Env) (f : Evm.Fork) (hf : ρ "fork-ord" = f.ord) (hp : f.ord < 14) :
    bombDelayE.eval ρ = bombDelay f := by
  simp only [bombDelayE, forkBelow, fork, Expr.eval, hf]
  cases f <;> simp_all [Evm.Fork.ord, bombDelay]

/-- The EIP-2 / EIP-100 adjustment in Nat is the spec's signed one. -/
theorem adjusted_int (pdiff c q : Nat) :
    ((if q < c then pdiff + pdiff / 2048 * (c - q) else pdiff - pdiff / 2048 * min (q - c) 99 : Nat) : Int)
      = (pdiff : Int) + ((pdiff / 2048 : Nat) : Int) * max ((c : Int) - (q : Int)) (-99) := by
  have hD : pdiff / 2048 * 2048 ≤ pdiff := Nat.div_mul_le_self pdiff 2048
  generalize pdiff / 2048 = D at *
  by_cases h : q < c
  · rw [ite_eq_left h, Int.max_eq_left (by omega)]
    rw [Int.natCast_add, Int.natCast_mul, Int.natCast_sub (Nat.le_of_lt h)]
  · rw [ite_eq_right h]
    have hm : min (q - c) 99 ≤ 99 := Nat.min_le_right _ _
    have hle : D * min (q - c) 99 ≤ pdiff :=
      Nat.le_trans (Nat.mul_le_mul_left _ hm) (by omega)
    rw [Int.natCast_sub hle, Int.natCast_mul]
    have hmax : max ((c : Int) - (q : Int)) (-99) = - ((min (q - c) 99 : Nat) : Int) := by
      rcases Nat.lt_or_ge (q - c) 99 with h' | h'
      · rw [Nat.min_eq_left (Nat.le_of_lt h'), Int.max_eq_left (by omega), Int.natCast_sub (by omega : c ≤ q)]
        omega
      · rw [Nat.min_eq_right h', Int.max_eq_right (by omega)]
        rfl
    rw [hmax, Int.mul_neg]
    omega

/-- The bomb and the floor: Python's `(number - delay) // 100000 - 2 >= 0`, `+ 2**…` and
    `max(…, MINIMUM_DIFFICULTY)` over the signed difficulty `d`, in Nat once `d` is a Nat. -/
theorem bomb_floor (X n D : Nat) (d : Int) (hd : d = (X : Int)) :
    max (X + (if (n - D) / 100000 < 2 then 0 else 2 ^ ((n - D) / 100000 - 2))) 131072
      = (max (if ((n : Int) - (D : Int)) / 100000 - 2 ≥ 0 then d + 2 ^ (((n : Int) - (D : Int)) / 100000 - 2).toNat else d)
             ((131072 : Nat) : Int)).toNat := by
  subst hd
  by_cases h : (n - D) / 100000 < 2
  · rw [ite_eq_left h, ite_eq_right (by omega)]; omega
  · rw [ite_eq_right h, ite_eq_left (by omega)]
    have : (((n : Int) - (D : Int)) / 100000 - 2).toNat = (n - D) / 100000 - 2 := by omega
    have h2 : (2 : Int) ^ ((n - D) / 100000 - 2) = ((2 ^ ((n - D) / 100000 - 2) : Nat) : Int) := by
      rw [Int.natCast_pow]; rfl
    rw [this, h2]; omega

set_option backward.isDefEq.respectTransparency false in
theorem blockDifficulty_eq_spec (ρ : Env) (f : Evm.Fork) (hp : f.ord < 14) (pho : Bool)
    (hf : ρ "fork-ord" = f.ord) (hpo : ρ "parent-has-ommers" = if pho then 1 else 0) :
    blockDifficulty.eval ρ
      = calculateBlockDifficulty f (ρ "number") (ρ "timestamp") (ρ "parent-timestamp") (ρ "parent-difficulty") pho := by
  have hb := bombDelayE_eval ρ f hf hp
  simp only [blockDifficulty, adjusted, forkBelow, ifSet, fork, pdiff, tsDelta, v, Expr.eval]
  rw [hb, hf, hpo]
  simp only [calculateBlockDifficulty, minimumDifficulty]
  refine bomb_floor _ _ _ _ ?_
  rcases Nat.lt_or_ge f.ord 1 with h0 | h0
  · have hfr : f = .frontier := by cases f <;> simp_all [Evm.Fork.ord]
    subst hfr
    simp only [Evm.Fork.ord, ite_true, Nat.zero_lt_one]
    by_cases h : ρ "timestamp" < ρ "parent-timestamp" + 13 <;> simp [h]
  · have hfr : f ≠ .frontier := by intro e; subst e; simp [Evm.Fork.ord] at h0
    rw [ite_eq_right hfr, ite_eq_right (show ¬ f.ord < 1 by omega)]
    by_cases hb5 : f.ord < 5
    · have : f.atLeast .byzantium = false := by
        have : Evm.Fork.byzantium.ord = 5 := rfl
        simp only [Evm.Fork.atLeast, this, decide_eq_false_iff_not]; omega
      rw [ite_eq_left hb5]; simp only [this, Bool.false_eq_true, ite_false]
      exact (adjusted_int _ 1 _).symm
    · have : f.atLeast .byzantium = true := by
        have : Evm.Fork.byzantium.ord = 5 := rfl
        simp only [Evm.Fork.atLeast, this, decide_eq_true_eq]; omega
      rw [ite_eq_right hb5]; simp only [this, ite_true]
      cases pho
      · simpa using (adjusted_int (ρ "parent-difficulty") 1 ((ρ "timestamp" - ρ "parent-timestamp") / 9)).symm
      · simpa using (adjusted_int (ρ "parent-difficulty") 2 ((ρ "timestamp" - ρ "parent-timestamp") / 9)).symm


theorem ifNe_eval (ρ : Env) (a b t e : Expr) :
    (ifNe a b t e).eval ρ = if a.eval ρ ≠ b.eval ρ then t.eval ρ else e.eval ρ := by
  simp only [ifNe, Expr.eval]
  by_cases h1 : a.eval ρ < b.eval ρ
  · simp [h1, Nat.ne_of_lt h1]
  · by_cases h2 : b.eval ρ < a.eval ρ
    · simp [h1, h2, Nat.ne_of_gt h2]
    · have : a.eval ρ = b.eval ρ := by omega
      simp [this]

theorem ifLe_eval (ρ : Env) (a b t e : Expr) :
    (ifLe a b t e).eval ρ = if a.eval ρ ≤ b.eval ρ then t.eval ρ else e.eval ρ := by
  simp only [ifLe, Expr.eval]
  by_cases h : b.eval ρ < a.eval ρ
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.not_lt.mp h]

theorem ifSet_eval (ρ : Env) (x : String) (b : Bool) (hx : ρ x = if b then 1 else 0) (t e : Expr) :
    (ifSet x t e).eval ρ = if b then t.eval ρ else e.eval ρ := by
  cases b <;> simp [ifSet, v, Expr.eval, hx]

set_option backward.isDefEq.respectTransparency false in
theorem forkBelow_eval (ρ : Env) (k : Nat) (t e : Expr) :
    (forkBelow k t e).eval ρ = if ρ "fork-ord" < k then t.eval ρ else e.eval ρ := by
  simp [forkBelow, fork, Expr.eval]

theorem zero_lt_flag (c : Prop) [Decidable c] : (0 < if c then 0 else 1) ↔ ¬ c := by
  by_cases h : c <;> simp [h]

theorem code_ite (c : Prop) [Decidable c] (x y : Option Violation) :
    code (if c then x else y) = if c then code x else code y := by
  split <;> rfl

/-- **The emitted header gate is `validate_header`**: for every fork (to BPO2) and header. -/
theorem headerViolation_eq_spec (ρ : Env) (f : Evm.Fork) (h p : View)
    (extraIsDao ommersEmpty parentHasOmmers londonForkBlock : Bool)
    (hf : ρ "fork-ord" = f.ord) (ham : f ≠ .amsterdam)
    (hn : ρ "number" = h.number) (hts : ρ "timestamp" = h.timestamp) (hgl : ρ "gas-limit" = h.gasLimit)
    (hgu : ρ "gas-used" = h.gasUsed) (hx : ρ "extra-len" = h.extraLen) (hd : ρ "difficulty" = h.difficulty)
    (hno : ρ "nonce" = h.nonce) (hbf : ρ "base-fee" = h.baseFee) (hex : ρ "excess-blob-gas" = h.excessBlobGas)
    (hpn : ρ "parent-number" = p.number) (hpts : ρ "parent-timestamp" = p.timestamp)
    (hpgl : ρ "parent-gas-limit" = p.gasLimit) (hpgu : ρ "parent-gas-used" = p.gasUsed)
    (hpd : ρ "parent-difficulty" = p.difficulty) (hpbf : ρ "parent-base-fee" = p.baseFee)
    (hpex : ρ "parent-excess-blob-gas" = p.excessBlobGas) (hpbu : ρ "parent-blob-gas-used" = p.blobGasUsed)
    (hdao : ρ "extra-is-dao" = if extraIsDao then 1 else 0)
    (hoe : ρ "ommers-empty" = if ommersEmpty then 1 else 0)
    (hpo : ρ "parent-has-ommers" = if parentHasOmmers then 1 else 0)
    (hlf : ρ "london-fork-block" = if londonForkBlock then 1 else 0) :
    headerViolation.eval ρ = code (validateHeader f h p extraIsDao ommersEmpty parentHasOmmers londonForkBlock) := by
  have hdiff : f.ord < 14 → blockDifficulty.eval ρ
      = calculateBlockDifficulty f h.number h.timestamp p.timestamp p.difficulty parentHasOmmers := by
    intro hp; rw [blockDifficulty_eq_spec ρ f hp parentHasOmmers hf hpo, hn, hts, hpts, hpd]
  have hbase := Evm.CL.GasEmitLondon.nextBaseFee_eq_spec ρ p.gasUsed p.gasLimit p.baseFee hpgu hpgl hpbf
  have hexc := Evm.CL.GasEmitCancun.nextExcessBlobGas_eq_spec ρ f p.excessBlobGas p.blobGasUsed p.baseFee hf hpex hpbu hpbf
  have hgas : ∀ t e : Expr, (ifGasLimitBad t e).eval ρ
      = if checkGasLimit h.gasLimit p.gasLimit then e.eval ρ else t.eval ρ := by
    intro t e; rw [ifGasLimitBad_eval, hgl, hpgl]
  simp only [headerViolation, ifNe_eval, ifLe_eval, forkBelow_eval, hgas,
    ifSet_eval ρ _ _ hdao, ifSet_eval ρ _ _ hoe, ifSet_eval ρ _ _ hlf, v, fork, Expr.eval,
    hbase, hexc, hf, hn, hts, hgl, hgu, hx, hd, hno, hbf, hex, hpn, hpts]
  simp only [validateHeader]
  simp only [code_ite]
  simp only [code, Violation.code]
  cases f
  case amsterdam => exact absurd rfl ham
  all_goals simp only [Evm.Fork.ord] at hdiff ⊢
  all_goals first | rw [hdiff (by decide)] | skip
  all_goals simp (config := { decide := true }) [initialBaseFee,
    Evm.London.Spec.initialBaseFee, Expr.eval]
  all_goals by_cases hc : checkGasLimit h.gasLimit p.gasLimit <;> simp [hc]
  all_goals cases ommersEmpty <;> cases extraIsDao <;> cases londonForkBlock <;> try simp [zero_lt_flag]
  -- dao_fork: the window test as nested comparisons
  all_goals by_cases hd1 : daoForkBlock ≤ h.number <;> by_cases hd2 : h.number < daoForkBlock + 10 <;>
    simp [hd1, hd2, (Nat.not_le (a := daoForkBlock) (b := h.number)).symm]

/-! ## Mainnet vectors: the emitted difficulty on real headers (`eth_getBlockByNumber`):
    Frontier block 1, Homestead 1,150,000 (bomb period 9), Byzantium 4,370,000 (EIP-649's
    delay: period 11 where Spurious Dragon would add 2^41) -/

example : blockDifficulty.eval (mkEnv [("fork-ord",0),("number",1),("timestamp",1438269988),
    ("parent-timestamp",0),("parent-difficulty",17179869184)]) = 17171480576 := by native_decide
example : blockDifficulty.eval (mkEnv [("fork-ord",1),("number",1150000),("timestamp",1457981393),
    ("parent-timestamp",1457981342),("parent-difficulty",20513164863791)]) = 20473100089179 := by native_decide
example : blockDifficulty.eval (mkEnv [("fork-ord",5),("number",4370000),("timestamp",1508131331),
    ("parent-timestamp",1508131303),("parent-difficulty",2997274096101735)]) = 2994347070619309 := by native_decide

end Evm.CL.HeaderEmit
