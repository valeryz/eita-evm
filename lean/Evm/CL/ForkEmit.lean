import Evm.CL.GasEmit
import Evm.Testnets

/-! Ethereum mainnet's fork schedule as an emitted `Expr`: `spec-mainnet-fork-ord (n ts)`
    in `src/generated/host.lisp` is the ordinal of `Evm.Fork.ofBlock n ts`, proved
    below, so the Lisp replay's fork choice comes from the one Lean table. Hoodi's,
    `spec-hoodi-fork-ord (ts)`, is `Evm.Fork.ofHoodi ts` the same way, and a devnet's,
    `spec-times-fork-ord (ts prague osaka bpo1 bpo2)`, is `Evm.Fork.ofTimes`. -/

namespace Evm.CL.ForkEmit
open Evm.CL.GasEmit

/-- `if v ≥ k₁ then o₁ else if v ≥ k₂ then o₂ … else d`. -/
def geChain (v : String) : List (Nat × Nat) → Nat → Expr
  | [], d => .lit d
  | (k, o) :: r, d => .ite (.var v) (.lit k) (geChain v r d) (.lit o)

/-- Mirrors `Fork.ofBlock`: block-number activations before the Merge, timestamps after. -/
def mainnetForkOrd : Expr :=
  .ite (.var "n") (.lit Fork.mergeTransitionBlock)
    (geChain "n" [(15050000, 13), (13773000, 12), (12965000, 11), (12244000, 10), (9200000, 9),
                  (9069000, 8), (7280000, 7), (4370000, 5), (2675000, 4), (2463000, 3),
                  (1920000, 2), (1150000, 1)] 0)
    (geChain "ts" [(1767747671, 20), (1765290071, 19), (1764798551, 18), (1746612311, 17),
                   (1710338135, 16), (1681338455, 15)] 14)

set_option backward.isDefEq.respectTransparency false in
theorem mainnetForkOrd_eq_spec (ρ : Env) :
    mainnetForkOrd.eval ρ = (Fork.ofBlock (ρ "n") (ρ "ts")).ord := by
  simp only [mainnetForkOrd, geChain, Expr.eval, Fork.ofBlock, Fork.mergeTransitionBlock]
  simp only [apply_ite (f := Fork.ord)]
  simp only [Fork.ord]
  -- The activation numbers become variables first: deciding `n < 15537394` by reduction
  -- would unfold the literal (the Nat-literal whnf trap); both sides test the same ones.
  generalize (15537394 : Nat) = k0 at *
  generalize (15050000 : Nat) = k1 at *
  generalize (13773000 : Nat) = k2 at *
  generalize (12965000 : Nat) = k3 at *
  generalize (12244000 : Nat) = k4 at *
  generalize (9200000 : Nat) = k5 at *
  generalize (9069000 : Nat) = k6 at *
  generalize (7280000 : Nat) = k7 at *
  generalize (4370000 : Nat) = k8 at *
  generalize (2675000 : Nat) = k9 at *
  generalize (2463000 : Nat) = k10 at *
  generalize (1920000 : Nat) = k11 at *
  generalize (1150000 : Nat) = k12 at *
  generalize (1767747671 : Nat) = k13a at *
  generalize (1765290071 : Nat) = k13b at *
  generalize (1764798551 : Nat) = k13 at *
  generalize (1746612311 : Nat) = k14 at *
  generalize (1710338135 : Nat) = k15 at *
  generalize (1681338455 : Nat) = k16 at *
  simp only [ge_iff_le, ← Nat.not_lt, ite_not]

/-- Mirrors `Fork.ofHoodi`: Cancun from genesis, then the timestamps. -/
def hoodiForkOrd : Expr :=
  geChain "ts" [(1762955544, 20), (1762365720, 19), (1761677592, 18), (1742999832, 17)] 16

set_option backward.isDefEq.respectTransparency false in
theorem hoodiForkOrd_eq_spec (ρ : Env) :
    hoodiForkOrd.eval ρ = (Fork.ofHoodi (ρ "ts")).ord := by
  simp only [hoodiForkOrd, geChain, Expr.eval, Fork.ofHoodi]
  simp only [apply_ite (f := Fork.ord)]
  simp only [Fork.ord]
  generalize (1762955544 : Nat) = k1 at *
  generalize (1762365720 : Nat) = k2 at *
  generalize (1761677592 : Nat) = k3 at *
  generalize (1742999832 : Nat) = k4 at *
  simp only [ge_iff_le, ← Nat.not_lt, ite_not]

/-- Mirrors `Fork.ofTimes`: the activation times are inputs (a devnet's genesis.json). -/
def timesForkOrd : Expr :=
  .ite (.var "ts") (.var "bpo2")
    (.ite (.var "ts") (.var "bpo1")
      (.ite (.var "ts") (.var "osaka")
        (.ite (.var "ts") (.var "prague") (.lit 16) (.lit 17))
        (.lit 18))
      (.lit 19))
    (.lit 20)

theorem timesForkOrd_eq_spec (ρ : Env) :
    timesForkOrd.eval ρ
      = (Fork.ofTimes (ρ "prague") (ρ "osaka") (ρ "bpo1") (ρ "bpo2") (ρ "ts")).ord := by
  simp only [timesForkOrd, Expr.eval, Fork.ofTimes, ge_iff_le]
  -- one case per fork, newest first: each side's tests decided by the same hypotheses
  by_cases h1 : ρ "bpo2" ≤ ρ "ts"
  · simp only [h1, ite_true, Nat.not_lt.mpr h1, ite_false]; rfl
  by_cases h2 : ρ "bpo1" ≤ ρ "ts"
  · simp only [h1, h2, ite_true, ite_false, Nat.not_lt.mpr h2, Nat.lt_of_not_le h1]; rfl
  by_cases h3 : ρ "osaka" ≤ ρ "ts"
  · simp only [h1, h2, h3, ite_true, ite_false, Nat.not_lt.mpr h3, Nat.lt_of_not_le h1,
      Nat.lt_of_not_le h2]; rfl
  by_cases h4 : ρ "prague" ≤ ρ "ts"
  · simp only [h1, h2, h3, h4, ite_true, ite_false, Nat.not_lt.mpr h4, Nat.lt_of_not_le h1,
      Nat.lt_of_not_le h2, Nat.lt_of_not_le h3]; rfl
  · simp only [h1, h2, h3, h4, ite_true, ite_false, Nat.lt_of_not_le h1, Nat.lt_of_not_le h2,
      Nat.lt_of_not_le h3, Nat.lt_of_not_le h4]; rfl

end Evm.CL.ForkEmit
