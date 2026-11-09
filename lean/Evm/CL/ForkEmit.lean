import Evm.CL.GasEmit
import Evm.Forks

/-! Ethereum mainnet's fork schedule as an emitted `Expr`: `spec-mainnet-fork-ord (n ts)`
    in `src/generated/host.lisp` is the ordinal of `Evm.Fork.ofBlock n ts`, proved
    below, so the Lisp replay's fork choice comes from the one Lean table. -/

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

end Evm.CL.ForkEmit
