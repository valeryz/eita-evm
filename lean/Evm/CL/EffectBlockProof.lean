import Evm.CL.EffectBlock

/-! # CL/EffectBlockProof — the derived block credits are every fork's

`credits_refines`: for every fork `k`, state, coinbase, block number, ommer list and
withdrawal list, running `Evm.CL.EffectBlock.credits` changes exactly the world state, to
`Evm.Frontier.Vm.Block.postBlock` — EELS `pay_rewards` then `process_withdrawals`. No
assumptions: the term reads nothing but its inputs and the state. -/

namespace Evm.CL.EffectBlockProof

open Evm.CL.EffectIR Evm.CL.EffectBlock
open Evm.Frontier (State)

/-- The inputs `spec-block-credits` is called with. -/
def ctxB (k : Nat) (cb : Evm.Address) (number : Nat) (ommers ws : List (Evm.Address × Nat)) : Ctx :=
  { fork := k,
    addr := fun y => if y = "coinbase" then cb else 0,
    nat := fun y => if y = "number" then number else 0,
    pairs := fun y => if y = "uncles" then ommers else if y = "withdrawals" then ws else [] }

/-- A `forPairs` loop whose body changes only the state, by `f`, is the fold of `f`. -/
theorem forPairs_state (c : Ctx) (body : Stmt) (f : State → Evm.Address × Nat → State)
    (hb : ∀ p (h : HState), body.run (c.withPair p) h = { h with state := f h.state p }) :
    ∀ (l : List (Evm.Address × Nat)) (h : HState),
      l.foldl (fun h' p => body.run (c.withPair p) h') h = { h with state := l.foldl f h.state } := by
  intro l
  induction l with
  | nil => intro h; rfl
  | cons p t ih => intro h; simp only [List.foldl_cons]; rw [hb]; exact ih _

theorem exists_addBalance (s : State) (a : Evm.Address) (d : Evm.U256) :
    (s.addBalance a d).accountExists a = true := by
  simp [State.addBalance, State.setAccount, State.accountExists]

theorem env_k (k : Nat) :
    (fun y => if y = "fork-ord" then k else 0) = Evm.Frontier.Vm.Block.env k 0 0 := by
  funext y
  simp only [Evm.Frontier.Vm.Block.env]
  by_cases h1 : y = "fork-ord" <;> simp [h1]

theorem run_seq (c : Ctx) (a b : Stmt) (h : HState) : (Stmt.seq a b).run c h = b.run c (a.run c h) := rfl
theorem run_ite (c : Ctx) (p : BExp) (a b : Stmt) (h : HState) :
    (Stmt.ite p a b).run c h = if p.eval c h then a.run c h else b.run c h := rfl
theorem run_forPairs (c : Ctx) (l : String) (b : Stmt) (h : HState) :
    (Stmt.forPairs l b).run c h = (c.pairs l).foldl (fun h' p => b.run (c.withPair p) h') h := rfl
theorem run_pay (c : Ctx) (a : AExp) (g : GExp) (h : HState) :
    (Stmt.pay a g).run c h = { h with state := h.state.addBalance (a.eval c) (Evm.U256.ofNat (g.eval c h)) } := rfl

/-- One ommer's credit (the body of `payRewards`'s fold). -/
def ommerStep (k number : Nat) (s : State) (o : Evm.Address × Nat) : State :=
  s.addBalance o.1 (Evm.U256.ofNat (Evm.Frontier.Vm.Block.ommerReward k number o.2))

theorem rewards_run (k : Nat) (cb : Evm.Address) (number : Nat) (ommers ws : List (Evm.Address × Nat))
    (h : HState) :
    rewards.run (ctxB k cb number ommers ws) h
      = { h with state := Evm.Frontier.Vm.Block.payRewards k h.state cb number ommers } := by
  unfold rewards Evm.Frontier.Vm.Block.payRewards
  by_cases hk : k ≥ 14
  · simp [Stmt.run, BExp.eval, ctxB, hk]
  · have hstep : ∀ p (h' : HState), (Stmt.pay pAddr ommerG).run ((ctxB k cb number ommers ws).withPair p) h'
        = { h' with state := ommerStep k number h'.state p } := by
      intro p h'
      simp [Stmt.run, AExp.eval, ommerG, GExp.eval, Ctx.withPair, ctxB, ommerStep,
        Evm.Frontier.Vm.Block.ommerReward]
      rfl
    have hl := forPairs_state ((ctxB k cb number ommers ws)) (Stmt.pay pAddr ommerG)
      (ommerStep k number) hstep
    have hf : (BExp.not (BExp.forkGe 14)).eval (ctxB k cb number ommers ws) h = true := by
      simp [BExp.eval, ctxB, hk]
    rw [run_ite, hf, ite_eq_left rfl, run_seq, run_forPairs,
      show (ctxB k cb number ommers ws).pairs "uncles" = ommers by simp [ctxB], hl, run_pay, ite_eq_right hk]
    simp [AExp.eval, minerG, GExp.eval, ctxB, Evm.Frontier.Vm.Block.minerReward, env_k]
    rfl

theorem withdrawal_run (c : Ctx) (p : Evm.Address × Nat) (h : HState) :
    withdrawal.run (c.withPair p) h = { h with state := Evm.Frontier.Vm.Block.withdraw h.state p } := by
  unfold withdrawal Evm.Frontier.Vm.Block.withdraw
  rw [run_seq, run_pay, run_ite]
  simp only [AExp.eval, BExp.eval, GExp.eval, Ctx.withPair, isDead, exists_addBalance, ite_true,
    pAddr]
  split <;> rfl

theorem withdrawals_run (k : Nat) (cb : Evm.Address) (number : Nat) (ommers ws : List (Evm.Address × Nat))
    (h : HState) :
    withdrawals.run (ctxB k cb number ommers ws) h
      = { h with state := Evm.Frontier.Vm.Block.processWithdrawals k h.state ws } := by
  unfold withdrawals Evm.Frontier.Vm.Block.processWithdrawals
  by_cases hk : k ≥ 15
  · have hf : (BExp.forkGe 15).eval (ctxB k cb number ommers ws) h = true := by
      simp [BExp.eval, ctxB, hk]
    rw [run_ite, hf, ite_eq_left rfl, run_forPairs,
      show (ctxB k cb number ommers ws).pairs "withdrawals" = ws by simp [ctxB], ite_eq_left hk]
    exact forPairs_state _ withdrawal Evm.Frontier.Vm.Block.withdraw (withdrawal_run _) ws h
  · simp [Stmt.run, BExp.eval, hk, ctxB]

/-- **The derived block credits are every fork's.** -/
theorem credits_refines (k : Nat) (cb : Evm.Address) (number : Nat)
    (ommers ws : List (Evm.Address × Nat)) (h : HState) :
    credits.run (ctxB k cb number ommers ws) h
      = { h with state := Evm.Frontier.Vm.Block.postBlock k h.state cb number ommers ws } := by
  simp only [credits, Stmt.run, rewards_run, withdrawals_run, Evm.Frontier.Vm.Block.postBlock]

end Evm.CL.EffectBlockProof
