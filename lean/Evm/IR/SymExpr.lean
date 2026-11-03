/-
  Evm.IR.SymExpr — symbolic stack for the JIT's chunk-local
  partial evaluation (#221 stage 1, issue #11).

  `Expr` is a pure value language over the chunk's ENTRY stack:
  leaves are compile-time constants and `stackAt d` (the entry
  stack slot at depth `d`); interior nodes are exactly the
  stack-pure compute ops of `IR.execOp`. There is deliberately no
  context/state/memory provenance and no byte-slice tree — ops
  whose value depends on anything but the entry stack (EXP's
  dynamic gas included) are *not representable*, and `symStep`
  returns `none` so the emitter falls back to the materialized
  stack. Stage 3 reintroduces memory promotion on top of this.

  Semantics come in two layers, kept honest by construction:

    * `eval e es` evaluates an `Expr` against the entry stack
      `es`. Every arm mirrors the value expression of the
      corresponding `IR.execOp` arm verbatim.
    * The `execOp_*_shape` theorems are `rfl` anchors pinning each
      covered `execOp` arm to a canonical shape (`binaryExec f`
      etc.). If an `execOp` arm drifts, the anchor fails to
      elaborate — there is no second hand-written semantics that
      can silently diverge.

  The bridge is `symStep_sound`: if `symStep op ss = some ss'` and
  the concrete stack is `ss.denote es`, then a successful
  `execOp evm op` produces exactly `{ evm with stack := ss'.denote es }`.
  Success of `execOp` is a hypothesis, not a conclusion: the
  stage-2 emitter discharges underflow with a single chunk-entry
  depth check (`consumed` is monotone) and overflow at flush
  against the region's peak depth, as the 6c folder already does.
-/

import Evm.IR.Execute
import Evm.Frontier.Vm.Step

namespace Evm.IR.SymExpr

open Evm Evm.Frontier.Vm Evm.Frontier.Vm.Spec

/-! ## Expression language -/

/-- U256-valued symbolic expressions over a chunk's entry stack.
    `stackAt 0` is top-of-stack at chunk entry. Constructor names
    track `IR.Op` (with `_` suffixes where Lean keywords collide). -/
inductive Expr where
  | const      (val : U256)
  | stackAt    (depth : Nat)
  -- Arithmetic
  | add        (a b : Expr)
  | mul        (a b : Expr)
  | sub        (a b : Expr)
  | div        (a b : Expr)
  | sdiv       (a b : Expr)
  | mod_       (a b : Expr)
  | smod_      (a b : Expr)
  | addmod     (a b n : Expr)
  | mulmod     (a b n : Expr)
  | signExtend (a b : Expr)
  -- Comparison
  | lt         (a b : Expr)
  | gt         (a b : Expr)
  | slt        (a b : Expr)
  | sgt        (a b : Expr)
  | eq_        (a b : Expr)
  | isZero     (a : Expr)
  -- Bitwise
  | and_       (a b : Expr)
  | or_        (a b : Expr)
  | xor_       (a b : Expr)
  | not_       (a : Expr)
  | byte_      (i x : Expr)
  | shl_       (sh x : Expr)
  | shr_       (sh x : Expr)
  | sar_       (sh x : Expr)
  deriving Repr, DecidableEq, Inhabited

/-- Evaluate an `Expr` against the entry stack `es` (`stackAt d`
    out of range evaluates to 0; the soundness theorem never
    exercises that default because `execOp` success implies the
    entry stack was deep enough). Each arm mirrors the value
    expression of the matching `IR.execOp` arm. -/
def eval : Expr → List U256 → U256
  | .const v,    _  => v
  | .stackAt n,  es => es.getD n 0
  | .add a b,    es => eval a es + eval b es
  | .mul a b,    es => eval a es * eval b es
  | .sub a b,    es => eval a es - eval b es
  | .div a b,    es =>
      if eval b es = 0 then 0 else BitVec.udiv (eval a es) (eval b es)
  | .sdiv a b,   es =>
      if eval b es = 0 then 0 else BitVec.sdiv (eval a es) (eval b es)
  | .mod_ a b,   es =>
      if eval b es = 0 then 0 else BitVec.umod (eval a es) (eval b es)
  | .smod_ a b,  es =>
      if eval b es = 0 then 0 else BitVec.srem (eval a es) (eval b es)
  | .addmod a b n, es =>
      if eval n es = 0 then 0
      else Evm.U256.ofNat (((eval a es).toNat + (eval b es).toNat) % (eval n es).toNat)
  | .mulmod a b n, es =>
      if eval n es = 0 then 0
      else Evm.U256.ofNat (((eval a es).toNat * (eval b es).toNat) % (eval n es).toNat)
  | .signExtend a b, es => Instructions.signExtend (eval a es) (eval b es)
  | .lt a b,     es => if eval a es < eval b es then 1 else 0
  | .gt a b,     es => if eval a es > eval b es then 1 else 0
  | .slt a b,    es => if BitVec.slt (eval a es) (eval b es) then 1 else 0
  | .sgt a b,    es => if BitVec.slt (eval b es) (eval a es) then 1 else 0
  | .eq_ a b,    es => if eval a es = eval b es then 1 else 0
  | .isZero a,   es => if eval a es = 0 then 1 else 0
  | .and_ a b,   es => eval a es &&& eval b es
  | .or_ a b,    es => eval a es ||| eval b es
  | .xor_ a b,   es => eval a es ^^^ eval b es
  | .not_ a,     es => ~~~ (eval a es)
  | .byte_ i x,  es => Instructions.byteOf (eval i es) (eval x es)
  | .shl_ sh x,  es =>
      if (eval sh es).toNat ≥ 256 then 0
      else Evm.U256.ofNat ((eval x es).toNat <<< (eval sh es).toNat)
  | .shr_ sh x,  es =>
      if (eval sh es).toNat ≥ 256 then 0
      else Evm.U256.ofNat ((eval x es).toNat >>> (eval sh es).toNat)
  | .sar_ sh x,  es =>
      if (eval sh es).toNat ≥ 256 then
        if (eval x es).toNat ≥ (1 <<< 255)
        then Evm.U256.ofNat ((1 <<< 256) - 1) else 0
      else if ¬ (eval x es).toNat ≥ (1 <<< 255) then
        Evm.U256.ofNat ((eval x es).toNat >>> (eval sh es).toNat)
      else
        Evm.U256.ofNat (((eval x es).toNat >>> (eval sh es).toNat) |||
          (((1 <<< 256) - 1) ^^^ ((1 <<< (256 - (eval sh es).toNat)) - 1)))

/-! ## Symbolic stack

    A `SymStack` is the compiler's view of the operand stack
    mid-chunk: an explicit prefix of `Expr`s on top of the (not
    yet inspected) remainder of the entry stack. `consumed` counts
    how many entry-stack slots the explicit prefix has absorbed,
    so the remainder is `entry.drop consumed`. `pop` is total:
    popping past the explicit prefix manufactures the
    `stackAt consumed` leaf and advances `consumed`. -/

structure SymStack where
  exprs    : List Expr := []
  consumed : Nat := 0
  deriving Repr, Inhabited

namespace SymStack

def pop : SymStack → Expr × SymStack
  | ⟨e :: tl, c⟩ => (e, ⟨tl, c⟩)
  | ⟨[], c⟩      => (.stackAt c, ⟨[], c + 1⟩)

def push (ss : SymStack) (e : Expr) : SymStack :=
  ⟨e :: ss.exprs, ss.consumed⟩

/-- Read depth `n` (0 = current top) without consuming. -/
def peek (ss : SymStack) (n : Nat) : Expr :=
  match ss.exprs[n]? with
  | some e => e
  | none   => .stackAt (ss.consumed + (n - ss.exprs.length))

/-- Pop `k` expressions (top first). Total, like `pop`. -/
def popN : Nat → SymStack → List Expr × SymStack
  | 0,     ss => ([], ss)
  | k + 1, ss =>
      let p := ss.pop
      let q := popN k p.2
      (p.1 :: q.1, q.2)

/-- Push a list of expressions; the head of the list ends up on top. -/
def pushAll (ss : SymStack) : List Expr → SymStack
  | []      => ss
  | e :: tl => (ss.pushAll tl).push e

/-- The concrete stack a `SymStack` stands for, given the entry
    stack `es`: evaluated explicit prefix on top of the unconsumed
    remainder of `es`. -/
def denote (ss : SymStack) (es : List U256) : List U256 :=
  ss.exprs.map (eval · es) ++ es.drop ss.consumed

end SymStack

/-! ## Symbolic execution of one op -/

def symUnary (mk : Expr → Expr) (ss : SymStack) : SymStack :=
  let p := ss.pop
  p.2.push (mk p.1)

def symBinary (mk : Expr → Expr → Expr) (ss : SymStack) : SymStack :=
  let p := ss.pop
  let q := p.2.pop
  q.2.push (mk p.1 q.1)

def symTernary (mk : Expr → Expr → Expr → Expr) (ss : SymStack) : SymStack :=
  let p := ss.pop
  let q := p.2.pop
  let r := q.2.pop
  r.2.push (mk p.1 q.1 r.1)

/-- Run one IR op on the symbolic stack. `none` means the op's
    value is not representable over the entry stack (state, memory,
    context, EXP's dynamic gas, KECCAK256, GAS, …) and the emitter
    must flush to the materialized stack at this op. -/
def symStep (op : Op) (ss : SymStack) : Option SymStack :=
  match op with
  | .push _ v   => some (ss.push (.const v))
  | .push0      => some (ss.push (.const 0))
  | .pc v       => some (ss.push (.const (Evm.U256.ofNat v)))
  | .jumpdest   => some ss
  | .pop        => some (ss.pop).2
  | .add        => some (symBinary .add ss)
  | .mul        => some (symBinary .mul ss)
  | .sub        => some (symBinary .sub ss)
  | .div        => some (symBinary .div ss)
  | .sdiv       => some (symBinary .sdiv ss)
  | .mod        => some (symBinary .mod_ ss)
  | .smod       => some (symBinary .smod_ ss)
  | .addmod     => some (symTernary .addmod ss)
  | .mulmod     => some (symTernary .mulmod ss)
  | .signextend => some (symBinary .signExtend ss)
  | .lt         => some (symBinary .lt ss)
  | .gt         => some (symBinary .gt ss)
  | .slt        => some (symBinary .slt ss)
  | .sgt        => some (symBinary .sgt ss)
  | .eq         => some (symBinary .eq_ ss)
  | .iszero     => some (symUnary .isZero ss)
  | .and_       => some (symBinary .and_ ss)
  | .or_        => some (symBinary .or_ ss)
  | .xor_       => some (symBinary .xor_ ss)
  | .not_       => some (symUnary .not_ ss)
  | .byte       => some (symBinary .byte_ ss)
  | .shl        => some (symBinary .shl_ ss)
  | .shr        => some (symBinary .shr_ ss)
  | .sar        => some (symBinary .sar_ ss)
  -- DUP1..DUP16 carry n ∈ {1..16}; a hypothetical `dup 0` would alias
  -- `dup 1` concretely (peek (0 - 1) = peek 0) but is not an entry read
  -- the region builder's `need` accounts for, so refuse it like `swap 0`.
  | .dup 0      => none
  | .dup n      => some (ss.push (ss.peek (n - 1)))
  -- SWAP1..SWAP16 carry n ∈ {1..16}; a hypothetical `swap 0` would
  -- alias `swap 1` concretely but not symbolically, so refuse it.
  | .swap 0     => none
  | .swap (n+1) =>
      let p := ss.popN (n + 2)
      let top := p.1.headD (.const 0)
      let rest := p.1.tail
      some (p.2.pushAll (rest.getD n (.const 0) :: rest.set n top))
  | _ => none

/-! ## Shape anchors

    Each covered `execOp` arm is definitionally one of four shapes.
    The `execOp_*_shape` theorems are `rfl`: they re-elaborate the
    arm against the shape on every build, so a semantic change to
    `execOp` breaks the anchor instead of silently outrunning the
    symbolic semantics. `eval` is tied to the same shapes through
    the `hmk` side conditions of the generic soundness lemmas,
    which are also discharged by `rfl`. -/

def pushExec (v : U256) (evm : Evm) : Except Exception Evm := do
  let s ← Stack.push evm.stack v
  return { evm with stack := s }

def popExec (evm : Evm) : Except Exception Evm := do
  let (_, s) ← Stack.pop evm.stack
  return { evm with stack := s }

def unaryExec (f : U256 → U256) (evm : Evm) : Except Exception Evm := do
  let (a, s) ← Stack.pop evm.stack
  let s ← Stack.push s (f a)
  return { evm with stack := s }

def binaryExec (f : U256 → U256 → U256) (evm : Evm) : Except Exception Evm := do
  let (a, b, s) ← Stack.pop2 evm.stack
  let s ← Stack.push s (f a b)
  return { evm with stack := s }

def ternaryExec (f : U256 → U256 → U256 → U256) (evm : Evm) :
    Except Exception Evm := do
  let (a, b, n, s) ← Stack.pop3 evm.stack
  let s ← Stack.push s (f a b n)
  return { evm with stack := s }

theorem execOp_push_shape (evm : Evm) (n : Nat) (v : U256) :
    execOp evm (.push n v) = pushExec v evm := rfl
theorem execOp_push0_shape (evm : Evm) :
    execOp evm .push0 = pushExec 0 evm := rfl
theorem execOp_pc_shape (evm : Evm) (v : Nat) :
    execOp evm (.pc v) = pushExec (Evm.U256.ofNat v) evm := rfl
theorem execOp_pop_shape (evm : Evm) :
    execOp evm .pop = popExec evm := rfl
theorem execOp_add_shape (evm : Evm) :
    execOp evm .add = binaryExec (· + ·) evm := rfl
theorem execOp_mul_shape (evm : Evm) :
    execOp evm .mul = binaryExec (· * ·) evm := rfl
theorem execOp_sub_shape (evm : Evm) :
    execOp evm .sub = binaryExec (· - ·) evm := rfl
theorem execOp_div_shape (evm : Evm) :
    execOp evm .div =
      binaryExec (fun a b => if b = 0 then 0 else BitVec.udiv a b) evm := rfl
theorem execOp_sdiv_shape (evm : Evm) :
    execOp evm .sdiv =
      binaryExec (fun a b => if b = 0 then 0 else BitVec.sdiv a b) evm := rfl
theorem execOp_mod_shape (evm : Evm) :
    execOp evm .mod =
      binaryExec (fun a b => if b = 0 then 0 else BitVec.umod a b) evm := rfl
theorem execOp_smod_shape (evm : Evm) :
    execOp evm .smod =
      binaryExec (fun a b => if b = 0 then 0 else BitVec.srem a b) evm := rfl
theorem execOp_addmod_shape (evm : Evm) :
    execOp evm .addmod =
      ternaryExec (fun a b n =>
        if n = 0 then 0
        else Evm.U256.ofNat ((a.toNat + b.toNat) % n.toNat)) evm := rfl
theorem execOp_mulmod_shape (evm : Evm) :
    execOp evm .mulmod =
      ternaryExec (fun a b n =>
        if n = 0 then 0
        else Evm.U256.ofNat ((a.toNat * b.toNat) % n.toNat)) evm := rfl
theorem execOp_signextend_shape (evm : Evm) :
    execOp evm .signextend = binaryExec Instructions.signExtend evm := rfl
theorem execOp_lt_shape (evm : Evm) :
    execOp evm .lt =
      binaryExec (fun a b => if a < b then 1 else 0) evm := rfl
theorem execOp_gt_shape (evm : Evm) :
    execOp evm .gt =
      binaryExec (fun a b => if a > b then 1 else 0) evm := rfl
theorem execOp_slt_shape (evm : Evm) :
    execOp evm .slt =
      binaryExec (fun a b => if BitVec.slt a b then 1 else 0) evm := rfl
theorem execOp_sgt_shape (evm : Evm) :
    execOp evm .sgt =
      binaryExec (fun a b => if BitVec.slt b a then 1 else 0) evm := rfl
theorem execOp_eq_shape (evm : Evm) :
    execOp evm .eq =
      binaryExec (fun a b => if a = b then 1 else 0) evm := rfl
theorem execOp_iszero_shape (evm : Evm) :
    execOp evm .iszero =
      unaryExec (fun a => if a = 0 then 1 else 0) evm := rfl
theorem execOp_and_shape (evm : Evm) :
    execOp evm .and_ = binaryExec (· &&& ·) evm := rfl
theorem execOp_or_shape (evm : Evm) :
    execOp evm .or_ = binaryExec (· ||| ·) evm := rfl
theorem execOp_xor_shape (evm : Evm) :
    execOp evm .xor_ = binaryExec (· ^^^ ·) evm := rfl
theorem execOp_not_shape (evm : Evm) :
    execOp evm .not_ = unaryExec (fun a => ~~~ a) evm := rfl
theorem execOp_byte_shape (evm : Evm) :
    execOp evm .byte = binaryExec Instructions.byteOf evm := rfl
theorem execOp_shl_shape (evm : Evm) :
    execOp evm .shl =
      binaryExec (fun shift value =>
        if shift.toNat ≥ 256 then 0
        else Evm.U256.ofNat (value.toNat <<< shift.toNat)) evm := rfl
theorem execOp_shr_shape (evm : Evm) :
    execOp evm .shr =
      binaryExec (fun shift value =>
        if shift.toNat ≥ 256 then 0
        else Evm.U256.ofNat (value.toNat >>> shift.toNat)) evm := rfl
theorem execOp_sar_shape (evm : Evm) :
    execOp evm .sar =
      binaryExec (fun shift value =>
        if shift.toNat ≥ 256 then
          if value.toNat ≥ (1 <<< 255)
          then Evm.U256.ofNat ((1 <<< 256) - 1) else 0
        else if ¬ value.toNat ≥ (1 <<< 255) then
          Evm.U256.ofNat (value.toNat >>> shift.toNat)
        else
          Evm.U256.ofNat ((value.toNat >>> shift.toNat) |||
            (((1 <<< 256) - 1) ^^^
             ((1 <<< (256 - shift.toNat)) - 1)))) evm := rfl

/-! ## Denotation lemmas -/

private theorem bind_eq_ok {α β : Type} {x : Except Exception α}
    {f : α → Except Exception β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, by simpa [bind, Except.bind] using h⟩

private theorem drop_eq_cons {c : Nat} {es rest : List U256} {v : U256}
    (h : es.drop c = v :: rest) :
    es.getD c 0 = v ∧ es.drop (c + 1) = rest := by
  induction c generalizing es with
  | zero =>
      cases es with
      | nil => simp at h
      | cons x xs =>
          simp only [List.drop_zero] at h
          cases h
          exact ⟨rfl, rfl⟩
  | succ k ih =>
      cases es with
      | nil => simp at h
      | cons x xs =>
          simp only [List.drop_succ_cons] at h
          exact ih h

/-- `(l.set m v).map f` commutes; private to dodge name drift in core. -/
private theorem map_set {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat) (a : α),
      (l.set i a).map f = (l.map f).set i (f a)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | x :: xs, i + 1, a => congrArg (f x :: ·) (map_set f xs i a)

/-- Setting an index inside the taken prefix commutes with
    `take_append_drop`. -/
private theorem set_take_append_drop {α : Type} :
    ∀ (l : List α) (k m : Nat) (v : α), m < k →
      (l.take k).set m v ++ l.drop k = l.set m v
  | [], _, _, _, _ => by simp
  | _ :: _, 0, m, _, h => absurd h (Nat.not_lt_zero m)
  | x :: xs, k + 1, 0, v, _ => by
      show v :: (xs.take k ++ xs.drop k) = v :: xs
      exact congrArg (v :: ·) (List.take_append_drop k xs)
  | x :: xs, k + 1, m + 1, v, h => by
      show x :: ((xs.take k).set m v ++ xs.drop k) = x :: xs.set m v
      exact congrArg (x :: ·)
        (set_take_append_drop xs k m v (Nat.lt_of_succ_lt_succ h))

namespace SymStack

theorem push_denote (ss : SymStack) (e : Expr) (es : List U256) :
    (ss.push e).denote es = eval e es :: ss.denote es := rfl

theorem pop_denote {ss : SymStack} {es : List U256} {v : U256}
    {rest : List U256} (h : ss.denote es = v :: rest) :
    eval (ss.pop).1 es = v ∧ (ss.pop).2.denote es = rest := by
  obtain ⟨exprs, c⟩ := ss
  cases exprs with
  | nil =>
      simp only [denote, List.map_nil, List.nil_append] at h
      obtain ⟨h1, h2⟩ := drop_eq_cons h
      exact ⟨h1, by simpa [pop, denote] using h2⟩
  | cons e tl =>
      simp only [denote, List.map_cons, List.cons_append,
                 List.cons.injEq] at h
      exact ⟨h.1, by simpa [pop, denote] using h.2⟩

theorem peek_denote {ss : SymStack} {es : List U256} {n : Nat} {v : U256}
    (h : (ss.denote es)[n]? = some v) :
    eval (ss.peek n) es = v := by
  obtain ⟨exprs, c⟩ := ss
  simp only [denote] at h
  by_cases hn : n < exprs.length
  · rw [List.getElem?_append_left (by simpa using hn)] at h
    rw [List.getElem?_map] at h
    cases he : exprs[n]? with
    | none => rw [he] at h; simp at h
    | some e =>
        rw [he] at h
        simp only [Option.map_some, Option.some.injEq] at h
        simp [peek, he, h]
  · have hge : exprs.length ≤ n := Nat.le_of_not_lt hn
    rw [List.getElem?_append_right (by simpa using hge)] at h
    have he : exprs[n]? = none := List.getElem?_eq_none hge
    rw [List.getElem?_drop] at h
    simp only [peek, he, List.length_map] at h ⊢
    simp [eval, List.getD, h]

theorem popN_denote {k : Nat} {ss : SymStack} {es vs rest : List U256}
    (hlen : vs.length = k) (h : ss.denote es = vs ++ rest) :
    (ss.popN k).1.map (eval · es) = vs ∧
      (ss.popN k).2.denote es = rest := by
  induction k generalizing ss vs with
  | zero =>
      have hnil : vs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hnil
      simpa [popN] using h
  | succ m ih =>
      cases vs with
      | nil => simp at hlen
      | cons v vtl =>
          simp only [List.cons_append] at h
          obtain ⟨h1, h2⟩ := pop_denote h
          obtain ⟨h3, h4⟩ := ih (by simpa using hlen) h2
          refine ⟨?_, ?_⟩
          · simp [popN, h1, h3]
          · simpa [popN] using h4

theorem pushAll_denote (ss : SymStack) (l : List Expr) (es : List U256) :
    (ss.pushAll l).denote es = l.map (eval · es) ++ ss.denote es := by
  induction l with
  | nil => rfl
  | cons e tl ih => simp [pushAll, push_denote, ih]

end SymStack

/-! ## Generic shape soundness

    One lemma per shape. The `hmk` premise ties the `Expr`
    constructor's `eval` arm to the same value function `f` the
    shape anchor pinned `execOp` to; at every use site it is
    discharged by `rfl`. Success of the concrete step is a
    hypothesis: the stage-2 emitter guards underflow with one
    chunk-entry depth check and overflow at flush against the
    region's peak depth. -/

theorem pushExec_sound {v : U256} {e : Expr} {evm evm' : Evm}
    {ss : SymStack} {es : List U256}
    (he : eval e es = v)
    (hstack : evm.stack = ss.denote es)
    (hexec : pushExec v evm = .ok evm') :
    evm' = { evm with stack := (ss.push e).denote es } := by
  unfold pushExec at hexec
  obtain ⟨s', hp, hr⟩ := bind_eq_ok hexec
  obtain ⟨-, rfl⟩ := (Stack.push_eq_ok_iff _ _ _).mp hp
  simp only [pure, Except.pure, Except.ok.injEq] at hr
  subst hr
  simp [SymStack.push_denote, he, hstack]

theorem popExec_sound {evm evm' : Evm} {ss : SymStack} {es : List U256}
    (hstack : evm.stack = ss.denote es)
    (hexec : popExec evm = .ok evm') :
    evm' = { evm with stack := (ss.pop).2.denote es } := by
  unfold popExec at hexec
  obtain ⟨⟨a, s⟩, hp, hr⟩ := bind_eq_ok hexec
  have hs : evm.stack = a :: s := (Stack.pop_eq_ok_iff _ _ _).mp hp
  simp only [pure, Except.pure, Except.ok.injEq] at hr
  subst hr
  rw [hstack] at hs
  obtain ⟨-, h2⟩ := SymStack.pop_denote hs
  rw [h2]

theorem unaryExec_sound {f : U256 → U256} {mk : Expr → Expr}
    (hmk : ∀ a es, eval (mk a) es = f (eval a es))
    {evm evm' : Evm} {ss : SymStack} {es : List U256}
    (hstack : evm.stack = ss.denote es)
    (hexec : unaryExec f evm = .ok evm') :
    evm' = { evm with stack := (symUnary mk ss).denote es } := by
  unfold unaryExec at hexec
  obtain ⟨⟨a, s₀⟩, hp, hexec⟩ := bind_eq_ok hexec
  obtain ⟨s₁, hq, hr⟩ := bind_eq_ok hexec
  have hs : evm.stack = a :: s₀ := (Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨-, rfl⟩ := (Stack.push_eq_ok_iff _ _ _).mp hq
  simp only [pure, Except.pure, Except.ok.injEq] at hr
  subst hr
  rw [hstack] at hs
  obtain ⟨h1, h2⟩ := SymStack.pop_denote hs
  simp [symUnary, SymStack.push_denote, hmk, h1, h2]

theorem binaryExec_sound {f : U256 → U256 → U256} {mk : Expr → Expr → Expr}
    (hmk : ∀ a b es, eval (mk a b) es = f (eval a es) (eval b es))
    {evm evm' : Evm} {ss : SymStack} {es : List U256}
    (hstack : evm.stack = ss.denote es)
    (hexec : binaryExec f evm = .ok evm') :
    evm' = { evm with stack := (symBinary mk ss).denote es } := by
  unfold binaryExec at hexec
  obtain ⟨⟨a, b, s₀⟩, hp, hexec⟩ := bind_eq_ok hexec
  obtain ⟨s₁, hq, hr⟩ := bind_eq_ok hexec
  have hs : evm.stack = a :: b :: s₀ := (Stack.pop2_eq_ok_iff _ _ _ _).mp hp
  obtain ⟨-, rfl⟩ := (Stack.push_eq_ok_iff _ _ _).mp hq
  simp only [pure, Except.pure, Except.ok.injEq] at hr
  subst hr
  rw [hstack] at hs
  obtain ⟨h1, h2⟩ := SymStack.pop_denote hs
  obtain ⟨h3, h4⟩ := SymStack.pop_denote h2
  simp [symBinary, SymStack.push_denote, hmk, h1, h3, h4]

theorem ternaryExec_sound
    {f : U256 → U256 → U256 → U256} {mk : Expr → Expr → Expr → Expr}
    (hmk : ∀ a b n es,
      eval (mk a b n) es = f (eval a es) (eval b es) (eval n es))
    {evm evm' : Evm} {ss : SymStack} {es : List U256}
    (hstack : evm.stack = ss.denote es)
    (hexec : ternaryExec f evm = .ok evm') :
    evm' = { evm with stack := (symTernary mk ss).denote es } := by
  unfold ternaryExec at hexec
  obtain ⟨⟨a, b, n, s₀⟩, hp, hexec⟩ := bind_eq_ok hexec
  obtain ⟨s₁, hq, hr⟩ := bind_eq_ok hexec
  have hs : evm.stack = a :: b :: n :: s₀ := (Stack.pop3_eq_ok_iff _ _ _ _ _).mp hp
  obtain ⟨-, rfl⟩ := (Stack.push_eq_ok_iff _ _ _).mp hq
  simp only [pure, Except.pure, Except.ok.injEq] at hr
  subst hr
  rw [hstack] at hs
  obtain ⟨h1, h2⟩ := SymStack.pop_denote hs
  obtain ⟨h3, h4⟩ := SymStack.pop_denote h2
  obtain ⟨h5, h6⟩ := SymStack.pop_denote h4
  simp [symTernary, SymStack.push_denote, hmk, h1, h3, h5, h6]

/-! ## DUP / SWAP soundness (proved against `execOp` directly) -/

theorem dup_sound {n : Nat} {evm evm' : Evm} {ss : SymStack} {es : List U256}
    (hstack : evm.stack = ss.denote es)
    (hexec : execOp evm (.dup n) = .ok evm') :
    evm' = { evm with stack := (ss.push (ss.peek (n - 1))).denote es } := by
  simp only [execOp] at hexec
  obtain ⟨s', hd, hr⟩ := bind_eq_ok hexec
  simp only [pure, Except.pure, Except.ok.injEq] at hr
  subst hr
  unfold Stack.dup at hd
  obtain ⟨v, hpk, hpu⟩ := bind_eq_ok hd
  have hv : evm.stack[n - 1]? = some v := by
    unfold Stack.peek at hpk
    cases hg : evm.stack[n - 1]? with
    | none => rw [hg] at hpk; simp at hpk
    | some w =>
        rw [hg] at hpk
        simp only [Except.ok.injEq] at hpk
        rw [hpk]
  obtain ⟨-, rfl⟩ := (Stack.push_eq_ok_iff _ _ _).mp hpu
  rw [hstack] at hv
  have hpkd := SymStack.peek_denote hv
  simp [SymStack.push_denote, hpkd, hstack]

theorem swap_sound {n : Nat} {evm evm' : Evm} {ss ss' : SymStack}
    {es : List U256}
    (hstep : symStep (.swap n) ss = some ss')
    (hstack : evm.stack = ss.denote es)
    (hexec : execOp evm (.swap n) = .ok evm') :
    evm' = { evm with stack := ss'.denote es } := by
  cases n with
  | zero => simp [symStep] at hstep
  | succ m =>
  simp only [symStep, Option.some.injEq] at hstep
  simp only [execOp] at hexec
  obtain ⟨s', hsw, hr⟩ := bind_eq_ok hexec
  simp only [pure, Except.pure, Except.ok.injEq] at hr
  subst hr
  unfold Stack.swap at hsw
  rcases hst : evm.stack with _ | ⟨top, crest⟩
  · rw [hst] at hsw; simp at hsw
  rw [hst] at hsw
  simp only [Nat.add_sub_cancel] at hsw
  rcases hro : crest[m]? with _ | other
  · rw [hro] at hsw; simp at hsw
  rw [hro] at hsw
  simp only [Except.ok.injEq] at hsw
  subst hsw
  -- index bound from the successful lookup
  have hm : m < crest.length := by
    cases Nat.lt_or_ge m crest.length with
    | inl h => exact h
    | inr h =>
        rw [List.getElem?_eq_none h] at hro
        simp at hro
  -- split the concrete stack at the swap window
  have hsplit : ss.denote es =
      (top :: crest.take (m + 1)) ++ crest.drop (m + 1) := by
    rw [← hstack, hst]
    simp [List.take_append_drop]
  have hlen : (top :: crest.take (m + 1)).length = m + 2 := by
    simp [List.length_take]; omega
  obtain ⟨hmap, hrest⟩ := SymStack.popN_denote hlen hsplit
  rcases hxe : (ss.popN (m + 2)).1 with _ | ⟨e0, etl⟩
  · rw [hxe] at hmap; simp at hmap
  rw [hxe] at hmap
  simp only [List.map_cons, List.cons.injEq] at hmap
  obtain ⟨he0, hetl⟩ := hmap
  -- the expression standing for the swapped-in value
  have htake : (crest.take (m + 1))[m]? = some other := by
    have hlt : m < (crest.take (m + 1)).length := by
      simp [List.length_take]; omega
    rw [← List.getElem?_append_left (l₂ := crest.drop (m + 1)) hlt,
        List.take_append_drop]
    exact hro
  have hmm : (etl.map (eval · es))[m]? = some other := by
    rw [hetl]; exact htake
  rw [List.getElem?_map] at hmm
  rcases hem : etl[m]? with _ | em
  · rw [hem] at hmm; simp at hmm
  rw [hem] at hmm
  simp only [Option.map_some, Option.some.injEq] at hmm
  -- compute the symbolic denotation
  have hden : ss'.denote es = other :: crest.set m top := by
    rw [← hstep, SymStack.pushAll_denote, hxe]
    simp only [List.headD_cons, List.tail_cons, List.map_cons,
               List.cons_append]
    rw [hrest]
    simp only [List.getD, hem, Option.getD_some]
    rw [hmm, map_set, hetl, he0,
        set_take_append_drop crest (m + 1) m top (Nat.lt_succ_self m)]
  rw [hden]

/-! ## The bridge: `symStep` refines `execOp` on the stack -/

/-- Master soundness theorem (the `eval_sound` bridge of issue #11
    stage 1). If the symbolic step covers `op` and the concrete
    stack is the denotation of the symbolic one, then a SUCCESSFUL
    concrete step changes nothing but the stack, and the new stack
    is the denotation of the new symbolic stack. Covered ops are
    stack-pure, so gas/memory/state equality falls out of the same
    record update. -/
theorem symStep_sound {op : Op} {ss ss' : SymStack} {es : List U256}
    {evm evm' : Evm}
    (hstep : symStep op ss = some ss')
    (hstack : evm.stack = ss.denote es)
    (hexec : execOp evm op = .ok evm') :
    evm' = { evm with stack := ss'.denote es } := by
  cases op
  case push n v =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_push_shape] at hexec
    exact pushExec_sound rfl hstack hexec
  case push0 =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_push0_shape] at hexec
    exact pushExec_sound rfl hstack hexec
  case pc v =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_pc_shape] at hexec
    exact pushExec_sound rfl hstack hexec
  case jumpdest =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    have h : evm = evm' := by
      simpa [execOp, pure, Except.pure] using hexec
    subst h
    rw [← hstack]
  case pop =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_pop_shape] at hexec
    exact popExec_sound hstack hexec
  case add =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_add_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case mul =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_mul_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case sub =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_sub_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case div =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_div_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case sdiv =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_sdiv_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case mod =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_mod_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case smod =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_smod_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case addmod =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_addmod_shape] at hexec
    exact ternaryExec_sound (fun _ _ _ _ => rfl) hstack hexec
  case mulmod =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_mulmod_shape] at hexec
    exact ternaryExec_sound (fun _ _ _ _ => rfl) hstack hexec
  case signextend =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_signextend_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case lt =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_lt_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case gt =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_gt_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case slt =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_slt_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case sgt =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_sgt_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case eq =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_eq_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case iszero =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_iszero_shape] at hexec
    exact unaryExec_sound (fun _ _ => rfl) hstack hexec
  case and_ =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_and_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case or_ =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_or_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case xor_ =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_xor_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case not_ =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_not_shape] at hexec
    exact unaryExec_sound (fun _ _ => rfl) hstack hexec
  case byte =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_byte_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case shl =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_shl_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case shr =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_shr_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case sar =>
    simp only [symStep, Option.some.injEq] at hstep
    subst hstep
    rw [execOp_sar_shape] at hexec
    exact binaryExec_sound (fun _ _ _ => rfl) hstack hexec
  case dup n =>
    cases n with
    | zero => simp [symStep] at hstep
    | succ n =>
      simp only [symStep, Option.some.injEq] at hstep
      subst hstep
      exact dup_sound hstack hexec
  case swap n => exact swap_sound hstep hstack hexec
  all_goals simp [symStep] at hstep

end Evm.IR.SymExpr
