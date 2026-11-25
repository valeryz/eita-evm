import Evm.BaseTypes
import Evm.Crypto.Hash
import Evm.Frontier.State

/-! # Evm/Witness/ReadSet — what a read set is (docs/readset.md)

A read set is a set of pre-state keys such that the execution's result depends on the
pre-state only through the values at those keys: two pre-states that agree on every key of
the set give the same result (gas, status, logs, state diff). This file is the one owner of
that notion; the recorder (`src/evm/readset.lisp`, format in `docs/readset-format.md`) and
the witness design (`docs/witness-design.md` §1.1, §2.2) implement and use it.

* `ReadKey`    — one pre-state key: an account field, a storage slot, or a block hash.
* `Answer k`   — the type of the value a pre-state holds at `k`.
* `Oracle`     — a pre-state seen through its keys (`(k : ReadKey) → Answer k`);
                 `oracleOf` is the spec's: `Frontier.State` + the block-hash window.
* `AgreeOn R`  — two oracles answer every key of `R` alike.
* `Sufficient` — agreement on `R` forces the same outcome.

`Sufficient` is stated over an arbitrary execution `run : σ → β`, its view of the pre-state
`obs : σ → Oracle` and an outcome relation `same : β → β → Prop`. For the EVM the intended
instance is `σ` = the pre-state, `run` = a fork's tx run and `same` = `SameOutcome` (gas,
status, logs, and equal state diffs, since the spec's `State` is a list and not
extensional); that instance needs the oracle-program executor of witness-design §2.3 and is
stated, not proved, in docs/readset.md. -/

namespace Evm.Witness

/-- One key of the pre-state an execution can observe. -/
inductive ReadKey where
  /-- Whether the account is in the state at all (pre-EIP-161 NEW_ACCOUNT, EIP-161
      emptiness, CREATE address collision). -/
  | exists_   (a : Evm.Address)
  | nonce     (a : Evm.Address)
  | balance   (a : Evm.Address)
  /-- The account leaf's code hash (EXTCODEHASH, emptiness): not the bytes. -/
  | codeHash  (a : Evm.Address)
  /-- The code bytes (CALL into the account, EXTCODECOPY, EXTCODESIZE). -/
  | code      (a : Evm.Address)
  | storage   (a : Evm.Address) (slot : Evm.U256)
  /-- The hash of block `n` (BLOCKHASH). -/
  | blockHash (n : Nat)
  deriving DecidableEq, Repr

/-- A read set (per tx, or per block): a finite set of keys, as a list. Order and
    duplicates carry no meaning; only membership is used. -/
abbrev ReadSet := List ReadKey

/-- The type of the value at a key. A block hash outside the window the execution may see
    is `none`. -/
def Answer : ReadKey → Type
  | .exists_ _   => Bool
  | .nonce _     => Nat
  | .balance _   => Evm.U256
  | .codeHash _  => Evm.Bytes
  | .code _      => Evm.Bytes
  | .storage _ _ => Evm.U256
  | .blockHash _ => Option Evm.Hash32

/-- A pre-state seen through its keys. -/
abbrev Oracle := (k : ReadKey) → Answer k

/-- The spec's pre-state as an oracle: the world state plus the block hashes the execution
    may read (`hashes n`, `none` outside the window). -/
def oracleOf (s : Evm.Frontier.State) (hashes : Nat → Option Evm.Hash32) : Oracle
  | .exists_ a   => s.accountExists a
  | .nonce a     => (s.getAccount a).nonce
  | .balance a   => (s.getAccount a).balance
  | .codeHash a  => Evm.Crypto.keccak256Bytes (s.getAccount a).code
  | .code a      => (s.getAccount a).code
  | .storage a k => s.getStorage a k
  | .blockHash n => hashes n

/-- Two oracles answer every key of `R` alike. -/
def AgreeOn (R : ReadSet) (o o' : Oracle) : Prop := ∀ k ∈ R, o k = o' k

/-- **Sufficiency.** `R` is sufficient for `run` at `s` when every pre-state that agrees
    with `s` on `R` gives the same outcome: changing any value outside `R` cannot change
    the result. -/
def Sufficient {σ β : Type} (obs : σ → Oracle) (same : β → β → Prop) (run : σ → β)
    (R : ReadSet) (s : σ) : Prop :=
  ∀ s', AgreeOn R (obs s) (obs s') → same (run s) (run s')

/-! ## AgreeOn -/

namespace AgreeOn

theorem refl (R : ReadSet) (o : Oracle) : AgreeOn R o o := fun _ _ => rfl

theorem symm {R : ReadSet} {o o' : Oracle} (h : AgreeOn R o o') : AgreeOn R o' o :=
  fun k hk => (h k hk).symm

theorem trans {R : ReadSet} {o o' o'' : Oracle} (h : AgreeOn R o o') (h' : AgreeOn R o' o'') :
    AgreeOn R o o'' := fun k hk => (h k hk).trans (h' k hk)

/-- Every pair of oracles agrees on the empty set. -/
theorem nil (o o' : Oracle) : AgreeOn [] o o' := fun _ hk => nomatch hk

/-- Agreement on a superset gives agreement on the subset. -/
theorem mono {R R' : ReadSet} {o o' : Oracle} (hsub : ∀ k ∈ R, k ∈ R') (h : AgreeOn R' o o') :
    AgreeOn R o o' := fun k hk => h k (hsub k hk)

/-- Agreement on a union is agreement on both parts. -/
theorem append_iff {R R' : ReadSet} {o o' : Oracle} :
    AgreeOn (R ++ R') o o' ↔ AgreeOn R o o' ∧ AgreeOn R' o o' := by
  constructor
  · intro h
    exact ⟨fun k hk => h k (List.mem_append_left _ hk), fun k hk => h k (List.mem_append_right _ hk)⟩
  · rintro ⟨h, h'⟩ k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact h k hk
    · exact h' k hk

end AgreeOn

/-! ## Sufficient -/

namespace Sufficient

variable {σ β : Type} {obs : σ → Oracle} {same : β → β → Prop} {run : σ → β}

/-- **Monotonicity.** A superset of a sufficient read set is sufficient. -/
theorem mono {R R' : ReadSet} {s : σ} (hsub : ∀ k ∈ R, k ∈ R')
    (h : Sufficient obs same run R s) : Sufficient obs same run R' s :=
  fun s' hag => h s' (AgreeOn.mono hsub hag)

/-- Adding keys keeps a read set sufficient (either side of a union). -/
theorem append_left {R : ReadSet} (R' : ReadSet) {s : σ}
    (h : Sufficient obs same run R s) : Sufficient obs same run (R ++ R') s :=
  mono (fun _ hk => List.mem_append_left _ hk) h

theorem append_right (R : ReadSet) {R' : ReadSet} {s : σ}
    (h : Sufficient obs same run R' s) : Sufficient obs same run (R ++ R') s :=
  mono (fun _ hk => List.mem_append_right _ hk) h

/-- The empty set is sufficient exactly when the outcome does not depend on the pre-state. -/
theorem nil_iff {s : σ} : Sufficient obs same run [] s ↔ ∀ s', same (run s) (run s') :=
  ⟨fun h s' => h s' (AgreeOn.nil _ _), fun h s' _ => h s'⟩

/-- Sufficiency transfers along agreement: if `R` is sufficient at `s` and `t` agrees with
    `s` on `R`, any `t'` agreeing with `t` on `R` has `run s`'s outcome. -/
theorem agree {R : ReadSet} {s t t' : σ} (h : Sufficient obs same run R s)
    (ht : AgreeOn R (obs s) (obs t)) (ht' : AgreeOn R (obs t) (obs t')) :
    same (run s) (run t') :=
  h t' (ht.trans ht')

/-- Weakening the outcome relation keeps sufficiency (e.g. from the full outcome to its
    gas alone). -/
theorem weaken {same' : β → β → Prop} {R : ReadSet} {s : σ}
    (himp : ∀ b b', same b b' → same' b b') (h : Sufficient obs same run R s) :
    Sufficient obs same' run R s :=
  fun s' hag => himp _ _ (h s' hag)

end Sufficient

end Evm.Witness
