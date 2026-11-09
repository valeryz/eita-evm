/-
  Evm.SpuriousDragon.Spec.Refinement — proofs that the SD Effect
  interpreter refines the SD Spec relations.

  SD introduces only state-machine deltas:

    * `CodeSizeCap.lean` — EIP-170 max-deployed-code cap (24576 bytes).
        Relations: `IsCodeSizeAllowed`, `IsCreateCodeSizeRevertStep`.
    * `SigChainId.lean` — EIP-155 chainId-augmented signing.
        Relations: `IsRecoverSenderStep`, `IsRecoverSenderEip155`,
                   `IsRecoverSenderLegacy`.
    * `SweepEmpty.lean` — EIP-158/161 end-of-tx empty-account pruning.
        Relations: `IsSweepOneStep`, `IsSweepEmptyStep`.
    * `TouchAccount.lean` — EIP-161 touched-set tracking.
        Relation: `IsTouchAccountStep`.

  All four are state-machine relations on `State` / `Evm` /
  `Transaction`. Per the SPEC-METHODOLOGY each gets a `sorry`-deferred
  soundness theorem stating the obligation against the SD impl.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.SpuriousDragon.Spec.CodeSizeCap
import Evm.SpuriousDragon.Spec.SigChainId
import Evm.SpuriousDragon.Spec.SweepEmpty
import Evm.SpuriousDragon.Spec.TouchAccount
import Evm.SpuriousDragon.Fork

namespace Evm.SpuriousDragon.Spec.Refinement

open Evm.Frontier (State Transaction)
open Evm.Frontier.Vm
open Evm.SpuriousDragon.Spec

/-! ## EIP-170 deployed-code cap refinement -/

set_option backward.isDefEq.respectTransparency false in
/-- EIP-170: `Create.start` then `Create.resume` at Spurious Dragon's rules (ordinal 4,
    `SpuriousDragon.Vm.Effect`'s CREATE) on a clean init run whose output exceeds
    24576 bytes land on `IsCreateCodeSizeRevertStep` of the pre-bump frame: the
    creation fails, only the creator's nonce bump survives, 0 is pushed. EELS
    `forks/spurious_dragon/vm/interpreter.py::process_create_message` 177-193. Same
    pattern as `Homestead.Spec.Refinement.createDepositRevert_sound`. -/
theorem createCodeSizeRevert_sound (evm subEvm parent' : Evm) (value : Evm.U256)
    (initCode : Evm.Bytes) (newAddr : Evm.Address) (base : Nat)
    (p : Evm) (m : Message) (st : Evm.Frontier.State)
    (hstart : Evm.Frontier.Vm.Create.start (Evm.Frontier.Vm.Create.Rules.ofOrd 4) evm value
      initCode newAddr base = .run p m st)
    (hres : Evm.Frontier.Vm.Create.resume (Evm.Frontier.Vm.Create.Rules.ofOrd 4) p newAddr
      (.ok subEvm) = .ok parent')
    (sender : Evm.Address) (senderAccNonce gasLeft : Nat) (mem : Memory) (s : Stack) (pc : Nat)
    (hsender : sender = evm.message.currentTarget)
    (hnonce : senderAccNonce = (evm.env.state.getAccount sender).nonce)
    (hg : gasLeft = p.gasLeft) (hm : mem = evm.memory) (hs' : s = evm.stack) (hpc : pc = evm.pc)
    (hrev : ¬ subEvm.reverted) (hhalt : subEvm.halted)
    (hsize : subEvm.output.size > maxCodeSize) :
    IsCreateCodeSizeRevertStep evm subEvm sender senderAccNonce gasLeft mem s pc parent' := by
  subst hsender hnonce hg hm hs' hpc
  have hsz : subEvm.output.size > Evm.SpuriousDragon.Vm.Gas.maxCodeSize := hsize
  simp only [Evm.Frontier.Vm.Create.start, Evm.Frontier.Vm.Create.Rules.ofOrd] at hstart
  split at hstart
  · cases hstart
  split at hstart
  · simp at *
  split at hstart
  · cases hstart
  split at hstart
  · cases hstart
  cases hstart
  by_cases hd : subEvm.gasLeft < Gas.codeDeposit * subEvm.output.size
  · simp only [Evm.Frontier.Vm.Create.resume, Evm.Frontier.Vm.Create.Rules.ofOrd, hrev, hd,
      Bool.false_eq_true, ite_false, ite_true, decide_eq_true_eq, Evm.Frontier.Vm.Create.push,
      Stack.push] at hres
    by_cases hs : evm.stack.length ≥ stackLimit
    · simp [hs, Functor.map, Except.map] at hres
    · simp only [hs, ite_false] at hres
      refine ⟨hrev, hhalt, hsize, by omega, ?_⟩
      cases hres
      simp
  · simp only [Evm.Frontier.Vm.Create.resume, Evm.Frontier.Vm.Create.Rules.ofOrd, hrev, hd, hsz,
      Bool.false_eq_true, ite_false, decide_eq_true_eq, Evm.Frontier.Vm.Create.push,
      Stack.push] at hres
    by_cases hs : evm.stack.length ≥ stackLimit
    · simp [hs, Functor.map, Except.map] at hres
    · simp only [hs, ite_false] at hres
      refine ⟨hrev, hhalt, hsize, by omega, ?_⟩
      cases hres
      simp

/-! ## EIP-155 signing refinement -/

/-- Homestead's literal low-s bound is EELS's `SECP256K1N // 2`. -/
theorem secp256k1nHalf_eq :
    Evm.Homestead.Utils.secp256k1nHalf = Evm.Frontier.Vm.Tx.secp256k1n / 2 := by
  unfold Evm.Homestead.Utils.secp256k1nHalf Evm.Frontier.Vm.Tx.secp256k1n; rfl

/-- Sender recovery at Spurious Dragon refines EELS `recover_sender` (relation
    `IsRecoverSenderStep`, clause by clause), with the curve recovery
    `Evm.Crypto.recover` as the oracle. EELS `forks/spurious_dragon/
    transactions.py::recover_sender` 166-198.

    `ecrecover` is any oracle the implementation's `Evm.Crypto.recover` agrees with
    (`hImpl`). Trust: the implementation checks only the low-s bound itself and leaves the
    other signature-range checks EELS states (`0 < r < N`, `0 < s`, `v ∈ {27,28}`
    in the oracle's convention) to the oracle — the hypothesis `hOracle`, the
    secp256k1 recovery contract of `c/ecrecover.c` (libsecp256k1 rejects a
    compact signature with `r` or `s` out of `[1, N)` and a recovery id out of
    `{0, 1}`). It is a hypothesis of this theorem, not an axiom. -/
theorem recoverSender_sound (tx : Transaction) (sender : Evm.Address)
    (ecrecover : Evm.Hash32 → Evm.U256 → Evm.U256 → Evm.U256 → Option Evm.Address)
    (hImpl : ∀ h v r s, Evm.Crypto.recover h v r s = ecrecover h v r s)
    (hOracle : ∀ h v r s a, ecrecover h v r s = some a →
      (v.toNat = 27 ∨ v.toNat = 28) ∧ 0 < r.toNat ∧ r.toNat < Evm.Frontier.Vm.Tx.secp256k1n ∧
      0 < s.toNat) :
    Evm.SpuriousDragon.Utils.recoverSender tx = some sender →
    IsRecoverSenderStep ecrecover tx sender := by
  have hfun : Evm.Crypto.recover = ecrecover := by
    funext h v r s; exact hImpl h v r s
  subst hfun
  intro h
  unfold Evm.SpuriousDragon.Utils.recoverSender at h
  dsimp only at h
  split at h
  · rename_i hv
    split at h
    · exact absurd h (by simp)
    · rename_i hs
      obtain ⟨_, hr0, hrN, hs0⟩ := hOracle _ _ _ _ _ h
      refine ⟨hr0, hrN, hs0, by rw [← secp256k1nHalf_eq]; omega, Or.inr ⟨hv, ?_⟩⟩
      have hv' : (tx.v.toNat - 35) % 2 + 27 = tx.v.toNat - Evm.SpuriousDragon.Utils.chainId * 2 - 35 + 27 := by
        simp only [Evm.SpuriousDragon.Utils.chainId] at hv ⊢; omega
      rw [hv']; exact h
  · rename_i hv
    unfold Evm.Homestead.Utils.recoverSender Evm.Frontier.Utils.recoverSender at h
    split at h
    · exact absurd h (by simp)
    · rename_i hs
      obtain ⟨hv27, hr0, hrN, hs0⟩ := hOracle _ _ _ _ _ h
      exact ⟨hr0, hrN, hs0, by rw [← secp256k1nHalf_eq]; omega, Or.inl ⟨hv27, h⟩⟩

/-! ## EIP-158/161 end-of-tx sweep refinement -/

/-- `Evm.SpuriousDragon.sweepEmptyAccounts` is sound w.r.t.
    `IsSweepEmptyStep`. The impl folds over the touched list; the
    spec relation is its inductive version. -/
theorem sweepEmptyAccounts_sound
    (state : State) (touched : List Evm.Address) :
    IsSweepEmptyStep state touched
      (Evm.SpuriousDragon.sweepEmptyAccounts state touched) := by
  -- The witness theorem already exists in `SweepEmpty.lean` as
  -- `sweepEmptyAccounts_sound`; restate here for the Refinement
  -- module's interface.
  exact Evm.SpuriousDragon.Spec.sweepEmptyAccounts_sound state touched

/-! ## EIP-161 touched-set tracking refinement -/

/-- `Call.touch` (EIP-161's touched-set insert, run on every message's target) is an
    `IsTouchAccountStep` when applied to the frame's environment. EELS
    `forks/spurious_dragon/vm/interpreter.py` 120 (`evm.touched_accounts.add(...)`) and
    `vm/__init__.py` 165. -/
theorem touchAccount_sound (evm evm' : Evm) (addr : Evm.Address) :
    { evm with env := Evm.Frontier.Vm.Call.touch evm.env addr } = evm' →
    IsTouchAccountStep evm addr evm' := by
  intro h; subst h
  unfold IsTouchAccountStep Evm.Frontier.Vm.Call.touch
  split <;> simp_all

/-! ## Notes

    - The `sweepEmptyAccounts_sound` theorem is already proven in
      `SweepEmpty.lean` (modulo its internal `sorry` placeholder).
      Re-exposing it here keeps every fork-level Refinement.lean
      surfacing the inductive soundness obligation for its sweeps.

    - SD's primary new opcode-level deltas are all in the
      trampoline (post-merge / sub-frame setup) — no
      `Vm/Instructions/` files in this fork. The Frontier
      refinement applies unchanged to every step-level opcode. -/

end Evm.SpuriousDragon.Spec.Refinement
