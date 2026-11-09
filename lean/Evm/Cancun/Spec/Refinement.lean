/-
  Evm.Cancun.Spec.Refinement — proofs that the Cancun Effect
  interpreter refines the Cancun Spec relations.

  Cancun adds:

    * `TransientStorageStep.lean` — EIP-1153 0x5c TLOAD / 0x5d TSTORE.
    * `McopyStep.lean`            — EIP-5656 0x5e MCOPY.
    * `BlobhashStep.lean`         — EIP-4844 0x49 BLOBHASH.
    * `BlobbasefeeStep.lean`      — EIP-7516 0x4a BLOBBASEFEE.
    * `BlobTx.lean`               — EIP-4844 type-3 tx + blob fee mkt.
    * `KzgStep.lean`              — EIP-4844 point-evaluation precompile.
    * `Selfdestruct.lean`         — EIP-6780 same-tx-only destruction.

  Per SPEC-METHODOLOGY: TLOAD/TSTORE/MCOPY/BLOBHASH are state-touching
  or env-reading; BLOBBASEFEE is a one-line nullary-push refinement
  via `Frontier.Spec.Refinement.nullaryPush_sound`. BlobTx and Kzg
  are at the tx / precompile levels (the EIP-4788 system call is
  `Evm.Frontier.Vm.System`, proved in `Evm.CL.EffectSystemProof`); SELFDESTRUCT
  touches state. State-touching obligations are `sorry`-deferred.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Cancun.Spec.TransientStorageStep
import Evm.Cancun.Spec.McopyStep
import Evm.Cancun.Spec.BlobhashStep
import Evm.Cancun.Spec.BlobbasefeeStep
import Evm.Cancun.Spec.BlobTx
import Evm.Cancun.Spec.KzgStep
import Evm.Cancun.Spec.Selfdestruct
import Evm.Cancun.Vm.Instructions
import Evm.Cancun.Vm.Effect
import Evm.Frontier.Vm.Tx

namespace Evm.Cancun.Spec.Refinement

open Evm.Frontier (State)
open Evm.Frontier.Vm
open Evm.Cancun.Spec

/-! ## EIP-1153 TLOAD (0x5c) / TSTORE (0x5d) -/

/-- 0x5c TLOAD: pop the key, charge `GAS_WARM_ACCESS` (100), push the transient value of
    `(current_target, key)` (0 if unset). EELS `forks/cancun/vm/instructions/storage.py::
    tload`. -/
theorem tload_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.tload evm = .ok evm' → IsTloadStep evm evm' := by
  intro h
  unfold Evm.Cancun.Vm.Instructions.tload at h
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨g, hg, ⟨a, rest⟩, hp, s', hpush, h⟩
  obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
  obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hlt, rfl⟩ := (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨a, rest, hStack, hlt, hle, rfl⟩

/-- 0x5d TSTORE: static-context check, charge `GAS_WARM_ACCESS`, pop key and value, write
    `transient_storage[(current_target, key)]`. EELS `forks/cancun/vm/instructions/
    storage.py::tstore` (`if evm.message.is_static: raise WriteInStaticContext`). -/
theorem tstore_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.tstore evm = .ok evm' → IsTstoreStep evm evm' := by
  intro h
  unfold Evm.Cancun.Vm.Instructions.tstore at h
  by_cases hs : evm.message.isStatic = true
  · simp [hs, bind, Except.bind] at h
  · have hs' : evm.message.isStatic = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, ite_false, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
    rcases h with ⟨u, hu, ⟨a, b, rest⟩, hp, h⟩
    obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hu
    obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨a, b, rest, hStack, hs', hle, rfl⟩

/-! ## EIP-5656 MCOPY (0x5e) -/

/-- 0x5e MCOPY refines `IsMcopyStep`: charge `GAS_VERY_LOW + GAS_COPY · words +
    extend_memory.cost` with the expansion over both windows (none when `len = 0`), read
    the source from the expanded memory, write it at the destination. EELS
    `forks/cancun/vm/instructions/memory.py::mcopy` (141-174). -/
theorem mcopy_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.mcopy evm = .ok evm' →
    IsMcopyStep evm evm' := by
  intro h
  unfold Evm.Cancun.Vm.Instructions.mcopy at h
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨⟨d, sr, l, rest⟩, hp, g0, hg0, ⟨g1, m⟩, hc, g2, hg2, h⟩
  obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop3_eq_ok_iff _ _ _ _ _).mp hp
  obtain ⟨hle0, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg0
  obtain ⟨hle1, rfl, rfl⟩ := Evm.Frontier.Spec.chargeMemory_spec hc
  obtain ⟨hle2, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg2
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only at hle1 hle2 ⊢
  have hE : Evm.Frontier.Spec.memExpansionGas evm.memory 0
      (if l.toNat = 0 then 0 else Nat.max (d.toNat + l.toNat) (sr.toNat + l.toNat))
      = mcopyExpansionGas evm.memory d.toNat sr.toNat l.toNat := by
    unfold Evm.Frontier.Spec.memExpansionGas mcopyExpansionGas
    by_cases hl : l.toNat = 0
    · simp [hl]
    · simp [hl]
  have hX : Evm.Frontier.Spec.memAfterExpand evm.memory 0
      (if l.toNat = 0 then 0 else Nat.max (d.toNat + l.toNat) (sr.toNat + l.toNat))
      = mcopyExpand evm.memory d.toNat sr.toNat l.toNat := by
    unfold Evm.Frontier.Spec.memAfterExpand mcopyExpand
    by_cases hl : l.toNat = 0
    · simp [hl]
    · simp [hl]
  rw [hE] at hle1 hle2 ⊢
  rw [hX]
  obtain ⟨hA, hB⟩ := Evm.Frontier.Spec.charge3_nat hle0 hle1 hle2
  exact ⟨d, sr, l, rest, hStack, hA, by rw [hB]; rfl⟩

/-! ## EIP-4844 BLOBHASH (0x49) -/

/-- 0x49 BLOBHASH: charge `GAS_BLOBHASH_OPCODE` (3), pop the index, push
    `blob_versioned_hashes[index]` or 0 out of range. EELS `forks/cancun/vm/instructions/
    environment.py::blob_hash`. -/
theorem blobhash_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.blobhash evm = .ok evm' → IsBlobhashStep evm evm' := by
  intro h
  unfold Evm.Cancun.Vm.Instructions.blobhash at h
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨g, hg, ⟨a, rest⟩, hp, s', hpush, h⟩
  obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
  obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hlt, rfl⟩ := (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨a, rest, hStack, hlt, hle, ?_⟩
  simp only [blobHashAt]
  split <;> rename_i hh
  · simp_all; rfl
  · simp_all; rfl

/-! ## EIP-7516 BLOBBASEFEE (0x4a) -/

/-- BLOBBASEFEE is a NullaryPushStep over `env.blobBaseFee`. One-line
    proof via the `nullaryPush_sound` shape lemma. -/
theorem blobbasefee_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.blobbasefee evm = .ok evm' →
    IsBlobbasefeeStep evm evm' := by
  intro h
  exact Evm.Frontier.Spec.Refinement.nullaryPush_sound
    _ (fun e => Evm.U256.ofNat e.env.blobBaseFee) evm evm' h

/-! ## EIP-4844 blob tx / blob fee market (tx-level) -/

/-- `IsBlobCountValid`: in a Cancun (`k = 16`) block the implementation runs
    (`Tx.runAll`), every blob tx it accepts carries at least one blob and fits in what
    the block has left of `MAX_BLOB_GAS_PER_BLOCK` (`bg` the blob gas of the earlier
    txs). EELS `forks/cancun/fork.py::check_transaction` 432-439 and 472-473. -/
theorem blobCountValid_sound (benv : Environment)
    (pre : Environment → Evm.Address → Option _root_.Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm)
    (recover : Evm.Prague.Authorization → Option Evm.Address) (st : State)
    (tx : Evm.Frontier.Vm.Tx.Tx) (sender : Evm.Address)
    (rest : List (Evm.Frontier.Vm.Tx.Tx × Evm.Address)) (g bg : Nat)
    (ls : List Evm.Frontier.Vm.Log) (out : State × Nat × List Evm.Frontier.Vm.Log) :
    Evm.Frontier.Vm.Tx.runAll 16 benv pre runSub recover st ((tx, sender) :: rest) g bg ls
      = .ok out →
    tx.type = 3 →
    IsBlobCountValid bg tx.blobHashes.length := by
  intro h h3
  unfold Evm.Frontier.Vm.Tx.runAll at h
  by_cases hb : Evm.Frontier.Vm.Tx.blobGasExceeds 16 bg tx = true
  · simp [hb, bind, Except.bind] at h
  · simp only [hb, Bool.false_eq_true, ite_false, bind, Except.bind] at h
    split at h
    · exact absurd h (by simp)
    · rename_i r hr
      unfold Evm.Frontier.Vm.Tx.run at hr
      split at hr
      · exact absurd hr (by simp)
      · rename_i hv
        have hn := Evm.Frontier.Vm.Tx.rules_false_of_valid hv
          (decide (tx.type = 3 ∧ tx.blobHashes.length = 0), "no blobs")
          (by simp [Evm.Frontier.Vm.Tx.rules])
        simp [h3] at hn
        have hm : Evm.CL.GasEmit.maxBlobGasPerBlock.eval
            (fun y => if y = "fork-ord" then 16 else 0) = 786432 := by
          simp [Evm.CL.GasEmit.maxBlobGasPerBlock, Evm.CL.GasEmit.bySchedule,
            Evm.CL.GasEmit.Expr.eval, Evm.CL.GasEmit.fork]
        simp only [Evm.Frontier.Vm.Tx.blobGasExceeds, hm, decide_eq_true_eq, not_and,
          Nat.not_lt] at hb
        have hb' := hb (by omega)
        refine ⟨Nat.pos_of_ne_zero (by simpa using hn), ?_⟩
        simp only [txBlobGas, gasPerBlob, maxBlobGasPerBlock, Evm.Frontier.Vm.Tx.blobGas] at hb' ⊢
        omega

/-- `IsBlobAffordable`: a blob tx (type 3) the tx layer accepts (`Tx.invalid = none`) has a
    sender whose balance covers `value + gas · max_fee_per_gas + blob_gas ·
    max_fee_per_blob_gas`. EELS `forks/cancun/fork.py::check_transaction` 462-497
    (`max_gas_fee = tx.gas * tx.max_fee_per_gas`, `+= calculate_total_blob_gas(tx) *
    tx.max_fee_per_blob_gas`, `if balance < max_gas_fee + tx.value: raise
    InsufficientBalanceError`). -/
theorem blobAffordable_sound (k : Nat) (benv : Environment) (st : State)
    (sender : Evm.Address) (tx : Evm.Frontier.Vm.Tx.Tx) :
    Evm.Frontier.Vm.Tx.invalid k benv st sender tx = none → tx.type = 3 →
    IsBlobAffordable (st.getAccount sender).balance.toNat tx.value.toNat tx.gas tx.maxFee
      tx.maxFeePerBlobGas tx.blobHashes.length := by
  intro h h3
  have hr := Evm.Frontier.Vm.Tx.rules_false_of_valid h
    (decide ((st.getAccount sender).balance.toNat <
      Evm.Frontier.Vm.Tx.maxGasFee tx + tx.value.toNat), "insufficient balance")
    (by simp [Evm.Frontier.Vm.Tx.rules])
  simp only [decide_eq_false_iff_not, Nat.not_lt] at hr
  simp only [Evm.Frontier.Vm.Tx.maxGasFee, Evm.Frontier.Vm.Tx.blobGas, h3] at hr
  unfold IsBlobAffordable txBlobGas gasPerBlob
  simp at hr
  rw [Nat.mul_comm tx.maxFeePerBlobGas]
  omega

/-- `IsBlobFeeBidSufficient`: a blob tx the tx layer accepts bids at least the block's
    blob base fee. EELS `forks/cancun/fork.py::check_transaction` 480-484
    (`if tx.max_fee_per_blob_gas < blob_gas_price: raise InsufficientMaxFeePerBlobGasError`). -/
theorem blobFeeBidSufficient_sound (k : Nat) (benv : Environment) (st : State)
    (sender : Evm.Address) (tx : Evm.Frontier.Vm.Tx.Tx) :
    Evm.Frontier.Vm.Tx.invalid k benv st sender tx = none → tx.type = 3 →
    IsBlobFeeBidSufficient tx.maxFeePerBlobGas benv.blobBaseFee := by
  intro h h3
  have hr := Evm.Frontier.Vm.Tx.rules_false_of_valid h
    (decide (tx.type = 3 ∧ tx.maxFeePerBlobGas < benv.blobBaseFee),
      "max blob fee below blob base fee") (by simp [Evm.Frontier.Vm.Tx.rules])
  simp [h3] at hr
  exact hr

/-! ## EIP-4844 KZG point-evaluation precompile (0x0a) -/

private theorem forIn_push_size (l : List Nat) (b : ByteArray) (f : Nat → UInt8) :
    (forIn (m := Id) l b (fun i s => pure (ForInStep.yield (s.push (f i))))).run.size
      = b.size + l.length := by
  induction l generalizing b with
  | nil => rfl
  | cons i l ih =>
    rw [List.forIn_cons]
    show (forIn (m := Id) l (b.push (f i)) _).run.size = _
    rw [ih, ByteArray.size_push, List.length_cons]; omega

/-- A word's big-endian encoding is 32 bytes. -/
theorem toBytesBE_size (x : Evm.U256) : (Evm.U256.toBytesBE x).size = 32 := by
  unfold Evm.U256.toBytesBE
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn_push_size _ _ _

theorem kzgSuccessOutput_size : kzgSuccessOutput.size = 64 := by
  unfold kzgSuccessOutput be32
  rw [ByteArray.size_append, toBytesBE_size, toBytesBE_size]

/-- The point-evaluation FFI's contract (`lean/c/point_evaluation.c` over blst, the
    trust boundary): it returns the canonical output exactly on inputs EELS accepts,
    with `verify` the KZG pairing oracle, and nothing 64 bytes long otherwise. -/
def PointEvaluationFFI (verify : Evm.Bytes → Evm.Bytes → Evm.Bytes → Evm.Bytes → Bool) : Prop :=
  ∀ input, (pointEvaluationAccepts verify input →
      Evm.Cancun.Vm.PrecompiledContracts.pointEvaluationRaw input = kzgSuccessOutput) ∧
    (¬ pointEvaluationAccepts verify input →
      (Evm.Cancun.Vm.PrecompiledContracts.pointEvaluationRaw input).size ≠ 64)

/-- 0x0a point evaluation, success: the implementation returns only on an accepted
    input with the 50000 gas available, and returns the canonical 64 bytes. EELS
    `forks/cancun/vm/precompiled_contracts/point_evaluation.py::point_evaluation`
    32-72. Hypothesis: the FFI contract `PointEvaluationFFI verify`. -/
theorem kzg_success_sound (verify : Evm.Bytes → Evm.Bytes → Evm.Bytes → Evm.Bytes → Bool)
    (hFFI : PointEvaluationFFI verify)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    Evm.Cancun.Vm.PrecompiledContracts.pointEvaluation input gas = .ok (output, gas') →
    IsKzgPrecompileSuccess verify input gas output gas' := by
  intro h
  unfold Evm.Cancun.Vm.PrecompiledContracts.pointEvaluation at h
  by_cases hg : gas < Evm.Cancun.Vm.Gas.pointEvaluation
  · simp [hg, bind, Except.bind] at h
  · simp only [hg, ite_false] at h
    by_cases hs : (Evm.Cancun.Vm.PrecompiledContracts.pointEvaluationRaw input).size ≠ 64
    · simp [hs, bind, Except.bind] at h
    · simp only [hs, ite_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hacc : pointEvaluationAccepts verify input :=
        Classical.byContradiction fun hn => hs ((hFFI input).2 hn)
      have hg' : gas ≥ pointEvaluationGas := by
        simp only [Evm.Cancun.Vm.Gas.pointEvaluation] at hg
        simp only [pointEvaluationGas]; omega
      exact ⟨hacc, hg', (hFFI input).1 hacc, rfl⟩

/-- 0x0a point evaluation, failure: the implementation raises only on a rejected
    input or too little gas (`KZGProofError`). Hypothesis: the FFI contract. -/
theorem kzg_failure_sound (verify : Evm.Bytes → Evm.Bytes → Evm.Bytes → Evm.Bytes → Bool)
    (hFFI : PointEvaluationFFI verify)
    (input : Evm.Bytes) (gas : Nat) (e : Exception) :
    Evm.Cancun.Vm.PrecompiledContracts.pointEvaluation input gas = .error e →
    IsKzgPrecompileFailure verify input gas := by
  intro h
  unfold Evm.Cancun.Vm.PrecompiledContracts.pointEvaluation at h
  by_cases hg : gas < Evm.Cancun.Vm.Gas.pointEvaluation
  · exact Or.inr (by simpa [pointEvaluationGas, Evm.Cancun.Vm.Gas.pointEvaluation] using hg)
  · simp only [hg, ite_false] at h
    by_cases hs : (Evm.Cancun.Vm.PrecompiledContracts.pointEvaluationRaw input).size ≠ 64
    · refine Or.inl fun hacc => hs ?_
      rw [(hFFI input).1 hacc, kzgSuccessOutput_size]
    · simp [hs, pure, Except.pure] at h

/-! ## EIP-6780 SELFDESTRUCT (same-tx-only destruction) -/

/-- 0xff SELFDESTRUCT at Cancun refines `IsSelfdestructStep`, on the path that runs:
    Cancun's `step1` (`doSelfdestruct`: static check, pop, the 5000 + cold 2600 +
    new-account 25000 charge, the beneficiary warmed) yields `.selfdestruct`, and
    `handleYield` discharges it (`selfdestructEIP6780`: move the balance, zero the
    originator unless it survives as its own beneficiary, queue it in
    `selfDestructSet` only when created in this tx, touch the beneficiary, halt).
    EELS `forks/cancun/vm/instructions/system.py::selfdestruct` 508-564. -/
theorem selfdestruct_sound (lookup : Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (evm evm1 evm' : Evm) (eff : Evm.Byzantium.Vm.Effect.YieldEffect)
    (runSub : Evm → Except Exception Evm)
    (hHalt : evm.halted = false) (hpc : evm.pc < evm.message.code.size)
    (hop : (evm.message.code.get! evm.pc).toNat = 0xff) :
    Evm.Cancun.Vm.Effect.step1 evm = .yield evm1 eff →
    Evm.Cancun.Vm.Effect.handleYield lookup evm1 eff runSub = .ok evm' →
    IsSelfdestructStep evm evm' := by
  intro h1 h2
  simp only [Evm.Cancun.Vm.Effect.step1, hHalt, Bool.false_eq_true, ite_false,
    show ¬ evm.pc ≥ evm.message.code.size from Nat.not_le.mpr hpc, hop] at h1
  unfold Evm.Cancun.Vm.Effect.doSelfdestruct at h1
  by_cases hs : evm.message.isStatic = true
  · simp [hs] at h1
  have hs' : evm.message.isStatic = false := by simpa using hs
  simp only [hs', Bool.false_eq_true, ite_false] at h1
  split at h1
  · exact absurd h1 (by simp)
  rename_i benW rest hp
  obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  split at h1
  · exact absurd h1 (by simp)
  rename_i g hg
  obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
  simp only [Evm.Byzantium.Vm.Effect.StepResult.yield.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  simp only [Evm.Cancun.Vm.Effect.handleYield, Evm.Cancun.Vm.Effect.selfdestructEIP6780,
    hs', Bool.false_eq_true, ite_false, pure, Except.pure, bind, Except.bind] at h2
  injection h2 with h2
  subst h2
  refine ⟨benW, rest, hStack, hs', ?_⟩
  simp only [Evm.TangerineWhistle.Vm.Gas.selfDestruct, Evm.Frontier.Vm.Gas.newAccount,
    Evm.Berlin.Vm.Gas.coldAccountAccess, gasSelfdestructBase, gasSelfdestructNewAccount,
    gasColdAccountAccess, Evm.Cancun.State.wasCreatedThisTx] at hle ⊢
  have hb : Evm.Cancun.Vm.Effect.u256ToAddrL benW = Evm.Address.ofNat benW.toNat := rfl
  have hcost : ∀ (e i : Bool) (bal : Evm.U256) (c : Bool),
      (5000 + (if bal ≠ 0 ∧ (if e = true then i else true) = true then 25000 else 0) +
        (if ¬ c = true then 2600 else 0)) =
      (5000 + (if bal ≠ 0 ∧ ¬(e = true ∧ ¬ i = true) then 25000 else 0) +
        (if ¬ c = true then 2600 else 0)) := by
    intro e i bal c; cases e <;> cases i <;> simp
  simp only [hb, hcost] at hle ⊢
  refine ⟨hle, ?_⟩
  unfold Evm.SpuriousDragon.Vm.touchAddr
  by_cases hcr : evm.env.createdAccounts.contains evm.message.currentTarget = true
  · simp only [hcr, ite_true, not_true_eq_false, false_and, ite_false, true_and, Nat.add_zero]
    by_cases ht : evm.env.touched.contains (Evm.Address.ofNat benW.toNat) = true <;>
      by_cases hsd : evm.env.selfDestructSet.contains evm.message.currentTarget = true <;>
      simp only [ht, hsd, ite_true, ite_false, Bool.false_eq_true, not_true_eq_false,
        not_false_eq_true] <;> rfl
  · simp only [hcr, Bool.false_eq_true, ite_false, not_false_eq_true, true_and, false_and]
    by_cases ht : evm.env.touched.contains (Evm.Address.ofNat benW.toNat) = true <;>
      simp only [ht, ite_true, ite_false, Bool.false_eq_true] <;> rfl

/-! ## Notes

    - Most tx- and block-level predicates above are equational; their
      refinement reduces to definitional equality once the impl
      callsite (in `Cancun.Fork` / `Cancun.Vm.Effect`) is extracted.

    - The KZG spec is intentionally minimal: the cryptographic
      semantics are deferred to external libraries.

    - The spec relations match the EIPs Cancun ships (EIP-4788's
      system call is `Evm.Frontier.Vm.System`); every one has a
      soundness obligation here. -/

end Evm.Cancun.Spec.Refinement
