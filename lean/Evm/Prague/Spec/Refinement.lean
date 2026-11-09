/-
  Evm.Prague.Spec.Refinement — proofs that the Prague Effect
  interpreter refines the Prague Spec relations.

  Prague adds:

    * `Bls12381Step.lean`  — EIP-2537 BLS12-381 precompiles at
                              0x0b..0x11 (seven new precompiles).
    * `CalldataCost.lean`  — EIP-7623 calldata reprice + floor.
    * `Requests.lean`      — EIP-7685 execution-layer requests hash.
    * `SetCodeStep.lean`   — EIP-7702 set-code tx + CALL delegation.

  All four are cross-cutting state-machine deltas (precompiles,
  block-validity predicates, intrinsic-gas formulas, requests-hash,
  tx-shape / CALL-delegation). All `sorry`-deferred per methodology.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Prague.Spec.Bls12381Step
import Evm.Prague.Spec.CalldataCost
import Evm.Prague.Spec.Requests
import Evm.Prague.Spec.SetCodeStep
import Evm.Prague.Vm.Effect
import Evm.CL.GasEmitPrague
import Evm.Frontier.Vm.Tx

namespace Evm.Prague.Spec.Refinement

open Evm.Frontier (State Transaction)
open Evm.Frontier.Vm
open Evm.Prague.Spec

/-! ## EIP-2537 BLS12-381 precompiles (0x0b..0x11)

    Seven new precompiles. Each soundness theorem states the
    precompile's `(input, gas) → (output, gas')` shape against the
    spec relation; crypto correctness is delegated to axiomatised
    predicates. -/

theorem g1Add_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsG1AddSuccess input gas output gas' →
    IsG1AddSuccess input gas output gas' := by
  intro h; exact h

theorem g2Add_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsG2AddSuccess input gas output gas' →
    IsG2AddSuccess input gas output gas' := by
  intro h; exact h

theorem g1Msm_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsG1MsmSuccess input gas output gas' →
    IsG1MsmSuccess input gas output gas' := by
  intro h; exact h

theorem g2Msm_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsG2MsmSuccess input gas output gas' →
    IsG2MsmSuccess input gas output gas' := by
  intro h; exact h

theorem pairingCheck_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsPairingCheckSuccess input gas output gas' →
    IsPairingCheckSuccess input gas output gas' := by
  intro h; exact h

theorem mapFpToG1_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsMapFpToG1Success input gas output gas' →
    IsMapFpToG1Success input gas output gas' := by
  intro h; exact h

theorem mapFp2ToG2_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsMapFp2ToG2Success input gas output gas' →
    IsMapFp2ToG2Success input gas output gas' := by
  intro h; exact h

/-! ## EIP-2935 (history storage)

    EIP-2935 as shipped leaves the BLOCKHASH opcode alone (EELS
    `forks/prague/vm/instructions/block.py::block_hash` still reads
    `block_env.block_hashes`, the 256 most recent), so Prague has no
    BLOCKHASH relation of its own: the obligation is Frontier's
    `IsBlockhashStep`. The history contract is fed by the block-start system
    call (`Evm.Prague.Fork`, `Evm.Frontier.Vm.System`). A draft relation that
    re-pointed BLOCKHASH at the contract's storage was deleted 2026-11-09. -/

/-! ## EIP-7623 calldata cost (tx-level) -/

/-- EIP-7623 (+ EIP-7702's per-authorization cost): a Prague+ (`k ≥ 17`) tx the tx
    layer accepts (`Tx.invalid = none`) declares at least `max(regular,
    calldata_floor)`, with the regular cost's extras read off the tx (creation,
    access list, authorizations). EELS `forks/prague/transactions.py::
    validate_transaction` 578-579 and `calculate_intrinsic_cost` 594-660. The
    implementation's costs are the emitted `GasEmit` formulas, equal to the spec's
    by `Evm.CL.GasEmitPrague`. -/
theorem intrinsicGasSufficient_sound (k : Nat) (hk : 17 ≤ k) (benv : Environment)
    (st : Evm.Frontier.State) (sender : Evm.Address) (tx : Evm.Frontier.Vm.Tx.Tx)
    (extras : Nat)
    (hx : extras = baseExtras tx.to.isNone tx.data.size tx.accessList.length
      (tx.accessList.map (·.2.length)).sum tx.auths.length) :
    Evm.Frontier.Vm.Tx.invalid k benv st sender tx = none →
    IsIntrinsicGasSufficient tx.gas tx.data extras := by
  intro h
  subst hx
  have hr := Evm.Frontier.Vm.Tx.rules_false_of_valid h
    (decide (max (Evm.Frontier.Vm.Tx.intrinsic k tx) (Evm.Frontier.Vm.Tx.floor k tx) > tx.gas),
      "intrinsic gas") (by simp [Evm.Frontier.Vm.Tx.rules])
  simp only [decide_eq_false_iff_not, Nat.not_lt] at hr
  have hf : (Evm.Frontier.Vm.Tx.gasEnv k tx) "fork-ord" = k := by
    simp [Evm.Frontier.Vm.Tx.gasEnv]
  have hfl := Evm.CL.GasEmitPrague.calldataFloor_eq_spec (Evm.Frontier.Vm.Tx.gasEnv k tx)
    (by rw [hf]; exact hk)
  have hz : (Evm.Frontier.Vm.Tx.gasEnv k tx) "zero-bytes" =
      Evm.Frontier.Vm.Tx.zeroBytes tx.data := by simp [Evm.Frontier.Vm.Tx.gasEnv]
  have hnz : (Evm.Frontier.Vm.Tx.gasEnv k tx) "nonzero-bytes" =
      tx.data.size - Evm.Frontier.Vm.Tx.zeroBytes tx.data := by
    simp [Evm.Frontier.Vm.Tx.gasEnv]
  have hdl : (Evm.Frontier.Vm.Tx.gasEnv k tx) "data-len" = tx.data.size := by
    simp [Evm.Frontier.Vm.Tx.gasEnv]
  have hal : (Evm.Frontier.Vm.Tx.gasEnv k tx) "al-addrs" = tx.accessList.length := by
    simp [Evm.Frontier.Vm.Tx.gasEnv]
  have hak : (Evm.Frontier.Vm.Tx.gasEnv k tx) "al-keys" =
      (tx.accessList.map (·.2.length)).sum := by simp [Evm.Frontier.Vm.Tx.gasEnv]
  rw [hz, hnz] at hfl
  unfold IsIntrinsicGasSufficient countBytes intrinsicCost
  simp only [Evm.Frontier.Vm.Tx.intrinsic, Evm.Frontier.Vm.Tx.floor, hfl, hz, hnz,
    show k ≥ 17 from hk, ite_true] at hr
  show tx.gas ≥ max (standardCost (Evm.Frontier.Vm.Tx.zeroBytes tx.data)
      (tx.data.size - Evm.Frontier.Vm.Tx.zeroBytes tx.data) _) _
  cases hc : tx.to.isNone
  · have hci : (Evm.Frontier.Vm.Tx.gasEnv k tx) "is-create" = 0 := by
      simp [Evm.Frontier.Vm.Tx.gasEnv, hc]
    rw [Evm.CL.GasEmitPrague.intrinsicCall_eq_spec _ (by rw [hf]; exact hk) hci, hz, hnz,
      hal, hak] at hr
    unfold baseExtras
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add, authPerEmptyAccount]
    simp only [standardCost, floorCost, tokens, txBaseCost, txDataTokenStandard,
      txDataTokenFloor, tokensPerNonZero, Evm.Frontier.Vm.Tx.zeroBytes] at hr hfl ⊢
    omega
  · have hci : (Evm.Frontier.Vm.Tx.gasEnv k tx) "is-create" = 1 := by
      simp [Evm.Frontier.Vm.Tx.gasEnv, hc]
    rw [Evm.CL.GasEmitPrague.intrinsicCreate_eq_spec _ (by rw [hf]; exact hk) hci, hz, hnz,
      hal, hak, hdl] at hr
    unfold baseExtras
    simp only [ite_true, authPerEmptyAccount, txCreateCost, initCodeWordCost]
    simp only [standardCost, floorCost, tokens, txBaseCost, txDataTokenStandard,
      txDataTokenFloor, tokensPerNonZero, Evm.Frontier.Vm.Tx.zeroBytes] at hr hfl ⊢
    omega

/-! ## EIP-7685 requests hash (block-level) -/

/-- EIP-7685: the implementation's commitment over the request lists `applyBlock`
    builds (`ofOutput` of the deposit data and of each predeploy's output, in type
    order) is EELS's `compute_requests_hash` over EELS's `requests_from_execution`.
    So `applyBlock`'s check `computeRequestsHash (dreqs ++ wreqs ++ creqs) =
    header.requestsHash` is `IsRequestsHashValid`. EELS `forks/prague/requests.py::
    compute_requests_hash` 289-308, `forks/prague/fork.py::
    process_general_purpose_requests` 767-810 and the header check 245, 263.

    (Implementation gap, visible: `Prague.harvestDepositRequests` is a stub
    returning `[]` — EIP-6110 deposit parsing from receipt logs is not
    implemented at the `Prague.applyBlock` layer, whose body runs no
    transactions; this theorem covers any deposit data `d`.) -/
theorem requestsHashValid_sound (d w c : Evm.Bytes) (requests : List Evm.Bytes)
    (headerHash : Evm.Hash32) (hreq : requests = requestsFromExecution d w c) :
    Evm.Prague.Requests.computeRequestsHash
        (Evm.Prague.Requests.ofOutput 0 d ++ Evm.Prague.Requests.ofOutput 1 w ++
          Evm.Prague.Requests.ofOutput 2 c) = headerHash →
    IsRequestsHashValid requests headerHash := by
  intro h
  subst h hreq
  unfold IsRequestsHashValid requestsFromExecution Evm.Prague.Requests.ofOutput
  by_cases hd : d.size = 0 <;> by_cases hw : w.size = 0 <;> by_cases hc : c.size = 0 <;>
    simp only [hd, hw, hc, ite_true, ite_false, List.nil_append, List.append_nil,
      List.cons_append] <;> rfl

/-! ## EIP-7702 set-code tx + CALL delegation -/

/-- The implementation's designator parser is the spec's recogniser and address
    extraction (EELS `get_delegated_code_address`: `Address(code[3:])` exactly when
    `is_valid_delegation(code)`). -/
theorem parseDelegation_eq (c : Evm.Bytes) :
    Evm.Prague.State.parseDelegation c =
      if isDelegationDesignator c then some (parseDelegated c) else none := by
  unfold Evm.Prague.State.parseDelegation isDelegationDesignator parseDelegated
  by_cases h0 : c.size = 23
  · by_cases h1 : c.get! 0 = 0xef <;> by_cases h2 : c.get! 1 = 0x01 <;>
      by_cases h3 : c.get! 2 = 0x00 <;>
      simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, ite_true,
        ite_false, decide_true, decide_false, Bool.and_true, Bool.and_false] <;> try rfl
    simp only [Evm.Bytes.sliceZeroPad, Std.Legacy.Range.forIn_eq_forIn_range', h0]
    rfl
  · simp [h0]

/-- One EIP-7702 authorization: the implementation `Tx.authorize` (over the tx
    environment, with the same `recover` oracle) refines `IsApplyAuthorization` —
    the prechecks, the authority warmed, its code and nonce checks, then the 12500
    refund when it exists, the code, the nonce. EELS `forks/prague/vm/
    eoa_delegation.py::validate_authorization` 155-189, `recover_authority` 77-128,
    `set_delegation` 192-237. -/
theorem applyAuthorization_sound (chainId : Evm.U256)
    (recover : Evm.Prague.Authorization → Option Evm.Address)
    (env env' : Environment) (auth : Evm.Prague.Authorization) :
    Evm.Frontier.Vm.Tx.authorize chainId recover env auth = env' →
    IsApplyAuthorization chainId recover auth env env' := by
  intro h
  subst h
  unfold Evm.Frontier.Vm.Tx.authorize IsApplyAuthorization
  have hN : Evm.Frontier.Vm.Tx.secp256k1n = secp256k1n := rfl
  rw [hN]
  by_cases hpre : AuthPrechecks chainId auth
  · rw [if_neg (not_not_intro hpre)]
    obtain ⟨hc, hn, hy, hr0, hrN, hs0, hsN⟩ := hpre
    rw [if_neg (not_not_intro hc), if_neg (by omega),
      if_neg (not_not_intro ⟨hy, hr0, hrN, hs0, hsN⟩)]
    cases hr : recover auth with
    | none => rfl
    | some au =>
      simp only [Evm.Frontier.Vm.Call.warm]
      have hpd := parseDelegation_eq (env.state.getAccount au).code
      by_cases hw : env.accessedAddresses.contains au = true
      · simp only [hw, ite_true]
        by_cases hd : isDelegationDesignator (env.state.getAccount au).code = true
        · simp only [hpd, hd, ite_true, Option.isNone_some, Bool.false_eq_true, and_false,
            false_or]
          by_cases hno : (env.state.getAccount au).nonce = auth.nonce.toNat <;>
            simp only [hno, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              or_false, or_true, false_or, and_false, and_true] <;>
            by_cases hsz : (env.state.getAccount au).code.size = 0 <;>
            simp only [hsz, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              true_and, false_and, or_false, false_or] <;>
            first | rfl | trivial | (exfalso; simp_all [isDelegationDesignator])
        · simp only [hpd, hd, Bool.false_eq_true, ite_false, Option.isNone_none, and_true]
          by_cases hno : (env.state.getAccount au).nonce = auth.nonce.toNat <;>
            simp only [hno, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              or_false, or_true, false_or, and_false, and_true] <;>
            by_cases hsz : (env.state.getAccount au).code.size = 0 <;>
            simp only [hsz, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              true_and, false_and, or_false, false_or] <;>
            first | rfl | trivial | (exfalso; simp_all [isDelegationDesignator])
      · simp only [hw, Bool.false_eq_true, ite_false]
        by_cases hd : isDelegationDesignator (env.state.getAccount au).code = true
        · simp only [hpd, hd, ite_true, Option.isNone_some, Bool.false_eq_true, and_false,
            false_or]
          by_cases hno : (env.state.getAccount au).nonce = auth.nonce.toNat <;>
            simp only [hno, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              or_false, or_true, false_or, and_false, and_true] <;>
            by_cases hsz : (env.state.getAccount au).code.size = 0 <;>
            simp only [hsz, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              true_and, false_and, or_false, false_or] <;>
            first | rfl | trivial | (exfalso; simp_all [isDelegationDesignator])
        · simp only [hpd, hd, Bool.false_eq_true, ite_false, Option.isNone_none, and_true]
          by_cases hno : (env.state.getAccount au).nonce = auth.nonce.toNat <;>
            simp only [hno, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              or_false, or_true, false_or, and_false, and_true] <;>
            by_cases hsz : (env.state.getAccount au).code.size = 0 <;>
            simp only [hsz, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
              true_and, false_and, or_false, false_or] <;>
            first | rfl | trivial | (exfalso; simp_all [isDelegationDesignator])
  · rw [if_pos hpre]
    by_cases hc : auth.chainId = chainId ∨ auth.chainId = 0
    · rw [if_neg (not_not_intro hc)]
      by_cases hn : auth.nonce.toNat ≥ 2 ^ 64 - 1
      · rw [if_pos hn]
      · rw [if_neg hn]
        have hsig : ¬ (auth.yParity.toNat ≤ 1 ∧ 0 < auth.r.toNat ∧ auth.r.toNat < secp256k1n ∧
            0 < auth.s.toNat ∧ auth.s.toNat ≤ secp256k1n / 2) := fun hs =>
          hpre ⟨hc, by omega, hs⟩
        rw [if_pos hsig]
    · rw [if_pos hc]

/-- The authorization list (`Tx.message`'s `tx.auths.foldl (authorize …)`) refines
    `IsApplyAuthorizations`, by induction from `applyAuthorization_sound`. EELS
    `set_delegation` 209-228 (the loop). -/
theorem applyAuthorizations_sound (chainId : Evm.U256)
    (recover : Evm.Prague.Authorization → Option Evm.Address)
    (auths : List Evm.Prague.Authorization) (env env' : Environment) :
    auths.foldl (Evm.Frontier.Vm.Tx.authorize chainId recover) env = env' →
    IsApplyAuthorizations chainId recover auths env env' := by
  induction auths generalizing env with
  | nil => intro h; exact h.symm
  | cons a rest ih =>
    intro h
    exact ⟨_, applyAuthorization_sound chainId recover env _ a rfl, ih _ h⟩

/-- CALL delegation (EIP-7702, Prague: `pragueDelegation` on): the code a CALL into
    `to` runs (`Call.codeOf`) is the delegate's when `to`'s code is a designator,
    else `to`'s own. EELS `forks/prague/vm/instructions/system.py::generic_call` via
    `vm/eoa_delegation.py::get_delegated_code_address` (`access_delegation`). -/
theorem effectiveCallCode_sound (env : Environment) (to : Evm.Address)
    (hP : env.pragueDelegation = true) :
    IsEffectiveCallCode env.state to (Evm.Frontier.Vm.Call.codeOf env to) := by
  unfold IsEffectiveCallCode Evm.Frontier.Vm.Call.codeOf Evm.Frontier.Vm.Call.delegate
  dsimp only
  simp only [hP, ite_true, parseDelegation_eq]
  by_cases hd : isDelegationDesignator (env.state.getAccount to).code = true
  · simp only [hd, ite_true]
  · simp only [hd, Bool.false_eq_true, ite_false]

/-! ## Notes

    - Seven BLS12-381 precompiles, two new tx-level
      predicates, one new block-validity predicate, and three
      EIP-7702 state-machine predicates ⇒ 13 soundness obligations
      stated here. None closed (per methodology) but all of the
      correct shape.

    - The cryptographic predicates (`IsValidG1Point`, `IsValidKzg
      Proof`, `RecoverAuthority`, …) are axiomatic in the spec;
      discharging them requires linking external libraries. -/

end Evm.Prague.Spec.Refinement
