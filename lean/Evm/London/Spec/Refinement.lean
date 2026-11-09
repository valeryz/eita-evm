/-
  Evm.London.Spec.Refinement — proofs that the London Effect
  interpreter refines the London Spec relations.

  London adds:

    * `BaseFee.lean` — EIP-1559 base-fee formula (block-level).
    * `BasefeeStep.lean` — EIP-3198 0x48 BASEFEE opcode.
    * `CodePrefix.lean` — EIP-3541 0xEF deployed-code prefix reject.
    * `FeeMarket.lean` — EIP-1559 effective price / coinbase credit /
                          burn.
    * `RefundCap.lean` — EIP-3529 refund cap (gas_used / 5 instead of
                          / 2).
    * `Selfdestruct.lean` — EIP-3529 SELFDESTRUCT refund removal.

  BASEFEE is a NullaryPushStep; the rest are tx- / block-level
  relations (block-validity formulas, deposit-code checks, refund
  caps, SELFDESTRUCT refund deltas). All `sorry`-deferred per
  methodology.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.London.Spec.BaseFee
import Evm.London.Spec.BasefeeStep
import Evm.London.Spec.CodePrefix
import Evm.London.Spec.FeeMarket
import Evm.London.Spec.RefundCap
import Evm.London.Spec.Selfdestruct
import Evm.London.Vm.Instructions.Block
import Evm.London.Vm.Effect
import Evm.Frontier.Vm.Tx
import Evm.CL.GasEmitLondon
import Evm.CL.EffectSettleProof

namespace Evm.London.Spec.Refinement

open Evm.Frontier.Vm
open Evm.London.Spec

/-! ## EIP-3198 BASEFEE (0x48) -/

/-- BASEFEE is a NullaryPushStep over `env.baseFeePerGas`. One-line
    proof via the `nullaryPush_sound` shape lemma. -/
theorem basefee_sound (evm evm' : Evm) :
    Evm.London.Vm.Instructions.baseFee evm = .ok evm' →
    IsBasefeeStep evm evm' := by
  intro h
  exact Evm.Frontier.Spec.Refinement.nullaryPush_sound
    _ (fun e => Evm.U256.ofNat e.env.baseFeePerGas) evm evm' h

/-! ## EIP-1559 base-fee formula refinement -/

/-- EIP-1559 base fee: the number the host checks a London+ header's `base_fee_per_gas`
    against (`Evm.CL.GasEmit.nextBaseFee`, emitted into `spec-header-violation`) is the
    spec formula over the parent's `(gas_used, gas_limit / ELASTICITY_MULTIPLIER,
    base_fee)`. EELS `forks/london/fork.py::calculate_base_fee_per_gas` (226-). -/
theorem calculateBaseFee_sound (ρ : Evm.CL.GasEmit.Env) (used limit target base f : Nat)
    (hu : ρ "parent-gas-used" = used) (hl : ρ "parent-gas-limit" = limit)
    (hb : ρ "parent-base-fee" = base) (ht : limit / elasticityMultiplier = target) :
    Evm.CL.GasEmit.Expr.eval ρ Evm.CL.GasEmit.nextBaseFee = f →
    IsCalculatedBaseFee used target base f := by
  intro h; subst h ht
  exact Evm.CL.GasEmitLondon.nextBaseFee_eq_spec ρ used limit base hu hl hb

/-! ## EIP-3541 deployed-code prefix refinement -/

/-- EIP-3541 at a creating tx: when `Tx.createEnd` reports success at London+ (`k ≥ 11`),
    the deployed code does not start with 0xEF. EELS `forks/london/vm/interpreter.py::
    process_create_message` 192-193 (`if contract_code[0] == 0xEF: raise
    InvalidContractPrefix`). -/
theorem validDeployedCode_tx_sound (k : Nat) (snap : Environment) (newAddr : Evm.Address)
    (sub : Evm) :
    (Evm.Frontier.Vm.Tx.createEnd k snap newAddr (.ok sub)).success = true → 11 ≤ k →
    IsValidDeployedCode sub.output := by
  intro h hk
  unfold IsValidDeployedCode eofPrefixByte
  by_cases he : 0 < sub.output.size ∧ sub.output.get! 0 = (0xEF : UInt8)
  · exfalso
    unfold Evm.Frontier.Vm.Tx.createEnd at h
    simp only [hk, he, and_self, if_true] at h
    split at h <;> simp at h
  · by_cases hz : sub.output.size = 0
    · exact Or.inl hz
    · exact Or.inr (fun h' => he ⟨by omega, h'⟩)

/-- EIP-3541 at CREATE / CREATE2: when `Create.resume` under the EIP-3541 rules pushes
    anything but 0 (the failure value), the deployed code does not start with 0xEF. Same EELS
    clause (`process_create_message` 192-193). -/
theorem validDeployedCode_create_sound (r : Evm.Frontier.Vm.Create.Rules) (parent : Evm)
    (newAddr : Evm.Address) (sub evm' : Evm) :
    Evm.Frontier.Vm.Create.resume r parent newAddr (.ok sub) = .ok evm' →
    evm'.stack.head? ≠ some 0 → r.eip3541 = true →
    IsValidDeployedCode sub.output := by
  intro h h0 hr
  unfold IsValidDeployedCode eofPrefixByte
  by_cases he : 0 < sub.output.size ∧ sub.output.get! 0 = (0xEF : UInt8)
  · exfalso
    unfold Evm.Frontier.Vm.Create.resume at h
    simp only [hr, he, and_self, if_true] at h
    split at h
    · unfold Evm.Frontier.Vm.Create.push at h
      simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
      obtain ⟨s, hs, h⟩ := h
      obtain ⟨-, rfl⟩ := (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hs
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; exact h0 rfl
    · unfold Evm.Frontier.Vm.Create.push at h
      simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
      obtain ⟨s, hs, h⟩ := h
      obtain ⟨-, rfl⟩ := (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hs
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; exact h0 rfl
  · by_cases hz : sub.output.size = 0
    · exact Or.inl hz
    · exact Or.inr (fun h' => he ⟨by omega, h'⟩)

/-! ## EIP-1559 fee-market refinement (tx-level) -/

/-- EIP-1559 settlement: from London (`k ≥ 11`) the fee settlement `Tx.finish` runs
    (`Tx.settle` with refund `(gas − gasUsed) · price` and miner fee `gasUsed · (price −
    baseFee)`) is an `IsFeeSettlement`. Precondition: the coinbase credit does not
    overflow 2^256 (EELS's `U256 +` raises there; unreachable with real balances).
    EELS `forks/london/fork.py::process_transaction` 813-835. -/
theorem feeSettlement_sound (k : Nat) (s : Evm.Frontier.State) (sender coinbase : Evm.Address)
    (gasLimit gasUsed price baseFee : Nat) (hk : 11 ≤ k)
    (hno : ((s.addBalance sender (Evm.U256.ofNat ((gasLimit - gasUsed) * price))).getAccount
              coinbase).balance.toNat + gasUsed * (price - baseFee) < 2 ^ 256) :
    IsFeeSettlement sender coinbase gasLimit gasUsed price baseFee s
      (Evm.Frontier.Vm.Tx.settle k s sender coinbase ((gasLimit - gasUsed) * price)
        (gasUsed * (price - baseFee))) := by
  unfold IsFeeSettlement Evm.Frontier.Vm.Tx.settle
  rw [ite_eq_left (by omega)]
  unfold Evm.SpuriousDragon.settleFees Evm.SpuriousDragon.payCoinbase
  generalize s.addBalance sender (Evm.U256.ofNat ((gasLimit - gasUsed) * price)) = r at hno ⊢
  generalize gasUsed * (price - baseFee) = M at hno ⊢
  simp only
  by_cases h1 : (r.getAccount coinbase).balance + Evm.U256.ofNat M ≠ 0
  · rw [ite_eq_left h1]
    refine ⟨by simp [Evm.CL.EffectSelfdestruct.getAccount_setAccount], ?_⟩
    intro a ha; simp [Evm.CL.EffectSelfdestruct.getAccount_setAccount, ha]
  · rw [ite_eq_right h1]
    have h0 : (r.getAccount coinbase).balance + Evm.U256.ofNat M = 0 := by simpa using h1
    have hz : (r.getAccount coinbase).balance = 0 ∧ M = 0 := by
      have hno' : BitVec.toNat (r.getAccount coinbase).balance + M < 2 ^ 256 := hno
      have hM : M < 2 ^ 256 := by omega
      have hz0 : BitVec.toNat (0 : Evm.U256) = 0 := rfl
      have := congrArg BitVec.toNat h0
      simp only [BitVec.toNat_add, Evm.U256.ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hM,
        Nat.mod_eq_of_lt hno', hz0] at this
      refine ⟨BitVec.eq_of_toNat_eq ?_, by omega⟩
      rw [hz0]; omega
    split
    · refine ⟨by simp [Evm.CL.EffectSettle.getAccount_deleteAccount, hz.2, hz.1]; rfl, ?_⟩
      intro a ha; simp [Evm.CL.EffectSettle.getAccount_deleteAccount, ha]
    · exact ⟨by simp [hz.1, hz.2]; rfl, fun _ _ => rfl⟩

/-! ## EIP-3529 refund cap refinement (tx-level) -/

/-- EIP-3529 refund cap: from London (`k ≥ 11`) the gas a tx is charged
    (`Tx.gasUsed`, the emitted `txGasUsed`) is the gas it used less the refund
    `min(refund_counter, gas_used // 5)` (and from Prague at least the EIP-7623 floor).
    EELS `forks/london/fork.py::process_transaction` 809-810 (`tx_gas_refund = min(
    tx_gas_used_before_refund // 5, refund_counter)`). -/
theorem refundCap_sound (k g : Nat) (tx : Evm.Frontier.Vm.Tx.Tx) (o : Evm.Frontier.Vm.Tx.Out) :
    Evm.Frontier.Vm.Tx.gasUsed k tx o = g → 11 ≤ k →
    ∃ refund, IsRefundCapped (tx.gas - o.gasLeft) o.env.refundCounter refund ∧
      g = max ((tx.gas - o.gasLeft) - refund) (Evm.Frontier.Vm.Tx.floor k tx) := by
  intro hg hk; subst hg
  refine ⟨_, rfl, ?_⟩
  have hk' : ¬ k < 11 := by omega
  simp [Evm.Frontier.Vm.Tx.gasUsed, Evm.Frontier.Vm.Tx.floor, Evm.CL.GasEmit.txGasUsed,
    Evm.CL.GasEmit.refundCap, Evm.CL.GasEmit.Expr.eval, Evm.Frontier.Vm.Tx.gasEnv, refundCapDivisor,
    Evm.CL.GasEmit.fork, Evm.CL.GasEmit.calldataFloorGas, hk']

/-! ## EIP-3529 SELFDESTRUCT refund removal -/

/-- EIP-3529 SELFDESTRUCT: London's handler leaves the refund counter alone. EELS
    `forks/london/vm/instructions/system.py::selfdestruct` (493-) has no `refund_counter`
    line (Berlin's `evm.refund_counter += REFUND_SELF_DESTRUCT` is gone). -/
theorem selfdestructRefundDelta_sound (evm evm' : Evm) :
    Evm.London.Vm.Effect.doSelfdestructLondon evm = .ok evm' →
    ∃ delta, IsSelfdestructRefundDelta evm.env evm'.env delta := by
  intro h
  refine ⟨0, ?_⟩
  unfold Evm.London.Vm.Effect.doSelfdestructLondon at h
  by_cases hs : evm.message.isStatic = true
  · simp [hs, bind, Except.bind] at h
  · simp only [hs, Bool.false_eq_true, ite_false, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
    rcases h with ⟨u, -, g, -, h⟩
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨rfl, ?_⟩
    simp only [Evm.SpuriousDragon.Vm.touchAddr, Evm.Berlin.Vm.Effect.warmAddr]
    split <;> split <;> rfl

/-! ## Notes

    - Several of the above are *identity refinements*: the spec
      relation is a closed-form equation and the impl computes it
      directly. The soundness obligation reduces to definitional
      equality once the impl callsite is extracted.

    - BASEFEE soundness is a one-liner via the
      `nullaryPush_sound` shape lemma. -/

end Evm.London.Spec.Refinement
