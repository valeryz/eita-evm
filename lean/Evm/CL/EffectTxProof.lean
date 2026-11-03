import Evm.CL.EffectTx
import Evm.CL.EffectCallProof
import Evm.CL.EffectEndTxProof

/-! # CL/EffectTxProof — `EffectTx.term` IS every fork's transaction

`tx_refines`: for every fork ordinal `k`, block environment, world, sender and tx, ANY
precompile table `pre`, ANY frame run `runSub` and ANY authority recovery `recover`, the
derived tx effect run from the world (no per-tx sets yet) and the spec's message
(`Evm.Frontier.Vm.Tx.message`, which every fork's `processTransaction` runs) agree:

* the term rejects exactly the txs `Tx.invalid` rejects;
* for a valid tx, the term's world, accounts_to_delete, touched set and refund counter are
  the message's (EQUAL), the gas it charged is the gas the message used, and its flag is
  the message's success.

`apply_tx_refines` composes it with the settlement (`settle_refines`) and the end of tx
(`endTx_refines`): the wrapper's sequence — the term, `spec-tx-gas-used`, the two
settlement terms, the two end-of-tx terms — leaves the state `Tx.run` does (extensionally:
existence, accounts, storage), with its gas used and success.

Assumptions, stated: a frame never ends with more gas than it was given (`hmono`); a
precompile never returns more gas than it got (`hpmono`); for the settlement and the end of
tx, the message leaves the sender existing and only existing accounts carrying storage
(`WF`) and the fee does not wrap the coinbase balance (as `settle_refines`). Logs are not
part of the effect state (the observed call frames and transfer facts aside); chain rules
(Arc's veto and native precompiles) are outside (meaning "none"). -/

set_option linter.unusedSimpArgs false

namespace Evm.CL.EffectTx

open Evm.CL.EffectIR
open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Environment Evm Exception Message)
open Evm.Frontier.Vm.Tx

/-! ## The validation -/

theorem validateFrom_run (c : Ctx) (h : HState) (hck : c.bool "checked" = true) :
    ∀ (ps : List BExp) (n : Nat) (s : Stmt),
      (validateFrom n ps s).run c h =
        match ps.findIdx? (fun p => p.eval c h) with
        | some i => { h with rej := n + i }
        | none => s.run c h := by
  intro ps
  induction ps with
  | nil => intro n s; simp [validateFrom]
  | cons p ps ih =>
    intro n s
    simp only [validateFrom, Stmt.run, BExp.eval, hck, Bool.true_and, List.findIdx?_cons]
    cases hp : p.eval c h
    · simp only [Bool.false_eq_true, if_false, ih]
      cases ps.findIdx? (fun p => p.eval c h) <;> simp [Nat.add_assoc, Nat.add_comm 1]
    · simp

/-! ## The term's inputs -/

/-- The term's inputs as `apply-tx` computes them for a tx of the chain (validated,
    no chain extra), with the precompile table `pre`, the frame oracle `child` and the
    authority recovery `recover`. -/
def ctxOf (k : Nat) (benv : Environment) (st : State) (sender : Evm.Address) (tx : Tx)
    (pre : Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (child : HState → Nat → ChildRes)
    (recover : Evm.Prague.Authorization → Option Evm.Address) : Ctx :=
  { fork := k
    addr := fun x => if x = "sender" then sender else if x = "target" then Evm.Frontier.Vm.Tx.target st sender tx
                     else if x = "coinbase" then benv.coinbase else 0
    word := fun x => if x = "value" then tx.value else if x = "chain-id" then benv.chainId else 0
    bool := fun x => if x = "create" then tx.to.isNone else if x = "prague" then decide (k ≥ 17)
                     else if x = "checked" then true
                     else if x = "blob-version-ok" then tx.blobHashes.all versionOk
                     else false
    nat := fun x =>
      if x = "gas-limit" then tx.gas else if x = "intrinsic" then intrinsic k tx
      else if x = "floor" then floor k tx else if x = "egp" then egp benv.baseFeePerGas tx
      else if x = "type" then tx.type else if x = "tx-nonce" then tx.nonce
      else if x = "max-fee" then tx.maxFee else if x = "max-prio" then tx.maxPrio
      else if x = "gas-price" then tx.gasPrice else if x = "base-fee" then benv.baseFeePerGas
      else if x = "blob-count" then tx.blobHashes.length
      else if x = "max-fee-blob" then tx.maxFeePerBlobGas
      else if x = "blob-base-fee" then benv.blobBaseFee
      else if x = "auth-count" then tx.auths.length
      else if x = "data-len" then tx.data.size else 0
    accessList := tx.accessList, auths := tx.auths, recover := recover, input := tx.data,
    pre := pre, child := child }

/-- The term's starting state: the world, no per-tx sets yet. -/
def h0 (st : State) : HState :=
  { state := st, destroyed := [], touched := [], accessed := [], created := [], refund := 0 }

/-- `letLt`'s binding. -/
def lb (c : Ctx) (h : HState) (x : String) (a b : GExp) : Ctx :=
  { c with bool := fun y => if y = x then decide (a.eval c h < b.eval c h) else c.bool y }

/-- The context once `compares` has bound its comparisons. -/
def cmpCtx (c : Ctx) (h : HState) : Ctx :=
  let c := lb c h "lt-gas" gasLimit required
  let c := lb c h "big-init" (.lit 49152) (.var "data-len")
  let c := lb c h "nonce-ok" (.var "tx-nonce") (.lit (2 ^ 64 - 1))
  let c := lb c h "big-gas" (.lit 16777216) gasLimit
  let c := lb c h "lt-prio" (.var "max-fee") (.var "max-prio")
  let c := lb c h "lt-mf" (.var "max-fee") (.var "base-fee")
  let c := lb c h "lt-gp" (.var "gas-price") (.var "base-fee")
  let c := lb c h "many-blobs" (.lit 6) (.var "blob-count")
  let c := lb c h "lt-mfb" (.var "max-fee-blob") (.var "blob-base-fee")
  let c := lb c h "n-lo" (.nonce sender) (.var "tx-nonce")
  let c := lb c h "n-hi" (.var "tx-nonce") (.nonce sender)
  lb c h "poor" (.ofWord (.balance sender)) maxCost

theorem compares_run (c : Ctx) (h : HState) (s : Stmt) :
    (compares s).run c h = s.run (cmpCtx c h) h := by
  -- v4.29: also unfold the GExp literals so `GExp.eval _ h required`
  -- reduces away from the differing (nested) records on the two sides; the
  -- residual is kernel-defeq (iota under free variables), which `rfl` closes.
  simp only [compares, Stmt.run, cmpCtx, lb, GExp.eval, BExp.eval, WExp.eval, AExp.eval,
    required, gasLimit, maxCost]
  try rfl

theorem maxInit_eq : Evm.Frontier.Vm.Create.maxInitCodeSize = 49152 := rfl

theorem type3_iff (t : Nat) : (3 ≤ t ∧ t < 4) ↔ t = 3 := by omega

theorem isType3_eq (t : Nat) : (decide (3 ≤ t) && !decide (4 ≤ t)) = decide (t = 3) := by
  apply Bool.eq_iff_iff.mpr; simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]; omega
theorem isType4_eq (t : Nat) : (decide (4 ≤ t) && !decide (5 ≤ t)) = decide (t = 4) := by
  apply Bool.eq_iff_iff.mpr; simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]; omega
theorem not_one_le_length {α : Type} (l : List α) : (!decide (1 ≤ l.length)) = decide (l = []) := by
  cases l <;> simp
theorem lt_gas_iff (g i f : Nat) : g < i + (f - i) ↔ g < max i f := by
  simp only [Nat.max_def]; split <;> omega
theorem badType_eq (k t : Nat) :
    (decide (1 ≤ t) && !decide (10 ≤ k) || (decide (2 ≤ t) && !decide (11 ≤ k) ||
      (decide (3 ≤ t) && !decide (16 ≤ k) || (decide (4 ≤ t) && !decide (17 ≤ k) || decide (5 ≤ t)))))
    = decide ((if 17 ≤ k then 4 else if 16 ≤ k then 3 else if 11 ≤ k then 2 else if 10 ≤ k then 1 else 0) < t) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  repeat' split
  all_goals omega
theorem nonce_ok_eq (n : Nat) : decide (n < 18446744073709551615) = !decide (18446744073709551615 ≤ n) := by
  by_cases h : n < 18446744073709551615 <;> simp [h] <;> omega
theorem lt_gp_eq (t a b : Nat) : (!decide (2 ≤ t) && decide (a < b)) = (decide (t < 2) && decide (a < b)) := by
  by_cases h : t < 2 <;> simp [h] <;> omega

theorem rules_eval (k : Nat) (benv : Environment) (st : State) (sender : Evm.Address) (tx : Tx)
    pre child recover :
    rules.map (fun p => p.eval (cmpCtx (ctxOf k benv st sender tx pre child recover) (h0 st)) (h0 st))
      = (Evm.Frontier.Vm.Tx.rules k benv st sender tx).map (·.1) := by
  simp [rules, Evm.Frontier.Vm.Tx.rules, cmpCtx, lb, ctxOf, h0, BExp.eval, GExp.eval, WExp.eval, AExp.eval,
    badType, isType, required, maxCost, blobGas, gasLimit, maxType, maxGasFee, Evm.Frontier.Vm.Tx.blobGas, maxInit_eq,
    Evm.Frontier.State.getBalance, type3_iff, isType3_eq, isType4_eq, not_one_le_length,
    lt_gas_iff, badType_eq]
  and_intros
  all_goals first
    | exact nonce_ok_eq _
    | (apply Bool.eq_iff_iff.mpr; simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not]; omega)
    | exact lt_gp_eq _ _ _
    | (cases tx.to <;> simp)
    | (cases Evm.Prague.State.parseDelegation (st.getAccount sender).code <;> simp)
    | skip

theorem findIdx_rules (k : Nat) (benv : Environment) (st : State) (sender : Evm.Address) (tx : Tx)
    pre child recover :
    rules.findIdx? (fun p => p.eval (cmpCtx (ctxOf k benv st sender tx pre child recover) (h0 st)) (h0 st))
      = (Evm.Frontier.Vm.Tx.rules k benv st sender tx).findIdx? (·.1) := by
  have h := congrArg (fun l => List.findIdx? id l) (rules_eval k benv st sender tx pre child recover)
  simp only [List.findIdx?_map] at h
  exact h

theorem invalid_none_iff (k : Nat) (benv : Environment) (st : State) (sender : Evm.Address) (tx : Tx) :
    invalid k benv st sender tx = none ↔
      (Evm.Frontier.Vm.Tx.rules k benv st sender tx).findIdx? (·.1) = none := by
  unfold invalid
  rw [Option.map_eq_none_iff, List.find?_eq_none, List.findIdx?_eq_none_iff]
  simp

/-- **The validation.** The term rejects exactly the txs `Tx.invalid` rejects; a valid tx
    goes on to `main` with the comparisons bound. -/
theorem validate_run (k : Nat) (benv : Environment) (st : State) (sender : Evm.Address) (tx : Tx)
    pre child recover :
    let c := ctxOf k benv st sender tx pre child recover
    (invalid k benv st sender tx = none → term.run c (h0 st) = main.run (cmpCtx c (h0 st)) (h0 st)) ∧
    (invalid k benv st sender tx ≠ none → (term.run c (h0 st)).rej ≠ 0) := by
  intro c
  have hck : (cmpCtx c (h0 st)).bool "checked" = true := by simp [c, cmpCtx, lb, ctxOf]
  have hrun : term.run c (h0 st) = (validate main).run (cmpCtx c (h0 st)) (h0 st) := by
    simp only [term, Stmt.run, compares_run]
  rw [hrun]
  unfold validate
  rw [validateFrom_run _ _ hck, findIdx_rules]
  constructor
  · intro hv; rw [(invalid_none_iff _ _ _ _ _).mp hv]
  · intro hv
    cases hf : (Evm.Frontier.Vm.Tx.rules k benv st sender tx).findIdx? (·.1) with
    | none => exact absurd ((invalid_none_iff _ _ _ _ _).mpr hf) hv
    | some i => simp

/-! ## The prologue: the charge, the accessed sets -/

open Evm.CL.EffectCreate (envOf toRes)
open Evm.CL.EffectCall (cwarm_eq ctouch_eq existsDead)

theorem ins_eq : Evm.Frontier.Vm.Tx.ins = insertSet := rfl

/-- What the context must hold for the prologue. -/
structure PBound (c : Ctx) (k : Nat) (benv : Environment) (st : State) (sdr : Evm.Address) (tx : Tx) :
    Prop where
  fork  : c.fork = k
  snd   : c.addr "sender" = sdr
  tgt   : c.addr "target" = Evm.Frontier.Vm.Tx.target st sdr tx
  cb    : c.addr "coinbase" = benv.coinbase
  al    : c.accessList = tx.accessList
  gl    : c.nat "gas-limit" = tx.gas
  egp   : c.nat "egp" = egp benv.baseFeePerGas tx
  bc    : c.nat "blob-count" = tx.blobHashes.length
  bbf   : c.nat "blob-base-fee" = benv.blobBaseFee
  extra : c.nat "extra" = 0

/-- The charge and the warm-ups leave the tx environment the message starts in. -/
theorem prologue_run (c : Ctx) (k : Nat) (benv : Environment) (st : State) (sdr : Evm.Address) (tx : Tx)
    (hB : PBound c k benv st sdr tx) :
    warmS.run c (chargeS.run c (h0 st)) = HState.ofEnv (env0 k benv st sdr tx) := by
  simp only [chargeS, warmS, Stmt.run, BExp.eval, AExp.eval,
    hB.snd, hB.tgt, hB.cb, hB.al, hB.fork]
  simp only [upfront, GExp.eval, BExp.eval, hB.gl, hB.egp, hB.bc, hB.bbf, hB.extra, blobGas, gasLimit,
    hB.fork, Nat.add_zero]
  unfold HState.ofEnv env0 charged accessedSeed slotSeed Evm.Frontier.Vm.Tx.blobGas
  by_cases h10 : k ≥ 10 <;> simp [h0, h10, ins_eq, Nat.mul_assoc]

/-! ## EIP-7702: the authorization list -/

theorem ofNat_toNat_small (n : Nat) (h : n < 2 ^ 256) : (Evm.U256.ofNat n).toNat = n := by
  simp [Evm.U256.ofNat, Evm.U256.toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem pos_iff (x : Evm.U256) : x ≠ 0 ↔ 0 < x.toNat := by
  unfold Evm.U256.toNat
  constructor
  · intro h; apply Nat.pos_of_ne_zero; intro h0; exact h (BitVec.eq_of_toNat_eq (by simpa using h0))
  · intro h h0; subst h0; simp at h

/-- One authorization: the term's body is `Tx.authorize`. -/
theorem authBody_run (c : Ctx) (e : Environment) (a : Evm.Prague.Authorization)
    (hc : c.word "chain-id" = e.chainId) :
    authBody.run (c.withAuth a) (HState.ofEnv e) = HState.ofEnv (authorize e.chainId c.recover e a) := by
  have hcid : (c.withAuth a).word "chain-id" = e.chainId := by simp [Ctx.withAuth, hc]
  have h2 : (Evm.U256.ofNat 2).toNat = 2 := ofNat_toNat_small 2 (by decide)
  have hN : (Evm.U256.ofNat secp256k1n).toNat = secp256k1n := ofNat_toNat_small _ (by decide)
  have hN2 : (Evm.U256.ofNat (secp256k1n / 2)).toNat = secp256k1n / 2 := ofNat_toNat_small _ (by decide)
  have hsc : ((decide (a.yParity.toNat < 2) && (decide (a.r ≠ 0) && (decide (a.r.toNat < secp256k1n) &&
      (decide (a.s ≠ 0) && !decide (secp256k1n / 2 < a.s.toNat))))) = true) ↔
      (a.yParity.toNat ≤ 1 ∧ 0 < a.r.toNat ∧ a.r.toNat < secp256k1n ∧ 0 < a.s.toNat ∧
        a.s.toNat ≤ secp256k1n / 2) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, pos_iff]
    omega
  unfold authBody authorize
  simp only [Stmt.run, BExp.eval, WExp.eval, GExp.eval, AExp.eval, hcid]
  simp only [Ctx.withAuth, if_true, show ("a-yp" = "a-chain") = False by decide,
    show ("a-r" = "a-chain") = False by decide, show ("a-r" = "a-yp") = False by decide,
    show ("a-s" = "a-chain") = False by decide, show ("a-s" = "a-yp") = False by decide,
    show ("a-s" = "a-r") = False by decide, show ("authority" = "a-addr") = False by decide,
    if_false, h2, secpN, hN, hN2]
  by_cases hch : a.chainId = e.chainId ∨ a.chainId = 0
  · have hch' : (!(decide (a.chainId = e.chainId) || decide (a.chainId = 0))) = false := by
      rcases hch with h | h <;> simp [h]
    simp only [hch', hch, Bool.false_eq_true, if_false, not_true_eq_false]
    by_cases hno : BitVec.toNat a.nonce < 2 ^ 64 - 1
    · have hno' : ¬ (a.nonce.toNat ≥ 2 ^ 64 - 1) := by
        simp only [Evm.U256.toNat] at *; omega
      simp only [hno, if_true, hno', if_false]
      by_cases hs : a.yParity.toNat ≤ 1 ∧ 0 < a.r.toNat ∧ a.r.toNat < secp256k1n ∧ 0 < a.s.toNat ∧
          a.s.toNat ≤ secp256k1n / 2
      · rw [if_pos (hsc.mpr hs), if_neg (fun h => h hs)]
        cases hr : c.recover a with
        | none => rfl
        | some au =>
          simp only [HState.ofEnv, cwarm_eq]
          -- v4.29: simp's HState.ofEnv/cwarm_eq unfolding normalizes the
          -- condition to this form; state the case split in exactly it, or
          -- if_pos/if_neg can't match the ite.
          by_cases hcode : ¬(e.state.getAccount au).code = ByteArray.empty ∧
              Evm.Prague.State.parseDelegation (e.state.getAccount au).code = none
          · have hb : (!decide ((e.state.getAccount au).code.size = 0) &&
                !(Evm.Prague.State.parseDelegation (e.state.getAccount au).code).isSome) = true := by
              -- v4.29: simp's decide/≠ normal forms no longer match the
              -- Bool lemmas' shapes; case-split the two booleans instead.
              by_cases hsz : (e.state.getAccount au).code.size = 0
              · cases hpd : (Evm.Prague.State.parseDelegation (e.state.getAccount au).code).isSome
                · simp_all
                · simp_all
              · cases hpd : (Evm.Prague.State.parseDelegation (e.state.getAccount au).code).isSome
                · simp_all
                · simp_all
            -- v4.29: neither rw nor simp only [if_pos ...] matches these
            -- ites; rewriting the condition propositions themselves works.
            simp [hb, hcode]
          · have hb : ¬ (!decide ((e.state.getAccount au).code.size = 0) &&
                !(Evm.Prague.State.parseDelegation (e.state.getAccount au).code).isSome) = true := by
              by_cases hsz : (e.state.getAccount au).code.size = 0 <;>
                cases hpd : (Evm.Prague.State.parseDelegation (e.state.getAccount au).code).isSome <;>
                simp_all
            simp [hb, hcode]
            by_cases hnon : (e.state.getAccount au).nonce = a.nonce.toNat
            · -- v4.29: discharge the nonce if by rewriting its (bare Prop)
              -- condition; rw/if_pos can't match the ite here.
              simp [hnon]
              by_cases hex : e.state.accountExists au = true
              · simp [hex, hnon]
              · simp [hex, hnon]
            · have hnb : ¬ decide ((e.state.getAccount au).nonce = BitVec.toNat a.nonce) = true := by
                simpa using hnon
              simp [hnb, hnon]
      · simp only [if_neg (fun h => hs (hsc.mp h)), if_pos hs]
    · have hno' : a.nonce.toNat ≥ 2 ^ 64 - 1 := by simp only [Evm.U256.toNat] at *; omega
      simp only [hno, if_false, hno', if_true]
  · have hch' : (!(decide (a.chainId = e.chainId) || decide (a.chainId = 0))) = true := by
      have h1 : decide (a.chainId = e.chainId) = false := decide_eq_false (fun h => hch (Or.inl h))
      have h0 : decide (a.chainId = 0) = false := decide_eq_false (fun h => hch (Or.inr h))
      rw [h1, h0]; rfl
    simp only [hch', if_true]
    simp only [if_pos hch]

theorem authorize_chainId (cid : Evm.U256) (r : Evm.Prague.Authorization → Option Evm.Address)
    (e : Environment) (a : Evm.Prague.Authorization) : (authorize cid r e a).chainId = e.chainId := by
  unfold authorize
  simp only [cwarm_eq]
  repeat' split
  all_goals rfl

/-- The authorization list: the term's loop is `Tx.authorize` folded over it. -/
theorem forAuths_fold (c : Ctx) (cid : Evm.U256) (hc : c.word "chain-id" = cid) :
    ∀ (l : List Evm.Prague.Authorization) (e : Environment), e.chainId = cid →
      l.foldl (fun h' a => authBody.run (c.withAuth a) h') (HState.ofEnv e)
        = HState.ofEnv (l.foldl (authorize cid c.recover) e) := by
  intro l
  induction l with
  | nil => intro e _; rfl
  | cons a l ih =>
    intro e he
    subst he
    simp only [List.foldl_cons]
    rw [authBody_run c e a hc]
    exact ih _ (authorize_chainId _ _ _ _)

/-- The spec's environment after the authorizations (`Tx.call`'s `e1`). -/
def e1S (k : Nat) (e : Environment) (tx : Tx) (recover : Evm.Prague.Authorization → Option Evm.Address) :
    Environment :=
  if k ≥ 17 then tx.auths.foldl (authorize e.chainId recover) e else e

theorem authsS_run (c : Ctx) (k : Nat) (e : Environment) (tx : Tx)
    (hk : c.bool "prague" = decide (k ≥ 17)) (hcr : c.bool "create" = tx.to.isNone)
    (hau : c.auths = tx.auths) (hc : c.word "chain-id" = e.chainId) :
    authsS.run c (HState.ofEnv e) =
      HState.ofEnv (if tx.to.isNone then e else e1S k e tx c.recover) := by
  unfold authsS e1S
  simp only [Stmt.run, BExp.eval, hk, hcr, hau]
  cases hto : tx.to.isNone
  · by_cases h17 : k ≥ 17
    · simp only [h17, decide_true, Bool.not_false, Bool.and_self, if_true, Bool.false_eq_true, if_false]
      exact forAuths_fold c e.chainId hc tx.auths e rfl
    · simp [h17]
  · simp

/-! ## The message -/

/-- What the context holds when the message starts. -/
structure MBound (c : Ctx) (k : Nat) (sdr tgt : Evm.Address) (tx : Tx) (G : Nat) (hasd : Bool)
    (dlg : Evm.Address) : Prop where
  fork   : c.fork = k
  snd    : c.addr "sender" = sdr
  tgt    : c.addr "target" = tgt
  dlg    : c.addr "deleg" = dlg
  create : c.bool "create" = tx.to.isNone
  hasd   : c.bool "hasdeleg" = hasd
  value  : c.word "value" = tx.value
  gas    : c.nat "gas-limit" - c.nat "intrinsic" = G
  input  : c.input = tx.data

theorem gas_eval (c : Ctx) (h : HState) : gas.eval c h = c.nat "gas-limit" - c.nat "intrinsic" := rfl

/-- The term's state after a child run `res` from `h` (`runTx`). -/
def afterRes (h : HState) : ChildRes → HState
  | .err => h
  | .ok h' _ _ _ => { h' with gas := h.gas, out := h.out, rdata := h.rdata, facts := h.facts, rej := h.rej }

/-- `callEnd`, closed: the snapshot `s` (what `rollback` restores), the state `h` the run left. -/
def callEndC (c : Ctx) (s h : HState) (G : Nat) (tgt : Evm.Address) : ChildRes → HState
  | .err => { s with gas := h.gas + G, out := 0, rdata := h.rdata }
  | .ok _ g _ true => { s with gas := h.gas + (G - g), out := 0, rdata := h.rdata }
  | .ok _ g _ false =>
    let h' := if h.state.accountExists tgt && EffectIR.isDead h.state tgt
              then (if c.fork ≥ 4 then { h with touched := insertSet h.touched tgt } else h) else h
    { h' with gas := h.gas + (G - g), out := Evm.U256.ofNat 1 }

theorem callEnd_run (c : Ctx) (h : HState) (G : Nat) (tgt : Evm.Address)
    (hG : c.nat "gas-limit" - c.nat "intrinsic" = G) (ht : c.addr "target" = tgt) :
    callEnd.run c h = callEndC c (c.snaps "snap") h G tgt (c.res "r") := by
  unfold callEnd fail0 used callEndC
  cases hr : c.res "r" with
  | err => simp [Stmt.run, BExp.eval, GExp.eval, WExp.eval, hr, ChildRes.isErr, gas_eval, hG]
  | ok h' g o rv =>
    cases rv
    · simp only [Stmt.run, BExp.eval, GExp.eval, WExp.eval, AExp.eval, hr, ChildRes.isErr, ChildRes.isRev,
        Bool.false_eq_true, if_false, gas_eval, hG, ht, ChildRes.gas]
      cases (h.state.accountExists tgt && EffectIR.isDead h.state tgt) <;> by_cases h4 : c.fork ≥ 4 <;>
        simp [h4]
    · simp [Stmt.run, BExp.eval, GExp.eval, WExp.eval, hr, ChildRes.isErr, ChildRes.isRev, gas_eval, hG,
        ChildRes.gas]

/-- The frame's code: the delegate's under EIP-7702, else the target's. -/
def codeOfD (e2 : Environment) (to : Evm.Address) (d : Option Evm.Address) : Evm.Bytes :=
  match d with
  | some a => (e2.state.getAccount a).code
  | none => (e2.state.getAccount to).code

/-- The call's frame run as the spec does it, from the term's state. -/
def callOracle (e2 : Environment) (sdr to : Evm.Address) (tx : Tx) (d : Option Evm.Address)
    (runSub : Evm → Except Exception Evm) : HState → Nat → ChildRes := fun h g =>
  toRes (runSub (Evm.fresh (callMsg sdr to tx (codeOfD e2 to d) g) (envOf e2 h)))

/-- The child's world of a call: existence before EIP-161, the value. -/
def callWorld (k : Nat) (e2 : Environment) (sdr to : Evm.Address) (v : Evm.U256) : State :=
  let st := if k ≥ 4 then e2.state else e2.state.touchAccount to
  if v = 0 then st else (st.subBalance sdr v).addBalance to v

theorem envOf_world (e : Environment) (st : State) (fs) :
    envOf e { HState.ofEnv e with state := st, facts := fs } = { e with state := st } := by
  simp [envOf, HState.ofEnv]

theorem pre_eval (c : Ctx) (h : HState) (a : AExp) : (BExp.pre a).eval c h = (c.pre (a.eval c)).isSome := rfl

/-- `callTail`'s end on the frame's result. -/
def callResO (k : Nat) (e2 : Environment) (to : Evm.Address) : Except Exception Evm → Out
  | .error _ => { env := e2, gasLeft := 0, success := false }
  | .ok sub =>
    if sub.reverted then { env := e2, gasLeft := sub.gasLeft, success := false, output := sub.output }
    else
      { env := if k ≥ 4 ∧ sub.env.state.accountExists to ∧ (sub.env.state.getAccount to).isEmpty
               then Evm.Frontier.Vm.Call.touch sub.env to else sub.env,
        gasLeft := sub.gasLeft, success := true, output := sub.output }

/-- The term's end of a call agrees with `callResO`. -/
theorem callEnd_res (c : Ctx) (k : Nat) (e2 : Environment) (to : Evm.Address) (G : Nat) (h : HState)
    (res : Except Exception Evm) (hk : c.fork = k) (hg : h.gas = 0)
    (hm : ∀ sub, res = .ok sub → sub.gasLeft ≤ G) (hr0 : h.rej = 0) :
    let R := callEndC c (HState.ofEnv e2) (afterRes h (toRes res)) G to (toRes res)
    let o := callResO k e2 to res
    R.state = o.env.state ∧ R.destroyed = o.env.selfDestructSet ∧ R.touched = o.env.touched ∧
      R.refund = o.env.refundCounter ∧ R.gas + o.gasLeft = G ∧
      R.out = (if o.success then Evm.U256.ofNat 1 else 0) ∧ R.rej = 0 := by
  intro R o
  cases res with
  | error e => simp [R, o, callEndC, toRes, afterRes, callResO, HState.ofEnv, hg]
  | ok sub =>
    have hs : (sub.gasLeft : Nat) ≤ G := hm sub rfl
    have hsub : ∀ g : Nat, g ≤ G → G - g + g = G := fun g hg => by omega
    cases hrv : sub.reverted
    · simp only [R, o, callEndC, toRes, afterRes, callResO, hrv, Bool.false_eq_true, if_false, HState.ofEnv, hg,
        Nat.zero_add, existsDead, hk]
      by_cases h4 : k ≥ 4 <;> by_cases hex : (sub.env.state.accountExists to && (sub.env.state.getAccount to).isEmpty) = true
      · have hex' : sub.env.state.accountExists to = true ∧ (sub.env.state.getAccount to).isEmpty = true := by
          simpa using hex
        simp [h4, hex, hex', ctouch_eq, hr0]; exact hsub _ hs
      · have hex' : ¬ (sub.env.state.accountExists to = true ∧ (sub.env.state.getAccount to).isEmpty = true) := by
          simpa using hex
        simp [h4, hex, hex', hr0]; exact hsub _ hs
      · simp [h4, hex, hr0]; exact hsub _ hs
      · simp [h4, hex, hr0]; exact hsub _ hs
    · simp [R, o, callEndC, toRes, afterRes, callResO, hrv, HState.ofEnv, hg]; exact hsub _ hs

/-- **The call's tail.** From the snapshot `e2`, the term's call path is `Tx.callTail`. -/
theorem callPath_run (c : Ctx) (k : Nat) (e2 : Environment) (sdr to : Evm.Address) (tx : Tx) (G : Nat)
    (d : Option Evm.Address) (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm)
    (hB : MBound c k sdr to tx G d.isSome (d.getD 0))
    (hsnap : c.snaps "snap" = HState.ofEnv e2) (hpre : c.pre = pre e2)
    (hchild : c.child = callOracle e2 sdr to tx d runSub)
    (hmono : ∀ sub, runSub (Evm.fresh (callMsg sdr to tx (codeOfD e2 to d) G)
        { e2 with state := callWorld k e2 sdr to tx.value }) = .ok sub → sub.gasLeft ≤ G)
    (hpmono : ∀ p o g', pre e2 to = some p → p tx.data G = .ok (o, g') → g' ≤ G) :
    let o := callTail k e2 sdr to tx G d pre runSub
    let R := callPath.run c (HState.ofEnv e2)
    R.state = o.env.state ∧ R.destroyed = o.env.selfDestructSet ∧ R.touched = o.env.touched ∧
      R.refund = o.env.refundCounter ∧ R.gas + o.gasLeft = G ∧
      R.out = (if o.success then Evm.U256.ofNat 1 else 0) ∧ R.rej = 0 := by
  intro o R
  -- the child's world, in the term
  let fs : List (Nat × Evm.Address × Evm.Address × Evm.U256) :=
    if tx.value = 0 then [] else [(0, sdr, to, tx.value)]
  let h2 : HState := { HState.ofEnv e2 with state := callWorld k e2 sdr to tx.value, facts := fs }
  have hpref : R = (Stmt.ite (.and (.not (.var "hasdeleg")) (.pre EffectTx.target))
      (.runPreTx EffectTx.target gas "r" callEnd) (.runTx gas "r" callEnd)).run c h2 := by
    simp only [R, callPath, transfer, Stmt.run, BExp.eval, WExp.eval, AExp.eval, hB.fork, hB.snd, hB.tgt,
      hB.value]
    unfold h2 callWorld fs
    by_cases h4 : k ≥ 4 <;> by_cases hv : tx.value = 0#256 <;>
      simp [h4, hv, HState.ofEnv, Evm.Frontier.State.subBalance, Evm.Frontier.State.getBalance]
  have hce : ∀ (rr : ChildRes) (hh : HState), callEnd.run { c with res := fun y => if y = "r" then rr else c.res y } hh
      = callEndC c (HState.ofEnv e2) hh G to rr := by
    intro rr hh
    rw [callEnd_run _ hh G to (by simpa using hB.gas) (by simpa using hB.tgt)]
    simp only [hsnap]; rfl
  have hworld : envOf e2 h2 = { e2 with state := callWorld k e2 sdr to tx.value } := envOf_world _ _ _
  rw [hpref]
  simp only [Stmt.run, BExp.eval, pre_eval, AExp.eval, hB.hasd, hB.tgt, gas_eval, hB.gas]
  rw [hce, hce]
  simp only [hpre]
  have hh2 : h2.gas = 0 := rfl
  -- the frame, as the spec builds it
  have hfr : ∀ code : Evm.Bytes, Evm.Frontier.Vm.Call.child
      { gasLeft := 0, message := callMsg sdr to tx code G, env := e2 } (callMsg sdr to tx code G)
      (if tx.value = 0 then (if k ≥ 4 then e2.state else e2.state.touchAccount to)
       else ((if k ≥ 4 then e2.state else e2.state.touchAccount to).subBalance sdr tx.value).addBalance to tx.value)
      = Evm.fresh (callMsg sdr to tx code G) { e2 with state := callWorld k e2 sdr to tx.value } := by
    intro code; rfl
  cases d with
  | some a =>
    simp only [Option.isSome_some, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
    rw [hchild]
    simp only [callOracle, hworld]
    simp only [o, callTail, Option.isSome_some, if_true, Option.bind_none, Evm.Frontier.Vm.Call.runChild, hfr]
    have key := callEnd_res c k e2 to G h2 (runSub (Evm.fresh (callMsg sdr to tx (codeOfD e2 to (some a)) G)
      { e2 with state := callWorld k e2 sdr to tx.value })) hB.fork rfl hmono rfl
    simp only [afterRes, callResO, codeOfD] at key ⊢
    exact key
  | none =>
    cases hp : pre e2 to with
    | none =>
      simp only [Option.isSome_none, Bool.not_false, Bool.true_and, hp, Option.isSome_none, Bool.false_eq_true,
        if_false]
      rw [hchild]
      simp only [callOracle, hworld]
      simp only [o, callTail, Option.isSome_none, Bool.false_eq_true, if_false, Option.bind_some, hp,
        Evm.Frontier.Vm.Call.runChild, hfr]
      have key := callEnd_res c k e2 to G h2 (runSub (Evm.fresh (callMsg sdr to tx (codeOfD e2 to none) G)
        { e2 with state := callWorld k e2 sdr to tx.value })) hB.fork rfl hmono rfl
      simp only [afterRes, callResO, codeOfD] at key ⊢
      exact key
    | some p =>
      simp only [Option.isSome_none, Bool.not_false, Bool.true_and, hp, Option.isSome_some, if_true]
      simp only [o, callTail, Option.isSome_none, Bool.false_eq_true, if_false, Option.bind_some, hp,
        Evm.Frontier.Vm.Call.runChild, callMsg, hB.input]
      cases hpr : p tx.data G with
      | error e =>
        have key := callEnd_res c k e2 to G h2 (.error e) hB.fork rfl (fun _ h => by cases h) rfl
        simp only [afterRes, callResO, toRes] at key ⊢
        exact key
      | ok og =>
        obtain ⟨out, g'⟩ := og
        have hg := hpmono p out g' hp hpr
        have key := callEnd_res c k e2 to G h2
          (.ok { Evm.Frontier.Vm.Call.child { gasLeft := 0, message := callMsg sdr to tx (codeOfD e2 to none) G, env := e2 }
                  (callMsg sdr to tx (codeOfD e2 to none) G)
                  (if tx.value = 0 then (if k ≥ 4 then e2.state else e2.state.touchAccount to)
                   else ((if k ≥ 4 then e2.state else e2.state.touchAccount to).subBalance sdr tx.value).addBalance to tx.value)
                with gasLeft := g', output := out, halted := true })
          hB.fork rfl (fun sub h => by cases h; exact hg) rfl
        simp only [afterRes, callResO, toRes, callMsg, codeOfD] at key ⊢
        exact key

/-! ### The creation -/

/-- The init frame's run as the spec does it, from the term's state. -/
def createOracle (e : Environment) (sdr new : Evm.Address) (tx : Tx)
    (runSub : Evm → Except Exception Evm) : HState → Nat → ChildRes := fun h g =>
  toRes (runSub (Evm.fresh (createMsg sdr new tx g)
    { envOf e h with originalState := e.originalState.destroyStorage new }))

theorem deposit_eval' (c : Ctx) (h : HState) :
    deposit.eval c h = Evm.Frontier.Vm.Gas.codeDeposit * (c.res "r").out.size := by
  simp only [deposit, GExp.eval]
  exact Evm.CL.EffectCreate.deposit_eval _

/-- The term's end of a creation agrees with `Tx.createEnd`. -/
theorem createEnd_res (c : Ctx) (k : Nat) (e : Environment) (new : Evm.Address) (G : Nat) (h : HState)
    (res : Except Exception Evm) (hk : c.fork = k) (hg : h.gas = 0)
    (hm : ∀ sub, res = .ok sub → sub.gasLeft ≤ G)
    (hsnap : c.snaps "snap" = HState.ofEnv e) (hres : c.res "r" = toRes res)
    (hG : c.nat "gas-limit" - c.nat "intrinsic" = G) (ht : c.addr "target" = new) (hr0 : h.rej = 0) :
    let R := createEnd.run c (afterRes h (toRes res))
    let o := Evm.Frontier.Vm.Tx.createEnd k e new res
    R.state = o.env.state ∧ R.destroyed = o.env.selfDestructSet ∧ R.touched = o.env.touched ∧
      R.refund = o.env.refundCounter ∧ R.gas + o.gasLeft = G ∧
      R.out = (if o.success then Evm.U256.ofNat 1 else 0) ∧ R.rej = 0 := by
  intro R o
  have hsub : ∀ g : Nat, g ≤ G → G - g + g = G := fun g hg => by omega
  have hsub2 : ∀ g d : Nat, g ≤ G → d ≤ g → G - g + d + (g - d) = G := fun g d h1 h2 => by omega
  cases res with
  | error x =>
    simp [R, o, createEnd, fail0, Stmt.run, BExp.eval, GExp.eval, WExp.eval, hres, toRes, afterRes,
      ChildRes.isErr, Evm.Frontier.Vm.Tx.createEnd, hsnap, HState.ofEnv, hg, gas_eval, hG]
  | ok sub =>
    have hs : (sub.gasLeft : Nat) ≤ G := hm sub rfl
    cases hrv : sub.reverted
    · -- the frame succeeded: the code deposit
      have hEF : ∀ (b : Bool), b = decide (0 < sub.output.size ∧ sub.output.get! 0 = (0xEF : UInt8)) → True :=
        fun _ _ => trivial
      simp only [R, o, createEnd, Stmt.run, BExp.eval, GExp.eval, hres, toRes, afterRes, ChildRes.isErr,
        ChildRes.isRev, hrv, Bool.false_eq_true, if_false, Evm.Frontier.Vm.Tx.createEnd, ChildRes.out,
        ChildRes.gas, deposit_eval', hk, gas_eval, hG]
      by_cases hef : k ≥ 11 ∧ 0 < sub.output.size ∧ sub.output.get! 0 = (0xEF : UInt8)
      · have hb : (decide (k ≥ 11) && decide (0 < sub.output.size ∧ sub.output.get! 0 = (0xEF : UInt8))) = true := by
          simp [hef.1, hef.2.1, hef.2.2]
        simp [hb, hef, fail0, Stmt.run, hsnap, HState.ofEnv, hg, used, gas_eval, hG, GExp.eval, hres, toRes,
          WExp.eval]
      · have hb : (decide (k ≥ 11) && decide (0 < sub.output.size ∧ sub.output.get! 0 = (0xEF : UInt8))) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          by_cases h11 : k ≥ 11
          · exact Or.inr (fun h' => hef ⟨h11, h'⟩)
          · exact Or.inl h11
        simp only [hb, hef, Bool.false_eq_true, if_false]
        by_cases hd : sub.gasLeft < Evm.Frontier.Vm.Gas.codeDeposit * sub.output.size
        · simp only [hd, if_true]
          by_cases h1 : k ≥ 1
          · simp [h1, fail0, Stmt.run, BExp.eval, hsnap, HState.ofEnv, hg, gas_eval, hG, GExp.eval, WExp.eval, hk]
          · simp [h1, Stmt.run, BExp.eval, HState.ofEnv, hg, used, gas_eval, hG, GExp.eval, WExp.eval, hk, hres,
              toRes, ChildRes.gas]
            exact ⟨hsub _ hs, hr0⟩
        · simp only [hd, if_false]
          have hdl : Evm.Frontier.Vm.Gas.codeDeposit * sub.output.size ≤ sub.gasLeft := Nat.le_of_not_lt hd
          by_cases hsz : k ≥ 4 ∧ sub.output.size > Evm.SpuriousDragon.Vm.Gas.maxCodeSize
          · simp only [hsz, and_self, if_true]
            have : 24576 < sub.output.size := hsz.2
            simp [hsz.1, this, Evm.SpuriousDragon.Vm.Gas.maxCodeSize, GExp.eval, hres, toRes, ChildRes.out,
              fail0, Stmt.run, BExp.eval, hsnap, HState.ofEnv, hg, gas_eval, hG, WExp.eval]
          · simp only [if_neg hsz]
            have hnf : ¬ (k ≥ 4 ∧ Evm.SpuriousDragon.Vm.Gas.maxCodeSize < sub.output.size) := hsz
            have hsel : ∀ (X S : HState), (if decide (k ≥ 4) = true then
                if Evm.SpuriousDragon.Vm.Gas.maxCodeSize < sub.output.size then X else S else S) = S := by
              intro X S; by_cases h4 : k ≥ 4
              · have : ¬ Evm.SpuriousDragon.Vm.Gas.maxCodeSize < sub.output.size := fun hh => hnf ⟨h4, hh⟩
                simp [h4, this]
              · simp [h4]
            rw [hsel]
            simp [succeed, Stmt.run, AExp.eval, ht, hres, toRes, ChildRes.out, GExp.eval, used, gas_eval, hG,
              deposit_eval', ChildRes.gas, HState.ofEnv, hg, WExp.eval]
            exact ⟨hsub2 _ _ hs hdl, hr0⟩
    · simp [R, o, createEnd, Stmt.run, BExp.eval, GExp.eval, WExp.eval, hres, toRes, afterRes, ChildRes.isErr,
        ChildRes.isRev, hrv, Evm.Frontier.Vm.Tx.createEnd, hsnap, HState.ofEnv, hg, used, gas_eval, hG,
        ChildRes.gas]
      exact hsub _ hs

/-- The init frame's world (`Create.childState`), the creation marked. -/
def createH (k : Nat) (e : Environment) (sdr new : Evm.Address) (tx : Tx) : HState :=
  { HState.ofEnv e with
    state := Evm.Frontier.Vm.Create.childState (Evm.Frontier.Vm.Create.Rules.ofOrd k) e.state sdr new tx.value,
    created := if e.createdAccounts.contains new then e.createdAccounts else new :: e.createdAccounts,
    facts := if tx.value = 0 then [] else [(0, sdr, new, tx.value)] }

theorem createFrame_eq (k : Nat) (e : Environment) (sdr new : Evm.Address) (tx : Tx) (G : Nat) :
    Evm.fresh (createMsg sdr new tx G)
        { envOf e (createH k e sdr new tx) with originalState := e.originalState.destroyStorage new }
      = Evm.Frontier.Vm.Create.child { gasLeft := 0, message := createMsg sdr new tx G, env := e }
          (createMsg sdr new tx G)
          (Evm.Frontier.Vm.Create.childState (Evm.Frontier.Vm.Create.Rules.ofOrd k) e.state sdr new tx.value) := by
  simp [Evm.Frontier.Vm.Create.child, envOf, createH, HState.ofEnv, createMsg]

/-- **The creation.** From the snapshot `e`, the term's creation path is `Tx.create`. -/
theorem createPath_run (c : Ctx) (k : Nat) (e : Environment) (sdr new : Evm.Address) (tx : Tx) (G : Nat)
    (runSub : Evm → Except Exception Evm)
    (hB : MBound c k sdr new tx G false 0)
    (hsnap : c.snaps "snap" = HState.ofEnv e)
    (hchild : c.child = createOracle e sdr new tx runSub)
    (hmono : ∀ sub, runSub (Evm.Frontier.Vm.Create.child { gasLeft := 0, message := createMsg sdr new tx G, env := e }
        (createMsg sdr new tx G)
        (Evm.Frontier.Vm.Create.childState (Evm.Frontier.Vm.Create.Rules.ofOrd k) e.state sdr new tx.value))
        = .ok sub → sub.gasLeft ≤ G) :
    let o := Evm.Frontier.Vm.Tx.create k e sdr new tx G runSub
    let R := createPath.run c (HState.ofEnv e)
    R.state = o.env.state ∧ R.destroyed = o.env.selfDestructSet ∧ R.touched = o.env.touched ∧
      R.refund = o.env.refundCounter ∧ R.gas + o.gasLeft = G ∧
      R.out = (if o.success then Evm.U256.ofNat 1 else 0) ∧ R.rej = 0 := by
  intro o R
  by_cases hcol : Evm.Frontier.Vm.Create.collides e.state new = true
  · simp [R, o, createPath, Stmt.run, BExp.eval, AExp.eval, hB.tgt, hcol, Evm.Frontier.Vm.Tx.create,
      HState.ofEnv, gas_eval, hB.gas, WExp.eval]
  · have hpref : R = (Stmt.runTx gas "r" createEnd).run c (createH k e sdr new tx) := by
      have hcol' : Evm.Frontier.Vm.Create.collides (HState.ofEnv e).state new = false := by
        simpa [HState.ofEnv] using hcol
      simp only [R, createPath, Stmt.run, BExp.eval, AExp.eval, hB.tgt, hcol', Bool.false_eq_true, if_false,
        transfer, WExp.eval, hB.snd, hB.value, hB.fork]
      unfold createH Evm.Frontier.Vm.Create.childState Evm.Frontier.Vm.Create.Rules.ofOrd
      by_cases h4 : k ≥ 4 <;> by_cases hv : tx.value = 0#256 <;>
        simp [h4, hv, HState.ofEnv, Evm.Frontier.State.subBalance, Evm.Frontier.State.getBalance,
          Evm.Frontier.State.touchAccount]
    rw [hpref]
    simp only [Stmt.run, gas_eval, hB.gas, hchild, createOracle, createFrame_eq]
    have hcm : ¬ Evm.Frontier.Vm.Create.collides e.state new = true := hcol
    have ho : o = Evm.Frontier.Vm.Tx.createEnd k e new (runSub (Evm.Frontier.Vm.Create.child
        { gasLeft := 0, message := createMsg sdr new tx G, env := e } (createMsg sdr new tx G)
        (Evm.Frontier.Vm.Create.childState (Evm.Frontier.Vm.Create.Rules.ofOrd k) e.state sdr new tx.value))) := by
      simp [o, Evm.Frontier.Vm.Tx.create, hcm]
    rw [ho]
    exact createEnd_res _ k e new G (createH k e sdr new tx) _ hB.fork rfl hmono (by simpa using hsnap)
      (by simp) (by simpa using hB.gas) (by simpa using hB.tgt) rfl

/-! ## The delegation and the snapshot -/

/-- The context once the delegation is bound (`deleg`, `hasdeleg`, and the warm-up's flag). -/
def cDel (c : Ctx) (d : Option Evm.Address) (dc : Bool) : Ctx :=
  let c1 : Ctx := { c with addr := fun y => if y = "deleg" then d.getD 0 else c.addr y,
                           bool := fun y => if y = "hasdeleg" then d.isSome else c.bool y }
  { c1 with bool := fun y => if y = "dcold" then dc else c1.bool y }

theorem cDel_bool (c : Ctx) (d : Option Evm.Address) (dc : Bool) (x : String)
    (h1 : x ≠ "dcold") (h2 : x ≠ "hasdeleg") : (cDel c d dc).bool x = c.bool x := by
  simp [cDel, h1, h2]

/-- The delegation (`Tx.call`'s `d` and `e2`): the delegate warmed. -/
theorem delegS_run (c : Ctx) (s : Stmt) (e1 : Environment) (tgt : Evm.Address) (g : Bool)
    (hg : (c.bool "prague" && !c.bool "create") = g) (ht : c.addr "target" = tgt) :
    let d := if g then Evm.Prague.State.parseDelegation (e1.state.getAccount tgt).code else none
    let e2 := match d with | some a => Evm.Frontier.Vm.Call.warm e1 a | none => e1
    ∃ dc, (delegS s).run c (HState.ofEnv e1) = s.run (cDel c d dc) (HState.ofEnv e2) := by
  intro d e2
  unfold delegS
  simp only [Stmt.run, BExp.eval, AExp.eval, hg, ht]
  cases hd : d with
  | none =>
    refine ⟨false, ?_⟩
    have : (if g = true then Evm.Prague.State.parseDelegation ((HState.ofEnv e1).state.getAccount tgt).code
            else none) = none := by simpa [HState.ofEnv, d] using hd
    simp only [this, Option.isSome_none, Bool.false_eq_true, if_false, if_true, e2, hd]
    rfl
  | some a =>
    refine ⟨!e1.accessedAddresses.contains a, ?_⟩
    have : (if g = true then Evm.Prague.State.parseDelegation ((HState.ofEnv e1).state.getAccount tgt).code
            else none) = some a := by simpa [HState.ofEnv, d] using hd
    simp only [this, Option.isSome_some, if_true, Option.getD_some, e2, hd, cwarm_eq]
    rfl

/-- The snapshot, then the creation or the call. -/
theorem messageS_run (c : Ctx) (h : HState) :
    messageS.run c h =
      (Stmt.ite (.var "create") createPath callPath).run { c with snaps := fun y => if y = "snap" then h else c.snaps y } h := by
  rfl

/-! ## The transaction -/

section tx
variable (k : Nat) (benv : Environment) (st : State) (sdr : Evm.Address) (tx : Tx)
  (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
  (runSub : Evm → Except Exception Evm) (recover : Evm.Prague.Authorization → Option Evm.Address)

/-- The spec's environments along a call (`Tx.call`'s `e1`, `d`, `e2`). -/
def e0S : Environment := env0 k benv st sdr tx
def tgtS : Evm.Address := Evm.Frontier.Vm.Tx.target st sdr tx
def e1S' : Environment := e1S k (e0S k benv st sdr tx) tx recover
def dS : Option Evm.Address :=
  if k ≥ 17 then Evm.Prague.State.parseDelegation ((e1S' k benv st sdr tx recover).state.getAccount (tgtS st sdr tx)).code
  else none
def e2S : Environment :=
  match dS k benv st sdr tx recover with
  | some a => Evm.Frontier.Vm.Call.warm (e1S' k benv st sdr tx recover) a
  | none => e1S' k benv st sdr tx recover

/-- The frame oracle and the precompile table the theorem gives the term: the spec's frame
    for this tx's message. -/
def oracleOf : HState → Nat → ChildRes :=
  if tx.to.isNone then createOracle (e0S k benv st sdr tx) sdr (tgtS st sdr tx) tx runSub
  else callOracle (e2S k benv st sdr tx recover) sdr (tgtS st sdr tx) tx (dS k benv st sdr tx recover) runSub
def preOf : Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile :=
  pre (e2S k benv st sdr tx recover)

/-- The term's context for this tx. -/
def ctxTx : Ctx :=
  ctxOf k benv st sdr tx (preOf k benv st sdr tx pre recover) (oracleOf k benv st sdr tx runSub recover) recover

end tx

theorem e0S_chainId (k : Nat) (benv : Environment) (st : State) (sdr : Evm.Address) (tx : Tx) :
    (e0S k benv st sdr tx).chainId = benv.chainId := rfl

set_option maxHeartbeats 4000000 in
/-- **The derived tx effect is every fork's message.** For a valid tx, the term's world,
    accounts_to_delete, touched set and refund counter are the message's, the gas it charged
    is the gas the message used, and its flag is the message's success. -/
theorem tx_refines (k : Nat) (benv : Environment) (st : State) (sdr : Evm.Address) (tx : Tx)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm) (recover : Evm.Prague.Authorization → Option Evm.Address)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hpmono : ∀ a p i g o g', pre (e2S k benv st sdr tx recover) a = some p → p i g = .ok (o, g') → g' ≤ g)
    (hv : invalid k benv st sdr tx = none) :
    let R := term.run (ctxTx k benv st sdr tx pre runSub recover) (h0 st)
    let o := message k benv st sdr tx pre runSub recover
    R.rej = 0 ∧ R.state = o.env.state ∧ R.destroyed = o.env.selfDestructSet ∧ R.touched = o.env.touched ∧
      R.refund = o.env.refundCounter ∧ R.gas + o.gasLeft = tx.gas - intrinsic k tx ∧
      R.out = (if o.success then Evm.U256.ofNat 1 else 0) := by
  intro R o
  have hval := (validate_run k benv st sdr tx (preOf k benv st sdr tx pre recover)
    (oracleOf k benv st sdr tx runSub recover) recover).1 hv
  -- the context after the comparisons
  let c' := cmpCtx (ctxTx k benv st sdr tx pre runSub recover) (h0 st)
  have hR : R = (delegS messageS).run c' (authsS.run c' (warmS.run c' (chargeS.run c' (h0 st)))) := by
    simp only [R, ctxTx]; rw [hval]; rfl
  have hPB : PBound c' k benv st sdr tx := by
    constructor <;> simp [c', cmpCtx, lb, ctxTx, ctxOf]
  rw [prologue_run c' k benv st sdr tx hPB] at hR
  rw [authsS_run c' k (env0 k benv st sdr tx) tx (by simp [c', cmpCtx, lb, ctxTx, ctxOf])
    (by simp [c', cmpCtx, lb, ctxTx, ctxOf]) (by simp [c', cmpCtx, lb, ctxTx, ctxOf])
    (by simp [c', cmpCtx, lb, ctxTx, ctxOf, env0])] at hR
  have hrec : c'.recover = recover := rfl
  rw [hrec] at hR
  have hvalid : (Evm.Frontier.Vm.Tx.rules k benv st sdr tx).findIdx? (·.1) = none :=
    (invalid_none_iff _ _ _ _ _).mp hv
  have hrej : ∀ (c3 : Ctx) (s : Stmt) (h : HState), h.rej = 0 → True := fun _ _ _ _ => trivial
  cases hto : tx.to with
  | none =>
    have hcr : tx.to.isNone = true := by simp [hto]
    obtain ⟨dc, hdel⟩ := delegS_run c' messageS (env0 k benv st sdr tx) (tgtS st sdr tx) false
      (by simp [c', cmpCtx, lb, ctxTx, ctxOf, hcr]) (by simp [c', cmpCtx, lb, ctxTx, ctxOf, tgtS])
    simp only [hcr, if_true, Bool.false_eq_true, if_false] at hR hdel
    rw [hdel, messageS_run] at hR
    let c4 := { cDel c' none dc with snaps := fun y => if y = "snap" then HState.ofEnv (env0 k benv st sdr tx)
                                                       else (cDel c' none dc).snaps y }
    have hcreate : (cDel c' none dc).bool "create" = true := by
      rw [cDel_bool _ _ _ _ (by decide) (by decide)]
      simp [c', cmpCtx, lb, ctxTx, ctxOf, hcr]
    have hR2 : R = createPath.run c4 (HState.ofEnv (env0 k benv st sdr tx)) := by
      rw [hR]; simp only [Stmt.run, BExp.eval, hcreate]; rfl
    have hB : MBound c4 k sdr (tgtS st sdr tx) tx (tx.gas - intrinsic k tx) false 0 := by
      constructor <;> simp [c4, cDel, c', cmpCtx, lb, ctxTx, ctxOf, tgtS, hcr]
    have hch : c4.child = createOracle (env0 k benv st sdr tx) sdr (tgtS st sdr tx) tx runSub := by
      simp [c4, cDel, c', cmpCtx, lb, ctxTx, ctxOf, oracleOf, hcr, e0S]
    have key := createPath_run c4 k (env0 k benv st sdr tx) sdr (tgtS st sdr tx) tx (tx.gas - intrinsic k tx)
      runSub hB (by simp [c4]) hch (fun sub hs => by
        have := hmono _ sub hs; simpa [Evm.Frontier.Vm.Create.child, Evm.fresh, createMsg] using this)
    have ho : o = Evm.Frontier.Vm.Tx.create k (env0 k benv st sdr tx) sdr (tgtS st sdr tx) tx
        (tx.gas - intrinsic k tx) runSub := by
      simp only [o, message, hto, tgtS]
    rw [hR2, ho]
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := key
    exact ⟨k7, k1, k2, k3, k4, k5, k6⟩
  | some to =>
    have hcr : tx.to.isNone = false := by simp [hto]
    have htg' : Evm.Frontier.Vm.Tx.target st sdr tx = to := by simp [Evm.Frontier.Vm.Tx.target, hto]
    have htg : tgtS st sdr tx = to := htg'
    obtain ⟨dc, hdel⟩ := delegS_run c' messageS (e1S k (env0 k benv st sdr tx) tx recover) to (decide (k ≥ 17))
      (by simp [c', cmpCtx, lb, ctxTx, ctxOf, hcr]) (by simp [c', cmpCtx, lb, ctxTx, ctxOf, htg'])
    simp only [hcr, Bool.false_eq_true, if_false] at hR
    rw [hdel, messageS_run] at hR
    have hdS : (if decide (k ≥ 17) = true then Evm.Prague.State.parseDelegation
        ((e1S k (env0 k benv st sdr tx) tx recover).state.getAccount to).code else none)
        = dS k benv st sdr tx recover := by
      simp [dS, e1S', e0S, htg]
    have he2 : (match dS k benv st sdr tx recover with
        | some a => Evm.Frontier.Vm.Call.warm (e1S k (env0 k benv st sdr tx) tx recover) a
        | none => e1S k (env0 k benv st sdr tx) tx recover) = e2S k benv st sdr tx recover := by
      simp only [e2S, e1S', e0S]
    rw [hdS, he2] at hR
    let c4 := { cDel c' (dS k benv st sdr tx recover) dc with
      snaps := fun y => if y = "snap" then HState.ofEnv (e2S k benv st sdr tx recover)
                        else (cDel c' (dS k benv st sdr tx recover) dc).snaps y }
    have hcreate : (cDel c' (dS k benv st sdr tx recover) dc).bool "create" = false := by
      rw [cDel_bool _ _ _ _ (by decide) (by decide)]
      simp [c', cmpCtx, lb, ctxTx, ctxOf, hcr]
    have hR2 : R = callPath.run c4 (HState.ofEnv (e2S k benv st sdr tx recover)) := by
      rw [hR]; simp only [Stmt.run, BExp.eval, hcreate]; rfl
    have hB : MBound c4 k sdr to tx (tx.gas - intrinsic k tx) (dS k benv st sdr tx recover).isSome
        ((dS k benv st sdr tx recover).getD 0) := by
      constructor <;> simp [c4, cDel, c', cmpCtx, lb, ctxTx, ctxOf, tgtS, hcr, htg']
    have hch : c4.child = callOracle (e2S k benv st sdr tx recover) sdr to tx (dS k benv st sdr tx recover) runSub := by
      simp [c4, cDel, c', cmpCtx, lb, ctxTx, ctxOf, oracleOf, hcr, htg]
    have hpr : c4.pre = pre (e2S k benv st sdr tx recover) := by
      simp [c4, cDel, c', cmpCtx, lb, ctxTx, ctxOf, preOf]
    have key := callPath_run c4 k (e2S k benv st sdr tx recover) sdr to tx (tx.gas - intrinsic k tx)
      (dS k benv st sdr tx recover) pre runSub hB (by simp [c4]) hpr hch
      (fun sub hs => by have := hmono _ sub hs; simpa [Evm.fresh, callMsg] using this)
      (fun p o' g' hp hpo => hpmono _ _ _ _ _ _ hp hpo)
    have ho : o = callTail k (e2S k benv st sdr tx recover) sdr to tx (tx.gas - intrinsic k tx)
        (dS k benv st sdr tx recover) pre runSub := by
      simp only [o, message, hto]
      unfold Evm.Frontier.Vm.Tx.call e2S dS e1S' e1S e0S tgtS
      rw [htg']
      rfl
    rw [hR2, ho]
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := key
    exact ⟨k7, k1, k2, k3, k4, k5, k6⟩

/-! ## The settlement and the end of tx after the message -/

open Evm.CL.EffectSettle (SAgree WF run_settle settle_refines specSettle refundState coinbaseState)
open Evm.CL.EffectEndTx (obs fold_obs stepP pDestroy pSweep hP_destroy hP_sweep destroy_eq sweep_eq
  specEndTx endTx_refines sagree_of_obs)

theorem WF_touch {s : State} (h : WF s) (a : Evm.Address) : WF (s.touchAccount a) := by
  unfold State.touchAccount; split
  · exact h
  · exact h.setAccount _ _

theorem settle_wf (k : Nat) (h : HState) (sender coinbase : Evm.Address) (gl gu egp bf : Nat)
    (hwf : WF h.state) : WF (EffectSettle.settle.run (EffectSettle.ctxOf k sender coinbase gl gu egp bf) h).state := by
  rw [run_settle]
  simp only [coinbaseState, refundState]
  repeat' split
  all_goals repeat (first | exact hwf | apply EffectSettle.WF.deleteAccount | apply WF_touch | apply EffectSettle.WF.addBalance)

theorem obs_of_sagree {s t : State} (h : SAgree s t) (x : Evm.Address) : obs s x = obs t x := by
  unfold obs
  rw [h.exists_ x, h.account x]
  congr 2
  funext k; exact h.storage x k

/-- A fold of `stepP P` keeps two states that agree in agreement, when `P` reads only what an
    observation sees. -/
theorem fold_congr (P : State → Evm.Address → Bool)
    (hP : ∀ s a x, x ≠ a → P (s.deleteAccount a) x = P s x)
    (hPo : ∀ s t x, obs s x = obs t x → P s x = P t x)
    (l : List Evm.Address) (s t : State) (h : SAgree s t) :
    SAgree (l.foldl (stepP P) s) (l.foldl (stepP P) t) := by
  apply sagree_of_obs
  intro x
  rw [fold_obs P hP l s x, fold_obs P hP l t x, obs_of_sagree h x, hPo s t x (obs_of_sagree h x)]

theorem pSweep_obs (s t : State) (x : Evm.Address) (h : obs s x = obs t x) : pSweep s x = pSweep t x := by
  unfold pSweep
  have h1 : s.accountExists x = t.accountExists x := congrArg Prod.fst h
  have h2 : s.getAccount x = t.getAccount x := congrArg (fun p => p.2.1) h
  rw [h1, h2]

/-- The fork's end of tx respects agreement. -/
theorem specEndTx_congr (k : Nat) (s t : State) (D T : List Evm.Address) (h : SAgree s t) :
    SAgree (specEndTx k s D T) (specEndTx k t D T) := by
  have hd := fold_congr pDestroy hP_destroy (fun _ _ _ _ => rfl) D s t h
  rw [← destroy_eq, ← destroy_eq] at hd
  unfold specEndTx
  split
  · unfold Evm.SpuriousDragon.finishTx
    have := fold_congr pSweep hP_sweep pSweep_obs T _ _ hd
    rwa [← sweep_eq, ← sweep_eq] at this
  · exact hd

/-- What a valid tx guarantees the settlement: the gas limit covers the intrinsic gas and the
    floor, and the effective price covers the base fee. -/
theorem valid_facts (k : Nat) (benv : Environment) (st : State) (sdr : Evm.Address) (tx : Tx)
    (hv : invalid k benv st sdr tx = none) :
    max (intrinsic k tx) (floor k tx) ≤ tx.gas ∧ benv.baseFeePerGas ≤ egp benv.baseFeePerGas tx := by
  have hall := List.findIdx?_eq_none_iff.mp ((invalid_none_iff _ _ _ _ _).mp hv)
  have r2 := hall _ (by simp [Evm.Frontier.Vm.Tx.rules] : (decide (max (intrinsic k tx) (floor k tx) > tx.gas),
    "intrinsic gas") ∈ Evm.Frontier.Vm.Tx.rules k benv st sdr tx)
  have r7 := hall _ (by simp [Evm.Frontier.Vm.Tx.rules] : (decide (tx.type ≥ 2 ∧ tx.maxFee < benv.baseFeePerGas),
    "max fee below base fee") ∈ Evm.Frontier.Vm.Tx.rules k benv st sdr tx)
  have r8 := hall _ (by simp [Evm.Frontier.Vm.Tx.rules] : (decide (tx.type < 2 ∧ tx.gasPrice < benv.baseFeePerGas),
    "gas price below base fee") ∈ Evm.Frontier.Vm.Tx.rules k benv st sdr tx)
  simp only [decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not] at r2 r7 r8
  refine ⟨by omega, ?_⟩
  unfold egp
  split
  · rename_i ht
    simp only [Evm.CL.GasEmit.effectiveGasPrice, Evm.CL.GasEmit.Expr.eval, if_true]
    simp
    have : ¬ tx.maxFee < benv.baseFeePerGas := fun h => r7 ⟨ht, h⟩
    omega
  · rename_i ht
    have : ¬ tx.gasPrice < benv.baseFeePerGas := fun h => r8 ⟨by omega, h⟩
    omega

theorem floor_eval (k : Nat) (tx : Tx) (u r : Nat) :
    Evm.CL.GasEmit.calldataFloorGas.eval (fun y =>
      if y = "gas-used" then u else if y = "refund-counter" then r else gasEnv k tx y) = floor k tx := by
  simp [floor, Evm.CL.GasEmit.calldataFloorGas, Evm.CL.GasEmit.Expr.eval, Evm.CL.GasEmit.fork, gasEnv]

theorem gasUsed_le (k : Nat) (tx : Tx) (o : Out) (hf : floor k tx ≤ tx.gas) :
    gasUsed k tx o ≤ tx.gas := by
  unfold gasUsed
  simp only [Evm.CL.GasEmit.txGasUsed, Evm.CL.GasEmit.Expr.eval]
  rw [floor_eval]
  apply Nat.max_le.mpr
  refine ⟨?_, hf⟩
  simp only [if_true]
  exact Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)

set_option maxHeartbeats 4000000 in
/-- **The wrapper's sequence is every fork's transaction.** `run-evm-tx` runs the term, then
    `spec-tx-gas-used` on the intrinsic gas plus the gas the term charged and the refund
    counter, then the settlement (`spec-gas-refund-effect`, `spec-coinbase-fee-effect`) and
    the end of tx (`spec-destroy-effect`, `spec-sweep-effect`). For a valid tx that sequence
    leaves the state `Tx.run` does (existence, accounts, storage), charges its gas, and
    reports its success. Assumptions beyond `tx_refines`'s: the message leaves the sender
    existing and only existing accounts carrying storage (`WF`), and the coinbase's fee does
    not wrap its balance to 0 (`settle_refines`'). -/
theorem apply_tx_refines (k : Nat) (benv : Environment) (st : State) (sdr : Evm.Address) (tx : Tx)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm) (recover : Evm.Prague.Authorization → Option Evm.Address)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hpmono : ∀ a p i g o g', pre (e2S k benv st sdr tx recover) a = some p → p i g = .ok (o, g') → g' ≤ g)
    (hv : invalid k benv st sdr tx = none)
    (hsender : (message k benv st sdr tx pre runSub recover).env.state.accountExists sdr = true)
    (hwf : WF (message k benv st sdr tx pre runSub recover).env.state)
    (hnowrap : let o := message k benv st sdr tx pre runSub recover
               let gu := gasUsed k tx o
               let p := egp benv.baseFeePerGas tx
               ((o.env.state.addBalance sdr (BitVec.ofNat 256 ((tx.gas - gu) * p))).getAccount benv.coinbase).balance
                 + BitVec.ofNat 256 (gu * (p - benv.baseFeePerGas)) = 0 →
               BitVec.ofNat 256 (gu * (p - benv.baseFeePerGas)) = 0) :
    let R := term.run (ctxTx k benv st sdr tx pre runSub recover) (h0 st)
    let gu := Evm.CL.GasEmit.txGasUsed.eval (fun y =>
      if y = "gas-used" then intrinsic k tx + R.gas else if y = "refund-counter" then R.refund else gasEnv k tx y)
    let p := egp benv.baseFeePerGas tx
    let S := EffectSettle.settle.run (EffectSettle.ctxOf k sdr benv.coinbase tx.gas gu p benv.baseFeePerGas) R
    let E := EffectEndTx.endTx.run (EffectEndTx.ctxOf k) S
    R.rej = 0 ∧ ∃ r, run k benv st sdr tx pre runSub recover = .ok r ∧
      SAgree r.state E.state ∧ r.gasUsed = gu ∧ (r.success = true ↔ R.out = Evm.U256.ofNat 1) := by
  intro R gu p S E
  obtain ⟨hrej, hst, hdes, htou, href, hgas, hout⟩ := tx_refines k benv st sdr tx pre runSub recover hmono hpmono hv
  obtain ⟨hmax, hbf⟩ := valid_facts k benv st sdr tx hv
  let o := message k benv st sdr tx pre runSub recover
  have hrun : run k benv st sdr tx pre runSub recover = .ok (finish k benv sdr tx o) := by
    simp only [run, hv, o]
  -- the gas: the term's charge plus the intrinsic gas is what the message used
  have hi : intrinsic k tx ≤ tx.gas := Nat.le_trans (Nat.le_max_left _ _) hmax
  have hused : intrinsic k tx + R.gas = tx.gas - o.gasLeft := by
    have : R.gas + o.gasLeft = tx.gas - intrinsic k tx := hgas
    omega
  have href' : R.refund = o.env.refundCounter := href
  have hgu : gu = gasUsed k tx o := by
    simp only [gu, gasUsed, hused, href']
  refine ⟨hrej, finish k benv sdr tx o, hrun, ?_, by simp [finish, hgu], ?_⟩
  · -- the settlement, then the end of tx
    have hgl : gu ≤ tx.gas := by rw [hgu]; exact gasUsed_le k tx o (Nat.le_trans (Nat.le_max_right _ _) hmax)
    have hRs : R.state = o.env.state := hst
    obtain ⟨hA, hSd, hSt, -⟩ := settle_refines k R sdr benv.coinbase tx.gas gu p benv.baseFeePerGas hgl hbf
      (by rw [hRs]; exact hsender) (by rw [hRs]; exact hwf) (by rw [hRs, hgu]; exact hnowrap)
    have hwfS : WF S.state := settle_wf k R sdr benv.coinbase tx.gas gu p benv.baseFeePerGas (by rw [hRs]; exact hwf)
    obtain ⟨hB, -⟩ := endTx_refines k S hwfS
    have hC := specEndTx_congr k _ _ S.destroyed S.touched hA
    have hfin : (finish k benv sdr tx o).state
        = specEndTx k (specSettle k R.state sdr benv.coinbase ((tx.gas - gu) * p) (gu * (p - benv.baseFeePerGas)))
            S.destroyed S.touched := by
      rw [hSd, hSt, hRs, hdes, htou, hgu]
      rfl
    rw [hfin]
    exact EffectSettle.SAgree.trans hC hB
  · have hout' : R.out = (if o.success then Evm.U256.ofNat 1 else 0) := hout
    show o.success = true ↔ R.out = Evm.U256.ofNat 1
    rw [hout']
    cases o.success
    · simp only [Bool.false_eq_true, if_false, false_iff]; decide
    · simp

end Evm.CL.EffectTx
