import Evm.CL.GasEmit
import Evm.London.Vm.Effect
import Evm.Amsterdam.Vm.StatePricing

/-! # Evm.CL.RepriceEmit — the per-charge prices of the re-costing tool, both schedules

The re-costing tool (`scripts/reprice.lisp`) executes history exactly as it happened and,
at each charge site whose price EIP-8037/8038 changes, prices the same operation twice:
under the schedule that ran (Osaka) and under Amsterdam's EIP-8037/8038 schedule. Both
prices are `GasEmit.Expr` terms emitted to `scripts/generated/reprice-amsterdam.lisp` by
`lake exe emitRepriceCL`, and each term is PROVED equal, for all inputs, to its spec here:

* Osaka: the production formulas where they exist (`GasEmit.codeDepositGas`,
  `newAccountFee`, `selfdestructColdGas` — the very terms `host.lisp` runs) and otherwise
  the fork spec's definitions (`London.Vm.Effect.eip2200London`, `Berlin.Vm.Effect.callGasPlan`,
  the Berlin/Frontier constants);
* Amsterdam: `Evm.Amsterdam.Vm.StatePricing` / `Evm.Amsterdam.Vm.Gas` (EELS 636b5f1).

Inputs are the facts each site decides on, as 0/1 flags or naturals; the CL seam computes
them from the values it observes (`=` on words). Nothing here is loaded by the replay. -/

namespace Evm.CL.RepriceEmit

open Evm.CL.GasEmit (Expr Env)
open Evm.Amsterdam.Vm.Gas (params accessParams storageSet newAccount callValue createAccess
  refundStorageClear txAccessListAddress txAccessListStorageKey)
open Evm.Amsterdam.Vm.StatePricing

/-- `if 0 < x then t else e` — a 0/1 flag. -/
def flag (x : String) (t e : Expr) : Expr := .ite (.lit 0) (.var x) t e

def b2n (b : Bool) : Nat := if b then 1 else 0

theorem flag_eval (ρ : Env) (x : String) (t e : Expr) (b : Bool) (h : ρ x = b2n b) :
    (flag x t e).eval ρ = if b then t.eval ρ else e.eval ρ := by
  cases b <;> simp [flag, Expr.eval, h, b2n]

/-! ## SSTORE -/

/-- The flags an SSTORE is priced on (orientation as in `eip2200London` / `sstore`). -/
def sstoreEnv (c : Bool) (o cu n : Evm.U256) : Env := fun x =>
  if x = "cold" then b2n c
  else if x = "new-eq-cur" then b2n (decide (n = cu))
  else if x = "cur-eq-orig" then b2n (decide (cu = o))
  else if x = "new-eq-orig" then b2n (decide (n = o))
  else if x = "orig-zero" then b2n (decide (o = 0))
  else if x = "cur-zero" then b2n (decide (cu = 0))
  else if x = "new-zero" then b2n (decide (n = 0))
  else 0

def sstoreVars : List String := ["cold", "new-eq-cur", "cur-eq-orig", "new-eq-orig", "orig-zero", "cur-zero", "new-zero"]

/-- Osaka (London's EIP-2200/3529 schedule plus the EIP-2929 cold surcharge): the charge. -/
def osakaSstoreCost : Expr :=
  .add (flag "cold" (.lit 2100) (.lit 0))
       (flag "new-eq-cur" (.lit 100) (flag "cur-eq-orig" (flag "orig-zero" (.lit 20000) (.lit 2900)) (.lit 100)))
/-- Osaka: refund-counter additions. -/
def osakaSstoreRefundAdd : Expr :=
  flag "new-eq-cur" (.lit 0)
    (flag "cur-eq-orig" (flag "orig-zero" (.lit 0) (flag "new-zero" (.lit 4800) (.lit 0)))
      (.add (flag "orig-zero" (.lit 0) (flag "cur-zero" (.lit 0) (flag "new-zero" (.lit 4800) (.lit 0))))
            (flag "new-eq-orig" (flag "orig-zero" (.lit 19900) (.lit 2800)) (.lit 0))))
/-- Osaka: refund-counter subtractions. -/
def osakaSstoreRefundSub : Expr :=
  flag "new-eq-cur" (.lit 0) (flag "cur-eq-orig" (.lit 0) (flag "orig-zero" (.lit 0) (flag "cur-zero" (.lit 4800) (.lit 0))))

/-- Amsterdam, from `StatePricing.sstore` at the default parameters. -/
def amsSstoreExecution : Expr :=
  .add (flag "cold" (.lit accessParams.coldStorageAccess) (.lit accessParams.warmAccess))
       (flag "cur-eq-orig" (flag "new-eq-cur" (.lit 0) (.lit accessParams.storageWrite)) (.lit 0))
def amsSstoreState : Expr :=
  flag "cur-eq-orig" (flag "new-eq-cur" (.lit 0) (flag "orig-zero" (.lit storageSet) (.lit 0))) (.lit 0)
def amsSstoreStateCredit : Expr :=
  flag "new-eq-cur" (.lit 0) (flag "new-eq-orig" (flag "orig-zero" (.lit storageSet) (.lit 0)) (.lit 0))
def amsSstoreRefundAdd : Expr :=
  flag "new-eq-cur" (.lit 0)
    (.add (flag "orig-zero" (.lit 0) (flag "cur-zero" (.lit 0) (flag "new-zero" (.lit refundStorageClear) (.lit 0))))
          (flag "new-eq-orig" (.lit accessParams.storageWrite) (.lit 0)))
def amsSstoreRefundSub : Expr :=
  flag "new-eq-cur" (.lit 0) (flag "orig-zero" (.lit 0) (flag "cur-zero" (.lit refundStorageClear) (.lit 0)))

section
open Evm.London.Vm.Effect (eip2200London)

/-- The Osaka terms are London's schedule (EELS london/vm/instructions/storage.py, as
    `eip2200London`) with Berlin's cold surcharge, for ALL slot values. -/
theorem osakaSstore_eq_spec (c : Bool) (o cu n : Evm.U256) :
    osakaSstoreCost.eval (sstoreEnv c o cu n) =
      (if c then Evm.Berlin.Vm.Gas.sstoreColdSurcharge else 0) + (eip2200London o cu n).1 ∧
    osakaSstoreRefundAdd.eval (sstoreEnv c o cu n) = (eip2200London o cu n).2.1 ∧
    osakaSstoreRefundSub.eval (sstoreEnv c o cu n) = (eip2200London o cu n).2.2 := by
  cases c <;>
    simp [osakaSstoreCost, osakaSstoreRefundAdd, osakaSstoreRefundSub, flag, sstoreEnv, b2n,
      Expr.eval, eip2200London, Evm.Berlin.Vm.Gas.sstoreColdSurcharge,
      Evm.Berlin.Vm.Gas.coldSload, Evm.Berlin.Vm.Instructions.Storage.sstoreSet,
      Evm.Berlin.Vm.Instructions.Storage.sstoreReset, Evm.Berlin.Vm.Gas.warmAccess,
      Evm.London.Vm.Gas.sStoreClearRefund] <;>
    by_cases h1 : n = cu <;> by_cases h2 : cu = o <;> by_cases h3 : n = o <;>
    by_cases h4 : o = 0#256 <;> by_cases h5 : cu = 0#256 <;> by_cases h6 : n = 0#256 <;> simp_all

end

/-- The Amsterdam terms are EELS amsterdam `sstore` (`StatePricing.sstore`), all values. -/
theorem amsSstore_eq_spec (c : Bool) (o cu n : Evm.U256) :
    amsSstoreExecution.eval (sstoreEnv c o cu n) = (sstore c o cu n).execution ∧
    amsSstoreState.eval (sstoreEnv c o cu n) = (sstore c o cu n).state ∧
    amsSstoreStateCredit.eval (sstoreEnv c o cu n) = (sstore c o cu n).stateCredit ∧
    amsSstoreRefundAdd.eval (sstoreEnv c o cu n) = (sstore c o cu n).refundAdd ∧
    amsSstoreRefundSub.eval (sstoreEnv c o cu n) = (sstore c o cu n).refundSub := by
  cases c <;>
    simp [amsSstoreExecution, amsSstoreState, amsSstoreStateCredit, amsSstoreRefundAdd,
      amsSstoreRefundSub, flag, sstoreEnv, b2n, Expr.eval, sstore] <;>
    by_cases h1 : n = cu <;> by_cases h2 : cu = o <;> by_cases h3 : n = o <;>
    by_cases h4 : o = 0#256 <;> by_cases h5 : cu = 0#256 <;> by_cases h6 : n = 0#256 <;> simp_all

/-! ## Account access, CALL, CREATE, SELFDESTRUCT, the top frame -/

/-- Osaka BALANCE/EXTCODE* (EIP-2929): cold 2600, warm 100. -/
def osakaAccountAccess : Expr :=
  flag "cold" (.lit Evm.Berlin.Vm.Gas.coldAccountAccess) (.lit Evm.Berlin.Vm.Gas.warmAccess)
/-- Amsterdam: `StatePricing.accountAccess` (input `code-read`: EXTCODESIZE/EXTCODECOPY). -/
def amsAccountAccess : Expr :=
  .add (flag "cold" (.lit accessParams.coldAccountAccess) (.lit accessParams.warmAccess))
       (flag "code-read" (.lit accessParams.warmAccess) (.lit 0))

theorem amsAccountAccess_eq_spec (ρ : Env) (c r : Bool) (hc : ρ "cold" = b2n c) (hr : ρ "code-read" = b2n r) :
    amsAccountAccess.eval ρ = accountAccess c r := by
  cases c <;> cases r <;> simp [amsAccountAccess, flag, Expr.eval, hc, hr, b2n, accountAccess]

/-- Osaka CALL-family charge before the forward: `Berlin.Vm.Effect.callGasPlan`'s `charge`
    (inputs `cold`, `value`, `new-account` flags and `deleg`, the delegate access the
    plan is given: 0, 100 or 2600). -/
def osakaCallCharge : Expr :=
  .add (.add (.add (flag "cold" (.lit 2600) (.lit 100)) (flag "value" (.lit 9000) (.lit 0)))
             (flag "new-account" (.lit 25000) (.lit 0))) (.var "deleg")

theorem osakaCallCharge_eq_spec (ρ : Env) (c v na : Bool) (hc : ρ "cold" = b2n c)
    (hv : ρ "value" = b2n v) (hn : ρ "new-account" = b2n na) (g a : Nat) :
    osakaCallCharge.eval ρ = (Evm.Berlin.Vm.Effect.callGasPlan c v na (ρ "deleg") g a).charge := by
  cases c <;> cases v <;> cases na <;>
    simp [osakaCallCharge, flag, Expr.eval, hc, hv, hn, b2n, Evm.Berlin.Vm.Effect.callGasPlan,
      Evm.Berlin.Vm.Effect.callBaseCost, Evm.Berlin.Vm.Gas.coldAccountAccess, Evm.Berlin.Vm.Gas.warmAccess,
      Evm.Frontier.Vm.Gas.callValue, Evm.Frontier.Vm.Gas.newAccount] <;> omega

/-- Amsterdam CALL execution part (`has-deleg`, `deleg-cold` flags). -/
def amsCallExecution : Expr :=
  .add (.add (flag "cold" (.lit accessParams.coldAccountAccess) (.lit accessParams.warmAccess))
             (flag "value" (.lit callValue) (.lit 0)))
       (flag "has-deleg" (flag "deleg-cold" (.lit accessParams.coldAccountAccess) (.lit accessParams.warmAccess)) (.lit 0))
/-- Amsterdam CALL state part (`new-account`). -/
def amsCallState : Expr := flag "new-account" (.lit newAccount) (.lit 0)

theorem amsCall_eq_spec (ρ : Env) (c v na hd dc : Bool) (hc : ρ "cold" = b2n c)
    (hv : ρ "value" = b2n v) (hn : ρ "new-account" = b2n na) (hh : ρ "has-deleg" = b2n hd)
    (hdc : ρ "deleg-cold" = b2n dc) :
    amsCallExecution.eval ρ = callExecution c v (if hd then some dc else none) ∧
    amsCallState.eval ρ = callState na := by
  cases c <;> cases v <;> cases na <;> cases hd <;> cases dc <;>
    simp [amsCallExecution, amsCallState, flag, Expr.eval, hc, hv, hn, hh, hdc, b2n,
      callExecution, callState]

/-- CREATE's flat charge: Osaka `GAS_CREATE` 32000 (`Frontier.Vm.Gas.create`), Amsterdam
    `CREATE_ACCESS`. The init-code words, CREATE2's hash and memory are the same in both. -/
def osakaCreateFlat : Expr := .lit Evm.Frontier.Vm.Gas.create
def amsCreateExecution : Expr := .lit createAccess
def amsCreateState : Expr := flag "dest-alive" (.lit 0) (.lit newAccount)

theorem amsCreate_eq_spec (ρ : Env) (al : Bool) (h : ρ "dest-alive" = b2n al) :
    amsCreateExecution.eval ρ = createExecution ∧ amsCreateState.eval ρ = createState al := by
  cases al <;> simp [amsCreateExecution, amsCreateState, flag, Expr.eval, h, b2n, createExecution, createState]

/-- Code deposit: Osaka is the production term `GasEmit.codeDepositGas` (200/byte). -/
def osakaCodeDeposit : Expr := Evm.CL.GasEmit.codeDepositGas
def amsCodeDepositExecution : Expr :=
  .mul (.lit accessParams.keccakPerWord) (.fdiv (.add (.var "nbytes") (.lit 31)) (.lit 32))
def amsCodeDepositState : Expr := .mul (.var "nbytes") (.lit params.costPerStateByte)

theorem amsCodeDeposit_eq_spec (ρ : Env) :
    amsCodeDepositExecution.eval ρ = (codeDeposit (ρ "nbytes")).1 ∧
    amsCodeDepositState.eval ρ = (codeDeposit (ρ "nbytes")).2 := by
  simp [amsCodeDepositExecution, amsCodeDepositState, Expr.eval, codeDeposit]

/-- SELFDESTRUCT: Osaka is `5000` (TangerineWhistle) plus the production terms
    `selfdestructColdGas` and `newAccountFee` (as `spec-selfdestruct-effect` charges them). -/
def osakaSelfdestruct : Expr :=
  .add (.add (.lit Evm.TangerineWhistle.Vm.Gas.selfDestruct) Evm.CL.GasEmit.selfdestructColdGas)
       (flag "new-account" Evm.CL.GasEmit.newAccountFee (.lit 0))
def amsSelfdestructExecution : Expr :=
  .add (.add (.lit 5000) (flag "cold" (.lit accessParams.coldAccountAccess) (.lit 0)))
       (flag "new-account" (.lit accessParams.accountWrite) (.lit 0))
def amsSelfdestructState : Expr := flag "new-account" (.lit newAccount) (.lit 0)

theorem amsSelfdestruct_eq_spec (ρ : Env) (c na : Bool) (hc : ρ "cold" = b2n c) (hn : ρ "new-account" = b2n na) :
    amsSelfdestructExecution.eval ρ = selfdestructExecution c na ∧
    amsSelfdestructState.eval ρ = selfdestructState na := by
  cases c <;> cases na <;>
    simp [amsSelfdestructExecution, amsSelfdestructState, flag, Expr.eval, hc, hn, b2n,
      selfdestructExecution, selfdestructState]

/-- The top frame: Amsterdam's `NEW_ACCOUNT` for a value tx to a non-alive recipient or a
    creation at an empty address (`creates`), and the delegated target's access. -/
def amsTopLevelState : Expr := flag "creates" (.lit newAccount) (.lit 0)
def amsTopLevelDelegation : Expr :=
  flag "has-deleg" (flag "deleg-cold" (.lit accessParams.coldAccountAccess) (.lit accessParams.warmAccess)) (.lit 0)

theorem amsTopLevel_eq_spec (ρ : Env) (cr hd dc : Bool) (h1 : ρ "creates" = b2n cr)
    (h2 : ρ "has-deleg" = b2n hd) (h3 : ρ "deleg-cold" = b2n dc) :
    amsTopLevelState.eval ρ = topLevelState cr ∧
    amsTopLevelDelegation.eval ρ = topLevelDelegation (if hd then some dc else none) := by
  cases cr <;> cases hd <;> cases dc <;>
    simp [amsTopLevelState, amsTopLevelDelegation, flag, Expr.eval, h1, h2, h3, b2n,
      topLevelState, topLevelDelegation]

/-- The access list's intrinsic charge: Osaka (EIP-2930) and Amsterdam (EIP-8038). -/
def osakaAccessList : Expr :=
  .add (.mul (.var "al-addrs") (.lit Evm.Berlin.Vm.Gas.accessListAddress))
       (.mul (.var "al-keys") (.lit Evm.Berlin.Vm.Gas.accessListStorageKey))
def amsAccessList : Expr :=
  .add (.mul (.var "al-addrs") (.lit txAccessListAddress)) (.mul (.var "al-keys") (.lit txAccessListStorageKey))

theorem amsAccessList_eq_spec (ρ : Env) :
    amsAccessList.eval ρ = accessListIntrinsic (ρ "al-addrs") (ρ "al-keys") := by
  simp [amsAccessList, Expr.eval, accessListIntrinsic]

/-- The settled gas: `settle_transaction_gas`'s `gas_used` for a pre-refund usage
    `before` (execution plus state gas, EIP-8037), the refund counter and the floor. -/
def amsTxGasUsed : Expr :=
  .emax (.sub (.var "before") (.emin (.fdiv (.var "before") (.lit 5)) (.var "refund"))) (.var "floor")

theorem amsTxGasUsed_eq_spec (ρ : Env) (txGas : Nat) (h : ρ "before" ≤ txGas) (su : Int) :
    amsTxGasUsed.eval ρ =
      (Evm.Amsterdam.Vm.Gas.settleTransactionGas txGas (ρ "floor") (txGas - ρ "before") 0
        (ρ "refund") su).gasUsed := by
  simp only [amsTxGasUsed, Expr.eval, Evm.Amsterdam.Vm.Gas.settleTransactionGas]
  have : txGas - (txGas - ρ "before") - 0 = ρ "before" := by omega
  rw [this]

/-! ## The emitted table -/

/-- `(CL name, inputs, term)` for every price the tool reads. -/
def table : List (String × List String × Expr) :=
  [ ("rp-osaka-sstore-cost",        sstoreVars, osakaSstoreCost),
    ("rp-osaka-sstore-refund-add",  sstoreVars, osakaSstoreRefundAdd),
    ("rp-osaka-sstore-refund-sub",  sstoreVars, osakaSstoreRefundSub),
    ("rp-ams-sstore-execution",     sstoreVars, amsSstoreExecution),
    ("rp-ams-sstore-state",         sstoreVars, amsSstoreState),
    ("rp-ams-sstore-state-credit",  sstoreVars, amsSstoreStateCredit),
    ("rp-ams-sstore-refund-add",    sstoreVars, amsSstoreRefundAdd),
    ("rp-ams-sstore-refund-sub",    sstoreVars, amsSstoreRefundSub),
    ("rp-osaka-account-access",     ["cold"], osakaAccountAccess),
    ("rp-ams-account-access",       ["cold", "code-read"], amsAccountAccess),
    ("rp-osaka-call-charge",        ["cold", "value", "new-account", "deleg"], osakaCallCharge),
    ("rp-ams-call-execution",       ["cold", "value", "has-deleg", "deleg-cold"], amsCallExecution),
    ("rp-ams-call-state",           ["new-account"], amsCallState),
    ("rp-osaka-create-flat",        [], osakaCreateFlat),
    ("rp-ams-create-execution",     [], amsCreateExecution),
    ("rp-ams-create-state",         ["dest-alive"], amsCreateState),
    ("rp-osaka-code-deposit",       ["nbytes"], osakaCodeDeposit),
    ("rp-ams-code-deposit-execution", ["nbytes"], amsCodeDepositExecution),
    ("rp-ams-code-deposit-state",   ["nbytes"], amsCodeDepositState),
    ("rp-osaka-selfdestruct",       ["cold", "new-account"], osakaSelfdestruct),
    ("rp-ams-selfdestruct-execution", ["cold", "new-account"], amsSelfdestructExecution),
    ("rp-ams-selfdestruct-state",   ["new-account"], amsSelfdestructState),
    ("rp-ams-top-level-state",      ["creates"], amsTopLevelState),
    ("rp-ams-top-level-delegation", ["has-deleg", "deleg-cold"], amsTopLevelDelegation),
    ("rp-osaka-access-list",        ["al-addrs", "al-keys"], osakaAccessList),
    ("rp-ams-access-list",          ["al-addrs", "al-keys"], amsAccessList),
    ("rp-ams-tx-gas-used",          ["before", "refund", "floor"], amsTxGasUsed) ]

/-- The parameters the report prints (provenance of the schedule). -/
def paramLines : List (String × Nat) :=
  [ ("cost-per-state-byte", params.costPerStateByte), ("new-account", newAccount),
    ("storage-set", storageSet), ("tx-max-gas-limit", params.txMaxGasLimit),
    ("cold-account-access", accessParams.coldAccountAccess), ("storage-write", accessParams.storageWrite),
    ("account-write", accessParams.accountWrite), ("refund-storage-clear", refundStorageClear) ]

def emit : String :=
  let fns := table.map fun (nm, vs, e) =>
    s!"(defun {nm} ({" ".intercalate vs})\n  (declare (ignorable {" ".intercalate vs}))\n  {e.toCL})"
  let ps := paramLines.map fun (k, v) => s!"(:{k} . {v})"
  ";;;; AUTO-GENERATED by lean/EmitRepriceCL.lean — do not hand-edit.\n" ++
  ";;;; The re-costing tool's per-charge prices (Evm.CL.RepriceEmit, each proved equal to its\n" ++
  ";;;; spec: Osaka's schedule and EIP-8037/8038 as in EELS 636b5f1). NOT loaded by the replay.\n" ++
  "(in-package :eita.evm)\n\n" ++
  s!"(defparameter *rp-schedule* '({" ".intercalate ps}))\n\n" ++
  "\n\n".intercalate fns ++ "\n"

end Evm.CL.RepriceEmit
