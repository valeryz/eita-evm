/-
  Evm.Amsterdam.Vm.StatePricing — what each EIP-8037/8038 charge site prices, as pure
  functions of the facts the site decides on (warmth, the slot's original/current/new
  values, existence, the deployed length).

  EELS: ethereum/execution-specs 636b5f1, `src/ethereum/forks/amsterdam/` (cited per
  definition). The constants are `Evm.Amsterdam.Vm.Gas.Params` / `AccessParams` (one
  place). Each site splits into its EXECUTION charge (`charge_gas`), its STATE charge
  (`charge_state_gas`, drawn from the reservoir first) and, where EELS has one, the state
  gas it credits back (`credit_state_gas_refund`) and the refund-counter moves.

  Only the sites whose price changes under EIP-8037/8038 are here; every other opcode
  costs what it costs at Osaka. The other Amsterdam repricings (EIP-2780 intrinsic
  restructuring, EIP-7976/7981 floors, EIP-7778 block accounting, EIP-7928 BAL item
  costs) are NOT part of this schedule.
-/

import Evm.BaseTypes
import Evm.Amsterdam.Vm.Gas

namespace Evm.Amsterdam.Vm.StatePricing

open Evm.Amsterdam.Vm.Gas

/-! ## SSTORE (EELS `vm/instructions/storage.py:68-158`) -/

/-- One SSTORE's pricing. -/
structure SstorePrice where
  /-- `charge_gas(evm, gas_cost)`: access plus `STORAGE_WRITE`, storage.py:93-98, 121-123. -/
  execution   : Nat
  /-- `charge_state_gas(evm, state_gas)`: `STORAGE_SET` for a first set of a zero slot,
      storage.py:144-146. -/
  state       : Nat
  /-- `credit_state_gas_refund(…, STORAGE_SET)`: a slot set then cleared, storage.py:148-151. -/
  stateCredit : Nat
  /-- Refund counter additions, storage.py:126-139. -/
  refundAdd   : Nat
  /-- Refund counter subtractions, storage.py:133-134. -/
  refundSub   : Nat
  deriving Repr, DecidableEq

/-- EELS `sstore`, storage.py:68-158, for a slot whose tx-start value is `original`, current
    value `current`, written with `new_`; `isCold` = `(current_target, key)` not yet accessed. -/
def sstore (isCold : Bool) (original current new_ : Evm.U256)
    (p : Params := params) (q : AccessParams := accessParams) : SstorePrice :=
  let access := if isCold then q.coldStorageAccess else q.warmAccess   -- storage.py:93-98
  let moves := decide (current = original) && !decide (new_ = current)  -- storage.py:121
  let write := if moves then q.storageWrite else 0                       -- storage.py:122-123
  let changes := !decide (new_ = current)                                -- storage.py:126
  let clear := if changes && !decide (original = 0) && !decide (current = 0) && decide (new_ = 0)
               then refundStorageClear q else 0                          -- storage.py:127-130
  let unclear := if changes && !decide (original = 0) && decide (current = 0)
                 then refundStorageClear q else 0                        -- storage.py:132-134
  let restore := if changes && decide (new_ = original) then q.storageWrite else 0  -- storage.py:136-139
  { execution := access + write
    state := if moves && decide (original = 0) then storageSet p else 0  -- storage.py:144-146
    stateCredit := if changes && decide (new_ = original) && decide (original = 0)
                   then storageSet p else 0                              -- storage.py:148-151
    refundAdd := clear + restore
    refundSub := unclear }

/-! ## Account access (EELS `vm/instructions/environment.py`) -/

/-- BALANCE (environment.py:58-86), EXTCODEHASH (476-510): warm or cold access.
    EXTCODESIZE (330-361) and EXTCODECOPY (364-408) add one `WARM_ACCESS` for the code
    read (environment.py:349, 392: "Code reading cost (EIP-8038)"). The copy's per-word
    and memory costs are Osaka's. -/
def accountAccess (isCold codeRead : Bool) (q : AccessParams := accessParams) : Nat :=
  (if isCold then q.coldAccountAccess else q.warmAccess) + (if codeRead then q.warmAccess else 0)

/-! ## The CALL family (EELS `vm/instructions/system.py`) -/

/-- CALL (system.py:466-589) / CALLCODE (592-702): access, `CALL_VALUE` for a value
    transfer (system.py:504) and the EIP-7702 delegation's access
    (`calculate_delegation_cost`, eoa_delegation.py:160-195: warm or cold) — the
    EXECUTION part. DELEGATECALL/STATICCALL: `valueTransfer = false`. -/
def callExecution (isCold valueTransfer : Bool) (delegCold : Option Bool)
    (q : AccessParams := accessParams) : Nat :=
  (if isCold then q.coldAccountAccess else q.warmAccess)
  + (if valueTransfer then callValue q else 0)
  + (match delegCold with
     | none => 0
     | some c => if c then q.coldAccountAccess else q.warmAccess)

/-- CALL's STATE part, system.py:541-546: `NEW_ACCOUNT` when the value transfer will create
    the recipient; refilled by `generic_call` when the creation fails or never happens
    (system.py:389-392, 449-451). CALLCODE never charges it (its value stays in the caller). -/
def callState (newAccount' : Bool) (p : Params := params) : Nat :=
  if newAccount' then newAccount p else 0

/-! ## CREATE / CREATE2 (EELS `vm/instructions/system.py:59-305`, `vm/interpreter.py`) -/

/-- The creating frame's execution charge, system.py:213-216 (CREATE) / 268-272 (CREATE2):
    `CREATE_ACCESS` replaces Osaka's 32000 (the init-code words, CREATE2's hash and the
    memory expansion are Osaka's). -/
def createExecution (q : AccessParams := accessParams) : Nat := createAccess q

/-- The creating frame's state charge, system.py:104-109: `NEW_ACCOUNT` iff the destination
    is not alive, refilled when the child fails (system.py:178-180). -/
def createState (destAlive : Bool) (p : Params := params) : Nat :=
  if destAlive then 0 else newAccount p

/-- The code deposit, `process_create` (interpreter.py:366-379): an execution hash cost of
    `OPCODE_KECCAK256_PER_WORD` per word and `COST_PER_STATE_BYTE` per deployed byte of
    state gas (Osaka: 200 per byte). Returns `(execution, state)`. -/
def codeDeposit (len : Nat) (p : Params := params) (q : AccessParams := accessParams) : Nat × Nat :=
  (q.keccakPerWord * ((len + 31) / 32), len * p.costPerStateByte)

/-! ## SELFDESTRUCT (EELS `vm/instructions/system.py:705-777`) -/

/-- Execution part: `OPCODE_SELFDESTRUCT_BASE` (5000, unchanged), the cold access
    (system.py:723-725) and `ACCOUNT_WRITE` for a sweep that creates the beneficiary
    (system.py:740-746). -/
def selfdestructExecution (isCold createsBeneficiary : Bool) (q : AccessParams := accessParams) : Nat :=
  5000 + (if isCold then q.coldAccountAccess else 0) + (if createsBeneficiary then q.accountWrite else 0)

/-- State part, system.py:740-756: `NEW_ACCOUNT` for that sweep. -/
def selfdestructState (createsBeneficiary : Bool) (p : Params := params) : Nat :=
  if createsBeneficiary then newAccount p else 0

/-! ## The top frame (EELS `vm/interpreter.py:119-233`) and the intrinsic cost -/

/-- `charge_value_transfer_to_non_alive_account` (interpreter.py:119-130, called at 180-182):
    a value-bearing tx to a non-alive recipient pays `NEW_ACCOUNT`; a creation tx whose
    address' pre-state is empty pays it too (interpreter.py:172-178). -/
def topLevelState (createsAccount : Bool) (p : Params := params) : Nat :=
  if createsAccount then newAccount p else 0

/-- `resolve_delegated_code_address` (eoa_delegation.py:84-109): a delegated tx target's
    code address is charged warm or cold (Osaka charged nothing). -/
def topLevelDelegation (delegCold : Option Bool) (q : AccessParams := accessParams) : Nat :=
  match delegCold with
  | none => 0
  | some c => if c then q.coldAccountAccess else q.warmAccess

/-- The EIP-8038 part of the intrinsic cost, transactions.py:747-753: the access list's
    per-address and per-key charges. -/
def accessListIntrinsic (addrs keys : Nat) (q : AccessParams := accessParams) : Nat :=
  addrs * txAccessListAddress q + keys * txAccessListStorageKey q

/-! ## Facts -/

/-- Setting a zero slot and clearing it again in one tx nets the state gas to zero and
    refunds the write: what EIP-8037 means by "refunded if the slot is cleared". -/
theorem sstore_set_then_clear (x : Evm.U256) (hx : x ≠ 0) :
    (sstore false 0 0 x).state = storageSet ∧
    (sstore false 0 x 0).stateCredit = storageSet ∧
    (sstore false 0 x 0).refundAdd = accessParams.storageWrite := by
  have h1 : ¬ x = 0#256 := hx
  have h2 : ¬ 0#256 = x := fun h => hx h.symm
  simp [sstore, h1, h2]

/-- A no-op SSTORE costs the access only, in both dimensions. -/
theorem sstore_noop (c : Bool) (o x : Evm.U256) :
    (sstore c o x x).execution = (if c then accessParams.coldStorageAccess else accessParams.warmAccess) ∧
    (sstore c o x x).state = 0 ∧ (sstore c o x x).refundAdd = 0 ∧ (sstore c o x x).refundSub = 0 := by
  simp [sstore]

/-- State gas is only ever charged for a zero slot (state creation, not modification). -/
theorem sstore_state_only_zero (c : Bool) (o x y : Evm.U256) (h : o ≠ 0) :
    (sstore c o x y).state = 0 := by
  have h1 : ¬ o = 0#256 := h
  simp [sstore, h1]

/-- Under the default parameters a CREATE of an `n`-byte contract at a fresh address costs
    `12000 + 6·⌈n/32⌉` execution gas and `(120 + n)·1530` state gas — EIP-8037's
    `(120 + L) × CPSB`. -/
theorem create_fresh (n : Nat) :
    createExecution + (codeDeposit n).1 = 12000 + 6 * ((n + 31) / 32) ∧
    createState false + (codeDeposit n).2 = (120 + n) * 1530 := by
  simp only [createExecution, createAccess, codeDeposit, createState, newAccount, params, accessParams]
  constructor <;> simp <;> omega

end Evm.Amsterdam.Vm.StatePricing
