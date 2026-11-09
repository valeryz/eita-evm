/-
  Evm.Amsterdam.Vm.Gas — EIP-8037 (state creation gas, two gas pools) and the EIP-8038
  (state access) constants: the delta of EELS `forks/amsterdam/vm/gas.py` over Osaka.

  EELS: ethereum/execution-specs 636b5f1 (branch `forks/bogota`, which carries the
  Amsterdam fork with EIP-8037/8038 merged), `src/ethereum/forks/amsterdam/vm/gas.py`.
  Line numbers below are that file's unless another file is named.

  Both EIPs are contested and in Last Call (2026-11); the constants are not final. They
  live in ONE place: `Params` (EIP-8037) and `AccessParams` (EIP-8038) with EELS's values
  as defaults. Every derived cost below and in `Evm.Amsterdam.Vm.StatePricing` reads
  them from there (EELS itself marks both classes "may be patched at runtime by a future
  gas repricing utility", gas.py:37-38 / 61).

  Modelled: the constants, the per-frame `GasMeter` and every operation EELS performs on
  it (charge, the LIFO refill, commit, the rollbacks, the child grant and merge-time
  repayment), the transaction's split into execution gas and reservoir under
  `TX_MAX_GAS_LIMIT`, the settlement and the per-dimension block capacity check.
  Not modelled here: the wiring of the meter into Amsterdam's frame machinery
  (`Evm.Amsterdam.processTransaction` still runs Osaka's single-pool tx level; recorded in
  `Evm.Amsterdam.Fork`). The re-costing tool (scripts/reprice.lisp) uses only the
  per-charge prices, which do not need the wiring.
-/

namespace Evm.Amsterdam.Vm.Gas

/-! ## Parameters (the one place) -/

/-- EIP-8037 state-gas constants, gas.py:39-59 (`StateGasCosts`) and the two tx caps
    gas.py:153-154. -/
structure Params where
  /-- `COST_PER_STATE_BYTE` (CPSB), gas.py:47. -/
  costPerStateByte  : Nat := 1530
  /-- `STATE_BYTES_PER_NEW_ACCOUNT`, gas.py:48. -/
  bytesNewAccount   : Nat := 120
  /-- `STATE_BYTES_PER_STORAGE_SET`, gas.py:49. -/
  bytesStorageSet   : Nat := 64
  /-- `STATE_BYTES_PER_AUTH_BASE`, gas.py:50. -/
  bytesAuthBase     : Nat := 23
  /-- `TX_MAX_GAS_LIMIT` (EIP-7825; bounds the execution dimension only), gas.py:153. -/
  txMaxGasLimit     : Nat := 16777216
  /-- `TX_MAX_TOTAL_GAS_LIMIT` (EIP-8037), gas.py:154. -/
  txMaxTotalGasLimit : Nat := 4294967295
  deriving Repr

/-- EIP-8038 execution-gas constants that differ from Osaka, gas.py:75-100. -/
structure AccessParams where
  /-- `WARM_ACCESS`, gas.py:76. -/
  warmAccess        : Nat := 100
  /-- `COLD_ACCOUNT_ACCESS` (Osaka 2600), gas.py:77. -/
  coldAccountAccess : Nat := 3000
  /-- `COLD_STORAGE_ACCESS` (unchanged), gas.py:78. -/
  coldStorageAccess : Nat := 2100
  /-- `STORAGE_WRITE` (new), gas.py:81. -/
  storageWrite      : Nat := 10000
  /-- `CALL_STIPEND`, gas.py:84. -/
  callStipend       : Nat := 2300
  /-- `ACCOUNT_WRITE` (new), gas.py:85. -/
  accountWrite      : Nat := 9000
  /-- `OPCODE_KECCAK256_PER_WORD` (the code-deposit hash cost), gas.py:246. -/
  keccakPerWord     : Nat := 6
  deriving Repr

def params : Params := {}
def accessParams : AccessParams := {}

/-- `StateGasCosts.STORAGE_SET`, gas.py:51-53. -/
def storageSet (p : Params := params) : Nat := p.bytesStorageSet * p.costPerStateByte
/-- `StateGasCosts.NEW_ACCOUNT`, gas.py:54-56. -/
def newAccount (p : Params := params) : Nat := p.bytesNewAccount * p.costPerStateByte
/-- `StateGasCosts.AUTH_BASE`, gas.py:57-59. -/
def authBase (p : Params := params) : Nat := p.bytesAuthBase * p.costPerStateByte

/-- `CALL_VALUE = ACCOUNT_WRITE + CALL_STIPEND`, gas.py:86 (Osaka: 9000 flat). -/
def callValue (q : AccessParams := accessParams) : Nat := q.accountWrite + q.callStipend
/-- `CREATE_ACCESS = ACCOUNT_WRITE + COLD_ACCOUNT_ACCESS`, gas.py:90 (Osaka `CREATE`: 32000). -/
def createAccess (q : AccessParams := accessParams) : Nat := q.accountWrite + q.coldAccountAccess
/-- `REFUND_STORAGE_CLEAR = (STORAGE_WRITE + COLD_STORAGE_ACCESS) * 4800 // 5000`,
    gas.py:98-100 (Osaka 4800). -/
def refundStorageClear (q : AccessParams := accessParams) : Nat :=
  (q.storageWrite + q.coldStorageAccess) * 4800 / 5000
/-- `TX_ACCESS_LIST_ADDRESS = COLD_ACCOUNT_ACCESS - WARM_ACCESS`, gas.py:147-149 (Osaka 2400). -/
def txAccessListAddress (q : AccessParams := accessParams) : Nat := q.coldAccountAccess - q.warmAccess
/-- `TX_ACCESS_LIST_STORAGE_KEY = COLD_STORAGE_ACCESS - WARM_ACCESS`, gas.py:150-152 (Osaka 1900). -/
def txAccessListStorageKey (q : AccessParams := accessParams) : Nat := q.coldStorageAccess - q.warmAccess

example : storageSet = 97920 := rfl
example : newAccount = 183600 := rfl
example : authBase = 35190 := rfl
example : callValue = 11300 := rfl
example : createAccess = 12000 := rfl
example : refundStorageClear = 11616 := rfl
example : txAccessListAddress = 2900 := rfl
example : txAccessListStorageKey = 2000 := rfl

/-! ## The gas meter (gas.py:266-326) -/

/-- EELS `GasMeter`, gas.py:266-326: a frame's execution gas, its state-gas reservoir,
    the reservoir level a rollback refills to, the refund counter, the spill (execution
    gas spent on state charges after the reservoir emptied, EIP-8037's
    `state_gas_from_gas_left`) and the committed spill. -/
structure GasMeter where
  gasLeft                : Nat
  stateGasLeft           : Nat
  stateGasBaseline       : Nat
  refundCounter          : Int := 0
  stateGasSpilled        : Nat := 0
  stateGasCommittedSpill : Nat := 0
  deriving Repr, DecidableEq

/-- `charge_gas_from_meter`, gas.py:379-393: execution charges draw on `gas_left` only.
    `none` = `OutOfGasError`. -/
def chargeGas (m : GasMeter) (amount : Nat) : Option GasMeter :=
  if m.gasLeft < amount then none else some { m with gasLeft := m.gasLeft - amount }

/-- `charge_state_gas_from_meter`, gas.py:413-436: the reservoir first, then `gas_left`,
    the overflow tracked as spill. -/
def chargeStateGas (m : GasMeter) (amount : Nat) : Option GasMeter :=
  if amount ≤ m.stateGasLeft then
    some { m with stateGasLeft := m.stateGasLeft - amount }
  else if amount ≤ m.stateGasLeft + m.gasLeft then
    let remainder := amount - m.stateGasLeft
    some { m with stateGasLeft := 0, gasLeft := m.gasLeft - remainder,
                  stateGasSpilled := m.stateGasSpilled + remainder }
  else none

/-- `commit_state_gas`, gas.py:459-490: the state bought so far becomes non-refillable. -/
def commitStateGas (m : GasMeter) : GasMeter :=
  { m with stateGasCommittedSpill := m.stateGasCommittedSpill + m.stateGasSpilled,
           stateGasBaseline := m.stateGasLeft, stateGasSpilled := 0 }

/-- `restore_state_gas`, gas.py:493-517: on revert or halt the spill returns to
    `gas_left` first, the reservoir resets to the baseline, the refunds are dropped. -/
def restoreStateGas (m : GasMeter) : GasMeter :=
  { m with gasLeft := m.gasLeft + m.stateGasSpilled, stateGasSpilled := 0,
           stateGasLeft := m.stateGasBaseline, refundCounter := 0 }

/-- `restore_state_gas_to_entry`, gas.py:520-555: every spill (committed or not) back to
    `gas_left`, the reservoir and baseline back to the frame's grant. -/
def restoreStateGasToEntry (m : GasMeter) (reservoir : Nat) : GasMeter :=
  { m with gasLeft := m.gasLeft + m.stateGasSpilled + m.stateGasCommittedSpill,
           stateGasSpilled := 0, stateGasCommittedSpill := 0,
           stateGasLeft := reservoir, stateGasBaseline := reservoir }

/-- `tx_state_gas_used`, gas.py:558-591: reservoir drawn since the grant plus the spill,
    outstanding or committed; negative when refunds exceed charges. -/
def txStateGasUsed (m : GasMeter) (reservoir : Nat) : Int :=
  (reservoir : Int) - m.stateGasLeft + m.stateGasSpilled + m.stateGasCommittedSpill

/-- `credit_state_gas_refund`, gas.py:594-616: LIFO — `gas_left` up to the spill, the
    rest to the reservoir. -/
def creditStateGasRefund (m : GasMeter) (amount : Nat) : GasMeter :=
  let fromGasLeft := min amount m.stateGasSpilled
  { m with gasLeft := m.gasLeft + fromGasLeft, stateGasSpilled := m.stateGasSpilled - fromGasLeft,
           stateGasLeft := m.stateGasLeft + (amount - fromGasLeft) }

/-- `repay_state_gas_spill`, gas.py:619-647: after a successful child merges, the
    reservoir repays the spill still outstanding. -/
def repayStateGasSpill (m : GasMeter) : GasMeter :=
  let repayment := min m.stateGasLeft m.stateGasSpilled
  { m with gasLeft := m.gasLeft + repayment, stateGasLeft := m.stateGasLeft - repayment,
           stateGasSpilled := m.stateGasSpilled - repayment }

/-- `forfeit_remaining_gas`, gas.py:650-663 (EELS asserts the spill was restored first). -/
def forfeitRemainingGas (m : GasMeter) : GasMeter := { m with gasLeft := 0 }

/-- `max_message_call_gas`, gas.py:846-861: all but one 64th. -/
def maxMessageCallGas (gas : Nat) : Nat := gas - gas / 64

/-- `withhold_create_gas`, gas.py:666-686: the 63/64 rule applies to `gas_left` only. -/
def withholdCreateGas (m : GasMeter) : GasMeter × Nat :=
  let child := maxMessageCallGas m.gasLeft
  ({ m with gasLeft := m.gasLeft - child }, child)

/-- `drain_state_gas_reservoir`, gas.py:689-710: the child gets the WHOLE reservoir. -/
def drainStateGasReservoir (m : GasMeter) : GasMeter × Nat :=
  ({ m with stateGasLeft := 0 }, m.stateGasLeft)

/-- `restore_child_gas`, gas.py:713-734: a child never entered returns both grants. -/
def restoreChildGas (m : GasMeter) (gas reservoir : Nat) : GasMeter :=
  { m with gasLeft := m.gasLeft + gas, stateGasLeft := m.stateGasLeft + reservoir }

/-- The `GAS` opcode under EIP-8037 pushes `gas_left` only, never the reservoir: EELS
    `vm/instructions/control_flow.py:125-143` (`gas_left`) pushes `evm.gas_meter.gas_left`. -/
def gasOpcodeValue (m : GasMeter) : Nat := m.gasLeft

/-! ## The transaction's two pools and its settlement -/

/-- `allocate_evm_gas`, gas.py:1105-1137: execution gas capped by what remains under
    `TX_MAX_GAS_LIMIT` after the intrinsic cost; the rest is the reservoir.
    Returns `(execution_gas, state_gas_reservoir)`. -/
def allocateEvmGas (txGas intrinsicExecution : Nat) (p : Params := params) : Nat × Nat :=
  let evmGas := txGas - intrinsicExecution
  let budget := p.txMaxGasLimit - intrinsicExecution
  let execution := min budget evmGas
  (execution, evmGas - execution)

/-- EELS `TransactionGasSettlement`, gas.py:1140-1160. -/
structure Settlement where
  gasUsed          : Nat
  gasLeft          : Nat
  executionGasUsed : Nat
  stateGasUsed     : Nat
  deriving Repr, DecidableEq

/-- `settle_transaction_gas`, gas.py:1163-1228: refund capped at a fifth of the pre-refund
    usage (which INCLUDES state gas), the calldata floor, and the per-dimension block
    amounts (state gas clamped at 0; execution gas pre-refund, EIP-7778). -/
def settleTransactionGas (txGas calldataFloor gasLeft stateGasLeft : Nat) (refundCounter : Nat)
    (stateGasUsed : Int) : Settlement :=
  let before := txGas - gasLeft - stateGasLeft
  let refund := min (before / 5) refundCounter
  let gasUsed := max (before - refund) calldataFloor
  let settledState := stateGasUsed.toNat
  { gasUsed, gasLeft := txGas - gasUsed,
    executionGasUsed := max (before - settledState) calldataFloor,
    stateGasUsed := settledState }

/-- `check_block_gas_capacity`, gas.py:1038-1102 (execution and state dimensions; the blob
    dimension is Osaka's): the execution check is against `min(TX_MAX_GAS_LIMIT, tx.gas)`,
    the state check against the full `tx.gas`. `true` = fits. -/
def blockGasCapacityOk (blockGasLimit blockGasUsed blockStateGasUsed txGas : Nat)
    (p : Params := params) : Bool :=
  decide (min p.txMaxGasLimit txGas ≤ blockGasLimit - blockGasUsed) &&
  decide (txGas ≤ blockGasLimit - blockStateGasUsed)

/-! ## Facts (all proved) -/

/-- A state charge takes exactly `amount` out of the two pools together. -/
theorem chargeStateGas_pools {m m' : GasMeter} {a : Nat} (h : chargeStateGas m a = some m') :
    m'.gasLeft + m'.stateGasLeft + a = m.gasLeft + m.stateGasLeft := by
  unfold chargeStateGas at h
  split at h
  · cases h; simp only; omega
  · split at h
    · cases h; simp only; omega
    · cases h

/-- A state charge never touches the baseline, the refunds or the committed spill. -/
theorem chargeStateGas_keeps {m m' : GasMeter} {a : Nat} (h : chargeStateGas m a = some m') :
    m'.stateGasBaseline = m.stateGasBaseline ∧ m'.refundCounter = m.refundCounter ∧
    m'.stateGasCommittedSpill = m.stateGasCommittedSpill := by
  unfold chargeStateGas at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl⟩
  · split at h
    · cases h; exact ⟨rfl, rfl, rfl⟩
    · cases h

/-- LIFO exactness (gas.py:598-601 "restores the exact pools the charge drew from"): with
    no spill outstanding, crediting back a charge restores the meter exactly. -/
theorem credit_after_charge {m m' : GasMeter} {a : Nat} (hs : m.stateGasSpilled = 0)
    (h : chargeStateGas m a = some m') : creditStateGasRefund m' a = m := by
  unfold chargeStateGas at h
  split at h
  · cases h; cases m; simp only [creditStateGasRefund] at *; subst hs; congr 1 <;> omega
  · split at h
    · cases h; cases m; simp only [creditStateGasRefund] at *; subst hs; congr 1 <;> omega
    · cases h

/-- A rollback leaves the reservoir at the baseline and no spill outstanding. -/
theorem restoreStateGas_resets (m : GasMeter) :
    (restoreStateGas m).stateGasLeft = m.stateGasBaseline ∧ (restoreStateGas m).stateGasSpilled = 0 :=
  ⟨rfl, rfl⟩

/-- After a merge-time repayment the claim and the credit cannot both survive (the EELS
    assert, gas.py:644-647). -/
theorem repay_exclusive (m : GasMeter) :
    (repayStateGasSpill m).stateGasLeft = 0 ∨ (repayStateGasSpill m).stateGasSpilled = 0 := by
  simp only [repayStateGasSpill]; omega

/-- Granting a child the whole reservoir and returning it unused is the identity. -/
theorem drain_restore (m : GasMeter) :
    restoreChildGas (drainStateGasReservoir m).1 0 (drainStateGasReservoir m).2 = m := by
  cases m; simp [drainStateGasReservoir, restoreChildGas]

/-- The split loses nothing and the execution part stays under `TX_MAX_GAS_LIMIT`. -/
theorem allocate_split (txGas i : Nat) (p : Params) :
    (allocateEvmGas txGas i p).1 + (allocateEvmGas txGas i p).2 = txGas - i ∧
    i + (allocateEvmGas txGas i p).1 ≤ max p.txMaxGasLimit i := by
  simp only [allocateEvmGas]; omega

/-- A tx under `TX_MAX_GAS_LIMIT` gets no reservoir: its gas is all execution gas, as
    before EIP-8037 (state charges then spill into `gas_left`). -/
theorem allocate_small (txGas i : Nat) (p : Params) (h : txGas ≤ p.txMaxGasLimit) :
    (allocateEvmGas txGas i p).2 = 0 := by
  simp only [allocateEvmGas]; omega

/-- The settled gas never undercuts the calldata floor nor exceeds the limit's pre-refund
    usage (with the floor). -/
theorem settle_bounds (txGas fl gl sl r : Nat) (su : Int) :
    fl ≤ (settleTransactionGas txGas fl gl sl r su).gasUsed ∧
    (settleTransactionGas txGas fl gl sl r su).gasUsed ≤ max (txGas - gl - sl) fl := by
  simp only [settleTransactionGas]; omega

end Evm.Amsterdam.Vm.Gas
