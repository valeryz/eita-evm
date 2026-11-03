/-
  Evm.Frontier.Spec.HeaderValidity — `validate_header`: the consensus rules a block header
  must satisfy against its parent, every fork from Frontier to Osaka/BPO2, fork-typed.

  EELS references (execution-specs `src/ethereum/forks/`), translated clause by clause:

  * `frontier/fork.py` `validate_header` 209-269 (homestead, tangerine_whistle,
    spurious_dragon identical):
        if header.gas_used > header.gas_limit: raise
        if header.timestamp <= parent_header.timestamp: raise
        if header.number != parent_header.number + 1: raise
        if not check_gas_limit(header.gas_limit, parent_header.gas_limit): raise
        if len(header.extra_data) > 32: raise
        if header.difficulty != calculate_block_difficulty(...): raise
        if header.parent_hash != keccak256(rlp.encode(parent_header)): raise
        validate_proof_of_work(header)
  * `dao_fork/fork.py` `validate_header` 221-290: the same, then for
    `FORK_CRITERIA.block_number <= number < FORK_CRITERIA.block_number + 10` (1,920,000 on
    mainnet) `header.extra_data == b"dao-hard-fork"`.
  * `byzantium/fork.py` `validate_header` 215-277 (to berlin): the same, with
    `parent_has_ommers = parent_header.ommers_hash != EMPTY_OMMER_HASH` fed to the difficulty.
  * `london/fork.py` `validate_header` 289-365: gas_used; then, except on the fork block
    (`header.number != FORK_CRITERIA.block_number`, where the expected base fee is
    `INITIAL_BASE_FEE` and the gas limit is NOT checked), `calculate_base_fee_per_gas`
    226-286, whose first act is `check_gas_limit` (raise); the base fee; timestamp; number;
    extra_data; difficulty. `arrow_glacier`/`gray_glacier` 287-356: the same without the
    fork-block case.
  * `paris/fork.py` `validate_header` 280-330 (shanghai identical): gas_used; base fee (with
    `check_gas_limit` inside); timestamp; number; extra_data; `difficulty != 0`;
    `nonce != b"\x00" * 8`; `ommers_hash != EMPTY_OMMER_HASH` (EIP-3675).
  * `cancun/fork.py` `validate_header` 315-369 (prague 337-391, osaka 347-401 identical):
    `excess_blob_gas != calculate_excess_blob_gas(parent_header)` first, then as Paris.
  * `check_gas_limit` (`frontier/fork.py` 705-742; the same text in every fork, osaka
    1001-1035): `delta = parent_gas_limit // LIMIT_ADJUSTMENT_FACTOR (1024)`; false when
    `gas_limit >= parent + delta`, `gas_limit <= parent - delta` or `gas_limit <
    LIMIT_MINIMUM (5000)` (`frontier/vm/gas.py` 79-80, `osaka/vm/gas.py` 113-114).
  * `calculate_block_difficulty` (`frontier/fork.py` 745-797; `homestead` 745-806, EIP-2;
    `byzantium` 764-832, EIP-100 + EIP-649; constantinople .. gray_glacier the same with
    their `BOMB_DELAY_BLOCKS`: 3,000,000 byzantium; 5,000,000 constantinople/istanbul
    (EIP-1234); 9,000,000 muir_glacier/berlin (EIP-2384); 9,700,000 london (EIP-3554);
    10,700,000 arrow_glacier (EIP-4345); 11,400,000 gray_glacier (EIP-5133)).

  ## What's encoded vs left to the caller

  * Encoded: every clause above, in EELS's order (`validateHeader` returns the FIRST clause
    that raises, so the host names the same rule EELS would reach first); the base fee and
    the excess blob gas through the existing fork specs (`Evm.London.Spec.calculateBaseFeePerGas`,
    `Evm.Osaka.Spec.calculateExcessBlobGasAt`).
  * The caller (the host's header gate) supplies the facts that are byte comparisons over
    header fields: `extraIsDao` (extra_data = b"dao-hard-fork"), `ommersEmpty`
    (ommers_hash = keccak256(rlp([]))), `parentHasOmmers`, `londonForkBlock` (the London
    fork block: on mainnet 12,965,000 — the block whose parent has no base fee), the nonce
    as an integer.
  * Not here: `parent_hash = keccak256(rlp(parent))` (the host ties every block to the
    hash of the block it replayed before it, and each header to its own hash);
    `validate_proof_of_work` (ethash: out of scope — the replay does not verify the seal);
    `validate_ommers` (set rules over recent blocks: the host's, src/chains/block-system.lisp,
    with this function for each ommer's own header); Osaka's `MAX_RLP_BLOCK_SIZE`
    (state_transition, not validate_header).
  * Amsterdam (unscheduled) is not modelled: from Cancun on this is Cancun's rule.
-/

import Evm.Forks
import Evm.London.Spec.BaseFee
import Evm.Osaka.Spec.BlobSchedule

namespace Evm.Frontier.Spec.HeaderValidity

/-- `GasCosts.LIMIT_ADJUSTMENT_FACTOR` (`frontier/vm/gas.py` 79). -/
def limitAdjustmentFactor : Nat := 1024
/-- `GasCosts.LIMIT_MINIMUM` (`frontier/vm/gas.py` 80). -/
def limitMinimum : Nat := 5000
/-- `MINIMUM_DIFFICULTY` (`frontier/fork.py` 59). -/
def minimumDifficulty : Nat := 131072
/-- The DAO fork block, `dao_fork/__init__.py` `FORK_CRITERIA = ByBlockNumber(1920000)`. -/
def daoForkBlock : Nat := 1920000

/-- `check_gas_limit(gas_limit, parent_gas_limit)`. -/
def checkGasLimit (gasLimit parentGasLimit : Nat) : Bool :=
  let delta := parentGasLimit / limitAdjustmentFactor
  if gasLimit ≥ parentGasLimit + delta then false
  else if gasLimit ≤ parentGasLimit - delta then false
  else if gasLimit < limitMinimum then false
  else true

/-- `BOMB_DELAY_BLOCKS` of fork `f` (0: Frontier .. Spurious Dragon have none). -/
def bombDelay : Evm.Fork → Nat
  | .byzantium => 3000000
  | .constantinople | .petersburg | .istanbul => 5000000
  | .muirGlacier | .berlin => 9000000
  | .london => 9700000
  | .arrowGlacier => 10700000
  | .grayGlacier => 11400000
  | _ => 0

/-- `calculate_block_difficulty` of fork `f` (before Paris), Python's integer arithmetic as
    `Int` (`//` is floor division: `Int./` is Euclidean, the same for a positive divisor).
    Called after the timestamp clause, so `timestamp > parentTimestamp` (EELS subtracts them
    as U256). -/
def calculateBlockDifficulty (f : Evm.Fork) (number timestamp parentTimestamp parentDifficulty : Nat)
    (parentHasOmmers : Bool) : Nat :=
  let difficulty : Int :=
    if f = .frontier then
      -- frontier: max_adjustment_delta = parent // 2048, +/- by the 13-second rule (Uint)
      let delta := parentDifficulty / 2048
      if timestamp < parentTimestamp + 13 then ((parentDifficulty + delta : Nat) : Int)
      else ((parentDifficulty - delta : Nat) : Int)
    else
      -- homestead (EIP-2): parent // 2048 * max(1 - (ts - pts) // 10, -99);
      -- byzantium (EIP-100): parent // 2048 * max((2 if parent_has_ommers else 1) - (ts - pts) // 9, -99)
      let c : Int := if f.atLeast .byzantium then (if parentHasOmmers then 2 else 1) else 1
      let k : Nat := if f.atLeast .byzantium then 9 else 10
      let offset : Int := ((parentDifficulty / 2048 : Nat) : Int) * max (c - (((timestamp - parentTimestamp) / k : Nat) : Int)) (-99)
      (parentDifficulty : Int) + offset
  let numBombPeriods : Int := ((number : Int) - (bombDelay f : Int)) / 100000 - 2
  let difficulty := if numBombPeriods ≥ 0 then difficulty + 2 ^ numBombPeriods.toNat else difficulty
  (max difficulty (minimumDifficulty : Int)).toNat

/-- The header fields `validate_header` reads (numbers as integers). -/
structure View where
  number        : Nat
  timestamp     : Nat
  gasLimit      : Nat
  gasUsed       : Nat
  extraLen      : Nat
  difficulty    : Nat
  nonce         : Nat
  baseFee       : Nat
  excessBlobGas : Nat
  blobGasUsed   : Nat

/-- The `raise InvalidBlock` sites of `validate_header`, named. -/
inductive Violation where
  | excessBlobGas | gasUsedAboveLimit | gasLimit | baseFee | timestamp | number
  | extraData | difficulty | nonce | ommersHash | daoExtraData
  deriving DecidableEq, Repr

/-- The code the host's emitted term returns for each (0 = valid). -/
def Violation.code : Violation → Nat
  | .excessBlobGas => 1 | .gasUsedAboveLimit => 2 | .gasLimit => 3 | .baseFee => 4
  | .timestamp => 5 | .number => 6 | .extraData => 7 | .difficulty => 8 | .nonce => 9
  | .ommersHash => 10 | .daoExtraData => 11

def code : Option Violation → Nat
  | none => 0
  | some v => v.code

/-- `validate_header(chain, header)` of fork `f` against the parent header `p` (the clauses
    the module note lists, in EELS's order): the first that raises, `none` when valid. -/
def validateHeader (f : Evm.Fork) (h p : View) (extraIsDao ommersEmpty parentHasOmmers londonForkBlock : Bool) :
    Option Violation :=
  let difficultyOk : Prop :=
    h.difficulty = calculateBlockDifficulty f h.number h.timestamp p.timestamp p.difficulty parentHasOmmers
  if ¬ f.atLeast .london then
    -- frontier .. berlin (dao_fork: the extra-data rule last, before the seal)
    if h.gasUsed > h.gasLimit then some .gasUsedAboveLimit
    else if h.timestamp ≤ p.timestamp then some .timestamp
    else if h.number ≠ p.number + 1 then some .number
    else if ¬ checkGasLimit h.gasLimit p.gasLimit then some .gasLimit
    else if h.extraLen > 32 then some .extraData
    else if ¬ difficultyOk then some .difficulty
    else if f = .daoFork ∧ daoForkBlock ≤ h.number ∧ h.number < daoForkBlock + 10 ∧ ¬ extraIsDao
    then some .daoExtraData
    else none
  else
    -- london on: after the base fee (computed by calculate_base_fee_per_gas, which first
    -- checks the gas limit; on the London fork block INITIAL_BASE_FEE, unchecked limit)
    let rest : Option Violation :=
      if h.timestamp ≤ p.timestamp then some .timestamp
      else if h.number ≠ p.number + 1 then some .number
      else if h.extraLen > 32 then some .extraData
      else if ¬ f.atLeast .paris then (if ¬ difficultyOk then some .difficulty else none)
      else if h.difficulty ≠ 0 then some .difficulty
      else if h.nonce ≠ 0 then some .nonce
      else if ¬ ommersEmpty then some .ommersHash
      else none
    let afterExcess : Option Violation :=
      if h.gasUsed > h.gasLimit then some .gasUsedAboveLimit
      else if f = .london ∧ londonForkBlock then
        (if h.baseFee ≠ Evm.London.Spec.initialBaseFee then some .baseFee else rest)
      else if ¬ checkGasLimit h.gasLimit p.gasLimit then some .gasLimit
      else if h.baseFee ≠ Evm.London.Spec.calculateBaseFeePerGas p.gasUsed
                             (p.gasLimit / Evm.London.Spec.elasticityMultiplier) p.baseFee
      then some .baseFee
      else rest
    -- cancun on: the excess blob gas first
    if f.atLeast .cancun ∧
       h.excessBlobGas ≠ Evm.Osaka.Spec.calculateExcessBlobGasAt f p.excessBlobGas p.blobGasUsed p.baseFee
    then some .excessBlobGas
    else afterExcess

end Evm.Frontier.Spec.HeaderValidity
