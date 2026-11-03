/-
  Evm.Osaka — Fusaka hard fork ("Osaka" execution-layer name).

  EELS reference: `ethereum/forks/osaka/`. Mainnet activation:
  timestamp 1,764,798,551 (2025-12-03 21:49:11 UTC).

  EIPs introduced relative to Prague (per `osaka/__init__.py`):

    * EIP-7594 — PeerDAS (consensus / networking only; no EL semantics).
    * EIP-7823 — MODEXP input length caps (≤ 1024 bytes per operand).
                 Implemented in `Vm/PrecompiledContracts.lean`.
    * EIP-7825 — Per-transaction gas cap (`TX_MAX_GAS_LIMIT = 16_777_216`).
                 Implemented in `Transactions.lean`.
    * EIP-7883 — MODEXP gas cost increase. Implemented in
                 `Vm/PrecompiledContracts.lean` (formula changes).
    * EIP-7918 — Blob base fee bounded by execution cost. The reserve-price
                 clause of `calculate_excess_blob_gas` is `Spec/BlobSchedule.lean`
                 (`calculateExcessBlobGasAt`), emitted and proved for the host.
    * EIP-7934 — RLP execution block size limit (`MAX_RLP_BLOCK_SIZE =
                 MAX_BLOCK_SIZE - SAFETY_MARGIN = 10_485_760 - 2_097_152
                 = 8_388_608` bytes). Block-level constant in this file.
    * EIP-7935 — Default gas limit raised to 60M (validator policy
                 only; no spec change beyond a constant).
    * EIP-7939 — CLZ opcode (0x1E). Implemented in `Vm/Effect.lean`
                 and specced in `Spec/ClzStep.lean`.
    * EIP-7951 — P256VERIFY precompile (0x100). Implemented in
                 `Vm/PrecompiledContracts.lean` and specced in
                 `Spec/P256VerifyStep.lean`.
    * EIP-7892 — Blob parameter only hardforks: `Evm.Fork.bpo1` / `.bpo2`
                 (mainnet timestamps in `Evm.Forks`), their schedule entries
                 in `Spec/BlobSchedule.lean` (`blobParamsAt`).
    * EIP-7642 / EIP-7910 — eth/69 networking + JSON-RPC, no EL effect.

  The block-level transition is otherwise Prague-shaped: same system
  contract sequencing (beacon-roots, history-storage, withdrawal/
  consolidation requests), same withdrawals semantics, same
  `requestsHash` reconciliation.

  Per-tx processing inherits Prague's `process_transaction` and adds
  the EIP-7825 gas cap as an early-error check; per-tx EVM execution
  delegates to `Evm.Osaka.Vm.Effect.applyMessage` so CLZ and
  P256VERIFY are reachable inside every CALL / CREATE sub-frame.
-/

import Evm.BaseTypes
import Evm.Prague.Fork
import Evm.Osaka.Vm.Effect

namespace Evm.Osaka

/-! ## EIP-7825 transaction gas cap

    EELS `forks/osaka/transactions.py` lines 30-31 + 547-548:

        TX_MAX_GAS_LIMIT = Uint(16_777_216)
        ...
        if tx.gas > TX_MAX_GAS_LIMIT:
            raise TransactionGasLimitExceededError(...)

    Enforced as a precondition in `processTransaction`. -/
def txMaxGasLimit : Nat := 16_777_216

/-! ## EIP-7934 block RLP size cap

    EELS `forks/osaka/fork.py` lines 120-123 + 224-226:

        MAX_BLOCK_SIZE     = 10_485_760
        SAFETY_MARGIN      = 2_097_152
        MAX_RLP_BLOCK_SIZE = MAX_BLOCK_SIZE - SAFETY_MARGIN

    Enforced against `rlp.encode(block)`. We don't currently re-encode
    the block to RLP at `applyBlock` time (it arrives pre-decoded from
    the replay harness), so the check is exposed as a helper and left
    unwired in the block driver — a TODO for the real bring-up that
    threads raw RLP through. -/
def maxBlockSize       : Nat := 10_485_760
def blockSafetyMargin  : Nat :=  2_097_152
def maxRlpBlockSize    : Nat := maxBlockSize - blockSafetyMargin

/-! ## EIP-7892 / blob count cap (Osaka tightening)

    EELS `forks/osaka/fork.py` line 123: `BLOB_COUNT_LIMIT = 6`. The
    pre-Osaka effective cap of 6 was implicit in
    `MAX_BLOB_GAS_PER_BLOCK / GAS_PER_BLOB`; Osaka exposes it as a
    distinct guard so type-3 transactions over the limit fail early
    with `BlobCountExceededError`. -/
def blobCountLimit : Nat := 6

/-! ## Per-transaction processing -/

/-- Run one transaction (EELS `process_transaction`): `Evm.Frontier.Vm.Tx.run` at Osaka
    (fork ordinal 18: EIP-7825's gas cap and the six-blob cap join the validation,
    EIP-7883's MODEXP and EIP-7951's P256VERIFY the table), with Osaka's trampoline. -/
def processTransaction
    (state       : Evm.Prague.State)
    (header      : Evm.Prague.Header)
    (blockHashes : List Evm.Hash32)
    (sender      : Evm.Address)
    (tx          : Evm.Prague.Transaction) :
    Except String (Evm.Prague.State × Evm.Frontier.TxResult) :=
  Evm.Prague.processTransaction state header blockHashes sender tx 18 Evm.Osaka.Vm.Effect.trampoline

/-! ## Block-level transition

    Block-level invariants and sequencing are unchanged from Prague.
    The Osaka header introduces no new fields (all PeerDAS-related
    additions live on the consensus layer). We expose `applyBlock` as
    a thin wrapper so downstream callers can target Osaka by name. -/

abbrev Header     := Evm.Prague.Header
abbrev Block      := Evm.Prague.Block
abbrev BlockResult := Evm.Prague.BlockResult

/-- EELS `forks/osaka/fork.py::apply_body` is structurally identical
    to Prague's; the only Osaka-distinctive guard at block-level is the
    EIP-7934 RLP size cap (see `maxRlpBlockSize` above), which we don't
    currently enforce in the replay harness because we don't re-RLP
    blocks here. -/
def applyBlock (state : Evm.Prague.State) (block : Block) :
    Except String BlockResult :=
  -- TODO (EIP-7934): when raw block RLP is threaded through, enforce
  -- `rlp.encode(block).size ≤ maxRlpBlockSize`.
  Evm.Prague.applyBlock state block 18 Evm.Osaka.Vm.Effect.trampoline

end Evm.Osaka
