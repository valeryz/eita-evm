/-
  Evm.Prague.Blocks — Prague (Pectra) block, header, withdrawal, and
  execution-layer request types.

  EELS reference: ethereum/forks/prague/blocks.py.
  Activation: timestamp 1,746,612,311 (mainnet, 2025-05-07).

  Delta from Cancun:
    * EIP-7685 adds `requests_hash` to the header (32-byte sha256 commitment
      over all execution-layer requests in the block; computed by
      `Prague.Requests.computeRequestsHash`).
    * The block body gains execution-layer *requests* derived during
      `apply_body`: deposits (EIP-6110), withdrawal requests (EIP-7002),
      and validator consolidations (EIP-7251). These are not stored in
      the block as transmitted (they are recomputed by the verifier from
      receipts + system contract reads) so they don't appear in `Block`;
      only their commitment `requests_hash` does.

  The other Header fields are inherited from Cancun (= London + Shanghai
  + 4844 additions): baseFeePerGas (London / EIP-1559), withdrawalsRoot
  (Shanghai / EIP-4895), blobGasUsed + excessBlobGas (Cancun / EIP-4844),
  parentBeaconBlockRoot (Cancun / EIP-4788).
-/

import Evm.BaseTypes
import Evm.Frontier.Bloom

namespace Evm.Prague

open Evm.Frontier (Bloom)

/-- Prague header. Matches `ethereum/forks/prague/blocks.py::Header`
    field-for-field. Numeric widths use `U256` (difficulty, baseFee) /
    `U64` (number, gas counters, timestamp) the same way EELS does. -/
structure Header where
  parentHash            : Evm.Hash32
  ommersHash            : Evm.Hash32
  coinbase              : Evm.Address
  stateRoot             : Evm.Hash32
  transactionsRoot      : Evm.Hash32
  receiptsRoot          : Evm.Hash32
  logsBloom             : Bloom
  difficulty            : Evm.U256
  number                : Evm.U64
  gasLimit              : Evm.U64
  gasUsed               : Evm.U64
  timestamp             : Evm.U64
  extraData             : Evm.Bytes
  /-- Post-merge: `prevRandao` from the beacon chain replaces the
      pre-merge `mixDigest`/PoW field. EELS keeps the same name
      `prev_randao`. -/
  prevRandao            : Evm.Hash32
  /-- Post-merge: 8 bytes, fixed to all-zero. -/
  nonce                 : Evm.Bytes
  /-- EIP-1559 (London). -/
  baseFeePerGas         : Evm.U256
  /-- EIP-4895 (Shanghai). -/
  withdrawalsRoot       : Evm.Hash32
  /-- EIP-4844 (Cancun). -/
  blobGasUsed           : Evm.U64
  /-- EIP-4844 (Cancun). -/
  excessBlobGas         : Evm.U64
  /-- EIP-4788 (Cancun). -/
  parentBeaconBlockRoot : Evm.Hash32
  /-- EIP-7685 (Prague): sha256 over the per-type request commitments.
      Computed by `Prague.Requests.computeRequestsHash` after all txs
      and system contract calls have executed. -/
  requestsHash          : Evm.Hash32
  deriving Repr, Inhabited

/-- A beacon-chain withdrawal queued for execution on the EL.
    EELS: `ethereum/forks/prague/blocks.py::Withdrawal`.
    Identical to Shanghai's `Withdrawal` (EIP-4895). -/
structure Withdrawal where
  index          : Evm.U64
  validatorIndex : Evm.U64
  address        : Evm.Address
  /-- Amount in *Gwei* (not wei). EELS converts to wei (×10⁹) when
      crediting the recipient. -/
  amount         : Evm.U64
  deriving Repr, Inhabited

/-- An EIP-7685 execution-layer request. Discriminant byte ("type")
    selects the payload schema:

      * 0x00 — deposit (EIP-6110): parsed from logs of
        DEPOSIT_CONTRACT_ADDRESS; 192 bytes
        (pubkey 48 || withdrawal_credentials 32 || amount 8 ||
         signature 96 || index 8).
      * 0x01 — withdrawal request (EIP-7002): read from
        WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS after the post-tx system
        call; 76 bytes (source_address 20 || validator_pubkey 48 ||
        amount 8).
      * 0x02 — consolidation request (EIP-7251): read from
        CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS after the post-tx
        system call; 116 bytes (source_address 20 ||
        source_pubkey 48 || target_pubkey 48).

    See `Prague.Requests` for the canonical hash. -/
structure Request where
  /-- Single-byte type tag, 0x00 / 0x01 / 0x02. -/
  type    : UInt8
  /-- Raw payload bytes, schema selected by `type`. -/
  payload : Evm.Bytes
  deriving Repr, Inhabited

/-- The block body. Note that requests are NOT transmitted in the block
    — they are recomputed during execution (deposits from logs;
    withdrawal/consolidation requests from system-contract reads) and
    only the `requestsHash` is checked against the header.

    `transactions` is held as raw RLP bytes here so the same field can
    carry legacy / typed envelopes; decoding to a typed `Transaction`
    happens in `Prague.Transactions`. -/
structure Block where
  header       : Header
  transactions : List Evm.Bytes
  /-- Ommers are forbidden post-Merge: `ommersHash` must equal
      `keccak256(rlp([]))`. We keep the field for shape parity but
      `applyBlock` enforces emptiness. -/
  ommers       : List Header
  withdrawals  : List Withdrawal
  deriving Repr, Inhabited

end Evm.Prague
