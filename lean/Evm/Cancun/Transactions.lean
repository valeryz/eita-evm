/-
  Evm.Cancun.Transactions — EIP-2718 typed envelopes including
  EIP-4844 BlobTransaction.

  EELS reference: ethereum/forks/cancun/transactions.py.

  Cancun's `Transaction` is a tagged union over four envelopes:
    - 0x00 (untyped legacy)         — `LegacyTransaction`
    - 0x01 (EIP-2930 access list)   — `AccessListTransaction`
    - 0x02 (EIP-1559 fee market)    — `FeeMarketTransaction`
    - 0x03 (EIP-4844 blob)          — `BlobTransaction`

  This module declares all four variants but currently only the
  legacy and the blob shapes are routed through the dispatcher
  (the others are stubs that re-use the legacy field set).
  Berlin/London bring-up will fill in the 2930 / 1559 paths.
-/

import Evm.BaseTypes
import Evm.Frontier.Transactions

namespace Evm.Cancun

/-- EELS `forks/cancun/transactions.py:AccessListEntry`. A single
    address with a list of warm storage keys. -/
structure AccessListEntry where
  address     : Evm.Address
  storageKeys : List Evm.U256
  deriving Repr, Inhabited

/-- EIP-4844 typed envelope (tx-type byte `0x03`).

    EELS `forks/cancun/transactions.py:BlobTransaction` lines
    78-99 (May 2024 snapshot). Note the absence of `to = none`:
    EIP-4844 forbids contract-creation in a blob tx
    (`forks/cancun/transactions.py:BlobTransaction.to: Address`).

    The blob data itself is *not* visible to the EVM — only the
    versioned hashes are, via the BLOBHASH opcode. -/
structure BlobTransaction where
  chainId              : Evm.U256
  nonce                : Evm.U256
  /-- Per EIP-1559: max priority fee (tip) per unit gas. -/
  maxPriorityFeePerGas : Evm.U256
  /-- Per EIP-1559: total max fee per unit gas (tip + base). -/
  maxFeePerGas         : Evm.U256
  gas                  : Evm.U256
  /-- 4844 forbids contract-creation; must be an address. -/
  to                   : Evm.Address
  value                : Evm.U256
  data                 : Evm.Bytes
  accessList           : List AccessListEntry
  /-- EIP-4844 unique: cap on the per-unit blob gas fee. -/
  maxFeePerBlobGas     : Evm.U256
  /-- KZG commitments hashed and version-tagged. Indexed by BLOBHASH. -/
  blobVersionedHashes  : List Evm.Hash32
  /-- Signature parity bit (post-EIP-2718 envelopes use `y_parity`
      not the legacy `v`). -/
  yParity              : Evm.U256
  r                    : Evm.U256
  s                    : Evm.U256
  deriving Repr, Inhabited

/-- Discriminated union for Cancun's `Transaction`.

    EELS `forks/cancun/transactions.py:Transaction = Union[...]`. -/
inductive Transaction where
  | legacy       (tx : Evm.Frontier.Transaction)
  | accessList   (tx : Evm.Frontier.Transaction)        -- placeholder
  | feeMarket    (tx : Evm.Frontier.Transaction)        -- placeholder
  | blob         (tx : BlobTransaction)
  deriving Repr, Inhabited

namespace Transaction

/-- Extract the underlying gas limit, irrespective of variant. -/
def gas : Transaction → Evm.U256
  | .legacy t       => t.gas
  | .accessList t   => t.gas
  | .feeMarket t    => t.gas
  | .blob t         => t.gas

/-- Extract `to`, with `none` for contract-creation. EIP-4844 blob
    txs always have a `to`. -/
def to : Transaction → Option Evm.Address
  | .legacy t       => t.to
  | .accessList t   => t.to
  | .feeMarket t    => t.to
  | .blob t         => some t.to

/-- EIP-4844 blob hashes (empty for non-blob txs). Drives BLOBHASH. -/
def blobVersionedHashes : Transaction → List Evm.Hash32
  | .blob t   => t.blobVersionedHashes
  | _         => []

end Transaction

end Evm.Cancun
