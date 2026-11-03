/-
  Evm.Cancun.Blocks — Cancun block & header.

  EELS reference: ethereum/forks/cancun/blocks.py.

  Delta from Shanghai:
    - EIP-4844: header gains `blobGasUsed`, `excessBlobGas`.
    - EIP-4788: header gains `parentBeaconBlockRoot`.

  Pre-Cancun fields (everything else) are carried forward unchanged
  from the post-merge London/Shanghai header layout. To avoid
  re-declaring the full 17-field record we *embed* Frontier's header
  for the parts that are stable since Frontier (parent/coinbase/...)
  and add the post-merge/post-blob fields next to it. This is a small
  practical compromise — EELS keeps a flat per-fork record but the
  refinement is the same.
-/

import Evm.BaseTypes
import Evm.Frontier.Blocks
import Evm.Shanghai.Withdrawals

namespace Evm.Cancun

/-- A Cancun block header.

    EELS `forks/cancun/blocks.py:Header` (the canonical Python
    `@slotted_freezable` dataclass). Fields appear here in roughly
    the same order EELS uses; types follow our `BaseTypes` mapping.

    Pre-merge fields like `difficulty` and `nonce` are kept as a
    structural placeholder — Paris/Shanghai retain them in the
    header layout even though `difficulty` is forced to 0 and
    `nonce` is forced to zero-byte. -/
structure Header where
  parentHash            : Evm.Hash32
  ommersHash            : Evm.Hash32
  coinbase              : Evm.Address
  stateRoot             : Evm.Hash32
  transactionsRoot      : Evm.Hash32
  receiptRoot           : Evm.Hash32
  bloom                 : Evm.Frontier.Bloom
  difficulty            : Nat
  number                : Nat
  gasLimit              : Nat
  gasUsed               : Nat
  timestamp             : Nat
  extraData             : Evm.Bytes
  /-- Post-merge: `mix_hash` repurposed as `prev_randao` (EIP-4399).
      We keep the original field name to match the wire encoding. -/
  mixDigest             : Evm.Hash32
  /-- 8 bytes; zero post-merge but retained for header-RLP shape. -/
  nonce                 : Evm.Bytes
  /-- EIP-1559 (London). -/
  baseFeePerGas         : Evm.U256
  /-- EIP-4895 (Shanghai) — root of the withdrawals list. -/
  withdrawalsRoot       : Evm.Hash32
  /-- EIP-4844 (Cancun) — `GAS_PER_BLOB · (#blobs in this block)`.
      EELS `forks/cancun/blocks.py:Header.blob_gas_used`. -/
  blobGasUsed           : Nat
  /-- EIP-4844 (Cancun) — block-level "excess" blob gas, used as the
      argument to `fake_exponential` for the blob base fee. EELS
      `forks/cancun/blocks.py:Header.excess_blob_gas`. -/
  excessBlobGas         : Nat
  /-- EIP-4788 (Cancun) — root of the beacon-chain block whose
      execution-layer manifestation is *this* block's parent.
      Exposed to contracts via the `BEACON_ROOTS_ADDRESS` system
      contract; see `Fork.applyBlock` for the system call.
      EELS `forks/cancun/blocks.py:Header.parent_beacon_block_root`. -/
  parentBeaconBlockRoot : Evm.Hash32
  deriving Repr

/-- A Cancun block: header + transactions + ommers (always empty
    post-merge but retained for the header layout's `ommersHash`) +
    EIP-4895 withdrawals list.

    EELS `forks/cancun/blocks.py:Block`. Transactions are heterogenous
    (legacy / 2930 / 1559 / 4844) — see `Evm.Cancun.Transactions`. -/
structure Block where
  header       : Header
  transactions : List Evm.Frontier.Transaction
                 -- TODO: switch to the heterogenous Cancun Transaction
                 -- union once the 2930/1559/4844 variants are wired
                 -- through `processTransaction`. Until then the
                 -- driver wraps each tx as a Frontier-legacy carrying
                 -- the relevant scalar fields.
  ommers       : List Evm.Frontier.Header
  withdrawals  : List Evm.Shanghai.Withdrawal
  deriving Repr

end Evm.Cancun
