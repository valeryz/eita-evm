/-
  Evm.Shanghai.Blocks — Shanghai-shaped block header and body.

  EELS reference: ethereum/forks/shanghai/blocks.py.

  Deltas from London (Paris is a stub in this repo):
    * Header gains `withdrawals_root` (EIP-4895; blocks.py line 206).
    * Block body gains `withdrawals : Tuple[Withdrawal, ...]`
      (blocks.py line 260).

  Inherits from London: `base_fee_per_gas` (EIP-1559). From Paris:
  ommers field exists but is always empty and `difficulty` carries
  PREVRANDAO bits via `prev_randao` (blocks.py line 187).

  The `Withdrawal` record matches EELS blocks.py lines 34-62:

      index           : U64       -- monotonically increasing
      validator_index : U64
      address         : Address   -- execution-layer recipient
      amount          : U256      -- denominated in GWEI

  Note on the amount unit: EIP-4895 specifies the amount as a `uint64`
  in gwei; EELS stores it as `U256` (gwei) and multiplies by `10^9` at
  application time (`process_withdrawals`, fork.py line 663:
  `create_ether(wd_state, wd.address, wd.amount * U256(10**9))`).
  We follow EELS here and store in gwei; `Fork.applyBlock` performs
  the multiplication.
-/

import Evm.BaseTypes
import Evm.Shanghai.Withdrawals

-- `Withdrawal` is defined in `Evm.Shanghai.Withdrawals`; we re-use
-- that one rather than duplicating the structure here.
namespace Evm.Shanghai

/-- Shanghai block header. Mirrors EELS
    `ethereum/forks/shanghai/blocks.py` `Header` (lines 65-210).

    Field set is the union of pre-Shanghai (with `mix_digest` renamed
    to `prev_randao` per Paris/EIP-4399) plus the new
    `withdrawals_root` from EIP-4895.

    Compared to `Evm.Frontier.Header`, the Shanghai header drops
    `mix_digest`, renames it `prev_randao`, and adds:
      * `base_fee_per_gas` (London/EIP-1559)
      * `withdrawals_root` (Shanghai/EIP-4895). -/
structure Header where
  parentHash       : Evm.Hash32
  /-- Post-merge: always `keccak256(rlp([]))` (EMPTY_OMMER_HASH). -/
  ommersHash       : Evm.Hash32
  coinbase         : Evm.Address
  stateRoot        : Evm.Hash32
  transactionsRoot : Evm.Hash32
  receiptRoot      : Evm.Hash32
  logsBloom        : Evm.Bytes
  /-- Post-merge: fixed at 0 (EIP-3675). -/
  difficulty       : Nat
  number           : Nat
  gasLimit         : Nat
  gasUsed          : Nat
  timestamp        : Nat
  extraData        : Evm.Bytes
  /-- PREVRANDAO (EIP-4399). Pre-merge this was `mix_hash` from PoW. -/
  prevRandao       : Evm.Hash32
  /-- Mining nonce, 8 bytes. Post-merge: fixed at zero (EIP-3675). -/
  nonce            : Evm.Bytes
  /-- EIP-1559 base fee per gas. -/
  baseFeePerGas    : Nat
  /-- EIP-4895: root of the withdrawals trie. -/
  withdrawalsRoot  : Evm.Hash32
  deriving Repr, Inhabited

/-- A Shanghai block: header, transactions, ommers (post-merge: empty),
    and withdrawals (Shanghai+).

    EELS `ethereum/forks/shanghai/blocks.py` `Block`, lines 213-263.
    Pre-merge fields kept for shape continuity even though `ommers`
    must always be empty (validated by `check_pow` / equivalent
    block-validity rule). -/
structure Block where
  header       : Header
  /-- Tx-list type left abstract; we model as raw RLP bytes since the
      tx-decoder is Berlin+ territory and this fork stub doesn't yet
      need to dispatch typed transactions. -/
  transactions : List Evm.Bytes
  ommers       : List Header
  withdrawals  : List Withdrawal
  deriving Repr, Inhabited

end Evm.Shanghai
