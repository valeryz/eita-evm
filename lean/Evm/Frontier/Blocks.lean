/-
  Evm.Frontier.Blocks — block and header types for Frontier.

  EELS reference: ethereum/frontier/blocks.py.
-/

import Evm.BaseTypes
import Evm.Frontier.Bloom
import Evm.Frontier.Transactions

namespace Evm.Frontier

/-- Frontier block header. Note: `withdrawalsRoot`, blob-gas fields,
    `prevRandao`, and `parentBeaconBlockRoot` arrive at Shanghai,
    Cancun, Paris, and Cancun respectively.

    `baseFeePerGas` is introduced at London (EIP-1559); for pre-London
    forks it defaults to 0 and is ignored. EELS keeps a separate Header
    struct per fork (see `forks/london/blocks.py` line 176, the added
    `base_fee_per_gas: Uint` field). The Lean delta-only layout keeps
    one Header and lets the field default for predecessors. -/
structure Header where
  parentHash       : Evm.Hash32
  ommersHash       : Evm.Hash32
  coinbase         : Evm.Address
  stateRoot        : Evm.Hash32
  transactionsRoot : Evm.Hash32
  receiptRoot      : Evm.Hash32
  bloom            : Bloom
  difficulty       : Nat
  number           : Nat
  gasLimit         : Nat
  gasUsed          : Nat
  timestamp        : Nat
  extraData        : Evm.Bytes
  mixDigest        : Evm.Hash32
  /-- 8 bytes; mining nonce (PoW). -/
  nonce            : Evm.Bytes
  /-- EIP-1559 (London+); 0 for pre-London forks. EELS:
      `forks/london/blocks.py` line 176. See `Evm.London.Blocks`. -/
  baseFeePerGas    : Nat              := 0
  deriving Repr

/-- A Frontier block: a header plus its transactions and uncle headers. -/
structure Block where
  header       : Header
  transactions : List Transaction
  ommers       : List Header
  deriving Repr

end Evm.Frontier
