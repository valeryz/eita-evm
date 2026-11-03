/-
  Evm.London.Transactions — typed-transaction envelope (Berlin + London).

  EELS reference:
    * `forks/berlin/transactions.py`  — LegacyTransaction + AccessListTransaction
    * `forks/london/transactions.py`  — adds FeeMarketTransaction (type 0x02)
                                        (lines 177-251)

  The London `Transaction` is a sum of three shapes:
    * 0x00 / untyped: LegacyTransaction       (Frontier-shape)
    * 0x01:           AccessListTransaction   (Berlin / EIP-2930)
    * 0x02:           FeeMarketTransaction    (London / EIP-1559)

  The two typed variants carry a non-empty `accessList`; FeeMarket
  replaces `gasPrice` with `maxFeePerGas` / `maxPriorityFeePerGas`.

  We re-use Frontier's `Transaction` for the legacy shape and add an
  `Access` record + the two new variants here so London-aware code
  (and signature recovery, and `encode_transaction`) can pattern-match
  on the envelope.
-/

import Evm.BaseTypes
import Evm.Frontier.Transactions

namespace Evm.London

/-- EELS `forks/london/transactions.py` lines 87-103 (`Access`). -/
structure Access where
  account : Evm.Address
  /-- A list of 32-byte storage slots. -/
  slots   : List Evm.U256
  deriving Repr, Inhabited

/-- EELS `forks/london/transactions.py` lines 106-175 (`AccessListTransaction`,
    EIP-2930). Same shape as a legacy tx plus chainId + accessList; uses
    `y_parity` instead of `v` since the chainId is no longer rolled in. -/
structure AccessListTransaction where
  chainId    : Evm.U256
  nonce      : Evm.U256
  gasPrice   : Evm.U256
  gas        : Evm.U256
  to         : Option Evm.Address
  value      : Evm.U256
  data       : Evm.Bytes
  accessList : List Access
  yParity    : Evm.U256
  r          : Evm.U256
  s          : Evm.U256
  deriving Repr, Inhabited

/-- EELS `forks/london/transactions.py` lines 177-251 (`FeeMarketTransaction`,
    EIP-1559). No `gasPrice` — replaced by the (maxFee, maxPriorityFee)
    pair. The effective gas price the sender pays is
    `min(maxFeePerGas, baseFeePerGas + maxPriorityFeePerGas)`. -/
structure FeeMarketTransaction where
  chainId               : Evm.U256
  nonce                 : Evm.U256
  maxPriorityFeePerGas  : Evm.U256
  maxFeePerGas          : Evm.U256
  gas                   : Evm.U256
  to                    : Option Evm.Address
  value                 : Evm.U256
  data                  : Evm.Bytes
  accessList            : List Access
  yParity               : Evm.U256
  r                     : Evm.U256
  s                     : Evm.U256
  deriving Repr, Inhabited

/-- EELS `forks/london/transactions.py` line 254 (`Transaction = Legacy |
    AccessList | FeeMarket`). The decoder in EELS picks by the
    first-byte type tag (`b"\x01"` / `b"\x02"`), falling back to
    legacy. We mirror that as a Lean inductive. -/
inductive Transaction where
  | legacy     (tx : Evm.Frontier.Transaction)
  | accessList (tx : AccessListTransaction)
  | feeMarket  (tx : FeeMarketTransaction)
  deriving Repr, Inhabited

namespace Transaction

/-- Common projections so callers don't always have to destructure. -/

def nonce : Transaction → Evm.U256
  | .legacy tx     => tx.nonce
  | .accessList tx => tx.nonce
  | .feeMarket tx  => tx.nonce

def gas : Transaction → Evm.U256
  | .legacy tx     => tx.gas
  | .accessList tx => tx.gas
  | .feeMarket tx  => tx.gas

def to : Transaction → Option Evm.Address
  | .legacy tx     => tx.to
  | .accessList tx => tx.to
  | .feeMarket tx  => tx.to

def value : Transaction → Evm.U256
  | .legacy tx     => tx.value
  | .accessList tx => tx.value
  | .feeMarket tx  => tx.value

def data : Transaction → Evm.Bytes
  | .legacy tx     => tx.data
  | .accessList tx => tx.data
  | .feeMarket tx  => tx.data

/-- The access list of typed transactions. Empty for legacy. The
    field name `accessList` would clash with the inductive constructor
    `Transaction.accessList`; we use `accessEntries` here. -/
def accessEntries : Transaction → List Access
  | .legacy _      => []
  | .accessList tx => tx.accessList
  | .feeMarket tx  => tx.accessList

end Transaction

end Evm.London
