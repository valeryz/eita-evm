/-
  Evm.Berlin.Transactions — EIP-2718 typed-tx envelope + EIP-2930 access lists.

  EELS reference: ethereum/forks/berlin/transactions.py.

  Berlin introduces the EIP-2718 envelope: a transaction is now either
  the legacy form (no type byte; RLP straight through) or a typed form
  `type_byte || rlp(payload)`, where `type_byte ∈ {0x00, 0x01}` is
  defined here. Berlin defines type `0x01` for `AccessListTransaction`
  (EIP-2930). Later forks add more types: `0x02` at London (EIP-1559),
  `0x03` at Cancun (EIP-4844), `0x04` at Prague (EIP-7702).

  Per EELS' `forks/berlin/transactions.py`, the on-chain `Transaction`
  union is `Union[LegacyTransaction, AccessListTransaction]`. We model
  this with an inductive carrying both variants.

  The `legacy` constructor reuses `Evm.Frontier.Transaction` so all
  the pre-Berlin processing code keeps compiling unchanged (delta-only
  fork rule: don't duplicate types that haven't changed shape).
-/

import Evm.BaseTypes
import Evm.Frontier.Transactions

namespace Evm.Berlin

/-- A single access-list tuple: an account plus the list of storage
    slots within it that the caller declares it will touch. -/
structure AccessListEntry where
  address : Evm.Address
  /-- Storage slots, given as raw `U256` keys (not as 32-byte keccak
      inputs — EIP-2929 is per `(address, slot)`, not per Merkle path). -/
  storageKeys : List Evm.U256
  deriving Repr, Inhabited

/-- EIP-2930 type-1 transaction payload (decoded).

    EELS reference: class `AccessListTransaction` in
    `forks/berlin/transactions.py`. Differs from a legacy transaction
    in three places:
      * `chainId` is part of the signed payload (not folded into `v`).
      * `gasPrice` is still flat (EIP-1559 multi-gas arrives at London).
      * `accessList : List AccessListEntry` is part of the payload AND
        pre-warms the listed `(address, slot)` pairs at tx start. -/
structure AccessListTransaction where
  chainId    : Evm.U256
  nonce      : Evm.U256
  gasPrice   : Evm.U256
  gas        : Evm.U256
  to         : Option Evm.Address
  value      : Evm.U256
  data       : Evm.Bytes
  accessList : List AccessListEntry
  /-- Signature `y_parity` flag — 0 or 1 (no chainId folding; that's
      in `chainId` above). EELS calls this `y_parity`. -/
  yParity    : Evm.U256
  r          : Evm.U256
  s          : Evm.U256
  deriving Repr, Inhabited

/-- EIP-2718 union. `legacy` carries the Frontier-shape transaction
    unchanged (kept here so post-Berlin code paths can treat any
    Berlin transaction uniformly without round-tripping through the
    pre-Berlin call sites). `accessList` is the Berlin EIP-2930 form. -/
inductive Transaction where
  | legacy     (tx : Evm.Frontier.Transaction)
  | accessList (tx : AccessListTransaction)
  deriving Repr, Inhabited

namespace Transaction

/-- Tx nonce (uniform projection across variants). -/
def nonce : Transaction → Evm.U256
  | .legacy tx     => tx.nonce
  | .accessList tx => tx.nonce

/-- Effective gas price = `gas_price` for both legacy and
    type-1 forms (London EIP-1559 introduces the priority-fee
    split for the type-2 form). -/
def gasPrice : Transaction → Evm.U256
  | .legacy tx     => tx.gasPrice
  | .accessList tx => tx.gasPrice

def gas : Transaction → Evm.U256
  | .legacy tx     => tx.gas
  | .accessList tx => tx.gas

def to : Transaction → Option Evm.Address
  | .legacy tx     => tx.to
  | .accessList tx => tx.to

def value : Transaction → Evm.U256
  | .legacy tx     => tx.value
  | .accessList tx => tx.value

def data : Transaction → Evm.Bytes
  | .legacy tx     => tx.data
  | .accessList tx => tx.data

/-- Empty list for legacy form (which carries no access list). -/
def accessListOf : Transaction → List AccessListEntry
  | .legacy _      => []
  | .accessList tx => tx.accessList

end Transaction

end Evm.Berlin
