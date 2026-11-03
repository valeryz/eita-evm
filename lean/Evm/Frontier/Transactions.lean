/-
  Evm.Frontier.Transactions — Frontier transaction type.

  EELS reference: ethereum/frontier/transactions.py.

  Frontier predates EIP-2718 (Berlin) so there is only one transaction
  shape — the legacy form. It is signed with the homestead-incompatible
  `v ∈ {27, 28}` convention (no chainId; EIP-155 replay protection arrives
  at Spurious Dragon).
-/

import Evm.BaseTypes

namespace Evm.Frontier

/-- A legacy (Frontier) transaction. `to = none` means a contract-creation
    transaction; otherwise `to = some addr` for a call. -/
structure Transaction where
  nonce    : Evm.U256
  gasPrice : Evm.U256
  gas      : Evm.U256
  to       : Option Evm.Address
  value    : Evm.U256
  data     : Evm.Bytes
  v        : Evm.U256
  r        : Evm.U256
  s        : Evm.U256
  deriving Repr, Inhabited

end Evm.Frontier
