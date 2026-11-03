/-
  Evm.Frontier.ForkTypes — basic fork-level data types.

  EELS reference: ethereum/frontier/fork_types.py.

  Account is in-memory: `code` holds the raw bytes; the trie representation
  (which uses `codeHash` and `storageRoot`) is derived when needed.
-/

import Evm.BaseTypes

namespace Evm.Frontier

/-- An externally-owned account or a contract account. Storage is held
    separately in `State`, keyed by `(address, slot)`. -/
structure Account where
  nonce   : Nat       := 0
  balance : Evm.U256  := 0
  code    : Evm.Bytes := Evm.Bytes.empty
  deriving Inhabited

namespace Account

/-- A freshly-created, empty account. -/
def empty : Account := {}

/-- Per EIP-161-precursor heuristics (only relevant at later forks):
    an account is "empty" if zero everywhere. Kept here for shared use. -/
def isEmpty (a : Account) : Bool :=
  a.nonce = 0 ∧ a.balance = (0 : Evm.U256) ∧ a.code.size = 0

end Account

end Evm.Frontier
