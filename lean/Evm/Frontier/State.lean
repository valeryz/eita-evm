/-
  Evm.Frontier.State — world state.

  EELS reference: ethereum/frontier/state.py. The state holds the mapping
  from addresses to accounts, plus per-account storage. Frontier has no
  notion of transient storage, access lists, or warm/cold accounting —
  those arrive at Cancun, Berlin, and Berlin respectively.

  Storage and accounts are tracked separately in EELS to support cheap
  snapshotting (`begin_transaction` / `commit_transaction`). Here we
  expose plain getters/setters; a snapshot stack will be added when CALL
  reverts need to roll back uncommitted changes.
-/

import Evm.BaseTypes
import Evm.Frontier.ForkTypes

namespace Evm.Frontier

/-- The world state: accounts and their storage. Lookups for absent
    addresses return the empty account; absent storage slots return 0. -/
structure State where
  accounts : List (Evm.Address × Account) := []
  /-- `(address, slot) → value`. -/
  storage  : List ((Evm.Address × Evm.U256) × Evm.U256) := []
  deriving Inhabited

namespace State

def empty : State := {}

/-- Whether `addr` is present in the state map (as opposed to merely
    being defaulted to an empty account on lookup). The Yellow Paper /
    EELS Frontier rule for the `NEW_ACCOUNT` (25000) CALL charge is
    based on this, not on whether the account's fields are zero. -/
def accountExists (s : State) (addr : Evm.Address) : Bool :=
  (s.accounts.find? (fun (a, _) => a = addr)).isSome

/-- Account at `addr`, or the empty account if absent. -/
def getAccount (s : State) (addr : Evm.Address) : Account :=
  match s.accounts.find? (fun (a, _) => a = addr) with
  | some (_, a) => a
  | none        => Account.empty

/-- Set the account at `addr`. -/
def setAccount (s : State) (addr : Evm.Address) (acc : Account) : State :=
  { s with
      accounts := (addr, acc) ::
        s.accounts.filter (fun (a, _) => a ≠ addr) }

/-- Remove `addr` from state entirely — both the account and all its
    storage entries. Used by the end-of-tx SELFDESTRUCT sweep, which
    must produce a state where `accountExists addr = false` (so a later
    call into the same address re-triggers the `NEW_ACCOUNT` cost). -/
def deleteAccount (s : State) (addr : Evm.Address) : State :=
  { s with
      accounts := s.accounts.filter (fun (a, _) => a ≠ addr),
      storage  := s.storage.filter (fun ((a, _), _) => a ≠ addr) }

/-- EELS `destroy_storage`: the whole storage of `addr` goes (the account stays). -/
def destroyStorage (s : State) (addr : Evm.Address) : State :=
  { s with storage := s.storage.filter (fun ((a, _), _) => a ≠ addr) }

/-- Bring `addr` into the state map as an empty account if it isn't
    already there. No-op if it is.

    EELS reference: `touch_account` in
    `src/ethereum/forks/frontier/state_tracker.py`:
        if not account_exists(tx_state, address):
            set_account(tx_state, address, EMPTY_ACCOUNT)

    Called from EELS `process_message` *unconditionally* before any
    value transfer — so every CALL (including value=0 calls to a
    non-existent address) brings the target into the trie as an
    empty account. Pre-EIP-161 Frontier behaviour; EIP-158 / -161
    will later prune empty accounts touched during execution. -/
def touchAccount (s : State) (addr : Evm.Address) : State :=
  if s.accountExists addr then s
  else s.setAccount addr Account.empty

/-- Storage at `(addr, slot)`, or 0 if absent. -/
def getStorage (s : State) (addr : Evm.Address) (slot : Evm.U256) : Evm.U256 :=
  match s.storage.find? (fun (k, _) => k = (addr, slot)) with
  | some (_, v) => v
  | none        => 0

/-- Set storage at `(addr, slot)`. Setting to 0 removes the entry to keep
    later root computations consistent with the "empty trie" semantics. -/
def setStorage (s : State) (addr : Evm.Address) (slot value : Evm.U256) : State :=
  let pruned := s.storage.filter (fun (k, _) => k ≠ (addr, slot))
  { s with
      storage := if value = (0 : Evm.U256) then pruned else ((addr, slot), value) :: pruned }

/-- Account balance at `addr`. -/
def getBalance (s : State) (addr : Evm.Address) : Evm.U256 :=
  (s.getAccount addr).balance

/-- Increment / decrement balance, wrapping per `U256`. (Callers should
    enforce no-overflow / no-underflow at the transaction level.) -/
def addBalance (s : State) (addr : Evm.Address) (delta : Evm.U256) : State :=
  let a := s.getAccount addr
  s.setAccount addr { a with balance := a.balance + delta }

def subBalance (s : State) (addr : Evm.Address) (delta : Evm.U256) : State :=
  let a := s.getAccount addr
  s.setAccount addr { a with balance := a.balance - delta }

end State

end Evm.Frontier
