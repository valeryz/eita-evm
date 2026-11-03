/-
  Evm.Prague.State — world-state delta over Frontier.

  EELS reference: ethereum/forks/prague/state.py.

  Conceptually the Prague world state is Frontier's `accounts +
  storage` plus four post-Frontier additions:

    1. Transient storage (EIP-1153, Cancun): per-account `(slot → value)`
       map that is reset between transactions but persists across call
       frames within a single transaction.
    2. `created_accounts` (EIP-6780, Cancun): the set of addresses that
       were CREATEd within the current transaction; SELFDESTRUCT only
       performs the full account-delete when the target is in this set.
    3. Warm/cold tracking (EIP-2929, Berlin): `accessed_addresses` and
       `accessed_storage_keys`, reset per transaction. Stored here
       rather than in `Environment` so SLOAD/SSTORE/CALL gas dispatch
       can mutate them at the world level.
    4. EIP-2930 / EIP-1559 / EIP-4844 / EIP-7702 access-list and
       authorization-list pre-warming happens by seeding (3).

  For the moment we represent Prague.State as a thin newtype wrapper
  over `Frontier.State` carrying the extra fields. Re-using
  `Frontier.State` lets the Byzantium-shaped processTransaction path
  keep working unmodified for legacy transactions (which is most of
  what mainnet sees at Prague — typed txs are still the minority).

  The `transientStorage`, `createdAccounts`, and access-set fields are
  populated by Prague-fork opcodes; the Byzantium effect interpreter
  doesn't read them, so a legacy tx that flows through it gets the
  same semantics as on Byzantium itself (correct for tx types that
  don't use the new features).
-/

import Evm.BaseTypes
import Evm.Frontier.State

namespace Evm.Prague

/-- Prague world state. Wraps the Frontier state and carries the
    post-Frontier per-account / per-tx scratch maps.

    `inner` holds accounts + persistent storage exactly as Frontier.
    Note Prague accounts conceptually carry the same fields as Frontier
    (nonce, balance, code) — EIP-7702 delegations are stored as the
    23-byte `0xef0100 || delegated_address` prefix written into the
    account's `code` field, so no new account-level field is needed. -/
structure State where
  inner             : Evm.Frontier.State                                := {}
  /-- EIP-1153 transient storage: per-(address, slot) value, cleared
      between transactions. -/
  transientStorage  : List ((Evm.Address × Evm.U256) × Evm.U256)        := []
  /-- EIP-6780 (Cancun) created-in-this-tx set. SELFDESTRUCT only
      really removes an account if it appears here. Cleared at end
      of every transaction. -/
  createdAccounts   : List Evm.Address                                   := []
  /-- EIP-2929 (Berlin) warm addresses. Reset per transaction. -/
  accessedAddresses : List Evm.Address                                   := []
  /-- EIP-2929 (Berlin) warm storage keys. Reset per transaction. -/
  accessedKeys      : List (Evm.Address × Evm.U256)                      := []
  deriving Inhabited

namespace State

def empty : State := {}

/-! ## Frontier compatibility — direct re-exports
    These mirror the `Frontier.State` API so call sites that don't
    care about the Prague additions can use a `Prague.State` as if it
    were a `Frontier.State`. -/

def accountExists (s : State) (a : Evm.Address) : Bool :=
  s.inner.accountExists a

def getAccount (s : State) (a : Evm.Address) : Evm.Frontier.Account :=
  s.inner.getAccount a

def setAccount (s : State) (a : Evm.Address) (acc : Evm.Frontier.Account) : State :=
  { s with inner := s.inner.setAccount a acc }

def deleteAccount (s : State) (a : Evm.Address) : State :=
  { s with inner := s.inner.deleteAccount a }

def touchAccount (s : State) (a : Evm.Address) : State :=
  { s with inner := s.inner.touchAccount a }

def getStorage (s : State) (a : Evm.Address) (slot : Evm.U256) : Evm.U256 :=
  s.inner.getStorage a slot

def setStorage (s : State) (a : Evm.Address) (slot v : Evm.U256) : State :=
  { s with inner := s.inner.setStorage a slot v }

def getBalance (s : State) (a : Evm.Address) : Evm.U256 :=
  s.inner.getBalance a

def addBalance (s : State) (a : Evm.Address) (d : Evm.U256) : State :=
  { s with inner := s.inner.addBalance a d }

def subBalance (s : State) (a : Evm.Address) (d : Evm.U256) : State :=
  { s with inner := s.inner.subBalance a d }

/-! ## Prague additions -/

/-- EIP-1153 TLOAD. -/
def getTransientStorage (s : State) (a : Evm.Address) (slot : Evm.U256) : Evm.U256 :=
  match s.transientStorage.find? (fun (k, _) => k = (a, slot)) with
  | some (_, v) => v
  | none        => 0

/-- EIP-1153 TSTORE. -/
def setTransientStorage (s : State) (a : Evm.Address) (slot v : Evm.U256) : State :=
  let pruned := s.transientStorage.filter (fun (k, _) => k ≠ (a, slot))
  { s with transientStorage :=
      if v = (0 : Evm.U256) then pruned else ((a, slot), v) :: pruned }

/-- EIP-6780 mark: the account was just created in this tx. -/
def markCreated (s : State) (a : Evm.Address) : State :=
  if s.createdAccounts.contains a then s
  else { s with createdAccounts := a :: s.createdAccounts }

/-- EIP-6780 query. -/
def isCreatedThisTx (s : State) (a : Evm.Address) : Bool :=
  s.createdAccounts.contains a

/-- EIP-2929 warm an address. Returns the updated state and whether
    the address was already warm (false = cold, true = warm). -/
def accessAddress (s : State) (a : Evm.Address) : State × Bool :=
  if s.accessedAddresses.contains a then (s, true)
  else ({ s with accessedAddresses := a :: s.accessedAddresses }, false)

/-- EIP-2929 warm a storage key. -/
def accessKey (s : State) (a : Evm.Address) (slot : Evm.U256) : State × Bool :=
  if s.accessedKeys.contains (a, slot) then (s, true)
  else ({ s with accessedKeys := (a, slot) :: s.accessedKeys }, false)

/-- End-of-transaction reset of the per-tx scratch fields. EELS
    `begin_transaction`/`commit_transaction` boundary in
    `ethereum/forks/prague/state.py`. -/
def resetTransactionScratch (s : State) : State :=
  { s with
      transientStorage  := []
      createdAccounts   := []
      accessedAddresses := []
      accessedKeys      := [] }

/-- EIP-7702 delegation designator prefix: `0xef 0x01 0x00`. -/
def delegationPrefix : Evm.Bytes :=
  ByteArray.mk (Array.mk [0xef, 0x01, 0x00])

/-- Check whether `code` is an EIP-7702 delegation designator and, if
    so, return the delegated address.
    Designator format: `0xef 0x01 0x00 || delegated_address` (23 bytes,
    EIP-7702 §"Behavior"). -/
def parseDelegation (code : Evm.Bytes) : Option Evm.Address :=
  if code.size ≠ 23 then none
  else if code.get! 0 ≠ 0xef then none
  else if code.get! 1 ≠ 0x01 then none
  else if code.get! 2 ≠ 0x00 then none
  else
    -- Bytes [3..23) are the 20-byte big-endian delegated address.
    let bs : Evm.Bytes := Id.run do
      let mut out : ByteArray := ByteArray.empty
      for i in [3:23] do
        out := out.push (code.get! i)
      pure out
    some (Evm.Address.ofBytesBE bs)

/-- Write the EIP-7702 designator into `addr`'s account code, with
    the given `delegated` address as the suffix. -/
def setDelegation (s : State) (addr : Evm.Address) (delegated : Evm.Address) : State :=
  let suffix := Evm.Address.toBytesBE delegated
  let designator := delegationPrefix ++ suffix
  let acc := s.getAccount addr
  s.setAccount addr { acc with code := designator }

end State

end Evm.Prague
