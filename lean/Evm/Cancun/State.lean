/-
  Evm.Cancun.State — transient storage (EIP-1153) + created-accounts
  set (EIP-6780) helpers.

  EELS reference: ethereum/forks/cancun/state.py — the `set_transient_storage`
  / `get_transient_storage` pair and the `add_to_created_accounts`
  predicate used by SELFDESTRUCT.

  We store both pieces of state on the existing `Frontier.Vm.Environment`
  record (extended with optional fields, default-empty for pre-Cancun
  forks). This avoids forcing every fork to re-thread its own env type
  through the trampoline.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm

namespace Evm.Cancun.State

open Evm.Frontier.Vm (Environment)

/-! ## EIP-1153 transient storage

    Transient storage is a `(address, slot) → value` map that:
      * lives for the duration of a single transaction,
      * is shared across all frames in that tx (so reentry sees
        the parent's TSTOREs),
      * is *not* reverted by a frame REVERT — clarified in EIP-1153
        version `2024-06-04` (EELS follows this).

    Implementation note: we mirror Frontier.State's storage map
    (list of `((addr, slot), val)`) — O(n) lookup, simple replay. -/

/-- Read transient storage at `(addr, slot)`; 0 if absent. -/
def getTransient (env : Environment) (addr : Evm.Address) (slot : Evm.U256) :
    Evm.U256 :=
  match env.transientStorage.find? (fun (k, _) => k = (addr, slot)) with
  | some (_, v) => v
  | none        => 0

/-- Write transient storage at `(addr, slot)`. Setting to 0 removes
    the entry (mirror of `Frontier.State.setStorage`). -/
def setTransient (env : Environment) (addr : Evm.Address) (slot value : Evm.U256) :
    Environment :=
  let pruned := env.transientStorage.filter (fun (k, _) => k ≠ (addr, slot))
  { env with
      transientStorage :=
        if value = (0 : Evm.U256) then pruned
        else ((addr, slot), value) :: pruned }

/-- Clear transient storage between transactions (EELS does this
    implicitly by allocating a fresh `Environment` per tx; we provide
    an explicit reset for tx-driver code). -/
def clearTransient (env : Environment) : Environment :=
  { env with transientStorage := [] }

/-! ## EIP-6780 created-accounts set

    A *contract* (account with code) created during the current tx is
    eligible for full destruction by SELFDESTRUCT. Accounts that
    pre-existed the tx are not — SELFDESTRUCT just transfers their
    balance to the beneficiary, leaving code/storage in place.

    The set is *not* reset by frame reverts — but obviously a reverted
    frame's CREATEs do not get committed, so the parent never sees
    them in the first place. Practical handling: we add to the set
    at the *successful* CREATE merge point.
-/

/-- Whether `addr` was CREATEd within the current tx. Drives the
    full-destroy branch of EIP-6780 SELFDESTRUCT. -/
def wasCreatedThisTx (env : Environment) (addr : Evm.Address) : Bool :=
  env.createdAccounts.contains addr

/-- Mark `addr` as CREATEd in the current tx. Called at the parent
    frame's CREATE-success resume. -/
def addCreatedAccount (env : Environment) (addr : Evm.Address) : Environment :=
  if env.createdAccounts.contains addr then env
  else { env with createdAccounts := addr :: env.createdAccounts }

/-- Clear the created-accounts set between transactions. -/
def clearCreatedAccounts (env : Environment) : Environment :=
  { env with createdAccounts := [] }

end Evm.Cancun.State
