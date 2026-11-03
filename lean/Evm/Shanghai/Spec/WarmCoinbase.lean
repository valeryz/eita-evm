/-
  Evm.Shanghai.Spec.WarmCoinbase — EIP-3651 "warm COINBASE".

  EELS reference: `forks/shanghai/fork.py` line 575:
      `access_list_addresses.add(block_env.coinbase)`
  inside `process_transaction`, after the standard EIP-2929 seeds
  (sender, recipient, and the explicit access-list addresses).

  Refines Berlin's per-transaction `accessedAddresses` initialization.
  At Berlin the initial warm set is roughly `{sender, recipient,
  precompiles, accessList}`; at Shanghai the coinbase is added to it
  unconditionally. The intent: many MEV-flavored patterns hot-call
  the coinbase, and pre-EIP-3651 they paid the 2600-gas cold-access
  penalty every time.

  This is a *tx-level* state-machine delta, not an opcode delta. It
  shows up only in the initial value of `Environment.accessedAddresses`
  at the start of `processTransaction`; thereafter the standard
  Berlin warm/cold logic applies unchanged.

  Inheritance: applies unchanged at Cancun and Prague.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Forks

namespace Evm.Shanghai.Spec

open Evm.Frontier.Vm (Environment)

/-! ## Refinement of Berlin's initial warm set

    Berlin / EIP-2929 says: at tx-start the warm set is
        `{sender, recipient, precompiles} ∪ tx.accessList.addresses`.
    Shanghai / EIP-3651 amends this to also include `coinbase`.

    The predicate `IsBerlinInitialAccessSet` (declared in
    `Evm.Berlin.Spec.AccessList`, currently a stub) is the Berlin
    starting point; here we describe the Shanghai delta by an
    equation on the resulting list. -/

/-- An address list "contains the coinbase" iff `coinbase ∈ addrs`.
    Phrased as `List.contains` to match the implementation idiom. -/
def WarmCoinbase (coinbase : Evm.Address) (warmSet : List Evm.Address) : Prop :=
  warmSet.contains coinbase

/-- The Shanghai initial warm-address set is exactly Berlin's seed
    *plus* the block's coinbase. We don't have a Berlin spec module
    to reference yet, so we encode it as a direct equation on the
    `Environment.accessedAddresses` field at tx-entry.

    The spec form is: if `env` is the freshly-built tx environment
    (immediately before opcode execution begins), then
    `env.accessedAddresses` must list `coinbase`. -/
def IsWarmCoinbaseInit (coinbase : Evm.Address) (env : Environment) : Prop :=
  WarmCoinbase coinbase env.accessedAddresses

/-! ## Note on under-specification

    A stronger Shanghai spec would say "Berlin's seed list, with
    `coinbase` appended/inserted". That requires a Berlin
    `IsBerlinInitialAccessSet` predicate to refine, which doesn't
    yet exist in this tree (Berlin's Spec/ is a TODO). Once Berlin
    ships, this file should be updated to:

        IsShanghaiInitialAccessSet env =
          ∃ berlinSet, IsBerlinInitialAccessSet env berlinSet ∧
                       env.accessedAddresses = berlinSet ++ [coinbase]

    For now the weaker "coinbase is present" predicate is the
    refinement-target. The tx level (`Evm.Frontier.Vm.Tx.seedAddrs`)
    seeds `coinbase` into the accessed set from Shanghai. -/

/-! ## Fork-conditional value (iff form)

    EIP-3651 adds the coinbase address to the EIP-2929 warm-seed
    starting at Shanghai. Stated as a single iff:

      `warmCoinbaseAt f = true  ↔  f ≥ Shanghai`.

    The implementation wires this in `Evm.Frontier.Vm.Tx.seedAddrs`
    (`k ≥ 15`). -/

def warmCoinbaseAt (f : Evm.Fork) : Bool := f.atLeast .shanghai

theorem warm_coinbase_iff_shanghai (f : Evm.Fork) :
    warmCoinbaseAt f = true ↔ f.atLeast .shanghai := by
  unfold warmCoinbaseAt; rfl

end Evm.Shanghai.Spec
