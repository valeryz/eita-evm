/-
  Evm.Optimism.Replay.Prestate — parse `debug_traceBlockByNumber`'s
  `prestateTracer` output and reconstruct a block's pre-state.

  Tracer output shape (default mode — no `diffMode`):
    result : List
              (per-tx) result : Object
                (per-account-touched) addr : Object
                  balance : hex string (wei)
                  nonce   : decimal number
                  code    : hex string (may be empty)
                  storage : Object (slot-hex → value-hex)

  Each per-tx `result` lists the accounts that THAT tx touched, with
  their values JUST BEFORE the tx ran (reflecting prior-tx effects
  within the block).

  To rebuild the block's PRE-state (state at the parent block's
  height), we union all per-tx maps but take each account's value
  from the EARLIEST tx that touched it — i.e. the value AS OF
  block N-1, which is what we want for replay.
-/

import Lean.Data.Json
import Evm.BaseTypes
import Evm.Frontier.State
import Evm.Optimism.Replay.Parse

namespace Evm.Optimism.Replay.Prestate

open Lean (Json)
open Evm.Frontier (State Account)
open Evm.Optimism.Replay.Parse (hexToNat hexToBytes hexToU256 hexToAddress)

/-- Decode a single account entry from the tracer JSON. Missing
    fields default to empty / zero. -/
private def parseAccount (j : Json) : Except String Account := do
  let balance : Evm.U256 :=
    match j.getObjVal? "balance" with
    | .ok (.str s) => hexToU256 s
    | _ => 0
  let nonce : Nat :=
    match j.getObjVal? "nonce" with
    | .ok (.num n) => n.toFloat.toUInt64.toNat   -- Nat-from-JSON
    | .ok (.str s) => hexToNat s
    | _ => 0
  let code : Evm.Bytes :=
    match j.getObjVal? "code" with
    | .ok (.str s) => (hexToBytes s).getD ByteArray.empty
    | _ => ByteArray.empty
  return { balance := balance, nonce := nonce, code := code }

/-- The prestate-tracer's per-tx result is an object whose KEYS are
    account addresses (as hex strings). Decode the whole object into
    a list of `(Address, Account, List (slot, value))` tuples. -/
private def parseTxResult (j : Json) :
    Except String (List (Evm.Address × Account × List (Evm.U256 × Evm.U256))) :=
  match j with
  | .obj entries =>
    entries.toArray.toList.mapM fun ⟨addrStr, accJ⟩ => do
      let addr := hexToAddress addrStr
      let acc ← parseAccount accJ
      let slots : List (Evm.U256 × Evm.U256) :=
        match accJ.getObjVal? "storage" with
        | .ok (.obj storage) =>
          storage.toArray.toList.map fun ⟨k, v⟩ =>
            (hexToU256 k,
             match v with | .str s => hexToU256 s | _ => 0)
        | _ => []
      return (addr, acc, slots)
  | _ => .error "tx result is not an object"

/-- Top-level parser: takes the JSON returned by
    `debug_traceBlockByNumber` and returns the block's pre-state. -/
def parseBlockPrestate (responseJson : Json) : Except String State := do
  let result ← responseJson.getObjVal? "result"
  let arr ← result.getArr?
  -- Each tx's result. Some shapes nest under `result`, some don't —
  -- handle both.
  let perTx ← arr.toList.mapM fun txEntry => do
    let inner ←
      match txEntry.getObjVal? "result" with
      | .ok r => .ok r
      | .error _ => .ok txEntry
    parseTxResult inner
  -- Union by EARLIEST occurrence, AT THE (account, slot) GRANULARITY.
  -- Account fields (balance/nonce/code) come from the first tx that
  -- touches the account; each individual storage slot comes from the
  -- first tx that touches THAT SLOT — which may be a different tx
  -- (a contract can be touched by tx N for slot A and by later tx
  -- M > N for slot B, and we need both slot values to reconstruct
  -- the block-pre-state). Caught by debugging block 0x4a0000 tx 4
  -- where slot 0x6c20…6312 of 0xc4e4 was missing from our state
  -- because tx 1 had touched the account (different slots) before
  -- tx 4 added this slot.
  let mut state := Evm.Frontier.State.empty
  let mut seenAccounts : List Evm.Address := []
  let mut seenSlots : List (Evm.Address × Evm.U256) := []
  for txAccounts in perTx do
    for (addr, acc, slots) in txAccounts do
      if ¬ seenAccounts.contains addr then
        seenAccounts := seenAccounts ++ [addr]
        state := state.setAccount addr acc
      for (slot, val) in slots do
        if ¬ seenSlots.contains (addr, slot) then
          seenSlots := seenSlots ++ [(addr, slot)]
          state := { state with
            storage := state.storage ++ [((addr, slot), val)] }
  return state

end Evm.Optimism.Replay.Prestate
