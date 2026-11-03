/-
  Evm.Frontier.StateRoot — compute the world-state trie root for a
  given `State`.

  EELS reference: ethereum/frontier/state.py `state_root` and
  ethereum/frontier/trie.py `root`.

  Encoding (Frontier; same through Cancun for the account fields):
    * Account-trie key: `keccak256(address)` (32 bytes).
    * Account-trie value (leaf payload):
        `rlp([nonce, balance, storageRoot, codeHash])`.
      - `nonce`, `balance` use RLP's minimal-big-endian unsigned
        encoding (`0` → empty bytes).
      - `storageRoot` is 32 bytes — recursively, the trie root of
        the account's storage.
      - `codeHash` is `keccak256(code)`. For empty code that is the
        canonical "empty code hash" `c5d24601…`.
    * Storage-trie key: `keccak256(slot.toBE32)`.
    * Storage-trie value: `rlp(value as minimal big-endian)`.
-/

import Evm.BaseTypes
import Evm.Rlp
import Evm.Crypto.Hash
import Evm.Trie
import Evm.Frontier.State
import Std.Data.HashMap

namespace Evm.Frontier

/-- Keccak-256 of the empty byte string — the canonical "code hash"
    of an account with no code. -/
def emptyCodeHashBytes : Evm.Bytes :=
  Evm.Crypto.keccak256Bytes Evm.Bytes.empty

/-- Trie root of `addr`'s storage. Slots holding the value 0 are
    treated as absent (`State.setStorage` already prunes them). -/
def storageRootBytes (state : State) (addr : Evm.Address) : Evm.Bytes :=
  let items := state.storage.filterMap fun ((a, slot), v) =>
    if a = addr then
      some ( Evm.Crypto.keccak256Bytes (Evm.U256.toBytesBE slot)
           , Evm.Rlp.encode (.bytes (Evm.Rlp.natToBytes v.toNat)) )
    else none
  Evm.Trie.rootBytes items

/-- RLP-encoded account payload for the world-state trie. -/
def accountRlp (storageR codeH : Evm.Bytes) (acc : Account) : Evm.Bytes :=
  Evm.Rlp.encode (.list
    [ .bytes (Evm.Rlp.natToBytes acc.nonce)
    , .bytes (Evm.Rlp.natToBytes acc.balance.toNat)
    , .bytes storageR
    , .bytes codeH ])

/-- World-state trie root of `state`.

    Storage is pre-grouped by address in ONE pass (`O(total_storage)`); each
    account's storage root then reads its own slots from the group instead of
    re-scanning all of `state.storage`. The previous per-account
    `storageRootBytes` (a full `state.storage.filterMap` per account) made this
    `O(accounts × total_storage)` — ~300 accounts/s, infeasible past ~100k
    accounts. Output is byte-identical: each account's slot items are kept in
    their original `state.storage` order (the prepend-then-`reverse`), and the
    account list order is unchanged; trie roots are anyway order-independent
    over the (unique) keys. -/
def stateRootBytes (state : State) : Evm.Bytes :=
  let storageByAddr : Std.HashMap Nat (List (Evm.Bytes × Evm.Bytes)) :=
    state.storage.foldl
      (fun m ((a, slot), v) =>
        let item := ( Evm.Crypto.keccak256Bytes (Evm.U256.toBytesBE slot)
                    , Evm.Rlp.encode (.bytes (Evm.Rlp.natToBytes v.toNat)) )
        m.insert a.toNat (item :: m.getD a.toNat []))
      (∅ : Std.HashMap Nat (List (Evm.Bytes × Evm.Bytes)))
  let items := state.accounts.map fun (addr, acc) =>
    let key      := Evm.Crypto.keccak256Bytes (Evm.Address.toBytesBE addr)
    let storageR := Evm.Trie.rootBytes ((storageByAddr.getD addr.toNat []).reverse)
    let codeH    :=
      if acc.code.size = 0 then emptyCodeHashBytes
      else Evm.Crypto.keccak256Bytes acc.code
    (key, accountRlp storageR codeH acc)
  Evm.Trie.rootBytes items

end Evm.Frontier
