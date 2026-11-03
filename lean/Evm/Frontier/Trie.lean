/-
  Evm.Frontier.Trie — Merkle Patricia Trie (placeholder).

  EELS reference: ethereum/frontier/trie.py. The MPT is the same data
  structure across all forks; differences live in which keys are stored
  (e.g. account-level fields change). A full implementation is TODO; this
  module currently exposes a key-value pair list and a placeholder root.
-/

import Evm.BaseTypes
import Evm.Crypto.Hash

namespace Evm.Frontier

/-- Trie key: an arbitrary byte string (nibble-decomposition is internal
    to the MPT encoding). -/
abbrev TrieKey := Evm.Bytes

/-- Trie value: an arbitrary RLP-encoded byte string. -/
abbrev TrieValue := Evm.Bytes

/-- A trie. TODO: replace with a real radix-16 Merkle tree. -/
structure Trie where
  default : Option Evm.Bytes := none
  entries : List (TrieKey × TrieValue) := []
  deriving Inhabited

namespace Trie

def empty : Trie := {}

def set (t : Trie) (k : TrieKey) (v : TrieValue) : Trie :=
  { t with entries := (k, v) :: t.entries.filter (fun (k', _) => k' ≠ k) }

def get? (t : Trie) (k : TrieKey) : Option TrieValue :=
  (t.entries.find? (fun (k', _) => k' = k)).map Prod.snd

/-- Compute the Merkle root. Currently a stub; depends on a working
    keccak256 and the full MPT serialisation. -/
def root (_t : Trie) : Evm.Hash32 := Evm.Crypto.keccak256 Evm.Bytes.empty

end Trie

end Evm.Frontier
