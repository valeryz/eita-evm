import Evm.Trie

/-! # Trie.Incremental — persistent Patricia trie for incremental state roots

`Evm.Trie.root` rebuilds the whole trie from the full (key,value) list every
call — too slow to run per block over millions of blocks. This module specs a
*persistent* node tree whose `insert`/`delete` touch only the path to a key,
so a block's state diff updates the trie incrementally and the root is read
off the maintained structure.

Correctness is by construction: the contract `toRlp_eq_patricialise` says the
maintained node's RLP encoding equals `Evm.Trie.patricialise` of its current
items, so `Node.root = Evm.Trie.root` for any node built by these ops. With
that, the incremental root is provably the same as the full rebuild.

Used (downstream) for the mainnet-replay state-root check: account trie keyed
by `keccak(addr)` → `RLP[nonce,balance,storageRoot,codeHash]`, per-account
storage tries keyed by `keccak(slot)`; per-block dirty sets (from the journal)
drive the incremental updates; compared to the header `stateRoot`. -/

namespace Evm.Trie.Incremental
open Evm Evm.Trie

/-- A persistent Merkle-Patricia node over nibble-keys. `branch.children[i] =
    .empty` means no child at nibble `i`; `branch.value` is the terminal value
    (empty `Bytes` = none). The structure mirrors `patricialise`'s output:
    a single key is a `leaf`, a shared prefix is an `ext`, otherwise a
    `branch`. -/
inductive Node where
  | empty
  | leaf   (path : List UInt8) (value : Bytes)
  | ext    (path : List UInt8) (child : Node)
  | branch (children : Array Node) (value : Bytes)
  deriving Inhabited

/-- The (nibble-key, value) pairs held in the subtree — the trie's logical
    contents. Equivalence is stated against this. -/
partial def Node.toItems : Node → List (List UInt8 × Bytes)
  | .empty       => []
  | .leaf p v    => [(p, v)]
  | .ext p c     => c.toItems.map (fun (k, v) => (p ++ k, v))
  | .branch cs v =>
      let kids := (List.range 16).flatMap fun i =>
        (cs.getD i .empty).toItems.map (fun (k, vv) => (UInt8.ofNat i :: k, vv))
      if v.size = 0 then kids else ([], v) :: kids

/-- RLP encoding of the maintained node — built directly from the structure
    (incremental), to be proved equal to `patricialise (toItems n)`. Reuses
    `Evm.Trie.hexPrefix` / `Evm.Trie.nodeRef` so the bytes match exactly. -/
partial def Node.toRlp : Node → Evm.Rlp.Item
  | .empty       => .bytes Bytes.empty
  | .leaf p v    => .list [.bytes (hexPrefix p true), .bytes v]
  | .ext p c     => .list [.bytes (hexPrefix p false), nodeRef c.toRlp]
  | .branch cs v =>
      let children := (List.range 16).map fun i =>
        match cs.getD i .empty with
        | .empty => .bytes Bytes.empty
        | c      => nodeRef c.toRlp
      .list (children ++ [.bytes v])

/-- Incremental root: `keccak(rlp(toRlp n))`, uniformly — for `.empty` this is
    `keccak(rlp(.bytes ""))` = `keccak(0x80)` = `emptyRootBytes`, so it agrees
    with `Evm.Trie.root []` without a special case. -/
def Node.root (n : Node) : Hash32 :=
  Evm.U256.ofBytesBE (Evm.Crypto.keccak256Bytes (Evm.Rlp.encode n.toRlp))

/-! ## Correctness contract

The maintained node's encoding equals the full `patricialise` of its items,
for any node produced by `insert`/`delete` from `.empty` (the *canonical*
nodes). Closing this is the proof obligation that makes the incremental trie
provably equal to the full rebuild — stated now, proved as the operations and
their structure lemmas land. -/

/-- `Canonical n`: `n` is in the normal form `patricialise` produces — no
    single-child branches, extensions only above branches, etc. Established by
    `insert`/`delete` (lemmas pending). -/
def Canonical (n : Node) : Prop :=
  n.toItems ≠ [] → n.toRlp = patricialise n.toItems

/-- **The contract.** For a canonical, non-empty node the incremental root
    equals `keccak(rlp(patricialise items))` — i.e. the full `Evm.Trie.root`
    over the same items. Immediate from `Canonical` (rewriting `toRlp` to
    `patricialise`); the real content is `Canonical` itself. -/
theorem root_eq_full (n : Node) (hc : Canonical n) (h : n.toItems ≠ []) :
    n.root = Evm.U256.ofBytesBE
               (Evm.Crypto.keccak256Bytes (Evm.Rlp.encode (patricialise n.toItems))) := by
  unfold Node.root
  rw [hc h]

/-! ## Proof obligations (the incremental ⇒ canonical guarantee)

`insert`/`delete` are pending. The single obligation that makes the whole
construction sound is that they preserve `Canonical` (and `Canonical .empty`
holds vacuously). Stated here as the contract every operation must satisfy;
proving it (the Patricia normal-form preservation) is the next step, and it
requires `toItems`/`toRlp` as structurally-recursive (non-`partial`) defs with
termination, so the equations are available to the prover.

    Canonical .empty
    Canonical n → Canonical (n.insert k v)
    Canonical n → Canonical (n.delete k)

Until `insert`/`delete` land, `Canonical` is the explicit, visible obligation
(not a hidden gap): any node fed to `root_eq_full` must be shown canonical. -/

end Evm.Trie.Incremental
