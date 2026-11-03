/-
  Evm.Trie — Modified Merkle Patricia Trie.

  EELS reference: ethereum/<fork>/trie.py. The MPT is fork-invariant so
  this module lives at the top of the spec; per-fork code parameterises
  the (key, value) shape but reuses the algorithm here.

  Yellow Paper Appendix D defines the trie structurally:
    - Empty trie:        keccak256(rlp(b'')) = `emptyRoot` below.
    - Leaf node:         [hexPrefix(path, leaf=true), value]
    - Extension node:    [hexPrefix(path, leaf=false), nodeRef(child)]
    - Branch node:       [child_0, …, child_15, value_at_this_level]

  Node-ref rule: a child is embedded inline (as its RLP) when the RLP is
  < 32 bytes, otherwise as `keccak256(rlp(child))`. Within the parent's
  RLP list this is just "an Rlp.Item": the inline form is the child's
  own structured item; the long form is `.bytes hash`.
-/

import Evm.BaseTypes
import Evm.Rlp
import Evm.Crypto.Hash

namespace Evm.Trie

/-! ## Nibble manipulation -/

/-- Decompose a byte string into nibbles (high then low for each byte). -/
def bytesToNibbles (b : Bytes) : List UInt8 := Id.run do
  let mut out : List UInt8 := []
  for i in [0:b.size] do
    let byte := b.get! i
    out := out ++ [byte >>> 4, byte &&& 0x0f]
  pure out

/-- Pack a sequence of nibbles (must be even length) into bytes,
    each byte taking two consecutive nibbles. -/
def packNibbles (ns : List UInt8) : Bytes := Id.run do
  let mut out : Bytes := ByteArray.empty
  let mut rest := ns
  while rest.length ≥ 2 do
    match rest with
    | hi :: lo :: tail =>
      out := out.push ((hi <<< 4) ||| lo)
      rest := tail
    | _ => break
  pure out

/-- "Hex-prefix" / compact encoding of a nibble sequence for a node
    path. First nibble of the output encodes leaf-vs-extension and
    parity; subsequent bytes pack pairs of nibbles. -/
def hexPrefix (path : List UInt8) (isLeaf : Bool) : Bytes :=
  let flag : UInt8 := if isLeaf then 0x20 else 0x00
  let odd  := path.length % 2 = 1
  if odd then
    let first := flag ||| 0x10 ||| (path.headD 0)
    ByteArray.mk #[first] ++ packNibbles (path.tailD [])
  else
    ByteArray.mk #[flag] ++ packNibbles path

/-! ## Patricialise -/

private partial def commonPrefix : List UInt8 → List UInt8 → List UInt8
  | a :: as', b :: bs' => if a = b then a :: commonPrefix as' bs' else []
  | _, _ => []

private partial def listCommonPrefix : List (List UInt8) → List UInt8
  | []                 => []
  | [xs]               => xs
  | xs :: ys :: rest   => listCommonPrefix (commonPrefix xs ys :: rest)

/-- Partition a list of (nibble-key, value) pairs by the first nibble.
    Returns the 16 buckets (with the leading nibble dropped from each
    key) plus a "value at this level" if any key is empty. -/
private def partition16 (items : List (List UInt8 × Bytes)) :
    Array (List (List UInt8 × Bytes)) × Bytes := Id.run do
  let mut buckets : Array (List (List UInt8 × Bytes)) := Array.replicate 16 []
  let mut terminal : Bytes := ByteArray.empty
  for (k, v) in items do
    match k with
    | []        => terminal := v
    | n :: rest =>
      let idx := n.toNat
      buckets := buckets.set! idx ((rest, v) :: buckets[idx]!)
  pure (buckets, terminal)

mutual

/-- Wrap a node as it should appear in its parent: inline if its RLP
    encoding is < 32 bytes, else as a 32-byte keccak hash. -/
partial def nodeRef (node : Evm.Rlp.Item) : Evm.Rlp.Item :=
  let enc := Evm.Rlp.encode node
  if enc.size < 32 then node
  else .bytes (Evm.Crypto.keccak256Bytes enc)

/-- Build the root node for the given (nibble-key, value) pairs. -/
partial def patricialise (items : List (List UInt8 × Bytes)) : Evm.Rlp.Item :=
  match items with
  | [] => .bytes Evm.Bytes.empty
  | [(k, v)] =>
    .list [.bytes (hexPrefix k true), .bytes v]
  | _ =>
    let keys := items.map Prod.fst
    let common := listCommonPrefix keys
    if common.length > 0 then
      let stripped := items.map fun (k, v) => (k.drop common.length, v)
      let sub := patricialise stripped
      .list [.bytes (hexPrefix common false), nodeRef sub]
    else
      let (buckets, terminal) := partition16 items
      let children : List Evm.Rlp.Item := (List.range 16).map fun i =>
        let bucket := buckets[i]!
        if bucket.isEmpty then .bytes Evm.Bytes.empty
        else nodeRef (patricialise bucket)
      .list (children ++ [.bytes terminal])

end

/-! ## Root -/

/-- Hash of the empty trie: `keccak256(rlp(empty bytes)) = keccak256(0x80)`.
    Equals `0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421`. -/
def emptyRootBytes : Bytes :=
  Evm.Crypto.keccak256Bytes (ByteArray.mk #[0x80])

def emptyRoot : Hash32 := Evm.U256.ofBytesBE emptyRootBytes

/-- Compute the trie root for the given (key, value) byte-string pairs.
    Empty input returns `emptyRoot`; otherwise the root is always
    `keccak256(rlp(rootNode))`, regardless of how short rlp(rootNode) is.
    -/
def root (items : List (Bytes × Bytes)) : Hash32 :=
  if items.isEmpty then emptyRoot
  else
    let nibbleItems := items.map fun (k, v) => (bytesToNibbles k, v)
    let rootNode := patricialise nibbleItems
    Evm.U256.ofBytesBE (Evm.Crypto.keccak256Bytes (Evm.Rlp.encode rootNode))

/-- Same as `root` but returning the raw 32 bytes. -/
def rootBytes (items : List (Bytes × Bytes)) : Bytes :=
  if items.isEmpty then emptyRootBytes
  else
    let nibbleItems := items.map fun (k, v) => (bytesToNibbles k, v)
    let rootNode := patricialise nibbleItems
    Evm.Crypto.keccak256Bytes (Evm.Rlp.encode rootNode)

end Evm.Trie
