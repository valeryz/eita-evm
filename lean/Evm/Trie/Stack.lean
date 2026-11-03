import Evm.Trie

/-! # Trie.Stack — the streaming (stack) build of a Patricia trie over sorted leaves

`Evm.Trie.patricialise` is a recursion over the whole item list: the reference, but it
holds every key at once. `src/state/root.lisp` computes state roots over hundreds
of millions of leaves in bounded memory with the build specified here: leaves arrive in
ascending key order and only the *open rightmost path* of the trie is kept — a stack of
at most `keyLength` frames, each a branch under construction (16 finished child
references and the extension above it). A node is encoded and hashed (`nodeRef`) the
moment its key range closes, i.e. when a key arrives that does not share its prefix.
This is geth's StackTrie, written against our `patricialise`.

The Lisp mirrors these definitions one to one (`st-push` = `St.push`, `settle` is its
inner loop, `st-finish` = `St.finish`, `Frame.close` = `st-close`), with nibble vectors
and an offset in place of lists; `tests/snapshot-root.lisp` checks it against
`trie-root` on random key sets.

**Statement.** For distinct keys of one length, pushed in ascending order, the stack
build yields the very RLP item `patricialise` returns (`build_eq_patricialise`), hence
the same root (`rootBytes_eq`); and the root over keys with two or more distinct first
nibbles is the branch of the per-nibble subtries built at depth 1 (`build_split`) — the
parallel path of the checker. These are stated, not proved: `patricialise` is a
`partial def`, opaque to the kernel, so nothing about it can be unfolded until the trie
spec is made total (the same prerequisite `Trie/Incremental.lean` records for
`Canonical`). The `sorry`s below are that visible gap. -/

namespace Evm.Trie.Stack
open Evm Evm.Trie

/-- `.bytes ""`: an absent child, and the empty value of every branch (fixed-length keys
    never end at a branch). -/
def emptyItem : Rlp.Item := .bytes Bytes.empty

/-- A branch under construction at nibble `depth`: its finished children, as `nodeRef`
    leaves them, and above it an extension over nibbles `[extFrom, depth)`, which every
    key below the frame shares. The frame above it (if any) has `depth = extFrom - 1`. -/
structure Frame where
  depth    : Nat
  extFrom  : Nat
  children : Array Rlp.Item

def Frame.open (depth extFrom : Nat) : Frame := ⟨depth, extFrom, Array.replicate 16 emptyItem⟩

def Frame.set (f : Frame) (nib : UInt8) (child : Rlp.Item) : Frame :=
  { f with children := f.children.set! nib.toNat child }

/-- Nibble `d` of a key. -/
def nib (k : List UInt8) (d : Nat) : UInt8 := k.getD d 0

/-- The leaf of key `k` whose path begins at nibble `start`. -/
def leafItem (k : List UInt8) (start : Nat) (v : Bytes) : Rlp.Item :=
  .list [.bytes (hexPrefix (k.drop start) true), .bytes v]

/-- The frame's node once its key range is closed: its branch, under an extension over
    nibbles `[start, depth)` of `k` — any key of the frame — when `start < depth`. -/
def Frame.close (f : Frame) (k : List UInt8) (start : Nat) : Rlp.Item :=
  let branch : Rlp.Item := .list (f.children.toList ++ [emptyItem])
  if start < f.depth then
    .list [.bytes (hexPrefix ((k.drop start).take (f.depth - start)) false), nodeRef branch]
  else branch

/-- The pending leaf — the last key pushed, finished only when the next key shows where
    its path ends — placed as a child of `f`. -/
def place (f : Frame) (pend : Option (List UInt8 × Bytes)) : Frame :=
  match pend with
  | none        => f
  | some (k, v) => f.set (nib k f.depth) (nodeRef (leafItem k (f.depth + 1) v))

/-- Length of the longest common prefix. -/
def lcp : List UInt8 → List UInt8 → Nat
  | a :: as, b :: bs => if a = b then lcp as bs + 1 else 0
  | _, _ => 0

/-- The build state: the path's start depth, the pending leaf, and the open frames (top
    first). `base = 0` builds a whole trie; `base = 1` the subtrie of one first nibble. -/
structure St where
  base   : Nat
  prev   : Option (List UInt8 × Bytes)
  frames : List Frame

def St.empty (base : Nat) : St := ⟨base, none, []⟩

/-- A new key splits from the previous key `p` at nibble `l` (their common prefix ends
    there). Frames deeper than `l` are complete: each is closed into its node and becomes a
    child of the frame below, or — when the split falls inside its extension — of a new
    branch at `l` that takes its place. The pending leaf `pend` (of `p`) is finished into
    the first frame that takes it. The new key becomes pending afterwards (`St.push`). -/
def settle (p : List UInt8) (pend : Option (List UInt8 × Bytes)) (l base : Nat) :
    List Frame → List Frame
  | [] =>                                      -- two keys so far: they split at l
    match pend with
    | some _ => [place (Frame.open l base) pend]
    | none   => []
  | top :: rest =>
    if l > top.depth then                      -- the new key goes under the pending leaf
      place (Frame.open l (top.depth + 1)) pend :: top :: rest
    else if l = top.depth then                 -- a new child of top
      place top pend :: rest
    else                                       -- l is above top: top is complete
      let top  := place top pend
      let node := top.close p (max top.extFrom (l + 1))
      if l ≥ top.extFrom then                  -- the split is inside top's extension
        (Frame.open l top.extFrom).set (nib p l) (nodeRef node) :: rest
      else
        match rest with
        | below :: rest' =>
          settle p none l base (below.set (nib p below.depth) (nodeRef node) :: rest')
        | [] => []                             -- unreachable: l ≥ base = extFrom of the bottom frame
termination_by fs => fs.length

def St.push (st : St) (k : List UInt8) (v : Bytes) : St :=
  match st.prev with
  | none         => { st with prev := some (k, v) }
  | some (p, pv) =>
    let l := st.base + lcp (p.drop st.base) (k.drop st.base)
    { st with prev := some (k, v), frames := settle p (some (p, pv)) l st.base st.frames }

/-- No more keys: close the frames from the top; the bottom one's node is the root. -/
def finishFrames (p : List UInt8) : List Frame → Option Rlp.Item
  | []                 => none
  | [f]                => some (f.close p f.extFrom)
  | f :: below :: rest =>
    finishFrames p (below.set (nib p below.depth) (nodeRef (f.close p f.extFrom)) :: rest)
termination_by fs => fs.length

def St.finish (st : St) : Option Rlp.Item :=
  match st.prev, st.frames with
  | none, _               => none
  | some (p, v), []       => some (leafItem p st.base v)
  | some (p, v), top :: rest => finishFrames p (place top (some (p, v)) :: rest)

/-- The streaming build over `items` in the order given: the root node's item, `none`
    when there are no items. -/
def build (base : Nat) (items : List (List UInt8 × Bytes)) : Option Rlp.Item :=
  (items.foldl (fun st kv => st.push kv.1 kv.2) (St.empty base)).finish

/-- `Trie.rootBytes` through the streaming build. -/
def rootBytes (items : List (Bytes × Bytes)) : Bytes :=
  match build 0 (items.map fun kv => (bytesToNibbles kv.1, kv.2)) with
  | none      => emptyRootBytes
  | some node => Evm.Crypto.keccak256Bytes (Evm.Rlp.encode node)

/-! ## The statements -/

/-- Distinct keys of one length `n`, in ascending (lexicographic) order, all beyond `base`
    sharing their first `base` nibbles (`base = 0`: no condition). -/
def SortedKeys (base n : Nat) (items : List (List UInt8 × Bytes)) : Prop :=
  (∀ kv ∈ items, kv.1.length = n) ∧
  items.Pairwise (fun a b => a.1 < b.1) ∧
  (∀ a ∈ items, ∀ b ∈ items, a.1.take base = b.1.take base)

/-- **The stack build is `patricialise`.** -/
theorem build_eq_patricialise (items : List (List UInt8 × Bytes)) (n : Nat)
    (h : SortedKeys 0 n items) (hne : items ≠ []) :
    build 0 items = some (patricialise items) := by
  sorry

/-- The checker's root equals the spec's, for 32-byte keys in ascending order. -/
theorem rootBytes_eq (items : List (Bytes × Bytes))
    (hlen : ∀ kv ∈ items, kv.1.size = 32)
    (hsorted : items.Pairwise (fun a b => a.1.toList < b.1.toList)) :
    rootBytes items = Evm.Trie.rootBytes items := by
  sorry

/-- **The parallel path.** With two or more distinct first nibbles the root is a branch
    whose child `i` is the subtrie, built at depth 1, of the keys starting with `i`. -/
theorem build_split (items : List (List UInt8 × Bytes)) (n : Nat)
    (h : SortedKeys 0 n items)
    (hsplit : ∃ a ∈ items, ∃ b ∈ items, nib a.1 0 ≠ nib b.1 0) :
    build 0 items =
      some (.list ((List.range 16).map (fun i =>
        match build 1 (items.filter fun kv => nib kv.1 0 = UInt8.ofNat i) with
        | none      => emptyItem
        | some node => nodeRef node) ++ [emptyItem])) := by
  sorry

/-! ## Executable checks

Shapes whose node encodings stay under 32 bytes, so `nodeRef` never hashes and the build
evaluates here (keccak is an `extern` with no interpreter implementation): one branch,
bare or under an extension. Every deeper shape — a split inside an extension, several
frames closing at once, million-leaf tries — is what `tests/snapshot-root.lisp`
checks against `trie-root`. `#guard` fails the build if an item differs from
`patricialise`'s. -/

private partial def itemEq : Rlp.Item → Rlp.Item → Bool
  | .bytes a, .bytes b => a == b
  | .list xs, .list ys => xs.length == ys.length && (xs.zip ys).all fun (x, y) => itemEq x y
  | _, _ => false

private def ex (ks : List (List UInt8)) : List (List UInt8 × Bytes) :=
  ks.map fun k => (k, ByteArray.mk #[k.foldl (· + ·) 7])

private def agrees (ks : List (List UInt8)) : Bool :=
  match build 0 (ex ks) with
  | some node => itemEq node (patricialise (ex ks))
  | none => false

#guard agrees [[1, 2, 3, 4]]                                    -- a leaf
#guard agrees [[1, 2, 3, 4], [1, 2, 3, 5]]                      -- extension over a branch
#guard agrees [[1, 2, 3, 4], [2, 2, 3, 5]]                      -- branch at the root
#guard agrees [[1, 2, 3, 4], [1, 2, 3, 5], [1, 2, 3, 9]]        -- three siblings
#guard (build 0 (ex [])).isNone

end Evm.Trie.Stack
