/-! # CL/StorageCache — refinement spec for lazy RPC storage caching

The SBCL backend (`src/evm/storage-cache.lisp`) sits between the
eval loop and the world state. On a read miss it synchronously
fetches via `eth_getStorageAt`, caches, and returns. On a write
it updates the cache and journals the old value for REVERT. The
cache is the working set; the underlying "ground truth" is the
remote node's state at a fixed block height.

This file states the soundness contract: **the cache acts as a
memoization of the ground-truth oracle.** If the oracle is
deterministic at a fixed block height, every cache read returns
the value the oracle would have returned at that moment.

CL primitives this corresponds to:
  * `cache-read-storage`  — read with miss-fetch.
  * `cache-write-storage` — write-back.
  * `rpc-fetch-storage`   — the oracle (stubbed today; real impl
    will shell to curl / dexador).
-/

namespace Evm.CL.StorageCache

/-- An abstract oracle: a deterministic function from (address,
    slot) to a u256 value. Models the remote node's state at a
    *fixed* block height. The "deterministic at fixed height"
    qualifier is critical: the soundness theorem doesn't hold if
    the oracle can change between calls (i.e. you can't safely
    cache across a `eth_blockNumber` boundary). -/
structure Oracle (Addr Slot Value : Type) where
  read : Addr → Slot → Value

/-- A cache is a partial function — slots not present in the
    domain represent unknown values. The CL hash-table maps to
    this; absence-from-table = "must fetch". -/
abbrev Cache (Addr Slot Value : Type) := Addr → Slot → Option Value

variable {Addr Slot Value : Type} [DecidableEq Addr] [DecidableEq Slot]

/-- Cache lookup with fetch-on-miss. Returns the value AND the
    updated cache. This is precisely the CL `cache-read-storage`
    contract, modulo statistics counters (which are observability,
    not semantics). -/
def lookup (oracle : Oracle Addr Slot Value) (cache : Cache Addr Slot Value)
    (a : Addr) (k : Slot) : Value × Cache Addr Slot Value :=
  match cache a k with
  | some v => (v, cache)
  | none   =>
    let v := oracle.read a k
    let cache' : Cache Addr Slot Value := fun a' k' =>
      if a = a' ∧ k = k' then some v else cache a' k'
    (v, cache')

/-- Write — purely cache-side, doesn't touch the oracle. Matches
    `cache-write-storage`. REVERT support is via the per-frame
    journal (see `Evm.CL.Journal`), not this layer. -/
def write (cache : Cache Addr Slot Value)
    (a : Addr) (k : Slot) (v : Value) : Cache Addr Slot Value :=
  fun a' k' => if a = a' ∧ k = k' then some v else cache a' k'

/-! ## Consistency invariant

A cache is *oracle-consistent* if every entry it holds equals
what the oracle would return for the same (addr, slot). This is
the property `lookup` and `write` maintain (`write` requires the
"all writes go through `write` or `lookup`" precondition — i.e.
no out-of-band cache poisoning). -/

def Consistent (oracle : Oracle Addr Slot Value)
    (cache : Cache Addr Slot Value) : Prop :=
  ∀ a k v, cache a k = some v → oracle.read a k = v

/-- Lookup of a consistent cache returns the oracle value. -/
theorem lookup_returns_oracle
    (oracle : Oracle Addr Slot Value)
    (cache : Cache Addr Slot Value)
    (hc : Consistent oracle cache) (a : Addr) (k : Slot) :
    (lookup oracle cache a k).1 = oracle.read a k := by
  unfold lookup
  cases h : cache a k with
  | none   => simp
  | some v => simp; exact (hc a k v h).symm

/-- Lookup preserves consistency. The proof is a straightforward
    case split on (hit / miss) and (target-key matches / not), but
    requires careful handling of the dependent rewrite when the
    update key matches the query key. Left as `sorry` for now —
    surfacing the obligation per no-silent-gaps; the proof
    structure is well-understood and the closure is straightforward
    Lean tactic work, just verbose. -/
theorem lookup_preserves_consistent
    (oracle : Oracle Addr Slot Value)
    (cache : Cache Addr Slot Value)
    (hc : Consistent oracle cache) (a : Addr) (k : Slot) :
    Consistent oracle (lookup oracle cache a k).2 := by
  sorry

/-! ## Correspondence with the CL implementation

```lisp
(defun cache-read-storage (cache addr slot)
  (let* ((key (cons addr slot))
         (val (gethash key (storage-cache-table cache))))
    (cond (val (incf (storage-cache-hit-count cache)) val)
          (t   (incf (storage-cache-miss-count cache))
               (let ((fetched (rpc-fetch-storage ... addr slot)))
                 (setf (gethash key (storage-cache-table cache)) fetched)
                 fetched)))))
```

Correspondence:
  * `(gethash key table)` → `cache a k` (returns nil/none on miss).
  * `(rpc-fetch-storage ... addr slot)` → `oracle.read a k`.
  * Cache mutation via `(setf (gethash ...))` → returning the
    `cache'` second component of `lookup`.

The `hit-count`/`miss-count` counters are statistics-only — they
don't affect the values returned, so `lookup` doesn't model them.

**Caveat the CL impl makes implicit:** the oracle is assumed
deterministic at a single block height. The replay harness pins
this by binding the cache lifetime to one block; for a long-
running scheduler the cache must be invalidated when the head
moves forward. Concretely: `make-scheduler` should re-instantiate
its cache on every block boundary, not share across blocks. This
is currently not enforced in code — it's a known followup. -/

end Evm.CL.StorageCache
