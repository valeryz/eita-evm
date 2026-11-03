import Evm.CL.Arena

/-! # CL/CodeArena — bounded executable arena for JIT chunks (#259), proved safe

The DoS region JITs thousands of unique throwaway contracts; each goes into its
own `mmap` of executable memory, and on macOS every new executable mapping makes
dyld re-serialize its whole process-image atlas → an O(n²) storm that is ~70 % of
the peak batch (#248, measured via #247). The fix is to `mmap` **one** fixed
RX region and bump/evict chunks within it (ring/LRU): dyld serializes once, the
storm is gone, and threshold=1 / full all-JIT coverage is preserved.

The subtle bug this hides is a lifetime one, the executable twin of
`Evm.CL.Arena`'s escape-safety: when a contract CALLs a not-yet-JIT'd callee, the
**caller's chunk is on the call stack, executing**. If allocating the callee's
chunk evicts/overwrites the caller's chunk, the caller crashes on return. So the
load-bearing invariant is **never overwrite a chunk on the live call stack**.

We model the allocator and prove exactly that: `place` returns a byte range
disjoint from every *pinned* chunk (the ones on the stack) and evicts only
non-pinned chunks. Combined with `Arena.read_write_disjoint`, writing the new
chunk's code leaves every pinned chunk's bytes intact. The CL allocator must
refine this; the only trust surface left is the FFI `mmap`/`memcpy`. -/

namespace Evm.CL.CodeArena
open Evm.CL.Arena

abbrev Hash : Type := Nat

/-- A loaded chunk: its code hash and its `[off, off+len)` byte range in the arena. -/
structure Chunk where
  hash : Hash
  off  : Nat
  len  : Nat
deriving DecidableEq, Repr

/-- The arena: a fixed byte capacity and the currently-live chunks. -/
structure Arena where
  cap  : Nat
  live : List Chunk
deriving Repr

/-- Boolean disjointness, matching `Arena.Disjoint`. -/
def disjointB (o₁ l₁ o₂ l₂ : Nat) : Bool :=
  decide (o₁ + l₁ ≤ o₂) || decide (o₂ + l₂ ≤ o₁)

theorem disjointB_iff (o₁ l₁ o₂ l₂ : Nat) :
    disjointB o₁ l₁ o₂ l₂ = true ↔ Disjoint o₁ l₁ o₂ l₂ := by
  unfold disjointB Disjoint
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]

/-- Place chunk `c` (the bump head's choice of `c.off`), given `pinned` = the
    hashes currently on the call stack. Evict the non-pinned chunks that overlap
    `c`; **refuse** (`none`) if `c` would overflow the region or overlap a PINNED
    chunk (that would corrupt a live frame). Returns the new arena and the evicted
    chunks (whose code-hashes the CL drops from `*jit-cache*`). -/
def place (a : Arena) (c : Chunk) (pinned : Hash → Bool) : Option (Arena × List Chunk) :=
  if c.off + c.len > a.cap then none
  else if (a.live.filter (fun d => ! disjointB c.off c.len d.off d.len)).any
            (fun d => pinned d.hash) then none
  else some ({ a with live := c :: a.live.filter (fun d => disjointB c.off c.len d.off d.len) },
             a.live.filter (fun d => ! disjointB c.off c.len d.off d.len))

/-- **Allocation safety.** If `place` succeeds, the newly written range is disjoint
    from every PINNED live chunk, and nothing pinned was evicted. So a callee's JIT
    never overwrites an executing caller. -/
theorem place_safe {a : Arena} {c : Chunk} {pinned : Hash → Bool}
    {a' : Arena} {ev : List Chunk}
    (h : place a c pinned = some (a', ev)) :
    (∀ d ∈ a.live, pinned d.hash = true → Disjoint c.off c.len d.off d.len) ∧
    (∀ d ∈ ev, pinned d.hash = false) := by
  unfold place at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i hpin
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      have hev : ev = a.live.filter (fun d => ! disjointB c.off c.len d.off d.len) := h.2.symm
      have hpin' : (a.live.filter (fun d => ! disjointB c.off c.len d.off d.len)).any
                     (fun d => pinned d.hash) = false := by
        simpa using hpin
      refine ⟨?_, ?_⟩
      · intro d hd hdp
        cases hb : disjointB c.off c.len d.off d.len with
        | true => exact (disjointB_iff _ _ _ _).mp hb
        | false =>
          exfalso
          have hmem : d ∈ a.live.filter (fun d => ! disjointB c.off c.len d.off d.len) :=
            List.mem_filter.mpr ⟨hd, by simp [hb]⟩
          have hany : (a.live.filter (fun d => ! disjointB c.off c.len d.off d.len)).any
                       (fun d => pinned d.hash) = true :=
            List.any_eq_true.mpr ⟨d, hmem, hdp⟩
          rw [hpin'] at hany; exact Bool.noConfusion hany
      · intro d hd
        rw [hev] at hd
        cases hb : pinned d.hash with
        | false => rfl
        | true =>
          have hany : (a.live.filter (fun d => ! disjointB c.off c.len d.off d.len)).any
                       (fun d => pinned d.hash) = true :=
            List.any_eq_true.mpr ⟨d, hd, hb⟩
          rw [hpin'] at hany; exact Bool.noConfusion hany

/-- **Code preservation** (the safety payoff): writing chunk `c`'s code into the
    backing region leaves every pinned chunk's bytes unchanged — so the executing
    caller still reads its own code. Direct from `place_safe` + `Arena` separation. -/
theorem place_preserves_pinned {a : Arena} {c : Chunk} {pinned : Hash → Bool}
    {a' : Arena} {ev : List Chunk} (r : Region) (data : List Byte)
    (hlen : data.length = c.len)
    (h : place a c pinned = some (a', ev))
    {d : Chunk} (hd : d ∈ a.live) (hp : pinned d.hash = true) :
    read (write r c.off data) d.off d.len = read r d.off d.len := by
  apply read_write_disjoint
  rw [hlen]
  exact (place_safe h).1 d hd hp

end Evm.CL.CodeArena
