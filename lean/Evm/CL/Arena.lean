/-! # CL/Arena — provably-safe call-frame arena allocation (#250 / #248)

The replay's per-sub-call structs (`sub_state` 544 B, `sub_arena` 72 B, calldata,
the callbacks vtable) are `foreign-alloc`'d and freed on every CALL/CREATE. In the
2016-DoS region that allocation prologue — CFFI `parse-type` + `malloc` +
`:initial-element` zeroing — is ~70 % of execution (sb-sprof, #248), not the EVM.

The fix is to bump-allocate those structs from a flat per-depth **arena** instead.
The hazard that has bitten this twice before
(`feedback_arena_output_ptr_lifetime`, `feedback_arena_depth_off_by_one`) is the
**escape bug**: a child frame's `output` / the caller's `returnData` is a *slice*
into the arena; if the caller reads it *after* the region is reused by a later
sub-call, it reads clobbered bytes — a silent, gas-invisible state corruption.

This module models the arena the same way `Evm.CL.AsmCore` models handlers: one
term, two interpretations, proved equal. The spec view stores `returnData` as a
value `Bytes` (exactly `returnData := subFinal.output` in `…/Vm/Effect.lean`); the
arena view stores it as a `(off, len)` slice of a flat region. Their agreement is
a **separation theorem** (`read` of a region is unchanged by a `write` to a
disjoint region). The discipline that makes the arena correct — *copy `output`
into a buffer disjoint from every future frame's scratch before reuse* — is then
forced: drop it and `arenaReturnData ≠ specReturnData` is provable
(`alias_is_wrong`). So the escape bug is not "audited away", it's ruled out by the
refinement that the emitted code must satisfy. -/

namespace Evm.CL.Arena

abbrev Byte : Type := UInt8

/-- A flat backing region as a total byte map (the `foreign-alloc`'d buffer; the
    bump arena lives inside it). Total ⇒ no partiality to reason about; reads
    outside written ranges return the prior contents (0 after a scrub). -/
abbrev Region : Type := Nat → Byte

/-- Write `data` into `[off, off + data.length)`; bytes elsewhere are untouched. -/
def write (r : Region) (off : Nat) (data : List Byte) : Region :=
  fun i => if off ≤ i ∧ i < off + data.length then data.getD (i - off) 0 else r i

/-- Read `len` bytes starting at `off` (RETURNDATACOPY / the call-output read). -/
def read (r : Region) (off len : Nat) : List Byte :=
  (List.range len).map (fun k => r (off + k))

/-- Two ranges are disjoint. -/
def Disjoint (o₁ l₁ o₂ l₂ : Nat) : Prop := o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁

/-- **Separation.** A write to a range disjoint from `[off, off+len)` leaves the
    read of `[off, off+len)` unchanged. This is the whole safety argument: a
    later sub-call writes only inside its own scratch, so a `returnData` copy
    held in a disjoint buffer survives it. -/
theorem read_write_disjoint
    (r : Region) (wo : Nat) (data : List Byte) (off len : Nat)
    (h : Disjoint wo data.length off len) :
    read (write r wo data) off len = read r off len := by
  unfold read write
  apply List.map_congr_left
  intro k hk
  have hk' : k < len := by simpa [List.mem_range] using hk
  have : ¬ (wo ≤ off + k ∧ off + k < wo + data.length) := by
    rcases h with h | h
    · -- wo + |data| ≤ off ≤ off+k  ⇒  off+k ≥ wo+|data|, so the upper bound fails
      intro hc; omega
    · -- off + len ≤ wo ≤ off+k  ⇒  but k < len ⇒ off+k < off+len ≤ wo, lower bound fails
      intro hc; omega
  simp [this]

/-! ## The call protocol: one term, two interpretations

A frame returns an `output : List Byte`. The caller observes `returnData`, then
may issue a *second* sub-call whose scratch reuses the same region base, then
read the *first* `returnData` again (RETURNDATACOPY after another CALL is legal
until the next call overwrites it — and that "until" is exactly the bug). -/

/-- Abstract trace of what a caller does after a sub-call returns `out`: it then
    runs a later sub-call that writes `next` into the shared scratch at `base`. -/
structure CallTrace where
  base   : Nat            -- shared frame-scratch base reused by every sub-call
  out    : List Byte      -- first child's output
  next   : List Byte      -- second child's scratch write (reuses `base`)
  retOff : Nat            -- where the impl parked `returnData` (slice offset)

/-- **Spec** (value semantics): `returnData` is the first child's `out`, full
    stop — a later call cannot change a value already copied. -/
def specReturnData (t : CallTrace) : List Byte := t.out

/-- **Arena, copy-out** (correct impl): on return, copy `out` into a buffer at
    `retOff` chosen **disjoint** from every future scratch `[base, …)`. -/
def arenaReturnData (r : Region) (t : CallTrace) : List Byte :=
  let r₁ := write r t.retOff t.out                  -- copy out
  let r₂ := write r₁ t.base t.next                   -- later sub-call reuses scratch
  read r₂ t.retOff t.out.length

/-- **Arena, aliasing** (the bug): `returnData` slice points *into* the scratch
    (`retOff = base`); the later sub-call's write clobbers it. -/
def arenaReturnDataAlias (r : Region) (t : CallTrace) : List Byte :=
  let r₁ := write r t.base t.out                     -- output lives in the scratch
  let r₂ := write r₁ t.base t.next                    -- later sub-call overwrites it
  read r₂ t.base t.out.length

/-- **Refinement.** With copy-out into a disjoint buffer, the arena's
    `returnData` equals the spec's value `returnData`, for any region and any
    later sub-call — escape-safe by construction. -/
theorem arena_refines_spec
    (r : Region) (t : CallTrace)
    (hdisj : Disjoint t.base t.next.length t.retOff t.out.length)
    -- the copied-out bytes actually land where we read them:
    (hcopy : read (write r t.retOff t.out) t.retOff t.out.length = t.out) :
    arenaReturnData r t = specReturnData t := by
  unfold arenaReturnData specReturnData
  -- the later scratch write is disjoint from the returnData buffer
  rw [read_write_disjoint _ _ _ _ _ (by
        unfold Disjoint at *; omega)]
  exact hcopy

/-- A clean instance of `hcopy`: writing `out` to a buffer and reading exactly
    `out.length` bytes back returns `out` (a fresh, big-enough buffer). -/
theorem read_write_self (r : Region) (off : Nat) (data : List Byte) :
    read (write r off data) off data.length = data := by
  unfold read write
  have : (List.range data.length).map
            (fun k => if off ≤ off + k ∧ off + k < off + data.length
                      then data.getD ((off + k) - off) 0 else r (off + k))
         = data := by
    have hlen : (List.range data.length).length = data.length := by simp
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      have hn : n < data.length := by simpa using h₂
      simp [Nat.le_add_right, hn, List.getD]
  simpa using this

/-- **The escape bug is real**: the aliasing impl disagrees with the spec on a
    concrete trace (first output `[1]`, later sub-call writes `[2]` over the same
    scratch). So a refinement proof *forces* copy-out — the bug is unrepresentable
    as a refinement, not merely discouraged. -/
theorem alias_is_wrong :
    ∃ (r : Region) (t : CallTrace),
      arenaReturnDataAlias r t ≠ specReturnData t := by
  refine ⟨(fun _ => 0), ⟨0, [1], [2], 0⟩, ?_⟩
  decide

end Evm.CL.Arena
