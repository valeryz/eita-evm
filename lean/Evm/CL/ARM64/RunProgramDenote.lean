import Evm.CL.GasEmit

/-
  Evm.CL.ARM64.RunProgramDenote — what `_eita_execute_program` computes, and
  where it deliberately differs from `IR.executeProgram`.

  Stage 1 of #238. `ARM64.RunProgram` emits the chunk-dispatch trampoline as 26
  lines of asm, "case-for-case against the spec" per its header. Writing the
  loop down as a function found that the cases are NOT in the same order, and
  the difference is observable:

      spec (IR.Execute.executeProgram)        asm (Lrp_loop)
      ──────────────────────────────────      ──────────────────────────────
      fuel = 0            → .outOfGas         halted              → return 0
      lookup pc = none    → .invalidJumpDest  fuel = 0            → return 2
      execute, then halted → .ok              lookup pc = none    → return 1
      otherwise           → loop              execute, then loop

  The asm tests `halted` at the TOP of the loop, so on the first iteration it
  tests the ENTRY state — which the spec never does — and on later iterations it
  is the spec's post-execute test. The two therefore agree for every
  non-halted entry state, and disagree on exactly one input: an already-halted
  entry with no fuel, where the asm returns 0 (ok) and the spec says
  `.outOfGas`. Both facts are theorems below.

  That case is unreachable through the host — `run-jit-frame` passes
  `gas_left + 1 ≥ 1` and never enters on a halted frame — and the asm's
  behaviour is the more useful one (an already-finished frame is not out of
  gas). It is recorded here rather than left as the header's "case-for-case",
  which is what it is not.

  ## The dispatch table

  The asm does not scan the `(pc, fn)` manifest: it indexes a table by pc
  (`fn[pc]`, 0 = no chunk, a pc past the end = no chunk), which the host
  loader builds from the manifest (`build`, emitted as `spec-dispatch-table` in
  src/generated/host.lisp). `tableLookup_build` proves the indexed load
  answers exactly what the first-match-wins scan of the manifest answers, given
  no chunk address is 0 (which the emitted builder checks) — so
  `runAsm_eq_runSpec` is stated against the manifest itself. (The scan it
  replaced cost ~400-1,800 iterations per chunk transition on near-tip
  mainnet contracts and made the JIT tier 2x slower than the interpreter.)

  ## What this module does not cover

  That the manifest is the emitted image of `Program.lookup`'s chunk table
  (built in `ARM64.JIT.emitChunk`'s `_eita_jit_entries`) is a separate
  obligation, and one this file does not discharge; so is `buildCL`'s fold skeleton
  and FFI around the two `Expr.toCL` steps (a CL template, like `fakeExponentialCL`).
-/

namespace Evm.CL.ARM64.RunProgramDenote

/-- The state the loop can observe and change, abstracted: the loop only ever
    reads `pc` and `halted` and calls the per-program chunk runner. Keeping the
    state opaque is what makes the two orderings comparable at all — nothing
    here depends on what a chunk does. -/
structure Loop (σ : Type) where
  pc     : σ → Nat
  halted : σ → Bool
  run    : σ → Nat → σ        -- `blr x21` — run_chunk(state, fn)

/-- The manifest: `(pc, fn)` pairs, first match wins (duplicates would be
    shadowed, as `dedupByPc` already guarantees there are none). -/
def manifestLookup : List (Nat × Nat) → Nat → Option Nat
  | [],            _  => none
  | (p, fn) :: ms, pc => if p = pc then some fn else manifestLookup ms pc

theorem manifestLookup_mem : ∀ (m : List (Nat × Nat)) (pc fn : Nat),
    manifestLookup m pc = some fn → (pc, fn) ∈ m
  | [], _, _, h => by simp [manifestLookup] at h
  | (p, f) :: ms, pc, fn, h => by
    unfold manifestLookup at h; split at h <;> grind [manifestLookup_mem ms pc fn]

open Evm.CL.GasEmit (Expr Env)

/-- Pass 1, per entry: the table grows to cover `pc` (so `n = 1 + max pc`). -/
def sizeStep : Expr := .emax (.var "n") (.add (.var "pc") (.lit 1))
/-- Pass 2, per entry: write `fn` at `pc` iff the slot is still 0 (first match wins). -/
def slotStep : Expr := .ite (.lit 0) (.var "slot") (.var "slot") (.var "fn")

def bind2 (a : String) (x : Nat) (b : String) (y : Nat) : Env := fun v => if v = a then x else if v = b then y else 0

/-- The dispatch table the loader builds (`spec-dispatch-table`, src/generated/host.lisp): pass 1
    folds `sizeStep` over the manifest for the size `n`, pass 2 `slotStep` into `n` zeroed words. -/
def tableSize (m : List (Nat × Nat)) : Nat := m.foldl (fun n e => sizeStep.eval (bind2 "n" n "pc" e.1)) 0
def build (m : List (Nat × Nat)) : List Nat :=
  m.foldl (fun t e => t.modify e.1 fun s => slotStep.eval (bind2 "slot" s "fn" e.2))
    (List.replicate (tableSize m) 0)

/-- `Lrp_loop`'s lookup: `cmp x9, x10; b.hs miss` (pc past the table), then
    `ldr x1, [x11, x9, lsl #3]; cbz x1, miss`. -/
def tableLookup (t : List Nat) (pc : Nat) : Option Nat :=
  match t[pc]? with
  | some fn => if fn = 0 then none else some fn
  | none    => none

theorem tableSize_covers (m : List (Nat × Nat)) : ∀ e ∈ m, e.1 < tableSize m := by
  suffices ∀ (m : List (Nat × Nat)) n0, n0 ≤ m.foldl (fun n e => max n (e.1 + 1)) n0 ∧
      ∀ e ∈ m, e.1 < m.foldl (fun n e => max n (e.1 + 1)) n0 by
    simpa [tableSize, sizeStep, Expr.eval, bind2] using (this m 0).2
  intro m; induction m with
  | nil => simp
  | cons e ms ih => intro n0; have := ih (max n0 (e.1 + 1)); grind

theorem build_getElem? (m : List (Nat × Nat)) (hfn : ∀ e ∈ m, e.2 ≠ 0) :
    ∀ (t : List Nat) (i : Nat),
      (m.foldl (fun t e => t.modify e.1 fun s => slotStep.eval (bind2 "slot" s "fn" e.2)) t)[i]?
        = t[i]?.map (fun s => if s = 0 then (manifestLookup m i).getD 0 else s) := by
  induction m with
  | nil => intro t i; simp only [List.foldl_nil]; cases t[i]? <;> simp [manifestLookup]
  | cons e ms ih =>
    intro t i; obtain ⟨p, f⟩ := e
    rw [List.foldl_cons, ih (fun e he => hfn e (List.mem_cons_of_mem _ he)), List.getElem?_modify]
    have := hfn _ List.mem_cons_self
    cases t[i]? <;> simp [slotStep, Expr.eval, bind2, manifestLookup] <;> grind

/-- **The indexed load is the manifest scan**, for the table the loader builds from a
    manifest with no zero chunk address. -/
theorem tableLookup_build (m : List (Nat × Nat)) (hfn : ∀ e ∈ m, e.2 ≠ 0) (pc : Nat) :
    tableLookup (build m) pc = manifestLookup m pc := by
  have := fun fn (hl : manifestLookup m pc = some fn) =>
    And.intro (hfn _ (manifestLookup_mem m pc fn hl)) (tableSize_covers m _ (manifestLookup_mem m pc fn hl))
  unfold tableLookup build
  rw [build_getElem? m hfn, List.getElem?_replicate]
  cases hl : manifestLookup m pc <;> grind

/-- `build` as Common Lisp: the steps are `Expr.toCL` of `sizeStep` / `slotStep` over
    variables named as they are bound here; the error is `hfn`, checked before any write.
    PAIRS is the manifest as `(pc . fn)` conses; the result is calloc'd `{n; fn[0..n-1]}`. -/
def buildCL : String :=
  "(defun spec-dispatch-table (pairs)\n" ++
  "  (let ((n 0))\n" ++
  "    (loop for (pc . fn) in pairs\n" ++
  "          do (when (zerop fn) (error \"spec-dispatch-table: chunk at pc ~D has address 0\" pc))\n" ++
  s!"             (setf n {sizeStep.toCL}))\n" ++
  "    (let ((tab (foreign-funcall \"calloc\" :size (1+ n) :size 8 :pointer)))\n" ++
  "      (when (null-pointer-p tab) (error \"spec-dispatch-table: calloc ~D words failed\" (1+ n)))\n" ++
  "      (setf (mem-aref tab :uint64 0) n)\n" ++
  "      (loop for (pc . fn) in pairs for slot = (mem-aref tab :uint64 (1+ pc))\n" ++
  s!"            do (setf (mem-aref tab :uint64 (1+ pc)) {slotStep.toCL}))\n" ++
  "      tab)))\n" ++
  ";; The (pc . fn) pairs of a `_eita_jit_entries` manifest {count; (pc, fn)...} (JIT.entriesTable).\n" ++
  "(defun spec-manifest-pairs (entries)\n" ++
  "  (loop for k below (mem-aref entries :uint64 0)\n" ++
  "        collect (cons (mem-aref entries :uint64 (+ 1 (* 2 k)))\n" ++
  "                      (mem-aref entries :uint64 (+ 2 (* 2 k))))))"

/-- The emitted loop, in the emitted order, over the dispatch table T. Return
    codes as the host reads them: 0 ok, 1 manifest miss (compiler coverage gap,
    logged, frame finishes on the interp tier), 2 fuel. -/
def runAsm {σ : Type} (L : Loop σ) (t : List Nat) : Nat → σ → Nat × σ
  | fuel, s =>
    if L.halted s then (0, s)
    else
      match fuel with
      | 0      => (2, s)
      | f + 1  =>
        match tableLookup t (L.pc s) with
        | none    => (1, s)
        | some fn => runAsm L t f (L.run s fn)

/-- `IR.executeProgram`'s order: fuel, then lookup, then execute, then halted. -/
def runSpec {σ : Type} (L : Loop σ) (m : List (Nat × Nat)) : Nat → σ → Nat × σ
  | 0,     s => (2, s)
  | f + 1, s =>
    match manifestLookup m (L.pc s) with
    | none    => (1, s)
    | some fn =>
      let s' := L.run s fn
      if L.halted s' then (0, s') else runSpec L m f s'

/-- A halted state stops the loop at once, whatever the fuel — the top-of-loop
    test. Used twice below. -/
theorem runAsm_halted {σ : Type} (L : Loop σ) (t : List Nat)
    (fuel : Nat) (s : σ) (hs : L.halted s = true) : runAsm L t fuel s = (0, s) := by
  unfold runAsm
  simp [hs]

/-- **The loop refines the spec for every entry state the host can produce**,
    over the table the loader builds from the manifest. The induction is on
    fuel, and the step case is where the asm's top-of-loop `halted` test
    becomes the spec's post-execute test. -/
theorem runAsm_eq_runSpec {σ : Type} (L : Loop σ) (m : List (Nat × Nat))
    (hfn : ∀ e ∈ m, e.2 ≠ 0) :
    ∀ (fuel : Nat) (s : σ), L.halted s = false →
      runAsm L (build m) fuel s = runSpec L m fuel s := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hs
    simp [runAsm, runSpec, hs]
  | succ f ih =>
    intro s hs
    simp only [runAsm, runSpec, hs, if_false, Bool.false_eq_true, tableLookup_build m hfn]
    cases manifestLookup m (L.pc s) with
    | none => rfl
    | some fn =>
      -- The asm recurses and tests `halted` at the top of the next iteration;
      -- the spec tests it here. Same test, same state.
      cases hh : L.halted (L.run s fn)
      · simpa [hh] using ih (L.run s fn) hh
      · simp [hh, runAsm_halted L _ f (L.run s fn) hh]

/-- **…and the one input where they differ**: an already-halted entry with no
    fuel. The asm calls it ok, the spec calls it out of gas. Unreachable through
    the host (`gas_left + 1 ≥ 1`, and frames are not entered halted), and
    recorded so the ordering cannot be called "case-for-case". -/
theorem halted_entry_differs :
    ∃ (L : Loop Bool) (m : List (Nat × Nat)) (s : Bool),
      L.halted s = true ∧ runAsm L (build m) 0 s ≠ runSpec L m 0 s := by
  refine ⟨{ pc := fun _ => 0, halted := id, run := fun s _ => s }, [], true, rfl, ?_⟩
  simp [runAsm, runSpec]

/-- With fuel, a halted entry is not a divergence: both stop at once, because
    the spec's lookup-then-execute cannot move a halted state either — provided
    the pc is in the manifest. (Outside the manifest the spec reports a miss
    where the asm reports ok; the host's manifest covers the frame's entry pc by
    construction, which is the same obligation the module header names.) -/
theorem halted_entry_with_fuel {σ : Type} (L : Loop σ) (t : List Nat)
    (f : Nat) (s : σ) (hs : L.halted s = true) :
    runAsm L t (f + 1) s = (0, s) :=
  runAsm_halted L t (f + 1) s hs

end Evm.CL.ARM64.RunProgramDenote
