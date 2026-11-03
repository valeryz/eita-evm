/-
  Evm.CL.X86.FlushScaleX — what `OpInstrs.spScale` makes of the x86-64 flush
  program: `emitRegionFlushT x86Flush r`, instruction by instruction, is the
  explicit program `emitRegionFlushX r` built from the pieces `FlushSemX` and
  `MemCommitSemX` reason about (byte-scaled depth immediates, the stack-address
  idiom as a plain add, everything else unchanged).
-/

import Evm.CL.X86.FlushSemX
import Evm.CL.X86.MemCommitSemX
import Evm.CL.OpInstrs

namespace Evm.CL.X86.FlushScaleX

open Evm.CL.AsmCore Evm.CL.ARM64.JIT Evm.CL.X86.FlushSemX Evm.CL.OpInstrs
open Evm.IR.SymExpr (Expr)

/-- The lowering's per-instruction pass over a program. -/
def scaleP (p : List AInstr) : List AInstr := p.flatMap spScale

@[simp] theorem scaleP_nil : scaleP [] = [] := rfl
@[simp] theorem scaleP_cons (i : AInstr) (p : List AInstr) : scaleP (i :: p) = spScale i ++ scaleP p := rfl
@[simp] theorem scaleP_append (p q : List AInstr) : scaleP (p ++ q) = scaleP p ++ scaleP q := by
  simp [scaleP, List.flatMap_append]
theorem scaleP_flatMap {α : Type} (f : α → List AInstr) (l : List α) :
    scaleP (l.flatMap f) = l.flatMap (fun a => scaleP (f a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- A program `spScale` leaves alone. -/
theorem scaleP_id (p : List AInstr) (h : ∀ i ∈ p, spScale i = [i]) : scaleP p = p := by
  induction p with
  | nil => rfl
  | cons i p ih => rw [scaleP_cons, h i (by simp), ih (fun j hj => h j (by simp [hj]))]; rfl

/-! ## Pieces -/

theorem scale_spAddr (r : Reg) (k : Nat) (hr : isNos r = false) :
    scaleP (Evm.CL.X86JIT.x86Flush.spAddr r k) = spAddrX r k := by
  simp [scaleP, Evm.CL.X86JIT.x86Flush, spAddrX, spScale, dest?, hr]

theorem scale_loadSlot (lo : Reg) (k : Nat) :
    scaleP (loadSlotT Evm.CL.X86JIT.x86Flush lo k) = loadSlotX lo k := by
  cases lo <;> rfl

theorem scale_storeSlot (k : Nat) : scaleP (storeSlotT Evm.CL.X86JIT.x86Flush k) = storeSlotX k := rfl

theorem scale_evalNode (idx : Expr → Nat) (e : Expr) :
    scaleP (evalNodeT Evm.CL.X86JIT.x86Flush idx e) = evalNodeX idx e := by
  cases e <;> rfl

theorem scale_exitOne (idx : Expr → Nat) (net : Int) (e : Expr) (m : Nat) :
    scaleP (exitOneT Evm.CL.X86JIT.x86Flush idx net e m) = exitOneX idx net e m := by
  unfold exitOneT exitOneX
  dsimp only
  split <;> rfl

theorem scale_exitStores (idx : Expr → Nat) (net : Int) (exprs : List Expr) :
    scaleP (exitStoresT Evm.CL.X86JIT.x86Flush idx net exprs) = exitStoresX idx net exprs := by
  unfold exitStoresT exitStoresX
  rw [scaleP_flatMap]
  congr 1
  funext p
  exact scale_exitOne idx net p.1 p.2

theorem scale_frameOpen (n : Nat) : scaleP (Evm.CL.X86JIT.x86Flush.frameOpen n) = frameOpenX n := rfl
theorem scale_frameClose (n : Nat) : scaleP (Evm.CL.X86JIT.x86Flush.frameClose n) = frameCloseX n := rfl

theorem scale_depthUpdate (net : Int) : scaleP (depthUpdate net) = depthUpdateX net := by
  unfold depthUpdate depthUpdateX
  split
  · rfl
  · split <;> rfl

theorem scale_cacheReload : scaleP Evm.CL.X86JIT.x86Flush.cacheReload = cacheReloadX := rfl

theorem scale_far (sym : String) : scaleP (Evm.CL.X86JIT.x86Flush.far sym) = [.bTramp sym] := rfl

/-- The memory commit is untouched by the pass. -/
theorem scale_memBaseAt (o : Nat) : scaleP (memBaseAtT Evm.CL.X86JIT.x86Flush o) = memBaseAtT Evm.CL.X86JIT.x86Flush o := by
  unfold memBaseAtT
  split
  · rfl
  · split <;> rfl

theorem scale_memWrite (idx : Expr → Nat) (w : MemWrite) :
    scaleP (emitMemWriteT Evm.CL.X86JIT.x86Flush idx w) = emitMemWriteT Evm.CL.X86JIT.x86Flush idx w := by
  unfold emitMemWriteT
  rw [scaleP_append, scaleP_append, scale_memBaseAt]
  have h1 : scaleP (loadSlotT Evm.CL.X86JIT.x86Flush .x6 (idx w.val)) = loadSlotT Evm.CL.X86JIT.x86Flush .x6 (idx w.val) := rfl
  rw [h1]
  split <;> rfl

theorem scale_memExpand (maxEnd : Nat) :
    scaleP (memExpandFlushT Evm.CL.X86JIT.x86Flush maxEnd) = memExpandFlushT Evm.CL.X86JIT.x86Flush maxEnd := rfl

theorem scale_mpUpdate (maxEnd : Nat) :
    scaleP (mpUpdateFlushT Evm.CL.X86JIT.x86Flush maxEnd) = mpUpdateFlushT Evm.CL.X86JIT.x86Flush maxEnd := rfl

theorem scale_memCommit (idx : Expr → Nat) (ws : List MemWrite) :
    scaleP (memCommitT Evm.CL.X86JIT.x86Flush idx ws) = memCommitT Evm.CL.X86JIT.x86Flush idx ws := by
  unfold memCommitT
  split
  · rfl
  · rw [scaleP_append, scaleP_append, scale_memExpand, scale_mpUpdate, scaleP_flatMap]
    congr 2
    funext w
    exact scale_memWrite idx w

/-- The checks. -/
theorem scale_underflow (need : Nat) :
    scaleP ([AInstr.cmpImm .x23 need, .bcLbl .hs "8f"] ++ Evm.CL.X86JIT.x86Flush.far "_eita_stack_underflow" ++ [.label "8"]) =
      [AInstr.cmpImm .x23 (32 * need), .bcLbl .hs "8f", .bTramp "_eita_stack_underflow", .label "8"] := rfl

theorem scale_overflow (lim : Nat) :
    scaleP ([AInstr.cmpImm .x23 lim, .bcLbl .lo "9f"] ++ Evm.CL.X86JIT.x86Flush.far "_eita_stack_overflow" ++ [.label "9"]) =
      [AInstr.cmpImm .x23 (32 * lim), .bcLbl .lo "9f", .bTramp "_eita_stack_overflow", .label "9"] := rfl

/-! ## The whole flush -/

theorem scale_s1 (r : Region) :
    scaleP (if r.need > 0
      then [AInstr.cmpImm .x23 r.need, .bcLbl .hs "8f"] ++ Evm.CL.X86JIT.x86Flush.far "_eita_stack_underflow" ++ [.label "8"]
      else []) =
    (if r.need > 0
      then [AInstr.cmpImm .x23 (32 * r.need), .bcLbl .hs "8f", .bTramp "_eita_stack_underflow", .label "8"] else []) := by
  split <;> rfl

theorem scale_s2 (r : Region) :
    scaleP (if r.maxNet > 0
      then [AInstr.cmpImm .x23 (1025 - r.maxNet).toNat, .bcLbl .lo "9f"] ++ Evm.CL.X86JIT.x86Flush.far "_eita_stack_overflow" ++ [.label "9"]
      else []) =
    (if r.maxNet > 0
      then [AInstr.cmpImm .x23 (32 * (1025 - r.maxNet).toNat), .bcLbl .lo "9f", .bTramp "_eita_stack_overflow", .label "9"]
      else []) := by
  split <;> rfl

theorem scale_body (slots : Array Expr) (idx : Expr → Nat) (ws : List MemWrite) (net : Int) (exprs : List Expr) :
    scaleP (if slots.size > 0 then
        Evm.CL.X86JIT.x86Flush.frameOpen slots.size ++ slots.toList.flatMap (evalNodeT Evm.CL.X86JIT.x86Flush idx) ++
        memCommitT Evm.CL.X86JIT.x86Flush idx ws ++ exitStoresT Evm.CL.X86JIT.x86Flush idx net exprs ++
        Evm.CL.X86JIT.x86Flush.frameClose slots.size
      else []) =
    (if slots.size > 0 then
        frameOpenX slots.size ++ slots.toList.flatMap (evalNodeX idx) ++ memCommitT Evm.CL.X86JIT.x86Flush idx ws ++
        exitStoresX idx net exprs ++ frameCloseX slots.size
      else []) := by
  split
  · simp only [scaleP_append, scale_frameOpen, scale_frameClose, scale_memCommit, scale_exitStores, scaleP_flatMap,
               scale_evalNode]
  · rfl

/-- `emitRegionFlushT x86Flush r` after `spScale`, as explicit pieces. -/
def emitRegionFlushX (r : Region) : List AInstr :=
  let p := r.ss.exprs.length
  let c := r.ss.consumed
  let net : Int := (p : Int) - c
  let idle := p == 0 && c == 0 && r.writes.isEmpty
  if idle && r.need == 0 && r.maxNet ≤ 0 then [] else
  if r.need > 1024 then [.bTramp "_eita_stack_underflow"] else
  let s1 := if r.need > 0
    then [AInstr.cmpImm .x23 (32 * r.need), .bcLbl .hs "8f", .bTramp "_eita_stack_underflow", .label "8"] else []
  if r.maxNet > 0 && 1025 - r.maxNet ≤ 0 then s1 ++ [.bTramp "_eita_stack_overflow"] else
  let s2 := s1 ++ (if r.maxNet > 0
    then [AInstr.cmpImm .x23 (32 * (1025 - r.maxNet).toNat), .bcLbl .lo "9f", .bTramp "_eita_stack_overflow", .label "9"]
    else [])
  if idle then s2 else
  let (slots, idx) := dagSlots (r.ss.exprs ++ r.writes.map (·.val))
  let n := slots.size
  let body := if n > 0 then
      frameOpenX n ++ slots.toList.flatMap (evalNodeX idx) ++ memCommitT Evm.CL.X86JIT.x86Flush idx r.writes ++
      exitStoresX idx net r.ss.exprs ++ frameCloseX n
    else []
  s2 ++ body ++ depthUpdateX net ++ cacheReloadX

theorem scale_emitRegionFlush (r : Region) :
    scaleP (emitRegionFlushT Evm.CL.X86JIT.x86Flush r) = emitRegionFlushX r := by
  unfold emitRegionFlushT emitRegionFlushX
  simp only
  split
  · rfl
  · split
    · rfl
    · split
      · rw [scaleP_append, scale_s1, scale_far]
      · split
        · rw [scaleP_append, scale_s1, scale_s2]
        · rw [scaleP_append, scaleP_append, scaleP_append, scaleP_append, scale_s1, scale_s2, scale_body,
              scale_depthUpdate, scale_cacheReload]

end Evm.CL.X86.FlushScaleX
