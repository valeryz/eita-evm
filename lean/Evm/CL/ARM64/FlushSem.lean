/-
  Evm.CL.ARM64.FlushSem — the region flush (`ARM64.JIT.emitRegionFlushT` at
  `armFlush`) run under `AsmRun` computes the region's symbolic stack.

  The flush is: depth checks; a scratch frame of 32-byte slots on the machine
  stack; the exit DAG evaluated slot by slot (`evalNodeT`: constants, entry
  reads, the u256 cores of `CoreSem`, helper calls); the exit prefix stored to
  the EVM stack; the depth updated; the TOS/NOS caches reloaded. Each piece
  gets a lemma over an invariant `Inv` (frame base in sp, depth in x23, stack
  base in x24, the entry stack intact in memory, the slots evaluated so far
  holding `eval`); the layout facts the pieces need — no address wrap, the
  frame disjoint from the EVM stack, both outside the helpers' stack window —
  are a hypothesis `Lay`.
-/

import Evm.CL.AsmRunMem
import Evm.CL.ARM64.CoreSem
import Evm.CL.ARM64.ChunkGasSem

namespace Evm.CL.ARM64.FlushSem

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.ARM64.JIT Evm.CL.ARM64.CoreSem
open Evm.CL.ARM64.ChunkGasSem (movImmInstrs_run)
open Evm.IR.SymExpr (Expr eval)

/-! ## Layout -/

/-- The frame: its base `fp` (sp while the DAG is evaluated), its slot count
    `n`, the EVM stack base and entry depth, the entry stack. -/
structure Fr where
  fp   : BitVec 64
  n    : Nat
  base : BitVec 64
  d    : Nat
  es   : List Evm.U256

def slotAddr (fp : BitVec 64) (k : Nat) : BitVec 64 := off fp (32 * k)
/-- Entry slot `k` (0 = top) of a stack of depth `d`. -/
def stackAddr (base : BitVec 64) (d k : Nat) : BitVec 64 := off base (32 * (d - 1 - k))

/-- What the layout guarantees: nothing wraps, the frame and the EVM stack are
    disjoint, neither is in the helpers' stack window. -/
structure Lay (F : Fr) : Prop where
  fpOk   : F.fp.toNat + 32 * F.n + 16 < 2 ^ 64
  /-- the EVM stack arena: 1024 slots -/
  baseOk : F.base.toNat + 32 * 1024 < 2 ^ 64
  dLe    : F.d ≤ 1024
  /-- the frame and the saved fp/lr above it, against the whole arena -/
  disj   : ∀ i < 32 * F.n + 16, ∀ j < 32 * 1024, off F.fp i ≠ off F.base j
  stackOut : ∀ j < 32 * 1024, belowSp F.fp (off F.base j) = false
  esLen  : F.es.length = F.d

theorem Lay.dOk {F : Fr} (hL : Lay F) : F.d < 2 ^ 32 := by have := hL.dLe; omega

/-- The invariant while the DAG is evaluated: `done` are the slots computed. -/
structure Inv (F : Fr) (idx : Expr → Nat) (done : List Expr) (s : RS) : Prop where
  sp    : s.sp = F.fp
  x23   : s.regs .x23 = BitVec.ofNat 64 F.d
  x24   : s.regs .x24 = F.base
  stack : ∀ k < F.d, ld256 s.mem (stackAddr F.base F.d k) = F.es.getD k 0
  slots : ∀ e ∈ done, ld256 s.mem (slotAddr F.fp (idx e)) = eval e F.es

/-- Registers a node leaves alone (the frame's and the callee-saved ones). -/
def keep : Reg → Bool
  | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 | .x28 => true
  | _ => false

/-- A kept register is none of the scratch ones. -/
theorem keep_ne (r : Reg) (h : keep r = true) :
    r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧
    r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x16 ∧ r ≠ .x17 := by
  cases r <;> simp [keep] at h ⊢

theorem set_regs_ne (s : RS) (r r' : Reg) (v : BitVec 64) (h : r' ≠ r) : (s.set r v).regs r' = s.regs r' := by
  simp [RS.set, h]

/-! ## Slot addressing -/

theorem spAddrA_run (H : Helpers) (r : Reg) (k : Nat) (hk : 32 * k < 2 ^ 64) (rest : List AInstr) (s : RS) :
    run H (spAddrA r k ++ rest) s = run H rest (s.set r (off s.sp (32 * k))) := by
  simp only [spAddrA]
  split
  · rw [List.singleton_append, run_cons_data H _ _ s (ctrl_addSp ..), step_addSp]
  · rw [movImmA, List.append_assoc, movImmInstrs_run H _ _ hk, List.singleton_append,
        run_cons_data H _ _ _ (by rfl), step_addSpReg, set_set_same]
    simp only [AsmRun.set_sp, AsmRun.set_regs, ite_true]

/-! ## Slot loads and stores -/

/-- `loadSlotA .x6 k`: x6-x9 ← the slot; x14 is scratch. -/
theorem loadSlot_x6_run (H : Helpers) (k : Nat) (hk : 32 * k < 2 ^ 64) (rest : List AInstr) (s : RS) :
    ∃ s', run H (loadSlotA .x6 k ++ rest) s = run H rest s' ∧
      lhs s' = ld256 s.mem (slotAddr s.sp k) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → s'.regs r = s.regs r) := by
  simp only [loadSlotA, loadSlotT, quadT, armFlush]
  rw [List.append_assoc, spAddrA_run H _ _ hk, List.cons_append,
      run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..), List.singleton_append,
      run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..)]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [lhs, AsmRun.set_regs, AsmRun.set_mem, reduceCtorEq, ite_true, ite_false, Nat.reduceAdd,
               slotAddr, ld256_eq_ofLimbs, off, BitVec.add_zero]
  · intro r h6 h7 h8 h9 h14; simp [RS.set, h6, h7, h8, h9, h14]

/-- `loadSlotA .x10 k`: x10-x13 ← the slot; x14 is scratch. -/
theorem loadSlot_x10_run (H : Helpers) (k : Nat) (hk : 32 * k < 2 ^ 64) (rest : List AInstr) (s : RS) :
    ∃ s', run H (loadSlotA .x10 k ++ rest) s = run H rest s' ∧
      rhs armRq s' = ld256 s.mem (slotAddr s.sp k) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → s'.regs r = s.regs r) := by
  simp only [loadSlotA, loadSlotT, quadT, armFlush]
  rw [List.append_assoc, spAddrA_run H _ _ hk, List.cons_append,
      run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..), List.singleton_append,
      run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..)]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [rhs, armRq, AsmRun.set_regs, AsmRun.set_mem, reduceCtorEq, ite_true, ite_false, Nat.reduceAdd,
               slotAddr, ld256_eq_ofLimbs, off, BitVec.add_zero]
  · intro r h10 h11 h12 h13 h14; simp [RS.set, h10, h11, h12, h13, h14]

/-- `storeSlotA k`: the slot ← x6-x9; x14 is scratch. -/
theorem storeSlot_run (H : Helpers) (k : Nat) (hk : 32 * k < 2 ^ 64) (rest : List AInstr) (s : RS) :
    ∃ s', run H (storeSlotA k ++ rest) s = run H rest s' ∧
      s'.mem = st256 s.mem (slotAddr s.sp k) (lhs s) ∧ s'.sp = s.sp ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x14 → s'.regs r = s.regs r) := by
  simp only [storeSlotA, storeSlotT, armFlush]
  rw [List.append_assoc, spAddrA_run H _ _ hk, List.cons_append,
      run_cons_step H _ _ _ _ (ctrl_stpOff ..) (step_stpOff ..), List.singleton_append,
      run_cons_step H _ _ _ _ (ctrl_stpOff ..) (step_stpOff ..)]
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · simp only [lhs, AsmRun.store64_mem, AsmRun.store64_regs, AsmRun.set_regs, reduceCtorEq, ite_true, ite_false,
               Nat.reduceAdd, slotAddr]
    rw [← st64_four_eq_st256]
    simp only [off, BitVec.add_zero]
    rfl
  · intro r h14; simp [RS.set, h14]

/-! ## Leaves -/

theorem limb_lt (v : Evm.U256) (i : Nat) : limb v i < 2 ^ 64 := Nat.mod_lt _ (by decide)

/-- `limb v i`, as the limb. -/
theorem ofNat_limb (v : Evm.U256) (i : Nat) :
    BitVec.ofNat 64 (limb v i) = v.extractLsb' (64 * i) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [limb, Evm.U256.toNat, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat]
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]

/-- `sub x14, x23, #(k+1) ; add x14, x24, x14, lsl #5` is the entry slot `k`. -/
theorem stackAt_addr (base : BitVec 64) (d k : Nat) (hk : k < d) (hd : d < 2 ^ 32) :
    base + ((BitVec.ofNat 64 d - BitVec.ofNat 64 (k + 1)) <<< 5) = stackAddr base d k := by
  simp only [stackAddr, off]
  congr 1
  have hle : BitVec.ofNat 64 (k + 1) ≤ BitVec.ofNat 64 d := by
    rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_sub_of_le hle]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 32 * (d - 1 - k) < 2 ^ 64), Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
  · omega
  · have : (d - (k + 1)) * 2 ^ 5 ≤ d * 32 := by
      rw [show (2 : Nat) ^ 5 = 32 from rfl]; exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega

/-- What a node leaves behind: the frame base, the kept registers, the memory
    outside its own slot and the helpers' window. -/
structure NodeOut (F : Fr) (idx : Expr → Nat) (e : Expr) (s s' : RS) : Prop where
  sp   : s'.sp = s.sp
  regs : ∀ r, keep r = true → s'.regs r = s.regs r
  slot : ld256 s'.mem (slotAddr F.fp (idx e)) = eval e F.es
  mem  : ∀ x, (∀ i < 32, x ≠ off (slotAddr F.fp (idx e)) i) → belowSp F.fp x = false → s'.mem x = s.mem x

/-- A `const` node. -/
theorem node_const (H : Helpers) (F : Fr) (idx : Expr → Nat) (v : Evm.U256) (rest : List AInstr) (s : RS)
    (hsp : s.sp = F.fp) (hn : 32 * idx (.const v) < 2 ^ 64) :
    ∃ s', run H (evalNodeT armFlush idx (.const v) ++ rest) s = run H rest s' ∧
      NodeOut F idx (.const v) s s' := by
  simp only [evalNodeT, armFlush, movImmA, List.append_assoc]
  rw [movImmInstrs_run H _ _ (limb_lt v 0), movImmInstrs_run H _ _ (limb_lt v 1),
      movImmInstrs_run H _ _ (limb_lt v 2), movImmInstrs_run H _ _ (limb_lt v 3)]
  obtain ⟨s', h1, hmem, hsp', hfl, hregs⟩ := storeSlot_run H _ hn rest _
  refine ⟨s', h1, ⟨?_, ?_, ?_, ?_⟩⟩
  · simp [hsp', hsp]
  · intro r hr
    obtain ⟨_, _, _, _, h6, h7, h8, h9, _, _, _, _, h14, _, _, _⟩ := keep_ne r hr
    rw [hregs r h14, set_regs_ne _ _ _ _ h9, set_regs_ne _ _ _ _ h8, set_regs_ne _ _ _ _ h7, set_regs_ne _ _ _ _ h6]
  · rw [hmem]
    simp only [AsmRun.set_sp, hsp, lhs, AsmRun.set_regs, reduceCtorEq, ite_true, ite_false,
               ofNat_limb, Nat.reduceMul, Nat.mul_zero]
    rw [ld256_st256_same, ofLimbs_extract]
    rfl
  · intro x hx _
    rw [hmem]
    simp only [AsmRun.set_sp, hsp]
    exact st256_out _ _ _ _ hx

/-- A `stackAt k` node: the entry stack is read where `Inv` says it is. -/
theorem node_stackAt (H : Helpers) (F : Fr) (idx : Expr → Nat) (done : List Expr) (k : Nat)
    (rest : List AInstr) (s : RS) (hI : Inv F idx done s) (hL : Lay F)
    (hk : k < F.d) (hn : 32 * idx (.stackAt k) < 2 ^ 64) :
    ∃ s', run H (evalNodeT armFlush idx (.stackAt k) ++ rest) s = run H rest s' ∧
      NodeOut F idx (.stackAt k) s s' := by
  simp only [evalNodeT, armFlush, List.cons_append, List.nil_append]
  rw [run_cons_step H _ _ _ _ (ctrl_subImm ..) (step_subImm ..),
      run_cons_step H _ _ _ _ (ctrl_addLsl5 ..) (step_addLsl5 ..),
      run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..),
      run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..)]
  obtain ⟨s', h1, hmem, hsp', hfl, hregs⟩ := storeSlot_run H _ hn rest _
  refine ⟨s', h1, ⟨?_, ?_, ?_, ?_⟩⟩
  · simp [hsp', hI.sp]
  · intro r hr
    obtain ⟨_, _, _, _, h6, h7, h8, h9, _, _, _, _, h14, _, _, _⟩ := keep_ne r hr
    rw [hregs r h14, set_regs_ne _ _ _ _ h9, set_regs_ne _ _ _ _ h8, set_regs_ne _ _ _ _ h7,
        set_regs_ne _ _ _ _ h6, set_regs_ne _ _ _ _ h14, set_regs_ne _ _ _ _ h14]
  · rw [hmem]
    simp only [AsmRun.set_sp, hI.sp, lhs]
    rw [ld256_st256_same]
    simp only [AsmRun.set_regs, AsmRun.set_mem, reduceCtorEq, ite_true, ite_false, Nat.reduceAdd,
               hI.x23, hI.x24, stackAt_addr F.base F.d k hk hL.dOk, BitVec.add_zero]
    rw [← ld256_eq_ofLimbs, hI.stack k hk]
    rfl
  · intro x hx _
    rw [hmem]
    simp only [AsmRun.set_sp, hI.sp]
    exact st256_out _ _ _ _ hx

/-! ## Binary and unary cores -/

/-- Any core that computes `op` into x6-x9 from the two quads. -/
def CoreSpec (H : Helpers) (core : List AInstr) (op : Evm.U256 → Evm.U256 → Evm.U256) : Prop :=
  ∀ rest s, ∃ s', run H (core ++ rest) s = run H rest s' ∧
    lhs s' = op (lhs s) (rhs armRq s) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
    (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → s'.regs r = s.regs r)

theorem node_bin (H : Helpers) (F : Fr) (idx : Expr → Nat) (done : List Expr) (e a b : Expr)
    (core : List AInstr) (op : Evm.U256 → Evm.U256 → Evm.U256) (rest : List AInstr) (s : RS)
    (hcore : CoreSpec H core op) (heval : eval e F.es = op (eval a F.es) (eval b F.es))
    (hI : Inv F idx done s) (ha : a ∈ done) (hb : b ∈ done)
    (hn : 32 * idx e < 2 ^ 64) (hna : 32 * idx a < 2 ^ 64) (hnb : 32 * idx b < 2 ^ 64) :
    ∃ s', run H ((loadSlotT armFlush .x6 (idx a) ++ loadSlotT armFlush .x10 (idx b) ++ core ++
                  storeSlotT armFlush (idx e)) ++ rest) s = run H rest s' ∧ NodeOut F idx e s s' := by
  simp only [List.append_assoc]
  obtain ⟨s1, h1, hv1, hsp1, hmem1, _, hregs1⟩ := loadSlot_x6_run H (idx a) hna _ s
  rw [show loadSlotT armFlush .x6 (idx a) = loadSlotA .x6 (idx a) from rfl, h1]
  obtain ⟨s2, h2, hv2, hsp2, hmem2, _, hregs2⟩ := loadSlot_x10_run H (idx b) hnb _ s1
  rw [show loadSlotT armFlush .x10 (idx b) = loadSlotA .x10 (idx b) from rfl, h2]
  obtain ⟨s3, h3, hv3, hsp3, hmem3, hregs3⟩ := hcore _ s2
  rw [h3]
  obtain ⟨s4, h4, hmem4, hsp4, _, hregs4⟩ := storeSlot_run H (idx e) hn rest s3
  rw [show storeSlotT armFlush (idx e) = storeSlotA (idx e) from rfl, h4]
  have hsp : s3.sp = F.fp := by rw [hsp3, hsp2, hsp1, hI.sp]
  have hlhs2 : lhs s2 = lhs s1 := by
    simp only [lhs]; rw [hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine ⟨s4, rfl, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hsp4, hsp, hI.sp]
  · intro r hr
    obtain ⟨_, _, _, _, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, _, _⟩ := keep_ne r hr
    rw [hregs4 r h14, hregs3 r h6 h7 h8 h9 h14 h15, hregs2 r h10 h11 h12 h13 h14, hregs1 r h6 h7 h8 h9 h14]
  · rw [hmem4, hsp, ld256_st256_same, hv3, hlhs2, hv1, hv2, hmem1, hI.sp, hsp1, hI.sp,
        hI.slots a ha, hI.slots b hb, heval]
  · intro x hx _
    rw [hmem4, hsp, st256_out _ _ _ _ hx, hmem3, hmem2, hmem1]

/-- Any unary core that computes `op` into x6-x9. -/
def UnSpec (H : Helpers) (core : List AInstr) (op : Evm.U256 → Evm.U256) : Prop :=
  ∀ rest s, ∃ s', run H (core ++ rest) s = run H rest s' ∧
    lhs s' = op (lhs s) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
    (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → s'.regs r = s.regs r)

theorem node_un (H : Helpers) (F : Fr) (idx : Expr → Nat) (done : List Expr) (e a : Expr)
    (core : List AInstr) (op : Evm.U256 → Evm.U256) (rest : List AInstr) (s : RS)
    (hcore : UnSpec H core op) (heval : eval e F.es = op (eval a F.es))
    (hI : Inv F idx done s) (ha : a ∈ done) (hn : 32 * idx e < 2 ^ 64) (hna : 32 * idx a < 2 ^ 64) :
    ∃ s', run H ((loadSlotT armFlush .x6 (idx a) ++ core ++ storeSlotT armFlush (idx e)) ++ rest) s =
            run H rest s' ∧ NodeOut F idx e s s' := by
  simp only [List.append_assoc]
  obtain ⟨s1, h1, hv1, hsp1, hmem1, _, hregs1⟩ := loadSlot_x6_run H (idx a) hna _ s
  rw [show loadSlotT armFlush .x6 (idx a) = loadSlotA .x6 (idx a) from rfl, h1]
  obtain ⟨s3, h3, hv3, hsp3, hmem3, hregs3⟩ := hcore _ s1
  rw [h3]
  obtain ⟨s4, h4, hmem4, hsp4, _, hregs4⟩ := storeSlot_run H (idx e) hn rest s3
  rw [show storeSlotT armFlush (idx e) = storeSlotA (idx e) from rfl, h4]
  have hsp : s3.sp = F.fp := by rw [hsp3, hsp1, hI.sp]
  refine ⟨s4, rfl, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hsp4, hsp, hI.sp]
  · intro r hr
    obtain ⟨_, _, _, _, h6, h7, h8, h9, _, _, _, _, h14, h15, _, _⟩ := keep_ne r hr
    rw [hregs4 r h14, hregs3 r h6 h7 h8 h9 h14 h15, hregs1 r h6 h7 h8 h9 h14]
  · rw [hmem4, hsp, ld256_st256_same, hv3, hv1, hI.sp, hI.slots a ha, heval]
  · intro x hx _
    rw [hmem4, hsp, st256_out _ _ _ _ hx, hmem3, hmem1]

/-! ## Helper calls -/

theorem belowSp_off_false (fp : BitVec 64) (i : Nat) (h : fp.toNat + i < 2 ^ 64) :
    belowSp fp (off fp i) = false := by
  simp only [belowSp, BitVec.ult, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt]
  left; rw [toNat_add_ofNat fp i h]; omega

theorem keep_not_callerSaved (r : Reg) (h : keep r = true) : callerSaved r = false := by
  cases r <;> simp [keep, callerSaved] at h ⊢

@[simp] theorem callHelper_sp (H : Helpers) (h : String) (s : RS) : (callHelper H h s).sp = s.sp := rfl

theorem callHelper_regs_keep (H : Helpers) (h : String) (s : RS) (r : Reg) (hr : keep r = true) :
    (callHelper H h s).regs r = s.regs r := by
  simp [callHelper, keep_not_callerSaved r hr]

theorem callHelper_mem (H : Helpers) (hC : H.conv = armConv) (h : String) (s : RS) :
    (callHelper H h s).mem =
      st256 (fun x => if belowSp s.sp x then H.junk h s x else s.mem x) (s.regs .x0)
        (if ternary h then H.fn3 h (ld256 s.mem (s.regs .x1)) (ld256 s.mem (s.regs .x2)) (ld256 s.mem (s.regs .x3))
         else H.fn2 h (ld256 s.mem (s.regs .x1)) (ld256 s.mem (s.regs .x2))) := by
  simp only [callHelper, hC, armConv]

theorem run_cons_blFar (H : Helpers) (h : String) (rest : List AInstr) (s : RS) :
    run H (.blFar h :: rest) s = run H rest (callHelper H h s) := by simp [run, ctrl]

/-- A two-argument helper node. -/
theorem node_call2 (H : Helpers) (hC : H.conv = armConv) (F : Fr) (idx : Expr → Nat) (done : List Expr) (e a b : Expr) (h : String)
    (rest : List AInstr) (s : RS)
    (ht : ternary h = false) (hval : H.fn2 h (eval a F.es) (eval b F.es) = eval e F.es)
    (hI : Inv F idx done s) (_hL : Lay F) (ha : a ∈ done) (hb : b ∈ done)
    (hn : 32 * idx e < 2 ^ 64) (hna : 32 * idx a < 2 ^ 64) (hnb : 32 * idx b < 2 ^ 64) :
    ∃ s', run H ((spAddrA .x0 (idx e) ++ spAddrA .x1 (idx a) ++ spAddrA .x2 (idx b) ++ [AInstr.blFar h]) ++ rest) s =
            run H rest s' ∧ NodeOut F idx e s s' := by
  simp only [List.append_assoc]
  rw [spAddrA_run H _ _ hn, spAddrA_run H _ _ hna, spAddrA_run H _ _ hnb, List.singleton_append, run_cons_blFar]
  refine ⟨_, rfl, ⟨rfl, ?_, ?_, ?_⟩⟩
  · intro r hr
    obtain ⟨h0, h1, h2, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := keep_ne r hr
    rw [callHelper_regs_keep _ _ _ _ hr, set_regs_ne _ _ _ _ h2, set_regs_ne _ _ _ _ h1, set_regs_ne _ _ _ _ h0]
  · rw [callHelper_mem H hC]
    simp only [AsmRun.set_regs, AsmRun.set_mem, AsmRun.set_sp, reduceCtorEq, ite_true, ite_false, ht,
               Bool.false_eq_true, hI.sp, slotAddr]
    rw [ld256_st256_same]
    have hsa := hI.slots a ha; have hsb := hI.slots b hb
    simp only [slotAddr] at hsa hsb
    rw [hsa, hsb, hval]
  · intro x hx hw
    rw [callHelper_mem H hC]
    simp only [AsmRun.set_regs, AsmRun.set_mem, AsmRun.set_sp, reduceCtorEq, ite_true, ite_false, hI.sp]
    simp only [slotAddr] at hx
    rw [st256_out _ _ _ _ hx]
    simp [hw]

/-- A three-argument helper node (addmod, mulmod). -/
theorem node_call3 (H : Helpers) (hC : H.conv = armConv) (F : Fr) (idx : Expr → Nat) (done : List Expr) (e a b c : Expr) (h : String)
    (rest : List AInstr) (s : RS)
    (ht : ternary h = true) (hval : H.fn3 h (eval a F.es) (eval b F.es) (eval c F.es) = eval e F.es)
    (hI : Inv F idx done s) (_hL : Lay F) (ha : a ∈ done) (hb : b ∈ done) (hc : c ∈ done)
    (hn : 32 * idx e < 2 ^ 64) (hna : 32 * idx a < 2 ^ 64) (hnb : 32 * idx b < 2 ^ 64) (hnc : 32 * idx c < 2 ^ 64) :
    ∃ s', run H ((spAddrA .x0 (idx e) ++ spAddrA .x1 (idx a) ++ spAddrA .x2 (idx b) ++ spAddrA .x3 (idx c) ++
                  [AInstr.blFar h]) ++ rest) s = run H rest s' ∧ NodeOut F idx e s s' := by
  simp only [List.append_assoc]
  rw [spAddrA_run H _ _ hn, spAddrA_run H _ _ hna, spAddrA_run H _ _ hnb, spAddrA_run H _ _ hnc,
      List.singleton_append, run_cons_blFar]
  refine ⟨_, rfl, ⟨rfl, ?_, ?_, ?_⟩⟩
  · intro r hr
    obtain ⟨h0, h1, h2, h3, _, _, _, _, _, _, _, _, _, _, _, _⟩ := keep_ne r hr
    rw [callHelper_regs_keep _ _ _ _ hr, set_regs_ne _ _ _ _ h3, set_regs_ne _ _ _ _ h2, set_regs_ne _ _ _ _ h1,
        set_regs_ne _ _ _ _ h0]
  · rw [callHelper_mem H hC]
    simp only [AsmRun.set_regs, AsmRun.set_mem, AsmRun.set_sp, reduceCtorEq, ite_true, ite_false, ht, hI.sp,
               slotAddr]
    rw [ld256_st256_same]
    have hsa := hI.slots a ha; have hsb := hI.slots b hb; have hsc := hI.slots c hc
    simp only [slotAddr] at hsa hsb hsc
    rw [hsa, hsb, hsc, hval]
  · intro x hx hw
    rw [callHelper_mem H hC]
    simp only [AsmRun.set_regs, AsmRun.set_mem, AsmRun.set_sp, reduceCtorEq, ite_true, ite_false, hI.sp]
    simp only [slotAddr] at hx
    rw [st256_out _ _ _ _ hx]
    simp [hw]

/-! ## Every node -/

theorem armFlush_rq : armFlush.rq = armRq := rfl

section specs
variable (H : Helpers)

theorem cs_add : CoreSpec H (addCoreT armRq) (· + ·) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, h5⟩ := addCore_run H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem cs_sub : CoreSpec H (subCoreT armRq) (· - ·) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, h5⟩ := subCore_run H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem cs_and : CoreSpec H (bitCoreT armRq .and3) (· &&& ·) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, _, h5⟩ := andCore_run H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem cs_or : CoreSpec H (bitCoreT armRq .orr3) (· ||| ·) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, _, h5⟩ := orCore_run H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem cs_xor : CoreSpec H (bitCoreT armRq .eor3) (· ^^^ ·) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, _, h5⟩ := xorCore_run H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem cs_lt : CoreSpec H (cmpCoreT armRq false .lo) (fun x y => if x < y then 1 else 0) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, h5⟩ := ltCore_run H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem cs_gt : CoreSpec H (cmpCoreT armRq true .lo) (fun x y => if y < x then 1 else 0) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, h5⟩ := gtCore_run H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem cs_slt : CoreSpec H (cmpCoreT armRq false .lt) (fun x y => if BitVec.slt x y then 1 else 0) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, h5⟩ := sltCore_run H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem cs_sgt : CoreSpec H (cmpCoreT armRq true .lt) (fun x y => if BitVec.slt y x then 1 else 0) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, h5⟩ := sgtCore_run H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem cs_eq : CoreSpec H (eqCoreT armRq) (fun x y => if x = y then 1 else 0) := eqCore_run H
theorem us_isZero : UnSpec H isZeroCoreA (fun x => if x = 0 then 1 else 0) := isZeroCore_run H
theorem us_not : UnSpec H notCoreA (~~~ ·) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, _, h5⟩ := notCore_run H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩

end specs

/-- The dispatcher: one node of any kind. -/
theorem node_run (H : Helpers) (hS : H.Spec) (hC : H.conv = armConv) (F : Fr) (idx : Expr → Nat) (done : List Expr) (e : Expr)
    (rest : List AInstr) (s : RS) (hI : Inv F idx done s) (hL : Lay F)
    (hkids : ∀ k ∈ exprKids e, k ∈ done) (hwf : ∀ k, e = .stackAt k → k < F.d)
    (hn : 32 * idx e < 2 ^ 64) (hnk : ∀ k ∈ exprKids e, 32 * idx k < 2 ^ 64) :
    ∃ s', run H (evalNodeT armFlush idx e ++ rest) s = run H rest s' ∧ NodeOut F idx e s s' := by
  cases e with
  | const v => exact node_const H F idx v rest s hI.sp hn
  | stackAt k => exact node_stackAt H F idx done k rest s hI hL (hwf k rfl) hn
  | add a b =>
    simp only [evalNodeT, armFlush_rq]
    exact node_bin H F idx done _ a b _ _ rest s (cs_add H) rfl hI
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | sub a b =>
    simp only [evalNodeT, armFlush_rq]
    exact node_bin H F idx done _ a b _ _ rest s (cs_sub H) rfl hI
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | and_ a b =>
    simp only [evalNodeT, armFlush_rq]
    exact node_bin H F idx done _ a b _ _ rest s (cs_and H) rfl hI
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | or_ a b =>
    simp only [evalNodeT, armFlush_rq]
    exact node_bin H F idx done _ a b _ _ rest s (cs_or H) rfl hI
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | xor_ a b =>
    simp only [evalNodeT, armFlush_rq]
    exact node_bin H F idx done _ a b _ _ rest s (cs_xor H) rfl hI
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | lt a b =>
    simp only [evalNodeT, armFlush_rq]
    exact node_bin H F idx done _ a b _ _ rest s (cs_lt H) rfl hI
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | gt a b =>
    simp only [evalNodeT, armFlush_rq]
    exact node_bin H F idx done _ a b _ _ rest s (cs_gt H) rfl hI
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | slt a b =>
    simp only [evalNodeT, armFlush_rq]
    exact node_bin H F idx done _ a b _ _ rest s (cs_slt H) rfl hI
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | sgt a b =>
    simp only [evalNodeT, armFlush_rq]
    exact node_bin H F idx done _ a b _ _ rest s (cs_sgt H) rfl hI
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | eq_ a b =>
    simp only [evalNodeT, armFlush_rq]
    exact node_bin H F idx done _ a b _ _ rest s (cs_eq H) rfl hI
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | isZero a =>
    simp only [evalNodeT]
    exact node_un H F idx done _ a _ _ rest s (us_isZero H) rfl hI
      (hkids a (by simp [exprKids])) hn (hnk a (by simp [exprKids]))
  | not_ a =>
    simp only [evalNodeT]
    exact node_un H F idx done _ a _ _ rest s (us_not H) rfl hI
      (hkids a (by simp [exprKids])) hn (hnk a (by simp [exprKids]))
  | mul a b =>
    simp only [evalNodeT, armFlush]
    exact node_call2 H hC F idx done _ a b "_eita_helper_mul" rest s (by decide) (by simp [hS.mul, eval]) hI hL
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | div a b =>
    simp only [evalNodeT, armFlush]
    exact node_call2 H hC F idx done _ a b "_eita_helper_div" rest s (by decide) (by simp [hS.div, eval]) hI hL
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | sdiv a b =>
    simp only [evalNodeT, armFlush]
    exact node_call2 H hC F idx done _ a b "_eita_helper_sdiv" rest s (by decide) (by simp [hS.sdiv, eval]) hI hL
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | mod_ a b =>
    simp only [evalNodeT, armFlush]
    exact node_call2 H hC F idx done _ a b "_eita_helper_mod" rest s (by decide) (by simp [hS.mod_, eval]) hI hL
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | smod_ a b =>
    simp only [evalNodeT, armFlush]
    exact node_call2 H hC F idx done _ a b "_eita_helper_smod" rest s (by decide) (by simp [hS.smod_, eval]) hI hL
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | signExtend a b =>
    simp only [evalNodeT, armFlush]
    exact node_call2 H hC F idx done _ a b "_eita_helper_signextend" rest s (by decide) (by simp [hS.signextend, eval]) hI hL
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | byte_ a b =>
    simp only [evalNodeT, armFlush]
    exact node_call2 H hC F idx done _ a b "_eita_helper_byte" rest s (by decide) (by simp [hS.byte_, eval]) hI hL
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | shl_ a b =>
    simp only [evalNodeT, armFlush]
    exact node_call2 H hC F idx done _ a b "_eita_helper_shl" rest s (by decide) (by simp [hS.shl, eval]) hI hL
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | shr_ a b =>
    simp only [evalNodeT, armFlush]
    exact node_call2 H hC F idx done _ a b "_eita_helper_shr" rest s (by decide) (by simp [hS.shr, eval]) hI hL
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | sar_ a b =>
    simp only [evalNodeT, armFlush]
    exact node_call2 H hC F idx done _ a b "_eita_helper_sar" rest s (by decide) (by simp [hS.sar, eval]) hI hL
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids]))
  | addmod a b n =>
    simp only [evalNodeT, armFlush]
    exact node_call3 H hC F idx done _ a b n "_eita_helper_addmod" rest s (by decide) (by simp [hS.addmod, eval]) hI hL
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) (hkids n (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids])) (hnk n (by simp [exprKids]))
  | mulmod a b n =>
    simp only [evalNodeT, armFlush]
    exact node_call3 H hC F idx done _ a b n "_eita_helper_mulmod" rest s (by decide) (by simp [hS.mulmod, eval]) hI hL
      (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) (hkids n (by simp [exprKids])) hn
      (hnk a (by simp [exprKids])) (hnk b (by simp [exprKids])) (hnk n (by simp [exprKids]))

/-! ## The DAG, slot by slot -/

/-- `Inv` only reads `done` through membership. -/
theorem Inv_of_mem_iff (F : Fr) (idx : Expr → Nat) (d1 d2 : List Expr) (s : RS)
    (h : ∀ x, x ∈ d1 ↔ x ∈ d2) (hI : Inv F idx d1 s) : Inv F idx d2 s :=
  ⟨hI.sp, hI.x23, hI.x24, hI.stack, fun e he => hI.slots e ((h e).mpr he)⟩

/-- Two slots' byte ranges are disjoint. -/
theorem slot_disj (F : Fr) (hL : Lay F) (i j : Nat) (hi : i < F.n) (hj : j < F.n) (hij : i ≠ j) :
    ∀ a < 32, ∀ b < 32, off (slotAddr F.fp i) a ≠ off (slotAddr F.fp j) b := by
  intro a ha b hb
  have := hL.fpOk
  simp only [slotAddr, off_off]
  exact off_ne_off F.fp _ _ (by omega) (by omega) (by omega)

/-- A slot's bytes are not the EVM stack's. -/
theorem slot_stack_disj (F : Fr) (hL : Lay F) (i k : Nat) (hi : i < F.n) (hk : k < F.d) :
    ∀ a < 32, ∀ b < 32, off (stackAddr F.base F.d k) b ≠ off (slotAddr F.fp i) a := by
  intro a ha b hb
  have := hL.dLe
  simp only [slotAddr, stackAddr, off_off]
  exact (hL.disj _ (by omega) _ (by omega)).symm

theorem slot_not_below (F : Fr) (hL : Lay F) (i : Nat) (hi : i < F.n) (a : Nat) (ha : a < 32) :
    belowSp F.fp (off (slotAddr F.fp i) a) = false := by
  simp only [slotAddr, off_off]
  exact belowSp_off_false F.fp _ (by have := hL.fpOk; omega)

/-- After a node, the invariant extends to it. -/
theorem Inv_step (F : Fr) (idx : Expr → Nat) (done : List Expr) (e : Expr) (s s' : RS)
    (hL : Lay F) (hI : Inv F idx done s) (hO : NodeOut F idx e s s')
    (hn : idx e < F.n) (hnd : ∀ e' ∈ done, idx e' < F.n)
    (hdist : ∀ e' ∈ done, idx e' = idx e → eval e' F.es = eval e F.es) :
    Inv F idx (e :: done) s' where
  sp := by rw [hO.sp, hI.sp]
  x23 := by rw [hO.regs .x23 rfl, hI.x23]
  x24 := by rw [hO.regs .x24 rfl, hI.x24]
  stack := by
    intro k hk
    rw [← hI.stack k hk]
    apply ld256_eq_of_eq_on
    intro b hb
    apply hO.mem
    · intro a ha; exact slot_stack_disj F hL (idx e) k hn hk a ha b hb
    · simp only [stackAddr, off_off]; exact hL.stackOut _ (by have := hL.dLe; omega)
  slots := by
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact hO.slot
    · by_cases hidx : idx e' = idx e
      · rw [hidx, hO.slot, hdist e' he' hidx]
      · rw [← hI.slots e' he']
        apply ld256_eq_of_eq_on
        intro b hb
        apply hO.mem
        · intro a ha; exact slot_disj F hL (idx e') (idx e) (hnd e' he') hn hidx b hb a ha
        · exact slot_not_below F hL (idx e') (hnd e' he') b hb

/-- The slot list, well formed for in-order evaluation. -/
structure WFSlots (F : Fr) (idx : Expr → Nat) (slots : List Expr) : Prop where
  kids    : ∀ i (h : i < slots.length), ∀ k ∈ exprKids slots[i], k ∈ slots.take i
  idxLt   : ∀ e ∈ slots, idx e < F.n
  dist    : ∀ e e', e ∈ slots → e' ∈ slots → idx e = idx e' → e = e'
  stackLt : ∀ e ∈ slots, ∀ k, e = .stackAt k → k < F.d

/-- What the whole DAG evaluation leaves: the frame base, the kept registers,
    the memory outside the frame and the helpers' window. -/
structure DagOut (F : Fr) (s s' : RS) : Prop where
  sp   : s'.sp = s.sp
  regs : ∀ r, keep r = true → s'.regs r = s.regs r
  mem  : ∀ x, (∀ i < 32 * F.n, x ≠ off F.fp i) → belowSp F.fp x = false → s'.mem x = s.mem x

theorem DagOut.refl (F : Fr) (s : RS) : DagOut F s s := ⟨rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem DagOut.trans (F : Fr) (s1 s2 s3 : RS) (a : DagOut F s1 s2) (b : DagOut F s2 s3) : DagOut F s1 s3 :=
  ⟨by rw [b.sp, a.sp], fun r h => by rw [b.regs r h, a.regs r h], fun x h1 h2 => by rw [b.mem x h1 h2, a.mem x h1 h2]⟩

theorem DagOut.of_node (F : Fr) (idx : Expr → Nat) (e : Expr) (s s' : RS) (hn : idx e < F.n)
    (hO : NodeOut F idx e s s') : DagOut F s s' :=
  ⟨hO.sp, hO.regs, fun x hx hw => hO.mem x (fun i hi => by
      simp only [slotAddr, off_off]; exact hx _ (by omega)) hw⟩

/-- The loop: the suffix `suf` evaluated after the prefix `pre`. -/
theorem dag_loop (H : Helpers) (hS : H.Spec) (hC : H.conv = armConv) (F : Fr) (idx : Expr → Nat) (rest : List AInstr) (hL : Lay F) :
    ∀ (suf pre : List Expr) (s : RS), WFSlots F idx (pre ++ suf) → Inv F idx pre s →
      ∃ s', run H (suf.flatMap (evalNodeT armFlush idx) ++ rest) s = run H rest s' ∧
        Inv F idx (pre ++ suf) s' ∧ DagOut F s s' := by
  intro suf
  induction suf with
  | nil => intro pre s _ hI; exact ⟨s, by simp, by simpa using hI, DagOut.refl F s⟩
  | cons e suf ih =>
    intro pre s hW hI
    have hlen : pre.length < (pre ++ e :: suf).length := by simp
    have hget : (pre ++ e :: suf)[pre.length] = e := by simp
    have hkids : ∀ k ∈ exprKids e, k ∈ pre := by
      intro k hk
      have h := hW.kids pre.length hlen
      rw [hget] at h
      simpa using h k hk
    have he : e ∈ pre ++ e :: suf := by simp
    have hn : idx e < F.n := hW.idxLt e he
    have h32 : 32 * idx e < 2 ^ 64 := by have := hL.fpOk; omega
    obtain ⟨s1, h1, hO⟩ := node_run H hS hC F idx pre e _ s hI hL hkids (hW.stackLt e he) h32
      (fun k hk => by have := hW.idxLt k (by simp [hkids k hk]); have := hL.fpOk; omega)
    have hI1 : Inv F idx (pre ++ [e]) s1 :=
      Inv_of_mem_iff F idx (e :: pre) _ s1 (by intro x; simp [or_comm])
        (Inv_step F idx pre e s s1 hL hI hO hn (fun e' he' => hW.idxLt e' (by simp [he']))
          (fun e' he' hidx => by rw [hW.dist e' e (by simp [he']) he hidx]))
    have hW1 : WFSlots F idx ((pre ++ [e]) ++ suf) := by rw [List.append_assoc]; simpa using hW
    obtain ⟨s', h2, hI', hD⟩ := ih (pre ++ [e]) s1 hW1 hI1
    refine ⟨s', ?_, by simpa using hI', DagOut.trans F s s1 s' (DagOut.of_node F idx e s s1 hn hO) hD⟩
    rw [List.flatMap_cons, List.append_assoc, h1, h2]

/-! ## The exit prefix -/

/-- `add x14, x23, #k ; add x14, x24, x14, lsl #5`. -/
theorem exit_addr_add (base : BitVec 64) (d k : Nat) (h : d + k < 2 ^ 32) :
    base + ((BitVec.ofNat 64 d + BitVec.ofNat 64 k) <<< 5) = off base (32 * (d + k)) := by
  simp only [off]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : d + k < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 32 * (d + k) < 2 ^ 64),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by rw [show (2 : Nat) ^ 5 = 32 from rfl]; omega)]
  rw [show (2 : Nat) ^ 5 = 32 from rfl]; omega

/-- `sub x14, x23, #k ; add x14, x24, x14, lsl #5`. -/
theorem exit_addr_sub (base : BitVec 64) (d k : Nat) (hk : k ≤ d) (hd : d < 2 ^ 32) :
    base + ((BitVec.ofNat 64 d - BitVec.ofNat 64 k) <<< 5) = off base (32 * (d - k)) := by
  simp only [off]
  congr 1
  have hle : BitVec.ofNat 64 k ≤ BitVec.ofNat 64 d := by
    rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_sub_of_le hle]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 32 * (d - k) < 2 ^ 64), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by rw [show (2 : Nat) ^ 5 = 32 from rfl]; omega)]
  rw [show (2 : Nat) ^ 5 = 32 from rfl]; omega

/-- The depth after the region. -/
def newDepth (d len c : Nat) : Nat := d + len - c

/-- One exit store: expression `e` (in its slot) to position `m` of the new stack. -/
theorem exit_one_run (H : Helpers) (F : Fr) (hL : Lay F) (idx : Expr → Nat) (e : Expr) (m len c : Nat)
    (rest : List AInstr) (s : RS)
    (hsp : s.sp = F.fp) (h23 : s.regs .x23 = BitVec.ofNat 64 F.d) (h24 : s.regs .x24 = F.base)
    (hslot : ld256 s.mem (slotAddr F.fp (idx e)) = eval e F.es)
    (hm : m < len) (hc : c ≤ F.d) (hd' : newDepth F.d len c ≤ 1024) (hn : 32 * idx e < 2 ^ 64) :
    ∃ s', run H (exitOneT armFlush idx ((len : Int) - c) e m ++ rest) s = run H rest s' ∧
      s'.mem = st256 s.mem (stackAddr F.base (newDepth F.d len c) m) (eval e F.es) ∧
      s'.sp = s.sp ∧ (∀ r, keep r = true → s'.regs r = s.regs r) := by
  simp only [exitOneT, List.append_assoc]
  obtain ⟨s1, h1, hv1, hsp1, hmem1, _, hregs1⟩ := loadSlot_x6_run H (idx e) hn _ s
  rw [show loadSlotT armFlush .x6 (idx e) = loadSlotA .x6 (idx e) from rfl, h1]
  have h23' : s1.regs .x23 = BitVec.ofNat 64 F.d := by
    rw [hregs1 _ (by decide) (by decide) (by decide) (by decide) (by decide), h23]
  have h24' : s1.regs .x24 = F.base := by
    rw [hregs1 _ (by decide) (by decide) (by decide) (by decide) (by decide), h24]
  have hdOk := hL.dOk
  have hlhs1 : lhs s1 = eval e F.es := by rw [hv1, hsp, hslot]
  have hd2 : F.d + len - c ≤ 1024 := hd'
  have hlen : len ≤ 1024 := by omega
  -- the two `stp`s, once x14 holds the address
  have tail : ∀ (s2 : RS), s2.regs .x14 = stackAddr F.base (newDepth F.d len c) m → s2.mem = s.mem →
      lhs s2 = eval e F.es → s2.sp = s.sp → (∀ r, keep r = true → s2.regs r = s.regs r) →
      ∃ s', run H ([AInstr.stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16] ++ rest) s2 = run H rest s' ∧
        s'.mem = st256 s.mem (stackAddr F.base (newDepth F.d len c) m) (eval e F.es) ∧
        s'.sp = s.sp ∧ (∀ r, keep r = true → s'.regs r = s.regs r) := by
    intro s2 hx14 hmem2 hl2 hsp2 hk2
    rw [List.cons_append, run_cons_step H _ _ _ _ (ctrl_stpOff ..) (step_stpOff ..), List.singleton_append,
        run_cons_step H _ _ _ _ (ctrl_stpOff ..) (step_stpOff ..)]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [AsmRun.store64_mem, AsmRun.store64_regs, hx14, Nat.reduceAdd, off_zero]
      rw [st64_four_eq_st256, hmem2]
      exact congrArg _ hl2
    · simp only [AsmRun.store64_sp, hsp2]
    · intro r hr; simp only [AsmRun.store64_regs]; exact hk2 r hr
  -- after the address computation, the register file is s1 with x14 replaced
  have after : ∀ v : BitVec 64, ∀ s', (s' = (s1.set .x14 v).set .x14 ((s1.set .x14 v).regs .x24 + ((s1.set .x14 v).regs .x14 <<< 5))) →
      s'.regs .x14 = F.base + (v <<< 5) ∧ s'.mem = s.mem ∧ lhs s' = eval e F.es ∧ s'.sp = s.sp ∧
      (∀ r, keep r = true → s'.regs r = s.regs r) := by
    intro v s' hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [AsmRun.set_regs, reduceCtorEq, ite_true, ite_false, h24']
    · simp only [AsmRun.set_mem, hmem1]
    · simp only [lhs, AsmRun.set_regs, reduceCtorEq, ite_false]; exact hlhs1
    · simp only [AsmRun.set_sp, hsp1]
    · intro r hr
      obtain ⟨_, _, _, _, h6, h7, h8, h9, _, _, _, _, h14, _, _, _⟩ := keep_ne r hr
      rw [set_regs_ne _ _ _ _ h14, set_regs_ne _ _ _ _ h14, hregs1 r h6 h7 h8 h9 h14]
  by_cases hk : ((len : Int) - c) - 1 - m ≥ 0
  · rw [if_pos hk, List.singleton_append, run_cons_step H _ _ _ _ (ctrl_addImm ..) (step_addImm ..),
        List.cons_append, run_cons_step H _ _ _ _ (ctrl_addLsl5 ..) (step_addLsl5 ..)]
    obtain ⟨a1, a2, a3, a4, a5⟩ := after _ _ rfl
    apply tail _ _ a2 a3 a4 a5
    rw [a1, h23', exit_addr_add F.base F.d _ (by omega)]
    simp only [stackAddr]
    congr 2
    simp only [newDepth]; omega
  · rw [if_neg hk, List.singleton_append, run_cons_step H _ _ _ _ (ctrl_subImm ..) (step_subImm ..),
        List.cons_append, run_cons_step H _ _ _ _ (ctrl_addLsl5 ..) (step_addLsl5 ..)]
    obtain ⟨a1, a2, a3, a4, a5⟩ := after _ _ rfl
    apply tail _ _ a2 a3 a4 a5
    rw [a1, h23', exit_addr_sub F.base F.d _ (by omega) hdOk]
    simp only [stackAddr]
    congr 2
    simp only [newDepth]; omega

/-- The invariant across the exit stores: the frame and the slots as before,
    the UNCONSUMED part of the entry stack intact. -/
structure ExitInv (F : Fr) (idx : Expr → Nat) (slots : List Expr) (c : Nat) (s : RS) : Prop where
  sp    : s.sp = F.fp
  x23   : s.regs .x23 = BitVec.ofNat 64 F.d
  x24   : s.regs .x24 = F.base
  slots : ∀ e ∈ slots, ld256 s.mem (slotAddr F.fp (idx e)) = eval e F.es
  keepStack : ∀ k, c ≤ k → k < F.d → ld256 s.mem (stackAddr F.base F.d k) = F.es.getD k 0

theorem ExitInv.of_Inv (F : Fr) (idx : Expr → Nat) (slots : List Expr) (c : Nat) (s : RS)
    (hI : Inv F idx slots s) : ExitInv F idx slots c s :=
  ⟨hI.sp, hI.x23, hI.x24, hI.slots, fun k _ hk => hI.stack k hk⟩

/-- Two positions of a stack of depth `d' ≤ 1024` have disjoint bytes. -/
theorem stack_pos_disj (base : BitVec 64) (_hb : base.toNat + 32 * 1024 < 2 ^ 64) (d' i j : Nat)
    (hd : d' ≤ 1024) (hi : i < d') (hj : j < d') (hij : i ≠ j) :
    ∀ a < 32, ∀ b < 32, off (stackAddr base d' i) a ≠ off (stackAddr base d' j) b := by
  intro a ha b hb'
  simp only [stackAddr, off_off]
  exact off_ne_off base _ _ (by omega) (by omega) (by omega)

/-- An entry position `k` (depth `d`) and a new position `m` (depth `d'`) coincide
    iff `k + (d' - d) = m`. -/
theorem stackAddr_shift (base : BitVec 64) (d d' k m : Nat) (_hk : k < d) (_hm : m < d')
    (h : d - 1 - k = d' - 1 - m) : stackAddr base d k = stackAddr base d' m := by
  simp only [stackAddr, h]

/-- The exit stores, from position `m0` on. -/
theorem exit_loop (H : Helpers) (F : Fr) (hL : Lay F) (idx : Expr → Nat) (slots : List Expr) (c len : Nat)
    (rest : List AInstr) (hc : c ≤ F.d) (hd' : newDepth F.d len c ≤ 1024) (hidx : ∀ e ∈ slots, idx e < F.n) :
    ∀ (suf : List Expr) (m0 : Nat) (s : RS), m0 + suf.length = len → (∀ e ∈ suf, e ∈ slots) →
      (∀ e ∈ suf, 32 * idx e < 2 ^ 64) → ExitInv F idx slots c s →
      ∃ s', run H ((suf.zipIdx m0).flatMap (fun (e, m) => exitOneT armFlush idx ((len : Int) - c) e m) ++ rest) s =
              run H rest s' ∧
        ExitInv F idx slots c s' ∧
        (∀ i (h : i < suf.length), ld256 s'.mem (stackAddr F.base (newDepth F.d len c) (m0 + i)) = eval suf[i] F.es) ∧
        s'.sp = s.sp ∧ (∀ r, keep r = true → s'.regs r = s.regs r) ∧
        (∀ x, (∀ m, m0 ≤ m → m < m0 + suf.length → ∀ b < 32, x ≠ off (stackAddr F.base (newDepth F.d len c) m) b) →
          s'.mem x = s.mem x) := by
  intro suf
  induction suf with
  | nil =>
    intro m0 s _ _ _ hX
    exact ⟨s, by simp, hX, fun i h => by simp at h, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons e suf ih =>
    intro m0 s hlen hmem hn hX
    have hd2 : F.d + len - c ≤ 1024 := hd'
    have hlen' : m0 + suf.length + 1 = len := by simp at hlen; omega
    have hm0 : m0 < len := by omega
    obtain ⟨s1, h1, hmem1, hsp1, hregs1⟩ := exit_one_run H F hL idx e m0 len c _ s hX.sp hX.x23 hX.x24
      (hX.slots e (hmem e (by simp))) hm0 hc hd' (hn e (by simp))
    have hpos : newDepth F.d len c - 1 - m0 < 1024 := by simp only [newDepth]; omega
    -- the written position is in the arena, away from the frame and the unconsumed entries
    have hX1 : ExitInv F idx slots c s1 := by
      refine ⟨by rw [hsp1, hX.sp], by rw [hregs1 .x23 rfl, hX.x23], by rw [hregs1 .x24 rfl, hX.x24], ?_, ?_⟩
      · intro e' he'
        rw [← hX.slots e' he', hmem1]
        apply ld256_eq_of_eq_on
        intro b hb
        apply st256_out
        intro a ha
        simp only [slotAddr, stackAddr, off_off]
        have := hidx e' he'
        exact hL.disj _ (by omega) _ (by omega)
      · intro k hck hkd
        rw [← hX.keepStack k hck hkd, hmem1]
        apply ld256_eq_of_eq_on
        intro b hb
        apply st256_out
        intro a ha
        simp only [stackAddr, off_off]
        have := hL.baseOk
        exact off_ne_off F.base _ _ (by have := hL.dLe; omega) (by omega) (by simp only [newDepth]; omega)
    obtain ⟨s', h2, hX', hstored, hsp', hregs', hmem'⟩ := ih (m0 + 1) s1 (by simp at hlen ⊢; omega)
      (fun e' he' => hmem e' (by simp [he'])) (fun e' he' => hn e' (by simp [he'])) hX1
    refine ⟨s', ?_, hX', ?_, by rw [hsp', hsp1], fun r hr => by rw [hregs' r hr, hregs1 r hr], ?_⟩
    · rw [List.zipIdx_cons, List.flatMap_cons, List.append_assoc, h1, h2]
    · intro i hi
      cases i with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [← ld256_st256_same s.mem (stackAddr F.base (newDepth F.d len c) m0) (eval e F.es), ← hmem1]
        apply ld256_eq_of_eq_on
        intro b hb
        apply hmem'
        intro m hm1 hm2 a ha
        have hd3 : len ≤ newDepth F.d len c := by simp only [newDepth]; omega
        exact stack_pos_disj F.base hL.baseOk _ m0 m hd' (by omega) (by omega) (by omega) b hb a ha
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [show m0 + (i + 1) = m0 + 1 + i by omega]
        exact hstored i (by simpa using hi)
    · intro x hx
      rw [hmem' x (fun m hm1 hm2 b hb => hx m (by omega) (by simp; omega) b hb), hmem1]
      apply st256_out
      intro a ha
      exact hx m0 (Nat.le_refl _) (by simp) a ha

/-! ## Frame open and close -/

/-- `frameOpen n`: fp/lr saved at sp-16, sp lowered by 16 + 32n. -/
theorem frameOpen_run (H : Helpers) (n : Nat) (hn : 32 * n < 2 ^ 64) (rest : List AInstr) (s : RS) :
    ∃ s', run H (armFlush.frameOpen n ++ rest) s = run H rest s' ∧
      s'.sp = s.sp - BitVec.ofNat 64 16 - BitVec.ofNat 64 (32 * n) ∧
      s'.mem = st64 (st64 s.mem (s.sp - BitVec.ofNat 64 16) (s.regs .x29))
                    (off (s.sp - BitVec.ofNat 64 16) 8) (s.regs .x30) ∧
      s'.flags = s.flags ∧ (∀ r, r ≠ .x15 → s'.regs r = s.regs r) := by
  simp only [armFlush, List.cons_append, List.nil_append]
  rw [run_cons_step H _ _ _ _ (ctrl_stpFpLr) (step_stpFpLr _)]
  split
  · rw [List.singleton_append, run_cons_step H _ _ _ _ (ctrl_spSub _) (step_spSub _ _)]
    refine ⟨_, rfl, rfl, rfl, rfl, fun r _ => rfl⟩
  · rw [movImmA, List.append_assoc, movImmInstrs_run H _ _ hn, List.singleton_append,
        run_cons_step H _ _ _ _ (ctrl_spSubReg _) (step_spSubReg _ _)]
    refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
    · simp [RS.set]
    · intro r h15; simp [RS.set, h15]

/-- `frameClose n`: sp raised by 32n, fp/lr reloaded from the top of the frame, sp raised by 16. -/
theorem frameClose_run (H : Helpers) (n : Nat) (hn : 32 * n < 2 ^ 64) (rest : List AInstr) (s : RS) :
    ∃ s', run H (armFlush.frameClose n ++ rest) s = run H rest s' ∧
      s'.sp = off (s.sp + BitVec.ofNat 64 (32 * n)) 16 ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      s'.regs .x29 = ld64 s.mem (s.sp + BitVec.ofNat 64 (32 * n)) ∧
      s'.regs .x30 = ld64 s.mem (off (s.sp + BitVec.ofNat 64 (32 * n)) 8) ∧
      (∀ r, r ≠ .x15 → r ≠ .x29 → r ≠ .x30 → s'.regs r = s.regs r) := by
  simp only [armFlush, List.append_assoc]
  split
  · rw [List.singleton_append, run_cons_step H _ _ _ _ (ctrl_spAdd _) (step_spAdd _ _), List.singleton_append,
        run_cons_step H _ _ _ _ (ctrl_ldpFpLr) (step_ldpFpLr _)]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [RS.set]
    · simp [RS.set]
    · intro r _ h29 h30; simp [RS.set, h29, h30]
  · rw [movImmA, List.append_assoc, movImmInstrs_run H _ _ hn, List.singleton_append,
        run_cons_step H _ _ _ _ (ctrl_spAddReg _) (step_spAddReg _ _), List.singleton_append,
        run_cons_step H _ _ _ _ (ctrl_ldpFpLr) (step_ldpFpLr _)]
    refine ⟨_, rfl, ?_, rfl, rfl, ?_, ?_, ?_⟩
    · simp [RS.set]
    · simp [RS.set]
    · simp [RS.set]
    · intro r h15 h29 h30; simp [RS.set, h15, h29, h30]

/-! ## Depth update and cache reload -/

theorem depthUpdate_run (H : Helpers) (net : Int) (d : Nat) (hd : (d : Int) + net ≥ 0)
    (hw : d + net.toNat < 2 ^ 64) (rest : List AInstr) (s : RS) (h23 : s.regs .x23 = BitVec.ofNat 64 d) :
    ∃ s', run H (depthUpdate net ++ rest) s = run H rest s' ∧
      s'.regs .x23 = BitVec.ofNat 64 ((d : Int) + net).toNat ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.flags = s.flags ∧ (∀ r, r ≠ .x23 → s'.regs r = s.regs r) := by
  simp only [depthUpdate]
  split
  · rw [List.singleton_append, run_cons_step H _ _ _ _ (ctrl_addImm ..) (step_addImm ..)]
    refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r h => by simp [RS.set, h]⟩
    simp only [AsmRun.set_regs, ite_true, h23]
    rw [← BitVec.ofNat_add]
    congr 1; omega
  · split
    · rw [List.singleton_append, run_cons_step H _ _ _ _ (ctrl_subImm ..) (step_subImm ..)]
      refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r h => by simp [RS.set, h]⟩
      simp only [AsmRun.set_regs, ite_true, h23]
      have hk : (-net).toNat ≤ d := by omega
      have hle : BitVec.ofNat 64 (-net).toNat ≤ BitVec.ofNat 64 d := by
        rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hk
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le hle]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [List.nil_append]
      refine ⟨s, rfl, ?_, rfl, rfl, rfl, fun _ _ => rfl⟩
      rw [h23]; congr 1; omega

/-- `cmp x23, #k ; b.lt` on a small depth: taken iff `d < k`. -/
theorem lt_small (d k : Nat) (hd : d < 2 ^ 32) (hk : k < 2 ^ 32) :
    bcHolds .lt (subFlags (BitVec.ofNat 64 d) (BitVec.ofNat 64 k)) = decide (d < k) := by
  simp only [bcHolds, subFlags]
  have ha : (BitVec.ofNat 64 d).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_false (by omega)
  have hb : (BitVec.ofNat 64 k).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_false (by omega)
  by_cases h : d < k
  · have hr : (BitVec.ofNat 64 d - BitVec.ofNat 64 k).msb = true := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega)]
      exact decide_eq_true (by omega)
    simp [ha, hb, hr, h]
  · have hr : (BitVec.ofNat 64 d - BitVec.ofNat 64 k).msb = false := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
          show 2 ^ 64 - k + d = (d - k) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      exact decide_eq_false (by omega)
    simp [ha, hb, hr, h]

/-- One guarded reload into tos: `cmp x23, #1 ; b.lt 8f ; sub x14, x23, #1 ;
    add x14, x24, x14, lsl #5 ; ldp ; ldp ; 8:`. -/
theorem reload_tos_run (H : Helpers) (base : BitVec 64) (d : Nat) (hd : d < 2 ^ 32)
    (rest : List AInstr) (s : RS) (h23 : s.regs .x23 = BitVec.ofNat 64 d) (h24 : s.regs .x24 = base) :
    ∃ s', run H ([AInstr.cmpImm .x23 1, .bcLbl .lt "8f", .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14,
                   .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16, .label "8"] ++ rest) s = run H rest s' ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (1 ≤ d → ofLimbs (s'.regs .x6) (s'.regs .x7) (s'.regs .x8) (s'.regs .x9) =
        ld256 s.mem (stackAddr base d 0)) ∧
      (d < 1 → ∀ r, r ≠ .x14 → s'.regs r = s.regs r) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → s'.regs r = s.regs r) := by
  rw [List.cons_append, run_cons_step H _ _ _ _ (ctrl_cmpImm ..) (step_cmpImm ..), List.cons_append,
      run_cons_bcLbl]
  simp only [AsmRun.withFlags_flags, h23, lt_small d 1 hd (by decide)]
  by_cases h : d < 1
  · rw [decide_eq_true h, if_pos rfl]
    simp only [AsmRun.skipTo, List.cons_append, List.nil_append]
    rw [if_pos (by decide), run_cons_label]
    exact ⟨_, rfl, rfl, rfl, fun hkd => absurd hkd (by omega), fun _ r _ => rfl, fun r _ _ _ _ _ => rfl⟩
  · rw [decide_eq_false h, if_neg (by simp)]
    simp only [List.cons_append, List.nil_append]
    rw [run_cons_step H _ _ _ _ (ctrl_subImm ..) (step_subImm ..),
        run_cons_step H _ _ _ _ (ctrl_addLsl5 ..) (step_addLsl5 ..),
        run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..),
        run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..), run_cons_label]
    refine ⟨_, rfl, rfl, rfl, ?_, fun hdk => absurd hdk h, ?_⟩
    · intro hkd
      simp only [AsmRun.withFlags_regs, AsmRun.withFlags_mem, AsmRun.set_regs, AsmRun.set_mem, reduceCtorEq,
                 ite_true, ite_false, Nat.reduceAdd, h23, h24, exit_addr_sub base d 1 hkd hd, BitVec.add_zero]
      rw [ld256_eq_ofLimbs]
      rfl
    · intro r ha hb hc he h14
      simp [RS.set, ha, hb, hc, he, h14]

/-- One guarded reload into nos: `cmp x23, #2 ; b.lt 9f ; sub x14, x23, #2 ;
    add x14, x24, x14, lsl #5 ; ldp ; ldp ; 9:`. -/
theorem reload_nos_run (H : Helpers) (base : BitVec 64) (d : Nat) (hd : d < 2 ^ 32)
    (rest : List AInstr) (s : RS) (h23 : s.regs .x23 = BitVec.ofNat 64 d) (h24 : s.regs .x24 = base) :
    ∃ s', run H ([AInstr.cmpImm .x23 2, .bcLbl .lt "9f", .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14,
                   .ldpOff .x10 .x11 .x14 0, .ldpOff .x12 .x13 .x14 16, .label "9"] ++ rest) s = run H rest s' ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (2 ≤ d → ofLimbs (s'.regs .x10) (s'.regs .x11) (s'.regs .x12) (s'.regs .x13) =
        ld256 s.mem (stackAddr base d 1)) ∧
      (d < 2 → ∀ r, r ≠ .x14 → s'.regs r = s.regs r) ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → s'.regs r = s.regs r) := by
  rw [List.cons_append, run_cons_step H _ _ _ _ (ctrl_cmpImm ..) (step_cmpImm ..), List.cons_append,
      run_cons_bcLbl]
  simp only [AsmRun.withFlags_flags, h23, lt_small d 2 hd (by decide)]
  by_cases h : d < 2
  · rw [decide_eq_true h, if_pos rfl]
    simp only [AsmRun.skipTo, List.cons_append, List.nil_append]
    rw [if_pos (by decide), run_cons_label]
    exact ⟨_, rfl, rfl, rfl, fun hkd => absurd hkd (by omega), fun _ r _ => rfl, fun r _ _ _ _ _ => rfl⟩
  · rw [decide_eq_false h, if_neg (by simp)]
    simp only [List.cons_append, List.nil_append]
    rw [run_cons_step H _ _ _ _ (ctrl_subImm ..) (step_subImm ..),
        run_cons_step H _ _ _ _ (ctrl_addLsl5 ..) (step_addLsl5 ..),
        run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..),
        run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..), run_cons_label]
    refine ⟨_, rfl, rfl, rfl, ?_, fun hdk => absurd hdk h, ?_⟩
    · intro hkd
      simp only [AsmRun.withFlags_regs, AsmRun.withFlags_mem, AsmRun.set_regs, AsmRun.set_mem, reduceCtorEq,
                 ite_true, ite_false, Nat.reduceAdd, h23, h24, exit_addr_sub base d 2 hkd hd, BitVec.add_zero]
      rw [ld256_eq_ofLimbs]
      rfl
    · intro r ha hb hc he h14
      simp [RS.set, ha, hb, hc, he, h14]

/-- The cache reload: TOS if the depth is ≥ 1, NOS if ≥ 2, from the stack in memory. -/
theorem cacheReload_run (H : Helpers) (base : BitVec 64) (d : Nat) (hd : d < 2 ^ 32) (rest : List AInstr) (s : RS)
    (h23 : s.regs .x23 = BitVec.ofNat 64 d) (h24 : s.regs .x24 = base) :
    ∃ s', run H (armCacheReload ++ rest) s = run H rest s' ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (1 ≤ d → lhs s' = ld256 s.mem (stackAddr base d 0)) ∧
      (2 ≤ d → rhs armRq s' = ld256 s.mem (stackAddr base d 1)) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 →
        s'.regs r = s.regs r) := by
  have split : armCacheReload ++ rest =
      [AInstr.cmpImm .x23 1, .bcLbl .lt "8f", .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14,
       .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16, .label "8"] ++
      ([AInstr.cmpImm .x23 2, .bcLbl .lt "9f", .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14,
        .ldpOff .x10 .x11 .x14 0, .ldpOff .x12 .x13 .x14 16, .label "9"] ++ rest) := rfl
  rw [split]
  obtain ⟨s1, h1, hsp1, hmem1, htos, hsmall1, hregs1⟩ := reload_tos_run H base d hd _ s h23 h24
  rw [h1]
  have h23' : s1.regs .x23 = BitVec.ofNat 64 d := by
    rw [hregs1 _ (by decide) (by decide) (by decide) (by decide) (by decide), h23]
  have h24' : s1.regs .x24 = base := by
    rw [hregs1 _ (by decide) (by decide) (by decide) (by decide) (by decide), h24]
  obtain ⟨s2, h2, hsp2, hmem2, hnos, hsmall2, hregs2⟩ := reload_nos_run H base d hd rest s1 h23' h24'
  refine ⟨s2, h2, by rw [hsp2, hsp1], by rw [hmem2, hmem1], ?_, ?_, ?_⟩
  · intro h1d
    simp only [lhs]
    rw [hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact htos h1d
  · intro h2d
    simp only [rhs, armRq]
    rw [hmem1] at hnos
    exact hnos h2d
  · intro r h6 h7 h8 h9 h10 h11 h12 h13 h14
    rw [hregs2 r h10 h11 h12 h13 h14, hregs1 r h6 h7 h8 h9 h14]

/-! ## Depth checks -/

open Evm.CL.ARM64.ChunkGasSem (hs_subFlags) in
/-- `cmp x23, #need ; b.hs 8f ; b _eita_stack_underflow ; 8:`. -/
theorem underflowCheck_run (H : Helpers) (need d : Nat) (hd : d < 2 ^ 32) (hneed : need < 2 ^ 32)
    (rest : List AInstr) (s : RS) (h23 : s.regs .x23 = BitVec.ofNat 64 d) :
    run H (AInstr.cmpImm .x23 need :: .bcLbl .hs "8f" :: .bFar "_eita_stack_underflow" :: .label "8" :: rest) s =
      if need ≤ d then run H rest (s.withFlags (subFlags (BitVec.ofNat 64 d) (BitVec.ofNat 64 need)))
      else .fault "_eita_stack_underflow" (s.withFlags (subFlags (BitVec.ofNat 64 d) (BitVec.ofNat 64 need))) := by
  rw [run_cons_step H _ _ _ _ (ctrl_cmpImm ..) (step_cmpImm ..), run_cons_bcLbl]
  simp only [AsmRun.withFlags_flags, h23, hs_subFlags _ _ (by omega : need < 2 ^ 64), BitVec.toNat_ofNat,
             Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
  by_cases h : need ≤ d
  · rw [decide_eq_true h, if_pos rfl, if_pos h]
    simp only [AsmRun.skipTo]
    rw [if_pos (by decide), run_cons_label]
  · rw [decide_eq_false h, if_neg (by simp), if_neg h, run_cons_bFar]

/-- `cmp x23, #lim ; b.lo 9f ; b _eita_stack_overflow ; 9:` -/
theorem overflowCheck_run (H : Helpers) (lim d : Nat) (hd : d < 2 ^ 32) (hlim : lim < 2 ^ 32)
    (rest : List AInstr) (s : RS) (h23 : s.regs .x23 = BitVec.ofNat 64 d) :
    run H (AInstr.cmpImm .x23 lim :: .bcLbl .lo "9f" :: .bFar "_eita_stack_overflow" :: .label "9" :: rest) s =
      if d < lim then run H rest (s.withFlags (subFlags (BitVec.ofNat 64 d) (BitVec.ofNat 64 lim)))
      else .fault "_eita_stack_overflow" (s.withFlags (subFlags (BitVec.ofNat 64 d) (BitVec.ofNat 64 lim))) := by
  rw [run_cons_step H _ _ _ _ (ctrl_cmpImm ..) (step_cmpImm ..), run_cons_bcLbl]
  have hlo : bcHolds .lo (subFlags (BitVec.ofNat 64 d) (BitVec.ofNat 64 lim)) = decide (d < lim) := by
    simp only [bcHolds, subFlags, BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64),
               Nat.mod_eq_of_lt (by omega : lim < 2 ^ 64)]
    cases Nat.lt_or_ge d lim with
    | inl h => simp [h, Nat.not_le.mpr h]
    | inr h => simp [h, Nat.not_lt.mpr h]
  simp only [AsmRun.withFlags_flags, h23, hlo]
  by_cases h : d < lim
  · rw [decide_eq_true h, if_pos rfl, if_pos h]
    simp only [AsmRun.skipTo]
    rw [if_pos (by decide), run_cons_label]
  · rw [decide_eq_false h, if_neg (by simp), if_neg h, run_cons_bFar]

/-! ## The new stack -/

/-- The region's stack after the flush: `SymStack.denote` written out. -/
def newStack (exprs : List Expr) (es : List Evm.U256) (c : Nat) : List Evm.U256 :=
  exprs.map (eval · es) ++ es.drop c

theorem newStack_eq_denote (exprs : List Expr) (es : List Evm.U256) (c : Nat) :
    newStack exprs es c = Evm.IR.SymExpr.SymStack.denote ⟨exprs, c⟩ es := rfl

theorem newStack_length (exprs : List Expr) (es : List Evm.U256) (c : Nat) (hc : c ≤ es.length) :
    (newStack exprs es c).length = es.length + exprs.length - c := by
  simp [newStack]; omega

/-- Stored positions plus kept entries make the new stack, position by position. -/
theorem newStack_of_mem (base : BitVec 64) (m : Mem) (exprs : List Expr) (es : List Evm.U256) (d c : Nat)
    (_hes : es.length = d) (_hc : c ≤ d)
    (hstored : ∀ i (h : i < exprs.length), ld256 m (stackAddr base (newDepth d exprs.length c) i) = eval exprs[i] es)
    (hkept : ∀ k, c ≤ k → k < d → ld256 m (stackAddr base d k) = es.getD k 0) :
    ∀ j < newDepth d exprs.length c, ld256 m (stackAddr base (newDepth d exprs.length c) j) =
      (newStack exprs es c).getD j 0 := by
  intro j hj
  simp only [newDepth] at hj
  by_cases hjl : j < exprs.length
  · rw [hstored j hjl]
    simp only [newStack, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by rw [List.length_map]; exact hjl), List.getElem?_map,
        List.getElem?_eq_getElem hjl]
    rfl
  · have hk : c ≤ j - exprs.length + c := by omega
    have hkd : j - exprs.length + c < d := by omega
    have haddr : stackAddr base (newDepth d exprs.length c) j = stackAddr base d (j - exprs.length + c) := by
      simp only [stackAddr, newDepth]; congr 2; omega
    rw [haddr, hkept _ hk hkd]
    simp only [newStack, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop]
    simp only [List.length_map]
    congr 2; omega

end Evm.CL.ARM64.FlushSem
