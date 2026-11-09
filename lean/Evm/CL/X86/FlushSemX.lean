/-
  Evm.CL.X86.FlushSemX — the region flush at the x86-64 target
  (`X86JIT.x86Flush`, after `OpInstrs.spScale`), piece by piece under
  `AsmRun`: the x86-64 twin of `ARM64.FlushSem`.

  What differs from ARM64, and how it shows here:
    * the depth register x23 (r13) holds the depth in BYTES, `32·d`, so every
      sp-derived immediate is scaled and the stack-address idiom is a plain
      `add x14, x24, x14` (`InvX.x23`, `stackAt_addrX`, `exit_addr_*X`);
    * the frame is `32n + 8` bytes with no saved fp/lr (`LayX`, `frameOpenX`);
    * slot addresses are `add r, sp, #32k` (`spAddrX`), immediates one `mov`;
    * the right quad is x15/x17/x16/x0 (`CoreSemX.x86Rq`), the helper
      arguments x3/x2/x1/x14 (`X86Sem.x86Conv`), calls are `blSym`;
    * far exits go through the chunk's trampolines (`bTramp`), and only the
      TOS cache is reloaded.
  The target-independent pieces (`Fr`, `slotAddr`, `stackAddr`, `keep`,
  `NodeOut`, `DagOut`, `WFSlots`, `newStack`) are reused from `FlushSem`.
-/

import Evm.CL.ARM64.FlushSem
import Evm.CL.X86.CoreSemX
import Evm.CL.X86Sem

namespace Evm.CL.X86.FlushSemX

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.ARM64.JIT Evm.CL.ARM64.CoreSem Evm.CL.X86.CoreSemX
open Evm.CL.ARM64.FlushSem (Fr slotAddr stackAddr keep keep_ne set_regs_ne limb_lt ofNat_limb NodeOut DagOut
  WFSlots belowSp_off_false callHelper_sp callHelper_regs_keep Inv_of_mem_iff newDepth)
open Evm.CL.X86Sem (x86Conv)
open Evm.IR.SymExpr (Expr eval)

/-! ## Layout -/

/-- The x86-64 layout: the frame is `32n + 8` bytes (no saved fp/lr). -/
structure LayX (F : Fr) : Prop where
  fpOk   : F.fp.toNat + 32 * F.n + 8 < 2 ^ 64
  baseOk : F.base.toNat + 32 * 1024 < 2 ^ 64
  dLe    : F.d ≤ 1024
  disj   : ∀ i < 32 * F.n + 8, ∀ j < 32 * 1024, off F.fp i ≠ off F.base j
  stackOut : ∀ j < 32 * 1024, belowSp F.fp (off F.base j) = false
  esLen  : F.es.length = F.d

theorem LayX.dOk {F : Fr} (hL : LayX F) : F.d < 2 ^ 32 := by have := hL.dLe; omega

/-- The invariant while the DAG is evaluated: x23 is the depth in bytes. -/
structure InvX (F : Fr) (idx : Expr → Nat) (done : List Expr) (s : RS) : Prop where
  sp    : s.sp = F.fp
  x23   : s.regs .x23 = BitVec.ofNat 64 (32 * F.d)
  x24   : s.regs .x24 = F.base
  stack : ∀ k < F.d, ld256 s.mem (stackAddr F.base F.d k) = F.es.getD k 0
  slots : ∀ e ∈ done, ld256 s.mem (slotAddr F.fp (idx e)) = eval e F.es

/-! ## The scaled pieces, as explicit instruction lists -/

def spAddrX (r : Reg) (slot : Nat) : List AInstr := [.addSp r (32 * slot)]

def loadSlotX (lo : Reg) (slot : Nat) : List AInstr :=
  let (a, b, c, d) := quadT Evm.CL.X86JIT.x86Flush lo
  spAddrX .x14 slot ++ [.ldpOff a b .x14 0, .ldpOff c d .x14 16]

def storeSlotX (slot : Nat) : List AInstr :=
  spAddrX .x14 slot ++ [.stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16]

/-- `evalNodeT x86Flush` after `spScale`. -/
def evalNodeX (idx : Expr → Nat) (e : Expr) : List AInstr :=
  let me := idx e
  let bin (core : List AInstr) (a b : Expr) : List AInstr :=
    loadSlotX .x6 (idx a) ++ loadSlotX .x10 (idx b) ++ core ++ storeSlotX me
  let un (core : List AInstr) (a : Expr) : List AInstr :=
    loadSlotX .x6 (idx a) ++ core ++ storeSlotX me
  let call2 (h : String) (a b : Expr) : List AInstr :=
    spAddrX .x3 me ++ spAddrX .x2 (idx a) ++ spAddrX .x1 (idx b) ++ [.blSym h]
  let call3 (h : String) (a b c : Expr) : List AInstr :=
    spAddrX .x3 me ++ spAddrX .x2 (idx a) ++ spAddrX .x1 (idx b) ++ spAddrX .x14 (idx c) ++ [.blSym h]
  match e with
  | .const v =>
      [.movImm .x6 (limb v 0), .movImm .x7 (limb v 1), .movImm .x8 (limb v 2), .movImm .x9 (limb v 3)] ++
      storeSlotX me
  | .stackAt k =>
      [.subImm .x14 .x23 (32 * (k + 1)), .addReg .x14 .x24 .x14,
       .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16] ++ storeSlotX me
  | .add a b        => bin (addCoreT x86Rq) a b
  | .sub a b        => bin (subCoreT x86Rq) a b
  | .and_ a b       => bin (bitCoreT x86Rq .and3) a b
  | .or_ a b        => bin (bitCoreT x86Rq .orr3) a b
  | .xor_ a b       => bin (bitCoreT x86Rq .eor3) a b
  | .lt a b         => bin (cmpCoreT x86Rq false .lo) a b
  | .gt a b         => bin (cmpCoreT x86Rq true  .lo) a b
  | .slt a b        => bin (cmpCoreT x86Rq false .lt) a b
  | .sgt a b        => bin (cmpCoreT x86Rq true  .lt) a b
  | .eq_ a b        => bin (eqCoreT x86Rq) a b
  | .isZero a       => un isZeroCoreA a
  | .not_ a         => un notCoreA a
  | .mul a b        => call2 "_eita_helper_mul" a b
  | .div a b        => call2 "_eita_helper_div" a b
  | .sdiv a b       => call2 "_eita_helper_sdiv" a b
  | .mod_ a b       => call2 "_eita_helper_mod" a b
  | .smod_ a b      => call2 "_eita_helper_smod" a b
  | .signExtend a b => call2 "_eita_helper_signextend" a b
  | .byte_ a b      => call2 "_eita_helper_byte" a b
  | .shl_ a b       => call2 "_eita_helper_shl" a b
  | .shr_ a b       => call2 "_eita_helper_shr" a b
  | .sar_ a b       => call2 "_eita_helper_sar" a b
  | .addmod a b n   => call3 "_eita_helper_addmod" a b n
  | .mulmod a b n   => call3 "_eita_helper_mulmod" a b n

/-! ## Slot addressing, loads and stores -/

theorem spAddrX_run (H : Helpers) (r : Reg) (k : Nat) (rest : List AInstr) (s : RS) :
    run H (spAddrX r k ++ rest) s = run H rest (s.set r (off s.sp (32 * k))) := by
  simp only [spAddrX, List.singleton_append]
  rw [run_cons_data H _ _ s (ctrl_addSp ..), step_addSp]

theorem loadSlotX_x6_run (H : Helpers) (k : Nat) (rest : List AInstr) (s : RS) :
    ∃ s', run H (loadSlotX .x6 k ++ rest) s = run H rest s' ∧
      lhs s' = ld256 s.mem (slotAddr s.sp k) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → s'.regs r = s.regs r) := by
  simp only [loadSlotX, quadT]
  rw [List.append_assoc, spAddrX_run, List.cons_append,
      run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..), List.singleton_append,
      run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..)]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [lhs, AsmRun.set_regs, AsmRun.set_mem, reduceCtorEq, ite_true, ite_false, Nat.reduceAdd,
               slotAddr, ld256_eq_ofLimbs, off, BitVec.add_zero]
  · intro r h6 h7 h8 h9 h14; simp [RS.set, h6, h7, h8, h9, h14]

/-- `loadSlotX .x10 k`: the x86 right quad x15/x17/x16/x0 ← the slot; x14 is scratch. -/
theorem loadSlotX_x10_run (H : Helpers) (k : Nat) (rest : List AInstr) (s : RS) :
    ∃ s', run H (loadSlotX .x10 k ++ rest) s = run H rest s' ∧
      rhs x86Rq s' = ld256 s.mem (slotAddr s.sp k) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x15 → r ≠ .x17 → r ≠ .x16 → r ≠ .x0 → r ≠ .x14 → s'.regs r = s.regs r) := by
  simp only [loadSlotX, quadT, Evm.CL.X86JIT.x86Flush]
  rw [List.append_assoc, spAddrX_run, List.cons_append,
      run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..), List.singleton_append,
      run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..)]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [rhs, x86Rq, AsmRun.set_regs, AsmRun.set_mem, reduceCtorEq, ite_true, ite_false, Nat.reduceAdd,
               slotAddr, ld256_eq_ofLimbs, off, BitVec.add_zero]
  · intro r h15 h17 h16 h0 h14; simp [RS.set, h15, h17, h16, h0, h14]

theorem storeSlotX_run (H : Helpers) (k : Nat) (rest : List AInstr) (s : RS) :
    ∃ s', run H (storeSlotX k ++ rest) s = run H rest s' ∧
      s'.mem = st256 s.mem (slotAddr s.sp k) (lhs s) ∧ s'.sp = s.sp ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x14 → s'.regs r = s.regs r) := by
  simp only [storeSlotX]
  rw [List.append_assoc, spAddrX_run, List.cons_append,
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

/-- `sub x14, x23, #32(k+1) ; add x14, x24, x14` with x23 = 32d is entry slot `k`. -/
theorem stackAt_addrX (base : BitVec 64) (d k : Nat) (hk : k < d) (hd : d < 2 ^ 32) :
    base + (BitVec.ofNat 64 (32 * d) - BitVec.ofNat 64 (32 * (k + 1))) = stackAddr base d k := by
  simp only [stackAddr, off]
  congr 1
  have hle : BitVec.ofNat 64 (32 * (k + 1)) ≤ BitVec.ofNat 64 (32 * d) := by
    rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le hle]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 32 * d < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 32 * (k + 1) < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 32 * (d - 1 - k) < 2 ^ 64)]
  omega

theorem node_constX (H : Helpers) (F : Fr) (idx : Expr → Nat) (v : Evm.U256) (rest : List AInstr) (s : RS)
    (hsp : s.sp = F.fp) :
    ∃ s', run H (evalNodeX idx (.const v) ++ rest) s = run H rest s' ∧ NodeOut F idx (.const v) s s' := by
  simp only [evalNodeX, List.cons_append, List.nil_append]
  rw [run_cons_step H _ _ _ _ (ctrl_movImm ..) (step_movImm ..),
      run_cons_step H _ _ _ _ (ctrl_movImm ..) (step_movImm ..),
      run_cons_step H _ _ _ _ (ctrl_movImm ..) (step_movImm ..),
      run_cons_step H _ _ _ _ (ctrl_movImm ..) (step_movImm ..)]
  obtain ⟨s', h1, hmem, hsp', hfl, hregs⟩ := storeSlotX_run H _ rest _
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

theorem node_stackAtX (H : Helpers) (F : Fr) (idx : Expr → Nat) (done : List Expr) (k : Nat)
    (rest : List AInstr) (s : RS) (hI : InvX F idx done s) (hL : LayX F) (hk : k < F.d) :
    ∃ s', run H (evalNodeX idx (.stackAt k) ++ rest) s = run H rest s' ∧
      NodeOut F idx (.stackAt k) s s' := by
  simp only [evalNodeX, List.cons_append, List.nil_append]
  rw [run_cons_step H _ _ _ _ (ctrl_subImm ..) (step_subImm ..),
      run_cons_step H _ _ _ _ (ctrl_addReg ..) (step_addReg ..),
      run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..),
      run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..)]
  obtain ⟨s', h1, hmem, hsp', hfl, hregs⟩ := storeSlotX_run H _ rest _
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
               hI.x23, hI.x24, stackAt_addrX F.base F.d k hk hL.dOk, BitVec.add_zero]
    rw [← ld256_eq_ofLimbs, hI.stack k hk]
    rfl
  · intro x hx _
    rw [hmem]
    simp only [AsmRun.set_sp, hI.sp]
    exact st256_out _ _ _ _ hx

/-! ## Binary and unary cores -/

def CoreSpecX (H : Helpers) (core : List AInstr) (op : Evm.U256 → Evm.U256 → Evm.U256) : Prop :=
  ∀ rest s, ∃ s', run H (core ++ rest) s = run H rest s' ∧
    lhs s' = op (lhs s) (rhs x86Rq s) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
    (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → s'.regs r = s.regs r)

theorem node_binX (H : Helpers) (F : Fr) (idx : Expr → Nat) (done : List Expr) (e a b : Expr)
    (core : List AInstr) (op : Evm.U256 → Evm.U256 → Evm.U256) (rest : List AInstr) (s : RS)
    (hcore : CoreSpecX H core op) (heval : eval e F.es = op (eval a F.es) (eval b F.es))
    (hI : InvX F idx done s) (ha : a ∈ done) (hb : b ∈ done) :
    ∃ s', run H ((loadSlotX .x6 (idx a) ++ loadSlotX .x10 (idx b) ++ core ++ storeSlotX (idx e)) ++ rest) s =
            run H rest s' ∧ NodeOut F idx e s s' := by
  simp only [List.append_assoc]
  obtain ⟨s1, h1, hv1, hsp1, hmem1, _, hregs1⟩ := loadSlotX_x6_run H (idx a) _ s
  rw [h1]
  obtain ⟨s2, h2, hv2, hsp2, hmem2, _, hregs2⟩ := loadSlotX_x10_run H (idx b) _ s1
  rw [h2]
  obtain ⟨s3, h3, hv3, hsp3, hmem3, hregs3⟩ := hcore _ s2
  rw [h3]
  obtain ⟨s4, h4, hmem4, hsp4, _, hregs4⟩ := storeSlotX_run H (idx e) rest s3
  rw [h4]
  have hsp : s3.sp = F.fp := by rw [hsp3, hsp2, hsp1, hI.sp]
  have hlhs2 : lhs s2 = lhs s1 := by
    simp only [lhs]; rw [hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  refine ⟨s4, rfl, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hsp4, hsp, hI.sp]
  · intro r hr
    obtain ⟨h0, _, _, _, h6, h7, h8, h9, _, _, _, _, h14, h15, h16, h17⟩ := keep_ne r hr
    rw [hregs4 r h14, hregs3 r h6 h7 h8 h9 h14 h15, hregs2 r h15 h17 h16 h0 h14, hregs1 r h6 h7 h8 h9 h14]
  · rw [hmem4, hsp, ld256_st256_same, hv3, hlhs2, hv1, hv2, hmem1, hI.sp, hsp1, hI.sp,
        hI.slots a ha, hI.slots b hb, heval]
  · intro x hx _
    rw [hmem4, hsp, st256_out _ _ _ _ hx, hmem3, hmem2, hmem1]

def UnSpecX (H : Helpers) (core : List AInstr) (op : Evm.U256 → Evm.U256) : Prop :=
  ∀ rest s, ∃ s', run H (core ++ rest) s = run H rest s' ∧
    lhs s' = op (lhs s) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
    (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → s'.regs r = s.regs r)

theorem node_unX (H : Helpers) (F : Fr) (idx : Expr → Nat) (done : List Expr) (e a : Expr)
    (core : List AInstr) (op : Evm.U256 → Evm.U256) (rest : List AInstr) (s : RS)
    (hcore : UnSpecX H core op) (heval : eval e F.es = op (eval a F.es))
    (hI : InvX F idx done s) (ha : a ∈ done) :
    ∃ s', run H ((loadSlotX .x6 (idx a) ++ core ++ storeSlotX (idx e)) ++ rest) s = run H rest s' ∧
      NodeOut F idx e s s' := by
  simp only [List.append_assoc]
  obtain ⟨s1, h1, hv1, hsp1, hmem1, _, hregs1⟩ := loadSlotX_x6_run H (idx a) _ s
  rw [h1]
  obtain ⟨s3, h3, hv3, hsp3, hmem3, hregs3⟩ := hcore _ s1
  rw [h3]
  obtain ⟨s4, h4, hmem4, hsp4, _, hregs4⟩ := storeSlotX_run H (idx e) rest s3
  rw [h4]
  have hsp : s3.sp = F.fp := by rw [hsp3, hsp1, hI.sp]
  refine ⟨s4, rfl, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hsp4, hsp, hI.sp]
  · intro r hr
    obtain ⟨_, _, _, _, h6, h7, h8, h9, _, _, _, _, h14, h15, _, _⟩ := keep_ne r hr
    rw [hregs4 r h14, hregs3 r h6 h7 h8 h9 h14 h15, hregs1 r h6 h7 h8 h9 h14]
  · rw [hmem4, hsp, ld256_st256_same, hv3, hv1, hI.sp, hI.slots a ha, heval]
  · intro x hx _
    rw [hmem4, hsp, st256_out _ _ _ _ hx, hmem3, hmem1]

section specs
variable (H : Helpers)
theorem csX_add : CoreSpecX H (addCoreT x86Rq) (· + ·) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, h5⟩ := addCore_runX H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem csX_sub : CoreSpecX H (subCoreT x86Rq) (· - ·) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, h5⟩ := subCore_runX H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem csX_and : CoreSpecX H (bitCoreT x86Rq .and3) (· &&& ·) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, _, h5⟩ := andCore_runX H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem csX_or : CoreSpecX H (bitCoreT x86Rq .orr3) (· ||| ·) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, _, h5⟩ := orCore_runX H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem csX_xor : CoreSpecX H (bitCoreT x86Rq .eor3) (· ^^^ ·) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, _, h5⟩ := xorCore_runX H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem csX_lt : CoreSpecX H (cmpCoreT x86Rq false .lo) (fun x y => if x < y then 1 else 0) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, h5⟩ := ltCore_runX H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem csX_gt : CoreSpecX H (cmpCoreT x86Rq true .lo) (fun x y => if y < x then 1 else 0) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, h5⟩ := gtCore_runX H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem csX_slt : CoreSpecX H (cmpCoreT x86Rq false .lt) (fun x y => if BitVec.slt x y then 1 else 0) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, h5⟩ := sltCore_runX H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem csX_sgt : CoreSpecX H (cmpCoreT x86Rq true .lt) (fun x y => if BitVec.slt y x then 1 else 0) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, h5⟩ := sgtCore_runX H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
theorem csX_eq : CoreSpecX H (eqCoreT x86Rq) (fun x y => if x = y then 1 else 0) := eqCore_runX H
theorem usX_isZero : UnSpecX H isZeroCoreA (fun x => if x = 0 then 1 else 0) := isZeroCore_run H
theorem usX_not : UnSpecX H notCoreA (~~~ ·) := fun rest s =>
  let ⟨s', h1, h2, h3, h4, _, h5⟩ := notCore_run H rest s; ⟨s', h1, h2, h3, h4, fun r a b c d _ _ => h5 r a b c d⟩
end specs

/-! ## Helper calls, SysV through x3/x2/x1/x14 -/

theorem callHelper_memX (H : Helpers) (hC : H.conv = x86Conv) (h : String) (s : RS) :
    (callHelper H h s).mem =
      st256 (fun x => if belowSp s.sp x then H.junk h s x else s.mem x) (s.regs .x3)
        (if ternary h then H.fn3 h (ld256 s.mem (s.regs .x2)) (ld256 s.mem (s.regs .x1)) (ld256 s.mem (s.regs .x14))
         else H.fn2 h (ld256 s.mem (s.regs .x2)) (ld256 s.mem (s.regs .x1))) := by
  simp only [callHelper, hC, x86Conv]

theorem run_cons_blSym (H : Helpers) (h : String) (rest : List AInstr) (s : RS) :
    run H (.blSym h :: rest) s = run H rest (callHelper H h s) := by simp [run, ctrl]

theorem node_call2X (H : Helpers) (hC : H.conv = x86Conv) (F : Fr) (idx : Expr → Nat) (done : List Expr)
    (e a b : Expr) (h : String) (rest : List AInstr) (s : RS)
    (ht : ternary h = false) (hval : H.fn2 h (eval a F.es) (eval b F.es) = eval e F.es)
    (hI : InvX F idx done s) (ha : a ∈ done) (hb : b ∈ done) :
    ∃ s', run H ((spAddrX .x3 (idx e) ++ spAddrX .x2 (idx a) ++ spAddrX .x1 (idx b) ++ [AInstr.blSym h]) ++ rest) s =
            run H rest s' ∧ NodeOut F idx e s s' := by
  simp only [List.append_assoc]
  rw [spAddrX_run, spAddrX_run, spAddrX_run, List.singleton_append, run_cons_blSym]
  refine ⟨_, rfl, ⟨rfl, ?_, ?_, ?_⟩⟩
  · intro r hr
    obtain ⟨_, h1, h2, h3, _, _, _, _, _, _, _, _, _, _, _, _⟩ := keep_ne r hr
    rw [callHelper_regs_keep _ _ _ _ hr, set_regs_ne _ _ _ _ h1, set_regs_ne _ _ _ _ h2, set_regs_ne _ _ _ _ h3]
  · rw [callHelper_memX H hC]
    simp only [AsmRun.set_regs, AsmRun.set_mem, AsmRun.set_sp, reduceCtorEq, ite_true, ite_false, ht,
               Bool.false_eq_true, hI.sp, slotAddr]
    rw [ld256_st256_same]
    have hsa := hI.slots a ha; have hsb := hI.slots b hb
    simp only [slotAddr] at hsa hsb
    rw [hsa, hsb, hval]
  · intro x hx hw
    rw [callHelper_memX H hC]
    simp only [AsmRun.set_regs, AsmRun.set_mem, AsmRun.set_sp, reduceCtorEq, ite_true, ite_false, hI.sp]
    simp only [slotAddr] at hx
    rw [st256_out _ _ _ _ hx]
    simp [hw]

theorem node_call3X (H : Helpers) (hC : H.conv = x86Conv) (F : Fr) (idx : Expr → Nat) (done : List Expr)
    (e a b c : Expr) (h : String) (rest : List AInstr) (s : RS)
    (ht : ternary h = true) (hval : H.fn3 h (eval a F.es) (eval b F.es) (eval c F.es) = eval e F.es)
    (hI : InvX F idx done s) (ha : a ∈ done) (hb : b ∈ done) (hc : c ∈ done) :
    ∃ s', run H ((spAddrX .x3 (idx e) ++ spAddrX .x2 (idx a) ++ spAddrX .x1 (idx b) ++ spAddrX .x14 (idx c) ++
                  [AInstr.blSym h]) ++ rest) s = run H rest s' ∧ NodeOut F idx e s s' := by
  simp only [List.append_assoc]
  rw [spAddrX_run, spAddrX_run, spAddrX_run, spAddrX_run, List.singleton_append, run_cons_blSym]
  refine ⟨_, rfl, ⟨rfl, ?_, ?_, ?_⟩⟩
  · intro r hr
    obtain ⟨_, h1, h2, h3, _, _, _, _, _, _, _, _, h14, _, _, _⟩ := keep_ne r hr
    rw [callHelper_regs_keep _ _ _ _ hr, set_regs_ne _ _ _ _ h14, set_regs_ne _ _ _ _ h1, set_regs_ne _ _ _ _ h2,
        set_regs_ne _ _ _ _ h3]
  · rw [callHelper_memX H hC]
    simp only [AsmRun.set_regs, AsmRun.set_mem, AsmRun.set_sp, reduceCtorEq, ite_true, ite_false, ht, hI.sp,
               slotAddr]
    rw [ld256_st256_same]
    have hsa := hI.slots a ha; have hsb := hI.slots b hb; have hsc := hI.slots c hc
    simp only [slotAddr] at hsa hsb hsc
    rw [hsa, hsb, hsc, hval]
  · intro x hx hw
    rw [callHelper_memX H hC]
    simp only [AsmRun.set_regs, AsmRun.set_mem, AsmRun.set_sp, reduceCtorEq, ite_true, ite_false, hI.sp]
    simp only [slotAddr] at hx
    rw [st256_out _ _ _ _ hx]
    simp [hw]


/-! ## Every node -/

theorem node_runX (H : Helpers) (hS : H.Spec) (hC : H.conv = x86Conv) (F : Fr) (idx : Expr → Nat) (done : List Expr)
    (e : Expr) (rest : List AInstr) (s : RS) (hI : InvX F idx done s) (hL : LayX F)
    (hkids : ∀ k ∈ exprKids e, k ∈ done) (hwf : ∀ k, e = .stackAt k → k < F.d) :
    ∃ s', run H (evalNodeX idx e ++ rest) s = run H rest s' ∧ NodeOut F idx e s s' := by
  cases e with
  | const v => exact node_constX H F idx v rest s hI.sp
  | stackAt k => exact node_stackAtX H F idx done k rest s hI hL (hwf k rfl)
  | add a b => exact node_binX H F idx done _ a b _ _ rest s (csX_add H) rfl hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | sub a b => exact node_binX H F idx done _ a b _ _ rest s (csX_sub H) rfl hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | and_ a b => exact node_binX H F idx done _ a b _ _ rest s (csX_and H) rfl hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | or_ a b => exact node_binX H F idx done _ a b _ _ rest s (csX_or H) rfl hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | xor_ a b => exact node_binX H F idx done _ a b _ _ rest s (csX_xor H) rfl hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | lt a b => exact node_binX H F idx done _ a b _ _ rest s (csX_lt H) rfl hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | gt a b => exact node_binX H F idx done _ a b _ _ rest s (csX_gt H) rfl hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | slt a b => exact node_binX H F idx done _ a b _ _ rest s (csX_slt H) rfl hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | sgt a b => exact node_binX H F idx done _ a b _ _ rest s (csX_sgt H) rfl hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | eq_ a b => exact node_binX H F idx done _ a b _ _ rest s (csX_eq H) rfl hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | isZero a => exact node_unX H F idx done _ a _ _ rest s (usX_isZero H) rfl hI (hkids a (by simp [exprKids]))
  | not_ a => exact node_unX H F idx done _ a _ _ rest s (usX_not H) rfl hI (hkids a (by simp [exprKids]))
  | mul a b => exact node_call2X H hC F idx done _ a b "_eita_helper_mul" rest s (by decide) (by simp [hS.mul, eval]) hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | div a b => exact node_call2X H hC F idx done _ a b "_eita_helper_div" rest s (by decide) (by simp [hS.div, eval]) hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | sdiv a b => exact node_call2X H hC F idx done _ a b "_eita_helper_sdiv" rest s (by decide) (by simp [hS.sdiv, eval]) hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | mod_ a b => exact node_call2X H hC F idx done _ a b "_eita_helper_mod" rest s (by decide) (by simp [hS.mod_, eval]) hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | smod_ a b => exact node_call2X H hC F idx done _ a b "_eita_helper_smod" rest s (by decide) (by simp [hS.smod_, eval]) hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | signExtend a b => exact node_call2X H hC F idx done _ a b "_eita_helper_signextend" rest s (by decide) (by simp [hS.signextend, eval]) hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | byte_ a b => exact node_call2X H hC F idx done _ a b "_eita_helper_byte" rest s (by decide) (by simp [hS.byte_, eval]) hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | shl_ a b => exact node_call2X H hC F idx done _ a b "_eita_helper_shl" rest s (by decide) (by simp [hS.shl, eval]) hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | shr_ a b => exact node_call2X H hC F idx done _ a b "_eita_helper_shr" rest s (by decide) (by simp [hS.shr, eval]) hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | sar_ a b => exact node_call2X H hC F idx done _ a b "_eita_helper_sar" rest s (by decide) (by simp [hS.sar, eval]) hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids]))
  | addmod a b n => exact node_call3X H hC F idx done _ a b n "_eita_helper_addmod" rest s (by decide) (by simp [hS.addmod, eval]) hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) (hkids n (by simp [exprKids]))
  | mulmod a b n => exact node_call3X H hC F idx done _ a b n "_eita_helper_mulmod" rest s (by decide) (by simp [hS.mulmod, eval]) hI (hkids a (by simp [exprKids])) (hkids b (by simp [exprKids])) (hkids n (by simp [exprKids]))

/-! ## The DAG, slot by slot -/

theorem InvX_of_mem_iff (F : Fr) (idx : Expr → Nat) (d1 d2 : List Expr) (s : RS)
    (h : ∀ x, x ∈ d1 ↔ x ∈ d2) (hI : InvX F idx d1 s) : InvX F idx d2 s :=
  ⟨hI.sp, hI.x23, hI.x24, hI.stack, fun e he => hI.slots e ((h e).mpr he)⟩

theorem slot_disjX (F : Fr) (hL : LayX F) (i j : Nat) (hi : i < F.n) (hj : j < F.n) (hij : i ≠ j) :
    ∀ a < 32, ∀ b < 32, off (slotAddr F.fp i) a ≠ off (slotAddr F.fp j) b := by
  intro a ha b hb
  have := hL.fpOk
  simp only [slotAddr, off_off]
  exact off_ne_off F.fp _ _ (by omega) (by omega) (by omega)

theorem slot_stack_disjX (F : Fr) (hL : LayX F) (i k : Nat) (hi : i < F.n) (hk : k < F.d) :
    ∀ a < 32, ∀ b < 32, off (stackAddr F.base F.d k) b ≠ off (slotAddr F.fp i) a := by
  intro a ha b hb
  have := hL.dLe
  simp only [slotAddr, stackAddr, off_off]
  exact (hL.disj _ (by omega) _ (by omega)).symm

theorem slot_not_belowX (F : Fr) (hL : LayX F) (i : Nat) (hi : i < F.n) (a : Nat) (ha : a < 32) :
    belowSp F.fp (off (slotAddr F.fp i) a) = false := by
  simp only [slotAddr, off_off]
  exact belowSp_off_false F.fp _ (by have := hL.fpOk; omega)

theorem InvX_step (F : Fr) (idx : Expr → Nat) (done : List Expr) (e : Expr) (s s' : RS)
    (hL : LayX F) (hI : InvX F idx done s) (hO : NodeOut F idx e s s')
    (hn : idx e < F.n) (hnd : ∀ e' ∈ done, idx e' < F.n)
    (hdist : ∀ e' ∈ done, idx e' = idx e → eval e' F.es = eval e F.es) :
    InvX F idx (e :: done) s' where
  sp := by rw [hO.sp, hI.sp]
  x23 := by rw [hO.regs .x23 rfl, hI.x23]
  x24 := by rw [hO.regs .x24 rfl, hI.x24]
  stack := by
    intro k hk
    rw [← hI.stack k hk]
    apply ld256_eq_of_eq_on
    intro b hb
    apply hO.mem
    · intro a ha; exact slot_stack_disjX F hL (idx e) k hn hk a ha b hb
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
        · intro a ha; exact slot_disjX F hL (idx e') (idx e) (hnd e' he') hn hidx b hb a ha
        · exact slot_not_belowX F hL (idx e') (hnd e' he') b hb

theorem DagOut_of_node (F : Fr) (idx : Expr → Nat) (e : Expr) (s s' : RS) (hn : idx e < F.n)
    (hO : NodeOut F idx e s s') : DagOut F s s' :=
  ⟨hO.sp, hO.regs, fun x hx hw => hO.mem x (fun i hi => by
      simp only [slotAddr, off_off]; exact hx _ (by omega)) hw⟩

theorem dag_loopX (H : Helpers) (hS : H.Spec) (hC : H.conv = x86Conv) (F : Fr) (idx : Expr → Nat) (rest : List AInstr)
    (hL : LayX F) :
    ∀ (suf pre : List Expr) (s : RS), WFSlots F idx (pre ++ suf) → InvX F idx pre s →
      ∃ s', run H (suf.flatMap (evalNodeX idx) ++ rest) s = run H rest s' ∧
        InvX F idx (pre ++ suf) s' ∧ DagOut F s s' := by
  intro suf
  induction suf with
  | nil => intro pre s _ hI; exact ⟨s, by simp, by simpa using hI, Evm.CL.ARM64.FlushSem.DagOut.refl F s⟩
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
    obtain ⟨s1, h1, hO⟩ := node_runX H hS hC F idx pre e _ s hI hL hkids (hW.stackLt e he)
    have hI1 : InvX F idx (pre ++ [e]) s1 :=
      InvX_of_mem_iff F idx (e :: pre) _ s1 (by intro x; simp [or_comm])
        (InvX_step F idx pre e s s1 hL hI hO hn (fun e' he' => hW.idxLt e' (by simp [he']))
          (fun e' he' hidx => by rw [hW.dist e' e (by simp [he']) he hidx]))
    have hW1 : WFSlots F idx ((pre ++ [e]) ++ suf) := by rw [List.append_assoc]; simpa using hW
    obtain ⟨s', h2, hI', hD⟩ := ih (pre ++ [e]) s1 hW1 hI1
    refine ⟨s', ?_, by simpa using hI', Evm.CL.ARM64.FlushSem.DagOut.trans F s s1 s' (DagOut_of_node F idx e s s1 hn hO) hD⟩
    rw [List.flatMap_cons, List.append_assoc, h1, h2]

/-! ## The exit prefix -/

theorem exit_addr_addX (base : BitVec 64) (d k : Nat) (_h : d + k < 2 ^ 32) :
    base + (BitVec.ofNat 64 (32 * d) + BitVec.ofNat 64 (32 * k)) = off base (32 * (d + k)) := by
  simp only [off]
  rw [← BitVec.ofNat_add]
  congr 2; omega

theorem exit_addr_subX (base : BitVec 64) (d k : Nat) (hk : k ≤ d) (hd : d < 2 ^ 32) :
    base + (BitVec.ofNat 64 (32 * d) - BitVec.ofNat 64 (32 * k)) = off base (32 * (d - k)) := by
  simp only [off]
  congr 1
  have hle : BitVec.ofNat 64 (32 * k) ≤ BitVec.ofNat 64 (32 * d) := by
    rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le hle]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 32 * d < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 32 * k < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 32 * (d - k) < 2 ^ 64)]
  omega

/-- `exitOneT x86Flush` after `spScale`. -/
def exitOneX (idx : Expr → Nat) (net : Int) (e : Expr) (m : Nat) : List AInstr :=
  let d : Int := net - 1 - m
  loadSlotX .x6 (idx e) ++
  [if d ≥ 0 then .addImm .x14 .x23 (32 * d.toNat) else .subImm .x14 .x23 (32 * (-d).toNat)] ++
  [.addReg .x14 .x24 .x14, .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16]

def exitStoresX (idx : Expr → Nat) (net : Int) (exprs : List Expr) : List AInstr :=
  exprs.zipIdx.flatMap (fun (e, m) => exitOneX idx net e m)

theorem exit_oneX_run (H : Helpers) (F : Fr) (hL : LayX F) (idx : Expr → Nat) (e : Expr) (m len c : Nat)
    (rest : List AInstr) (s : RS)
    (hsp : s.sp = F.fp) (h23 : s.regs .x23 = BitVec.ofNat 64 (32 * F.d)) (h24 : s.regs .x24 = F.base)
    (hslot : ld256 s.mem (slotAddr F.fp (idx e)) = eval e F.es)
    (hm : m < len) (hc : c ≤ F.d) (hd' : newDepth F.d len c ≤ 1024) :
    ∃ s', run H (exitOneX idx ((len : Int) - c) e m ++ rest) s = run H rest s' ∧
      s'.mem = st256 s.mem (stackAddr F.base (newDepth F.d len c) m) (eval e F.es) ∧
      s'.sp = s.sp ∧ (∀ r, keep r = true → s'.regs r = s.regs r) := by
  simp only [exitOneX, List.append_assoc]
  obtain ⟨s1, h1, hv1, hsp1, hmem1, _, hregs1⟩ := loadSlotX_x6_run H (idx e) _ s
  rw [h1]
  have h23' : s1.regs .x23 = BitVec.ofNat 64 (32 * F.d) := by
    rw [hregs1 _ (by decide) (by decide) (by decide) (by decide) (by decide), h23]
  have h24' : s1.regs .x24 = F.base := by
    rw [hregs1 _ (by decide) (by decide) (by decide) (by decide) (by decide), h24]
  have hdOk := hL.dOk
  have hlhs1 : lhs s1 = eval e F.es := by rw [hv1, hsp, hslot]
  have hd2 : F.d + len - c ≤ 1024 := hd'
  have hlen : len ≤ 1024 := by omega
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
  have after : ∀ v : BitVec 64, ∀ s', (s' = (s1.set .x14 v).set .x14 ((s1.set .x14 v).regs .x24 + (s1.set .x14 v).regs .x14)) →
      s'.regs .x14 = F.base + v ∧ s'.mem = s.mem ∧ lhs s' = eval e F.es ∧ s'.sp = s.sp ∧
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
  · rw [ite_eq_left hk, List.singleton_append, run_cons_step H _ _ _ _ (ctrl_addImm ..) (step_addImm ..),
        List.cons_append, run_cons_step H _ _ _ _ (ctrl_addReg ..) (step_addReg ..)]
    obtain ⟨a1, a2, a3, a4, a5⟩ := after _ _ rfl
    apply tail _ _ a2 a3 a4 a5
    rw [a1, h23', exit_addr_addX F.base F.d _ (by omega)]
    simp only [stackAddr]
    congr 2
    simp only [newDepth]; omega
  · rw [ite_eq_right hk, List.singleton_append, run_cons_step H _ _ _ _ (ctrl_subImm ..) (step_subImm ..),
        List.cons_append, run_cons_step H _ _ _ _ (ctrl_addReg ..) (step_addReg ..)]
    obtain ⟨a1, a2, a3, a4, a5⟩ := after _ _ rfl
    apply tail _ _ a2 a3 a4 a5
    rw [a1, h23', exit_addr_subX F.base F.d _ (by omega) hdOk]
    simp only [stackAddr]
    congr 2
    simp only [newDepth]; omega

structure ExitInvX (F : Fr) (idx : Expr → Nat) (slots : List Expr) (c : Nat) (s : RS) : Prop where
  sp    : s.sp = F.fp
  x23   : s.regs .x23 = BitVec.ofNat 64 (32 * F.d)
  x24   : s.regs .x24 = F.base
  slots : ∀ e ∈ slots, ld256 s.mem (slotAddr F.fp (idx e)) = eval e F.es
  keepStack : ∀ k, c ≤ k → k < F.d → ld256 s.mem (stackAddr F.base F.d k) = F.es.getD k 0

theorem ExitInvX.of_InvX (F : Fr) (idx : Expr → Nat) (slots : List Expr) (c : Nat) (s : RS)
    (hI : InvX F idx slots s) : ExitInvX F idx slots c s :=
  ⟨hI.sp, hI.x23, hI.x24, hI.slots, fun k _ hk => hI.stack k hk⟩

theorem exit_loopX (H : Helpers) (F : Fr) (hL : LayX F) (idx : Expr → Nat) (slots : List Expr) (c len : Nat)
    (rest : List AInstr) (hc : c ≤ F.d) (hd' : newDepth F.d len c ≤ 1024) (hidx : ∀ e ∈ slots, idx e < F.n) :
    ∀ (suf : List Expr) (m0 : Nat) (s : RS), m0 + suf.length = len → (∀ e ∈ suf, e ∈ slots) →
      ExitInvX F idx slots c s →
      ∃ s', run H ((suf.zipIdx m0).flatMap (fun (e, m) => exitOneX idx ((len : Int) - c) e m) ++ rest) s =
              run H rest s' ∧
        ExitInvX F idx slots c s' ∧
        (∀ i (h : i < suf.length), ld256 s'.mem (stackAddr F.base (newDepth F.d len c) (m0 + i)) = eval suf[i] F.es) ∧
        s'.sp = s.sp ∧ (∀ r, keep r = true → s'.regs r = s.regs r) ∧
        (∀ x, (∀ m, m0 ≤ m → m < m0 + suf.length → ∀ b < 32, x ≠ off (stackAddr F.base (newDepth F.d len c) m) b) →
          s'.mem x = s.mem x) := by
  intro suf
  induction suf with
  | nil =>
    intro m0 s _ _ hX
    exact ⟨s, by simp, hX, fun i h => by simp at h, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons e suf ih =>
    intro m0 s hlen hmem hX
    have hd2 : F.d + len - c ≤ 1024 := hd'
    have hlen' : m0 + suf.length + 1 = len := by simp at hlen; omega
    have hm0 : m0 < len := by omega
    obtain ⟨s1, h1, hmem1, hsp1, hregs1⟩ := exit_oneX_run H F hL idx e m0 len c _ s hX.sp hX.x23 hX.x24
      (hX.slots e (hmem e (by simp))) hm0 hc hd'
    have hpos : newDepth F.d len c - 1 - m0 < 1024 := by simp only [newDepth]; omega
    have hX1 : ExitInvX F idx slots c s1 := by
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
      (fun e' he' => hmem e' (by simp [he'])) hX1
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
        exact Evm.CL.ARM64.FlushSem.stack_pos_disj F.base hL.baseOk _ m0 m hd' (by omega) (by omega) (by omega) b hb a ha
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [show m0 + (i + 1) = m0 + 1 + i by omega]
        exact hstored i (by simpa using hi)
    · intro x hx
      rw [hmem' x (fun m hm1 hm2 b hb => hx m (by omega) (by simp; omega) b hb), hmem1]
      apply st256_out
      intro a ha
      exact hx m0 (Nat.le_refl _) (by simp) a ha

/-! ## Frame, depth update, TOS reload, checks -/

def frameOpenX (n : Nat) : List AInstr := [.spSub (32 * n + 8)]
def frameCloseX (n : Nat) : List AInstr := [.spAdd (32 * n + 8)]

theorem frameOpenX_run (H : Helpers) (n : Nat) (rest : List AInstr) (s : RS) :
    run H (frameOpenX n ++ rest) s = run H rest (s.withSp (s.sp - BitVec.ofNat 64 (32 * n + 8))) := by
  simp only [frameOpenX, List.singleton_append]
  rw [run_cons_step H _ _ _ _ (ctrl_spSub _) (step_spSub _ _)]

theorem frameCloseX_run (H : Helpers) (n : Nat) (rest : List AInstr) (s : RS) :
    run H (frameCloseX n ++ rest) s = run H rest (s.withSp (s.sp + BitVec.ofNat 64 (32 * n + 8))) := by
  simp only [frameCloseX, List.singleton_append]
  rw [run_cons_step H _ _ _ _ (ctrl_spAdd _) (step_spAdd _ _)]

/-- `depthUpdate` after `spScale`: byte counts. -/
def depthUpdateX (net : Int) : List AInstr :=
  if net > 0 then [.addImm .x23 .x23 (32 * net.toNat)]
  else if net < 0 then [.subImm .x23 .x23 (32 * (-net).toNat)] else []

theorem depthUpdateX_run (H : Helpers) (net : Int) (d : Nat) (hd : (d : Int) + net ≥ 0)
    (hw : 32 * (d + net.toNat) < 2 ^ 64) (rest : List AInstr) (s : RS) (h23 : s.regs .x23 = BitVec.ofNat 64 (32 * d)) :
    ∃ s', run H (depthUpdateX net ++ rest) s = run H rest s' ∧
      s'.regs .x23 = BitVec.ofNat 64 (32 * ((d : Int) + net).toNat) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.flags = s.flags ∧ (∀ r, r ≠ .x23 → s'.regs r = s.regs r) := by
  simp only [depthUpdateX]
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
      have hle : BitVec.ofNat 64 (32 * (-net).toNat) ≤ BitVec.ofNat 64 (32 * d) := by
        rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le hle]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [List.nil_append]
      refine ⟨s, rfl, ?_, rfl, rfl, rfl, fun _ _ => rfl⟩
      rw [h23]; congr 1; omega

/-- `x86Flush.cacheReload` after `spScale`: TOS only, from the byte depth. -/
def cacheReloadX : List AInstr :=
  [ .cmpImm .x23 32, .bcLbl .lt "8f", .subImm .x14 .x23 32, .addReg .x14 .x24 .x14,
    .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16, .label "8" ]

theorem cacheReloadX_run (H : Helpers) (base : BitVec 64) (d : Nat) (hd : d ≤ 1024) (rest : List AInstr) (s : RS)
    (h23 : s.regs .x23 = BitVec.ofNat 64 (32 * d)) (h24 : s.regs .x24 = base) :
    ∃ s', run H (cacheReloadX ++ rest) s = run H rest s' ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (1 ≤ d → lhs s' = ld256 s.mem (stackAddr base d 0)) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → s'.regs r = s.regs r) := by
  simp only [cacheReloadX, List.cons_append, List.nil_append]
  rw [run_cons_step H _ _ _ _ (ctrl_cmpImm ..) (step_cmpImm ..), run_cons_bcLbl]
  simp only [AsmRun.withFlags_flags, h23, Evm.CL.ARM64.FlushSem.lt_small (32 * d) 32 (by omega) (by decide)]
  by_cases h : d < 1
  · rw [decide_eq_true (by omega), ite_eq_left rfl]
    simp only [AsmRun.skipTo]
    rw [ite_eq_left (by decide), run_cons_label]
    exact ⟨_, rfl, rfl, rfl, fun hkd => absurd hkd (by omega), fun r _ _ _ _ _ => rfl⟩
  · rw [decide_eq_false (by omega), ite_eq_right (by simp)]
    rw [run_cons_step H _ _ _ _ (ctrl_subImm ..) (step_subImm ..),
        run_cons_step H _ _ _ _ (ctrl_addReg ..) (step_addReg ..),
        run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..),
        run_cons_step H _ _ _ _ (ctrl_ldpOff ..) (step_ldpOff ..), run_cons_label]
    refine ⟨_, rfl, rfl, rfl, ?_, ?_⟩
    · intro hkd
      have e1 : base + (BitVec.ofNat 64 (32 * d) - BitVec.ofNat 64 32) = stackAddr base d 0 := by
        have := exit_addr_subX base d 1 hkd (by omega)
        simpa [stackAddr] using this
      simp only [AsmRun.withFlags_regs, AsmRun.withFlags_mem, AsmRun.set_regs, AsmRun.set_mem, reduceCtorEq,
                 ite_true, ite_false, Nat.reduceAdd, h23, h24, e1, BitVec.add_zero]
      rw [ld256_eq_ofLimbs]
      rfl
    · intro r ha hb hc he h14
      simp [RS.set, ha, hb, hc, he, h14]

theorem run_cons_bTramp (H : Helpers) (sym : String) (rest : List AInstr) (s : RS) :
    run H (.bTramp sym :: rest) s = .fault sym s := by simp [run, ctrl]

open Evm.CL.ARM64.ChunkGasSem (hs_subFlags) in
theorem underflowCheckX_run (H : Helpers) (need d : Nat) (hd : d < 2 ^ 32) (hneed : need < 2 ^ 32)
    (rest : List AInstr) (s : RS) (h23 : s.regs .x23 = BitVec.ofNat 64 (32 * d)) :
    run H (AInstr.cmpImm .x23 (32 * need) :: .bcLbl .hs "8f" :: .bTramp "_eita_stack_underflow" :: .label "8" :: rest) s =
      if need ≤ d then run H rest (s.withFlags (subFlags (BitVec.ofNat 64 (32 * d)) (BitVec.ofNat 64 (32 * need))))
      else .fault "_eita_stack_underflow" (s.withFlags (subFlags (BitVec.ofNat 64 (32 * d)) (BitVec.ofNat 64 (32 * need)))) := by
  rw [run_cons_step H _ _ _ _ (ctrl_cmpImm ..) (step_cmpImm ..), run_cons_bcLbl]
  simp only [AsmRun.withFlags_flags, h23, hs_subFlags _ _ (by omega : 32 * need < 2 ^ 64), BitVec.toNat_ofNat,
             Nat.mod_eq_of_lt (by omega : 32 * d < 2 ^ 64)]
  by_cases h : need ≤ d
  · rw [decide_eq_true (by omega), ite_eq_left rfl, ite_eq_left h]
    simp only [AsmRun.skipTo]
    rw [ite_eq_left (by decide), run_cons_label]
  · rw [decide_eq_false (by omega), ite_eq_right (by simp), ite_eq_right h, run_cons_bTramp]

theorem overflowCheckX_run (H : Helpers) (lim d : Nat) (hd : d < 2 ^ 32) (hlim : lim < 2 ^ 32)
    (rest : List AInstr) (s : RS) (h23 : s.regs .x23 = BitVec.ofNat 64 (32 * d)) :
    run H (AInstr.cmpImm .x23 (32 * lim) :: .bcLbl .lo "9f" :: .bTramp "_eita_stack_overflow" :: .label "9" :: rest) s =
      if d < lim then run H rest (s.withFlags (subFlags (BitVec.ofNat 64 (32 * d)) (BitVec.ofNat 64 (32 * lim))))
      else .fault "_eita_stack_overflow" (s.withFlags (subFlags (BitVec.ofNat 64 (32 * d)) (BitVec.ofNat 64 (32 * lim)))) := by
  rw [run_cons_step H _ _ _ _ (ctrl_cmpImm ..) (step_cmpImm ..), run_cons_bcLbl]
  have hlo : bcHolds .lo (subFlags (BitVec.ofNat 64 (32 * d)) (BitVec.ofNat 64 (32 * lim))) = decide (d < lim) := by
    simp only [bcHolds, subFlags, BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 32 * d < 2 ^ 64),
               Nat.mod_eq_of_lt (by omega : 32 * lim < 2 ^ 64)]
    cases Nat.lt_or_ge d lim with
    | inl h => simp [h, Nat.not_le.mpr (by omega : 32 * d < 32 * lim)]
    | inr h => simp [Nat.not_lt.mpr h, (by omega : 32 * lim ≤ 32 * d)]
  simp only [AsmRun.withFlags_flags, h23, hlo]
  by_cases h : d < lim
  · rw [decide_eq_true h, ite_eq_left rfl, ite_eq_left h]
    simp only [AsmRun.skipTo]
    rw [ite_eq_left (by decide), run_cons_label]
  · rw [decide_eq_false h, ite_eq_right (by simp), ite_eq_right h, run_cons_bTramp]

end Evm.CL.X86.FlushSemX
