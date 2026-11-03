/-
  Evm.CL.PushWide — PUSH-N's immediate by wide loads (`AsmCore.pushWideInstrs`:
  ⌈n/8⌉ eight-byte loads + byte reverse, `ldr`+`rev` / `mov`+`bswap`), proved for
  every n in 1..32 on both backends. It replaces a per-byte bounds check + 256-bit
  shift (~10 instructions per byte). With no branch, a byte past code_size comes
  from the code image's zero padding: `PadContract` (the 32 bytes after the code are
  0) is a hypothesis here, as `BlobEnv` takes the host's table, and the host makes
  it true in one place (src/evm/frames.lisp `frame-code-image`).

   * `pushWide_run`: the loads leave the big-endian n bytes at x26+x21 in x6..x9.
   * `pushWide_correct`: under the contract that is `pushAccum`, the fold
     `Op.denote` uses (EELS `push_n`: `buffer_read` zero-fills, then
     `U256.from_be_bytes`).
   * `pushWide_x86`: the x86-64 lowering ends related to it (`sim_run`).
   * `pushWide_needs_padding`: without the contract a code-end PUSH1 is wrong.
   * `pushWide_reads_window`: no load reaches past pc + 32.
-/

import Evm.CL.ARM64.CoreSem
import Evm.CL.X86Xfer
import Mathlib.Tactic.IntervalCases

namespace Evm.CL.PushWide

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.ARM64.CoreSem
open Evm.CL.X86Items Evm.CL.X86Sem Evm.CL.X86SemCtrl Evm.CL.X86Xfer

@[simp] theorem step_ldrBase (s : RS) (d b : Reg) :
    AsmRun.step s (.ldrBase d b) = some (s.set d (ld64 s.mem (s.regs b))) := rfl

/-! ## The spec, in bit vectors -/

/-- The big-endian value of `f 0, …, f (n-1)` (`f 0` most significant). -/
def beBytes (f : Nat → BitVec 8) : Nat → BitVec 256
  | 0 => 0
  | k + 1 => (beBytes f k <<< 8) ||| (f k).setWidth 256

theorem beBytes_congr (f g : Nat → BitVec 8) : ∀ n, (∀ i < n, f i = g i) → beBytes f n = beBytes g n
  | 0, _ => rfl
  | k + 1, h => by
    simp only [beBytes]
    rw [beBytes_congr f g k (fun i hi => h i (by omega)), h k (by omega)]

/-! ## The contract -/

/-- **The padding contract.** The 32 bytes after the code are zero. -/
def PadContract (mem : Mem) (cb : BitVec 64) (codeSize : Nat) : Prop :=
  ∀ i, codeSize ≤ i → i < codeSize + 32 → mem (cb + BitVec.ofNat 64 i) = 0

/-- The code bytes are at `cb`. -/
def CodeAt (mem : Mem) (cb : BitVec 64) (code : Nat → Nat) (codeSize : Nat) : Prop :=
  ∀ i < codeSize, mem (cb + BitVec.ofNat 64 i) = BitVec.ofNat 8 (code i)

/-! ## The instructions, for each n -/

/-- What the wide loads leave, instruction by instruction: unfold the program,
    then let `bv_decide` match the concatenations of byte atoms. -/
syntax "push_wide_run" term:max term:max term:max term:max term:max : tactic
macro_rules
  | `(tactic| push_wide_run $hA $h6 $h7 $h8 $h9) =>
    `(tactic| (
      simp only [pushWideInstrs, tosLimb, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceMul,
        List.range, List.range.loop, List.flatMap, List.map, List.flatten, List.cons_append, List.nil_append,
        List.append_assoc, List.singleton_append, List.append_eq, List.append_nil, reduceIte, Nat.reduceEqDiff,
        if_false, if_true, run_cons_data, ctrl_addReg, ctrl_addImm, ctrl_ldrOff, ctrl_ldrBase, ctrl_rev,
        ctrl_lsrImm, step_addReg, step_addImm, step_ldrOff, step_rev, step_lsrImm, step_ldrBase]
      refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, ?_⟩
      · simp only [lhs, AsmRun.set_regs, AsmRun.set_mem, reduceCtorEq, if_true, if_false, $hA:term]
        simp only [AsmRun.set_regs, AsmRun.set_mem, reduceCtorEq, if_true, if_false, $h6:term, $h7:term, $h8:term, $h9:term, beBytes,
          ofLimbs, ld64, rev64, off, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat]
        dsimp only [Evm.U256] at *
        bv_decide
      · simp [AsmRun.set_regs]
      · intro r h6' h7' h8' h9' h15 h21
        simp [AsmRun.set_regs, h6', h7', h8', h9', h15, h21]))

set_option maxHeartbeats 16000000 in
/-- **The wide loads read the n bytes at `x26 + x21`, big-endian.** For every
    n in 1..32; TOS zeroed on entry (`loadZeroTos`), so the limbs above the
    immediate stay 0. x21 advances by n; only x6..x9, x15 and x21 change. -/
theorem pushWide_run (H : Helpers) (rest : List AInstr) (n : Nat) (hn1 : 1 ≤ n) (hn : n ≤ 32)
    (s : RS) (A : BitVec 64) (hA : s.regs .x26 + s.regs .x21 = A)
    (h6 : s.regs .x6 = 0) (h7 : s.regs .x7 = 0) (h8 : s.regs .x8 = 0) (h9 : s.regs .x9 = 0) :
    ∃ s', run H (pushWideInstrs n ++ rest) s = run H rest s' ∧
      lhs s' = beBytes (fun i => s.mem (A + BitVec.ofNat 64 i)) n ∧
      s'.regs .x21 = s.regs .x21 + BitVec.ofNat 64 n ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x15 → r ≠ .x21 → s'.regs r = s.regs r) := by
  interval_cases n <;> push_wide_run hA h6 h7 h8 h9

/-! ## The byte fold, in bit vectors -/

/-- The fold's last step: `pushAccum` over k+1 bytes is the k-byte fold with
    byte k shifted in. -/
theorem pushAccum_snoc (code : Nat → Nat) (cs : Nat) :
    ∀ (k pc : Nat) (a : AsmCore.U256), pushAccum code cs pc (k + 1) a =
      shiftInByte (pushAccum code cs pc k a) (if pc + k < cs then code (pc + k) else 0)
  | 0, pc, a => by simp [pushAccum]
  | k + 1, pc, a => by
    rw [pushAccum, pushAccum_snoc code cs k (pc + 1)]
    simp only [pushAccum, Nat.add_zero, show pc + 1 + k = pc + (k + 1) by omega]

/-- Every limb fits 64 bits. -/
def Lim (a : AsmCore.U256) : Prop := a.l0 < 2^64 ∧ a.l1 < 2^64 ∧ a.l2 < 2^64 ∧ a.l3 < 2^64

theorem shiftInByte_lim (a : AsmCore.U256) (b : Nat) (ha : Lim a) (hb : b < 256) : Lim (shiftInByte a b) := by
  obtain ⟨h0, h1, h2, h3⟩ := ha
  simp only [Lim, shiftInByte]
  omega

theorem shiftInByte_toNat (a : AsmCore.U256) (b : Nat) (ha : Lim a) (hb : b < 256) :
    (shiftInByte a b).toNat = (a.toNat * 256 + b) % 2^256 := by
  obtain ⟨h0, h1, h2, h3⟩ := ha
  simp only [shiftInByte, AsmCore.U256.toNat]
  omega

theorem shl8_or (x : BitVec 256) (b : BitVec 8) : (x <<< 8 ||| b.setWidth 256) = x <<< 8 + b.setWidth 256 := by
  bv_decide

theorem toNat_shl8_add (P B : Nat) (hB : B < 256) :
    ((BitVec.ofNat 256 P) <<< 8 + (BitVec.ofNat 8 B).setWidth 256).toNat = (P * 256 + B) % 2 ^ 256 := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := B) (by omega), Nat.mod_eq_of_lt (a := B) (by omega)]
  conv => rhs; rw [Nat.add_mod, Nat.mul_mod]
  conv => lhs; rw [Nat.add_mod]
  simp only [Nat.mod_mod]
  rfl

/-- **The bit-vector fold is the limb fold.** -/
theorem beBytes_eq_pushAccum (code : Nat → Nat) (cs pc : Nat)
    (hb : ∀ i, (if pc + i < cs then code (pc + i) else 0) < 256) :
    ∀ n, beBytes (fun i => BitVec.ofNat 8 (if pc + i < cs then code (pc + i) else 0)) n
        = BitVec.ofNat 256 (pushAccum code cs pc n ⟨0, 0, 0, 0⟩).toNat ∧
      Lim (pushAccum code cs pc n ⟨0, 0, 0, 0⟩)
  | 0 => by simp [beBytes, pushAccum, Lim, AsmCore.U256.toNat]
  | k + 1 => by
    obtain ⟨ih, hl⟩ := beBytes_eq_pushAccum code cs pc hb k
    have hbk := hb k
    refine ⟨?_, ?_⟩
    · rw [pushAccum_snoc, beBytes, ih, shl8_or]
      apply BitVec.eq_of_toNat_eq
      rw [shiftInByte_toNat _ _ hl hbk, toNat_shl8_add _ _ hbk, BitVec.toNat_ofNat]
      exact (Nat.mod_mod _ _).symm
    · rw [pushAccum_snoc]; exact shiftInByte_lim _ _ hl hbk

/-! ## Under the contract: the spec -/

/-- **PUSH-N by wide loads is `pushAccum`.** The code bytes at `cb`, the padding
    contract, the pc (already past the opcode) at most codeSize: the wide loads
    leave in x6..x9 exactly the immediate `Op.denote` pushes — bytes past
    codeSize read as zero — and advance the pc by n. -/
theorem pushWide_correct (H : Helpers) (rest : List AInstr) (n : Nat) (hn1 : 1 ≤ n) (hn : n ≤ 32)
    (code : Nat → Nat) (codeSize pc : Nat) (cb : BitVec 64) (s : RS)
    (h26 : s.regs .x26 = cb) (h21 : s.regs .x21 = BitVec.ofNat 64 pc) (hpc : pc ≤ codeSize)
    (hcode : CodeAt s.mem cb code codeSize) (hbyte : ∀ i < codeSize, code i < 256)
    (hpad : PadContract s.mem cb codeSize)
    (h6 : s.regs .x6 = 0) (h7 : s.regs .x7 = 0) (h8 : s.regs .x8 = 0) (h9 : s.regs .x9 = 0) :
    ∃ s', run H (pushWideInstrs n ++ rest) s = run H rest s' ∧
      lhs s' = BitVec.ofNat 256 (pushAccum code codeSize pc n ⟨0, 0, 0, 0⟩).toNat ∧
      s'.regs .x21 = BitVec.ofNat 64 (pc + n) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x15 → r ≠ .x21 → s'.regs r = s.regs r) := by
  obtain ⟨s', hrun, hv, hpc', hm, hsp, hf, hfr⟩ :=
    pushWide_run H rest n hn1 hn s (cb + BitVec.ofNat 64 pc) (by rw [h26, h21]) h6 h7 h8 h9
  refine ⟨s', hrun, ?_, ?_, hm, hsp, hf, hfr⟩
  · rw [hv, ← (beBytes_eq_pushAccum code codeSize pc (fun i => by
        split
        · exact hbyte _ (by assumption)
        · omega) n).1]
    apply beBytes_congr
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    split
    · exact hcode _ (by assumption)
    · exact hpad _ (by omega) (by omega)
  · rw [hpc', h21, BitVec.ofNat_add]

/-! ## The contract is load-bearing -/

/-- **Without the padding a code-end PUSH is wrong.** A PUSH1 whose immediate is
    the first byte past the code (pc = codeSize), with that byte 1 instead of 0:
    the wide load pushes 1, the spec (EELS's zero-fill) pushes 0. A per-byte
    bounds check made this impossible; the contract is what replaces it. -/
theorem pushWide_needs_padding (H : Helpers) (code : Nat → Nat) (codeSize : Nat) (cb : BitVec 64) (s : RS)
    (h26 : s.regs .x26 = cb) (h21 : s.regs .x21 = BitVec.ofNat 64 codeSize)
    (h6 : s.regs .x6 = 0) (h7 : s.regs .x7 = 0) (h8 : s.regs .x8 = 0) (h9 : s.regs .x9 = 0)
    (hjunk : s.mem (cb + BitVec.ofNat 64 codeSize) = 1) :
    ∃ s', run H (pushWideInstrs 1) s = .done s' ∧
      lhs s' ≠ BitVec.ofNat 256 (pushAccum code codeSize codeSize 1 ⟨0, 0, 0, 0⟩).toNat := by
  obtain ⟨s', hrun, hv, -⟩ :=
    pushWide_run H [] 1 (by omega) (by omega) s (cb + BitVec.ofNat 64 codeSize) (by rw [h26, h21]) h6 h7 h8 h9
  refine ⟨s', by simpa using hrun, ?_⟩
  rw [hv]
  simp [beBytes, pushAccum, shiftInByte, AsmCore.U256.toNat, hjunk]

/-! ## Every read stays in the window -/

/-- The end (exclusive, relative to `x26 + x21`) of each load the program makes,
    tracking x15's offset. -/
def loadEnds : List AInstr → Nat → List Nat
  | [], _ => []
  | .addReg .x15 .x26 .x21 :: rest, _ => loadEnds rest 0
  | .addImm .x15 .x15 k :: rest, o => loadEnds rest (o + k)
  | .ldrBase _ .x15 :: rest, o => (o + 8) :: loadEnds rest o
  | .ldrOff _ .x15 k :: rest, o => (o + k + 8) :: loadEnds rest o
  | _ :: rest, o => loadEnds rest o

/-- **No load reaches past pc + 32.** With pc ≤ codeSize every byte the handler
    reads is in the code or its 32-byte padding. (The only loads are the ones
    `loadEnds` sees: x15-based, after x15 = x26 + x21.) -/
theorem pushWide_reads_window :
    ∀ n ∈ List.range 33, 1 ≤ n → (loadEnds (pushWideInstrs n) 0).all (· ≤ 32) = true ∧
      (pushWideInstrs n).all (fun i => match i with
        | .ldrBase _ b | .ldrOff _ b _ => b == .x15 | _ => true) = true := by
  decide

/-! ## x86-64 -/

/-- Live across the handler body: the TOS cache and the pinned registers. -/
def Lpush : List Reg := [.x6, .x7, .x8, .x9, .x20, .x21, .x22, .x23, .x24, .x26]

/-- The liveness/provenance certificate of the lowering, computed for each n. -/
theorem pushWide_frag (n : Nat) (hn1 : 1 ≤ n) (hn : n ≤ 32) :
    ∃ L' p', fragB [] (pushWideInstrs n) Lpush .unknown = some (L', p') ∧ ∀ r ∈ Lpush, r ∈ L' := by
  interval_cases n <;> exact ⟨_, _, rfl, by decide⟩

theorem pushWide_labelsOk (n : Nat) (hn1 : 1 ≤ n) (hn : n ≤ 32) : LabelsOk (pushWideInstrs n) := by
  interval_cases n <;> exact LabelsOk_of_lokB _ (by decide)

/-- **The x86-64 bytes.** The lowered program (`mov`+`bswap` per limb), run on
    the x86-64 machine from a state related to the ARM-level one, falls off its
    end related to the state `pushWide_correct` describes: r8..r11 (the homes of
    x6..x9) hold the immediate `pushAccum` gives, rbp the advanced pc. -/
theorem pushWide_x86 (H : Helpers) (HX : XHelpers) (hfns : HX.fns = H) (hconv : H.conv = X86Sem.x86Conv)
    (hsym : ∀ h, HX.sym s!"Lsym_{h}" = h)
    (hjunk : ∀ h (s : RS) (x : XS) y, x.mem = s.mem → x.regs .rsp = s.sp → HX.junk h x y = H.junk h s y)
    (n : Nat) (hn1 : 1 ≤ n) (hn : n ≤ 32)
    (code : Nat → Nat) (codeSize pc : Nat) (cb : BitVec 64) (s : RS) (x : XS) (hR : Rel Lpush .unknown s x)
    (h26 : s.regs .x26 = cb) (h21 : s.regs .x21 = BitVec.ofNat 64 pc) (hpc : pc ≤ codeSize)
    (hcode : CodeAt s.mem cb code codeSize) (hbyte : ∀ i < codeSize, code i < 256)
    (hpad : PadContract s.mem cb codeSize)
    (h6 : s.regs .x6 = 0) (h7 : s.regs .x7 = 0) (h8 : s.regs .x8 = 0) (h9 : s.regs .x9 = 0) :
    ∃ s' x', xrun HX (progItems (pushWideInstrs n)) x = .done x' ∧ Rel Lpush .unknown s' x' ∧
      lhs s' = BitVec.ofNat 256 (pushAccum code codeSize pc n ⟨0, 0, 0, 0⟩).toNat ∧
      s'.regs .x21 = BitVec.ofNat 64 (pc + n) := by
  obtain ⟨s', hrun, hv, h21', -⟩ :=
    pushWide_correct H [] n hn1 hn code codeSize pc cb s h26 h21 hpc hcode hbyte hpad h6 h7 h8 h9
  obtain ⟨L', p', hB, hsup⟩ := pushWide_frag n hn1 hn
  have hOk : Ok (annOf []) Lpush .unknown (pushWideInstrs n) Lpush .unknown :=
    Ok_of_Frag (Frag.ofB_sup (Lend := Lpush) (pend := .unknown) Lpush hB hsup) (Or.inr ⟨fun _ h => h, Or.inl rfl⟩)
  have hsim := sim_run H HX (annOf []) Lpush .unknown hfns hconv hsym hjunk _ (pushWideInstrs n) (Nat.le_refl _)
    Lpush .unknown s x hOk (pushWide_labelsOk n hn1 hn) hR
  rw [List.append_nil] at hrun
  rw [hrun, run_nil] at hsim
  obtain ⟨s'', x', h⟩ := hsim
  rcases h with ⟨⟨h1, h2⟩ | ⟨h1, _⟩, hRel⟩ | ⟨_, _, _, h1, _, _⟩
  · cases h1
    exact ⟨s', x', h2, hRel, hv, h21'⟩
  · cases h1
  · cases h1

end Evm.CL.PushWide
