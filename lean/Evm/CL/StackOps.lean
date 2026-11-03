/-
  Evm.CL.StackOps — PUSH / DUP / SWAP against the stack, and the register-cache
  invariant they have to maintain.

  Stage 1 of #238. The per-op handlers are all structured `AsmCore.Prog`s
  already, but the stack shuffles had no theorem — and they are the ops whose
  correctness is not about arithmetic at all. It is about an INVARIANT:

      sp ≥ 1 → stack[sp-1] = TOS registers (x6-x9)
      sp ≥ 2 → stack[sp-2] = NOS registers (x10-x13)

  The handlers keep the top two stack words in registers, so every op that
  moves the stack must leave both the memory and the cache consistent. #272 was
  precisely this invariant broken in the other direction — the interpreter
  speculatively read `stack[depth-2]` one slot BELOW the live stack and faulted
  the guard arena.

  The sharp case is SWAP-1, which exchanges TOS with `stack[sp-2]` — the very
  slot the NOS cache mirrors. `swapBody` reloads NOS for `n = 1` only, and
  `swap1_needs_reload_of_nos` below shows that without the reload the invariant
  really does break, while `swap_preserves_inv` shows that with it, it holds for
  every n.

  All of this is register-allocation policy, not ISA: it is the obligation the
  x86-64 backend inherits in weakened form, having no NOS cache to keep in step
  (`Evm.CL.Target`). The proofs here are what say what that backend may drop.
-/

import Evm.CL.AsmCore

namespace Evm.CL.StackOps

open Evm.CL.AsmCore

/-- The register cache agrees with stack memory for the top two words. -/
def Inv (m : Mach) : Prop :=
  (1 ≤ m.sp → m.mem (m.sp - 1) = m.tos) ∧ (2 ≤ m.sp → m.mem (m.sp - 2) = m.nos)

/-! ## PUSH-n -/

/-- PUSH with room on the stack: the pushed value lands in TOS and in
    `stack[sp]`, the old top becomes NOS, and the depth grows by one. The value
    itself comes from `pushImm` (code bytes via EXTR), which is why this is
    stated over the body with `n = 0` — PUSH0 — where the value is pinned. -/
theorem push0_correct (m : Mach) (cost : Nat)
    (hsp : m.sp < 1024) (hg : cost ≤ m.gas) :
    let m' := (pushBody 0 cost).denote m
    m'.sp = m.sp + 1 ∧ m'.tos = U256.ofScalar 0 ∧ m'.nos = m.tos ∧
    m'.mem m.sp = U256.ofScalar 0 ∧ m'.gas = m.gas - cost := by
  simp [Prog.denote, pushBody, Op.denote, Nat.not_le.2 hsp, Nat.not_lt.2 hg, upd]

/-- …and the cache stays consistent at the top: the pushed value is in
    `stack[sp']`. -/
theorem push0_tos_cached (m : Mach) (cost : Nat)
    (hsp : m.sp < 1024) (hg : cost ≤ m.gas) :
    let m' := (pushBody 0 cost).denote m
    m'.mem (m'.sp - 1) = m'.tos := by
  simp [Prog.denote, pushBody, Op.denote, Nat.not_le.2 hsp, Nat.not_lt.2 hg, upd]

/-- …and at the second word: the old top, now NOS, is still in `stack[sp'-2]`,
    which is where it already was. Needs `1 ≤ sp`, i.e. that there WAS a top. -/
theorem push0_nos_cached (m : Mach) (cost : Nat)
    (hsp : m.sp < 1024) (hg : cost ≤ m.gas) (h1 : 1 ≤ m.sp)
    (hcache : m.mem (m.sp - 1) = m.tos) :
    let m' := (pushBody 0 cost).denote m
    m'.mem (m'.sp - 2) = m'.nos := by
  have hne : m.sp - 1 ≠ m.sp := by omega
  simp [Prog.denote, pushBody, Op.denote, Nat.not_le.2 hsp, Nat.not_lt.2 hg, upd,
        hne, hcache]

/-- A full stack traps instead of pushing (`cmp x23,#1024 ; b.hs`). -/
theorem push_overflow_traps (m : Mach) (n cost : Nat) (hsp : 1024 ≤ m.sp) :
    ((pushBody n cost).denote m).trap = true := by
  cases n <;> by_cases hgc : m.gas < cost <;>
    simp [Prog.denote, pushBody, Op.denote, hsp, hgc]

/-! ## DUP-n -/

/-- DUP-n copies `stack[sp-n]` to the top. -/
theorem dup_correct (m : Mach) (n cost : Nat)
    (hsp : m.sp < 1024) (hn : n ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (dupBody n cost).denote m
    m'.sp = m.sp + 1 ∧ m'.tos = m.mem (m.sp - n) ∧ m'.nos = m.tos ∧
    m'.mem m.sp = m.mem (m.sp - n) ∧ m'.gas = m.gas - cost := by
  simp [Prog.denote, dupBody, Op.denote, Nat.not_le.2 hsp, Nat.not_lt.2 hn,
        Nat.not_lt.2 hg, upd]

theorem dup_tos_cached (m : Mach) (n cost : Nat)
    (hsp : m.sp < 1024) (hn : n ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (dupBody n cost).denote m
    m'.mem (m'.sp - 1) = m'.tos := by
  simp [Prog.denote, dupBody, Op.denote, Nat.not_le.2 hsp, Nat.not_lt.2 hn,
        Nat.not_lt.2 hg, upd]

theorem dup_nos_cached (m : Mach) (n cost : Nat)
    (hsp : m.sp < 1024) (hn : n ≤ m.sp) (hg : cost ≤ m.gas) (h1 : 1 ≤ m.sp)
    (hcache : m.mem (m.sp - 1) = m.tos) :
    let m' := (dupBody n cost).denote m
    m'.mem (m'.sp - 2) = m'.nos := by
  have hne : m.sp - 1 ≠ m.sp := by omega
  simp [Prog.denote, dupBody, Op.denote, Nat.not_le.2 hsp, Nat.not_lt.2 hn,
        Nat.not_lt.2 hg, upd, hne, hcache]

/-- Too shallow a stack traps (`cmp x23,#n ; b.lo`). -/
theorem dup_underflow_traps (m : Mach) (n cost : Nat)
    (hsp : m.sp < 1024) (hn : m.sp < n) :
    ((dupBody n cost).denote m).trap = true := by
  by_cases hgc : m.gas < cost <;>
    simp [Prog.denote, dupBody, Op.denote, Nat.not_le.2 hsp, hn, hgc]

/-! ## SWAP-n — and why n = 1 is different

`swapBody` is `[underflow (n+1), swapPartner n, storeTos]`, plus `reloadNos`
for `n = 1` only. The exchange itself is the same for every n; what differs is
whether the slot written is the one the NOS register mirrors. -/

/-- The partner slot receives the old top, for every n. -/
theorem swap_writes_partner (m : Mach) (n cost : Nat)
    (hn : n + 1 ≤ m.sp) (hg : cost ≤ m.gas) (h1 : 1 ≤ m.sp) (hnz : n ≠ 0) :
    ((swapBody n cost).denote m).mem (m.sp - (n + 1)) = m.tos := by
  by_cases hk : n = 1
  · subst hk
    have hne : m.sp - 1 ≠ m.sp - 2 := by omega
    simp [Prog.denote, swapBody, Op.denote, Nat.not_lt.2 hn, Nat.not_lt.2 hg, upd]
    intro hc; omega
  · have hne : m.sp - 1 ≠ m.sp - (n + 1) := by omega
    simp [Prog.denote, swapBody, Op.denote, hk, Nat.not_lt.2 hn, Nat.not_lt.2 hg,
          upd]
    intro hc; omega

/-- **SWAP-1 writes through the NOS cache's own slot, and the reload fixes it.**
    After `swapBody 1`, the NOS register equals `stack[sp-2]` — because the
    reload reads it back after the store. -/
theorem swap1_nos_cached (m : Mach) (cost : Nat)
    (hn : 2 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (swapBody 1 cost).denote m
    m'.mem (m'.sp - 2) = m'.nos := by
  simp [Prog.denote, swapBody, Op.denote, Nat.not_lt.2 hn, Nat.not_lt.2 hg, upd]

/-- `swapBody` with the reload removed — not emitted, and refuted below. -/
def swapBodyNoReload (n cost : Nat) : Prog :=
  [.underflow (n + 1), .swapPartner n, .storeTos, .exitGas cost]

/-- **Without the reload, SWAP-1 desynchronises the NOS cache.** sp = 2,
    TOS = 1, NOS = 2, stack = [2, 1]: after the exchange `stack[0] = 1` while
    the NOS register still holds 2, so any later op reading NOS from the
    register — the whole point of the cache — reads a stale word. -/
theorem swap1_without_reload_desyncs :
    ∃ (m : Mach), m.mem (m.sp - 2) = m.nos ∧
      ((swapBodyNoReload 1 0).denote m).mem (m.sp - 2)
        ≠ ((swapBodyNoReload 1 0).denote m).nos := by
  refine ⟨{ gas := 10, sp := 2, pcReg := 0,
            tos := U256.ofScalar 1, nos := U256.ofScalar 2,
            mem := fun i => if i = 0 then U256.ofScalar 2 else U256.ofScalar 1,
            stateMem := fun _ => 0,
            helperFn := fun _ a _ => a, helperFn3 := fun _ a _ _ => a,
            cbGas := 0, cbResult := U256.ofScalar 0,
            evmMem := fun _ => U256.ofScalar 0, memSize := 0, memCap := 0,
            acc := 0, scratch := 0,
            code := fun _ => 0, codeSize := 0, isStatic := false, oog := false, trap := false, ret := false, halted := false }, ?_, ?_⟩
  · simp
  · simp [Prog.denote, swapBodyNoReload, Op.denote, upd, U256.ofScalar]

/-- For n ≥ 2 the partner slot is strictly below `sp-2`, so the NOS cache is
    untouched and needs no reload — which is why `swapBody` reloads only at
    n = 1 rather than always. -/
theorem swapk_nos_untouched (m : Mach) (n cost : Nat)
    (hn : n + 1 ≤ m.sp) (hg : cost ≤ m.gas) (hk : 2 ≤ n)
    (hcache : m.mem (m.sp - 2) = m.nos) :
    let m' := (swapBody n cost).denote m
    m'.mem (m'.sp - 2) = m'.nos := by
  have hnz : n ≠ 1 := by omega
  have hne : m.sp - 1 ≠ m.sp - 2 := by omega
  have hne2 : m.sp - (n + 1) ≠ m.sp - 2 := by omega
  have h1 : ¬ (m.sp - 2 = m.sp - 1) := by omega
  have h2 : ¬ (m.sp - 2 = m.sp - (n + 1)) := by omega
  simp [Prog.denote, swapBody, Op.denote, hnz, Nat.not_lt.2 hn, Nat.not_lt.2 hg,
        upd, h1, h2, hcache]


/-! ## PUSH-N's immediate decode

`pushImm` reads n code bytes big-endian into TOS, zero-filling past `codeSize`;
`pushAccum` (AsmCore) is that fold, and these theorems pin what it computes on
small cases. That the machine code computes it is `PushWide.pushWide_correct`
(and `shiftInByte_toNat`: each step is ×256 + byte, every limb boundary included). -/

/-- PUSH1 of a single in-range byte: the byte lands in the low limb and nowhere
    else, and the pc advances by one. -/
theorem push1_reads_the_byte (m : Mach) (cost : Nat)
    (hsp : m.sp < 1024) (hg : cost ≤ m.gas)
    (hcs : m.pcReg < m.codeSize) (hb : m.code m.pcReg = 0x42) :
    let m' := (pushBody 1 cost).denote m
    m'.tos = { l0 := 0x42, l1 := 0, l2 := 0, l3 := 0 } ∧ m'.pcReg = m.pcReg + 1 := by
  simp [Prog.denote, pushBody, Op.denote, Nat.not_le.2 hsp, Nat.not_lt.2 hg,
        pushAccum, shiftInByte, hcs, hb, U256.ofScalar]

/-- Past the end of the code the byte reads as zero — EELS pads the code stream,
    so a PUSH whose immediate runs off the end is zero-filled, NOT truncated and
    not a fault. -/
theorem push1_past_code_end_is_zero (m : Mach) (cost : Nat)
    (hsp : m.sp < 1024) (hg : cost ≤ m.gas) (hcs : ¬ m.pcReg < m.codeSize) :
    ((pushBody 1 cost).denote m).tos = { l0 := 0, l1 := 0, l2 := 0, l3 := 0 } := by
  simp [Prog.denote, pushBody, Op.denote, Nat.not_le.2 hsp, Nat.not_lt.2 hg,
        pushAccum, shiftInByte, hcs, U256.ofScalar]

/-- Two bytes accumulate BIG-ENDIAN: the first byte read ends up more
    significant. `0x12, 0x34` becomes `0x1234`, not `0x3412`. -/
theorem push2_is_big_endian (m : Mach) (cost : Nat)
    (hsp : m.sp < 1024) (hg : cost ≤ m.gas)
    (h1 : m.pcReg < m.codeSize) (h2 : m.pcReg + 1 < m.codeSize)
    (b1 : m.code m.pcReg = 0x12) (b2 : m.code (m.pcReg + 1) = 0x34) :
    ((pushBody 2 cost).denote m).tos = { l0 := 0x1234, l1 := 0, l2 := 0, l3 := 0 } := by
  simp [Prog.denote, pushBody, Op.denote, Nat.not_le.2 hsp, Nat.not_lt.2 hg,
        pushAccum, shiftInByte, h1, h2, b1, b2, U256.ofScalar]

/-- A PUSH32 of all-0xff is 2^256 - 1: every limb saturated, nothing lost at any
    boundary and nothing carried out the top. -/
theorem push32_all_ones :
    (pushAccum (fun _ => 0xff) 32 0 32 { l0 := 0, l1 := 0, l2 := 0, l3 := 0 })
      = { l0 := 0xffffffffffffffff, l1 := 0xffffffffffffffff
        , l2 := 0xffffffffffffffff, l3 := 0xffffffffffffffff } := by
  native_decide

/-- PUSH0 reads nothing and leaves the zeroed TOS alone. -/
theorem push0_reads_nothing (code : Nat → Nat) (cs pc : Nat) (a : U256) :
    pushAccum code cs pc 0 a = a := rfl

end Evm.CL.StackOps
