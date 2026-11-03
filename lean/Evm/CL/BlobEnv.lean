/-
  Evm.CL.BlobEnv — BLOBHASH (0x49, EIP-4844) and BLOBBASEFEE (0x4a, EIP-7516): the two
  handlers that pushed 0.

  Until 2026-10-25 both native handlers were stubs: `blobhashBody` replaced the index
  with 0 and BLOBBASEFEE was `pushZeroBody`, because the frame state carried neither the
  tx's versioned hashes nor the block's blob base fee. Mainnet rollup inboxes read
  BLOBHASH in every batch-posting tx from Cancun (19,426,587) on, so a replay past Cancun
  diverged on the first blob batch: the inbox saw "no blob" and reverted where the chain
  accepted. There was nothing to prove false — the stub denoted exactly what it did.

  Now EvmState carries the tx's hash table (#552, count #560; installed by the host per
  tx, empty for a non-blob tx) and the block's blob base fee (#568; the emitted
  `spec-blob-base-fee`, computed once per block). `AsmCore.blobhashLookup` denotes EELS
  `blob_hash` — `hashes[index]` when `index < len(hashes)`, else 0 — with the range test
  over all four limbs of the index, and BLOBBASEFEE is `envU256Body 568`. The theorems
  below pin: the in-range, out-of-range and wide-index cases; the handler's value against
  the spec's `blobHashAt` under the host's table contract; BLOBBASEFEE against the fee
  the host wrote; and the old stub as a counterexample, so it cannot come back as
  "equivalent".
-/

import Evm.CL.AsmCore
import Evm.Cancun.Spec.BlobhashStep
import Evm.Prague.Spec.BlobSchedule

namespace Evm.CL.BlobEnv

open Evm.CL.AsmCore

/-- An index that fits u64. -/
def narrow (a : AsmCore.U256) : Prop := a.l1 = 0 ∧ a.l2 = 0 ∧ a.l3 = 0

/-- A Nat as the four little-endian limbs the host writes (`u256-write`). -/
def limbsOf (n : Nat) : AsmCore.U256 :=
  ⟨n % 2^64, n / 2^64 % 2^64, n / 2^128 % 2^64, n / 2^192 % 2^64⟩

theorem limbsOf_zero : limbsOf 0 = AsmCore.U256.ofScalar 0 := by
  simp [limbsOf, AsmCore.U256.ofScalar]

/-- The limbs read back as the number, for every value that fits 256 bits. -/
theorem limbsOf_toNat (n : Nat) (h : n < 2^256) : (limbsOf n).toNat = n := by
  simp only [limbsOf, AsmCore.U256.toNat, Nat.reducePow] at *
  omega

/-! ## BLOBHASH -/

/-- A narrow index below the count reads the table at its low limb; gas charged, sp
    unchanged (pop 1, push 1). -/
theorem blobhash_in_range (m : Mach) (cost : Nat)
    (hsp : 1 ≤ m.sp) (hg : cost ≤ m.gas) (hn : narrow m.tos) (hb : m.tos.l0 < m.stateMem 560) :
    let m' := (blobhashBody cost).denote m
    m'.tos = m.blobHash m.tos.l0 ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp := by
  obtain ⟨h1, h2, h3⟩ := hn
  simp [Prog.denote, blobhashBody, Op.denote, Nat.not_lt.2 hsp, Nat.not_lt.2 hg,
        h1, h2, h3, hb]

/-- **An index at or past the count pushes 0** — whatever the table holds there. -/
theorem blobhash_out_of_range_zero (m : Mach) (cost : Nat)
    (hsp : 1 ≤ m.sp) (hg : cost ≤ m.gas) (hb : m.stateMem 560 ≤ m.tos.l0) :
    let m' := (blobhashBody cost).denote m
    m'.tos = AsmCore.U256.ofScalar 0 ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp := by
  have hw' : ¬ (m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0 ∧ m.tos.l0 < m.stateMem 560) :=
    fun ⟨_, _, _, h⟩ => absurd h (Nat.not_lt.2 hb)
  simp [Prog.denote, blobhashBody, Op.denote, Nat.not_lt.2 hsp, Nat.not_lt.2 hg, hw']

/-- **An index that does not fit u64 pushes 0, never the entry at its low limb** — the
    #260 / JUMP width class: `2^64 + 0` is not index 0. -/
theorem blobhash_wide_index_zero (m : Mach) (cost : Nat)
    (hsp : 1 ≤ m.sp) (hg : cost ≤ m.gas) (hw : ¬ narrow m.tos) :
    let m' := (blobhashBody cost).denote m
    m'.tos = AsmCore.U256.ofScalar 0 ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp := by
  have hw' : ¬ (m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0 ∧ m.tos.l0 < m.stateMem 560) :=
    fun ⟨h1, h2, h3, _⟩ => hw ⟨h1, h2, h3⟩
  simp [Prog.denote, blobhashBody, Op.denote, Nat.not_lt.2 hsp, Nat.not_lt.2 hg, hw']

/-- The host's contract for EvmState #552/#560 (src/evm/frames.lisp `install-blob-env!`): the
    count is the tx's number of versioned hashes and entry `i` of the table is hash `i`
    as four limbs. -/
def HostTable (m : Mach) (env : Evm.Frontier.Vm.Environment) : Prop :=
  m.stateMem 560 = env.blobVersionedHashes.length ∧
  m.stateMem 560 < 2^64 ∧
  ∀ i, i < env.blobVersionedHashes.length →
    m.blobHash i = limbsOf (BitVec.toNat ((env.blobVersionedHashes[i]?).getD 0))

/-- **The handler is the spec** (`Evm.Cancun.Spec.blobHashAt`, EELS `blob_hash`): under
    the host's table contract, for every index — narrow or not — the pushed word is the
    spec's hash at `index.toNat`, as limbs. The index's limbs are u64s (the stack holds
    nothing else). -/
theorem blobhash_is_spec (m : Mach) (env : Evm.Frontier.Vm.Environment) (cost : Nat)
    (hsp : 1 ≤ m.sp) (hg : cost ≤ m.gas) (ht : HostTable m env)
    (h0 : m.tos.l0 < 2^64) (h1 : m.tos.l1 < 2^64) (h2 : m.tos.l2 < 2^64) (h3 : m.tos.l3 < 2^64) :
    ((blobhashBody cost).denote m).tos
      = limbsOf (BitVec.toNat (Evm.Cancun.Spec.blobHashAt env m.tos.toNat)) := by
  obtain ⟨hcount, hc64, htab⟩ := ht
  by_cases hn : narrow m.tos
  · obtain ⟨e1, e2, e3⟩ := hn
    have htos : m.tos.toNat = m.tos.l0 := by
      simp [AsmCore.U256.toNat, e1, e2, e3]
    rw [htos]
    by_cases hb : m.tos.l0 < m.stateMem 560
    · rw [(blobhash_in_range m cost hsp hg ⟨e1, e2, e3⟩ hb).1]
      rw [hcount] at hb
      rw [htab _ hb]
      simp [Evm.Cancun.Spec.blobHashAt, List.getElem?_eq_getElem hb]
    · rw [(blobhash_out_of_range_zero m cost hsp hg (Nat.not_lt.1 hb)).1]
      rw [hcount] at hb
      simp [Evm.Cancun.Spec.blobHashAt, List.getElem?_eq_none_iff.2 (Nat.not_lt.1 hb), limbsOf_zero]
  · rw [(blobhash_wide_index_zero m cost hsp hg hn).1]
    -- a wide index is ≥ 2^64 > the count, so the spec reads past the list: 0
    have hbig : env.blobVersionedHashes.length ≤ m.tos.toNat := by
      simp only [narrow] at hn
      simp only [AsmCore.U256.toNat, Nat.reducePow] at *
      omega
    simp [Evm.Cancun.Spec.blobHashAt, List.getElem?_eq_none_iff.2 hbig, limbsOf_zero]

/-! ## BLOBBASEFEE -/

/-- The host's contract for EvmState #568 (src/evm/frames.lisp `install-blob-env!`): the
    block's blob base fee, `calculate_blob_gas_price` at the block's fork
    (the emitted `spec-blob-base-fee`, `Evm.CL.GasEmitCancun.blobBaseFee_eq_spec`). -/
def HostFee (m : Mach) (f : Evm.Fork) (excess : Nat) : Prop :=
  let fee := limbsOf (Evm.Prague.Spec.calculateBlobGasPriceAt f excess)
  m.stateMem 568 = fee.l0 ∧ m.stateMem 576 = fee.l1 ∧ m.stateMem 584 = fee.l2 ∧ m.stateMem 592 = fee.l3

/-- **BLOBBASEFEE pushes the block's blob base fee** (EELS `blob_base_fee`:
    `push(U256(calculate_blob_gas_price(excess_blob_gas)))`, GAS_BASE), as the limbs the
    host wrote; gas charged, one word pushed. -/
theorem blobbasefee_is_spec (m : Mach) (cost : Nat) (f : Evm.Fork) (excess : Nat)
    (hsp : m.sp < 1024) (hg : cost ≤ m.gas) (hf : HostFee m f excess) :
    let m' := (envU256Body 568 cost).denote m
    m'.tos = limbsOf (Evm.Prague.Spec.calculateBlobGasPriceAt f excess)
    ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp + 1 := by
  obtain ⟨e0, e1, e2, e3⟩ := hf
  have := envU256_correct 568 cost m hsp hg
  simp only [Prog.denote, envU256Body, Op.denote] at this ⊢
  refine ⟨?_, this.2.1, this.2.2⟩
  rw [this.1, e0, e1, e2, e3]

/-! ## The old handlers, as counterexamples -/

/-- The stub exactly as it was: pop the index, push 0. -/
def blobhashStub (cost : Nat) : Prog := [.underflow 1, .loadZeroTos, .storeTos, .exitGas cost]

/-- A machine with one blob hash installed and index 0 on the stack, the rest inert. -/
def machWithOneHash (h : AsmCore.U256) : Mach :=
  { gas := 100, sp := 1, pcReg := 0, tos := AsmCore.U256.ofScalar 0, nos := AsmCore.U256.ofScalar 0,
    mem := fun _ => AsmCore.U256.ofScalar 0,
    stateMem := fun off => if off = 560 then 1 else 0,
    helperFn := fun _ a _ => a, helperFn3 := fun _ a _ _ => a,
    cbGas := 0, cbResult := AsmCore.U256.ofScalar 0,
    evmMem := fun _ => AsmCore.U256.ofScalar 0, memSize := 0, memCap := 0,
    acc := 0, scratch := 0, code := fun _ => 0, codeSize := 0,
    blobHash := fun i => if i = 0 then h else AsmCore.U256.ofScalar 0,
    isStatic := false, oog := false, trap := false, ret := false, halted := false }

/-- **The stub is wrong on the first blob tx**: with one hash installed, BLOBHASH 0 must
    push it; the stub pushed 0 — which is why every rollup inbox reverted. -/
theorem stub_is_wrong :
    let h : AsmCore.U256 := ⟨1, 2, 3, 4⟩
    ((blobhashStub 3).denote (machWithOneHash h)).tos = AsmCore.U256.ofScalar 0 ∧
    ((blobhashBody 3).denote (machWithOneHash h)).tos = h := by
  constructor <;> decide

/-- The old BLOBBASEFEE (`pushZeroBody`, deleted) pushed 0 whatever the host held at #568;
    the fee is at least the 1-wei floor, so the two never agreed on any block. -/
theorem fee_floor_is_positive (f : Evm.Fork) (excess : Nat) :
    0 < Evm.Prague.Spec.calculateBlobGasPriceAt f excess ∨
    Evm.Prague.Spec.calculateBlobGasPriceAt f 0 = 1 := by
  right
  cases f <;> native_decide

end Evm.CL.BlobEnv
