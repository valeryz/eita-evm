/-! # CL/AsmCore — a typed, denotational ARM64 micro-DSL

`Evm.CL.ARM64` emits handlers as raw `String`s, so a *wrong* instruction is
invisible to any checker — the two worst bugs this cycle were exactly that:
MSIZE loading `[x20,#24]` (`mp`) instead of `#48` (`memory_size`), and a bare
`sub x22` gas charge instead of the OOG-checked `subs;b.lo`.

This module represents handlers as a small `Op` IR with **two interpretations of
one term** — `emit` (the asm) and `denote` (semantics over an abstract
register-cached-stack machine) — the same pattern as `Evm.CL.HostEmit`
(`toCL`/`eval`) and `Expr`/`SymExpr`. With a denotation we can *prove* a handler
equals its spec; with `emit` byte-identical to the hand-written asm, the ported
handlers drop into `ARM64.lean` with `handlers.S` unchanged.

The machine mirrors the handler ABI: the top two EVM stack cells are cached in
registers (`tos` = x6-x9, `nos` = x10-x13, four 64-bit limbs each = a `U256`),
`gas` = x22, `sp` = x23 (depth), `pcReg` = x21, EvmState fields by NAME, the
stack memory, and trap flags. Covers the value-pusher family (MSIZE/PC/GAS) and
the bitwise binary family (AND/OR/XOR); the next stage adds add/sub/compare. -/

namespace Evm.CL.AsmCore

/-- Named EvmState fields; the byte offset (the MSIZE bug) lives in `offset`. -/
inductive Field where
  | pc | gasLeft | sp | mp | memSize | memCap
  deriving DecidableEq, Repr

def Field.offset : Field → Nat
  | .pc => 0 | .gasLeft => 8 | .sp => 16
  | .mp => 24 | .memSize => 48 | .memCap => 56

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-- A 256-bit word as four 64-bit limbs (l0 least significant) — the
    register-cached representation (x6=l0 … x9=l3 for the top of stack). -/
structure U256 where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A scalar (e.g. MSIZE/GAS/PC) as a U256: value in limb0, high limbs zero. -/
def U256.ofScalar (n : Nat) : U256 := ⟨n, 0, 0, 0⟩

/-- Leading zero bits of a 256-bit value: `256 − bit_length n` (EIP-7939, EELS
    `count_leading_zeros`); `bit_length 0 = 0`, else `log2 n + 1`. The machine
    computes it limb-wise (`clzReduce`); this is what that asm denotes. -/
@[irreducible] def clzNat (n : Nat) : Nat := if n = 0 then 256 else 255 - Nat.log2 n
/-- AArch64 `clz` on a 64-bit limb: 64 for 0, else `63 − log2 x`. -/
@[irreducible] def clz64 (x : Nat) : Nat := if x = 0 then 64 else 63 - Nat.log2 x
/-- What the `clzReduce` asm computes: the first non-zero limb from the top decides,
    lower limbs add 64 each (`clz(l3)`, `64 + clz(l2)`, `128 + clz(l1)`, `192 + clz(l0)`). -/
@[irreducible] def clzLimbs (a : U256) : Nat :=
  if a.l3 ≠ 0 then clz64 a.l3
  else if a.l2 ≠ 0 then 64 + clz64 a.l2
  else if a.l1 ≠ 0 then 128 + clz64 a.l1
  else 192 + clz64 a.l0

/-- Bitwise binary op kinds (the ARM64 mnemonic + the per-limb Nat function). -/
inductive BitOp where | and | orr | eor
  deriving DecidableEq, Repr

def BitOp.mnem : BitOp → String
  | .and => "and" | .orr => "orr" | .eor => "eor"

def BitOp.apply : BitOp → Nat → Nat → Nat
  | .and => Nat.land | .orr => Nat.lor | .eor => Nat.xor

/-- Limb-wise application — exactly what `{op} xD,xA,xB` over four limbs does,
    and exactly the EVM AND/OR/XOR semantics (a u256 bitwise op IS limb-wise). -/
def U256.bin (op : BitOp) (a b : U256) : U256 :=
  ⟨op.apply a.l0 b.l0, op.apply a.l1 b.l1, op.apply a.l2 b.l2, op.apply a.l3 b.l3⟩

/-- The integer value of a U256 (l0 least significant). -/
def U256.toNat (a : U256) : Nat :=
  a.l0 + a.l1 * 2^64 + a.l2 * 2^128 + a.l3 * 2^192

/-- 4-limb add with carry — exactly `adds;adcs;adcs;adc` (final carry dropped,
    i.e. mod 2^256). Each limb is (sum mod 2^64), carry = (sum / 2^64). -/
def U256.addChain (a b : U256) : U256 :=
  let s0 := a.l0 + b.l0
  let s1 := a.l1 + b.l1 + s0 / 2^64
  let s2 := a.l2 + b.l2 + s1 / 2^64
  let s3 := a.l3 + b.l3 + s2 / 2^64
  ⟨s0 % 2^64, s1 % 2^64, s2 % 2^64, s3 % 2^64⟩

/-- 4-limb subtract with borrow — exactly `subs;sbcs;sbcs;sbc` (mod 2^256).
    `aᵢ + 2^64 − bᵢ − borrowᵢ`: quotient 1 = no borrow, 0 = borrow. -/
def U256.subChain (a b : U256) : U256 :=
  let d0 := a.l0 + 2^64 - b.l0
  let d1 := a.l1 + 2^64 - b.l1 - (1 - d0 / 2^64)
  let d2 := a.l2 + 2^64 - b.l2 - (1 - d1 / 2^64)
  let d3 := a.l3 + 2^64 - b.l3 - (1 - d2 / 2^64)
  ⟨d0 % 2^64, d1 % 2^64, d2 % 2^64, d3 % 2^64⟩

inductive ArithKind where | add | sub
  deriving DecidableEq, Repr

def ArithKind.mnems : ArithKind → String × String × String
  | .add => ("adds", "adcs", "adc")
  | .sub => ("subs", "sbcs", "sbc")

def ArithKind.apply : ArithKind → U256 → U256 → U256
  | .add => U256.addChain | .sub => U256.subChain

/-- Two's-complement signed value of a u256 (for SLT/SGT). -/
def U256.toSigned (a : U256) : Int :=
  if a.toNat < 2^255 then (a.toNat : Int) else (a.toNat : Int) - (2^256 : Int)

/-- Comparison condition after the subs-chain: `lo` (unsigned below, = ¬carry)
    or `lt` (signed less, = N≠V). NOTE the Z-dependent conditions (eq/ne/hi/ls)
    are NOT modelled — they are unreliable after a chained sbcs (see
    `chained_z_unreliable`), which is why EQ uses a separate XOR-fold handler. -/
inductive CmpCond where | lo | lt
  deriving DecidableEq, Repr

def CmpCond.mnem : CmpCond → String | .lo => "lo" | .lt => "lt"

/-- The 0/1 result of `cmp{,Swapped} … ; cset cond`. `swapped` selects whether
    the chain computes (tos−nos) or (nos−tos). `lo` ⇒ unsigned <, `lt` ⇒ signed
    <, on (minuend, subtrahend). -/
def cmpResult (swapped : Bool) (cond : CmpCond) (tos nos : U256) : Nat :=
  let a := if swapped then nos else tos
  let b := if swapped then tos else nos
  match cond with
  | .lo => if a.toNat < b.toNat then 1 else 0
  | .lt => if a.toSigned < b.toSigned then 1 else 0

/-! ## PUSH-N immediate decode — the spec fold

`pushImm n` reads n code bytes big-endian into TOS, zero-filling past
`code_size` (EELS `push_n`: `buffer_read(evm.code, pc + 1, n)` then
`U256.from_be_bytes`). `pushAccum` states that as a fold, one byte at a time:
the 256-bit value shifted left 8 bits with the byte in the low 8. It is the
SPEC the handler is held to; the machine code is `pushWideInstrs` (whole-limb
loads), and `PushWide.pushWide_correct` proves the loads compute this fold.

In limbs, a shift-left-by-8 must take each limb's new high byte from the limb
below BEFORE that limb is shifted — written low-to-high it would feed
already-shifted limbs upward and lose a byte per step (`shiftInByte`). -/

/-- One step of the fold: the 256-bit value shifted left 8 bits, with `b` in the
    low byte, limb by limb. -/
def shiftInByte (a : U256) (b : Nat) : U256 :=
  { l0 := (a.l0 * 256) % 2^64 + b
  , l1 := (a.l1 * 256) % 2^64 + a.l0 / 2^56
  , l2 := (a.l2 * 256) % 2^64 + a.l1 / 2^56
  , l3 := (a.l3 * 256) % 2^64 + a.l2 / 2^56 }

/-- The n-byte fold, bytes taken at `pc, pc+1, …` and zero past `codeSize`. -/
def pushAccum (code : Nat → Nat) (codeSize pc : Nat) : Nat → U256 → U256
  | 0,     a => a
  | k + 1, a =>
      let i := pc + (0 : Nat)
      let b := if i < codeSize then code i else 0
      pushAccum code codeSize (pc + 1) k (shiftInByte a b)

/-- The abstract machine. `stateMem off` = the 64-bit EvmState word at byte
    offset `off` (the host struct); a named `Field` reads it via `Field.offset`,
    so `memSize` (#48) and `mp` (#24) can't be confused. -/
structure Mach where
  gas      : Nat
  sp       : Nat
  pcReg    : Nat
  tos      : U256
  nos      : U256
  mem      : Nat → U256
  stateMem : Nat → Nat
  -- Opaque results of the pure-compute C helpers (mul/div/…, addmod/mulmod):
  -- the DSL models the CALL boundary; the value-semantics are the verified C
  -- functions, so they enter the machine as uninterpreted functions.
  helperFn  : String → U256 → U256 → U256
  helperFn3 : String → U256 → U256 → U256 → U256
  -- Host callback boundary (SLOAD/BALANCE/EXTCODE*/…): the cb returns the gas to
  -- charge (in x0) and writes a result to scratch; both are host-provided, so
  -- they enter the model as these fields.
  cbGas    : Nat
  cbResult : U256
  -- Memory model: byte-addressed EVM memory (abstract value semantics), the
  -- aligned size + capacity, and the x17/x0 scratch the memexp gadget uses.
  evmMem   : Nat → U256       -- value at a byte offset (abstract read/write)
  memSize  : Nat              -- aligned memory size (multiple of 32)
  memCap   : Nat              -- host buffer capacity
  acc      : Nat              -- x17 gas accumulator
  scratch  : Nat              -- x0 (newEnd etc.)
  -- The frame's bytecode, for the ops that read it: the PUSH immediate decode
  -- (`pushImm`) is the only one today, and modelling it is what lets the EXTR
  -- shift chain and the zero-fill past `codeSize` be proved rather than
  -- annotated "host".
  code     : Nat → Nat        -- byte at a code offset
  codeSize : Nat
  -- EvmState #136: the frame's valid-JUMPDEST map, built by the host from the code
  -- (EELS `get_valid_jump_destinations`: a 0x5b byte that is not inside a PUSH
  -- immediate). The handlers consult the map, never the code byte — a JUMP into
  -- PUSH data whose byte happens to be 0x5b is invalid (block 5,800,596 tx 117).
  jumpDest : Nat → Bool := fun _ => false
  -- EvmState #552: the tx's EIP-4844 versioned blob hashes (EELS
  -- `tx_env.blob_versioned_hashes`), one u256 per index, installed by the host per
  -- tx; their count is the u64 field #560 (`stateMem 560`). BLOBHASH reads the table
  -- through this, never a constant — the first handler pushed 0 for every index.
  blobHash : Nat → U256 := fun _ => U256.ofScalar 0
  -- EvmState byte #130: the frame is inside a STATICCALL. Modelled so EIP-214
  -- write protection is a theorem (`StaticGuard`) rather than "no static flag".
  isStatic : Bool
  oog      : Bool
  trap     : Bool          -- stack over/underflow / static violation
  ret      : Bool
  halted   : Bool          -- EvmState.halted byte set (STOP/RETURN)

/-! ## Structured memory-expansion instruction layer (#260 follow-up, S1)

The CALL/CREATE/COPY memory-expansion prologue used to be a hand-written
multi-instruction assembly STRING that read the (offset,length) operands with a
single `ldr` (limb0 only), silently wrapping a huge u256 length to a tiny range
(block 4466928 relay `0x39dc3f7a`: argsLen `0x..._0000000000000000` → low limb 0
→ we ran a 0-length CALL & succeeded where mainnet OOGs). This layer replaces
that string with a STRUCTURED instruction list: each `AInstr` is one machine
instruction with a single-purpose `emitARM64` printer (an `emitX86` would be a
second printer over the same IR), and the gas/OOG meaning lives in the pure
`memRangeEnd` semantics — proved against EELS `memoryExpansionCost` in
`Evm.CL.MemExpandSpec`. No opaque per-handler asm blob; the guard is structural. -/

/-- The register set the gas/memexp gadgets touch (TOS x6-9, NOS x10-13, scratch,
    gas x22, depth x23, stack base x24, state ptr x20). -/
inductive Reg where
  | x0 | x4 | x6 | x7 | x8 | x9 | x10 | x11 | x12 | x13
  | x14 | x15 | x16 | x17 | x22 | x23 | x24 | x20
  | x1 | x2 | x3                     -- the C-ABI argument scratch the tails borrow
  | x21 | x26                        -- pc and code base (PUSH's byte fetch)
  | x27                              -- continuation (ARM64 only; x86-64 uses ret)
  | x5                               -- the sixth C-ABI argument (LOG's len)
  -- the frame's callee-saved pairs and the saved stack pointer (stage 4r)
  | x19 | x25 | x28 | x29 | x30
  deriving DecidableEq, Repr

/-- The conditions the handler bodies branch on to an external symbol
    (`_eita_oog`, `_eita_stack_underflow`, …), typed so each target can map
    them: ARM64's `lo` is x86's `b`, `hs` is `ae`, and so on. -/
inductive BCond where
  | lo | hs | hi | ls | eq | ne | lt
  deriving DecidableEq, Repr

/-- The conditions `cset` materialises in the handler bodies. -/
inductive SetCond where
  | eq | lo | lt
  deriving DecidableEq, Repr

def SetCond.s : SetCond → String
  | .eq => "eq" | .lo => "lo" | .lt => "lt"

def BCond.s : BCond → String
  | .lo => "lo" | .hs => "hs" | .hi => "hi" | .ls => "ls" | .eq => "eq" | .ne => "ne" | .lt => "lt"

def Reg.s : Reg → String
  | .x0 => "x0" | .x4 => "x4" | .x6 => "x6" | .x7 => "x7" | .x8 => "x8" | .x9 => "x9"
  | .x10 => "x10" | .x11 => "x11" | .x12 => "x12" | .x13 => "x13"
  | .x14 => "x14" | .x15 => "x15" | .x16 => "x16"
  | .x17 => "x17" | .x22 => "x22" | .x23 => "x23" | .x24 => "x24" | .x20 => "x20"
  | .x1 => "x1" | .x2 => "x2" | .x3 => "x3"
  | .x21 => "x21" | .x26 => "x26" | .x27 => "x27" | .x5 => "x5"
  | .x19 => "x19" | .x25 => "x25" | .x28 => "x28" | .x29 => "x29" | .x30 => "x30"

/-- The 32-bit name (`w16` for `x16`), for the byte-load and `mov w, #0`. -/
def Reg.w (r : Reg) : String := (r.s).replace "x" "w"

/-- Structured ARM64 instruction subset for the memexp prologue (no asm strings:
    the only String is the per-instruction `emitARM64` printer). -/
inductive AInstr where
  | subImm  (dst a : Reg) (imm : Nat)     -- sub  dst, a, #imm
  | addLsl5 (dst a b : Reg)               -- add  dst, a, b, lsl #5
  | ldrOff  (dst base : Reg) (off : Nat)  -- ldr  dst, [base, #off]
  | ldrBase (dst base : Reg)              -- ldr  dst, [base]
  | movImm  (dst : Reg) (imm : Nat)       -- mov  dst, #imm
  | orr3    (dst a b : Reg)               -- orr  dst, a, b
  | adds    (dst a b : Reg)               -- adds dst, a, b
  | cmpReg  (a b : Reg)                    -- cmp  a, b
  | cselHi  (dst a b : Reg)               -- csel dst, a, b, hi
  | cbnzOog (r : Reg)                      -- cbnz r, _eita_oog
  | bcsOog                                 -- b.cs _eita_oog  (carry ⇒ off+len ≥ 2^64)
  | bhiOog                                 -- b.hi _eita_oog  (newEnd > memCap)
  | bloOog                                 -- b.lo _eita_oog  (carry-clear / insufficient gas)
  | subsReg (dst a b : Reg)                -- subs dst, a, b   (flag-setting subtract)
  | ldpOff  (r1 r2 base : Reg) (off : Nat) -- ldp  r1, r2, [base, #off]
  | blsLbl  (lbl : String)                 -- b.ls lbl        (no growth)
  | cbzLbl  (r : Reg) (lbl : String)       -- cbz  r, lbl
  | bLbl    (lbl : String)                 -- b    lbl
  | label   (lbl : String)                 -- lbl:
  -- memexp-gadget arithmetic
  | addImm  (dst a : Reg) (imm : Nat)      -- add  dst, a, #imm
  | subReg  (dst a b : Reg)                -- sub  dst, a, b
  | addReg  (dst a b : Reg)                -- add  dst, a, b
  | mulReg  (dst a b : Reg)                -- mul  dst, a, b
  | clzReg  (dst a : Reg)                  -- clz  dst, a
  | lsrImm  (dst a : Reg) (sh : Nat)       -- lsr  dst, a, #sh
  | lslImm  (dst a : Reg) (sh : Nat)       -- lsl  dst, a, #sh
  | addLsr  (dst a b : Reg) (sh : Nat)     -- add  dst, a, b, lsr #sh
  | addLsl  (dst a b : Reg) (sh : Nat)     -- add  dst, a, b, lsl #sh
  | strOff  (src base : Reg) (off : Nat)   -- str  src, [base, #off]
  -- the handler-body vocabulary (MLOAD/MSTORE and friends), #238 stage 4
  | cmpImm  (a : Reg) (imm : Nat)          -- cmp  a, #imm
  | bSym    (c : BCond) (sym : String)     -- b.<c> sym      (external symbol)
  | addsImm (dst a : Reg) (imm : Nat)      -- adds dst, a, #imm   (sets carry)
  | rev     (dst a : Reg)                  -- rev  dst, a    (byte swap)
  | movReg  (dst a : Reg)                  -- mov  dst, a
  | stpOff  (r1 r2 base : Reg) (off : Nat) -- stp  r1, r2, [base, #off]  ([base] when 0)
  | brCont                                 -- br   x27   (continue; `ret` on x86-64)
  -- the arithmetic family (stage 4j): carry chains, the other bit ops, NOT
  | adcs    (dst a b : Reg)                -- adcs dst, a, b
  | adc     (dst a b : Reg)                -- adc  dst, a, b
  | sbcs    (dst a b : Reg)                -- sbcs dst, a, b
  | sbc     (dst a b : Reg)                -- sbc  dst, a, b
  | and3    (dst a b : Reg)                -- and  dst, a, b
  | eor3    (dst a b : Reg)                -- eor  dst, a, b
  | subsImm (dst a : Reg) (imm : Nat)      -- subs dst, a, #imm
  | mvn     (dst a : Reg)                  -- mvn  dst, a
  -- the comparison family (stage 4k): flag-only chains and cset
  | subsZr  (a b : Reg)                    -- subs xzr, a, b   (compare)
  | sbcsZr  (a b : Reg)                    -- sbcs xzr, a, b   (compare with borrow)
  | cset    (dst : Reg) (c : SetCond)      -- cset dst, c
  -- the byte fetch (stage 4l)
  | ldrbReg (dst base idx : Reg)           -- ldrb wdst, [base, idx]
  | bcLbl   (c : BCond) (lbl : String)     -- b.<c> lbl   (local label)
  | movImmW (dst : Reg) (imm : Nat)        -- mov  wdst, #imm
  -- the C-ABI call sequence (stage 4m): scratch frame, args, call, result
  | spSub   (n : Nat)                      -- sub  sp, sp, #n
  | spAdd   (n : Nat)                      -- add  sp, sp, #n
  | stpFpLr                                -- stp  x29, x30, [sp, #-16]!
  | ldpFpLr                                -- ldp  x29, x30, [sp], #16
  | addSp   (dst : Reg) (n : Nat)          -- add  dst, sp, #n
  | ldrSp   (dst : Reg) (off : Nat)        -- ldr  dst, [sp, #off]
  | blSym   (sym : String)                 -- bl   sym   (C helper)
  | blr     (r : Reg)                      -- blr  r     (host callback through a slot)
  -- control flow, flags and bytes (stage 4o)
  | bSymU   (sym : String)                 -- b    sym   (unconditional, external)
  | ldrbOff (dst base : Reg) (off : Nat)   -- ldrb wdst, [base, #off]
  | strbOff (src base : Reg) (off : Nat)   -- strb wsrc, [base, #off]
  | strbReg (src base idx : Reg)           -- strb wsrc, [base, idx]
  | cbnzSym (r : Reg) (sym : String)       -- cbnz r, sym
  | cmpImmWHex (r : Reg) (imm : Nat)       -- cmp  wr, #0x..   (printed in hex)
  | loadSymAddr (dst : Reg) (sym : String) -- adrp + add :lo12 (the address of a symbol)
  | brReg   (r : Reg)                      -- br   r
  | cselNe  (dst a b : Reg)                -- csel dst, a, b, ne
  | cbnzSymW (r : Reg) (sym : String)      -- cbnz wr, sym   (32-bit test of a zero-extended byte)
  | movzImm (dst : Reg) (imm : Nat)        -- movz dst, #imm (imm < 2^16)
  -- the journal append (stage 4p)
  | madd    (dst a b c : Reg)              -- madd dst, a, b, c   (dst = a*b + c)
  | strZr   (base : Reg) (off : Nat)       -- str  xzr, [base, #off]
  -- the call/create/log frames (stage 4q): sp-relative scratch traffic
  | strWSp  (src : Reg) (off : Nat)        -- str  wsrc, [sp, #off]
  | strWzrSp (off : Nat)                   -- str  wzr, [sp, #off]
  | stpZrSp (off : Nat)                    -- stp  xzr, xzr, [sp, #off]
  | stpSp   (r1 r2 : Reg) (off : Nat)      -- stp  r1, r2, [sp, #off]
  | strSp   (src : Reg) (off : Nat)        -- str  src, [sp, #off]
  | ldrWSp  (dst : Reg) (off : Nat)        -- ldr  wdst, [sp, #off]
  | cbzWLbl (r : Reg) (lbl : String)       -- cbz  wr, lbl
  | andImmHex (dst a : Reg) (imm : Nat)    -- and  dst, a, #0x..
  | csinvEqZr (dst a : Reg)                -- csinv dst, a, xzr, eq   (dst = eq ? a : ~0)
  -- the frame, the dispatcher and the fault stubs (stage 4r)
  | global  (sym : String)                 -- .global sym
  | p2align2                               -- .p2align 2
  | symLabel (sym : String)                -- sym:
  | stpPreSp (r1 r2 : Reg) (n : Nat)       -- stp  r1, r2, [sp, #-n]!
  | ldpPostSp (r1 r2 : Reg) (n : Nat)      -- ldp  r1, r2, [sp], #n
  | ldpSp   (r1 r2 : Reg) (off : Nat)      -- ldp  r1, r2, [sp, #off]
  | movToSp (r : Reg)                      -- mov  sp, r
  | movFromSp (r : Reg)                    -- mov  r, sp
  | ret                                    -- ret
  | ldrLsl3 (dst base idx : Reg)           -- ldr  dst, [base, idx, lsl #3]  (table dispatch)
  | loadSymValue (dst : Reg) (sym : String)    -- adrp dst, sym@PAGE; ldr dst, [dst, sym@PAGEOFF]
  | loadSymGotValue (dst : Reg) (sym : String) -- adrp dst, sym@GOTPAGE; ldr dst, [dst, sym@GOTPAGEOFF]
  -- the JIT chunk algebra (stage 4s)
  | movkImm (dst : Reg) (imm hw : Nat)      -- movk dst, #imm, lsl #(16·hw)
  | addSpReg (r : Reg)                     -- add  r, sp, r
  | spAddReg (r : Reg)                     -- add  sp, sp, r
  | spSubReg (r : Reg)                     -- sub  sp, sp, r
  | adrLbl  (dst : Reg) (lbl : String)     -- adr  dst, lbl (local)
  | brk0                                   -- brk  #0
  | strBase (src base : Reg)               -- str  src, [base]
  | strbBase (src base : Reg)              -- strb wsrc, [base]
  -- cross-image control transfer: `b`/`bl` to a symbol in ANOTHER image. The
  -- text is the plain instruction (the linker stubs it); the in-process byte
  -- path has no linker and materialises the absolute address (20 bytes).
  | bFar    (sym : String)                 -- b    sym   (far)
  | bTramp  (sym : String)                 -- far exit to `sym` through the x86-64 chunk's trampoline
                                           -- (`jmp Lx_<sym>`); on ARM64 the same as `bFar`
  | bcTramp (c : BCond) (sym : String)     -- conditional far exit through the trampoline (`jcc Lx_<sym>`;
                                           -- `b.<c> sym` on ARM64)
  | blFar   (sym : String)                 -- bl   sym   (far)
  -- the gas routines, the program loop, the data tables (stage 4t)
  | csel    (dst a b : Reg) (c : BCond)    -- csel dst, a, b, c
  | cselZrA (dst b : Reg) (c : BCond)      -- csel dst, xzr, b, c
  | cselZrB (dst a : Reg) (c : BCond)      -- csel dst, a, xzr, c
  | eorImm1 (dst a : Reg)                  -- eor  dst, a, #1
  | tstImm  (r : Reg) (imm : Nat)          -- tst  r, #imm    (imm a power of two)
  | cbnzLbl (r : Reg) (lbl : String)       -- cbnz r, lbl
  | cbnzWLbl (r : Reg) (lbl : String)      -- cbnz wr, lbl
  | blank                                  -- an empty line
  | textSection                            -- .section __TEXT,__text,regular,pure_instructions
  | dataSection                            -- .data
  | p2align3                               -- .p2align 3
  | quadSym (sym : String)                 -- .quad   sym
  | quadPair (a b : Nat) (comment : String) -- .quad a, b    // comment
  | commentLine (txt : String)             -- // txt
  deriving Repr, DecidableEq

/-- The per-chunk trampoline label an x86-64 far exit jumps to. -/
def trampLabel : String → String
  | "_eita_oog"             => "Lx_oog"
  | "_eita_stack_underflow" => "Lx_under"
  | "_eita_stack_overflow"  => "Lx_over"
  | "_eita_sync_and_ret"    => "Lx_sync"
  | s                       => "Lx_" ++ s

/-- `mov r, #v` for any 64-bit `v`: `movz` of the low halfword, then a `movk`
    per non-zero higher halfword (the JIT's `movImm`/`movImmI`, once). -/
def movImmInstrs (r : Reg) (v : Nat) : List AInstr :=
  AInstr.movzImm r (v % 65536) ::
  ((List.range 3).filterMap (fun i =>
    let f := (v >>> (16 * (i + 1))) % 65536
    if f > 0 then some (AInstr.movkImm r f (i + 1)) else none))


/-- Hex without a prefix, lowercase, for the `#0x5b` form the bodies print. -/
def hexStr (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def AInstr.emitARM64 : AInstr → String
  | .subImm d a i  => s!"    sub   {d.s}, {a.s}, #{i}\n"
  | .addLsl5 d a b => s!"    add   {d.s}, {a.s}, {b.s}, lsl #5\n"
  | .ldrOff d b o  => s!"    ldr   {d.s}, [{b.s}, #{o}]\n"
  | .ldrBase d b   => s!"    ldr   {d.s}, [{b.s}]\n"
  | .movImm d i    => s!"    mov   {d.s}, #{i}\n"
  | .orr3 d a b    => s!"    orr   {d.s}, {a.s}, {b.s}\n"
  | .adds d a b    => s!"    adds  {d.s}, {a.s}, {b.s}\n"
  | .cmpReg a b    => s!"    cmp   {a.s}, {b.s}\n"
  | .cselHi d a b  => s!"    csel  {d.s}, {a.s}, {b.s}, hi\n"
  | .cbnzOog r     => s!"    cbnz  {r.s}, _eita_oog\n"
  | .bcsOog        => s!"    b.cs  _eita_oog\n"
  | .bhiOog        => s!"    b.hi  _eita_oog\n"
  | .bloOog        => s!"    b.lo  _eita_oog\n"
  | .subsReg d a b => s!"    subs  {d.s}, {a.s}, {b.s}\n"
  | .ldpOff r1 r2 b o =>
      -- `[b]` at offset 0, as the hand-written bodies print it (no gadget emits
      -- a `#0` form, so handlers.S is unchanged)
      if o == 0 then s!"    ldp   {r1.s}, {r2.s}, [{b.s}]\n"
      else s!"    ldp   {r1.s}, {r2.s}, [{b.s}, #{o}]\n"
  | .blsLbl l      => s!"    b.ls  {l}\n"
  | .cbzLbl r l    => s!"    cbz   {r.s}, {l}\n"
  | .bLbl l        => s!"    b     {l}\n"
  | .label l       => s!"{l}:\n"
  | .addImm d a i  => s!"    add   {d.s}, {a.s}, #{i}\n"
  | .subReg d a b  => s!"    sub   {d.s}, {a.s}, {b.s}\n"
  | .addReg d a b  => s!"    add   {d.s}, {a.s}, {b.s}\n"
  | .mulReg d a b  => s!"    mul   {d.s}, {a.s}, {b.s}\n"
  | .clzReg d a    => s!"    clz   {d.s}, {a.s}\n"
  | .lsrImm d a sh => s!"    lsr   {d.s}, {a.s}, #{sh}\n"
  | .lslImm d a sh => s!"    lsl   {d.s}, {a.s}, #{sh}\n"
  | .addLsr d a b sh => s!"    add   {d.s}, {a.s}, {b.s}, lsr #{sh}\n"
  | .addLsl d a b sh => s!"    add   {d.s}, {a.s}, {b.s}, lsl #{sh}\n"
  | .strOff s b o  => s!"    str   {s.s}, [{b.s}, #{o}]\n"
  | .cmpImm a i    => s!"    cmp   {a.s}, #{i}\n"
  | .bSym c sym    => s!"    b.{c.s}  {sym}\n"
  | .addsImm d a i => s!"    adds  {d.s}, {a.s}, #{i}\n"
  | .rev d a       => s!"    rev   {d.s}, {a.s}\n"
  | .movReg d a    => s!"    mov   {d.s}, {a.s}\n"
  | .stpOff r1 r2 b o =>
      if o == 0 then s!"    stp   {r1.s}, {r2.s}, [{b.s}]\n"
      else s!"    stp   {r1.s}, {r2.s}, [{b.s}, #{o}]\n"
  | .brCont        => "    br    x27\n"
  | .adcs d a b    => s!"    adcs  {d.s}, {a.s}, {b.s}\n"
  | .adc d a b     => s!"    adc   {d.s}, {a.s}, {b.s}\n"
  | .sbcs d a b    => s!"    sbcs  {d.s}, {a.s}, {b.s}\n"
  | .sbc d a b     => s!"    sbc   {d.s}, {a.s}, {b.s}\n"
  | .and3 d a b    => s!"    and   {d.s}, {a.s}, {b.s}\n"
  | .eor3 d a b    => s!"    eor   {d.s}, {a.s}, {b.s}\n"
  | .subsImm d a i => s!"    subs  {d.s}, {a.s}, #{i}\n"
  | .mvn d a       => s!"    mvn   {d.s}, {a.s}\n"
  | .subsZr a b    => s!"    subs  xzr, {a.s}, {b.s}\n"
  | .sbcsZr a b    => s!"    sbcs  xzr, {a.s}, {b.s}\n"
  | .cset d c      => s!"    cset  {d.s}, {c.s}\n"
  | .ldrbReg d b i => s!"    ldrb  {d.w}, [{b.s}, {i.s}]\n"
  | .bcLbl c l     => s!"    b.{c.s}  {l}\n"
  | .movImmW d i   => s!"    mov   {d.w}, #{i}\n"
  | .spSub n       => s!"    sub   sp, sp, #{n}\n"
  | .spAdd n       => s!"    add   sp, sp, #{n}\n"
  | .stpFpLr       => "    stp   x29, x30, [sp, #-16]!\n"
  | .ldpFpLr       => "    ldp   x29, x30, [sp], #16\n"
  | .addSp d n     => s!"    add   {d.s}, sp, #{n}\n"
  | .ldrSp d o     => s!"    ldr   {d.s}, [sp, #{o}]\n"
  | .blSym sym     => s!"    bl    {sym}\n"
  | .blr r         => s!"    blr   {r.s}\n"
  | .bSymU sym     => s!"    b     {sym}\n"
  | .ldrbOff d b o => s!"    ldrb  {d.w}, [{b.s}, #{o}]\n"
  | .strbOff s b o => s!"    strb  {s.w}, [{b.s}, #{o}]\n"
  | .strbReg s b i => s!"    strb  {s.w}, [{b.s}, {i.s}]\n"
  | .cbnzSym r sym => s!"    cbnz  {r.s}, {sym}\n"
  | .cmpImmWHex r i => s!"    cmp   {r.w}, #0x{hexStr i}\n"
  | .loadSymAddr d sym => s!"    adrp  {d.s}, {sym}@PAGE\n    add   {d.s}, {d.s}, {sym}@PAGEOFF\n"
  | .brReg r       => s!"    br    {r.s}\n"
  | .cselNe d a b  => s!"    csel  {d.s}, {a.s}, {b.s}, ne\n"
  | .cbnzSymW r sym => s!"    cbnz  {r.w}, {sym}\n"
  | .movzImm d i   => s!"    movz  {d.s}, #{i}\n"
  | .madd d a b c  => s!"    madd  {d.s}, {a.s}, {b.s}, {c.s}\n"
  | .strZr b o     => s!"    str   xzr, [{b.s}, #{o}]\n"
  | .strWSp s o    => s!"    str   {s.w}, [sp, #{o}]\n"
  | .strWzrSp o    => s!"    str   wzr, [sp, #{o}]\n"
  | .stpZrSp o     => s!"    stp   xzr, xzr, [sp, #{o}]\n"
  | .stpSp r1 r2 o => s!"    stp   {r1.s}, {r2.s}, [sp, #{o}]\n"
  | .strSp s o     => s!"    str   {s.s}, [sp, #{o}]\n"
  | .ldrWSp d o    => s!"    ldr   {d.w}, [sp, #{o}]\n"
  | .cbzWLbl r l   => s!"    cbz   {r.w}, {l}\n"
  | .andImmHex d a i => s!"    and   {d.s}, {a.s}, #0x{hexStr i}\n"
  | .csinvEqZr d a => s!"    csinv {d.s}, {a.s}, xzr, eq\n"
  | .global s      => s!".global {s}\n"
  | .p2align2      => ".p2align 2\n"
  | .symLabel s    => s!"{s}:\n"
  | .stpPreSp r1 r2 n => s!"    stp   {r1.s}, {r2.s}, [sp, #-{n}]!\n"
  | .ldpPostSp r1 r2 n => s!"    ldp   {r1.s}, {r2.s}, [sp], #{n}\n"
  | .ldpSp r1 r2 o => s!"    ldp   {r1.s}, {r2.s}, [sp, #{o}]\n"
  | .movToSp r     => s!"    mov   sp, {r.s}\n"
  | .movFromSp r   => s!"    mov   {r.s}, sp\n"
  | .ret           => "    ret\n"
  | .ldrLsl3 d b i => s!"    ldr   {d.s}, [{b.s}, {i.s}, lsl #3]\n"
  | .loadSymValue d s => s!"    adrp  {d.s}, {s}@PAGE\n    ldr   {d.s}, [{d.s}, {s}@PAGEOFF]\n"
  | .loadSymGotValue d s => s!"    adrp  {d.s}, {s}@GOTPAGE\n    ldr   {d.s}, [{d.s}, {s}@GOTPAGEOFF]\n"
  | .movkImm d i hw => s!"    movk  {d.s}, #{i}, lsl #{16 * hw}\n"
  | .addSpReg r    => s!"    add   {r.s}, sp, {r.s}\n"
  | .spAddReg r    => s!"    add   sp, sp, {r.s}\n"
  | .spSubReg r    => s!"    sub   sp, sp, {r.s}\n"
  | .adrLbl d l    => s!"    adr   {d.s}, {l}\n"
  | .brk0          => "    brk   #0\n"
  | .strBase s b   => s!"    str   {s.s}, [{b.s}]\n"
  | .strbBase s b  => s!"    strb  {s.w}, [{b.s}]\n"
  | .bFar sym      => s!"    b     {sym}\n"
  | .bTramp sym    => s!"    b     {sym}\n"
  | .bcTramp c sym => s!"    b.{c.s}  {sym}\n"
  | .blFar sym     => s!"    bl    {sym}\n"
  | .csel d a b c  => s!"    csel  {d.s}, {a.s}, {b.s}, {c.s}\n"
  | .cselZrA d b c => s!"    csel  {d.s}, xzr, {b.s}, {c.s}\n"
  | .cselZrB d a c => s!"    csel  {d.s}, {a.s}, xzr, {c.s}\n"
  | .eorImm1 d a   => s!"    eor   {d.s}, {a.s}, #1\n"
  | .tstImm r i    => s!"    tst   {r.s}, #{i}\n"
  | .cbnzLbl r l   => s!"    cbnz  {r.s}, {l}\n"
  | .cbnzWLbl r l  => s!"    cbnz  {r.w}, {l}\n"
  | .blank         => "\n"
  | .textSection   => ".section __TEXT,__text,regular,pure_instructions\n"
  | .dataSection   => ".data\n"
  | .p2align3      => ".p2align 3\n"
  | .quadSym s     => s!"    .quad   {s}\n"
  | .quadPair a b c => s!"    .quad {a}, {b}    // {c}\n"
  | .commentLine t => s!"    // {t}\n"

/-- One (offset,length) range → its memory-expansion END, computed over the FULL
    u256. `none` = OOG (length ≥ 2^64, or offset ≥ 2^64, or off+len overflows
    u64 — all mean the true end ≥ 2^64, which EELS charges as unaffordable).
    `some 0` = zero length, no expansion. This is the value semantics of
    `memRangeInstrs`; the refinement vs EELS is `MemExpandSpec.memRangeEnd_*`. -/
def memRangeEnd (off len : U256) : Option Nat :=
  if len.l1 ≠ 0 ∨ len.l2 ≠ 0 ∨ len.l3 ≠ 0 then none
  else if len.l0 = 0 then some 0
  else if off.l1 ≠ 0 ∨ off.l2 ≠ 0 ∨ off.l3 ≠ 0 ∨ 2^64 ≤ off.l0 + len.l0 then none
  else some (off.l0 + len.l0)

/-- Structured emit for one range: load len (slot `lenP`) and off (slot `offP`)
    as full u256, OOG on any high limb (or carry), leave the end in `dst`. Mirrors
    `memRangeEnd`. `lblZero`/`lblDone` thread the len=0 fast path. -/
def memRangeInstrs (lenP offP : Nat) (dst : Reg) (lblZero lblDone : String) : List AInstr :=
  [ .subImm .x14 .x23 lenP, .addLsl5 .x14 .x24 .x14,
    .ldrOff .x16 .x14 0,                                   -- len.l0
    .ldrOff .x15 .x14 8, .ldrOff .x17 .x14 16, .orr3 .x15 .x15 .x17,
    .ldrOff .x17 .x14 24, .orr3 .x15 .x15 .x17, .cbnzOog .x15,   -- len high ≥ 2^64 ⇒ OOG
    .subImm .x14 .x23 offP, .addLsl5 .x14 .x24 .x14,
    .cbzLbl .x16 lblZero,                                  -- len.l0 = 0 ⇒ end 0
    .ldrOff .x15 .x14 8, .ldrOff .x17 .x14 16, .orr3 .x15 .x15 .x17,
    .ldrOff .x17 .x14 24, .orr3 .x15 .x15 .x17, .cbnzOog .x15,   -- off high ⇒ OOG
    .ldrOff .x17 .x14 0, .adds dst .x17 .x16, .bcsOog,          -- off.l0+len.l0 ≥ 2^64 ⇒ OOG
    .bLbl lblDone, .label lblZero, .movImm dst 0, .label lblDone ]

/-- The memory-expansion gas gadget as STRUCTURED instructions (newEnd in x0,
    accumulate `memoryExpansionCost` into x17, update memory_size at [x20,#48];
    OOG if newEnd > memCap[x20,#56]). Shared by MLOAD/MSTORE/MSTORE8 (the
    `memExpand` op), RETURN/REVERT, and the CALL/CREATE memexp. The quadratic is
    `cost(w) = 3w + w²/512`; the delta charged is `cost(nw) − cost(ow)` =
    `Gas.memoryExpansionCost ow nw` — proved in MemExpandSpec. (#238 S2) -/
def memExpandInstrs : List AInstr :=
  [ .ldrOff .x14 .x20 56, .cmpReg .x0 .x14, .bhiOog,
    .addImm .x14 .x0 31, .lsrImm .x14 .x14 5, .ldrOff .x15 .x20 48, .lsrImm .x15 .x15 5,
    .cmpReg .x14 .x15, .blsLbl "7f",
    .mulReg .x16 .x14 .x14, .addLsr .x16 .x14 .x16 9, .addLsl .x16 .x16 .x14 1,
    .mulReg .x14 .x15 .x15, .addLsr .x14 .x15 .x14 9, .addLsl .x14 .x14 .x15 1,
    .subReg .x16 .x16 .x14, .addReg .x17 .x17 .x16,
    .addImm .x14 .x0 31, .lsrImm .x14 .x14 5, .lslImm .x14 .x14 5, .strOff .x14 .x20 48,
    .label "7" ]

/-- Byte-identical to the former hand-written `memExpandStr` (so handlers.S is
    unchanged); now generated from the structured `memExpandInstrs`. -/
def memExpandStr : String := String.join (memExpandInstrs.map AInstr.emitARM64)

/-- The full CALL/CREATE memexp prologue as structured asm: in-range end → x0,
    out-range end → x14, max into x0, then the quadratic memexp gadget
    (`memExpandStr`, the one remaining shared primitive — S2 will structify it). -/
def callMemExpandEmit (inOffP inLenP outOffP outLenP : Nat) (name : String) : String :=
  String.join ((memRangeInstrs inLenP inOffP .x0 s!".Lcfin0_{name}" s!".Lcfin1_{name}").map AInstr.emitARM64) ++
  String.join ((memRangeInstrs outLenP outOffP .x14 s!".Lcfout0_{name}" s!".Lcfout1_{name}").map AInstr.emitARM64) ++
  String.join ([AInstr.cmpReg .x0 .x14, AInstr.cselHi .x0 .x0 .x14, AInstr.movImm .x17 0,
                AInstr.cbzLbl .x0 "4f"].map AInstr.emitARM64) ++
  memExpandStr ++
  "    subs  x22, x22, x17\n    b.lo  _eita_oog\n4:\n"

/-- Single-region memexp for CREATE/CREATE2 (#266): charge memory expansion over
    the init-code range [offset, offset+length). EELS create/create2 charge
    `calculate_gas_extend_memory` over the init range ON TOP of GAS_CREATE — the
    native createCore omitted it entirely, undercharging every CREATE whose init
    code grows memory (offset+len past memory_size). `offP`/`lenP` are the
    stack-depth positions of offset and length. -/
def createMemExpandEmit (offP lenP : Nat) (name : String) : String :=
  String.join ((memRangeInstrs lenP offP .x0 s!".Lcrin0_{name}" s!".Lcrin1_{name}").map AInstr.emitARM64) ++
  String.join ([AInstr.movImm .x17 0, AInstr.cbzLbl .x0 "4f"].map AInstr.emitARM64) ++
  memExpandStr ++
  "    subs  x22, x22, x17\n    b.lo  _eita_oog\n4:\n    str   x22, [x20, #8]\n"

/-- KECCAK256 gas: high-limb OOG on len (x10-13) and off (x6-9), 30 + 6·⌈len/32⌉ +
    memexp, charge. Structured (#238 S2); byte-identical to the former string. -/
def keccakGasInstrs (cost : Nat) : List AInstr :=
  [ .orr3 .x14 .x11 .x12, .orr3 .x14 .x14 .x13, .cbnzOog .x14,
    .addImm .x17 .x10 31, .cmpReg .x17 .x10, .bloOog,
    .lsrImm .x17 .x17 5, .addLsl .x17 .x17 .x17 1, .addReg .x17 .x17 .x17,
    .addImm .x17 .x17 cost,
    .cbzLbl .x10 "4f", .orr3 .x14 .x7 .x8, .orr3 .x14 .x14 .x9, .cbnzOog .x14,
    .adds .x0 .x6 .x10, .bcsOog ] ++ memExpandInstrs ++
  [ .label "4", .subsReg .x22 .x22 .x17, .bloOog ]

/-- COPY-family gas (CALLDATACOPY/CODECOPY/RETURNDATACOPY): high-limb OOG on the
    len (slot sp-3) and off (x6-9), base + 3·⌈len/32⌉ + memexp, charge. -/
def copyGasInstrs (cost : Nat) : List AInstr :=
  [ .subImm .x14 .x23 3, .addLsl5 .x15 .x24 .x14, .ldrBase .x14 .x15,
    .ldpOff .x16 .x0 .x15 8, .orr3 .x16 .x16 .x0, .ldrOff .x0 .x15 24,
    .orr3 .x16 .x16 .x0, .cbnzOog .x16,
    .movImm .x17 cost,
    .addImm .x16 .x14 31, .cmpReg .x16 .x14, .bloOog, .lsrImm .x16 .x16 5,
    .addLsl .x16 .x16 .x16 1, .addReg .x17 .x17 .x16,
    .cbzLbl .x14 "6f", .orr3 .x16 .x7 .x8, .orr3 .x16 .x16 .x9, .cbnzOog .x16,
    .adds .x0 .x6 .x14, .bcsOog ] ++ memExpandInstrs ++
  [ .label "6", .subsReg .x22 .x22 .x17, .bloOog ]

/-- MCOPY gas (#270): unlike CALLDATACOPY/CODECOPY/RETURNDATACOPY, MCOPY's source
    is MEMORY, so memory must expand to cover BOTH ranges — EELS charges
    `memexp(max(dst+len, src+len))`, not `memexp(dst+len)`. Reuses the proven
    `memRangeInstrs` (off+len with OOG + len=0→0) for each range and the same
    `cmp;cselHi` max + `memExpandInstrs` the CALL prologue uses. base + 3·⌈len/32⌉
    is added on top. Stack: TOS=dst (sp-1), NOS=src (sp-2), NNOS=len (sp-3). -/
def mcopyGasInstrs (cost : Nat) : List AInstr :=
  -- dst+len → x0, src+len → x14, then x0 := max (both 0 when len=0).
  memRangeInstrs 3 1 .x0  ".Lmcd0" ".Lmcd1"
  ++ memRangeInstrs 3 2 .x14 ".Lmcs0" ".Lmcs1"
  ++ [ .cmpReg .x0 .x14, .cselHi .x0 .x0 .x14,
       -- word-copy cost: x17 = cost + 3·⌈len/32⌉ (len.l0 at sp-3; high limbs
       -- already OOG-checked by memRangeInstrs above).
       .subImm .x14 .x23 3, .addLsl5 .x15 .x24 .x14, .ldrBase .x14 .x15,
       .movImm .x17 cost,
       .addImm .x16 .x14 31, .cmpReg .x16 .x14, .bloOog, .lsrImm .x16 .x16 5,
       .addLsl .x16 .x16 .x16 1, .addReg .x17 .x17 .x16,
       .cbzLbl .x0 "6f" ]                          -- len=0 ⇒ no memexp
  ++ memExpandInstrs                                -- adds memexp(max end) into x17
  ++ [ .label "6", .subsReg .x22 .x22 .x17, .bloOog ]

/-- RETURNDATACOPY bound (EIP-211; EELS byzantium+ returndatacopy): src + size must
    not pass the return buffer — exceptional halt otherwise, even for size 0. Over
    the full u256: src (NOS, x10-13) or size (stack[sp-3]) high limbs ⇒ halt,
    src+size carry ⇒ halt, src+size > returndata_size ([x20,#104]) ⇒ halt. -/
def returndataBoundsInstrs : List AInstr :=
  [ .orr3 .x14 .x11 .x12, .orr3 .x14 .x14 .x13, .cbnzOog .x14,
    .subImm .x14 .x23 3, .addLsl5 .x14 .x24 .x14,
    .ldrOff .x15 .x14 8, .ldrOff .x16 .x14 16, .orr3 .x15 .x15 .x16,
    .ldrOff .x16 .x14 24, .orr3 .x15 .x15 .x16, .cbnzOog .x15,
    .ldrOff .x15 .x14 0, .adds .x15 .x10 .x15, .bcsOog,
    .ldrOff .x16 .x20 104, .cmpReg .x15 .x16, .bhiOog ]

/-- The JUMPDEST test of `jumpValidate` / `jumpiCheck`, after the width and bounds
    checks have passed with the destination in x6: byte `dest` of the frame's
    valid-JUMPDEST map (EvmState #136, `Mach.jumpDest`) must be 1. The map, not the
    code byte, is the spec's `valid_jump_destinations`: a 0x5b inside a PUSH immediate
    is data, and reading `code[dest]` accepted it (mainnet 5,800,596 tx 117 — a
    creation whose init code jumps to offset 1 of `PUSH9 0x5b…`; geth halts, the
    byte test ran on). -/
def jumpDestInstrs : List AInstr :=
  [ .ldrOff .x14 .x20 136, .ldrbReg .x14 .x14 .x6, .cmpImmWHex .x14 0x1,
    .bSym .ne "_eita_invalid_jump" ]

/-- EIP-4844 BLOBHASH lookup (EELS cancun/vm/instructions/environment.py `blob_hash`:
    `if index < len(tx_env.blob_versioned_hashes): push hashes[index] else push 0`). The
    index is the u256 in x6-x9 and the range test covers ALL FOUR limbs: a nonzero high
    limb is out of range, never truncated to its low limb (the #260 / JUMP width class).
    The count is EvmState #560 and the table EvmState #552 — one hash per 32 bytes, four
    little-endian limbs, written by the host per tx — so the hit is two `ldp`s at
    `table + 32·index`. Both exits leave the hash (or 0) in x6-x9; the index is gone. -/
def blobHashInstrs : List AInstr :=
  [ .orr3 .x14 .x7 .x8, .orr3 .x14 .x14 .x9, .cbnzLbl .x14 ".Lbh_zero",
    .ldrOff .x14 .x20 560, .cmpReg .x6 .x14, .bcLbl .hs ".Lbh_zero",
    .ldrOff .x15 .x20 552, .addLsl5 .x14 .x15 .x6,
    .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16, .bLbl ".Lbh_done",
    .label ".Lbh_zero", .movImm .x6 0, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0,
    .label ".Lbh_done" ]

/-- EIP-214 for CALL: in a static frame a nonzero value is a static violation (EELS
    byzantium+ `call`: is_static ∧ value ≠ 0 ⇒ WriteInStaticContext). value =
    stack[sp-3], over all four limbs. CALLCODE moves no value to another account and
    has no such check. -/
def staticValueGuardInstrs : List AInstr :=
  [ .ldrbOff .x14 .x20 130, .cbzWLbl .x14 "93f",
    .subImm .x14 .x23 3, .addLsl5 .x14 .x24 .x14,
    .ldrOff .x15 .x14 0, .ldrOff .x16 .x14 8, .orr3 .x15 .x15 .x16,
    .ldrOff .x16 .x14 16, .orr3 .x15 .x15 .x16, .ldrOff .x16 .x14 24, .orr3 .x15 .x15 .x16,
    .cbnzSym .x15 "_eita_static_violation", .label "93" ]

/-- EXTCODECOPY memexp gas: memexp(dst+len) over the full u256 (len or dst high limbs
    ⇒ OOG, via memRangeInstrs; was low limbs only), charge. -/
def extcodecopyGasInstrs : List AInstr :=
  memRangeInstrs 4 2 .x0 ".Lxcd0" ".Lxcd1" ++
  [ .movImm .x17 0, .cbzLbl .x0 "90f" ] ++ memExpandInstrs ++
  [ .subsReg .x22 .x22 .x17, .bloOog, .label "90" ]

/-- EXP gas: ebytes = ⌈log256(exponent)⌉ from the exponent limbs' MSB via clz
    (x10-13 = exponent), gas = cost + byteCost·ebytes, charge. Structured (#238 S2). -/
def expGasInstrs (cost byteCost : Nat) : List AInstr :=
  [ .movImm .x14 0, .cbzLbl .x13 ".Lexp_l2", .clzReg .x15 .x13,
    .movImm .x14 256, .subReg .x14 .x14 .x15, .bLbl ".Lexp_charge",
    .label ".Lexp_l2", .cbzLbl .x12 ".Lexp_l1", .clzReg .x15 .x12,
    .movImm .x14 192, .subReg .x14 .x14 .x15, .bLbl ".Lexp_charge",
    .label ".Lexp_l1", .cbzLbl .x11 ".Lexp_l0", .clzReg .x15 .x11,
    .movImm .x14 128, .subReg .x14 .x14 .x15, .bLbl ".Lexp_charge",
    .label ".Lexp_l0", .cbzLbl .x10 ".Lexp_zero_e", .clzReg .x15 .x10,
    .movImm .x14 64, .subReg .x14 .x14 .x15,
    .label ".Lexp_charge", .addImm .x14 .x14 7, .lsrImm .x14 .x14 3, .bLbl ".Lexp_do_gas",
    .label ".Lexp_zero_e", .movImm .x14 0,
    .label ".Lexp_do_gas", .movImm .x15 byteCost, .mulReg .x14 .x14 .x15,
    .addImm .x14 .x14 cost, .subsReg .x22 .x22 .x14, .bloOog ]

/-- CLZ (EIP-7939) of the 256-bit TOS into x6 (l3 = most significant limb in x9):
    clz(l3) if l3 ≠ 0, else 64 + clz(l2) if l2 ≠ 0, else 128 + clz(l1), else 192 + clz(l0)
    (clz(0) = 64 on AArch64, so the all-zero word yields 256); x7-x9 zeroed. Branch-free,
    on the SCRATCH registers x0/x14/x15/x17 — on both backends. It used to compute in
    x10-x13 ("free in a unary op"), but on ARM64 those are the register-cached NOS, which
    a unary op must keep: the next AND read the clobbered x10 (mainnet 26,042,126 tx 135,
    `clz(x) & ~1` in a sqrt gave 0x40 for 0xe0; x86-64 keeps NOS in memory and was right).
    `ARM64.Interp.handler_stack_cache_coherent` now checks every body for it. -/
def clzReduceInstrs : List AInstr :=
  [ .clzReg .x0 .x9, .clzReg .x14 .x8, .clzReg .x15 .x7, .clzReg .x17 .x6,
    .addImm .x14 .x14 64, .addImm .x15 .x15 128, .addImm .x17 .x17 192,
    .cmpImm .x7 0, .cselNe .x15 .x15 .x17, .cmpImm .x8 0, .cselNe .x14 .x14 .x15,
    .cmpImm .x9 0, .cselNe .x6 .x0 .x14, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0 ]

/-- The register of TOS limb `k` (x6 = limb 0, least significant … x9 = limb 3). -/
def tosLimb : Nat → Reg
  | 0 => .x6 | 1 => .x7 | 2 => .x8 | _ => .x9

/-- PUSH-N's immediate as wide loads: the n bytes at `code + pc` are
    `r = n % 8` leading bytes (the partial top limb) then `q = n / 8` whole
    limbs. Each whole limb is one 8-byte load and a byte reverse (`ldr`+`rev`;
    x86-64 `mov`+`bswap`); the partial limb is the 8 bytes at `pc` reversed and
    shifted right by `64 − 8r`, which keeps exactly its r leading bytes. No
    per-byte branch: a byte past `codeSize` is read from the code image's zero
    padding (≥ 32 bytes after the code — `PushWide`'s contract), so it reads 0
    exactly as EELS's `buffer_read` zero-fills it. The limbs not written stay as
    `loadZeroTos` left them. `PushWide.pushWide_correct` proves this is the
    `pushAccum` fold for every n in 1..32. -/
def pushWideInstrs (n : Nat) : List AInstr :=
  let q := n / 8
  let r := n % 8
  [.addReg .x15 .x26 .x21] ++
  (if r = 0 then [] else
     [.ldrBase (tosLimb q) .x15, .rev (tosLimb q) (tosLimb q),
      .lsrImm (tosLimb q) (tosLimb q) (64 - 8 * r)] ++
     (if q = 0 then [] else [.addImm .x15 .x15 r])) ++
  ((List.range q).flatMap fun j =>
     [.ldrOff (tosLimb (q - 1 - j)) .x15 (8 * j), .rev (tosLimb (q - 1 - j)) (tosLimb (q - 1 - j))]) ++
  [.addImm .x21 .x21 n]

/-- One handler op (a combinator that emits a fixed asm block and denotes a
    value-level effect). Each maps 1:1 to a block in `ARM64.lean`. -/
inductive Op where
  | ovfGuard                       -- cmp x23,#1024 ; b.hs _eita_stack_overflow
  | underflow (n : Nat)            -- cmp x23,#n   ; b.lo _eita_stack_underflow
  | tosToNos                       -- mov x10-13, x6-9      (push: old top → 2nd)
  | nosToTos                       -- mov x6-9, x10-13      (pop: 2nd → top)
  | loadFieldTos (f : Field)       -- ldr x6,[x20,#off f] ; zero x7-9  (new top)
  | loadU64Off (off : Nat)         -- ldr x6,[x20,#off] ; zero x7-9   (u64 env field)
  | loadU256Off (off : Nat)        -- ldp x6,x7/x8,x9 [x20,#off]      (u256 env field)
  | loadZeroTos                    -- mov x6-9, #0                    (zero push)
  | pcMinus1Tos                    -- sub x6,x21,#1 ; zero x7-9         (PC value)
  | chargeGasPushTos (cost : Nat)  -- subs;b.lo ; mov x6,x22 ; zero x7-9 (GAS)
  | bitwise (op : BitOp)           -- {op} x10-13,x10-13,x6-9 ; mov x6-9,x10-13
  | arith (k : ArithKind)          -- adds/adcs/adc (or subs/sbcs/sbc) ; mov
  | cmpChain (swapped : Bool) (cond : CmpCond)  -- subs-chain + cset cond ; zero
  | eqReduce                       -- EQ: eor/orr fold + cset eq ; zero x7-9
  | iszeroReduce                   -- ISZERO: orr fold + cset eq ; zero x7-9
  | clzReduce                      -- CLZ (EIP-7939): per-limb clz + csel chain ; zero x7-9
  | notLimbs                       -- NOT: mvn x6-9
  | spInc                          -- add x23,x23,#1
  | spDec                          -- sub x23,x23,#1
  | spDec2                         -- sub x23,x23,#2  (ternary pops 3 pushes 1)
  | binHelper (helper : String)    -- frame; bl helper(res,&top,&nos); load res
  | ternaryHelper (helper : String)-- frame; bl helper(res,&top,&nos,&third); load
  -- host-callback marshaling (SLOAD/BALANCE/EXTCODE*/BLOCKHASH/TLOAD)
  | cbEnter (scratch : Nat)        -- sub sp,#scratch ; stp x29,x30,[sp,#-16]!
  | cbExit (scratch : Nat)         -- ldp x29,x30,[sp],#16 ; add sp,#scratch
  | loadCtx (reg : Nat)            -- ldr x{reg},[x20,#504]                (arena)
  | loadCtxVia14 (reg : Nat)       -- ldr x14,[x20,#504] ; mov x{reg},x14
  | loadTxStateCtx (reg : Nat)     -- ldr x14,[x20,#504] ; ldr x{reg},[x14,#64]
  | argStateField (reg off : Nat)  -- add x{reg},x20,#off
  | argStackPtr (reg n : Nat)      -- sub x14,x23,#n ; add x{reg},x24,x14,lsl#5
  | argScratch (reg : Nat)         -- add x{reg},sp,#16
  | argStateBase (reg : Nat)       -- mov x{reg},x20   (pass &EvmState)
  | cbSlot (slot : Nat)            -- ldr x14,[x20,#496] ; ldr x14,[x14,#slot] ; blr
  | cbDirect (name : String)       -- bl name
  | chargeGasX0                    -- subs x22,x22,x0 ; b.lo oog   (cb-returned gas)
  | chargeGasX0Via14               -- mov x14,x0 ; subs x22,x22,x14 ; b.lo oog
  | chargeFixed (n : Nat)          -- mov x14,#n ; subs x22,x22,x14 ; b.lo oog
  | loadScratchTos                 -- add x14,sp,#16 ; ldp x6,x7/x8,x9   (u256 result)
  | loadScratchU64Tos              -- ldr x6,[sp,#16] ; zero x7-9         (u64 result)
  -- memory ops (MLOAD/MSTORE/MSTORE8)
  | boundCheckHiTos                -- orr x14,x7,x8 ; orr x14,x14,x9 ; cbnz oog
  | newEndTos (add : Nat)          -- adds x0,x6,#add ; b.cs oog   (newEnd=off+add)
  | setAcc (base : Nat)            -- mov x17,#base
  | memExpand                      -- memExpandInto x0 x17 (quadratic memexp gas)
  | chargeAcc                      -- subs x22,x22,x17 ; b.lo oog
  | mloadTail                      -- mp update + BE load memory[off] → x6-9
  | mstoreTail                     -- mp update + BE store x10-13 → memory[off]; pop2
  | mstore8Tail                    -- mp update + strb w10 → memory[off]; pop2
  -- RETURN / REVERT
  | memExpandIfLen (tag : String)   -- acc:=0; if len(x10)>0 memexp(off+len)+charge (label 4:)
  | setOutput                      -- output_size/ptr := len/&memory[off]; mp update
  | setReverted                    -- strb w14,[x20,#129]  (after setHalted sets w14=1)
  -- COPY family (CALLDATACOPY/CODECOPY/RETURNDATACOPY/MCOPY)
  | copyGasCharge (cost : Nat)     -- len/dst bound checks + base+3·words + memexp + charge (6:)
  | mcopyGasCharge (cost : Nat)    -- #270: base+3·words + memexp(max(dst,src)+len) + charge (6:)
  | returndataBounds               -- EIP-211: src+len ≤ returndata_size over u256, else halt
  | staticValueGuard               -- EIP-214: CALL with value ≠ 0 in a static frame ⇒ violation
  | copyCbPop3 (helper : String)   -- bl helper(state,&dst,&src,&len) ; pop 3 + reload (7:,8:)
  -- KECCAK256
  | keccakGasCharge (cost : Nat)   -- len/off bound checks + 30+6·words + memexp + charge (4:)
  | keccakCbPop1                   -- bl _eita_helper_keccak256(state,&off,&len,&res) ; pop 1
  -- EXTCODECOPY (4-pop host cb)
  | extcodecopyGasMem              -- len/dst loads + memexp(dst+len) + charge (90:)
  | extcodecopyCb                  -- cb->ext_code_copy(ctx,&addr,&mem[dst],src,len); pop 4 + reload (91:,92:)
  -- JUMP / JUMPI (control flow)
  | jumpValidate                   -- width + bounds + JUMPDEST-map check on dest(x6); mov x21,x6 (else _eita_invalid_jump)
  | jumpiCheck                     -- cond zero→fallthrough; else validate+setpc; _eita_jumpi_pop:
  | jumpiTailGas (cost : Nat)      -- charge cost; br x27; _eita_jumpi_fallthrough: b _eita_jumpi_pop
  -- BLOBHASH (EIP-4844)
  | blobhashLookup                 -- x6-9 := index < count(#560) (all limbs) ? table(#552)[index] : 0
  -- static-context guard + TSTORE
  | staticGuard                    -- ldrb [#130]; cbnz _eita_static_violation
  | tstoreCb                       -- sync TOS/NOS; eita_ts_tstore(ts,arena,&addr,&slot,&val); pop 2 + reload
  -- LOG-N
  | logEmit (n cost : Nat)         -- gas=cost+8·len+memexp; bump log_count; mp; pop 2+n; charge; cb->log if set (M1b); reload; br x27
  -- PUSH-N immediate (n > 0)
  | pushImm (n : Nat)              -- read n code bytes (zero past code_size) into x6-9 by wide loads; pc += n
  -- SSTORE
  | sstoreSentry (sentry : Nat)    -- gas-sentry: if gas ≤ sentry → OOG (movImm + cmp + b.ls)
  | sstoreCb                       -- cb->sstore(ctx,&addr,&slot,&val) gas; journal entry; pop 2 + reload
  -- SELFDESTRUCT
  | selfdestructCb                 -- sync TOS; cb->selfdestruct(ctx,&addr,&benef); charge cb gas
  -- CALL family (CALL/CALLCODE/DELEGATECALL/STATICCALL)
  | callFamilyCore (name : String) (kind staticp : Nat) (withValue : Bool)
    -- memexp(max in/out range); build CallParams; cb->call; returndata→mem; pop args; push success; charge gas_used
  -- CREATE / CREATE2
  | createCore                     -- build CallParams kind=4; cb->create; push addr/0; pop 3 push 1; charge gas_used
  | create2Core                    -- like CREATE + salt (kind=5); pop 4 push 1
  -- EXP variable gas
  | expGasCharge (cost byteCost : Nat)  -- ebytes from e (clz per limb); charge cost + byteCost·ebytes (.Lexp_*)
  | storeTos                       -- write x6-9 to stack[sp-1]
  | reloadNos                      -- load x10-13 from stack[sp-2]
  | brCont                         -- br x27
  | exitGas (cost : Nat)           -- subs;b.lo ; br x27
  | pcDec                          -- sub x21,x21,#1     (STOP: undo trampoline)
  | setHalted                      -- mov w14,#1 ; strb w14,[x20,#128]
  | jumpSyncRet                    -- adrp/add x27,_eita_sync_and_ret ; br x27
  | branchOOG                      -- b _eita_oog        (INVALID / undefined)
  | dupLoad (n : Nat)              -- load stack[sp-n] into x6-9 (DUP-n)
  | swapPartner (n : Nat)          -- swap x6-9 with stack[sp-1-n] (SWAP-n)
  deriving Repr, DecidableEq


/-- Materialize a Nat into a register via movz + movk (16-bit fields).
    Matches `ARM64.movImm` byte-for-byte. -/
def movImmStr (reg : String) (v : Nat) : String := Id.run do
  let mut s := s!"    movz  {reg}, #{v % 65536}\n"
  for i in [1:4] do
    let field := (v >>> (16 * i)) % 65536
    if field > 0 then
      s := s ++ s!"    movk  {reg}, #{field}, lsl #{16 * i}\n"
  return s

def Op.emit : Op → String
  | .ovfGuard =>
      "    cmp   x23, #1024\n    b.hs  _eita_stack_overflow\n"
  | .underflow n =>
      s!"    cmp   x23, #{n}\n    b.lo  _eita_stack_underflow\n"
  | .tosToNos =>
      "    mov   x10, x6\n    mov   x11, x7\n    mov   x12, x8\n    mov   x13, x9\n"
  | .nosToTos =>
      "    mov   x6, x10\n    mov   x7, x11\n    mov   x8, x12\n    mov   x9, x13\n"
  | .loadFieldTos f =>
      s!"    ldr   x6, [x20, #{f.offset}]\n    mov   x7, #0\n    mov   x8, #0\n    mov   x9, #0\n"
  | .loadU64Off off =>
      s!"    ldr   x6, [x20, #{off}]\n    mov   x7, #0\n    mov   x8, #0\n    mov   x9, #0\n"
  | .loadU256Off off =>
      if off + 16 ≤ 504 then
        s!"    ldp   x6, x7, [x20, #{off}]\n    ldp   x8, x9, [x20, #{off + 16}]\n"
      else
        s!"    add   x14, x20, #{off}\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n"
  | .loadZeroTos =>
      "    mov   x6, #0\n    mov   x7, #0\n    mov   x8, #0\n    mov   x9, #0\n"
  | .pcMinus1Tos =>
      "    sub   x6, x21, #1\n    mov   x7, #0\n    mov   x8, #0\n    mov   x9, #0\n"
  | .chargeGasPushTos c =>
      s!"    subs  x22, x22, #{c}\n    b.lo  _eita_oog\n    mov   x6, x22\n    mov   x7, #0\n    mov   x8, #0\n    mov   x9, #0\n"
  | .bitwise op =>
      let m := op.mnem
      s!"    {m}   x10, x10, x6\n    {m}   x11, x11, x7\n    {m}   x12, x12, x8\n    {m}   x13, x13, x9\n" ++
      "    mov   x6, x10\n    mov   x7, x11\n    mov   x8, x12\n    mov   x9, x13\n"
  | .arith k =>
      let (f, mid, l) := k.mnems
      s!"    {f}  x10, x6, x10\n    {mid}  x11, x7, x11\n    {mid}  x12, x8, x12\n    {l}   x13, x9, x13\n" ++
      "    mov   x6, x10\n    mov   x7, x11\n    mov   x8, x12\n    mov   x9, x13\n"
  | .cmpChain swapped cond =>
      (if swapped then
        "    subs  xzr, x10, x6\n    sbcs  xzr, x11, x7\n    sbcs  xzr, x12, x8\n    sbcs  xzr, x13, x9\n"
       else
        "    subs  xzr, x6, x10\n    sbcs  xzr, x7, x11\n    sbcs  xzr, x8, x12\n    sbcs  xzr, x9, x13\n") ++
      s!"    cset  x6, {cond.mnem}\n    mov   x7, #0\n    mov   x8, #0\n    mov   x9, #0\n"
  | .eqReduce =>
      "    eor   x14, x6, x10\n    eor   x15, x7, x11\n    orr   x14, x14, x15\n" ++
      "    eor   x15, x8, x12\n    orr   x14, x14, x15\n    eor   x15, x9, x13\n    orr   x14, x14, x15\n" ++
      "    cmp   x14, #0\n    cset  x6, eq\n    mov   x7, #0\n    mov   x8, #0\n    mov   x9, #0\n"
  | .iszeroReduce =>
      "    orr   x14, x6, x7\n    orr   x15, x8, x9\n    orr   x14, x14, x15\n" ++
      "    cmp   x14, #0\n    cset  x6, eq\n    mov   x7, #0\n    mov   x8, #0\n    mov   x9, #0\n"
  | .clzReduce => String.join (clzReduceInstrs.map AInstr.emitARM64)
  | .notLimbs =>
      "    mvn   x6, x6\n    mvn   x7, x7\n    mvn   x8, x8\n    mvn   x9, x9\n"
  | .spInc =>
      "    add   x23, x23, #1\n"
  | .spDec =>
      "    sub   x23, x23, #1\n"
  | .spDec2 =>
      "    sub   x23, x23, #2\n"
  | .binHelper helper =>
      "    sub   sp, sp, #32\n    stp   x29, x30, [sp, #-16]!\n    add   x0, sp, #16\n" ++
      "    sub   x14, x23, #1\n    add   x1, x24, x14, lsl #5\n" ++
      "    sub   x14, x23, #2\n    add   x2, x24, x14, lsl #5\n" ++
      s!"    bl    {helper}\n" ++
      "    add   x14, sp, #16\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n" ++
      "    ldp   x29, x30, [sp], #16\n    add   sp, sp, #32\n"
  | .ternaryHelper helper =>
      "    sub   sp, sp, #32\n    stp   x29, x30, [sp, #-16]!\n    add   x0, sp, #16\n" ++
      "    sub   x14, x23, #1\n    add   x1, x24, x14, lsl #5\n" ++
      "    sub   x14, x23, #2\n    add   x2, x24, x14, lsl #5\n" ++
      "    sub   x14, x23, #3\n    add   x3, x24, x14, lsl #5\n" ++
      s!"    bl    {helper}\n" ++
      "    add   x14, sp, #16\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n" ++
      "    ldp   x29, x30, [sp], #16\n    add   sp, sp, #32\n"
  | .cbEnter scratch    => s!"    sub   sp, sp, #{scratch}\n    stp   x29, x30, [sp, #-16]!\n"
  | .cbExit scratch     => s!"    ldp   x29, x30, [sp], #16\n    add   sp, sp, #{scratch}\n"
  | .loadCtx reg        => s!"    ldr   x{reg}, [x20, #504]\n"
  | .loadCtxVia14 reg   => s!"    ldr   x14, [x20, #504]\n    mov   x{reg}, x14\n"
  | .loadTxStateCtx reg => s!"    ldr   x14, [x20, #504]\n    ldr   x{reg}, [x14, #64]\n"
  | .argStateField reg off => s!"    add   x{reg}, x20, #{off}\n"
  | .argStackPtr reg n  => s!"    sub   x14, x23, #{n}\n    add   x{reg}, x24, x14, lsl #5\n"
  | .argScratch reg     => s!"    add   x{reg}, sp, #16\n"
  | .argStateBase reg   => s!"    mov   x{reg}, x20\n"
  | .cbSlot slot        => s!"    ldr   x14, [x20, #496]\n    ldr   x14, [x14, #{slot}]\n    blr   x14\n"
  | .cbDirect name      => s!"    bl    {name}\n"
  | .chargeGasX0        => "    subs  x22, x22, x0\n    b.lo  _eita_oog\n"
  | .chargeGasX0Via14   => "    mov   x14, x0\n    subs  x22, x22, x14\n    b.lo  _eita_oog\n"
  | .chargeFixed n      => s!"    mov   x14, #{n}\n    subs  x22, x22, x14\n    b.lo  _eita_oog\n"
  | .loadScratchTos     => "    add   x14, sp, #16\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n"
  | .loadScratchU64Tos  => "    ldr   x6, [sp, #16]\n    mov   x7, #0\n    mov   x8, #0\n    mov   x9, #0\n"
  | .boundCheckHiTos    => "    orr   x14, x7, x8\n    orr   x14, x14, x9\n    cbnz  x14, _eita_oog\n"
  | .newEndTos add      => s!"    adds  x0, x6, #{add}\n    b.cs  _eita_oog\n"
  | .setAcc base        => s!"    mov   x17, #{base}\n"
  | .memExpand          => memExpandStr
  | .chargeAcc          => "    subs  x22, x22, x17\n    b.lo  _eita_oog\n"
  | .mloadTail          =>
      "    ldr   x14, [x20, #40]\n    add   x15, x6, #32\n    ldr   x16, [x20, #24]\n    cmp   x15, x16\n    csel  x16, x15, x16, hi\n    str   x16, [x20, #24]\n" ++
      "    add   x14, x14, x6\n    ldr   x6, [x14, #0]\n    ldr   x7, [x14, #8]\n    ldr   x8, [x14, #16]\n    ldr   x9, [x14, #24]\n" ++
      "    rev   x6, x6\n    rev   x7, x7\n    rev   x8, x8\n    rev   x9, x9\n" ++
      "    mov   x14, x6\n    mov   x6, x9\n    mov   x9, x14\n    mov   x14, x7\n    mov   x7, x8\n    mov   x8, x14\n"
  | .mstoreTail         =>
      "    add   x15, x6, #32\n    ldr   x16, [x20, #24]\n    cmp   x15, x16\n    csel  x16, x15, x16, hi\n    str   x16, [x20, #24]\n" ++
      "    ldr   x14, [x20, #40]\n    add   x14, x14, x6\n" ++
      "    rev   x0, x13\n    rev   x1, x12\n    rev   x2, x11\n    rev   x3, x10\n" ++
      "    str   x0, [x14, #0]\n    str   x1, [x14, #8]\n    str   x2, [x14, #16]\n    str   x3, [x14, #24]\n" ++
      "    sub   x23, x23, #2\n    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n"
  | .mstore8Tail        =>
      "    ldr   x14, [x20, #40]\n    add   x15, x6, #1\n    ldr   x16, [x20, #24]\n    cmp   x15, x16\n    csel  x16, x15, x16, hi\n    str   x16, [x20, #24]\n" ++
      "    strb  w10, [x14, x6]\n" ++
      "    sub   x23, x23, #2\n    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n"
  | .memExpandIfLen tag =>
      -- WAS: `cbz x10, 4f ; add x0, x6, x10` — the length's LOW LIMB decided
      -- "zero length", so a RETURN/REVERT of 2^64 bytes (low limb 0) skipped
      -- the expansion entirely and returned empty with gas to spare, where
      -- EELS charges an unaffordable expansion and OOGs. The #260 bug, in a
      -- different op. Now the range goes through `memRangeInstrs` (off at
      -- sp-1, len at sp-2), whose full-u256 semantics are proved against EELS
      -- in MemExpandSpec.
      String.join ((memRangeInstrs 2 1 .x0 s!".Lro{tag}0" s!".Lro{tag}1").map AInstr.emitARM64) ++
      "    mov   x17, #0\n    cbz   x0, 4f\n" ++
      memExpandStr ++
      "    subs  x22, x22, x17\n    b.lo  _eita_oog\n4:\n"
  | .setOutput          =>
      "    str   x10, [x20, #120]\n    ldr   x14, [x20, #40]\n    add   x14, x14, x6\n    str   x14, [x20, #112]\n" ++
      "    add   x15, x6, x10\n    ldr   x16, [x20, #24]\n    cmp   x15, x16\n    csel  x16, x15, x16, hi\n    str   x16, [x20, #24]\n"
  | .setReverted        => "    strb  w14, [x20, #129]\n"
  | .copyGasCharge cost => String.join ((copyGasInstrs cost).map AInstr.emitARM64)
  | .returndataBounds => String.join (returndataBoundsInstrs.map AInstr.emitARM64)
  | .staticValueGuard => String.join (staticValueGuardInstrs.map AInstr.emitARM64)
  | .mcopyGasCharge cost => String.join ((mcopyGasInstrs cost).map AInstr.emitARM64)
  | .copyCbPop3 helper  =>
      "    stp   x29, x30, [sp, #-16]!\n    mov   x0, x20\n" ++
      "    sub   x14, x23, #1\n    add   x1, x24, x14, lsl #5\n" ++
      "    sub   x14, x23, #2\n    add   x2, x24, x14, lsl #5\n" ++
      "    sub   x14, x23, #3\n    add   x3, x24, x14, lsl #5\n" ++
      s!"    bl    {helper}\n    ldp   x29, x30, [sp], #16\n" ++
      "    sub   x23, x23, #3\n    cmp   x23, #1\n    b.lt  7f\n    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n7:\n" ++
      "    cmp   x23, #2\n    b.lt  8f\n    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    ldp   x10, x11, [x14]\n    ldp   x12, x13, [x14, #16]\n8:\n"
  | .keccakGasCharge cost => String.join ((keccakGasInstrs cost).map AInstr.emitARM64)
  | .keccakCbPop1 =>
      "    sub   sp, sp, #32\n    stp   x29, x30, [sp, #-16]!\n    mov   x0, x20\n" ++
      "    sub   x14, x23, #1\n    add   x1, x24, x14, lsl #5\n" ++
      "    sub   x14, x23, #2\n    add   x2, x24, x14, lsl #5\n" ++
      "    add   x3, sp, #16\n    bl    _eita_helper_keccak256\n" ++
      "    add   x14, sp, #16\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n" ++
      "    ldp   x29, x30, [sp], #16\n    add   sp, sp, #32\n    sub   x23, x23, #1\n"
  | .extcodecopyGasMem => String.join (extcodecopyGasInstrs.map AInstr.emitARM64)
  | .extcodecopyCb =>
      "    stp   x29, x30, [sp, #-16]!\n    ldr   x0, [x20, #504]\n" ++
      "    sub   x14, x23, #1\n    add   x1, x24, x14, lsl #5\n" ++
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    ldr   x15, [x14]\n" ++
      "    ldr   x16, [x20, #40]\n    add   x2, x16, x15\n" ++
      "    sub   x14, x23, #3\n    add   x14, x24, x14, lsl #5\n    ldr   x3, [x14]\n" ++
      -- src is a u256: any high limb ⇒ pass 2^64-1 (past any code, so the host zero-fills;
      -- the low limb alone wrapped 2^160 to 0 and copied code byte 0 — randomStatetest571)
      "    ldr   x15, [x14, #8]\n    ldr   x16, [x14, #16]\n    orr   x15, x15, x16\n" ++
      "    ldr   x16, [x14, #24]\n    orr   x15, x15, x16\n    cbz   x15, 94f\n" ++
      "    mov   x3, #0\n    sub   x3, x3, #1\n94:\n" ++
      -- len (the FIFTH argument, x4) is loaded HERE, by the op that passes it. It used
      -- to be inherited from `extcodecopyGasInstrs`, whose old form left len.l0 in x4;
      -- f812945 rebuilt that gadget on `memRangeInstrs` (len.l0 in x16, then clobbered)
      -- and x4 reached the host stale — a wrong copy length, wrong access gas and a
      -- memset past the memory arena (mainnet 4,972,698 tx 17). The low limb is exact:
      -- len ≥ 2^64 is already OOG in the gas gadget. `handler_callback_args_defined`
      -- now forbids any callback argument that an earlier op left behind.
      "    sub   x14, x23, #4\n    add   x14, x24, x14, lsl #5\n    ldr   x4, [x14]\n" ++
      "    ldr   x14, [x20, #496]\n    ldr   x14, [x14, #56]\n    blr   x14\n" ++
      "    subs  x22, x22, x0\n    b.lo  _eita_oog\n    ldp   x29, x30, [sp], #16\n" ++
      "    sub   x23, x23, #4\n" ++
      "    cmp   x23, #1\n    b.lt  91f\n    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n91:\n" ++
      "    cmp   x23, #2\n    b.lt  92f\n    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    ldp   x10, x11, [x14]\n    ldp   x12, x13, [x14, #16]\n92:\n"
  | .jumpValidate =>
      -- The destination is a u256 in x6-x9 and `cmp x6, x14` compares the LOW
      -- LIMB ONLY, so a dest of 2^64+k whose low limb lands on a real JUMPDEST
      -- used to jump where the spec (dest.toNat ≥ code_size → invalid) halts.
      -- Fold the high limbs first — the #260 / chained-sbcs family.
      "    orr   x14, x7, x8\n    orr   x14, x14, x9\n    cbnz  x14, _eita_invalid_jump\n" ++
      "    ldr   x14, [x20, #72]\n    cmp   x6, x14\n    b.hs  _eita_invalid_jump\n" ++
      String.join (jumpDestInstrs.map AInstr.emitARM64) ++ "    mov   x21, x6\n"
  | .jumpiCheck =>
      -- The CONDITION is folded over all four limbs (any nonzero word takes the
      -- branch); the DESTINATION was not — same single-limb compare as JUMP.
      "    orr   x14, x10, x11\n    orr   x15, x12, x13\n    orr   x14, x14, x15\n    cbz   x14, _eita_jumpi_fallthrough\n" ++
      "    orr   x14, x7, x8\n    orr   x14, x14, x9\n    cbnz  x14, _eita_invalid_jump\n" ++
      "    ldr   x14, [x20, #72]\n    cmp   x6, x14\n    b.hs  _eita_invalid_jump\n" ++
      String.join (jumpDestInstrs.map AInstr.emitARM64) ++ "    mov   x21, x6\n" ++
      "_eita_jumpi_pop:\n"
  | .jumpiTailGas cost =>
      s!"    subs  x22, x22, #{cost}\n    b.lo  _eita_oog\n    br    x27\n" ++
      "_eita_jumpi_fallthrough:\n    b     _eita_jumpi_pop\n"
  | .blobhashLookup => String.join (blobHashInstrs.map AInstr.emitARM64)
  | .staticGuard =>
      "    ldrb  w14, [x20, #130]\n    cbnz  w14, _eita_static_violation\n"
  | .sstoreSentry sentry =>
      movImmStr "x14" sentry ++ "    cmp   x22, x14\n    b.ls  _eita_oog\n"
  | .callFamilyCore name kind staticpFlag withValue =>
      let argsCount : Nat := if withValue then 7 else 6
      let inOffStackPos : Nat := if withValue then 4 else 3
      let inLenStackPos : Nat := if withValue then 5 else 4
      let outOffStackPos : Nat := if withValue then 6 else 5
      let outLenStackPos : Nat := if withValue then 7 else 6
      -- Memexp over the in/out ranges, full-u256, via the STRUCTURED AInstr IR
      -- (`callMemExpandEmit`) — no opaque asm blob; the full-u256 OOG guard is in
      -- `memRangeInstrs`/`memRangeEnd`, proved vs EELS in MemExpandSpec. Before
      -- this, the prologue read operands as u64 (limb0) and a huge argsLen whose
      -- low limb is 0 wrapped to a 0-length CALL (block 4466928 relay). (#260)
      callMemExpandEmit inOffStackPos inLenStackPos outOffStackPos outLenStackPos name ++
      "    sub   sp, sp, #192\n    stp   x29, x30, [sp, #-16]!\n" ++
      "    str   x21, [x20, #0]\n    str   x22, [x20, #8]\n    str   x23, [x20, #16]\n" ++
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    stp   x6, x7, [x14]\n    stp   x8, x9, [x14, #16]\n" ++
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    stp   x10, x11, [x14]\n    stp   x12, x13, [x14, #16]\n" ++
      s!"    mov   w0, #{kind}\n    str   w0, [sp, #16]\n" ++
      s!"    mov   w0, #{staticpFlag}\n    str   w0, [sp, #20]\n" ++
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    ldp   x0, x1, [x14]\n    ldp   x2, x3, [x14, #16]\n    stp   x0, x1, [sp, #24]\n    stp   x2, x3, [sp, #40]\n" ++
      (if withValue then
        "    sub   x14, x23, #3\n    add   x14, x24, x14, lsl #5\n    ldp   x0, x1, [x14]\n    ldp   x2, x3, [x14, #16]\n    stp   x0, x1, [sp, #56]\n    stp   x2, x3, [sp, #72]\n"
       else
        "    stp   xzr, xzr, [sp, #56]\n    stp   xzr, xzr, [sp, #72]\n") ++
      s!"    sub   x14, x23, #{inOffStackPos}\n" ++
      "    add   x14, x24, x14, lsl #5\n    ldr   x15, [x14]\n    ldr   x16, [x20, #40]\n    add   x15, x16, x15\n    str   x15, [sp, #88]\n" ++
      s!"    sub   x14, x23, #{inLenStackPos}\n" ++
      "    add   x14, x24, x14, lsl #5\n    ldr   x15, [x14]\n    str   x15, [sp, #96]\n" ++
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    ldp   x15, x16, [x14]\n    ldp   x0, x1, [x14, #16]\n    orr   x16, x16, x0\n    orr   x16, x16, x1\n    cmp   x16, #0\n    csinv x15, x15, xzr, eq\n    str   x15, [sp, #104]\n" ++
      "    stp   xzr, xzr, [sp, #112]\n    stp   xzr, xzr, [sp, #128]\n" ++
      "    ldr   x0, [x20, #504]\n    add   x1, sp, #16\n    add   x2, sp, #144\n    ldr   x14, [x20, #496]\n    ldr   x14, [x14, #88]\n    blr   x14\n" ++
      "    ldr   x0, [sp, #152]\n    str   x0, [x20, #96]\n    ldr   x0, [sp, #160]\n    str   x0, [x20, #104]\n" ++
      s!"    sub   x14, x23, #{outOffStackPos}\n" ++
      "    add   x14, x24, x14, lsl #5\n    ldr   x1, [x14]\n" ++
      s!"    sub   x14, x23, #{outLenStackPos}\n" ++
      "    add   x14, x24, x14, lsl #5\n    ldr   x2, [x14]\n    mov   x0, x20\n    bl    _eita_helper_returndata_to_mem\n" ++
      "    ldr   w15, [sp, #144]\n    ldr   x0, [sp, #168]\n" ++
      s!"    sub   x23, x23, #{argsCount - 1}\n" ++
      "    mov   x6, x15\n    and   x6, x6, #0xff\n    mov   x7, #0\n    mov   x8, #0\n    mov   x9, #0\n" ++
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    stp   x6, x7, [x14]\n    stp   x8, x9, [x14, #16]\n" ++
      s!"    cmp   x23, #2\n    b.lt  L_callret_{name}\n" ++
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    ldp   x10, x11, [x14]\n    ldp   x12, x13, [x14, #16]\n" ++
      s!"L_callret_{name}:\n" ++
      "    ldr   x22, [x20, #8]\n    subs  x22, x22, x0\n    b.lo  _eita_oog\n    ldp   x29, x30, [sp], #16\n    add   sp, sp, #192\n    br    x27\n"
  | .createCore =>
      "    sub   sp, sp, #192\n    stp   x29, x30, [sp, #-16]!\n" ++
      "    str   x21, [x20, #0]\n    str   x22, [x20, #8]\n    str   x23, [x20, #16]\n" ++
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    stp   x6, x7, [x14]\n    stp   x8, x9, [x14, #16]\n" ++
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    stp   x10, x11, [x14]\n    stp   x12, x13, [x14, #16]\n" ++
      -- #266: charge memexp over the init-code range [offset, offset+length)
      -- (operands now spilled to the stack arena). EELS create charges this.
      createMemExpandEmit 2 3 "create" ++
      "    mov   w0, #4\n    str   w0, [sp, #16]\n    str   wzr, [sp, #20]\n" ++
      "    stp   xzr, xzr, [sp, #24]\n    stp   xzr, xzr, [sp, #40]\n" ++
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    ldp   x0, x1, [x14]\n    ldp   x2, x3, [x14, #16]\n    stp   x0, x1, [sp, #56]\n    stp   x2, x3, [sp, #72]\n" ++
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    ldr   x15, [x14]\n    ldr   x16, [x20, #40]\n    add   x15, x16, x15\n    str   x15, [sp, #88]\n" ++
      "    sub   x14, x23, #3\n    add   x14, x24, x14, lsl #5\n    ldr   x15, [x14]\n    str   x15, [sp, #96]\n" ++
      "    str   x22, [sp, #104]\n    stp   xzr, xzr, [sp, #112]\n    stp   xzr, xzr, [sp, #128]\n" ++
      "    ldr   x0, [x20, #504]\n    add   x1, sp, #16\n    add   x2, sp, #144\n    ldr   x14, [x20, #496]\n    ldr   x14, [x14, #96]\n    blr   x14\n" ++
      -- EELS `create`: the frame's return data becomes the child's output — the init
      -- code's REVERT bytes on failure, empty on success (cb-create sets both cases).
      "    ldr   x14, [sp, #152]\n    str   x14, [x20, #96]\n    ldr   x14, [sp, #160]\n    str   x14, [x20, #104]\n" ++
      "    ldr   w15, [sp, #144]\n    cbz   w15, L_create_fail\n" ++
      "    add   x14, sp, #176\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n    b     L_create_done\n" ++
      "L_create_fail:\n    mov   x6, #0\n    mov   x7, #0\n    mov   x8, #0\n    mov   x9, #0\n" ++
      "L_create_done:\n    ldr   x0, [sp, #168]\n    ldr   x22, [x20, #8]\n    subs  x22, x22, x0\n    b.lo  _eita_oog\n" ++
      "    sub   x23, x23, #2\n    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    stp   x6, x7, [x14]\n    stp   x8, x9, [x14, #16]\n" ++
      "    cmp   x23, #2\n    b.lt  L_create_done2\n    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    ldp   x10, x11, [x14]\n    ldp   x12, x13, [x14, #16]\n" ++
      "L_create_done2:\n    ldp   x29, x30, [sp], #16\n    add   sp, sp, #192\n    br    x27\n"
  | .create2Core =>
      "    sub   sp, sp, #192\n    stp   x29, x30, [sp, #-16]!\n" ++
      "    str   x21, [x20, #0]\n    str   x22, [x20, #8]\n    str   x23, [x20, #16]\n" ++
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    stp   x6, x7, [x14]\n    stp   x8, x9, [x14, #16]\n" ++
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    stp   x10, x11, [x14]\n    stp   x12, x13, [x14, #16]\n" ++
      -- #266: memexp over init range [offset, offset+length) — same omission as
      -- CREATE. (CREATE2 keccak word cost is already in spec-create-gas.)
      createMemExpandEmit 2 3 "create2" ++
      "    mov   w0, #5\n    str   w0, [sp, #16]\n    str   wzr, [sp, #20]\n" ++
      "    stp   xzr, xzr, [sp, #24]\n    stp   xzr, xzr, [sp, #40]\n" ++
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    ldp   x0, x1, [x14]\n    ldp   x2, x3, [x14, #16]\n    stp   x0, x1, [sp, #56]\n    stp   x2, x3, [sp, #72]\n" ++
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    ldr   x15, [x14]\n    ldr   x16, [x20, #40]\n    add   x15, x16, x15\n    str   x15, [sp, #88]\n" ++
      "    sub   x14, x23, #3\n    add   x14, x24, x14, lsl #5\n    ldr   x15, [x14]\n    str   x15, [sp, #96]\n" ++
      "    str   x22, [sp, #104]\n" ++
      "    sub   x14, x23, #4\n    add   x14, x24, x14, lsl #5\n    ldp   x0, x1, [x14]\n    ldp   x2, x3, [x14, #16]\n    stp   x0, x1, [sp, #112]\n    stp   x2, x3, [sp, #128]\n" ++
      "    ldr   x0, [x20, #504]\n    add   x1, sp, #16\n    add   x2, sp, #144\n    ldr   x14, [x20, #496]\n    ldr   x14, [x14, #96]\n    blr   x14\n" ++
      -- EELS `create2`: same return-data rule as CREATE.
      "    ldr   x14, [sp, #152]\n    str   x14, [x20, #96]\n    ldr   x14, [sp, #160]\n    str   x14, [x20, #104]\n" ++
      "    ldr   w15, [sp, #144]\n    cbz   w15, L_create2_fail\n" ++
      "    add   x14, sp, #176\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n    b     L_create2_done\n" ++
      "L_create2_fail:\n    mov   x6, #0\n    mov   x7, #0\n    mov   x8, #0\n    mov   x9, #0\n" ++
      "L_create2_done:\n    ldr   x0, [sp, #168]\n    ldr   x22, [x20, #8]\n    subs  x22, x22, x0\n    b.lo  _eita_oog\n" ++
      "    sub   x23, x23, #3\n    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    stp   x6, x7, [x14]\n    stp   x8, x9, [x14, #16]\n" ++
      "    cmp   x23, #2\n    b.lt  L_create2_done2\n    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    ldp   x10, x11, [x14]\n    ldp   x12, x13, [x14, #16]\n" ++
      "L_create2_done2:\n    ldp   x29, x30, [sp], #16\n    add   sp, sp, #192\n    br    x27\n"
  | .expGasCharge cost byteCost => String.join ((expGasInstrs cost byteCost).map AInstr.emitARM64)
  | .selfdestructCb =>
      "    stp   x29, x30, [sp, #-16]!\n" ++
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    stp   x6, x7, [x14]\n    stp   x8, x9, [x14, #16]\n" ++
      "    ldr   x0, [x20, #504]\n    add   x1, x20, #144\n    mov   x2, x14\n" ++
      "    ldr   x14, [x20, #496]\n    ldr   x14, [x14, #104]\n    blr   x14\n" ++
      "    subs  x22, x22, x0\n    b.lo  _eita_oog\n    ldp   x29, x30, [sp], #16\n"
  | .sstoreCb =>
      "    stp   x29, x30, [sp, #-16]!\n" ++
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    stp   x6, x7, [x14]\n    stp   x8, x9, [x14, #16]\n" ++
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    stp   x10, x11, [x14]\n    stp   x12, x13, [x14, #16]\n" ++
      "    ldr   x0, [x20, #504]\n    add   x1, x20, #144\n" ++
      "    sub   x14, x23, #1\n    add   x2, x24, x14, lsl #5\n" ++
      "    sub   x14, x23, #2\n    add   x3, x24, x14, lsl #5\n" ++
      "    ldr   x14, [x20, #496]\n    ldr   x14, [x14, #8]\n    blr   x14\n" ++
      "    subs  x22, x22, x0\n    b.lo  _eita_oog\n    ldp   x29, x30, [sp], #16\n" ++
      "    ldr   x14, [x20, #504]\n    ldr   x15, [x14, #0]\n    ldr   x16, [x14, #16]\n    mov   x17, #104\n    madd  x0, x15, x17, x16\n" ++
      "    str   xzr, [x0, #0]\n    ldp   x1, x2, [x20, #144]\n    ldp   x3, x4, [x20, #160]\n    stp   x1, x2, [x0, #8]\n    stp   x3, x4, [x0, #24]\n" ++
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n" ++
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    ldp   x10, x11, [x14]\n    ldp   x12, x13, [x14, #16]\n" ++
      "    stp   x6, x7, [x0, #40]\n    stp   x8, x9, [x0, #56]\n    stp   x10, x11, [x0, #72]\n    stp   x12, x13, [x0, #88]\n" ++
      "    ldr   x14, [x20, #504]\n    add   x15, x15, #1\n    str   x15, [x14, #0]\n" ++
      "    sub   x23, x23, #2\n" ++
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n"
  | .logEmit n cost =>
      -- Spill the register-cached TOS/NOS (off, len) so the stack memory the
      -- host will be pointed at is current (same discipline as sstoreCb).
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    stp   x6, x7, [x14]\n    stp   x8, x9, [x14, #16]\n" ++
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    stp   x10, x11, [x14]\n    stp   x12, x13, [x14, #16]\n" ++
      -- len ≥ 2^64 ⇒ OOG (8·len alone exceeds any gas); len = 0 ⇒ no memexp, any
      -- offset (EELS skips size 0); else off ≥ 2^64 or off+len ≥ 2^64 ⇒ OOG.
      "    orr   x14, x11, x12\n    orr   x14, x14, x13\n    cbnz  x14, _eita_oog\n" ++
      s!"    mov   x17, #{cost}\n" ++
      "    add   x17, x17, x10, lsl #3\n" ++
      "    cbz   x10, 4f\n" ++
      "    orr   x14, x7, x8\n    orr   x14, x14, x9\n    cbnz  x14, _eita_oog\n" ++
      "    adds  x0, x6, x10\n    b.cs  _eita_oog\n" ++
      memExpandStr ++
      "4:\n" ++
      "    ldr   x14, [x20, #504]\n    ldr   x15, [x14, #8]\n    add   x15, x15, #1\n    str   x15, [x14, #8]\n" ++
      "    add   x15, x6, x10\n    ldr   x16, [x20, #24]\n    cmp   x15, x16\n    csel  x16, x15, x16, hi\n    str   x16, [x20, #24]\n" ++
      s!"    sub   x23, x23, #{2 + n}\n" ++
      "    subs  x22, x22, x17\n    b.lo  _eita_oog\n" ++
      -- Deliver the log to the host (vtable slot 9, cb->log) — the observation seam.
      -- Null slot ⇒ skip: replays that do not collect logs are byte-identical.
      -- After the pop the popped slots still hold the operands: off at sp+n+1,
      -- len at sp+n, topic_i at sp+n-1-i (so x3 → topic_{n-1}, ascending to topic_0).
      -- Args: x0 ctx, x1 &address, x2 n, x3 topics, x4 memory+off, x5 len.
      "    ldr   x14, [x20, #496]\n    ldr   x14, [x14, #72]\n    cbz   x14, 7f\n" ++
      "    stp   x29, x30, [sp, #-16]!\n" ++
      "    ldr   x0, [x20, #504]\n    add   x1, x20, #144\n" ++
      s!"    mov   x2, #{n}\n" ++
      "    add   x3, x24, x23, lsl #5\n" ++
      s!"    add   x15, x23, #{n + 1}\n" ++
      "    add   x15, x24, x15, lsl #5\n    ldr   x15, [x15]\n    ldr   x4, [x20, #40]\n    add   x4, x4, x15\n" ++
      s!"    add   x15, x23, #{n}\n" ++
      "    add   x15, x24, x15, lsl #5\n    ldr   x5, [x15]\n" ++
      "    blr   x14\n    ldp   x29, x30, [sp], #16\n" ++
      "7:\n" ++
      "    cmp   x23, #1\n    b.lt  5f\n    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n5:\n" ++
      "    cmp   x23, #2\n    b.lt  6f\n    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    ldp   x10, x11, [x14]\n    ldp   x12, x13, [x14, #16]\n6:\n" ++
      "    br    x27\n"
  | .pushImm n =>
      -- `pushWideInstrs`: wide big-endian loads, no per-byte branch (the code
      -- image's zero padding supplies the bytes past code_size).
      String.join ((pushWideInstrs n).map AInstr.emitARM64)
  | .tstoreCb =>
      "    stp   x29, x30, [sp, #-16]!\n" ++
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    stp   x6, x7, [x14]\n    stp   x8, x9, [x14, #16]\n" ++
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    stp   x10, x11, [x14]\n    stp   x12, x13, [x14, #16]\n" ++
      "    ldr   x1, [x20, #504]\n    ldr   x0, [x1, #64]\n    add   x2, x20, #144\n" ++
      "    sub   x14, x23, #1\n    add   x3, x24, x14, lsl #5\n" ++
      "    sub   x14, x23, #2\n    add   x4, x24, x14, lsl #5\n" ++
      "    bl    _eita_ts_tstore\n    ldp   x29, x30, [sp], #16\n" ++
      "    sub   x23, x23, #2\n" ++
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n" ++
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    ldp   x10, x11, [x14]\n    ldp   x12, x13, [x14, #16]\n"
  | .storeTos =>
      "    sub   x14, x23, #1\n    add   x14, x24, x14, lsl #5\n    stp   x6, x7, [x14]\n    stp   x8, x9, [x14, #16]\n"
  | .reloadNos =>
      "    sub   x14, x23, #2\n    add   x14, x24, x14, lsl #5\n    ldp   x10, x11, [x14]\n    ldp   x12, x13, [x14, #16]\n"
  | .brCont =>
      "    br    x27\n"
  | .exitGas c =>
      s!"    subs  x22, x22, #{c}\n    b.lo  _eita_oog\n    br    x27\n"
  | .pcDec =>
      "    sub   x21, x21, #1\n"
  | .setHalted =>
      "    mov   w14, #1\n    strb  w14, [x20, #128]\n"
  | .jumpSyncRet =>
      "    adrp  x27, _eita_sync_and_ret@PAGE\n    add   x27, x27, _eita_sync_and_ret@PAGEOFF\n    br    x27\n"
  | .branchOOG =>
      "    b     _eita_oog\n"
  | .dupLoad n =>
      s!"    sub   x14, x23, #{n}\n    add   x14, x24, x14, lsl #5\n    ldp   x6, x7, [x14]\n    ldp   x8, x9, [x14, #16]\n"
  | .swapPartner n =>
      s!"    sub   x14, x23, #{n + 1}\n    add   x14, x24, x14, lsl #5\n" ++
      "    ldp   x0, x1, [x14]\n    ldp   x2, x3, [x14, #16]\n" ++
      "    stp   x6, x7, [x14]\n    stp   x8, x9, [x14, #16]\n" ++
      "    mov   x6, x0\n    mov   x7, x1\n    mov   x8, x2\n    mov   x9, x3\n"

/-- Effect of an op. A trap (`oog`/`trap`) sets its flag; the real handler then
    branches to a fault label, discarding the rest, so post-trap register state
    is irrelevant — we set the flag (never cleared) and don't model a guard. -/
def Op.denote : Op → Mach → Mach
  | .ovfGuard, m         => if m.sp ≥ 1024 then { m with trap := true } else m
  | .underflow n, m      => if m.sp < n then { m with trap := true } else m
  | .tosToNos, m         => { m with nos := m.tos }
  | .nosToTos, m         => { m with tos := m.nos }
  | .loadFieldTos f, m   => { m with tos := U256.ofScalar (m.stateMem f.offset) }
  | .loadU64Off off, m   => { m with tos := U256.ofScalar (m.stateMem off) }
  | .loadU256Off off, m  =>
      { m with tos := ⟨m.stateMem off, m.stateMem (off+8), m.stateMem (off+16), m.stateMem (off+24)⟩ }
  | .loadZeroTos, m      => { m with tos := U256.ofScalar 0 }
  | .pcMinus1Tos, m      => { m with tos := U256.ofScalar (m.pcReg - 1) }
  | .chargeGasPushTos c, m =>
      if m.gas < c then { m with oog := true }
      else { m with gas := m.gas - c, tos := U256.ofScalar (m.gas - c) }
  | .bitwise op, m       => { m with tos := U256.bin op m.nos m.tos }
  | .arith k, m          => { m with tos := k.apply m.tos m.nos }
  | .cmpChain swapped cond, m => { m with tos := U256.ofScalar (cmpResult swapped cond m.tos m.nos) }
  | .eqReduce, m         => { m with tos := U256.ofScalar (if m.tos = m.nos then 1 else 0) }
  | .iszeroReduce, m     => { m with tos := U256.ofScalar (if m.tos = ⟨0,0,0,0⟩ then 1 else 0) }
  | .clzReduce, m        => { m with tos := U256.ofScalar (clzLimbs m.tos) }
  | .notLimbs, m         =>
      { m with tos := ⟨2^64-1 - m.tos.l0, 2^64-1 - m.tos.l1, 2^64-1 - m.tos.l2, 2^64-1 - m.tos.l3⟩ }
  | .spInc, m            => { m with sp := m.sp + 1 }
  | .spDec, m            => { m with sp := m.sp - 1 }
  | .spDec2, m           => { m with sp := m.sp - 2 }
  | .binHelper h, m      => { m with tos := m.helperFn h m.tos m.nos }
  | .ternaryHelper h, m  => { m with tos := m.helperFn3 h m.tos m.nos (m.mem (m.sp - 3)) }
  -- frame mgmt + arg-register setup + the cb invoke have no effect on the
  -- modelled machine; the cb's gas (cbGas) and result (cbResult) are inputs.
  | .cbEnter _, m        => m
  | .cbExit _, m         => m
  | .loadCtx _, m        => m
  | .loadCtxVia14 _, m   => m
  | .loadTxStateCtx _, m => m
  | .argStateField _ _, m => m
  | .argStackPtr _ _, m  => m
  | .argScratch _, m     => m
  | .argStateBase _, m   => m
  | .cbSlot _, m         => m
  | .cbDirect _, m       => m
  | .chargeGasX0, m      => if m.gas < m.cbGas then { m with oog := true } else { m with gas := m.gas - m.cbGas }
  | .chargeGasX0Via14, m => if m.gas < m.cbGas then { m with oog := true } else { m with gas := m.gas - m.cbGas }
  | .chargeFixed n, m    => if m.gas < n then { m with oog := true } else { m with gas := m.gas - n }
  | .loadScratchTos, m   => { m with tos := m.cbResult }
  | .loadScratchU64Tos, m => { m with tos := m.cbResult }
  | .boundCheckHiTos, m  =>
      if m.tos.l1 ≠ 0 ∨ m.tos.l2 ≠ 0 ∨ m.tos.l3 ≠ 0 then { m with oog := true } else m
  | .newEndTos add, m    =>
      if 2^64 ≤ m.tos.l0 + add then { m with oog := true } else { m with scratch := m.tos.l0 + add }
  | .setAcc base, m      => { m with acc := base }
  | .memExpand, m        =>
      if m.memCap < m.scratch then { m with oog := true }
      else
        let nw := (m.scratch + 31) / 32
        let ow := m.memSize / 32
        if nw ≤ ow then m
        else { m with acc := m.acc + ((3*nw + nw*nw/512) - (3*ow + ow*ow/512)), memSize := nw * 32 }
  | .chargeAcc, m        => if m.gas < m.acc then { m with oog := true } else { m with gas := m.gas - m.acc }
  | .mloadTail, m        => { m with tos := m.evmMem m.tos.l0 }     -- mp(#24) is dead post-MSIZE-fix
  | .mstoreTail, m       =>
      { m with evmMem := upd m.evmMem m.tos.l0 m.nos, sp := m.sp - 2, tos := m.mem (m.sp - 3) }
  | .mstore8Tail, m      =>
      { m with evmMem := upd m.evmMem m.tos.l0 m.nos, sp := m.sp - 2, tos := m.mem (m.sp - 3) }
  | .memExpandIfLen _, m =>
      -- `memRangeEnd` over the FULL u256 (none = the true end is ≥ 2^64, which
      -- EELS charges as unaffordable; some 0 = zero length, no expansion).
      let m0 := { m with acc := 0 }
      match memRangeEnd m.tos m.nos with
      | none => { m0 with oog := true }
      | some 0 => m0
      | some newEnd =>
        if m.memCap < newEnd then { m0 with oog := true }
        else
          let nw := (newEnd + 31) / 32
          let ow := m.memSize / 32
          let a := if nw ≤ ow then 0 else (3*nw + nw*nw/512) - (3*ow + ow*ow/512)
          let ms := if nw ≤ ow then m.memSize else nw * 32
          if m.gas < a then { m0 with oog := true, memSize := ms }
          else { m0 with gas := m.gas - a, memSize := ms }
  | .setOutput, m        => m   -- output_ptr/size host-read; mp(#24) dead
  | .setReverted, m      => m   -- EvmState.reverted byte (host-observable)
  | .copyGasCharge _, m  => m   -- coarse: gas computed/charged (host effect); byte-identical emit is the guarantee
  | .returndataBounds, m => m  -- coarse: the bound reads returndata_size (host state)
  | .staticValueGuard, m =>
      -- static flag, then the four limbs of stack[sp-3] (CALL's value) OR'd: cbnz ⇒ violation
      if m.isStatic ∧ m.mem (m.sp - 3) ≠ U256.ofScalar 0 then { m with trap := true } else m
  | .mcopyGasCharge _, m => m   -- coarse: gas computed/charged (host effect); #270 memexp(max(dst,src)+len)
  | .copyCbPop3 _, m     => { m with sp := m.sp - 3 }
  | .keccakGasCharge _, m => m   -- coarse: gas computed/charged (host effect); byte-identical emit is the guarantee
  | .keccakCbPop1, m     => { m with sp := m.sp - 1, tos := m.cbResult }
  | .extcodecopyGasMem, m => m   -- coarse: memexp gas (host effect); byte-identical emit is the guarantee
  | .extcodecopyCb, m    => { m with sp := m.sp - 4 }
  | .jumpValidate, m     =>
      -- Refined twice. (1) A destination that does not fit u64 is INVALID, never
      -- truncated (was `pc := tos.l0` unconditionally). (2) The in-range and
      -- JUMPDEST tests are modelled, not left as "host control flow": the
      -- destination must be below codeSize and marked in the host's
      -- valid-JUMPDEST map (`jumpDest`, EvmState #136). The map, not `code dest
      -- = 0x5b`, is what the asm reads — the byte test accepted a 0x5b inside a
      -- PUSH immediate (5,800,596 tx 117), and a coarse denotation hid it.
      if m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0 ∧ m.tos.l0 < m.codeSize
         ∧ m.jumpDest m.tos.l0 = true
      then { m with pcReg := m.tos.l0 }
      else { m with trap := true }
  | .blobhashLookup, m   =>
      -- EELS `blob_hash`: hashes[index] when index < len(hashes), else 0. The range
      -- test is over the whole u256 (high limbs fold into the `cbnz`), the count is
      -- the u64 field #560 and the table the host's per-tx array behind #552.
      if m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0 ∧ m.tos.l0 < m.stateMem 560
      then { m with tos := m.blobHash m.tos.l0 }
      else { m with tos := U256.ofScalar 0 }
  | .jumpiCheck, m       =>
      -- Taken only when the condition (NOS, all four limbs) is nonzero; the
      -- destination then faces the same width, bounds and map tests as JUMP.
      if m.nos.l0 = 0 ∧ m.nos.l1 = 0 ∧ m.nos.l2 = 0 ∧ m.nos.l3 = 0 then m
      else if m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0 ∧ m.tos.l0 < m.codeSize
              ∧ m.jumpDest m.tos.l0 = true
      then { m with pcReg := m.tos.l0 }
      else { m with trap := true }
  | .jumpiTailGas c, m   => if m.gas < c then { m with oog := true } else { m with gas := m.gas - c, ret := true }
  | .staticGuard, m      =>
      -- `ldrb w14, [x20, #130] ; cbnz w14, _eita_static_violation`
      if m.isStatic then { m with trap := true } else m
  | .tstoreCb, m         => { m with sp := m.sp - 2 }
  | .logEmit n _, m      => { m with sp := m.sp - (2 + n), ret := true }   -- gas/log/mp are host effects
  | .pushImm n, m        =>
      -- The immediate is the n bytes from `pc`, big-endian, 0 once `pc+i`
      -- reaches `codeSize` (EELS pads the code stream with zeros): the
      -- `pushAccum` fold. `PushWide.pushWide_correct` proves the wide loads
      -- compute it under the code image's padding contract.
      { m with pcReg := m.pcReg + n
             , tos := pushAccum m.code m.codeSize m.pcReg n m.tos }
  | .sstoreSentry s, m   => if m.gas ≤ s then { m with oog := true } else m   -- EIP-1706 gas sentry
  | .sstoreCb, m         => { m with sp := m.sp - 2 }   -- cb gas + journal entry are host effects
  | .selfdestructCb, m   => m   -- cb gas + world destruct are host effects
  | .callFamilyCore _ _ _ wv, m =>   -- pop argsCount, push success (gas/sub-frame/returndata are host effects)
      { m with sp := m.sp - (if wv then 6 else 5), ret := true }
  | .createCore, m       => { m with sp := m.sp - 2, ret := true }   -- pop 3 push 1 (host create)
  | .create2Core, m      => { m with sp := m.sp - 3, ret := true }   -- pop 4 push 1 (host create)
  | .expGasCharge _ _, m => m   -- coarse: ebytes-based gas (host effect); byte-identical emit is the guarantee
  | .storeTos, m         => { m with mem := upd m.mem (m.sp - 1) m.tos }
  | .reloadNos, m        => { m with nos := m.mem (m.sp - 2) }
  | .brCont, m           => { m with ret := true }
  | .exitGas c, m        =>
      if m.gas < c then { m with oog := true }
      else { m with gas := m.gas - c, ret := true }
  | .pcDec, m            => { m with pcReg := m.pcReg - 1 }
  | .setHalted, m        => { m with halted := true }
  | .jumpSyncRet, m      => { m with ret := true }
  | .branchOOG, m        => { m with oog := true }
  | .dupLoad n, m        => { m with tos := m.mem (m.sp - n) }
  | .swapPartner n, m    =>
      { m with tos := m.mem (m.sp - (n + 1))
             , mem := upd m.mem (m.sp - (n + 1)) m.tos }

abbrev Prog := List Op

def Prog.emit (p : Prog) : String := String.join (p.map Op.emit)
def Prog.denote (p : Prog) (m : Mach) : Mach := p.foldl (fun s o => o.denote s) m

/-! ## The value-pusher family (MSIZE / PC / GAS) -/

def msizeBody (cost : Nat) : Prog :=
  [.ovfGuard, .tosToNos, .loadFieldTos .memSize, .spInc, .storeTos, .exitGas cost]

def pcBody (cost : Nat) : Prog :=
  [.ovfGuard, .tosToNos, .pcMinus1Tos, .spInc, .storeTos, .exitGas cost]

def gasBody (cost : Nat) : Prog :=
  [.ovfGuard, .tosToNos, .chargeGasPushTos cost, .spInc, .storeTos, .brCont]

/-- MSIZE pushes the (aligned) memory size field. -/
def msizeSpec (m : Mach) : U256 := U256.ofScalar (m.stateMem Field.memSize.offset)

theorem msize_correct (m : Mach) (cost : Nat) (hsp : m.sp < 1024) (hg : cost ≤ m.gas) :
    let m' := (msizeBody cost).denote m
    m'.tos = msizeSpec m ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp + 1
    ∧ m'.mem m.sp = msizeSpec m := by
  simp [Prog.denote, msizeBody, Op.denote, msizeSpec, upd,
        Nat.not_le.2 hsp, Nat.not_lt.2 hg]

/-- The exact bug we shipped: load `mp` (#24) instead of `memSize` (#48). -/
def msizeBugBody (cost : Nat) : Prog :=
  [.ovfGuard, .tosToNos, .loadFieldTos .mp, .spInc, .storeTos, .exitGas cost]

/-- **The bug is rejected by the proof**: a state with `mp ≠ memSize` makes the
    buggy handler push the wrong value, so it cannot meet the spec. -/
theorem msize_bug_rejected :
    ∃ (m : Mach) (cost : Nat), m.sp < 1024 ∧ cost ≤ m.gas
      ∧ ((msizeBugBody cost).denote m).tos ≠ msizeSpec m := by
  refine ⟨{ gas := 100, sp := 0, pcReg := 0, tos := default, nos := default
          , mem := fun _ => default
          , stateMem := fun off => if off = Field.memSize.offset then 32 else 0
          , helperFn := fun _ _ _ => default, helperFn3 := fun _ _ _ _ => default
          , cbGas := 0, cbResult := default
          , evmMem := fun _ => default, memSize := 0, memCap := 0, acc := 0, scratch := 0
          , code := fun _ => 0, codeSize := 0, isStatic := false, oog := false, trap := false, ret := false, halted := false }, 3,
          by decide, by decide, ?_⟩
  simp [Prog.denote, msizeBugBody, Op.denote, msizeSpec, U256.ofScalar, Field.offset]

theorem pc_correct (m : Mach) (cost : Nat) (hsp : m.sp < 1024) (hg : cost ≤ m.gas) :
    let m' := (pcBody cost).denote m
    m'.tos = U256.ofScalar (m.pcReg - 1) ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp + 1 := by
  simp [Prog.denote, pcBody, Op.denote, Nat.not_le.2 hsp, Nat.not_lt.2 hg]

theorem gas_correct (m : Mach) (cost : Nat) (hsp : m.sp < 1024) (hg : cost ≤ m.gas) :
    let m' := (gasBody cost).denote m
    m'.tos = U256.ofScalar (m.gas - cost) ∧ m'.gas = m.gas - cost := by
  simp [Prog.denote, gasBody, Op.denote, Nat.not_le.2 hsp, Nat.not_lt.2 hg]

/-! ## The bitwise binary family (AND / OR / XOR) -/

def bitwiseBody (op : BitOp) (cost : Nat) : Prog :=
  [.underflow 2, .bitwise op, .spDec, .storeTos, .reloadNos, .exitGas cost]

/-- EVM AND/OR/XOR pop top + second and push their limb-wise combination. -/
def bitwiseSpec (op : BitOp) (m : Mach) : U256 := U256.bin op m.nos m.tos

theorem bitwise_correct (op : BitOp) (m : Mach) (cost : Nat)
    (hsp : 2 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (bitwiseBody op cost).denote m
    m'.tos = bitwiseSpec op m ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp - 1 := by
  simp [Prog.denote, bitwiseBody, Op.denote, bitwiseSpec, upd,
        Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

/-! ## Env value-pushers (ADDRESS/CALLER/…, CALLDATASIZE/…, BLOBBASEFEE) + POP

BLOBBASEFEE (0x4a, EIP-7516) is `envU256Body 568 2`: the host computes the block's
blob base fee once per block (the emitted `spec-blob-base-fee`, Evm.CL.GasEmit) and
writes it to EvmState #568; `Evm.CL.BlobEnv` ties the pushed limbs to the spec. -/

/-- Push a full u256 EvmState field (4 limbs from byte offset `off`). -/
def envU256Body (off cost : Nat) : Prog :=
  [.ovfGuard, .tosToNos, .loadU256Off off, .spInc, .storeTos, .exitGas cost]

/-- Push a u64 EvmState field (offset `off`), high limbs zero. -/
def envU64Body (off cost : Nat) : Prog :=
  [.ovfGuard, .tosToNos, .loadU64Off off, .spInc, .storeTos, .exitGas cost]

/-- POP: drop the top, the old second becomes the new top. -/
def popBody (cost : Nat) : Prog :=
  [.underflow 1, .nosToTos, .spDec, .reloadNos, .exitGas cost]

theorem envU256_correct (off cost : Nat) (m : Mach) (hsp : m.sp < 1024) (hg : cost ≤ m.gas) :
    let m' := (envU256Body off cost).denote m
    m'.tos = ⟨m.stateMem off, m.stateMem (off+8), m.stateMem (off+16), m.stateMem (off+24)⟩
    ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp + 1 := by
  simp [Prog.denote, envU256Body, Op.denote, Nat.not_le.2 hsp, Nat.not_lt.2 hg]

theorem envU64_correct (off cost : Nat) (m : Mach) (hsp : m.sp < 1024) (hg : cost ≤ m.gas) :
    let m' := (envU64Body off cost).denote m
    m'.tos = U256.ofScalar (m.stateMem off) ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp + 1 := by
  simp [Prog.denote, envU64Body, Op.denote, Nat.not_le.2 hsp, Nat.not_lt.2 hg]

theorem pop_correct (cost : Nat) (m : Mach) (hsp : 1 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (popBody cost).denote m
    m'.tos = m.nos ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp - 1 := by
  simp [Prog.denote, popBody, Op.denote, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

/-! ## ADD / SUB (4-limb carry/borrow)

The limb-carry/borrow `denote` mirrors the `adds;adcs;adc` / `subs;sbcs;sbc`
asm exactly. The structural correctness (pushes `k.apply tos nos`, charges,
pops) is proved here; the deeper `U256.toNat (addChain a b) = (a.toNat +
b.toNat) % 2^256` value-correctness (multi-limb addition) is a focused
follow-up — these carry chains are standard and have not been bug sources. -/

def arithBody (k : ArithKind) (cost : Nat) : Prog :=
  [.underflow 2, .arith k, .spDec, .storeTos, .reloadNos, .exitGas cost]

theorem arith_correct (k : ArithKind) (m : Mach) (cost : Nat)
    (hsp : 2 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (arithBody k cost).denote m
    m'.tos = k.apply m.tos m.nos ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp - 1 := by
  simp [Prog.denote, arithBody, Op.denote, upd, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

/-! ## COPY family (CALLDATACOPY/CODECOPY/RETURNDATACOPY/MCOPY)

3-pop, gas = base + 3·⌈len/32⌉ + memexp(dst+len), then a state-aware C helper
writes memory. Emit byte-identical; denote coarse (sp-=3; gas/memory are host
effects). -/
def copyBody (helper : String) (cost : Nat) : Prog :=
  [.underflow 3, .copyGasCharge cost, .copyCbPop3 helper, .brCont]

/-- RETURNDATACOPY: the copy body behind the EIP-211 bound (CALLDATACOPY/CODECOPY
    zero-pad past the end; RETURNDATACOPY halts). -/
def returndatacopyBody (cost : Nat) : Prog :=
  [.underflow 3, .returndataBounds, .copyGasCharge cost, .copyCbPop3 "_eita_helper_returndatacopy", .brCont]

/-- MCOPY (#270): same shape as copyBody but the memexp covers BOTH the source
    and destination memory ranges (EELS `memexp(max(dst+len, src+len))`). -/
def mcopyBody (helper : String) (cost : Nat) : Prog :=
  [.underflow 3, .mcopyGasCharge cost, .copyCbPop3 helper, .brCont]

/-! ## KECCAK256

2-pop→1-push: gas = 30 + 6·⌈len/32⌉ + memexp(off+len), then a C helper hashes
memory[off..off+len] → result (popping len, replacing off with the 32-byte hash).
Emit byte-identical; denote coarse (sp-=1, tos:=hash; gas/memexp are host
effects, guaranteed by byte-identical emit). -/
def keccak256Body (cost : Nat) : Prog :=
  [.underflow 2, .keccakGasCharge cost, .keccakCbPop1, .storeTos, .reloadNos, .brCont]

/-! ## EXP (variable gas)

Same shape as a binary C-helper compute, but gas = cost + byteCost·⌈log256(e)⌉,
where `byteCost` is the per-byte exponent fee (10 Frontier, 50 from EIP-160).
ebytes is derived from the exponent's MSB via clz per limb. Emit byte-identical;
denote replaces TOS with the helper result, pops 1 (gas is a host effect). -/
def expBody (cost byteCost : Nat) : Prog :=
  [.underflow 2, .expGasCharge cost byteCost, .binHelper "_eita_helper_exp",
   .spDec, .storeTos, .reloadNos, .brCont]

/-! ## BLOBHASH (Cancun, EIP-4844)

Pop the index, push `blob_versioned_hashes[index]` or 0 when out of range (EELS
cancun/vm/instructions/environment.py `blob_hash`, `GAS_BLOBHASH = 3`): net pop 1
push 1, so TOS is replaced in place and sp is unchanged. The lookup is
`blobhashLookup` (`blobHashInstrs`); the theorems are in `Evm.CL.BlobEnv`. Until
2026-10-25 this body pushed 0 for every index (no blob state in the frame), which
mainnet rollup inboxes read as "no blob" from Cancun on. -/
def blobhashBody (cost : Nat) : Prog :=
  [.underflow 1, .blobhashLookup, .storeTos, .exitGas cost]

/-! ## EXTCODECOPY

4-pop (addr, dst, src, len): compute memexp(dst+len) gas up front (OOG cleanly
on oversized growth), then a host cb (ext_code_copy, slot #56) copies code into
memory and returns the access gas to charge. Emit byte-identical; denote coarse
(sp-=4; gas/memory are host effects) — so the cb's ARGUMENTS are checked at the
instruction level instead: `ARM64.Interp.handler_callback_args_defined`. -/
def extcodecopyBody : Prog :=
  [.underflow 4, .extcodecopyGasMem, .extcodecopyCb, .brCont]

/-! ## JUMP / JUMPI (control flow)

JUMP: pop dest, validate (in-bounds + code[dest]=JUMPDEST else _eita_invalid_jump),
set pc=dest, reload TOS/NOS, charge. JUMPI: same but gated on cond≠0; cond=0 falls
through (pc unchanged). Emit byte-identical; denote sets pc/ret (control flow is
the host guarantee). The reload (sub#1; ldp) is `dupLoad 1`. -/
def jumpBody (cost : Nat) : Prog :=
  [.underflow 1, .jumpValidate, .spDec, .dupLoad 1, .reloadNos, .exitGas cost]

def jumpiBody (cost : Nat) : Prog :=
  [.underflow 2, .jumpiCheck, .spDec2, .dupLoad 1, .reloadNos, .jumpiTailGas cost]

/-! ## TSTORE (transient storage; not journaled)

Static-guard, pop slot+val, charge the fixed Cancun 100 up front (so an OOG
frame never journals), then eita_ts_tstore writes through the tx-state. Emit
byte-identical; denote pops 2 (gas charged via chargeFixed). -/
def tstoreBody : Prog :=
  [.staticGuard, .underflow 2, .chargeFixed 100, .tstoreCb, .brCont]

/-! ## LOG-N (n = 0..4)

Static-guard, underflow (2+n), then gas = cost(375+375n) + 8·len + memexp(off+len),
bump the arena log_count, update mp, pop off+len+n topics, charge, then hand the
record (address, topics, memory[off..off+len)) to the host through vtable slot 9
(`cb->log`) when it is installed — the observation seam; a null slot is skipped so
log-less replays stay byte-identical. Denote pops 2+n (gas/log/memory are host
effects). -/
def logBody (n cost : Nat) : Prog :=
  [.staticGuard, .underflow (2 + n), .logEmit n cost]

/-! ## PUSH-N (n = 0..32)

Overflow-guard, shift old TOS→NOS, zero TOS, then (for n>0) read n code bytes
big-endian into TOS by wide loads (`pushWideInstrs`; bytes past code_size come
from the image's zero padding) and advance pc by n; push (sp+=1), store, charge.
Denote pushes the immediate (`pushAccum`) and advances pc. -/
def pushBody (n cost : Nat) : Prog :=
  [.ovfGuard, .tosToNos, .loadZeroTos] ++
  (if n > 0 then [Op.pushImm n] else []) ++
  [.spInc, .storeTos, .exitGas cost]

/-! ## SSTORE

Static-guard, underflow 2, optional EIP-1706 gas sentry (if gas ≤ sentry → OOG),
then cb->sstore returns the gas to charge; we also push a journal entry (type 0,
addr/slot/old_val) for revert tracking, pop slot+val, reload. Emit byte-identical;
denote pops 2 + models the sentry trap (gas/journal are host effects). -/
def sstoreBody (sentry : Nat) : Prog :=
  [.staticGuard, .underflow 2] ++
  (if sentry > 0 then [Op.sstoreSentry sentry] else []) ++
  [.sstoreCb, .reloadNos, .brCont]

/-! ## SELFDESTRUCT

Static-guard, undo trampoline pc-inc, charge base `cost`, cb->selfdestruct (returns
cold-access + new-account surcharge), halt, pop beneficiary, sync+return. Emit
byte-identical; denote halts + pops 1 (gas/world destruct are host effects). -/
def selfdestructBody (cost : Nat) : Prog :=
  [.staticGuard, .underflow 1, .pcDec, .chargeFixed cost, .selfdestructCb,
   .setHalted, .spDec, .jumpSyncRet]

/-! ## CALL family (CALL / CALLCODE / DELEGATECALL / STATICCALL)

Underflow (7 with value, else 6), memexp over max(in_range, out_range), build a
CallParams on the local frame, cb->call (host-recursive sub-frame), copy returndata
into memory[out_off..], pop args, push success, charge the sub-frame's gas_used.
Emit byte-identical; denote pops argsCount-1 and pushes success (gas/sub-frame/
returndata are host effects). -/
def callFamilyBody (name : String) (kind staticp : Nat) (withValue : Bool) : Prog :=
  [.underflow (if withValue then 7 else 6)] ++
  (if kind = 0 ∧ withValue then [.staticValueGuard] else []) ++
  [.callFamilyCore name kind staticp withValue]

/-! ## CREATE / CREATE2

Static-guard, underflow (3 / 4), build a CallParams (kind 4 / 5; value, init code
ptr, gas; CREATE2 adds salt), cb->create (host-recursive), push the created address
(or 0 on failure), pop 3/4 push 1, charge gas_used. Emit byte-identical; denote
pushes the result address and pops accordingly (host effects otherwise). -/
def createBody : Prog :=
  [.staticGuard, .underflow 3, .createCore]

def create2Body : Prog :=
  [.staticGuard, .underflow 4, .create2Core]

/-! ## #266 structural close — CREATE/CREATE2 init-range memexp

`createCore`/`create2Core` omitted the init-range memory-expansion gas (EELS
`calculate_gas_extend_memory` over `[offset, offset+length)`), undercharging
every CREATE that grew memory (a consensus-state bug — it shifts the sender
refund and coinbase fee, moving the state root). The fix routes through
`createMemExpandEmit`, which reuses the SAME `.memExpand` gadget the (verified)
copy/keccak ops use. Two checked guarantees pin it:

1. `memExpand_charges_eels`: the gadget charges EXACTLY the EELS expansion delta.
2. A build-time regression guard: the charge is PRESENT in the emit, so the
   omission is unrepresentable — deleting `createMemExpandEmit` fails the build.

(Full denotation modelling of the create/call memexp as structured Ops — so the
fork-equivalence proof itself catches the omission, not just a presence guard —
is the remaining #238-stage-2 decomposition. This is the scoped close.) -/

/-- EELS memory cost: `memCost w = 3·w + ⌊w²/512⌋`. -/
def memCost (w : Nat) : Nat := 3 * w + w * w / 512

/-- The `.memExpand` gadget (used by `createMemExpandEmit`) charges exactly the
    EELS memory-expansion delta into the `acc` gas accumulator. -/
theorem memExpand_charges_eels (m : Mach)
    (hcap  : ¬ m.memCap < m.scratch)
    (hgrow : ¬ (m.scratch + 31) / 32 ≤ m.memSize / 32) :
    (Op.denote .memExpand m).acc
      = m.acc + (memCost ((m.scratch + 31) / 32) - memCost (m.memSize / 32)) := by
  simp only [Op.denote, memCost, hcap, hgrow, if_false]

-- Regression guard: createCore/create2Core MUST emit the init-range memexp.
-- The `.Lcrin0_*` label is produced ONLY by createMemExpandEmit; removing the
-- #266 fix deletes it and fails this build-time check.
example : 1 < (createBody.emit.splitOn ".Lcrin0_create").length := by native_decide
example : 1 < (create2Body.emit.splitOn ".Lcrin0_create2").length := by native_decide

/-! ## RETURN / REVERT (conditional memexp + output capture + halt)

Emit byte-identical to the validated asm; denote sets halted (+ models the
conditional memexp gas). -/

def returnBody : Prog :=
  [.underflow 2, .pcDec, .memExpandIfLen "r", .setOutput, .setHalted, .spDec2, .jumpSyncRet]

def revertBody : Prog :=
  [.underflow 2, .pcDec, .memExpandIfLen "v", .setOutput, .setHalted, .setReverted, .spDec2, .jumpSyncRet]

theorem return_halts (m : Mach) : (returnBody.denote m).halted = true := by
  simp only [Prog.denote, returnBody, List.foldl, Op.denote]
  repeat' first | rfl | split | simp

/-! ## Memory ops (MLOAD / MSTORE / MSTORE8)

The bound checks (boundCheckHiTos, newEndTos), the memexp quadratic gas
(memExpand — `cost w = 3w + w²/512`, matching memExpandInto) and the OOG-checked
charge (chargeAcc) are modelled faithfully; the byte-level value read/write is
abstract (evmMem). The emit is byte-identical to the validated hand-written asm
(the behavioral guarantee). -/

def mloadBody (cost : Nat) : Prog :=
  [.underflow 1, .boundCheckHiTos, .newEndTos 32, .setAcc cost, .memExpand,
   .chargeAcc, .mloadTail, .storeTos, .brCont]

def mstoreBody (cost : Nat) : Prog :=
  [.underflow 2, .boundCheckHiTos, .newEndTos 32, .setAcc cost, .memExpand,
   .chargeAcc, .mstoreTail, .reloadNos, .brCont]

def mstore8Body (cost : Nat) : Prog :=
  [.underflow 2, .boundCheckHiTos, .newEndTos 1, .setAcc cost, .memExpand,
   .chargeAcc, .mstore8Tail, .reloadNos, .brCont]

/-- MLOAD, no-growth happy path (offset in-bounds, no memory expansion, gas ok):
    pushes the memory word and charges exactly `cost`. -/
theorem mload_correct (m : Mach) (cost : Nat)
    (hsp : 1 ≤ m.sp) (hhi : m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0)
    (hov : m.tos.l0 + 32 < 2^64) (hcap : m.tos.l0 + 32 ≤ m.memCap)
    (hgrow : (m.tos.l0 + 32 + 31) / 32 ≤ m.memSize / 32) (hg : cost ≤ m.gas) :
    let m' := (mloadBody cost).denote m
    m'.tos = m.evmMem m.tos.l0 ∧ m'.gas = m.gas - cost := by
  obtain ⟨h1, h2, h3⟩ := hhi
  simp [Prog.denote, mloadBody, Op.denote, h1, h2, h3, hgrow,
        Nat.not_lt.2 hsp, Nat.not_le.2 hov, Nat.not_lt.2 hcap, Nat.not_lt.2 hg]

/-! ## Host-callback handlers (SLOAD/TLOAD/BALANCE/SELFBALANCE/EXTCODESIZE/
       EXTCODEHASH/BLOCKHASH)

Each marshals args and invokes a host callback that returns the gas to charge
(cbGas) and writes a result (cbResult). The DSL captures the marshaling + the
cb boundary + the OOG-checked gas charge; the cb's value-semantics are the host
(CL vtable / tx-state). -/

def sloadBody : Prog :=
  [.underflow 1, .cbEnter 32, .loadCtxVia14 0, .argStateField 1 144,
   .argStackPtr 2 1, .argScratch 3, .cbSlot 0, .chargeGasX0,
   .loadScratchTos, .cbExit 32, .storeTos, .reloadNos, .brCont]

def tloadBody : Prog :=
  [.underflow 1, .chargeFixed 100, .cbEnter 32, .loadTxStateCtx 0,
   .argStateField 1 144, .argStackPtr 2 1, .argScratch 3, .cbDirect "_eita_ts_tload",
   .loadScratchTos, .cbExit 32, .storeTos, .reloadNos, .brCont]

def balanceBody : Prog :=
  [.underflow 1, .cbEnter 32, .loadCtx 0, .argStackPtr 1 1, .argScratch 2,
   .cbSlot 32, .chargeGasX0, .loadScratchTos, .cbExit 32, .storeTos, .reloadNos, .brCont]

def selfbalanceBody (cost : Nat) : Prog :=
  [.ovfGuard, .tosToNos, .cbEnter 32, .loadCtx 0, .argStateField 1 144, .argScratch 2,
   .cbSlot 32, .loadScratchTos, .cbExit 32, .spInc, .storeTos, .reloadNos, .exitGas cost]

def extcodesizeBody : Prog :=
  [.underflow 1, .cbEnter 16, .loadCtx 0, .argStackPtr 1 1, .argScratch 2,
   .cbSlot 40, .chargeGasX0Via14, .loadScratchU64Tos, .cbExit 16, .storeTos, .reloadNos, .brCont]

def extcodehashBody : Prog :=
  [.underflow 1, .cbEnter 32, .loadCtx 0, .argStackPtr 1 1, .argScratch 2,
   .cbSlot 48, .chargeGasX0, .loadScratchTos, .cbExit 32, .storeTos, .reloadNos, .brCont]

def blockhashBody (cost : Nat) : Prog :=
  [.underflow 1, .cbEnter 32, .loadCtx 0, .argStackPtr 1 1, .argScratch 2,
   .cbSlot 64, .loadScratchTos, .cbExit 32, .storeTos, .reloadNos, .exitGas cost]

theorem sload_correct (m : Mach) (hsp : 1 ≤ m.sp) (hg : m.cbGas ≤ m.gas) :
    let m' := sloadBody.denote m
    m'.tos = m.cbResult ∧ m'.gas = m.gas - m.cbGas := by
  simp [Prog.denote, sloadBody, Op.denote, upd, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

theorem balance_correct (m : Mach) (hsp : 1 ≤ m.sp) (hg : m.cbGas ≤ m.gas) :
    let m' := balanceBody.denote m
    m'.tos = m.cbResult ∧ m'.gas = m.gas - m.cbGas := by
  simp [Prog.denote, balanceBody, Op.denote, upd, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

theorem extcodehash_correct (m : Mach) (hsp : 1 ≤ m.sp) (hg : m.cbGas ≤ m.gas) :
    let m' := extcodehashBody.denote m
    m'.tos = m.cbResult ∧ m'.gas = m.gas - m.cbGas := by
  simp [Prog.denote, extcodehashBody, Op.denote, upd, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

theorem extcodesize_correct (m : Mach) (hsp : 1 ≤ m.sp) (hg : m.cbGas ≤ m.gas) :
    let m' := extcodesizeBody.denote m
    m'.tos = m.cbResult ∧ m'.gas = m.gas - m.cbGas := by
  simp [Prog.denote, extcodesizeBody, Op.denote, upd, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

theorem tload_correct (m : Mach) (hsp : 1 ≤ m.sp) (hg : 100 ≤ m.gas) :
    let m' := tloadBody.denote m
    m'.tos = m.cbResult ∧ m'.gas = m.gas - 100 := by
  simp [Prog.denote, tloadBody, Op.denote, upd, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

theorem selfbalance_correct (m : Mach) (cost : Nat) (hsp : m.sp < 1024) (hg : cost ≤ m.gas) :
    let m' := (selfbalanceBody cost).denote m
    m'.tos = m.cbResult ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp + 1 := by
  simp [Prog.denote, selfbalanceBody, Op.denote, upd, Nat.not_le.2 hsp, Nat.not_lt.2 hg]

theorem blockhash_correct (m : Mach) (cost : Nat) (hsp : 1 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (blockhashBody cost).denote m
    m'.tos = m.cbResult ∧ m'.gas = m.gas - cost := by
  simp [Prog.denote, blockhashBody, Op.denote, upd, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

/-- CALLDATALOAD: helper(result, &state, &off) → result replaces TOS. -/
def calldataloadBody (cost : Nat) : Prog :=
  [.underflow 1, .cbEnter 32, .argScratch 0, .argStateBase 1, .argStackPtr 2 1,
   .cbDirect "_eita_helper_calldataload", .loadScratchTos, .cbExit 32,
   .storeTos, .reloadNos, .exitGas cost]

theorem calldataload_correct (m : Mach) (cost : Nat) (hsp : 1 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (calldataloadBody cost).denote m
    m'.tos = m.cbResult ∧ m'.gas = m.gas - cost := by
  simp [Prog.denote, calldataloadBody, Op.denote, upd, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

/-! ## Pure-compute C helpers (MUL/DIV/…/BYTE/SIGNEXTEND, ADDMOD/MULMOD)

The handler frames a call to a verified C helper; the DSL captures the call
boundary (operands staged, result loaded, stack popped) and the result enters
as the uninterpreted `helperFn`/`helperFn3`. -/

def binComputeBody (helper : String) (cost : Nat) : Prog :=
  [.underflow 2, .binHelper helper, .spDec, .storeTos, .reloadNos, .exitGas cost]

def ternaryComputeBody (helper : String) (cost : Nat) : Prog :=
  [.underflow 3, .ternaryHelper helper, .spDec2, .storeTos, .reloadNos, .exitGas cost]

theorem binCompute_correct (helper : String) (m : Mach) (cost : Nat)
    (hsp : 2 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (binComputeBody helper cost).denote m
    m'.tos = m.helperFn helper m.tos m.nos ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp - 1 := by
  simp [Prog.denote, binComputeBody, Op.denote, upd, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

theorem ternaryCompute_correct (helper : String) (m : Mach) (cost : Nat)
    (hsp : 3 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (ternaryComputeBody helper cost).denote m
    m'.tos = m.helperFn3 helper m.tos m.nos (m.mem (m.sp - 3))
    ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp - 2 := by
  simp [Prog.denote, ternaryComputeBody, Op.denote, upd, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

/-! ## Comparisons LT / GT / SLT / SGT (the chained-sbcs family)

`lt` = cmpBody false .lo, `gt` = cmpBody true .lo, `slt` = cmpBody false .lt,
`sgt` = cmpBody true .lt. The `denote` gives the value-level comparison; the
flag-chain↔result derivation (C = unsigned-ge, N≠V = signed-lt) is the deferred
verification depth (like add/sub's toNat). What IS captured here is the reason
only C/N-V conditions are used (`chained_z_unreliable`). -/

def cmpBody (swapped : Bool) (cond : CmpCond) (cost : Nat) : Prog :=
  [.underflow 2, .cmpChain swapped cond, .spDec, .storeTos, .reloadNos, .exitGas cost]

theorem cmp_correct (swapped : Bool) (cond : CmpCond) (m : Mach) (cost : Nat)
    (hsp : 2 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (cmpBody swapped cond cost).denote m
    m'.tos = U256.ofScalar (cmpResult swapped cond m.tos m.nos)
    ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp - 1 := by
  simp [Prog.denote, cmpBody, Op.denote, upd, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

/-- **Why EQ/GT/SGT don't read Z after the chain.** The Z flag after a chained
    `subs;sbcs;sbcs;sbcs` reflects ONLY the final (high) limb, not the full
    256-bit equality: there is `a ≠ b` whose high subtraction limb is 0, so
    `cset eq` would wrongly report equality. (Killed EQ/GT/SGT historically.) -/
theorem chained_z_unreliable :
    ∃ a b : U256, a ≠ b ∧ (U256.subChain a b).l3 = 0 := by
  exact ⟨⟨5,0,0,0⟩, ⟨3,0,0,0⟩, by decide, by native_decide⟩

/-! ## EQ / ISZERO / NOT (no subs-chain — value-level)

These sidestep the chained-sbcs flag trap (EQ via XOR-fold, ISZERO via OR-fold,
NOT via per-limb MVN), so the denote is value-level. -/

def eqBody (cost : Nat) : Prog :=
  [.underflow 2, .eqReduce, .spDec, .storeTos, .reloadNos, .exitGas cost]

def iszeroBody (cost : Nat) : Prog :=
  [.underflow 1, .iszeroReduce, .storeTos, .exitGas cost]

def notBody (cost : Nat) : Prog :=
  [.underflow 1, .notLimbs, .storeTos, .exitGas cost]

/-- CLZ (0x1e, EIP-7939): pop x, push 256 − bit_length(x). Evm.Osaka.Spec.ClzStep. -/
def clzBody (cost : Nat) : Prog :=
  [.underflow 1, .clzReduce, .storeTos, .exitGas cost]

theorem eq_correct (m : Mach) (cost : Nat) (hsp : 2 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (eqBody cost).denote m
    m'.tos = U256.ofScalar (if m.tos = m.nos then 1 else 0)
    ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp - 1 := by
  simp [Prog.denote, eqBody, Op.denote, upd, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

theorem iszero_correct (m : Mach) (cost : Nat) (hsp : 1 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (iszeroBody cost).denote m
    m'.tos = U256.ofScalar (if m.tos = ⟨0,0,0,0⟩ then 1 else 0) ∧ m'.gas = m.gas - cost := by
  simp [Prog.denote, iszeroBody, Op.denote, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

theorem clz_correct (m : Mach) (cost : Nat) (hsp : 1 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (clzBody cost).denote m
    m'.tos = U256.ofScalar (clzLimbs m.tos) ∧ m'.gas = m.gas - cost := by
  simp [Prog.denote, clzBody, Op.denote, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

/-- TRUST BRIDGE (open): the limb-wise count equals the spec's `256 − bit_length`
    (Evm.Osaka.Spec.ClzStep / `clzU256`) for every in-range word. Checked on the
    boundary cases below; the general statement needs `Nat.log2` of a limb sum. -/
theorem clzLimbs_eq_clzNat (a : U256) (h0 : a.l0 < 2^64) (h1 : a.l1 < 2^64)
    (h2 : a.l2 < 2^64) (h3 : a.l3 < 2^64) : clzLimbs a = clzNat a.toNat := by
  sorry

example : clzLimbs ⟨0, 0, 0, 0⟩ = 256 := by unfold clzLimbs clz64; simp
example : clzLimbs ⟨1, 0, 0, 0⟩ = 255 := by unfold clzLimbs clz64; native_decide
example : clzLimbs ⟨0, 1, 0, 0⟩ = 191 := by unfold clzLimbs clz64; native_decide
example : clzLimbs ⟨0, 0, 0, 2^63⟩ = 0 := by unfold clzLimbs clz64; native_decide
example : clzNat 0 = 256 := by unfold clzNat; simp
example : clzNat 1 = 255 := by unfold clzNat; native_decide

theorem not_correct (m : Mach) (cost : Nat) (hsp : 1 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (notBody cost).denote m
    m'.tos = ⟨2^64-1 - m.tos.l0, 2^64-1 - m.tos.l1, 2^64-1 - m.tos.l2, 2^64-1 - m.tos.l3⟩
    ∧ m'.gas = m.gas - cost := by
  simp [Prog.denote, notBody, Op.denote, Nat.not_lt.2 hsp, Nat.not_lt.2 hg]

/-! ## Control (STOP / JUMPDEST / INVALID) + DUP / SWAP -/

def jumpdestBody (cost : Nat) : Prog := [.exitGas cost]
def stopBody : Prog := [.pcDec, .setHalted, .jumpSyncRet]
def invalidBody : Prog := [.branchOOG]

/-- DUP-n: copy stack[sp-n] to a new top (n 1-indexed; DUP1 = top). -/
def dupBody (n cost : Nat) : Prog :=
  [.ovfGuard, .underflow n, .tosToNos, .dupLoad n, .spInc, .storeTos, .exitGas cost]

/-- SWAP-n: exchange top with stack[sp-1-n]. n=1 also reloads NOS regs. -/
def swapBody (n cost : Nat) : Prog :=
  [.underflow (n + 1), .swapPartner n, .storeTos]
    ++ (if n = 1 then [.reloadNos] else []) ++ [.exitGas cost]

theorem jumpdest_correct (m : Mach) (cost : Nat) (hg : cost ≤ m.gas) :
    ((jumpdestBody cost).denote m).gas = m.gas - cost := by
  simp [Prog.denote, jumpdestBody, Op.denote, Nat.not_lt.2 hg]

/-- STOP halts the frame and returns (sets EvmState.halted, exits via sync). -/
theorem stop_correct (m : Mach) :
    let m' := stopBody.denote m
    m'.halted = true ∧ m'.ret = true ∧ m'.pcReg = m.pcReg - 1 := by
  simp [Prog.denote, stopBody, Op.denote]

theorem invalid_oog (m : Mach) : (invalidBody.denote m).oog = true := by
  simp [Prog.denote, invalidBody, Op.denote]

theorem dup_correct (n cost : Nat) (m : Mach)
    (ho : m.sp < 1024) (hu : n ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (dupBody n cost).denote m
    m'.tos = m.mem (m.sp - n) ∧ m'.gas = m.gas - cost ∧ m'.sp = m.sp + 1 := by
  simp [Prog.denote, dupBody, Op.denote, Nat.not_le.2 ho,
        Nat.not_lt.2 hu, Nat.not_lt.2 hg]

/-- SWAP-n puts the old stack[sp-1-n] on top and writes the old top there. -/
theorem swap_correct (n cost : Nat) (m : Mach)
    (hu : n + 1 ≤ m.sp) (hg : cost ≤ m.gas) :
    let m' := (swapBody n cost).denote m
    m'.tos = m.mem (m.sp - (n + 1)) ∧ m'.gas = m.gas - cost := by
  by_cases h1 : n = 1
  · subst h1
    simp [Prog.denote, swapBody, Op.denote, upd, Nat.not_lt.2 hu, Nat.not_lt.2 hg]
  · simp [Prog.denote, swapBody, Op.denote, h1, Nat.not_lt.2 hu, Nat.not_lt.2 hg]

/-! ## OOG / underflow safety by construction -/

theorem exitGas_traps (m : Mach) (c : Nat) (h : m.gas < c) :
    ((Op.exitGas c).denote m).oog = true := by simp [Op.denote, h]

theorem chargeGasPush_traps (m : Mach) (c : Nat) (h : m.gas < c) :
    ((Op.chargeGasPushTos c).denote m).oog = true := by simp [Op.denote, h]

theorem underflow_traps (m : Mach) (n : Nat) (h : m.sp < n) :
    ((Op.underflow n).denote m).trap = true := by simp [Op.denote, h]

end Evm.CL.AsmCore
