# IR.Op design — enum + metadata contract

> **Status: historical** (written 2026-06). Accurate as of then; the current system is described in `docs/replay-architecture.md` and the code.

> The IR is the data structure
> both the interp tier and the JIT tier consume. This document
> pins down its shape *before* code lands, because it's the
> contract everything depends on.

Date: 2026-06-10. Status: **draft, awaiting approval**.

## Goals

1. **Single per-op atom that both tiers consume.** Interp emits one
   handler per `IR.Op`. JIT walks a list of `IR.Op` and emits one
   native function per chunk. Same input shape, two output shapes.

2. **Per-op soundness theorem fits.** For each `IR.Op.X`, prove
   `interp X evm = Fork.Instructions.X evm` and (for JIT) prove
   the emitted assembly behaves equivalently.

3. **Fork-aware without proliferating types.** One `IR.Op` enum
   that grows monotonically with new forks (PUSH0 in Shanghai,
   BLOBHASH in Cancun, …). Per-fork variation lives in *metadata*,
   not in the enum itself.

4. **Self-describing for the JIT.** Each op declares its gas
   schedule, stack effect, and host-data access shape. The JIT
   never re-derives this from the op's name; if the JIT needs to
   know "does this op need a callback", the metadata says so.

## Non-goals

- A semantic-bearing IR. The IR's *semantics* is "execute via
  the corresponding `Fork.Instructions.X` Effect handler." There
  is no separate "what does `IR.Op.add` mean" definition.
- Reuse of `IR.Op` across forks for storage layout. We keep one
  enum for the whole project; fork-incompatibility is enforced
  by `metadata fork op = none`, not by separate types.
- Hand-optimized representations (bitfields, packed enums). Lean
  builds use plain inductive types. The CL/asm consumer reads
  through the metadata API; representation can shift later.

## The enum

Grouped by EELS organization. Each variant carries its immediate
operand if any (`push n imm`, `dup n`, `swap n`, `log n`).

```lean
inductive IR.Op where
  -- 0x00..0x0b: arithmetic
  | stop | add | mul | sub | div | sdiv | mod | smod
  | addmod | mulmod | exp | signextend
  -- 0x10..0x1d: comparison & bitwise
  | lt | gt | slt | sgt | eq | iszero
  | and_ | or_ | xor_ | not_ | byte | shl | shr | sar
  -- 0x20: keccak
  | keccak256
  -- 0x30..0x3f: environment
  | address | balance | origin | caller | callvalue
  | calldataload | calldatasize | calldatacopy
  | codesize | codecopy | gasprice
  | extcodesize | extcodecopy | returndatasize | returndatacopy
  | extcodehash
  -- 0x40..0x4a: block context
  | blockhash | coinbase | timestamp | number | prevrandao
  | gaslimit | chainid | selfbalance | basefee
  | blobhash | blobbasefee                        -- Cancun+
  -- 0x50..0x5f: stack / memory / storage / flow / push0
  | pop | mload | mstore | mstore8
  | sload | sstore
  | jump | jumpi | pc | msize | gas | jumpdest
  | tload | tstore | mcopy                        -- Cancun+
  | push0                                         -- Shanghai+
  -- 0x60..0x7f: PUSH1..PUSH32 (immediate value carried)
  | push  (n : Nat) (imm : Evm.U256)              -- n ∈ {1..32}
  -- 0x80..0x8f: DUP1..DUP16
  | dup   (n : Nat)                               -- n ∈ {1..16}
  -- 0x90..0x9f: SWAP1..SWAP16
  | swap  (n : Nat)                               -- n ∈ {1..16}
  -- 0xa0..0xa4: LOG0..LOG4
  | log   (n : Nat)                               -- n ∈ {0..4}
  -- 0xf0..0xff: system
  | create | call | callcode | return_ | delegatecall
  | create2                                       -- Constantinople+
  | staticcall                                    -- Byzantium+
  | revert                                        -- Byzantium+
  | invalid | selfdestruct
  -- Prague/Osaka/Amsterdam additions slot in as those forks land:
  | clz                                            -- Osaka
  -- (placeholders for future fork opcodes here)
  deriving Inhabited, Repr, DecidableEq
```

Approximately 100 distinct variants. The current 12-op enum becomes
a subset.

### Why not split PUSH into PUSH0..PUSH32?

Compactness, and the immediate is the only thing that distinguishes
them. The handler emission for PUSH-N is parametric in `n`.

### Why parametrize DUP/SWAP/LOG rather than expand?

Same reason — `n` is the only difference, and handlers can be
parametric in it. Lean enumeration with explicit `n` lets us
state `metadata` as a function over `n`.

## Metadata

```lean
structure OpMetadata where
  /-- Gas charged before the op runs, independent of runtime state.
      Per-fork — BALANCE went 20 (Frontier) → 700 (Berlin) → 2600
      (Berlin cold) and similar. -/
  staticCost   : Nat
  /-- Gas the op may charge in addition to `staticCost`, as a
      function of runtime state. -/
  dynamicGas   : DynamicGasShape
  /-- What the op pops/pushes on the operand stack. Compile-time
      known. JIT uses this for register allocation. -/
  stackEffect  : StackEffect
  /-- What memory range the op accesses, if any. Offsets may be
      symbolic (popped from stack). JIT uses this for memory
      bounds-check hoisting. -/
  memoryAccess : MemoryAccess
  /-- What host-state callback this op invokes, if any. JIT keeps
      its EvmState cache coherent around these. -/
  worldAccess  : WorldAccess
  deriving Repr

structure StackEffect where
  popCount  : Nat
  pushCount : Nat
  deriving Repr, DecidableEq

inductive DynamicGasShape where
  | none_                       -- staticCost is the whole story
  | memExpand                   -- + memory-expansion cost; off/len from stack
  | coldAccount                 -- + 2500 if !accessed_addrs.contains(target)
  | coldStorage                 -- + 2100 if !accessed_slots.contains((addr, slot))
  | sstoreEip2200               -- full SSTORE matrix per EIP-2200
  | keccakPerWord               -- + 6 per ceil((stack-popped-len)/32)
  | expPerByte                  -- + 50 per byte of exponent magnitude
  | logPerByte                  -- + 8 per byte of data + 375 per topic
  | copyPerWord                 -- + 3 per ceil(len/32) + memExpand
  | callForward                 -- EIP-150 cap + 9000 if value + 25000 if new account
  | createBase                  -- 32000 + EIP-3860 init-code surcharge
  | selfdestructFee             -- 5000 base + 25000 if beneficiary new
  | modexpComplexity            -- EIP-2565 formula
  deriving Repr

inductive MemoryAccess where
  | none_
  | readWord    (offSrc  : StackSrc)
  | writeWord   (offSrc  : StackSrc)
  | writeByte   (offSrc  : StackSrc)
  | readRange   (offSrc  : StackSrc) (lenSrc : StackSrc)
  | writeRange  (offSrc  : StackSrc) (lenSrc : StackSrc)
  | copyRange   (dstSrc  : StackSrc) (srcSrc : StackSrc) (lenSrc : StackSrc)
  deriving Repr

/-- `StackSrc` references a value on the stack by position from top
    (0 = top, 1 = second from top, …). Lets the JIT trace memory
    args back through the chunk's symbolic stack. -/
abbrev StackSrc := Nat

inductive WorldAccess where
  | none_
  | sloadSlot                    -- needs (addr, slot)
  | sstoreSlot                   -- needs (addr, slot, value)
  | tloadSlot                    -- transient, per-tx
  | tstoreSlot
  | balanceOf                    -- needs addr
  | codeSizeOf
  | codeHashOf
  | codeCopyOf
  | blockHashOf                  -- needs block number
  | logEmit  (n : Nat)
  | callSub                      -- CALL/CALLCODE/DELEGATECALL/STATICCALL
  | createSub                    -- CREATE/CREATE2
  | selfdestructTo
  deriving Repr
```

### Per-fork metadata lookup

```lean
def IR.Op.metadata (fork : Fork) (op : IR.Op) : Option OpMetadata
```

Returns `none` if the op isn't supported on that fork (BLOBHASH on
Istanbul, PUSH0 on Berlin, …). The compiler refuses to emit such
ops; the interpreter treats them as `INVALID`.

For the common case (op exists in fork), the metadata is built from
a per-fork table. We'll generate this from a single source-of-truth
spreadsheet (Lean term or external file — TBD).

## Terminators — first-class with their own soundness obligations

Terminators carry as much semantic weight as opcodes. CALL alone
has: EIP-150 63/64 forwarding cap, value-fee (9000), stipend
(2300), depth check (1024), value transfer + revert rollback,
EIP-2929 cold/warm + 2500 surcharge, EIP-7 new-account fee
(25000), sub-frame state setup (gas, staticp propagation, code
lookup), and result handling (gas refund, output copy, success
flag push). Every one of those is a place CL hand-coded
`cb_call` got wrong in the previous push.

Treat terminators as a *peer* of opcodes, not as opcode siblings.
Per-terminator metadata, per-terminator soundness theorem against
the corresponding Effect handler, per-terminator audit fixtures.

### The enum

```lean
inductive IR.Terminator where
  -- Frame-ending (no sub-frame; the frame just ends)
  | stop                          -- 0x00
  | ret                           -- 0xf3
  | revert                        -- 0xfd  (Byzantium+)
  | invalid                       -- 0xfe; also fallthrough trap
  | selfdestruct                  -- 0xff  (EIP-6780 same-tx-created interacts)
  -- Frame-yielding (trampoline must build a sub-frame, run it, resume)
  | call    (kind : CallKind)     -- CALL / CALLCODE / DELEGATECALL / STATICCALL
  | create  (kind : CreateKind)   -- CREATE / CREATE2
  -- Control flow within the program (no yield, no host call)
  | fallthrough (next : Nat)
  | jump        (dest : Nat)      -- compile-time-constant target
  | jumpDynamic                   -- runtime-resolved via JUMPDEST table
  | jumpi       (dest : Nat)
  | jumpiDynamic
  | endOfCode                     -- implicit STOP past end of code

inductive CallKind   where | call | callcode | delegatecall | staticcall
inductive CreateKind where | create | create2
```

Static vs. dynamic JUMP/JUMPI is the classic basic-block split:
- If the JUMP destination is from a recently-PUSHed constant on
  the stack (compiler can constant-fold), terminator is `jump dest`.
- Otherwise `jumpDynamic` — runtime dispatch through the JUMPDEST
  table (cost: one indirect branch).

### Terminator metadata

Same shape as `OpMetadata` but with trampoline-specific extras:

```lean
structure TerminatorMetadata where
  /-- Gas charged at the terminator itself, independent of sub-frame.
      For CALL: cold/warm access cost + value-fee. For CREATE: 32000
      + EIP-3860 init-code surcharge. -/
  staticCost      : Nat
  /-- Gas math that depends on runtime state. -/
  dynamicGas      : DynamicGasShape
  /-- What the terminator pops from the parent's stack to construct
      its sub-frame (CALL pops 7, STATICCALL pops 6, etc.). -/
  popCount        : Nat
  /-- What it pushes onto the parent's stack on RESUMPTION, after the
      sub-frame returns. 0 for non-yielding terminators; 1 (success
      flag) for CALL family; 1 (deployed address or 0) for CREATE. -/
  pushOnResume    : Nat
  /-- For yielding terminators, the metadata of the sub-frame setup:
      what gas math runs, what state mutates, what gets rolled back
      on REVERT. -/
  trampoline      : Option TrampolineSpec
  deriving Repr

inductive TrampolineSpec where
  | callTrampoline    (kind : CallKind)
  | createTrampoline  (kind : CreateKind)
  | selfdestructTrampoline
  deriving Repr
```

### Trampoline semantics — separate, verified module

Trampoline math is its own file, `Evm/IR/Trampoline.lean`, with
one function per `TrampolineSpec` variant that mirrors the
corresponding Effect handler:

```lean
namespace Evm.IR.Trampoline

/-- Spec of the CALL trampoline: builds a sub-frame, runs it via
    the supplied `runSubFrame` callback, processes the result.
    Pure modulo the callback. Proven equivalent to
    `Fork.Instructions.call` (per fork). -/
def callTrampoline (fork : Fork) (kind : CallKind)
    (parent : Evm) (runSubFrame : Evm → Evm) : Evm := ...

/-- Same shape for CREATE. -/
def createTrampoline ...

/-- Same shape for SELFDESTRUCT (no sub-frame, but balance transfer
    + EIP-6780 same-tx-created check needs verified semantics). -/
def selfdestructTrampoline ...

end Evm.IR.Trampoline
```

### Per-terminator soundness theorem shape

Same template as per-op:

```lean
theorem call_terminator_sound (fork : Fork) (kind : CallKind)
    (parent parent' : Evm) (runSubFrame : Evm → Evm)
    (hSub : ∀ sub sub', runSubFrame sub = sub' →
            Effect.runFrame sub = .halt sub' _) :
    Trampoline.callTrampoline fork kind parent runSubFrame = parent' →
    Fork.Instructions.call kind parent = .ok parent'
```

The `hSub` hypothesis is the recursion: sub-frame execution refines
its own Effect handler. With sub-frame correctness assumed, the
trampoline's wrapper math is verified.

This is *exactly* the obligation `cb_call` was discharging by
hand in `src/evm/`. Once verified in Lean, the
ARM64.Interp/JIT emitters generate the trampoline's machine
code from the verified spec instead of hand-encoding it.

### Where trampoline lives in the JIT story

Trampoline logic is *structural* — same shape across all CALL
variants, parametric in `kind`. The JIT emits one trampoline
template per `CallKind`/`CreateKind`/`selfdestruct`, parameterized
by the parent chunk's symbolic stack layout. The Interp tier
emits a single trampoline runtime function called by the
relevant terminator handlers.

Either way the *content* is the verified Trampoline.lean
function. No hand-encoded "9000 if value > 0" constants in the
emitter.

## Program

```lean
structure IR.Program where
  /-- Entry pc; conventionally 0 for top-level code. -/
  entry      : Nat
  /-- Chunks indexed by start-pc. -/
  chunks     : Std.HashMap Nat Chunk
  /-- The set of valid JUMPDEST locations in the original bytecode.
      Used at runtime to validate dynamic JUMPs. -/
  jumpdests  : Std.HashSet Nat
  /-- The fork this program was compiled for. Embedded so the
      runtime knows which metadata table to use for dynamic gas. -/
  fork       : Fork
```

## Compatibility with the current 12-op IR

The existing `IR.Types.Op` is a subset. Migration:

1. Extend the enum in this design pass (new file, perhaps
   `IR/Types/OpV2.lean`, then rename once stable).
2. Existing `Compile.lean` keeps producing the small subset; we
   widen its output as opcodes get verified.
3. Existing `Execute.lean` keeps interpreting; we widen its dispatch.
4. The 76 soundness theorems in `Extract.lean` get rewritten against
   `IR.Op` in Phase 2 — same content, different LHS/RHS.

No big-bang flag day. Each opcode crosses from "Form-and-MacroSpec"
to "IR.Op + per-fork metadata + Effect-handler-target soundness"
independently.

## Open questions for review

1. **Fork-indexed enum or fork-indexed metadata?** Currently
   proposing latter (single `IR.Op` enum, `metadata fork op`
   table). The alternative is `Frontier.IR.Op` vs `Cancun.IR.Op`,
   which makes the compiler per-fork-typed but means moving opcodes
   between fork-types when they get added. I think single-enum +
   metadata-table is cleaner. **Confirm?**

2. **PUSH0..PUSH32 as `push n imm` or `pushN imm` with `pushN`
   per width?** Parametric `push n imm` is more compact and the
   handler factors over `n`. Counter: hand-written audit fixtures
   might prefer the explicit variants. Proposing parametric.

3. **DynamicGasShape inhabitants — finite enum or open-ended
   record?** Listed shapes cover all current EVM opcodes. Future
   fork additions (KZG, BLS12-381, …) would extend. Inductive enum
   keeps each shape's signature in one place; record/struct would
   give a uniform `gasFn : EvmState → Stack → Nat` but lose the
   structural info JIT uses. Proposing enum.

4. **Where do precompile gas formulas live?** Precompiles are
   reached via CALL, so they're sub-frame work. Their gas
   schedules are properties of the *target address*, not the
   CALL op. Probably belongs in a separate `Precompile.Metadata`
   table indexed by precompile address × fork. **Defer to Phase 6?**

5. **MemoryAccess `StackSrc` semantics.** Defined as "popped from
   stack at position from top." After op runs, those slots are gone.
   For symbolic analysis, the JIT wants to see "MLOAD's offset is
   stack[0] at op entry." Is this clearer named `stackArg`? **Bike
   shed.**

6. **Terminators for CALL/CREATE.** Listed as `Terminator.call`,
   `Terminator.create`. The IR.Op enum also lists them. Should
   they appear only as terminators? Currently EVM models CALL as
   an op that returns a value (success flag); IR could model the
   whole-frame-yield separately from "push success flag at parent
   resume." Probably terminator-only is right, and the parent's
   resumption is part of the parent chunk's compiled body. **Confirm.**

## Sequence after approval

- (Phase 1, **today**): land the IR.Op enum + IR.Terminator enum +
  metadata types in `Evm/IR/Types.lean` (or a new file). Stub
  `Evm/IR/Trampoline.lean` with the spec function signatures.
  No theorems yet, no metadata table populated yet beyond a few
  opcodes.
- (Phase 2a): per-op soundness theorems against Effect handlers,
  porting content from Extract.lean. ~140 opcodes.
- (Phase 2b): per-terminator soundness theorems against Effect
  handlers. CALL/CREATE/SELFDESTRUCT each get their own
  trampoline-spec proof; STOP/RETURN/REVERT/INVALID/JUMP/JUMPI
  are simpler. **Equal weight to Phase 2a — the trampoline math
  is where the 25% GST failure surface lived.**
- (Phase 3): chunk-level soundness — IR.execute on a chunk
  equals Effect.runFrame on the chunk's bytecode. Depends on
  both 2a and 2b.
- (Phase 4): multi-chunk pipeline + JUMPDEST validation.
- (Phase 5): ARM64.Interp emit consumes IR.Op + IR.Terminator
  metadata; trampoline machine code derives from Trampoline.lean.
- (Phase 6): ARM64.JIT per-chunk emit, including JIT-shaped
  trampoline call sequences.
