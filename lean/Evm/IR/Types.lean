/-
  Evm.IR.Types — the shared IR consumed by both the interpreter tier
  (ARM64 threaded dispatch handlers) and the JIT tier (per-chunk native
  emit). Designed per docs/ir-op-design.md.

  This is a DATA STRUCTURE for compilation, not a separate semantic
  layer. Each `IR.Op` and `IR.Terminator` variant corresponds to one
  or a small group of EVM opcodes; its *semantics* is defined by the
  matching `Fork.Instructions.X` Effect handler (Phase 2 will prove
  the equivalence).

  Both tiers consume:
    - the IR.Op / IR.Terminator enums (this file)
    - the per-fork metadata table (this file, populated in Phase 2)
    - the per-fork Effect handlers (Evm/<Fork>/Vm/Instructions/*.lean,
      untouched)

  The trampoline (CALL/CREATE/SELFDESTRUCT control flow) is a peer of
  per-op semantics — its specs live in `Evm/IR/Trampoline.lean`. -/

import Evm.BaseTypes
import Evm.Forks

namespace Evm.IR

/-! ## Stack effect

    Compile-time-known stack arity. JIT uses this for register
    allocation across a chunk. -/

structure StackEffect where
  popCount  : Nat
  pushCount : Nat
  deriving Repr, DecidableEq, Inhabited

/-! ## Stack-position references

    `StackSrc n` references the value at position `n` from the top of
    the operand stack *at the moment the op runs* (before any pops).
    Used to declare runtime data dependencies (e.g. "MLOAD's offset is
    StackSrc 0 — the current top of stack"). -/

abbrev StackSrc := Nat

/-! ## Dynamic gas shapes

    Each op declares HOW its runtime gas depends on runtime state.
    The JIT branches on this to decide what to compute at chunk-head
    vs. at op-site. Interp tier ignores it (charges per-op as needed). -/

inductive DynamicGasShape where
  | none_
  | memExpand                   -- + memory-expansion cost; off/len from stack
  | coldAccount                 -- + 2500 if !accessed_addrs.contains(target)
  | coldStorage                 -- + 2100 if !accessed_slots.contains((addr, slot))
  | sstoreEip2200               -- full SSTORE matrix per EIP-2200
  | keccakPerWord               -- + 6 per ceil(stack-popped-len/32) + memExpand
  | expPerByte                  -- + per byte of exponent magnitude (10 pre-SpuriousDragon, 50 after)
  | logPerByte                  -- + 8 per byte of data + memExpand (375 base + 375/topic is staticCost)
  | copyPerWord                 -- + 3 per ceil(len/32) + memExpand
  | coldAccountPlusCopy         -- EXTCODECOPY: coldAccount surcharge AND copyPerWord
  | callForward                 -- EIP-150 cap + value-fee + new-account fee
  | createBase                  -- 32000 + EIP-3860 init-code surcharge + memExpand
  | selfdestructFee             -- + 25000 if beneficiary new (+ cold 2600 Berlin+); 5000 base is staticCost
  | modexpComplexity            -- EIP-2565 formula
  deriving Repr, DecidableEq, Inhabited

/-! ## Memory access shapes

    Declares what memory range an op touches and from where the
    offset/length come. JIT uses this for bounds-check hoisting. -/

inductive MemoryAccess where
  | none_
  | readWord    (offSrc  : StackSrc)
  | writeWord   (offSrc  : StackSrc)
  | writeByte   (offSrc  : StackSrc)
  | readRange   (offSrc lenSrc : StackSrc)
  | writeRange  (offSrc lenSrc : StackSrc)
  | copyRange   (dstSrc srcSrc lenSrc : StackSrc)
  deriving Repr, DecidableEq, Inhabited

/-! ## World-state access shapes

    Declares what host callback an op invokes, if any. After Phase 3
    (lift transient state into EvmState), most of these stay as host
    callbacks because storage is host-owned. -/

inductive WorldAccess where
  | none_
  | sloadSlot
  | sstoreSlot
  | tloadSlot
  | tstoreSlot
  | balanceOf
  | codeSizeOf
  | codeHashOf
  | codeCopyOf
  | blockHashOf
  | logEmit  (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-! ## CALL / CREATE flavor tags -/

inductive CallKind where
  | call | callcode | delegatecall | staticcall
  deriving Repr, DecidableEq, Inhabited

inductive CreateKind where
  | create | create2
  deriving Repr, DecidableEq, Inhabited

/-! ## Pure operations

    Cover all EVM opcodes EXCEPT control-flow / sub-frame yields,
    which are Terminators. Each variant has a compile-time-known
    stack effect and (per fork) static + dynamic gas decomposition. -/

inductive Op where
  -- 0x01..0x0b: arithmetic
  | add | mul | sub | div | sdiv | mod | smod
  | addmod | mulmod | exp | signextend
  -- 0x10..0x1d: comparison + bitwise
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
  | blobhash                                                  -- Cancun+
  | blobbasefee                                               -- Cancun+
  -- 0x50..0x5f: stack / memory / storage / flow / push0
  | pop | mload | mstore | mstore8
  | sload | sstore
  -- PC and GAS carry compile-time literals: the compiler knows the
  -- op's pc, and (within a pre-charged chunk) the gas remaining at
  -- the op is the frame's gasLeft plus the chunk's still-uncharged
  -- suffix gas `rem` — both fixed at compile time.
  | pc (v : Nat) | msize | gas (rem : Nat) | jumpdest
  | tload | tstore                                            -- Cancun+
  | mcopy                                                     -- Cancun+
  | push0                                                     -- Shanghai+
  -- 0x60..0x7f: PUSH1..PUSH32 (n ∈ {1..32}, imm = n-byte big-endian)
  | push (n : Nat) (imm : Evm.U256)
  -- 0x80..0x8f: DUP1..DUP16 (n ∈ {1..16})
  | dup  (n : Nat)
  -- 0x90..0x9f: SWAP1..SWAP16 (n ∈ {1..16})
  | swap (n : Nat)
  -- 0xa0..0xa4: LOG0..LOG4 (n ∈ {0..4} topics)
  | log  (n : Nat)
  -- 0x1c: CLZ (Osaka+) — placeholder so the enum can grow per fork
  | clz
  deriving Repr, DecidableEq, Inhabited

/-! ## Terminators — first-class with their own soundness obligations

    A terminator ends a chunk. Frame-ending terminators (STOP/RETURN/…)
    finish the frame; frame-yielding ones (CALL/CREATE/SELFDESTRUCT)
    invoke the trampoline. Control-flow terminators (JUMP/JUMPI/
    fallthrough) hand off to a successor chunk. -/

inductive Terminator where
  -- Frame-ending
  | stop                            -- 0x00
  | ret                             -- 0xf3
  | revert                          -- 0xfd  (Byzantium+)
  | invalid                         -- 0xfe; also fallthrough trap
  -- Frame-yielding (trampoline)
  | call            (kind : CallKind)
  | create          (kind : CreateKind)
  | selfdestruct                    -- 0xff  (EIP-6780 interacts)
  -- Control flow within the program
  | fallthrough     (next : Nat)
  | jump            (dest : Nat)    -- compile-time-constant target
  | jumpDynamic                     -- runtime-resolved via JUMPDEST table
  | jumpi           (dest : Nat)
  | jumpiDynamic
  | endOfCode                       -- implicit STOP past end of code
  deriving Repr, DecidableEq, Inhabited

/-! ## Op metadata

    Per-fork data about each op. `metadata fork op = none` means the
    op is not legal on that fork (e.g. PUSH0 pre-Shanghai). -/

structure OpMetadata where
  staticCost   : Nat
  dynamicGas   : DynamicGasShape
  stackEffect  : StackEffect
  memoryAccess : MemoryAccess
  worldAccess  : WorldAccess
  deriving Repr, Inhabited

/-! ## Terminator metadata

    Same shape plus trampoline reference. `trampoline` is `none` for
    frame-ending / control-flow terminators (STOP, RET, REVERT,
    INVALID, JUMP, JUMPI, fallthrough, endOfCode). -/

inductive TrampolineSpec where
  | callTrampoline    (kind : CallKind)
  | createTrampoline  (kind : CreateKind)
  | selfdestructTrampoline
  deriving Repr, DecidableEq, Inhabited

structure TerminatorMetadata where
  staticCost   : Nat
  dynamicGas   : DynamicGasShape
  popCount     : Nat
  /-- Stack pushes that happen on RESUMPTION (after the sub-frame
      returns). 0 for non-yielding terminators. -/
  pushOnResume : Nat
  trampoline   : Option TrampolineSpec
  deriving Repr, Inhabited

/-! ## Metadata lookup

    `none` means the op does not exist on that fork (e.g. PUSH0
    pre-Shanghai). Static costs follow EELS `vm/gas.py` of each fork;
    rows whose cost is fork-stable use the literal, fork-varying rows
    (BALANCE / SLOAD / EXTCODE* — repriced by EIP-150, EIP-1884,
    EIP-2929) branch on `fork.atLeast`. For Berlin+ the staticCost of
    an account/storage-touching op is the WARM access cost; the cold
    surcharge is declared via `dynamicGas`. -/

private def mkOp (staticCost : Nat) (dyn : DynamicGasShape)
    (pops pushes : Nat)
    (mem : MemoryAccess := .none_) (world : WorldAccess := .none_) :
    Option OpMetadata :=
  some { staticCost := staticCost, dynamicGas := dyn,
         stackEffect := { popCount := pops, pushCount := pushes },
         memoryAccess := mem, worldAccess := world }

def Op.metadata (fork : Evm.Fork) (op : Op) : Option OpMetadata :=
  -- EIP-2929 (Berlin) splits state-access gas into warm static + cold
  -- dynamic; pre-Berlin the whole cost is static and there is no cold
  -- shape.
  let acctDyn : DynamicGasShape :=
    if fork.atLeast .berlin then .coldAccount else .none_
  -- GAS_SLOAD: 50 Frontier; 200 EIP-150; 800 EIP-1884; 100 warm EIP-2929.
  let sloadCost : Nat :=
    if fork.atLeast .berlin then 100
    else if fork.atLeast .istanbul then 800
    else if fork.atLeast .tangerineWhistle then 200
    else 50
  -- GAS_BALANCE: 20 Frontier; 400 EIP-150; 700 EIP-1884; 100 warm EIP-2929.
  let balanceCost : Nat :=
    if fork.atLeast .berlin then 100
    else if fork.atLeast .istanbul then 700
    else if fork.atLeast .tangerineWhistle then 400
    else 20
  -- GAS_EXTERNAL (EXTCODESIZE/EXTCODECOPY base): 20 Frontier; 700
  -- EIP-150; 100 warm EIP-2929.
  let extcodeCost : Nat :=
    if fork.atLeast .berlin then 100
    else if fork.atLeast .tangerineWhistle then 700
    else 20
  -- GAS_CODE_HASH: 400 at introduction (EIP-1052, Constantinople);
  -- 700 EIP-1884; 100 warm EIP-2929.
  let extcodehashCost : Nat :=
    if fork.atLeast .berlin then 100
    else if fork.atLeast .istanbul then 700
    else 400
  match op with
  -- 0x01..0x0b: arithmetic
  | .add        => mkOp 3 .none_ 2 1
  | .mul        => mkOp 5 .none_ 2 1
  | .sub        => mkOp 3 .none_ 2 1
  | .div        => mkOp 5 .none_ 2 1
  | .sdiv       => mkOp 5 .none_ 2 1
  | .mod        => mkOp 5 .none_ 2 1
  | .smod       => mkOp 5 .none_ 2 1
  | .addmod     => mkOp 8 .none_ 3 1
  | .mulmod     => mkOp 8 .none_ 3 1
  | .exp        => mkOp 10 .expPerByte 2 1
  | .signextend => mkOp 5 .none_ 2 1
  -- 0x10..0x1d: comparison + bitwise
  | .lt     => mkOp 3 .none_ 2 1
  | .gt     => mkOp 3 .none_ 2 1
  | .slt    => mkOp 3 .none_ 2 1
  | .sgt    => mkOp 3 .none_ 2 1
  | .eq     => mkOp 3 .none_ 2 1
  | .iszero => mkOp 3 .none_ 1 1
  | .and_   => mkOp 3 .none_ 2 1
  | .or_    => mkOp 3 .none_ 2 1
  | .xor_   => mkOp 3 .none_ 2 1
  | .not_   => mkOp 3 .none_ 1 1
  | .byte   => mkOp 3 .none_ 2 1
  | .shl    => if fork.atLeast .constantinople then mkOp 3 .none_ 2 1 else none
  | .shr    => if fork.atLeast .constantinople then mkOp 3 .none_ 2 1 else none
  | .sar    => if fork.atLeast .constantinople then mkOp 3 .none_ 2 1 else none
  -- 0x20
  | .keccak256 => mkOp 30 .keccakPerWord 2 1 (.readRange 0 1)
  -- 0x30..0x3f: environment
  | .balance       => mkOp balanceCost acctDyn 1 1 .none_ .balanceOf
  | .address       => mkOp 2 .none_ 0 1
  | .origin        => mkOp 2 .none_ 0 1
  | .caller        => mkOp 2 .none_ 0 1
  | .callvalue     => mkOp 2 .none_ 0 1
  | .calldataload  => mkOp 3 .none_ 1 1
  | .calldatasize  => mkOp 2 .none_ 0 1
  | .calldatacopy  => mkOp 3 .copyPerWord 3 0 (.writeRange 0 2)
  | .codesize      => mkOp 2 .none_ 0 1
  | .codecopy      => mkOp 3 .copyPerWord 3 0 (.writeRange 0 2)
  | .gasprice      => mkOp 2 .none_ 0 1
  | .extcodesize   => mkOp extcodeCost acctDyn 1 1 .none_ .codeSizeOf
  | .extcodecopy   =>
    mkOp extcodeCost
         (if fork.atLeast .berlin then .coldAccountPlusCopy else .copyPerWord)
         4 0 (.writeRange 1 3) .codeCopyOf
  | .returndatasize =>
    if fork.atLeast .byzantium then mkOp 2 .none_ 0 1 else none
  | .returndatacopy =>
    if fork.atLeast .byzantium
    then mkOp 3 .copyPerWord 3 0 (.writeRange 0 2) else none
  | .extcodehash   =>
    if fork.atLeast .constantinople
    then mkOp extcodehashCost acctDyn 1 1 .none_ .codeHashOf else none
  -- 0x40..0x4a: block context
  | .blockhash   => mkOp 20 .none_ 1 1 .none_ .blockHashOf
  | .coinbase    => mkOp 2 .none_ 0 1
  | .timestamp   => mkOp 2 .none_ 0 1
  | .number      => mkOp 2 .none_ 0 1
  | .prevrandao  => mkOp 2 .none_ 0 1   -- DIFFICULTY pre-Paris, same byte/cost
  | .gaslimit    => mkOp 2 .none_ 0 1
  | .chainid     =>
    if fork.atLeast .istanbul then mkOp 2 .none_ 0 1 else none
  | .selfbalance =>
    if fork.atLeast .istanbul then mkOp 5 .none_ 0 1 .none_ .balanceOf else none
  | .basefee     =>
    if fork.atLeast .london then mkOp 2 .none_ 0 1 else none
  | .blobhash    =>
    if fork.atLeast .cancun then mkOp 3 .none_ 1 1 else none
  | .blobbasefee =>
    if fork.atLeast .cancun then mkOp 2 .none_ 0 1 else none
  -- 0x50..0x5f
  | .pop      => mkOp 2 .none_ 1 0
  | .mload    => mkOp 3 .memExpand 1 1 (.readWord 0)
  | .mstore   => mkOp 3 .memExpand 2 0 (.writeWord 0)
  | .mstore8  => mkOp 3 .memExpand 2 0 (.writeByte 0)
  | .sload    => mkOp sloadCost
                      (if fork.atLeast .berlin then .coldStorage else .none_)
                      1 1 .none_ .sloadSlot
  | .sstore   => mkOp 0 .sstoreEip2200 2 0 .none_ .sstoreSlot
  | .pc _     => mkOp 2 .none_ 0 1
  | .msize    => mkOp 2 .none_ 0 1
  | .gas _    => mkOp 2 .none_ 0 1
  | .jumpdest => mkOp 1 .none_ 0 0
  | .tload    =>
    if fork.atLeast .cancun then mkOp 100 .none_ 1 1 .none_ .tloadSlot else none
  | .tstore   =>
    if fork.atLeast .cancun then mkOp 100 .none_ 2 0 .none_ .tstoreSlot else none
  | .mcopy    =>
    if fork.atLeast .cancun
    then mkOp 3 .copyPerWord 3 0 (.copyRange 0 1 2) else none
  | .push0    =>
    if fork.atLeast .shanghai then mkOp 2 .none_ 0 1 else none
  -- 0x60..0xa4: PUSH / DUP / SWAP / LOG
  | .push _ _ => mkOp 3 .none_ 0 1
  | .dup _    => mkOp 3 .none_ 0 1   -- reads stack[n-1], net effect +1
  | .swap _   => mkOp 3 .none_ 0 0
  | .log n    =>
    mkOp (375 + 375 * n) .logPerByte (2 + n) 0 (.readRange 0 1) (.logEmit n)
  -- 0x1e: CLZ (EIP-7939)
  | .clz      => if fork.atLeast .osaka then mkOp 5 .none_ 1 1 else none

/-- Static gas, per fork — the `Op.metadata` staticCost (the Phase-1
    table is the single source of truth for the per-fork repricings:
    EIP-150, EIP-1884, EIP-2929 warm costs). `0` for an op with no
    metadata row is unreachable from `compileLoop`: every arm is
    gated on the op's introducing fork, where the row exists. Lives
    next to the table because BOTH ends of the pipeline read it: the
    compiler's chunk pre-charge sums it, and `execOpFor` credits it
    back when routing a Berlin+ access op to its self-pricing
    handler. -/
def staticGasFor (fork : Evm.Fork) (op : Op) : Nat :=
  match Op.metadata fork op with
  | some m => m.staticCost
  | none   => 0

def Terminator.metadata (fork : Evm.Fork) (t : Terminator) :
    Option TerminatorMetadata :=
  match t with
  | .stop      => some { staticCost := 0, dynamicGas := .none_,
                         popCount := 0, pushOnResume := 0, trampoline := none }
  | .ret       => some { staticCost := 0, dynamicGas := .memExpand,
                         popCount := 2, pushOnResume := 0, trampoline := none }
  | .revert    =>
    if fork.atLeast .byzantium then
      some { staticCost := 0, dynamicGas := .memExpand,
             popCount := 2, pushOnResume := 0, trampoline := none }
    else none
  -- INVALID consumes ALL remaining gas — that is exceptional-halt
  -- semantics, not a chargeable cost, so staticCost is 0.
  | .invalid   => some { staticCost := 0, dynamicGas := .none_,
                         popCount := 0, pushOnResume := 0, trampoline := none }
  -- DELEGATECALL ships in Homestead (EIP-7), STATICCALL in Byzantium
  -- (EIP-214); before that the byte is undefined — same gates as
  -- `compileLoop` and `Terminator.stepHandler`.
  | .call k    =>
    if (k == .delegatecall && !fork.atLeast .homestead)
       || (k == .staticcall && !fork.atLeast .byzantium) then none
    else some { staticCost := 0, dynamicGas := .callForward,
                popCount := (match k with | .call | .callcode => 7 | _ => 6),
                pushOnResume := 1, trampoline := some (.callTrampoline k) }
  -- CREATE2 ships in Constantinople (EIP-1014).
  | .create k  =>
    if k == .create2 && !fork.atLeast .constantinople then none
    else some { staticCost := 32000, dynamicGas := .createBase,
                popCount := (match k with | .create => 3 | .create2 => 4),
                pushOnResume := 1,
                trampoline := some (.createTrampoline k) }
  -- GAS_SELF_DESTRUCT: 0 Frontier; 5000 EIP-150.
  | .selfdestruct =>
    some { staticCost := if fork.atLeast .tangerineWhistle then 5000 else 0,
           dynamicGas := .selfdestructFee,
           popCount := 1, pushOnResume := 0,
           trampoline := some .selfdestructTrampoline }
  | .fallthrough _ => some { staticCost := 0, dynamicGas := .none_,
                             popCount := 0, pushOnResume := 0, trampoline := none }
  | .jump _        => some { staticCost := 8, dynamicGas := .none_,
                             popCount := 1, pushOnResume := 0, trampoline := none }
  | .jumpDynamic   => some { staticCost := 8, dynamicGas := .none_,
                             popCount := 1, pushOnResume := 0, trampoline := none }
  | .jumpi _       => some { staticCost := 10, dynamicGas := .none_,
                             popCount := 2, pushOnResume := 0, trampoline := none }
  | .jumpiDynamic  => some { staticCost := 10, dynamicGas := .none_,
                             popCount := 2, pushOnResume := 0, trampoline := none }
  | .endOfCode     => some { staticCost := 0, dynamicGas := .none_,
                             popCount := 0, pushOnResume := 0, trampoline := none }

/-! ## Chunks and Programs

    A chunk is the unit of compilation: ordered list of `Op`s plus
    one `Terminator`. JIT compiles a whole chunk into native code;
    interp tier walks ops via the dispatch table.

    A program is `entry pc + map<pc, chunk> + jumpdest set + fork`.
    The fork is embedded so runtime gas math can look up the right
    metadata table. -/

structure Chunk where
  startPc   : Nat
  /-- The `pc` value the EVM frame holds when this chunk's terminator
      fires: the STOP's own pc (STOP halts without advancing), the
      byte AFTER a RETURN (its handler advances pc before halting),
      or the first pc past the last op for `endOfCode` (which can
      exceed `code.size` when a truncated PUSH immediate runs off the
      end). `IR.execTerm` writes it into the halted frame so the IR
      result matches `Effect.runFrame` exactly, pc included. -/
  endPc     : Nat
  /-- Static gas cost = sum of `op.metadata.staticCost` over ops.
      Pre-charged at chunk head by both interp + JIT. -/
  staticGas : Nat
  ops       : List Op
  term      : Terminator
  deriving Repr, Inhabited

structure Program where
  entry      : Nat
  /-- For the single-chunk slice (no JUMP/JUMPI), this maps `entry`
      to the one chunk. Multi-chunk lands in Phase 4. -/
  chunks     : List (Nat × Chunk)
  /-- Set of valid JUMPDEST locations in the original bytecode,
      represented as a sorted list for now (a HashSet costs more
      machinery than is justified for the current phase). -/
  jumpdests  : List Nat
  fork       : Evm.Fork
  deriving Repr, Inhabited

end Evm.IR
