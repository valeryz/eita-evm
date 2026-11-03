/-
  Evm.IR.Compile — bytecode → IR compiler (no-jump slice).

  Walks EVM bytecode left-to-right, emitting Op-level IR plus the
  appropriate Terminator. Static gas cost is accumulated as we go.

  Scope:
    - Single chunk (entry pc 0, no JUMP/JUMPI yet).
    - Truncated PUSH (immediate runs past end of code) is handled
      by zero-padding, matching EVM semantics.
    - Unknown / fork-undefined opcode → `.invalid` terminator
      (exceptional halt, all gas consumed), never a CompileError.
      Per EVM semantics an opcode undefined in the active fork is a
      runtime INVALID, not a compile failure; emitting `.invalid`
      keeps such contracts on the JIT path instead of dropping the
      whole code to the slower interpreter.
-/

import Evm.IR.Types
import Evm.BaseTypes
import Evm.Frontier.Vm.Gas   -- per-opcode static gas constants
import Evm.Constantinople.Vm.Gas
import Evm.Istanbul.Vm.Gas
import Evm.Cancun.Vm.Gas

namespace Evm.IR

open Evm.Frontier.Vm.Gas

/-! ## Compile errors -/

inductive CompileError where
  | unknownOpcode (op : UInt8) (pc : Nat)
  deriving Repr

/-! ## Per-opcode static gas

    These are the *constant-time* gas costs. Ops with dynamic
    components (MLOAD/MSTORE charge memory-expansion at runtime;
    EXP charges per-byte at runtime) declare only their fixed
    component here, with the dynamic part computed by the
    runtime / interpreter / compiled chunk. -/

/-! ## Reading a PUSH immediate

    EVM zero-pads when the immediate runs past the end of code. -/

/-- The PUSH immediate is exactly what `Instructions.push` computes at
    runtime: the `n` bytes after the opcode, big-endian, zero-padded
    when the code ends early. Defined as that expression VERBATIM so
    the compiler/handler agreement in `IR.Soundness` is `rfl`. -/
def readImmediate (code : Evm.Bytes) (pc n : Nat) : Evm.U256 :=
  Evm.U256.ofBytesBE (Evm.Bytes.sliceZeroPad code (pc + 1) n)

/-! ## The compile loop

    Walks bytecode emitting ops until it sees a terminator. Returns
    `(ops, staticGas, terminator, endPc)` — see `Chunk.endPc` for the
    endPc convention.

    Direct (non-accumulator) recursion, total via the `code.size - pc`
    measure: the chunk-level soundness induction in `IR.Soundness`
    follows this definition's structure, which a `partial def` (opaque
    to the kernel) or an accumulator (invariant threading) would
    obstruct. -/

def compileLoop (fork : Evm.Fork) (code : Evm.Bytes) (pc : Nat) :
    Except CompileError (List Op × Nat × Terminator × Nat) :=
  if _h : pc ≥ code.size then
    .ok ([], 0, .endOfCode, pc)
  else
    let opcode := code.get! pc
    match opcode.toNat with
    | 0x00 => .ok ([], 0, .stop, pc)        -- STOP halts at its own pc
    | 0xf3 => .ok ([], 0, .ret, pc + 1)     -- RETURN advances pc, then halts
    | 0x01 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.add :: ops, staticGasFor fork Op.add + gas, term, e)
    | 0x02 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.mul :: ops, staticGasFor fork Op.mul + gas, term, e)
    | 0x03 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.sub :: ops, staticGasFor fork Op.sub + gas, term, e)
    | 0x50 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.pop :: ops, staticGasFor fork Op.pop + gas, term, e)
    | 0x51 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.mload :: ops, staticGasFor fork Op.mload + gas, term, e)
    | 0x52 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.mstore :: ops, staticGasFor fork Op.mstore + gas, term, e)
    -- New arms are appended AFTER the 0x52 arm (and before the
    -- push/default arm) so `compileLoop.induct` keeps the case
    -- numbering of the arms above stable.
    | 0x04 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.div :: ops, staticGasFor fork Op.div + gas, term, e)
    | 0x05 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.sdiv :: ops, staticGasFor fork Op.sdiv + gas, term, e)
    | 0x06 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.mod :: ops, staticGasFor fork Op.mod + gas, term, e)
    | 0x07 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.smod :: ops, staticGasFor fork Op.smod + gas, term, e)
    | 0x08 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.addmod :: ops, staticGasFor fork Op.addmod + gas, term, e)
    | 0x09 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.mulmod :: ops, staticGasFor fork Op.mulmod + gas, term, e)
    | 0x0b => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.signextend :: ops, staticGasFor fork Op.signextend + gas, term, e)
    | 0x10 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.lt :: ops, staticGasFor fork Op.lt + gas, term, e)
    | 0x11 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.gt :: ops, staticGasFor fork Op.gt + gas, term, e)
    | 0x12 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.slt :: ops, staticGasFor fork Op.slt + gas, term, e)
    | 0x13 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.sgt :: ops, staticGasFor fork Op.sgt + gas, term, e)
    | 0x14 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.eq :: ops, staticGasFor fork Op.eq + gas, term, e)
    | 0x15 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.iszero :: ops, staticGasFor fork Op.iszero + gas, term, e)
    | 0x16 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.and_ :: ops, staticGasFor fork Op.and_ + gas, term, e)
    | 0x17 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.or_ :: ops, staticGasFor fork Op.or_ + gas, term, e)
    | 0x18 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.xor_ :: ops, staticGasFor fork Op.xor_ + gas, term, e)
    | 0x19 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.not_ :: ops, staticGasFor fork Op.not_ + gas, term, e)
    | 0x1a => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.byte :: ops, staticGasFor fork Op.byte + gas, term, e)
    | 0x0a => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.exp :: ops, staticGasFor fork Op.exp + gas, term, e)
    | 0x30 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.address :: ops, staticGasFor fork Op.address + gas, term, e)
    | 0x32 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.origin :: ops, staticGasFor fork Op.origin + gas, term, e)
    | 0x33 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.caller :: ops, staticGasFor fork Op.caller + gas, term, e)
    | 0x34 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.callvalue :: ops, staticGasFor fork Op.callvalue + gas, term, e)
    | 0x35 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.calldataload :: ops, staticGasFor fork Op.calldataload + gas, term, e)
    | 0x36 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.calldatasize :: ops, staticGasFor fork Op.calldatasize + gas, term, e)
    | 0x38 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.codesize :: ops, staticGasFor fork Op.codesize + gas, term, e)
    | 0x3a => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.gasprice :: ops, staticGasFor fork Op.gasprice + gas, term, e)
    | 0x41 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.coinbase :: ops, staticGasFor fork Op.coinbase + gas, term, e)
    | 0x42 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.timestamp :: ops, staticGasFor fork Op.timestamp + gas, term, e)
    | 0x43 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.number :: ops, staticGasFor fork Op.number + gas, term, e)
    | 0x44 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.prevrandao :: ops, staticGasFor fork Op.prevrandao + gas, term, e)
    | 0x45 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.gaslimit :: ops, staticGasFor fork Op.gaslimit + gas, term, e)
    | 0x53 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.mstore8 :: ops, staticGasFor fork Op.mstore8 + gas, term, e)
    -- PC's literal is this op's own pc.
    | 0x58 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.pc pc :: ops, staticGasFor fork (Op.pc pc) + gas, term, e)
    | 0x59 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.msize :: ops, staticGasFor fork Op.msize + gas, term, e)
    -- GAS's literal is the chunk's remaining static gas AFTER this
    -- op (the recursive call's `gas`): the pre-charge already took
    -- it from gasLeft, but a step-at-a-time frame wouldn't have.
    | 0x5a => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.gas gas :: ops, staticGasFor fork (Op.gas gas) + gas, term, e)
    | 0x5b => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.jumpdest :: ops, staticGasFor fork Op.jumpdest + gas, term, e)
    -- Control-flow terminators. Their gas (mid / high) is charged at
    -- runtime by `execTerm`, mirroring the handlers — NOT folded into
    -- the chunk's static pre-charge.
    | 0x56 => .ok ([], 0, .jumpDynamic, pc + 1)
    | 0x57 => .ok ([], 0, .jumpiDynamic, pc + 1)  -- endPc = fallthrough pc
    -- INVALID terminates the chunk; `execTerm` raises on it, so a
    -- chunk ending here compiles fine but can never run to `.ok`.
    | 0xfe => .ok ([], 0, .invalid, pc)
    | 0x20 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.keccak256 :: ops, staticGasFor fork Op.keccak256 + gas, term, e)
    | 0x37 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.calldatacopy :: ops, staticGasFor fork Op.calldatacopy + gas, term, e)
    | 0x39 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.codecopy :: ops, staticGasFor fork Op.codecopy + gas, term, e)
    | 0x31 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.balance :: ops, staticGasFor fork Op.balance + gas, term, e)
    | 0x3b => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.extcodesize :: ops, staticGasFor fork Op.extcodesize + gas, term, e)
    | 0x3c => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.extcodecopy :: ops, staticGasFor fork Op.extcodecopy + gas, term, e)
    | 0x40 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.blockhash :: ops, staticGasFor fork Op.blockhash + gas, term, e)
    | 0x54 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.sload :: ops, staticGasFor fork Op.sload + gas, term, e)
    | 0x55 => do
      let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
      return (Op.sstore :: ops, staticGasFor fork Op.sstore + gas, term, e)
    -- Yielding / frame-ending terminators (Stage C). endPc is the
    -- opcode's OWN pc: `doCall`/`doCallcode`/`doCreate` read `evm.pc`
    -- as the resume point (the resume functions set `pc + 1`), and
    -- `Vm.selfdestruct` halts with pc unchanged at the opcode — so
    -- the chunk runner positions the frame at endPc before
    -- dispatching. Cost is 0 statically: each handler does its own
    -- gas math (CALL base + value fee + new-account fee inside
    -- `doCall`, etc.).
    | 0xf0 => .ok ([], 0, .create .create, pc)
    | 0xf1 => .ok ([], 0, .call .call, pc)
    | 0xf2 => .ok ([], 0, .call .callcode, pc)
    | 0xff => .ok ([], 0, .selfdestruct, pc)
    -- Post-Frontier opcodes (#222). Each arm is gated on its
    -- INTRODUCING fork: below that fork the byte is undefined, so it
    -- compiles to `.invalid` (runtime exceptional halt), exactly like
    -- an all-forks-undefined byte. `execTerm .invalid` errors, so the
    -- Frontier-instantiated soundness theorems stay true (the
    -- gated-off cases are vacuous via the erroring terminator, no
    -- longer via a compile error). #246.
    | 0x1b =>
      if fork.atLeast .constantinople then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.shl :: ops, staticGasFor fork Op.shl + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x1c =>
      if fork.atLeast .constantinople then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.shr :: ops, staticGasFor fork Op.shr + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x1d =>
      if fork.atLeast .constantinople then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.sar :: ops, staticGasFor fork Op.sar + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x3d =>
      if fork.atLeast .byzantium then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.returndatasize :: ops, staticGasFor fork Op.returndatasize + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x3e =>
      if fork.atLeast .byzantium then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.returndatacopy :: ops, staticGasFor fork Op.returndatacopy + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x3f =>
      if fork.atLeast .constantinople then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.extcodehash :: ops, staticGasFor fork Op.extcodehash + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x46 =>
      if fork.atLeast .istanbul then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.chainid :: ops, staticGasFor fork Op.chainid + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x47 =>
      if fork.atLeast .istanbul then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.selfbalance :: ops, staticGasFor fork Op.selfbalance + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x48 =>
      if fork.atLeast .london then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.basefee :: ops, staticGasFor fork Op.basefee + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x49 =>
      if fork.atLeast .cancun then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.blobhash :: ops, staticGasFor fork Op.blobhash + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x4a =>
      if fork.atLeast .cancun then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.blobbasefee :: ops, staticGasFor fork Op.blobbasefee + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x5c =>
      if fork.atLeast .cancun then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.tload :: ops, staticGasFor fork Op.tload + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x5d =>
      if fork.atLeast .cancun then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.tstore :: ops, staticGasFor fork Op.tstore + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x5e =>
      if fork.atLeast .cancun then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.mcopy :: ops, staticGasFor fork Op.mcopy + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | 0x5f =>
      if fork.atLeast .shanghai then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.push0 :: ops, staticGasFor fork Op.push0 + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    -- REVERT mirrors RETURN's endPc convention: the handler sets
    -- `pc := evm.pc + 1`, then halts (reverted := true).
    | 0xfd =>
      if fork.atLeast .byzantium then .ok ([], 0, .revert, pc + 1)
      else .ok ([], 0, .invalid, pc)
    -- Yielding terminators: endPc is the opcode's OWN pc (same
    -- convention as CALL/CALLCODE/CREATE above).
    | 0xf4 =>
      if fork.atLeast .homestead then .ok ([], 0, .call .delegatecall, pc)
      else .ok ([], 0, .invalid, pc)
    | 0xfa =>
      if fork.atLeast .byzantium then .ok ([], 0, .call .staticcall, pc)
      else .ok ([], 0, .invalid, pc)
    | 0xf5 =>
      if fork.atLeast .constantinople then .ok ([], 0, .create .create2, pc)
      else .ok ([], 0, .invalid, pc)
    -- CLZ (Osaka, EIP-7939). Without this arm the byte fell to the
    -- default arm below and compiled to `.invalid` on Osaka+ too: the
    -- JIT halted every CLZ frame exceptionally (mainnet 24,538,111).
    | 0x1e =>
      if fork.atLeast .osaka then do
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.clz :: ops, staticGasFor fork Op.clz + gas, term, e)
      else .ok ([], 0, .invalid, pc)
    | n =>
      if 0x60 ≤ n ∧ n ≤ 0x7f then do
        let immBytes := n - 0x5f       -- PUSH1 = 0x60 → 1 byte
        let op := Op.push immBytes (readImmediate code pc immBytes)
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1 + immBytes)
        return (op :: ops, staticGasFor fork op + gas, term, e)
      else if 0x80 ≤ n ∧ n ≤ 0x8f then do
        -- DUP1 = 0x80 → depth 1
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.dup (n - 0x7f) :: ops, staticGasFor fork (Op.dup (n - 0x7f)) + gas, term, e)
      else if 0x90 ≤ n ∧ n ≤ 0x9f then do
        -- SWAP1 = 0x90 → depth 1
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.swap (n - 0x8f) :: ops, staticGasFor fork (Op.swap (n - 0x8f)) + gas, term, e)
      else if 0xa0 ≤ n ∧ n ≤ 0xa4 then do
        -- LOG0 = 0xa0 → 0 topics
        let (ops, gas, term, e) ← compileLoop fork code (pc + 1)
        return (Op.log (n - 0xa0) :: ops, staticGasFor fork (Op.log (n - 0xa0)) + gas, term, e)
      else
        -- A byte undefined in EVERY fork behaves exactly like INVALID
        -- (exceptional halt, all gas consumed), so compile it as the
        -- `.invalid` terminator instead of failing the whole code:
        -- deployed contracts are full of unreachable junk bytes, and
        -- whole-code CompileErrors would push them off the JIT path.
        -- Fork-GATED bytes (the `atLeast` arms above) compile to the
        -- SAME `.invalid` when below their introducing fork (#246), so
        -- no byte position ever yields a CompileError.
        .ok ([], 0, .invalid, pc)
termination_by code.size - pc
decreasing_by all_goals omega

/-- Compile EVM bytecode into a single-chunk IR (no-jump slice).
    The chunk starts at pc 0. -/
def compile (fork : Evm.Fork) (code : Evm.Bytes) : Except CompileError Chunk := do
  let (ops, gas, term, endPc) ← compileLoop fork code 0
  return { startPc := 0, endPc := endPc, staticGas := gas,
           ops := ops, term := term }

/-! ## Multi-chunk programs (Phase 4)

    Design: OVERLAPPING chunks, no chunk-splitting. A chunk is
    compiled at every possible control-transfer landing site:

      entries = {0} ∪ {JUMPDEST pcs} ∪ {pc+1 : code[pc] = JUMPI}
              ∪ {pc+1 : code[pc] ∈ {CREATE, CALL, CALLCODE}}

    (the last set: sub-frame terminators resume the parent at pc+1)

    and each entry runs the ordinary `compileLoop`, which walks
    THROUGH any interior JUMPDESTs (they are plain `Op.jumpdest`
    ops) until a real terminator (STOP / RETURN / JUMP / JUMPI /
    INVALID / end-of-code). A JUMPDEST reachable both by fallthrough
    and by jump is therefore covered twice — once inside the longer
    chunk, once as its own chunk head — which is tail duplication,
    not a semantic fork: chunk soundness holds per chunk regardless
    of overlap.

    Completeness caveat (soundness is NOT affected): the entry scan
    walks the code linearly skipping PUSH immediates, so a JUMPI
    byte sitting inside data (or a chunk reaching an opcode outside
    the compiled slice) makes `compileProgram` fail loudly with
    `CompileError`. Refining the entry analysis (reachability) is
    future work; `executeProgram` likewise errors — never silently
    diverges — on a missing chunk. -/

/-- Skip over a PUSH-n opcode's immediate bytes, returning the pc of
    the next instruction. For non-PUSH opcodes, returns `pc + 1`. -/
def nextInstrPc (op : UInt8) (pc : Nat) : Nat :=
  if 0x60 ≤ op.toNat ∧ op.toNat ≤ 0x7f then
    pc + 1 + (op.toNat - 0x5f)
  else
    pc + 1

private theorem nextInstrPc_gt (op : UInt8) (pc : Nat) :
    pc < nextInstrPc op pc := by
  unfold nextInstrPc; split <;> omega

/-- Scan the code for chunk-entry pcs: each JUMPDEST (a jump landing
    site) and each pc after a JUMPI (its fallthrough landing site).
    PUSH immediates are skipped, so data bytes never register. -/
def chunkEntries (code : Evm.Bytes) (pc : Nat) : List Nat :=
  if _h : pc ≥ code.size then []
  else
    let op := code.get! pc
    let tail := chunkEntries code (nextInstrPc op pc)
    if op.toNat = 0x5b then pc :: tail
    else if op.toNat = 0x57 then (pc + 1) :: tail
    -- CALL-family / CREATE-family resume at pc+1 (`resumeCall*` /
    -- `Create.resume` set `pc + 1`), so the byte after them is a
    -- chunk-entry landing site. Fork-blind: a spurious entry for a
    -- not-yet-active opcode byte just compiles an extra chunk.
    else if op.toNat = 0xf0 ∨ op.toNat = 0xf1 ∨ op.toNat = 0xf2
         ∨ op.toNat = 0xf4 ∨ op.toNat = 0xfa ∨ op.toNat = 0xf5 then
      (pc + 1) :: tail
    else tail
termination_by code.size - pc
decreasing_by have := nextInstrPc_gt (code.get! pc) pc; omega

/-- Compile the chunk whose entry is `pc`. -/
def compileChunkAt (fork : Evm.Fork) (code : Evm.Bytes) (pc : Nat) :
    Except CompileError Chunk := do
  let (ops, gas, term, endPc) ← compileLoop fork code pc
  return { startPc := pc, endPc := endPc, staticGas := gas,
           ops := ops, term := term }

/-- Compile bytecode into a multi-chunk `Program`: one chunk per
    entry pc. Duplicate entries are harmless (first hit wins on
    lookup; all carry identical chunks). -/
def compileProgram (fork : Evm.Fork) (code : Evm.Bytes) : Except CompileError Program := do
  let entries := 0 :: chunkEntries code 0
  let chunks ← entries.mapM (fun e => do
    let ch ← compileChunkAt fork code e
    return (e, ch))
  return { entry := 0, chunks := chunks,
           jumpdests := entries.filter
             (fun e => e < code.size ∧ (code.get! e).toNat = 0x5b),
           fork := fork }

end Evm.IR
