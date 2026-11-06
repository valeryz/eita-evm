/-
  Evm.CL.ARM64 — ARM64 threaded-interpreter emitter.

  ## Calling convention (threaded interp)

  Once `eita_run_one` (or the production entry point) has set up the
  cached state, each opcode handler runs with the following registers
  live across calls. Handlers do NOT preserve callee-saved registers
  beyond what's required by the trampoline at entry/exit; within a
  threaded run, they tail-jump via `br x27` to the continuation.

    x6-x9    : TOS limbs 0..3 (LSB first)
    x10-x13  : NOS limbs 0..3
    x20      : EvmState *
    x21      : pc            (cached; sync'd to memory only at boundaries)
    x22      : gas_left      (cached)
    x23      : sp            (cached)
    x24      : stack base    (pointer to u256_t[1024])
    x25      : dispatch_table (256 × function pointer)
    x26      : code base
    x27      : continuation  (next or sync_and_ret)
    x0-x5    : scratch + C ABI arg slots for callbacks
    x14-x17  : scratch
    v0-v15   : scratch (NEON for bitwise ops, byte-swap)

  ## The `next` continuation

  ```
  next:
      ldrb w14, [x26, x21]          ; fetch opcode byte at pc
      add  x21, x21, #1             ; pc++
      ldr  x14, [x25, x14, lsl #3]  ; dispatch_table[op]
      br   x14
  ```

  Note: pc is pre-incremented past the opcode itself. Variable-length
  ops (PUSH-N) then advance pc by an additional N.

  ## The `sync_and_ret` continuation

  Writes cached state back to memory and returns to the C caller. The
  trampoline `eita_run_one` sets x27 = sync_and_ret so the first
  handler's `next` lands us here, exiting after exactly one opcode.

  ## Stack invariant

  At every handler boundary:
    - if sp >= 1: stack memory at [sp-1] equals x6-x9 (TOS)
    - if sp >= 2: stack memory at [sp-2] equals x10-x13 (NOS)

  Each handler is responsible for maintaining this invariant on exit:
  any change to TOS/NOS must be reflected in both registers AND memory.
  This keeps the slow path (callbacks, halts, third-from-top access)
  correct without per-handler sync overhead.
-/

import Evm.CL.Extract
import Evm.CL.AsmCore
import Evm.CL.OpInstrs
import Evm.CL.Frame

namespace Evm.CL.ARM64

open Evm.CL.Extract

/-! ## Field offsets (from c/evm_state.h). -/

namespace Offset
  def pc           : Nat := 0
  def gasLeft      : Nat := 8
  def sp           : Nat := 16
  def mp           : Nat := 24
  def stack        : Nat := 32
  def memory       : Nat := 40
  def memorySize   : Nat := 48
  def code         : Nat := 64
  def codeSize     : Nat := 72
  def address      : Nat := 144
  def origin       : Nat := 176
  def caller       : Nat := 208
  def callvalue    : Nat := 240
  def gasprice     : Nat := 272
  def chainid      : Nat := 304
  def coinbase     : Nat := 336
  def timestamp    : Nat := 368
  def blockNumber  : Nat := 400
  def gaslimit     : Nat := 432
  def basefee      : Nat := 464
  def cb           : Nat := 496
  def cbCtx        : Nat := 504
  -- EIP-4844 blob env (Cancun): the tx's versioned-hash table and count, the block's
  -- blob base fee. Read by `AsmCore.blobHashInstrs` (552/560) and BLOBBASEFEE (568).
  def blobHashes   : Nat := 552
  def blobHashCount : Nat := 560
  def blobBaseFee  : Nat := 568
  -- x86-64 direct threading: the table every handler's continuation jumps through.
  def contTable    : Nat := 600
end Offset

/-- Materialize a 64-bit literal into a register (movz + movk chain;
    fields that are zero are skipped). -/
def movImm (reg : String) (v : Nat) : String := Id.run do
  let mut s := s!"    movz  {reg}, #{v % 65536}\n"
  for i in [1:4] do
    let field := (v >>> (16 * i)) % 65536
    if field > 0 then
      s := s ++ s!"    movk  {reg}, #{field}, lsl #{16 * i}\n"
  return s

/-! ## Handler header + footer

The threaded convention: handler is just a label; ends with `br x27`. -/

def hdrSpec (name : String) : String :=
  s!".global _eita_handler_{name}\n" ++
  s!".p2align 2\n" ++
  s!"_eita_handler_{name}:\n"

/-- The header, printed from `Frame.handlerHeader`. -/
def hdr (name : String) : String := Frame.text (Frame.handlerHeader name)

theorem hdr_derived :
    ["add", "sstore", "call", "push32", "sstore_nosentry"].all
      (fun n => hdr n == hdrSpec n) = true := by native_decide

/-- Fault stubs: all halt + revert and exit via sync_and_ret. Crucially,
    they restore `sp` from x28 (set by the eita_run prologue to the
    post-callee-save SP) so handlers that allocated scratch frames
    (sload/sstore/keccak/call/...) don't leave sync_and_ret reading
    callee-saved registers from the wrong offset. -/
def faultStubs : String :=
  ".global _eita_oog\n" ++
  ".p2align 2\n" ++
  "_eita_oog:\n" ++
  "    mov   sp, x28\n" ++                       -- restore SP from trampoline-saved
  "    mov   x22, #0\n" ++                       -- gas = 0
  "    mov   w14, #1\n" ++
  "    strb  w14, [x20, #128]\n" ++              -- halted
  "    strb  w14, [x20, #129]\n" ++              -- reverted
  "    adrp  x27, _eita_sync_and_ret@PAGE\n" ++
  "    add   x27, x27, _eita_sync_and_ret@PAGEOFF\n" ++
  "    br    x27\n" ++
  ".global _eita_stack_overflow\n" ++
  ".p2align 2\n" ++
  "_eita_stack_overflow:\n" ++
  "    mov   sp, x28\n" ++
  "    mov   x22, #0\n" ++
  "    mov   w14, #1\n" ++
  "    strb  w14, [x20, #128]\n" ++
  "    strb  w14, [x20, #129]\n" ++
  "    adrp  x27, _eita_sync_and_ret@PAGE\n" ++
  "    add   x27, x27, _eita_sync_and_ret@PAGEOFF\n" ++
  "    br    x27\n" ++
  ".global _eita_stack_underflow\n" ++
  ".p2align 2\n" ++
  "_eita_stack_underflow:\n" ++
  "    mov   sp, x28\n" ++
  "    mov   x22, #0\n" ++
  "    mov   w14, #1\n" ++
  "    strb  w14, [x20, #128]\n" ++
  "    strb  w14, [x20, #129]\n" ++
  "    adrp  x27, _eita_sync_and_ret@PAGE\n" ++
  "    add   x27, x27, _eita_sync_and_ret@PAGEOFF\n" ++
  "    br    x27\n" ++
  ".global _eita_static_violation\n" ++
  ".p2align 2\n" ++
  "_eita_static_violation:\n" ++
  "    mov   sp, x28\n" ++
  "    mov   x22, #0\n" ++
  "    mov   w14, #1\n" ++
  "    strb  w14, [x20, #128]\n" ++
  "    strb  w14, [x20, #129]\n" ++
  "    adrp  x27, _eita_sync_and_ret@PAGE\n" ++
  "    add   x27, x27, _eita_sync_and_ret@PAGEOFF\n" ++
  "    br    x27\n"

/-! ## Per-shape handler emitters -/

/-- Binary arith with carry chain. `top OP nos → result`; pop 1.
    `firstOp` sets flags (adds/subs), then 2× `midOp`s, then `lastOp`. -/
def binArithHandler (name : String) (cost : Nat)
    (firstOp _midOp _lastOp : String) : String :=
  let k : AsmCore.ArithKind := if firstOp == "subs" then .sub else .add
  hdr name ++ (AsmCore.arithBody k cost).emitDerived

/-- Bitwise: limb-wise AND/OR/EOR. ARM64 op is one of "and", "orr", "eor".
    Emitted from the typed DSL `Evm.CL.AsmCore`, where `bitwise_correct` proves
    `denote (bitwiseBody op cost)` pushes the limb-wise combination of the two
    stack operands. Emit is byte-identical to the previous hand-written asm. -/
def bitwiseHandler (name : String) (cost : Nat) (op : String) : String :=
  let bop : AsmCore.BitOp := if op == "orr" then .orr else if op == "eor" then .eor else .and
  hdr name ++ (AsmCore.bitwiseBody bop cost).emitDerived

/-- Comparison: result is 0/1 in low limb. Cond is ARM64 code following a
    `subs` chain that computes (top - nos).

    **Only C-flag conditions (lo/hs) and N!=V conditions (lt/ge) propagate
    correctly** across the chained sbcs. Z-dependent conditions (eq/ne/hi/ls/
    gt/le) are unreliable: Z after sbcs reflects only the highest limb, not
    the overall 256-bit result. EQ/GT/SGT use their own handlers that
    sidestep this. -/
def cmpHandler (name : String) (cost : Nat) (cond : String) : String :=
  hdr name ++ (AsmCore.cmpBody false (if cond == "lt" then .lt else .lo) cost).emitDerived

/-- Like cmpHandler, but swaps operands so `cond` is applied to (nos - top)
    instead of (top - nos). Lets us use the reliable `lo`/`lt` conditions
    for GT/SGT (where "top > nos" = "nos < top"). -/
def cmpHandlerSwapped (name : String) (cost : Nat) (cond : String) : String :=
  hdr name ++ (AsmCore.cmpBody true (if cond == "lt" then .lt else .lo) cost).emitDerived

/-- EQ: pop top + nos, push 1 if equal else 0.
    Cannot use the cmpHandler subs-chain because Z after sbcs reflects only
    the last limb. OR the per-limb XOR results and ISZERO that. -/
def eqHandler (cost : Nat) : String :=
  hdr "eq" ++ (AsmCore.eqBody cost).emitDerived

/-- ISZERO: pop top, push 1 if top = 0 else 0. Stack stays at same depth. -/
def iszeroHandler (cost : Nat) : String :=
  hdr "iszero" ++ (AsmCore.iszeroBody cost).emitDerived

/-- NOT: bitwise complement of top. Stack depth unchanged. -/
def notHandler (cost : Nat) : String :=
  hdr "not" ++ (AsmCore.notBody cost).emitDerived

/-- CLZ (EIP-7939, Osaka+): count leading zeros of top. Stack depth unchanged. -/
def clzHandler (cost : Nat) : String :=
  hdr "clz" ++ (AsmCore.clzBody cost).emitDerived

/-- POP: discard top; NOS becomes new TOS. -/
def popHandler (cost : Nat) : String :=
  hdr "pop" ++ (AsmCore.popBody cost).emitDerived

/-- STOP: set halted=1. Spec leaves pc unchanged; the trampoline
    pre-incremented it (mimicking `next`), so we undo that here.
    Then branch to sync_and_ret. -/
def stopHandler : String :=
  hdr "stop" ++ AsmCore.stopBody.emit

/-- JUMPDEST: no-op; pc was already pre-incremented by `next`. -/
def jumpdestHandler (cost : Nat) : String :=
  hdr "jumpdest" ++ (AsmCore.jumpdestBody cost).emitDerived

/-- INVALID: brk. Caller debugs. -/
def invalidHandler : String :=
  -- INVALID and any undefined opcode consume all remaining gas and halt
  -- with reverted=1 (no refund). Same shape as the OOG fault stub.
  hdr "invalid" ++ AsmCore.invalidBody.emit

/-- Push U256 from a struct field. Pre-condition: x20=state, x21=pc, etc.
    Post: new TOS in x6-x9, old TOS shuffled to NOS regs, old NOS written
    to memory (since the stack invariant requires stack[sp-2] = NOS regs
    after sp increment, which means the old TOS at memory[sp-1] becomes
    the new NOS in memory[sp_new-2] = memory[sp_old-1], i.e., no move). -/
def pushU256FromField (name : String) (cost : Nat) (offset : Nat) : String :=
  hdr name ++ (AsmCore.envU256Body offset cost).emitDerived

/-- PREVRANDAO (0x44, formerly DIFFICULTY): pushes state.prev_randao (offset 512). -/
def prevrandaoHandler (cost : Nat) : String := pushU256FromField "prevrandao" cost 512

/-- BLOBBASEFEE (0x4a, Cancun, EIP-7516): pushes state.blob_base_fee (offset 568), the
    block's fake_exponential(excess_blob_gas) the host writes once per block. -/
def blobbasefeeHandler (cost : Nat) : String :=
  pushU256FromField "blobbasefee" cost Offset.blobBaseFee

/-- BLOBHASH (0x49, Cancun, EIP-4844): pops the index, pushes the tx's versioned hash at
    that index from the table at state.blob_hashes (offset 552, count at 560), or 0. -/
def blobhashHandler (cost : Nat) : String :=
  hdr "blobhash" ++ (AsmCore.blobhashBody cost).emitDerived

/-- Push a u64 from a struct field as U256 (high limbs zero). -/
def pushU64FromField (name : String) (cost : Nat) (offset : Nat) : String :=
  hdr name ++ (AsmCore.envU64Body offset cost).emitDerived

/-- PC: pushes the *opcode* pc (i.e., x21 - 1, since `next` pre-incremented). -/
-- PC pushes (pc of the PC op) = x21-1. Emitted from AsmCore (`pc_correct`).
def pcHandler (cost : Nat) : String :=
  hdr "pc" ++ (AsmCore.pcBody cost).emitDerived

/-- GAS: pushes (gasLeft - cost) after charging cost. Emitted from AsmCore
    (`gas_correct`); the gas charge goes through the OOG-checked combinator. -/
def gasHandler (cost : Nat) : String :=
  hdr "gas" ++ (AsmCore.gasBody cost).emitDerived

/-- MSIZE: pushes mp (always loaded from memory; not cached). -/
-- MSIZE returns the *aligned* memory size — `memory_size` (#48, kept aligned by
-- memExpandInto), NOT the raw high-water mark `mp` (#24). This handler is now
-- emitted from the typed DSL `Evm.CL.AsmCore`, where `AsmCore.msize_correct`
-- PROVES `denote (msizeBody cost)` pushes `fields .memSize` (and
-- `msize_bug_rejected` shows the `mp` version violates the spec). Emit is
-- byte-identical to the previous hand-written asm.
def msizeHandler (cost : Nat) : String :=
  hdr "msize" ++ (AsmCore.msizeBody cost).emitDerived

/-- SSTORE: arena-based journal bump. Pop slot (top) + val (nos);
    bump journal_count; write JournalEntry.

    `sentry` is the EIP-1706/EIP-2200 trip-wire: refuse the SSTORE
    outright when `gasLeft ≤ sentry`, BEFORE the cb computes the real
    cost (EELS Istanbul+ `sstore` lines 66-67). 0 = no check —
    pre-Istanbul forks (including Constantinople's EIP-1283, which
    shipped without EIP-1706) use the `_nosentry` variant. -/
def sstoreHandler (sentry : Nat) : String :=
  -- static-guard, optional EIP-1706 gas sentry, cb->sstore (returns gas),
  -- journal entry (type 0), pop slot+val, reload. See AsmCore.sstoreBody.
  hdr "sstore" ++ (AsmCore.sstoreBody sentry).emitDerived

/-- Signed comparison: like cmpHandler but uses signed condition code.
    The `subs` chain on 256-bit values gives correct N+Z flags; for
    signed compare we use lt/gt (signed less/greater). -/
def signedCmpHandler (name : String) (cost : Nat) (cond : String) : String :=
  cmpHandler name cost cond

/-! ## C-helper wrappers

Handlers that delegate to pure-compute C functions in c/eita_compute.c.
Convention: handler stages operands into stack scratch space, sets up x0/x1/x2/x3
with pointers to result/operands, calls the helper, then loads result back. -/

-- Stack scratch space: we reserve 32 bytes on SP for the result, write
-- operand pointers to existing EVM-stack memory slots, save x29/x30 for
-- the bl, set up x0/x1/x2 with pointers, bl helper, load result, restore.

/-- Binary compute helper: pop top + nos, call helper(result, top, nos),
    push result. cost is gas; helper_name is e.g. "_eita_helper_mul". -/
def binComputeHandler (name : String) (cost : Nat) (helperName : String) : String :=
  hdr name ++ (AsmCore.binComputeBody helperName cost).emitDerived

/-- CALLDATALOAD: pop off, push 32 BE bytes from calldata. Pure replace TOS. -/
def calldataloadHandler (cost : Nat) : String :=
  hdr "calldataload" ++ (AsmCore.calldataloadBody cost).emitDerived

/-- 3-pop helper that calls a C function with (state, dst, src, len).
    Result is written to memory side-effect via the helper; just pop. -/
def stateTernaryHandler (name : String) (cost : Nat) (helperName : String) : String :=
  hdr name ++ (AsmCore.copyBody helperName cost).emitDerived

/-- MCOPY (#270): like stateTernaryHandler but memexp covers max(dst+len,src+len)
    since the source is memory too. -/
def returndatacopyHandler (cost : Nat) : String :=
  hdr "returndatacopy" ++ (AsmCore.returndatacopyBody cost).emitDerived

def mcopyHandler (name : String) (cost : Nat) (helperName : String) : String :=
  hdr name ++ (AsmCore.mcopyBody helperName cost).emitDerived

/-! ## Callback-using handlers (vtable at EvmState.cb, offset 496)

    Callback offsets (cb table layout in evm_state.h):
      0   sload      (ctx, addr_ptr, slot_ptr, out_ptr)
      8   sstore     (ctx, addr_ptr, slot_ptr, val_ptr)
     16   tload      (ctx, slot_ptr, out_ptr)
     24   tstore     (ctx, slot_ptr, val_ptr)
     32   balance    (ctx, addr_ptr, out_ptr)
     40   ext_code_size  (ctx, addr_ptr, &u64)
     48   ext_code_hash  (ctx, addr_ptr, out_ptr)
     56   ext_code_copy  (ctx, addr_ptr, dst_ptr, src_off, len)
     64   block_hash     (ctx, blk_u64, out_ptr)
-/

/-- SLOAD: pop slot, call cb->sload(ctx, &state.address, &slot, &result), push.
    cb returns gas in x0; we charge it. -/
def sloadHandler : String :=
  hdr "sload" ++ AsmCore.sloadBody.emit

/-- TLOAD: pop slot, native eita_ts_tload(ts, &address, &slot, &result),
    push. Keyed (address, slot) per EIP-1153; ts = arena->tx_state.
    Charges the fixed Cancun 100 itself (chargedCost = 0, both tiers). -/
def tloadHandler : String :=
  hdr "tload" ++ AsmCore.tloadBody.emit

/-- BALANCE: pop addr, call cb->balance(ctx, &addr, &result), push. -/
def balanceHandler : String :=
  hdr "balance" ++ AsmCore.balanceBody.emit

/-- SELFBALANCE: no pop, call cb->balance(ctx, &address, &result), push. -/
def selfbalanceHandler (cost : Nat) : String :=
  hdr "selfbalance" ++ (AsmCore.selfbalanceBody cost).emitDerived

/-- EXTCODESIZE: pop addr, call cb->ext_code_size(ctx, &addr, &u64_result). -/
def extcodesizeHandler : String :=
  hdr "extcodesize" ++ AsmCore.extcodesizeBody.emit

/-- EXTCODEHASH: pop addr, call cb->ext_code_hash, push. -/
def extcodehashHandler : String :=
  hdr "extcodehash" ++ AsmCore.extcodehashBody.emit

/-- BLOCKHASH: pop n (U256), call cb->block_hash(ctx, &n, &result), push.
    Signature uses u256_t* for the key to match the spec's worldBlockHashByVal. -/
def blockhashHandler (cost : Nat) : String :=
  hdr "blockhash" ++ (AsmCore.blockhashBody cost).emitDerived

/-- EXTCODECOPY: pop addr, dst, src, len. Memory-side copy via callback. -/
def extcodecopyHandler : String :=
  -- 4-pop (addr, dst, src, len): memexp(dst+len) gas up front, then the
  -- ext_code_copy host cb (slot #56) writes code → memory and returns the
  -- access gas. See AsmCore.extcodecopyBody.
  hdr "extcodecopy" ++ (AsmCore.extcodecopyBody).emitDerived


/-! ## CALL family (host-callback recursive trampoline)

    STATICCALL stack (top → bottom):
      gas, addr, in_off, in_len, out_off, out_len      → success

    The handler:
      1. Syncs cached state (pc/gas/sp) to EvmState memory — sub-frame
         may need to inspect it, and we'll reload on return.
      2. Builds a CallParams struct on the local stack (128 bytes).
      3. Calls cb->call(ctx, &params, &result).
      4. Copies returndata back to memory[out_off..min(out_len, len)].
      5. Sets state.returndata to point at the sub-frame's output.
      6. Pops 6, pushes success (0 or 1).
      7. Reloads cached state (sp/gas may have changed via gas_used).

    Gas accounting is intentionally simplified for the MVP: we forward
    `gas` as requested (no 63/64 cap) and just subtract the sub-frame's
    `gas_used`. The 2929 warm/cold + base 700 cost are not added yet
    (item 1b). Audit will catch any drift if/when the spec tightens. -/

/-- Generic handler for the CALL family. `kind` selects the variant:
      0 = CALL          (7 stack args: gas, addr, value, in_off, in_len, out_off, out_len)
      1 = CALLCODE      (7 args, same as CALL)
      2 = DELEGATECALL  (6 args: no value; sub-frame inherits caller/value)
      3 = STATICCALL    (6 args: no value; staticp=1 in sub-frame)
    For with-value variants (kind 0/1), value is pulled from stack[sp-3].
    The handler structure is identical otherwise. The arg-position arithmetic +
    the whole body now live in `AsmCore.callFamilyBody`. -/
def callFamilyHandler (name : String) (kind : Nat) (staticpFlag : Nat) (withValue : Bool) : String :=
  -- memexp(max in/out range), build CallParams, cb->call, returndata→mem, pop
  -- args, push success, charge gas_used. See AsmCore.callFamilyBody.
  hdr name ++ (AsmCore.callFamilyBody name kind staticpFlag withValue).emitDerived

-- Convenience aliases using the parametric helper.
def callOp : String         := callFamilyHandler "call"         0 0 true
def callcodeOp : String     := callFamilyHandler "callcode"     1 0 true
def delegatecallOp : String := callFamilyHandler "delegatecall" 2 0 false

/-- SELFDESTRUCT: pop beneficiary address; mark frame for destruction at tx end.
    Invokes cb->selfdestruct(ctx, &state.address, &beneficiary). State-mutating,
    so guarded by staticGuard. Halts the current frame. -/
def selfdestructHandler (cost : Nat) : String :=
  -- static-guard, undo trampoline pc-inc, charge base cost, cb->selfdestruct
  -- (cold/new-account surcharge), halt, pop beneficiary. See AsmCore.selfdestructBody.
  hdr "selfdestruct" ++ (AsmCore.selfdestructBody cost).emitDerived

/-- CREATE: pop value, in_off, in_len. Deploy a contract using init code at
    memory[in_off..in_off+in_len]. Push deployed-contract address (or 0 on fail).
    Uses CallParams with kind=4 + cb->create. -/
def createHandler : String :=
  -- static-guard, build CallParams (kind=4, value/init-code/gas), cb->create,
  -- push created addr (0 on fail), pop 3 push 1, charge gas_used. See AsmCore.createBody.
  hdr "create" ++ AsmCore.createBody.emit

/-- CREATE2: like CREATE but with 32-byte salt for deterministic address. -/
def create2Handler : String :=
  hdr "create2" ++ AsmCore.create2Body.emit

/-! ## KECCAK256 (via C keccak helper) -/

/-- KECCAK256: pop off+len, hash memory[off..off+len], push 32-byte digest.
    Calls _eita_helper_keccak256(state, off_ptr, len_ptr, &result). -/
def keccak256Handler (cost : Nat) : String :=
  -- TOS = off (x6 low, x7/x8/x9 high), NOS = len (x10 low, x11/x12/x13 high).
  -- Spec fidelity (EELS computes memexp over the full Uint range): a len or off
  -- whose HIGH limbs are non-zero means the hashed range end ≥ 2^64, so the
  -- memory-expansion gas is unaffordable ⇒ OOG. The native helper only consumes
  -- limb[0], so without these checks KECCAK256(huge_off, huge_len) whose low
  -- limbs fit would silently charge a modest cost instead of OOGing as mainnet.
  -- Gas = 30 + 6·⌈len/32⌉ + memExpand(off+len). See AsmCore.keccak256Body.
  hdr "keccak256" ++ (AsmCore.keccak256Body cost).emitDerived

/-- EXP: same shape as binCompute but with variable gas
    (cost + byteCost * ceil(log256(e))). `byteCost` is the per-byte
    exponent fee — 10 Frontier, 50 from Spurious Dragon (EIP-160);
    the caller passes the fork's `Vm.Gas.expByte`.
    Computes ebytes from the exponent's MSB and charges accordingly. -/
def expHandler (cost byteCost : Nat) : String :=
  -- gas = cost + byteCost·ebytes (ebytes from exponent MSB via clz), then
  -- the exp C helper. See AsmCore.expBody.
  hdr "exp" ++ (AsmCore.expBody cost byteCost).emitDerived

/-- Ternary compute helper: pop top + nos + third, call helper(result, top, nos, third),
    push result. For ADDMOD/MULMOD. -/
def ternaryComputeHandler (name : String) (cost : Nat) (helperName : String) : String :=
  hdr name ++ (AsmCore.ternaryComputeBody helperName cost).emitDerived

/-! ## Memory ops (preallocated; quadratic gas calculation in handler) -/

/-- MLOAD: pop offset, push 32 bytes from memory[off..off+32] as U256
    (big-endian). Charges 3 + memory-expansion gas.
    Spec uses `MacroSpec.U256Ops.padMem` which models the in-bounds extension;
    we assume the host-allocated memory buffer is large enough.

    For now we read 32 bytes directly with bounds check via mp update;
    actual zero-padding past memory_size is not done (preallocated buffer
    starts zero-initialized, so past-end reads naturally give 0 IF the
    buffer is large enough). -/
def mloadHandler (cost : Nat) : String :=
  hdr "mload" ++ (AsmCore.mloadBody cost).emitDerived

/-- MSTORE: pop offset (top), value (nos). Write 32 BE bytes to memory[off..off+32].
    sp -= 2; mp = max(mp, off+32); charge 3. -/
def mstoreHandler (cost : Nat) : String :=
  hdr "mstore" ++ (AsmCore.mstoreBody cost).emitDerived

/-- MSTORE8: pop offset (top), value (nos). Write low byte of value to memory[off]. -/
def mstore8Handler (cost : Nat) : String :=
  hdr "mstore8" ++ (AsmCore.mstore8Body cost).emitDerived

/-! ## Halt with output (RETURN/REVERT) -/

/-- RETURN: pop off+len, set output, set halted, branch to sync_and_ret.
    The output buffer is host-pre-allocated; we just record offset/size and
    let the host snapshot. For simplicity, write off+len into output_size
    field and output ptr = memory + off. -/
def returnHandler : String :=
  hdr "return" ++ AsmCore.returnBody.emit

/-- REVERT: like RETURN, but also sets reverted=1. -/
def revertHandler : String :=
  hdr "revert" ++ AsmCore.revertBody.emit

/-! ## JUMP / JUMPI -/

/-- JUMP: pop dest; require dest < code_size and code[dest] == 0x5b (JUMPDEST);
    pc = dest. Bypass trampoline pre-inc by setting pc directly. -/
def jumpHandler (cost : Nat) : String :=
  -- pop dest, bounds + JUMPDEST validate, set pc=dest, reload, charge.
  -- See AsmCore.jumpBody.
  hdr "jump" ++ (AsmCore.jumpBody cost).emitDerived

/-- JUMPI: pop dest + cond; if cond != 0 then JUMP semantics, else just bump pc.
    See AsmCore.jumpiBody. -/
def jumpiHandler (cost : Nat) : String :=
  hdr "jumpi" ++ (AsmCore.jumpiBody cost).emitDerived

/-- Invalid-jump trap. Per spec, JUMP/JUMPI to a non-JUMPDEST (or out of
    code bounds) is an exception that consumes all remaining gas. -/
def invalidJumpStub : String :=
  ".global _eita_invalid_jump\n" ++
  ".p2align 2\n" ++
  "_eita_invalid_jump:\n" ++
  "    b     _eita_oog\n"

/-! ## TSTORE (arena bump like SSTORE; entry_type = 1) + LOG-N -/

/-- TSTORE: pop slot + val. Per EELS/spec, transient storage is per-tx
    and NOT journaled (doesn't revert with frame revert). The native
    impl just pops; actual storage would go through a callback. -/
def tstoreHandler : String :=
  -- static-guard, pop slot+val, charge fixed Cancun 100 up front (OOG frame
  -- never journals), then eita_ts_tstore. See AsmCore.tstoreBody.
  hdr "tstore" ++ AsmCore.tstoreBody.emit

/-- LOG-N: arena log_count bump. Doesn't write log entry contents
    (audit doesn't compare log content); just records that one was made.
    Pops off + len + n topics; updates mp = max(mp, off+len). Charges
    `cost` (= 375 + 375*n). Static-context check (TODO).  -/
def logHandler (n cost : Nat) : String :=
  -- static-guard, gas=cost+8·len+memexp, bump log_count, mp, pop 2+n, reload,
  -- charge. See AsmCore.logBody.
  hdr s!"log{n}" ++ (AsmCore.logBody n cost).emitDerived

/-! ## PUSH-N (n = 0..32) -/

/-- PUSH-N for any n in [0, 32]: the immediate is ⌈n/8⌉ wide loads with a byte
    reverse each (`AsmCore.pushWideInstrs`), no per-byte branch; the bytes past
    code_size are the code image's zero padding (`PushWide`'s contract). -/
def pushHandler (n cost : Nat) : String :=
  -- overflow-guard, TOS→NOS, zero TOS, read n big-endian code bytes by wide
  -- loads, pc+=n, push, store, charge. See AsmCore.pushBody.
  hdr s!"push{n}" ++ (AsmCore.pushBody n cost).emitDerived

/-! ## DUP-n, SWAP-n (parametric) -/

/-- DUP-n: copy stack[sp-n] to top. n in [1, 16]. -/
def dupHandler (n cost : Nat) : String :=
  hdr s!"dup{n}" ++ (AsmCore.dupBody n cost).emitDerived

/-- SWAP-n: swap top with stack[sp-1-n]. n in [1, 16]. -/
def swapHandler (n cost : Nat) : String :=
  hdr s!"swap{n}" ++ (AsmCore.swapBody n cost).emitDerived

/-! ## Trampoline + dispatch table

    The per-op handler registry lives in `Evm.CL.ARM64.Interp`, which
    instantiates the shape emitters above with static costs drawn from
    `IR.Op.metadata` / `IR.Terminator.metadata`. -/

/-- `eita_run_one(state*, opcode_byte)`: set up cached state, dispatch
    to the requested opcode handler, sync back on exit. -/
def trampolineCode : String :=
  ".global _eita_run_one\n" ++
  ".p2align 2\n" ++
  "_eita_run_one:\n" ++
  -- Save callee-saved registers (we use x19-x28)
  "    stp   x29, x30, [sp, #-96]!\n" ++
  "    stp   x19, x20, [sp, #16]\n" ++
  "    stp   x21, x22, [sp, #32]\n" ++
  "    stp   x23, x24, [sp, #48]\n" ++
  "    stp   x25, x26, [sp, #64]\n" ++
  "    stp   x27, x28, [sp, #80]\n" ++
  -- x0 = state, x1 = opcode
  "    mov   x20, x0\n" ++
  "    ldr   x21, [x0, #0]\n" ++             -- pc
  "    ldr   x22, [x0, #8]\n" ++             -- gas
  "    ldr   x23, [x0, #16]\n" ++            -- sp
  "    ldr   x24, [x0, #32]\n" ++            -- stack base
  "    ldr   x26, [x0, #64]\n" ++            -- code base
  -- Load TOS into x6-x9 (if sp >= 1)
  "    cmp   x23, #1\n" ++
  "    b.lt  1f\n" ++
  "    sub   x14, x23, #1\n" ++
  "    add   x14, x24, x14, lsl #5\n" ++
  "    ldp   x6, x7, [x14]\n" ++
  "    ldp   x8, x9, [x14, #16]\n" ++
  "1:\n" ++
  -- Load NOS into x10-x13 (if sp >= 2)
  "    cmp   x23, #2\n" ++
  "    b.lt  2f\n" ++
  "    sub   x14, x23, #2\n" ++
  "    add   x14, x24, x14, lsl #5\n" ++
  "    ldp   x10, x11, [x14]\n" ++
  "    ldp   x12, x13, [x14, #16]\n" ++
  "2:\n" ++
  -- Pre-increment pc past the opcode being run (mimics `next`'s pre-inc)
  "    add   x21, x21, #1\n" ++
  -- Continuation = sync_and_ret
  "    adrp  x27, _eita_sync_and_ret@PAGE\n" ++
  "    add   x27, x27, _eita_sync_and_ret@PAGEOFF\n" ++
  -- Look up handler in the active fork's dispatch table
  -- (_eita_dispatch_ptr is set by _eita_set_fork; defaults to Cancun)
  "    adrp  x25, _eita_dispatch_ptr@PAGE\n" ++
  "    ldr   x25, [x25, _eita_dispatch_ptr@PAGEOFF]\n" ++
  "    ldr   x14, [x25, x1, lsl #3]\n" ++
  "    br    x14\n"

/-- `next`: production continuation. Fetches the opcode at x21, pre-increments
    pc, dispatches through the table. Handlers end with `br x27`; in production
    x27 = _eita_next, so the chain runs without per-opcode CFFI round-trip.

    If `cb->trace_step` (at vtable offset 112) is non-null, calls it with
    `(state, pc, gas, sp, opcode)` before dispatching. Tracing is opt-in
    via the CL callback table; production runs leave the slot null and pay
    only two loads + a cbz on the hot path. -/
def nextCode : String :=
  ".global _eita_next\n" ++
  ".p2align 2\n" ++
  "_eita_next:\n" ++
  -- Tracing fast path: check cb->trace_step at offset 112; null skips.
  "    ldr   x14, [x20, #496]\n" ++             -- cb table ptr
  "    ldr   x14, [x14, #112]\n" ++             -- cb->trace_step
  "    cbz   x14, 1f\n" ++
  -- Save live registers across the BL.
  "    stp   x29, x30, [sp, #-96]!\n" ++
  "    stp   x6, x7, [sp, #16]\n" ++
  "    stp   x8, x9, [sp, #32]\n" ++
  "    stp   x10, x11, [sp, #48]\n" ++
  "    stp   x12, x13, [sp, #64]\n" ++
  -- Arguments: (state, pc, gas, sp, opcode_byte).
  "    mov   x0, x20\n" ++
  "    mov   x1, x21\n" ++
  "    mov   x2, x22\n" ++
  "    mov   x3, x23\n" ++
  "    ldrb  w4, [x26, x21]\n" ++
  "    blr   x14\n" ++
  "    ldp   x6, x7, [sp, #16]\n" ++
  "    ldp   x8, x9, [sp, #32]\n" ++
  "    ldp   x10, x11, [sp, #48]\n" ++
  "    ldp   x12, x13, [sp, #64]\n" ++
  "    ldp   x29, x30, [sp], #96\n" ++
  "1:\n" ++
  "    ldrb  w14, [x26, x21]\n" ++
  "    add   x21, x21, #1\n" ++
  "    ldr   x14, [x25, x14, lsl #3]\n" ++
  "    br    x14\n"

/-- `eita_run(state*)`: production entry. Loads cached state, sets x27 = next,
    starts dispatch. Runs until STOP/RETURN/REVERT branches to sync_and_ret. -/
def runCode : String :=
  ".global _eita_run\n" ++
  ".p2align 2\n" ++
  "_eita_run:\n" ++
  "    stp   x29, x30, [sp, #-96]!\n" ++
  "    stp   x19, x20, [sp, #16]\n" ++
  "    stp   x21, x22, [sp, #32]\n" ++
  "    stp   x23, x24, [sp, #48]\n" ++
  "    stp   x25, x26, [sp, #64]\n" ++
  "    stp   x27, x28, [sp, #80]\n" ++
  -- Stash the post-prologue SP into x28. Fault stubs (OOG, stack
  -- under/overflow, static-violation, invalid-jump) restore `sp` from x28
  -- before branching to sync_and_ret, so handlers that pushed extra
  -- scratch frames (sload/sstore/tload/.../keccak/call/create) don't leave
  -- sync_and_ret reading callee-saved from the wrong offset.
  "    mov   x28, sp\n" ++
  "    mov   x20, x0\n" ++
  "    ldr   x21, [x0, #0]\n" ++
  "    ldr   x22, [x0, #8]\n" ++
  "    ldr   x23, [x0, #16]\n" ++
  "    ldr   x24, [x0, #32]\n" ++
  "    ldr   x26, [x0, #64]\n" ++
  "    cmp   x23, #1\n" ++
  "    b.lt  10f\n" ++
  "    sub   x14, x23, #1\n" ++
  "    add   x14, x24, x14, lsl #5\n" ++
  "    ldp   x6, x7, [x14]\n" ++
  "    ldp   x8, x9, [x14, #16]\n" ++
  "10:\n" ++
  "    cmp   x23, #2\n" ++
  "    b.lt  11f\n" ++
  "    sub   x14, x23, #2\n" ++
  "    add   x14, x24, x14, lsl #5\n" ++
  "    ldp   x10, x11, [x14]\n" ++
  "    ldp   x12, x13, [x14, #16]\n" ++
  "11:\n" ++
  "    adrp  x27, _eita_next@PAGE\n" ++
  "    add   x27, x27, _eita_next@PAGEOFF\n" ++
  "    adrp  x25, _eita_dispatch_ptr@PAGE\n" ++
  "    ldr   x25, [x25, _eita_dispatch_ptr@PAGEOFF]\n" ++
  "    ldrb  w14, [x26, x21]\n" ++
  "    add   x21, x21, #1\n" ++
  "    ldr   x14, [x25, x14, lsl #3]\n" ++
  "    br    x14\n"

/-- `sync_and_ret`: write cached state back to memory and return to the
    C caller (both eita_run_one and eita_run share this exit). -/
def syncAndRetCode : String :=
  ".global _eita_sync_and_ret\n" ++
  ".p2align 2\n" ++
  "_eita_sync_and_ret:\n" ++
  "    str   x21, [x20, #0]\n" ++
  "    str   x22, [x20, #8]\n" ++
  "    str   x23, [x20, #16]\n" ++
  -- Sync TOS to memory (if sp >= 1)
  "    cmp   x23, #1\n" ++
  "    b.lt  3f\n" ++
  "    sub   x14, x23, #1\n" ++
  "    add   x14, x24, x14, lsl #5\n" ++
  "    stp   x6, x7, [x14]\n" ++
  "    stp   x8, x9, [x14, #16]\n" ++
  "3:\n" ++
  "    cmp   x23, #2\n" ++
  "    b.lt  4f\n" ++
  "    sub   x14, x23, #2\n" ++
  "    add   x14, x24, x14, lsl #5\n" ++
  "    stp   x10, x11, [x14]\n" ++
  "    stp   x12, x13, [x14, #16]\n" ++
  "4:\n" ++
  -- Restore callee-saved and return
  "    ldp   x27, x28, [sp, #80]\n" ++
  "    ldp   x25, x26, [sp, #64]\n" ++
  "    ldp   x23, x24, [sp, #48]\n" ++
  "    ldp   x21, x22, [sp, #32]\n" ++
  "    ldp   x19, x20, [sp, #16]\n" ++
  "    ldp   x29, x30, [sp], #96\n" ++
  "    ret\n"

/-- Map of opcode byte (0..255) to registry handler name. Bytes not
    listed are undefined on every fork (→ invalid). -/
def opcodeNameMap : List (Nat × String) := [
    (0x00, "stop"),  (0x01, "add"),  (0x02, "mul"),  (0x03, "sub"),
    (0x04, "div"),   (0x05, "sdiv"), (0x06, "mod"),  (0x07, "smod"),
    (0x08, "addmod"),(0x09, "mulmod"), (0x0a, "exp"), (0x0b, "signextend"),
    (0x10, "lt"),    (0x11, "gt"),   (0x12, "slt"),  (0x13, "sgt"),
    (0x14, "eq"),    (0x15, "iszero"),
    (0x16, "and"),   (0x17, "or"),   (0x18, "xor"),  (0x19, "not"),
    (0x1a, "byte"),  (0x1b, "shl"),  (0x1c, "shr"),  (0x1d, "sar"),  (0x1e, "clz"),
    (0x20, "keccak256"),
    (0x30, "address"), (0x31, "balance"), (0x32, "origin"),  (0x33, "caller"),
    (0x34, "callvalue"), (0x35, "calldataload"),
    (0x36, "calldatasize"), (0x37, "calldatacopy"),
    (0x38, "codesize"), (0x39, "codecopy"),
    (0x3a, "gasprice"), (0x3b, "extcodesize"), (0x3c, "extcodecopy"),
    (0x3d, "returndatasize"), (0x3e, "returndatacopy"), (0x3f, "extcodehash"),
    (0x40, "blockhash"), (0x41, "coinbase"), (0x42, "timestamp"),
    (0x43, "number"),  (0x44, "prevrandao"), (0x45, "gaslimit"),
    (0x46, "chainid"), (0x47, "selfbalance"), (0x48, "basefee"),
    (0x49, "blobhash"), (0x4a, "blobbasefee"),
    (0x50, "pop"),     (0x51, "mload"),   (0x52, "mstore"),
    (0x53, "mstore8"), (0x54, "sload"),   (0x55, "sstore"),
    (0x56, "jump"),    (0x57, "jumpi"),
    (0x58, "pc"),      (0x59, "msize"),   (0x5a, "gas"),
    (0x5b, "jumpdest"), (0x5c, "tload"),  (0x5d, "tstore"),
    (0x5e, "mcopy"),   (0x5f, "push0"),
    (0xa0, "log0"), (0xa1, "log1"), (0xa2, "log2"), (0xa3, "log3"), (0xa4, "log4"),
    (0xf1, "call"), (0xf2, "callcode"), (0xf4, "delegatecall"), (0xfa, "staticcall"),
    (0xf0, "create"), (0xf5, "create2"),
    (0xf3, "return"), (0xfd, "revert"), (0xfe, "invalid"), (0xff, "selfdestruct")
  ] ++ (List.range 32 |>.map (fun i => (0x60 + i, s!"push{i+1}")))
    ++ (List.range 16 |>.map (fun i => (0x80 + i, s!"dup{i+1}")))
    ++ (List.range 16 |>.map (fun i => (0x90 + i, s!"swap{i+1}")))

/-- Emit a 256-entry dispatch table named `symbol`. `resolve` maps a
    registry handler name to the handler SYMBOL the entry should hold
    (the per-fork emitters route absent ops to `_eita_handler_invalid`
    and repriced ops to variant bodies). -/
def dispatchTableNamedSpec (symbol : String) (resolve : String → String) : String :=
  let entries : List String := (List.range 256).map fun b =>
    match opcodeNameMap.find? (fun (op, _) => op == b) with
    | some (_, nm) => s!"    .quad   {resolve nm}"
    | none         => "    .quad   _eita_handler_invalid"
  ".data\n" ++
  s!".global {symbol}\n" ++
  ".p2align 3\n" ++
  s!"{symbol}:\n" ++
  String.intercalate "\n" entries ++ "\n"

/-- The same table as directives (stage 4t). -/
def dispatchTableNamedInstrs (symbol : String) (resolve : String → String) : List Evm.CL.AsmCore.AInstr :=
  ([ .dataSection, .global symbol, .p2align3, .symLabel symbol ] : List Evm.CL.AsmCore.AInstr) ++
  (List.range 256).map fun b =>
    match opcodeNameMap.find? (fun (op, _) => op == b) with
    | some (_, nm) => Evm.CL.AsmCore.AInstr.quadSym (resolve nm)
    | none         => Evm.CL.AsmCore.AInstr.quadSym "_eita_handler_invalid"

def dispatchTableNamed (symbol : String) (resolve : String → String) : String :=
  Frame.text (dispatchTableNamedInstrs symbol resolve)

theorem dispatchTableNamed_derived :
    dispatchTableNamed "_t" (fun n => "_eita_handler_" ++ n) =
      dispatchTableNamedSpec "_t" (fun n => "_eita_handler_" ++ n) := by native_decide

/-- The `_eita_dispatch_ptr` cell. -/
def dispatchPtrInstrs : List Evm.CL.AsmCore.AInstr :=
  [ Evm.CL.AsmCore.AInstr.global "_eita_dispatch_ptr", .p2align3, .symLabel "_eita_dispatch_ptr", .quadSym "_eita_dispatch_table" ]

/-- The default (Cancun-registry) dispatch table, plus the mutable
    `_eita_dispatch_ptr` cell the trampoline/run/chunk entries load the
    active table from. `_eita_set_fork` repoints the cell; hosts that
    never call it run the default. -/
def dispatchTable (handlerNames : List (String × String)) (present : String → Bool := fun _ => true) : String :=
  dispatchTableNamed "_eita_dispatch_table" (fun opName =>
    match handlerNames.find? (fun (n, _) => n == opName) with
    | some _ => if present opName then s!"_eita_handler_{opName}" else "_eita_handler_invalid"
    | none   => "_eita_handler_invalid") ++
  Frame.text dispatchPtrInstrs

theorem dispatchPtr_derived :
    Frame.text dispatchPtrInstrs =
      ".global _eita_dispatch_ptr\n.p2align 3\n_eita_dispatch_ptr:\n    .quad   _eita_dispatch_table\n" := by
  native_decide

/-! ## Label suffixing (JIT flat-handler variants)

    The JIT tier (Phase 6b) emits a second copy of every op handler
    with static cost 0, so a chunk can pre-charge the sum at its head.
    A verbatim second copy would redefine the handler's symbol and its
    internal labels; instead we rename every label DEFINED in the body
    (and all references to it), leaving references to shared runtime
    symbols (_eita_oog, _eita_sync_and_ret, _eita_helper_*, ...) —
    which the body references but does not define — untouched. Numeric
    locals (`1:` / `1f`) resolve to the nearest definition, so verbatim
    duplication is safe for them. -/

private def isIdentChar (c : Char) : Bool := c.isAlphanum || c = '_'

/-- Labels defined in an asm body: `.global N` directives and
    non-numeric `N:` definition lines. -/
def definedLabels (body : String) : List String := Id.run do
  let mut out : List String := []
  for line in body.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.startsWith ".global " then
      out := (t.drop 8).trimAscii.toString :: out
    else if t.endsWith ":" then
      let n := (t.dropEnd 1).toString
      -- Assembler-local labels (`.Lfoo:`): the dot is not an ident
      -- char, so record the ident part — tokenized renaming then
      -- hits definition and references alike.
      let n := if n.startsWith "." then (n.drop 1).toString else n
      if n.length > 0 ∧ ¬ n.front.isDigit ∧ n.toList.all isIdentChar then
        out := n :: out
  return out

/-- Append `suffix` to every occurrence of every label defined in
    `body`. Whole-identifier tokenization, so a label that is a prefix
    of another is never corrupted. -/
def suffixDefinedLabels (body : String) (suffix : String) : String := Id.run do
  let names := definedLabels body
  let mut out := ""
  let mut cur := ""
  for c in body.toList do
    if isIdentChar c then
      cur := cur.push c
    else
      if cur ≠ "" then
        out := out ++ (if names.contains cur then cur ++ suffix else cur)
        cur := ""
      out := out.push c
  if cur ≠ "" then
    out := out ++ (if names.contains cur then cur ++ suffix else cur)
  return out

/-! ## The scaffolding is derived (stage 4r)

The strings above are the specification; `Evm.CL.Frame` holds the same code
as `AInstr` programs, and these identities are what let `emitWith` print the
programs instead. -/

theorem trampoline_derived : Frame.text Frame.runOne = trampolineCode := by native_decide
theorem run_derived : Frame.text Frame.run = runCode := by native_decide
theorem next_derived : Frame.text Frame.next = nextCode := by native_decide
theorem syncAndRet_derived : Frame.text Frame.syncAndRet = syncAndRetCode := by native_decide
theorem faultStubs_derived : Frame.text Frame.faultStubs = faultStubs := by native_decide
theorem invalidJump_derived : Frame.text Frame.invalidJump = invalidJumpStub := by native_decide

/-- Assemble the full handlers.S text from a handler registry
    (name → asm). The registry is built in `Evm.CL.ARM64.Interp`. The
    scaffolding is printed from its `Frame` programs. -/
def emitWith (handlers : List (String × String)) (present : String → Bool := fun _ => true) : String :=
  ".section __TEXT,__text,regular,pure_instructions\n" ++
  Frame.text Frame.runOne ++ "\n" ++
  Frame.text Frame.run ++ "\n" ++
  Frame.text Frame.next ++ "\n" ++
  Frame.text Frame.syncAndRet ++ "\n" ++
  Frame.text Frame.faultStubs ++ "\n" ++
  Frame.text Frame.invalidJump ++ "\n" ++
  String.intercalate "\n" (handlers.map Prod.snd) ++ "\n" ++
  dispatchTable handlers present

end Evm.CL.ARM64
