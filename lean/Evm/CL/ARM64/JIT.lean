/-
  Evm.CL.ARM64.JIT — per-chunk native emit (Phase 6, tier 2).

  Consumes `IR.Chunk` (the verified compiler's output) and emits one
  straight-line native function per chunk. Stage 6a is subroutine-
  threaded: every op site branches to the SAME audited handler the
  interp tier uses, with the continuation register pointing at the
  next inline site instead of the `next` dispatch loop. What the JIT
  removes is the per-op work `next` does — opcode fetch, dispatch-
  table load, indirect branch through a 256-entry table — while the
  handler bodies (and therefore the fixture audit that covers them)
  are shared verbatim.

  Stage 6b adds the chunk-head gas pre-charge (the spec-side contract
  `IR.execute` already states: charge the chunk's static gas up
  front). The head subtracts Σ `Interp.chargedCost` over the chunk's
  ops once, and op sites branch to the `_f` (flat, cost-0) handler
  variants, so per-op static `subs/b.lo` pairs vanish; dynamic gas
  (memory expansion, per-word/per-byte, callback-returned) still
  charges inside the shared bodies. Mid-chunk OOG thereby moves to
  the chunk head: an OOG frame halts with gas=0/reverted=1 as
  before, but its pc/stack at death differ from the interp tier —
  per-opcode accounting is explicitly out of scope (the audit
  compares exceptional halts on the flattened observables only).

  GAS is the one op that reads x22 mid-chunk. Its site compensates:
  add back rem = Σ chargedCost over the strictly-later ops before
  the handler (the interp charges GAS's own cost before pushing, so
  it is already paid in both tiers), subtract rem after. The IR's
  `Op.gas` literal is ignored — it is Frontier-schedule; the JIT
  sums the Cancun chargedCost itself.

  Register convention is identical to the interp tier (see
  Evm/CL/ARM64.lean). The one obligation each op site discharges is
  the `next` pre-increment contract: handlers expect
  `x21 = site_pc + 1` at entry (STOP subtracts one back, PUSH-N
  advances by N, RETURN keeps it). Since every op's pc is compile-
  time-known, the site materializes the literal.

  Terminators branch to their interp handler with
  `x27 = sync_and_ret`, so JUMP/JUMPI/RETURN/CALL-family exit to the
  host after the handler runs; the host reads the synced frame and
  dispatches the next chunk (or yields the sub-frame request through
  the same callbacks the interp tier uses). `fallthrough`/`endOfCode`
  have no opcode byte: the former syncs with pc = next chunk entry,
  the latter is the implicit STOP.

  Stage 6c folds constant-stack regions at emit time (see the
  "Constant folding" section): PUSH/PC-fed pure ops never emit a
  site; their results materialize as inline constant pushes at the
  first dynamic use. The folding evaluator IS `IR.execOp` run on a
  synthetic frame, so the fold inherits the verified semantics
  rather than re-deriving them.

  Stage 6d (issue #11 stage 2) generalizes 6c from constant to
  symbolic regions: any run of stack-pure ops — known values or not
  — executes at emit time over `SymExpr.SymStack` (whose `symStep`
  is proved sound against `IR.execOp` in Evm/IR/SymExpr.lean).
  Stack shuffles (PUSH/POP/DUP/SWAP/PC/JUMPDEST) emit no code at
  all; compute ops materialize once, at the region flush, as an
  expression DAG evaluated into an SP scratch frame — shared
  subtrees (DUP) compute once. Cheap ops inline the audited handler
  cores verbatim (same carry chains, same condition codes); hard
  ops `bl` the same C helpers the handlers call. The 6c constant
  folder still runs first, on the region's constant prefix, because
  it alone can evaluate EXP and fold its dynamic gas into the head
  pre-charge. Underflow is discharged with one region-entry depth
  check (`symStep`'s consumed count is monotone, and DUP peeks are
  folded into the same bound); overflow with one peak-net check, as
  in 6c. Both fault to the shared stubs, landing in the same
  flattened exceptional-halt observables the audit compares.

  Stage 6e (issue #11 stage 3) promotes constant-offset memory
  writes into the region: an MSTORE/MSTORE8 whose offset is a
  compile-time constant buffers (offset, value-DAG) instead of
  flushing. The region commits the writes at its flush: one merged
  memory-expansion charge (per-op deltas telescope to
  cost(maxEnd) − cost(entry size), and the charge stays relative to
  the RUNTIME memory size — the expansion-gas hazard never arises
  because every size reader, MLOAD/MSIZE/KECCAK256/GAS/dynamic-
  offset stores/yields/terminators, is a barrier that flushes
  first), one mp high-water update, then the buffered words in
  program order (replay order IS the alias handling; there is no
  alias analysis). This keeps the dominant Solidity mapping-slot
  idiom (MSTORE key→0x00, MSTORE slot→0x20, KECCAK256(0,64))
  inside one region.

  Later stages: hotness-gated runtime integration in the SBCL
  replay (6f).
-/

import Evm.CL.ARM64
import Evm.CL.Frame
import Evm.CL.AsmItems
import Evm.CL.ARM64.ChunkGas
import Evm.CL.ARM64.Interp
import Evm.CL.ARM64.JITEmit
import Evm.IR.Compile
import Evm.IR.Execute
import Evm.IR.SymExpr

namespace Evm.CL.ARM64.JIT

open Evm.IR

/-- Dispatch name of the interp handler implementing `op` — the same
    names `Evm.CL.ARM64.Interp.allHandlers` registers. Panics at emit
    time (never at run time) on ops with no handler. -/
def opName : Op → String
  | .add => "add" | .mul => "mul" | .sub => "sub" | .div => "div"
  | .sdiv => "sdiv" | .mod => "mod" | .smod => "smod"
  | .addmod => "addmod" | .mulmod => "mulmod"
  | .exp => "exp" | .signextend => "signextend"
  | .lt => "lt" | .gt => "gt" | .slt => "slt" | .sgt => "sgt"
  | .eq => "eq" | .iszero => "iszero"
  | .and_ => "and" | .or_ => "or" | .xor_ => "xor" | .not_ => "not"
  | .byte => "byte" | .shl => "shl" | .shr => "shr" | .sar => "sar"
  | .keccak256 => "keccak256"
  | .address => "address" | .balance => "balance" | .origin => "origin"
  | .caller => "caller" | .callvalue => "callvalue"
  | .calldataload => "calldataload" | .calldatasize => "calldatasize"
  | .calldatacopy => "calldatacopy"
  | .codesize => "codesize" | .codecopy => "codecopy"
  | .gasprice => "gasprice"
  | .extcodesize => "extcodesize" | .extcodecopy => "extcodecopy"
  | .returndatasize => "returndatasize" | .returndatacopy => "returndatacopy"
  | .extcodehash => "extcodehash"
  | .blockhash => "blockhash" | .coinbase => "coinbase"
  | .timestamp => "timestamp" | .number => "number"
  | .prevrandao => "prevrandao" | .gaslimit => "gaslimit"
  | .chainid => "chainid" | .selfbalance => "selfbalance"
  | .basefee => "basefee" | .blobhash => "blobhash"
  | .blobbasefee => "blobbasefee"
  | .pop => "pop" | .mload => "mload" | .mstore => "mstore"
  | .mstore8 => "mstore8"
  | .sload => "sload" | .sstore => "sstore"
  | .pc _ => "pc" | .msize => "msize" | .gas _ => "gas"
  | .jumpdest => "jumpdest"
  | .tload => "tload" | .tstore => "tstore" | .mcopy => "mcopy"
  | .push0 => "push0"
  | .push n _ => s!"push{n}"
  | .dup n => s!"dup{n}"
  | .swap n => s!"swap{n}"
  | .log n => s!"log{n}"
  | .clz => "clz"

/-- Bytecode width of an op: 1 + immediate bytes. -/
def opWidth : Op → Nat
  | .push n _ => 1 + n
  | _ => 1

/-- Dispatch name of the interp handler implementing a terminator.
    `none` for the byte-less terminators (`fallthrough`, `endOfCode`),
    which the chunk emitter open-codes. -/
def termName : Terminator → Option String
  | .stop => some "stop"
  | .ret => some "return"
  | .revert => some "revert"
  | .invalid => some "invalid"
  | .call .call => some "call"
  | .call .callcode => some "callcode"
  | .call .delegatecall => some "delegatecall"
  | .call .staticcall => some "staticcall"
  | .create .create => some "create"
  | .create .create2 => some "create2"
  | .selfdestruct => some "selfdestruct"
  | .jump _ => some "jump"
  | .jumpDynamic => some "jump"
  | .jumpi _ => some "jumpi"
  | .jumpiDynamic => some "jumpi"
  | .fallthrough _ => none
  | .endOfCode => none

def chunkSym (startPc : Nat) : String := s!"_eita_chunk_{startPc}"

/-! ## Constant folding (Stage 6c)

    A chunk region whose values all come from PUSH literals (or PC, or
    ops over those) is evaluated at emit time and materialized as
    inline constant pushes at the first point something dynamic needs
    the stack. The evaluator is not re-derived: each candidate op runs
    through the verified `IR.execOp` on a synthetic frame whose stack
    is exactly the known segment, so folding inherits the IR
    interpreter's semantics (div-by-zero, mod-0, two's-complement,
    EVM-order DUP/SWAP) wholesale. A stack-underflow error from
    `execOp` is the signal that the op consumes below the known
    segment — it degrades to an ordinary handler site, never a fault.

    Faulting stays observably identical: underflow checks happen in
    the emitted handler the op degrades to; overflow is checked at
    flush against the region's PEAK depth (the interp faults on the
    push that crosses 1024, even if later pops shrink the net), and
    out-of-gas from EXP's folded dynamic cost moves into the chunk-
    head pre-charge — all three land in the flattened exceptional-
    halt observables the audit compares. -/

/-- Ops the folder may evaluate at emit time: pure stack transforms,
    plus EXP (its dynamic gas is computed from the known exponent and
    added to the chunk-head pre-charge). Everything else — memory,
    state, env, GAS — flushes. -/
def foldable : Op → Bool
  | .push _ _ | .add | .mul | .sub | .div | .sdiv | .mod | .smod
  | .addmod | .mulmod | .exp | .signextend
  | .slt | .sgt | .eq | .iszero | .not_ | .byte
  | .and_ | .or_ | .xor_ | .lt | .gt | .pop
  | .dup _ | .swap _ | .pc _ | .jumpdest
  | .shl | .shr | .sar | .push0 => true
  | _ => false

/-- Fold one op over the known segment `ks` (head = top) by running
    the verified IR interpreter on a synthetic frame. `none` = emit a
    handler site instead. -/
def foldStep (ks : List Evm.U256) (op : Op) : Option (List Evm.U256) :=
  if !foldable op then none else
  let evm : Evm.Frontier.Vm.Evm :=
    { (default : Evm.Frontier.Vm.Evm) with stack := ks, gasLeft := 10 ^ 18 }
  match execOp evm op with
  | .ok e    => some e.stack
  | .error _ => none

/-- Dynamic gas of a folded op. Only EXP has any: `expByteCost f` per
    exponent byte (10, or 50 from EIP-160), the same coefficient the
    fork's exp handler body charges inline. (`execOp`'s own charge is
    Frontier-schedule, so it is not read.) -/
def foldDynCost (f : Evm.Fork) (ks : List Evm.U256) : Op → Nat
  | .exp => match ks with
    | _ :: e :: _ =>
      Interp.expByteCost f * Evm.Frontier.Vm.Instructions.expByteSize e.toNat
    | _ => 0
  | _ => 0

def limb (v : Evm.U256) (i : Nat) : Nat :=
  (v.toNat >>> (64 * i)) % (2 ^ 64)

/-! ## Symbolic regions (Stage 6d, issue #11 stage 2)

    A region is a maximal run of stack-pure ops. It executes at emit
    time over the verified symbolic stack: `SymExpr.symStep` (proved
    sound against `IR.execOp` by `symStep_sound`) when values are
    unknown, the 6c `foldStep` on the region's constant prefix when
    they are known (that path alone evaluates EXP and folds its
    dynamic gas into the head pre-charge). The region emits no code
    per op; everything materializes once at the flush.

    Flush layout (x23 = region-entry depth throughout, because region
    ops emitted nothing):
      1. depth checks — one `cmp x23, #need` underflow check (`need`
         bounds every pop and DUP peek; consumed is monotone, so the
         interp faults on some mid-region op iff entry depth < need)
         and one `cmp x23, #1025-maxNet` overflow check against the
         region's peak net growth (the interp faults on the push that
         crosses 1024 even if later pops shrink the net);
      2. a scratch frame of one 32-byte slot per DISTINCT DAG node
         (structural sharing from DUP computes once), evaluated in
         dependency (post)order: entry-stack leaves load from the
         canonical stack, which is intact until step 3; cheap ops
         inline the audited handler cores; hard ops `bl` the same
         C helpers the handlers call (slots live in memory, so the
         AAPCS caller-saved clobber is harmless); then (6e) buffered
         constant-offset memory writes commit: one merged expansion
         charge to the writes' max end, one mp update, the words in
         program order;
      3. the exit prefix stores to the canonical stack — only slots
         in [entry−consumed, entry+net) are touched, everything
         below is untouched-and-correct by `SymStack.denote`;
      4. x23 += net, then the TOS/NOS register cache reloads exactly
         like the `eita_run_chunk` prologue.
    Pure pops (exit prefix empty, consumed > 0) skip 2–3. A region
    that moved nothing and proved nothing emits nothing. -/

open Evm.IR.SymExpr

/-- Longest all-constant prefix of the symbolic stack, as values. -/
def constPrefix : List Expr → List Evm.U256
  | .const v :: tl => v :: constPrefix tl
  | _ => []

/-- A buffered constant-offset memory write (stage 6e): `off` is the
    compile-time byte offset, `val` the value DAG. `isByte` marks
    MSTORE8 (one byte: the value's low byte) vs MSTORE (32 BE bytes). -/
structure MemWrite where
  off    : Nat
  val    : Expr
  isByte : Bool

/-- One op against the open region. -/
inductive RegStep where
  /-- 6c constant fold over the const prefix; `dyn` = folded dynamic
      gas (EXP only), to be added to the chunk-head pre-charge. -/
  | fold (ss' : SymStack) (dyn : Nat)
  /-- Verified symbolic step. -/
  | sym (ss' : SymStack)
  /-- Constant-offset memory write absorbed into the region (6e). -/
  | store (ss' : SymStack) (w : MemWrite)
  /-- Not stack-pure (or `swap 0`): flush and emit a handler site. -/
  | flush

/-- MSTORE/MSTORE8 against the open region: absorb iff the offset is
    a compile-time constant whose end fits 64-bit address arithmetic
    (the handler OOGs on anything wider — wider degrades to it). -/
def regionStore (ss : SymStack) (isByte : Bool) : RegStep :=
  match ss.exprs with
  | .const off :: _ =>
      let width := if isByte then 1 else 32
      if off.toNat + width < 2 ^ 64 then
        let v := (ss.pop).2.pop
        .store v.2 ⟨off.toNat, v.1, isByte⟩
      else .flush
  | _ => .flush

/-- Step the region: constant folder first (EXP + cheaper at run
    time: the result is a literal, not a DAG), then the verified
    symbolic step. `foldStep`'s underflow-degrade contract means an
    op reaching below the constant prefix falls through to `symStep`
    rather than faulting. -/
def regionStep (f : Evm.Fork) (ss : SymStack) (op : Op) : RegStep :=
  match op with
  | .mstore  => regionStore ss false
  | .mstore8 => regionStore ss true
  | _ =>
    let ks := constPrefix ss.exprs
    match foldStep ks op with
    | some ks' =>
        .fold { ss with exprs := ks'.map .const ++ ss.exprs.drop ks.length }
              (foldDynCost f ks op)
    | none =>
        match symStep op ss with
        | some ss' => .sym ss'
        | none     => .flush

structure Region where
  ss     : SymStack := {}
  /-- Entry-stack depth the region requires: max consumed count, plus
      DUP peeks beyond the explicit prefix (peek does not consume). -/
  need   : Nat := 0
  /-- Peak of (prefix length − consumed) after any op: the region's
      maximal net growth over the entry depth. -/
  maxNet : Int := 0
  /-- Buffered constant-offset memory writes, in program order (6e). -/
  writes : List MemWrite := []

def Region.step (r : Region) (op : Op) (ss' : SymStack) : Region :=
  let dupNeed := match op with
    | .dup n =>
        if n > r.ss.exprs.length
        then r.ss.consumed + n - r.ss.exprs.length else 0
    | _ => 0
  { r with
    ss     := ss'
    need   := max r.need (max ss'.consumed dupNeed)
    maxNet := max r.maxNet ((ss'.exprs.length : Int) - ss'.consumed) }

/-- `xreg ← sp + 32*slot`. -/
private def spAddr (xreg : String) (slot : Nat) : String :=
  let off := 32 * slot
  if off ≤ 4095 then s!"    add   {xreg}, sp, #{off}\n"
  else movImm xreg off ++ s!"    add   {xreg}, sp, {xreg}\n"

/-- Load scratch slot into the quad at x{lo}..x{lo+3} (lo ∈ {6, 10}). -/
private def loadSlot (lo : Nat) (slot : Nat) : String :=
  spAddr "x14" slot ++
  s!"    ldp   x{lo}, x{lo+1}, [x14]\n" ++
  s!"    ldp   x{lo+2}, x{lo+3}, [x14, #16]\n"

/-- Store x6-x9 into a scratch slot. -/
private def storeSlot (slot : Nat) : String :=
  spAddr "x14" slot ++
  "    stp   x6, x7, [x14]\n" ++
  "    stp   x8, x9, [x14, #16]\n"

private def zeroHi : String :=
  "    mov   x7, #0\n" ++
  "    mov   x8, #0\n" ++
  "    mov   x9, #0\n"

/-! Inline cores: a = x6-x9, b = x10-x13, result → x6-x9. Verbatim
    copies of the audited handler cores — same carry chains, and only
    the borrow (`lo`) / signed (`lt`) condition codes that survive a
    chained `sbcs` (Z reflects just the last limb; EQ has its own
    XOR/ORR core, exactly like `eqHandler`). -/

private def addCore : String :=
  "    adds  x6, x6, x10\n" ++
  "    adcs  x7, x7, x11\n" ++
  "    adcs  x8, x8, x12\n" ++
  "    adc   x9, x9, x13\n"

private def subCore : String :=
  "    subs  x6, x6, x10\n" ++
  "    sbcs  x7, x7, x11\n" ++
  "    sbcs  x8, x8, x12\n" ++
  "    sbc   x9, x9, x13\n"

private def bitCore (op : String) : String :=
  s!"    {op}   x6, x6, x10\n" ++
  s!"    {op}   x7, x7, x11\n" ++
  s!"    {op}   x8, x8, x12\n" ++
  s!"    {op}   x9, x9, x13\n"

private def notCore : String :=
  "    mvn   x6, x6\n" ++
  "    mvn   x7, x7\n" ++
  "    mvn   x8, x8\n" ++
  "    mvn   x9, x9\n"

private def isZeroCore : String :=
  "    orr   x14, x6, x7\n" ++
  "    orr   x15, x8, x9\n" ++
  "    orr   x14, x14, x15\n" ++
  "    cmp   x14, #0\n" ++
  "    cset  x6, eq\n" ++ zeroHi

private def eqCore : String :=
  "    eor   x14, x6, x10\n" ++
  "    eor   x15, x7, x11\n" ++
  "    orr   x14, x14, x15\n" ++
  "    eor   x15, x8, x12\n" ++
  "    orr   x14, x14, x15\n" ++
  "    eor   x15, x9, x13\n" ++
  "    orr   x14, x14, x15\n" ++
  "    cmp   x14, #0\n" ++
  "    cset  x6, eq\n" ++ zeroHi

/-- Compare core: `swapped` compares (b ? a) instead of (a ? b), so
    GT/SGT use the reliable `lo`/`lt` conditions (see cmpHandler). -/
private def cmpCore (swapped : Bool) (cond : String) : String :=
  let a := ["x6", "x7", "x8", "x9"]
  let b := ["x10", "x11", "x12", "x13"]
  let (l, r) := if swapped then (b, a) else (a, b)
  s!"    subs  xzr, {l[0]!}, {r[0]!}\n" ++
  s!"    sbcs  xzr, {l[1]!}, {r[1]!}\n" ++
  s!"    sbcs  xzr, {l[2]!}, {r[2]!}\n" ++
  s!"    sbcs  xzr, {l[3]!}, {r[3]!}\n" ++
  s!"    cset  x6, {cond}\n" ++ zeroHi

def exprKids : Expr → List Expr
  | .const _ | .stackAt _ => []
  | .isZero a | .not_ a => [a]
  | .addmod a b n | .mulmod a b n => [a, b, n]
  | .add a b | .mul a b | .sub a b | .div a b | .sdiv a b
  | .mod_ a b | .smod_ a b | .signExtend a b
  | .lt a b | .gt a b | .slt a b | .sgt a b | .eq_ a b
  | .and_ a b | .or_ a b | .xor_ a b
  | .byte_ a b | .shl_ a b | .shr_ a b | .sar_ a b => [a, b]

/-- Postorder slot assignment over the exit DAG, deduplicated by
    structural equality (DUP sharing computes once). Children precede
    parents, so evaluating slots in order satisfies dependencies. Total
    (structural): the kids are collected first, in `exprKids` order, then
    `e` is appended unless present. -/
def collectSlots (acc : List Expr) (e : Expr) : List Expr :=
  if acc.contains e then acc
  else
    let acc' := match e with
      | .const _ | .stackAt _ => acc
      | .isZero a | .not_ a => collectSlots acc a
      | .addmod a b n | .mulmod a b n => collectSlots (collectSlots (collectSlots acc a) b) n
      | .add a b | .mul a b | .sub a b | .div a b | .sdiv a b
      | .mod_ a b | .smod_ a b | .signExtend a b
      | .lt a b | .gt a b | .slt a b | .sgt a b | .eq_ a b
      | .and_ a b | .or_ a b | .xor_ a b
      | .byte_ a b | .shl_ a b | .shr_ a b | .sar_ a b => collectSlots (collectSlots acc a) b
    acc' ++ [e]

/-- Constructor tag + leaf payload for the structural-CSE key. Internal nodes
    have payload 0 (their identity is the tag + child slots); leaves carry the
    const value / entry-stack depth so `const 5` and `const 7` don't merge. -/
private def exprCtor : Expr → Nat
  | .const _ => 0 | .stackAt _ => 1
  | .add .. => 2 | .mul .. => 3 | .sub .. => 4 | .div .. => 5 | .sdiv .. => 6
  | .mod_ .. => 7 | .smod_ .. => 8 | .addmod .. => 9 | .mulmod .. => 10
  | .signExtend .. => 11 | .lt .. => 12 | .gt .. => 13 | .slt .. => 14
  | .sgt .. => 15 | .eq_ .. => 16 | .isZero .. => 17 | .and_ .. => 18
  | .or_ .. => 19 | .xor_ .. => 20 | .not_ .. => 21 | .byte_ .. => 22
  | .shl_ .. => 23 | .shr_ .. => 24 | .sar_ .. => 25
private def exprPayload : Expr → Nat
  | .const v => v.toNat | .stackAt n => n | _ => 0

/-- Postorder numbering of the exit DAG with **structural CSE** — the linear
    realization of the pure `collectSlots`/`==` spec. `symStep` shares DUP'd
    subtrees physically, but recomputation (e.g. a contract building `x*x` twice
    via separate ops) yields address-distinct, structurally-EQUAL subtrees. A
    structural `==`/`hash` walk is 2^k for a `(DUP1 MUL)^k` DAG (it re-walks the
    DAG as a tree), so we key TWO memos: `ptrMemo` (USize → slot) keeps the walk
    linear in allocated nodes; `structMemo` ((ctor, payload, child-slots) → slot)
    collapses structurally-equal subtrees to ONE slot — O(1) per node because the
    children are already numbered. With this, the unsafe impl matches the pure
    `dagSlots` exactly (it too dedups by `==`), where before it left duplicate
    slots for equal-but-unshared subtrees (redundant evalNode emission). -/
private unsafe def dagSlotsGo (e : Expr) :
    StateM (Std.HashMap USize Nat × Std.HashMap (Nat × Nat × List Nat) Nat
            × Array Expr) Nat := do
  let addr := ptrAddrUnsafe e
  match (← get).1.get? addr with
  | some i => pure i
  | none =>
      let kids ← (exprKids e).mapM dagSlotsGo
      let key : Nat × Nat × List Nat := (exprCtor e, exprPayload e, kids)
      match (← get).2.1.get? key with
      | some i => modify (fun s => (s.1.insert addr i, s.2)); pure i   -- CSE hit
      | none =>
          modifyGet fun s =>
            let n := s.2.2.size
            (n, (s.1.insert addr n, (s.2.1.insert key n, s.2.2.push e)))

private unsafe def dagSlotsImpl (roots : List Expr) :
    Array Expr × (Expr → Nat) :=
  let st := (roots.forM fun e => discard (dagSlotsGo e)).run ({}, {}, #[]) |>.2
  (st.2.2, fun e => (st.1.get? (ptrAddrUnsafe e)).getD 0)

/-- Reference semantics (never executed): the structural-dedup path.
    `implemented_by` swaps in the linear pointer-memoized version;
    both assign every root and child a slot computed before use, which
    is the only property `emitRegionFlush` needs. -/
@[implemented_by dagSlotsImpl]
def dagSlots (roots : List Expr) : Array Expr × (Expr → Nat) :=
  let slots := roots.foldl collectSlots []
  (slots.toArray, fun e => (slots.findIdx? (· == e)).getD 0)

/-- Emit code computing one DAG node into its scratch slot. -/
private def evalNode (idx : Expr → Nat) (e : Expr) : String :=
  let me := idx e
  let bin (core : String) (a b : Expr) : String :=
    loadSlot 6 (idx a) ++ loadSlot 10 (idx b) ++ core ++ storeSlot me
  let un (core : String) (a : Expr) : String :=
    loadSlot 6 (idx a) ++ core ++ storeSlot me
  let call2 (h : String) (a b : Expr) : String :=
    spAddr "x0" me ++ spAddr "x1" (idx a) ++ spAddr "x2" (idx b) ++
    s!"    bl    {h}\n"
  let call3 (h : String) (a b c : Expr) : String :=
    spAddr "x0" me ++ spAddr "x1" (idx a) ++ spAddr "x2" (idx b) ++
    spAddr "x3" (idx c) ++ s!"    bl    {h}\n"
  match e with
  | .const v =>
      movImm "x6" (limb v 0) ++ movImm "x7" (limb v 1) ++
      movImm "x8" (limb v 2) ++ movImm "x9" (limb v 3) ++
      storeSlot me
  | .stackAt k =>
      -- Entry slot k (0 = entry TOS): canonical at x24 + (x23-1-k)*32;
      -- the entry stack is intact until the exit-store phase.
      s!"    sub   x14, x23, #{k + 1}\n" ++
      "    add   x14, x24, x14, lsl #5\n" ++
      "    ldp   x6, x7, [x14]\n" ++
      "    ldp   x8, x9, [x14, #16]\n" ++
      storeSlot me
  | .add a b        => bin addCore a b
  | .sub a b        => bin subCore a b
  | .and_ a b       => bin (bitCore "and") a b
  | .or_ a b        => bin (bitCore "orr") a b
  | .xor_ a b       => bin (bitCore "eor") a b
  | .lt a b         => bin (cmpCore false "lo") a b
  | .gt a b         => bin (cmpCore true  "lo") a b
  | .slt a b        => bin (cmpCore false "lt") a b
  | .sgt a b        => bin (cmpCore true  "lt") a b
  | .eq_ a b        => bin eqCore a b
  | .isZero a       => un isZeroCore a
  | .not_ a         => un notCore a
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

/-- Merged memory-expansion charge for the region's buffered writes:
    the inline `memExpandInto` logic with the cross-image `b.cond`
    faults rewritten as branch-arounds (this code lives in the chunk
    image; the stubs do not). One charge to `maxEnd` equals the
    interp's per-op deltas: expansion cost is a function of the word
    count alone and the size is monotone, so the deltas telescope —
    and the charge stays relative to the RUNTIME entry memory size.
    Clobbers x0, x14-x16, flags. -/
private def memExpandFlush (maxEnd : Nat) : String :=
  movImm "x0" maxEnd ++
  "    ldr   x14, [x20, #56]\n" ++          -- memory_cap
  "    cmp   x0, x14\n" ++
  "    b.ls  5f\n" ++
  "    b     _eita_oog\n" ++
  "5:\n" ++
  "    add   x14, x0, #31\n" ++
  "    lsr   x14, x14, #5\n" ++             -- new_words
  "    ldr   x15, [x20, #48]\n" ++          -- memory_size (aligned)
  "    lsr   x15, x15, #5\n" ++             -- old_words
  "    cmp   x14, x15\n" ++
  "    b.ls  7f\n" ++
  "    mul   x16, x14, x14\n" ++
  "    add   x16, x14, x16, lsr #9\n" ++
  "    add   x16, x16, x14, lsl #1\n" ++    -- new_cost = 3w + w²/512
  "    mul   x14, x15, x15\n" ++
  "    add   x14, x15, x14, lsr #9\n" ++
  "    add   x14, x14, x15, lsl #1\n" ++    -- old_cost
  "    sub   x16, x16, x14\n" ++            -- delta
  "    subs  x22, x22, x16\n" ++
  "    b.hs  6f\n" ++
  "    b     _eita_oog\n" ++
  "6:\n" ++
  "    add   x14, x0, #31\n" ++
  "    lsr   x14, x14, #5\n" ++
  "    lsl   x14, x14, #5\n" ++
  "    str   x14, [x20, #48]\n" ++          -- memory_size = align(maxEnd)
  "7:\n"

/-- mp = max(mp, maxEnd) — the same raw-byte high-water the handlers
    keep per op; the max of the per-op maxes is the max of the ends. -/
private def mpUpdateFlush (maxEnd : Nat) : String :=
  movImm "x15" maxEnd ++
  "    ldr   x16, [x20, #24]\n" ++
  "    cmp   x15, x16\n" ++
  "    csel  x16, x15, x16, hi\n" ++
  "    str   x16, [x20, #24]\n"

/-- x14 ← memory base + constant offset. -/
private def memBaseAt (off : Nat) : String :=
  "    ldr   x14, [x20, #40]\n" ++
  (if off == 0 then ""
   else if off ≤ 4095 then s!"    add   x14, x14, #{off}\n"
   else movImm "x15" off ++ "    add   x14, x14, x15\n")

/-- Commit one buffered write from its value slot (the same BE byte
    order mstoreHandler writes; mstore8Handler's low-byte strb). -/
private def emitMemWrite (idx : Expr → Nat) (w : MemWrite) : String :=
  loadSlot 6 (idx w.val) ++
  memBaseAt w.off ++
  (if w.isByte then
    "    strb  w6, [x14]\n"
  else
    "    rev   x0, x9\n" ++
    "    rev   x1, x8\n" ++
    "    rev   x2, x7\n" ++
    "    rev   x3, x6\n" ++
    "    str   x0, [x14]\n" ++
    "    str   x1, [x14, #8]\n" ++
    "    str   x2, [x14, #16]\n" ++
    "    str   x3, [x14, #24]\n")

/-- Materialize a region at its end (numeric local labels keep this
    position-independent; see the module doc for the phase layout). -/
def emitRegionFlush (r : Region) : String := Id.run do
  let p := r.ss.exprs.length
  let c := r.ss.consumed
  let net : Int := (p : Int) - c
  let idle := p == 0 && c == 0 && r.writes.isEmpty
  if idle && r.need == 0 && r.maxNet ≤ 0 then return ""
  let mut s := ""
  -- 1. Depth checks. b.cond can't reach a cross-image stub, so branch
  --    around an unconditional b, as the chunk head does.
  if r.need > 1024 then
    -- The interp would fault on every possible entry depth.
    return "    b     _eita_stack_underflow\n"
  if r.need > 0 then
    s := s ++ s!"    cmp   x23, #{r.need}\n" ++
         "    b.hs  8f\n" ++
         "    b     _eita_stack_underflow\n" ++
         "8:\n"
  if r.maxNet > 0 then
    let lim := 1025 - r.maxNet
    if lim ≤ 0 then
      return s ++ "    b     _eita_stack_overflow\n"
    s := s ++ s!"    cmp   x23, #{lim}\n" ++
         "    b.lo  9f\n" ++
         "    b     _eita_stack_overflow\n" ++
         "9:\n"
  if idle then return s
  -- 2. Scratch frame + DAG evaluation (write values are roots too).
  let (slots, idx) := dagSlots (r.ss.exprs ++ r.writes.map (·.val))
  let n := slots.size
  if n > 0 then
    s := s ++ "    stp   x29, x30, [sp, #-16]!\n"
    s := s ++ (if 32 * n ≤ 4095 then s!"    sub   sp, sp, #{32 * n}\n"
               else movImm "x15" (32 * n) ++ "    sub   sp, sp, x15\n")
    for e in slots do
      s := s ++ evalNode idx e
    -- 2.5 Memory commit (6e): merged expansion charge (may OOG —
    --     the fault stub restores sp from x28, so the open frame is
    --     fine), mp high-water, then the words in program order.
    if !r.writes.isEmpty then
      let maxEnd := r.writes.foldl
        (fun m w => max m (w.off + if w.isByte then 1 else 32)) 0
      s := s ++ memExpandFlush maxEnd ++ mpUpdateFlush maxEnd
      for w in r.writes do
        s := s ++ emitMemWrite idx w
    -- 3. Exit-prefix stores (x23 still = entry depth; all entry-stack
    --    reads happened in phase 2).
    let mut m : Nat := 0
    for e in r.ss.exprs do
      s := s ++ loadSlot 6 (idx e)
      let d : Int := net - 1 - m
      s := s ++ (if d ≥ 0 then s!"    add   x14, x23, #{d}\n"
                 else s!"    sub   x14, x23, #{-d}\n")
      s := s ++ "    add   x14, x24, x14, lsl #5\n" ++
           "    stp   x6, x7, [x14]\n" ++
           "    stp   x8, x9, [x14, #16]\n"
      m := m + 1
    s := s ++ (if 32 * n ≤ 4095 then s!"    add   sp, sp, #{32 * n}\n"
               else movImm "x15" (32 * n) ++ "    add   sp, sp, x15\n")
    s := s ++ "    ldp   x29, x30, [sp], #16\n"
  -- 4. Depth update + TOS/NOS cache reload (run_chunk-prologue shape).
  if net > 0 then s := s ++ s!"    add   x23, x23, #{net}\n"
  else if net < 0 then s := s ++ s!"    sub   x23, x23, #{-net}\n"
  s := s ++ "    cmp   x23, #1\n" ++
       "    b.lt  8f\n" ++
       "    sub   x14, x23, #1\n" ++
       "    add   x14, x24, x14, lsl #5\n" ++
       "    ldp   x6, x7, [x14]\n" ++
       "    ldp   x8, x9, [x14, #16]\n" ++
       "8:\n" ++
       "    cmp   x23, #2\n" ++
       "    b.lt  9f\n" ++
       "    sub   x14, x23, #2\n" ++
       "    add   x14, x24, x14, lsl #5\n" ++
       "    ldp   x10, x11, [x14]\n" ++
       "    ldp   x12, x13, [x14, #16]\n" ++
       "9:\n"
  return s

/-- Set x27 (continuation) = sync_and_ret. GOT-indirect because the
    symbol lives in the handlers dylib, not this image — adrp@PAGE
    can't reach across images. -/
private def syncCont : String := Frame.text Frame.syncCont

/-- Instructions whose HANDLER reads the *instantaneous* `gas_left`, so the chunk-head
    pre-charge of strictly-later ops must be handed back before the handler runs and
    taken again afterwards.

    * `GAS` pushes `gas_left` (EELS `gas_left` after charging its own cost).
    * `SSTORE` carries the EIP-2200/EIP-1706 reentrancy sentry `gas_left <= 2300 → OOG`
      (EIP-1706; Istanbul+ — the pre-Istanbul `sstore_nosentry` body reads no gas, so
      compensating there is a harmless no-op).

    Every other op's semantics is a function of the stack, memory and world only, so
    pre-charging is invisible to it. THIS LIST IS THE OBLIGATION: an op added here
    without a compensated emission (or added to the IR with a gas-reading handler and
    NOT listed here) breaks `runChunk = fold execOp`, which is how Arc block 12857262
    turned a 2-gas margin into a reverted Uniswap v3 swap. -/
def observesGas : Op → Bool
  | .gas _  => true
  | .sstore => true
  | _       => false

/-! The chunk's three gas gadgets — head pre-charge, hand-back around an
    `observesGas` handler, and the re-take afterwards — live in
    `Evm.CL.ARM64.ChunkGas`, with a denotation and the refinement theorem that
    says the scheme charges exactly what per-op charging would
    (`compensation_refines`). Both emitters below go through those definitions,
    so there is one source for each gadget and the unchecked re-take that was
    the second JIT bug is not representable. -/

/-! ## The chunk emitter, once

`emitChunk` (text, assembled by clang at build time) and `emitChunkItems`
(machine code, assembled in-process at run time) used to be two copies of the
same algorithm: same region pre-pass, same body loop, same terminator cases,
differing only in which constructor each step produced. Two copies is how
`ChunkGas`'s `retake` ended up with a bare `sub` on one side only — the second
JIT gas bug — and the JIT is the path we actually run.

So the algorithm lives here once, parameterised by an output algebra. The two
outputs are instantiations; neither can drift from the other, because there is
nothing to keep in step.

The two paths are deliberately NOT byte-identical: `b <sym>` is four bytes
through the linker, while the in-process path has no linker and materialises an
absolute address in twenty (`BrSym`). That difference lives in the algebra, not
in the algorithm. -/

/-- What a chunk emitter needs from its output type: a monoid, plus one
    operation per step the algorithm takes. -/
structure ChunkOut (α : Type) where
  /-- the empty program -/
  nil      : α
  /-- concatenation -/
  cat      : α → α → α
  /-- chunk entry: `.global`/alignment/symbol, or just the label -/
  head     : Nat → α
  /-- `mov x21, #pc` — publish the pc the host will see -/
  setPc    : Nat → α
  /-- one of the three gas gadgets -/
  gas      : ChunkGas.GInstr → α
  /-- flush the symbolic region to the real stack; `uid` disambiguates the
      labels the byte path needs and the text path derives differently -/
  flush    : Nat → Region → α
  /-- `adr x27, <local label>` — the continuation an op site returns to -/
  adrCont  : String → α
  /-- a local label definition -/
  label    : String → α
  /-- an op site: enter a flat handler, which continues at the label after -/
  callSym  : String → α
  /-- tail-call an external handler symbol (a terminator) -/
  tailSym  : String → α
  /-- `br x27` — jump to the continuation already in x27 -/
  brCont   : α
  /-- load the sync-and-return continuation into x27 -/
  syncCont : α
  /-- `brk #0`, unreachable -/
  brk      : α

/-- The per-op state of `emitChunkGen`'s body pass. -/
structure BodySt (α : Type) where
  body : α
  pc   : Nat
  i    : Nat
  r    : Region
  uid  : Nat

/-- Region pre-pass: per-op dynamic cost of folded ops (EXP over a constant
    prefix only). Needed before emission because the head pre-charge and the
    GAS-site compensation both sum over it. Mirrors the body pass exactly
    (same `regionStep`). -/
def dynCosts (f : Evm.Fork) (ops : List Op) : List Nat :=
  (ops.foldl (fun (st : SymStack × List Nat) op =>
    match regionStep f st.1 op with
    | .fold ss' d  => (ss', d :: st.2)
    | .sym ss'     => (ss', 0 :: st.2)
    | .store ss' _ => (ss', 0 :: st.2)
    | .flush       => ({}, 0 :: st.2)) ({}, [])).2.reverse

/-- One op of the body pass: extend the open region, or flush it and emit a
    handler site. -/
def bodyStep {α : Type} (O : ChunkOut α) (f : Evm.Fork) (id : Nat) (costs dynAt : List Nat)
    (st : BodySt α) (op : Op) : BodySt α :=
  let st' : BodySt α :=
    match regionStep f st.r.ss op with
    | .fold ss' _  => { st with r := st.r.step op ss' }
    | .sym ss'     => { st with r := st.r.step op ss' }
    | .store ss' w => { st with r := { st.r.step op ss' with writes := st.r.writes ++ [w] } }
    | .flush =>
      let body := O.cat st.body (O.flush st.uid st.r)
      let body := O.cat body (O.setPc (st.pc + 1))
      -- One path for every op: hand the pre-charge back around the handlers
      -- that read gas (`observesGas`), then take it again.  `rem` is the static
      -- cost of strictly-later ops plus any folded dynamic cost the head
      -- already took.
      let rem := if observesGas op then (costs.drop (st.i + 1)).sum + (dynAt.drop (st.i + 1)).sum else 0
      let body := if rem != 0 then O.cat body (O.gas (ChunkGas.GInstr.handBack rem)) else body
      let ret := s!"Lj_{id}_{st.i}"
      let body := O.cat body (O.adrCont ret)
      let body := O.cat body (O.callSym s!"{Interp.handlerSymbol f (opName op)}_f")
      let body := O.cat body (O.label ret)
      let body := if rem != 0 then O.cat body (O.gas (ChunkGas.GInstr.retake rem s!"Lr_{id}_{st.i}")) else body
      { st with body := body, uid := st.uid + 1, r := {} }
  { st' with pc := st'.pc + opWidth op, i := st'.i + 1 }

/-- The algorithm. Both `emitChunk` and `emitChunkItems` are this, at different
    algebras. -/
def emitChunkGen {α : Type} (O : ChunkOut α) (f : Evm.Fork) (c : Chunk) : α :=
  let id := c.startPc
  -- `chargedCost` is fork-invariant: cb-driven ops charge 0 in every fork (the
  -- host cb carries the fork's cost) and every other op's static cost is
  -- pinned — `Interp.handlerSymbol` panics at emitARM64 time, across all
  -- dispatch-table forks, on any drift.
  let costs := c.ops.map Interp.chargedCost
  let dynAt := dynCosts f c.ops
  -- Body pass.
  let st := c.ops.foldl (bodyStep O f id costs dynAt)
    { body := O.nil, pc := c.startPc, i := 0, r := {}, uid := 0 }
  let body := O.cat st.body (O.flush st.uid st.r)
  let body := O.cat body O.syncCont
  let body := match c.term with
    | .fallthrough next =>
      -- No opcode byte: the frame simply continues at the next chunk entry. Sync
      -- with pc = next; halted stays clear.
      O.cat (O.cat body (O.setPc next)) O.brCont
    | .endOfCode =>
      -- Implicit STOP past the end of code. stopHandler undoes the
      -- pre-increment, leaving pc = the first pc past the last op — the chunk's
      -- endPc, matching IR.execTerm.
      O.cat (O.cat body (O.setPc (st.pc + 1))) (O.tailSym "_eita_handler_stop")
    | t =>
      match termName t with
      | some nm =>
        -- Terminators stay interp-tier; per-fork selection (e.g.
        -- selfdestruct_pre150) mirrors the dispatch tables.
        O.cat (O.cat body (O.setPc (st.pc + 1))) (O.tailSym (Interp.handlerSymbol f nm))
      | none => O.cat body O.brk   -- unreachable by the match above
  -- Head: pre-charge static gas + folded dynamic gas in one subs.
  let total := costs.sum + dynAt.sum
  let s := O.head id
  let s := if total > 0 then O.cat s (O.gas (ChunkGas.GInstr.charge total s!"Lg_{id}")) else s
  O.cat s body

/-- The text algebra: what clang assembles into the per-program `.S`. -/
def textOut : ChunkOut String where
  nil      := ""
  cat      := (· ++ ·)
  head id  := s!".global {chunkSym id}\n.p2align 2\n{chunkSym id}:\n"
  setPc n  := movImm "x21" n
  gas g    := g.emit
  flush _ r := emitRegionFlush r
  adrCont l := s!"    adr   x27, {l}\n"
  label l  := s!"{l}:\n"
  callSym sym := s!"    b     {sym}\n"
  tailSym sym := s!"    b     {sym}\n"
  brCont   := "    br    x27\n"
  syncCont := syncCont
  brk      := "    brk   #0\n"


/-! ## The algebra at `List AInstr` (stage 4s)

The text algebra above and the item algebra below were written twice, in two
vocabularies — the duplication the handler work retired (`Op.toAInstrs`). This
section is the chunk emitter written ONCE as `AInstr`; `emitChunk` prints it
and `emitChunkItems` lowers it through `AsmItems`. `textOut` stays as the
specification (`chunk_text_derived` gates the fixture corpus character for
character); the hand-written item algebra is gated bytes-identical and
retired. -/

section InstrEmit
open Evm.CL.AsmCore

def movImmA (r : Reg) (v : Nat) : List AInstr := movImmInstrs r v

def spAddrA (r : Reg) (slot : Nat) : List AInstr :=
  let off := 32 * slot
  if off ≤ 4095 then [.addSp r off] else movImmA r off ++ [.addSpReg r]

/-! ### The flush, target-generically (stage 4x)

The region flush is one algorithm over a few target choices: which registers
hold the right operand of a binary core (ARM64 caches NOS in x10-x13; x86-64
has no NOS registers and uses four temporaries), how an immediate is
materialised, how a scratch slot is addressed, how the scratch frame opens
and closes, how a fault symbol is reached, which registers carry a helper's
arguments and how it is called, the base-register store forms, and what the
flush reloads at its end. `FlushTarget` names those; `armFlush` is the ARM64
instance (its output is the stage-4s text, `chunk_text_derived` below) and
`Evm.CL.X86JIT.x86Flush` the x86-64 one. -/
structure FlushTarget where
  /-- the right operand's four limbs (lo → hi) -/
  rq          : Reg × Reg × Reg × Reg
  /-- materialise an immediate -/
  movImm      : Reg → Nat → List AInstr
  /-- the address of scratch slot `k` (32 bytes each, at sp) -/
  spAddr      : Reg → Nat → List AInstr
  /-- open / close the scratch frame of `n` slots -/
  frameOpen   : Nat → List AInstr
  frameClose  : Nat → List AInstr
  /-- jump to a fault symbol (`_eita_oog`, …) -/
  far         : String → List AInstr
  /-- a helper's argument registers: out, a, b, c -/
  helperArgs  : Reg × Reg × Reg × Reg
  /-- call a helper symbol -/
  call        : String → List AInstr
  /-- `str src, [base]` and `strb src, [base]` -/
  storeWord   : Reg → Reg → List AInstr
  storeByte   : Reg → Reg → List AInstr
  /-- the cache reload at the flush's end (run_chunk-prologue shape) -/
  cacheReload : List AInstr

/-- ARM64: TOS then NOS, each under its depth guard. -/
def armCacheReload : List AInstr :=
  [ .cmpImm .x23 1, .bcLbl .lt "8f", .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14,
    .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16, .label "8",
    .cmpImm .x23 2, .bcLbl .lt "9f", .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14,
    .ldpOff .x10 .x11 .x14 0, .ldpOff .x12 .x13 .x14 16, .label "9" ]

def armFlush : FlushTarget where
  rq := (.x10, .x11, .x12, .x13)
  movImm := movImmA
  spAddr := spAddrA
  frameOpen n :=
    [.stpFpLr] ++ (if 32 * n ≤ 4095 then [.spSub (32 * n)] else movImmA .x15 (32 * n) ++ [.spSubReg .x15])
  frameClose n :=
    (if 32 * n ≤ 4095 then [.spAdd (32 * n)] else movImmA .x15 (32 * n) ++ [.spAddReg .x15]) ++ [.ldpFpLr]
  far sym := [.bFar sym]
  helperArgs := (.x0, .x1, .x2, .x3)
  call h := [.blFar h]
  storeWord s b := [.strBase s b]
  storeByte s b := [.strbBase s b]
  cacheReload := armCacheReload

/-- The four limbs starting at `lo`: x6, or (for x10) the target's right quad. -/
def quadT (T : FlushTarget) : Reg → Reg × Reg × Reg × Reg
  | .x10 => T.rq
  | _    => (.x6, .x7, .x8, .x9)

def loadSlotT (T : FlushTarget) (lo : Reg) (slot : Nat) : List AInstr :=
  let (a, b, c, d) := quadT T lo
  T.spAddr .x14 slot ++ [.ldpOff a b .x14 0, .ldpOff c d .x14 16]

def storeSlotT (T : FlushTarget) (slot : Nat) : List AInstr :=
  T.spAddr .x14 slot ++ [.stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16]

def loadSlotA (lo : Reg) (slot : Nat) : List AInstr := loadSlotT armFlush lo slot
def storeSlotA (slot : Nat) : List AInstr := storeSlotT armFlush slot

def zeroHiA : List AInstr := [.movImm .x7 0, .movImm .x8 0, .movImm .x9 0]

/-- The binary cores over a right quad `(r0, r1, r2, r3)`; the left operand
    and the result are x6-x9. -/
def addCoreT (rq : Reg × Reg × Reg × Reg) : List AInstr :=
  let (r0, r1, r2, r3) := rq
  [.adds .x6 .x6 r0, .adcs .x7 .x7 r1, .adcs .x8 .x8 r2, .adc .x9 .x9 r3]
def subCoreT (rq : Reg × Reg × Reg × Reg) : List AInstr :=
  let (r0, r1, r2, r3) := rq
  [.subsReg .x6 .x6 r0, .sbcs .x7 .x7 r1, .sbcs .x8 .x8 r2, .sbc .x9 .x9 r3]
def bitCoreT (rq : Reg × Reg × Reg × Reg) (f : Reg → Reg → Reg → AInstr) : List AInstr :=
  let (r0, r1, r2, r3) := rq
  [f .x6 .x6 r0, f .x7 .x7 r1, f .x8 .x8 r2, f .x9 .x9 r3]
def notCoreA : List AInstr := [.mvn .x6 .x6, .mvn .x7 .x7, .mvn .x8 .x8, .mvn .x9 .x9]
def isZeroCoreA : List AInstr :=
  [.orr3 .x14 .x6 .x7, .orr3 .x15 .x8 .x9, .orr3 .x14 .x14 .x15, .cmpImm .x14 0, .cset .x6 .eq] ++ zeroHiA
/-- x14/x15 are scratch: the x86-64 right quad's first limb lives in x15, and
    it is consumed by the first `eor` before x15 is written. -/
def eqCoreT (rq : Reg × Reg × Reg × Reg) : List AInstr :=
  let (r0, r1, r2, r3) := rq
  [.eor3 .x14 .x6 r0, .eor3 .x15 .x7 r1, .orr3 .x14 .x14 .x15,
   .eor3 .x15 .x8 r2, .orr3 .x14 .x14 .x15, .eor3 .x15 .x9 r3,
   .orr3 .x14 .x14 .x15, .cmpImm .x14 0, .cset .x6 .eq] ++ zeroHiA
def cmpCoreT (rq : Reg × Reg × Reg × Reg) (swapped : Bool) (c : SetCond) : List AInstr :=
  let a : Reg × Reg × Reg × Reg := (.x6, .x7, .x8, .x9)
  let ((l0, l1, l2, l3), (r0, r1, r2, r3)) := if swapped then (rq, a) else (a, rq)
  [.subsZr l0 r0, .sbcsZr l1 r1, .sbcsZr l2 r2, .sbcsZr l3 r3, .cset .x6 c] ++ zeroHiA

def addCoreA : List AInstr := addCoreT armFlush.rq
def subCoreA : List AInstr := subCoreT armFlush.rq
def bitCoreA (f : Reg → Reg → Reg → AInstr) : List AInstr := bitCoreT armFlush.rq f
def eqCoreA : List AInstr := eqCoreT armFlush.rq
def cmpCoreA (swapped : Bool) (c : SetCond) : List AInstr := cmpCoreT armFlush.rq swapped c

def evalNodeT (T : FlushTarget) (idx : Expr → Nat) (e : Expr) : List AInstr :=
  let me := idx e
  let (o, a1, a2, a3) := T.helperArgs
  let bin (core : List AInstr) (a b : Expr) : List AInstr :=
    loadSlotT T .x6 (idx a) ++ loadSlotT T .x10 (idx b) ++ core ++ storeSlotT T me
  let un (core : List AInstr) (a : Expr) : List AInstr :=
    loadSlotT T .x6 (idx a) ++ core ++ storeSlotT T me
  let call2 (h : String) (a b : Expr) : List AInstr :=
    T.spAddr o me ++ T.spAddr a1 (idx a) ++ T.spAddr a2 (idx b) ++ T.call h
  let call3 (h : String) (a b c : Expr) : List AInstr :=
    T.spAddr o me ++ T.spAddr a1 (idx a) ++ T.spAddr a2 (idx b) ++ T.spAddr a3 (idx c) ++ T.call h
  match e with
  | .const v =>
      T.movImm .x6 (limb v 0) ++ T.movImm .x7 (limb v 1) ++
      T.movImm .x8 (limb v 2) ++ T.movImm .x9 (limb v 3) ++ storeSlotT T me
  | .stackAt k =>
      [.subImm .x14 .x23 (k + 1), .addLsl5 .x14 .x24 .x14,
       .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16] ++ storeSlotT T me
  | .add a b        => bin (addCoreT T.rq) a b
  | .sub a b        => bin (subCoreT T.rq) a b
  | .and_ a b       => bin (bitCoreT T.rq .and3) a b
  | .or_ a b        => bin (bitCoreT T.rq .orr3) a b
  | .xor_ a b       => bin (bitCoreT T.rq .eor3) a b
  | .lt a b         => bin (cmpCoreT T.rq false .lo) a b
  | .gt a b         => bin (cmpCoreT T.rq true  .lo) a b
  | .slt a b        => bin (cmpCoreT T.rq false .lt) a b
  | .sgt a b        => bin (cmpCoreT T.rq true  .lt) a b
  | .eq_ a b        => bin (eqCoreT T.rq) a b
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

def memBaseAtT (T : FlushTarget) (off : Nat) : List AInstr :=
  .ldrOff .x14 .x20 40 ::
  (if off == 0 then []
   else if off ≤ 4095 then [.addImm .x14 .x14 off]
   else T.movImm .x15 off ++ [.addReg .x14 .x14 .x15])

def memExpandFlushT (T : FlushTarget) (maxEnd : Nat) : List AInstr :=
  T.movImm .x0 maxEnd ++
  [ .ldrOff .x14 .x20 56, .cmpReg .x0 .x14, .blsLbl "5f" ] ++ T.far "_eita_oog" ++ [ .label "5",
    .addImm .x14 .x0 31, .lsrImm .x14 .x14 5,
    .ldrOff .x15 .x20 48, .lsrImm .x15 .x15 5,
    .cmpReg .x14 .x15, .blsLbl "7f",
    .mulReg .x16 .x14 .x14, .addLsr .x16 .x14 .x16 9, .addLsl .x16 .x16 .x14 1,
    .mulReg .x14 .x15 .x15, .addLsr .x14 .x15 .x14 9, .addLsl .x14 .x14 .x15 1,
    .subReg .x16 .x16 .x14,
    .subsReg .x22 .x22 .x16, .bcLbl .hs "6f" ] ++ T.far "_eita_oog" ++ [ .label "6",
    .addImm .x14 .x0 31, .lsrImm .x14 .x14 5, .lslImm .x14 .x14 5, .strOff .x14 .x20 48,
    .label "7" ]

def mpUpdateFlushT (T : FlushTarget) (maxEnd : Nat) : List AInstr :=
  T.movImm .x15 maxEnd ++
  [ .ldrOff .x16 .x20 24, .cmpReg .x15 .x16, .cselHi .x16 .x15 .x16, .strOff .x16 .x20 24 ]

def emitMemWriteT (T : FlushTarget) (idx : Expr → Nat) (w : MemWrite) : List AInstr :=
  loadSlotT T .x6 (idx w.val) ++ memBaseAtT T w.off ++
  (if w.isByte then T.storeByte .x6 .x14
   else [.rev .x0 .x9, .rev .x1 .x8, .rev .x2 .x7, .rev .x3 .x6] ++
        T.storeWord .x0 .x14 ++ [.strOff .x1 .x14 8, .strOff .x2 .x14 16, .strOff .x3 .x14 24])

/-- Step 3: the exit prefix, expression `m` of `exprs` to its slot in the NEW
    stack (x23 is still the entry depth). -/
def exitOneT (T : FlushTarget) (idx : Expr → Nat) (net : Int) (e : Expr) (m : Nat) : List AInstr :=
  let d : Int := net - 1 - m
  loadSlotT T .x6 (idx e) ++
  [if d ≥ 0 then .addImm .x14 .x23 d.toNat else .subImm .x14 .x23 (-d).toNat] ++
  [.addLsl5 .x14 .x24 .x14, .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16]

def exitStoresT (T : FlushTarget) (idx : Expr → Nat) (net : Int) (exprs : List Expr) : List AInstr :=
  exprs.zipIdx.flatMap (fun (e, m) => exitOneT T idx net e m)

/-- Step 2.5: the memory commit. -/
def memCommitT (T : FlushTarget) (idx : Expr → Nat) (writes : List MemWrite) : List AInstr :=
  if writes.isEmpty then [] else
  let maxEnd := writes.foldl (fun m w => max m (w.off + if w.isByte then 1 else 32)) 0
  memExpandFlushT T maxEnd ++ mpUpdateFlushT T maxEnd ++ writes.flatMap (emitMemWriteT T idx)

/-- Step 4: the depth update. -/
def depthUpdate (net : Int) : List AInstr :=
  if net > 0 then [.addImm .x23 .x23 net.toNat]
  else if net < 0 then [.subImm .x23 .x23 (-net).toNat] else []

/-- The region flush, once, at a target, as list combinators (stage 7: so the
    pieces can be reasoned about one at a time). Numeric local labels as in
    the text; each byte path's `resolveLocals` makes them unique. -/
def emitRegionFlushT (T : FlushTarget) (r : Region) : List AInstr :=
  let p := r.ss.exprs.length
  let c := r.ss.consumed
  let net : Int := (p : Int) - c
  let idle := p == 0 && c == 0 && r.writes.isEmpty
  if idle && r.need == 0 && r.maxNet ≤ 0 then [] else
  -- 1. Depth checks: branch around a far `b` (a b.cond cannot reach the stub).
  if r.need > 1024 then T.far "_eita_stack_underflow" else
  let s1 := if r.need > 0
    then [.cmpImm .x23 r.need, .bcLbl .hs "8f"] ++ T.far "_eita_stack_underflow" ++ [.label "8"] else []
  if r.maxNet > 0 && 1025 - r.maxNet ≤ 0 then s1 ++ T.far "_eita_stack_overflow" else
  let s2 := s1 ++ (if r.maxNet > 0
    then [.cmpImm .x23 (1025 - r.maxNet).toNat, .bcLbl .lo "9f"] ++ T.far "_eita_stack_overflow" ++ [.label "9"]
    else [])
  if idle then s2 else
  -- 2. Scratch frame + DAG evaluation (write values are roots too), 2.5 the
  -- memory commit, 3. the exit-prefix stores.
  let (slots, idx) := dagSlots (r.ss.exprs ++ r.writes.map (·.val))
  let n := slots.size
  let body := if n > 0 then
      T.frameOpen n ++ slots.toList.flatMap (evalNodeT T idx) ++ memCommitT T idx r.writes ++
      exitStoresT T idx net r.ss.exprs ++ T.frameClose n
    else []
  -- 4. Depth update + cache reload.
  s2 ++ body ++ depthUpdate net ++ T.cacheReload

def emitRegionFlushA (r : Region) : List AInstr := emitRegionFlushT armFlush r

/-- The one algebra. -/
def instrOut : ChunkOut (List AInstr) where
  nil      := []
  cat      := (· ++ ·)
  head id  := Evm.CL.Frame.header (chunkSym id)
  setPc n  := movImmA .x21 n
  gas g    := g.instrs
  flush _ r := emitRegionFlushA r
  adrCont l := [.adrLbl .x27 l]
  label l  := [.label l]
  callSym sym := [.bFar sym]
  tailSym sym := [.bFar sym]
  brCont   := [.brCont]
  syncCont := Evm.CL.Frame.syncCont
  brk      := [.brk0]

/-- A chunk as instructions. -/
def emitChunkInstrs (f : Evm.Fork) (c : Chunk) : List AInstr := emitChunkGen instrOut f c

end InstrEmit

/-- The text, printed from the instructions (`chunk_text_derived` below gates
    it against `textOut` over the fixture corpus). -/
def emitChunk (f : Evm.Fork) (c : Chunk) : String := Evm.CL.Frame.text (emitChunkInstrs f c)

/-- The specification: the hand-written text algebra. -/
def emitChunkSpec (f : Evm.Fork) (c : Chunk) : String := emitChunkGen textOut f c

/-- Bytecode covering the paths the chunk emitter branches on: plain
    arithmetic, a gas-reading op (`observesGas`), a store, a memory op, and
    each terminator kind. The corpus the derivation gates run over; the
    snapshot exe dumps both lowerings of it. -/
def fixtureCorpus : List (String × List Nat) :=
  [ ("arith",      [0x60, 0x05, 0x60, 0x03, 0x01, 0x60, 0x02, 0x02, 0x00]),
    ("gas_read",   [0x5a, 0x60, 0x01, 0x01, 0x00]),
    ("sstore",     [0x60, 0x01, 0x60, 0x02, 0x55, 0x00]),
    ("memory",     [0x60, 0x20, 0x60, 0x40, 0x52, 0x00]),
    ("mstore8",    [0x60, 0x7f, 0x60, 0x40, 0x53, 0x00]),
    ("keccak",     [0x60, 0x20, 0x60, 0x00, 0x20, 0x00]),
    ("jump",       [0x60, 0x04, 0x56, 0x00, 0x5b, 0x00]),
    ("endofcode",  [0x60, 0x01, 0x60, 0x02, 0x01]),
    ("call",       [0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00,
                    0x60, 0x00, 0x60, 0x00, 0xf1, 0x00]),
    ("exp_fold",   [0x60, 0x02, 0x60, 0x08, 0x0a, 0x00]),
    ("dup_swap",   [0x60, 0x01, 0x60, 0x02, 0x80, 0x91, 0x01, 0x00]),
    ("cmp_bits",   [0x60, 0x01, 0x60, 0x02, 0x10, 0x60, 0x03, 0x11, 0x16, 0x60, 0x04, 0x12, 0x17,
                    0x60, 0x05, 0x13, 0x18, 0x14, 0x15, 0x19, 0x00]),
    ("helpers",    [0x60, 0x07, 0x60, 0x03, 0x04, 0x60, 0x05, 0x06, 0x60, 0x02, 0x1b, 0x60, 0x01, 0x1c,
                    0x60, 0x09, 0x60, 0x04, 0x60, 0x06, 0x08, 0x00]),
    ("big_const",  [0x7f, 0xde, 0xad, 0xbe, 0xef, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                    0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15,
                    0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x60, 0x01, 0x01, 0x00]) ]

/-- The chunks of the corpus (Cancun), or none if a fixture does not compile. -/
def corpusChunks : Option (List Chunk) := Id.run do
  let mut out : List Chunk := []
  for (_, bytes) in fixtureCorpus do
    match Evm.IR.compileProgram .cancun ⟨(bytes.map (fun n => UInt8.ofNat n)).toArray⟩ with
    | .ok prog => out := out ++ prog.chunks.map (·.2)
    | .error _ => return none
  return some out

/-- **Text identity over the corpus**: the derived chunk text IS the
    hand-written algebra's, character for character. -/
theorem chunk_text_derived :
    (match corpusChunks with
     | some cs => cs.length ≥ 14 && cs.all (fun c => emitChunk .cancun c == emitChunkSpec .cancun c)
     | none => false) = true := by native_decide


/-- The entry, printed from `Frame.runChunk` (stage 4r). -/
def runChunkCode : String := Frame.text Frame.runChunk

/-- First-occurrence-wins dedup of `Program.chunks` (overlapping-chunk
    compilation may list an entry twice; emitting twice would define
    duplicate symbols). -/
def dedupByPc (l : List (Nat × Chunk)) : List (Nat × Chunk) := Id.run do
  let mut seen : List Nat := []
  let mut out : List (Nat × Chunk) := []
  for (p, c) in l do
    unless seen.contains p do
      seen := p :: seen
      out := (p, c) :: out
  return out.reverse

/-- Entry manifest the host driver reads via FFI:
    `{ count : u64; entries : { pc : u64; fn : void* }[count] }`. -/
def entriesTable (chunks : List (Nat × Chunk)) : String :=
  ".data\n" ++
  ".global _eita_jit_entries\n" ++
  ".p2align 3\n" ++
  "_eita_jit_entries:\n" ++
  s!"    .quad   {chunks.length}\n" ++
  String.join (chunks.map fun (p, _) =>
    s!"    .quad   {p}\n    .quad   {chunkSym p}\n")

/-- The full per-program .S text. Links against the handlers dylib —
    nothing here redefines a handler or the runtime scaffolding. -/
def emitProgram (f : Evm.Fork) (p : Program) : String :=
  let chunks := dedupByPc p.chunks
  ".section __TEXT,__text,regular,pure_instructions\n" ++
  runChunkCode ++ "\n" ++
  String.intercalate "\n" (chunks.map fun (_, c) => emitChunk f c) ++ "\n" ++
  entriesTable chunks

/-! ## In-process `List Item` emitter (#235)

The byte path is `instrOut` lowered through `AsmItems` — the same instructions
the text is printed from. Nothing here describes a chunk a second time; what
remains is the entry (`runChunkItems`, from `Frame.runChunk`), the
continuation, and the serialized image the SBCL loader consumes. -/

section ItemEmit
open Evm.CL.AsmEncode Evm.CL.AsmEncode.Insn Evm.CL.AsmEncode.Item Evm.CL.ARM64.JITEmit

/-- x27 (continuation) = sync_and_ret, from `Frame.syncCont` (an `AbsSym`:
    movabs, not GOT — the in-process image has no linker). -/
private def syncContI : List Item := Evm.CL.AsmItems.progItems Frame.syncCont

/-- The items, lowered from the same instructions the text is printed from
    (numeric locals made unique by `resolveLocals`). -/
def emitChunkItems (f : Evm.Fork) (c : Chunk) : List Item :=
  Evm.CL.AsmItems.resolveLocals (Evm.CL.AsmItems.progItems (emitChunkInstrs f c))

/-- The entry as items, from the same program the text comes from (stage 4r):
    the two paths no longer describe the prologue twice. -/
def runChunkItems : List Item :=
  Evm.CL.AsmItems.resolveLocals (Evm.CL.AsmItems.progItems Frame.runChunk)

/-! ### Serialized image blob (consumed by the SBCL in-process loader)

Layout (little-endian u64 unless noted; every section 8-aligned):
```
magic=0x314A_4154_4945 ("EITAJ1")  imageSize  runChunkOff  entryCount  relocCount
[image bytes, padded to 8]
entries: (pc, off)            * entryCount
relocs:  (kind, off, symLen, sym[padded to 8]) * relocCount   -- kind: movabs=4
```
The image is `runChunkItems` then each chunk, concatenated (all 4-aligned); the
loader mmaps it RX, patches each `movabs` reloc with `dlsym(sym)`'s halfwords,
and builds an absolute (pc, fn) manifest from `entries`. -/

private def relocCode : RelocKind → Nat
  | .b26 => 0 | .b19 => 1 | .adrp => 2 | .adr => 3 | .movabs => 4

private def pushU64 (ba : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut b := ba
  for i in List.range 8 do
    b := b.push (UInt8.ofNat ((n >>> (8 * i)) % 256))
  return b

private def pad8 (ba : ByteArray) : ByteArray := Id.run do
  let mut b := ba
  while b.size % 8 != 0 do b := b.push 0
  return b

/-- Concatenate the parts once, into a preallocated array. (Per-chunk `++`
    copied the growing image every time — quadratic; a 20 000-JUMPDEST contract
    (stQuadraticComplexityTest's Call20KbytesContract50) took minutes and
    gigabytes in the emit daemon.) -/
def concatParts (parts : Array ByteArray) (total : Nat) : ByteArray :=
  parts.foldl (fun acc q => q.copySlice 0 acc acc.size q.size) (ByteArray.emptyWithCapacity total)

/-- Assemble the full program into the serialized loader blob. -/
def emitProgramImage (f : Evm.Fork) (p : Program) : ByteArray := Id.run do
  let chunks := dedupByPc p.chunks
  let (rcBytes, rcRelocs) := AsmEncode.assemble runChunkItems
  let mut parts : Array ByteArray := #[rcBytes]
  let mut size := rcBytes.size
  let mut relocs : Array (RelocKind × Nat × String) :=
    (rcRelocs.map (fun r => (r.kind, r.byteOff, r.sym))).toArray
  let mut entries : Array (Nat × Nat) := #[]
  for (pc, c) in chunks do
    let base := size
    let (cb, cr) := AsmEncode.assemble (emitChunkItems f c)
    parts := parts.push cb
    size := size + cb.size
    for r in cr do
      relocs := relocs.push (r.kind, base + r.byteOff, r.sym)
    entries := entries.push (pc, base)
  let image := concatParts parts size
  -- serialize
  let mut out := ByteArray.emptyWithCapacity (image.size + 64 + 16 * entries.size + 48 * relocs.size)
  out := pushU64 out 0x314A_4154_4945      -- "EITAJ1"
  out := pushU64 out image.size
  out := pushU64 out 0                      -- runChunkOff (run_chunk is first)
  out := pushU64 out entries.size
  out := pushU64 out relocs.size
  out := pad8 (image.copySlice 0 out out.size image.size)
  for (pc, off) in entries do
    out := pushU64 out pc; out := pushU64 out off
  for (k, off, sym) in relocs do
    out := pushU64 out (relocCode k)
    out := pushU64 out off
    out := pushU64 out sym.toUTF8.size
    out := pad8 (out ++ sym.toUTF8)
  return out

end ItemEmit

end Evm.CL.ARM64.JIT
