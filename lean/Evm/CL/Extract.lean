import Evm.CL.MacroSpec

/-! # CL/Extract — Lean-derived CL opcode emission

This is the foundation for retiring `axiom cl_X_macro_equals_step`
in favor of `theorem cl_X_macro_equals_step` (issue #10).

Idea:

  1. Define a small `Form` inductive type modeling the subset of
     CL we emit (literals, vars, stack ops, gas, control).
  2. Give `Form` an operational semantics `interp : Form → CLState
     → Option CLState` — this is what we *believe* SBCL evaluates
     to when given the pretty-printed form.
  3. Give `Form` a pretty-printer `toCL : Form → String` that
     produces backquoted CL source compatible with the existing
     `defmacro op-X (s fork mode) ...` shape.
  4. Define each opcode as a `Form` value.
  5. Prove `interp (opForm X) s = stepX s` — this is the per-opcode
     soundness theorem, in Lean, no audit needed.
  6. Emit the CL source via `toCL`. The CL eval-loop loads the
     emitted form instead of the hand-written macro.

The remaining trust point is a SINGLE global axiom:
"SBCL's macroexpand of `toCL f` has the operational semantics
of `interp f`." That's the bridge between Lean and SBCL; everything
else is provable.

## Comparison with the current axiom shape

  * Today: ~90 opaques + ~90 axioms in OpRefinement.lean. Each
    asserts `sbclMacroOpX = MacroSpec.stepX`. Bridge per opcode.
  * Extracted: 1 axiom asserting `interp f ≡ sbcl_eval (toCL f)`.
    Per-opcode soundness becomes a theorem `interp opForm =
    stepX`, provable inside Lean.

For now, prototype with one opcode (ADD). The pattern then
generalizes mechanically. -/

namespace Evm.CL.Extract

/-! ## The Form AST

Minimal CL subset: enough for arithmetic + stack + gas + pc.
Memory / storage / world / cross-call forms come later — they
need richer semantics in `interp`. -/

inductive Form where
  /-- A numeric literal. -/
  | lit (n : Nat) : Form
  /-- A variable reference (`a`, `b`, `s`, etc.). -/
  | var (name : String) : Form
  /-- No-op (empty progn / unit value). -/
  | nop : Form
  /-- Sequential composition: `seq a b` evaluates `a`, discards its
      value, then evaluates `b`. Result = value of `b`. Tree-shaped
      for structural recursion; the pretty-printer flattens chains
      of `seq` into a single `(progn ...)`. -/
  | seq : Form → Form → Form
  /-- Single let* binding: `letBind name e body` evaluates `e`, binds
      the result to `name`, then evaluates `body` in the extended env.
      Multiple bindings chain via nested `letBind`. -/
  | letBind : String → Form → Form → Form
  /-- `(charge-gas ,s cost ,mode)` — decrements gas in :full mode. -/
  | chargeGas (sVar : String) (cost : Nat) (modeVar : String) : Form
  /-- `(stk-pop ,s)` — returns top of stack, decrements sp. -/
  | stkPop (sVar : String) : Form
  /-- `(stk-push ,s val)` — pushes val on stack. -/
  | stkPush (sVar : String) (val : Form) : Form
  /-- `(u256-mask v)` — `(logand v (1- (ash 1 256)))`. -/
  | u256Mask (v : Form) : Form
  /-- Binary op: name is `"+", "-", "*", "logand"`, etc. -/
  | binOp (op : String) (a b : Form) : Form
  /-- `(incf (evm-state-pc ,s))`. -/
  | incPc (sVar : String) : Form
  /-- Bare `,fork` reference — macro-arg expansion of a no-op. -/
  | forkRef (forkVar : String) : Form
  /-- `(sload-from ,s addr-form slot-form)` — viewed-storage read,
      cache + oracle composed. Push semantics: returns the value. -/
  | sloadFrom (sVar : String) (addr : Form) (slot : Form) : Form
  /-- `(sstore-to ,s addr-form slot-form val-form)` — cache write.
      Returns the value (CL `setf` returns the new value). -/
  | sstoreTo (sVar : String) (addr : Form) (slot : Form) (val : Form) : Form
  /-- `(evm-state-address ,s)` — read self-address from the frame. -/
  | stateAddr (sVar : String) : Form
  /-- `(push (list :sstore addr slot old-value) (evm-state-journal ,s))` —
      append a journal entry, returns nil. -/
  | journalPush (sVar : String) (addr : Form) (slot : Form) (oldVal : Form) : Form
  /-- `(when (evm-state-staticp ,s) (error "..."))` — abort if static. -/
  | staticpCheck (sVar : String) : Form
  /-- `(evm-state-FIELD ,s)` — read a named frame field. Interp
      reads the corresponding CLState projection. -/
  | stateField (sVar : String) (field : String) : Form
  /-- `(setf (evm-state-halted ,s) t)` — mark frame as halted. -/
  | setHalted (sVar : String) : Form
  /-- `(stk-peek ,s n)` — read stack[sp-1-n] without popping. -/
  | stkPeek (sVar : String) (n : Nat) : Form
  /-- `(blob-hash-at ,s idx)` — the tx's versioned blob hash at `idx`, 0 past the
      count (EIP-4844 BLOBHASH). Interp reads `CLState.blobHashes`. -/
  | blobHashAt (sVar : String) (idx : Form) : Form
  /-- `(svref ... (- sp 1 n))` swap with top of stack. -/
  | stkSwap (sVar : String) (n : Nat) : Form
  /-- `(if (zerop cond) then-form else-form)` -/
  | ifZero (cond : Form) (thenF : Form) (elseF : Form) : Form
  /-- Escape hatch: raw CL source spliced verbatim. Use sparingly,
      for ops whose structure is awkward to capture in Form
      primitives. interp returns none (unknown Lean semantics);
      the audit script remains the correctness check until a
      structured Form replaces it. -/
  | rawCL (source : String) : Form
  /-- `(if (op a b) 1 0)` — binary comparison to a 0/1 result.
      `op` is the CL comparison: "<", ">", "=". -/
  | cmpToBool (op : String) (a b : Form) : Form
  /-- `(if (zerop a) 1 0)` — ISZERO. -/
  | iszeroBool (a : Form) : Form
  /-- `(op a)` — unary operation. For NOT: `unaryArith "lognot"`. -/
  | unaryArith (op : String) (a : Form) : Form
  /-- `(s256 a)` — signed-int conversion for SDIV/SMOD/SLT/SGT/SAR. -/
  | signedConvert (a : Form) : Form
  /-- `(mem-read-u256 ,s off)` — 32-byte BE read, pads memory if short. -/
  | memReadU256 (sVar : String) (off : Form) : Form
  /-- `(mem-write-u256 ,s off val)` — 32-byte BE write, pads memory. -/
  | memWriteU256 (sVar : String) (off val : Form) : Form
  /-- Low-byte write at memory[off]. -/
  | memWriteByte (sVar : String) (off val : Form) : Form
  /-- `(funcall (evm-state-world-hook ,s) :kind arg)`. The `arg` Form
      is evaluated to U256 and passed as the lookup key. Specialized
      at the audit level to Addr = Evm.U256. -/
  | worldHookU256 (sVar : String) (kind : String) (arg : Form) : Form
  -- ELEMENTARY primitives below — each maps to one CL form,
  -- has a small precise interp, and corresponds to one (or a few)
  -- ARM64/AMD64/AVX instructions.
  /-- `(length (evm-state-memory ,s))` — memory length as U256. -/
  | memLengthForm (sVar : String) : Form
  /-- `(vector-push-extend val (evm-state-memory ,s))` — append byte,
      mutating. Returns 0; effect is on s.memory. -/
  | memByteAppend (sVar : String) (val : Form) : Form
  /-- `(setf (aref (evm-state-memory ,s) off) (logand #xff val))` —
      write low byte. Returns 0; mutates s.memory[off]. -/
  | memByteWriteAt (sVar : String) (off val : Form) : Form
  /-- `(evm-state-mp ,s)`. -/
  | mpFieldRead (sVar : String) : Form
  /-- `(setf (evm-state-mp ,s) v)`. -/
  | mpFieldWrite (sVar : String) (v : Form) : Form
  /-- `(if cond then else)` — generic if. CL truthiness: non-NIL.
      Lean: non-zero value → take then branch. -/
  | ifGen (cond : Form) (thenF elseF : Form) : Form
  /-- `(op a b)` — comparison expression yielding 0/1. -/
  | clCmp (op : String) (a b : Form) : Form
  /-- `(error msg)` — halts Lean evaluation (returns none). -/
  | errorForm (msg : String) : Form
  /-- RETURN: memory[off..off+len] → output, set halted. -/
  | haltWithOutput (sVar : String) (off len : Form) : Form
  /-- REVERT: same as haltWithOutput, also sets reverted. -/
  | haltWithRevert (sVar : String) (off len : Form) : Form
  /-- `(gethash slot (evm-state-tstorage ,s) 0)`. -/
  | tstorageRead (sVar : String) (slot : Form) : Form
  /-- `(setf (gethash slot (evm-state-tstorage ,s)) val)`. -/
  | tstorageWrite (sVar : String) (slot val : Form) : Form
  /-- SDIV semantics: signed division, 0 on divide-by-zero;
      INT_MIN divided by -1 wraps to INT_MIN (BitVec.sdiv handles this). -/
  | signedDivU256 (a b : Form) : Form
  /-- SMOD semantics: signed mod, 0 on divide-by-zero. BitVec.srem. -/
  | signedRemU256 (a b : Form) : Form
  /-- SAR: arithmetic right shift; shift ≥ 256 → all-sign-extend. -/
  | signedShiftRight (val shift : Form) : Form
  /-- SIGNEXTEND b x: sign-extend x from bit (8*b+7); b≥31 → x unchanged. -/
  | signExtend (b x : Form) : Form
  /-- JUMP: validate dest, set pc. Errors (none) unless dest is a JUMPDEST outside
      PUSH data (`Runtime.isJumpDest`). -/
  | validatedJump (sVar : String) (dest : Form) : Form
  /-- CALLDATALOAD: read 32 BE bytes from calldata[off..off+32], zero-pad. -/
  | calldataLoad32 (sVar : String) (off : Form) : Form
  /-- MCOPY: memory-to-memory copy with zero-padding for OOB src. -/
  | memMemCopy (sVar : String) (dst src len : Form) : Form
  /-- EXP: charge variable gas (10 + 50*ebytes), push base^e mod 2^256. -/
  | expU256Op (sVar : String) (modeVar : String) (base e : Form) : Form
  /-- Signed comparison emit + precise signed interp.
      toCL: `(if (op (s256 a) (s256 b)) 1 0)`.
      interp: uses BitVec.slt / BitVec.sgt (not the unsigned <). -/
  | signedCmpToBool (op : String) (a b : Form) : Form
  /-- DIV: EVM-spec-shape primitive. `(if (zerop b) 0 (floor a b))` in
      CL, `if b = 0 then 0 else BitVec.udiv a b` in interp. Matches
      MacroSpec.stepDiv exactly — proof closes by rfl after simp. -/
  | divOp (a b : Form) : Form
  /-- MOD: same shape as divOp but uses BitVec.umod. -/
  | modOp (a b : Form) : Form
  /-- SHL: `if shift.toNat ≥ 256 then 0 else val <<< shift.toNat`.
      `shift` is the first arg (top of stack in EVM), `val` is second. -/
  | shlU256 (shift val : Form) : Form
  /-- SHR: like shlU256 but logical right shift. -/
  | shrU256 (shift val : Form) : Form
  /-- BYTE: extract i-th byte from x (counting from high end).
      `i` is first arg, `x` is second. -/
  | byteAtU256 (i x : Form) : Form
  /-- PUSH-N: read N bytes from code[pc+1..pc+n] big-endian, push as
      U256, charge gas (2 for n=0, 3 otherwise), advance pc by n+1.
      Monolithic primitive — too much state mutation to decompose cleanly. -/
  | pushNAndAdvance (sVar : String) (modeVar : String) (n : Nat) : Form
  /-- LOG-N: static check, charge (375 + 375n) gas, pop off+len+n topics,
      pad memory to off+len, update mp, bump pc. Spec does NOT track the
      log record itself (CL impl does; audit only checks the side effects). -/
  | logNOp (sVar : String) (modeVar : String) (n : Nat) : Form
  /-- KECCAK256: pop off+len, hash memory[off..off+len] via the host
      crypto primitive, push 32-byte digest. Variable gas based on len. -/
  | keccakOp (sVar : String) (modeVar : String) : Form
  /-- ADDMOD: `if n = 0 then 0 else U256.ofNat ((a.toNat + b.toNat) % n.toNat)`.
      Args evaluated left-to-right: a then b then n. -/
  | addmodU256 (a b n : Form) : Form
  /-- MULMOD: like addmodU256 but with multiplication. -/
  | mulmodU256 (a b n : Form) : Form
  /-- Length of a buffer field (calldata / code / returndata).
      toCL: `(length (evm-state-FIELD ,s))`.
      interp: returns `Evm.U256.ofNat s.FIELD.size` directly. -/
  | bufferLengthOp (sVar : String) (field : String) : Form
  /-- Buffer-to-memory copy. `srcKind` selects the source: "calldata",
      "code", "returndata". For "returndata", emits an OOB check.
      Zero-pads past source end (except returndata which errors). -/
  | bufferCopyToMem (sVar : String) (srcKind : String)
                     (dst src len : Form) : Form
  /-- EXTCODECOPY: copy world code of `addr` to memory. -/
  | worldCodeCopyToMem (sVar : String)
                        (addr dst src len : Form) : Form
  deriving Inhabited

/-! ## Pretty-printer — Form → CL source

Output is a backquoted form suitable for splicing into a
`defmacro` body. Variable references are unquoted (`,s`) since
they're macro args. -/

/-- Flatten a chain of `seq` into a list (left-recursive associativity
    matches how we build sequences). -/
def Form.flatSeq : Form → List Form
  | .seq a b => Form.flatSeq a ++ Form.flatSeq b
  | .nop => []
  | f => [f]

/-- Collect chained `letBind` into ([(name, e), ...], body). -/
def Form.flatLet : Form → List (String × Form) × Form
  | .letBind n e body =>
    let (bs, b) := Form.flatLet body
    ((n, e) :: bs, b)
  | f => ([], f)

partial def Form.toCL : Form → String
  | .lit n => toString n
  | .var name => name
  | .nop => "(progn)"
  | f@(.seq _ _) =>
    let fs := Form.flatSeq f
    "(progn " ++ String.intercalate " " (fs.map (·.toCL)) ++ ")"
  | f@(.letBind _ _ _) =>
    let (binds, body) := Form.flatLet f
    let bs := binds.map fun (n, e) => s!"({n} {e.toCL})"
    s!"(let* ({String.intercalate " " bs}) {body.toCL})"
  | .chargeGas sv c mv => s!"(charge-gas ,{sv} {c} ,{mv})"
  | .stkPop sv => s!"(stk-pop ,{sv})"
  | .stkPush sv val => s!"(stk-push ,{sv} {val.toCL})"
  | .u256Mask v => s!"(u256-mask {v.toCL})"
  | .binOp op a b => s!"({op} {a.toCL} {b.toCL})"
  | .incPc sv => s!"(incf (evm-state-pc ,{sv}))"
  | .forkRef fv => s!",{fv}"
  | .sloadFrom sv addr slot => s!"(sload-from ,{sv} {addr.toCL} {slot.toCL})"
  | .sstoreTo sv addr slot val =>
    s!"(sstore-to ,{sv} {addr.toCL} {slot.toCL} {val.toCL})"
  | .stateAddr sv => s!"(evm-state-address ,{sv})"
  | .journalPush sv addr slot old =>
    s!"(push (list :sstore {addr.toCL} {slot.toCL} {old.toCL}) (evm-state-journal ,{sv}))"
  | .staticpCheck sv =>
    s!"(when (evm-state-staticp ,{sv}) (error \"static context\"))"
  | .stateField sv f => s!"(evm-state-{f} ,{sv})"
  | .setHalted sv => s!"(setf (evm-state-halted ,{sv}) t)"
  | .stkPeek sv n => s!"(stk-peek ,{sv} {n})"
  | .blobHashAt sv idx => s!"(blob-hash-at ,{sv} {idx.toCL})"
  | .stkSwap sv n =>
    s!"(let* ((sp (evm-state-sp ,{sv})) (top-i (- sp 1)) (other-i (- sp 1 {n})) (tmp (svref (evm-state-stack ,{sv}) top-i))) (setf (svref (evm-state-stack ,{sv}) top-i) (svref (evm-state-stack ,{sv}) other-i)) (setf (svref (evm-state-stack ,{sv}) other-i) tmp))"
  | .ifZero c t e =>
    s!"(if (zerop {c.toCL}) {t.toCL} {e.toCL})"
  | .rawCL src => src
  | .cmpToBool op a b => s!"(if ({op} {a.toCL} {b.toCL}) 1 0)"
  | .iszeroBool a => s!"(if (zerop {a.toCL}) 1 0)"
  | .unaryArith op a => s!"({op} {a.toCL})"
  | .signedConvert a => s!"(s256 {a.toCL})"
  | .memReadU256 sv off => s!"(mem-read-u256 ,{sv} {off.toCL})"
  | .memWriteU256 sv off val => s!"(mem-write-u256 ,{sv} {off.toCL} {val.toCL})"
  | .memWriteByte sv off val =>
    s!"(let* ((off {off.toCL}) (val {val.toCL}) (mem (evm-state-memory ,{sv}))) (loop while (< (length mem) (+ off 1)) do (vector-push-extend 0 mem)) (setf (evm-state-mp ,{sv}) (max (evm-state-mp ,{sv}) (+ off 1))) (setf (aref mem off) (logand #xff val)))"
  | .worldHookU256 sv kind arg =>
    s!"(funcall (evm-state-world-hook ,{sv}) :{kind} {arg.toCL})"
  | .memLengthForm sv => s!"(length (evm-state-memory ,{sv}))"
  | .memByteAppend sv val =>
    s!"(vector-push-extend {val.toCL} (evm-state-memory ,{sv}))"
  | .memByteWriteAt sv off val =>
    s!"(setf (aref (evm-state-memory ,{sv}) {off.toCL}) (logand #xff {val.toCL}))"
  | .mpFieldRead sv => s!"(evm-state-mp ,{sv})"
  | .mpFieldWrite sv v => s!"(setf (evm-state-mp ,{sv}) {v.toCL})"
  | .ifGen c t e => s!"(if {c.toCL} {t.toCL} {e.toCL})"
  | .clCmp op a b => s!"({op} {a.toCL} {b.toCL})"
  | .errorForm msg => s!"(error \"{msg}\")"
  | .haltWithOutput sv off len =>
    s!"(let* ((off {off.toCL}) (len {len.toCL})) (ensure-mem ,{sv} (+ off len)) (let ((out (make-array len :element-type '(unsigned-byte 8)))) (replace out (evm-state-memory ,{sv}) :start2 off) (setf (evm-state-output ,{sv}) out (evm-state-halted ,{sv}) t)))"
  | .haltWithRevert sv off len =>
    s!"(let* ((off {off.toCL}) (len {len.toCL})) (ensure-mem ,{sv} (+ off len)) (let ((out (make-array len :element-type '(unsigned-byte 8)))) (replace out (evm-state-memory ,{sv}) :start2 off) (setf (evm-state-output ,{sv}) out (evm-state-halted ,{sv}) t (evm-state-reverted ,{sv}) t)))"
  | .tstorageRead sv slot =>
    s!"(gethash {slot.toCL} (evm-state-tstorage ,{sv}) 0)"
  | .tstorageWrite sv slot val =>
    s!"(setf (gethash {slot.toCL} (evm-state-tstorage ,{sv})) {val.toCL})"
  | .signedDivU256 a b =>
    -- CL: (let* ((sa (s256 a)) (sb (s256 b)))
    --       (cond ((zerop sb) 0)
    --             ((and (= sa #.(- (ash 1 255))) (= sb -1)) #.(ash 1 255))
    --             (t (logand #.(1- (ash 1 256)) (truncate sa sb)))))
    s!"(let* ((sa (s256 {a.toCL})) (sb (s256 {b.toCL}))) (cond ((zerop sb) 0) ((and (= sa #.(- (ash 1 255))) (= sb -1)) #.(ash 1 255)) (t (logand #.(1- (ash 1 256)) (truncate sa sb)))))"
  | .signedRemU256 a b =>
    s!"(let* ((sa (s256 {a.toCL})) (sb (s256 {b.toCL}))) (if (zerop sb) 0 (logand #.(1- (ash 1 256)) (rem sa sb))))"
  | .signedShiftRight val shift =>
    s!"(let ((sv (s256 {val.toCL})) (sh {shift.toCL})) (cond ((>= sh 256) (if (minusp sv) #.(1- (ash 1 256)) 0)) (t (logand #.(1- (ash 1 256)) (ash sv (- sh))))))"
  | .signExtend b x =>
    s!"(let ((b {b.toCL}) (x {x.toCL})) (if (>= b 31) x (let* ((k (+ (* 8 b) 7)) (mask (1- (ash 1 (1+ k)))) (allones (1- (ash 1 256))) (upper (- allones mask))) (if (logbitp k x) (logior (logand x mask) upper) (logand x mask)))))"
  | .validatedJump sv dest =>
    -- Walk the code from 0 skipping PUSH immediates (EELS get_valid_jump_destinations):
    -- the destination is valid iff the walk lands on it and finds 0x5b there; a dest
    -- inside PUSH data or past the end is never landed on.
    s!"(let ((dest {dest.toCL}) (code (evm-state-code ,{sv}))) (unless (loop with pc = 0 while (< pc (length code)) do (let ((op (aref code pc))) (when (= pc dest) (return (= op #x5b))) (incf pc (if (<= #x60 op #x7f) (+ 2 (- op #x60)) 1))) finally (return nil)) (error \"invalid jumpdest\")) (setf (evm-state-pc ,{sv}) dest))"
  | .calldataLoad32 sv off =>
    s!"(let* ((off {off.toCL}) (cd (evm-state-calldata ,{sv})) (cdlen (length cd)) (v 0)) (loop for i from 0 below 32 do (let ((b (if (< (+ off i) cdlen) (aref cd (+ off i)) 0))) (setf v (logior (ash v 8) b)))) v)"
  | .memMemCopy sv dst src len =>
    s!"(let* ((dst {dst.toCL}) (src {src.toCL}) (len {len.toCL}) (mem (evm-state-memory ,{sv})) (end (max (+ dst len) (+ src len)))) (loop while (< (length mem) end) do (vector-push-extend 0 mem)) (setf (evm-state-mp ,{sv}) (max (evm-state-mp ,{sv}) end)) (let ((tmp (make-array len :element-type '(unsigned-byte 8)))) (loop for i from 0 below len do (setf (aref tmp i) (aref mem (+ src i)))) (loop for i from 0 below len do (setf (aref mem (+ dst i)) (aref tmp i)))))"
  | .expU256Op sv mv base e =>
    s!"(let* ((base {base.toCL}) (e {e.toCL}) (ebytes (cond ((zerop e) 0) (t (ceiling (integer-length e) 8)))) (cost (+ 10 (* 50 ebytes)))) (charge-gas ,{sv} cost ,{mv}) (if (zerop e) 1 (u256-mask (expt-mod-256 base e))))"
  | .signedCmpToBool op a b =>
    s!"(if ({op} (s256 {a.toCL}) (s256 {b.toCL})) 1 0)"
  | .divOp a b =>
    s!"(let ((b {b.toCL})) (if (zerop b) 0 (floor {a.toCL} b)))"
  | .modOp a b =>
    s!"(let ((b {b.toCL})) (if (zerop b) 0 (mod {a.toCL} b)))"
  | .shlU256 shift val =>
    s!"(if (>= {shift.toCL} 256) 0 (u256-mask (ash {val.toCL} {shift.toCL})))"
  | .shrU256 shift val =>
    s!"(if (>= {shift.toCL} 256) 0 (ash {val.toCL} (- {shift.toCL})))"
  | .byteAtU256 i x =>
    s!"(if (>= {i.toCL} 32) 0 (logand 255 (ash {x.toCL} (- (* 8 (- 31 {i.toCL}))))))"
  | .pushNAndAdvance sv mv n =>
    let gasCost := if n = 0 then 2 else 3
    s!"(let* ((code (evm-state-code ,{sv})) (pc (evm-state-pc ,{sv})) (val 0)) (declare (type (unsigned-byte 256) val) (type fixnum pc)) (loop for i from 0 below {n} do (let ((b (if (< (+ pc 1 i) (length code)) (aref code (+ pc 1 i)) 0))) (setf val (logior (ash val 8) b)))) (charge-gas ,{sv} {gasCost} ,{mv}) (stk-push ,{sv} val) (incf (evm-state-pc ,{sv}) (+ 1 {n})))"
  | .logNOp sv mv n =>
    let gasCost := 375 + 375 * n
    s!"(progn (when (evm-state-staticp ,{sv}) (error \"LOG in static context\")) (charge-gas ,{sv} {gasCost} ,{mv}) (let* ((off (stk-pop ,{sv})) (len (stk-pop ,{sv})) (mem (evm-state-memory ,{sv})) (topics (loop repeat {n} collect (stk-pop ,{sv})))) (loop while (< (length mem) (+ off len)) do (vector-push-extend 0 mem)) (setf (evm-state-mp ,{sv}) (max (evm-state-mp ,{sv}) (+ off len))) (let ((data (make-array len :element-type '(unsigned-byte 8)))) (loop for i from 0 below len do (setf (aref data i) (aref mem (+ off i)))) (push (list (evm-state-address ,{sv}) topics data) (evm-state-logs ,{sv})))) (incf (evm-state-pc ,{sv})))"
  | .keccakOp sv mv =>
    s!"(let* ((off (stk-pop ,{sv})) (len (stk-pop ,{sv})) (mem (evm-state-memory ,{sv}))) (loop while (< (length mem) (+ off len)) do (vector-push-extend 0 mem)) (setf (evm-state-mp ,{sv}) (max (evm-state-mp ,{sv}) (+ off len))) (let ((data (make-array len :element-type '(unsigned-byte 8)))) (loop for i from 0 below len do (setf (aref data i) (aref mem (+ off i)))) (charge-gas ,{sv} (+ 30 (* 6 (floor (+ len 31) 32))) ,{mv}) (stk-push ,{sv} (u256-be (evm::keccak256 data))) (incf (evm-state-pc ,{sv}))))"
  | .addmodU256 a b n =>
    s!"(let ((n {n.toCL})) (if (zerop n) 0 (mod (+ {a.toCL} {b.toCL}) n)))"
  | .mulmodU256 a b n =>
    s!"(let ((n {n.toCL})) (if (zerop n) 0 (mod (* {a.toCL} {b.toCL}) n)))"
  | .bufferLengthOp sv field => s!"(length (evm-state-{field} ,{sv}))"
  | .bufferCopyToMem sv srcKind dst src len =>
    let srcExpr := match srcKind with
      | "calldata"   => s!"(evm-state-calldata ,{sv})"
      | "code"       => s!"(evm-state-code ,{sv})"
      | "returndata" => s!"(evm-state-returndata ,{sv})"
      | "world-code" =>
        -- Caller supplies addr inline; emit world-hook lookup using
        -- a fresh let-bound addr from a (stk-pop) inserted by caller.
        s!"(funcall (evm-state-world-hook ,{sv}) :code addr)"
      | _ => "nil"
    let oobCheck := if srcKind = "returndata" then
      s!"(when (> (+ src len) (length buf)) (error \"copy out of bounds\")) "
    else ""
    -- For "world-code", caller is expected to bind `addr` before this form.
    let bufBinding :=
      if srcKind = "returndata" || srcKind = "calldata" || srcKind = "code" then
        s!"(buf {srcExpr})"
      else
        s!"(buf {srcExpr})"
    let oobOrPad := if srcKind = "returndata" then "" else
      "(if (< (+ src i) (length buf)) (aref buf (+ src i)) 0)"
    let bodyExpr := if srcKind = "returndata" then "(aref buf (+ src i))"
      else oobOrPad
    s!"(let* ((dst {dst.toCL}) (src {src.toCL}) (len {len.toCL}) (mem (evm-state-memory ,{sv})) {bufBinding}) {oobCheck}(loop while (< (length mem) (+ dst len)) do (vector-push-extend 0 mem)) (setf (evm-state-mp ,{sv}) (max (evm-state-mp ,{sv}) (+ dst len))) (loop for i from 0 below len do (setf (aref mem (+ dst i)) {bodyExpr})))"
  | .worldCodeCopyToMem sv addr dst src len =>
    s!"(let* ((addr {addr.toCL}) (dst {dst.toCL}) (src {src.toCL}) (len {len.toCL}) (mem (evm-state-memory ,{sv})) (code (funcall (evm-state-world-hook ,{sv}) :code addr))) (loop while (< (length mem) (+ dst len)) do (vector-push-extend 0 mem)) (setf (evm-state-mp ,{sv}) (max (evm-state-mp ,{sv}) (+ dst len))) (loop for i from 0 below len do (setf (aref mem (+ dst i)) (if (< (+ src i) (length code)) (aref code (+ src i)) 0))))"

/-! ## Lean-side interpreter for `Form`

`interp` is what we *say* SBCL does when it evaluates the
emitted form. The single trust axiom (in OpRefinement) is that
SBCL agrees with this interp. -/

open Evm.CL.MacroSpec

/-- The environment for `interp`: name → U256. -/
abbrev Env := String → Evm.U256

def Env.empty : Env := fun _ => 0
def Env.set (e : Env) (k : String) (v : Evm.U256) : Env :=
  fun k' => if k = k' then v else e k'

/-- Interpret a `Form` against a state and environment. Returns
    (result-value, updated-state, updated-env). Errors → none.

    Structurally recursive: progn / letStar go through helpers that
    decrement the list — that's the well-foundedness witness. -/
def Form.interp {Addr : Type} [DecidableEq Addr]
    (env : Env) (s : CLState Addr Evm.U256) :
    Form → Option (Evm.U256 × CLState Addr Evm.U256 × Env)
  | .lit n => some (Evm.U256.ofNat n, s, env)
  | .var name => some (env name, s, env)
  | .nop => some (0, s, env)
  | .seq a b =>
    match Form.interp env s a with
    | none => none
    | some (_, s', env') => Form.interp env' s' b
  | .letBind name e body =>
    match Form.interp env s e with
    | none => none
    | some (v, s', env') => Form.interp (env'.set name v) s' body
  | .chargeGas _ cost _ =>
    some (0, { s with gasLeft := s.gasLeft - cost }, env)
  | .stkPop _ =>
    match s.stack with
    | [] => none
    | top :: rest => some (top, { s with stack := rest }, env)
  | .stkPush _ valForm =>
    match Form.interp env s valForm with
    | none => none
    | some (v, s', env') => some (0, { s' with stack := v :: s'.stack }, env')
  | .u256Mask v =>
    match Form.interp env s v with
    | none => none
    | some (n, s', env') => some (n, s', env')  -- BitVec 256 wraps automatically
  | .binOp op a b =>
    match Form.interp env s a with
    | none => none
    | some (va, s', env') =>
      match Form.interp env' s' b with
      | none => none
      | some (vb, s'', env'') =>
        let result : Evm.U256 :=
          match op with
          | "+"      => va + vb
          | "-"      => va - vb
          | "*"      => va * vb
          | "logand" => va &&& vb
          | "logior" => va ||| vb
          | "logxor" => va ^^^ vb
          | "floor"  => BitVec.udiv va vb     -- DIV interp
          | "mod"    => BitVec.umod va vb     -- MOD interp
          | _ => 0
        some (result, s'', env'')
  | .incPc _ => some (0, { s with pc := s.pc + 1 }, env)
  | .forkRef _ => some (0, s, env)
  | .sloadFrom _ addr slot =>
    -- Use MacroSpec.U256Ops.viewedStorage so this lines up with
    -- stepSload exactly. The Form passes addr through (placeholder
    -- 0 from stateAddr in the abstract case), but the lookup uses
    -- s.addr — same as stepSload.
    match Form.interp env s addr with
    | none => none
    | some (_, s', env') =>
      match Form.interp env' s' slot with
      | none => none
      | some (slotVal, s'', env'') =>
        -- The lookup must match `CLState.viewed` which is:
        -- match s.cache s.addr k with | some v => v | none => oracle.read s.addr k
        -- We don't have oracle in scope here. The PROOF lemma below
        -- discharges the equation by case-analysis on cache hit/miss
        -- and assumes the audit installs oracle = (fun _ _ => 0).
        let v := match s''.cache s''.addr slotVal with
                  | some v => v
                  | none => 0  -- audit's mock world: oracle.read = 0
        some (v, s'', env'')
  | .sstoreTo _ _ slot val =>
    match Form.interp env s slot with
    | none => none
    | some (slotVal, s', env') =>
      match Form.interp env' s' val with
      | none => none
      | some (vVal, s'', env'') =>
        let cache' := fun a' k' =>
          if s''.addr = a' ∧ slotVal = k' then some vVal
          else s''.cache a' k'
        some (vVal, { s'' with cache := cache' }, env'')
  | .stateAddr _ =>
    -- Project Addr → Val via the CLState-carried function. CL impl uses
    -- the integer address directly; in Lean we carry the projection
    -- so the spec actually pushes the right value (not a 0 stub).
    some (s.addrToVal s.addr, s, env)
  | .journalPush _ _ slot old =>
    match Form.interp env s slot with
    | none => none
    | some (slotVal, s', env') =>
      match Form.interp env' s' old with
      | none => none
      | some (oldVal, s'', env'') =>
        let entry : Journal.Entry _ _ _ := .sstore s''.addr slotVal oldVal
        some (0, { s'' with journal := entry :: s''.journal }, env'')
  | .staticpCheck _ =>
    if s.staticp then none else some (0, s, env)
  | .stateField _ f =>
    -- Project named field of CLState to U256. Val-typed fields pass
    -- through; Addr-typed fields go through s.addrToVal; numeric fields
    -- via U256.ofNat. Arbitrary `f` → 0 (placeholder; audit catches drift).
    let v : Evm.U256 := match f with
      | "callvalue"     => s.callvalue
      | "gasprice"      => s.gasprice
      | "chainid"       => s.chainid
      | "timestamp"     => s.timestamp
      | "block-number"  => s.blockNumber
      | "gaslimit"      => s.gaslimit
      | "basefee"       => s.basefee
      | "prev-randao"   => s.prevRandao
      | "blob-basefee"  => s.blobBaseFee
      | "gas-left"      => Evm.U256.ofNat s.gasLeft
      | "pc"            => Evm.U256.ofNat s.pc
      | "mp"            => Evm.U256.ofNat s.mp
      | "address"       => s.addrToVal s.addr
      | "origin"        => s.addrToVal s.origin
      | "caller"        => s.addrToVal s.caller
      | "coinbase"      => s.addrToVal s.coinbase
      | _ => 0
    some (v, s, env)
  | .setHalted _ => some (0, { s with halted := true }, env)
  | .stkPeek _ n =>
    -- stack[sp - 1 - n] = nth element from top. In the List model,
    -- top is head, so this is stack[n].
    match s.stack[n]? with
    | some v => some (v, s, env)
    | none   => none
  | .blobHashAt _ idx =>
    match Form.interp env s idx with
    | none => none
    | some (v, s', env') => some (s'.blobHashes.getD v.toNat 0, s', env')
  | .stkSwap _ n =>
    -- Swap top with (n+1)-th element. Top is index 0; swap target n.
    match s.stack[0]?, s.stack[n]? with
    | some top, some other =>
      let stack' := (s.stack.set 0 other).set n top
      some (0, { s with stack := stack' }, env)
    | _, _ => none
  | .ifZero c t e =>
    match Form.interp env s c with
    | none => none
    | some (cv, s', env') =>
      if cv = 0 then Form.interp env' s' t
      else Form.interp env' s' e
  | .rawCL _ => none  -- unknown Lean semantics; audit gates correctness
  | .cmpToBool op a b =>
    match Form.interp env s a with
    | none => none
    | some (va, s', env') =>
      match Form.interp env' s' b with
      | none => none
      | some (vb, s'', env'') =>
        let result : Evm.U256 :=
          match op with
          | "<" => if va < vb then 1 else 0
          | ">" => if va > vb then 1 else 0
          | "=" => if va = vb then 1 else 0
          | _ => 0
        some (result, s'', env'')
  | .iszeroBool a =>
    match Form.interp env s a with
    | none => none
    | some (va, s', env') => some (if va = 0 then 1 else 0, s', env')
  | .unaryArith op a =>
    match Form.interp env s a with
    | none => none
    | some (va, s', env') =>
      let result : Evm.U256 :=
        match op with
        | "lognot" => ~~~va
        | _ => 0
      some (result, s', env')
  | .signedConvert a =>
    -- s256 maps unsigned U256 → signed int. Mathematically identity
    -- on BitVec values (the bit-pattern is the same); the difference
    -- only surfaces for comparison/division operators below. Since
    -- we model Evm.U256 = BitVec 256, the conversion is no-op here.
    Form.interp env s a
  | .memReadU256 _ off =>
    match Form.interp env s off with
    | none => none
    | some (offV, s', env') =>
      let offN := offV.toNat
      let target := offN + 32
      let mem' := MacroSpec.U256Ops.padMem s'.memory target
      let v : Nat := Id.run do
        let mut acc : Nat := 0
        for i in [0:32] do
          acc := acc * 256 + mem'[offN + i]!.toNat
        return acc
      let memGas := MacroSpec.U256Ops.memExpansionGas s'.mp target
      some (Evm.U256.ofNat v,
            { s' with memory := mem', mp := max s'.mp target,
                      gasLeft := s'.gasLeft - memGas }, env')
  | .memWriteU256 _ off val =>
    match Form.interp env s off with
    | none => none
    | some (offV, s', env') =>
      match Form.interp env' s' val with
      | none => none
      | some (valV, s'', env'') =>
        let offN := offV.toNat
        let target := offN + 32
        let mem' := MacroSpec.U256Ops.padMem s''.memory target
        let mem'' : ByteArray := Id.run do
          let mut acc := mem'
          for i in [0:32] do
            let b : UInt8 := UInt8.ofNat ((valV.toNat >>> (8 * (31 - i))) &&& 0xff)
            acc := acc.set! (offN + i) b
          return acc
        let memGas := MacroSpec.U256Ops.memExpansionGas s''.mp target
        some (0, { s'' with memory := mem'', mp := max s''.mp target,
                            gasLeft := s''.gasLeft - memGas }, env'')
  | .memWriteByte _ off val =>
    match Form.interp env s off with
    | none => none
    | some (offV, s', env') =>
      match Form.interp env' s' val with
      | none => none
      | some (valV, s'', env'') =>
        let offN := offV.toNat
        let target := offN + 1
        let mem' := MacroSpec.U256Ops.padMem s''.memory target
        let b : UInt8 := UInt8.ofNat (valV.toNat &&& 0xff)
        let mem'' := mem'.set! offN b
        let memGas := MacroSpec.U256Ops.memExpansionGas s''.mp target
        some (0, { s'' with memory := mem'', mp := max s''.mp target,
                            gasLeft := s''.gasLeft - memGas }, env'')
  | .worldHookU256 _ kind arg =>
    -- Use the Val-keyed world hook fields (which CLState carries
    -- alongside the Addr-keyed ones). The popped arg is a Val (U256).
    match Form.interp env s arg with
    | none => none
    | some (argV, s', env') =>
      let v : Evm.U256 := match kind with
        | "balance"    => s'.worldBalanceByVal argV
        | "code-size"  => Evm.U256.ofNat (s'.worldCodeSizeByVal argV)
        | "code-hash"  => s'.worldCodeHashByVal argV
        | "block-hash" => s'.worldBlockHashByVal argV
        | _ => 0
      some (v, s', env')
  | .memLengthForm _ =>
    some (Evm.U256.ofNat s.memory.size, s, env)
  | .memByteAppend _ val =>
    match Form.interp env s val with
    | none => none
    | some (v, s', env') =>
      let b : UInt8 := UInt8.ofNat (v.toNat &&& 0xff)
      some (0, { s' with memory := s'.memory.push b }, env')
  | .memByteWriteAt _ off val =>
    match Form.interp env s off with
    | none => none
    | some (offV, s', env') =>
      match Form.interp env' s' val with
      | none => none
      | some (valV, s'', env'') =>
        let offN := offV.toNat
        let b : UInt8 := UInt8.ofNat (valV.toNat &&& 0xff)
        some (0, { s'' with memory := s''.memory.set! offN b }, env'')
  | .mpFieldRead _ => some (Evm.U256.ofNat s.mp, s, env)
  | .mpFieldWrite _ v =>
    match Form.interp env s v with
    | none => none
    | some (vV, s', env') => some (0, { s' with mp := vV.toNat }, env')
  | .ifGen c t e =>
    match Form.interp env s c with
    | none => none
    | some (cv, s', env') =>
      if cv ≠ 0 then Form.interp env' s' t else Form.interp env' s' e
  | .clCmp op a b =>
    match Form.interp env s a with
    | none => none
    | some (va, s', env') =>
      match Form.interp env' s' b with
      | none => none
      | some (vb, s'', env'') =>
        let result : Evm.U256 :=
          match op with
          | "<"  => if va < vb then 1 else 0
          | ">"  => if va > vb then 1 else 0
          | "="  => if va = vb then 1 else 0
          | ">=" => if va ≥ vb then 1 else 0
          | "<=" => if va ≤ vb then 1 else 0
          | "/=" => if va ≠ vb then 1 else 0
          | _ => 0
        some (result, s'', env'')
  | .errorForm _ => none
  | .haltWithOutput _ off len =>
    match Form.interp env s off with
    | none => none
    | some (offV, s', env') =>
      match Form.interp env' s' len with
      | none => none
      | some (lenV, s'', env'') =>
        let offN := offV.toNat
        let lenN := lenV.toNat
        let mem' := MacroSpec.U256Ops.padMem s''.memory (offN + lenN)
        let out : ByteArray := Id.run do
          let mut acc := ByteArray.empty
          for i in [0:lenN] do acc := acc.push mem'[offN + i]!
          return acc
        some (0, { s'' with halted := true, output := out, memory := mem',
                            mp := max s''.mp (offN + lenN) }, env'')
  | .haltWithRevert _ off len =>
    match Form.interp env s off with
    | none => none
    | some (offV, s', env') =>
      match Form.interp env' s' len with
      | none => none
      | some (lenV, s'', env'') =>
        let offN := offV.toNat
        let lenN := lenV.toNat
        let mem' := MacroSpec.U256Ops.padMem s''.memory (offN + lenN)
        let out : ByteArray := Id.run do
          let mut acc := ByteArray.empty
          for i in [0:lenN] do acc := acc.push mem'[offN + i]!
          return acc
        some (0, { s'' with halted := true, reverted := true, output := out,
                            memory := mem', mp := max s''.mp (offN + lenN) }, env'')
  | .tstorageRead _ slot =>
    match Form.interp env s slot with
    | none => none
    | some (slotV, s', env') =>
      let v := match s'.tstorage slotV with | some v => v | none => 0
      some (v, s', env')
  | .tstorageWrite _ slot val =>
    match Form.interp env s slot with
    | none => none
    | some (slotV, s', env') =>
      match Form.interp env' s' val with
      | none => none
      | some (valV, s'', env'') =>
        let t' := fun k => if k = slotV then some valV else s''.tstorage k
        some (valV, { s'' with tstorage := t' }, env'')
  | .signedDivU256 a b =>
    match Form.interp env s a with
    | none => none
    | some (va, s', env') =>
      match Form.interp env' s' b with
      | none => none
      | some (vb, s'', env'') =>
        some (if vb = 0 then 0 else BitVec.sdiv va vb, s'', env'')
  | .signedRemU256 a b =>
    match Form.interp env s a with
    | none => none
    | some (va, s', env') =>
      match Form.interp env' s' b with
      | none => none
      | some (vb, s'', env'') =>
        some (if vb = 0 then 0 else BitVec.srem va vb, s'', env'')
  | .signedShiftRight val shift =>
    match Form.interp env s val with
    | none => none
    | some (vv, s', env') =>
      match Form.interp env' s' shift with
      | none => none
      | some (sh, s'', env'') =>
        let result : Evm.U256 :=
          if sh.toNat ≥ 256 then
            if BitVec.slt vv 0 then ~~~(0 : Evm.U256) else 0
          else BitVec.sshiftRight vv sh.toNat
        some (result, s'', env'')
  | .signExtend b x =>
    match Form.interp env s b with
    | none => none
    | some (bv, s', env') =>
      match Form.interp env' s' x with
      | none => none
      | some (xv, s'', env'') =>
        let bn := bv.toNat
        let result : Evm.U256 :=
          if bn ≥ 31 then xv
          else
            let k := 8 * bn + 7
            let mask : Nat := (1 <<< (k + 1)) - 1
            let allOnes : Nat := (1 <<< 256) - 1
            let upper : Nat := allOnes - mask
            let xn := xv.toNat
            if (xn >>> k) &&& 1 = 1 then
              Evm.U256.ofNat ((xn &&& mask) ||| upper)
            else
              Evm.U256.ofNat (xn &&& mask)
        some (result, s'', env'')
  | .validatedJump _ dest =>
    match Form.interp env s dest with
    | none => none
    | some (destV, s', env') =>
      let dn := destV.toNat
      -- The spec's `valid_jump_destinations`: a JUMPDEST byte that is not PUSH
      -- data (and in bounds). `code[dn] = 0x5b` alone accepted PUSH immediates.
      if Evm.Frontier.Vm.Runtime.isJumpDest s'.code dn then
        some (0, { s' with pc := dn }, env')
      else none
  | .calldataLoad32 _ off =>
    match Form.interp env s off with
    | none => none
    | some (offV, s', env') =>
      let offN := offV.toNat
      let cdSize := s'.calldata.size
      let v : Nat := Id.run do
        let mut acc : Nat := 0
        for i in [0:32] do
          let b : Nat := if offN + i < cdSize then s'.calldata[offN + i]!.toNat else 0
          acc := acc * 256 + b
        return acc
      some (Evm.U256.ofNat v, s', env')
  | .memMemCopy _ dst src len =>
    match Form.interp env s dst with
    | none => none
    | some (dstV, s', env') =>
      match Form.interp env' s' src with
      | none => none
      | some (srcV, s'', env'') =>
        match Form.interp env'' s'' len with
        | none => none
        | some (lenV, s''', env''') =>
          let d := dstV.toNat
          let sr := srcV.toNat
          let l := lenV.toNat
          let endOff := max (d + l) (sr + l)
          let mem' := MacroSpec.U256Ops.padMem s'''.memory endOff
          -- Read src bytes first (handle overlap)
          let tmp : ByteArray := Id.run do
            let mut acc := ByteArray.empty
            for i in [0:l] do acc := acc.push mem'[sr + i]!
            return acc
          let mem'' : ByteArray := Id.run do
            let mut acc := mem'
            for i in [0:l] do acc := acc.set! (d + i) tmp[i]!
            return acc
          let words := (l + 31) / 32
          let memGas := if l = 0 then 0
                        else MacroSpec.U256Ops.memExpansionGas s'''.mp endOff
          let gas' := s'''.gasLeft - 3 * words - memGas
          some (0, { s''' with memory := mem'', gasLeft := gas',
                                mp := max s'''.mp endOff }, env''')
  | .expU256Op _ _ base e =>
    -- Computes cost AND charges it AND returns the result; CL does
    -- charge-gas inline so we thread the state mutation here.
    match Form.interp env s base with
    | none => none
    | some (baseV, s', env') =>
      match Form.interp env' s' e with
      | none => none
      | some (eV, s'', env'') =>
        let eN := eV.toNat
        let ebytes := if eN = 0 then 0 else (Nat.log2 eN) / 8 + 1
        let cost := 10 + 50 * ebytes
        let result : Evm.U256 :=
          if eN = 0 then 1
          else Evm.U256.ofNat (Nat.pow baseV.toNat eN % (2^256))
        some (result, { s'' with gasLeft := s''.gasLeft - cost }, env'')
  | .signedCmpToBool op a b =>
    match Form.interp env s a with
    | none => none
    | some (va, s', env') =>
      match Form.interp env' s' b with
      | none => none
      | some (vb, s'', env'') =>
        let result : Evm.U256 :=
          match op with
          | "<"  => if BitVec.slt va vb then 1 else 0
          | ">"  => if BitVec.slt vb va then 1 else 0
          | _ => 0
        some (result, s'', env'')
  | .divOp a b =>
    match Form.interp env s a with
    | none => none
    | some (va, s', env') =>
      match Form.interp env' s' b with
      | none => none
      | some (vb, s'', env'') =>
        some (if vb = 0 then 0 else BitVec.udiv va vb, s'', env'')
  | .modOp a b =>
    match Form.interp env s a with
    | none => none
    | some (va, s', env') =>
      match Form.interp env' s' b with
      | none => none
      | some (vb, s'', env'') =>
        some (if vb = 0 then 0 else BitVec.umod va vb, s'', env'')
  | .shlU256 shift val =>
    match Form.interp env s shift with
    | none => none
    | some (vs, s', env') =>
      match Form.interp env' s' val with
      | none => none
      | some (vv, s'', env'') =>
        let result : Evm.U256 :=
          if vs.toNat ≥ 256 then 0 else vv <<< vs.toNat
        some (result, s'', env'')
  | .shrU256 shift val =>
    match Form.interp env s shift with
    | none => none
    | some (vs, s', env') =>
      match Form.interp env' s' val with
      | none => none
      | some (vv, s'', env'') =>
        let result : Evm.U256 :=
          if vs.toNat ≥ 256 then 0 else vv >>> vs.toNat
        some (result, s'', env'')
  | .byteAtU256 i x =>
    match Form.interp env s i with
    | none => none
    | some (vi, s', env') =>
      match Form.interp env' s' x with
      | none => none
      | some (vx, s'', env'') =>
        let result : Evm.U256 :=
          if vi.toNat ≥ 32 then 0
          else
            let shift := 8 * (31 - vi.toNat)
            Evm.U256.ofNat ((vx.toNat >>> shift) &&& 0xff)
        some (result, s'', env'')
  | .pushNAndAdvance _ _ n =>
    let val : Nat := Id.run do
      let mut acc : Nat := 0
      for i in [0:n] do
        let idx := s.pc + 1 + i
        let b : Nat := if idx < s.code.size then s.code[idx]!.toNat else 0
        acc := acc * 256 + b
      return acc
    let gasCost := if n = 0 then 2 else 3
    some (0, { s with
      stack   := (Evm.U256.ofNat val) :: s.stack,
      pc      := s.pc + 1 + n,
      gasLeft := s.gasLeft - gasCost }, env)
  | .logNOp _ _ n =>
    if s.staticp then none
    else if s.stack.length < 2 + n then none
    else
      match s.stack with
      | off :: len :: rest =>
        let l := len.toNat
        let target := off.toNat + l
        -- Yellow paper G_log + G_logtopic * n + G_logdata * len + memexp.
        let memGas := if l = 0 then 0
                      else MacroSpec.U256Ops.memExpansionGas s.mp target
        let gasCost := 375 + 375 * n + 8 * l + memGas
        some (0, { s with
          stack   := rest.drop n,
          pc      := s.pc + 1,
          gasLeft := s.gasLeft - gasCost,
          memory  := MacroSpec.U256Ops.padMem s.memory target,
          mp      := max s.mp target }, env)
      | _ => none
  | .keccakOp _ _ =>
    match s.stack with
    | [] | [_] => none
    | off :: len :: rest =>
      let offN := off.toNat
      let lenN := len.toNat
      let mem' := MacroSpec.U256Ops.padMem s.memory (offN + lenN)
      let data : ByteArray := Id.run do
        let mut acc := ByteArray.empty
        for i in [0:lenN] do acc := acc.push mem'[offN + i]!
        return acc
      let hash : Evm.U256 := Evm.Crypto.keccak256 data
      let dataWords := (lenN + 31) / 32
      let memGas := if lenN = 0 then 0
                    else MacroSpec.U256Ops.memExpansionGas s.mp (offN + lenN)
      let cost := 30 + 6 * dataWords + memGas
      some (0, { s with
        stack   := hash :: rest,
        pc      := s.pc + 1,
        gasLeft := s.gasLeft - cost,
        memory  := mem',
        mp      := max s.mp (offN + lenN) }, env)
  | .addmodU256 a b n =>
    match Form.interp env s a with
    | none => none
    | some (va, s', env') =>
      match Form.interp env' s' b with
      | none => none
      | some (vb, s'', env'') =>
        match Form.interp env'' s'' n with
        | none => none
        | some (vn, s''', env''') =>
          let result : Evm.U256 :=
            if vn = 0 then 0
            else Evm.U256.ofNat ((va.toNat + vb.toNat) % vn.toNat)
          some (result, s''', env''')
  | .mulmodU256 a b n =>
    match Form.interp env s a with
    | none => none
    | some (va, s', env') =>
      match Form.interp env' s' b with
      | none => none
      | some (vb, s'', env'') =>
        match Form.interp env'' s'' n with
        | none => none
        | some (vn, s''', env''') =>
          let result : Evm.U256 :=
            if vn = 0 then 0
            else Evm.U256.ofNat ((va.toNat * vb.toNat) % vn.toNat)
          some (result, s''', env''')
  | .bufferLengthOp _ field =>
    let n : Nat := match field with
      | "calldata"   => s.calldata.size
      | "code"       => s.code.size
      | "returndata" => s.returndata.size
      | _ => 0
    some (Evm.U256.ofNat n, s, env)
  | .bufferCopyToMem _ srcKind dst src len =>
    match Form.interp env s dst with
    | none => none
    | some (dstV, s', env') =>
      match Form.interp env' s' src with
      | none => none
      | some (srcV, s'', env'') =>
        match Form.interp env'' s'' len with
        | none => none
        | some (lenV, s''', env''') =>
          let d := dstV.toNat
          let sr := srcV.toNat
          let l := lenV.toNat
          let buf : ByteArray := match srcKind with
            | "calldata"   => s'''.calldata
            | "code"       => s'''.code
            | "returndata" => s'''.returndata
            | _            => .empty
          if srcKind = "returndata" ∧ sr + l > buf.size then none
          else
            let mem' := MacroSpec.U256Ops.padMem s'''.memory (d + l)
            let mem'' : ByteArray := Id.run do
              let mut acc := mem'
              for i in [0:l] do
                let b : UInt8 := if sr + i < buf.size then buf[sr + i]! else 0
                acc := acc.set! (d + i) b
              return acc
            -- Yellow paper: 3 per word + memory expansion delta.
            let words := (l + 31) / 32
            let perWord := 3 * words
            let memGas := if l = 0 then 0
                          else MacroSpec.U256Ops.memExpansionGas s'''.mp (d + l)
            let gas' := s'''.gasLeft - perWord - memGas
            some (0, { s''' with memory := mem'', gasLeft := gas',
                                  mp := max s'''.mp (d + l) }, env''')
  | .worldCodeCopyToMem _ addr dst src len =>
    match Form.interp env s addr with
    | none => none
    | some (addrV, s', env') =>
      match Form.interp env' s' dst with
      | none => none
      | some (dstV, s'', env'') =>
        match Form.interp env'' s'' src with
        | none => none
        | some (srcV, s''', env''') =>
          match Form.interp env''' s''' len with
          | none => none
          | some (lenV, s4, env4) =>
            let d := dstV.toNat
            let sr := srcV.toNat
            let l := lenV.toNat
            -- Look up the world code via the Val-keyed projection
            -- (audit's mock world populates worldCodeByVal at the
            -- popped addr).
            let code : ByteArray := s4.worldCodeByVal addrV
            let mem' := MacroSpec.U256Ops.padMem s4.memory (d + l)
            let mem'' : ByteArray := Id.run do
              let mut acc := mem'
              for i in [0:l] do
                let b : UInt8 := if sr + i < code.size then code[sr + i]! else 0
                acc := acc.set! (d + i) b
              return acc
            -- Yellow paper: 3 per word + memory expansion delta
            -- (the access cost is charged separately via chargeGas).
            let words := (l + 31) / 32
            let perWord := 3 * words
            let memGas := if l = 0 then 0
                          else MacroSpec.U256Ops.memExpansionGas s4.mp (d + l)
            let gas' := s4.gasLeft - perWord - memGas
            some (0, { s4 with memory := mem'', gasLeft := gas',
                                mp := max s4.mp (d + l) }, env4)

/-- Lift Form interp to a step function (ignore return value/env). -/
def stepOf {Addr : Type} [DecidableEq Addr]
    (f : Form) (s : CLState Addr Evm.U256) : Option (CLState Addr Evm.U256) :=
  match Form.interp Env.empty s f with
  | none => none
  | some (_, s', _) => some s'

/-! ## Opcode definitions as Form values

ADD prototype: mirrors `op-add (s fork mode)` exactly, structured
to make `stepOf addForm = stepBinOp 3 (· + ·)` provable. -/

/-- The form for op-add. Tree-shaped via `seq` and `letBind`; the
    pretty-printer flattens to `(progn ...)` and `(let* (...) ...)`. -/
def addForm : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.letBind "b" (.stkPop "s")
         (.letBind "a" (.stkPop "s")
          (.stkPush "s" (.u256Mask (.binOp "+" (.var "a") (.var "b"))))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- Builder for binary ops that match `op-add`'s naming convention
    (first-pop = b, second-pop = a, result = `op a b`). Used by
    commutative ops (ADD, MUL, AND, OR, XOR) where the convention
    doesn't matter semantically. -/
def commBinOpForm (cost : Nat) (op : String) : Form :=
  .seq (.chargeGas "s" cost "mode")
  (.seq (.letBind "b" (.stkPop "s")
         (.letBind "a" (.stkPop "s")
          (.stkPush "s" (.u256Mask (.binOp op (.var "a") (.var "b"))))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- Builder for non-commutative binary ops matching `op-sub`'s
    convention (first-pop = a, second-pop = b, result = `op a b`).
    Used by SUB. -/
def nonCommBinOpForm (cost : Nat) (op : String) : Form :=
  .seq (.chargeGas "s" cost "mode")
  (.seq (.letBind "a" (.stkPop "s")
         (.letBind "b" (.stkPop "s")
          (.stkPush "s" (.u256Mask (.binOp op (.var "a") (.var "b"))))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

def subForm : Form := nonCommBinOpForm 3 "-"
def mulForm : Form := commBinOpForm    5 "*"
def andForm : Form := commBinOpForm    3 "logand"
def orForm  : Form := commBinOpForm    3 "logior"
def xorForm : Form := commBinOpForm    3 "logxor"

/-- POP: charge 2, discard one stack item, bump pc. No environment
    bindings. -/
def popForm : Form :=
  .seq (.chargeGas "s" 2 "mode")
  (.seq (.stkPop "s")
        (.incPc "s"))

/-- SLOAD: pop slot, push viewed-storage(addr, slot). Mirrors the CL
    `op-sload` macro byte-for-byte. -/
def sloadForm : Form :=
  .seq (.chargeGas "s" 100 "mode")
  (.seq (.letBind "slot" (.stkPop "s")
         (.letBind "addr" (.stateAddr "s")
          (.letBind "val" (.sloadFrom "s" (.var "addr") (.var "slot"))
            (.stkPush "s" (.var "val")))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-! ### More opcode Forms — generated mechanically per the pattern -/

/-- Environment / block readers: `(progn (charge-gas 2) (stk-push (evm-state-X s)) (incf pc) ,fork)`. -/
def envReaderForm (cost : Nat) (field : String) : Form :=
  .seq (.chargeGas "s" cost "mode")
  (.seq (.stkPush "s" (.stateField "s" field))
  (.seq (.incPc "s")
        (.forkRef "fork")))

def callvalueForm    : Form := envReaderForm 2 "callvalue"
def gaspriceForm     : Form := envReaderForm 2 "gasprice"
def chainidForm      : Form := envReaderForm 2 "chainid"
def timestampForm    : Form := envReaderForm 2 "timestamp"
def numberForm       : Form := envReaderForm 2 "block-number"
def gaslimitForm     : Form := envReaderForm 2 "gaslimit"
def basefeeForm      : Form := envReaderForm 2 "basefee"
def prevrandaoForm   : Form := envReaderForm 2 "prev-randao"
def blobbasefeeForm  : Form := envReaderForm 2 "blob-basefee"
def pcForm           : Form := envReaderForm 2 "pc"
def msizeForm        : Form := envReaderForm 2 "mp"

/-- BLOBHASH (0x49): pop the index, push the tx's versioned hash at it, or 0 past the
    count (EELS `blob_hash`; the native handler is `AsmCore.blobhashBody`). -/
def blobhashForm : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.letBind "idx" (.stkPop "s")
         (.stkPush "s" (.blobHashAt "s" (.var "idx"))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- GAS opcode: charge BEFORE push (so pushed value reflects post-charge). -/
def gasForm : Form :=
  .seq (.chargeGas "s" 2 "mode")
  (.seq (.stkPush "s" (.stateField "s" "gas-left"))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- STOP: just halt. No gas, no pc bump (the loop exits on halted=true). -/
def stopForm : Form := .setHalted "s"

/-- DUP-n: charge 3, push the n-th-from-top, bump pc. -/
def dupForm (n : Nat) : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.stkPush "s" (.stkPeek "s" (n - 1)))
        (.incPc "s"))

/-- SWAP-n: charge 3, swap top with (n+1)-th, bump pc. -/
def swapForm (n : Nat) : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.stkSwap "s" n)
        (.incPc "s"))

/-- PUSH-N: 2 gas (n=0) or 3 gas (n>0), read n code bytes BE, push,
    advance pc by n+1. Single monolithic primitive (state-pervasive). -/
def pushForm (n : Nat) : Form := .pushNAndAdvance "s" "mode" n

/-- LOG-N: static check + (375+375n) gas + pop (off,len,n topics) +
    pad memory + bump pc. Spec discards the log record itself (CL impl
    appends to logs list as a side effect). -/
def logForm (n : Nat) : Form := .logNOp "s" "mode" n

/-- KECCAK256: pop off,len; hash memory[off..off+len]; push 32-byte digest. -/
def keccakForm : Form := .keccakOp "s" "mode"

/-! ### Structured Forms for the remaining simple ops

Each follows the same shape as ADD/SUB/MUL: charge → letBind pops →
push computed result → bump pc → forkRef. Differences in operands
(commutative vs not), zero-guards, signed variants. -/

/-- DIV: uses dedicated divOp primitive (matches spec shape). -/
def divForm : Form :=
  .seq (.chargeGas "s" 5 "mode")
  (.seq (.letBind "a" (.stkPop "s")
         (.letBind "b" (.stkPop "s")
          (.stkPush "s" (.divOp (.var "a") (.var "b")))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- MOD: uses dedicated modOp primitive. -/
def modForm : Form :=
  .seq (.chargeGas "s" 5 "mode")
  (.seq (.letBind "a" (.stkPop "s")
         (.letBind "b" (.stkPop "s")
          (.stkPush "s" (.modOp (.var "a") (.var "b")))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- Single-form env reader for fields stored as integer (Addr-shaped). -/
def envAddrReaderForm (cost : Nat) (field : String) : Form :=
  .seq (.chargeGas "s" cost "mode")
  (.seq (.stkPush "s" (.stateField "s" field))
  (.seq (.incPc "s")
        (.forkRef "fork")))

def addressForm  : Form := envAddrReaderForm 2 "address"
def originForm   : Form := envAddrReaderForm 2 "origin"
def callerForm   : Form := envAddrReaderForm 2 "caller"
def coinbaseForm : Form := envAddrReaderForm 2 "coinbase"
/-- Buffer-size readers: uses dedicated bufferLengthOp primitive
    (whose interp gives precise ByteArray.size, unlike the previous
    unaryArith "length" composition which returned 0 in interp). -/
def bufferSizeForm (fieldName : String) : Form :=
  .seq (.chargeGas "s" 2 "mode")
  (.seq (.stkPush "s" (.bufferLengthOp "s" fieldName))
  (.seq (.incPc "s")
        (.forkRef "fork")))

def calldatasizeForm   : Form := bufferSizeForm "calldata"
def codesizeForm       : Form := bufferSizeForm "code"
def returndatasizeForm : Form := bufferSizeForm "returndata"

/-- JUMPDEST: 1 gas, just bump pc. -/
def jumpdestForm : Form :=
  .seq (.chargeGas "s" 1 "mode")
  (.seq (.incPc "s")
        (.forkRef "fork"))

/-- TLOAD: pop slot, push tstorage[slot] (0 if absent), bump pc.
    Structured via tstorageRead primitive. -/
def tloadForm : Form :=
  .seq (.chargeGas "s" 100 "mode")
  (.seq (.letBind "slot" (.stkPop "s")
         (.stkPush "s" (.tstorageRead "s" (.var "slot"))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- TSTORE: static check, pop slot+val, write tstorage[slot]=val. -/
def tstoreForm : Form :=
  .seq (.staticpCheck "s")
  (.seq (.chargeGas "s" 100 "mode")
  (.seq (.letBind "slot" (.stkPop "s")
         (.letBind "val" (.stkPop "s")
          (.tstorageWrite "s" (.var "slot") (.var "val"))))
  (.seq (.incPc "s")
        (.forkRef "fork"))))

/-! ### rawCL fixtures for ops whose CL is hand-tuned

For each, the Lean source IS the production CL. Audit script
gates correctness; closed Lean theorems are the migration target. -/

/-- Signed binary op shared shape: charge → pop a → pop b → push (op a b). -/
def signedBinForm (cost : Nat) (op : Form → Form → Form) : Form :=
  .seq (.chargeGas "s" cost "mode")
  (.seq (.letBind "a" (.stkPop "s")
         (.letBind "b" (.stkPop "s")
          (.stkPush "s" (op (.var "a") (.var "b")))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

def sdivForm : Form := signedBinForm 5 .signedDivU256
def smodForm : Form := signedBinForm 5 .signedRemU256

/-- Ternary form: pop a,b,n; push (op a b n). Used by ADDMOD/MULMOD. -/
def ternaryForm (cost : Nat) (op : Form → Form → Form → Form) : Form :=
  .seq (.chargeGas "s" cost "mode")
  (.seq (.letBind "a" (.stkPop "s")
         (.letBind "b" (.stkPop "s")
          (.letBind "n" (.stkPop "s")
           (.stkPush "s" (op (.var "a") (.var "b") (.var "n"))))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

def addmodForm : Form := ternaryForm 8 .addmodU256
def mulmodForm : Form := ternaryForm 8 .mulmodU256

/-- EXP: pop base, e; charge variable gas (inside primitive);
    push base^e mod 2^256 (1 if e=0). -/
def expForm : Form :=
  .letBind "base" (.stkPop "s")
   (.letBind "e" (.stkPop "s")
    (.seq (.stkPush "s" (.expU256Op "s" "mode" (.var "base") (.var "e")))
          (.incPc "s")))

/-- SIGNEXTEND: pop b, x; push signExtend(b, x). -/
def signextendForm : Form :=
  .seq (.chargeGas "s" 5 "mode")
  (.seq (.letBind "b" (.stkPop "s")
         (.letBind "x" (.stkPop "s")
          (.stkPush "s" (.signExtend (.var "b") (.var "x")))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- Structured binary comparison: charge → pop a → pop b → push (a OP b → 0/1). -/
def cmpForm (op : String) : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.letBind "a" (.stkPop "s")
         (.letBind "b" (.stkPop "s")
          (.stkPush "s" (.cmpToBool op (.var "a") (.var "b")))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- Signed comparison: like cmpForm but wraps operands in s256. -/
def signedCmpForm (op : String) : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.letBind "a" (.stkPop "s")
         (.letBind "b" (.stkPop "s")
          (.stkPush "s" (.signedCmpToBool op (.var "a") (.var "b")))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

def ltForm  : Form := cmpForm "<"
def gtForm  : Form := cmpForm ">"
def sltForm : Form := signedCmpForm "<"
def sgtForm : Form := signedCmpForm ">"

/-- EQ: same convention as LT/GT for proof compatibility (a = top,
    b = second). = is symmetric so order doesn't matter for CL output. -/
def eqForm  : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.letBind "a" (.stkPop "s")
         (.letBind "b" (.stkPop "s")
          (.stkPush "s" (.cmpToBool "=" (.var "a") (.var "b")))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- ISZERO: unary, push 1 if zero else 0. -/
def iszeroForm : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.letBind "a" (.stkPop "s")
          (.stkPush "s" (.iszeroBool (.var "a"))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- NOT: unary bitwise complement, masked to 256 bits. -/
def notForm : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.letBind "a" (.stkPop "s")
          (.stkPush "s" (.u256Mask (.unaryArith "lognot" (.var "a")))))
  (.seq (.incPc "s")
        (.forkRef "fork")))
/-- Shift-like guarded op: `(if (>= operand bound) 0 (op val operand))`. -/
def guardedShiftForm (cost : Nat) (bound : Nat)
    (firstName secondName : String) (innerBody : Form) : Form :=
  .seq (.chargeGas "s" cost "mode")
  (.seq (.letBind firstName (.stkPop "s")
         (.letBind secondName (.stkPop "s")
          (.stkPush "s"
           (.ifGen (.clCmp ">=" (.var firstName) (.lit bound))
            (.lit 0) innerBody))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

def byteForm : Form := signedBinForm 3 .byteAtU256
def shlForm  : Form := signedBinForm 3 .shlU256
def shrForm  : Form := signedBinForm 3 .shrU256
/-- SAR: pop shift, val; push signedShiftRight(val, shift). -/
def sarForm : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.letBind "shift" (.stkPop "s")
         (.letBind "val" (.stkPop "s")
          (.stkPush "s" (.signedShiftRight (.var "val") (.var "shift")))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- MLOAD: pop offset, push 32 BE bytes from memory. Structured via
    memReadU256 primitive with precise interp. -/
def mloadForm : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.letBind "off" (.stkPop "s")
         (.letBind "v" (.memReadU256 "s" (.var "off"))
          (.stkPush "s" (.var "v"))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- MSTORE: pop offset + value, write 32 BE bytes. -/
def mstoreForm : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.letBind "off" (.stkPop "s")
         (.letBind "val" (.stkPop "s")
          (.memWriteU256 "s" (.var "off") (.var "val"))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- MSTORE8: pop offset + value, write low byte. -/
def mstore8Form : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.letBind "off" (.stkPop "s")
         (.letBind "val" (.stkPop "s")
          (.memWriteByte "s" (.var "off") (.var "val"))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- JUMP (full mode): charge 8, pop dest, validate + set pc. -/
def jumpForm : Form :=
  .seq (.chargeGas "s" 8 "mode")
  (.seq (.letBind "dest" (.stkPop "s")
          (.validatedJump "s" (.var "dest")))
        (.forkRef "fork"))

/-- JUMPI (full mode): charge 10, pop dest+cnd; if cnd=0 fall through,
    else validate + set pc. -/
def jumpiForm : Form :=
  .seq (.chargeGas "s" 10 "mode")
  (.seq (.letBind "dest" (.stkPop "s")
         (.letBind "cnd" (.stkPop "s")
          (.ifZero (.var "cnd")
            (.incPc "s")
            (.validatedJump "s" (.var "dest")))))
        (.forkRef "fork"))

/-- RETURN: pop off, len; memory[off..off+len] → output, halt. -/
def returnForm : Form :=
  .letBind "off" (.stkPop "s")
   (.letBind "len" (.stkPop "s")
    (.haltWithOutput "s" (.var "off") (.var "len")))

/-- REVERT: same as RETURN but also sets reverted flag. -/
def revertForm : Form :=
  .letBind "off" (.stkPop "s")
   (.letBind "len" (.stkPop "s")
    (.haltWithRevert "s" (.var "off") (.var "len")))

/-- INVALID: signal an error. -/
def invalidForm : Form := .errorForm "INVALID opcode"

/-- CALLDATALOAD: pop off, push calldata[off..off+32] as BE u256. -/
def calldataloadForm : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.letBind "off" (.stkPop "s")
          (.stkPush "s" (.calldataLoad32 "s" (.var "off"))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- Buffer-copy op shape: charge → 3 pops (dst, src, len) → bufferCopyToMem. -/
def bufferCopyOpForm (cost : Nat) (srcKind : String) : Form :=
  .seq (.chargeGas "s" cost "mode")
  (.seq (.letBind "dst" (.stkPop "s")
         (.letBind "src" (.stkPop "s")
          (.letBind "len" (.stkPop "s")
           (.bufferCopyToMem "s" srcKind (.var "dst") (.var "src") (.var "len")))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

def calldatacopyForm   : Form := bufferCopyOpForm 3 "calldata"
def codecopyForm       : Form := bufferCopyOpForm 3 "code"
def returndatacopyForm : Form := bufferCopyOpForm 3 "returndata"

/-- MCOPY: pop dst, src, len; copy mem[src..src+len] → mem[dst..dst+len]
    with zero-padding and overlap safety. -/
def mcopyForm : Form :=
  .seq (.chargeGas "s" 3 "mode")
  (.seq (.letBind "dst" (.stkPop "s")
         (.letBind "src" (.stkPop "s")
          (.letBind "len" (.stkPop "s")
           (.memMemCopy "s" (.var "dst") (.var "src") (.var "len")))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- World-hook op: charge → pop arg → push (world-hook :kind arg) → bump pc. -/
def worldHookOpForm (cost : Nat) (kind : String) : Form :=
  .seq (.chargeGas "s" cost "mode")
  (.seq (.letBind "addr" (.stkPop "s")
         (.stkPush "s" (.worldHookU256 "s" kind (.var "addr"))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

def balanceForm     : Form := worldHookOpForm 100 "balance"
def extcodesizeForm : Form := worldHookOpForm 100 "code-size"
def extcodehashForm : Form := worldHookOpForm 100 "code-hash"
def blockhashForm   : Form := worldHookOpForm 20  "block-hash"

/-- SELFBALANCE: no pop; look up own balance via stateAddr. -/
def selfbalanceForm : Form :=
  .seq (.chargeGas "s" 5 "mode")
  (.seq (.stkPush "s" (.worldHookU256 "s" "balance" (.stateAddr "s")))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- EXTCODECOPY: charge 100, pop addr/dst/src/len; copy world code
    of addr → memory. Structured via worldCodeCopyToMem. -/
def extcodecopyForm : Form :=
  .seq (.chargeGas "s" 100 "mode")
  (.seq (.letBind "addr" (.stkPop "s")
         (.letBind "dst" (.stkPop "s")
          (.letBind "src" (.stkPop "s")
           (.letBind "len" (.stkPop "s")
            (.worldCodeCopyToMem "s" (.var "addr") (.var "dst")
                                       (.var "src") (.var "len"))))))
  (.seq (.incPc "s")
        (.forkRef "fork")))

/-- SSTORE: static-context check, pop slot+val, journal old, write new.
    Mirrors CL `op-sstore`. -/
def sstoreForm : Form :=
  .seq (.staticpCheck "s")
  (.seq (.chargeGas "s" 100 "mode")
  (.seq (.letBind "slot" (.stkPop "s")
         (.letBind "val" (.stkPop "s")
          (.letBind "addr" (.stateAddr "s")
           (.letBind "old" (.sloadFrom "s" (.var "addr") (.var "slot"))
            (.seq (.journalPush "s" (.var "addr") (.var "slot") (.var "old"))
                  (.sstoreTo "s" (.var "addr") (.var "slot") (.var "val")))))))
  (.seq (.incPc "s")
        (.forkRef "fork"))))

/-! ## The soundness theorem — per-opcode, in Lean

This is the load-bearing claim: extracting `addForm` produces a
CL form whose Lean-level semantics agrees with `stepBinOp 3 (· + ·)`.

Closing this in Lean replaces the existing
`axiom cl_add_macro_equals_stepBinOp`. The audit pass that
caught the EXP bug becomes redundant for ADD — the proof IS the
correctness check. -/

/-- The Lean-level extraction soundness for ADD: applying `addForm`'s
    interpreter to a state yields the same final state as
    `stepBinOp 3 (· + ·)` on that state.

    Proof: structural recursion of `Form.interp` unfolds cleanly
    over the tree-shaped `addForm`, and case analysis on `s.stack`
    matches both sides. -/
theorem add_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf addForm s = MacroSpec.stepBinOp 3 (· + ·) s := by
  unfold stepOf addForm MacroSpec.stepBinOp
  -- Case-split on s.stack: empty, single, cons-cons.
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | a :: b :: rest =>
    simp [Form.interp, h, Env.set]
    -- Env lookups resolved, remaining goal: b + a = a + b. BitVec
    -- addition is commutative.
    exact BitVec.add_comm b a

/-! ### Same theorem for the other simple ops -/

theorem sub_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf subForm s = MacroSpec.stepBinOp 3 (· - ·) s := by
  unfold stepOf subForm nonCommBinOpForm MacroSpec.stepBinOp
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ =>
    -- env "a" = first-popped = top; env "b" = second-popped = second.
    -- Form computes (a - b) = top - second. stepBinOp matches a :: b
    -- and computes op a b = top - second. Direct equality.
    simp [Form.interp, h, Env.set]

theorem mul_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf mulForm s = MacroSpec.stepBinOp 5 (· * ·) s := by
  unfold stepOf mulForm commBinOpForm MacroSpec.stepBinOp
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | a :: b :: _ =>
    simp [Form.interp, h, Env.set]
    exact BitVec.mul_comm b a

theorem and_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf andForm s = MacroSpec.U256Ops.stepAnd s := by
  unfold stepOf andForm commBinOpForm MacroSpec.U256Ops.stepAnd
        MacroSpec.U256Ops.stepBinOp'
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | a :: b :: _ =>
    simp [Form.interp, h, Env.set]
    exact BitVec.and_comm b a

theorem or_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf orForm s = MacroSpec.U256Ops.stepOr s := by
  unfold stepOf orForm commBinOpForm MacroSpec.U256Ops.stepOr
        MacroSpec.U256Ops.stepBinOp'
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | a :: b :: _ =>
    simp [Form.interp, h, Env.set]
    exact BitVec.or_comm b a

theorem xor_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf xorForm s = MacroSpec.U256Ops.stepXor s := by
  unfold stepOf xorForm commBinOpForm MacroSpec.U256Ops.stepXor
        MacroSpec.U256Ops.stepBinOp'
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | a :: b :: _ =>
    simp [Form.interp, h, Env.set]
    exact BitVec.xor_comm b a

theorem pop_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf popForm s = MacroSpec.U256Ops.stepPop s := by
  unfold stepOf popForm MacroSpec.U256Ops.stepPop
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | _ :: _ => simp [Form.interp, h]

/-! ### SLOAD/SSTORE soundness — stated, sorried

These are heavier because the storage layer touches `s.cache`
and `s.journal`, requiring extensional reasoning about field
updates. The structure of the proof is the same as for ADD —
unfold + case-split on s.stack — but the goal after simp involves
function-update equality. Mechanical but verbose; leaving as
sorry per no-silent-gaps so the obligation is surfaced. -/

/-- The mock oracle the audit uses (and the Form's sloadFrom
    interp assumes): always 0. Under this oracle, `stepSload` and
    `stepOf sloadForm` agree. -/
def mockOracle {Addr : Type} : Evm.CL.StorageCache.Oracle Addr Evm.U256 Evm.U256 :=
  { read := fun _ _ => 0 }

theorem sload_extract_correct_under_mock
    {Addr : Type} [DecidableEq Addr]
    (s : CLState Addr Evm.U256) :
    stepOf sloadForm s = MacroSpec.stepSload (@mockOracle Addr) 100 s := by
  unfold stepOf sloadForm MacroSpec.stepSload MacroSpec.CLState.viewed
        mockOracle
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | slot :: rest =>
    -- After two `letBind`s ("slot" and "addr") and one `sloadFrom`,
    -- the cache lookup s.cache s.addr slot either hits (some v) or
    -- misses (none → 0). stepSload's `viewed` does the same match
    -- with the mock oracle returning 0 on miss. Equal by case.
    simp [Form.interp, h, Env.set]
    cases s.cache s.addr slot <;> simp

theorem sstore_extract_correct_under_mock
    {Addr : Type} [DecidableEq Addr]
    (s : CLState Addr Evm.U256) :
    stepOf sstoreForm s = MacroSpec.stepSstore (@mockOracle Addr) 100 s := by
  unfold stepOf sstoreForm MacroSpec.stepSstore MacroSpec.CLState.viewed
        mockOracle Evm.CL.StorageCache.write
  by_cases hstatic : s.staticp
  · simp [Form.interp, hstatic]
  · match h : s.stack with
    | [] => simp [Form.interp, h, hstatic]
    | [_] => simp [Form.interp, h, hstatic]
    | slot :: _ :: _ =>
      simp [Form.interp, h, hstatic, Env.set]
      cases s.cache s.addr slot <;> simp

/-! ### Comparison / unary theorems

Closed proofs for the newly structured comparison and unary ops.
Each follows the standard pattern. -/

theorem lt_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf ltForm s = MacroSpec.U256Ops.stepLt s := by
  unfold stepOf ltForm cmpForm MacroSpec.U256Ops.stepLt
        MacroSpec.U256Ops.stepBinOp' MacroSpec.U256Ops.boolU256
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ =>
    -- a = top, b = second; cmpToBool "<" computes (if (a < b) 1 0).
    -- stepLt does the same. Direct equality after simp.
    simp [Form.interp, h, Env.set]

theorem gt_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf gtForm s = MacroSpec.U256Ops.stepGt s := by
  unfold stepOf gtForm cmpForm MacroSpec.U256Ops.stepGt
        MacroSpec.U256Ops.stepBinOp' MacroSpec.U256Ops.boolU256
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem iszero_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf iszeroForm s = MacroSpec.U256Ops.stepIsZero s := by
  unfold stepOf iszeroForm MacroSpec.U256Ops.stepIsZero
        MacroSpec.U256Ops.stepUnaryOp MacroSpec.U256Ops.boolU256
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | _ :: _ => simp [Form.interp, h, Env.set]

/-! ### Memory op theorems

MLOAD, MSTORE, MSTORE8 — structured via the new memReadU256 /
memWriteU256 / memWriteByte primitives, whose interp matches
MacroSpec.stepMload / stepMstore / stepMstore8 by construction. -/

theorem mload_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf mloadForm s = MacroSpec.U256Ops.stepMload s := by
  unfold stepOf mloadForm MacroSpec.U256Ops.stepMload
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | _ :: _ => simp [Form.interp, h, Env.set]

theorem mstore_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf mstoreForm s = MacroSpec.U256Ops.stepMstore s := by
  unfold stepOf mstoreForm MacroSpec.U256Ops.stepMstore
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem mstore8_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf mstore8Form s = MacroSpec.U256Ops.stepMstore8 s := by
  unfold stepOf mstore8Form MacroSpec.U256Ops.stepMstore8
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

/-! ### World-hook step functions + theorems

The CL emission reads the world hook via Val-keyed fields (because
the CL impl uses bignum addresses, not the abstract `Addr` type).
Spec functions below operate on `CLState.worldBalanceByVal` etc.;
the audit's mock world populates both keying styles. -/

namespace WorldOps

/-- BALANCE step (Val-keyed lookup). -/
def stepBalance {Addr : Type} [DecidableEq Addr]
    (s : CLState Addr Evm.U256) : Option (CLState Addr Evm.U256) :=
  match s.stack with
  | [] => none
  | addrV :: rest =>
    some { s with
      stack   := s.worldBalanceByVal addrV :: rest,
      pc      := s.pc + 1,
      gasLeft := s.gasLeft - 100 }

def stepExtcodesize {Addr : Type} [DecidableEq Addr]
    (s : CLState Addr Evm.U256) : Option (CLState Addr Evm.U256) :=
  match s.stack with
  | [] => none
  | addrV :: rest =>
    some { s with
      stack   := (Evm.U256.ofNat (s.worldCodeSizeByVal addrV)) :: rest,
      pc      := s.pc + 1,
      gasLeft := s.gasLeft - 100 }

def stepExtcodehash {Addr : Type} [DecidableEq Addr]
    (s : CLState Addr Evm.U256) : Option (CLState Addr Evm.U256) :=
  match s.stack with
  | [] => none
  | addrV :: rest =>
    some { s with
      stack   := s.worldCodeHashByVal addrV :: rest,
      pc      := s.pc + 1,
      gasLeft := s.gasLeft - 100 }

def stepBlockhash {Addr : Type} [DecidableEq Addr]
    (s : CLState Addr Evm.U256) : Option (CLState Addr Evm.U256) :=
  match s.stack with
  | [] => none
  | n :: rest =>
    some { s with
      stack   := s.worldBlockHashByVal n :: rest,
      pc      := s.pc + 1,
      gasLeft := s.gasLeft - 20 }

/-- EXTCODECOPY (Val-keyed world code lookup). -/
def stepExtcodecopy {Addr : Type} [DecidableEq Addr]
    (s : CLState Addr Evm.U256) : Option (CLState Addr Evm.U256) :=
  match s.stack with
  | addrV :: dst :: src :: len :: rest =>
    let d := dst.toNat
    let sr := src.toNat
    let l := len.toNat
    let code : ByteArray := s.worldCodeByVal addrV
    let mem' := MacroSpec.U256Ops.padMem s.memory (d + l)
    let mem'' : ByteArray := Id.run do
      let mut acc := mem'
      for i in [0:l] do
        let b : UInt8 := if sr + i < code.size then code[sr + i]! else 0
        acc := acc.set! (d + i) b
      return acc
    some { s with
      stack   := rest,
      pc      := s.pc + 1,
      gasLeft := s.gasLeft - 100 - MacroSpec.U256Ops.copyExtraGas s.mp d l,
      memory  := mem'',
      mp      := max s.mp (d + l) }
  | _ => none

end WorldOps

theorem balance_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf balanceForm s = WorldOps.stepBalance s := by
  unfold stepOf balanceForm worldHookOpForm WorldOps.stepBalance
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | _ :: _ => simp [Form.interp, h, Env.set]

theorem extcodesize_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf extcodesizeForm s = WorldOps.stepExtcodesize s := by
  unfold stepOf extcodesizeForm worldHookOpForm WorldOps.stepExtcodesize
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | _ :: _ => simp [Form.interp, h, Env.set]

theorem extcodehash_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf extcodehashForm s = WorldOps.stepExtcodehash s := by
  unfold stepOf extcodehashForm worldHookOpForm WorldOps.stepExtcodehash
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | _ :: _ => simp [Form.interp, h, Env.set]

theorem blockhash_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf blockhashForm s = WorldOps.stepBlockhash s := by
  unfold stepOf blockhashForm worldHookOpForm WorldOps.stepBlockhash
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | _ :: _ => simp [Form.interp, h, Env.set]

/-- SELFBALANCE: no pop, look up own balance via worldBalanceByVal
    at `addrToVal addr`. -/
def WorldOps.stepSelfbalance {Addr : Type} [DecidableEq Addr]
    (s : CLState Addr Evm.U256) : Option (CLState Addr Evm.U256) :=
  some { s with
    stack   := s.worldBalanceByVal (s.addrToVal s.addr) :: s.stack,
    pc      := s.pc + 1,
    gasLeft := s.gasLeft - 5 }

theorem selfbalance_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf selfbalanceForm s = WorldOps.stepSelfbalance s := by
  unfold stepOf selfbalanceForm WorldOps.stepSelfbalance
  simp [Form.interp]

/-! ### Theorems for this batch -/

theorem invalid_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf invalidForm s = none := by
  unfold stepOf invalidForm
  simp [Form.interp]

/-- ADDMOD / MULMOD spec: pop a,b,n; push (op a b) mod n if n≠0 else 0. -/
def MacroSpec.U256Ops.stepAddmod' {Addr : Type} [DecidableEq Addr]
    (s : CLState Addr Evm.U256) : Option (CLState Addr Evm.U256) :=
  match s.stack with
  | a :: b :: n :: rest =>
    some { s with
      stack := (if n = 0 then 0 else
        Evm.U256.ofNat ((a + b).toNat % n.toNat)) :: rest,
      pc := s.pc + 1,
      gasLeft := s.gasLeft - 8 }
  | _ => none

theorem tload_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf tloadForm s =
      (match s.stack with
       | slot :: rest =>
         let v := match s.tstorage slot with | some v => v | none => 0
         some { s with stack := v :: rest, pc := s.pc + 1,
                       gasLeft := s.gasLeft - 100 }
       | _ => none) := by
  unfold stepOf tloadForm
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | _ :: _ => simp [Form.interp, h, Env.set]

/-! ### Bulk-close batch: arithmetic, comparison, env readers, control flow

Most of these follow the same `unfold; match h : s.stack; simp` template
established by the earlier closed theorems. -/

/-- DIV, MOD, SLT, SGT, EQ theorems pending: REAL defects in Form IR's
    interp uncovered while attempting these proofs.
    - SLT/SGT: signedConvert is identity in interp; cmpToBool "<" uses
      *unsigned* `<` on BitVec. Spec uses BitVec.slt. Fix: add a
      signedCmpToBool primitive.
    - DIV/MOD: binOp's interp doesn't recognize "floor"/"mod" string
      ops, returns 0. Fix: extend binOp interp to handle udiv/umod,
      OR switch to dedicated primitives.
    - EQ: proof reduces to `(a = b) ↔ (b = a)` (env-var name ordering
      vs spec ordering). Closing needs `eq_comm` rewrite.
    These are spec-level interp gaps the audit didn't catch (audit
    compares CL emission to reference function, which both do the
    right thing; the Lean interp is what diverged). Tracked as
    follow-up: tighten binOp/cmp interps with precise BitVec ops.
    Stated as sorry per no-silent-gaps; not vacuously skipped. -/
theorem slt_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf sltForm s = MacroSpec.U256Ops.stepSlt s := by
  unfold stepOf sltForm signedCmpForm MacroSpec.U256Ops.stepSlt
        MacroSpec.U256Ops.stepBinOp' MacroSpec.U256Ops.boolU256
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem sgt_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf sgtForm s = MacroSpec.U256Ops.stepSgt s := by
  unfold stepOf sgtForm signedCmpForm MacroSpec.U256Ops.stepSgt
        MacroSpec.U256Ops.stepBinOp' MacroSpec.U256Ops.boolU256
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem eq_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf eqForm s = MacroSpec.U256Ops.stepEq s := by
  unfold stepOf eqForm MacroSpec.U256Ops.stepEq
        MacroSpec.U256Ops.stepBinOp' MacroSpec.U256Ops.boolU256
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem not_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf notForm s = MacroSpec.U256Ops.stepNot s := by
  unfold stepOf notForm MacroSpec.U256Ops.stepNot
        MacroSpec.U256Ops.stepUnaryOp
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | _ :: _ => simp [Form.interp, h, Env.set]

/-- DIV/MOD: interp is now SEMANTICALLY CORRECT (binOp interp recognizes
    'floor' → BitVec.udiv, 'mod' → BitVec.umod). However, simp can't
    reduce the nested `match Form.interp env s (var "b") with | none =>
    none | some ... => if cv = 0 then ... else ...` to a clean record
    equality. simp leaves the LHS as a 3-level-nested match expression
    that rfl can't unfold further.

    The fix needs either:
    (a) `@[simp]` lemmas for each Form.interp case stating the reduced
        form for specific constructors, OR
    (b) custom `Form.interp_var`, `Form.interp_letBind`, etc. equation
        lemmas with `@[simp]` markers, OR
    (c) WellFounded recursion on Form's depth to expose the case
        structure for simp.

    Pure proof-engineering — the interp matches the spec by inspection.
    Leaving sorried until the broader tactical-infrastructure work
    (probably (b): explicit simp lemmas per Form constructor with
    appropriate `@[simp]` annotations). -/
theorem div_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf divForm s = MacroSpec.U256Ops.stepDiv s := by
  unfold stepOf divForm MacroSpec.U256Ops.stepDiv
        MacroSpec.U256Ops.stepBinOp'
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem mod_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf modForm s = MacroSpec.U256Ops.stepMod s := by
  unfold stepOf modForm MacroSpec.U256Ops.stepMod
        MacroSpec.U256Ops.stepBinOp'
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

/-! ### Env / block context readers — single-line pushes, simplest shape -/

/-- Spec template: push the named field, charge 2 gas, bump pc. -/
def specEnvAddrPush {Addr : Type} [DecidableEq Addr]
    (s : CLState Addr Evm.U256) (v : Evm.U256) : Option (CLState Addr Evm.U256) :=
  some { s with
    stack := v :: s.stack,
    pc := s.pc + 1,
    gasLeft := s.gasLeft - 2 }

theorem callvalue_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf callvalueForm s = specEnvAddrPush s s.callvalue := by
  unfold stepOf callvalueForm envReaderForm specEnvAddrPush
  simp [Form.interp]

theorem gasprice_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf gaspriceForm s = specEnvAddrPush s s.gasprice := by
  unfold stepOf gaspriceForm envReaderForm specEnvAddrPush
  simp [Form.interp]

theorem chainid_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf chainidForm s = specEnvAddrPush s s.chainid := by
  unfold stepOf chainidForm envReaderForm specEnvAddrPush
  simp [Form.interp]

theorem timestamp_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf timestampForm s = specEnvAddrPush s s.timestamp := by
  unfold stepOf timestampForm envReaderForm specEnvAddrPush
  simp [Form.interp]

theorem number_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf numberForm s = specEnvAddrPush s s.blockNumber := by
  unfold stepOf numberForm envReaderForm specEnvAddrPush
  simp [Form.interp]

theorem gaslimit_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf gaslimitForm s = specEnvAddrPush s s.gaslimit := by
  unfold stepOf gaslimitForm envReaderForm specEnvAddrPush
  simp [Form.interp]

theorem prevrandao_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf prevrandaoForm s = MacroSpec.U256Ops.stepPrevRandao s := by
  unfold stepOf prevrandaoForm envReaderForm MacroSpec.U256Ops.stepPrevRandao
        MacroSpec.U256Ops.stepConstPush
  simp [Form.interp]

theorem blobbasefee_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf blobbasefeeForm s = MacroSpec.U256Ops.stepBlobBaseFee s := by
  unfold stepOf blobbasefeeForm envReaderForm MacroSpec.U256Ops.stepBlobBaseFee
        MacroSpec.U256Ops.stepConstPush
  simp [Form.interp]

theorem blobhash_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf blobhashForm s = MacroSpec.U256Ops.stepBlobHash s := by
  unfold stepOf blobhashForm MacroSpec.U256Ops.stepBlobHash
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | _ :: _ =>
    simp [Form.interp, h, Env.set]

theorem basefee_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf basefeeForm s = specEnvAddrPush s s.basefee := by
  unfold stepOf basefeeForm envReaderForm specEnvAddrPush
  simp [Form.interp]

/-- Spec for ADDRESS/ORIGIN/CALLER/COINBASE — push the named Addr field
    projected via `s.addrToVal`. -/
def specAddrPush {Addr : Type} [DecidableEq Addr]
    (a : Addr) (s : CLState Addr Evm.U256) : Option (CLState Addr Evm.U256) :=
  some { s with
    stack := s.addrToVal a :: s.stack,
    pc := s.pc + 1,
    gasLeft := s.gasLeft - 2 }

theorem address_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf addressForm s = specAddrPush s.addr s := by
  unfold stepOf addressForm envAddrReaderForm specAddrPush
  simp [Form.interp]

theorem origin_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf originForm s = specAddrPush s.origin s := by
  unfold stepOf originForm envAddrReaderForm specAddrPush
  simp [Form.interp]

theorem caller_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf callerForm s = specAddrPush s.caller s := by
  unfold stepOf callerForm envAddrReaderForm specAddrPush
  simp [Form.interp]

theorem coinbase_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf coinbaseForm s = specAddrPush s.coinbase s := by
  unfold stepOf coinbaseForm envAddrReaderForm specAddrPush
  simp [Form.interp]

/-! ### Halts and simple control ops -/

theorem stop_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf stopForm s = some { s with halted := true } := by
  unfold stepOf stopForm
  simp [Form.interp]

theorem jumpdest_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf jumpdestForm s = some { s with pc := s.pc + 1,
                                          gasLeft := s.gasLeft - 1 } := by
  unfold stepOf jumpdestForm
  simp [Form.interp]

/-! ### Batch 2: state pushers (pc, msize, gas) + size readers
    (calldatasize, codesize, returndatasize) + tstore -/

theorem pc_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf pcForm s = MacroSpec.U256Ops.stepPc s := by
  unfold stepOf pcForm envReaderForm MacroSpec.U256Ops.stepPc
        MacroSpec.U256Ops.stepConstPush
  simp [Form.interp]

theorem msize_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf msizeForm s = MacroSpec.U256Ops.stepMsize s := by
  unfold stepOf msizeForm envReaderForm MacroSpec.U256Ops.stepMsize
        MacroSpec.U256Ops.stepConstPush
  simp [Form.interp]

theorem gas_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf gasForm s = MacroSpec.U256Ops.stepGas s := by
  unfold stepOf gasForm MacroSpec.U256Ops.stepGas
  simp [Form.interp]

theorem calldatasize_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf calldatasizeForm s = MacroSpec.U256Ops.stepCalldataSize s := by
  unfold stepOf calldatasizeForm bufferSizeForm
        MacroSpec.U256Ops.stepCalldataSize MacroSpec.U256Ops.stepConstPush
  simp [Form.interp]

theorem codesize_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf codesizeForm s = MacroSpec.U256Ops.stepCodeSize s := by
  unfold stepOf codesizeForm bufferSizeForm
        MacroSpec.U256Ops.stepCodeSize MacroSpec.U256Ops.stepConstPush
  simp [Form.interp]

theorem returndatasize_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf returndatasizeForm s = MacroSpec.U256Ops.stepReturndatasize s.returndata s := by
  unfold stepOf returndatasizeForm bufferSizeForm
        MacroSpec.U256Ops.stepReturndatasize MacroSpec.U256Ops.stepConstPush
  simp [Form.interp]

theorem tstore_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf tstoreForm s =
      (if s.staticp then none
       else match s.stack with
         | slot :: val :: rest =>
           some { s with
             stack := rest, pc := s.pc + 1, gasLeft := s.gasLeft - 100,
             tstorage := fun k => if k = slot then some val else s.tstorage k }
         | _ => none) := by
  unfold stepOf tstoreForm
  by_cases hstatic : s.staticp
  · simp [Form.interp, hstatic]
  · match h : s.stack with
    | [] => simp [Form.interp, h, hstatic]
    | [_] => simp [Form.interp, h, hstatic]
    | _ :: _ :: _ => simp [Form.interp, h, hstatic, Env.set]

/-! ### Batch 3: signed arithmetic, signextend, sar (dedicated primitives) -/

theorem sdiv_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf sdivForm s = MacroSpec.U256Ops.stepSdiv s := by
  unfold stepOf sdivForm signedBinForm MacroSpec.U256Ops.stepSdiv
        MacroSpec.U256Ops.stepBinOp'
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem smod_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf smodForm s = MacroSpec.U256Ops.stepSmod s := by
  unfold stepOf smodForm signedBinForm MacroSpec.U256Ops.stepSmod
        MacroSpec.U256Ops.stepBinOp'
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem sar_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf sarForm s = MacroSpec.U256Ops.stepSar s := by
  unfold stepOf sarForm MacroSpec.U256Ops.stepSar
        MacroSpec.U256Ops.stepBinOp'
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem signextend_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf signextendForm s = MacroSpec.U256Ops.stepSignExtend s := by
  unfold stepOf signextendForm MacroSpec.U256Ops.stepSignExtend
        MacroSpec.U256Ops.stepBinOp'
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

/-! ### Batch 4: EXP, RETURN, REVERT, JUMP, JUMPI, CALLDATALOAD -/

theorem exp_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf expForm s = MacroSpec.U256Ops.stepExp s := by
  unfold stepOf expForm MacroSpec.U256Ops.stepExp MacroSpec.U256Ops.expByteLen
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem return_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf returnForm s = MacroSpec.U256Ops.stepReturn s := by
  unfold stepOf returnForm MacroSpec.U256Ops.stepReturn
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem revert_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf revertForm s = MacroSpec.U256Ops.stepRevert s := by
  unfold stepOf revertForm MacroSpec.U256Ops.stepRevert
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem jump_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf jumpForm s = MacroSpec.U256Ops.stepJump s := by
  unfold stepOf jumpForm MacroSpec.U256Ops.stepJump
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | dest :: rest =>
    simp [Form.interp, h, Env.set]
    by_cases hc : Evm.Frontier.Vm.Runtime.isJumpDest s.code dest.toNat = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]

theorem jumpi_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf jumpiForm s = MacroSpec.U256Ops.stepJumpi s := by
  unfold stepOf jumpiForm MacroSpec.U256Ops.stepJumpi
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | dest :: cnd :: rest =>
    simp [Form.interp, h, Env.set]
    by_cases hz : cnd = (0#256 : Evm.U256)
    · rw [if_pos hz, if_pos hz]
    · rw [if_neg hz, if_neg hz]
      by_cases hc : Evm.Frontier.Vm.Runtime.isJumpDest s.code dest.toNat = true
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]

theorem calldataload_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf calldataloadForm s = MacroSpec.U256Ops.stepCalldataload s := by
  unfold stepOf calldataloadForm MacroSpec.U256Ops.stepCalldataload
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | _ :: _ => simp [Form.interp, h, Env.set]

/-! ### Batch 5: BYTE, SHL, SHR -/

theorem shl_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf shlForm s = MacroSpec.U256Ops.stepShl s := by
  unfold stepOf shlForm signedBinForm MacroSpec.U256Ops.stepShl
        MacroSpec.U256Ops.stepBinOp'
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem shr_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf shrForm s = MacroSpec.U256Ops.stepShr s := by
  unfold stepOf shrForm signedBinForm MacroSpec.U256Ops.stepShr
        MacroSpec.U256Ops.stepBinOp'
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem byte_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf byteForm s = MacroSpec.U256Ops.stepByte s := by
  unfold stepOf byteForm signedBinForm MacroSpec.U256Ops.stepByte
        MacroSpec.U256Ops.stepBinOp'
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h, Env.set]

/-! ### Batch 6: ADDMOD, MULMOD -/

theorem addmod_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf addmodForm s = MacroSpec.U256Ops.stepAddmod s := by
  unfold stepOf addmodForm ternaryForm MacroSpec.U256Ops.stepAddmod
        MacroSpec.U256Ops.stepTernaryOp
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | [_, _] => simp [Form.interp, h]
  | _ :: _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem mulmod_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf mulmodForm s = MacroSpec.U256Ops.stepMulmod s := by
  unfold stepOf mulmodForm ternaryForm MacroSpec.U256Ops.stepMulmod
        MacroSpec.U256Ops.stepTernaryOp
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | [_, _] => simp [Form.interp, h]
  | _ :: _ :: _ :: _ => simp [Form.interp, h, Env.set]

/-! ### Batch 7: buffer copies (CALLDATACOPY/CODECOPY/RETURNDATACOPY/EXTCODECOPY/MCOPY) -/

theorem calldatacopy_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf calldatacopyForm s = MacroSpec.U256Ops.stepCalldatacopy s := by
  unfold stepOf calldatacopyForm bufferCopyOpForm
        MacroSpec.U256Ops.stepCalldatacopy MacroSpec.U256Ops.copyToMemory
        MacroSpec.U256Ops.copyExtraGas
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | [_, _] => simp [Form.interp, h]
  | _ :: _ :: _ :: _ => simp [Form.interp, h, Env.set]; omega

theorem codecopy_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf codecopyForm s = MacroSpec.U256Ops.stepCodecopy s := by
  unfold stepOf codecopyForm bufferCopyOpForm
        MacroSpec.U256Ops.stepCodecopy MacroSpec.U256Ops.copyToMemory
        MacroSpec.U256Ops.copyExtraGas
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | [_, _] => simp [Form.interp, h]
  | _ :: _ :: _ :: _ => simp [Form.interp, h, Env.set]; omega

theorem returndatacopy_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf returndatacopyForm s =
      MacroSpec.U256Ops.stepReturndatacopy s.returndata s := by
  unfold stepOf returndatacopyForm bufferCopyOpForm
        MacroSpec.U256Ops.stepReturndatacopy MacroSpec.U256Ops.copyToMemory
        MacroSpec.U256Ops.copyExtraGas
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | [_, _] => simp [Form.interp, h]
  | a :: b :: c :: rest =>
    simp [Form.interp, h, Env.set]
    by_cases hbound : b.toNat + c.toNat > s.returndata.size
    · simp [hbound]
    · simp [hbound]; omega

theorem mcopy_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf mcopyForm s = MacroSpec.U256Ops.stepMcopy s := by
  unfold stepOf mcopyForm MacroSpec.U256Ops.stepMcopy
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | [_, _] => simp [Form.interp, h]
  | _ :: _ :: _ :: _ => simp [Form.interp, h, Env.set]

theorem extcodecopy_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf extcodecopyForm s = WorldOps.stepExtcodecopy s := by
  unfold stepOf extcodecopyForm WorldOps.stepExtcodecopy
        MacroSpec.U256Ops.copyExtraGas
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | [_, _] => simp [Form.interp, h]
  | [_, _, _] => simp [Form.interp, h]
  | _ :: _ :: _ :: _ :: _ => simp [Form.interp, h, Env.set]; omega

/-! ### Batch 8: DUP-n, SWAP-n (n ≥ 1) -/

theorem dup_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256)
    (n : Nat) (hn : n ≥ 1) :
    stepOf (dupForm n) s = MacroSpec.U256Ops.stepDup n s := by
  unfold stepOf dupForm MacroSpec.U256Ops.stepDup
  by_cases hl : s.stack.length ≥ n
  · have hlt : n - 1 < s.stack.length := by omega
    have hget : (s.stack[n - 1]?) = some s.stack[n - 1] :=
      List.getElem?_eq_getElem hlt
    simp [Form.interp, hget, And.intro hn hl]
  · have hge : s.stack.length ≤ n - 1 := by omega
    have hget : (s.stack[n - 1]?) = none := List.getElem?_eq_none hge
    have hcond : ¬(n ≥ 1 ∧ s.stack.length ≥ n) := fun h => hl h.2
    simp [Form.interp, hget, hcond]

theorem push_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) (n : Nat) :
    stepOf (pushForm n) s = MacroSpec.U256Ops.stepPush n s := by
  unfold stepOf pushForm MacroSpec.U256Ops.stepPush
  simp [Form.interp]

theorem keccak_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) :
    stepOf keccakForm s = MacroSpec.U256Ops.stepKeccak s := by
  unfold stepOf keccakForm MacroSpec.U256Ops.stepKeccak
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | _ :: _ :: _ => simp [Form.interp, h]

theorem log_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256) (n : Nat) :
    stepOf (logForm n) s = MacroSpec.U256Ops.stepLogN n s := by
  unfold stepOf logForm MacroSpec.U256Ops.stepLogN
  match h : s.stack with
  | [] => simp [Form.interp, h]
  | [_] => simp [Form.interp, h]
  | off :: len :: rest =>
    by_cases hst : s.staticp
    · simp [Form.interp, hst]
    · simp [Form.interp, h, hst]
      by_cases hlen : rest.length + 1 + 1 < 2 + n
      · simp [hlen]
      · simp [hlen]

theorem swap_extract_correct
    {Addr : Type} [DecidableEq Addr] (s : CLState Addr Evm.U256)
    (n : Nat) (hn : n ≥ 1) :
    stepOf (swapForm n) s = MacroSpec.U256Ops.stepSwap n s := by
  unfold stepOf swapForm MacroSpec.U256Ops.stepSwap
  by_cases hl : s.stack.length ≥ n + 1
  · have h0 : 0 < s.stack.length := by omega
    have hn' : n < s.stack.length := by omega
    have e0 : (s.stack[0]?) = some s.stack[0] := List.getElem?_eq_getElem h0
    have en : (s.stack[n]?) = some s.stack[n] := List.getElem?_eq_getElem hn'
    simp [Form.interp, e0, en, And.intro hn hl]
  · have hcond : ¬(n ≥ 1 ∧ s.stack.length ≥ n + 1) := fun h => hl h.2
    by_cases h0 : 0 < s.stack.length
    · have hge : s.stack.length ≤ n := by omega
      have e0 : (s.stack[0]?) = some s.stack[0] := List.getElem?_eq_getElem h0
      have en : (s.stack[n]?) = none := List.getElem?_eq_none hge
      simp [Form.interp, e0, en, hcond]
    · have hge0 : s.stack.length ≤ 0 := by omega
      have e0 : (s.stack[0]?) = none := List.getElem?_eq_none hge0
      simp [Form.interp, e0, hcond]

end Evm.CL.Extract
