/-
  Evm.IR.Emit — render compiled IR as s-expressions for the CL side.

  Bridge between the Lean compiler and the Lisp interpreter. The
  output is a string that, when `READ` from Lisp, produces a list
  matching the `ir-chunk` shape expected by `eita-ir.lisp`.

  Format:
    (:start-pc N :static-gas N :ops ((:OP ...) ...) :term :TAG)

  Once the Lisp side has a verified reader, this is the entire
  bytecode → executable pipeline:

    bytecode (hex string)
      ↓ Lean IR.compile
    Chunk : Lean record
      ↓ Lean IR.emit
    String of s-expressions
      ↓ Lisp READ
    ir-chunk struct
      ↓ Lisp eita-ir interpreter, OR
      ↓ Lisp SBCL compiler-backend (future)
    halted frame with output
-/

import Evm.IR.Compile

namespace Evm.IR

def renderOp : Op → String
  | .push n v => s!"(:push {n} {v.toNat})"
  | .add      => "(:add)"
  | .mul      => "(:mul)"
  | .sub      => "(:sub)"
  | .div      => "(:div)"
  | .and_     => "(:and)"
  | .or_      => "(:or)"
  | .xor_     => "(:xor)"
  | .lt       => "(:lt)"
  | .gt       => "(:gt)"
  | .pop      => "(:pop)"
  | .mload    => "(:mload)"
  | .mstore   => "(:mstore)"
  -- Opcodes outside the no-jump slice render with their tag; the
  -- Lisp side dispatches further. Phase 2 wires the full set.
  | other     => s!"(:op {repr other})"

def renderTerm : Terminator → String
  | .stop      => ":stop"
  | .ret       => ":ret"
  | .endOfCode => ":end-of-code"
  -- New terminators get rendered with a tag; full s-expr shape
  -- (e.g. call kind, jump target) lands in Phase 4.
  | other      => s!"(:term {repr other})"

def renderChunk (c : Chunk) : String :=
  let opsStr := String.intercalate " " (c.ops.map renderOp)
  s!"(:start-pc {c.startPc} :static-gas {c.staticGas} :ops ({opsStr}) :term {renderTerm c.term})"

end Evm.IR
