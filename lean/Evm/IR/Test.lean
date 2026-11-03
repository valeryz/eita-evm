/-
  Evm.IR.Test — compile-the-canonical-bytecode smoke test.

  Compile `PUSH1 10; PUSH1 20; ADD; PUSH1 0; MSTORE; PUSH1 32;
  PUSH1 0; RETURN` and dump the resulting Chunk. Run via:

      lake env lean Evm/IR/Test.lean
-/

import Evm.IR.Compile
import Evm.BaseTypes

namespace Evm.IR.Test

open Evm.IR

def canonicalBytes : Evm.Bytes :=
  ByteArray.mk #[0x60, 0x0a, 0x60, 0x14, 0x01, 0x60, 0x00, 0x52,
                 0x60, 0x20, 0x60, 0x00, 0xf3]

#eval do
  match compile .frontier canonicalBytes with
  | .ok chunk =>
    IO.println s!"OK: startPc={chunk.startPc}, staticGas={chunk.staticGas}"
    IO.println s!"  ops ({chunk.ops.length}): {repr chunk.ops}"
    IO.println s!"  term: {repr chunk.term}"
  | .error e =>
    IO.println s!"FAIL: {repr e}"

end Evm.IR.Test
