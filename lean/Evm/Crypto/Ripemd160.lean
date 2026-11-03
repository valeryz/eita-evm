/-
  Evm.Crypto.Ripemd160 — RIPEMD-160.

  Bound via `@[extern]` to the C implementation in `c/ripemd160.c`.
  Output is 20 bytes. EVM's precompile at 0x03 left-zero-pads to 32.
-/

import Evm.BaseTypes

namespace Evm.Crypto

@[extern "lean_ripemd160"]
opaque ripemd160 (input : @& ByteArray) : ByteArray

end Evm.Crypto
