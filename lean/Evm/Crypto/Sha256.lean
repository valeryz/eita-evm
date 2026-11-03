/-
  Evm.Crypto.Sha256 — FIPS 180-4 SHA-256.

  Bound via `@[extern]` to the C implementation in `c/sha256.c`. Output
  is 32 bytes, big-endian by SHA-256 convention.
-/

import Evm.BaseTypes

namespace Evm.Crypto

@[extern "lean_sha256"]
opaque sha256 (input : @& ByteArray) : ByteArray

end Evm.Crypto
