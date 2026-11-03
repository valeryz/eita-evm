/-
  Evm.Crypto.EcRecover — secp256k1 public-key recovery, EVM-style.

  Bound via `@[extern]` to `c/ecrecover.c`, which links against Bitcoin
  Core's libsecp256k1.

  Input layout (the EVM ABI for the 0x01 precompile):
    `hash (32 bytes) ‖ v (32 bytes) ‖ r (32 bytes) ‖ s (32 bytes)` = 128 bytes.

  Output: a 32-byte big-endian word holding the recovered Ethereum
  address in its low 20 bytes (high 12 bytes zero), OR the empty
  `ByteArray` if the signature was malformed / failed recovery — the
  caller treats that as "invalid signature".
-/

import Evm.BaseTypes

namespace Evm.Crypto

/-- Raw FFI entry: takes the 128-byte EVM-formatted input, returns the
    32-byte padded address or empty bytes on failure. -/
@[extern "lean_ecrecover"]
opaque ecrecoverRaw (input : @& ByteArray) : ByteArray

/-- Recover the signer of `messageHash` from `(v, r, s)`. `v` must be
    27 or 28 (the pre-EIP-155 convention used by Frontier / Homestead);
    EIP-155 adjustment is the caller's responsibility. Returns `none`
    on any failure. -/
def recover
    (messageHash : Hash32) (v r s : U256) : Option Address := Id.run do
  -- Pack 128-byte EVM-ABI input.
  let mut buf : ByteArray := ByteArray.empty
  buf := buf ++ U256.toBytesBE messageHash
  buf := buf ++ U256.toBytesBE v
  buf := buf ++ U256.toBytesBE r
  buf := buf ++ U256.toBytesBE s
  let result := ecrecoverRaw buf
  if result.size = 32 then
    pure (some (Address.ofBytesBE (Bytes.sliceZeroPad result 12 20)))
  else
    pure none

end Evm.Crypto
