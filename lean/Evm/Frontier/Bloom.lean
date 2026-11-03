/-
  Evm.Frontier.Bloom — log bloom filter (256 bytes / 2048 bits).

  EELS reference: ethereum/frontier/bloom.py. A 2048-bit Bloom filter
  populated from the logs of every transaction in a block; entries are
  derived from `keccak256(topic-or-address)`.
-/

import Evm.BaseTypes

namespace Evm.Frontier

/-- A 256-byte (2048-bit) Bloom filter. -/
abbrev Bloom := Evm.Bytes

namespace Bloom

/-- The all-zero Bloom filter (no log entries). -/
def empty : Bloom :=
  ByteArray.mk (Array.replicate 256 (0 : UInt8))

end Bloom

end Evm.Frontier
