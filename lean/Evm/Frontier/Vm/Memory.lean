/-
  Evm.Frontier.Vm.Memory — byte-addressable execution memory.

  EELS reference: ethereum/frontier/vm/memory.py. Memory is conceptually
  a byte array that grows in 32-byte words; reads past the end are
  zero-padded, writes expand it. Gas accounting for expansion lives in
  `Frontier.Vm.Gas`.
-/

import Evm.BaseTypes

namespace Evm.Frontier.Vm

abbrev Memory : Type := Evm.Bytes

namespace Memory

def empty : Memory := Evm.Bytes.empty

def size (m : Memory) : Nat := ByteArray.size m

/-- Active 32-byte words: `⌈size / 32⌉`. -/
def words (m : Memory) : Nat := (ByteArray.size m + 31) / 32

/-- Read `len` bytes starting at `offset`, zero-padding past the end. -/
def read (m : Memory) (offset len : Nat) : Evm.Bytes :=
  Evm.Bytes.sliceZeroPad m offset len

/-- Ensure memory is at least `n` bytes, rounded up to a 32-byte boundary.
    Returns the (possibly grown) memory. -/
def extend (m : Memory) (n : Nat) : Memory :=
  let target := ((n + 31) / 32) * 32
  if target ≤ ByteArray.size m then m
  else m ++ ByteArray.mk (Array.replicate (target - ByteArray.size m) (0 : UInt8))

/-- Write `value` starting at `offset`, extending memory as needed.
    No-op (no extension) when `value.size = 0` — important for
    CALL-family return-data merging when retLen = 0, where an
    `extend m offset` would wrongly grow the parent's buffer past
    its EELS-spec'd msize. (Caught by block 0x800000 tx 7: a CALL
    with retOff=128 retLen=0 wrongly extended the parent to 128
    bytes, which then made a later MSTORE charge 3 less gas than
    op-geth because its msize was 4 words instead of 3.) -/
def write (m : Memory) (offset : Nat) (value : Evm.Bytes) : Memory :=
  if value.size = 0 then m
  else Id.run do
    let mut mem := extend m (offset + value.size)
    for i in [0:value.size] do
      mem := mem.set! (offset + i) (value.get! i)
    pure mem

/-- Write a single byte. -/
def writeByte (m : Memory) (offset : Nat) (b : UInt8) : Memory :=
  (extend m (offset + 1)).set! offset b

end Memory

end Evm.Frontier.Vm
