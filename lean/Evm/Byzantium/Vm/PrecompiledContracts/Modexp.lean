/-
  Evm.Byzantium.Vm.PrecompiledContracts.Modexp — EIP-198 modular
  exponentiation precompile at address 0x05.

  EELS reference: `forks/byzantium/vm/precompiled_contracts/modexp.py`.

  Input layout (all big-endian, lengths in bytes):
    bytes 0..31      Blen = length of B (base)        [U256]
    bytes 32..63     Elen = length of E (exponent)    [U256]
    bytes 64..95     Mlen = length of M (modulus)     [U256]
    bytes 96..96+Blen           B
    bytes 96+Blen..96+Blen+Elen E
    bytes 96+Blen+Elen..        M

  Output: `B**E mod M`, big-endian, exactly Mlen bytes.

  Gas formula (EIP-198 Byzantium-era; Berlin re-prices via EIP-2565):

    floor(mult_complexity(max(Blen, Mlen)) * max(adjusted_exp_length, 1) / GQUADDIVISOR)

  where GQUADDIVISOR = 20 and:

    mult_complexity(x) = x^2                        if x ≤ 64
                       = x^2 / 4 + 96 x - 3072      if 64 < x ≤ 1024
                       = x^2 / 16 + 480 x - 199680  otherwise

    adjusted_exp_length =
        if Elen ≤ 32 and E == 0:        0
        if Elen ≤ 32 and E > 0:         bit_length(E) - 1
        if Elen > 32:                   8 * (Elen - 32) +
                                          (bit_length of leading 32 bytes - 1, or 0)
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Frontier.Vm.PrecompiledContracts

namespace Evm.Byzantium.Vm.PrecompiledContracts

open Evm.Frontier.Vm.PrecompiledContracts (Precompile)

/-! ## Helpers -/

/-- Read up to `n` BE bytes starting at `off`, zero-padded on the right
    if `off + n` exceeds the input. Returns a Nat. -/
def readBytesAsNat (input : Evm.Bytes) (off n : Nat) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [0:n] do
    let b := if off + i < input.size then input.get! (off + i) else (0 : UInt8)
    acc := acc * 256 + b.toNat
  pure acc

/-- BE-encode `n` as exactly `len` bytes (truncating high bits if too
    large; left-padding with zeros if too small). -/
def natToBytesBE (n : Nat) (len : Nat) : Evm.Bytes := Id.run do
  let mut out : Evm.Bytes := ByteArray.empty
  let mut k := n
  let mut acc : List UInt8 := []
  for _ in [0:len] do
    acc := UInt8.ofNat (k % 256) :: acc
    k := k / 256
  for b in acc do out := out.push b
  pure out

/-- `bit_length(n)` = the number of bits needed to represent n,
    i.e. `0` for `n = 0`, else `Nat.log2 n + 1`. -/
private def bitLength : Nat → Nat
  | 0     => 0
  | n+1   => Nat.log2 (n+1) + 1

/-- EIP-198 Byzantium-era complexity function. -/
def multComplexity (x : Nat) : Nat :=
  if x ≤ 64 then x * x
  else if x ≤ 1024 then x * x / 4 + 96 * x - 3072
  else x * x / 16 + 480 * x - 199680

/-- EIP-198 `adjusted_exponent_length`. -/
def adjustedExpLength (input : Evm.Bytes) (eOff eLen : Nat) : Nat :=
  if eLen ≤ 32 then
    let e := readBytesAsNat input eOff eLen
    if e = 0 then 0 else bitLength e - 1
  else
    let head := readBytesAsNat input eOff 32
    let bl := if head = 0 then 0 else bitLength head - 1
    8 * (eLen - 32) + bl

/-- Modular exponentiation via square-and-multiply, with reduction at
    every step. Lean's `Nat.pow b e` builds the full bignum and panics
    on multi-thousand-bit exponents — modexp's exponents can be up to
    `eLen * 8` bits, which for the `modexp_3_09984_39936_*` corpus is
    over 300 K bits. This stays in O(log e · M(m)) instead. -/
partial def powMod (b e m : Nat) : Nat :=
  if m = 0 then 0
  else if m = 1 then 0
  else
    let rec go (b e acc : Nat) : Nat :=
      if e = 0 then acc
      else
        let acc' := if e % 2 = 1 then acc * b % m else acc
        go (b * b % m) (e / 2) acc'
    go (b % m) e 1

/-! ## The precompile -/

/-- 0x05 MODEXP. Returns `(out, gasLeft)`; raises `outOfGas` if the
    caller didn't supply enough. -/
def modexp : Precompile := fun input gasLeft => do
  let bLen := readBytesAsNat input 0 32
  let eLen := readBytesAsNat input 32 32
  let mLen := readBytesAsNat input 64 32
  let bOff := 96
  let eOff := bOff + bLen
  let mOff := eOff + eLen
  let cost :=
    let mc := multComplexity (Nat.max bLen mLen)
    let ael := Nat.max (adjustedExpLength input eOff eLen) 1
    mc * ael / 20
  if gasLeft < cost then
    .error .outOfGas
  let gasLeft' := gasLeft - cost
  if mLen = 0 then
    return (ByteArray.empty, gasLeft')
  let b := readBytesAsNat input bOff bLen
  let e := readBytesAsNat input eOff eLen
  let m := readBytesAsNat input mOff mLen
  let result := powMod b e m
  return (natToBytesBE result mLen, gasLeft')

end Evm.Byzantium.Vm.PrecompiledContracts
