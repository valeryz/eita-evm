/-
  Evm.Crypto.Blake2f — the BLAKE2b compression function F with a rounds parameter
  (EIP-152), in pure Lean.

  Source: RFC 7693 (BLAKE2), §2.1 (BLAKE2b parameters: w = 64, R1..R4 = 32, 24, 16, 63),
  §2.6 (IV), §2.7 (SIGMA), §3.1 (the mixing function G) and §3.2 (the compression
  function F). EIP-152 makes the round count (12 in RFC 7693) an input; SIGMA is indexed
  `i mod 10`, as §3.2 already does for rounds 10 and 11. The same algorithm is EELS
  `ethereum/crypto/blake2.py::Blake2.compress` 194-247 (its `G` 152-192).

  This is the spec AND the executable: the Lean replay's 0x09 runs `compress`
  (`Evm.Istanbul.Vm.PrecompiledContracts.blake2f`). The production C (`lean/c/blake2f.c`)
  is checked against it by the `cryptoTests` differential test (EIP-152 vectors and
  random inputs).
-/

import Evm.BaseTypes

namespace Evm.Crypto.Blake2f

/-- RFC 7693 §2.6: the BLAKE2b IV (= SHA-512's). -/
def iv : Array UInt64 :=
  #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- RFC 7693 §2.7: the message schedule SIGMA (ten permutations). -/
def sigma : Array (Array Nat) :=
  #[#[ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,10,11,12,13,14,15],
    #[14,10, 4, 8, 9,15,13, 6, 1,12, 0, 2,11, 7, 5, 3],
    #[11, 8,12, 0, 5, 2,15,13,10,14, 3, 6, 7, 1, 9, 4],
    #[ 7, 9, 3, 1,13,12,11,14, 2, 6, 5,10, 4, 0,15, 8],
    #[ 9, 0, 5, 7, 2, 4,10,15,14, 1,11,12, 6, 8, 3,13],
    #[ 2,12, 6,10, 0,11, 8, 3, 4,13, 7, 5,15,14, 1, 9],
    #[12, 5, 1,15,14,13, 4,10, 0, 7, 6, 3, 9, 2, 8,11],
    #[13,11, 7,14,12, 1, 3, 9, 5, 0,15, 4, 8, 6, 2,10],
    #[ 6,15,14, 9,11, 3, 0, 8,12, 2,13, 7, 1, 4,10, 5],
    #[10, 2, 8, 4, 7, 6, 1, 5,15,11, 9,14, 3,12,13, 0]]

/-- RFC 7693 §2.3: right rotation of a 64-bit word (`x >>> n`, 0 < n < 64). -/
@[inline] def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- RFC 7693 §3.1, the mixing function G with BLAKE2b's rotation constants
    (R1, R2, R3, R4) = (32, 24, 16, 63) (§2.1). Additions are mod 2^64 (UInt64). -/
@[inline] def mix (v : Array UInt64) (a b c d : Nat) (x y : UInt64) : Array UInt64 :=
  let v := v.set! a (v[a]! + v[b]! + x)
  let v := v.set! d (rotr (v[d]! ^^^ v[a]!) 32)
  let v := v.set! c (v[c]! + v[d]!)
  let v := v.set! b (rotr (v[b]! ^^^ v[c]!) 24)
  let v := v.set! a (v[a]! + v[b]! + y)
  let v := v.set! d (rotr (v[d]! ^^^ v[a]!) 16)
  let v := v.set! c (v[c]! + v[d]!)
  v.set! b (rotr (v[b]! ^^^ v[c]!) 63)

/-- One round of RFC 7693 §3.2's loop: the eight G applications, columns then
    diagonals, with the message words permuted by `SIGMA[i mod 10]`. -/
def round (m : Array UInt64) (v : Array UInt64) (i : Nat) : Array UInt64 :=
  let s := sigma[i % 10]!
  let v := mix v 0 4  8 12 m[s[0]!]!  m[s[1]!]!
  let v := mix v 1 5  9 13 m[s[2]!]!  m[s[3]!]!
  let v := mix v 2 6 10 14 m[s[4]!]!  m[s[5]!]!
  let v := mix v 3 7 11 15 m[s[6]!]!  m[s[7]!]!
  let v := mix v 0 5 10 15 m[s[8]!]!  m[s[9]!]!
  let v := mix v 1 6 11 12 m[s[10]!]! m[s[11]!]!
  let v := mix v 2 7  8 13 m[s[12]!]! m[s[13]!]!
  mix v 3 4  9 14 m[s[14]!]! m[s[15]!]!

/-- RFC 7693 §3.2, the compression function F, with the round count a parameter
    (EIP-152): `h` the 8-word state, `m` the 16-word block, `t0`/`t1` the low/high
    words of the offset counter, `f` the final-block flag. Returns the new state. -/
def compress (rounds : Nat) (h m : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    Array UInt64 := Id.run do
  -- v[0..7] := h[0..7]; v[8..15] := IV[0..7]
  let mut v := h ++ iv
  -- v[12] := v[12] ^ (t mod 2**w); v[13] := v[13] ^ (t >> w)
  v := v.set! 12 (v[12]! ^^^ t0)
  v := v.set! 13 (v[13]! ^^^ t1)
  -- IF f = TRUE THEN v[14] := v[14] ^ 0xFF..FF
  if f then v := v.set! 14 (v[14]! ^^^ 0xFFFFFFFFFFFFFFFF)
  for i in [0:rounds] do
    v := round m v i
  -- h[i] := h[i] ^ v[i] ^ v[i + 8]
  return (List.range 8).toArray.map fun i => h[i]! ^^^ v[i]! ^^^ v[i + 8]!

/-! ## EIP-152 encoding (EELS `Blake2.get_blake2_parameters` 133-150) -/

/-- A little-endian 64-bit word at `off` (EELS `spit_le_to_uint` 10-31). -/
def leWord (b : Evm.Bytes) (off : Nat) : UInt64 :=
  (List.range 8).foldr (fun k acc => (acc <<< 8) ||| (b.get! (off + k)).toUInt64) 0

/-- `n` consecutive little-endian words from `off`. -/
def leWords (b : Evm.Bytes) (off n : Nat) : Array UInt64 :=
  (List.range n).toArray.map fun i => leWord b (off + 8 * i)

/-- The round count: bytes 0..4, big-endian (`Uint.from_be_bytes(data[:4])`). -/
def rounds (b : Evm.Bytes) : Nat :=
  (b.get! 0).toNat * 2 ^ 24 + (b.get! 1).toNat * 2 ^ 16 + (b.get! 2).toNat * 2 ^ 8 +
    (b.get! 3).toNat

/-- The final-block flag byte (`Uint.from_be_bytes(data[212:])`). -/
def flag (b : Evm.Bytes) : Nat := (b.get! 212).toNat

/-- The 64-byte output: the new state as 8 little-endian words (EELS `struct.pack("<8Q")`,
    blake2.py 247). -/
def encode (h : Array UInt64) : Evm.Bytes := Id.run do
  let mut out := ByteArray.empty
  for w in h do
    for k in [0:8] do
      out := out.push (w >>> (8 * k).toUInt64).toUInt8
  return out

/-- EIP-152's F over a 213-byte input: `blake2b.compress(rounds, h, m, t_0, t_1, f)`
    after `get_blake2_parameters` (EELS istanbul `blake2f.py` 35-42). -/
def ofInput (b : Evm.Bytes) : Evm.Bytes :=
  encode (compress (rounds b) (leWords b 4 8) (leWords b 68 16) (leWord b 196) (leWord b 204)
    (flag b ≠ 0))

end Evm.Crypto.Blake2f
