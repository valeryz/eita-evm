/-
  cryptoTests — the crypto oracles against the native libraries, bounded (< 1 min).

  1. BLAKE2F: the pure-Lean RFC 7693 F (`Evm.Crypto.Blake2f`) against the EIP-152 vectors
     (EELS tests/istanbul/eip152_blake2) and against lean/c/blake2f.c on random inputs; the
     precompile wrapper's failures (length, flag) against the C.
  2. BLS12-381: the contracts of `Evm.Crypto.Contracts.Bls12381` as property tests of
     `Evm.Crypto.Bls12381.native` (blst) — the group law against a pure-Lean affine
     reference over Fp / Fp2, associativity / identity / inverse / commutativity, scalar
     multiplication against repeated addition and double-and-add, the subgroup test against
     [r]P = O, map-to-curve on the curve and in the subgroup, MSM against Σ mᵢ·Pᵢ, pairing
     bilinearity e(aP, bQ) = e(P, Q)^(ab) and e(P, Q)·e(−P, Q) = 1 and non-degeneracy;
     then the EIP-2537 precompiles (the proved Lean wrapper over `native`) against the
     production C entries (lean/c/bls12381.cpp) and the chain's vectors
     (lean/c/testdata/bls12381-vectors.json), on valid and mutated inputs.
  3. P-256: `Evm.Crypto.Contracts.P256.EcdsaAccepts` made executable (affine arithmetic
     over Fp, FIPS 186-5 §6.4.2), sign / verify round trips (signatures made in Lean,
     verified by OpenSSL), tampered signatures, the two Base chain inputs of
     tests/p256verify.lisp, and edge inputs: the EELS wrapper over OpenSSL against
     OpenSSL alone (the production entry).

  Exit status 1 on any failure; every failure is printed.
-/

import Lean.Data.Json
import Evm.Crypto.Blake2f
import Evm.Crypto.Bls12381
import Evm.Crypto.P256Verify
import Evm.Istanbul.Vm.PrecompiledContracts.Blake2f
import Evm.Prague.Vm.PrecompiledContracts
import Evm.Osaka.Vm.PrecompiledContracts

open Evm.Crypto.Bls12381 (G1 G2 Fp2 p r native g1Encode g2Encode g1Zero g2Zero)

/-! ## Production C entries (bound here only) -/

@[extern "lean_blake2f"] opaque blake2fC (input : @& ByteArray) : ByteArray
@[extern "lean_bls_g1add"] opaque prodG1Add (input : @& ByteArray) : ByteArray
@[extern "lean_bls_g1msm"] opaque prodG1Msm (input : @& ByteArray) : ByteArray
@[extern "lean_bls_g2add"] opaque prodG2Add (input : @& ByteArray) : ByteArray
@[extern "lean_bls_g2msm"] opaque prodG2Msm (input : @& ByteArray) : ByteArray
@[extern "lean_bls_pairing"] opaque prodPairing (input : @& ByteArray) : ByteArray
@[extern "lean_bls_map_fp_to_g1"] opaque prodMapFpToG1 (input : @& ByteArray) : ByteArray
@[extern "lean_bls_map_fp2_to_g2"] opaque prodMapFp2ToG2 (input : @& ByteArray) : ByteArray

/-! ## Utilities -/

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0

def ofHex (s : String) : ByteArray := Id.run do
  let l := s.toList
  let cs := (if l.take 2 == ['0', 'x'] then l.drop 2 else l).toArray
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    out := out.push (UInt8.ofNat (hexVal cs[2*i]! * 16 + hexVal cs[2*i+1]!))
  return out

def toHex (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ (if x < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 x.toNat)) ""

def be (n len : Nat) : ByteArray := Evm.Byzantium.Vm.PrecompiledContracts.natToBytesBE n len
def powMod := Evm.Byzantium.Vm.PrecompiledContracts.powMod

/-- splitmix64. -/
structure Rng where s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- A uniform-ish natural below 2^(64·words). -/
def rNat (rng : IO.Ref Rng) (words : Nat) : IO Nat := do
  let mut acc := 0
  for _ in [0:words] do
    let (x, g) := (← rng.get).next
    rng.set g
    acc := acc * 2 ^ 64 + x.toNat
  return acc

def rBelow (rng : IO.Ref Rng) (m : Nat) : IO Nat := do
  return (← rNat rng ((Nat.log2 m) / 64 + 2)) % m

def rBytes (rng : IO.Ref Rng) (n : Nat) : IO ByteArray := do
  let mut b := ByteArray.empty
  for _ in [0:n] do
    b := b.push (← rBelow rng 256).toUInt8
  return b

structure Tally where
  pass : Nat := 0
  fail : Nat := 0

def check (t : IO.Ref (Std.HashMap String Tally)) (name : String) (ok : Bool)
    (detail : Unit → String := fun _ => "") : IO Unit := do
  let m ← t.get
  let c := m.getD name {}
  t.set (m.insert name (if ok then { c with pass := c.pass + 1 } else { c with fail := c.fail + 1 }))
  unless ok do IO.println s!"FAIL {name}: {detail ()}"

/-! ## Pure-Lean reference arithmetic (affine, for checking blst) -/

def inv (a m : Nat) : Nat := powMod (a % m) (m - 2) m
def fsub (a b m : Nat) : Nat := (a % m + m - b % m) % m

namespace RefG1
def add (P Q : G1) : G1 :=
  if P == g1Zero then Q else if Q == g1Zero then P
  else if P.1 == Q.1 then
    if (P.2 + Q.2) % p == 0 then g1Zero
    else
      let l := 3 * P.1 * P.1 % p * inv (2 * P.2) p % p
      let x := fsub (l * l) (2 * P.1) p
      (x, fsub (l * fsub P.1 x p) P.2 p)
  else
    let l := fsub Q.2 P.2 p * inv (fsub Q.1 P.1 p) p % p
    let x := fsub (fsub (l * l) P.1 p) Q.1 p
    (x, fsub (l * fsub P.1 x p) P.2 p)
def neg (P : G1) : G1 := if P == g1Zero then P else (P.1, (p - P.2) % p)
partial def mul (P : G1) (n : Nat) : G1 :=
  if n == 0 then g1Zero
  else let h := mul (add P P) (n / 2); if n % 2 == 1 then add h P else h
end RefG1

namespace RefG2
open Evm.Crypto.Bls12381 (fp2Add fp2Mul)
def fp2Sub (a b : Fp2) : Fp2 := (fsub a.1 b.1 p, fsub a.2 b.2 p)
def fp2Inv (a : Fp2) : Fp2 :=
  let d := inv ((a.1 * a.1 + a.2 * a.2) % p) p
  (a.1 * d % p, (p - a.2 * d % p) % p)
def add (P Q : G2) : G2 :=
  if P == g2Zero then Q else if Q == g2Zero then P
  else if P.1 == Q.1 then
    if fp2Add P.2 Q.2 == (0, 0) then g2Zero
    else
      let l := fp2Mul (fp2Mul (3, 0) (fp2Mul P.1 P.1)) (fp2Inv (fp2Mul (2, 0) P.2))
      let x := fp2Sub (fp2Mul l l) (fp2Mul (2, 0) P.1)
      (x, fp2Sub (fp2Mul l (fp2Sub P.1 x)) P.2)
  else
    let l := fp2Mul (fp2Sub Q.2 P.2) (fp2Inv (fp2Sub Q.1 P.1))
    let x := fp2Sub (fp2Sub (fp2Mul l l) P.1) Q.1
    (x, fp2Sub (fp2Mul l (fp2Sub P.1 x)) P.2)
def neg (P : G2) : G2 := if P == g2Zero then P else (P.1, ((p - P.2.1) % p, (p - P.2.2) % p))
partial def mul (P : G2) (n : Nat) : G2 :=
  if n == 0 then g2Zero
  else let h := mul (add P P) (n / 2); if n % 2 == 1 then add h P else h
end RefG2

/-! ## P-256, executable (FIPS 186-5 §6.4) -/

namespace RefP256
open Evm.Crypto (p256P p256N p256A)
abbrev P := Nat × Nat
def O : P := (0, 0)
def add (A B : P) : P :=
  if A == O then B else if B == O then A
  else if A.1 == B.1 then
    if (A.2 + B.2) % p256P == 0 then O
    else
      let l := (3 * A.1 * A.1 + p256A) % p256P * inv (2 * A.2) p256P % p256P
      let x := fsub (l * l) (2 * A.1) p256P
      (x, fsub (l * fsub A.1 x p256P) A.2 p256P)
  else
    let l := fsub B.2 A.2 p256P * inv (fsub B.1 A.1 p256P) p256P % p256P
    let x := fsub (fsub (l * l) A.1 p256P) B.1 p256P
    (x, fsub (l * fsub A.1 x p256P) A.2 p256P)
partial def mul (A : P) (n : Nat) : P :=
  if n == 0 then O else let h := mul (add A A) (n / 2); if n % 2 == 1 then add h A else h
def G : P := (Evm.Crypto.p256Gx, Evm.Crypto.p256Gy)
/-- `EcdsaAccepts`, executable. -/
def verify (z r s qx qy : Nat) : Bool :=
  let w := inv s p256N
  let R := add (mul G (z * w % p256N)) (mul (qx, qy) (r * w % p256N))
  R != O && R.1 % p256N == r
end RefP256

/-! ## The tests -/

def blake2fVectors : List (Nat × String × Nat × Bool × String) :=
  -- (rounds, m, t0, f, expected) — EELS tests/istanbul/eip152_blake2/test_blake2.py
  let abc := "6162630000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000"
  let abcde := "6162636465000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000000"
  [ (0, abc, 3, true, "08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b"),
    (12, abc, 3, true, "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"),
    (12, abc, 3, false, "75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d2875298743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735"),
    (1, abc, 3, true, "b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fba551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421"),
    (12, abcde, 5, true, "f3e89a60ec4b0b1854744984e421d22b82f181bd4601fb9b1726b2662da61c29dff09e75814acb2639fd79e56616e55fc135f8476f0302b3dc8d44e082eb83a8"),
    (16, abc, 3, true, "a8ef8236e5f48a74af375df15681d128457891c1cc4706f30747b2d40300b2f49d19f80fbd0945fd87736e1fc1ff10a80fd85a7aa5125154f3aaa3789ddff673"),
    (1024, abc, 3, true, "689419d2bf32b5a9901a2c733b9946727026a60d8773117eabb35f04a52cdcf1b8fb4473454cf03d46c36a10b3f784aae4dc80a24424960e66a8ad5a8c2bfb30") ]

def blake2fInput (rounds : Nat) (m : String) (t0 : Nat) (f : Bool) : ByteArray :=
  let h := "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b"
  be rounds 4 ++ ofHex h ++ ofHex m ++
    ByteArray.mk ((List.range 8).toArray.map fun k => UInt8.ofNat (t0 / 256 ^ k % 256)) ++
    ByteArray.mk (Array.replicate 8 0) ++ ByteArray.mk #[if f then 1 else 0]

def blake2fTests (t : IO.Ref (Std.HashMap String Tally)) (rng : IO.Ref Rng) : IO Unit := do
  for (rounds, m, t0, f, want) in blake2fVectors do
    let inp := blake2fInput rounds m t0 f
    let got := Evm.Crypto.Blake2f.ofInput inp
    check t "blake2f: EIP-152 vector (Lean F)" (toHex got == want) fun _ => s!"rounds {rounds}: {toHex got}"
    check t "blake2f: EIP-152 vector (C)" (toHex (blake2fC inp) == want)
    match Evm.Istanbul.Vm.PrecompiledContracts.blake2f inp 100000 with
    | .ok (out, g) => check t "blake2f: precompile output and gas" (toHex out == want && g == 100000 - rounds)
    | .error _ => check t "blake2f: precompile output and gas" false
  for _ in [0:300] do
    let rounds ← rBelow rng 600
    let body ← rBytes rng 208
    let f ← rBelow rng 2
    let inp := be rounds 4 ++ body ++ ByteArray.mk #[f.toUInt8]
    check t "blake2f: random input, Lean F = C" (Evm.Crypto.Blake2f.ofInput inp == blake2fC inp)
      fun _ => toHex inp
  -- failures: bad flag, wrong length (C returns empty; the wrapper halts)
  for _ in [0:50] do
    let body ← rBytes rng 212
    let fb ← rBelow rng 256
    let inp := body ++ ByteArray.mk #[fb.toUInt8]
    let bad := fb > 1
    let w := match Evm.Istanbul.Vm.PrecompiledContracts.blake2f inp (2 ^ 40) with
      | .ok _ => false | .error _ => true
    check t "blake2f: flag validity (wrapper = C)" (w == bad && (blake2fC inp).size == (if bad then 0 else 64))
  for n in [0, 1, 212, 214, 300] do
    let inp ← rBytes rng n
    let w := match Evm.Istanbul.Vm.PrecompiledContracts.blake2f inp (2 ^ 40) with
      | .ok _ => false | .error _ => true
    check t "blake2f: wrong length halts (wrapper = C)" (w && (blake2fC inp).size == 0)

/-- A random on-curve G1 point (usually NOT in the subgroup): x random, y = √(x³+4). -/
partial def randG1Curve (rng : IO.Ref Rng) : IO G1 := do
  let x ← rBelow rng p
  let rhs := (x * x % p * x + 4) % p
  let y := powMod rhs ((p + 1) / 4) p
  if y * y % p == rhs then return (x, y) else randG1Curve rng

def randG1Sub (rng : IO.Ref Rng) : IO G1 := do return native.mapFpToG1 (← rBelow rng p)
def randG2Sub (rng : IO.Ref Rng) : IO G2 := do
  return native.mapFp2ToG2 ((← rBelow rng p), (← rBelow rng p))

open Evm.Crypto.Bls12381 (g1OnCurve g2OnCurve) in
def blsGroupTests (t : IO.Ref (Std.HashMap String Tally)) (rng : IO.Ref Rng)
    (nonSub : IO.Ref Nat) : IO Unit := do
  let o := native
  for _ in [0:12] do
    let a ← randG1Sub rng; let b ← randG1Sub rng; let c ← randG1Sub rng
    let x ← randG1Curve rng; let y ← randG1Curve rng
    check t "G1: map_fp_to_g1 on the curve" (g1OnCurve a && a != g1Zero)
    check t "G1: map_fp_to_g1 in the subgroup (in_g1)" (o.g1InSubgroup a)
    check t "G1: map_fp_to_g1 in the subgroup ([r]P = O, Lean)" (RefG1.mul a r == g1Zero)
    check t "G1: add = Lean affine group law (subgroup points)" (o.g1Add a b == RefG1.add a b)
    check t "G1: add = Lean affine group law (non-subgroup points)" (o.g1Add x y == RefG1.add x y)
    check t "G1: doubling = Lean (non-subgroup)" (o.g1Add x x == RefG1.add x x)
    check t "G1: associativity" (o.g1Add (o.g1Add a b) c == o.g1Add a (o.g1Add b c))
    check t "G1: associativity (non-subgroup)" (o.g1Add (o.g1Add x y) a == o.g1Add x (o.g1Add y a))
    check t "G1: commutativity" (o.g1Add a x == o.g1Add x a)
    check t "G1: identity" (o.g1Add a g1Zero == a && o.g1Add g1Zero x == x)
    check t "G1: inverse" (o.g1Add a (RefG1.neg a) == g1Zero && o.g1Add x (RefG1.neg x) == g1Zero)
    check t "G1: subgroup test rejects a non-subgroup point (in_g1 = ([r]P = O))"
      (o.g1InSubgroup x == (RefG1.mul x r == g1Zero))
    let n ← rNat rng 4
    check t "G1: mul = Lean double-and-add (subgroup, 256-bit scalar)" (o.g1Mul a n == RefG1.mul a n)
    -- NOT a contract (G1MulContract is restricted to the subgroup): blst's GLV path for
    -- scalars < r is wrong off the subgroup. Counted, reported, not a failure.
    if o.g1Mul x n != RefG1.mul x n then
      nonSub.modify (· + 1)
      check t "G1: mul off the subgroup differs from n·P only via GLV (n < r)" (n < r)
    let k ← rBelow rng 9
    check t "G1: mul by small k = repeated add" (o.g1Mul a k == (List.replicate k a).foldl o.g1Add g1Zero)
    check t "G1: mul by r = O (subgroup)" (o.g1Mul a r == g1Zero)
  for _ in [0:6] do
    let a ← randG2Sub rng; let b ← randG2Sub rng; let c ← randG2Sub rng
    check t "G2: map_fp2_to_g2 on the curve" (g2OnCurve a && a != g2Zero)
    check t "G2: map_fp2_to_g2 in the subgroup (in_g2)" (o.g2InSubgroup a)
    check t "G2: add = Lean affine group law over Fp2" (o.g2Add a b == RefG2.add a b)
    check t "G2: doubling = Lean" (o.g2Add a a == RefG2.add a a)
    check t "G2: associativity" (o.g2Add (o.g2Add a b) c == o.g2Add a (o.g2Add b c))
    check t "G2: commutativity" (o.g2Add a b == o.g2Add b a)
    check t "G2: identity" (o.g2Add a g2Zero == a && o.g2Add g2Zero a == a)
    check t "G2: inverse" (o.g2Add a (RefG2.neg a) == g2Zero)
    let n ← rNat rng 4
    check t "G2: mul = Lean double-and-add (256-bit scalar)" (o.g2Mul a n == RefG2.mul a n)
    let k ← rBelow rng 9
    check t "G2: mul by small k = repeated add" (o.g2Mul a k == (List.replicate k a).foldl o.g2Add g2Zero)
    check t "G2: [r]Q = O" (o.g2Mul a r == g2Zero && RefG2.mul a r == g2Zero)
  -- MSM against Σ mᵢ·Pᵢ (Lean reference) and the production entry
  for _ in [0:8] do
    let k := 1 + (← rBelow rng 4)
    let mut inp1 := ByteArray.empty; let mut sum1 := g1Zero
    let mut inp2 := ByteArray.empty; let mut sum2 := g2Zero
    for _ in [0:k] do
      let P ← randG1Sub rng; let Q ← randG2Sub rng; let m ← rNat rng 4
      inp1 := inp1 ++ g1Encode P ++ be m 32; sum1 := RefG1.add sum1 (RefG1.mul P m)
      inp2 := inp2 ++ g2Encode Q ++ be m 32; sum2 := RefG2.add sum2 (RefG2.mul Q m)
    let p1 := prodG1Msm inp1
    check t "G1MSM: production = Σ mᵢ·Pᵢ (Lean)" (p1 == g1Encode sum1)
    check t "G1MSM: Lean wrapper over blst = Σ mᵢ·Pᵢ"
      (match Evm.Prague.Vm.PrecompiledContracts.blsG1MsmWith o inp1 (2 ^ 40) with
       | .ok (out, _) => out == g1Encode sum1 | .error _ => false)
    check t "G2MSM: production = Σ mᵢ·Qᵢ (Lean)" (prodG2Msm inp2 == g2Encode sum2)
  -- pairing
  for _ in [0:4] do
    let P ← randG1Sub rng; let Q ← randG2Sub rng
    let a := 1 + (← rBelow rng (r - 1)); let b := 1 + (← rBelow rng (r - 1))
    let ab := a * b % r
    let aP := o.g1Mul P a; let bQ := o.g2Mul Q b
    check t "pairing: bilinear, e(aP, bQ)·e(−(ab)P, Q) = 1"
      (o.pairingCheck [(aP, bQ), (RefG1.neg (o.g1Mul P ab), Q)])
    check t "pairing: e(P, Q)·e(−P, Q) = 1" (o.pairingCheck [(P, Q), (RefG1.neg P, Q)])
    check t "pairing: e(P, Q)·e(P, −Q) = 1" (o.pairingCheck [(P, Q), (P, RefG2.neg Q)])
    check t "pairing: non-degenerate, e(P, Q) ≠ 1" (!o.pairingCheck [(P, Q)])
    check t "pairing: e(aP, bQ)·e(−(ab+1)P, Q) ≠ 1"
      (!o.pairingCheck [(aP, bQ), (RefG1.neg (o.g1Mul P ((ab + 1) % r)), Q)])
    check t "pairing: e(O, Q) = e(P, O) = 1" (o.pairingCheck [(g1Zero, Q), (P, g2Zero)])

/-- The Lean wrapper's verdict over `native` vs the production entry: both fail, or both
    return the same bytes. -/
def agree (lean : Except Evm.Frontier.Vm.Exception (ByteArray × Nat)) (prod : ByteArray) : Bool :=
  match lean with
  | .ok (out, _) => prod.size != 0 && out == prod
  | .error _ => prod.size == 0

open Evm.Prague.Vm.PrecompiledContracts in
def blsWrapperTests (t : IO.Ref (Std.HashMap String Tally)) (rng : IO.Ref Rng) : IO Unit := do
  let o := native
  let ops : List (String × (ByteArray → Nat → Except Evm.Frontier.Vm.Exception (ByteArray × Nat)) ×
      (ByteArray → ByteArray)) :=
    [("G1ADD", blsG1AddWith o, prodG1Add), ("G1MSM", blsG1MsmWith o, prodG1Msm),
     ("G2ADD", blsG2AddWith o, prodG2Add), ("G2MSM", blsG2MsmWith o, prodG2Msm),
     ("PAIRING_CHECK", blsPairingWith o, prodPairing),
     ("MAP_FP_TO_G1", blsMapFpToG1With o, prodMapFpToG1),
     ("MAP_FP2_TO_G2", blsMapFp2ToG2With o, prodMapFp2ToG2)]
  let txt ← IO.FS.readFile "c/testdata/bls12381-vectors.json"
  let some vs := (do let j ← Lean.Json.parse txt; let a ← j.getObjValAs? (Array Lean.Json) "vectors"; pure a).toOption
    | check t "EIP-2537 vectors: parse" false; return
  for v in vs do
    let op := (v.getObjValAs? String "op").toOption.getD ""
    let inp := ofHex ((v.getObjValAs? String "input").toOption.getD "")
    let want := ofHex ((v.getObjValAs? String "output").toOption.getD "")
    let ok := (v.getObjValAs? String "expect").toOption == some "ok"
    let gasUsed := (v.getObjValAs? Nat "gas_used").toOption.getD 0
    match ops.find? (·.1 == op) with
    | none => check t "EIP-2537 vectors: known op" false fun _ => op
    | some (_, f, prod) =>
      let res := f inp 10000000
      let good := match res with
        | .ok (out, g) => ok && out == want && (gasUsed == 0 || 10000000 - g == gasUsed)
        | .error _ => !ok
      check t s!"EIP-2537 vectors: Lean wrapper over blst ({op})" good fun _ => toHex inp
      check t s!"EIP-2537 vectors: Lean wrapper = production ({op})" (agree res (prod inp))
      -- mutations of the vector: one random byte changed, and a coordinate pushed ≥ p
      for _ in [0:6] do
        if inp.size == 0 then break
        let i ← rBelow rng inp.size
        let x ← rBelow rng 256
        let m := inp.set! i x.toUInt8
        check t s!"mutated inputs: Lean wrapper = production ({op})" (agree (f m 10000000) (prod m))
          fun _ => toHex m
      if inp.size ≥ 64 then
        let k := (← rBelow rng (inp.size / 64)) * 64
        let hi := be (p + (← rBelow rng 1000)) 64
        let m := inp.extract 0 k ++ hi ++ inp.extract (k + 64) inp.size
        check t s!"field element ≥ p: Lean wrapper = production ({op})" (agree (f m 10000000) (prod m))
  -- a non-subgroup point: accepted by ADD, rejected by MSM and PAIRING (EIP-2537)
  for _ in [0:4] do
    let x ← randG1Curve rng
    let a ← randG1Sub rng
    let addIn := g1Encode x ++ g1Encode a
    check t "non-subgroup point: G1ADD accepts (both)" (agree (blsG1AddWith o addIn 10000) (prodG1Add addIn) &&
      (prodG1Add addIn).size == 128)
    let msmIn := g1Encode x ++ be 5 32
    check t "non-subgroup point: G1MSM rejects (both)" (agree (blsG1MsmWith o msmIn 100000) (prodG1Msm msmIn) &&
      (prodG1Msm msmIn).size == 0)
    let pairIn := g1Encode x ++ g2Encode (← randG2Sub rng)
    check t "non-subgroup point: PAIRING rejects (both)" (agree (blsPairingWith o pairIn 1000000) (prodPairing pairIn) &&
      (prodPairing pairIn).size == 0)
  -- random valid inputs
  for _ in [0:6] do
    let a ← randG1Sub rng; let b ← randG1Sub rng
    let q ← randG2Sub rng; let q2 ← randG2Sub rng
    check t "random: G1ADD Lean wrapper = production" (agree (blsG1AddWith o (g1Encode a ++ g1Encode b) 1000) (prodG1Add (g1Encode a ++ g1Encode b)))
    check t "random: G2ADD Lean wrapper = production" (agree (blsG2AddWith o (g2Encode q ++ g2Encode q2) 1000) (prodG2Add (g2Encode q ++ g2Encode q2)))
    let u ← rBytes rng 48
    let fp := ByteArray.mk (Array.replicate 16 0) ++ u
    check t "random: MAP_FP_TO_G1 Lean wrapper = production" (agree (blsMapFpToG1With o fp 10000) (prodMapFpToG1 fp))
    let pin := g1Encode a ++ g2Encode q ++ g1Encode (RefG1.neg a) ++ g2Encode q
    check t "random: PAIRING Lean wrapper = production (= 1)" (agree (blsPairingWith o pin 1000000) (prodPairing pin) &&
      prodPairing pin == be 1 32)
  -- wrong lengths and too little gas
  for n in [0, 1, 128, 255, 257, 320] do
    let inp ← rBytes rng n
    for (op, f, prod) in ops do
      check t s!"random bytes / wrong length: Lean wrapper = production ({op})" (agree (f inp 10000000) (prod inp))
  check t "too little gas halts (G1ADD at 374)"
    (match blsG1AddWith o (g1Encode g1Zero ++ g1Encode g1Zero) 374 with | .error _ => true | _ => false)

open Evm.Crypto in
def p256Tests (t : IO.Ref (Std.HashMap String Tally)) (rng : IO.Ref Rng) : IO Unit := do
  let w (n : Nat) := be n 32
  let wrapper (inp : ByteArray) : Bool :=
    match Evm.Osaka.Vm.PrecompiledContracts.p256verify inp 100000 with
    | .ok (out, g) => g == 100000 - 6900 && out == p256SuccessOutput
    | .error _ => false
  let prod (inp : ByteArray) : Bool := verifyRaw inp == 1
  -- G is on the curve (the contract's base point)
  check t "P-256: G on the curve" (p256OnCurve RefP256.G.1 RefP256.G.2)
  check t "P-256: [n]G = O (Lean)" (RefP256.mul RefP256.G p256N == RefP256.O)
  -- the Base chain inputs of tests/p256verify.lisp (accepted on chain)
  for hex in ["032863bc9bc69fa311ab0f532a4a1a00d53080b42d249de8647a5ad7c012a46d68af4c313bcfdf538d4e0f0d27da604e7d4bbff7227b061540171ea64a78f35262a2f530cd9781d78769ba30b571165310f472a3a33d12823f64fb6af9b87731b91548a7471175c93715b4f4c51157f2ff4b6a410033a5f1e74a3d85a0f2b1fbea2f9d0852046f31ad80fb758237d02e2643cb0b657c5fa7535c95595b0dd184",
              "283fcf929fa281c119c65363a7f798c0da2ace33fa4397a7a6b6b679c2bed14bbb80edae42797723ae992a3520069295e73d448911db7688a97546a49a6d5a191aa6cf56dc23598cebfe9ab0e4b87cc3959df632c8f31ccbd2ff82fbc1622536bb1e45ddec2e4d7dca4223dc6c502d7031b6b2ec95170031221a0d57391323965e98a445978d25833642b1c237143ca724516d583054581df2508e32fa3c1fe5"] do
    let inp := ofHex hex
    let wd (k : Nat) := p256Word inp (32 * k)
    check t "P-256: chain input, Lean wrapper over OpenSSL accepts" (wrapper inp)
    check t "P-256: chain input, executable EcdsaAccepts accepts" (RefP256.verify (wd 0) (wd 1) (wd 2) (wd 3) (wd 4))
  -- sign in Lean, verify with OpenSSL
  for _ in [0:12] do
    let d := 1 + (← rBelow rng (p256N - 1))
    let Q := RefP256.mul RefP256.G d
    let z ← rNat rng 4
    let k := 1 + (← rBelow rng (p256N - 1))
    let R := RefP256.mul RefP256.G k
    let rr := R.1 % p256N
    let s := inv k p256N * ((z + rr * d) % p256N) % p256N
    if rr == 0 || s == 0 then continue
    let inp := w z ++ w rr ++ w s ++ w Q.1 ++ w Q.2
    check t "P-256: sign (Lean) / verify (OpenSSL) round trip" (isValidP256Signature z rr s Q.1 Q.2)
    check t "P-256: round trip through the precompile wrapper" (wrapper inp)
    check t "P-256: executable EcdsaAccepts agrees" (RefP256.verify z rr s Q.1 Q.2)
    let s' := p256N - s
    check t "P-256: (r, n − s) also verifies (no low-s rule)" (isValidP256Signature z rr s' Q.1 Q.2 && RefP256.verify z rr s' Q.1 Q.2)
    for (lbl, z2, r2, s2, qx, qy) in [("digest", (z + 1) % 2 ^ 256, rr, s, Q.1, Q.2),
        ("r", z, rr % (p256N - 1) + 1, s, Q.1, Q.2), ("s", z, rr, s % (p256N - 1) + 1, Q.1, Q.2),
        ("key", z, rr, s, (RefP256.add Q RefP256.G).1, (RefP256.add Q RefP256.G).2)] do
      if (lbl == "r" && r2 == rr) || (lbl == "s" && s2 == s) then continue
      check t s!"P-256: tampered {lbl} rejected (OpenSSL = EcdsaAccepts = false)"
        (!isValidP256Signature z2 r2 s2 qx qy && !RefP256.verify z2 r2 s2 qx qy)
    -- edge inputs: EELS's bounds (the wrapper) vs OpenSSL alone (the production entry)
    let edges : List (String × ByteArray) :=
      [("r = 0", w z ++ w 0 ++ w s ++ w Q.1 ++ w Q.2), ("r = n", w z ++ w p256N ++ w s ++ w Q.1 ++ w Q.2),
       ("s = n", w z ++ w rr ++ w p256N ++ w Q.1 ++ w Q.2),
       ("r + n", w z ++ w (rr + p256N) ++ w s ++ w Q.1 ++ w Q.2),
       ("qx + p", w z ++ w rr ++ w s ++ w (Q.1 + p256P) ++ w Q.2),
       ("qy + p", w z ++ w rr ++ w s ++ w Q.1 ++ w (Q.2 + p256P)),
       ("Q = (0, 0)", w z ++ w rr ++ w s ++ w 0 ++ w 0),
       ("Q off the curve", w z ++ w rr ++ w s ++ w Q.1 ++ w ((Q.2 + 1) % p256P))]
    for (lbl, e) in edges do
      check t s!"P-256 edge {lbl}: wrapper rejects" (!wrapper e)
      check t s!"P-256 edge {lbl}: OpenSSL alone (production) agrees with EELS" (!prod e)
        fun _ => toHex e
  check t "P-256: wrong length → empty output, gas charged"
    (match Evm.Osaka.Vm.PrecompiledContracts.p256verify (ByteArray.mk (Array.replicate 159 1)) 7000 with
     | .ok (out, g) => out.size == 0 && g == 100 | .error _ => false)
  check t "P-256: too little gas halts"
    (match Evm.Osaka.Vm.PrecompiledContracts.p256verify ByteArray.empty 6899 with
     | .error _ => true | .ok _ => false)

def main : IO UInt32 := do
  let t ← IO.mkRef ({} : Std.HashMap String Tally)
  let rng ← IO.mkRef (⟨0x5eed1e55⟩ : Rng)
  let t0 ← IO.monoMsNow
  blake2fTests t rng
  let nonSub ← IO.mkRef 0
  blsGroupTests t rng nonSub
  blsWrapperTests t rng
  p256Tests t rng
  let m ← t.get
  let rows := m.toList.toArray.qsort (fun a b => a.1 < b.1)
  let mut fails := 0
  for (name, c) in rows do
    IO.println s!"{if c.fail == 0 then "ok  " else "FAIL"} {c.pass}/{c.pass + c.fail}  {name}"
    fails := fails + c.fail
  IO.println s!"info: blst G1 mul on random NON-subgroup points differed from n·P in {← nonSub.get}/12 cases (outside G1MulContract; the wrapper never multiplies such points)"
  IO.println s!"cryptoTests: {rows.size} properties, {fails} failure(s), {(← IO.monoMsNow) - t0} ms"
  return if fails == 0 then 0 else 1
