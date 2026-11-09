/-
  Evm.Crypto.Contracts — what the crypto oracles are ASSUMED to compute, in Mathlib terms.

  The EIP-2537 and P256VERIFY wrappers are proved against EELS for every oracle
  (`Evm.Prague.Spec.Refinement.*_sound`, `Evm.Osaka.Spec.Refinement.p256Verify_sound`).
  The replay runs one instance per library — `Evm.Crypto.Bls12381.native` (blst) and
  `Evm.Crypto.isValidP256Signature` (OpenSSL). The propositions below say what those
  instances should be: the elliptic-curve group law of Mathlib's `WeierstrassCurve.Affine`
  over the right field, scalar multiplication as `•` in that group, the subgroup test as
  `r • P = 0`, map-to-curve landing in the order-r subgroup, the pairing check as the
  product of a bilinear non-degenerate pairing, and P-256 verification as FIPS 186-5 ECDSA
  over Mathlib's curve.

  These are documented ASSUMPTIONS: not axioms, and not hypotheses of any theorem (the
  wrapper theorems hold for every oracle). They are the trusted surface stated precisely;
  `cryptoTests` checks them on random inputs against the native libraries. Primality of
  the moduli (needed for `ZMod p` to be a field) and irreducibility of `X² + 1` over Fp are
  instance arguments, also assumed rather than proved here.

  Found by the property tests (2026-11-09) and reflected here: blst's scalar
  multiplication is `n • P` only on the order-r subgroup (`G1MulContract`).

  Gaps, stated: the pairing is an abstract bilinear non-degenerate map (Mathlib has no
  pairings), not the optimal ate pairing of BLS12-381; the map-to-curve contracts say
  "lands in the subgroup", not "is RFC 9380's SSWU map + isogeny + cofactor clearing".
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Field.ZMod
import Evm.Crypto.Bls12381
import Evm.Crypto.P256Verify

namespace Evm.Crypto.Contracts

open Polynomial

/-! ## BLS12-381 -/

namespace Bls12381

open Evm.Crypto.Bls12381 (Oracle G1 G2 p r)

/-- The base field Fp. -/
abbrev Fp := ZMod p

/-- G1's curve E : y² = x³ + 4 over Fp. -/
def E1 : WeierstrassCurve.Affine Fp := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 4 }

/-- Fp2 = Fp[u]/(u² + 1). -/
abbrev Fp2 := AdjoinRoot (X ^ 2 + 1 : Fp[X])

/-- `c0 + c1·u`. -/
noncomputable def fp2 (c0 c1 : Nat) : Fp2 :=
  AdjoinRoot.of _ (c0 : Fp) + AdjoinRoot.of _ (c1 : Fp) * AdjoinRoot.root _

/-- G2's curve E' : y² = x³ + 4(1 + u) over Fp2 (the M-type sextic twist). -/
noncomputable def E2 : WeierstrassCurve.Affine Fp2 :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := fp2 4 4 }

/-- The coordinate pair `c` (EIP-2537's affine encoding, (0, 0) = infinity) denotes `P`. -/
def Rep1 (c : G1) (P : WeierstrassCurve.Affine.Point E1) : Prop :=
  match P with
  | .zero => c = (0, 0)
  | .some x y _ => c = (x.val, y.val)

/-- An Fp2 coordinate pair in canonical range denotes `z`. -/
def RepFp2 (c : Nat × Nat) (z : Fp2) : Prop := c.1 < p ∧ c.2 < p ∧ z = fp2 c.1 c.2

def Rep2 (c : G2) (Q : WeierstrassCurve.Affine.Point E2) : Prop :=
  match Q with
  | .zero => c = ((0, 0), (0, 0))
  | .some x y _ => RepFp2 c.1 x ∧ RepFp2 c.2 y

variable [hp : Fact (Nat.Prime p)] [hi : Fact (Irreducible (X ^ 2 + 1 : Fp[X]))]
include hp hi

/-- G1 addition is the Mathlib group law. -/
def G1AddContract (o : Oracle) : Prop :=
  ∀ a b P Q, Rep1 a P → Rep1 b Q → Rep1 (o.g1Add a b) (P + Q)

/-- G1 scalar multiplication is `n • P` on the order-r subgroup (scalars < 2²⁵⁶), which is
    where the wrapper uses it (MSM points are subgroup-checked first). NOT on the whole
    curve: blst's `blst_p1_mult` takes the GLV path for scalars < r, which is only valid in
    the subgroup — `cryptoTests` measures the difference on random non-subgroup points
    (found 2026-11-09 by this file's first property run). -/
def G1MulContract (o : Oracle) : Prop :=
  ∀ a P n, n < 2 ^ 256 → Rep1 a P → r • P = 0 → Rep1 (o.g1Mul a n) (n • P)

/-- The G1 subgroup test is `r • P = 0` (EELS: `is_inf(multiply(P, curve_order))`). -/
def G1SubgroupContract (o : Oracle) : Prop :=
  ∀ a P, Rep1 a P → (o.g1InSubgroup a = true ↔ r • P = 0)

def G2AddContract (o : Oracle) : Prop :=
  ∀ a b P Q, Rep2 a P → Rep2 b Q → Rep2 (o.g2Add a b) (P + Q)

/-- G2 scalar multiplication on the order-r subgroup (as for G1: blst's endomorphism
    path is only valid there). -/
def G2MulContract (o : Oracle) : Prop :=
  ∀ a P n, n < 2 ^ 256 → Rep2 a P → r • P = 0 → Rep2 (o.g2Mul a n) (n • P)

def G2SubgroupContract (o : Oracle) : Prop :=
  ∀ a P, Rep2 a P → (o.g2InSubgroup a = true ↔ r • P = 0)

/-- MAP_FP_TO_G1 lands on E and in the order-r subgroup. -/
def MapFpToG1Contract (o : Oracle) : Prop :=
  ∀ u, u < p → ∃ P, Rep1 (o.mapFpToG1 u) P ∧ r • P = 0

/-- MAP_FP2_TO_G2 lands on E' and in the order-r subgroup. -/
def MapFp2ToG2Contract (o : Oracle) : Prop :=
  ∀ u : Nat × Nat, u.1 < p → u.2 < p → ∃ Q, Rep2 (o.mapFp2ToG2 u) Q ∧ r • Q = 0

/-- The pairing check is `∏ e(Pᵢ, Qᵢ) = 1` for some bilinear, non-degenerate `e` on the
    order-r subgroups (abstract: Mathlib has no pairings; TODO the optimal ate pairing). -/
def PairingContract (o : Oracle) : Prop :=
  ∃ (GT : Type) (_ : CommGroup GT)
    (e : WeierstrassCurve.Affine.Point E1 → WeierstrassCurve.Affine.Point E2 → GT),
    (∀ P P' Q, r • P = 0 → r • P' = 0 → r • Q = 0 → e (P + P') Q = e P Q * e P' Q) ∧
    (∀ P Q Q', r • P = 0 → r • Q = 0 → r • Q' = 0 → e P (Q + Q') = e P Q * e P Q') ∧
    (∀ P, r • P = 0 → P ≠ 0 → ∃ Q, r • Q = 0 ∧ e P Q ≠ 1) ∧
    (∀ Q, r • Q = 0 → Q ≠ 0 → ∃ P, r • P = 0 ∧ e P Q ≠ 1) ∧
    ∀ (ps : List (G1 × G2)) (Ps : List (WeierstrassCurve.Affine.Point E1 ×
        WeierstrassCurve.Affine.Point E2)),
      List.Forall₂ (fun c P => Rep1 c.1 P.1 ∧ Rep2 c.2 P.2 ∧ r • P.1 = 0 ∧ r • P.2 = 0) ps Ps →
      (o.pairingCheck ps = true ↔ (Ps.map fun P => e P.1 P.2).prod = 1)

/-- Every BLS12-381 contract of the oracle. -/
def Contract (o : Oracle) : Prop :=
  G1AddContract o ∧ G1MulContract o ∧ G1SubgroupContract o ∧
  G2AddContract o ∧ G2MulContract o ∧ G2SubgroupContract o ∧
  MapFpToG1Contract o ∧ MapFp2ToG2Contract o ∧ PairingContract o

/-- MSM is the sum of the scalar multiples: under the add and mul contracts, EELS's fold
    (`Evm.Crypto.Bls12381.g1MsmSum`) over subgroup points denotes `Σ nᵢ • Pᵢ`. -/
theorem g1MsmSum_contract (o : Oracle) (hadd : G1AddContract o) (hmul : G1MulContract o) :
    ∀ (ps : List (G1 × Nat)) (Ps : List (WeierstrassCurve.Affine.Point E1)),
      List.Forall₂ (fun c P => Rep1 c.1 P ∧ c.2 < 2 ^ 256 ∧ r • P = 0) ps Ps → ps ≠ [] →
      Rep1 (Evm.Crypto.Bls12381.g1MsmSum o ps) ((List.zipWith (fun c P => c.2 • P) ps Ps).sum) := by
  intro ps Ps h hne
  cases h with
  | nil => exact absurd rfl hne
  | @cons c P ps' Ps' hc hrest =>
    simp only [Evm.Crypto.Bls12381.g1MsmSum, List.zipWith_cons_cons, List.sum_cons]
    -- generalize the accumulator
    have key : ∀ (acc : G1) (A : WeierstrassCurve.Affine.Point E1), Rep1 acc A →
        ∀ (qs : List (G1 × Nat)) (Qs : List (WeierstrassCurve.Affine.Point E1)),
        List.Forall₂ (fun c P => Rep1 c.1 P ∧ c.2 < 2 ^ 256 ∧ r • P = 0) qs Qs →
        Rep1 (qs.foldl (fun acc q => o.g1Add acc (o.g1Mul q.1 q.2)) acc)
          (A + (List.zipWith (fun c P => c.2 • P) qs Qs).sum) := by
      intro acc A hA qs Qs hq
      induction hq generalizing acc A with
      | nil => simpa using hA
      | @cons q Q qs Qs hq _ ih =>
        simp only [List.foldl_cons, List.zipWith_cons_cons, List.sum_cons, ← add_assoc]
        exact ih _ _ (hadd _ _ _ _ hA (hmul _ _ _ hq.2.1 hq.1 hq.2.2))
    exact key _ _ (hmul _ _ _ hc.2.1 hc.1 hc.2.2) _ _ hrest

end Bls12381

/-! ## P-256 (secp256r1) -/

namespace P256

/-- The base field. -/
abbrev Fp := ZMod p256P

/-- secp256r1: y² = x³ + a·x + b over Fp (SEC 2 §2.4.2, EELS `elliptic_curve.py` 79-90). -/
def E : WeierstrassCurve.Affine Fp :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := (p256A : Fp), a₆ := (p256B : Fp) }


def Rep (c : Nat × Nat) (P : WeierstrassCurve.Affine.Point E) : Prop :=
  match P with
  | .zero => c = (0, 0)
  | .some x y _ => c = (x.val, y.val)

variable [hp : Fact (Nat.Prime p256P)]
include hp

/-- FIPS 186-5 §6.4.2 ECDSA verification of `(r, s)` on the 256-bit digest `z` under the
    public key `Q` with base point `G` (e = z, as n has 256 bits): w = s⁻¹ mod n,
    R = (z·w)·G + (r·w)·Q, accept iff R ≠ O and x(R) ≡ r (mod n). -/
def EcdsaAccepts (G Q : WeierstrassCurve.Affine.Point E) (z r s : Nat) : Prop :=
  let w : ZMod p256N := (s : ZMod p256N)⁻¹
  let u1 := ((z : ZMod p256N) * w).val
  let u2 := ((r : ZMod p256N) * w).val
  match u1 • G + u2 • Q with
  | .zero => False
  | .some x _ _ => x.val % p256N = r

/-- The verifier accepts exactly the valid ECDSA signatures, for in-range `r`, `s` and a
    public key on the curve other than infinity (what the wrapper passes it). -/
def P256VerifyContract (verify : P256Verifier) : Prop :=
  ∀ G, Rep (p256Gx, p256Gy) G → ∀ qx qy Q, Rep (qx, qy) Q → Q ≠ 0 →
    ∀ z r s, z < 2 ^ 256 → 0 < r → r < p256N → 0 < s → s < p256N →
      (verify z r s qx qy = true ↔ EcdsaAccepts G Q z r s)

end P256

end Evm.Crypto.Contracts
