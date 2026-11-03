import Evm.Cancun.Spec.BlobTx
import Evm.Cancun.Spec.KzgStep
import Evm.Optimism.Fjord.Spec.P256Verify

/-! # Evm.CL.GasEmit — arithmetic gas IR, emitted to CL (closes #260 / #261)

`HostEmit.Pred` is a boolean decision IR; consensus gas formulas need integer
arithmetic. This module adds an `Expr` IR over named Nat inputs with the SAME
`eval`/`toCL` discipline: `eval` is the Lean semantics we check against the EIP
numbers, `toCL` emits the identical computation as Common Lisp. The hand-written
`modexp-gas` in `src/evm/precompiles.lisp` (a parallel, fork-blind copy that caused
the Byzantium divergence #260) is replaced by the emitted `spec-modexp-gas`; the
byte-reading stays the hand-written seam, exactly like `Pred`'s world queries. -/

namespace Evm.CL.GasEmit

/-- Bit length, matching Common Lisp `integer-length` for non-negative integers:
    `blen 0 = 0`, else `⌊log2 n⌋ + 1`. -/
def blen (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- Arithmetic gas IR over named Nat runtime inputs. -/
inductive Expr where
  | lit  (n : Nat)
  | var  (name : String)
  | add  (a b : Expr)
  | sub  (a b : Expr)            -- truncated Nat subtraction (Nat.sub)
  | mul  (a b : Expr)
  | fdiv (a b : Expr)            -- floor division (divisor is a nonzero literal here)
  | emax (a b : Expr)
  | emin (a b : Expr)
  | bits (a : Expr)              -- bit length = CL integer-length
  | ite  (lo hi t e : Expr)      -- if lo < hi then t else e
  | fakeExp (factor numer denom : Expr)   -- EIP-4844 fake_exponential (integer Taylor series)
  | pow2 (a : Expr)              -- 2^a (the difficulty bomb's 2**num_bomb_periods)
  deriving Inhabited, Repr

/-- The runtime environment: each named input bound to a Nat. -/
abbrev Env := String → Nat

/-- Lean semantics — the meaning we check the EIP numbers against. -/
def Expr.eval (ρ : Env) : Expr → Nat
  | .lit n        => n
  | .var x        => ρ x
  | .add a b      => a.eval ρ + b.eval ρ
  | .sub a b      => a.eval ρ - b.eval ρ
  | .mul a b      => a.eval ρ * b.eval ρ
  | .fdiv a b     => a.eval ρ / b.eval ρ
  | .emax a b     => max (a.eval ρ) (b.eval ρ)
  | .emin a b     => min (a.eval ρ) (b.eval ρ)
  | .bits a       => blen (a.eval ρ)
  | .ite lo hi t e => if lo.eval ρ < hi.eval ρ then t.eval ρ else e.eval ρ
  | .fakeExp f n d => Evm.Cancun.Spec.fakeExponential (f.eval ρ) (n.eval ρ) (d.eval ρ)
  | .pow2 a        => 2 ^ a.eval ρ

/-- EELS `fake_exponential` (cancun/vm/gas.py) as Common Lisp, the one loop the `Expr`
    IR has: `spec-fake-exponential` is emitted once (EmitHostCL) and `.fakeExp` calls it.
    The Lean meaning is `Evm.Cancun.Spec.fakeExponential`, fuel-bounded for totality;
    the examples below pin the two on the Cancun and Prague fractions. -/
def fakeExponentialCL : String :=
  "(let ((i 1) (output 0) (accum (* factor denominator)))\n" ++
  "    (loop while (plusp accum)\n" ++
  "          do (incf output accum)\n" ++
  "             (setf accum (floor (* accum numerator) (* denominator i)))\n" ++
  "             (incf i))\n" ++
  "    (floor output denominator))"

/-- CL code generation — the SAME term as Common Lisp. -/
def Expr.toCL : Expr → String
  | .lit n        => toString n
  | .var x        => x
  | .add a b      => s!"(+ {a.toCL} {b.toCL})"
  | .sub a b      => s!"(max 0 (- {a.toCL} {b.toCL}))"
  | .mul a b      => s!"(* {a.toCL} {b.toCL})"
  | .fdiv a b     => s!"(floor {a.toCL} {b.toCL})"
  | .emax a b     => s!"(max {a.toCL} {b.toCL})"
  | .emin a b     => s!"(min {a.toCL} {b.toCL})"
  | .bits a       => s!"(integer-length {a.toCL})"
  | .ite lo hi t e => s!"(if (< {lo.toCL} {hi.toCL}) {t.toCL} {e.toCL})"
  | .fakeExp f n d => s!"(spec-fake-exponential {f.toCL} {n.toCL} {d.toCL})"
  | .pow2 a        => s!"(expt 2 {a.toCL})"

/-- Substitute expression `a` for variable `x` (composition of emitted formulas: a later
    stage's input is an earlier stage's output). -/
def Expr.subst : Expr → String → Expr → Expr
  | .lit n,         _, _ => .lit n
  | .var y,         x, a => if y = x then a else .var y
  | .add p q,       x, a => .add (p.subst x a) (q.subst x a)
  | .sub p q,       x, a => .sub (p.subst x a) (q.subst x a)
  | .mul p q,       x, a => .mul (p.subst x a) (q.subst x a)
  | .fdiv p q,      x, a => .fdiv (p.subst x a) (q.subst x a)
  | .emax p q,      x, a => .emax (p.subst x a) (q.subst x a)
  | .emin p q,      x, a => .emin (p.subst x a) (q.subst x a)
  | .bits p,        x, a => .bits (p.subst x a)
  | .ite lo hi t e, x, a => .ite (lo.subst x a) (hi.subst x a) (t.subst x a) (e.subst x a)
  | .fakeExp f n d, x, a => .fakeExp (f.subst x a) (n.subst x a) (d.subst x a)
  | .pow2 p,        x, a => .pow2 (p.subst x a)

/-- Evaluating a substitution = evaluating in the environment updated at `x`. -/
theorem Expr.eval_subst (ρ : Env) (x : String) (a e : Expr) :
    (e.subst x a).eval ρ = e.eval (fun y => if y = x then a.eval ρ else ρ y) := by
  induction e with
  | lit n => simp [Expr.subst, Expr.eval]
  | var y => by_cases h : y = x <;> simp [Expr.subst, Expr.eval, h]
  | add p q ihp ihq | sub p q ihp ihq | mul p q ihp ihq | fdiv p q ihp ihq
  | emax p q ihp ihq | emin p q ihp ihq => simp [Expr.subst, Expr.eval, ihp, ihq]
  | bits p ih | pow2 p ih => simp [Expr.subst, Expr.eval, ih]
  | ite lo hi t e ihlo ihhi iht ihe => simp [Expr.subst, Expr.eval, ihlo, ihhi, iht, ihe]
  | fakeExp f n d ihf ihn ihd => simp [Expr.subst, Expr.eval, ihf, ihn, ihd]

/-- Build an `Env` from a binding list (unbound names → 0). For refinement vectors. -/
def mkEnv (xs : List (String × Nat)) : Env :=
  fun n => (xs.find? (·.1 = n)).elim 0 (·.2)

/-! ## MODEXP gas (EIP-198 pre-Berlin, EIP-2565 Berlin+)

Inputs (read from the precompile input by the CL seam): `base-sz`, `exp-sz`,
`mod-sz`, `exp-head` (first ≤32 bytes of the exponent as an integer), `fork-ord`. -/

private def base : Expr := .var "base-sz"
private def esz  : Expr := .var "exp-sz"
private def msz  : Expr := .var "mod-sz"
private def ehd  : Expr := .var "exp-head"
def fork : Expr := .var "fork-ord"
private def maxlen : Expr := .emax base msz

/-- adjusted_exponent_length (EIP-198 §, shared by EIP-2565). Truncated `sub`
    makes `blen 0 - 1 = 0`, so all four exponent cases collapse to one term. -/
private def adj : Expr :=
  .add (.ite (.lit 32) esz (.mul (.lit 8) (.sub esz (.lit 32))) (.lit 0))
       (.sub (.bits ehd) (.lit 1))

private def sq : Expr := .mul maxlen maxlen

/-- mult_complexity (EIP-198 3-piece curve). -/
private def mc198 : Expr :=
  .ite maxlen (.lit 65) sq
    (.ite maxlen (.lit 1025)
      (.add (.fdiv sq (.lit 4))  (.sub (.mul (.lit 96)  maxlen) (.lit 3072)))
      (.add (.fdiv sq (.lit 16)) (.sub (.mul (.lit 480) maxlen) (.lit 199680))))

private def eip198 : Expr := .fdiv (.mul mc198 (.emax adj (.lit 1))) (.lit 20)

private def words : Expr := .fdiv (.add maxlen (.lit 7)) (.lit 8)   -- ⌈maxlen/8⌉

private def eip2565 : Expr :=
  .emax (.lit 200) (.fdiv (.mul (.mul words words) (.emax adj (.lit 1))) (.lit 3))

/-- EIP-7883 (Osaka, fork ord 18+): adjusted exponent length counts 16 (not 8) per byte
    beyond 32; multiplication complexity is a flat 16 for operands ≤ 32 bytes and
    2·⌈maxlen/8⌉² above; the ÷3 (GQUADDIVISOR) is gone and the floor is 500.
    Pinned against Arc mainnet block 6 886 879 (13 calls, Σ 51 232, see examples). -/
private def adj7883 : Expr :=
  .add (.ite (.lit 32) esz (.mul (.lit 16) (.sub esz (.lit 32))) (.lit 0))
       (.sub (.bits ehd) (.lit 1))

private def mc7883 : Expr :=
  .ite maxlen (.lit 33) (.lit 16) (.mul (.lit 2) (.mul words words))

private def eip7883 : Expr :=
  .emax (.lit 500) (.mul mc7883 (.emax adj7883 (.lit 1)))

/-- The full fork-aware MODEXP gas: pre-Berlin (fork < 10) → EIP-198, Berlin..Prague
    → EIP-2565, Osaka+ (fork ≥ 18) → EIP-7883. -/
def modexpGas : Expr := .ite fork (.lit 10) eip198 (.ite fork (.lit 18) eip2565 eip7883)

-- EIP-7883 vectors from Arc block 6 886 879 (32/32/32-byte operands): exponent head of
-- 254 bits → 16·253 = 4048; 226 bits → 3600. Same inputs on Prague still price at 1349/1200.
example : modexpGas.eval (mkEnv [("base-sz",32),("exp-sz",32),("mod-sz",32),("exp-head",2^253),("fork-ord",18)]) = 4048 := by native_decide
example : modexpGas.eval (mkEnv [("base-sz",32),("exp-sz",32),("mod-sz",32),("exp-head",2^225),("fork-ord",18)]) = 3600 := by native_decide
example : modexpGas.eval (mkEnv [("base-sz",32),("exp-sz",32),("mod-sz",32),("exp-head",2^253),("fork-ord",17)]) = 1349 := by native_decide
-- the 500 floor and the >32-byte curve: 64-byte operands, 1-bit exponent → 2·64·1 = 128 → 500
example : modexpGas.eval (mkEnv [("base-sz",64),("exp-sz",1),("mod-sz",64),("exp-head",1),("fork-ord",18)]) = 500 := by native_decide

/-! ## Data-word precompiles (cost = base + perWord·⌈len/32⌉), fork-constant -/

private def dlen : Expr := .var "len"
private def words32 : Expr := .fdiv (.add dlen (.lit 31)) (.lit 32)   -- ⌈len/32⌉

/-- SHA256 (0x02): 60 + 12·⌈len/32⌉. -/
def sha256Gas    : Expr := .add (.lit 60)  (.mul (.lit 12)  words32)
/-- RIPEMD160 (0x03): 600 + 120·⌈len/32⌉. -/
def ripemd160Gas : Expr := .add (.lit 600) (.mul (.lit 120) words32)
/-- IDENTITY (0x04): 15 + 3·⌈len/32⌉. -/
def identityGas  : Expr := .add (.lit 15)  (.mul (.lit 3)   words32)
/-- ECRECOVER (0x01): flat 3000. -/
def ecrecoverGas : Expr := .lit 3000
/-- EIP-7951 P256VERIFY (0x100), Osaka+: `PRECOMPILE_P256VERIFY = 6900` (forks/osaka/vm/gas.py);
    the step relation is Evm.Osaka.Spec.P256VerifyStep. -/
def p256verifyGas : Expr := .lit 6900
/-- RIP-7212 P256VERIFY (0x100) on OP-Stack Fjord..Isthmus: 3450 — the spec's
    `Evm.Optimism.Fjord.Spec.rip7212Gas` (`p256VerifyGas f` before Azul). -/
def rip7212Gas : Expr := .lit Evm.Optimism.Fjord.Spec.rip7212Gas
example : rip7212Gas.eval (mkEnv []) = Evm.Optimism.Fjord.Spec.p256VerifyGas .isthmus := by native_decide
/-- EIP-4844 point evaluation (0x0a), Cancun+: `PRECOMPILE_POINT_EVALUATION = 50000`
    (forks/cancun/vm/gas.py; charged at point_evaluation.py:54); the step relation is
    Evm.Cancun.Spec.KzgStep, whose constant this is. -/
def pointEvaluationGas : Expr := .lit Evm.Cancun.Spec.pointEvaluationGas
example : pointEvaluationGas.eval (mkEnv []) = 50000 := by native_decide
/-- EIP-7702 (Prague+): intrinsic charge per authorization tuple and the refund for an
    authority that already existed — Evm.Prague.Spec.SetCodeStep.{authIntrinsicPerAuth,
    authRefundPerExistingAuthority} (25000 / 25000 − 12500). -/
def authIntrinsicPerAuth : Expr := .lit 25000
def authRefundExisting : Expr := .lit 12500

/-! ## bn256 (EIP-196/197 Byzantium; repriced by EIP-1108 at Istanbul, ord 8) -/

/-- bn256 ECADD (0x06): 500 pre-Istanbul, 150 Istanbul+. -/
def bn256AddGas : Expr := .ite fork (.lit 8) (.lit 500)   (.lit 150)
/-- bn256 ECMUL (0x07): 40000 pre-Istanbul, 6000 Istanbul+. -/
def bn256MulGas : Expr := .ite fork (.lit 8) (.lit 40000) (.lit 6000)
/-- bn256 ECPAIRING (0x08): (100000 + 80000·k) pre-Istanbul, (45000 + 34000·k) Istanbul+,
    where k = ⌊len/192⌋ pairs. -/
def bn256PairingGas : Expr :=
  let k : Expr := .fdiv dlen (.lit 192)
  .ite fork (.lit 8)
    (.add (.lit 100000) (.mul (.lit 80000) k))
    (.add (.lit 45000)  (.mul (.lit 34000) k))

/-- Refinement vectors for the data-word + bn256 precompiles (published gas costs). -/
example : sha256Gas.eval    (mkEnv [("len",0)])  = 60   := by native_decide
example : sha256Gas.eval    (mkEnv [("len",33)]) = 84   := by native_decide
example : ripemd160Gas.eval (mkEnv [("len",32)]) = 720  := by native_decide
example : identityGas.eval  (mkEnv [("len",64)]) = 21   := by native_decide
example : bn256AddGas.eval (mkEnv [("fork-ord",5)]) = 500   := by native_decide
example : bn256AddGas.eval (mkEnv [("fork-ord",8)]) = 150   := by native_decide
example : bn256MulGas.eval (mkEnv [("fork-ord",5)]) = 40000 := by native_decide
example : bn256MulGas.eval (mkEnv [("fork-ord",8)]) = 6000  := by native_decide
example : bn256PairingGas.eval (mkEnv [("fork-ord",5),("len",192)]) = 180000 := by native_decide
example : bn256PairingGas.eval (mkEnv [("fork-ord",8),("len",384)]) = 113000 := by native_decide

/-! ## EIP-2537 BLS12-381 (0x0b..0x11), Prague+

Every number here was MEASURED from the canonical client, not transcribed: a probe
contract deployed by state override calls the precompile and `debug_traceCall`
reports the inner frame's `gasUsed`, which is the precompile cost with no
transaction intrinsic mixed in (`scripts/gen-bls-gas-table.py`, recorded in
`lean/c/testdata/bls12381-gas.json`). The MSM discount tables are 128 entries plus
a plateau, and reciting them from memory is how a silent gas bug gets written. -/

/-- G1ADD (0x0b). -/
def blsG1AddGas : Expr := .lit 375
/-- G2ADD (0x0d). -/
def blsG2AddGas : Expr := .lit 600
/-- MAP_FP_TO_G1 (0x10). -/
def blsMapFpToG1Gas : Expr := .lit 5500
/-- MAP_FP2_TO_G2 (0x11). -/
def blsMapFp2ToG2Gas : Expr := .lit 23800
/-- PAIRING_CHECK (0x0f): 37700 + 32600·k over k = ⌊len/384⌋ pairs. -/
def blsPairingGas : Expr :=
  .add (.lit 37700) (.mul (.lit 32600) (.fdiv (.var "len") (.lit 384)))

/-- MSM multiplication bases: one pair costs the base exactly (discount 1000). -/
def blsG1MsmBase : Nat := 12000
def blsG2MsmBase : Nat := 22500

/-- Per-k discounts in thousandths, k = 1..128; beyond 128 the discount is constant. -/
def blsG1MsmDiscounts : List Nat :=
  [ 1000, 949, 848, 797, 764, 750, 738, 728, 719, 712, 705, 698, 692, 687, 682, 677,
    673, 669, 665, 661, 658, 654, 651, 648, 645, 642, 640, 637, 635, 632, 630, 627,
    625, 623, 621, 619, 617, 615, 613, 611, 609, 608, 606, 604, 603, 601, 599, 598,
    596, 595, 593, 592, 591, 589, 588, 586, 585, 584, 582, 581, 580, 579, 577, 576,
    575, 574, 573, 572, 570, 569, 568, 567, 566, 565, 564, 563, 562, 561, 560, 559,
    558, 557, 556, 555, 554, 553, 552, 551, 550, 549, 548, 547, 547, 546, 545, 544,
    543, 542, 541, 540, 540, 539, 538, 537, 536, 536, 535, 534, 533, 532, 532, 531,
    530, 529, 528, 528, 527, 526, 525, 525, 524, 523, 522, 522, 521, 520, 520, 519 ]
def blsG2MsmDiscounts : List Nat :=
  [ 1000, 1000, 923, 884, 855, 832, 812, 796, 782, 770, 759, 749, 740, 732, 724, 717,
    711, 704, 699, 693, 688, 683, 679, 674, 670, 666, 663, 659, 655, 652, 649, 646,
    643, 640, 637, 634, 632, 629, 627, 624, 622, 620, 618, 615, 613, 611, 609, 607,
    606, 604, 602, 600, 598, 597, 595, 593, 592, 590, 589, 587, 586, 584, 583, 582,
    580, 579, 578, 576, 575, 574, 573, 571, 570, 569, 568, 567, 566, 565, 563, 562,
    561, 560, 559, 558, 557, 556, 555, 554, 553, 552, 552, 551, 550, 549, 548, 547,
    546, 545, 545, 544, 543, 542, 541, 541, 540, 539, 538, 537, 537, 536, 535, 535,
    534, 533, 532, 532, 531, 530, 530, 529, 528, 528, 527, 526, 526, 525, 524, 524 ]
def blsG1MsmMaxDiscount : Nat := 519
def blsG2MsmMaxDiscount : Nat := 524

/-- `gas = k · base · discount(k) / 1000`, FLOOR division — which is why the discount
    cannot be read back out of a measured cost by exact division. k = 0 costs 0 and
    then fails in the operation itself (an empty MSM input is invalid). -/
def msmGas (base : Nat) (discounts : List Nat) (maxDiscount k : Nat) : Nat :=
  if k = 0 then 0 else k * base * (discounts.getD (k - 1) maxDiscount) / 1000

def blsG1MsmGas (len : Nat) : Nat := msmGas blsG1MsmBase blsG1MsmDiscounts blsG1MsmMaxDiscount (len / 160)
def blsG2MsmGas (len : Nat) : Nat := msmGas blsG2MsmBase blsG2MsmDiscounts blsG2MsmMaxDiscount (len / 288)

/-- Vectors pinned to the measured canonical costs, including the two ends of each
    discount table and the plateau past 128 pairs. -/
example : blsG1AddGas.eval (mkEnv []) = 375 := by native_decide
example : blsG2AddGas.eval (mkEnv []) = 600 := by native_decide
example : blsMapFpToG1Gas.eval (mkEnv []) = 5500 := by native_decide
example : blsMapFp2ToG2Gas.eval (mkEnv []) = 23800 := by native_decide
example : blsPairingGas.eval (mkEnv [("len", 384)]) = 70300 := by native_decide
example : blsPairingGas.eval (mkEnv [("len", 768)]) = 102900 := by native_decide
example : blsPairingGas.eval (mkEnv [("len", 1536)]) = 168100 := by native_decide
example : blsG1MsmDiscounts.length = 128 := by native_decide
example : blsG2MsmDiscounts.length = 128 := by native_decide
example : blsG1MsmGas 160 = 12000 := by native_decide
example : blsG1MsmGas 320 = 22776 := by native_decide
example : blsG1MsmGas 480 = 30528 := by native_decide
example : blsG1MsmGas (160 * 128) = 797184 := by native_decide
example : blsG1MsmGas (160 * 130) = 809640 := by native_decide
example : blsG2MsmGas 288 = 22500 := by native_decide
example : blsG2MsmGas 576 = 45000 := by native_decide
example : blsG2MsmGas 864 = 62302 := by native_decide
example : blsG2MsmGas (288 * 128) = 1509120 := by native_decide
example : blsG2MsmGas (288 * 130) = 1532700 := by native_decide

/-! ## Transaction intrinsic gas

Seam provides the byte counts and access-list sizes; this is the cost formula.
Inputs: `is-create` (0/1), `data-len`, `zero-bytes`, `nonzero-bytes`, `al-addrs`,
`al-keys`, `fork-ord`. -/

def intrinsicGas : Expr :=
  let isCreate : Expr := .var "is-create"
  let dataLen  : Expr := .var "data-len"
  -- +32000 CREATE base (Homestead+, fork≥1) and EIP-3860 2·⌈initcode/32⌉ (Shanghai+, fork≥15)
  let createTerm : Expr :=
    .ite (.lit 0) isCreate
      (.add (.ite fork (.lit 1) (.lit 0) (.lit 32000))
            (.ite fork (.lit 15) (.lit 0)
                  (.mul (.lit 2) (.fdiv (.add dataLen (.lit 31)) (.lit 32)))))
      (.lit 0)
  let zeroTerm    : Expr := .mul (.var "zero-bytes") (.lit 4)
  -- nonzero calldata byte: 68 pre-Istanbul, 16 (EIP-2028) Istanbul+
  let nonzeroTerm : Expr := .mul (.var "nonzero-bytes") (.ite fork (.lit 8) (.lit 68) (.lit 16))
  -- EIP-2930 access list (Berlin+; 0 on pre-Berlin txs since the seam passes 0)
  let alTerm      : Expr := .add (.mul (.var "al-addrs") (.lit 2400))
                                 (.mul (.var "al-keys")  (.lit 1900))
  .add (.add (.add (.lit 21000) createTerm) (.add zeroTerm nonzeroTerm)) alTerm

/-- Intrinsic-gas refinement vectors. -/
example : intrinsicGas.eval (mkEnv [("is-create",0),("fork-ord",5)]) = 21000 := by native_decide
example : intrinsicGas.eval (mkEnv [("is-create",1),("fork-ord",5)]) = 53000 := by native_decide  -- CREATE
example : intrinsicGas.eval (mkEnv [("is-create",1),("fork-ord",0)]) = 21000 := by native_decide  -- Frontier CREATE: no +32000
example : intrinsicGas.eval (mkEnv [("nonzero-bytes",1),("fork-ord",5)]) = 21068 := by native_decide
example : intrinsicGas.eval (mkEnv [("nonzero-bytes",1),("fork-ord",8)]) = 21016 := by native_decide  -- EIP-2028
example : intrinsicGas.eval (mkEnv [("zero-bytes",10),("fork-ord",8)]) = 21040 := by native_decide
example : intrinsicGas.eval (mkEnv [("al-addrs",1),("al-keys",2),("fork-ord",10)]) = 27200 := by native_decide

/-! ## CREATE / code-deposit / refunds / rewards / EIP-150 retention -/

/-- Code-deposit cost: 200 gas per deployed byte (all forks). -/
def codeDepositGas : Expr := .mul (.lit 200) (.var "nbytes")

/-- CREATE base gas: 32000 + EIP-3860 2·⌈initcode/32⌉ (Shanghai+) + CREATE2 keccak
    6·⌈initcode/32⌉ (`is-create2` 0/1). -/
def createGas : Expr :=
  let w : Expr := .fdiv (.add (.var "initcode-len") (.lit 31)) (.lit 32)
  .add (.add (.lit 32000)
             (.ite fork (.lit 15) (.lit 0) (.mul (.lit 2) w)))         -- EIP-3860 initcode word
       (.ite (.lit 0) (.var "is-create2") (.mul (.lit 6) w) (.lit 0))  -- CREATE2 keccak word

/-- EIP-3860 (Shanghai+, fork ≥ 15): CREATE/CREATE2 init code longer than
    `2 · MAX_CODE_SIZE = 49152` bytes is an exceptional halt of the CALLER — EELS
    cancun/vm/instructions/system.py `generic_create`: `if len(call_data) >
    MAX_INIT_CODE_SIZE: raise OutOfGasError` (after `charge_gas`, so the frame's whole
    gas is gone either way). 1 = oversize, 0 = within the cap or pre-Shanghai (no cap:
    randomStatetest646's 81914-byte init code is legal at Paris). The host (cb-create)
    reports a charge above the frame's gas so the native `subs; b.lo _eita_oog` faults;
    the decision itself is this term. `Evm.CL.GasEmitShanghai.createInitcodeOversize_eq_cap`
    proves it equal to the fork-typed spec predicate `Evm.Shanghai.Spec.initcodeWithinCapAt`. -/
def createInitcodeOversize : Expr :=
  .ite fork (.lit 15) (.lit 0)
       (.ite (.lit 49152) (.var "initcode-len") (.lit 1) (.lit 0))

/-- SELFDESTRUCT refund: 24000 pre-London, 0 London+ (EIP-3529). -/
def selfdestructRefund : Expr := .ite fork (.lit 11) (.lit 24000) (.lit 0)

/-- Refund cap = ⌊gas_used / divisor⌋, divisor 2 pre-London, 5 London+ (EIP-3529). -/
def refundCap : Expr := .fdiv (.var "gas-used") (.ite fork (.lit 11) (.lit 2) (.lit 5))

/-- EIP-150 63/64 retention: forwarded gas = gas (pre-TangerineWhistle, fork<3) else
    gas − ⌊gas/64⌋. Same quantity CALL derives — used to kill the CREATE asymmetry. -/
def retain63of64 : Expr :=
  .ite fork (.lit 3) (.var "gas") (.sub (.var "gas") (.fdiv (.var "gas") (.lit 64)))

/-- New-account fee (CALL/SELFDESTRUCT to a dead account): 25000, all forks. -/
def newAccountFee : Expr := .lit 25000

/-- Block base reward: 5 ETH (Frontier..Spurious), 3 ETH (Byzantium, EIP-649),
    2 ETH (Constantinople..Gray Glacier, EIP-1234), none from Paris (EIP-3675; fork 14).
    Evm.CL.GasEmitParis proves it equal to the Paris spec's `rewardAt` for every fork. -/
def blockBaseReward : Expr :=
  .ite fork (.lit 5) (.lit 5000000000000000000)
    (.ite fork (.lit 6) (.lit 3000000000000000000)
      (.ite fork (.lit 14) (.lit 2000000000000000000) (.lit 0)))

/-- Uncle inclusion bonus to the miner, per uncle = base_reward / 32. -/
def uncleInclusionBonus : Expr := .fdiv blockBaseReward (.lit 32)

/-- Uncle author reward = base_reward · (8 + uncle_number − block_number) / 8. -/
def uncleReward : Expr :=
  .fdiv (.mul blockBaseReward
              (.sub (.add (.lit 8) (.var "uncle-num")) (.var "block-num")))
        (.lit 8)

/-- EIP-1559 (London+) effective gas price the sender pays:
    `min(max_fee, base_fee + max_priority)`. Only reached on London+ (the call
    site is fork-gated), so no fork argument. -/
def effectiveGasPrice : Expr :=
  .emin (.var "max-fee") (.add (.var "base-fee") (.var "max-prio"))

/-- EIP-1559 coinbase priority fee (the tip), capped to what's left above
    base fee: `max(0, min(max_priority, gas_price - base_fee))`. `gas-price` is
    the effective price from `effectiveGasPrice`. -/
def priorityFee : Expr :=
  .emax (.lit 0) (.emin (.var "max-prio")
                        (.sub (.var "gas-price") (.var "base-fee")))

/-! ## EIP-4844 blob fee market: the schedule (Cancun; EIP-7691 Prague; EIP-7892 BPO1, BPO2)

The schedule entry in force is `Evm.Osaka.Spec.blobParamsAt`, keyed here by the fork
ordinal: Cancun (16) target 3 / max 6 / fraction 3338477; Prague (17) and Osaka (18) 6 / 9 /
5007716 (EIP-7691; Osaka keeps it); BPO1 (19) 10 / 15 / 8346193; BPO2 (20) 14 / 21 / 11684671
(EELS `{cancun,prague,osaka,bpo1,bpo2}/vm/gas.py` `GasCosts`; geth `chainspecs/mainnet.json`
`blobSchedule`). `bySchedule` is the one selector every blob formula reads its entry through.
The host computes the fee ONCE per block (`spec-blob-base-fee`) and writes it to every
frame's EvmState #568 for BLOBBASEFEE, and prices type-3 txs with it (`tx-blob-fee`);
`Evm.CL.GasEmitCancun` proves the terms equal to the fork-typed spec
(`Evm.Osaka.Spec.calculateBlobGasPriceAt`, `calculateExcessBlobGasAt`, `maxBlobGasPerBlockAt`). -/

/-- The schedule entry's field by fork: `if fork < 17 then c else if fork < 19 then p else
    if fork < 20 then b1 else b2` (Cancun / Prague+Osaka / BPO1 / BPO2). -/
def bySchedule (c p b1 b2 : Nat) : Expr :=
  .ite fork (.lit 17) (.lit c) (.ite fork (.lit 19) (.lit p) (.ite fork (.lit 20) (.lit b1) (.lit b2)))

/-- `BLOB_BASE_FEE_UPDATE_FRACTION` of the fork's entry. -/
def blobBaseFeeUpdateFraction : Expr := bySchedule 3338477 5007716 8346193 11684671
/-- `BLOB_TARGET_GAS_PER_BLOCK = target · GAS_PER_BLOB (131072)` of the fork's entry. -/
def blobTargetGasPerBlock : Expr := bySchedule 393216 786432 1310720 1835008
/-- `MAX_BLOB_GAS_PER_BLOCK = max · GAS_PER_BLOB` of the fork's entry (osaka/fork.py 103): the
    header gate `blobGasUsed ≤ MAX_BLOB_GAS_PER_BLOCK` (`check_transaction` 469-476). -/
def maxBlobGasPerBlock : Expr := bySchedule 786432 1179648 1966080 2752512
/-- `BLOB_SCHEDULE_MAX` (blobs) and `BLOB_SCHEDULE_MAX − BLOB_SCHEDULE_TARGET`, the EIP-7918
    reserve-branch ratio `blob_gas_used · delta // max`. -/
def blobScheduleMax   : Expr := bySchedule 6 9 15 21
def blobScheduleDelta : Expr := bySchedule 3 3 5 7

/-- `calculate_blob_gas_price(excess) = fake_exponential(MIN_BASE_FEE_PER_BLOB_GAS = 1,
    excess, fraction)`. Inputs: `excess-blob-gas`, `fork-ord`. -/
def blobBaseFee : Expr := .fakeExp (.lit 1) (.var "excess-blob-gas") blobBaseFeeUpdateFraction

/-- EIP-7825 `TX_MAX_GAS_LIMIT = 16_777_216` (osaka/vm/gas.py 109; `validate_transaction`,
    osaka/transactions.py 585-586, rejects `tx.gas` above it). Osaka+ only: the host gates it
    by fork, as the other Osaka tx-shape checks. -/
def txMaxGasLimit : Expr := .lit 16777216

-- excess 0 ⇒ the 1-wei floor; one fraction of excess ⇒ ⌊e⌋ = 2 at Cancun, 1 at Prague
-- (the series is ⌊e^(excess/fraction)⌋ and 3338477/5007716 < 1); ten fractions ⇒ ⌊e^10⌋.
example : blobBaseFee.eval (mkEnv [("excess-blob-gas",0),("fork-ord",16)]) = 1 := by native_decide
example : blobBaseFee.eval (mkEnv [("excess-blob-gas",3338477),("fork-ord",16)]) = 2 := by native_decide
example : blobBaseFee.eval (mkEnv [("excess-blob-gas",3338477),("fork-ord",17)]) = 1 := by native_decide
example : blobBaseFee.eval (mkEnv [("excess-blob-gas",33384770),("fork-ord",16)]) = 22026 := by native_decide
example : blobBaseFee.eval (mkEnv [("excess-blob-gas",33384770),("fork-ord",17)]) = 785 := by native_decide
-- 50 blocks at Cancun's 6-blob cap (excess 786432·50): 130392 wei/gas; the same excess at
-- Prague's slower curve: 2571. Mainnet-sized excess (10^8): 10203769476395 / 470442149.
example : blobBaseFee.eval (mkEnv [("excess-blob-gas",39321600),("fork-ord",16)]) = 130392 := by native_decide
example : blobBaseFee.eval (mkEnv [("excess-blob-gas",39321600),("fork-ord",17)]) = 2571 := by native_decide
example : blobBaseFee.eval (mkEnv [("excess-blob-gas",100000000),("fork-ord",16)]) = 10203769476395 := by native_decide
example : blobBaseFee.eval (mkEnv [("excess-blob-gas",100000000),("fork-ord",18)]) = 470442149 := by native_decide
-- one BPO2 fraction of excess on each curve: ⌊e^3.5⌋ = 33, ⌊e^2.33⌋ = 10, ⌊e^1.4⌋ = 4, ⌊e⌋ = 2
example : blobBaseFee.eval (mkEnv [("excess-blob-gas",11684671),("fork-ord",16)]) = 33 := by native_decide
example : blobBaseFee.eval (mkEnv [("excess-blob-gas",11684671),("fork-ord",18)]) = 10 := by native_decide
example : blobBaseFee.eval (mkEnv [("excess-blob-gas",11684671),("fork-ord",19)]) = 4 := by native_decide
example : blobBaseFee.eval (mkEnv [("excess-blob-gas",11684671),("fork-ord",20)]) = 2 := by native_decide
example : maxBlobGasPerBlock.eval (mkEnv [("fork-ord",16)]) = 786432 := by native_decide
example : maxBlobGasPerBlock.eval (mkEnv [("fork-ord",20)]) = 2752512 := by native_decide

/-! ## Header continuity: the base fee and the excess blob gas a block must carry

EELS validates two header fields against the PARENT header: `baseFeePerGas` (london/fork.py
`calculate_base_fee_per_gas`, EIP-1559: the gas target is `parent_gas_limit // 2`, the fee
moves by at most 1/8 per block, up-steps by at least 1 wei; `INITIAL_BASE_FEE = 10^9` on
the fork block) and `excessBlobGas` (cancun/vm/gas.py `calculate_excess_blob_gas`,
EIP-4844: `max(0, parent_excess + parent_blob_gas_used − TARGET)`, the target being the
fork's schedule entry's, and from Osaka EIP-7918's reserve-price clause — osaka/vm/gas.py
`calculate_excess_blob_gas` 398-441). Our headers are hash-checked canonical input, so these
gates catch a wrong formula (or an unmodelled fork rule) at the block where it starts, not a
corrupt header. Both are clauses of the header gate's term (`Evm.CL.HeaderEmit`, EELS
`validate_header`). `Evm.CL.GasEmitLondon` proves `nextBaseFee` equal to
`Evm.London.Spec.calculateBaseFeePerGas`; `Evm.CL.GasEmitCancun` proves `nextExcessBlobGas`
equal to `Evm.Osaka.Spec.calculateExcessBlobGasAt` for every fork. -/

def parentGasUsed   : Expr := .var "parent-gas-used"
/-- `parent_gas_limit // ELASTICITY_MULTIPLIER (2)`. -/
def parentGasTarget : Expr := .fdiv (.var "parent-gas-limit") (.lit 2)
def parentBaseFee   : Expr := .var "parent-base-fee"

/-- EIP-1559 `calculate_base_fee_per_gas` from the parent's gas used, gas limit and base
    fee (`ite lo hi t e` is `lo < hi`): below target the fee falls by
    `base·(target−used)/target/8`, above it rises by `max(base·(used−target)/target/8, 1)`,
    at target it is unchanged. The divisions chain left to right, as EELS's do. -/
def nextBaseFee : Expr :=
  .ite parentGasUsed parentGasTarget
    (.sub parentBaseFee
          (.fdiv (.fdiv (.mul parentBaseFee (.sub parentGasTarget parentGasUsed)) parentGasTarget) (.lit 8)))
    (.ite parentGasTarget parentGasUsed
      (.add parentBaseFee
            (.emax (.fdiv (.fdiv (.mul parentBaseFee (.sub parentGasUsed parentGasTarget)) parentGasTarget) (.lit 8))
                   (.lit 1)))
      parentBaseFee)

/-- `INITIAL_BASE_FEE = 10^9`: the base fee of the London fork block (its parent has none). -/
def initialBaseFee : Expr := .lit 1000000000

def parentExcessBlobGas : Expr := .var "parent-excess-blob-gas"
def parentBlobGasUsed   : Expr := .var "parent-blob-gas-used"
/-- `parent_blob_gas = excess_blob_gas + blob_gas_used` of the parent. -/
def parentBlobGas : Expr := .add parentExcessBlobGas parentBlobGasUsed

/-- EIP-4844 `calculate_excess_blob_gas` (osaka/vm/gas.py 398-441), the fork's schedule
    entry throughout: below the target the excess resets to 0; from Osaka (fork 18), when
    `BLOB_BASE_COST (8192) · parent_base_fee > GAS_PER_BLOB (131072) · blob_gas_price(parent
    excess)` (EIP-7918: the execution-cost reserve price is binding), the excess becomes
    `parent_excess + parent_used · (max − target) // max`; otherwise `parent_blob_gas −
    target`. Inputs: `parent-excess-blob-gas`, `parent-blob-gas-used`, `parent-base-fee` (all
    0 for a parent without the field), `fork-ord`. -/
def nextExcessBlobGas : Expr :=
  .ite parentBlobGas blobTargetGasPerBlock (.lit 0)
    (.ite fork (.lit 18)
      (.sub parentBlobGas blobTargetGasPerBlock)
      (.ite (.mul (.lit 131072) (.fakeExp (.lit 1) parentExcessBlobGas blobBaseFeeUpdateFraction))
            (.mul (.lit 8192) parentBaseFee)
            (.add parentExcessBlobGas (.fdiv (.mul parentBlobGasUsed blobScheduleDelta) blobScheduleMax))
            (.sub parentBlobGas blobTargetGasPerBlock)))

-- at target: unchanged; a full block: +1/8; an empty block: −1/8; one gas over target at a
-- tiny fee: the 1-wei floor (7·1/15M/8 rounds to 0); one over at 10^9: +8 (1e9/15e6/8).
example : nextBaseFee.eval (mkEnv [("parent-gas-used",15000000),("parent-gas-limit",30000000),("parent-base-fee",1000000000)]) = 1000000000 := by native_decide
example : nextBaseFee.eval (mkEnv [("parent-gas-used",30000000),("parent-gas-limit",30000000),("parent-base-fee",1000000000)]) = 1125000000 := by native_decide
example : nextBaseFee.eval (mkEnv [("parent-gas-used",0),("parent-gas-limit",30000000),("parent-base-fee",1000000000)]) = 875000000 := by native_decide
example : nextBaseFee.eval (mkEnv [("parent-gas-used",15000001),("parent-gas-limit",30000000),("parent-base-fee",7)]) = 8 := by native_decide
example : nextBaseFee.eval (mkEnv [("parent-gas-used",15000001),("parent-gas-limit",30000000),("parent-base-fee",1000000000)]) = 1000000008 := by native_decide
-- the ethereum/tests London chains: genesis 10^9 at gas used 0 ⇒ block 1 carries 875000000
example : initialBaseFee.eval (mkEnv []) = 1000000000 := by native_decide
-- six blobs on an empty excess: Cancun (target 3) leaves 3 blobs' gas, Prague (target 6) none
example : nextExcessBlobGas.eval (mkEnv [("parent-excess-blob-gas",0),("parent-blob-gas-used",786432),("fork-ord",16)]) = 393216 := by native_decide
example : nextExcessBlobGas.eval (mkEnv [("parent-excess-blob-gas",0),("parent-blob-gas-used",786432),("fork-ord",17)]) = 0 := by native_decide
example : nextExcessBlobGas.eval (mkEnv [("parent-excess-blob-gas",100),("parent-blob-gas-used",0),("fork-ord",16)]) = 0 := by native_decide
example : nextExcessBlobGas.eval (mkEnv [("parent-excess-blob-gas",1000000),("parent-blob-gas-used",393216),("fork-ord",16)]) = 1000000 := by native_decide
-- EIP-7918 at Osaka: a parent at target (6 blobs, excess 0 ⇒ 1-wei blob price) with a 1-gwei
-- base fee: 8192·10^9 > 131072 ⇒ the excess grows by 786432·3/9 = 262144 instead of staying
-- 0; at a 16-wei base fee 8192·16 = 131072 is not greater ⇒ 0. Prague ignores the base fee.
example : nextExcessBlobGas.eval (mkEnv [("parent-excess-blob-gas",0),("parent-blob-gas-used",786432),("parent-base-fee",1000000000),("fork-ord",18)]) = 262144 := by native_decide
example : nextExcessBlobGas.eval (mkEnv [("parent-excess-blob-gas",0),("parent-blob-gas-used",786432),("parent-base-fee",16),("fork-ord",18)]) = 0 := by native_decide
example : nextExcessBlobGas.eval (mkEnv [("parent-excess-blob-gas",0),("parent-blob-gas-used",786432),("parent-base-fee",1000000000),("fork-ord",17)]) = 0 := by native_decide
-- BPO2: a full 21-blob parent on an empty excess: 2752512 − 1835008 = 917504 at a 1-wei base
-- fee, and 0 + 2752512·7/21 = 917504 by the reserve clause at 1 gwei (max − target = max/3).
example : nextExcessBlobGas.eval (mkEnv [("parent-excess-blob-gas",0),("parent-blob-gas-used",2752512),("parent-base-fee",1),("fork-ord",20)]) = 917504 := by native_decide
example : nextExcessBlobGas.eval (mkEnv [("parent-excess-blob-gas",0),("parent-blob-gas-used",2752512),("parent-base-fee",1000000000),("fork-ord",20)]) = 917504 := by native_decide
-- BPO1, 15 blobs under a reserve-priced market with excess already 10^7: 10^7 + 1966080·5/15
example : nextExcessBlobGas.eval (mkEnv [("parent-excess-blob-gas",10000000),("parent-blob-gas-used",1966080),("parent-base-fee",1000000000),("fork-ord",19)]) = 10655360 := by native_decide

/-- Refinement vectors for the CREATE/refund/reward family. -/
example : codeDepositGas.eval   (mkEnv [("nbytes",100)]) = 20000 := by native_decide
-- EIP-1559: capped by max-fee; tip = priority within the base-fee headroom.
example : effectiveGasPrice.eval (mkEnv [("max-fee",100),("base-fee",30),("max-prio",5)])  = 35  := by native_decide -- base+prio < cap
example : effectiveGasPrice.eval (mkEnv [("max-fee",40), ("base-fee",30),("max-prio",50)]) = 40  := by native_decide -- capped at max-fee
example : priorityFee.eval      (mkEnv [("gas-price",35),("base-fee",30),("max-prio",5)])  = 5   := by native_decide -- full priority fits
example : priorityFee.eval      (mkEnv [("gas-price",40),("base-fee",30),("max-prio",50)]) = 10  := by native_decide -- capped by headroom (40-30)
example : createGas.eval        (mkEnv [("fork-ord",5),("is-create2",0)]) = 32000 := by native_decide
example : createGas.eval        (mkEnv [("fork-ord",16),("is-create2",1),("initcode-len",64)]) = 32016 := by native_decide -- +2·2(3860) +6·2(kec)=32000+4+12
-- EIP-3860 cap: one past the cap fails from Shanghai; the cap itself passes; no cap before.
example : createInitcodeOversize.eval (mkEnv [("fork-ord",15),("initcode-len",49153)]) = 1 := by native_decide
example : createInitcodeOversize.eval (mkEnv [("fork-ord",15),("initcode-len",49152)]) = 0 := by native_decide
example : createInitcodeOversize.eval (mkEnv [("fork-ord",16),("initcode-len",50000)]) = 1 := by native_decide -- randomStatetest307
example : createInitcodeOversize.eval (mkEnv [("fork-ord",14),("initcode-len",81914)]) = 0 := by native_decide -- Paris: legal
example : selfdestructRefund.eval (mkEnv [("fork-ord",5)])  = 24000 := by native_decide
example : selfdestructRefund.eval (mkEnv [("fork-ord",11)]) = 0     := by native_decide
example : refundCap.eval (mkEnv [("gas-used",100000),("fork-ord",5)])  = 50000 := by native_decide
example : refundCap.eval (mkEnv [("gas-used",100000),("fork-ord",11)]) = 20000 := by native_decide

/-! ## Account-access surcharges charged by the CL callbacks (EIP-2929 / EIP-7702) -/

/-- SELFDESTRUCT cold beneficiary (EELS berlin+/vm/instructions/system.py selfdestruct:
    `if beneficiary not in accessed_addresses: gas_cost += GAS_COLD_ACCOUNT_ACCESS`);
    a warm beneficiary adds nothing. Input `cold` (0/1). -/
def selfdestructColdGas : Expr := .ite (.lit 0) (.var "cold") (.lit 2600) (.lit 0)

/-- EIP-7702 delegate access (EELS prague/vm/eoa_delegation.py access_delegation:
    GAS_COLD_ACCOUNT_ACCESS if the delegate is cold, else GAS_WARM_ACCESS). -/
def delegateAccessGas : Expr := .ite (.lit 0) (.var "cold") (.lit 2600) (.lit 100)

example : selfdestructColdGas.eval (mkEnv [("cold",1)]) = 2600 := by native_decide
example : selfdestructColdGas.eval (mkEnv [("cold",0)]) = 0 := by native_decide
example : delegateAccessGas.eval (mkEnv [("cold",1)]) = 2600 := by native_decide
example : delegateAccessGas.eval (mkEnv [("cold",0)]) = 100 := by native_decide

/-! ## Transaction settlement: refund and the EIP-7623 calldata floor

EELS prague/fork.py:913-923. Inputs: `gas-used` (tx.gas − gas_left, intrinsic included),
`refund-counter`, the calldata byte counts, `fork-ord`. Evm.CL.GasEmitPrague proves both
equal the Prague spec (Evm.Prague.Spec.CalldataCost) from Prague on. -/

/-- EIP-7623 calldata floor: `TX_BASE + 10·(zeros + 4·nonzeros)` from Prague (fork 17);
    0 before it, so `max` with it is the identity there. -/
def calldataFloorGas : Expr :=
  .ite fork (.lit 17) (.lit 0)
    (.add (.lit 21000)
          (.mul (.lit 10) (.add (.var "zero-bytes") (.mul (.lit 4) (.var "nonzero-bytes")))))

/-- Gas the tx is charged: `max(used − min(refund, cap), floor)`. -/
def txGasUsed : Expr :=
  .emax (.sub (.var "gas-used") (.emin (.var "refund-counter") refundCap)) calldataFloorGas

example : calldataFloorGas.eval (mkEnv [("zero-bytes",10),("nonzero-bytes",10),("fork-ord",16)]) = 0 := by native_decide
example : calldataFloorGas.eval (mkEnv [("zero-bytes",10),("nonzero-bytes",10),("fork-ord",17)]) = 21500 := by native_decide
-- a calldata-heavy call that executes little: 1000 nonzero bytes, intrinsic 37000, used 40000
example : txGasUsed.eval (mkEnv [("gas-used",40000),("refund-counter",0),("nonzero-bytes",1000),("fork-ord",17)]) = 61000 := by native_decide
-- the same tx before Prague: no floor
example : txGasUsed.eval (mkEnv [("gas-used",40000),("refund-counter",0),("nonzero-bytes",1000),("fork-ord",16)]) = 40000 := by native_decide
-- refund capped at used/5 (London+)
example : txGasUsed.eval (mkEnv [("gas-used",100000),("refund-counter",50000),("fork-ord",17)]) = 80000 := by native_decide
example : txGasUsed.eval (mkEnv [("gas-used",100000),("refund-counter",50000),("fork-ord",5)]) = 50000 := by native_decide
example : retain63of64.eval (mkEnv [("gas",6400),("fork-ord",5)]) = 6300 := by native_decide
example : retain63of64.eval (mkEnv [("gas",6400),("fork-ord",2)]) = 6400 := by native_decide
example : blockBaseReward.eval (mkEnv [("fork-ord",4)]) = 5000000000000000000 := by native_decide
example : blockBaseReward.eval (mkEnv [("fork-ord",5)]) = 3000000000000000000 := by native_decide
example : blockBaseReward.eval (mkEnv [("fork-ord",6)]) = 2000000000000000000 := by native_decide
example : blockBaseReward.eval (mkEnv [("fork-ord",13)]) = 2000000000000000000 := by native_decide
example : blockBaseReward.eval (mkEnv [("fork-ord",14)]) = 0 := by native_decide
example : uncleReward.eval (mkEnv [("fork-ord",14),("uncle-num",98),("block-num",100)]) = 0 := by native_decide
example : uncleReward.eval (mkEnv [("fork-ord",4),("uncle-num",98),("block-num",100)]) = 3750000000000000000 := by native_decide -- 5e18·6/8

/-! ## Refinement vectors — `eval` against the EIPs' OWN published numbers.
    These are checked at build time; the emitted CL is `modexpGas.toCL`, so the
    CL computes the same function the kernel just verified. -/

/-- EIP-198 canonical example: modexp(3, 2²⁵⁶−2³²−978, 2²⁵⁶−2³²−977), all 32 bytes →
    pre-Berlin gas 13056 (mult_complexity 1024 · adj 255 / 20). -/
example : modexpGas.eval (mkEnv
    [("base-sz",32),("exp-sz",32),("mod-sz",32),
     ("exp-head", 2^256 - 2^32 - 978),("fork-ord",5)]) = 13056 := by native_decide

/-- Same input on Berlin+ → EIP-2565 gas 1360 (words² 16 · adj 255 / 3, floored, max 200). -/
example : modexpGas.eval (mkEnv
    [("base-sz",32),("exp-sz",32),("mod-sz",32),
     ("exp-head", 2^256 - 2^32 - 978),("fork-ord",10)]) = 1360 := by native_decide

/-- exp_len > 32: adj = 8·(64−32) + (blen(2²⁵⁵)−1) = 256 + 255 = 511, maxlen 1 →
    EIP-198 gas = ⌊1·511/20⌋ = 25. -/
example : modexpGas.eval (mkEnv
    [("base-sz",1),("exp-sz",64),("mod-sz",1),
     ("exp-head", 2^255),("fork-ord",5)]) = 25 := by native_decide

end Evm.CL.GasEmit
