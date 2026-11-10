import Evm.CL.GasEmit
import Evm.CL.ForkEmit

/-! # Evm.CL.GasEmitC — the gas IR, printed as freestanding C

`Evm.CL.GasEmit.Expr.toCL` prints the gas formulas as Common Lisp, where every
intermediate is a bignum for free. The RISC-V / bare-metal consumers have no
Lisp and no bignum: this module adds a second printer, `Expr.toC`, over the
SAME terms, so a C host computes gas from the Lean-proved formula instead of a
hand-written copy of it (`EmitHostCL`'s whole reason, for the other language).

Two deliberate differences from `toCL`, both loud rather than silent:

* **Width.** `Expr` is over unbounded `Nat`; C gets `uint64_t`. Every `add`,
  `mul`, `pow2` and division is therefore printed as a *checked* helper that
  calls `eita_spec_overflow` (declared `noreturn`) instead of wrapping. A
  consumer that cannot represent a formula's value refuses to act on it; it
  never acts on a wrapped one. Gas is bounded by the block gas limit, so the
  trap is unreachable for consensus-valid input — it guards the inputs a
  *signing* device is handed, which are arbitrary until verified.
* **256-bit leaves.** One input is not a 64-bit quantity: MODEXP's `exp-head`
  (the first ≤32 bytes of the exponent as an integer), which the formula
  consumes only through `bits`. It is typed `u256` and printed as a 4-limb
  pointer; the printer *errors* if such a variable reaches any other operator,
  so a 256-bit value can never be silently truncated to a limb.

`fakeExponential` is the one loop the IR has, and `GasEmit.fakeExponentialCL`
is already a hand-written Common Lisp bridge for it; `fakeExponentialC` is the
same bridge in C, mirroring it line for line (the Lean meaning is
`Evm.Cancun.Spec.fakeExponential`). -/

namespace Evm.CL.GasEmit

/-- The C type an IR variable carries. -/
inductive CTy where
  | u64
  | u256
  deriving DecidableEq, Repr

/-- What a formula's value *is*, which decides whether 64 bits can hold it.

`gas` is bounded by the block gas limit, so a u64 holds every value and every
intermediate. `wei` is not bounded by anything the chain enforces: an ether
reward is ~5·10^18 before it is multiplied by anything, and a transaction's fee
fields are u256 by the RLP. A `wei` formula at 64 bits would trap on its own
arithmetic (`uncle-reward` does, at the first vector), so those wait for the
256-bit printer rather than shipping a formula that is correct only for inputs
nobody checked. -/
inductive Dom where
  | gas
  | wei
  deriving DecidableEq, Repr

/-- IR variable name → C identifier (`base-sz` → `base_sz`). -/
def cname (s : String) : String := s.map (fun c => if c == '-' then '_' else c)

/-- The only 256-bit input in the emitted set: MODEXP's exponent head. -/
def cvarTy (name : String) : CTy := if name == "exp-head" then .u256 else .u64

/-- Free variables of a term, in first-occurrence order. -/
def Expr.varsOf : Expr → List String
  | .lit _         => []
  | .var x         => [x]
  | .add a b | .sub a b | .mul a b | .fdiv a b | .emax a b | .emin a b =>
      a.varsOf ++ b.varsOf
  | .bits a | .pow2 a => a.varsOf
  | .ite lo hi t e => lo.varsOf ++ hi.varsOf ++ t.varsOf ++ e.varsOf
  | .fakeExp f n d => f.varsOf ++ n.varsOf ++ d.varsOf

/-- Order-preserving deduplication. -/
def dedup (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- C code generation — the SAME term as C over `uint64_t`, every step checked. -/
def Expr.toC : Expr → (String → CTy) → Except String String
  | .lit n, _ =>
      if n < 2 ^ 64 then .ok s!"UINT64_C({n})"
      else .error s!"GasEmitC: literal {n} does not fit uint64_t"
  | .var x, ty =>
      match ty x with
      | .u64  => .ok (cname x)
      | .u256 => .error s!"GasEmitC: 256-bit input `{x}` used as a 64-bit operand"
  | .add a b, ty  => do .ok s!"eita_c_add({← a.toC ty}, {← b.toC ty})"
  | .sub a b, ty  => do .ok s!"eita_c_sub({← a.toC ty}, {← b.toC ty})"
  | .mul a b, ty  => do .ok s!"eita_c_mul({← a.toC ty}, {← b.toC ty})"
  | .fdiv a b, ty => do .ok s!"eita_c_fdiv({← a.toC ty}, {← b.toC ty})"
  | .emax a b, ty => do .ok s!"eita_c_max({← a.toC ty}, {← b.toC ty})"
  | .emin a b, ty => do .ok s!"eita_c_min({← a.toC ty}, {← b.toC ty})"
  | .pow2 a, ty   => do .ok s!"eita_c_pow2({← a.toC ty})"
  | .bits a, ty =>
      -- A u256 leaf is legal here and ONLY here: `bits` is its one consumer.
      match a with
      | .var x => match ty x with
                  | .u256 => .ok s!"eita_c_u256_blen({cname x})"
                  | .u64  => .ok s!"eita_c_blen({cname x})"
      | _ => do .ok s!"eita_c_blen({← a.toC ty})"
  | .ite lo hi t e, ty => do
      .ok s!"(({← lo.toC ty} < {← hi.toC ty}) ? {← t.toC ty} : {← e.toC ty})"
  | .fakeExp f n d, ty => do
      .ok s!"eita_c_fake_exponential({← f.toC ty}, {← n.toC ty}, {← d.toC ty})"

/-- An emitted C function: its name, its parameters in order, and the term. -/
structure CDef where
  name : String
  vars : List String
  term : Expr
  doc  : String := ""
  dom  : Dom := .gas

/-- The C parameter list (`u256` inputs arrive as a 4-limb pointer). -/
def paramList (vars : List String) : String :=
  if vars.isEmpty then "void"
  else ", ".intercalate (vars.map fun v =>
    match cvarTy v with
    | .u64  => s!"uint64_t {cname v}"
    | .u256 => s!"const uint64_t *{cname v}")

/-- A declared parameter list that does not match the term's free variables is an
    error, not a stale signature: a formula that gains an input cannot keep its
    old prototype. -/
def CDef.check (d : CDef) : Except String Unit :=
  let found := dedup d.term.varsOf
  let missing := found.filter (fun v => !d.vars.contains v)
  let extra := d.vars.filter (fun v => !found.contains v)
  if missing.isEmpty && extra.isEmpty then .ok ()
  else .error s!"GasEmitC: {d.name} parameters {d.vars} but the term uses {found}"

def CDef.proto (d : CDef) : String :=
  s!"uint64_t eita_spec_{cname d.name}({paramList d.vars})"

def CDef.toC (d : CDef) : Except String String := do
  d.check
  let body ← d.term.toC cvarTy
  .ok ((if d.doc.isEmpty then "" else s!"/* {d.doc} */\n") ++
       s!"{d.proto} \{\n  return {body};\n}\n")

/-! ## The checked arithmetic prelude

Hand-written, and deliberately the smallest thing that can be: each helper is
one line of C whose correspondence to the `Expr` constructor above it is
readable at a glance. `eita_c_sub` is `Nat.sub` (truncated), matching
`toCL`'s `(max 0 (- a b))`. -/

def preludeC : String :=
  "/* The checked arithmetic the printer targets. `eita_spec_overflow` is the\n" ++
  "   consumer's: a replay host may abort, a signing device must refuse to sign. */\n" ++
  "void eita_spec_overflow(const char *where) __attribute__((noreturn));\n" ++
  "\n" ++
  "static inline uint64_t eita_c_add(uint64_t a, uint64_t b) {\n" ++
  "  uint64_t r; if (__builtin_add_overflow(a, b, &r)) eita_spec_overflow(\"add\"); return r;\n}\n" ++
  "static inline uint64_t eita_c_mul(uint64_t a, uint64_t b) {\n" ++
  "  uint64_t r; if (__builtin_mul_overflow(a, b, &r)) eita_spec_overflow(\"mul\"); return r;\n}\n" ++
  "/* Nat.sub: truncated at zero, = toCL's (max 0 (- a b)) */\n" ++
  "static inline uint64_t eita_c_sub(uint64_t a, uint64_t b) { return a > b ? a - b : 0; }\n" ++
  "static inline uint64_t eita_c_fdiv(uint64_t a, uint64_t b) {\n" ++
  "  if (b == 0) eita_spec_overflow(\"div0\");\n  return a / b;\n}\n" ++
  "static inline uint64_t eita_c_max(uint64_t a, uint64_t b) { return a > b ? a : b; }\n" ++
  "static inline uint64_t eita_c_min(uint64_t a, uint64_t b) { return a < b ? a : b; }\n" ++
  "/* = CL integer-length on a non-negative integer: blen 0 = 0, else floor(log2 n)+1 */\n" ++
  "static inline uint64_t eita_c_blen(uint64_t a) {\n" ++
  "  return a == 0 ? 0 : (uint64_t)(64 - __builtin_clzll(a));\n}\n" ++
  "/* The same, for a 256-bit leaf: four limbs, least significant first. */\n" ++
  "static inline uint64_t eita_c_u256_blen(const uint64_t *a) {\n" ++
  "  for (int i = 3; i >= 0; i--)\n" ++
  "    if (a[i]) return (uint64_t)(64 * i) + (uint64_t)(64 - __builtin_clzll(a[i]));\n" ++
  "  return 0;\n}\n" ++
  "static inline uint64_t eita_c_pow2(uint64_t a) {\n" ++
  "  if (a >= 64) eita_spec_overflow(\"pow2\");\n  return UINT64_C(1) << a;\n}\n" ++
  "/* EIP-4844 fake_exponential (EELS cancun/vm/gas.py), the one loop the IR has —\n" ++
  "   line for line the same bridge as GasEmit.fakeExponentialCL. */\n" ++
  "static inline uint64_t eita_c_fake_exponential(uint64_t factor, uint64_t numerator,\n" ++
  "                                               uint64_t denominator) {\n" ++
  "  uint64_t i = 1, output = 0, accum = eita_c_mul(factor, denominator);\n" ++
  "  while (accum > 0) {\n" ++
  "    output = eita_c_add(output, accum);\n" ++
  "    accum = eita_c_fdiv(eita_c_mul(accum, numerator), eita_c_mul(denominator, i));\n" ++
  "    i++;\n" ++
  "  }\n" ++
  "  return eita_c_fdiv(output, denominator);\n}\n"


/-! ## The emitted set

Mirrors `EmitHostCL`'s table for the Ethereum formulas. Stated gaps (CONTRIBUTING
rule 3 — a gap is named, never skipped quietly), all of which the Lisp host still
emits and which no C consumer needs yet:

* `effectiveGasPrice` / `priorityFee` — their inputs are a transaction's
  `maxFeePerGas` / `maxPriorityFeePerGas`, which are *u256 wei*, not gas. They
  need a 256-bit printer, not a 64-bit one with a trap: an arbitrary
  signed-over transaction can legitimately carry a fee field above 2^64.
* `headerViolation` — EELS `validate_header`, 22 parameters. A stateless
  consumer is handed a header it does not itself validate; the replay host does.
* the EIP-2537 BLS MSM discount tables — data, not `Expr`, emitted specially.
* the Arc formulas (`spec-arc-*`) — chain-specific, and some are wei-valued.
-/

open Evm.CL.ForkEmit in
def defs : List CDef :=
  [ { name := "sha256-gas",              vars := ["len"],      term := sha256Gas,
      doc := "SHA2-256 precompile (0x02)" }
  , { name := "ripemd160-gas",           vars := ["len"],      term := ripemd160Gas }
  , { name := "identity-gas",            vars := ["len"],      term := identityGas }
  , { name := "ecrecover-gas",           vars := [],           term := ecrecoverGas }
  , { name := "p256verify-gas",          vars := [],           term := p256verifyGas }
  , { name := "rip7212-gas",             vars := [],           term := rip7212Gas }
  , { name := "point-evaluation-gas",    vars := [],           term := pointEvaluationGas }
  , { name := "auth-intrinsic-per-auth", vars := [],           term := authIntrinsicPerAuth }
  , { name := "auth-refund-existing",    vars := [],           term := authRefundExisting }
  , { name := "bn256-add-gas",           vars := ["fork-ord"], term := bn256AddGas }
  , { name := "bn256-mul-gas",           vars := ["fork-ord"], term := bn256MulGas }
  , { name := "bn256-pairing-gas",       vars := ["len", "fork-ord"], term := bn256PairingGas }
  , { name := "bls-g1add-gas",           vars := [],           term := blsG1AddGas }
  , { name := "bls-g2add-gas",           vars := [],           term := blsG2AddGas }
  , { name := "bls-map-fp-to-g1-gas",    vars := [],           term := blsMapFpToG1Gas }
  , { name := "bls-map-fp2-to-g2-gas",   vars := [],           term := blsMapFp2ToG2Gas }
  , { name := "bls-pairing-gas",         vars := ["len"],      term := blsPairingGas }
  , { name := "intrinsic-gas",
      vars := ["is-create", "data-len", "zero-bytes", "nonzero-bytes",
               "al-addrs", "al-keys", "fork-ord"],
      term := intrinsicGas,
      doc := "EELS calculate_intrinsic_cost (+ EIP-2930 access list, EIP-3860 initcode words)" }
  , { name := "code-deposit-gas",        vars := ["nbytes"],   term := codeDepositGas }
  , { name := "create-gas",              vars := ["fork-ord", "is-create2", "initcode-len"],
      term := createGas }
  , { name := "create-initcode-oversize", vars := ["fork-ord", "initcode-len"],
      term := createInitcodeOversize, doc := "EIP-3860 initcode cap" }
  , { name := "selfdestruct-refund",     vars := ["fork-ord"], term := selfdestructRefund }
  , { name := "calldata-floor-gas",      vars := ["zero-bytes", "nonzero-bytes", "fork-ord"],
      term := calldataFloorGas, doc := "EIP-7623" }
  , { name := "tx-gas-used",
      vars := ["gas-used", "refund-counter", "zero-bytes", "nonzero-bytes", "fork-ord"],
      term := txGasUsed }
  , { name := "selfdestruct-cold-gas",   vars := ["cold"],     term := selfdestructColdGas,
      doc := "EIP-2929" }
  , { name := "delegate-access-gas",     vars := ["cold"],     term := delegateAccessGas,
      doc := "EIP-7702" }
  , { name := "retain-63-64",            vars := ["gas", "fork-ord"], term := retain63of64 }
  , { name := "new-account-fee",         vars := [],           term := newAccountFee }
  , { name := "block-base-reward",       vars := ["fork-ord"], term := blockBaseReward, dom := .wei }
  , { name := "uncle-inclusion-bonus",   vars := ["fork-ord"], term := uncleInclusionBonus, dom := .wei }
  , { name := "uncle-reward",            vars := ["fork-ord", "uncle-num", "block-num"],
      term := uncleReward, dom := .wei }
  , { name := "blob-base-fee",           vars := ["excess-blob-gas", "fork-ord"],
      term := blobBaseFee, doc := "EIP-4844 / 7691 / 7892, by the fork's schedule entry",
      dom := .wei }
  , { name := "max-blob-gas-per-block",  vars := ["fork-ord"], term := maxBlobGasPerBlock }
  , { name := "tx-max-gas-limit",        vars := [],           term := txMaxGasLimit,
      doc := "EIP-7825 (Osaka+)" }
  , { name := "modexp-gas",
      vars := ["base-sz", "exp-sz", "mod-sz", "exp-head", "fork-ord"],
      term := modexpGas,
      doc := "MODEXP (0x05): EIP-198 pre-Berlin / EIP-2565 Berlin+ / EIP-7883 Osaka+" }
  , { name := "mainnet-fork-ord",        vars := ["n", "ts"],  term := mainnetForkOrd,
      doc := "Ethereum mainnet fork schedule (Evm.Forks.ofBlock)" }
  , { name := "effective-gas-price",     vars := ["max-fee", "base-fee", "max-prio"],
      term := effectiveGasPrice, doc := "EIP-1559", dom := .wei } ]

/-- The formulas a 64-bit C host gets. -/
def emitted : List CDef := defs.filter fun d => d.dom == .gas

/-- The formulas held back for the 256-bit printer — named, not dropped. -/
def deferred : List CDef := defs.filter fun d => d.dom == .wei

private def banner (what : String) : String :=
  s!"/* c/generated/{what} — EMITTED by `lake exe emitHostC` from lean/Evm/CL/GasEmitC.lean;\n" ++
  "   do not edit. Each function is the C printing of the same Evm.CL.GasEmit term that\n" ++
  "   src/generated/host.lisp prints as Common Lisp, so a C host and the Lisp host compute\n" ++
  "   one formula, owned by Lean. Regenerate, never hand-edit (CONTRIBUTING rule 2). */\n"

/-- `c/generated/host.h` — the prototypes. -/
def headerFile : Except String String := do
  let protos ← emitted.mapM fun d => do
    d.check
    .ok ((if d.doc.isEmpty then "" else s!"/* {d.doc} */\n") ++ s!"{d.proto};")
  .ok (banner "host.h" ++
    "#ifndef EITA_GENERATED_HOST_H\n#define EITA_GENERATED_HOST_H\n#include <stdint.h>\n\n" ++
    "void eita_spec_overflow(const char *where) __attribute__((noreturn));\n\n" ++
    "/* Held back for the 256-bit printer (wei-valued: not bounded by the gas limit,\n" ++
    "   and their intermediates exceed 2^64 — see Evm.CL.GasEmitC.Dom):\n" ++
    String.join (deferred.map fun d => s!"     spec-{d.name}\n") ++
    "   src/generated/host.lisp emits all of them. */\n\n" ++
    "\n".intercalate protos ++ "\n\n#endif\n")

/-- `c/generated/host.c` — the prelude and the functions. -/
def cFile : Except String String := do
  let fns ← emitted.mapM CDef.toC
  .ok (banner "host.c" ++ "#include \"host.h\"\n\n" ++ preludeC ++ "\n" ++
       "\n".intercalate fns)

/-! ## The gate: vectors computed by `Expr.eval`

`toC` is a second printer of a term whose meaning is `Expr.eval`, so the thing
worth checking is exactly that: for a sweep of inputs, the compiled C must agree
with what Lean computes. `emitHostC --vectors` prints that comparison as a C
program; `make -C c test_host_gas` builds and runs it, on the host and
cross-compiled. A printer bug (a swapped operand, a `max 0` dropped, a
truncated 256-bit leaf) fails it.

Why these inputs: `fork-ord` is swept over every fork, because that is where the
fork-delta logic lives; sizes are swept over the thresholds the formulas branch
on (32/33, 64/65, 1024/1025); and a `u256` leaf is swept *past* 2^64, which is
what catches a truncation. -/

private def sweepU64 : List Nat := [0, 1, 2, 7, 31, 32, 33, 64, 65, 1000, 1024, 1025, 100000]
private def sweepU256 : List Nat :=
  [0, 1, 255, 2^63, 2^64 - 1, 2^64, 2^128, 2^200, 2^256 - 1]

private def sweepVals (v : String) : List Nat :=
  match cvarTy v with
  | .u256 => sweepU256
  | .u64  => if v == "fork-ord" then List.range 21 else sweepU64

private def limbsOf (n : Nat) : List Nat :=
  [n % 2^64, (n / 2^64) % 2^64, (n / 2^128) % 2^64, (n / 2^192) % 2^64]

private def bindOf (binds : List (String × Nat)) (v : String) : Nat :=
  (binds.find? (·.1 == v)).elim 0 (·.2)

/-- One vector as a C block. A value the formula sends past 2^64 is skipped: there
    the emitted C traps by design, and the trap is the subject of its own test. -/
private def vectorOf (d : CDef) (binds : List (String × Nat)) : Option String :=
  let want := d.term.eval (mkEnv binds)
  if want ≥ 2 ^ 64 then none
  else
    let decls := String.join (d.vars.filterMap fun v =>
      match cvarTy v with
      | .u256 =>
          let ls := ", ".intercalate ((limbsOf (bindOf binds v)).map fun l => s!"UINT64_C({l})")
          some s!"const uint64_t {cname v}[4] = \{{ls}}; "
      | .u64  => none)
    let args := ", ".intercalate (d.vars.map fun v =>
      match cvarTy v with
      | .u256 => cname v
      | .u64  => s!"UINT64_C({bindOf binds v})")
    let shown := " ".intercalate (d.vars.map fun v => s!"{v}={bindOf binds v}")
    some s!"  \{ {decls}chk(\"eita_spec_{cname d.name}\", \"{shown}\", eita_spec_{cname d.name}({args}), UINT64_C({want})); }"

/-- Baseline 1 for every input, then one input varied at a time over its sweep. -/
private def vectorsFor (d : CDef) : List String :=
  let baseline := d.vars.map (fun v => (v, 1))
  let one := (vectorOf d baseline).toList
  one ++ (d.vars.flatMap fun v =>
    (sweepVals v).filterMap fun x =>
      vectorOf d (baseline.map fun (n, b) => if n == v then (n, x) else (n, b)))

/-- `c/test_host_gas.c` — the emitted comparison. -/
def vectorsFile : Except String String := do
  emitted.forM CDef.check
  let blocks := emitted.map fun d =>
    s!"  /* {d.name} */\n" ++ "\n".intercalate (vectorsFor d)
  let n := (emitted.map (fun d => (vectorsFor d).length)).foldl (· + ·) 0
  .ok (s!"/* c/test_host_gas.c — EMITTED by `lake exe emitHostC --vectors`; do not edit.\n" ++
    s!"   {n} vectors over c/generated/host.c, every expected value computed by\n" ++
    "   Evm.CL.GasEmit.Expr.eval in Lean — the meaning the printer is a second view of. */\n" ++
    "#include <stdio.h>\n#include <stdlib.h>\n#include <stdint.h>\n" ++
    "#include \"generated/host.h\"\n\n" ++
    "static int fails = 0, checks = 0;\n\n" ++
    "void eita_spec_overflow(const char *where) {\n" ++
    "  printf(\"FAIL: unexpected overflow trap in %s\\n\", where); exit(1);\n}\n\n" ++
    "static void chk(const char *fn, const char *inputs, uint64_t got, uint64_t want) {\n" ++
    "  checks++;\n" ++
    "  if (got != want) {\n" ++
    "    fails++;\n" ++
    "    printf(\"FAIL %s [%s]: C %llu, Lean %llu\\n\", fn, inputs,\n" ++
    "           (unsigned long long)got, (unsigned long long)want);\n  }\n}\n\n" ++
    "int main(void) {\n" ++
    "\n".intercalate blocks ++ "\n" ++
    "  printf(\"host gas vectors: %d checked, %d failed\\n\", checks, fails);\n" ++
    "  return fails != 0;\n}\n")

end Evm.CL.GasEmit
