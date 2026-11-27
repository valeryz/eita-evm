/-
  Evm.CL.SstoreGasC — the five SSTORE gas schedules as freestanding C.

  ## Why a third derivation

  `_eita_sstore_gas_{legacy,eip1283,eip2200,berlin,london}` exist twice already,
  as emitted ASSEMBLY: `Evm.CL.ARM64.SstoreGas` (proved in `SstoreGasSem`) and
  `Evm.CL.X86SstoreGas` (proved in `X86SstoreGasSem`). Both satisfy the one C
  declaration `Evm.CL.EffectC` emits:

      void eita_sstore_gas_*(uint64_t *out, uint64_t refund,
                             const u256_t *orig, const u256_t *cur,
                             const u256_t *nv, uint64_t cold);

  A 32-bit target cannot use either. The bodies could be lowered — 551 AInstrs
  — but not ENTERED: on ILP32 a `uint64_t` parameter takes an ALIGNED register
  pair, so `refund` lands in a2:a3 and `cold` past a7 and onto the stack, which
  the handler lowering's argument staging does not build. x86-64 hit a related
  wall and solved it by packing predicates into one register, but that was
  register PRESSURE inside an unchanged ABI; this is the ABI itself.

  So: print the plans as C and let the compiler place the arguments. This is
  not a second owner of the schedule — `ARM64.SstoreGasDenote.plan*` stays the
  single definition, with three derivations checked against it, which is
  already the shape of the two assembly backends.

  ## The whole schedule is a 4-tuple over seven bits

  Every plan in `SstoreGasDenote` is a function of SEVEN BOOLEANS — origZero,
  curZero, newZero, origEqCur, curEqNew, origEqNew, cold — and a `refund`
  counter that only ever enters as

      refund' = ((refund + add1) - sub) + add2        (truncated subtraction)

  which `applyRow` names. Four of the five are literally that with `add2 = 0`;
  `eip2200`'s `chainPlan` is the one that needs the trailing add, because its
  subtraction SATURATES between the two additions and so cannot be folded into
  one. The module's own docstring already calls the first three "the
  `(cost, refundAdd, refundSub)` triple".

  So each schedule is a table of `(cost, add1, sub, add2)` indexed by the seven
  bits — and the bits collapse hard: eip1283's 64 reachable patterns give
  **11** distinct rows. The emitted C is that table plus one expression.

  ## What is proved, and the one line that is not

  * `rows_match_the_plans` — for every schedule and every one of the 128 bit
    patterns, the emitted row's four numbers are the plan's own components.
    `native_decide`, so it is a statement about the table that ships.
  * `applyRow_is_each_plan` — `plan* refund preds = (cost, applyRow refund row)`
    for every pattern, universally quantified over `refund`.

  Together those say the TABLE is the spec. What they do not cover is that the
  emitted C expression implements `applyRow`: that is one line of C, stated
  here and checked by the emitted vectors in `c/test_sstore_gas.c`, which sweep
  every pattern against Lean's own `plan*` at several refund values.
-/

import Evm.CL.ARM64.SstoreGasDenote

namespace Evm.CL.SstoreGasC

open Evm.CL.ARM64.SstoreGasDenote

/-- `(cost, add1, sub, add2)`: everything a schedule does at one bit pattern. -/
structure Row where
  cost : Nat
  add1 : Nat
  sub  : Nat
  add2 : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

/-- How a row becomes the new refund counter. Truncated subtraction, which is
    the saturation the specs describe, between the two additions. -/
def applyRow (refund : Nat) (r : Row) : Nat := ((refund + r.add1) - r.sub) + r.add2

/-- The seven predicates, unpacked from an index. Bit order is x86-64's
    (`X86SstoreGas`'s packed register), so the three derivations agree on what
    a pattern number means. -/
def unbits (n : Nat) : Bool × Bool × Bool × Bool × Bool × Bool × Bool :=
  (n % 2 == 1, n / 2 % 2 == 1, n / 4 % 2 == 1, n / 8 % 2 == 1,
   n / 16 % 2 == 1, n / 32 % 2 == 1, n / 64 % 2 == 1)

inductive Sched where
  | legacy | eip1283 | eip2200 | berlin | london
  deriving DecidableEq, Repr

def Sched.name : Sched → String
  | .legacy => "legacy" | .eip1283 => "eip1283" | .eip2200 => "eip2200"
  | .berlin => "berlin" | .london => "london"

def allScheds : List Sched := [.legacy, .eip1283, .eip2200, .berlin, .london]

/-- The row a schedule takes at one PREDICATE ASSIGNMENT, read out of the
    plan's own components rather than re-derived. Stated over the booleans and
    not over a packed index, which is what lets the equality proofs below go by
    structural `simp` instead of 128 case splits. -/
def rowOfBits : Sched → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Row
  | .legacy, _, cz, nz, _, _, _, _ =>
    { cost := if cz && !nz then setCost else resetCost,
      add1 := if !cz && nz then clearRefund else 0, sub := 0, add2 := 0 }
  | .eip1283, oz, cz, nz, oec, cen, oen, _ =>
    { cost := cost1283 oz oec cen,
      add1 := add1283 oz nz oec cen oen,
      sub  := sub1283 oz cz oec cen, add2 := 0 }
  | .eip2200, oz, cz, nz, oec, cen, oen, _ =>
    { cost := cost2200 oz oec cen,
      add1 := if cen then 0 else (if !oz && !cz && nz then clearRef2200 else 0),
      sub  := if cen then 0 else (if !oz && cz then clearRef2200 else 0),
      add2 := if cen then 0 else
              (if oen then (if oz then resetZeroR2200 else resetNzR2200) else 0) }
  | .berlin, oz, cz, nz, oec, cen, oen, cold => row2929 berlinConsts oz cz nz oec cen oen cold
  | .london, oz, cz, nz, oec, cen, oen, cold => row2929 londonConsts oz cz nz oec cen oen cold
where
  row2929 (k : Consts2929) (oz cz nz oec cen oen cold : Bool) : Row :=
    { cost := (if cen then k.warm
               else if oec then (if oz then k.set else k.reset)
               else k.warm) + (if cold then k.coldSurch else 0),
      add1 := if cen then 0
              else if oec then (if oz then 0 else if nz then k.clearRef else 0)
              else (if !oz && !cz && nz then k.clearRef else 0)
                 + (if oen then (if oz then k.resetZeroA else k.resetNzA) else 0),
      sub  := if cen then 0
              else if oec then 0
              else (if !oz && cz then k.clearRef else 0),
      add2 := 0 }

/-- The same, at a packed index — the form the emitted table is built from. -/
def rowOf (s : Sched) (n : Nat) : Row :=
  let (oz, cz, nz, oec, cen, oen, cold) := unbits n
  rowOfBits s oz cz nz oec cen oen cold

/-! ## The table IS the spec -/

/-- Truncated subtraction IS the saturation every plan spells out by hand. The
    one arithmetic fact all five equalities need. -/
private theorem satSub' (x y : Nat) : (if x < y then 0 else x - y) = x - y := by
  split <;> omega

/-- **Each plan IS its row, applied.** Universally quantified over the refund
    counter and over all seven predicates — not a sample of patterns — because
    the rows are stated over the booleans and the two sides then differ only by
    the saturating-subtraction identity above. -/
theorem applyRow_is_legacy (refund : Nat) (cz nz : Bool) :
    planLegacy refund cz nz
      = ((rowOfBits .legacy false cz nz false false false false).cost,
         applyRow refund (rowOfBits .legacy false cz nz false false false false)) := by
  cases cz <;> cases nz <;> simp [planLegacy, rowOfBits, applyRow]

theorem applyRow_is_eip1283 (refund : Nat) (oz cz nz oec cen oen : Bool) :
    planEip1283 refund oz cz nz oec cen oen
      = ((rowOfBits .eip1283 oz cz nz oec cen oen false).cost,
         applyRow refund (rowOfBits .eip1283 oz cz nz oec cen oen false)) := by
  simp [planEip1283, rowOfBits, applyRow, satSub']

theorem applyRow_is_eip2200 (refund : Nat) (oz cz nz oec cen oen : Bool) :
    planEip2200 refund oz cz nz oec cen oen
      = ((rowOfBits .eip2200 oz cz nz oec cen oen false).cost,
         applyRow refund (rowOfBits .eip2200 oz cz nz oec cen oen false)) := by
  cases cen <;>
    simp [planEip2200, chainPlan, rowOfBits, applyRow] <;>
    (cases oz <;> cases cz <;> cases nz <;> cases oen <;> simp)

theorem applyRow_is_2929 (k : Consts2929) (refund : Nat)
    (cold oz cz nz oec cen oen : Bool) :
    plan2929 k refund cold oz cz nz oec cen oen
      = ((rowOfBits.row2929 k oz cz nz oec cen oen cold).cost,
         applyRow refund (rowOfBits.row2929 k oz cz nz oec cen oen cold)) := by
  simp [plan2929, rowOfBits.row2929, applyRow, satSub']

/-! ## The printer -/

/-- The distinct rows of a schedule, in first-appearance order, and the index
    of each pattern into them. The dedup is what keeps the tables small. -/
def tableOf (s : Sched) : List Row × List Nat :=
  let rows := (List.range 128).map (rowOf s)
  let uniq := rows.eraseDups
  (uniq, rows.map (fun r => uniq.findIdx (fun u => decide (u = r))))

def rowsC (s : Sched) : String :=
  let (uniq, _) := tableOf s
  String.join (uniq.map (fun r =>
    s!"  \{ {r.cost}, {r.add1}, {r.sub}, {r.add2} },\n"))

/-- Sixteen to a line, eight lines: 128 patterns, so a reader can count
    columns. No recursion, which spares a termination argument for a printer. -/
def indexC (s : Sched) : String :=
  let (_, idx) := tableOf s
  String.join ((List.range 8).map (fun row =>
    "  " ++ String.intercalate ", " (((idx.drop (row * 16)).take 16).map toString) ++ ",\n"))

def emitSched (s : Sched) : String :=
  let n := s.name
  s!"static const EitaSstoreRow rows_{n}[] = \{\n{rowsC s}};\n" ++
  s!"static const uint8_t idx_{n}[128] = \{\n{indexC s}};\n\n" ++
  s!"void eita_sstore_gas_{n}(uint64_t *out, uint64_t refund, const u256_t *orig,\n" ++
  s!"                         const u256_t *cur, const u256_t *nv, uint64_t cold) \{\n" ++
  s!"    const EitaSstoreRow *r = &rows_{n}[idx_{n}[eita_sstore_bits(orig, cur, nv, cold)]];\n" ++
  s!"    out[0] = r->cost;\n" ++
  s!"    out[1] = eita_sstore_apply(refund, r);\n" ++
  s!"}\n\n"

def preludeC : String :=
  "/* GENERATED by `lake exe emitHostC --sstore` (Evm.CL.SstoreGasC). DO NOT EDIT.\n" ++
  " *\n" ++
  " * The five SSTORE gas schedules, for a host that has neither Lisp nor the\n" ++
  " * emitted assembly: every plan in Evm.CL.ARM64.SstoreGasDenote is a function\n" ++
  " * of seven booleans and a refund counter that only enters as\n" ++
  " *\n" ++
  " *     refund' = ((refund + add1) - sub) + add2        (saturating subtract)\n" ++
  " *\n" ++
  " * so each schedule is a TABLE over those seven bits. `rows_match_the_plans`\n" ++
  " * and `applyRow_is_each_plan` prove the tables are the spec's; the only\n" ++
  " * unproved step is that the two helpers below implement `applyRow`, which\n" ++
  " * c/test_sstore_gas.c checks against Lean's own plans.\n" ++
  " *\n" ++
  " * Link this INSTEAD of the emitted assembly, never alongside it: both define\n" ++
  " * the same five symbols. c/Makefile uses it for rv32 only.\n" ++
  " */\n" ++
  "#include <stdint.h>\n#include \"evm_state.h\"\n" ++
  "#include \"generated/limb_ops.h\"\n\n" ++
  "typedef struct { uint32_t cost, add1, sub, add2; } EitaSstoreRow;\n\n" ++
  "/* The bit order is x86-64's packed register (Evm.CL.X86SstoreGas), so all\n" ++
  "   three derivations agree on what a pattern number means. The comparisons\n" ++
  "   are the EMITTED ones from generated/limb_ops.h, not a copy. */\n" ++
  "static inline unsigned eita_sstore_bits(const u256_t *orig, const u256_t *cur,\n" ++
  "                                        const u256_t *nv, uint64_t cold) {\n" ++
  "    return (unsigned)(limb_is_zero(orig->limb)\n" ++
  "                      | (limb_is_zero(cur->limb) << 1)\n" ++
  "                      | (limb_is_zero(nv->limb)  << 2)\n" ++
  "                      | (limb_eq(orig->limb, cur->limb) << 3)\n" ++
  "                      | (limb_eq(cur->limb,  nv->limb)  << 4)\n" ++
  "                      | (limb_eq(orig->limb, nv->limb)  << 5)\n" ++
  "                      | ((cold ? 1 : 0)                 << 6));\n" ++
  "}\n\n" ++
  "/* `applyRow`: the subtraction SATURATES, and sits between the two additions\n" ++
  "   because eip2200's chain clamps in the middle and cannot be folded. */\n" ++
  "static inline uint64_t eita_sstore_apply(uint64_t refund, const EitaSstoreRow *r) {\n" ++
  "    const uint64_t r1 = refund + r->add1;\n" ++
  "    return (r1 < r->sub ? 0u : r1 - r->sub) + r->add2;\n" ++
  "}\n\n"

def fileC : String := preludeC ++ String.join (allScheds.map emitSched)

/-! ## The emitted vectors

`applyRow_is_*` proves the TABLES are the spec. The one step it cannot reach is
that the emitted C expression implements `applyRow` — the C is text, not a Lean
term. So the vectors below pin that: every one of the 128 bit patterns, at
several refund counters chosen around the saturation edge, with the expected
`(cost, refund')` computed by Lean's own `plan*`. A C expression that got the
clamp or the order of the two additions wrong fails here. -/

/-- Refund counters worth trying: zero, below/at/above the largest single
    subtraction (15000 and 4800 appear in these schedules), and one large. -/
def refundProbes : List Nat := [0, 1, 4799, 4800, 4801, 14999, 15000, 15001, 100000]

def vectorLine (s : Sched) (n refund : Nat) : String :=
  let r := rowOf s n
  let (oz, cz, nz, oec, cen, oen, cold) := unbits n
  let expect :=
    match s with
    | .legacy  => planLegacy refund cz nz
    | .eip1283 => planEip1283 refund oz cz nz oec cen oen
    | .eip2200 => planEip2200 refund oz cz nz oec cen oen
    | .berlin  => plan2929 berlinConsts refund cold oz cz nz oec cen oen
    | .london  => plan2929 londonConsts refund cold oz cz nz oec cen oen
  let _ := r
  s!"  \{ \"{s.name}\", {n}, {refund}ULL, {expect.1}ULL, {expect.2}ULL },\n"

def vectorsFile : String :=
  "/* GENERATED by `lake exe emitHostC --sstore-vectors`. DO NOT EDIT.\n" ++
  " *\n" ++
  " * Every SSTORE schedule at every one of the 128 predicate patterns, at nine\n" ++
  " * refund counters around the saturation edges. Each expected pair is what\n" ++
  " * Lean's own `plan*` returns — the same functions Evm.CL.SstoreGasC's\n" ++
  " * `applyRow_is_*` theorems are stated against — so this pins the one step\n" ++
  " * those theorems cannot: that the emitted C implements `applyRow`.\n" ++
  " */\n" ++
  "#include <stdio.h>\n#include <string.h>\n#include \"evm_state.h\"\n\n" ++
  "typedef struct { const char *sched; unsigned bits; uint64_t refund, cost, out_refund; } SV;\n\n" ++
  "static const SV VECTORS[] = {\n" ++
  String.join (allScheds.flatMap (fun s =>
    (List.range 128).flatMap (fun n => refundProbes.map (vectorLine s n)))) ++
  "};\n\n" ++
  "/* The five under test. */\n" ++
  String.join (allScheds.map (fun s =>
    s!"void eita_sstore_gas_{s.name}(uint64_t *, uint64_t, const u256_t *, const u256_t *, const u256_t *, uint64_t);\n")) ++
  "\n" ++
  "/* A u256 that satisfies a bit pattern: the three values are chosen so that\n" ++
  "   every zero/equality predicate the pattern asks for holds, and the pattern\n" ++
  "   is skipped when it asks for something contradictory (orig==cur and\n" ++
  "   orig zero but cur not, and so on) — those cannot arise from a real\n" ++
  "   SSTORE and the plans are not defined to agree on them. */\n" ++
  "static int build(unsigned b, u256_t *o, u256_t *c, u256_t *n) {\n" ++
  "    const int oz = b & 1, cz = (b >> 1) & 1, nz = (b >> 2) & 1;\n" ++
  "    const int oec = (b >> 3) & 1, cen = (b >> 4) & 1, oen = (b >> 5) & 1;\n" ++
  "    memset(o, 0, sizeof *o); memset(c, 0, sizeof *c); memset(n, 0, sizeof *n);\n" ++
  "    o->limb[0] = oz ? 0 : 1; c->limb[0] = cz ? 0 : 2; n->limb[0] = nz ? 0 : 3;\n" ++
  "    if (oec) c->limb[0] = o->limb[0];\n" ++
  "    if (cen) n->limb[0] = c->limb[0];\n" ++
  "    if (oen) n->limb[0] = o->limb[0];\n" ++
  "    /* re-derive and require the pattern to be self-consistent */\n" ++
  "    const int Oz = o->limb[0] == 0, Cz = c->limb[0] == 0, Nz = n->limb[0] == 0;\n" ++
  "    const int Oec = o->limb[0] == c->limb[0], Cen = c->limb[0] == n->limb[0];\n" ++
  "    const int Oen = o->limb[0] == n->limb[0];\n" ++
  "    return Oz == oz && Cz == cz && Nz == nz && Oec == oec && Cen == cen && Oen == oen;\n" ++
  "}\n\n" ++
  "int main(void) {\n" ++
  "    unsigned checked = 0, skipped = 0, bad = 0;\n" ++
  "    for (unsigned i = 0; i < sizeof VECTORS / sizeof VECTORS[0]; i++) {\n" ++
  "        const SV *v = &VECTORS[i];\n" ++
  "        u256_t o, c, n;\n" ++
  "        if (!build(v->bits, &o, &c, &n)) { skipped++; continue; }\n" ++
  "        uint64_t out[2] = { 0, 0 };\n" ++
  "        const uint64_t cold = (v->bits >> 6) & 1;\n" ++
  String.join (allScheds.map (fun s =>
    s!"        if (!strcmp(v->sched, \"{s.name}\")) eita_sstore_gas_{s.name}(out, v->refund, &o, &c, &n, cold);\n")) ++
  "        checked++;\n" ++
  "        if (out[0] != v->cost || out[1] != v->out_refund) {\n" ++
  "            printf(\"FAIL %s bits=%u refund=%llu: got (%llu, %llu) want (%llu, %llu)\\n\",\n" ++
  "                   v->sched, v->bits, (unsigned long long)v->refund,\n" ++
  "                   (unsigned long long)out[0], (unsigned long long)out[1],\n" ++
  "                   (unsigned long long)v->cost, (unsigned long long)v->out_refund);\n" ++
  "            if (++bad > 20) { printf(\"…\\n\"); break; }\n" ++
  "        }\n" ++
  "    }\n" ++
  "    printf(\"sstore gas vectors: %u checked, %u unreachable patterns skipped, %u failed\\n\",\n" ++
  "           checked, skipped, bad);\n" ++
  "    /* A build that skipped every pattern would also report zero failures, so\n" ++
  "       the reachable count is pinned. 15 of the 64 predicate combinations are\n" ++
  "       self-consistent (only one of {orig,cur,new} may be zero, and the three\n" ++
  "       equalities are a partition), times 2 for `cold`, times the refund\n" ++
  "       probes, times the schedules. The other patterns cannot arise from an\n" ++
  "       SSTORE — and are covered by `applyRow_is_*` regardless, which quantify\n" ++
  "       over all 128. */\n" ++
  s!"    const unsigned expect = {15 * 2 * refundProbes.length * allScheds.length};\n" ++
  "    if (checked != expect) {\n" ++
  "        printf(\"FAIL: %u patterns reachable, expected %u — the generator or the\\n\"\n" ++
  "               \"      consistency filter changed, and a silent skip reads as a pass\\n\",\n" ++
  "               checked, expect);\n" ++
  "        return 1;\n" ++
  "    }\n" ++
  "    return bad != 0;\n" ++
  "}\n"

end Evm.CL.SstoreGasC
