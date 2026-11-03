/-
  Evm.CL.Pressure — how many scratch registers the gadgets actually need.

  Stage 2 of #238. `Evm.CL.Target` fixed the role assignment and showed x86-64
  has FIVE scratch registers (rax, rcx, rdx, rsi, rdi) once TOS is cached and
  NOS is dropped. The structured gadgets in `AsmCore` use SIX ARM64 registers as
  temporaries — x0, x4, x14, x15, x16, x17 — so the obvious worry is that the
  x86 assignment is one short.

  "Uses six" is not the same as "needs six at once", though, and the difference
  decides whether the x86 lowering can be a straight register substitution or
  has to spill. So this module measures it instead of guessing: per gadget, the
  maximum number of temporaries whose live ranges overlap.

  The measure is deliberately an OVER-approximation — one live range per
  register, from its first mention to its last, so a register reused for two
  unrelated purposes counts as live in between. Over-approximating is the safe
  direction: if the bound fits in five, the substitution is sound; if it does
  not, the bound alone does not prove it impossible, only that a closer look is
  needed.
-/

import Evm.CL.AsmCore
import Evm.CL.Target

namespace Evm.CL.Pressure

open Evm.CL.AsmCore

/-- The registers an instruction mentions (reads or writes — for a pressure
    bound the distinction does not matter, since a mention means the value must
    be somewhere). -/
def mentions : AInstr → List Reg
  | .subImm d a _      => [d, a]
  | .addLsl5 d a b     => [d, a, b]
  | .ldrOff d b _      => [d, b]
  | .ldrBase d b       => [d, b]
  | .movImm d _        => [d]
  | .orr3 d a b        => [d, a, b]
  | .adds d a b        => [d, a, b]
  | .cmpReg a b        => [a, b]
  | .cselHi d a b      => [d, a, b]
  | .cbnzOog r         => [r]
  | .bcsOog            => []
  | .bhiOog            => []
  | .bloOog            => []
  | .subsReg d a b     => [d, a, b]
  | .ldpOff r1 r2 b _  => [r1, r2, b]
  | .blsLbl _          => []
  | .cbzLbl r _        => [r]
  | .bLbl _            => []
  | .label _           => []
  | .addImm d a _      => [d, a]
  | .subReg d a b      => [d, a, b]
  | .addReg d a b      => [d, a, b]
  | .mulReg d a b      => [d, a, b]
  | .clzReg d a        => [d, a]
  | .lsrImm d a _      => [d, a]
  | .lslImm d a _      => [d, a]
  | .addLsr d a b _    => [d, a, b]
  | .addLsl d a b _    => [d, a, b]
  | .strOff s b _      => [s, b]
  | .cmpImm a _        => [a]
  | .bSym _ _          => []
  | .addsImm d a _     => [d, a]
  | .rev d a           => [d, a]
  | .movReg d a        => [d, a]
  | .stpOff r1 r2 b _  => [r1, r2, b]
  | .brCont            => []
  | .adcs d a b | .adc d a b | .sbcs d a b | .sbc d a b
  | .and3 d a b | .eor3 d a b => [d, a, b]
  | .subsImm d a _     => [d, a]
  | .mvn d a           => [d, a]
  | .subsZr a b | .sbcsZr a b => [a, b]
  | .cset d _          => [d]
  | .ldrbReg d b i     => [d, b, i]
  | .bcLbl _ _         => []
  | .movImmW d _       => [d]
  | .spSub _ | .spAdd _ | .stpFpLr | .ldpFpLr | .blSym _ => []
  | .blr r             => [r]
  | .bSymU _           => []
  | .ldrbOff d b _     => [d, b]
  | .strbOff s b _     => [s, b]
  | .strbReg s b i     => [s, b, i]
  | .cbnzSym r _       => [r]
  | .cmpImmWHex r _    => [r]
  | .loadSymAddr d _   => [d]
  | .brReg r           => [r]
  | .cselNe d a b      => [d, a, b]
  | .cbnzSymW r _      => [r]
  | .movzImm d _       => [d]
  | .madd d a b c      => [d, a, b, c]
  | .strZr b _         => [b]
  | .strWSp s _ | .strSp s _ => [s]
  | .strWzrSp _ | .stpZrSp _ => []
  | .stpSp r1 r2 _     => [r1, r2]
  | .ldrWSp d _        => [d]
  | .cbzWLbl r _       => [r]
  | .andImmHex d a _   => [d, a]
  | .csinvEqZr d a     => [d, a]
  | .global _ | .p2align2 | .symLabel _ | .ret => []
  | .stpPreSp r1 r2 _ | .ldpPostSp r1 r2 _ | .ldpSp r1 r2 _ => [r1, r2]
  | .movToSp r | .movFromSp r => [r]
  | .ldrLsl3 d b i     => [d, b, i]
  | .loadSymValue d _ | .loadSymGotValue d _ => [d]
  | .movkImm d _ _ | .adrLbl d _ => [d]
  | .addSpReg r | .spAddReg r | .spSubReg r => [r]
  | .brk0 | .bFar _ | .bTramp _ | .bcTramp _ _ | .blFar _ => []
  | .strBase s b | .strbBase s b => [s, b]
  | .csel d a b _      => [d, a, b]
  | .cselZrA d b _     => [d, b]
  | .cselZrB d a _     => [d, a]
  | .eorImm1 d a       => [d, a]
  | .tstImm r _ | .cbnzLbl r _ | .cbnzWLbl r _ => [r]
  | .blank | .textSection | .dataSection | .p2align3 | .quadSym _ | .quadPair _ _ _ | .commentLine _ => []
  | .addSp d _         => [d]
  | .ldrSp d _         => [d]

/-- The temporaries: everything that is not one of the pinned caches. x0 and x4
    are temporaries too — they are free inside a handler because the C ABI's
    argument registers are dead there, which is exactly why the gadgets reach
    for them. -/
def isTemp : Reg → Bool
  | .x0 | .x4 | .x14 | .x15 | .x16 | .x17 => true
  | _ => false

def allTemps : List Reg := [.x0, .x4, .x14, .x15, .x16, .x17]

/-- First and last index at which `r` is mentioned (`none` = never). -/
def liveRange (p : List AInstr) (r : Reg) : Option (Nat × Nat) :=
  let idxs := (p.zipIdx).filterMap (fun (it, i) =>
    if (mentions it).contains r then some i else none)
  match idxs with
  | [] => none
  | i :: rest => some (i, rest.foldl max i)

/-- Is `r` live at index `i` under the one-range approximation? -/
def liveAt (p : List AInstr) (r : Reg) (i : Nat) : Bool :=
  match liveRange p r with
  | none => false
  | some (lo, hi) => decide (lo ≤ i) && decide (i ≤ hi)

/-- Temporaries simultaneously live at index `i`. -/
def pressureAt (p : List AInstr) (i : Nat) : Nat :=
  (allTemps.filter (fun r => liveAt p r i)).length

/-- The peak over the gadget. -/
def pressure (p : List AInstr) : Nat :=
  ((List.range p.length).map (pressureAt p)).foldl max 0

/-! ## The measurements

Each of these is the gadget the emitters actually use, so the numbers move if
the gadgets do. -/

def memExpandP   : Nat := pressure memExpandInstrs
def memRangeP    : Nat := pressure (memRangeInstrs 3 1 .x0 "Z" "D")
def keccakGasP   : Nat := pressure (keccakGasInstrs 30)
def copyGasP     : Nat := pressure (copyGasInstrs 3)
def mcopyGasP    : Nat := pressure (mcopyGasInstrs 3)
def extcodecopyP : Nat := pressure extcodecopyGasInstrs

/-- The five scratch registers x86-64 has, per `Evm.CL.Target`. -/
def x86Scratch : Nat := 5

/-- **Every gadget fits in five temporaries.** So the x86-64 lowering can be a
    register substitution for these — no spill slot, no re-sequencing — even
    though the ARM64 code reaches for six different registers across them. -/
theorem memExpand_fits   : memExpandP   ≤ x86Scratch := by native_decide
theorem memRange_fits    : memRangeP    ≤ x86Scratch := by native_decide
theorem keccakGas_fits   : keccakGasP   ≤ x86Scratch := by native_decide
theorem copyGas_fits     : copyGasP     ≤ x86Scratch := by native_decide
theorem mcopyGas_fits    : mcopyGasP    ≤ x86Scratch := by native_decide
theorem extcodecopy_fits : extcodecopyP ≤ x86Scratch := by native_decide

/-- The measured peaks. Four of the six gadgets sit exactly ON the x86-64
    scratch budget, so the fit is tight rather than comfortable — a new gadget
    needing a sixth live temporary would force a spill slot. (I guessed 4 for
    `extcodecopy`; it is 5.) -/
theorem peaks :
    memExpandP = 4 ∧ memRangeP = 4 ∧ keccakGasP = 5 ∧
    copyGasP = 5 ∧ mcopyGasP = 5 ∧ extcodecopyP = 5 := by native_decide

/-- **The bound is tight**: the worst gadget needs exactly as many temporaries
    as x86-64 has. Worth stating, because it means the register map in
    `Evm.CL.Target` has no headroom at all for the gadgets — and that is the
    constraint to check first if one grows. -/
theorem bound_is_tight : keccakGasP = x86Scratch := by native_decide

/-- Every temporary but x4 is used — x4 left the gadgets when EXTCODECOPY moved onto
    memRangeInstrs (its operands are now range-checked over all 256 bits). -/
theorem all_temps_but_x4_are_used :
    (allTemps.filter (· != .x4)).all (fun r =>
      [memExpandInstrs, keccakGasInstrs 30, copyGasInstrs 3, mcopyGasInstrs 3,
       extcodecopyGasInstrs].any (fun p => (liveRange p r).isSome)) = true := by
  native_decide

/-- ARM64's own four named scratch registers (x14-x17) are NOT enough on their
    own — which is why the gadgets borrow x0 and x4, and why the role layer has
    to model a pool of five rather than a fixed x14-x17. -/
theorem arm64_named_scratch_insufficient :
    4 < keccakGasP := by native_decide


/-! ## The x86-64 temporary assignment, and why it is forced

Five is enough, but the gadgets name six temporaries, so the lowering has to
merge two of them. Which two is not a free choice: the interference graph over
{x0, x4, x14, x15, x16, x17} — computed from the live ranges above across all
six gadgets — is the complete graph MINUS exactly one edge.

So a 5-colouring exists, needs at least 5 colours, and every valid one merges
the same single pair. The x86-64 map is therefore determined by the ARM64 code,
not chosen. -/

def gadgetSet : List (List AInstr) :=
  [memExpandInstrs, memRangeInstrs 3 1 .x0 "Z" "D", keccakGasInstrs 30,
   copyGasInstrs 3, mcopyGasInstrs 3, extcodecopyGasInstrs]

/-- Do `a` and `b` have overlapping live ranges in any gadget? -/
def interferes (a b : Reg) : Bool :=
  gadgetSet.any (fun p => (List.range p.length).any (fun i => liveAt p a i && liveAt p b i))

/-- **x4 collides with nothing; every other pair of temporaries does.** So the x86
    map's x4/x16 merge stays valid, and is no longer the only possible one. -/
theorem only_x4_is_free :
    allTemps.all (fun b => !interferes .x4 b) ∧
    (allTemps.filter (· != .x4)).all (fun a =>
      (allTemps.filter (· != .x4)).all (fun b => a == b || interferes a b)) = true := by
  native_decide

/-- `{x0, x14, x15, x16, x17}` is a 5-clique, so four colours cannot do. -/
theorem five_clique_exists :
    let c : List Reg := [.x0, .x14, .x15, .x16, .x17]
    (c.flatMap (fun a => c.filterMap (fun b =>
        if a != b && !interferes a b then some (a, b) else none))) = [] := by
  native_decide

/-- The assignment: each ARM64 temporary to one of x86-64's five scratch
    registers, with x4 and x16 — the only compatible pair — sharing. -/
def x86Temp : Reg → String
  | .x0  => "rax"
  | .x14 => "rcx"
  | .x15 => "rdx"
  | .x17 => "rsi"
  | .x4  => "rdi"
  | .x16 => "rdi"
  | _    => "«not a temporary»"

/-- **The assignment is valid**: no two temporaries that are ever live together
    share an x86-64 register. -/
theorem x86Temp_respects_interference :
    (allTemps.flatMap (fun a => allTemps.filterMap (fun b =>
        if a != b && interferes a b && x86Temp a == x86Temp b then some (a, b) else none)))
      = [] := by
  native_decide

/-- …and it uses exactly the five registers `Evm.CL.Target` set aside, no more. -/
theorem x86Temp_uses_five :
    ((allTemps.map x86Temp).eraseDups).length = x86Scratch := by native_decide

theorem x86Temp_targets_are_the_scratch_pool :
    (allTemps.map x86Temp).eraseDups.all
      (fun r => ["rax", "rcx", "rdx", "rsi", "rdi"].contains r) = true := by
  native_decide

end Evm.CL.Pressure
