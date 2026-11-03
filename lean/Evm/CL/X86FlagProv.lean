/-
  Evm.CL.X86FlagProv — flag provenance is respected (x86-64).

  `X86Sem` shows the condition lowering (`bcondXc`) is correct only under the
  right provenance: after a `sub`-type instruction every condition agrees
  (x86 CF = borrow = ARM ¬C), after an `add`-type one only `eq`/`ne`/`lt` do
  (both carries are the carry, but ARM's `lo` is the carry CLEAR), and after a
  `tst` likewise (ARM clears C, x86 clears CF: `lo` holds on ARM only). The
  carry consumers are polarity-specific: `adc`/`bcsOog` need `add`,
  `sbb`/`bloOog`/`bhiOog` need `sub`. And several x86 instructions clobber the
  flags where their ARM originals do not (`add`/`sub`/`and`/`or`/`xor`/shifts/
  `imul`/`lzcnt`), which makes the provenance `unknown`.

  This is the static check that every flag consumer in every body the x86-64
  file emits, and in every chunk piece of the corpus, meets its requirement on
  every path — the flag counterpart of `X86Alias.no_alias_hazards`.
-/

import Evm.CL.X86Alias
import Evm.CL.X86JIT

namespace Evm.CL.X86FlagProv

open Evm.CL.AsmCore Evm.CL.X86Alias

/-- Possible flag origins at a point. -/
inductive P where
  | sub | add | logic | unknown
  deriving DecidableEq, Repr, BEq

/-- What an instruction leaves the flags as (`none` = unchanged). -/
def produces : AInstr → Option P
  | .adds .. | .addsImm .. | .adcs .. => some .add
  | .subsReg .. | .subsImm .. | .subsZr .. | .cmpReg .. | .cmpImm .. | .cmpImmWHex .. | .sbcs .. | .sbcsZr .. => some .sub
  | .tstImm .. => some .logic
  -- compare-and-branch forms lower to `cmp ; jcc`
  | .cbzLbl .. | .cbnzLbl .. | .cbzWLbl .. | .cbnzWLbl .. | .cbnzOog .. | .cbnzSym .. | .cbnzSymW .. => some .sub
  -- x86 clobbers where ARM does not
  | .addReg .. | .subReg .. | .and3 .. | .orr3 .. | .eor3 .. | .eorImm1 .. | .andImmHex ..
  | .mulReg .. | .madd .. | .lsrImm .. | .lslImm .. | .addLsr .. | .addLsl5 .. | .adc .. | .sbc ..
  | .clzReg .. | .spSub .. | .spAdd .. => some .unknown
  | .addLsl _ _ _ sh => if sh ≤ 3 then none else some .unknown
  | .addImm d a _ => if d == a || (X86Items.nosLimb a).isSome then some .unknown else none
  | .subImm d a _ => if d == a then some .unknown else none
  | _ => none

/-- Under which provenances a lowered condition is faithful. -/
def condOk (c : BCond) (p : P) : Bool :=
  match p with
  | .sub => true
  | .add | .logic => c == .eq || c == .ne || c == .lt
  | .unknown => false

def setcondOk (c : SetCond) (p : P) : Bool :=
  match p with
  | .sub => true
  | .add | .logic => c == .eq || c == .lt
  | .unknown => false

/-- The requirement an instruction places on the incoming provenance. -/
def requires : AInstr → Option (P → Bool)
  | .bcLbl c _ | .bSym c _ | .bcTramp c _ => some (condOk c)
  | .blsLbl _ => some (condOk .ls)
  | .csel _ _ _ c => some (condOk c)
  | .cselHi .. => some (condOk .hi)
  | .cselNe .. | .csinvEqZr .. => some (condOk .ne)
  | .cset _ c => some (setcondOk c)
  | .bcsOog | .adcs .. | .adc .. => some (fun p => p == .add)
  | .bloOog | .bhiOog | .sbcs .. | .sbc .. | .sbcsZr .. => some (fun p => p == .sub)
  | _ => none

def union (a b : List P) : List P := b.foldl (fun acc r => if acc.contains r then acc else r :: acc) a

/-- Forward dataflow: the provenances that can reach each instruction. Entry:
    unknown (a body is entered with arbitrary flags). -/
def provIn (p : Array AInstr) : Array (List P) := Id.run do
  let n := p.size
  let mut pi : Array (List P) := Array.replicate n []
  if n > 0 then pi := pi.set! 0 [.unknown]
  -- labels can be entered from a branch; a label at index 0 is the entry
  let mut changed := true
  let mut fuel := n * 8 + 8
  while changed && fuel > 0 do
    changed := false
    fuel := fuel - 1
    for i in List.range n do
      let out := match produces p[i]! with
        | some q => [q]
        | none => pi[i]!
      for j in succ p i do
        let merged := union pi[j]! out
        if merged.length != pi[j]!.length then
          pi := pi.set! j merged
          changed := true
  return pi

/-- (index, instruction, offending provenances). -/
def hazards (body : List AInstr) : List (Nat × String × List P) :=
  let p := body.toArray
  let pi := provIn p
  (List.range p.size).filterMap (fun i =>
    match requires p[i]! with
    | none => none
    | some req =>
      let bad := pi[i]!.filter (fun q => !req q)
      if bad.isEmpty then none else some (i, repr p[i]! |>.pretty, bad))

/-- Every body: the handlers, the gas routines, and the corpus's chunk pieces. -/
def allBodies : List (String × List AInstr) :=
  X86Alias.allBodies ++
  (match Evm.CL.ARM64.JIT.corpusChunks with
   | some cs => cs.flatMap (fun c => (X86JIT.chunkPieces .cancun c).zipIdx.map
       (fun (pc, k) => (s!"chunk{c.startPc}_piece{k}", pc)))
   | none => [])

def report : List (String × List (Nat × String × List P)) :=
  allBodies.filterMap (fun (n, b) => let h := hazards b; if h.isEmpty then none else some (n, h))

/-- **Every flag consumer meets its provenance requirement**, in every body the
    x86-64 file emits and every chunk piece of the corpus. -/
theorem no_flag_provenance_hazards : report.isEmpty = true := by native_decide

end Evm.CL.X86FlagProv
