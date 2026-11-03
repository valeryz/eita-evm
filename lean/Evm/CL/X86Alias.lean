/-
  Evm.CL.X86Alias — aliased registers are never live together (x86-64).

  Stage 5 of #238, from the first x86-64 Linux divergence. The x86-64 register map
  gives several `Reg`s ONE home — x1/x15 → rdx, x2/x17 → rsi, x3/x4/x16 →
  rdi (`X86Items.xreg?`, marked "provisional" there) — which is sound only
  while no two of them are live at once. Three bodies broke it, all while
  staging a host callback's arguments: the CALL family loaded the gas word's
  limb 3 into x1 over limb 0 in x15 (every sub-frame on x86-64 Linux started with
  gas 0), EXTCODECOPY loaded the memory base into x16 over the context in
  x3, LOG set the topic count in x1 before using x15 as an address temporary.
  The Rosetta vectors could not see it: their fake callbacks ignore their
  arguments.

  This is the check that makes the aliasing a theorem instead of a comment:
  an exact, branch-aware liveness over each body (forward and backward local
  labels; exits end a path), and `hazards` = every instruction that writes a
  register while another register with the same home is live after it, or
  that reads two registers with the same home. `no_alias_hazards` runs it
  over every handler the x86-64 file emits and the eight gas routines.
-/

import Evm.CL.X86Interp

namespace Evm.CL.X86Alias

open Evm.CL.AsmCore Evm.CL.X86Items

instance : Inhabited AInstr := ⟨.ret⟩

/-- The registers an instruction writes. -/
def writes (i : AInstr) : List Reg :=
  match i with
  | .ldpOff r1 r2 _ _ | .ldpSp r1 r2 _ | .ldpPostSp r1 r2 _ => [r1, r2]
  | .ldpFpLr => [.x29, .x30]
  | .tstImm _ _ | .cmpReg _ _ | .cmpImm _ _ | .cmpImmWHex _ _ | .subsZr _ _ | .sbcsZr _ _ => []
  | .csel d _ _ _ | .cselZrA d _ _ | .cselZrB d _ _ | .eorImm1 d _ => [d]
  | .movFromSp r => [r]
  | .loadSymValue d _ | .loadSymGotValue d _ | .ldrLsl3 d _ _ | .movkImm d _ _ | .adrLbl d _ => [d]
  | i => match Evm.CL.OpInstrs.dest? i with | some d => [d] | none => []

/-- The registers an instruction reads: its mentions minus the first
    occurrence of each written register (a source equal to the destination
    is mentioned twice and stays). -/
def reads (i : AInstr) : List Reg :=
  let ms := match i with
    | .tstImm r _ => [r]
    | .csel d a b _ => [d, a, b]
    | .cselZrA d b _ => [d, b]
    | .cselZrB d a _ => [d, a]
    | .eorImm1 d a => [d, a]
    | .cbnzLbl r _ | .cbnzWLbl r _ => [r]
    | .movkImm d _ _ => [d, d]
    | .ldrLsl3 d b idx => [d, b, idx]
    | i => Evm.CL.Pressure.mentions i
  (writes i).foldl (fun acc w => acc.erase w) ms

/-- Where a local label reference lands: `Nf` forward, `Nb` backward, a name
    anywhere. -/
def target (p : Array AInstr) (i : Nat) (l : String) : Option Nat :=
  let isLabel (n : String) (j : Nat) : Bool :=
    match p[j]? with | some (.label m) => m == n | _ => false
  if l.endsWith "f" then
    let n := (l.dropEnd 1).toString
    (List.range (p.size - i - 1)).findSome? (fun k => if isLabel n (i + 1 + k) then some (i + 1 + k) else none)
  else if l.endsWith "b" then
    let n := (l.dropEnd 1).toString
    (List.range i).reverse.findSome? (fun j => if isLabel n j then some j else none)
  else
    (List.range p.size).findSome? (fun j => if isLabel l j then some j else none)

/-- Successors in the body. Exits (`ret`, `brCont`, symbol jumps) end the
    path; conditional symbol branches (faults) fall through on the kept path. -/
def succ (p : Array AInstr) (i : Nat) : List Nat :=
  match p[i]? with
  | none => []
  | some (.bLbl l) => (target p i l).toList
  | some (.bSymU _) | some .brCont | some .ret | some (.brReg _) | some (.bFar _) | some (.bTramp _) => []
  | some (.bcTramp _ _) => if i + 1 < p.size then [i + 1] else []
  | some (.cbzLbl _ l) | some (.cbnzLbl _ l) | some (.bcLbl _ l) | some (.blsLbl l)
  | some (.cbzWLbl _ l) | some (.cbnzWLbl _ l) =>
      -- a chunk piece may END with a conditional fault branch (`jb Lx_oog`)
      (if i + 1 < p.size then [i + 1] else []) ++ (target p i l).toList
  | some _ => if i + 1 < p.size then [i + 1] else []

def union (a b : List Reg) : List Reg := b.foldl (fun acc r => if acc.contains r then acc else r :: acc) a

/-- `liveIn` for every index, by iteration to a fixpoint. -/
def liveIn (p : Array AInstr) : Array (List Reg) := Id.run do
  let n := p.size
  let mut li : Array (List Reg) := Array.replicate n []
  let mut changed := true
  let mut fuel := n * 64 + 8
  while changed && fuel > 0 do
    changed := false
    fuel := fuel - 1
    for i in (List.range n).reverse do
      let out := (succ p i).foldl (fun acc s => union acc (li[s]!)) []
      let inn := union (reads p[i]!) (out.filter (fun r => !(writes p[i]!).contains r))
      if inn.length != li[i]!.length then
        li := li.set! i inn
        changed := true
  return li

def home (r : Reg) : Option Evm.CL.X86Encode.XReg := xreg? r

/-- Two different registers with the same home. -/
def aliased (a b : Reg) : Bool :=
  a != b && (match home a, home b with | some x, some y => x == y | _, _ => false)

/-- (index, written register, aliased register live after it), and
    (index, r, r') for an instruction reading two aliased registers. -/
def hazards (body : List AInstr) : List (Nat × Reg × Reg) :=
  let p := body.toArray
  let li := liveIn p
  (List.range p.size).flatMap (fun i =>
    let out := (succ p i).foldl (fun acc s => union acc (li[s]!)) []
    let ws := (writes p[i]!).flatMap (fun w => out.filter (fun r => aliased w r) |>.map (fun r => (i, w, r)))
    let rs := (reads p[i]!).zipIdx
    let rr := rs.flatMap (fun (a, ia) => rs.filter (fun (b, ib) => ia < ib && aliased a b) |>.map (fun (b, _) => (i, a, b)))
    -- a write and a read of two aliased registers in ONE instruction: the
    -- two-operand lowering writes the destination before it reads the second
    -- source (`add x1, x8, x15` became `mov rdx, r10 ; add rdx, rdx`)
    let wr := (writes p[i]!).flatMap (fun w => (reads p[i]!).filter (fun r => aliased w r) |>.map (fun r => (i, w, r)))
    ws ++ rr ++ wr)

/-- Every body the x86-64 file emits. -/
def allBodies : List (String × List AInstr) :=
  Evm.CL.X86Interp.handlerList.map (fun (n, suf, p) => (n, Evm.CL.X86Interp.handlerInstrs suf p)) ++
  Evm.CL.X86CallGas.routines ++ Evm.CL.X86SstoreGas.routines

/-- The report: (name, hazards) for bodies with any. -/
def report : List (String × List (Nat × Reg × Reg)) :=
  allBodies.filterMap (fun (n, b) => let h := hazards b; if h.isEmpty then none else some (n, h))

/-- **No aliased registers are live together**, in any body the x86-64 file
    emits or any gas routine. -/
theorem no_alias_hazards : report.isEmpty = true := by native_decide

end Evm.CL.X86Alias
