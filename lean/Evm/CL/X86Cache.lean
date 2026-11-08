/-
  Evm.CL.X86Cache — the x86-64 stack-cache check, over the LOWERED body.

  x86-64 caches only the top stack word, in r8-r11 (the homes of x6-x9); the stack
  memory holds every word as well. A body is entered with r8-r11 = stack[sp-1] and must
  leave by every dispatch exit (`ret` — what `brCont` lowers to — and the threaded
  tail's `jmp [mem]`, and `jmp reg`) the same way for the sp it leaves (only if sp ≥ 1).
  sp is r13, a BYTE offset; the stack base is r12.

  The check walks the `XItem` list `x86Items` produces (the instructions
  `X86Sem.xstep` gives a meaning to, and `xskipTo`'s forward labels), every path
  separately, with the x86 register file. It replaced a mode of the ARM64 check
  (`OpInstrs.cacheIncoherent … true`) that read the `AInstr` body under ARM names,
  which was unsound on x86-64 five ways (`X86CacheSound.rejects_*`): registers that
  share an x86 home (x1/x15 = rdx, x2/x17 = rsi, x3/x4/x16 = rdi; a register with no
  home is written through rax), the temporaries the lowering writes (a NOS-source
  store's, `csinv`'s rax), the NOS names read as registers although x86-64 reads them
  from memory at the CURRENT sp, and `ret` (a dispatch exit on x86-64) not checked.

  A register or stack limb holds a symbolic value (`XV`): a stack limb as it was in a
  memory generation, the byte offset of a stack word (`lea d, [r13 - 32k]`), its address
  (`add d, r12`, or `[r12 + r13 + disp]`), the stack base, or the opaque result of one
  step. A call (`call [rip+slot]`, `call reg`) kills the SysV caller-saved registers
  (r8-r11 among them) and starts a new memory generation; a store through an operand
  that is not a stack address is assumed not to be the stack (`Sep`). `cmp r13, #32k ;
  jl` is the guarded reload. The check gives up where it cannot follow r13 or r12, a
  store into a stack word other than a whole-limb `mov`, or a `push` through a stack
  address. `X86CacheSound.xcacheIncoherent_sound` proves it sound against `xstep`.
-/

import Evm.CL.X86Sem

namespace Evm.CL.X86Cache

open Evm.CL.X86Encode Evm.CL.X86Items

/-- A symbolic 64-bit value. -/
inductive XV where
  | cell (g : Nat) (c : Int) (l : Nat)  -- limb l of stack word sp₀+c in memory generation g
  | idx (c : Int)                       -- the byte offset 32·(sp₀+c)
  | addr (c : Int)                      -- the address of stack word sp₀+c
  | base                                -- the stack base (r12)
  | fresh (j : Nat)                     -- what step j wrote
  | when (k : Int) (v : XV)             -- v, but only when sp₀ ≥ k (the entry cache)
  deriving DecidableEq, Repr, Inhabited

/-- One path's state: sp − sp₀ in words, the known register values, the stack limbs
    written in this memory generation (the rest hold `cell gen`), the generation, the
    known bound sp < `lt` (words), and `fl = some k` when the flags are `cmp r13, k`'s. -/
structure XCS where
  off  : Int
  regs : List (XReg × XV)
  mem  : List ((Int × Nat) × XV)
  gen  : Nat
  lt   : Option Int
  fl   : Option Int
  deriving DecidableEq, Repr, Inhabited

/-- The TOS cache, limb by limb. -/
def tosX : List XReg := [.r8, .r9, .r10, .r11]

/-- The sp-relative words the analysis names: offsets and addresses within `cwin`,
    cells within `W` (so two named words never alias modulo 2^64). -/
def cwin : Int := 65536
def W : Nat := 65538

def XCS.rv (s : XCS) (r : XReg) : Option XV :=
  if r = .r13 then some (.idx s.off) else if r = .r12 then some .base
  else (s.regs.find? (·.1 == r)).map (·.2)
def XCS.mv (s : XCS) (c : Int) (l : Nat) : XV :=
  ((s.mem.find? (·.1 == (c, l))).map (·.2)).getD (.cell s.gen c l)
def XCS.setR (s : XCS) (r : XReg) (v : Option XV) : XCS :=
  { s with regs := (match v with | some v => [(r, v)] | none => []) ++ s.regs.filter (·.1 != r) }
def XCS.setM (s : XCS) (c : Int) (l : Nat) (v : XV) : XCS :=
  { s with mem := ((c, l), v) :: s.mem.filter (·.1 != (c, l)) }

/-- At entry r8-r11 cache word sp₀-1, owed when sp₀ ≥ 1. -/
def XCS.entry : XCS :=
  { off := 0, mem := [], gen := 0, lt := none, fl := none,
    regs := tosX.zipIdx.map fun (r, l) => (r, XV.when 1 (.cell 0 (-1) l)) }

/-- The stack word c an operand's base (and index) address: the operand is
    base₀ + 32·(sp₀+c) + disp. -/
def XCS.wbase (s : XCS) (m : X86Encode.Mem) : Option Int :=
  match m.index with
  | none => match s.rv m.base with | some (.addr c) => some c | _ => none
  | some i =>
    if m.scale = 1 then
      match s.rv m.base, s.rv i with
      | some .base, some (.idx c) => some c
      | some (.idx c), some .base => some c
      | _, _ => none
    else none

/-- The named limb an operand addresses, if it is a whole limb of a named word. -/
def XCS.cellOf (s : XCS) (m : X86Encode.Mem) : Option (Int × Nat) :=
  match s.wbase m with
  | some c => if m.disp % 8 = 0 ∧ (c + m.disp / 32).natAbs ≤ W
              then some (c + m.disp / 32, (m.disp % 32 / 8).toNat) else none
  | none => none

/-- What `lea d, [m]` computes, if it is a stack word's offset or address. -/
def XCS.leaV (s : XCS) (m : X86Encode.Mem) : Option XV :=
  if m.disp % 32 ≠ 0 then none else
  match s.wbase m with
  | some c => if (c + m.disp / 32).natAbs ≤ cwin.natAbs then some (.addr (c + m.disp / 32)) else none
  | none =>
    match m.index, s.rv m.base with
    | none, some (.idx c) =>
      if (c + m.disp / 32).natAbs ≤ cwin.natAbs then some (.idx (c + m.disp / 32)) else none
    | _, _ => none

/-- `add d, a`: an offset plus the base is an address. -/
def addV (j : Nat) : Option XV → Option XV → XV
  | some (.idx c), some .base | some .base, some (.idx c) => .addr c
  | _, _ => .fresh j

/-- The register an instruction writes (named by the step), and the ones it
    clobbers besides (rsp, for `push`/`pop`). Flags and memory aside. -/
def wdst : XInsn → Option XReg
  | .movRR d _ | .movRM d _ | .movRI d _ | .shiftRI _ d _ | .imulRR d _ | .lea d _ | .cmovRR _ d _
  | .lzcnt d _ | .lzcntRM d _ | .bswap d | .notR d | .setcc _ d | .movzxB d _ | .movzxBM d _
  | .movRM32 d _ | .pop d => some d
  | .aluRR o d _ | .aluRM o d _ | .aluRI o d _ => match o with | .cmp => none | _ => some d
  | _ => none
def wkill : XInsn → List XReg
  | .push _ | .pop _ => [.rsp]
  | _ => []
def wr (i : XInsn) : List XReg := (wdst i).toList ++ wkill i

/-- The instructions that may write memory. -/
def storesX : XInsn → Bool
  | .movMR .. | .movMR8 .. | .movMI .. | .movMI32 .. | .movMR32 .. | .push _ => true
  | .aluMR o _ _ | .aluMI o _ _ => match o with | .cmp => false | _ => true
  | _ => false

/-- The operand a store writes through. -/
def storeMem : XInsn → Option X86Encode.Mem
  | .movMR m _ | .movMR8 m _ | .movMI m _ | .movMI32 m _ | .movMR32 m _ | .aluMR _ m _
  | .aluMI _ m _ => some m
  | _ => none

/-- The dispatch exits: `ret` (`brCont`), the threaded tail's `jmp [mem]`, `jmp reg`. -/
def isExit : XInsn → Bool
  | .ret | .jmpReg _ | .jmpMem _ => true
  | _ => false

def isCallI : XInsn → Bool
  | .callReg _ => true
  | _ => false

/-- The calls: `call reg`, `call [rip + slot]`, `call label`. -/
def isCallItem : XItem → Bool
  | .I (.callReg _) | .CallRip _ | .Call _ => true
  | _ => false

/-- `lea d, [rip + …]`. -/
def leaDst : XItem → Option XReg
  | .LeaRip d _ | .LeaRipSym d _ => some d
  | _ => none

/-- Items that change nothing on the edge taken: a label, a branch's fall-through. -/
def isSkip : XItem → Bool
  | .L _ | .Jcc .. | .JccSym .. => true
  | _ => false

def isBase (r : XReg) : Bool := r == .r12 || r == .r13

/-- The SysV caller-saved registers. -/
def callerSavedX : List XReg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

/-- A call: the caller-saved registers forgotten, rax named, the memory a new generation. -/
def callSt (j : Nat) (s : XCS) : XCS :=
  let t := callerSavedX.foldl (fun t r => t.setR r none) { s with fl := none }
  { t with mem := [], gen := j + 1 }.setR .rax (some (.fresh j))

/-- Any other instruction: its clobbers forgotten, its destination named. -/
def genSt (j : Nat) (i : XInsn) (s : XCS) : XCS :=
  let t := (wkill i).foldl (fun t r => t.setR r none) { s with fl := none }
  match wdst i with
  | some d => t.setR d (some (.fresh j))
  | none => t

/-- Store `r` into limb l of word c (an unknown register gets a name first). -/
def XCS.store (j : Nat) (s : XCS) (c : Int) (l : Nat) (r : XReg) : XCS :=
  match s.rv r with
  | some v => s.setM c l v
  | none => (s.setR r (some (.fresh j))).setM c l (.fresh j)

/-- sp moves by δ words. -/
def spAdj (s : XCS) (δ : Int) : Option XCS :=
  if (s.off + δ).natAbs ≤ cwin.natAbs
  then some { s with off := s.off + δ, lt := s.lt.map (· + δ), fl := none } else none

/-- The transfer of an instruction (`j` names its result); `none` where the analysis
    cannot follow (r12 or r13 written other than `add|sub r13, #32k`, a store into a
    stack word other than a whole-limb `mov`, a `push` through a stack address). -/
def xcstep (j : Nat) (i : XInsn) (s : XCS) : Option XCS :=
  let s0 : XCS := { s with fl := none }
  if (wr i).any isBase then
    match i with
    | .aluRI o d k =>
      if d = .r13 ∧ k % 32 = 0 then
        match o with
        | .add => spAdj s (k / 32)
        | .sub => spAdj s (-(k / 32))
        | _ => none
      else none
    | _ => none
  else
  let other : Option XCS :=
    if storesX i && ((storeMem i).bind s.wbase).isSome then none else some (genSt j i s)
  match i with
  | .aluRI o d k => if o = .cmp ∧ d = .r13 then some { s with fl := some k } else other
  | .lea d m => some (s0.setR d (some ((s.leaV m).getD (.fresh j))))
  | .movRR d a => some (s0.setR d (s.rv a))
  | .aluRR o d a => if o = .add then some (s0.setR d (some (addV j (s.rv d) (s.rv a)))) else other
  | .movRM d m =>
    some (s0.setR d (some (match s.cellOf m with | some (c, l) => s.mv c l | none => .fresh j)))
  | .movMR m r =>
    match s.wbase m, s.cellOf m with
    | some _, some (c, l) => some (XCS.store j s0 c l r)
    | some _, none => none
    | none, _ => some s0
  | .push _ => match s.rv .rsp with
    | some (.addr _) => none
    | _ => other
  | _ => other

/-- The state on the taken edge of `jl`: after `cmp r13, #32k`, sp < k words. -/
def takenSt (c : XCond) (s : XCS) : XCS :=
  match c, s.fl with
  | .l, some k =>
    if k % 32 = 0 ∧ (k / 32).natAbs ≤ cwin.natAbs
    then { s with lt := some (match s.lt with | some x => min x (k / 32) | none => k / 32) }
    else s
  | _, _ => s

def XV.strip : XV → XV | .when _ v => v.strip | v => v
def XV.okAt (t : Int) : XV → Bool | .when k v => k ≤ t && v.okAt t | _ => true

/-- At a dispatch exit: each TOS register equals the limb it caches, and the guards on
    both hold whenever the word is owed; or it is not owed (sp < 1). -/
def exitOk (s : XCS) : Bool :=
  s.lt.any (· ≤ 1) || tosX.zipIdx.all fun (r, l) => match s.rv r with
    | some v => v.strip == (s.mv (s.off - 1) l).strip && v.okAt (-(s.off - 1)) &&
                (s.mv (s.off - 1) l).okAt (-(s.off - 1))
    | none => false

/-- Where a branch to `l` lands, from the suffix `rest` after it: forward to the next
    `l:` (`Nf`: the next `N:`), `xskipTo`'s rule; else back to a named label's
    definition (JUMPI's `b _eita_jumpi_pop`). -/
def firstL (l : String) : List XItem → Option (List XItem)
  | [] => none
  | (.L t) :: rest => if t == l then some (.L t :: rest) else firstL l rest
  | _ :: rest => firstL l rest

def target (its rest : List XItem) (l : String) : Option (List XItem) :=
  match X86Sem.xskipTo l rest with
  | some q => some q
  | none => firstL l its

/-- A label the body defines (forward or backward). -/
def defines (its : List XItem) (l : String) : Bool :=
  its.any fun | .L t => l == t || l == t ++ "f" || l == t ++ "b" | _ => false

/-- Every path from the suffix `p`, `d` steps in: the item indices where a path fails
    (an exit that breaks the cache, an item the analysis cannot follow, falling off
    the end, a branch to a label the body defines but `target` does not resolve, out of
    fuel — the bodies are acyclic, so `length + 1` steps reach every exit).
    A branch to a label the body does not define (a trampoline) leaves it. -/
def xcwalk (its : List XItem) : Nat → Nat → List XItem → XCS → List Nat
  | 0, _, p, _ => [its.length - p.length]
  | _ + 1, _, [], _ => [its.length]
  | fuel + 1, d, it :: rest, s =>
    let here := [its.length - (rest.length + 1)]
    match it with
    | .I i =>
      if isExit i then (if exitOk s then [] else here)
      else if isCallI i then xcwalk its fuel (d + 1) rest (callSt d s)
      else match xcstep d i s with
        | some t => xcwalk its fuel (d + 1) rest t
        | none => here
    | .L _ => xcwalk its fuel (d + 1) rest s
    | .Jcc c l =>
      match target its rest l with
      | some q => xcwalk its fuel (d + 1) rest s ++ xcwalk its fuel (d + 1) q (takenSt c s)
      | none => if defines its l then here else xcwalk its fuel (d + 1) rest s
    | .Jmp l =>
      match target its rest l with
      | some q => xcwalk its fuel (d + 1) q s
      | none => if defines its l then here else []
    | .JccSym _ _ => xcwalk its fuel (d + 1) rest s
    | .JmpSym _ => []
    | .CallRip _ | .Call _ => xcwalk its fuel (d + 1) rest (callSt d s)
    | .LeaRip r _ | .LeaRipSym r _ =>
      if isBase r then here else xcwalk its fuel (d + 1) rest ({ s with fl := none }.setR r (some (.fresh d)))
    | _ => here

/-- Item indices where some path leaves the TOS cache incoherent (or the analysis lost
    it) — empty when the lowered body keeps the cache coherent. -/
def xcacheIncoherent (its : List XItem) : List Nat :=
  (xcwalk its (its.length + 1) 0 its XCS.entry).eraseDups

end Evm.CL.X86Cache
