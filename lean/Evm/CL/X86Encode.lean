/-
  Evm.CL.X86Encode — x86-64 machine code.

  Stage 3 of #238. `Evm.CL.Lowering` emits x86-64 TEXT, which the system
  assembler accepts (`scripts/verify-x86-emit.sh`). The JIT has no assembler at
  run time, so it needs bytes, exactly as the ARM64 side has
  `AsmEncode.Insn.encode`.

  x86-64's encoding is not a bit-packing of a fixed word; it is a prefix, an
  opcode, a ModRM byte, sometimes a SIB byte, sometimes a displacement, and
  sometimes an immediate, with several special cases that are invisible in the
  assembly text. Three of them hit our register map directly:

   * **`rsp`/`r12` as a base register forces a SIB byte.** `rm = 100` is the
     escape meaning "SIB follows", so there is no way to say `[r12 + disp]`
     without one. `r12` is our stackBase.
   * **`rbp`/`r13` as a base cannot use `mod = 00`.** That encoding means
     "no base, disp32 follows", so `[r13]` must be written as `[r13 + 0]` with
     an explicit zero displacement byte. `r13` is our sp.
   * **The SIB scale is two bits** — 1, 2, 4, 8 and nothing else. This is the
     rule that refuted the first version of the NOS addressing mode (scale 32),
     and `scale_32_is_not_encodable` records it as a theorem rather than a
     comment.

  Each of those would produce code that assembles-looking-correct in text and
  wrong bytes in the arena, which is why the gate
  (`scripts/verify-x86-encode.sh`) is differential against clang, byte for byte,
  the same way `verify-asm-encode.sh` gates the ARM64 encoder.
-/

import Evm.CL.Lowering

namespace Evm.CL.X86Encode

/-! ## Registers -/

inductive XReg where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

namespace XReg

def num : XReg → Nat
  | rax => 0 | rcx => 1 | rdx => 2  | rbx => 3
  | rsp => 4 | rbp => 5 | rsi => 6  | rdi => 7
  | r8  => 8 | r9  => 9 | r10 => 10 | r11 => 11
  | r12 => 12 | r13 => 13 | r14 => 14 | r15 => 15

/-- The low three bits, which go in a ModRM or SIB field. -/
def lo (r : XReg) : Nat := r.num % 8

/-- The fourth bit, which goes in the REX prefix. -/
def hi (r : XReg) : Bool := r.num ≥ 8

def name : XReg → String
  | rax => "rax" | rcx => "rcx" | rdx => "rdx" | rbx => "rbx"
  | rsp => "rsp" | rbp => "rbp" | rsi => "rsi" | rdi => "rdi"
  | r8  => "r8"  | r9  => "r9"  | r10 => "r10" | r11 => "r11"
  | r12 => "r12" | r13 => "r13" | r14 => "r14" | r15 => "r15"

/-- The byte register. With a REX prefix present, 4-7 are spl/bpl/sil/dil. -/
def name8 : XReg → String
  | rax => "al"  | rcx => "cl"  | rdx => "dl"  | rbx => "bl"
  | rsp => "spl" | rbp => "bpl" | rsi => "sil" | rdi => "dil"
  | r8  => "r8b" | r9  => "r9b" | r10 => "r10b" | r11 => "r11b"
  | r12 => "r12b" | r13 => "r13b" | r14 => "r14b" | r15 => "r15b"

/-- The 32-bit register name. -/
def name32 : XReg → String
  | rax => "eax" | rcx => "ecx" | rdx => "edx" | rbx => "ebx"
  | rsp => "esp" | rbp => "ebp" | rsi => "esi" | rdi => "edi"
  | r8  => "r8d" | r9  => "r9d" | r10 => "r10d" | r11 => "r11d"
  | r12 => "r12d" | r13 => "r13d" | r14 => "r14d" | r15 => "r15d"

/-- Needs a SIB byte when used as a base, whatever the displacement. -/
def baseNeedsSib (r : XReg) : Bool := r.lo == 4        -- rsp, r12

/-- Cannot be encoded with `mod = 00` as a base: that bit pattern means
    "no base". -/
def baseNeedsDisp (r : XReg) : Bool := r.lo == 5        -- rbp, r13

end XReg

/-! ## Memory operands -/

/-- `[base + index*scale + disp]`. `scale` must be 1, 2, 4 or 8. -/
structure Mem where
  base  : XReg
  index : Option XReg := none
  scale : Nat := 1
  disp  : Int := 0
  deriving Repr

/-- Is this address encodable? The scale is the interesting part. -/
def Mem.ok (m : Mem) : Bool :=
  (m.scale == 1 || m.scale == 2 || m.scale == 4 || m.scale == 8) &&
  -- rsp cannot be an INDEX (index = 100 means "no index")
  (match m.index with | some i => i != .rsp | none => true)

/-- The two-bit scale field. -/
def scaleBits : Nat → Nat
  | 1 => 0 | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0

/-! ## Instructions -/

inductive AluOp where
  | add | or_ | adc | sbb | and_ | sub | xor_ | cmp
  deriving DecidableEq, Repr

namespace AluOp
/-- The `/digit` used in the ModRM `reg` field for the immediate forms, which is
    also this operation's index in the opcode table. -/
def digit : AluOp → Nat
  | add => 0 | or_ => 1 | adc => 2 | sbb => 3
  | and_ => 4 | sub => 5 | xor_ => 6 | cmp => 7

/-- `op r/m64, r64` — the "to memory/register" direction. -/
def opcodeMR (o : AluOp) : Nat := 8 * o.digit + 1
/-- `op r64, r/m64` — the "from memory/register" direction. -/
def opcodeRM (o : AluOp) : Nat := 8 * o.digit + 3

def mnem : AluOp → String
  | add => "add" | or_ => "or" | adc => "adc" | sbb => "sbb"
  | and_ => "and" | sub => "sub" | xor_ => "xor" | cmp => "cmp"
end AluOp

inductive ShiftOp where | shl | shr | sar
  deriving DecidableEq, Repr

namespace ShiftOp
def digit : ShiftOp → Nat | shl => 4 | shr => 5 | sar => 7
def mnem : ShiftOp → String | shl => "shl" | shr => "shr" | sar => "sar"
end ShiftOp

/-- Condition codes, in the architectural order, so `code` is also the low
    nibble of a `Jcc`/`CMOVcc` opcode. -/
inductive XCond where
  | o | no | b | ae | e | ne | be | a | s | ns | p | np | l | ge | le | g
  deriving DecidableEq, Repr

namespace XCond
def code : XCond → Nat
  | o => 0 | no => 1 | b => 2 | ae => 3 | e => 4 | ne => 5 | be => 6 | a => 7
  | s => 8 | ns => 9 | p => 10 | np => 11 | l => 12 | ge => 13 | le => 14 | g => 15
def mnem : XCond → String
  | o => "o" | no => "no" | b => "b" | ae => "ae" | e => "e" | ne => "ne"
  | be => "be" | a => "a" | s => "s" | ns => "ns" | p => "p" | np => "np"
  | l => "l" | ge => "ge" | le => "le" | g => "g"
end XCond

inductive XInsn where
  | movRR   (dst src : XReg)
  | movRM   (dst : XReg) (m : Mem)             -- mov dst, [m]
  | movMR   (m : Mem) (src : XReg)             -- mov [m], src
  | movRI   (dst : XReg) (imm : Int)           -- mov dst, imm32 (sign-extended)
  | aluRR   (o : AluOp) (dst src : XReg)       -- op dst, src
  | aluRM   (o : AluOp) (dst : XReg) (m : Mem) -- op dst, [m]
  | aluMR   (o : AluOp) (m : Mem) (src : XReg) -- op [m], src
  | aluRI   (o : AluOp) (dst : XReg) (imm : Int)
  | aluMI   (o : AluOp) (m : Mem) (imm : Int)  -- op qword ptr [m], imm
  | shiftRI (o : ShiftOp) (dst : XReg) (amt : Nat)
  | imulRR  (dst src : XReg)
  | lea     (dst : XReg) (m : Mem)
  | cmovRR  (c : XCond) (dst src : XReg)
  | lzcnt   (dst src : XReg)
  | lzcntRM (dst : XReg) (m : Mem)             -- lzcnt r64, qword ptr [m]
  | push    (r : XReg)
  | pop     (r : XReg)
  | jmpReg  (r : XReg)                         -- jmp r64 (FF /4)
  | callReg (r : XReg)                         -- call r64 (FF /2)
  | jmpMem  (m : Mem)                          -- jmp qword ptr [m] (FF /4)
  | bswap   (r : XReg)                         -- bswap r64 (REX.W 0F C8+r)
  | notR    (r : XReg)                         -- not r64 (F7 /2)
  | setcc   (c : XCond) (r : XReg)             -- setcc r8   (0F 90+cc /0)
  | movzxB  (dst src : XReg)                   -- movzx r64, r8 (REX.W 0F B6 /r)
  | movzxBM (dst : XReg) (m : Mem)             -- movzx r64, byte ptr [m]
  | movMR8  (m : Mem) (src : XReg)             -- mov byte ptr [m], r8
  | movMI   (m : Mem) (imm : Int)              -- mov qword ptr [m], imm32 (sign-extended)
  | movMI32 (m : Mem) (imm : Int)              -- mov dword ptr [m], imm32
  | movMR32 (m : Mem) (src : XReg)             -- mov dword ptr [m], r32
  | movRM32 (dst : XReg) (m : Mem)             -- mov r32, dword ptr [m]  (zero-extends)
  | cmpRI32 (r : XReg) (imm : Int)             -- cmp r32, imm8/imm32
  | testRI  (r : XReg) (imm : Int)             -- test r64, imm32 (REX.W F7 /0 id)
  | ret
  deriving Repr

/-! ## Encoding -/

def rex (w r x b : Bool) : UInt8 :=
  UInt8.ofNat (0x40 ||| (if w then 8 else 0) ||| (if r then 4 else 0) |||
               (if x then 2 else 0) ||| (if b then 1 else 0))

def modrm (md reg rm : Nat) : UInt8 := UInt8.ofNat ((md % 4) * 64 + (reg % 8) * 8 + (rm % 8))

def sib (sc idx base : Nat) : UInt8 := UInt8.ofNat ((sc % 4) * 64 + (idx % 8) * 8 + (base % 8))

/-- One signed byte, two's complement. `Int.toNat` is 0 on negatives, so the
    wrap has to be explicit — without it a `-48` displacement encoded as `0x00`
    and the NOS address silently read the wrong stack slot. Caught by
    `nos_or_encodes_exactly`. -/
def imm8 (i : Int) : List UInt8 :=
  [UInt8.ofNat ((if i < 0 then i + 256 else i).toNat % 256)]

/-- Four bytes, little-endian, two's complement. -/
def imm32 (i : Int) : List UInt8 :=
  let n := (if i < 0 then i + 4294967296 else i).toNat % 4294967296
  [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256),
   UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 16777216 % 256)]

/-- Eight bytes, little-endian, two's complement. -/
def imm64 (i : Int) : List UInt8 :=
  let n := (if i < 0 then i + 18446744073709551616 else i).toNat % 18446744073709551616
  (List.range 8).map (fun k => UInt8.ofNat (n / 256 ^ k % 256))

def fitsI8 (i : Int) : Bool := -128 ≤ i && i ≤ 127

/-- The `mod` field and displacement bytes for a memory operand: the smallest
    form that encodes, honouring `rbp`/`r13`'s need for an explicit zero. -/
def dispPart (m : Mem) : Nat × List UInt8 :=
  if m.disp == 0 && !m.base.baseNeedsDisp then (0, [])
  else if fitsI8 m.disp then (1, imm8 m.disp)
  else (2, imm32 m.disp)

/-- ModRM + optional SIB + displacement for `[m]`, with `reg` already chosen. -/
def memBytes (reg : Nat) (m : Mem) : List UInt8 :=
  let (md, disp) := dispPart m
  match m.index with
  | some i => modrm md reg 4 :: sib (scaleBits m.scale) i.lo m.base.lo :: disp
  | none =>
      if m.base.baseNeedsSib then
        -- no index: index field 100 means "none"
        modrm md reg 4 :: sib 0 4 m.base.lo :: disp
      else
        modrm md reg m.base.lo :: disp

/-- The REX bits a memory operand contributes: `B` from the base, `X` from the
    index. -/
def memRex (m : Mem) : Bool × Bool :=
  (m.base.hi, match m.index with | some i => i.hi | none => false)

def encode : XInsn → List UInt8
  | .movRR dst src =>
      [rex true src.hi false dst.hi, 0x89, modrm 3 src.lo dst.lo]
  | .movRM dst m =>
      let (b, x) := memRex m
      rex true dst.hi x b :: 0x8B :: memBytes dst.lo m
  | .movMR m src =>
      let (b, x) := memRex m
      rex true src.hi x b :: 0x89 :: memBytes src.lo m
  | .movRI dst imm =>
      -- Two forms, by range. `C7 /0 imm32` SIGN-extends, so it is only right
      -- for [-2^31, 2^31); anything else is `REX.W B8+r imm64` (movabs), which
      -- is also what the assembler picks for a 64-bit destination. The first
      -- version used C7 unconditionally, and a 0xFFFFFFFF sentinel came back
      -- from the hardware as -1: caught by the EXECUTION gate, not by any byte
      -- gate, because the bytes were a valid instruction — just not the one
      -- meant. (A 32-bit `mov r32, imm32` would zero-extend in 5 bytes, but
      -- clang does not choose it for `mov r64, …`, and an exact gate is worth
      -- more than one byte.)
      if -2147483648 ≤ imm && imm < 2147483648 then
        rex true false false dst.hi :: 0xC7 :: modrm 3 0 dst.lo :: imm32 imm
      else
        rex true false false dst.hi :: UInt8.ofNat (0xB8 + dst.lo) :: imm64 imm
  | .aluRR o dst src =>
      [rex true src.hi false dst.hi, UInt8.ofNat o.opcodeMR, modrm 3 src.lo dst.lo]
  | .aluRM o dst m =>
      let (b, x) := memRex m
      rex true dst.hi x b :: UInt8.ofNat o.opcodeRM :: memBytes dst.lo m
  | .aluMR o m src =>
      let (b, x) := memRex m
      rex true src.hi x b :: UInt8.ofNat o.opcodeMR :: memBytes src.lo m
  | .aluRI o dst imm =>
      if fitsI8 imm then
        rex true false false dst.hi :: 0x83 :: modrm 3 o.digit dst.lo :: imm8 imm
      else
        rex true false false dst.hi :: 0x81 :: modrm 3 o.digit dst.lo :: imm32 imm
  | .aluMI o m imm =>
      let (b, x) := memRex m
      if fitsI8 imm then
        rex true false x b :: 0x83 :: memBytes o.digit m ++ imm8 imm
      else
        rex true false x b :: 0x81 :: memBytes o.digit m ++ imm32 imm
  | .shiftRI o dst amt =>
      -- `D1 /n` is the shift-by-one form: same operation, one byte shorter, and
      -- what the assembler picks. Matching it keeps the gate exact.
      if amt == 1 then
        [rex true false false dst.hi, 0xD1, modrm 3 o.digit dst.lo]
      else
        [rex true false false dst.hi, 0xC1, modrm 3 o.digit dst.lo, UInt8.ofNat (amt % 64)]
  | .imulRR dst src =>
      [rex true dst.hi false src.hi, 0x0F, 0xAF, modrm 3 dst.lo src.lo]
  | .lea dst m =>
      let (b, x) := memRex m
      rex true dst.hi x b :: 0x8D :: memBytes dst.lo m
  | .cmovRR c dst src =>
      [rex true dst.hi false src.hi, 0x0F, UInt8.ofNat (0x40 + c.code), modrm 3 dst.lo src.lo]
  | .lzcnt dst src =>
      [0xF3, rex true dst.hi false src.hi, 0x0F, 0xBD, modrm 3 dst.lo src.lo]
  | .lzcntRM dst m =>
      let (b, x) := memRex m
      [0xF3, rex true dst.hi x b, 0x0F, 0xBD] ++ memBytes dst.lo m
  -- push/pop are 64-bit by default: no REX.W, only REX.B for r8-r15
  | .push r => (if r.hi then [0x41] else []) ++ [UInt8.ofNat (0x50 + r.lo)]
  | .pop r  => (if r.hi then [0x41] else []) ++ [UInt8.ofNat (0x58 + r.lo)]
  | .jmpReg r => (if r.hi then [0x41] else []) ++ [0xFF, modrm 3 4 r.lo]
  | .callReg r => (if r.hi then [0x41] else []) ++ [0xFF, modrm 3 2 r.lo]
  | .bswap r => [rex true false false r.hi, 0x0F, UInt8.ofNat (0xC8 + r.lo)]
  | .notR r => [rex true false false r.hi, 0xF7, modrm 3 2 r.lo]
  -- the assembler's choice for the accumulator is the short form (REX.W A9 id)
  | .testRI r i => if r == .rax then [0x48, 0xA9] ++ imm32 i
                   else [rex true false false r.hi, 0xF7, modrm 3 0 r.lo] ++ imm32 i
  -- a REX prefix is needed to name sil/dil/spl/bpl as bytes (lo ≥ 4), and for r8b+
  | .setcc c r =>
      (if r.hi || r.lo ≥ 4 then [rex false false false r.hi] else []) ++
      [0x0F, UInt8.ofNat (0x90 + c.code), modrm 3 0 r.lo]
  | .movzxB dst src => [rex true dst.hi false src.hi, 0x0F, 0xB6, modrm 3 dst.lo src.lo]
  | .movzxBM dst m =>
      let (b, x) := memRex m
      rex true dst.hi x b :: 0x0F :: 0xB6 :: memBytes dst.lo m
  | .movMI m imm =>
      let (b, x) := memRex m
      rex true false x b :: 0xC7 :: memBytes 0 m ++ imm32 imm
  | .movMI32 m imm =>
      let (b, x) := memRex m
      (if b || x then [rex false false x b] else []) ++ (0xC7 :: memBytes 0 m) ++ imm32 imm
  | .movMR32 m src =>
      let (b, x) := memRex m
      (if src.hi || b || x then [rex false src.hi x b] else []) ++ (0x89 :: memBytes src.lo m)
  | .movRM32 dst m =>
      let (b, x) := memRex m
      (if dst.hi || b || x then [rex false dst.hi x b] else []) ++ (0x8B :: memBytes dst.lo m)
  | .cmpRI32 r imm =>
      if fitsI8 imm then
        (if r.hi then [rex false false false true] else []) ++ [0x83, modrm 3 7 r.lo] ++ imm8 imm
      else
        (if r.hi then [rex false false false true] else []) ++ [0x81, modrm 3 7 r.lo] ++ imm32 imm
  | .movMR8 m src =>
      -- 88 /r; REX needed for r8b+ (B/R bits) and for sil/dil/spl/bpl (any REX)
      let (b, x) := memRex m
      (if src.hi || x || b || src.lo ≥ 4 then [rex false src.hi x b] else []) ++ (0x88 :: memBytes src.lo m)
  | .jmpMem m =>
      -- no REX.W (the operand is 64-bit by default); REX only for high regs
      let (b, x) := memRex m
      (if b || x then [rex false false x b] else []) ++ (0xFF :: memBytes 4 m)
  | .ret => [0xC3]

/-! ## Assembly text, for the differential gate -/

def Mem.asm (m : Mem) : String :=
  let b := m.base.name
  let idx := match m.index with
    | some i => if m.scale == 1 then s!" + {i.name}" else s!" + {i.name}*{m.scale}"
    | none => ""
  let d :=
    if m.disp == 0 then ""
    else if m.disp < 0 then s!" - {-m.disp}"
    else s!" + {m.disp}"
  s!"[{b}{idx}{d}]"

def asm : XInsn → String
  | .movRR dst src => s!"mov {dst.name}, {src.name}"
  | .movRM dst m   => s!"mov {dst.name}, {m.asm}"
  | .movMR m src   => s!"mov {m.asm}, {src.name}"
  | .movRI dst imm => s!"mov {dst.name}, {imm}"
  | .aluRR o dst src => s!"{o.mnem} {dst.name}, {src.name}"
  | .aluRM o dst m   => s!"{o.mnem} {dst.name}, {m.asm}"
  | .aluMR o m src   => s!"{o.mnem} {m.asm}, {src.name}"
  | .aluRI o dst imm => s!"{o.mnem} {dst.name}, {imm}"
  | .aluMI o m imm   => s!"{o.mnem} qword ptr {m.asm}, {imm}"
  | .shiftRI o dst amt => s!"{o.mnem} {dst.name}, {amt}"
  | .imulRR dst src => s!"imul {dst.name}, {src.name}"
  | .lea dst m      => s!"lea {dst.name}, {m.asm}"
  | .cmovRR c dst src => s!"cmov{c.mnem} {dst.name}, {src.name}"
  | .lzcnt dst src  => s!"lzcnt {dst.name}, {src.name}"
  | .lzcntRM dst m  => s!"lzcnt {dst.name}, qword ptr {m.asm}"
  | .push r => s!"push {r.name}"
  | .pop r  => s!"pop {r.name}"
  | .jmpReg r => s!"jmp {r.name}"
  | .callReg r => s!"call {r.name}"
  | .jmpMem m => s!"jmp qword ptr {m.asm}"
  | .bswap r => s!"bswap {r.name}"
  | .notR r => s!"not {r.name}"
  | .testRI r i => s!"test {r.name}, {i}"
  | .setcc c r => s!"set{c.mnem} {r.name8}"
  | .movzxB dst src => s!"movzx {dst.name}, {src.name8}"
  | .movzxBM dst m => s!"movzx {dst.name}, byte ptr {m.asm}"
  | .movMR8 m src => s!"mov byte ptr {m.asm}, {src.name8}"
  | .movMI m imm => s!"mov qword ptr {m.asm}, {imm}"
  | .movMI32 m imm => s!"mov dword ptr {m.asm}, {imm}"
  | .movMR32 m src => s!"mov dword ptr {m.asm}, {src.name32}"
  | .movRM32 dst m => s!"mov {dst.name32}, dword ptr {m.asm}"
  | .cmpRI32 r imm => s!"cmp {r.name32}, {imm}"
  | .ret => "ret"

/-! ## The encoding rules that the assembly text cannot show

Each of these is a byte-level fact that would be invisible in a text diff and
wrong in the arena. The reference bytes come from clang. -/

/-- Our stackBase is `r12`, whose low three bits are 100 — the ModRM escape
    meaning "SIB follows". So `[r12 + disp]` carries a SIB byte even with no
    index, and the encoder must not emit the plain form. -/
theorem r12_base_forces_sib :
    (encode (.movRM .rcx { base := .r12, disp := 48 })).length = 5 := by native_decide

/-- Whereas an ordinary base needs no SIB and is one byte shorter. -/
theorem rbx_base_has_no_sib :
    encode (.movRM .rcx { base := .rbx, disp := 56 }) = [0x48, 0x8B, 0x4B, 0x38] := by
  native_decide

/-- Our sp is `r13`, whose low bits are 101 — the pattern that means "no base"
    under `mod = 00`. So `[r13]` must carry an explicit zero displacement. -/
theorem r13_base_forces_displacement :
    (encode (.movRM .rcx { base := .r13 })).length
      = (encode (.movRM .rcx { base := .rbx })).length + 1 := by native_decide

/-- **The scale is two bits.** This is the rule that refuted the first NOS
    addressing mode; `Mem.ok` rejects anything else, so the lowering cannot ask
    for `[r12 + r13*32]` again. -/
theorem scale_32_is_not_encodable :
    (Mem.ok { base := .r12, index := some .r13, scale := 32, disp := -48 }) = false := by
  native_decide

theorem scales_1_2_4_8_are_encodable :
    ([1, 2, 4, 8].all (fun s =>
      Mem.ok { base := .r12, index := some .r13, scale := s })) = true := by native_decide

/-- `rsp` cannot be an index register — that bit pattern means "no index". -/
theorem rsp_cannot_be_an_index :
    (Mem.ok { base := .rbx, index := some .rsp }) = false := by native_decide

/-- The NOS access as the lowering actually emits it, byte for byte against
    clang: `4b 0b 4c 2c d0`. -/
theorem nos_or_encodes_exactly :
    encode (.aluRM .or_ .rcx { base := .r12, index := some .r13, disp := -48 })
      = [0x4B, 0x0B, 0x4C, 0x2C, 0xD0] := by native_decide

/-- And the `lea` with scale 2 that the small shifted adds become: `48 8d 3c 4f`. -/
theorem lea_scale2_encodes_exactly :
    encode (.lea .rdi { base := .rdi, index := some .rcx, scale := 2 })
      = [0x48, 0x8D, 0x3C, 0x4F] := by native_decide

/-- A gas charge against `r15`: REX.B is required to name the high register, and
    the immediate stays one byte. `49 83 ef 64`. -/
theorem gas_charge_encodes_exactly :
    encode (.aluRI .sub .r15 100) = [0x49, 0x83, 0xEF, 0x64] := by native_decide

/-- The two `mov r64, imm` forms by range: 7 bytes up to 2^31, 10 beyond. The
    boundary is the hazard: 2^31 − 1 sign-extends correctly, 2^31 would not. -/
theorem movRI_forms_by_range :
    (encode (.movRI .rax 2147483647)).length = 7 ∧
    (encode (.movRI .rax 2147483648)).length = 10 ∧
    (encode (.movRI .rax 4294967295)).length = 10 ∧
    (encode (.movRI .rax (-1))).length = 7 := by native_decide

/-- A shift by one uses the dedicated short form, so even the shift family is
    variable-length. -/
theorem shift_by_one_is_shorter :
    (encode (.shiftRI .shl .rcx 1)).length + 1 = (encode (.shiftRI .shl .rcx 5)).length := by
  native_decide

/-- An immediate too wide for one byte takes the four-byte form, so instructions
    are variable-length — which is why `Evm.CL.Relax` exists. -/
theorem wide_immediate_is_longer :
    (encode (.movRI .rcx 1000000)).length = 7 ∧
    (encode (.aluRI .sub .r15 100)).length = 4 := by native_decide

end Evm.CL.X86Encode
