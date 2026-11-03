/-!
# Evm.CL.AsmEncode — ARM64 instruction IR with `encode` (machine code) + `asm` (text)

The chunk JIT (`Evm.CL.ARM64.JIT`) and the handlers (`Evm.CL.AsmCore`) currently
emit ARM64 as *strings* that an external `clang` assembles+links. For in-process
JIT (#235) we need the *bytes* directly. This module is the shared foundation:
one `Insn` per ARM64 instruction with two interpretations —

  * `Insn.encode : Insn → UInt32`  — the fixed 32-bit machine encoding
  * `Insn.asm    : Insn → String`  — the assembler text (for cross-checking)

Differential gate: `lake exe asmEncodeVectors` prints `<asm>\t<hex>` for a
battery of instructions; a script assembles the `<asm>` and checks the bytes
equal `<hex>`. So a wrong encoding is caught against the real assembler, exactly
like `audit-call-gas` checks the gas plan against the Lean oracle.

Registers are `Nat` 0..31; 31 means XZR in data-processing slots and SP in
the base of loads/stores (ARM64 reuses the same field — the caller picks).
ARM64 is little-endian; the 4 bytes of `encode` go out low-first.
-/
namespace Evm.CL.AsmEncode

/-- A condition code (the `b.<c>` / `cset`/`csel` suffix). -/
inductive Cond where
  | eq | ne | cs | cc | mi | pl | vs | vc | hi | ls | ge | lt | gt | le | al
  deriving Repr, DecidableEq

def Cond.code : Cond → Nat
  | .eq => 0 | .ne => 1 | .cs => 2 | .cc => 3
  | .mi => 4 | .pl => 5 | .vs => 6 | .vc => 7
  | .hi => 8 | .ls => 9 | .ge => 10 | .lt => 11
  | .gt => 12 | .le => 13 | .al => 14

def Cond.mnem : Cond → String
  | .eq => "eq" | .ne => "ne" | .cs => "cs" | .cc => "cc"
  | .mi => "mi" | .pl => "pl" | .vs => "vs" | .vc => "vc"
  | .hi => "hi" | .ls => "ls" | .ge => "ge" | .lt => "lt"
  | .gt => "gt" | .le => "le" | .al => "al"
  /-- `hs`/`lo` are aliases of `cs`/`cc`. -/
def Cond.ofString : String → Option Cond
  | "eq" => some .eq | "ne" => some .ne
  | "cs" => some .cs | "hs" => some .cs
  | "cc" => some .cc | "lo" => some .cc
  | "mi" => some .mi | "pl" => some .pl | "vs" => some .vs | "vc" => some .vc
  | "hi" => some .hi | "ls" => some .ls | "ge" => some .ge | "lt" => some .lt
  | "gt" => some .gt | "le" => some .le | "al" => some .al
  | _ => none

/-- Logical/arith register-form operation selector. -/
inductive RegOp where
  | add | sub | adds | subs        -- arithmetic (shifted register)
  | adc | sbc | adcs | sbcs        -- with carry
  | and | orr | eor | ands         -- logical (shifted register)
  deriving Repr, DecidableEq

/-- The instruction IR. Only the forms the emitters use. All 64-bit (`x`) unless
    noted; byte loads/stores use `w`/`b`. -/
inductive Insn where
  /-- `movz xd, #imm16, lsl #(16*hw)` -/
  | movz   (rd : Nat) (imm16 : Nat) (hw : Nat)
  | movzW  (rd : Nat) (imm16 : Nat)         -- movz wd, #imm16 (32-bit)
  /-- `movk xd, #imm16, lsl #(16*hw)` -/
  | movk   (rd : Nat) (imm16 : Nat) (hw : Nat)
  /-- `mov xd, xn` (ORR xd, xzr, xn) -/
  | movReg (rd rn : Nat)
  /-- `add/sub xd, xn, #imm12 [, lsl #12]` -/
  | addImm (sub : Bool) (setFlags : Bool) (rd rn : Nat) (imm12 : Nat) (lsl12 : Bool)
  /-- arith/logical register form: `op xd, xn, xm {, lsl #amt}` -/
  | reg    (op : RegOp) (rd rn rm : Nat) (lslAmt : Nat)
  /-- `mvn xd, xm` (ORN xd, xzr, xm) -/
  | mvn    (rd rm : Nat)
  /-- `lsl/lsr xd, xn, #sh` (UBFM) -/
  | lslImm (rd rn sh : Nat)
  | lsrImm (rd rn sh : Nat)
  /-- `lsl/lsr xd, xn, xm` (variable) -/
  | lslReg (rd rn rm : Nat)
  | lsrReg (rd rn rm : Nat)
  /-- `rev xd, xn` -/
  | rev    (rd rn : Nat)
  /-- `clz xd, xn` — count leading zeros -/
  | clz    (rd rn : Nat)
  /-- `mul xd, xn, xm` / `madd xd, xn, xm, xa` -/
  | madd   (rd rn rm ra : Nat)
  /-- `cmp xn, #imm12` (SUBS xzr) -/
  | cmpImm (rn : Nat) (imm12 : Nat)
  | cmpImmW (rn : Nat) (imm12 : Nat)        -- cmp wn, #imm12 (32-bit)
  /-- `cmp xn, xm` (SUBS xzr) -/
  | cmpReg (rn rm : Nat)
  /-- `cset xd, cond` -/
  | cset   (rd : Nat) (c : Cond)
  /-- `csel xd, xn, xm, cond` -/
  | csel   (rd rn rm : Nat) (c : Cond)
  /-- `csinv xd, xn, xm, cond` -/
  | csinv  (rd rn rm : Nat) (c : Cond)
  /-- `ldr/str xt, [xn, #imm]` (imm in BYTES; scaled by 8) -/
  | ldr    (rt rn : Nat) (imm : Nat)
  | str    (rt rn : Nat) (imm : Nat)
  -- 32-bit forms (stage 4q: the frame bodies' flag words)
  | ldrW   (rt rn : Nat) (imm : Nat)       -- ldr wt, [xn, #imm]   (imm = 4·k)
  | strW   (rt rn : Nat) (imm : Nat)       -- str wt, [xn, #imm]
  | andMask (rd rn k : Nat)                -- and xd, xn, #(2^k − 1), 1 ≤ k ≤ 63
  | eorMask (rd rn k : Nat)                -- eor xd, xn, #(2^k − 1)
  | tstBit  (rn p : Nat)                   -- tst xn, #(2^p)   (ands xzr, xn, #imm)
  /-- `ldrb/strb wt, [xn, #imm]` (imm in bytes, unscaled) -/
  | ldrb   (rt rn : Nat) (imm : Nat)
  | strb   (rt rn : Nat) (imm : Nat)
  /-- `ldr xt, [xn, xm, lsl #amt]` (amt 0 or 3) -/
  | ldrReg (rt rn rm : Nat) (lsl3 : Bool)
  /-- `ldrb wt, [xn, xm]` -/
  | ldrbReg (rt rn rm : Nat)
  /-- `strb wt, [xn, xm]` -/
  | strbReg (rt rn rm : Nat)
  /-- `ldp/stp xt, xt2, [xn, #imm]` (imm in bytes, signed, scaled by 8) -/
  | ldp    (rt rt2 rn : Nat) (imm : Int)
  | stp    (rt rt2 rn : Nat) (imm : Int)
  /-- `stp xt, xt2, [xn, #imm]!` (pre-index, writeback) -/
  | stpPre  (rt rt2 rn : Nat) (imm : Int)
  /-- `ldp xt, xt2, [xn], #imm` (post-index, writeback) -/
  | ldpPost (rt rt2 rn : Nat) (imm : Int)
  /-- `add xd, xn, xm, lsr #sh` (LSR-shifted register operand) -/
  | addLsrReg (rd rn rm sh : Nat)
  /-- `add/sub xd|sp, xn|sp, xm` — EXTENDED-register form (uxtx), the only add/sub
      that can read/write SP. rd/rn = 31 means SP here (not XZR). -/
  | addExtReg (sub : Bool) (rd rn rm : Nat)
  /-- `br/blr xn` ; `ret` -/
  | br     (rn : Nat)
  | blr    (rn : Nat)
  | ret
  /-- PC-relative branches; `off` is the BYTE displacement from this instruction
      (target = pc + off). The assembler fills these from label/symbol positions. -/
  | bImm    (off : Int)
  | blImm   (off : Int)
  | bcondImm (c : Cond) (off : Int)
  | cbzImm  (rt : Nat) (off : Int)
  | cbnzImm (rt : Nat) (off : Int)
  | cbzImmW  (rt : Nat) (off : Int)        -- cbz  wt, off
  | cbnzImmW (rt : Nat) (off : Int)        -- cbnz wt, off
  /-- `adrp xd, <page>` — `pageOff` is (page(target) - page(pc)) i.e. already
      >>12; split into immlo(2)+immhi(19). Resolved per-relocation at load. -/
  | adrpImm (rd : Nat) (pageOff : Int)
  /-- `adr xd, <label>` — `off` is the signed BYTE displacement (target = pc+off,
      ±1MB). Same immlo(2)/immhi(19) split as adrp but NOT page-scaled. -/
  | adrImm  (rd : Nat) (off : Int)
  /-- raw 32-bit word (escape hatch for anything not yet modelled) -/
  | raw    (w : UInt32)
  deriving Repr

open Insn

/-! ## Bit-field helpers -/

private def m (n : Nat) (width : Nat) : UInt32 :=
  (UInt32.ofNat n) &&& ((1 <<< width.toUInt32) - 1)

/-- imm scaled & masked to a field (used for the byte/word offsets). -/
private def field (n : Nat) (shift : Nat) (width : Nat) : UInt32 :=
  (m n width) <<< shift.toUInt32

/-- signed 7-bit immediate (LDP/STP), already divided by the scale. Take the mod
    BEFORE toNat — `Int.toNat` of a negative is 0, which would drop the sign. -/
private def s7 (i : Int) : UInt32 :=
  UInt32.ofNat (((i % 128 + 128) % 128).toNat)   -- two's-complement low 7 bits

/-- two's-complement low `bits` of a signed Int, as UInt32. -/
private def simm (i : Int) (bits : Nat) : UInt32 :=
  let p : Int := 2 ^ bits
  UInt32.ofNat (((i % p + p) % p).toNat)

/-! ## Encoding -/

def regBase : RegOp → UInt32
  | .add  => 0x8B000000 | .sub  => 0xCB000000
  | .adds => 0xAB000000 | .subs => 0xEB000000
  | .adc  => 0x9A000000 | .sbc  => 0xDA000000
  | .adcs => 0xBA000000 | .sbcs => 0xFA000000
  | .and  => 0x8A000000 | .orr  => 0xAA000000
  | .eor  => 0xCA000000 | .ands => 0xEA000000

def RegOp.isCarry : RegOp → Bool
  | .adc | .sbc | .adcs | .sbcs => true | _ => false

def Insn.encode : Insn → UInt32
  | movz rd imm hw  => 0xD2800000 ||| field hw 21 2 ||| field imm 5 16 ||| m rd 5
  | movzW rd imm    => 0x52800000 ||| field imm 5 16 ||| m rd 5
  | movk rd imm hw  => 0xF2800000 ||| field hw 21 2 ||| field imm 5 16 ||| m rd 5
  | movReg rd rn    => 0xAA0003E0 ||| field rn 16 5 ||| m rd 5        -- ORR rd,xzr,rn
  | addImm sub sf rd rn imm sh =>
      (if sub then (if sf then 0xF1000000 else 0xD1000000)
              else (if sf then 0xB1000000 else 0x91000000))
        ||| (if sh then 0x400000 else 0) ||| field imm 10 12 ||| field rn 5 5 ||| m rd 5
  | reg op rd rn rm amt =>
      -- carry forms have no shift field
      regBase op ||| field rm 16 5
        ||| (if op.isCarry then 0 else field amt 10 6) ||| field rn 5 5 ||| m rd 5
  | mvn rd rm       => 0xAA2003E0 ||| field rm 16 5 ||| m rd 5        -- ORN rd,xzr,rm
  | lslImm rd rn sh =>
      0xD3400000 ||| field ((64 - sh) % 64) 16 6 ||| field (63 - sh) 10 6 ||| field rn 5 5 ||| m rd 5
  | lsrImm rd rn sh =>
      0xD3400000 ||| field sh 16 6 ||| field 63 10 6 ||| field rn 5 5 ||| m rd 5
  | lslReg rd rn rm => 0x9AC02000 ||| field rm 16 5 ||| field rn 5 5 ||| m rd 5
  | lsrReg rd rn rm => 0x9AC02400 ||| field rm 16 5 ||| field rn 5 5 ||| m rd 5
  | rev rd rn       => 0xDAC00C00 ||| field rn 5 5 ||| m rd 5
  | clz rd rn       => 0xDAC01000 ||| field rn 5 5 ||| m rd 5
  | madd rd rn rm ra => 0x9B000000 ||| field rm 16 5 ||| field ra 10 5 ||| field rn 5 5 ||| m rd 5
  | cmpImm rn imm   => 0xF100001F ||| field imm 10 12 ||| field rn 5 5    -- SUBS xzr,rn,#imm
  | cmpImmW rn imm  => 0x7100001F ||| field imm 10 12 ||| field rn 5 5    -- SUBS wzr,wn,#imm
  | cmpReg rn rm    => 0xEB00001F ||| field rm 16 5 ||| field rn 5 5      -- SUBS xzr,rn,rm
  | cset rd c       => 0x9A9F07E0 ||| field (Nat.xor (Cond.code c) 1) 12 4 ||| m rd 5  -- CSINC rd,xzr,xzr,!c
  | csel rd rn rm c => 0x9A800000 ||| field rm 16 5 ||| field (Cond.code c) 12 4 ||| field rn 5 5 ||| m rd 5
  | csinv rd rn rm c => 0xDA800000 ||| field rm 16 5 ||| field (Cond.code c) 12 4 ||| field rn 5 5 ||| m rd 5
  | ldr rt rn imm   => 0xF9400000 ||| field (imm / 8) 10 12 ||| field rn 5 5 ||| m rt 5
  | str rt rn imm   => 0xF9000000 ||| field (imm / 8) 10 12 ||| field rn 5 5 ||| m rt 5
  | ldrW rt rn imm  => 0xB9400000 ||| field (imm / 4) 10 12 ||| field rn 5 5 ||| m rt 5
  | strW rt rn imm  => 0xB9000000 ||| field (imm / 4) 10 12 ||| field rn 5 5 ||| m rt 5
  -- logical immediate, 64-bit element (N = 1), immr = 0, imms = k − 1
  | andMask rd rn k => 0x92400000 ||| field (k - 1) 10 6 ||| field rn 5 5 ||| m rd 5
  | eorMask rd rn k => 0xD2400000 ||| field (k - 1) 10 6 ||| field rn 5 5 ||| m rd 5
  -- a single bit at p: element 64, immr = (64 − p) mod 64, imms = 0
  | tstBit rn p     => 0xF240001F ||| field ((64 - p) % 64) 16 6 ||| field rn 5 5
  | ldrb rt rn imm  => 0x39400000 ||| field imm 10 12 ||| field rn 5 5 ||| m rt 5
  | strb rt rn imm  => 0x39000000 ||| field imm 10 12 ||| field rn 5 5 ||| m rt 5
  | ldrReg rt rn rm lsl3 =>
      0xF8606800 ||| field rm 16 5 ||| (if lsl3 then (0x1000 : UInt32) else 0) ||| field rn 5 5 ||| m rt 5
  | ldrbReg rt rn rm => 0x38606800 ||| field rm 16 5 ||| field rn 5 5 ||| m rt 5
  | strbReg rt rn rm => 0x38206800 ||| field rm 16 5 ||| field rn 5 5 ||| m rt 5
  | ldp rt rt2 rn imm => 0xA9400000 ||| ((s7 (imm / 8)) <<< (15 : UInt32)) ||| field rt2 10 5 ||| field rn 5 5 ||| m rt 5
  | stp rt rt2 rn imm => 0xA9000000 ||| ((s7 (imm / 8)) <<< (15 : UInt32)) ||| field rt2 10 5 ||| field rn 5 5 ||| m rt 5
  | stpPre rt rt2 rn imm  => 0xA9800000 ||| ((s7 (imm / 8)) <<< (15 : UInt32)) ||| field rt2 10 5 ||| field rn 5 5 ||| m rt 5
  | ldpPost rt rt2 rn imm => 0xA8C00000 ||| ((s7 (imm / 8)) <<< (15 : UInt32)) ||| field rt2 10 5 ||| field rn 5 5 ||| m rt 5
  | addLsrReg rd rn rm sh => 0x8B400000 ||| field rm 16 5 ||| field sh 10 6 ||| field rn 5 5 ||| m rd 5
  | addExtReg sub rd rn rm =>
      (if sub then 0xCB200000 else 0x8B200000)   -- ADD/SUB extended register, UXTX
        ||| field rm 16 5 ||| field 3 13 3 ||| field rn 5 5 ||| m rd 5
  | br rn           => 0xD61F0000 ||| field rn 5 5
  | blr rn          => 0xD63F0000 ||| field rn 5 5
  | ret             => 0xD65F03C0
  | bImm off        => 0x14000000 ||| (simm (off / 4) 26)
  | blImm off       => 0x94000000 ||| (simm (off / 4) 26)
  | bcondImm c off  => 0x54000000 ||| ((simm (off / 4) 19) <<< (5 : UInt32)) ||| UInt32.ofNat (Cond.code c)
  | cbzImm rt off   => 0xB4000000 ||| ((simm (off / 4) 19) <<< (5 : UInt32)) ||| m rt 5
  | cbnzImm rt off  => 0xB5000000 ||| ((simm (off / 4) 19) <<< (5 : UInt32)) ||| m rt 5
  | cbzImmW rt off  => 0x34000000 ||| ((simm (off / 4) 19) <<< (5 : UInt32)) ||| m rt 5
  | cbnzImmW rt off => 0x35000000 ||| ((simm (off / 4) 19) <<< (5 : UInt32)) ||| m rt 5
  | adrpImm rd poff => 0x90000000 ||| ((simm poff 2) <<< (29 : UInt32))
                         ||| ((simm (poff / 4) 19) <<< (5 : UInt32)) ||| m rd 5
  | adrImm rd off   =>
      -- decompose the 21-bit two's-complement byte offset robustly (floor, not
      -- truncating, shift): take the low 21 bits then split immlo/immhi.
      let v := simm off 21
      0x10000000 ||| ((v &&& 3) <<< (29 : UInt32))
        ||| (((v >>> (2 : UInt32)) &&& 0x7ffff) <<< (5 : UInt32)) ||| m rd 5
  | raw w           => w

/-! ## Assembler text (for cross-check) -/

/-- clang PC-relative displacement: `.+N` / `.-N`. -/
private def disp (off : Int) : String :=
  if off < 0 then s!".{off}" else s!".+{off}"

private def X (n : Nat) : String := if n == 31 then "xzr" else s!"x{n}"
private def Xsp (n : Nat) : String := if n == 31 then "sp" else s!"x{n}"
private def W (n : Nat) : String := if n == 31 then "wzr" else s!"w{n}"

def RegOp.mnem : RegOp → String
  | .add => "add" | .sub => "sub" | .adds => "adds" | .subs => "subs"
  | .adc => "adc" | .sbc => "sbc" | .adcs => "adcs" | .sbcs => "sbcs"
  | .and => "and" | .orr => "orr" | .eor => "eor" | .ands => "ands"

def Insn.asm : Insn → String
  | movz rd imm hw  => s!"movz {X rd}, #{imm}" ++ (if hw == 0 then "" else s!", lsl #{16*hw}")
  | movzW rd imm    => s!"movz {W rd}, #{imm}"
  | movk rd imm hw  => s!"movk {X rd}, #{imm}" ++ (if hw == 0 then "" else s!", lsl #{16*hw}")
  | movReg rd rn    => s!"mov {X rd}, {X rn}"
  | addImm sub sf rd rn imm sh =>
      let mn := (if sub then "sub" else "add") ++ (if sf then "s" else "")
      -- non-flag form: rd=31 is SP; flag form (adds/subs): rd=31 is xzr.
      let rdS := if sf then X rd else Xsp rd
      s!"{mn} {rdS}, {Xsp rn}, #{imm}" ++ (if sh then ", lsl #12" else "")
  | reg op rd rn rm amt =>
      s!"{op.mnem} {X rd}, {X rn}, {X rm}" ++ (if op.isCarry || amt == 0 then "" else s!", lsl #{amt}")
  | mvn rd rm       => s!"mvn {X rd}, {X rm}"
  | lslImm rd rn sh => s!"lsl {X rd}, {X rn}, #{sh}"
  | lsrImm rd rn sh => s!"lsr {X rd}, {X rn}, #{sh}"
  | lslReg rd rn rm => s!"lsl {X rd}, {X rn}, {X rm}"
  | lsrReg rd rn rm => s!"lsr {X rd}, {X rn}, {X rm}"
  | rev rd rn       => s!"rev {X rd}, {X rn}"
  | clz rd rn       => s!"clz {X rd}, {X rn}"
  | madd rd rn rm ra => if ra == 31 then s!"mul {X rd}, {X rn}, {X rm}"
                        else s!"madd {X rd}, {X rn}, {X rm}, {X ra}"
  | cmpImm rn imm   => s!"cmp {Xsp rn}, #{imm}"
  | cmpImmW rn imm  => s!"cmp {W rn}, #{imm}"
  | cmpReg rn rm    => s!"cmp {X rn}, {X rm}"
  | cset rd c       => s!"cset {X rd}, {c.mnem}"
  | csel rd rn rm c => s!"csel {X rd}, {X rn}, {X rm}, {c.mnem}"
  | csinv rd rn rm c => s!"csinv {X rd}, {X rn}, {X rm}, {c.mnem}"
  | ldr rt rn imm   => if imm == 0 then s!"ldr {X rt}, [{Xsp rn}]" else s!"ldr {X rt}, [{Xsp rn}, #{imm}]"
  | str rt rn imm   => if imm == 0 then s!"str {X rt}, [{Xsp rn}]" else s!"str {X rt}, [{Xsp rn}, #{imm}]"
  | ldrW rt rn imm  => if imm == 0 then s!"ldr {W rt}, [{Xsp rn}]" else s!"ldr {W rt}, [{Xsp rn}, #{imm}]"
  | strW rt rn imm  => if imm == 0 then s!"str {W rt}, [{Xsp rn}]" else s!"str {W rt}, [{Xsp rn}, #{imm}]"
  | andMask rd rn k => s!"and {X rd}, {X rn}, #0x{String.ofList (Nat.toDigits 16 (2 ^ k - 1))}"
  | eorMask rd rn k => s!"eor {X rd}, {X rn}, #{2 ^ k - 1}"
  | tstBit rn p     => s!"tst {X rn}, #{2 ^ p}"
  | ldrb rt rn imm  => if imm == 0 then s!"ldrb {W rt}, [{Xsp rn}]" else s!"ldrb {W rt}, [{Xsp rn}, #{imm}]"
  | strb rt rn imm  => if imm == 0 then s!"strb {W rt}, [{Xsp rn}]" else s!"strb {W rt}, [{Xsp rn}, #{imm}]"
  | ldrReg rt rn rm lsl3 => s!"ldr {X rt}, [{Xsp rn}, {X rm}" ++ (if lsl3 then ", lsl #3]" else "]")
  | ldrbReg rt rn rm => s!"ldrb {W rt}, [{Xsp rn}, {X rm}]"
  | strbReg rt rn rm => s!"strb {W rt}, [{Xsp rn}, {X rm}]"
  | ldp rt rt2 rn imm => if imm == 0 then s!"ldp {X rt}, {X rt2}, [{Xsp rn}]" else s!"ldp {X rt}, {X rt2}, [{Xsp rn}, #{imm}]"
  | stp rt rt2 rn imm => if imm == 0 then s!"stp {X rt}, {X rt2}, [{Xsp rn}]" else s!"stp {X rt}, {X rt2}, [{Xsp rn}, #{imm}]"
  | stpPre rt rt2 rn imm  => s!"stp {X rt}, {X rt2}, [{Xsp rn}, #{imm}]!"
  | ldpPost rt rt2 rn imm => s!"ldp {X rt}, {X rt2}, [{Xsp rn}], #{imm}"
  | addLsrReg rd rn rm sh => s!"add {X rd}, {X rn}, {X rm}, lsr #{sh}"
  | addExtReg sub rd rn rm =>
      let mn := if sub then "sub" else "add"
      s!"{mn} {Xsp rd}, {Xsp rn}, {X rm}"
  | br rn           => s!"br {X rn}"
  | blr rn          => s!"blr {X rn}"
  | ret             => "ret"
  | bImm off        => s!"b {disp off}"
  | blImm off       => s!"bl {disp off}"
  | bcondImm c off  => s!"b.{c.mnem} {disp off}"
  | cbzImm rt off   => s!"cbz {X rt}, {disp off}"
  | cbnzImm rt off  => s!"cbnz {X rt}, {disp off}"
  | cbzImmW rt off  => s!"cbz {W rt}, {disp off}"
  | cbnzImmW rt off => s!"cbnz {W rt}, {disp off}"
  | adrpImm rd poff => s!"adrp {X rd}, {disp (poff * 4096)}"
  | adrImm rd off   => s!"adr {X rd}, {disp off}"
  | raw w           => s!".inst 0x{String.ofList (Nat.toDigits 16 w.toNat)}"

/-- Little-endian bytes of an instruction. -/
def Insn.bytes (i : Insn) : List UInt8 :=
  let w := i.encode
  [ (w &&& 0xff).toUInt8,
    ((w >>> 8) &&& 0xff).toUInt8,
    ((w >>> 16) &&& 0xff).toUInt8,
    ((w >>> 24) &&& 0xff).toUInt8 ]

def Insn.bytesBA (i : Insn) : ByteArray := ⟨i.bytes.toArray⟩

/-! ## Program assembler: labels + relocations

A chunk is a `List Item` — instructions, label markers, and branches to a *name*
that is either a LOCAL label (resolved here to a PC-relative offset) or an
EXTERNAL symbol (deferred to a `Reloc` the loader patches after `dlsym`). Two
passes: lay out byte offsets / collect labels, then encode. -/

inductive RelocKind where
  | b26    -- b / bl  (imm26, bits 0..25)
  | b19    -- b.cond / cbz / cbnz (imm19, bits 5..23)
  | adrp   -- adrp page (immlo bits 29..30, immhi bits 5..23)
  | adr    -- adr local (immlo bits 29..30, immhi bits 5..23, byte off)
  | movabs -- 4 consecutive movz/movk: loader ORs the symbol addr's 4 halfwords
  deriving Repr, DecidableEq

/-- Patch the instruction word at `byteOff` so its branch/adrp field reaches the
    runtime address of `sym`. Emitted as a placeholder (field 0) by `assemble`. -/
structure Reloc where
  sym     : String
  byteOff : Nat
  kind    : RelocKind
  deriving Repr

/-- The 4 placeholder `movz`/`movk` words an `AbsSym`/`BrSym`/`BlSym` lowers to;
    the loader ORs the symbol's runtime-address halfwords into the imm16 fields.
    `rd` is already encoded, so the loader only needs the `movabs` offset. -/
def absSymInsns (rd : Nat) : List Insn :=
  [Insn.movz rd 0 0, Insn.movk rd 0 1, Insn.movk rd 0 2, Insn.movk rd 0 3]

inductive Item where
  | I    (i : Insn)                  -- a fixed instruction
  | L    (name : String)             -- label marker (0 bytes)
  | B    (target : String)           -- b   to local label or external symbol
  | Bc   (c : Cond) (target : String)-- b.<c> to local label
  | Cbz  (rt : Nat) (target : String)
  | Cbnz (rt : Nat) (target : String)
  | CbzW  (rt : Nat) (target : String)   -- 32-bit test
  | CbnzW (rt : Nat) (target : String)
  | Bl   (sym : String)              -- bl  external symbol
  | Adrp (rd : Nat) (sym : String)   -- adrp external symbol
  -- in-process lowerings (no linker / no GOT): materialize an absolute address
  -- with movz/movk and branch indirect, robust to any image distance.
  | Adr    (rd : Nat) (target : String)  -- adr to LOCAL label (PC-relative)
  | AbsSym (rd : Nat) (sym : String)     -- rd ← &sym  (4 movs + movabs reloc)
  | BrSym  (sym : String)                -- x16 ← &sym; br  x16   (tail to external)
  | BlSym  (sym : String)                -- x16 ← &sym; blr x16   (call external)
  deriving Repr

namespace Item

/-- Bytes contributed by an item before resolution (labels: 0; all else: 4). -/
def width : Item → Nat
  | .L _ => 0
  | .AbsSym _ _ => 16
  | .BrSym _ | .BlSym _ => 20
  | _ => 4

/-- Pass 1: byte offset of each label. -/
def labelMap (items : List Item) : List (String × Nat) :=
  (items.foldl (fun (acc : List (String × Nat) × Nat) it =>
      match it with
      | .L name => (acc.1 ++ [(name, acc.2)], acc.2)
      | _       => (acc.1, acc.2 + it.width))
    ([], 0)).1

end Item

/-- Assemble a program: little-endian machine bytes + the external relocations.
    A branch/adrp whose target is a known local label is resolved to a
    PC-relative offset; otherwise it is emitted with a zero field and recorded as
    a `Reloc` for the loader to patch (after `dlsym`). -/
def assemble (items : List Item) : ByteArray × List Reloc := Id.run do
  let labels := Item.labelMap items
  let mut off : Nat := 0
  let mut out : ByteArray := ByteArray.empty
  let mut relocs : List Reloc := []
  let put := fun (ba : ByteArray) (b : ByteArray) => ba ++ b
  for it in items do
    match it with
    | .L _ => pure ()
    | .I i => out := put out i.bytesBA; off := off + 4
    | .B target =>
        match labels.lookup target with
        | some t => out := put out (Insn.bImm (Int.ofNat t - Int.ofNat off)).bytesBA
        | none   => out := put out (Insn.bImm 0).bytesBA
                    relocs := relocs ++ [⟨target, off, .b26⟩]
        off := off + 4
    | .Bc c target =>
        match labels.lookup target with
        | some t => out := put out (Insn.bcondImm c (Int.ofNat t - Int.ofNat off)).bytesBA
        | none   => out := put out (Insn.bcondImm c 0).bytesBA
                    relocs := relocs ++ [⟨target, off, .b19⟩]
        off := off + 4
    | .Cbz rt target =>
        match labels.lookup target with
        | some t => out := put out (Insn.cbzImm rt (Int.ofNat t - Int.ofNat off)).bytesBA
        | none   => out := put out (Insn.cbzImm rt 0).bytesBA
                    relocs := relocs ++ [⟨target, off, .b19⟩]
        off := off + 4
    | .Cbnz rt target =>
        match labels.lookup target with
        | some t => out := put out (Insn.cbnzImm rt (Int.ofNat t - Int.ofNat off)).bytesBA
        | none   => out := put out (Insn.cbnzImm rt 0).bytesBA
                    relocs := relocs ++ [⟨target, off, .b19⟩]
        off := off + 4
    | .CbzW rt target =>
        match labels.lookup target with
        | some t => out := put out (Insn.cbzImmW rt (Int.ofNat t - Int.ofNat off)).bytesBA
        | none   => out := put out (Insn.cbzImmW rt 0).bytesBA
                    relocs := relocs ++ [⟨target, off, .b19⟩]
        off := off + 4
    | .CbnzW rt target =>
        match labels.lookup target with
        | some t => out := put out (Insn.cbnzImmW rt (Int.ofNat t - Int.ofNat off)).bytesBA
        | none   => out := put out (Insn.cbnzImmW rt 0).bytesBA
                    relocs := relocs ++ [⟨target, off, .b19⟩]
        off := off + 4
    | .Bl sym => out := put out (Insn.blImm 0).bytesBA
                 relocs := relocs ++ [⟨sym, off, .b26⟩]; off := off + 4
    | .Adrp rd sym => out := put out (Insn.adrpImm rd 0).bytesBA
                      relocs := relocs ++ [⟨sym, off, .adrp⟩]; off := off + 4
    | .Adr rd target =>
        match labels.lookup target with
        | some t => out := put out (Insn.adrImm rd (Int.ofNat t - Int.ofNat off)).bytesBA
        | none   => out := put out (Insn.adrImm rd 0).bytesBA
                    relocs := relocs ++ [⟨target, off, .adr⟩]
        off := off + 4
    | .AbsSym rd sym =>
        for ins in absSymInsns rd do out := put out ins.bytesBA
        relocs := relocs ++ [⟨sym, off, .movabs⟩]; off := off + 16
    | .BrSym sym =>
        for ins in absSymInsns 16 do out := put out ins.bytesBA
        relocs := relocs ++ [⟨sym, off, .movabs⟩]
        out := put out (Insn.br 16).bytesBA; off := off + 20
    | .BlSym sym =>
        for ins in absSymInsns 16 do out := put out ins.bytesBA
        relocs := relocs ++ [⟨sym, off, .movabs⟩]
        out := put out (Insn.blr 16).bytesBA; off := off + 20
  (out, relocs)

end Evm.CL.AsmEncode
