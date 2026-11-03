#!/usr/bin/env bash
# verify-x86-encode.sh — differential gate: Evm.CL.X86Encode.encode vs clang.
#
# The Lean encoder emits `<hex bytes>\t<asm text>`; this assembles the text
# column for x86-64 and requires the bytes to match. x86 instructions are
# variable-length, so the comparison is byte-sequence against byte-sequence
# rather than word against word (cf. verify-asm-encode.sh for ARM64, where
# every instruction is exactly four bytes).
#
# This is the gate that knows the things assembly text cannot show: that an
# r12 base forces a SIB byte, that an r13 base forces a displacement, that the
# SIB scale is 1/2/4/8 only, and that a negative displacement is two's
# complement (which the first version of the encoder got wrong — Int.toNat is
# 0 on negatives, so -48 encoded as 0x00).
set -euo pipefail
# Portable across macOS (Rosetta oracle) and Linux x86-64 (native): the
# assembler, the object's text-section name and the runner differ.
case "$(uname -s)" in
  Darwin) CLANG_X86="clang -arch x86_64"; TEXTSEC="__text"; RUNX86="arch -x86_64" ;;
  *)      CLANG_X86="clang";              TEXTSEC=".text";  RUNX86="" ;;
esac
cd "$(dirname "$0")/.."
OUT="${TMPDIR:-/tmp}/eita-x86-encode"
mkdir -p "$OUT"
( cd lean && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe x86EncodeVectors ) > "$OUT/vec.tsv" 2>/dev/null
{ echo ".text"; echo ".intel_syntax noprefix"; echo ".globl _t"; echo "_t:";
  cut -f2 "$OUT/vec.tsv"; } > "$OUT/vec.s"
$CLANG_X86 -c -x assembler "$OUT/vec.s" -o "$OUT/vec.o"
# The whole __text section as one hex string (a disassembly listing wraps
# 10-byte instructions onto a second line and a per-line parser loses bytes;
# the section dump cannot). Ours is split back into instructions by the
# encoder's own lengths, so a mismatch is still reported per instruction.
objdump -s -j "$TEXTSEC" "$OUT/vec.o" \
  | sed -nE 's/^ *[0-9a-f]+ (([0-9a-f]{2,8} ?)+).*/\1/p' | tr -d ' \n' > "$OUT/clang.hex"
VEC="$OUT/vec.tsv" CLANG="$OUT/clang.hex" python3 -c '
import os,sys
exp=[];asm=[]
for l in open(os.environ["VEC"]):
    h,a=l.rstrip("\n").split("\t");exp.append(h);asm.append(a)
clang=open(os.environ["CLANG"]).read().strip()
pos=0;bad=[]
for i,(e,a) in enumerate(zip(exp,asm)):
    got=clang[pos:pos+len(e)]
    if got!=e: bad.append((i,a,e,got))
    pos+=len(e)
if pos!=len(clang): print(f"LENGTH MISMATCH: clang {len(clang)//2}B vs encode {pos//2}B")
for i,s,e,a in bad[:12]: print(f"  [{i}] {s}: encode={e} clang={a}")
ok = not bad and pos==len(clang)
print(f"{len(exp)-len(bad)}/{len(exp)} x86-64 encodings match clang"+(" OK" if ok else ""))
sys.exit(0 if ok else 1)
'
