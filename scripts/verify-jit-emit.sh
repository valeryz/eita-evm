#!/bin/bash
# Gate: the migrated JIT leaf-core emitters (Evm.CL.ARM64.JITEmit, Item lists)
# assemble byte-exact vs clang. Catches transcription typos in the String->Item
# migration (#235). The encoder/assembler themselves are gated by verify-asm-encode.sh.
set -e
# Portable: on macOS clang assembles arm64 natively; on Linux x86-64 it
# cross-assembles with -target (nothing is executed — this is a byte check).
case "$(uname -s)" in
  Darwin) CLANG_ARM="clang -arch arm64" ;;
  *)      CLANG_ARM="clang -target aarch64-linux-gnu" ;;
esac
case "$(uname -s)" in Darwin) SECTION="__text" ;; *) SECTION=".text" ;; esac
cd "$(dirname "$0")/../lean"
DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe asmEncodeVectors cores 2>/dev/null > /tmp/cores.tsv
{ echo ".text"; echo ".global _t"; echo "_t:"; cut -f2 /tmp/cores.tsv; } > /tmp/cores.s
$CLANG_ARM -c /tmp/cores.s -o /tmp/cores.o
objdump -s -j "$SECTION" /tmp/cores.o 2>/dev/null | python3 -c '
import sys,re
hexs="".join(m.group(1).replace(" ","") for l in sys.stdin if (m:=re.match(r"^ *[0-9a-f]+ ((?:[0-9a-f]{2,8} ?)+)",l)))
actual=[int(hexs[i+6:i+8]+hexs[i+4:i+6]+hexs[i+2:i+4]+hexs[i:i+2],16) for i in range(0,len(hexs),8)]
exp=[];asm=[]
for l in open("/tmp/cores.tsv"):
    w,a=l.rstrip().split("\t");exp.append(int(w));asm.append(a)
bad=[(i,s) for i,(e,a,s) in enumerate(zip(exp,actual,asm)) if e!=a]
for i,s in bad[:10]: print(f"  [{i}] {s}")
print(f"{len(exp)-len(bad)}/{len(exp)} JIT core insns byte-exact"+(" OK" if not bad else ""))
sys.exit(1 if bad else 0)
'
