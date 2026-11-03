#!/bin/bash
# Differential gate: Evm.CL.AsmEncode.encode vs the system assembler.
# Emits a battery of instructions as <encode-hex>\t<asm>, assembles the asm
# column, and checks the machine words equal the encode column.
set -e
# Portable: on macOS clang assembles arm64 natively; on Linux x86-64 it
# cross-assembles with -target (nothing is executed — this is a byte check).
case "$(uname -s)" in
  Darwin) CLANG_ARM="clang -arch arm64" ;;
  *)      CLANG_ARM="clang -target aarch64-linux-gnu" ;;
esac
case "$(uname -s)" in Darwin) SECTION="__text" ;; *) SECTION=".text" ;; esac
cd "$(dirname "$0")/../lean"
DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe asmEncodeVectors 2>/dev/null > /tmp/asmvec.tsv
{ echo ".text"; echo ".global _t"; echo "_t:"; cut -f2 /tmp/asmvec.tsv; } > /tmp/asmvec.s
$CLANG_ARM -c /tmp/asmvec.s -o /tmp/asmvec.o
SECTION=$SECTION python3 -c '
import re,subprocess,sys,os
SECTION=os.environ["SECTION"]
sec=subprocess.run(["objdump","-s","-j",SECTION,"/tmp/asmvec.o"],capture_output=True,text=True).stdout
hexs="".join(m.group(1).replace(" ","") for ln in sec.splitlines() if (m:=re.match(r"^ *[0-9a-f]+ ((?:[0-9a-f]{2,8} ?)+)",ln)))
actual=[int(hexs[i+6:i+8]+hexs[i+4:i+6]+hexs[i+2:i+4]+hexs[i:i+2],16) for i in range(0,len(hexs),8)]
exp=[];asm=[]
for ln in open("/tmp/asmvec.tsv"):
    w,a=ln.rstrip().split("\t");exp.append(int(w));asm.append(a)
if len(actual)!=len(exp): print(f"COUNT MISMATCH {len(actual)} vs {len(exp)}");sys.exit(1)
bad=[(i,s,e,a) for i,(e,a,s) in enumerate(zip(exp,actual,asm)) if e!=a]
for i,s,e,a in bad: print(f"  [{i}] {s}: encode={e:08x} asm={a:08x}")
print(f"{len(exp)-len(bad)}/{len(exp)} match"+(" OK" if not bad else ""))
sys.exit(1 if bad else 0)
'
