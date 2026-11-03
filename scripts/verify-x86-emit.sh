#!/usr/bin/env bash
# verify-x86-emit.sh — assemble the x86-64 lowering of every structured gadget.
#
# The Lean side (Evm.CL.Lowering) proves COVERAGE: no gadget emits an
# «unlowered» marker. It cannot know whether what it emitted is encodable x86 —
# and the first version was not: `[r12 + r13*32 - 48]` has a SIB scale of 32,
# which x86 does not have. This gate is the assembler's opinion, which is the
# authority on that question.
#
# Mirrors scripts/verify-asm-encode.sh, which does the same for ARM64.
set -euo pipefail
# Portable across macOS (Rosetta oracle) and Linux x86-64 (native): the
# assembler, the object's text-section name and the runner differ.
case "$(uname -s)" in
  Darwin) CLANG_X86="clang -arch x86_64"; TEXTSEC="__text"; RUNX86="arch -x86_64" ;;
  *)      CLANG_X86="clang";              TEXTSEC=".text";  RUNX86="" ;;
esac
cd "$(dirname "$0")/.."
OUT="${TMPDIR:-/tmp}/eita-x86-gadgets"
mkdir -p "$OUT"
( cd lean && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe emitX86 ) > "$OUT/gadgets.s"
$CLANG_X86 -c -x assembler "$OUT/gadgets.s" -o "$OUT/gadgets.o"
N=$(grep -c '^\.globl' "$OUT/gadgets.s")
I=$(grep -cE '^\s{4}[a-z]' "$OUT/gadgets.s")
# every «unlowered» marker would also be an assembler error, but say it plainly
if grep -q '«' "$OUT/gadgets.s"; then
  echo "FAIL: unlowered instruction in the emitted x86" >&2
  grep -n '«' "$OUT/gadgets.s" >&2
  exit 1
fi
echo "$N/6 x86-64 gadgets assemble OK ($I instructions)"
