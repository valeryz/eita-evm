#!/usr/bin/env bash
# verify-x86-interp.sh — the x86-64 threaded interpreter file assembles.
#
# `lake exe emitX86Interp` prints the whole x86-64 handlers file (frame, every
# registry handler through the x86-64 lowering, tables) in two flavours. Both
# must assemble with no «unlowered» marker: Mach-O with the Mac's clang (the
# same oracle as verify-x86-emit.sh), ELF cross-assembled for x86_64-linux-gnu
# (what libeita.so on x86-64 Linux is built from). The frame's bytes are covered by
# verify-x86-asm.sh (frame_* blocks). #238 stage 4.
set -euo pipefail
cd "$(dirname "$0")/.."
OUT="${TMPDIR:-/tmp}/eita-x86-interp"
rm -rf "$OUT"; mkdir -p "$OUT"
( cd lean && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe emitX86Interp ) > "$OUT/interp.S" 2>/dev/null
( cd lean && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe emitX86Interp elf ) > "$OUT/interp-elf.S" 2>/dev/null
if grep -q "«" "$OUT/interp.S"; then
  echo "FAIL: unlowered forms in the x86-64 interpreter:"; grep -n "«" "$OUT/interp.S" | head; exit 1
fi
clang -arch x86_64 -c "$OUT/interp.S" -o "$OUT/interp.o"
clang --target=x86_64-unknown-linux-gnu -c "$OUT/interp-elf.S" -o "$OUT/interp-elf.o"
n=$(grep -c "^_eita_handler_" "$OUT/interp.S")
echo "x86-64 interpreter assembles: $n handlers, Mach-O $(stat -f%z "$OUT/interp.o") B, ELF $(stat -f%z "$OUT/interp-elf.o") B OK"
