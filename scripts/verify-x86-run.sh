#!/usr/bin/env bash
# verify-x86-run.sh — EXECUTE X86Asm output and check the results.
#
# The other x86 gates compare bytes against clang; this one runs them. Lean
# emits small programs (X86RunVectors) with arguments and the value it says
# each must return; c/x86_run.c maps the bytes and calls them; Rosetta 2 runs
# the x86-64 harness on Apple Silicon. Encoder, relaxation, addressing modes
# and flag semantics all meet the hardware here, locally, before the Linux
# box ever sees them.
set -euo pipefail
# Portable across macOS (Rosetta oracle) and Linux x86-64 (native): the
# assembler, the object's text-section name and the runner differ.
case "$(uname -s)" in
  Darwin) CLANG_X86="clang -arch x86_64"; TEXTSEC="__text"; RUNX86="arch -x86_64"; RUNNER="Rosetta" ;;
  *)      CLANG_X86="clang";              TEXTSEC=".text";  RUNX86="";             RUNNER="native $(uname -m)" ;;
esac
cd "$(dirname "$0")/.."
OUT="${TMPDIR:-/tmp}/eita-x86-run"
mkdir -p "$OUT"
# the harness links the REAL compute helpers (c/eita_compute.c) for the helper-call handlers
$CLANG_X86 -O1 -I c lean/c/x86_run.c c/eita_compute.c -o "$OUT/x86_run"
( cd lean && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe x86RunVectors ) > "$OUT/vec.tsv" 2>/dev/null
pass=0; fail=0
while IFS=$'\t' read -r name hex args expected; do
  [ -z "$name" ] && continue
  # shellcheck disable=SC2086 — args are deliberately word-split
  if got=$($RUNX86 "$OUT/x86_run" "$hex" $args 2>&1); then
    if [ "$got" = "$expected" ]; then pass=$((pass+1))
    else fail=$((fail+1)); echo "  $name: expected $expected, got $got"; fi
  else
    fail=$((fail+1)); echo "  $name: CRASHED ($got)"
  fi
done < "$OUT/vec.tsv"
echo "$pass/$((pass+fail)) x86-64 programs execute correctly under $RUNNER$([ $fail = 0 ] && echo ' OK')"
[ $fail = 0 ]
