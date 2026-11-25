#!/bin/bash
# verify-velvet-slots.sh — the native slot table (c/world_slots_emit.c) is the Velvet package's
# output, byte for byte, and every proof behind it checks:
#   1. builds verify/velvet-slots/ (its own Lake package: Velvet, on core's toolchain): every
#      prove_correct and lemma; the printer;
#   2. the main theorems' axioms (Slots/Axioms.lean) are only propext, Classical.choice, Quot.sound;
#   3. the printer's negative tests (PrinterNeg.lean) still fail as expected;
#   4. re-emits c/world_slots_emit.c from the methods (Slots/Emit.lean): it must equal the
#      committed file.
# The emitted C itself: `make -C c test_world_slots test_world_slots_model` and c/cbmc/run.sh.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root/verify/velvet-slots" || exit 2
log=${TMPDIR:-/tmp}/_velvet_slots.log
run() { "$@" >"$log" 2>&1 || { echo "FAIL: $* (log tail):"; tail -40 "$log"; exit 1; }; }

run lake build Slots Slots.CPrint
run lake env lean Slots/Axioms.lean
n=$(grep -c '^#print axioms' Slots/Axioms.lean)
[ "$(grep -cE 'depends on axioms|does not depend on any axioms' "$log")" = "$n" ] ||
  { echo "FAIL: Slots/Axioms.lean: not one answer per #print axioms"; cat "$log"; exit 1; }
bad=$(grep 'depends on axioms' "$log" | sed 's/.*depends on axioms: \[//; s/\]$//' | tr ',' '\n' |
      tr -d ' ' | grep -vxE 'propext|Classical\.choice|Quot\.sound' | sort -u)
[ -z "$bad" ] || { echo "FAIL: non-standard axioms: $bad"; exit 1; }
run lake env lean PrinterNeg.lean
run lake env lean Slots/Emit.lean
git -C "$root" diff --quiet -- c/world_slots_emit.c ||
  { echo "FAIL: c/world_slots_emit.c re-emitted differs (git diff -- c/world_slots_emit.c)"; exit 1; }
echo "velvet-slots OK: $n theorems on the standard axioms; c/world_slots_emit.c = the printer's output"
