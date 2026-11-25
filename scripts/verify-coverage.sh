#!/bin/bash
# verify-coverage.sh — the refinement-debt ratchet. Regenerates the
# coverage matrix (scripts/refinement_coverage.py) and enforces:
#   1. drift: the fresh matrix must equal the committed copy, so any
#      status change arrives as a deliberate regeneration in the PR;
#   2. budget: fresh debt (Section A SORRY+SHAPE+SHAPE-UNSUFFIXED) must
#      not exceed scripts/generated/refinement-debt-ceiling.txt. The
#      ceiling is stored SEPARATELY from the generated matrix, so
#      running the documented regeneration command can never raise it;
#      raising it is a deliberate, review-visible edit of that file.
# A new `sorry` or `_shape` placeholder therefore fails CI unless debt
# also goes down elsewhere — or the ceiling is explicitly raised.
#   3. stats drift: the per-component Lean statistics (statement / proof
#      lines, theorems, sorry, native_decide, axiom closure) written by the
#      same generator must equal scripts/generated/verification-stats.md.
set -euo pipefail
cd "$(dirname "$0")/.."

gen=scripts/generated/refinement-coverage.md
ceil=scripts/generated/refinement-debt-ceiling.txt
tmp=/tmp/_refinement_coverage.md
stats=scripts/generated/verification-stats.md
tmpstats=/tmp/_verification-stats.md

# Classification regression checks (reviewer repros, synthetic tree).
python3 scripts/refinement_coverage.py --selftest || {
  echo "FAIL: coverage selftest failed"; exit 1; }

rc=0
python3 scripts/refinement_coverage.py --stats-md "$tmpstats" > "$tmp" 2>/tmp/_coverage.err || rc=$?
if [ "$rc" -ne 0 ]; then
  echo "FAIL: refinement_coverage.py exited $rc:"; cat /tmp/_coverage.err; exit 1
fi

ceiling=$(head -1 "$ceil" | grep -oE '[0-9]+')
fresh=$(grep -oE '^Debt \(SORRY\+SHAPE\+SHAPE-UNSUFFIXED\): [0-9]+\.' "$tmp" \
          | grep -oE '[0-9]+')
if [ -z "$ceiling" ] || [ -z "$fresh" ]; then
  echo "FAIL: could not read debt ceiling ($ceil) or fresh debt total"; exit 1
fi
if [ "$fresh" -gt "$ceiling" ]; then
  echo "FAIL: debt ceiling exceeded: fresh SORRY+SHAPE+UNSUFFIXED = $fresh > ceiling $ceiling"
  echo "  regeneration alone cannot fix this; a deliberate increase requires"
  echo "  editing scripts/generated/refinement-debt-ceiling.txt in the same PR"
  exit 1
fi

regen="python3 scripts/refinement_coverage.py --stats-md $stats > $gen"
if ! diff -q "$stats" "$tmpstats" >/dev/null 2>&1; then
  echo "DRIFT: the Lean statistics changed ($stats)"
  diff "$stats" "$tmpstats" | head -30
  echo "  regenerate: $regen"
  exit 1
fi
echo "lean statistics up to date OK"

if diff -q "$gen" "$tmp" >/dev/null 2>&1; then
  echo "refinement coverage matrix up to date OK (debt $fresh/$ceiling)"
else
  echo "DRIFT: the refinement coverage matrix changed (debt $fresh/$ceiling)"
  diff "$gen" "$tmp" | head -30
  echo "  if intended: $regen"
  exit 1
fi
