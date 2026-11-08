#!/bin/bash
# verify-axioms.sh — fail if the axiom closure of the audited theorems
# drifts from the committed audit (scripts/generated/axiom-audit.txt),
# or if a banned axiom reappears (trust_smt: SMT-solver discharge, from
# the removed loom dependency), or if a native_decide proof runs one of the
# spec's @[extern] / @[implemented_by] constants (the extern rule at the end
# of AxiomAudit.lean: it errors, naming theorem and path). Run in CI / pre-commit.
#
# Every fallible command prints its captured log on failure — a red gate
# must show a diagnosis (the silent-exit class fixed in
# verify-host-emit.sh; PR #44 review item 1).
set -euo pipefail
cd "$(dirname "$0")/../lean"

build() {
  local log="$1"; shift
  local rc=0
  lake build "$@" >"$log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "FAIL: lake build $* (exit $rc), log tail:"; tail -40 "$log"; exit 1
  fi
}

# The modules AxiomAudit.lean imports (one list: its import lines).
build /tmp/_axiom_audit_build.log $(sed -n 's/^import //p' AxiomAudit.lean)

# Print the closures (stderr captured so a Lean failure is diagnosed,
# not misreported as drift; pipefail so a broken pipe fails loudly).
rc=0
lake env lean AxiomAudit.lean 2>/tmp/_axiom_audit.err \
  | sed 's/^info: //' > /tmp/_axiom_audit.out || rc=$?
if [ "$rc" -ne 0 ]; then
  echo "FAIL: 'lake env lean AxiomAudit.lean' exited $rc:"
  grep -A40 'error' /tmp/_axiom_audit.out | head -80
  cat /tmp/_axiom_audit.err; exit 1
fi
# the extern rule's verdict is not part of the baseline (its count moves with every new native_decide)
grep '^extern rule OK' /tmp/_axiom_audit.out || { echo "FAIL: no extern rule verdict"; exit 1; }
grep -v '^extern rule OK' /tmp/_axiom_audit.out > /tmp/_axiom_audit.txt

if grep -q 'trust_smt' /tmp/_axiom_audit.txt; then
  echo "FAIL: trust_smt (SMT-solver discharge) in an audited theorem's axiom closure"
  exit 1
fi
if diff -q ../scripts/generated/axiom-audit.txt /tmp/_axiom_audit.txt >/dev/null 2>&1; then
  echo "axiom audit up to date OK"
else
  echo "DRIFT: the axiom closure of an audited theorem changed"
  diff ../scripts/generated/axiom-audit.txt /tmp/_axiom_audit.txt | head -20
  echo "  if intended: (cd lean && lake env lean AxiomAudit.lean | sed 's/^info: //' | grep -v '^extern rule OK' > ../scripts/generated/axiom-audit.txt)"
  exit 1
fi
