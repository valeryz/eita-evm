#!/bin/bash
# verify-axioms.sh — fail if the axiom closure of the audited theorems
# drifts from the committed audit (scripts/generated/axiom-audit.txt),
# or if a banned axiom reappears (trust_smt: SMT-solver discharge, from
# the removed loom dependency). Run in CI / pre-commit.
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

build /tmp/_axiom_audit_build.log \
  Evm.IR.Soundness Evm.IR.SymExpr \
  Evm.CL.EffectBlockProof Evm.CL.EffectCallProof Evm.CL.EffectCreateProof \
  Evm.CL.EffectEndTxProof Evm.CL.EffectSelfdestructProof \
  Evm.CL.EffectSettleProof Evm.CL.EffectSloadProof Evm.CL.EffectSstoreProof \
  Evm.CL.EffectSystemProof Evm.CL.EffectTxProof \
  Evm.CL.MemExpandSpec Evm.CL.GasEmitLondon Evm.CL.GasEmitCancun \
  Evm.CL.GasEmitPrague Evm.CL.HeaderEmit Evm.CL.Flags Evm.CL.ForkEmit Evm.CL.BlobEnv \
  Evm.CL.HostEmit Evm.Arc.Spec.BlockSystem \
  Evm.CL.ARM64.SstoreGasDenote Evm.CL.ARM64.MemCommitSem \
  Evm.CL.ARM64.CallGasDenote Evm.Parallel.BlockSTM

# Print the closures (stderr captured so a Lean failure is diagnosed,
# not misreported as drift; pipefail so a broken pipe fails loudly).
rc=0
lake env lean AxiomAudit.lean 2>/tmp/_axiom_audit.err \
  | sed 's/^info: //' > /tmp/_axiom_audit.txt || rc=$?
if [ "$rc" -ne 0 ]; then
  echo "FAIL: 'lake env lean AxiomAudit.lean' exited $rc, stderr:"
  cat /tmp/_axiom_audit.err; exit 1
fi

if grep -q 'trust_smt' /tmp/_axiom_audit.txt; then
  echo "FAIL: trust_smt (SMT-solver discharge) in an audited theorem's axiom closure"
  exit 1
fi
if diff -q ../scripts/generated/axiom-audit.txt /tmp/_axiom_audit.txt >/dev/null 2>&1; then
  echo "axiom audit up to date OK"
else
  echo "DRIFT: the axiom closure of an audited theorem changed"
  diff ../scripts/generated/axiom-audit.txt /tmp/_axiom_audit.txt | head -20
  echo "  if intended: (cd lean && lake env lean AxiomAudit.lean | sed 's/^info: //' > ../scripts/generated/axiom-audit.txt)"
  exit 1
fi
