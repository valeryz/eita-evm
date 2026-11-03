/-
  Evm.Petersburg.Spec.SstoreStep — Petersburg reverts EIP-1283.

  Petersburg is "Constantinople with EIP-1283 removed": the SSTORE
  opcode at 0x55 is metered the *same* way it was at Byzantium /
  Spurious Dragon / Tangerine Whistle / Homestead / Frontier — the
  pre-1283 two-bucket schedule

      old == 0, new != 0  → 20000 gas (sSet)
      otherwise           → 5000 gas (sReset)
      old != 0, new == 0  → additionally refund 15000 (sClearRefund)

  This is exactly `Evm.Frontier.Spec.IsSstoreStep` — the gas table
  hasn't been touched in the intervening forks (Homestead, Tangerine
  Whistle, Spurious Dragon, Byzantium make no changes to the SSTORE
  schedule; TW only re-prices SLOAD).

  ## Historical note
  EELS master has no `forks/petersburg/` directory: the maintainers
  fold Petersburg's semantics into `forks/constantinople/` (the
  flavour they keep is the post-revert one). Our Lean layout keeps
  the two forks distinct so the EIP-1283 decision tree can be
  inspected on its own at `Evm.Constantinople.Spec.IsSstoreStep`.

  ## Why an `abbrev`
  Per the fork-delta methodology (`Evm/SPEC-METHODOLOGY.md`), the
  relation for an opcode is whatever the *latest* fork in the
  lineage that re-defines it says. Petersburg re-defining SSTORE to
  Frontier's relation is the cleanest expression of "we reverted".
  The corresponding `Vm/Effect.lean` for Petersburg routes 0x55 to
  Byzantium's `doSstore` yield, which implements the same schedule.
-/

import Evm.Frontier.Spec.StorageStep

namespace Evm.Petersburg.Spec

/-- 0x55 SSTORE under Petersburg — identical to Frontier's relation
    (which has not been re-priced through any pre-Petersburg fork).
    See file docstring for the rationale. -/
abbrev IsSstoreStep := Evm.Frontier.Spec.IsSstoreStep

end Evm.Petersburg.Spec
