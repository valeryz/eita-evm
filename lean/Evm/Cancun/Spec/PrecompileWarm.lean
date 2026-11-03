/-
  Evm.Cancun.Spec.PrecompileWarm — EIP-4844 KZG precompile (0x0a) is
  in the EIP-2929 warm-seed at Cancun.

  EELS reference: at Cancun, `process_transaction` seeds the access
  list with precompiles 0x01..0x0a (one more than Berlin's 0x01..0x09).
  The KZG `point_evaluation` precompile lives at 0x0a; a contract
  doing `SD(0x0a)` or `CALL(0x0a)` at Cancun pays the 100-gas warm
  surcharge, not the 2600-gas cold surcharge.

  Reverse condition (verified below): pre-Cancun forks STOP at 0x09.
  Pre-Cancun, address 0x0a is just an EOA placeholder and is cold on
  first access. The tx level warms `Evm.Frontier.Vm.Tx.precompileAddrs`
  (Prague adds 0x0b..0x11, EIP-2537; Osaka 0x100, EIP-7951).
-/

import Evm.BaseTypes
import Evm.Forks

namespace Evm.Cancun.Spec

/-- The KZG point-evaluation precompile address (the one Cancun adds). -/
def kzgPrecompileAddr : Evm.Address := Evm.Address.ofNat 0x0a

/-- The pre-warmed precompile address list at a given fork —
    derived from `List.range count` the same way
    `Evm.Frontier.Vm.Tx.precompileAddrs` builds it. -/
def precompileWarmList (count : Nat) : List Evm.Address :=
  (List.range count).map (fun i => Evm.Address.ofNat (i + 1))

/-- Number of pre-warmed precompiles at a given fork.
    Byzantium adds 0x05..0x08 (Bn256 + modexp); Istanbul adds 0x09
    (Blake2f); Cancun adds 0x0a (KZG point-evaluation). -/
def precompileCountAt (f : Evm.Fork) : Nat :=
  if f.atLeast .cancun     then 10
  else if f.atLeast .istanbul then 9
  else if f.atLeast .byzantium then 8
  else 4   -- Frontier..Spurious Dragon: ecRecover, SHA256, RIPEMD160, identity.

/-! ## Fork-conditional iff for KZG (0x0a) -/

theorem kzg_warm_iff_cancun (f : Evm.Fork) :
    (precompileWarmList (precompileCountAt f)).contains kzgPrecompileAddr ↔
      f.atLeast .cancun := by
  -- The KZG byte (0x0a = 10) appears in `range n` iff n ≥ 10 iff
  -- f is Cancun-or-later by the `precompileCountAt` table. The
  -- four `if`-branches all decide.
  unfold precompileCountAt precompileWarmList kzgPrecompileAddr
  cases f <;> decide

end Evm.Cancun.Spec
