/-
  Evm.Paris.Spec.PrevrandaoStep — EIP-4399 PREVRANDAO opcode (0x44).

  EELS reference: `forks/paris/vm/instructions/block.py` `prev_randao`.
  Replaces the Frontier-through-GrayGlacier DIFFICULTY opcode at the
  same opcode byte (0x44). The push value is now
  `block_env.prev_randao` (a 32-byte beacon-chain random) reinterpreted
  as a U256. Gas cost is unchanged at `GAS_BASE = 2`.

  ```
  def prev_randao(evm: Evm) -> None:
      charge_gas(evm, GAS_BASE)
      push(evm.stack, U256.from_be_bytes(evm.message.block_env.prev_randao))
      evm.pc += 1
  ```

  Our `Environment` carries `prevRandao : Hash32` (= `BitVec 256`),
  which is bitvec-equivalent to a U256. Reinterpreting via a no-op
  cast.

  ## What's encoded vs glossed

  * Encoded: the push value (`env.prevRandao` cast to U256), gas
    cost (2), pc advance.
  * Glossed: the opcode-byte dispatch (0x44). Handled at the Vm
    layer.
-/

import Evm.Frontier.Spec.StepShapes

namespace Evm.Paris.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (IsNullaryPushStep)

/-- 0x44 PREVRANDAO (was DIFFICULTY). Pushes `env.prevRandao`
    reinterpreted as a `U256`; 2 gas; advance pc by 1. EELS:
    `forks/paris/vm/instructions/block.py` `prev_randao`.

    The reinterpretation `Hash32 → U256` is a no-op cast: both are
    `BitVec 256`, identical bit pattern. -/
abbrev IsPrevrandaoStep : Evm → Evm → Prop :=
  IsNullaryPushStep
    (fun evm => evm.env.prevRandao)
    Gas.base

end Evm.Paris.Spec
