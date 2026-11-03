/-
  Evm.London.Spec.BasefeeStep — EIP-3198 BASEFEE opcode (0x48).

  EELS reference: `forks/london/vm/instructions/block.py` `basefee`.
  A degenerate nullary push: pushes `block.base_fee_per_gas` onto
  the stack and charges `GAS_BASE = 2`.

  ```
  def base_fee(evm: Evm) -> None:
      charge_gas(evm, GAS_BASE)
      push(evm.stack, U256(evm.message.block_env.base_fee_per_gas))
      evm.pc += 1
  ```

  The opcode reads `env.baseFeePerGas` (a `Nat` in our `Environment`
  since BitVec arithmetic on it isn't needed), reinterpreted as a
  `U256` via `Evm.U256.ofNat`. Reads only — no mutation outside
  stack / gas / pc.

  ## What's encoded vs glossed

  * Encoded: the push value (`env.baseFeePerGas` as U256), gas cost
    (2 = `Gas.base`), pc advance.
  * Glossed: the EIP-3198 dispatch slot. The London Vm/Effect.lean
    will route 0x48 to this; the refinement file checks the routing.
-/

import Evm.Frontier.Spec.StepShapes

namespace Evm.London.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (IsNullaryPushStep)

/-- 0x48 BASEFEE. Pushes `env.baseFeePerGas` (reinterpreted as
    `U256`); 2 gas; advance pc by 1. EELS:
    `forks/london/vm/instructions/block.py` `base_fee`. -/
abbrev IsBasefeeStep : Evm → Evm → Prop :=
  IsNullaryPushStep
    (fun evm => Evm.U256.ofNat evm.env.baseFeePerGas)
    Gas.base

end Evm.London.Spec
