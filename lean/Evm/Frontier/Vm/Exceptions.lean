/-
  Evm.Frontier.Vm.Exceptions — exceptional halt conditions.

  EELS reference: ethereum/frontier/vm/exceptions.py. Frontier raises:
  StackUnderflow, StackOverflow, OutOfGas, InvalidOpcode, InvalidJumpDest.
  Later forks add WriteInStaticContext (Byzantium), RevertOpcode
  (Byzantium), AddressCollision (Constantinople), etc.
-/

namespace Evm.Frontier.Vm

inductive Exception where
  | stackUnderflow
  | stackOverflow
  | outOfGas
  | invalidOpcode (op : UInt8)
  | invalidJumpDest
  /-- Modelling artefact, not a real EVM condition: the fuel parameter
      threaded through the (now total) recursive mutual block was
      exhausted. Set the top-level fuel ceiling high enough that this
      never fires for legitimate executions. -/
  | fuelExhausted
  /-- EIP-214 (Byzantium+): a state-modifying opcode (SSTORE,
      SELFDESTRUCT, LOG*, CREATE, CALL with value > 0) was attempted
      in a frame whose `message.isStatic = true`. Never fires in
      pre-Byzantium forks because `isStatic` is always false. -/
  | writeInStaticContext
  deriving Repr, DecidableEq

end Evm.Frontier.Vm
