/-
  Evm.Frontier.Vm.Instructions.Log — opcodes 0xa0..0xa4 (LOG0..LOG4).

  EELS reference: ethereum/frontier/vm/instructions/log.py.

  Gas: `375 + 375·n + 8·len` (where `n` is the number of topics) plus the
  memory-expansion cost.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions
import Evm.Frontier.Vm.Instructions.Memory

namespace Evm.Frontier.Vm.Instructions

open Evm.Frontier.Vm

private def popTopics (s : Stack) : Nat → Except Exception (List Evm.U256 × Stack)
  | 0       => return ([], s)
  | k + 1 => do
    let (t, s')  ← Stack.pop s
    let (ts, s'') ← popTopics s' k
    return (t :: ts, s'')

/-- LOGn (n ∈ 0..4). -/
def log (n : Nat) : Handler := fun evm => do
  -- EIP-214 (Byzantium+): LOG is forbidden in a static context.
  if evm.message.isStatic then
    .error .writeInStaticContext
  let (offset, len, s) ← Stack.pop2 evm.stack
  let (topics, s)      ← popTopics s n
  let off  := offset.toNat
  let lenN := len.toNat
  let cost := Gas.log + Gas.logTopic * n + Gas.logData * lenN
  let gasLeft ← Gas.charge evm.gasLeft cost
  let (gasLeft, mem) ← chargeMemory gasLeft evm.memory off lenN
  let entry : Log :=
    { address := evm.message.currentTarget, topics := topics,
      data := Memory.read mem off lenN }
  return { evm with
    gasLeft := gasLeft, memory := mem, stack := s,
    env := { evm.env with logs := evm.env.logs ++ [entry] },
    pc := evm.pc + 1 }

end Evm.Frontier.Vm.Instructions
