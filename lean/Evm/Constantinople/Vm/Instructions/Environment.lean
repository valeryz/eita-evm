/-
  Evm.Constantinople.Vm.Instructions.Environment — EIP-1052 EXTCODEHASH.

  EELS reference: ethereum/forks/constantinople/vm/instructions/environment.py
  line 454 (`extcodehash`).

  Semantics per EIP-1052:
    * If `address` does not exist OR is empty (per EIP-161 `is_dead`),
      push 0.
    * Otherwise push `keccak256(account.code)`.

  Note the divergence from the naive "keccak of code" reading: for EOAs
  (no code) we still push `keccak256("") = KECCAK_EMPTY`, but only
  because the account exists. A *non-existent* account pushes 0.

  Gas: 400 (Constantinople `OPCODE_EXTCODEHASH`).
-/

import Evm.BaseTypes
import Evm.Crypto.Hash
import Evm.Frontier.State
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions
import Evm.Constantinople.Vm.Gas

namespace Evm.Constantinople.Vm.Instructions

open Evm.Frontier
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

private def u256ToAddr (x : Evm.U256) : Evm.Address :=
  Evm.Address.ofNat x.toNat

/-- 0x3f EXTCODEHASH (EIP-1052). -/
def extcodehash : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Evm.Constantinople.Vm.Gas.extCodeHash
  let (addrW, s) ← Stack.pop evm.stack
  let addr := u256ToAddr addrW
  -- EELS `extcodehash` (lines 463-478):
  --   account = get_account(state, address)
  --   if account == EMPTY_ACCOUNT: codehash = U256(0)
  --   else:                        codehash = U256.from_be_bytes(account.code_hash)
  --
  -- We faithfully use the "is dead" test (account absent OR empty),
  -- matching the EIP-1052 spec (which post-dates EIP-161 and inherits
  -- its dead-account semantics).
  let acc := evm.env.state.getAccount addr
  let isPresent := evm.env.state.accountExists addr
  let dead : Bool := !isPresent || acc.isEmpty
  let result : Evm.U256 :=
    if dead then 0
    else Evm.Crypto.keccak256 acc.code
  let s ← Stack.push s result
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

end Evm.Constantinople.Vm.Instructions
