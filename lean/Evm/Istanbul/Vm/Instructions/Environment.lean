/-
  Evm.Istanbul.Vm.Instructions.Environment — EIP-1884 SELFBALANCE
  (0x47) and EIP-1052 EXTCODEHASH (0x3f, Constantinople; price
  bumped at Istanbul).

  EELS reference: `forks/istanbul/vm/instructions/environment.py`
  functions `self_balance` (line 484) and `extcodehash` (line 454).

  SELFBALANCE pushes the current contract's balance, charging
  `FAST_STEP` (5 gas). Cheaper than `BALANCE address` because no
  account-state walk is needed.

  EXTCODEHASH pushes `keccak256(code)` of the queried account, or 0
  if the account doesn't exist (per EIP-1052). At Istanbul the cost
  rose to 700 (was 400 in Constantinople / Petersburg).
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions
import Evm.Crypto.Hash
import Evm.Istanbul.Vm.Gas

namespace Evm.Istanbul.Vm.Instructions

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

private def u256ToAddr (x : Evm.U256) : Evm.Address :=
  Evm.Address.ofNat x.toNat

/-- 0x47 SELFBALANCE — push the balance of the currently-executing
    contract. EELS `self_balance` lines 494-506:
        charge_gas(evm, GasCosts.FAST_STEP)
        balance = get_account(state, evm.message.current_target).balance
        push(stack, balance)
    Gas: 5 (FAST_STEP). -/
def selfbalance : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Evm.Istanbul.Vm.Gas.selfBalance
  let bal := evm.env.state.getBalance evm.message.currentTarget
  let s ← Stack.push evm.stack bal
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- 0x3f EXTCODEHASH — push `keccak256(code(addr))`. EELS `extcodehash`
    lines 464-478:
        address = to_address_masked(pop(evm.stack))
        charge_gas(evm, GasCosts.OPCODE_EXTCODEHASH)
        account = get_account(state, address)
        if account == EMPTY_ACCOUNT: codehash = U256(0)
        else: codehash = U256.from_be_bytes(account.code_hash)
    Gas: 700 at Istanbul (was 400 at Constantinople, EIP-1884
    re-priced it).

    EELS quirk we mirror: the "is the account empty?" check uses
    EELS' `EMPTY_ACCOUNT` test, which combines `nonce = 0 ∧ balance =
    0 ∧ code = b""`. An empty account hashes to 0; a non-existent
    account also returns 0 here (per EIP-1052). -/
def extcodehash : Handler := fun evm => do
  let (addrW, s) ← Stack.pop evm.stack
  let gasLeft ← Gas.charge evm.gasLeft Evm.Istanbul.Vm.Gas.extCodeHash
  let addr := u256ToAddr addrW
  let exists' := evm.env.state.accountExists addr
  let acc := evm.env.state.getAccount addr
  let codehash : Evm.U256 :=
    if ¬ exists' ∨ acc.isEmpty then 0
    else Evm.Crypto.keccak256 acc.code
  let s ← Stack.push s codehash
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

end Evm.Istanbul.Vm.Instructions
