/-
  Evm.Petersburg.Vm.Instructions.Environment — EIP-1052 EXTCODEHASH (0x3f).

  EELS reference: ethereum/forks/constantinople/vm/instructions/environment.py
  (function `extcodehash`). EELS has no separate Petersburg directory;
  its `constantinople` module is the EIP-1283-removed flavour our
  project labels "Petersburg".

  EIP-1052 specifies:

    * Pop one address from the stack.
    * Push `keccak256(account.code)` if the account exists, else 0.
    * EELS uses the strict `EMPTY_ACCOUNT` test — `keccak256(b"")` of an
      empty-code account is *not* 0; only non-existent accounts return 0.
    * Gas: `OPCODE_EXTCODEHASH = 400` (see constantinople/vm/gas.py).

  In our Frontier `State`, `accountExists` distinguishes the two cases
  the EIP cares about: an address present in the accounts map (even
  with empty code) hashes to `keccak256(empty)`, while an absent address
  pushes 0.
-/

import Evm.BaseTypes
import Evm.Crypto.Hash
import Evm.Frontier.State
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions

namespace Evm.Petersburg.Vm.Instructions

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

/-- EIP-1052 gas constant `OPCODE_EXTCODEHASH = 400`. EELS
    `constantinople/vm/gas.py` `GasCosts.OPCODE_EXTCODEHASH`. -/
def extcodehashGas : Nat := 400

private def u256ToAddr (x : Evm.U256) : Evm.Address :=
  Evm.Address.ofNat x.toNat

/-- 0x3f EXTCODEHASH — push keccak256 of the account's code, or 0 if
    the account does not exist.

    EELS `extcodehash` (constantinople/vm/instructions/environment.py):

      address = to_address_masked(pop(evm.stack))
      charge_gas(evm, GasCosts.OPCODE_EXTCODEHASH)
      account = get_account(state, address)
      if account == EMPTY_ACCOUNT:
        codehash = U256(0)
      else:
        codehash = U256.from_be_bytes(account.code_hash)
      push(evm.stack, codehash)

    EELS's `account == EMPTY_ACCOUNT` check returns 0 for both absent
    accounts AND present-but-empty accounts (the EIP-1052 spec text
    actually requires distinguishing these, but EELS chose the
    "is_empty" check to match EIP-161 semantics — touching an empty
    account during EXTCODEHASH is undesirable). Our Frontier `Account`
    lacks an `==` against an empty sentinel, so we use the same
    `isEmpty` predicate Spurious Dragon uses for EIP-161. -/
def extcodehash : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft extcodehashGas
  let (addrW, s) ← Stack.pop evm.stack
  let addr := u256ToAddr addrW
  let acc  := evm.env.state.getAccount addr
  let absent := ¬ evm.env.state.accountExists addr
  let hashWord : Evm.U256 :=
    if absent ∨ acc.isEmpty then 0
    else Evm.Crypto.keccak256 acc.code
  let s ← Stack.push s hashWord
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

end Evm.Petersburg.Vm.Instructions
