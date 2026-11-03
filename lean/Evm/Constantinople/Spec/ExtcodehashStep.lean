/-
  Evm.Constantinople.Spec.ExtcodehashStep — EIP-1052 EXTCODEHASH (0x3f).

  EELS reference: `forks/constantinople/vm/instructions/environment.py`
  `extcodehash`. Pops an address (truncated to 20 bytes), pushes the
  keccak256 of the queried account's code, or 0 if the account is
  empty / non-existent.

  Per EIP-1052:
    * address that doesn't exist → 0
    * account that exists but with empty code → keccak256("")
      (canonical "empty code hash"
       0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470)
    * otherwise → keccak256(code)

  EELS' `extcodehash` collapses these: it tests `EMPTY_ACCOUNT` which is
  `nonce = 0 ∧ balance = 0 ∧ code = b""`, returning 0 in that case
  (which catches both "non-existent" and "empty"). The implementation in
  `Evm.Constantinople.Vm.Instructions.Environment.extcodehash` mirrors
  this; the relation does too.

  Gas: 400 at Constantinople (EELS `GasCosts.OPCODE_EXTCODEHASH` in
  `forks/constantinople/vm/gas.py`). Istanbul re-prices this to 700
  (EIP-1884) but that's a later fork's delta — see
  `Evm.Istanbul.Spec.GasConstants`.
-/

import Evm.Frontier.Vm
import Evm.Frontier.State
import Evm.Frontier.Spec.StepShapes
import Evm.Crypto.Hash
import Evm.Constantinople.Vm.Gas

namespace Evm.Constantinople.Spec

open Evm.Frontier (State Account)
open Evm.Frontier.Vm

/-- Truncate a 256-bit stack word to a 160-bit address, matching the
    EELS `to_address` helper used at the entry of EXT* opcodes. -/
private def u256ToAddr (x : Evm.U256) : Evm.Address :=
  Evm.Address.ofNat x.toNat

/-- 0x3f EXTCODEHASH (Constantinople).

    Reads the queried account from `evm.env.state`. Empty / non-existent
    accounts yield 0; otherwise `keccak256(account.code)`. Charges 400
    gas at Constantinople. -/
def IsExtcodehashStep (evm evm' : Evm) : Prop :=
  ∃ addrW rest,
    evm.stack = addrW :: rest ∧
    rest.length < stackLimit ∧
    evm.gasLeft ≥ Evm.Constantinople.Vm.Gas.extCodeHash ∧
    let addr := u256ToAddr addrW
    let exists' := evm.env.state.accountExists addr
    let acc := evm.env.state.getAccount addr
    let codehash : Evm.U256 :=
      if ¬ exists' ∨ acc.isEmpty then 0
      else Evm.Crypto.keccak256 acc.code
    evm' = { evm with
      stack   := codehash :: rest,
      gasLeft := evm.gasLeft - Evm.Constantinople.Vm.Gas.extCodeHash,
      pc      := evm.pc + 1 }

end Evm.Constantinople.Spec
