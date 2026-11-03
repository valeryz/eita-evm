/-
  Evm.Frontier.Vm.Instructions.Block — opcodes 0x40..0x45.

  EELS reference: ethereum/frontier/vm/instructions/block.py.

  Frontier set: BLOCKHASH, COINBASE, TIMESTAMP, NUMBER, DIFFICULTY,
  GASLIMIT. DIFFICULTY's *semantics* change at Paris (EIP-4399, returns
  PREVRANDAO); the opcode number 0x44 is unchanged.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions

namespace Evm.Frontier.Vm.Instructions

open Evm.Frontier.Vm

/-- 0x40 BLOCKHASH: hash of one of the 256 most recent ancestor blocks;
    `0` if out of range or block is the current/future.

    `env.blockHashes` is chronologically ordered (oldest first) and
    contains hashes of blocks `[current - len, current - 1]`. So the
    hash of block `n` lives at index `len - (current - n)`. -/
def blockhash : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.blockHash
  let (n, s) ← Stack.pop evm.stack
  let nN := n.toNat
  let current := evm.env.number
  let hash : Evm.U256 :=
    if nN ≥ current ∨ current - nN > 256 then 0
    else
      let len := evm.env.blockHashes.length
      let idx := len - (current - nN)
      (evm.env.blockHashes[idx]?).getD 0
  let s ← Stack.push s hash
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- 0x41 COINBASE -/
def coinbase : Handler :=
  runNullaryPush Gas.base (fun evm => Evm.U256.ofNat evm.env.coinbase.toNat)

/-- 0x42 TIMESTAMP -/
def timestamp : Handler :=
  runNullaryPush Gas.base (fun evm => Evm.U256.ofNat evm.env.timestamp)

/-- 0x43 NUMBER -/
def number : Handler :=
  runNullaryPush Gas.base (fun evm => Evm.U256.ofNat evm.env.number)

/-- 0x44 DIFFICULTY -/
def difficulty : Handler :=
  runNullaryPush Gas.base (fun evm => Evm.U256.ofNat evm.env.difficulty)

/-- 0x45 GASLIMIT -/
def gaslimit : Handler :=
  runNullaryPush Gas.base (fun evm => Evm.U256.ofNat evm.env.gasLimit)

end Evm.Frontier.Vm.Instructions
