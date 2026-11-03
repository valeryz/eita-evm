/-
  Evm.Frontier.Spec.StateStep — BALANCE / EXTCODESIZE / EXTCODECOPY /
  BLOCKHASH / LOG0-4 specs.

  These five read (or append to) the environment rather than the
  frame-local stack/memory alone:
    - BALANCE / EXTCODESIZE / EXTCODECOPY read other accounts' state.
    - BLOCKHASH reads the ancestor-hash window.
    - LOG-n appends to the transaction's log list.

  SLOAD / SSTORE live in `StorageStep.lean`. In the Effect track all
  of these yield mid-instruction and are resolved by `handleYield`
  purely from the frame's own env; the spec describes the composed
  yield + resume as one atomic step, exactly like every other
  `IsAnyStep` arm.
-/

import Evm.Frontier.Spec.MemStep
import Evm.Frontier.State

namespace Evm.Frontier.Spec

open Evm.Frontier (State)
open Evm.Frontier.Vm

/-! ## BALANCE (0x31)

    Charge `balance` (= 20 at Frontier), pop address word, push the
    balance of that account (zero for absent accounts). -/

def IsBalanceStep (evm evm' : Evm) : Prop :=
  ∃ addrW rest,
    evm.stack = addrW :: rest ∧
    rest.length < stackLimit ∧
    evm.gasLeft ≥ Gas.balance ∧
    let v := evm.env.state.getBalance (Evm.Address.ofNat addrW.toNat)
    evm' = { evm with
      stack   := v :: rest,
      gasLeft := evm.gasLeft - Gas.balance,
      pc      := evm.pc + 1 }

/-! ## EXTCODESIZE (0x3b)

    Charge `extCode` (= 20 at Frontier), pop address word, push the
    code size of that account (zero for absent accounts). -/

def IsExtcodesizeStep (evm evm' : Evm) : Prop :=
  ∃ addrW rest,
    evm.stack = addrW :: rest ∧
    rest.length < stackLimit ∧
    evm.gasLeft ≥ Gas.extCode ∧
    let sz := (evm.env.state.getAccount (Evm.Address.ofNat addrW.toNat)).code.size
    evm' = { evm with
      stack   := Evm.U256.ofNat sz :: rest,
      gasLeft := evm.gasLeft - Gas.extCode,
      pc      := evm.pc + 1 }

/-! ## EXTCODECOPY (0x3c)

    Pop address, dest-offset, code-offset, length; charge
    `extCode + 3·⌈len/32⌉ + memExpansion(dest, len)`; expand memory;
    write the zero-padded slice of the TARGET account's code at
    `dest`. The only copy op whose source is another account. -/

def IsExtcodecopyStep (evm evm' : Evm) : Prop :=
  ∃ addrW memOff codeOff size rest,
    evm.stack = addrW :: memOff :: codeOff :: size :: rest ∧
    let memOffN := memOff.toNat
    let sizeN   := size.toNat
    let totalGas := Gas.extCode + Gas.copy * ((sizeN + 31) / 32)
                      + memExpansionGas evm.memory memOffN sizeN
    evm.gasLeft ≥ totalGas ∧
    let code := (evm.env.state.getAccount (Evm.Address.ofNat addrW.toNat)).code
    let mem' := Memory.write (memAfterExpand evm.memory memOffN sizeN) memOffN
                  (Evm.Bytes.sliceZeroPad code codeOff.toNat sizeN)
    evm' = { evm with
      stack   := rest,
      memory  := mem',
      gasLeft := evm.gasLeft - totalGas,
      pc      := evm.pc + 1 }

/-! ## BLOCKHASH (0x40)

    Charge `blockHash` (= 20 at Frontier), pop block number, push the
    hash of that ancestor block — or zero when the number is the
    current block or newer, or more than 256 blocks back.
    `env.blockHashes` holds the most recent ancestors, oldest first;
    index `len - (current - n)` selects the requested one. -/

def IsBlockhashStep (evm evm' : Evm) : Prop :=
  ∃ n rest,
    evm.stack = n :: rest ∧
    rest.length < stackLimit ∧
    evm.gasLeft ≥ Gas.blockHash ∧
    let nN   := (n : Evm.U256).toNat
    let curN := evm.env.number
    let h : Evm.Hash32 :=
      if nN ≥ curN ∨ curN - nN > 256 then 0
      else
        let len := evm.env.blockHashes.length
        let idx := len - (curN - nN)
        (evm.env.blockHashes[idx]?).getD 0
    evm' = { evm with
      stack   := h :: rest,
      gasLeft := evm.gasLeft - Gas.blockHash,
      pc      := evm.pc + 1 }

/-! ## LOG0-4 (0xa0-0xa4)

    Pop offset, length, then `n` topics; charge
    `log + logTopic·n + logData·len + memExpansion(off, len)`;
    expand memory; append a Log record carrying `currentTarget`,
    the topics (in stack order), and the memory slice. -/

def IsLogStep (n : Nat) (evm evm' : Evm) : Prop :=
  ∃ offset len topics rest,
    evm.stack = offset :: len :: (topics ++ rest) ∧
    topics.length = n ∧
    let off  := (offset : Evm.U256).toNat
    let lenN := (len : Evm.U256).toNat
    let totalGas := Gas.log + Gas.logTopic * n + Gas.logData * lenN
                      + memExpansionGas evm.memory off lenN
    evm.gasLeft ≥ totalGas ∧
    let mem' := memAfterExpand evm.memory off lenN
    let entry : Log :=
      { address := evm.message.currentTarget, topics := topics,
        data := Memory.read mem' off lenN }
    evm' = { evm with
      stack   := rest,
      memory  := mem',
      gasLeft := evm.gasLeft - totalGas,
      env     := { evm.env with logs := evm.env.logs ++ [entry] },
      pc      := evm.pc + 1 }

/-! ## Notes

    - There is NO isStatic clause: Frontier has no STATICCALL, so
      EELS Frontier's `sstore`/`log` have no static check. The
      Effect track errors on `isStatic` frames as a forward-looking
      guard, which is sound — the spec only constrains frames the
      implementation accepts.

    - The address argument is a 256-bit stack word truncated to
      160 bits (`Evm.Address.ofNat addrW.toNat`); high bits are
      ignored, matching EELS' `to_address`.

    - LOG topics are listed in stack order: the first popped topic
      is `topics[0]`. An implementation that reverses them fails
      the spec. -/

end Evm.Frontier.Spec
