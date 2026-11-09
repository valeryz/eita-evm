/-
  Evm.IR.Execute — Lean-side interpreter for the IR.

  Mirrors `src/evm/eita-ir.lisp` line for line. Used in:
    - Smoke tests (build a chunk in Lean, run it, check output)
    - Statements of the soundness theorems (the spec compares
      `IR.execute` against `Effect.runFrame`)

  Same chunk shape as `IR.Types.Chunk`: pre-charge static gas,
  walk ops, dispatch on terminator.

  Note: the Lean interpreter mirrors the Lisp; trust in their
  agreement is currently empirical (same output on the canonical
  bytecode). A future refinement obligation would prove
  `IR.execute` and the Lisp `execute-ir` produce the same state
  on the same inputs.
-/

import Evm.IR.Types
import Evm.IR.Dispatch
import Evm.IR.Trampoline
import Evm.Crypto.Hash
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions.Arithmetic
import Evm.Frontier.Vm.Instructions.Bitwise
import Evm.Frontier.Vm.Instructions.Memory
import Evm.Frontier.Vm.Instructions.ControlFlow
import Evm.Frontier.Vm.Effect
import Evm.Cancun.State
import Evm.Cancun.Vm.Gas
import Evm.Osaka.Vm.Effect

namespace Evm.IR

open Evm.Frontier.Vm

/-! ## Per-op execution -/

def execOp (evm : Evm) : Op → Except Exception Evm
  | .push _ v => do
      let s ← Stack.push evm.stack v
      return { evm with stack := s }
  | .add => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (a + b)
      return { evm with stack := s }
  | .mul => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (a * b)
      return { evm with stack := s }
  | .sub => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (a - b)
      return { evm with stack := s }
  | .div => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let r := if b = 0 then 0 else BitVec.udiv a b
      let s ← Stack.push s r
      return { evm with stack := s }
  | .sdiv => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (if b = 0 then 0 else BitVec.sdiv a b)
      return { evm with stack := s }
  | .mod => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (if b = 0 then 0 else BitVec.umod a b)
      return { evm with stack := s }
  | .smod => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (if b = 0 then 0 else BitVec.srem a b)
      return { evm with stack := s }
  | .addmod => do
      let (a, b, n, s) ← Stack.pop3 evm.stack
      let s ← Stack.push s
        (if n = 0 then 0 else Evm.U256.ofNat ((a.toNat + b.toNat) % n.toNat))
      return { evm with stack := s }
  | .mulmod => do
      let (a, b, n, s) ← Stack.pop3 evm.stack
      let s ← Stack.push s
        (if n = 0 then 0 else Evm.U256.ofNat ((a.toNat * b.toNat) % n.toNat))
      return { evm with stack := s }
  | .exp => do
      let (base, e, s) ← Stack.pop2 evm.stack
      let gasLeft ← Gas.charge evm.gasLeft
        (Gas.expByte * Instructions.expByteSize e.toNat)
      let s ← Stack.push s
        (Evm.U256.ofNat (Instructions.powMod base.toNat e.toNat (1 <<< 256)))
      return { evm with gasLeft := gasLeft, stack := s }
  | .signextend => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (Instructions.signExtend a b)
      return { evm with stack := s }
  | .slt => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (if BitVec.slt a b then 1 else 0)
      return { evm with stack := s }
  | .sgt => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (if BitVec.slt b a then 1 else 0)
      return { evm with stack := s }
  | .eq => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (if a = b then 1 else 0)
      return { evm with stack := s }
  | .iszero => do
      let (a, s) ← Stack.pop evm.stack
      let s ← Stack.push s (if a = 0 then 1 else 0)
      return { evm with stack := s }
  | .not_ => do
      let (a, s) ← Stack.pop evm.stack
      let s ← Stack.push s (~~~ a)
      return { evm with stack := s }
  | .byte => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (Instructions.byteOf a b)
      return { evm with stack := s }
  | .and_ => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (a &&& b)
      return { evm with stack := s }
  | .or_ => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (a ||| b)
      return { evm with stack := s }
  | .xor_ => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (a ^^^ b)
      return { evm with stack := s }
  | .lt => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (if a < b then 1 else 0)
      return { evm with stack := s }
  | .gt => do
      let (a, b, s) ← Stack.pop2 evm.stack
      let s ← Stack.push s (if a > b then 1 else 0)
      return { evm with stack := s }
  | .pop => do
      let (_, s) ← Stack.pop evm.stack
      return { evm with stack := s }
  | .mload => do
      let (off, s) ← Stack.pop evm.stack
      let offN := off.toNat
      let (gasLeft, mem) ← Instructions.chargeMemory evm.gasLeft evm.memory offN 32
      let value := Evm.U256.ofBytesBE (Memory.read mem offN 32)
      let s ← Stack.push s value
      return { evm with gasLeft := gasLeft, memory := mem, stack := s }
  | .mstore => do
      let (off, value, s) ← Stack.pop2 evm.stack
      let offN := off.toNat
      let (gasLeft, mem) ← Instructions.chargeMemory evm.gasLeft evm.memory offN 32
      let mem := Memory.write mem offN (Evm.U256.toBytesBE value)
      return { evm with gasLeft := gasLeft, memory := mem, stack := s }
  | .mstore8 => do
      let (off, value, s) ← Stack.pop2 evm.stack
      let offN := off.toNat
      let (gasLeft, mem) ← Instructions.chargeMemory evm.gasLeft evm.memory offN 1
      let mem := Memory.writeByte mem offN (UInt8.ofNat (value.toNat &&& 0xff))
      return { evm with gasLeft := gasLeft, memory := mem, stack := s }
  -- Nullary environment/block pushes: gas is fully covered by the
  -- chunk's static pre-charge, so the op just pushes. The pushed
  -- expressions are kept VERBATIM equal to the value lambdas in
  -- `Spec.Step` so the soundness wrappers close by `rfl`.
  | .address => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat evm.message.currentTarget.toNat)
      return { evm with stack := s }
  | .origin => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat evm.env.origin.toNat)
      return { evm with stack := s }
  | .caller => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat evm.message.caller.toNat)
      return { evm with stack := s }
  | .callvalue => do
      let s ← Stack.push evm.stack evm.message.value
      return { evm with stack := s }
  | .calldataload => do
      let (a, s) ← Stack.pop evm.stack
      let s ← Stack.push s
        (Evm.U256.ofBytesBE (Evm.Bytes.sliceZeroPad evm.message.data a.toNat 32))
      return { evm with stack := s }
  | .calldatasize => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat evm.message.data.size)
      return { evm with stack := s }
  | .codesize => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat evm.message.code.size)
      return { evm with stack := s }
  | .gasprice => do
      let s ← Stack.push evm.stack evm.env.gasPrice
      return { evm with stack := s }
  | .coinbase => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat evm.env.coinbase.toNat)
      return { evm with stack := s }
  | .timestamp => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat evm.env.timestamp)
      return { evm with stack := s }
  | .number => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat evm.env.number)
      return { evm with stack := s }
  | .prevrandao => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat evm.env.difficulty)
      return { evm with stack := s }
  | .gaslimit => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat evm.env.gasLimit)
      return { evm with stack := s }
  | .msize => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat evm.memory.size)
      return { evm with stack := s }
  -- PC pushes its compile-time literal.
  | .pc v => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat v)
      return { evm with stack := s }
  -- GAS pushes gasLeft + rem, where rem is the chunk's suffix static
  -- gas after this op: the pre-charge took it out of gasLeft up
  -- front, but the spec frame hasn't paid for the suffix yet.
  | .gas rem => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat (evm.gasLeft + rem))
      return { evm with stack := s }
  -- JUMPDEST: pure no-op inside a chunk (gas pre-charged, pc virtual).
  | .jumpdest => return evm
  -- KECCAK256: static 30 pre-charged; dynamic per-word + memory
  -- expansion charged here, mirroring `Instructions.keccak256` minus
  -- the `Gas.keccak256` summand.
  | .keccak256 => do
      let (offset, len, s) ← Stack.pop2 evm.stack
      let off  := offset.toNat
      let lenN := len.toNat
      let words := (lenN + 31) / 32
      let gasLeft ← Gas.charge evm.gasLeft (Gas.keccak256Word * words)
      let (gasLeft, mem) ← Instructions.chargeMemory gasLeft evm.memory off lenN
      let hash : Evm.Hash32 := Evm.Crypto.keccak256 (Memory.read mem off lenN)
      let s ← Stack.push s hash
      return { evm with gasLeft := gasLeft, memory := mem, stack := s }
  -- CALLDATACOPY / CODECOPY: static `veryLow` pre-charged; dynamic
  -- per-word + memory expansion here, mirroring the handlers'
  -- `copyToMemory` minus the `Gas.veryLow` summand.
  | .calldatacopy => do
      let (dest, off, len, s) ← Stack.pop3 evm.stack
      let destN := dest.toNat
      let offN  := off.toNat
      let lenN  := len.toNat
      let words := (lenN + 31) / 32
      let gasLeft ← Gas.charge evm.gasLeft (Gas.copy * words)
      let (gasLeft, mem) ← Instructions.chargeMemory gasLeft evm.memory destN lenN
      let mem := Memory.write mem destN (Evm.Bytes.sliceZeroPad evm.message.data offN lenN)
      return { evm with gasLeft := gasLeft, memory := mem, stack := s }
  | .codecopy => do
      let (dest, off, len, s) ← Stack.pop3 evm.stack
      let destN := dest.toNat
      let offN  := off.toNat
      let lenN  := len.toNat
      let words := (lenN + 31) / 32
      let gasLeft ← Gas.charge evm.gasLeft (Gas.copy * words)
      let (gasLeft, mem) ← Instructions.chargeMemory gasLeft evm.memory destN lenN
      let mem := Memory.write mem destN (Evm.Bytes.sliceZeroPad evm.message.code offN lenN)
      return { evm with gasLeft := gasLeft, memory := mem, stack := s }
  -- DUP-n / SWAP-n: gas fully static (pre-charged); pure stack edit.
  | .dup n => do
      let s ← Stack.dup evm.stack n
      return { evm with stack := s }
  | .swap n => do
      let s ← Stack.swap evm.stack n
      return { evm with stack := s }
  -- State ops: in the Effect track these yield mid-instruction and
  -- are resolved by `handleYield` purely from the frame's own env;
  -- here the yield+resume composition is inlined into one pure step.
  | .sload => do
      let (key, s) ← Stack.pop evm.stack
      let v := evm.env.state.getStorage evm.message.currentTarget key
      let s ← Stack.push s v
      return { evm with stack := s }
  -- SSTORE: no static pre-charge (cost depends on the old value);
  -- the full sSet/sReset charge plus refund happens here, mirroring
  -- `resumeSstore`.
  | .sstore => do
      if evm.message.isStatic then .error .writeInStaticContext
      else do
      let (key, value, s) ← Stack.pop2 evm.stack
      let addr := evm.message.currentTarget
      let oldValue := evm.env.state.getStorage addr key
      let cost := if oldValue = (0 : Evm.U256) ∧ value ≠ (0 : Evm.U256)
                  then Gas.sSet else Gas.sReset
      let gasLeft ← Gas.charge evm.gasLeft cost
      let refundDelta : Nat :=
        if oldValue ≠ (0 : Evm.U256) ∧ value = (0 : Evm.U256) then
          Gas.sClearRefund
        else 0
      return { evm with
        gasLeft := gasLeft, stack := s,
        env := { evm.env with
          state := evm.env.state.setStorage addr key value,
          refundCounter := evm.env.refundCounter + refundDelta } }
  | .balance => do
      let (addrW, s) ← Stack.pop evm.stack
      let bal := evm.env.state.getBalance (Evm.Address.ofNat addrW.toNat)
      let s ← Stack.push s bal
      return { evm with stack := s }
  | .extcodesize => do
      let (addrW, s) ← Stack.pop evm.stack
      let acc := evm.env.state.getAccount (Evm.Address.ofNat addrW.toNat)
      let s ← Stack.push s (Evm.U256.ofNat acc.code.size)
      return { evm with stack := s }
  -- EXTCODECOPY: static `extCode` pre-charged; mirrors `doExtcodecopy`'s
  -- order — memory expansion charged FIRST, then the per-word copy cost
  -- (opposite of calldatacopy/codecopy).
  | .extcodecopy => do
      let (addrW, s) ← Stack.pop evm.stack
      let (memOff, codeOff, size, s) ← Stack.pop3 s
      let memOffN := memOff.toNat
      let sizeN   := size.toNat
      let (gasLeft, mem) ← Instructions.chargeMemory evm.gasLeft evm.memory memOffN sizeN
      let gasLeft ← Gas.charge gasLeft (Gas.copy * ((sizeN + 31) / 32))
      let code := (evm.env.state.getAccount (Evm.Address.ofNat addrW.toNat)).code
      let mem := Memory.write mem memOffN (Evm.Bytes.sliceZeroPad code codeOff.toNat sizeN)
      return { evm with gasLeft := gasLeft, memory := mem, stack := s }
  | .blockhash => do
      let (n, s) ← Stack.pop evm.stack
      let nN := n.toNat
      let curN := evm.env.number
      let h : Evm.Hash32 :=
        if nN ≥ curN ∨ curN - nN > 256 then 0
        else
          let len := evm.env.blockHashes.length
          let idx := len - (curN - nN)
          (evm.env.blockHashes[idx]?).getD 0
      let s ← Stack.push s h
      return { evm with stack := s }
  -- LOG-n: static `log + logTopic*n` pre-charged; per-byte data cost
  -- then memory expansion here, mirroring `doLog`'s charge order.
  | .log n => do
      if evm.message.isStatic then .error .writeInStaticContext
      else do
      let (offset, len, s) ← Stack.pop2 evm.stack
      let (topics, s) ← Effect.popTopicsAux s n
      let off  := offset.toNat
      let lenN := len.toNat
      let gasLeft ← Gas.charge evm.gasLeft (Gas.logData * lenN)
      let (gasLeft, mem) ← Instructions.chargeMemory gasLeft evm.memory off lenN
      let entry : Log :=
        { address := evm.message.currentTarget, topics := topics,
          data := Memory.read mem off lenN }
      return { evm with
        gasLeft := gasLeft, memory := mem, stack := s,
        env := { evm.env with logs := evm.env.logs ++ [entry] } }
  -- Post-Frontier ops (#222). Each arm inlines its INTRODUCING-fork
  -- handler minus the static charge (covered by the chunk pre-charge;
  -- pc is virtual inside a chunk). Per-fork repricings are #223.
  -- SHL/SHR/SAR mirror `Constantinople.Vm.Instructions.shl/shr/sar`
  -- (EIP-145): stack top is `shift`, next is `value`.
  | .shl => do
      let (shift, value, s) ← Stack.pop2 evm.stack
      let sh := shift.toNat
      let r := if sh ≥ 256 then 0 else Evm.U256.ofNat (value.toNat <<< sh)
      let s ← Stack.push s r
      return { evm with stack := s }
  | .shr => do
      let (shift, value, s) ← Stack.pop2 evm.stack
      let sh := shift.toNat
      let r := if sh ≥ 256 then 0 else Evm.U256.ofNat (value.toNat >>> sh)
      let s ← Stack.push s r
      return { evm with stack := s }
  | .sar => do
      let (shift, value, s) ← Stack.pop2 evm.stack
      let sh := shift.toNat
      let neg := value.toNat ≥ (1 <<< 255)
      let r :=
        if sh ≥ 256 then
          if neg then Evm.U256.ofNat ((1 <<< 256) - 1) else 0
        else if ¬ neg then
          Evm.U256.ofNat (value.toNat >>> sh)
        else
          -- Arithmetic shift of a negative value: unsigned shift, then
          -- sign-extend the top `sh` bits with 1s (same trick as the
          -- Constantinople handler).
          let raw := value.toNat >>> sh
          let topMask : Nat := ((1 <<< 256) - 1) ^^^ ((1 <<< (256 - sh)) - 1)
          Evm.U256.ofNat (raw ||| topMask)
      let s ← Stack.push s r
      return { evm with stack := s }
  -- RETURNDATASIZE/RETURNDATACOPY mirror `Byzantium.Vm.Instructions`
  -- (EIP-211). The copy keeps the handler's charge order: bounds
  -- check, memory expansion, then per-word cost.
  | .returndatasize => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat evm.returnData.size)
      return { evm with stack := s }
  | .returndatacopy => do
      let (destOff, offset, len, s) ← Stack.pop3 evm.stack
      let destOffN := destOff.toNat
      let offsetN  := offset.toNat
      let lenN     := len.toNat
      if offsetN + lenN > evm.returnData.size then
        .error .outOfGas  -- EELS OutOfBounds; OOG is our nearest peer
      else do
        let (gasLeft, mem) ← Instructions.chargeMemory evm.gasLeft evm.memory destOffN lenN
        let gasLeft ← Gas.charge gasLeft (Gas.copy * ((lenN + 31) / 32))
        let mem := Memory.write mem destOffN
          (Evm.Bytes.sliceZeroPad evm.returnData offsetN lenN)
        return { evm with gasLeft := gasLeft, memory := mem, stack := s }
  -- EXTCODEHASH mirrors `Constantinople.Vm.Instructions.extcodehash`
  -- (EIP-1052): a dead account (absent OR empty per EIP-161) pushes 0.
  | .extcodehash => do
      let (addrW, s) ← Stack.pop evm.stack
      let addr := Evm.Address.ofNat addrW.toNat
      let acc := evm.env.state.getAccount addr
      let dead : Bool := !(evm.env.state.accountExists addr) || acc.isEmpty
      let s ← Stack.push s
        (if dead then (0 : Evm.U256) else Evm.Crypto.keccak256 acc.code)
      return { evm with stack := s }
  -- Nullary pushes (Istanbul chainid/selfbalance, London baseFee,
  -- Cancun blobbasefee, Shanghai push0): gas fully static.
  | .chainid => do
      let s ← Stack.push evm.stack evm.env.chainId
      return { evm with stack := s }
  | .selfbalance => do
      let s ← Stack.push evm.stack (evm.env.state.getBalance evm.message.currentTarget)
      return { evm with stack := s }
  | .basefee => do
      let s ← Stack.push evm.stack (Evm.U256.ofNat evm.env.baseFeePerGas)
      return { evm with stack := s }
  | .blobbasefee => do
      let s ← Stack.push evm.stack evm.env.blobBaseFee
      return { evm with stack := s }
  | .push0 => do
      let s ← Stack.push evm.stack 0
      return { evm with stack := s }
  -- BLOBHASH mirrors `Cancun.Vm.Instructions.blobhash` (EIP-4844).
  | .blobhash => do
      let (idx, s) ← Stack.pop evm.stack
      let idxN := idx.toNat
      let v : Evm.Hash32 :=
        if idxN < evm.env.blobVersionedHashes.length then
          evm.env.blobVersionedHashes[idxN]!
        else 0
      let s ← Stack.push s v
      return { evm with stack := s }
  -- TLOAD/TSTORE mirror `Cancun.Vm.Instructions.tload/tstore`
  -- (EIP-1153): the flat 100 is pre-charged; TSTORE keeps the
  -- static-context check.
  | .tload => do
      let (slot, s) ← Stack.pop evm.stack
      let v := Evm.Cancun.State.getTransient evm.env evm.message.currentTarget slot
      let s ← Stack.push s v
      return { evm with stack := s }
  | .tstore => do
      if evm.message.isStatic then .error .writeInStaticContext
      else do
      let (slot, value, s) ← Stack.pop2 evm.stack
      let env := Evm.Cancun.State.setTransient evm.env
                   evm.message.currentTarget slot value
      return { evm with stack := s, env := env }
  -- MCOPY mirrors `Cancun.Vm.Instructions.mcopy` (EIP-5656): base 3
  -- pre-charged; memory expansion over BOTH ranges, then per-word
  -- cost; read-then-write makes overlap safe.
  | .mcopy => do
      let (destOff, srcOff, len, s) ← Stack.pop3 evm.stack
      let destOffN := destOff.toNat
      let srcOffN  := srcOff.toNat
      let lenN     := len.toNat
      -- `len = 0` neither charges nor grows memory (EELS skips empty ranges).
      let highEnd := if lenN = 0 then 0 else Nat.max (destOffN + lenN) (srcOffN + lenN)
      let (gasLeft, mem) ← Instructions.chargeMemory evm.gasLeft evm.memory 0 highEnd
      let gasLeft ← Gas.charge gasLeft (Evm.Cancun.Vm.Gas.mcopyWord * ((lenN + 31) / 32))
      let src := Memory.read mem srcOffN lenN
      let mem := Memory.write mem destOffN src
      return { evm with gasLeft := gasLeft, memory := mem, stack := s }
  -- CLZ (Osaka, EIP-7939) mirrors `Osaka.Vm.Effect.doClz` minus the
  -- static charge: pop x, push `clzU256 x` (256 − bit_length x).
  | .clz => do
      let (x, s) ← Stack.pop evm.stack
      let s ← Stack.push s (Evm.Osaka.Vm.Effect.clzU256 x)
      return { evm with stack := s }

/-! ## Op-list execution -/

def execOps : Evm → List Op → Except Exception Evm
  | evm, []        => return evm
  | evm, op :: ops => do
      let evm' ← execOp evm op
      execOps evm' ops

/-! ## Fork-routed op execution

    The chunk pre-charge already carries the per-fork static gas
    (`staticGasFor` reads the fork-indexed `Op.metadata`), so most
    `execOp` arms are fork-correct as-is: their semantics never
    changed, only their price. Two exceptions route through
    `Dispatch.Op.handler`, binding the fork's own tested handler:

    * SSTORE — its gas AND refund accounting are the fork-varying
      part (Frontier flat, EIP-1283, EIP-2200, EIP-2929, EIP-3529)
      and `Op.metadata` prices it at 0, so the handler runs on the
      pre-charged gas as-is. Routed at EVERY fork (the ladder is
      total for `.sstore`).
    * Berlin+ access ops (SLOAD/BALANCE/EXTCODESIZE/EXTCODECOPY/
      EXTCODEHASH) — EIP-2929 makes their price state-dependent
      (warm vs cold), which no pre-charge can know. The pre-charge
      took the warm static (`staticGasFor` = 100); `execOpRepriced`
      credits exactly that back, then the handler charges the full
      warm/cold cost (plus memexp+copy for EXTCODECOPY) itself. Net:
      warm accesses cost what the pre-charge said, cold ones add the
      surcharge — gas-exact without touching `Op.metadata`, whose
      warm statics the ARM64 threaded-interp emit also reads.
      Pre-Berlin these ops are static-priced and stay on `execOp`.
    * EXP from Spurious Dragon on — EIP-160 reprices the per-byte
      cost 10 → 50, which `execOp`'s inline arm (Frontier
      `Gas.expByte`) doesn't know. Same credit-then-charge: the
      static 10 comes back, Spurious Dragon's own `exp` handler
      charges 10 + 50/byte.

    The handlers bump pc where `execOp`'s inline arms don't;
    mid-chunk pc is dead (the terminator overwrites it), so the two
    agree on everything observable. -/

/-- Credit-then-charge for an op whose dynamic gas is repriced from
    fork `since` on; before `since` the pre-charged `execOp` arm is
    exact and runs instead. -/
def execOpRepriced (fork since : Evm.Fork) (evm : Evm) (op : Op) (byte : UInt8) :
    Except Exception Evm :=
  if fork.atLeast since then
    match Dispatch.Op.handler fork op with
    | some h => h { evm with gasLeft := evm.gasLeft + staticGasFor fork op }
    | none => .error (.invalidOpcode byte)  -- unreachable: routed arms are total
  else execOp evm op

def execOpFor (fork : Evm.Fork) (evm : Evm) (op : Op) :
    Except Exception Evm :=
  match op with
  | .sstore =>
    match Dispatch.Op.handler fork .sstore with
    | some h => h evm
    | none => .error (.invalidOpcode 0x55)  -- unreachable: ladder is total
  | .exp         => execOpRepriced fork .spuriousDragon evm .exp 0x0a
  | .sload       => execOpRepriced fork .berlin evm .sload 0x54
  | .balance     => execOpRepriced fork .berlin evm .balance 0x31
  | .extcodesize => execOpRepriced fork .berlin evm .extcodesize 0x3b
  | .extcodecopy => execOpRepriced fork .berlin evm .extcodecopy 0x3c
  | .extcodehash => execOpRepriced fork .berlin evm .extcodehash 0x3f
  | op => execOp evm op

def execOpsFor (fork : Evm.Fork) : Evm → List Op → Except Exception Evm
  | evm, []        => return evm
  | evm, op :: ops => do
      let evm' ← execOpFor fork evm op
      execOpsFor fork evm' ops

/-- Pass-through spot check: every non-SSTORE op runs the same
    `execOp` arm on every fork. -/
theorem execOpFor_add_passthrough (fork : Evm.Fork) (evm : Evm) :
    execOpFor fork evm .add = execOp evm .add := rfl

/-- SSTORE bindings at the repricing boundaries (rfl — the routing IS
    `Dispatch.Op.handler`, already spot-checked per fork there). -/
theorem execOpFor_sstore_frontier (evm : Evm) :
    execOpFor .frontier evm .sstore = Instructions.sstore evm := rfl
theorem execOpFor_sstore_constantinople (evm : Evm) :
    execOpFor .constantinople evm .sstore
      = Evm.Constantinople.Vm.Instructions.sstore evm := rfl
theorem execOpFor_sstore_istanbul (evm : Evm) :
    execOpFor .istanbul evm .sstore
      = Evm.Istanbul.Vm.Instructions.sstore evm := rfl
theorem execOpFor_sstore_berlin (evm : Evm) :
    execOpFor .berlin evm .sstore
      = Evm.Berlin.Vm.Effect.doSstorePure evm := rfl
theorem execOpFor_sstore_cancun (evm : Evm) :
    execOpFor .cancun evm .sstore
      = Evm.London.Vm.Effect.doSstoreLondon evm := rfl

/-- EXP repricing boundary (EIP-160): pre-Spurious-Dragon the
    pre-charged `execOp` arm (10/byte) runs; from Spurious Dragon on
    the static 10 is credited back and the fork handler charges
    10 + 50/byte. -/
theorem execOpFor_exp_frontier (evm : Evm) :
    execOpFor .frontier evm .exp = execOp evm .exp := rfl
theorem execOpFor_exp_tangerine (evm : Evm) :
    execOpFor .tangerineWhistle evm .exp = execOp evm .exp := rfl
theorem execOpFor_exp_spurious (evm : Evm) :
    execOpFor .spuriousDragon evm .exp
      = Evm.SpuriousDragon.Vm.Instructions.exp
          { evm with gasLeft := evm.gasLeft + 10 } := rfl
theorem execOpFor_exp_london (evm : Evm) :
    execOpFor .london evm .exp
      = Evm.SpuriousDragon.Vm.Instructions.exp
          { evm with gasLeft := evm.gasLeft + 10 } := rfl

/-- Pre-Berlin, access ops stay on the pre-charged `execOp` arm. -/
theorem execOpFor_sload_frontier (evm : Evm) :
    execOpFor .frontier evm .sload = execOp evm .sload := rfl
theorem execOpFor_balance_istanbul (evm : Evm) :
    execOpFor .istanbul evm .balance = execOp evm .balance := rfl
theorem execOpFor_extcodehash_petersburg (evm : Evm) :
    execOpFor .petersburg evm .extcodehash = execOp evm .extcodehash := rfl

/-- Berlin+ bindings: the warm static (100) the chunk pre-charge took
    is credited back; the EIP-2929 handler charges warm/cold itself. -/
theorem execOpFor_sload_berlin (evm : Evm) :
    execOpFor .berlin evm .sload
      = Evm.Berlin.Vm.Effect.doSloadPure
          { evm with gasLeft := evm.gasLeft + 100 } := rfl
theorem execOpFor_balance_berlin (evm : Evm) :
    execOpFor .berlin evm .balance
      = Evm.Berlin.Vm.Effect.doBalancePure
          { evm with gasLeft := evm.gasLeft + 100 } := rfl
theorem execOpFor_extcodesize_london (evm : Evm) :
    execOpFor .london evm .extcodesize
      = Evm.Berlin.Vm.Effect.doExtcodesizePure
          { evm with gasLeft := evm.gasLeft + 100 } := rfl
theorem execOpFor_extcodecopy_berlin (evm : Evm) :
    execOpFor .berlin evm .extcodecopy
      = Evm.Berlin.Vm.Effect.doExtcodecopyPure
          { evm with gasLeft := evm.gasLeft + 100 } := rfl
theorem execOpFor_extcodehash_cancun (evm : Evm) :
    execOpFor .cancun evm .extcodehash
      = Evm.Berlin.Vm.Effect.doExtcodehashPure
          { evm with gasLeft := evm.gasLeft + 100 } := rfl

/-! ## Terminator handling

    `endPc` (from `Chunk.endPc`) is the pc the Effect interpreter
    holds at the halt; writing it into the halted frame makes the IR
    result match `Effect.runFrame` exactly, pc included. -/

def execTerm (evm : Evm) (endPc : Nat) : Terminator → Except Exception Evm
  | .stop      => return { evm with halted := true, pc := endPc }
  | .endOfCode => return { evm with halted := true, pc := endPc }
  | .ret => do
      let (off, len, s) ← Stack.pop2 evm.stack
      let offN := off.toNat
      let lenN := len.toNat
      let (gasLeft, mem) ← Instructions.chargeMemory evm.gasLeft evm.memory offN lenN
      let output := Memory.read mem offN lenN
      return { evm with
        gasLeft := gasLeft, memory := mem, stack := s,
        output := output, halted := true, pc := endPc }
  -- Control-flow terminators: mirror `Instructions.jump` / `jumpi`
  -- clause for clause. The result is a NON-halted frame whose pc is
  -- the transfer target; the program-level trampoline
  -- (`executeProgram`) dispatches the next chunk from it. Validity
  -- uses the same `isValidJumpDest` the Effect handler consults, so
  -- IR/Effect agreement on jump targets is definitional.
  | .jumpDynamic => do
      let gasLeft ← Gas.charge evm.gasLeft Gas.mid
      let (dest, s) ← Stack.pop evm.stack
      if Instructions.isValidJumpDest evm dest.toNat then
        return { evm with gasLeft := gasLeft, stack := s, pc := dest.toNat }
      else
        .error .invalidJumpDest
  -- JUMPI's false branch falls through to `endPc` (the byte after
  -- the JUMPI), which the compiler registered as a chunk entry.
  | .jumpiDynamic => do
      let gasLeft ← Gas.charge evm.gasLeft Gas.high
      let (dest, cond, s) ← Stack.pop2 evm.stack
      if cond = (0 : Evm.U256) then
        return { evm with gasLeft := gasLeft, stack := s, pc := endPc }
      else if Instructions.isValidJumpDest evm dest.toNat then
        return { evm with gasLeft := gasLeft, stack := s, pc := dest.toNat }
      else
        .error .invalidJumpDest
  -- SELFDESTRUCT is frame-ending and TOTAL at Frontier: `step1`
  -- wires 0xff to `Vm.selfdestruct` via `liftPure` (NOT the
  -- yield-based `doSelfdestruct`, which is Block-STM groundwork).
  -- Bind the same handler; it halts with pc unchanged, so position
  -- the frame at `endPc` (the 0xff opcode's own pc) first.
  | .selfdestruct => Evm.Frontier.Vm.selfdestruct { evm with pc := endPc }
  -- REVERT mirrors `Byzantium.Vm.Instructions.revert` (EIP-140):
  -- like RETURN but with the failure flag set; the call-resume layer
  -- keeps the output as returndata, pushes 0, refunds remaining gas.
  -- endPc is the byte after the 0xfd (the handler sets pc + 1).
  | .revert => do
      let (offset, len, s) ← Stack.pop2 evm.stack
      let off  := offset.toNat
      let lenN := len.toNat
      let (gasLeft, mem) ← Instructions.chargeMemory evm.gasLeft evm.memory off lenN
      let output := Memory.read mem off lenN
      return { evm with
        gasLeft := gasLeft, memory := mem, stack := s,
        output := output, halted := true, reverted := true, pc := endPc }
  -- Remaining terminators raise an explicit exception so the failure
  -- surface is loud. `.invalid` (0xfe) lands here BY DESIGN: the
  -- INVALID opcode is an exceptional halt. `.call` / `.create` land
  -- here BY DESIGN too: a sub-frame yield is not expressible in
  -- `Except` — the yielding track is `execTermStep` below.
  | _ => .error (.invalidOpcode 0xfe)

/-! ## Chunk execution -/

def execute (chunk : Chunk) (evm : Evm) : Except Exception Evm := do
  -- Pre-charge the chunk's static gas.
  let gasLeft ← Gas.charge evm.gasLeft chunk.staticGas
  let evm := { evm with gasLeft := gasLeft }
  -- Walk ops.
  let evm ← execOps evm chunk.ops
  -- Dispatch terminator.
  execTerm evm chunk.endPc chunk.term

/-! ## Yielding terminators (Stage C)

    CALL / CALLCODE / CREATE spawn sub-frames: their result is a
    `StepResult.yield` carrying the sub-frame request, not a final
    frame — inexpressible in the `Except`-valued track above. The
    `StepResult`-valued track dispatches them through
    `Trampoline.Terminator.stepHandler`, which binds the SAME
    `Effect.doCall` / `doCallcode` / `doCreate` the tested Effect
    interpreter runs (binding, not re-encoding). Every other
    terminator falls back to `execTerm`, lifted into a `StepResult`
    the same way `Effect.liftPure` lifts a `Handler`. -/

def execTermStep (fork : Evm.Fork) (evm : Evm) (endPc : Nat) (term : Terminator) :
    Trampoline.StepResultOf fork :=
  match Trampoline.Terminator.stepHandler fork term with
  -- The handler reads `evm.pc` as the yield's resume point, so
  -- position the frame at the terminator opcode's pc first.
  | some h => h { evm with pc := endPc }
  | none =>
    match term with
    -- Fork-sensitive frame-enders route through the fork's own
    -- Handler binding (`Terminator.handler` carries the repricing /
    -- gating ladders); `none` = terminator illegal on this fork.
    -- pc positioning mirrors each fork's `step1`, which runs the
    -- handler with pc AT the opcode: selfdestruct handlers halt with
    -- pc unchanged (endPc IS the 0xff pc); revert bumps pc by one
    -- (endPc is the byte after the 0xfd).
    | .selfdestruct =>
      match Trampoline.Terminator.handler fork .selfdestruct with
      | some h => Trampoline.StepResultOf.liftPure fork h
          { evm with pc := endPc }
      | none => Trampoline.StepResultOf.error fork evm (.invalidOpcode 0xff)
    | .revert =>
      match Trampoline.Terminator.handler fork .revert with
      | some h => Trampoline.StepResultOf.liftPure fork h
          { evm with pc := endPc - 1 }
      | none => Trampoline.StepResultOf.error fork evm (.invalidOpcode 0xfd)
    -- Everything else is fork-invariant: the plain-`Handler` track,
    -- lifted into the fork's own `StepResult` by the fork's own
    -- `liftPure` — at `.frontier` this is definitionally the old
    -- inline ok/halted/error match.
    | _ => Trampoline.StepResultOf.liftPure fork
        (fun e => execTerm e endPc term) evm

/-! Spot checks: the fallback's fork routing binds each fork's own
    frame-ending handler — rfl, the dispatch IS the binding. One
    theorem per repricing boundary plus a delegation check
    (Gray Glacier inherits London's EIP-3529 variant) and the
    illegal-below-introduction checks. -/

theorem execTermStep_selfdestruct_frontier (evm : Evm) (endPc : Nat) :
    execTermStep .frontier evm endPc .selfdestruct
      = Trampoline.StepResultOf.liftPure .frontier
          Evm.Frontier.Vm.selfdestruct { evm with pc := endPc } := rfl

theorem execTermStep_selfdestruct_tangerine (evm : Evm) (endPc : Nat) :
    execTermStep .tangerineWhistle evm endPc .selfdestruct
      = Trampoline.StepResultOf.liftPure .tangerineWhistle
          Evm.TangerineWhistle.Vm.selfdestruct { evm with pc := endPc } := rfl

theorem execTermStep_selfdestruct_spurious (evm : Evm) (endPc : Nat) :
    execTermStep .spuriousDragon evm endPc .selfdestruct
      = Trampoline.StepResultOf.liftPure .spuriousDragon
          Evm.SpuriousDragon.Vm.selfdestruct { evm with pc := endPc } := rfl

theorem execTermStep_selfdestruct_berlin (evm : Evm) (endPc : Nat) :
    execTermStep .berlin evm endPc .selfdestruct
      = Trampoline.StepResultOf.liftPure .berlin
          Evm.Berlin.Vm.Effect.doSelfdestructPure { evm with pc := endPc } := rfl

theorem execTermStep_selfdestruct_london (evm : Evm) (endPc : Nat) :
    execTermStep .london evm endPc .selfdestruct
      = Trampoline.StepResultOf.liftPure .london
          Evm.London.Vm.Effect.doSelfdestructLondon { evm with pc := endPc } := rfl

theorem execTermStep_selfdestruct_grayGlacier (evm : Evm) (endPc : Nat) :
    execTermStep .grayGlacier evm endPc .selfdestruct
      = Trampoline.StepResultOf.liftPure .grayGlacier
          Evm.London.Vm.Effect.doSelfdestructLondon { evm with pc := endPc } := rfl

theorem execTermStep_revert_byzantium (evm : Evm) (endPc : Nat) :
    execTermStep .byzantium evm endPc .revert
      = Trampoline.StepResultOf.liftPure .byzantium
          Evm.Byzantium.Vm.Instructions.revert { evm with pc := endPc - 1 } := rfl

theorem execTermStep_revert_shanghai (evm : Evm) (endPc : Nat) :
    execTermStep .shanghai evm endPc .revert
      = Trampoline.StepResultOf.liftPure .shanghai
          Evm.Byzantium.Vm.Instructions.revert { evm with pc := endPc - 1 } := rfl

theorem execTermStep_revert_invalid_frontier (evm : Evm) (endPc : Nat) :
    execTermStep .frontier evm endPc .revert
      = Trampoline.StepResultOf.error .frontier evm (.invalidOpcode 0xfd) := rfl

theorem execTermStep_revert_invalid_spurious (evm : Evm) (endPc : Nat) :
    execTermStep .spuriousDragon evm endPc .revert
      = Trampoline.StepResultOf.error .spuriousDragon evm
          (.invalidOpcode 0xfd) := rfl

def executeStep (fork : Evm.Fork) (chunk : Chunk) (evm : Evm) :
    Trampoline.StepResultOf fork :=
  match Gas.charge evm.gasLeft chunk.staticGas with
  | .error e => Trampoline.StepResultOf.error fork evm e
  | .ok gasLeft =>
    match execOpsFor fork { evm with gasLeft := gasLeft } chunk.ops with
    | .error e  => Trampoline.StepResultOf.error fork evm e
    | .ok evm'  => execTermStep fork evm' chunk.endPc chunk.term

/-! ## Program execution (Phase 4)

    The multi-chunk trampoline: look up the chunk at the frame's pc,
    run it via `execute`, and either stop (halted frame) or loop on
    the transfer target. `fuel` bounds the number of chunk
    transitions; exhaustion reports `.outOfGas`, the same convention
    `Effect.runFrame` uses for its step fuel.

    A missing chunk at a transfer target is a COMPILER coverage gap
    (see `compileProgram`); it surfaces as `.invalidJumpDest`, never
    as silent divergence. -/

def Program.lookup (p : Program) (pc : Nat) : Option Chunk :=
  match p.chunks.find? (fun e => e.1 = pc) with
  | some e => some e.2
  | none   => none

def executeProgram : Nat → Program → Evm → Except Exception Evm
  | 0, _, _ => .error .outOfGas
  | fuel + 1, prog, evm =>
    match prog.lookup evm.pc with
    | none => .error .invalidJumpDest
    | some ch =>
      match execute ch evm with
      | .error e => .error e
      | .ok evm' =>
        if evm'.halted then .ok evm'
        else executeProgram fuel prog evm'

/-- `Step`-valued program run: like `executeProgram`, but chunks run
    via `executeStep`, so a CALL / CALLCODE / CREATE terminator
    surfaces as `.yield` — the same shape `Effect.runFrameR` produces
    for structural yields. A `.continue` (CALL fail-fast pushes 0 and
    resumes at pc+1, a registered chunk entry) loops like a jump. -/
def executeProgramR (fork : Evm.Fork) :
    Nat → Program → Evm → Trampoline.StepOf fork
  | 0, _, evm => Trampoline.StepOf.error fork evm .outOfGas
  | fuel + 1, prog, evm =>
    match prog.lookup evm.pc with
    | none => Trampoline.StepOf.error fork evm .invalidJumpDest
    | some ch =>
      Trampoline.StepResultOf.cases fork (executeStep fork ch evm)
        (fun evm' => executeProgramR fork fuel prog evm')
        (fun step => step)

/-- Program-level trampoline: yields are discharged by the fork's
    own yield semantics (`Trampoline.runYieldOf`, each arm IS that
    fork's `handleYield`); sub-frames run in that fork's Effect
    interpreter (`Trampoline.trampolineOf`) — compiling sub-frame
    code through the IR is future work, and binding the tested
    runner keeps the semantics shared rather than re-encoded. -/
partial def runProgram (fork : Evm.Fork) (prog : Program) (evm : Evm) :
    Except Exception Evm :=
  Trampoline.StepOf.cases fork (executeProgramR fork (1 <<< 24) prog evm)
    (fun frame eff =>
      match Trampoline.runYieldOf fork frame eff
              (Trampoline.trampolineOf fork) with
      | .ok cont => runProgram fork prog cont
      | .error e => .error e)
    (fun finalEvm _output => .ok finalEvm)
    (fun _frame e => .error e)

end Evm.IR
