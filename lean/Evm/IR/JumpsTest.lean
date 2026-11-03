/-
  Evm.IR.JumpsTest — smoke tests for the Phase 4 multi-chunk
  pipeline (`compileProgram` + `executeProgram`).

  Each test compiles a bytecode with dynamic control flow, runs the
  chunk trampoline, runs the same code under `Effect.runFrame`, and
  checks the two agree on the final frame (pc, gasLeft, stack,
  output) — the executable counterpart of
  `compileProgram_sound_vs_effect`.

  Test 1 — forward JUMP over dead code:

    pc 0:  PUSH1 0x0a    -- push 10
    pc 2:  PUSH1 0x06    -- push 6 (the JUMPDEST address)
    pc 4:  JUMP          -- jump to 6
    pc 5:  STOP          -- unreachable
    pc 6:  JUMPDEST
    pc 7:  PUSH1 0x00
    pc 9:  MSTORE        -- mem[0..31] = 10
    pc 10: PUSH1 0x20
    pc 12: PUSH1 0x00
    pc 14: RETURN        -- return mem[0..31]

  Test 2 — countdown loop via JUMPI (backward jump, taken 4 times):

    pc 0:  PUSH1 0x05
    pc 2:  PUSH1 0x00
    pc 4:  MSTORE        -- mem[0..31] = 5
    pc 5:  JUMPDEST
    pc 6:  PUSH1 0x01
    pc 8:  PUSH1 0x00
    pc 10: MLOAD         -- stack: [counter, 1]
    pc 11: SUB           -- counter - 1
    pc 12: PUSH1 0x00
    pc 14: MSTORE        -- mem[0..31] = counter - 1
    pc 15: PUSH1 0x00
    pc 17: MLOAD
    pc 18: PUSH1 0x05    -- loop head
    pc 20: JUMPI         -- loop while counter ≠ 0
    pc 21: STOP

  Run via:  lake env lean Evm/IR/JumpsTest.lean
-/

import Evm.IR.Compile
import Evm.IR.Execute
import Evm.Frontier.Vm.Effect

namespace Evm.IR.JumpsTest

open Evm.IR
open Evm.Frontier.Vm

def jumpBytes : Evm.Bytes :=
  ByteArray.mk #[
    0x60, 0x0a,   -- PUSH1 10
    0x60, 0x06,   -- PUSH1 6
    0x56,         -- JUMP
    0x00,         -- STOP (unreachable)
    0x5b,         -- JUMPDEST
    0x60, 0x00,   -- PUSH1 0
    0x52,         -- MSTORE
    0x60, 0x20,   -- PUSH1 32
    0x60, 0x00,   -- PUSH1 0
    0xf3          -- RETURN
  ]

def loopBytes : Evm.Bytes :=
  ByteArray.mk #[
    0x60, 0x05,   -- PUSH1 5
    0x60, 0x00,   -- PUSH1 0
    0x52,         -- MSTORE
    0x5b,         -- JUMPDEST (pc 5)
    0x60, 0x01,   -- PUSH1 1
    0x60, 0x00,   -- PUSH1 0
    0x51,         -- MLOAD
    0x03,         -- SUB
    0x60, 0x00,   -- PUSH1 0
    0x52,         -- MSTORE
    0x60, 0x00,   -- PUSH1 0
    0x51,         -- MLOAD
    0x60, 0x05,   -- PUSH1 5
    0x57,         -- JUMPI
    0x00          -- STOP
  ]

/-- Build a minimal Evm to run against (no calldata, fresh state). -/
def freshEvm (code : Evm.Bytes) (gas : Nat) : Evm :=
  let msg : Message :=
    { caller := 0, target := some 0, currentTarget := 0,
      value := 0, data := Evm.Bytes.empty, code := code,
      gas := gas, depth := 0 }
  let env : Environment :=
    { origin := 0, gasPrice := 0, coinbase := 0,
      number := 0, difficulty := 0, gasLimit := 0, timestamp := 0,
      state := { accounts := [], storage := [] } }
  Evm.fresh msg env

/-- Compile + trampoline-run `code`, run the same frame under
    `Effect.runFrame`, and compare the final frames. -/
def runCase (name : String) (code : Evm.Bytes) : IO Unit := do
  match compileProgram .frontier code with
  | .error e => IO.println s!"{name}: compile FAIL: {repr e}"
  | .ok prog =>
    IO.println s!"{name}: compiled {prog.chunks.length} chunks, \
                  jumpdests={prog.jumpdests}"
    let evm := freshEvm code 100000
    match executeProgram 1000 prog evm with
    | .error e => IO.println s!"{name}: executeProgram FAIL: {repr e}"
    | .ok evmIR =>
      match Effect.runFrame 100000 evm with
      | .halt evmF out =>
        let same := evmIR.pc == evmF.pc && evmIR.gasLeft == evmF.gasLeft &&
                    evmIR.stack == evmF.stack && evmIR.output == out
        if same then
          IO.println s!"{name}: PASS (pc={evmIR.pc}, \
                        gasLeft={evmIR.gasLeft}, \
                        output={evmIR.output.toList})"
        else do
          IO.println s!"{name}: FAIL — IR/Effect frames differ"
          IO.println s!"  IR:     pc={evmIR.pc} gasLeft={evmIR.gasLeft} \
                        stack={evmIR.stack} output={evmIR.output.toList}"
          IO.println s!"  Effect: pc={evmF.pc} gasLeft={evmF.gasLeft} \
                        stack={evmF.stack} output={out.toList}"
      | .yield _ _ =>
        IO.println s!"{name}: Effect.runFrame yielded unexpectedly"
      | .error _ e =>
        IO.println s!"{name}: Effect.runFrame FAIL: {repr e}"

#eval runCase "jump" jumpBytes
#eval runCase "loop" loopBytes

end Evm.IR.JumpsTest
