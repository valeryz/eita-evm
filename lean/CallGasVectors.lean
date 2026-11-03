/-
  CallGasVectors.lean — `lake exe callGasVectors` prints Lean-oracle
  test vectors for the emitted call-gas plan symbols.

  One line per vector, space-separated:

    plan flags delegatedCost gasArg avail charge forward stipend

  where `plan` names the Lean definition (and the native symbol the
  audit binds it to):

    berlin    — `Evm.Berlin.Vm.Effect.callGasPlan`    → _eita_call_gas
    frontier  — `Evm.Frontier.Vm.Effect.callGasPlan`  → _eita_call_gas_frontier
    tangerine — `Evm.TangerineWhistle.Vm.Effect.callGasPlan`
                                                      → _eita_call_gas_tangerine

  flags: bit0 isCold, bit1 chargesValue, bit2 chargesNewAccount — the
  same packing the native ABI takes. The pre-Berlin plans ignore
  isCold/delegatedCost (and frontier also ignores avail); the full
  grid is still emitted for them so the audit proves the native
  symbols ignore exactly what the spec ignores. Consumed by
  `tests/audit-call-gas.lisp`.
-/

import Evm.Frontier.Vm.Effect
import Evm.TangerineWhistle.Vm.Effect
import Evm.Berlin.Vm.Effect

def u64Max : Nat := 2 ^ 64 - 1

/-- Adversarial scalar grid: boundaries of the ∸-clamp, the /64 cap,
    the min, and the u64 range. -/
def delegatedVals : List Nat := [0, 100, 2600]
def gasArgVals : List Nat :=
  [0, 1, 63, 64, 65, 2300, 2301, 65535, 65536, 2 ^ 32, 2 ^ 63, u64Max]
def availVals : List Nat :=
  [0, 1, 63, 64, 65, 99, 100, 101, 2599, 2600, 2601, 6464,
   9100, 11600, 11700, 36600, 36700, 65535, 2 ^ 32, 2 ^ 63 + 5, u64Max]

def main : IO Unit := do
  let mut out := ""
  for flags in List.range 8 do
    let isCold := flags % 2 == 1
    let cv     := (flags / 2) % 2 == 1
    let cna    := (flags / 4) % 2 == 1
    for d in delegatedVals do
      for g in gasArgVals do
        for a in availVals do
          let pb := Evm.Berlin.Vm.Effect.callGasPlan isCold cv cna d g a
          out := out ++ s!"berlin {flags} {d} {g} {a} {pb.charge} {pb.forward} {pb.stipend}\n"
          let pf := Evm.Frontier.Vm.Effect.callGasPlan cv cna g
          out := out ++ s!"frontier {flags} {d} {g} {a} {pf.charge} {pf.forward} {pf.stipend}\n"
          let pt := Evm.TangerineWhistle.Vm.Effect.callGasPlan cv cna g a
          out := out ++ s!"tangerine {flags} {d} {g} {a} {pt.charge} {pt.forward} {pt.stipend}\n"
  IO.print out
