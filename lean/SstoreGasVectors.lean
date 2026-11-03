/-
  SstoreGasVectors.lean — `lake exe sstoreGasVectors` prints Lean-oracle
  test vectors for the emitted per-fork SSTORE gas plans and the
  `_eita_access_costs` data table (Stage C-6 differential audit).

  SSTORE lines (one per vector, space-separated):

    plan refund orig cur new cold cost newRefund

  where `plan` names the Lean spec function (and the native symbol the
  audit binds it to):

    legacy   — `Evm.Frontier.Vm.Instructions.sstoreGas`
                                          → _eita_sstore_gas_legacy
    eip1283  — `Evm.Constantinople.Vm.Instructions.sstoreGas`
                                          → _eita_sstore_gas_eip1283
    eip2200  — `Evm.Istanbul.Vm.Instructions.sstoreGas`
                                          → _eita_sstore_gas_eip2200
    berlin   — `Evm.Berlin.Vm.Instructions.Storage.sstoreGas`
                                          → _eita_sstore_gas_berlin
    london   — `Evm.London.Vm.Effect.sstoreGas`
                                          → _eita_sstore_gas_london

  orig/cur/new are decimal u256 values. The grid includes single-limb
  values in every limb position plus pairs differing in exactly one
  limb — the native plans fold equality/zeroness across all four limbs,
  and single-limb diffs are the class random fixtures miss. cold is
  ignored by the pre-Berlin plans; the full grid is still emitted so
  the audit proves the natives ignore exactly what the spec ignores.

  Access-table lines:

    access ord kind cold cost

  computed by the SAME `warmCost`/`coldCost` functions Stage C-2 emits
  the table from — the audit checks the .dylib's data layout and
  byte-indexing, not an independent oracle. Consumed by
  `tests/audit-sstore-gas.lisp`.
-/

import Evm.CL.ARM64.SstoreGas

/-- Single-limb markers in every limb position, plus 2^192+1 which
    differs from 1 and from 2^192 in exactly one limb each. -/
def vals : List Nat :=
  [0, 1, 2, 2 ^ 64, 2 ^ 128, 2 ^ 192, 2 ^ 192 + 1]

/-- Refund-counter inputs: clamp boundaries (0, 1) and a large counter
    (< 2^63 per the plans' signed-compare precondition). -/
def refunds : List Nat := [0, 1, 4800, 14000, 20000, 2 ^ 40]

def main : IO Unit := do
  let mut out := ""
  for r in refunds do
    for o in vals do
      for c in vals do
        for n in vals do
          let ou := BitVec.ofNat 256 o
          let cu := BitVec.ofNat 256 c
          let nu := BitVec.ofNat 256 n
          let (c1, r1) := Evm.Frontier.Vm.Instructions.sstoreGas r cu nu
          out := out ++ s!"legacy {r} {o} {c} {n} 0 {c1} {r1}\n"
          let (c2, r2) := Evm.Constantinople.Vm.Instructions.sstoreGas r ou cu nu
          out := out ++ s!"eip1283 {r} {o} {c} {n} 0 {c2} {r2}\n"
          let (c3, r3) := Evm.Istanbul.Vm.Instructions.sstoreGas r ou cu nu
          out := out ++ s!"eip2200 {r} {o} {c} {n} 0 {c3} {r3}\n"
          for cold in [false, true] do
            let cb := if cold then 1 else 0
            let (c4, r4) := Evm.Berlin.Vm.Instructions.Storage.sstoreGas r cold ou cu nu
            out := out ++ s!"berlin {r} {o} {c} {n} {cb} {c4} {r4}\n"
            let (c5, r5) := Evm.London.Vm.Effect.sstoreGas r cold ou cu nu
            out := out ++ s!"london {r} {o} {c} {n} {cb} {c5} {r5}\n"
  for (f, _) in Evm.CL.ARM64.SstoreGas.tableForks do
    for k in List.range Evm.CL.ARM64.SstoreGas.accessKinds.length do
      let (_, op) := Evm.CL.ARM64.SstoreGas.accessKinds[k]!
      out := out ++ s!"access {f.ord} {k} 1 {Evm.CL.ARM64.SstoreGas.coldCost f op}\n"
      out := out ++ s!"access {f.ord} {k} 0 {Evm.CL.ARM64.SstoreGas.warmCost f op}\n"
  IO.print out
