/-
  Evm.Constantinople.Vm.Gas — Constantinople gas table delta.

  EELS reference: ethereum/forks/constantinople/vm/gas.py
  (current master collapses Constantinople and Petersburg into one
  reduced model — we additionally surface the EIP-1283 constants here
  because Constantinople originally shipped EIP-1283 net SSTORE
  metering, which Petersburg later reverted).

  Deltas from Byzantium:
    * EIP-1052 EXTCODEHASH: 400 gas (`OPCODE_EXTCODEHASH`).
    * EIP-1283 SSTORE (net metering): three new constants on top of
      the pre-existing 20000 / 5000 / 15000 schedule:
        - `sLoadDirty` / `dirtyWrite` = 200 (the "no-op" / "dirty" tier)
        - `sResetClearRefund`         = 15000 (already in Frontier)
        - `sResetRefund`              = 4800  (refund for resetting a
                                               dirty slot back to its
                                               nonzero original)
        - `sSetRefund`                = 19800 (refund for resetting a
                                               dirty slot back to its
                                               zero original)
    * EIP-1014 CREATE2: same `create` base (32000) plus per-word
      keccak256 cost (6 gas) over the initcode preimage.

  All Frontier / TW / SD / Byzantium constants remain valid; we only
  add what's strictly new.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Frontier.Vm.Gas

namespace Evm.Constantinople.Vm.Gas

open Evm.Frontier.Vm

/-- EIP-1052 EXTCODEHASH (0x3f). -/
def extCodeHash : Gas.Gas := 400

/-- EIP-1283 dirty-slot / no-op SSTORE tier. Identical to Tangerine
    Whistle's SLOAD reprice (200) by coincidence — both descended
    from the "fast disk read" gas target. -/
def sLoadGas : Gas.Gas := 200

/-- EIP-1283 refund when resetting a dirty slot back to its non-zero
    original value (cancels the prior 5000 "fresh reset" charge minus
    the 200 dirty re-charge). -/
def sResetRefund : Gas.Gas := 4800

/-- EIP-1283 refund when resetting a dirty slot back to its zero
    original (cancels the prior 20000 "fresh set" charge minus the
    200 dirty re-charge). -/
def sSetRefund : Gas.Gas := 19800

/-- Per-word keccak256 cost (6 gas), reused for CREATE2's
    `keccak256(init_code)` initcode-hash charge. -/
def keccak256Word : Gas.Gas := Evm.Frontier.Vm.Gas.keccak256Word

end Evm.Constantinople.Vm.Gas
