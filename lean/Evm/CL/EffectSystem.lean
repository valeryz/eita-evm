import Evm.CL.EffectTx
import Evm.Frontier.Vm.System

/-! # CL/EffectSystem — a system call, derived (docs/effect-layer-derivation.md §4.14)

A system transaction's effect (EELS `process_unchecked_system_transaction`, and the code rule
of `process_checked_system_transaction`) as one `EffectIR` term for every fork, proved in
`Evm.CL.EffectSystemProof` against `Evm.Frontier.Vm.System.message` and emitted as
`spec-system-effect`. It is the tx term's tail without the validation, the charge and the
authorizations:

* the target loaded; a checked call (`checked`: EIP-7002, EIP-7251) to a target without
  code is rejected (`reject 1`: the block is invalid);
* the chain rule's warm-up (`warmSys`; EELS: nothing — not the caller, the target or the
  precompiles; Arc: arc-node's, `Evm.Arc.Spec.BlockSystem.systemRule`);
* from Prague the target's delegation (`delegS`), then the message (the tx term's for a
  call: the snapshot, the observed top frame, `callPath` — the fork's precompile at the target
  or the frame —, its end), with `SYSTEM_ADDRESS` as the sender, no value, the whole
  `SYSTEM_TRANSACTION_GAS` and no intrinsic gas.

The wrapper (`system-call`, block-system.lisp) installs the chain rule (the warm-up as
`*system-seed*`, GASPRICE in the block context), calls the term, refuses a rejection and —
for a checked call — a failure (EELS `InvalidBlock`), and runs the end of tx only where the
chain's rule commits one (Arc; EELS drops the accounts_to_delete and the touched set). -/

namespace Evm.CL.EffectSystem

open Evm.CL.EffectIR

/-- The system call's effect. Inputs: `target`, `data`, `checked`, `prague` (EIP-7702 on), the
    block context (for the frame); bound by the defun: `sender` = `SYSTEM_ADDRESS`, no
    creation, value 0, `gas-limit` = `SYSTEM_TRANSACTION_GAS`, no intrinsic gas. Returns the
    gas the message used, the success flag, the rejection. -/
def term : Stmt :=
  .seq (.fault EffectTx.target) <|
  .ite (.and (.var "checked") (.codeEmpty EffectTx.target)) (.reject 1) <|
  .seq .warmSys <| EffectTx.delegS message

where
  /-- The tx term's message (`messageS`) for a call: the snapshot, then in the observed top
      frame the call path. -/
  message : Stmt := .save "snap" <| .txRow EffectTx.gas EffectTx.callPath

def params : List String := ["target", "data", "checked", "prague", "block-ctx"]

/-- `SYSTEM_ADDRESS` as a Lisp literal. -/
def senderCL : String :=
  "#x" ++ (String.ofList (Nat.toDigits 16 Evm.Frontier.Vm.System.systemAddressNat)).toUpper

def termCL : String :=
  s!"(defun spec-system-effect ({" ".intercalate params})\n  (let ((sender {senderCL}) (create nil) (value 0) (gas-limit {Evm.Frontier.Vm.System.systemGas}) (intrinsic 0)\n        (%gas 0) (%out 0) (%rej 0) (%child nil) (%rd nil))\n    (declare (ignorable create %child %rd))\n{Stmt.body "    " term}\n    (values %gas %out %rej)))"

end Evm.CL.EffectSystem
