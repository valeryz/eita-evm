/-
  Evm.Frontier.Vm.Settle — the end of every fork's transaction: the fee settlement and the
  end-of-tx deletions (EELS `process_transaction` after `process_message_call`). One home
  for the functions `Evm.Frontier.Vm.Tx.run` ends with and the derived effects are proved
  against (`Evm.CL.EffectSettleProof`, `Evm.CL.EffectEndTxProof`); the names keep their
  fork namespaces.
-/

import Evm.Frontier.Vm

namespace Evm.Frontier

open Evm.Frontier.Vm (Log)

/-- Result of running a single transaction. -/
structure TxResult where
  state    : State
  gasUsed  : Nat
  logs     : List Log
  success  : Bool
  deriving Inhabited

/-- The fee settlement (EELS frontier/fork.py `process_transaction`, after the message):
    refund the sender `refundWei` (its unused gas at the gas price), then credit the miner
    `minerWei` (`set_account_balance` of `balance + fee`, which creates the coinbase even
    for a zero fee). Derived as `Evm.CL.EffectSettle` (proved in `EffectSettleProof`). -/
def settleFees (s : State) (sender coinbase : Evm.Address) (refundWei minerWei : Nat) : State :=
  (s.addBalance sender (Evm.U256.ofNat refundWei)).addBalance coinbase (Evm.U256.ofNat minerWei)

/-- The end-of-tx deletion (EELS `process_transaction`: `for address in
    accounts_to_delete: destroy_account`), after the fee settlement, on every fork. From
    Cancun the set holds only accounts created in the tx (EIP-6780) — decided when the
    SELFDESTRUCT runs, not here. Derived as `Evm.CL.EffectEndTx` (proved in
    `EffectEndTxProof`). -/
def destroyAccounts (s : State) (destroyed : List Evm.Address) : State :=
  destroyed.foldl (fun st addr => st.deleteAccount addr) s

end Evm.Frontier

namespace Evm.SpuriousDragon

open Evm.Frontier (State Account)

/-- EIP-161 end-of-tx step: delete every account in the `touched` set
    that is now empty. The `touched` set is populated by
    `Evm.SpuriousDragon.Vm.touchAddr` (CALL family, CREATE,
    SELFDESTRUCT beneficiary) and seeded with sender + recipient/new
    address at the tx entry.

    The empty test is exactly EELS `account_is_empty`:
    `(nonce, balance, code) = 0`. STORAGE IS IRRELEVANT — a touched
    account that is empty in the three fields is deleted even if it
    still holds storage entries (which the deletion then discards).
    This matches mainnet: e.g. 0xd29dfe5a, the value-0 tx recipient of
    block 4457731, is empty-with-storage and gets swept (the post-#37
    4.5M state-root divergence; an earlier `¬ hasStorage` survivor
    clause wrongly kept it). The reverted-frame case it was meant to
    paper over is handled correctly by revert-scoping `touched` (a touch
    inside a reverted sub-frame never reaches this sweep — see
    `Evm.SpuriousDragon.Vm.Effect`). -/
def sweepEmptyAccounts (s : State) (touched : List Evm.Address) : State :=
  touched.foldl (fun st addr =>
    let acc := st.getAccount addr
    if st.accountExists addr ∧ acc.isEmpty then
      st.deleteAccount addr
    else st) s

/-- The EIP-161 coinbase credit (EELS spurious_dragon/fork.py `process_transaction`):
    `coinbase_balance_after_mining_fee = balance + fee`; if it is non-zero, set it;
    otherwise, if the coinbase exists and is empty, destroy it — a zero-fee tx neither
    creates an empty coinbase nor keeps one. The same rule holds to the last fork:
    constantinople … london/fork.py carry it verbatim, and from Paris EELS's
    `create_ether` → `modify_state` destroys an account a modification leaves empty
    (EIP-7523), which on the coinbase is this rule again. -/
def payCoinbase (s : State) (coinbase : Evm.Address) (minerWei : Nat) : State :=
  let coinbaseAcc := s.getAccount coinbase
  let coinbaseBalanceAfter := coinbaseAcc.balance + Evm.U256.ofNat minerWei
  if coinbaseBalanceAfter ≠ (0 : Evm.U256) then
    s.setAccount coinbase { coinbaseAcc with balance := coinbaseBalanceAfter }
  else if s.accountExists coinbase ∧ coinbaseAcc.isEmpty then
    s.deleteAccount coinbase
  else
    s

/-- The fee settlement from Spurious Dragon on: refund the sender its unused gas, then
    `payCoinbase`. Derived as `Evm.CL.EffectSettle` (proved in `EffectSettleProof`). -/
def settleFees (s : State) (sender coinbase : Evm.Address) (refundWei minerWei : Nat) : State :=
  payCoinbase (s.addBalance sender (Evm.U256.ofNat refundWei)) coinbase minerWei

/-- The end of a tx from Spurious Dragon: the accounts_to_delete, then the EIP-161 sweep
    of the touched accounts left empty (EELS `destroy_touched_empty_accounts`; from Paris
    EELS drops the sweep because `modify_state` already destroys an account a write leaves
    empty and EIP-7523 rules out pre-existing empty accounts — the same states). Derived as
    `Evm.CL.EffectEndTx` (proved in `EffectEndTxProof`). -/
def finishTx (s : State) (destroyed touched : List Evm.Address) : State :=
  sweepEmptyAccounts (Evm.Frontier.destroyAccounts s destroyed) touched

end Evm.SpuriousDragon
