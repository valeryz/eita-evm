/-
  Evm.Frontier.Vm.Block — the block's own state changes around its transactions, for every
  fork: the block and ommer rewards (EELS `pay_rewards`, Frontier..London) and the EIP-4895
  withdrawals (EELS `process_withdrawals`, Shanghai+). One definition keyed on the fork
  ordinal (`Evm.Fork.ord`), which every fork's `applyBlock` calls and the derived effect
  (`Evm.CL.EffectBlock`, proved in `Evm.CL.EffectBlockProof`) is proved against.

  The amounts are the emitted formulas (`Evm.CL.GasEmit.blockBaseReward`,
  `uncleInclusionBonus`, `uncleReward`); `Evm.CL.GasEmitParis.blockBaseReward_eq_rewardAt`
  proves the base reward the fork schedule (5 ETH, EIP-649 3 ETH, EIP-1234 2 ETH, EIP-3675
  none).
-/

import Evm.Frontier.State
import Evm.CL.GasEmit

namespace Evm.Frontier.Vm.Block

open Evm.Frontier (State)

/-- The formulas' inputs: the fork, an ommer's number, the block's number. -/
def env (k u n : Nat) : Evm.CL.GasEmit.Env := fun y =>
  if y = "fork-ord" then k else if y = "uncle-num" then u else if y = "block-num" then n else 0

/-- EELS `pay_rewards` (frontier/fork.py:554-591, unchanged to london/fork.py:683):
    `miner_reward = BLOCK_REWARD + ommer_count * (BLOCK_REWARD // 32)`. -/
def minerReward (k nOmmers : Nat) : Nat :=
  Evm.CL.GasEmit.blockBaseReward.eval (env k 0 0)
    + nOmmers * Evm.CL.GasEmit.uncleInclusionBonus.eval (env k 0 0)

/-- EELS `pay_rewards`: `((8 - ommer_age) * BLOCK_REWARD) // 8`, `ommer_age = number −
    ommer.number` (1..6 for a valid ommer, where the emitted `(8 + u − n)` agrees). -/
def ommerReward (k number u : Nat) : Nat :=
  Evm.CL.GasEmit.uncleReward.eval (env k u number)

/-- EELS `pay_rewards`: `create_ether` to the coinbase, then to each ommer's coinbase in
    order. From Paris (EIP-3675) `apply_body` calls no `pay_rewards`: nothing is credited,
    so an absent coinbase stays absent. OMMERS are (coinbase, number). -/
def payRewards (k : Nat) (st : State) (coinbase : Evm.Address) (number : Nat)
    (ommers : List (Evm.Address × Nat)) : State :=
  if k ≥ 14 then st
  else ommers.foldl (fun s o => s.addBalance o.1 (Evm.U256.ofNat (ommerReward k number o.2)))
         (st.addBalance coinbase (Evm.U256.ofNat (minerReward k ommers.length)))

/-- One withdrawal (EELS shanghai/fork.py:646 `create_ether(wd_state, wd.address,
    U256(wd.amount) * U256(10**9))`; the amount is in gwei). `create_ether` is
    `modify_state` (shanghai/state_tracker.py:480-492), which destroys the account if it
    exists and is empty afterwards: a zero withdrawal to an absent or empty account leaves
    none. W is (address, amount). -/
def withdraw (st : State) (w : Evm.Address × Nat) : State :=
  let st := st.addBalance w.1 (Evm.U256.ofNat (w.2 * 1000000000))
  if (st.getAccount w.1).isEmpty then st.deleteAccount w.1 else st

/-- EELS `process_withdrawals` (shanghai/fork.py:629-648; the same through amsterdam): the
    block's withdrawals in order, from Shanghai. -/
def processWithdrawals (k : Nat) (st : State) (ws : List (Evm.Address × Nat)) : State :=
  if k ≥ 15 then ws.foldl withdraw st else st

/-- The block's own state changes after its transactions (EELS `apply_body`): the rewards,
    then the withdrawals. -/
def postBlock (k : Nat) (st : State) (coinbase : Evm.Address) (number : Nat)
    (ommers ws : List (Evm.Address × Nat)) : State :=
  processWithdrawals k (payRewards k st coinbase number ommers) ws

end Evm.Frontier.Vm.Block
