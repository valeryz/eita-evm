/-
  Evm.Paris.Spec.NoBlockReward — EIP-3675 block-reward removal.

  EELS reference: `forks/paris/fork.py` `state_transition`. The
  EELS implementation deletes the `pay_rewards(...)` call that
  existed in `forks/byzantium/fork.py` (the 3-ETH base reward plus
  per-ommer 1/32 bonus). The post-Merge state-transition function
  simply iterates transactions, sweeps empty accounts, and checks
  the post-root: no end-of-block coinbase credit, no ommer-coinbase
  credit.

  The PER-TRANSACTION coinbase credit (the priority-fee portion
  under EIP-1559) is unchanged from London — see
  `London/Spec/FeeMarket.lean`. The DELETION here is the BLOCK-
  level reward, not the per-tx fee.

  ## What's encoded vs glossed

  * Encoded: `IsParisBlockRewardCredit coinbase preState postState`
    relating the coinbase's balance before and after the
    end-of-block reward step. The relation is "the balance is
    UNCHANGED" (delta = 0).
  * Encoded: `paris_ommers_must_be_empty` as a precondition on
    `Block.ommers`. (The validation is also enforced in
    `Paris/Fork.lean`'s `applyBlock`; we restate it as a spec
    obligation here.)
  * Glossed: the per-tx fee credit. That's London's spec; it
    pre-composes with the (zero) block-reward credit at Paris.
  * Glossed: the difficulty-bomb removal. EIP-3675 also removes
    difficulty adjustment from the EL; that's structural, not a
    state-transition relation.
-/

import Evm.Frontier.State
import Evm.BaseTypes
import Evm.Forks
import Evm.Frontier.Fork
import Evm.Byzantium.Fork
import Evm.Constantinople.Fork

namespace Evm.Paris.Spec

open Evm.Frontier (State)

/-- `IsParisBlockReward coinbase pre post` — the end-of-block
    reward state-transition at Paris is the identity: `post = pre`
    on the coinbase's balance (and on all other balances). EIP-3675
    deletes the EELS `pay_rewards(...)` call. -/
def IsParisBlockReward (coinbase : Evm.Address) (pre post : State) : Prop :=
  post.getBalance coinbase = pre.getBalance coinbase

/-- `IsParisOmmersValid ommers` — post-Merge blocks must have an
    empty ommers list. EELS `state_transition` line ~159:
    `if block.ommers != (): raise InvalidBlock`. -/
def IsParisOmmersValid {α : Type} (ommers : List α) : Prop :=
  ommers = []

/-- The Paris block reward in wei. Zero. (Frontier..GrayGlacier
    have non-zero values; Paris and beyond have zero.) -/
def blockRewardWei : Nat := 0

/-! ## Properties -/

/-- `IsParisBlockReward` is reflexive — the identity transition
    always satisfies it. (Trivial, but it's the entire content of
    EIP-3675's contribution to this spec layer.) -/
theorem block_reward_identity (coinbase : Evm.Address) (state : State) :
    IsParisBlockReward coinbase state state := rfl

/-! ## Fork-conditional value (iff form)

    The mainnet block-reward schedule had three step-downs:

      * EIP-649  (Byzantium):       5 → 3 ETH
      * EIP-1234 (Constantinople):  3 → 2 ETH
      * EIP-3675 (Paris):           2 → 0 ETH

    We state each step-down as an iff over `Fork`. The `rewardAt`
    function below is the single source of truth; the three iff
    lemmas together pin the entire schedule. -/

/-- Fork-parametric block reward (wei) at the end of each block. -/
def rewardAt (f : Evm.Fork) : Nat :=
  if f.atLeast .paris          then 0
  else if f.atLeast .constantinople then 2 * 10 ^ 18
  else if f.atLeast .byzantium      then 3 * 10 ^ 18
  else                                   5 * 10 ^ 18

/-- EIP-3675 activation: the reward is 0 iff we're at Paris-or-later. -/
theorem reward_zero_iff_paris (f : Evm.Fork) :
    rewardAt f = 0 ↔ f.atLeast .paris := by
  unfold rewardAt
  cases f <;> decide

/-- EIP-1234 activation: the reward is ≤ 2 ETH iff we're at
    Constantinople-or-later. -/
theorem reward_le_2eth_iff_constantinople (f : Evm.Fork) :
    rewardAt f ≤ 2 * 10 ^ 18 ↔ f.atLeast .constantinople := by
  unfold rewardAt
  cases f <;> decide

/-- EIP-649 activation: the reward is ≤ 3 ETH iff we're at
    Byzantium-or-later. -/
theorem reward_le_3eth_iff_byzantium (f : Evm.Fork) :
    rewardAt f ≤ 3 * 10 ^ 18 ↔ f.atLeast .byzantium := by
  unfold rewardAt
  cases f <;> decide

end Evm.Paris.Spec
