/-
  Evm.Optimism.Bedrock.Spec.DepositedTx — type-0x7E "deposited"
  transactions.

  Source: optimism-specs `specs/protocol/deposits.md` (Bedrock).
  Geth-side: op-geth `core/types/deposit_tx.go`.

  A deposited tx is the OP Stack's way of injecting L1-originated
  state changes (user deposits, L1 attribute updates) into L2 state.
  Distinguishing features vs. a regular EIP-2718 typed tx:

    * tx_type byte    = 0x7E
    * no signature    — `from` is encoded directly in the envelope
    * no chain id     — replay-protected by L1 origin
    * no nonce        — sequencer chooses ordering by `source_hash`
    * may MINT ETH    — the `mint` field credits the sender's account
                         before execution (used to bridge ETH from L1)
    * gas LIMIT only  — no gas-price (deposited gas is paid for at
                         deposit time on L1)
    * `is_system_tx`  — if set, gas accounting differs (Pre-Regolith
                         did not deduct gas from block gas pool;
                         Regolith fixed this)
    * `source_hash`   — derived from L1 block hash + L1 log index;
                         used by sequencer for ordering & dedup

  Envelope (RLP):
    [source_hash, from, to, mint, value, gas, is_system_tx, data]

  Execution semantics:
    1. Credit `mint` wei to `from` (creates the account if needed).
    2. If `to = None`: deposited contract creation (rare).
       Else: ordinary message call to `to` with `value` and `data`.
    3. Gas used is charged from block gas pool (post-Regolith).
    4. Failure does NOT roll back the mint — minted ETH stays.
    5. No L1 data fee, no priority fee, no base-fee burn — deposited
       txs are gas-free at the EL level.

  Every L2 block's FIRST tx is a deposited tx that calls the L1Block
  predeploy at 0x4200000000000000000000000000000000000015 with the
  current L1 attributes. See `L1Block.lean`.
-/

import Evm.BaseTypes
import Evm.Optimism.Forks

namespace Evm.Optimism.Bedrock.Spec

/-- Tx-envelope byte for deposited transactions. EIP-2718 transaction-
    type space; 0x7E was picked to be high enough to avoid collision
    with then-pending L1 type allocations. -/
def depositedTxType : UInt8 := 0x7E

/-- A deposited tx is *always* valid from Bedrock onwards (across
    every OP fork). Stated as an iff so any accidental gating of the
    envelope behind a later OP fork breaks here. -/
def acceptsDepositedTxAt (f : Evm.Optimism.OpFork) : Bool :=
  f.atLeast .bedrock

theorem deposited_accepted_iff_bedrock (f : Evm.Optimism.OpFork) :
    acceptsDepositedTxAt f = true ↔ f.atLeast .bedrock := by
  unfold acceptsDepositedTxAt; rfl

/-- Fields of a Bedrock deposited transaction. EELS-equivalent record
    shape; `to = none` ⇒ contract creation. -/
structure DepositedTx where
  sourceHash  : Evm.Hash32
  from_       : Evm.Address
  to          : Option Evm.Address
  mint        : Evm.U256
  value       : Evm.U256
  gas         : Evm.U256
  isSystemTx  : Bool
  data        : Evm.Bytes
  deriving Repr

/-- A deposited tx's gas cost to the block pool, post-Regolith
    (Bedrock launch shipped with Regolith). Both system and user
    deposited txs charge their full `gas` against the block pool. -/
def gasChargedToBlock (tx : DepositedTx) : Nat := tx.gas.toNat

end Evm.Optimism.Bedrock.Spec
