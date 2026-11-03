/-
  Evm.Optimism.Bedrock.Transactions — type-0x7E deposited transactions.

  Companion to the Spec module `Optimism/Bedrock/Spec/DepositedTx.lean`.
  This file carries the executable data type + JSON-decoded form.

  RLP envelope: 0x7E || rlp([source_hash, from, to, mint, value, gas,
                              is_system_tx, data]).

  Used by:
    * the L1 → L2 deposit pipeline (user deposits ETH/tokens via the
      OptimismPortal on L1, sequencer emits a deposited tx on L2),
    * the per-block prologue (first tx of every L2 block calls
      L1Block.setL1BlockValues* with the current L1 attributes).
-/

import Evm.BaseTypes

namespace Evm.Optimism.Bedrock

/-- Decoded deposited tx — what callers see after envelope parsing.

    `mint` is the OP-stack "credit before execute" amount. Used to
    bridge ETH from L1 into L2: the L1 OptimismPortal locks ETH on
    L1, emits a `TransactionDeposited` event whose payload becomes
    a deposited tx on L2; the L2-side mint credits the recipient
    even if the call fails.

    `isSystemTx` is preserved for envelope round-tripping. Pre-
    Regolith it altered gas accounting (system txs were free); from
    Regolith onward (i.e. Bedrock launch on Base mainnet) it has no
    semantic effect — all deposited txs charge their full `gas`
    against the block gas pool. -/
structure DepositedTx where
  sourceHash : Evm.Hash32
  from_      : Evm.Address
  to         : Option Evm.Address
  mint       : Evm.U256
  value      : Evm.U256
  gas        : Evm.U256
  isSystemTx : Bool
  data       : Evm.Bytes
  deriving Repr, Inhabited

namespace DepositedTx

/-- Is this the per-block L1-attributes system call?
    Distinguished by `from = depositorAccount` AND
    `to = some l1BlockPredeploy`. -/
def isL1AttributesCall (tx : DepositedTx) : Bool :=
  let depositor : Evm.Address := Evm.Address.ofNat 0xdeaddeaddeaddeaddeaddeaddeaddeaddead0001
  let l1Block   : Evm.Address := Evm.Address.ofNat 0x4200000000000000000000000000000000000015
  tx.from_ = depositor ∧ (tx.to = some l1Block)

/-- A deposited tx is a CREATE iff `to = none`. -/
def isCreate (tx : DepositedTx) : Bool := tx.to.isNone

end DepositedTx

end Evm.Optimism.Bedrock
