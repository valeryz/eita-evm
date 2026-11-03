/-
  Evm.Shanghai.Withdrawals — EIP-4895 withdrawal record.

  EELS reference: ethereum/forks/shanghai/blocks.py (`Withdrawal`,
  lines ~24-32).

  A `Withdrawal` is a credit issued from the beacon chain to an
  execution-layer address. They are listed in the block body
  (`Block.withdrawals`) and summed into the corresponding accounts
  *after* every transaction in the block has executed (EELS
  `process_withdrawal` in `forks/shanghai/fork.py` line ~430).

  Amounts on the wire are in **gwei** (1 gwei = 10^9 wei). The
  multiplication to wei happens in `processWithdrawal`.
-/

import Evm.BaseTypes

namespace Evm.Shanghai

/-- EELS `forks/shanghai/blocks.py:Withdrawal`. -/
structure Withdrawal where
  /-- Monotonically increasing identifier issued by the beacon chain. -/
  index          : Nat
  /-- Index of the validator the credit is for. -/
  validatorIndex : Nat
  address        : Evm.Address
  /-- Amount in **gwei** (not wei). Convert to wei via
      `amount * 10^9` when crediting the account. -/
  amount         : Nat
  deriving Repr, Inhabited

namespace Withdrawal

/-- Convert the gwei amount to wei. -/
def amountWei (w : Withdrawal) : Evm.U256 :=
  Evm.U256.ofNat (w.amount * 10 ^ 9)

end Withdrawal

end Evm.Shanghai
