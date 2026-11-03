/-
  Evm.DaoFork — irregular-state-change fork after The DAO hack.

  EELS reference: ethereum/dao_fork/.
  Activation: block 1,920,000 (2016-07-20).

  No EVM rule changes. Performs a one-time, hard-coded balance transfer
  from a list of DAO-related accounts into a withdrawal contract. The
  state transition is otherwise identical to Homestead.
-/

namespace Evm.DaoFork
end Evm.DaoFork
