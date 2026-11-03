/-
  Evm.Berlin.Vm.Gas — EIP-2929 / EIP-2930 / EIP-2565 gas constants.

  EELS reference: ethereum/forks/berlin/vm/gas.py.

  Berlin overhauls state-access pricing with warm/cold accounting
  (EIP-2929) and introduces the EIP-2930 access list with its own
  per-address / per-storage-key intrinsic costs. The previous TW/SD
  constants (CALL = 700, SLOAD = 200, BALANCE = 700, EXTCODE = 700)
  are superseded by the warm/cold pair below — *only* via the Berlin
  Effect dispatch path; the underlying TW/SD constants stay where
  they are so earlier forks keep working unchanged.

  Cited values are the canonical EELS constants (which match the
  EIP texts verbatim). The Lean delta-only-forks convention means
  these names are the *single source of truth* for Berlin gas:

  Constants (EELS `forks/berlin/vm/gas.py`):
    WARM_ACCESS_COST                 = 100
    COLD_SLOAD_COST                  = 2100
    COLD_ACCOUNT_ACCESS_COST         = 2600
    ACCESS_LIST_ADDRESS_COST         = 2400  (intrinsic, per address)
    ACCESS_LIST_STORAGE_KEY_COST     = 1900  (intrinsic, per key)

  EIP-2929 numbers (which EELS adopts verbatim):
    * SLOAD                cold 2100 / warm 100      (was TW 200)
    * BALANCE              cold 2600 / warm 100      (was TW 700)
    * EXTCODESIZE          cold 2600 / warm 100      (was TW 700)
    * EXTCODECOPY          cold 2600 / warm 100      (was TW 700)
    * EXTCODEHASH          cold 2600 / warm 100      (was Constantinople 700)
    * CALL family          cold 2600 / warm 100      (was TW 700)
    * SELFDESTRUCT         cold beneficiary +2600    (additive surcharge)
    * SSTORE               +2100 surcharge on cold slot

  EIP-2565 (modexp re-pricing) — handled in the Berlin modexp
  precompile (not yet implemented here, see Berlin/Vm/PrecompiledContracts).
-/

namespace Evm.Berlin.Vm.Gas

/-- EIP-2929 warm access cost. Charged when an address or storage key
    is already in the relevant warm set (sender, tx.to, precompiles
    0x01..0x09, EIP-2930 entries, or anything touched earlier in the
    same tx). Replaces TW's 200/700 baselines. -/
def warmAccess : Nat := 100

/-- EIP-2929 cold SLOAD cost. Charged on the first SLOAD of an
    `(address, slot)` pair in a transaction; subsequent loads cost
    `warmAccess`. -/
def coldSload : Nat := 2100

/-- EIP-2929 cold account-access cost. Charged on the first
    BALANCE / EXTCODESIZE / EXTCODECOPY / EXTCODEHASH / CALL family
    touch of an address in a transaction. -/
def coldAccountAccess : Nat := 2600

/-- EIP-2929 SSTORE cold surcharge. Charged on the first SSTORE to a
    cold `(address, slot)` pair (in *addition* to the EIP-2200
    net-gas-metering cost). -/
def sstoreColdSurcharge : Nat := coldSload

/-- EIP-2930 intrinsic cost per access-list address. Paid up-front in
    `intrinsicGas` so the listed address starts the tx warm. -/
def accessListAddress : Nat := 2400

/-- EIP-2930 intrinsic cost per access-list storage key. Paid up-front
    in `intrinsicGas` so the listed `(address, slot)` pair starts the
    tx warm. -/
def accessListStorageKey : Nat := 1900

end Evm.Berlin.Vm.Gas
