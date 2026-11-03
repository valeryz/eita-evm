/-
  Evm.Shanghai.Spec.InitcodeCap — EIP-3860 init-code size cap +
  per-word metering.

  EELS reference: `forks/shanghai/vm/interpreter.py` line 63
  (`MAX_INIT_CODE_SIZE = 2 * MAX_CODE_SIZE`) and
  `forks/shanghai/vm/gas.py` lines 55, 347-364
  (`CODE_INIT_PER_WORD = 2`, `init_code_cost`).

  Two things the EIP introduces:

    1. A hard cap on the length of init code: `len ≤ 49152` bytes,
       enforced at BOTH the opcode level (CREATE/CREATE2) AND the
       transaction level (tx-CREATE = tx with `to = none`).

    2. A new per-32-byte-word surcharge on init code:
       `init_code_cost(L) = 2 · ceil(L / 32)`. Charged in addition to
       the base CREATE / CREATE2 cost and on top of the tx-CREATE
       intrinsic gas.

  This file states the cap predicate and the surcharge formula. The
  CREATE / CREATE2 step relations themselves are large (they yield a
  sub-frame); we don't re-state the entire shape here, just the bits
  EIP-3860 modifies. A future Shanghai-CallStep refinement will assert
  that the new relations agree with these constants.

  Inheritance: cap + per-word surcharge are unchanged at Cancun and
  Prague. Prague's intrinsic gas (EIP-7623) is computed on top of the
  same `initCodeCost` formula; see `Evm.Prague.Fork.intrinsicGas`.
-/

import Evm.BaseTypes
import Evm.SpuriousDragon.Vm.Gas
import Evm.Forks

namespace Evm.Shanghai.Spec

/-- `MAX_CODE_SIZE` from EIP-170 (Spurious Dragon), reused as the
    base of the init-code limit. EELS:
    `forks/shanghai/vm/interpreter.py` line 63
    (`MAX_INIT_CODE_SIZE = 2 * MAX_CODE_SIZE`). -/
def maxInitCodeSize : Nat := 2 * Evm.SpuriousDragon.Vm.Gas.maxCodeSize

/-- The per-word constant. EELS `forks/shanghai/vm/gas.py` line 55
    (`CODE_INIT_PER_WORD = 2`). -/
def codeInitPerWord : Nat := 2

/-- EIP-3860 init-code metering: `2 · ceil(len / 32)`. Used in three
    places: CREATE (0xf0) extra gas, CREATE2 (0xf5) extra gas, and
    tx-CREATE intrinsic gas surcharge. EELS `forks/shanghai/vm/gas.py`
    lines 347-364 (`init_code_cost`). -/
def initCodeCost (initCodeLen : Nat) : Nat :=
  codeInitPerWord * ((initCodeLen + 31) / 32)

/-! ## Cap predicate

    Used at three sites:
      * `IsCreateStep` precondition: pop'd `len` must satisfy the cap.
      * `IsCreate2Step` precondition: same.
      * Transaction validation (`processTransaction`): if `tx.to = none`
        then `tx.data.size ≤ maxInitCodeSize`. EELS:
        `forks/shanghai/transactions.py::validate_transaction` line 332. -/

/-- The init-code-length cap predicate. `true` ↔ the length is accepted
    at Shanghai (and at all later forks — never relaxed). -/
def InitcodeWithinCap (initCodeLen : Nat) : Prop :=
  initCodeLen ≤ maxInitCodeSize

/-! ## Surcharge predicates

    A CREATE / CREATE2 / tx-CREATE that pays the EIP-3860 surcharge
    deducts `initCodeCost(L)` gas on top of the predecessor's cost
    schedule. We expose the formula and a `Prop` form for use by the
    CREATE specs / tx-intrinsic-gas spec. -/

/-- The extra gas a CREATE / CREATE2 charges at Shanghai+ that wasn't
    charged at Paris. Folded into `IsCreateStep`'s gas precondition by
    the Shanghai CallStep spec. -/
abbrev createInitSurcharge (initCodeLen : Nat) : Nat :=
  initCodeCost initCodeLen

/-- The extra intrinsic gas a contract-creation transaction
    (`tx.to = none`) pays at Shanghai+. EELS
    `forks/shanghai/transactions.py` line 369-370:
        `create_cost = GasCosts.TX_CREATE + init_code_cost(ulen(tx.data))`. -/
abbrev txCreateInitSurcharge (initCodeLen : Nat) : Nat :=
  initCodeCost initCodeLen

/-! ## Notes

    * The cap and the surcharge are bundled in one file because they
      were introduced by the same EIP and apply at the same set of
      call sites (CREATE, CREATE2, tx-CREATE). Splitting them would
      duplicate the EIP citation across two modules.

    * The implementation (`Evm.Shanghai.Vm.Effect.doCreate` /
      `doCreate2` / `Evm.Shanghai.Fork.intrinsicGas`) defines its
      own `initCodeCost` / `maxInitCodeSize` constants which agree
      with the ones here by construction; the refinement pass when
      it lands will discharge that equality. -/

/-! ## Fork-conditional value (iff form)

    EIP-3860 introduces two changes at Shanghai:
      (a) per-word init-code surcharge of `codeInitPerWord`;
      (b) hard cap at `maxInitCodeSize`.

    Both kick in iff Shanghai-or-later. -/

/-- Fork-parametric per-word init-code surcharge. -/
def initCodeCostAt (f : Evm.Fork) (initCodeLen : Nat) : Nat :=
  if f.atLeast .shanghai then initCodeCost initCodeLen else 0

/-- The surcharge is non-zero for non-empty init code iff Shanghai+. -/
theorem surcharge_active_iff_shanghai (f : Evm.Fork) :
    initCodeCostAt f 32 > 0 ↔ f.atLeast .shanghai := by
  unfold initCodeCostAt initCodeCost
  cases f <;> decide

/-- Fork-parametric init-code cap. -/
def initcodeWithinCapAt (f : Evm.Fork) (initCodeLen : Nat) : Bool :=
  if f.atLeast .shanghai then decide (initCodeLen ≤ maxInitCodeSize) else true

/-- The cap rejects oversized init code iff Shanghai+. Witnessed by a
    length one past the cap. -/
theorem cap_active_iff_shanghai (f : Evm.Fork) :
    initcodeWithinCapAt f (maxInitCodeSize + 1) = false ↔ f.atLeast .shanghai := by
  unfold initcodeWithinCapAt
  cases f <;> decide

end Evm.Shanghai.Spec
