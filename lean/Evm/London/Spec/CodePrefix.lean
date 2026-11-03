/-
  Evm.London.Spec.CodePrefix — EIP-3541 deployed-code prefix
  restriction.

  EELS reference: `forks/london/vm/instructions/system.py` (the
  CREATE / CREATE2 deposit branch) and `forks/london/fork.py`
  (the contract-creation tx deposit branch). Both deposit paths
  add an extra validity check on the to-be-deployed bytecode:

    ```
    if len(deploy_code) > 0 and deploy_code[0] == 0xEF:
        raise InvalidContractPrefix
    ```

  EIP-3541's rationale is to reserve the 0xEF prefix for a future
  EVM Object Format (EOF) without colliding with any existing
  on-chain bytecode. The check applies UNIFORMLY to:
    * Contract-creation transactions (tx.to == None).
    * CREATE opcode deposits.
    * CREATE2 opcode deposits.
  And it applies ONLY to the freshly-DEPLOYED code, NOT to the
  init-code that's executed to produce it. (The init-code itself
  can start with 0xEF; only its return value can't.)

  ## What's encoded vs glossed

  * Encoded: the empty-code special case (zero-length deploy code
    is always valid — fall-through to the existing no-code branch).
  * Encoded: the 0xEF check on the first byte.
  * Glossed: the deposit cost charge (200 gas/byte; unchanged from
    Frontier; lives in the create-step relation).
  * Glossed: the EIP-170 code-size cap (24576 bytes) — that's
    SpuriousDragon, inherited.
-/

import Evm.BaseTypes

namespace Evm.London.Spec

/-- The reserved EOF tag byte. EIP-3541. -/
def eofPrefixByte : UInt8 := 0xEF

/-- `IsValidDeployedCode bytes` — the bytes are admissible as
    deployed contract code under London (and beyond) rules. Any
    non-empty bytecode whose first byte is `0xEF` is rejected. -/
def IsValidDeployedCode (bytes : Evm.Bytes) : Prop :=
  bytes.size = 0 ∨ bytes.get! 0 ≠ eofPrefixByte

/-! ## Properties -/

/-- Empty code is always valid. -/
theorem empty_code_valid : IsValidDeployedCode Evm.Bytes.empty := by
  left; rfl

/-- The predicate is decidable (the body is a disjunction of two
    decidable comparisons). Useful as a refinement hook — the
    implementation can compute it and pattern-match. -/
instance (bytes : Evm.Bytes) : Decidable (IsValidDeployedCode bytes) := by
  unfold IsValidDeployedCode
  exact inferInstance

end Evm.London.Spec
