/-
  Evm.Amsterdam.Spec.BlockAccessList — EIP-7928 Block-Level Access Lists
  (stub).

  EELS reference: `forks/amsterdam/block_access_lists.py` (the entire
  module, ~600 lines: `BlockAccessListBuilder`, `BlockAccessList`,
  `build_block_access_list`, `hash_block_access_list`,
  `validate_block_access_list_gas_limit`).

  EIP-7928 reshapes block validation:

    * Every account/storage/code access made during a block is recorded
      in a per-block `BlockAccessList` (BAL) — flat lists of
      `(address, slot, pre_value, post_value)` (storage),
      `(address, pre_balance, post_balance)` (balance),
      `(address, post_code)` (code), plus the list of touched accounts.
    * The header carries `block_access_list_hash` (Keccak of the
      RLP-encoded BAL). Block validity requires the rebuilt BAL hash to
      match the header.
    * BAL construction is gas-metered to bound prover cost; see
      `validate_block_access_list_gas_limit`.
    * `Header.parent_block_access_list_root` is a separate field for the
      stateless-validation use case (the previous block's BAL).

  This file is intentionally a stub. The full BAL machinery is a
  significant addition (a dozen ancillary types, an entire trie-style
  serialiser, gas accounting that crosses every state-mutating opcode)
  and is out of scope for the first-pass Lean spec of Amsterdam. The
  TODOs:

    * Define `BlockAccessList` (per-block list of `BalEntry` tagged
      unions: balance change, code, slot read, slot write, account
      touch).
    * Define `IsBalForBlock : Evm.Prague.Block → BlockAccessList → Prop`
      (the BAL faithfully records the block's accesses).
    * Define `balHash : BlockAccessList → Hash32` mirroring
      `hash_block_access_list`.
    * Add `header.block_access_list_hash = balHash bal` to the
      Amsterdam block validity predicate.
-/

import Evm.BaseTypes

namespace Evm.Amsterdam.Spec

/-- Placeholder for the future BAL type. EELS:
    `forks/amsterdam/block_access_lists.py::BlockAccessList`. -/
abbrev BlockAccessList : Type := Unit

/-- Placeholder hash function. EELS `hash_block_access_list`. -/
def hashBlockAccessList (_bal : BlockAccessList) : Evm.Hash32 := 0

end Evm.Amsterdam.Spec
