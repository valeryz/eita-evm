/-
  Evm.Byzantium.Spec.PrecompileTable — what's at 0x01..0x08 at
  Byzantium and how dispatch MUST happen.

  EELS reference: `forks/byzantium/vm/precompiled_contracts/__init__.py`
  `PRE_COMPILED_CONTRACTS` mapping (the dispatch table).

  ## Why this needs to be a spec

  During the 2026-05-30 validation push, EVERY post-Byzantium fork's
  trampoline and `processTransaction` was found to be calling
  `Evm.Frontier.Vm.PrecompiledContracts.lookup` (Frontier's
  4-precompile table) for the precompile-dispatch step. The
  unqualified `PrecompiledContracts.lookup` resolved through `open
  Evm.Frontier.Vm` to Frontier's table — so any CALL or
  tx-with-`to`=0x05 ran the empty-account-code path instead of the
  precompile. The bug was silent at the implementation level (no
  type error, no obvious wrong output for most tests) — but
  catastrophic for the modexp / bn256 corpora.

  Implementations are free to merge the table with the dispatch
  decision however they like, BUT the **table itself** is a fork-
  level invariant: at Byzantium the set of precompile addresses MUST
  be `{0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08}`. Future
  forks may add but MUST NOT remove.

  ## The table

  | Address | Name                  | Source                |
  |---------|-----------------------|-----------------------|
  | 0x01    | ECRECOVER             | Frontier              |
  | 0x02    | SHA256                | Frontier              |
  | 0x03    | RIPEMD160             | Frontier              |
  | 0x04    | IDENTITY              | Frontier              |
  | 0x05    | MODEXP                | Byzantium  (EIP-198)  |
  | 0x06    | BN256_ADD             | Byzantium  (EIP-196)  |
  | 0x07    | BN256_MUL             | Byzantium  (EIP-196)  |
  | 0x08    | BN256_PAIRING_CHECK   | Byzantium  (EIP-197)  |

  Forks added later:
    Istanbul:  0x09 BLAKE2F (EIP-152)
    Cancun:    0x0a KZG point-evaluation (EIP-4844)
    Prague:    0x0b..0x11 BLS12-381 (EIP-2537)

  ## Dispatch invariant

  Any CALL / CALLCODE / DELEGATECALL / STATICCALL whose `to` matches
  a precompile address MUST invoke the precompile rather than
  executing account code at that address. Same for a tx whose `to`
  is a precompile (`tx.to ∈ precompileAddresses`).

  Implementations that mis-route precompile addresses to the bytecode
  path silently produce empty output and charge only the call's base
  gas — invariants in this file are the formal way to prevent that
  regression.
-/

import Evm.BaseTypes

namespace Evm.Byzantium.Spec

/-- The Byzantium precompile address set. Forks are free to add more
    addresses but MUST keep these eight. -/
def precompileAddresses : List Evm.Address :=
  [ Evm.Address.ofNat 0x01
  , Evm.Address.ofNat 0x02
  , Evm.Address.ofNat 0x03
  , Evm.Address.ofNat 0x04
  , Evm.Address.ofNat 0x05    -- MODEXP    (EIP-198)
  , Evm.Address.ofNat 0x06    -- BN256_ADD (EIP-196)
  , Evm.Address.ofNat 0x07    -- BN256_MUL (EIP-196)
  , Evm.Address.ofNat 0x08    -- BN256_PAIRING (EIP-197)
  ]

/-- `IsPrecompile addr` — true iff `addr` should dispatch to the
    precompile handler at the Byzantium fork. -/
def IsPrecompile (addr : Evm.Address) : Prop :=
  addr ∈ precompileAddresses

/-! ## Dispatch invariant

    The "precompile or bytecode" decision is a binary choice that
    every CALL family opcode AND the tx-level `to` dispatch must
    make. Implementations that pick the wrong branch silently turn
    a precompile invocation into an empty-bytecode no-op.

    `DispatchSound dispatch` is the predicate that an implementation's
    dispatch function honours the table: precompile addresses route
    to the precompile path, others route to the bytecode path. -/

inductive DispatchBranch where
  | precompile  -- run the precompile handler
  | bytecode    -- run the callee account's code (empty if absent)
  deriving Inhabited, DecidableEq

/-- An implementation's dispatch function is sound iff it picks the
    precompile branch exactly for precompile addresses. -/
def DispatchSound (dispatch : Evm.Address → DispatchBranch) : Prop :=
  ∀ addr,
    (IsPrecompile addr → dispatch addr = DispatchBranch.precompile) ∧
    (¬ IsPrecompile addr → dispatch addr = DispatchBranch.bytecode)

end Evm.Byzantium.Spec
