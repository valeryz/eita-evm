/-
  Evm.Constantinople.Spec.Create2Step — EIP-1014 CREATE2 (0xf5) entry
  relation.

  EELS reference: `forks/constantinople/vm/instructions/system.py`
  `create2` (the EIP-1014 implementation; current EELS master collapses
  Constantinople into Petersburg but the address-derivation and gas
  formula are preserved).

  CREATE2 differs from Frontier's CREATE in exactly two places:

    1. Gas charge gets an extra `keccak256Word * ceil(initCodeLen/32)`
       summand for hashing the init code into the address derivation
       preimage. EELS gas constant `GAS_KECCAK256_WORD = 6`.

    2. The new contract address is
         `keccak256(0xff || sender || salt || keccak256(initCode))[12:]`
       rather than `keccak256(rlp([sender, nonce]))[12:]`.
       See `Evm.Constantinople.Utils.Address.computeCreate2Address`.

  Sub-frame execution, collision handling, value transfer, nonce bump
  semantics, and code-deposit charging are unchanged from
  Frontier/Homestead CREATE. The implementation lives in
  `Evm.Constantinople.Vm.Effect.doCreate2`; this file is the relation
  form of its entry phase (everything up to the yield handing control
  to the sub-frame).

  ## Structure mirrors `Frontier.Spec.CallStep`
  We name three entry paths:

    * `IsCreate2FailFastDepth` — stack depth ≥ 1024. Push 0, refund
      forwarded gas (i.e. don't sub-frame). State unchanged.
    * `IsCreate2FailFastBalance` — caller can't pay `value`. Same shape
      as depth fast-fail.
    * `IsCreate2EntrySuccess` — all pre-checks pass, the sub-frame is
      provisioned. The post-state here is a `Create2SubFrameSetup`
      witness, not a fully-pinned `evm'`; the trampoline merges the
      sub-frame result back into the parent via the `.createLike`
      yield.

  ## Out of scope
    * EIP-214 static-context check — CREATE2 in a static frame raises;
      we describe only the *successful* (`isStatic = false`) branch.
    * Address collision — described separately as `IsCreate2Entry
      Collision`. **Important:** the collision predicate is
      `nonce > 0 ∨ code.size > 0 ∨ ∃ slot. state[(addr, slot)] ≠ 0`
      — pre-existing STORAGE also flags the slot as in-use, matching
      EELS. This was found via the stSStoreTest/InitCollision +
      stCreate2/create2collisionStorage corpus (2026-05-30) where an
      account with zeros for nonce/code but non-empty storage must
      block CREATE2 from overwriting it.
-/

import Evm.Frontier.Vm
import Evm.Frontier.State
import Evm.Frontier.Vm.Instructions.Memory
import Evm.Constantinople.Vm.Gas
import Evm.Constantinople.Utils.Address

namespace Evm.Constantinople.Spec

open Evm.Frontier (State Account)
open Evm.Frontier.Vm

/-! ## Operand structure -/

/-- The 4 operands CREATE2 pops, in pop order (top first). -/
structure Create2Args where
  value  : Evm.U256
  offset : Nat
  len    : Nat
  salt   : Evm.U256

/-- Combined gas the entry phase charges before the yield:
      `memoryExpansion + create(32000) + 6 * ceil(len/32)`.
    EIP-1014 gas formula; EELS `vm/gas.py`. -/
def Create2.entryGas
    (args : Create2Args) (preMemWords : Nat) : Nat :=
  let postMemWords :=
    max preMemWords ((args.offset + args.len + 31) / 32)
  let memCost := Gas.memoryExpansionCost preMemWords postMemWords
  let initWords := (args.len + 31) / 32
  memCost + Gas.create + Evm.Constantinople.Vm.Gas.keccak256Word * initWords

/-- Max call depth, as in `Byzantium.Vm.Effect.maxCallDepth = 1024`. -/
def maxCallDepth : Nat := 1024

/-! ## Sub-frame setup witness -/

structure Create2SubFrameSetup where
  subMsg         : Message
  newAddr        : Evm.Address
  subState       : State              -- world the sub-frame sees
                                      -- (after nonce bump + value
                                      -- transfer into the new account)
  parentSnapshot : Evm                -- parent state at the moment of
                                      -- yield (memory expanded, entry
                                      -- gas pre-paid, 1/64 retained)
  deriving Inhabited

/-! ## Three entry-path relations -/

/-- Depth-limit fail-fast. Pre-state pops the 4 operands, charges
    memory + create + keccak gas, push 0 onto the result stack, advances
    pc. State is untouched (the sub-frame never ran). -/
def IsCreate2FailFastDepth (evm evm' : Evm) : Prop :=
  ∃ args : Create2Args, ∃ rest,
    evm.stack = args.value :: Evm.U256.ofNat args.offset ::
                Evm.U256.ofNat args.len :: args.salt :: rest ∧
    evm.message.isStatic = false ∧
    evm.message.depth ≥ maxCallDepth ∧
    rest.length < stackLimit ∧
    let entryGas := Create2.entryGas args ((evm.memory.size + 31) / 32)
    evm.gasLeft ≥ entryGas ∧
    evm' = { evm with
      stack      := 0 :: rest,
      gasLeft    := evm.gasLeft - entryGas,
      returnData := Evm.Bytes.empty,
      pc         := evm.pc + 1 }

/-- Balance fail-fast: `value > caller balance`. Same effect as depth
    fail-fast. -/
def IsCreate2FailFastBalance (evm evm' : Evm) : Prop :=
  ∃ args : Create2Args, ∃ rest,
    evm.stack = args.value :: Evm.U256.ofNat args.offset ::
                Evm.U256.ofNat args.len :: args.salt :: rest ∧
    evm.message.isStatic = false ∧
    evm.message.depth < maxCallDepth ∧
    (evm.env.state.getBalance evm.message.currentTarget).toNat < args.value.toNat ∧
    rest.length < stackLimit ∧
    let entryGas := Create2.entryGas args ((evm.memory.size + 31) / 32)
    evm.gasLeft ≥ entryGas ∧
    evm' = { evm with
      stack      := 0 :: rest,
      gasLeft    := evm.gasLeft - entryGas,
      returnData := Evm.Bytes.empty,
      pc         := evm.pc + 1 }

/-- An account is "in use" — and therefore blocks CREATE/CREATE2 —
    iff it has a positive nonce, non-empty code, or non-empty
    storage. This is EELS Constantinople's
    `account_has_code_or_nonce ∨ account_has_storage`
    (`forks/constantinople/vm/instructions/system.py` line 92),
    exercised by stCreate2/create2collisionStorage and
    stExtCodeHash/dynamicAccountOverwriteEmpty.

    The storage clause is a Constantinople-era (and generally
    pre-Cancun) rule. The Cancun-era forks deliberately DROP it for
    op-geth fidelity: there EIP-684 (nonce/code) plus the EIP-7610
    CHAIN-SPECIFIC allowlist (28 mainnet entries, none on Base;
    `eip7610RejectedAccounts` in go-ethereum `core/vm/eip7610.go`)
    governs, and a blanket storage clause rejected legitimate
    redeploys on addresses with dangling storage from a
    pre-EIP-6780 selfdestruct (caught by Base 0x2c99000 tx 50 —
    see `Shanghai.Vm.Effect.isCreateCollision` and commit
    history). -/
def AccountInUse (state : State) (addr : Evm.Address) : Prop :=
  let acc := state.getAccount addr
  acc.nonce > 0 ∨ acc.code.size > 0 ∨
    state.storage.any (fun ((a, _), _) => a = addr) = true

/-- EIP-7610 chain-specific allowlist of addresses that ALSO get
    rejected on prior storage. Implementations are expected to
    materialise this from `params/eip7610.go` per chain ID; here we
    state the predicate axiomatically. Eita's
    `Constantinople.Vm.Effect.isCreateCollision` currently treats
    this as false everywhere — sound for Base (empty allowlist)
    and the BlockchainTest corpus (no fixture touches a mainnet
    allowlist entry). -/
axiom IsEip7610Rejected : Evm.U256 → Evm.Address → Prop

/-- The full deployed predicate combining EIP-684 + EIP-7610.
    `AccountInUse state addr` is the EIP-684 clause; the chain-id
    parametrised allowlist contributes the second disjunct. -/
def AccountInUseFull (chainId : Evm.U256) (state : State) (addr : Evm.Address) : Prop :=
  AccountInUse state addr ∨ IsEip7610Rejected chainId addr

/-- Address-collision branch: the derived address is already in use
    (nonzero nonce, non-empty code, or non-empty storage — see
    `AccountInUse`). Per EIP-1014: bump the sender's nonce, push 0,
    consume the full forwarded gas (1/64 retained). -/
def IsCreate2EntryCollision (evm evm' : Evm) : Prop :=
  ∃ args : Create2Args, ∃ rest,
    evm.stack = args.value :: Evm.U256.ofNat args.offset ::
                Evm.U256.ofNat args.len :: args.salt :: rest ∧
    evm.message.isStatic = false ∧
    evm.message.depth < maxCallDepth ∧
    (evm.env.state.getBalance evm.message.currentTarget).toNat ≥ args.value.toNat ∧
    rest.length < stackLimit ∧
    let entryGas := Create2.entryGas args ((evm.memory.size + 31) / 32)
    evm.gasLeft ≥ entryGas ∧
    let mem := evm.memory  -- spec doesn't pin the expanded contents
    let initCode := Evm.Bytes.sliceZeroPad mem args.offset args.len
    let newAddr  :=
      Evm.Constantinople.Utils.computeCreate2Address
        evm.message.currentTarget args.salt initCode
    AccountInUse evm.env.state newAddr ∧
    let senderAcc := evm.env.state.getAccount evm.message.currentTarget
    let stateBumped :=
      evm.env.state.setAccount evm.message.currentTarget
        { senderAcc with nonce := senderAcc.nonce + 1 }
    let gasAfter := evm.gasLeft - entryGas
    -- 1/64 of remaining gas is retained by the parent (EIP-150 forward
    -- rule, applied here mid-1014 because CREATE2 also inherits the
    -- 63/64 forwarding).
    evm' = { evm with
      env        := { evm.env with state := stateBumped },
      stack      := 0 :: rest,
      gasLeft    := gasAfter / 64,
      returnData := Evm.Bytes.empty,
      pc         := evm.pc + 1 }

/-- Successful entry into the sub-frame. The relation admits any
    `setup : Create2SubFrameSetup` whose fields match the values the
    spec computes from the parent frame. The trampoline runs the
    sub-frame from `setup.subMsg` against `setup.subState`; merging
    is described by `IsCreate2Merge` (TODO) further up the stack. -/
def IsCreate2EntrySuccess (evm : Evm) (setup : Create2SubFrameSetup) : Prop :=
  ∃ args : Create2Args, ∃ rest,
    evm.stack = args.value :: Evm.U256.ofNat args.offset ::
                Evm.U256.ofNat args.len :: args.salt :: rest ∧
    evm.message.isStatic = false ∧
    evm.message.depth < maxCallDepth ∧
    (evm.env.state.getBalance evm.message.currentTarget).toNat ≥ args.value.toNat ∧
    rest.length < stackLimit ∧
    let entryGas := Create2.entryGas args ((evm.memory.size + 31) / 32)
    evm.gasLeft ≥ entryGas ∧
    let mem      := evm.memory
    let initCode := Evm.Bytes.sliceZeroPad mem args.offset args.len
    let newAddr  :=
      Evm.Constantinople.Utils.computeCreate2Address
        evm.message.currentTarget args.salt initCode
    -- Storage check included (see `AccountInUse`): an address with
    -- pre-existing non-empty storage also blocks CREATE2.
    ¬ AccountInUse evm.env.state newAddr ∧
    let sender    := evm.message.currentTarget
    let senderAcc := evm.env.state.getAccount sender
    let gasAfter  := evm.gasLeft - entryGas
    let gasForward := gasAfter - gasAfter / 64
    let gasRetained := gasAfter / 64
    let stateForSub :=
      let st := evm.env.state.setAccount sender
        { senderAcc with
            nonce   := senderAcc.nonce + 1,
            balance := senderAcc.balance - args.value }
      let dest := st.getAccount newAddr
      st.setAccount newAddr
        { dest with balance := dest.balance + args.value, nonce := 1 }
    setup.newAddr             = newAddr ∧
    setup.subState            = stateForSub ∧
    setup.subMsg.caller        = sender ∧
    setup.subMsg.target        = some newAddr ∧
    setup.subMsg.currentTarget = newAddr ∧
    setup.subMsg.value         = args.value ∧
    setup.subMsg.data          = Evm.Bytes.empty ∧
    setup.subMsg.code          = initCode ∧
    setup.subMsg.gas           = gasForward ∧
    setup.subMsg.depth         = evm.message.depth + 1 ∧
    setup.parentSnapshot.gasLeft = gasRetained ∧
    setup.parentSnapshot.pc      = evm.pc

end Evm.Constantinople.Spec
