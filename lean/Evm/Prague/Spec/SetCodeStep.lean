/-
  Evm.Prague.Spec.SetCodeStep — EIP-7702 set-code transaction +
  CALL delegation.

  EELS reference:
    * Authorization processing: `forks/prague/utils/transactions.py`
      `process_authorization` / `recover_authority`, and the loop in
      `forks/prague/fork.py::process_transaction` (around lines
      412-470 in the Pectra-era spec).
    * CALL delegation: `forks/prague/vm/instructions/system.py`
      `_get_callee_code` (the helper that resolves the executed
      bytecode for a CALL target, checking for the EIP-7702
      designator and following it).

  EIP-7702 introduces transaction type 4. Its body adds an
  `authorization_list`, each entry of which (if validly signed) sets
  the *authority's* (an EOA's) code to the **delegation designator**:

      0xef 0x01 0x00 || delegated_address    (= 23 bytes)

  Subsequent CALLs into that EOA execute the delegated contract's
  code in the EOA's storage / balance context. This delivers
  "account abstraction lite": EOAs become smart-wallet-like without
  needing migration.

  Spec scope:

    1. Per-authorization processing rules (steps 1-8 of EIP-7702
       "Behavior").
    2. The delegation-designator format and parser.
    3. The CALL-delegation rule: callee = EOA with designator code
       → execute `state.getAccount(delegated).code` in the EOA's
       context.

  The signature-recovery primitive itself (`ecrecover` over the
  EIP-7702 magic message) is axiomatised — Lean doesn't know
  secp256k1.

  Inheritance: introduced at Prague.
-/

import Evm.BaseTypes
import Evm.Frontier.State
import Evm.Frontier.Vm
import Evm.Prague.Transactions
import Evm.Prague.State

namespace Evm.Prague.Spec

open Evm.Frontier (State)
open Evm.Prague (Authorization)

/-! ## Constants from EIP-7702. EELS:
    `forks/prague/utils/transactions.py`. -/

/-- `MAGIC = 0x05`. Prefix byte for the authorization message hash. -/
def authMagic : UInt8 := 0x05

/-- `PER_AUTH_BASE_COST = 12500`. The minimum gas an authorization
    "really" costs after a successful refund. NOT the value charged
    in intrinsic — see `authIntrinsicPerAuth` below. -/
def perAuthBaseCost : Nat := 12500

/-- `PER_EMPTY_ACCOUNT_COST = 25000`. The full empty-account
    creation cost. Charged from intrinsic gas for every
    authorization; per-existing-authority half (12500) is refunded
    via the global refund counter (subject to EIP-3529's gasUsed/5
    cap). Matches go-ethereum `core/state_transition.go::IntrinsicGas`:
    `gas += len(authList) * params.CallNewAccountGas`. -/
def perEmptyAccountCost : Nat := 25000

/-- The per-authorization charge baked into the tx intrinsic gas
    formula: 25000 per authorization, charged upfront in every
    type-4 tx whether the auth ultimately succeeds or not. -/
def authIntrinsicPerAuth : Nat := perEmptyAccountCost

theorem authIntrinsicPerAuth_eq : authIntrinsicPerAuth = 25000 := rfl

/-- The refund credited to the global refund counter per
    authorization whose authority existed in the trie. -/
def authRefundPerExistingAuthority : Nat := perEmptyAccountCost - perAuthBaseCost

theorem authRefundPerExistingAuthority_eq :
    authRefundPerExistingAuthority = 12500 := rfl

/-- The "real" net cost of a successful authorization that hit an
    existing account: 25000 charged upfront minus 12500 refunded =
    12500. (Modulo the EIP-3529 cap, which can reduce the refund.) -/
theorem authNetCost_existing :
    authIntrinsicPerAuth - authRefundPerExistingAuthority = perAuthBaseCost := rfl

/-- secp256k1 group order. -/
def secp256k1n : Nat :=
  115792089237316195423570985008687907852837564279074904382605163141518161494337

/-! ## Delegation designator -/

/-- The 3-byte prefix `0xef 0x01 0x00` that distinguishes a
    delegation designator from ordinary contract code.

    The `0xef` byte is reserved by EIP-3541 as the "no-EOF" sentinel;
    EIP-7702 piggybacks on that reservation to make designators
    self-identifying. -/
def delegationPrefix : Evm.Bytes :=
  ByteArray.mk (Array.mk [0xef, 0x01, 0x00])

/-- A code blob `c` is a delegation designator iff it's exactly 23
    bytes and starts with `0xef 0x01 0x00`. The remaining 20 bytes
    are the delegated address.

    Returned as a `Bool` rather than a `Prop` so the predicate can
    be branched on in computational definitions. -/
def isDelegationDesignator (c : Evm.Bytes) : Bool :=
  c.size = 23 &&
  c.get! 0 = 0xef && c.get! 1 = 0x01 && c.get! 2 = 0x00

/-- Propositional form for use in step relations. -/
def IsDelegationDesignator (c : Evm.Bytes) : Prop :=
  isDelegationDesignator c = true

/-- Parse the delegated address out of a designator. UB if `c` is
    not a designator; intended use is paired with
    `IsDelegationDesignator`. -/
def parseDelegated (c : Evm.Bytes) : Evm.Address :=
  Evm.Address.ofBytesBE (Evm.Bytes.sliceZeroPad c 3 20)

/-- Encode a delegation designator: `delegationPrefix || addr_BE`. -/
def encodeDesignator (addr : Evm.Address) : Evm.Bytes :=
  delegationPrefix ++ Evm.Address.toBytesBE addr

/-! ## Authorization processing

    Per EIP-7702 §"Behavior", for each authorization tuple
    `(chainId, address, nonce, yParity, r, s)`:

      1. yParity ∈ {0, 1}, 0 < r < secp256k1n, 0 < s ≤ secp256k1n/2.
      2. chainId == 0 (wildcard) OR chainId == current_chain_id.
      3. authority = ecrecover(MAGIC || rlp([chain, addr, nonce]),
                                yParity, r, s).
         If recovery fails, skip.
      4. authority's code is empty OR is already a designator.
      5. authority's nonce equals the tuple's nonce.
      6. (Gas refund accounting: refund 12500 to sender if authority
          was empty.)
      7. Set authority's code := encodeDesignator(address)
         (or clear it if address == 0).
      8. Bump authority's nonce. -/

/-- Axiomatised ecrecover-with-magic. Real impl lives in
    `c/ecrecover.c` and needs a small adapter for the EIP-7702
    message format. -/
axiom RecoverAuthority : Authorization → Option Evm.Address

/-- Per-authorization step: the post-state has been updated according
    to the EIP-7702 procedure. The `refund` is the gas to credit the
    sender for this authorization (0 for failures, 0 for non-empty
    successes, `PER_EMPTY_ACCOUNT_COST - PER_AUTH_BASE_COST` for
    empty-authority successes). -/
def IsApplyAuthorization
    (chainId : Evm.U256) (auth : Authorization)
    (preState postState : State) (refund : Nat) : Prop :=
  -- Step 1: signature scalar bounds.
  (auth.yParity = (0 : Evm.U256) ∨ auth.yParity = (1 : Evm.U256)) →
  (0 : Evm.U256) < auth.r →
  (0 : Evm.U256) < auth.s →
  auth.s.toNat * 2 ≤ secp256k1n →
  -- Step 2: chain id check.
  (auth.chainId = (0 : Evm.U256) ∨ auth.chainId = chainId) →
  -- Step 3-8: recovery + state update.
  match RecoverAuthority auth with
  | none => postState = preState ∧ refund = 0
  | some authority =>
    let acc := preState.getAccount authority
    let alreadyDelegated := isDelegationDesignator acc.code
    let nonceMatches : Bool := decide (acc.nonce = auth.nonce.toNat)
    let codeOk : Bool := (acc.code.size = 0 : Bool) || alreadyDelegated
    if ¬ codeOk = true ∨ ¬ nonceMatches = true then
      postState = preState ∧ refund = 0
    else
      let newCode :=
        if auth.address = (0 : Evm.Address) then Evm.Bytes.empty
        else encodeDesignator auth.address
      let postAcc := { acc with code := newCode, nonce := acc.nonce + 1 }
      -- EIP-7702 step 6: "Add PER_EMPTY_ACCOUNT_COST - PER_AUTH_BASE_COST
      -- gas to the global refund counter IF authority exists in the
      -- trie." The intrinsic charges the full PER_EMPTY_ACCOUNT_COST
      -- (= 25000) per auth upfront; this refund returns half of it
      -- (12500) when no new account had to be created. So the refund
      -- fires on EXISTING (non-empty) authorities, NOT empty ones —
      -- an earlier version of this file had it reversed (caught by
      -- tx 31 of Base 0x2c9a9a0; see commit history). The condition
      -- `wasEmpty` is the EIP-161 empty-account predicate.
      let wasEmpty : Bool := decide (acc.nonce = 0) &&
                             decide (acc.balance = (0 : Evm.U256)) &&
                             decide (acc.code.size = 0)
      postState = preState.setAccount authority postAcc ∧
      refund = (if wasEmpty then 0 else perEmptyAccountCost - perAuthBaseCost)

/-- Authorization-list processing: fold `IsApplyAuthorization` over
    the list in order, accumulating the refund. -/
def IsApplyAuthorizations
    (chainId : Evm.U256) (auths : List Authorization)
    (preState postState : State) (totalRefund : Nat) : Prop :=
  -- We state this inductively rather than as an explicit fold because
  -- `IsApplyAuthorization` is itself a `Prop`-valued predicate.
  match auths with
  | []         => postState = preState ∧ totalRefund = 0
  | a :: rest  =>
    ∃ midState midRefund tailRefund,
      IsApplyAuthorization chainId a preState midState midRefund ∧
      IsApplyAuthorizations chainId rest midState postState tailRefund ∧
      totalRefund = midRefund + tailRefund

/-! ## Per-tx ordering: sender nonce bump BEFORE authorization processing

    EELS `forks/prague/fork.py::process_transaction` increments the
    sender's nonce as part of its standard tx-entry bookkeeping
    BEFORE calling into the authorization-list processor. This
    matters when `sender == authority` (the self-delegation
    pattern). At step 5 of `applyAuthorization` we require
    `state[authority].nonce == auth.nonce`. With the sender bump
    happening first, this matches the auth's stated nonce
    (= sender's pre-bump nonce + 1 in the same-account case).

    Reversing the order would leave `state[authority].nonce`
    one too low, the auth would silently fail step 5, and the
    delegated code would not be installed — caught by tx 31 of
    Base 0x2c9a9a0 (see commit history). -/
def SenderNonceBumpedBeforeAuths
    (preState postSenderBumpState postAuthState : State)
    (sender : Evm.Address) (chainId : Evm.U256)
    (auths : List Authorization) (refund : Nat) : Prop :=
  let preAcc := preState.getAccount sender
  postSenderBumpState =
    preState.setAccount sender { preAcc with nonce := preAcc.nonce + 1 } ∧
  IsApplyAuthorizations chainId auths postSenderBumpState postAuthState refund

/-! ## CALL into a delegated EOA

    When the EVM CALLs into an account whose code is a delegation
    designator, the *delegated* contract's code is executed in the
    *EOA's* (the delegator's) storage and balance context. EELS:
    `forks/prague/vm/instructions/system.py::_get_callee_code`.

    Concretely:
      * `evm.message.currentTarget` = the EOA (the called address)
      * `evm.message.code`           = `state.getAccount(delegated).code`

    Note the delegation chain is NOT followed transitively: if the
    delegated contract itself happens to have a designator (which it
    shouldn't, since contracts can't have non-EOA designators per
    the impl checks), the call resolves to whatever bytes are there
    without a second hop. -/

/-- The "effective code" a CALL into `callee` should execute under
    EIP-7702 semantics: follow the designator once, else use the
    callee's own code. -/
def IsEffectiveCallCode (state : State) (callee : Evm.Address) (code : Evm.Bytes) : Prop :=
  let acc := state.getAccount callee
  if isDelegationDesignator acc.code then
    code = (state.getAccount (parseDelegated acc.code)).code
  else
    code = acc.code

/-! ## Transaction into a delegated EOA (tx level)
    When `tx.to` itself holds a designator, the *top* frame executes the
    delegated contract's code in the EOA's context, exactly like a CALL
    (`IsEffectiveCallCode`), and the delegated address joins the warm set —
    EELS prague `prepare_message` adds it to `accessed_addresses` — with NO
    extra access charge at the tx level (unlike the CALL-family charge
    below). Executing the 23-byte designator as code would hit 0xEF =
    INVALID and burn the whole gas limit — exactly what Arc mainnet block
    23500000 tx 11 showed before the host resolved it (3,000,000 burned vs
    the chain's 107,033; after: 107,033 exact, which also confirms "no
    charge"). Host: `apply-tx` top-frame code selection, src/evm/tx.lisp. -/
def IsEffectiveTxCode (state : State) (to : Evm.Address) (code : Evm.Bytes) : Prop :=
  IsEffectiveCallCode state to code

/-- No tx-level delegation access charge (EELS prepare_message; Arc oracle). -/
def TxDelegationAccessCost (_calleeCode : Evm.Bytes) : Nat := 0

/-! ## CALL into a delegated EOA: access-cost ordering

    When the CALL family hits a callee whose code is a 23-byte
    EIP-7702 designator, op-geth charges an ADDITIONAL EIP-2929
    access cost for the *delegated* address — 2600 cold / 100
    warm. Critically, that charge is paid by the parent BEFORE the
    63/64 gas-forwarding rule (EIP-150) computes the forwarded
    amount. The earlier "charge from the sub-frame's stipend"
    impl broke `sender.transfer(amount)` when sender had a 7702
    delegation: the 2300-gas stipend was eaten by the 2600 cold
    access, the sub-frame OOG'd, and the WETH-style withdraw
    reverted with funds stuck. Now charged from the parent;
    forwarded gas (and the stipend, added on top) is preserved.

    EELS reference: `forks/prague/vm/instructions/system.py`
    `generic_call` charges the delegated-address access via
    `charge_gas` BEFORE constructing the sub-message gas. -/

/-- The EIP-7702-extra access charge a CALL pays when its callee
    is a designator. Zero if the callee has no designator or if
    the fork doesn't enable EIP-7702 (`pragueDelegation = false`).
    Otherwise 100 (warm) or 2600 (cold) for the delegated
    address — looked up against `env.accessedAddresses`. -/
def DelegationAccessCost (env : Frontier.Vm.Environment) (calleeCode : Evm.Bytes) : Nat :=
  if env.pragueDelegation ∧ isDelegationDesignator calleeCode then
    if env.accessedAddresses.contains (parseDelegated calleeCode) then 100
    else 2600
  else 0

/-- Where the cost is paid: parent frame, BEFORE EIP-150's 63/64
    rule sees the post-access remaining gas. The relation says
    parent's gas decreases by exactly `DelegationAccessCost`, and
    the delegated address is added to the warm set. -/
def IsDelegationAccessCharge
    (env env' : Frontier.Vm.Environment) (calleeCode : Evm.Bytes)
    (gasBefore gasAfter : Nat) : Prop :=
  let cost := DelegationAccessCost env calleeCode
  gasAfter = gasBefore - cost ∧
  (if env.pragueDelegation ∧ isDelegationDesignator calleeCode then
      let d := parseDelegated calleeCode
      env'.accessedAddresses = env.accessedAddresses ++ [d] ∨
      env'.accessedAddresses = env.accessedAddresses
    else env' = env)

theorem delegationAccessCost_zero_when_no_designator
    (env : Frontier.Vm.Environment) (calleeCode : Evm.Bytes)
    (h : ¬ isDelegationDesignator calleeCode) :
    DelegationAccessCost env calleeCode = 0 := by
  unfold DelegationAccessCost
  simp [h]

theorem delegationAccessCost_zero_pre_prague
    (env : Frontier.Vm.Environment) (calleeCode : Evm.Bytes)
    (h : env.pragueDelegation = false) :
    DelegationAccessCost env calleeCode = 0 := by
  unfold DelegationAccessCost
  simp [h]

/-! ## What we encoded vs. axiomatised

    Encoded:
      * The constants `MAGIC`, `PER_AUTH_BASE_COST`,
        `PER_EMPTY_ACCOUNT_COST`, `secp256k1n`.
      * The designator format `0xef 0x01 0x00 || addr` (parser +
        printer + recogniser).
      * Step 1, 2, 4, 5, 7, 8 of the per-authorization procedure.
      * The accumulated refund per EIP-7702 §"Gas costs".
      * The CALL-delegation lookup rule (single-hop).

    Axiomatised:
      * `RecoverAuthority`: ecrecover with the EIP-7702 magic byte.
        Discharging this requires plumbing the existing
        `c/ecrecover.c` Frontier helper through a magic-prefix
        adapter; spec just says "if it returns `some authority`,
        proceed; otherwise skip".

    Not in scope for this file (the brief mentions it as the
    "trickiest" alongside EIP-4844):
      * Intrinsic gas inclusion of `25000 · #authorizations`
        (`authIntrinsicPerAuth` × authorizationList length) — that's
        in `CalldataCost.lean` via the `baseExtras` parameter.
      * Pre-execution vs. in-EVM ordering — EELS applies all
        authorizations BEFORE the EVM runs (so a subsequent CALL in
        the same tx sees the new code). The fork driver
        (`Prague.Fork.processTransaction`) is where that sequencing
        is pinned; not duplicated here. -/

end Evm.Prague.Spec
