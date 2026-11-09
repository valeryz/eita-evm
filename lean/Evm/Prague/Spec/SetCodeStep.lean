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
  EIP-7702 magic message) is a trusted oracle parameter `recover`.

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

/-! ## Authorization processing (EELS `forks/prague/vm/eoa_delegation.py`)

    `validate_authorization` 155-189, for each authorization:
      1. `chain_id ∈ (block chain id, 0)`; `nonce < 2^64 − 1` (`U64.MAX_VALUE`);
      2. `recover_authority` 77-128: `y_parity ∈ {0,1}`, `0 < r < N`,
         `0 < s ≤ N // 2`, then the secp256k1 recovery over
         `keccak(MAGIC ‖ rlp([chain_id, address, nonce]))` — a trusted oracle,
         the parameter `recover` (as in the implementation), not an axiom;
      3. the authority is warmed (`accessed_addresses.add`), even when a later
         check rejects it;
      4. its code is empty or a delegation; its nonce is the authorization's.
    `set_delegation` 192-237, for a valid one: refund
    `AUTH_PER_EMPTY_ACCOUNT − REFUND_AUTH_PER_EXISTING_ACCOUNT` (12500) when the
    authority EXISTS (`account_exists`), `set_code` (empty for the null address,
    else the designator), `increment_nonce`. An invalid authorization changes
    nothing but the warm set (and not even that before recovery).

    Restated 2026-11-09 over `Environment` (state, warm set, refund counter —
    where the implementation `Tx.authorize` works): the relation used to
    refund on "not empty", skip the nonce bound and `r < N`, take its
    hypotheses as implications (vacuous when false), and recover through an
    `axiom`. -/

/-- The checks before recovery (`validate_authorization` 166-170 and
    `recover_authority` 98-103). -/
@[reducible] def AuthPrechecks (chainId : Evm.U256) (auth : Authorization) : Prop :=
  (auth.chainId = chainId ∨ auth.chainId = 0) ∧ auth.nonce.toNat < 2 ^ 64 - 1 ∧
  auth.yParity.toNat ≤ 1 ∧ 0 < auth.r.toNat ∧ auth.r.toNat < secp256k1n ∧
  0 < auth.s.toNat ∧ auth.s.toNat ≤ secp256k1n / 2

/-- Per-authorization step over the tx environment. -/
def IsApplyAuthorization (chainId : Evm.U256)
    (recover : Authorization → Option Evm.Address) (auth : Authorization)
    (env env' : Evm.Frontier.Vm.Environment) : Prop :=
  if ¬ AuthPrechecks chainId auth then env' = env
  else
  match recover auth with
  | none => env' = env
  | some authority =>
    let envW : Evm.Frontier.Vm.Environment :=
      if env.accessedAddresses.contains authority then env
      else { env with accessedAddresses := env.accessedAddresses ++ [authority] }
    let acc := env.state.getAccount authority
    if (acc.code.size ≠ 0 ∧ isDelegationDesignator acc.code = false) ∨
       acc.nonce ≠ auth.nonce.toNat then env' = envW
    else
      let withCode := env.state.setAccount authority
        { acc with code := if auth.address = 0 then Evm.Bytes.empty
                           else encodeDesignator auth.address }
      let acc' := withCode.getAccount authority
      env' = { envW with
        refundCounter := if env.state.accountExists authority
                         then env.refundCounter + (perEmptyAccountCost - perAuthBaseCost)
                         else env.refundCounter,
        state := withCode.setAccount authority { acc' with nonce := acc'.nonce + 1 } }

/-- Authorization-list processing (`set_delegation`'s loop): the authorizations in order. -/
def IsApplyAuthorizations (chainId : Evm.U256)
    (recover : Authorization → Option Evm.Address) :
    List Authorization → Evm.Frontier.Vm.Environment → Evm.Frontier.Vm.Environment → Prop
  | [], env, env' => env' = env
  | a :: rest, env, env' =>
    ∃ mid, IsApplyAuthorization chainId recover a env mid ∧
      IsApplyAuthorizations chainId recover rest mid env'

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
def IsEffectiveCallCode (state : Evm.Frontier.State) (callee : Evm.Address) (code : Evm.Bytes) : Prop :=
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
def IsEffectiveTxCode (state : Evm.Frontier.State) (to : Evm.Address) (code : Evm.Bytes) : Prop :=
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

/-! ## What we encoded vs. took as an oracle

    Encoded:
      * The constants `MAGIC`, `PER_AUTH_BASE_COST`,
        `PER_EMPTY_ACCOUNT_COST`, `secp256k1n`.
      * The designator format `0xef 0x01 0x00 || addr` (parser +
        printer + recogniser).
      * Step 1, 2, 4, 5, 7, 8 of the per-authorization procedure.
      * The accumulated refund per EIP-7702 §"Gas costs".
      * The CALL-delegation lookup rule (single-hop).

    Oracle (a parameter, not an axiom):
      * `recover`: ecrecover with the EIP-7702 magic byte, the same
        parameter the implementation `Tx.authorize` takes.

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
