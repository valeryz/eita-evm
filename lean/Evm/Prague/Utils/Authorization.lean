/-
  Evm.Prague.Utils.Authorization — EIP-7702 set-code authorization
  processing.

  EELS reference: ethereum/forks/prague/utils/transactions.py
  (`process_authorization` / `recover_authority`) and
  ethereum/forks/prague/fork.py (`process_transaction`, the loop
  that consumes a type-4 tx's `authorizationList` after intrinsic
  gas is charged but before the EVM runs).

  Per EIP-7702 the per-authorization procedure is (citing the EIP
  rather than file:line since the EELS function spans ~50 lines):

      For each (chainId, address, nonce, yParity, r, s):
        1. Verify yParity ∈ {0, 1}; verify r,s in [1, secp256k1n/2].
           Otherwise skip.
        2. If chainId ≠ 0 and chainId ≠ this chain's id, skip.
        3. Recover `authority` = ecrecover(MAGIC || rlp(chain,addr,nonce),
                                           yParity, r, s).
           If recovery fails, skip.
        4. Skip if `authority` has non-empty code AND it's not already
           a delegation designator. (You can't overwrite a contract.)
        5. If state[authority].nonce ≠ nonce, skip.
        6. Charge `PER_EMPTY_ACCOUNT_COST` (25000) refund delta to the
           sender: if the authority account was empty, give the sender
           back `PER_EMPTY_ACCOUNT_COST - PER_AUTH_BASE_COST` (= 12500)
           in gas; otherwise charge nothing extra (the base 12500 was
           already in intrinsic gas — see `intrinsicGas`).
        7. Set authority's code to `0xef0100 || address` (or clear the
           designator if `address == 0`).
        8. Bump authority's nonce.

  This module exposes the per-authorization step as a pure function
  on `Prague.State` so the fork driver can fold it over the
  `authorizationList`.

  Sender / sig-recovery is currently stubbed (`recoverAuthority` always
  returns `none`); the same recovery primitive that Frontier uses for
  tx senders (`Frontier.Utils.recoverSender` → `c/ecrecover.c`) needs
  a `recover_authority` variant with the EIP-7702 magic prefix, which
  isn't wired yet. With the stub, every authorization is skipped at
  step 3, so the *shape* of processing is correct (state is unchanged)
  while gas accounting at the tx level is still right.
-/

import Evm.BaseTypes
import Evm.Rlp
import Evm.Crypto.Hash
import Evm.Crypto.EcRecover
import Evm.Prague.State
import Evm.Prague.Transactions

namespace Evm.Prague.Utils

open Evm.Prague (State Authorization)

/-- Per-authorization base gas cost (EELS `PER_AUTH_BASE_COST`). Folded
    into intrinsic gas; charged whether the authorization succeeds or
    fails. -/
def perAuthBaseCost : Nat := 12500

/-- Per-authorization "create an empty account" cost (EELS
    `PER_EMPTY_ACCOUNT_COST`). If the recovered authority is an empty
    account, the sender is refunded `PER_EMPTY_ACCOUNT_COST -
    PER_AUTH_BASE_COST = 12500` (= negative cost). -/
def perEmptyAccountCost : Nat := 25000

/-- secp256k1 group order. EIP-7702 reuses EIP-2 / EIP-155's `s ≤ n/2`
    malleability check. -/
def secp256k1n : Nat :=
  115792089237316195423570985008687907852837564279074904382605163141518161494337

/-- EIP-7702 magic byte for the authorization signing hash. -/
def authMagic : UInt8 := 0x05

/-- Recover the authority from an authorization tuple.

    EELS: `recover_authority` constructs
        keccak256(MAGIC || rlp([chain_id, address, nonce]))
    and ecrecovers `(yParity, r, s)` against it.

    Bound to `Evm.Crypto.recover` (libsecp256k1) — the same primitive
    we use for tx-sender recovery, just over the EIP-7702-magic'd
    message hash and with `v = yParity + 27`. -/
def recoverAuthority (a : Evm.Prague.Authorization) : Option Evm.Address :=
  -- rlp([chainId, address, nonce])
  let payload := Evm.Rlp.encode (.list
    [ .bytes (Evm.Rlp.natToBytes a.chainId.toNat)
    , .bytes (Evm.Address.toBytesBE a.address)
    , .bytes (Evm.Rlp.natToBytes a.nonce.toNat) ])
  -- MAGIC || rlp(...)
  let signedBytes : Evm.Bytes :=
    (ByteArray.mk #[authMagic]) ++ payload
  let msgHash := Evm.Crypto.keccak256 signedBytes
  -- EIP-7702 yParity ∈ {0,1}; ecrecover wants v ∈ {27,28}.
  let v : Evm.U256 := Evm.U256.ofNat (27 + a.yParity.toNat)
  Evm.Crypto.recover msgHash v a.r a.s

/-- The current chain id we accept authorizations for. Mainnet = 1.
    Authorizations with `chainId = 0` are wildcards. -/
def mainnetChainId : Evm.U256 := Evm.U256.ofNat 1

/-- Apply one authorization to `state`. Returns the post-state and the
    gas refund delta to credit the sender (0 if the authority was not
    previously an empty account; `PER_EMPTY_ACCOUNT_COST -
    PER_AUTH_BASE_COST` otherwise — but only when the authorization
    actually succeeds).

    Mirrors the per-authorization branches in
    `ethereum/forks/prague/fork.py` `process_transaction` around the
    set-code-tx block. -/
def applyAuthorization (state : Evm.Prague.State) (chainId : Evm.U256)
    (auth : Evm.Prague.Authorization) : Evm.Prague.State × Nat :=
  -- Step 1: y_parity / r,s bounds. We accept yParity ∈ {0, 1} and
  -- `0 < r,s < secp256k1n/2`. Failures are silent.
  if auth.yParity ≠ (0 : Evm.U256) ∧ auth.yParity ≠ (1 : Evm.U256) then
    (state, 0)
  else if auth.r = (0 : Evm.U256) ∨ auth.s = (0 : Evm.U256) then
    (state, 0)
  else if auth.s.toNat * 2 ≥ secp256k1n then
    (state, 0)
  -- Step 2: chain id check. 0 = wildcard.
  else if auth.chainId ≠ (0 : Evm.U256) ∧ auth.chainId ≠ chainId then
    (state, 0)
  else
    -- Step 3: ecrecover.
    match recoverAuthority auth with
    | none => (state, 0)
    | some authority =>
      let acc := state.getAccount authority
      -- Step 4: authority must have no code, OR its existing code must
      -- already be a delegation designator (overwriting a designator is
      -- explicitly allowed).
      let alreadyDelegated := (Evm.Prague.State.parseDelegation acc.code).isSome
      if acc.code.size > 0 ∧ ¬ alreadyDelegated then
        (state, 0)
      -- Step 5: nonce must match.
      else if acc.nonce ≠ auth.nonce.toNat then
        (state, 0)
      else
        -- Step 6 refund: per EIP-7702, "Add PER_EMPTY_ACCOUNT_COST
        -- - PER_AUTH_BASE_COST gas to the global refund counter
        -- if authority exists in the trie." So the refund is paid
        -- when the authority's account ALREADY EXISTS (non-empty in
        -- the EIP-161 sense). The intrinsic charges the full
        -- PER_EMPTY_ACCOUNT_COST (= 25000) per auth upfront; this
        -- refund returns half of it when no new account needed
        -- creating. Earlier we had this backwards (refund-if-empty),
        -- which over-credited new accounts and under-credited
        -- existing ones — caught by tx 31 of 0x2c9a9a0 (~3300 gas
        -- short after the EIP-3529 cap).
        let wasEmpty := ¬ state.accountExists authority ∨
                        (acc.nonce = 0 ∧ acc.balance = (0 : Evm.U256) ∧
                         acc.code.size = 0)
        let refund   := if wasEmpty then 0 else perEmptyAccountCost - perAuthBaseCost
        -- Step 7: set designator (or clear, if `address == 0`).
        let state := if auth.address = (0 : Evm.Address) then
                       state.setAccount authority { acc with code := Evm.Bytes.empty }
                     else
                       state.setDelegation authority auth.address
        -- Step 8: bump authority nonce.
        let acc2 := state.getAccount authority
        let state := state.setAccount authority
                       { acc2 with nonce := acc2.nonce + 1 }
        (state, refund)

/-- Fold `applyAuthorization` over the whole list, accumulating both
    state and refund. -/
def applyAuthorizations (state : Evm.Prague.State) (chainId : Evm.U256)
    (auths : List Evm.Prague.Authorization) : Evm.Prague.State × Nat :=
  auths.foldl
    (fun (st, refundAcc) a =>
      let (st', r) := applyAuthorization st chainId a
      (st', refundAcc + r))
    (state, 0)

end Evm.Prague.Utils
