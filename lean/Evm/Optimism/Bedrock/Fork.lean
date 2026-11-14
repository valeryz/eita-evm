/-
  Evm.Optimism.Bedrock.Fork — `processDepositedTx`.

  Executable counterpart of `Optimism/Bedrock/Spec/DepositedTx.lean`.
  Runs a single type-0x7E deposited tx against `State`:

    1. Bump `from`'s nonce.
    2. Credit `mint` wei to `from`.
    3. Execute the call or create.
    4. On failure: roll back state changes from (3) but KEEP the
       mint and the nonce bump. (Mint is the bridge invariant.)
    5. No fee accounting: deposited txs are gas-free at the L2 level;
       gas was paid for at deposit time on L1.

  The `applyMessage` parameter selects which fork's EVM is used for
  execution. Default = Cancun (Ecotone-era; the most common Base
  fork as of 2026-05). Pass `Evm.Prague.Vm.Effect.applyMessage` for
  Isthmus.

  EELS-equivalent reference: op-geth's
  `core/state_processor.go` `applyDepositTx` plus
  `core/vm/evm.go::Create`. There's no upstream EELS port for OP
  Stack; the optimism-monorepo Solidity tests are the next-best
  source of truth.
-/

import Evm.Frontier.State
import Evm.Frontier.Vm
import Evm.Frontier.Utils.Address
import Evm.Frontier.Fork
import Evm.Cancun.Vm.Effect
import Evm.Istanbul.Vm.Gas
import Evm.Prague.Transactions
import Evm.Prague.Utils.Authorization
import Evm.Optimism.Bedrock.Transactions
import Evm.Optimism.Bedrock.Spec.FeeVaults

namespace Evm.Optimism.Bedrock

open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Log Message Environment Evm Exception)

/-- Intrinsic-gas cost for a tx. Same shape as Istanbul+:
    21000 base + 32000 if CREATE + per-byte data cost (4/16 for
    zero/non-zero post-Istanbul). At Canyon+ (≡ Ethereum Shanghai),
    add EIP-3860's per-word init-code surcharge (2 gas/word) for
    tx-CREATE — pass `eip3860 := true`.

    Forward-declared so both `processDepositedTx` (Bedrock+,
    Regolith) and `processUserTx` can charge it. -/
def intrinsicGas (data : Evm.Bytes) (isCreate : Bool)
                 (eip3860 : Bool := false) : Nat := Id.run do
  let mut nZero    : Nat := 0
  let mut nNonZero : Nat := 0
  for i in [0 : data.size] do
    if data.get! i = (0 : UInt8) then nZero := nZero + 1
    else nNonZero := nNonZero + 1
  let dataCost := nZero * Evm.Istanbul.Vm.Gas.txDataZero
                + nNonZero * Evm.Istanbul.Vm.Gas.txDataNonZero
  let createCost : Nat := if isCreate then Evm.Frontier.Vm.Gas.create else 0
  -- EIP-3860: 2 gas per 32-byte word of init code, charged at
  -- tx-CREATE intrinsic time. Canyon (= Ethereum Shanghai) onwards.
  let initCodeCost : Nat :=
    if eip3860 ∧ isCreate then
      2 * ((data.size + 31) / 32)
    else 0
  pure (Evm.Frontier.Vm.Gas.transaction + dataCost + createCost + initCodeCost)

/-- Run one deposited tx. The block context (`coinbase`, `number`,
    etc.) flows into the EVM environment so opcodes like BLOCKHASH,
    COINBASE, NUMBER, etc. see the right values during execution. -/
def processDepositedTx
    (state          : State)
    (blockHashes    : List Evm.Hash32)
    (coinbase       : Evm.Address)
    (number gasLimit timestamp : Nat)
    (baseFeePerGas  : Nat)
    (prevRandao     : Evm.Hash32)
    (tx             : DepositedTx)
    (applyMessage   : Message → Environment →
                      Except Exception Evm :=
                      Evm.Cancun.Vm.Effect.applyMessage)
    (chainId        : Evm.U256 := 1) :
    Except String Evm.Frontier.TxResult := do
  -- Steps 1+2: bump nonce + credit mint, *before* execution. These
  -- survive even if step 3 fails.
  let sender   := tx.from_
  let preAcc   := state.getAccount sender
  let stateWithMint :=
    let st := state.setAccount sender
      { preAcc with nonce := preAcc.nonce + 1 }
    if tx.mint = (0 : Evm.U256) then st else st.addBalance sender tx.mint

  -- Step 3: execute the call or create.
  -- Post-Regolith (Bedrock launch on Base), deposited txs pay
  -- intrinsic gas like normal user txs — the receipt's gasUsed
  -- INCLUDES the calldata-cost intrinsic, so the EVM only sees
  -- `tx.gas - intrinsic` for execution. Pre-Regolith (never
  -- deployed on Base mainnet), the full tx.gas would flow to the
  -- EVM with intrinsic uncharged.
  let intrinsic := intrinsicGas tx.data tx.to.isNone
  let gasAvailable := tx.gas.toNat - intrinsic
  let env : Environment :=
    { origin              := sender
      gasPrice            := (0 : Evm.U256)   -- deposited txs are gas-free
      coinbase            := coinbase, number := number, difficulty := 0
      gasLimit            := gasLimit, timestamp := timestamp
      blockHashes         := blockHashes, state := stateWithMint
      touched             := [sender]
      accessedAddresses   := [sender]
      accessedStorageKeys := []
      baseFeePerGas       := baseFeePerGas
      blobVersionedHashes := []
      prevRandao          := prevRandao
      chainId             := chainId }

  let runResult : Except Exception Evm :=
    match tx.to with
    | some recipient =>
      let recipientAcc := stateWithMint.getAccount recipient
      let stateAfterTransfer :=
        if tx.value = (0 : Evm.U256) then stateWithMint
        else (stateWithMint.subBalance sender tx.value).addBalance recipient tx.value
      let envT := { env with state := stateAfterTransfer }
      let msg : Message :=
        { caller := sender, target := some recipient, currentTarget := recipient,
          value := tx.value, data := tx.data, code := recipientAcc.code,
          gas := gasAvailable, depth := 0 }
      (applyMessage msg envT).bind fun subEvm =>
        if subEvm.reverted then
          -- Roll back value transfer; mint+nonce already committed to
          -- `stateWithMint` and survive the rollback.
          .ok { subEvm with env := { envT with state := stateWithMint } }
        else
          .ok subEvm
    | none =>
      let newAddr := Evm.Frontier.Utils.computeContractAddress sender preAcc.nonce
      let envState :=
        let st := (stateWithMint.subBalance sender tx.value).addBalance newAddr tx.value
        let na := st.getAccount newAddr
        st.setAccount newAddr { na with nonce := 1 }
      let envT := { env with state := envState }
      let msg : Message :=
        { caller := sender, target := some newAddr, currentTarget := newAddr,
          value := tx.value, data := Evm.Bytes.empty, code := tx.data,
          gas := gasAvailable, depth := 0 }
      (applyMessage msg envT).bind fun subEvm =>
        if subEvm.reverted then
          -- Roll back CREATE; mint+nonce survive.
          .ok { subEvm with env := { env with state := stateWithMint },
                            output := Evm.Bytes.empty }
        else
          let codeBytes := subEvm.output
          let st := subEvm.env.state.setAccount newAddr
            { (subEvm.env.state.getAccount newAddr) with code := codeBytes }
          .ok { subEvm with env := { subEvm.env with state := st } }

  -- Step 4+5: pack the result. On hard error (exception thrown by
  -- the EVM beyond REVERT — e.g. invalid opcode), roll back ALL
  -- execution-side state changes but keep `stateWithMint`.
  let (newState, gasLeft, refund, logs, success) :=
    match runResult with
    | .ok subEvm => (subEvm.env.state, subEvm.gasLeft,
                     (if subEvm.reverted then 0 else subEvm.env.refundCounter),
                     subEvm.env.logs, !subEvm.reverted)
    | .error _   => (stateWithMint, 0, 0, ([] : List Log), false)

  -- Post-Regolith (Bedrock launch on Base mainnet) a deposit is metered as a type-2 tx
  -- (specs `deposits.md` §Execution: "processed exactly like a type-2 (EIP-1559)
  -- transaction … gas metering is the same"): the receipt's gasUsed is the gas used less
  -- the refund, capped at a fifth (EIP-3529; every OP fork is London+). No ETH moves for
  -- it — the gas price is 0. op-geth `innerExecute` (state_transition.go@79e9d24 610-690)
  -- adds `calcRefund` for deposits too. (Until 2026-11-14 this returned the gas used before
  -- the refund.)
  let used := tx.gas.toNat - gasLeft
  return { state   := newState
           gasUsed := used - min refund (used / 5)
           logs    := logs
           success := success }

/-! ## User-tx processing with OP fee semantics

    Distinct from `Evm.London.processTransaction` in three places:

      1. base-fee × gas_used → BaseFeeVault (NOT burnt)
      2. priority × gas_used → SequencerFeeVault (NOT the header
         coinbase — though on OP they happen to be the same address)
      3. L1 data fee → L1FeeVault (no Ethereum-mainnet analog)

    The EVM itself (opcode dispatch, gas charging, refund cap,
    EIP-3529 etc.) is the supplied `applyMessage`. -/

structure UserTxInputs where
  /-- Pre-recovered tx sender. -/
  sender            : Evm.Address
  /-- Effective gas price = `min(maxFee, baseFee + priorityFee)`
      for type-2; `gasPrice` for legacy/type-1. -/
  effectiveGasPrice : Nat
  /-- `tx.gas` — the gas limit. -/
  gas               : Nat
  to                : Option Evm.Address
  value             : Evm.U256
  data              : Evm.Bytes
  nonce             : Nat
  /-- Pre-computed L1 data fee (use `Evm.Optimism.Replay.l1FeeWei`).
      Charged to the sender on top of the EVM gas fee; credited to
      L1FeeVault. -/
  l1FeeWei          : Nat
  /-- EIP-2930 access list. Each entry is an account address +
      pre-declared storage slots. Adds to intrinsic gas (2400 per
      account, 1900 per slot) and pre-warms each in the EIP-2929
      access set. Legacy (type-0) txs leave this empty. -/
  accessList        : List (Evm.Address × List Evm.U256) := []
  deriving Inhabited

/-- Precompile warm-seed of every user tx: 0x01..0x0a (Cancun's full set,
    incl. KZG point eval at 0x0a) and RIP-7212 P256VERIFY at 0x100, which
    OP-stack adds at Fjord; warming it matches op-geth's pre-warm (the first
    STATICCALL of a handleOps batch pays warm 100, not cold 2600).

    KNOWN GAP: the seed is the same at every fork. op-geth warms only the
    fork's active precompiles, so before Fjord 0x100 — and before Ecotone
    (Cancun rules) 0x0a — must be cold; warming changes the access cost of a
    first CALL to them (an empty account is still charged cold). Stated as
    the open `Fjord.Spec.Soundness.precompile_warm_seed_per_fork`. -/
def userTxPrecompileWarmSeed : List Evm.Address :=
  (List.range 10).map (fun i => Evm.Address.ofNat (i + 1)) ++ [Evm.Address.ofNat 0x100]

/-- Run one non-deposited user tx with OP fee routing.

    Returns the post-state + gas used. Fee-vault credits are applied
    in this function (vs. London where the coinbase credit happens
    after `processTransaction` returns). -/
def processUserTx
    (state          : State)
    (blockHashes    : List Evm.Hash32)
    (coinbase       : Evm.Address)
    (number gasLimit timestamp : Nat)
    (baseFeePerGas  : Nat)
    (prevRandao     : Evm.Hash32)
    (tx             : UserTxInputs)
    (applyMessage   : Message → Environment →
                      Except Exception Evm :=
                      Evm.Cancun.Vm.Effect.applyMessage)
    (eip3860        : Bool := false)
    (chainId        : Evm.U256 := 1)
    (eip7623        : Bool := false)
    (authIntrinsic  : Nat := 0)
    (auths          : List Evm.Prague.Authorization := []) :
    Except String Evm.Frontier.TxResult := do
  -- Pre-execution sender bookkeeping. EVM-side accounting (intrinsic
  -- gas, EIP-2929 warm-seed) is delegated to applyMessage; the OP
  -- delta is purely how the *paid* fees are dispersed afterwards.
  let senderAcc := state.getAccount tx.sender
  if senderAcc.nonce ≠ tx.nonce then
    .error s!"nonce mismatch (got {senderAcc.nonce}, expected {tx.nonce})"
  -- EIP-2930 access-list intrinsic surcharge: 2400 per account, 1900
  -- per storage key. Charged at tx entry on top of the base intrinsic.
  let aclGas : Nat :=
    tx.accessList.foldl (init := 0)
      (fun acc (_, keys) => acc + 2400 + keys.length * 1900)
  -- EIP-7702: each authorization adds PER_AUTH_BASE_COST (12500) to
  -- intrinsic. Caller (Isthmus) passes the total.
  let intrinsic := intrinsicGas tx.data tx.to.isNone (eip3860 := eip3860)
                   + aclGas + authIntrinsic
  -- EIP-7623 (Prague / OP Isthmus) "calldata floor": the receipt's
  -- billed gasUsed is at least `21000 + 10 * tokens` where
  -- `tokens = zeros + 4 * nonzero`. When the EVM uses LESS than the
  -- floor, sender is charged the floor anyway (sender pays for
  -- calldata bandwidth even if execution was cheap). Computed here
  -- so the refund-cap step below can clamp against it. EIP-7623's
  -- floor INCLUDES the access-list surcharge.
  let floorGas : Nat :=
    if eip7623 then Id.run do
      let mut zeros : Nat := 0
      let mut nonZero : Nat := 0
      for i in [0:tx.data.size] do
        if tx.data.get! i = (0 : UInt8) then zeros := zeros + 1
        else nonZero := nonZero + 1
      pure (21000 + 10 * (zeros + 4 * nonZero) + aclGas)
    else 0
  if tx.gas < intrinsic then
    .error s!"intrinsic gas ({intrinsic}) exceeds tx gas limit ({tx.gas})"
  let upfront := tx.gas * tx.effectiveGasPrice + tx.l1FeeWei
  if senderAcc.balance.toNat < upfront + tx.value.toNat then
    .error "insufficient balance"
  let state := state.setAccount tx.sender
    { senderAcc with
        nonce   := senderAcc.nonce + 1
        balance := senderAcc.balance - Evm.U256.ofNat upfront }

  -- EIP-7702: apply set-code authorizations AFTER bumping the
  -- sender nonce (the sender-is-authority case relies on this
  -- ordering — see EELS `prague/fork.py::process_transaction`).
  let (state, authRefund) : State × Nat :=
    if auths.isEmpty then (state, 0)
    else
      let p0 : Evm.Prague.State := { inner := state }
      let (p1, r) := Evm.Prague.Utils.applyAuthorizations p0 chainId auths
      (p1.inner, r)

  -- EIP-2929 (Berlin+) warm seed for the tx:
  --   sender, tx.to (or derived CREATE address), precompiles 0x01..0x09.
  -- OP-stack adds COINBASE (= SequencerFeeVault) at Shanghai+
  -- (EIP-3651) — see L1Block's warmCoinbase plumbing on the
  -- per-fork applyMessage adapter. Bedrock pre-Shanghai never set
  -- it; Canyon-onwards (= every Base mainnet block) DOES want it,
  -- so we include coinbase unconditionally here. (Caught by tx 8
  -- of block 0x800000 — DELEGATECALL to tx.to was treated as
  -- cold (+2500 gas) when op-geth's pre-warm makes it warm.)
  let txToWarm : List Evm.Address :=
    match tx.to with
    | some t => [t]
    | none   =>
      [Evm.Frontier.Utils.computeContractAddress tx.sender senderAcc.nonce]
  let precompiles : List Evm.Address := userTxPrecompileWarmSeed
  -- EIP-2930: pre-warm access-list addresses + slots.
  let aclAddrs : List Evm.Address := tx.accessList.map Prod.fst
  let aclSlots : List (Evm.Address × Evm.U256) :=
    tx.accessList.foldl (init := []) (fun acc (a, ks) =>
      acc ++ ks.map (fun k => (a, k)))
  let warm : List Evm.Address :=
    ([tx.sender] ++ txToWarm ++ [coinbase] ++ precompiles ++ aclAddrs).foldl
      (init := ([] : List Evm.Address))
      (fun acc a => if acc.contains a then acc else acc ++ [a])

  -- Build env + run the call/create.
  let env : Environment :=
    { origin              := tx.sender
      gasPrice            := Evm.U256.ofNat tx.effectiveGasPrice
      coinbase            := coinbase, number := number, difficulty := 0
      gasLimit            := gasLimit, timestamp := timestamp
      blockHashes         := blockHashes, state := state
      touched             := warm
      accessedAddresses   := warm
      accessedStorageKeys := aclSlots
      baseFeePerGas       := baseFeePerGas
      blobVersionedHashes := []
      prevRandao          := prevRandao
      chainId             := chainId }
  let runResult : Except Exception Evm :=
    match tx.to with
    | some recipient =>
      let recipientAcc := state.getAccount recipient
      let stateAfterTransfer :=
        if tx.value = (0 : Evm.U256) then state
        else (state.subBalance tx.sender tx.value).addBalance recipient tx.value
      let envT := { env with state := stateAfterTransfer }
      let msg : Message :=
        { caller := tx.sender, target := some recipient, currentTarget := recipient,
          value := tx.value, data := tx.data, code := recipientAcc.code,
          gas := tx.gas - intrinsic, depth := 0 }
      (applyMessage msg envT).bind fun subEvm =>
        if subEvm.reverted then
          .ok { subEvm with env := { envT with state := state } }
        else .ok subEvm
    | none =>
      let newAddr := Evm.Frontier.Utils.computeContractAddress tx.sender senderAcc.nonce
      let envState :=
        let st := (state.subBalance tx.sender tx.value).addBalance newAddr tx.value
        let na := st.getAccount newAddr
        st.setAccount newAddr { na with nonce := 1 }
      let envT := { env with state := envState }
      let msg : Message :=
        { caller := tx.sender, target := some newAddr, currentTarget := newAddr,
          value := tx.value, data := Evm.Bytes.empty, code := tx.data,
          gas := tx.gas - intrinsic, depth := 0 }
      (applyMessage msg envT).bind fun subEvm =>
        if subEvm.reverted then
          .ok { subEvm with env := { env with state := state },
                            output := Evm.Bytes.empty }
        else
          -- EIP-170 / EIP-3860 code deposit: charge 200 gas per byte
          -- of returned runtime code. The opcode-level CREATE handler
          -- (Cancun trampoline `.createLike` branch) does this too;
          -- tx-level CREATE was previously skipping it, leaving us
          -- ~200 * runtime_size short on every deploy.
          let depositCost :=
            Evm.Frontier.Vm.Gas.codeDeposit * subEvm.output.size
          if subEvm.gasLeft < depositCost then
            .ok { subEvm with env := { env with state := state },
                              output := Evm.Bytes.empty,
                              reverted := true,
                              gasLeft := 0 }
          else
            let st := subEvm.env.state.setAccount newAddr
              { (subEvm.env.state.getAccount newAddr) with code := subEvm.output }
            .ok { subEvm with env := { subEvm.env with state := st },
                              gasLeft := subEvm.gasLeft - depositCost }

  let (newState, gasLeftFinal, logs, refundCtr, success) :=
    match runResult with
    | .ok subEvm =>
      (subEvm.env.state, subEvm.gasLeft, subEvm.env.logs,
       subEvm.env.refundCounter, !subEvm.reverted)
    | .error _   => (state, 0, ([] : List Log), 0, false)

  -- EIP-3529 refund accounting (London+, inherited by every OP fork):
  -- cap the SSTORE-clear refund at gasUsedRaw / 5 and DEDUCT it from
  -- the chargeable gasUsed. The receipt's gasUsed = post-refund
  -- value, so any divergence here surfaces as a gas mismatch.
  let gasUsedRaw := tx.gas - gasLeftFinal
  -- EIP-7702 contributes to the same refund pool as SSTORE-clear
  -- (per EELS prague/fork.py: refundCounter accumulates BOTH the
  -- per-existing-authority `PER_EMPTY_ACCOUNT_COST - PER_AUTH_BASE_COST`
  -- credit AND the EVM's SSTORE refunds before the cap is applied).
  let refund     := min (refundCtr + authRefund) (gasUsedRaw / 5)
  let gasUsedAfterRefund := gasUsedRaw - refund
  -- EIP-7623 calldata floor: gasUsed = max(post-refund, floor).
  let gasUsed    := max gasUsedAfterRefund floorGas
  let refundWei  := (tx.gas - gasUsed) * tx.effectiveGasPrice
  -- Sender gets unused gas + refund back.
  let newState := newState.addBalance tx.sender (Evm.U256.ofNat refundWei)

  -- OP fee routing: credit the three vaults.
  let priority := tx.effectiveGasPrice - baseFeePerGas
  let newState := newState.addBalance
                    Evm.Optimism.Bedrock.Spec.sequencerFeeVault
                    (Evm.U256.ofNat (priority * gasUsed))
  let newState := newState.addBalance
                    Evm.Optimism.Bedrock.Spec.baseFeeVault
                    (Evm.U256.ofNat (baseFeePerGas * gasUsed))
  let newState := newState.addBalance
                    Evm.Optimism.Bedrock.Spec.l1FeeVault
                    (Evm.U256.ofNat tx.l1FeeWei)

  return { state := newState, gasUsed := gasUsed, logs := logs, success := success }

/-! ## Block driver

    Loop the per-block tx list (one deposited prologue + zero-or-more
    user-and-additional-deposited) and produce a post-state.

    Pre-Isthmus there are no other block-level state transitions on
    OP — no validator withdrawals, no per-block system call beyond
    the L1-attributes prologue (which IS the first tx). Withdrawals
    list is required-empty from Canyon onwards (validated here, not
    walked).

    Isthmus adds the `withdrawalsRoot = L2ToL1MessagePasser.storageRoot`
    invariant (block-level); we check that in `Isthmus.Fork`, not here. -/

/-- A single tx in a Base block.

    * `deposited`        — type-0x7E system / L1 → L2 bridge tx.
    * `user`             — legacy / EIP-2930 / EIP-1559 / EIP-4844
                            user tx (the common case).
    * `userWithAuths`    — EIP-7702 set-code tx (type 4). Same shape as
                            `user` plus the authorization list that
                            MUST be applied to state at tx entry. Only
                            Isthmus+ knows how to handle this variant;
                            earlier OP forks error out. -/
inductive OpTx
  | deposited     (tx : DepositedTx)
  | user          (inputs : UserTxInputs)
  | userWithAuths (inputs : UserTxInputs) (auths : List Evm.Prague.Authorization)
  deriving Inhabited

/-- Block-level result: post-state + total gas used + concatenated logs. -/
structure BlockResult where
  state    : State
  gasUsed  : Nat
  logs     : List Log
  deriving Inhabited

private partial def applyAll
    (state : State)
    (blockHashes : List Evm.Hash32)
    (coinbase    : Evm.Address)
    (number gasLimit timestamp : Nat)
    (baseFeePerGas : Nat)
    (prevRandao  : Evm.Hash32)
    (applyMessage : Message → Environment → Except Exception Evm)
    (eip3860 : Bool)
    (chainId : Evm.U256)
    (eip7623 : Bool)
    (txs : List OpTx)
    (gasAcc : Nat) (logsAcc : List Log) :
    Except String BlockResult :=
  match txs with
  | [] => .ok { state := state, gasUsed := gasAcc, logs := logsAcc }
  | OpTx.deposited dtx :: rest => do
    let r ← processDepositedTx state blockHashes coinbase number
              gasLimit timestamp baseFeePerGas prevRandao dtx applyMessage
              (chainId := chainId)
    applyAll r.state blockHashes coinbase number gasLimit timestamp
      baseFeePerGas prevRandao applyMessage eip3860 chainId eip7623 rest
      (gasAcc + r.gasUsed) (logsAcc ++ r.logs)
  | OpTx.user u :: rest => do
    let r ← processUserTx state blockHashes coinbase number
              gasLimit timestamp baseFeePerGas prevRandao u applyMessage
              (eip3860 := eip3860) (chainId := chainId) (eip7623 := eip7623)
    applyAll r.state blockHashes coinbase number gasLimit timestamp
      baseFeePerGas prevRandao applyMessage eip3860 chainId eip7623 rest
      (gasAcc + r.gasUsed) (logsAcc ++ r.logs)
  | OpTx.userWithAuths _ _ :: _ =>
    -- Pre-Isthmus OP forks can't handle EIP-7702 set-code txs.
    -- Isthmus.applyBlock overrides this dispatch and applies the
    -- authorization list before processing the inner UserTxInputs.
    -- Reaching this arm here means the wiring routed a type-4 tx
    -- to a pre-Isthmus driver — refuse loudly rather than silently
    -- drop the auths.
    .error "EIP-7702 set-code transactions require Isthmus or later"

/-- Bedrock block driver. Run all txs in order; produce post-state.

    Takes the four block-context numerics directly (instead of a
    header type), so the caller plumbs whatever header it parsed. -/
def applyBlock
    (state          : State)
    (blockHashes    : List Evm.Hash32)
    (coinbase       : Evm.Address)
    (number gasLimit timestamp : Nat)
    (baseFeePerGas  : Nat)
    (prevRandao     : Evm.Hash32)
    (txs            : List OpTx)
    (applyMessage   : Message → Environment →
                      Except Exception Evm :=
                      Evm.Cancun.Vm.Effect.applyMessage)
    (opBn256PairingCap : Option Nat := none)
    (debugTrace        : Bool       := false)
    (eip3860           : Bool       := false)
    (chainId           : Evm.U256   := 1)
    (eip7623           : Bool       := false) :
    Except String BlockResult :=
  -- Wrap applyMessage so every call sees the OP Granite-cap setting
  -- in the Environment. mainnet callers pass `none` and pay no cost;
  -- OP Granite+ callers pass `some 1536` to enforce the input cap.
  -- `debugTrace` is propagated so tx-level tooling can flip it on
  -- per-tx in a block driver and get a per-step opcode trace
  -- (see `Evm.Cancun.Vm.Effect.runFrame`).
  let applyMessage' : Message → Environment → Except Exception Evm :=
    fun msg env =>
      applyMessage msg
        { env with
            opBn256PairingCap := opBn256PairingCap
            debugTrace        := debugTrace }
  applyAll state blockHashes coinbase number gasLimit timestamp
    baseFeePerGas prevRandao applyMessage' eip3860 chainId eip7623 txs 0 []

end Evm.Optimism.Bedrock
