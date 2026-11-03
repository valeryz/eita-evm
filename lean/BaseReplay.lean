/-
  BaseReplay — fetch a Base block + its pre-state, replay through
  Eita, compare the post-state root to the chain's reported
  `stateRoot`.

  Usage:
      export BASE_RPC_URL=https://base-mainnet.g.alchemy.com/v2/<key>
      .lake/build/bin/baseReplay 0x2c865c2
      .lake/build/bin/baseReplay finalized
-/

import Lean.Data.Json
import Evm.BaseTypes
import Evm.Crypto.Hash
import Evm.Frontier.StateRoot
import Evm.SpuriousDragon.Utils.Signature
import Evm.Optimism.Forks
import Evm.Optimism.Replay.Fetch
import Evm.Optimism.Replay.Parse
import Evm.Optimism.Replay.Prestate
import Evm.Optimism.Replay.Dispatch
import Evm.Optimism.Bedrock.Fork
import Evm.Prague.Transactions
import Evm.Prague.Utils.Authorization

open Lean (Json)

/-! ## Helpers (mirroring `BaseProbe.lean` for hex / args parsing). -/

private def decToHex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

private def parseBlockArg (arg : String) : String :=
  if arg.startsWith "0x" then arg
  else
    match arg.toNat? with
    | some n => decToHex n
    | none   => arg

/-- Bytes → hex string (no 0x). -/
private def bytesToHex (b : Evm.Bytes) : String := Id.run do
  let hexChar (n : Nat) : Char :=
    if n < 10 then Char.ofNat (n + '0'.toNat)
    else Char.ofNat (n - 10 + 'a'.toNat)
  let mut out := ""
  for i in [0:b.size] do
    let byte := b.get! i
    out := out.push (hexChar (byte.toNat >>> 4))
    out := out.push (hexChar (byte.toNat &&& 0xf))
  return out

/-! ## Tx conversion: JSON → OpTx -/

/-- Build a `UserTxInputs` from a parsed JSON tx + the block's
    baseFeePerGas + the receipt's `l1Fee`. Sender comes from the
    JSON's `from` field (Alchemy includes it for non-deposited txs). -/
private def buildUserTx (j : Json) (baseFeePerGas : Nat) (l1FeeWei : Nat) :
    Except String Evm.Optimism.Bedrock.UserTxInputs := do
  let txType : String := (j.getObjValAs? String "type").toOption.getD "0x0"
  let sender : Evm.Address :=
    match j.getObjVal? "from" with
    | .ok (.str s) => Evm.Optimism.Replay.Parse.hexToAddress s
    | _ => 0
  let to : Option Evm.Address :=
    match j.getObjVal? "to" with
    | .ok (.str s) => if s = "" then none else some (Evm.Optimism.Replay.Parse.hexToAddress s)
    | .ok .null    => none
    | _ => none
  let value : Evm.U256 :=
    match j.getObjVal? "value" with
    | .ok (.str s) => Evm.Optimism.Replay.Parse.hexToU256 s
    | _ => 0
  let gas : Nat :=
    match j.getObjVal? "gas" with
    | .ok (.str s) => Evm.Optimism.Replay.Parse.hexToNat s
    | _ => 0
  let nonce : Nat :=
    match j.getObjVal? "nonce" with
    | .ok (.str s) => Evm.Optimism.Replay.Parse.hexToNat s
    | _ => 0
  let data : Evm.Bytes :=
    match j.getObjVal? "input" with
    | .ok (.str s) => (Evm.Optimism.Replay.Parse.hexToBytes s).getD ByteArray.empty
    | _ => ByteArray.empty
  -- Effective gas price: type-2 uses min(maxFee, baseFee + maxPriority);
  -- legacy/type-1 uses gasPrice.
  let effGasPrice : Nat :=
    if txType = "0x2" ∨ txType = "0x3" ∨ txType = "0x4" then
      let maxFee :=
        match j.getObjVal? "maxFeePerGas" with
        | .ok (.str s) => Evm.Optimism.Replay.Parse.hexToNat s
        | _ => 0
      let maxPrio :=
        match j.getObjVal? "maxPriorityFeePerGas" with
        | .ok (.str s) => Evm.Optimism.Replay.Parse.hexToNat s
        | _ => 0
      min maxFee (baseFeePerGas + maxPrio)
    else
      match j.getObjVal? "gasPrice" with
      | .ok (.str s) => Evm.Optimism.Replay.Parse.hexToNat s
      | _ => 0
  -- L1 data fee: taken from the receipt's `l1Fee` field. A
  -- follow-up will cross-check this against our in-tree formula
  -- in `Evm.Optimism.Replay.l1FeeWei` (which needs the L1Block
  -- predeploy storage params extracted from the prologue tx's
  -- calldata).
  -- EIP-2930 access list (always present for type-1 / type-2 / type-3 /
  -- type-4; absent or empty for legacy type-0).
  let accessList : List (Evm.Address × List Evm.U256) :=
    match j.getObjVal? "accessList" with
    | .ok (.arr arr) =>
      arr.toList.filterMap fun entry =>
        match entry.getObjVal? "address", entry.getObjVal? "storageKeys" with
        | .ok (.str addrStr), .ok (.arr keysArr) =>
          let addr := Evm.Optimism.Replay.Parse.hexToAddress addrStr
          let keys := keysArr.toList.filterMap fun k =>
            match k with
            | .str s => some (Evm.Optimism.Replay.Parse.hexToU256 s)
            | _ => none
          some (addr, keys)
        | _, _ => none
    | _ => []
  return {
    sender            := sender
    effectiveGasPrice := effGasPrice
    gas               := gas
    to                := to
    value             := value
    data              := data
    nonce             := nonce
    l1FeeWei          := l1FeeWei
    accessList        := accessList
  }

/-- Parse the EIP-7702 authorization list from a type-4 tx JSON. -/
private def parseAuthorizations (j : Json) : List Evm.Prague.Authorization :=
  match j.getObjVal? "authorizationList" with
  | .ok (.arr arr) =>
    arr.toList.filterMap fun a =>
      match a.getObjVal? "chainId", a.getObjVal? "address",
            a.getObjVal? "nonce", a.getObjVal? "yParity",
            a.getObjVal? "r", a.getObjVal? "s" with
      | .ok (.str ch), .ok (.str ad), .ok (.str nc),
        .ok (.str yp), .ok (.str rh), .ok (.str sh) =>
        some {
          chainId := Evm.Optimism.Replay.Parse.hexToU256 ch
          address := Evm.Optimism.Replay.Parse.hexToAddress ad
          nonce   := BitVec.ofNat 64 (Evm.Optimism.Replay.Parse.hexToNat nc)
          yParity := Evm.Optimism.Replay.Parse.hexToU256 yp
          r       := Evm.Optimism.Replay.Parse.hexToU256 rh
          s       := Evm.Optimism.Replay.Parse.hexToU256 sh }
      | _, _, _, _, _, _ => none
  | _ => []

/-- Convert one tx JSON to an `OpTx`. `l1FeeWei` is taken from the
    matching receipt; deposited txs ignore it. Type-4 (EIP-7702
    set-code) txs become `.userWithAuths`. -/
private def buildOpTx (j : Json) (baseFeePerGas : Nat) (l1FeeWei : Nat) :
    Except String Evm.Optimism.Bedrock.OpTx := do
  if Evm.Optimism.Replay.Parse.isDeposited j then
    let dtx ← Evm.Optimism.Replay.Parse.parseDepositedTx j
    return .deposited dtx
  else
    let u ← buildUserTx j baseFeePerGas l1FeeWei
    -- Type-4: EIP-7702 set-code with an authorization list.
    let txType : String := (j.getObjValAs? String "type").toOption.getD "0x0"
    if txType = "0x4" then
      let auths := parseAuthorizations j
      let _ := dbgTrace s!"TYPE4 tx: auths_count={auths.length}" (fun _ => ())
      return .userWithAuths u auths
    else
      return .user u

/-! ## Entry point -/

/-- Extract the `--trace-tx N` flag from args. Returns the index
    (some N) or none, plus the remaining positional args. -/
private def extractTraceFlag (args : List String) : (Option Nat × List String) :=
  let rec go (acc : List String) (rest : List String) : Option Nat × List String :=
    match rest with
    | "--trace-tx" :: n :: tl => (n.toNat?, (acc.reverse) ++ tl)
    | x :: tl => go (x :: acc) tl
    | [] => (none, acc.reverse)
  go [] args

def main (args : List String) : IO Unit := do
  let (traceTx, positional) := extractTraceFlag args
  let url ← Evm.Optimism.Replay.Fetch.rpcUrl
  IO.println s!"endpoint: {url}"
  let blockHex ← (
    match positional with
    | []     => Evm.Optimism.Replay.Fetch.fetchBlockNumber
    | a :: _ => pure (parseBlockArg a) : IO String)
  IO.println s!"block:    {blockHex}"
  match traceTx with
  | some n => IO.println s!"TRACE MODE: tracing tx index {n} (output on stderr)"
  | none   => pure ()

  -- (1) Fetch the block.
  let blockResp ← Evm.Optimism.Replay.Fetch.fetchBlock blockHex
  let result : Json ← match blockResp.getObjVal? "result" with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"no result: {e}"

  -- (2) Parse the header.
  let header ← match Evm.Optimism.Replay.Parse.parseHeader result with
    | .ok h => pure h
    | .error e => throw <| IO.userError s!"bad header: {e}"
  let opFork := Evm.Optimism.OpFork.baseMainnetAt header.timestamp
  IO.println s!"OP fork:  {repr opFork}"

  -- (3) Fetch receipts for per-tx l1Fee.
  let receiptsResp ← Evm.Optimism.Replay.Fetch.fetchReceipts blockHex
  let receiptsArr : Array Json ← match receiptsResp.getObjValAs? (Array Json) "result" with
    | .ok a => pure a
    | .error e => throw <| IO.userError s!"no receipts: {e}"
  let l1Fees : List Nat := receiptsArr.toList.map fun r =>
    match r.getObjVal? "l1Fee" with
    | .ok (.str s) => Evm.Optimism.Replay.Parse.hexToNat s
    | _ => 0

  -- (4) Build OpTx list using the receipt's l1Fee per tx.
  let txArr ← match result.getObjValAs? (Array Json) "transactions" with
    | .ok a => pure a
    | .error e => throw <| IO.userError s!"no transactions: {e}"
  let pairs := txArr.toList.zip l1Fees
  let opTxs ← match pairs.mapM (fun (tx, fee) => buildOpTx tx header.baseFeePerGas fee) with
    | .ok l => pure l
    | .error e => throw <| IO.userError s!"tx parse: {e}"
  IO.println s!"txs:      {opTxs.length}"
  -- DEBUG: count type-4 in opTxs
  let n4 := opTxs.foldl (init := 0) (fun acc t =>
    match t with
    | .userWithAuths _ _ => acc + 1
    | _ => acc)
  IO.println s!"[debug] type-4 (userWithAuths) txs detected: {n4}"

  -- (4) Fetch prestate.
  IO.println "fetching prestate (this is the big one)..."
  let prestateResp ← Evm.Optimism.Replay.Fetch.fetchPrestate blockHex
  let preState0 ← match Evm.Optimism.Replay.Prestate.parseBlockPrestate prestateResp with
    | .ok s => pure s
    | .error e => throw <| IO.userError s!"bad prestate: {e}"
  let mut preState := preState0
  IO.println s!"prestate: {preState.accounts.length} accounts, {preState.storage.length} slots"

  -- EIP-7702 enrichment: prestate-tracer doesn't include the
  -- authority accounts (they're not READ by the EVM — auths are
  -- processed BEFORE the EVM runs). For every type-4 tx, recover
  -- each auth's authority and fetch its nonce + code at parent
  -- block height. Without this, step-5 of applyAuthorization
  -- always rejects (sees default nonce=0 vs auth.nonce=N≥1).
  let parentHex : String :=
    let n := Evm.Optimism.Replay.Parse.hexToNat blockHex
    if n = 0 then blockHex else decToHex (n - 1)
  let authorities : List Evm.Address := opTxs.foldl (init := []) fun acc t =>
    match t with
    | .userWithAuths _ auths =>
      auths.foldl (init := acc) fun acc' a =>
        match Evm.Prague.Utils.recoverAuthority a with
        | some addr => if acc'.contains addr then acc' else acc' ++ [addr]
        | none => acc'
    | _ => acc
  for addr in authorities do
    let addrHex := "0x" ++ String.ofList (Nat.toDigits 16 addr.toNat)
    let nonce ← Evm.Optimism.Replay.Fetch.fetchNonce addrHex parentHex
    let code  ← Evm.Optimism.Replay.Fetch.fetchCode  addrHex parentHex
    -- Only fill in if missing/empty in prestate.
    let existing := preState.getAccount addr
    if existing.nonce = 0 ∧ existing.code.size = 0 then
      preState := preState.setAccount addr
        { existing with nonce := nonce, code := code }
  if authorities.length > 0 then
    IO.println s!"  [eip-7702] enriched {authorities.length} authority accounts"

  -- BLOCKHASH support: env.blockHashes is indexed so that
  --   blockHashes[len - (curN - n)] = hash(block n).
  -- For len=256, that means blockHashes[255] = hash(curN-1) (parent),
  -- blockHashes[0] = hash(curN-256). We fetch the past `hashWindow`
  -- block hashes via lightweight `eth_getBlockByNumber(false)` calls
  -- (cached on disk; the first replay of a block range pays a
  -- one-time cost, subsequent runs are free). Tx 76 of 0x2c97f2e
  -- calls BLOCKHASH(curN - 32) — without this it returns 0 and the
  -- contract reverts.
  let curN := Evm.Optimism.Replay.Parse.hexToNat blockHex
  let hashWindow : Nat := 256
  let firstN := if curN ≥ hashWindow then curN - hashWindow else 0
  let mut blockHashes : List Evm.Hash32 := []
  for k in [firstN:curN] do
    let h ← Evm.Optimism.Replay.Fetch.fetchBlockHash (decToHex k)
    -- Parse "0xabcd..." (66 chars) → BitVec 256.
    let s := (h.replace "0x" "").replace "0X" ""
    let n : Nat := s.foldl (init := 0) fun acc c =>
      let d := if c.isDigit then c.toNat - '0'.toNat
               else if 'a' ≤ c ∧ c ≤ 'f' then 10 + c.toNat - 'a'.toNat
               else if 'A' ≤ c ∧ c ≤ 'F' then 10 + c.toNat - 'A'.toNat
               else 0
      acc * 16 + d
    blockHashes := blockHashes ++ [BitVec.ofNat 256 n]

  -- (5) Run applyBlockFor. If --trace-tx N: run prefix [0..N-1]
  -- silently, then run [txN] alone with debugTrace on.
  -- Base mainnet chain ID = 8453.
  let baseChainId : Evm.U256 := 8453
  let r ← match traceTx with
    | none =>
      match Evm.Optimism.Replay.applyBlockFor opFork
              preState blockHashes header.coinbase header.number header.gasLimit
              header.timestamp header.baseFeePerGas header.mixHash opTxs
              (chainId := baseChainId) with
      | .ok r => pure r
      | .error e => throw <| IO.userError s!"applyBlock: {e}"
    | some n => do
      let prefixTxs := opTxs.take n
      let targetTx  := opTxs.drop n |>.take 1
      let r1 ← match Evm.Optimism.Replay.applyBlockFor opFork
                  preState blockHashes header.coinbase header.number header.gasLimit
                  header.timestamp header.baseFeePerGas header.mixHash prefixTxs
                  (chainId := baseChainId) with
        | .ok r => pure r
        | .error e => throw <| IO.userError s!"prefix: {e}"
      IO.eprintln s!"--- BEGIN OPCODE TRACE FOR TX {n} ---"
      let r2 ← match Evm.Optimism.Replay.applyBlockFor opFork
                  r1.state blockHashes header.coinbase header.number header.gasLimit
                  header.timestamp header.baseFeePerGas header.mixHash targetTx
                  (debugTrace := true) (chainId := baseChainId) with
        | .ok r => pure r
        | .error e => throw <| IO.userError s!"trace tx: {e}"
      IO.eprintln s!"--- END OPCODE TRACE ---"
      pure { state := r2.state
             gasUsed := r1.gasUsed + r2.gasUsed
             logs := r1.logs ++ r2.logs }
  IO.println s!"replayed: gasUsed={r.gasUsed} (expected {header.gasUsed})"

  -- (5b) Per-tx breakdown: compare each tx's gasUsed (and status)
  -- against op-geth's receipt. Done by re-running prefixes of the
  -- tx list — wasteful but tractable for small blocks and clearly
  -- shows WHICH tx diverges.
  IO.println "\nper-tx gas/status comparison:"
  let mut prevTotal := 0
  for i in [0:opTxs.length] do
    let prefixTxs := opTxs.take (i + 1)
    let r' ← match Evm.Optimism.Replay.applyBlockFor opFork
              preState blockHashes header.coinbase header.number header.gasLimit
              header.timestamp header.baseFeePerGas header.mixHash
              prefixTxs (chainId := baseChainId) with
      | .ok r => pure r
      | .error _ => pure { state := preState, gasUsed := prevTotal, logs := [] }
    let txGas := r'.gasUsed - prevTotal
    prevTotal := r'.gasUsed
    let receiptJson := receiptsArr[i]!
    let expGas : Nat :=
      match receiptJson.getObjVal? "gasUsed" with
      | .ok (.str s) => Evm.Optimism.Replay.Parse.hexToNat s
      | _ => 0
    let expStatus : String :=
      match receiptJson.getObjVal? "status" with
      | .ok (.str s) => s
      | _ => "?"
    let mark := if txGas = expGas then "OK " else "DIFF"
    IO.println s!"  tx {i}: {mark} gas={txGas} (exp={expGas}) status_exp={expStatus}"

  -- (6) Per-account correctness check via the prestateTracer's
  -- `diffMode`. Full state-root matching would need the entire
  -- world state (gigabytes); the per-account diff check is the
  -- targeted-and-useful version.
  let diffResp ← Evm.Optimism.Replay.Fetch.fetchStateDiff blockHex
  let diffResult ← match diffResp.getObjVal? "result" with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"no diff result: {e}"
  let diffArr ← match diffResult.getArr? with
    | .ok a => pure a
    | .error e => throw <| IO.userError s!"diff not array: {e}"

  -- Union all per-tx `post` maps — each touched account's expected
  -- post-block value is the LAST tx that touched it.
  let mut expectedPost : List (Evm.Address × Json) := []
  for txEntry in diffArr.toList do
    let inner ←
      match txEntry.getObjVal? "result" with
      | .ok r => pure r
      | .error _ => pure txEntry
    match inner.getObjVal? "post" with
    | .ok (.obj entries) =>
      for ⟨addrStr, accJ⟩ in entries do
        let addr := Evm.Optimism.Replay.Parse.hexToAddress addrStr
        expectedPost := expectedPost.filter (·.1 ≠ addr) ++ [(addr, accJ)]
    | _ => pure ()

  IO.println s!"\nper-account diff check: {expectedPost.length} accounts changed"
  let mut matchedCount := 0
  let mut mismatches : List String := []
  for (addr, expJ) in expectedPost do
    let actualAcc := r.state.getAccount addr
    let expBal : Option Nat :=
      match expJ.getObjVal? "balance" with
      | .ok (.str s) => some (Evm.Optimism.Replay.Parse.hexToNat s)
      | _ => none
    let expNonce : Option Nat :=
      match expJ.getObjVal? "nonce" with
      | .ok (.num n) => some n.toFloat.toUInt64.toNat
      | _ => none
    let mut ok := true
    let mut why := ""
    if let some eb := expBal then
      if actualAcc.balance.toNat ≠ eb then
        ok := false; why := why ++ s!" balance(exp={eb} got={actualAcc.balance.toNat})"
    if let some en := expNonce then
      if actualAcc.nonce ≠ en then
        ok := false; why := why ++ s!" nonce(exp={en} got={actualAcc.nonce})"
    -- Check storage diffs.
    match expJ.getObjVal? "storage" with
    | .ok (.obj sEntries) =>
      for ⟨slotStr, valJ⟩ in sEntries do
        let slot := Evm.Optimism.Replay.Parse.hexToU256 slotStr
        let expVal :=
          match valJ with
          | .str s => Evm.Optimism.Replay.Parse.hexToU256 s
          | _ => 0
        let actualVal := r.state.getStorage addr slot
        if actualVal ≠ expVal then
          ok := false; why := why ++ s!" slot{slot.toNat}(exp={expVal.toNat} got={actualVal.toNat})"
    | _ => pure ()
    if ok then
      matchedCount := matchedCount + 1
    else
      mismatches := mismatches ++ [s!"  0x{Evm.Optimism.Replay.Parse.stripHex (String.ofList (Nat.toDigits 16 addr.toNat))} →{why}"]
  IO.println s!"  matched:    {matchedCount}"
  IO.println s!"  mismatched: {mismatches.length}"
  for m in mismatches do
    IO.println m
