/-
  Mainnet — replay real Ethereum mainnet block headers against our
  Frontier impl, starting from the genesis allocation.

  Inputs:
    * `chains/ethereum/genesis.json` — the mainnet pre-mine allocation
      (8893 addresses), in geth's standard genesis-spec format.
    * `data/blocks/headers/blocks-*.json` — JSONL of every pre-Merge
      mainnet block header. No transaction bodies, so we can only
      replay blocks where `transaction_count == 0` AND `sha3_uncles`
      is the empty-list hash. For those, the only state change is the
      5 ETH miner reward.

  Three modes:
    * `lake exe mainnet genesis <path>` — load alloc, compute state
      root, compare to the known mainnet root `d7f8974f…`.
    * `lake exe mainnet headers <genesis> <jsonl-file>` — verify the
      genesis root, then iterate the JSONL, applying empty blocks
      and verifying each header.state_root. Stops on the first block
      that's not pure-miner-reward.
-/

import Lean.Data.Json
import Evm.BaseTypes
import Evm.Frontier.Fork
import Evm.Frontier.StateRoot

open Lean (Json)

namespace Mainnet

/-! ## Helpers -/

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def stripHex (s : String) : String :=
  if s.startsWith "0x" ∨ s.startsWith "0X" then
    String.ofList (s.toList.drop 2)
  else s

def hexToNat (s : String) : Nat := Id.run do
  let mut acc : Nat := 0
  for c in (stripHex s).toList do
    match hexDigit? c with
    | some d => acc := acc * 16 + d
    | none   => return acc
  pure acc

def decToNat (s : String) : Nat := Id.run do
  let mut acc : Nat := 0
  for c in s.toList do
    if '0' ≤ c ∧ c ≤ '9' then
      acc := acc * 10 + (c.toNat - '0'.toNat)
    else
      return acc
  pure acc

def hexToBytes (s : String) : Evm.Bytes := Id.run do
  let hex := stripHex s
  let padded := if hex.length % 2 = 1 then "0" ++ hex else hex
  let mut out : Evm.Bytes := ByteArray.empty
  let mut rest := padded.toList
  while rest.length ≥ 2 do
    match rest with
    | hi :: lo :: tail =>
      out := out.push (UInt8.ofNat
        ((hexDigit? hi).getD 0 * 16 + (hexDigit? lo).getD 0))
      rest := tail
    | _ => rest := []
  pure out

private def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 0x30) else Char.ofNat (n - 10 + 0x61)

def bytesHex (b : ByteArray) : String := Id.run do
  let mut out := ""
  for i in [0:b.size] do
    let byte := b.get! i
    out := out ++ String.ofList
      [hexChar ((byte.toNat >>> 4) &&& 0xf), hexChar (byte.toNat &&& 0xf)]
  pure out

/-! ## Genesis -/

/-- Mainnet genesis state root, computed by every other client. -/
def mainnetGenesisStateRoot : String :=
  "d7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544"

private def parseAllocEntry (info : Json) : Except String (Nat × Evm.Bytes × Evm.U256) := do
  let balanceStr ← (← info.getObjVal? "balance").getStr?
  let balance := match String.toNat? balanceStr with
    | some n => n
    | none   => 0
  -- nonce / code may be present for some pre-deployed contracts at
  -- genesis (rare). Default to 0 / empty.
  let nonce : Nat := match info.getObjVal? "nonce" with
    | .ok j => match j.getStr? with
      | .ok s => hexToNat s
      | .error _ => 0
    | .error _ => 0
  let code : Evm.Bytes := match info.getObjVal? "code" with
    | .ok j => match j.getStr? with
      | .ok s => hexToBytes s
      | .error _ => Evm.Bytes.empty
    | .error _ => Evm.Bytes.empty
  return (nonce, code, Evm.U256.ofNat balance)

/-- Build a Frontier.State from the parsed genesis alloc object. -/
def loadGenesisState (allocJson : Json) :
    Except String Evm.Frontier.State := do
  let entries ← match allocJson with
    | .obj kvs => .ok kvs
    | _ => .error "genesis alloc is not a JSON object"
  let mut state := Evm.Frontier.State.empty
  for ⟨addrHex, info⟩ in entries.toArray do
    let addr := Evm.Address.ofNat (hexToNat addrHex)
    let (nonce, code, balance) ← parseAllocEntry info
    state := state.setAccount addr
      { nonce := nonce, balance := balance, code := code }
  return state

def checkGenesis (path : String) : IO Unit := do
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept (Lean.Json.parse contents)
  let alloc ← IO.ofExcept (json.getObjVal? "alloc")
  let state ← IO.ofExcept (loadGenesisState alloc)
  IO.println s!"loaded {state.accounts.length} genesis accounts"
  let root := Evm.Frontier.stateRootBytes state
  let rootHex := bytesHex root
  IO.println s!"computed: 0x{rootHex}"
  IO.println s!"mainnet:  0x{mainnetGenesisStateRoot}"
  IO.println s!"match:    {rootHex == mainnetGenesisStateRoot}"

/-! ## Empty-block header replay -/

/-- `keccak256(rlp(emptyList)) = 0x1dcc4de8…`. A block whose
    `sha3_uncles` equals this carries zero uncles. -/
def emptyUnclesHash : String :=
  "1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"

structure HeaderInfo where
  number     : Nat
  miner      : Evm.Address
  stateRoot  : String  -- hex without 0x prefix
  txCount    : Nat
  unclesHash : String  -- hex without 0x prefix

private def parseHeader (j : Json) : Except String HeaderInfo := do
  let numStr     ← (← j.getObjVal? "number").getStr?
  let minerStr   ← (← j.getObjVal? "miner").getStr?
  let srStr      ← (← j.getObjVal? "state_root").getStr?
  let txStr      ← (← j.getObjVal? "transaction_count").getStr?
  let unclesStr  ← (← j.getObjVal? "sha3_uncles").getStr?
  return {
    number     := decToNat numStr
    miner      := Evm.Address.ofNat (hexToNat minerStr)
    stateRoot  := stripHex srStr
    txCount    := decToNat txStr
    unclesHash := stripHex unclesStr }

/-- Replay empty mainnet blocks (`transaction_count == 0` and uncles
    list empty). The only state change is the 5 ETH miner reward. Stops
    at the first block we can't verify this way, or after `maxBlocks`. -/
def replayHeaders (genesisPath headersPath : String) (maxBlocks : Nat) : IO Unit := do
  -- Load + verify genesis
  let contents ← IO.FS.readFile genesisPath
  let gJson ← IO.ofExcept (Lean.Json.parse contents)
  let alloc ← IO.ofExcept (gJson.getObjVal? "alloc")
  let mut state ← IO.ofExcept (loadGenesisState alloc)
  let preRoot := bytesHex (Evm.Frontier.stateRootBytes state)
  if preRoot ≠ mainnetGenesisStateRoot then
    IO.println s!"genesis state root mismatch: got 0x{preRoot}"
    return
  IO.println s!"block      0 (genesis):     ✓ ({state.accounts.length} accounts)"

  -- Stream the JSONL file. Reading the whole file into memory is fine
  -- here — even the largest is ~340 MB and we never need it twice.
  let raw ← IO.FS.readFile headersPath
  let mut nVerified : Nat := 0
  let mut nUnchecked : Nat := 0
  let mut stopped := false
  for line in raw.splitOn "\n" do
    if line.length = 0 then continue
    if stopped then continue
    if nVerified + nUnchecked ≥ maxBlocks then
      stopped := true
      continue
    match Lean.Json.parse line with
    | .error e =>
      IO.println s!"  parse-error: {e}"
      stopped := true
    | .ok header =>
      match parseHeader header with
      | .error e =>
        IO.println s!"  header parse error at line: {e}"
        stopped := true
      | .ok h =>
        if h.number = 0 then
          pure ()  -- already handled
        else if h.txCount ≠ 0 ∨ h.unclesHash ≠ emptyUnclesHash then
          let why :=
            if h.txCount ≠ 0 then s!"{h.txCount} txs"
            else "non-empty uncles"
          IO.println s!"block {h.number}: {why} — can't verify with header-only data, stopping"
          stopped := true
        else
          state := Evm.Frontier.Vm.Block.payRewards 0 state h.miner h.number []
          let computed := bytesHex (Evm.Frontier.stateRootBytes state)
          if computed = h.stateRoot then
            nVerified := nVerified + 1
            IO.println s!"block {h.number}: ✓ (state has {state.accounts.length} accounts)"
          else
            IO.println s!"block {h.number}: STATE ROOT MISMATCH"
            IO.println s!"  expected: 0x{h.stateRoot}"
            IO.println s!"  got:      0x{computed}"
            stopped := true
  IO.println "---"
  IO.println s!"verified {nVerified} empty blocks"

/-! ## Bring-up: replay blocks with transactions, verify each state root

    Drives `Evm.Frontier.processTransaction` directly (bypassing
    `Utils.recoverSender` and supplying the pre-recovered `from`
    address straight from ethereum-etl). After all txs in a block are
    processed, applies the canonical Frontier rewards from the spec
    (`Evm.Frontier.Vm.Block.payRewards` at Frontier) — uncle numbers are recovered from BigQuery reward values
    and supplied alongside coinbase as a synthetic ommers list.

    Goal: every behavior we apply traces back to a clause in
    `Evm/Frontier/Fork.lean`. When this driver diverges from mainnet
    on some block, the fix is to patch the spec, not the driver.
-/

structure BringupTx where
  fromAddr : Evm.Address
  toAddr   : Option Evm.Address
  value    : Evm.U256
  gas      : Evm.U256
  gasPrice : Evm.U256
  nonce    : Evm.U256
  data     : Evm.Bytes

structure BringupOmmer where
  number   : Nat
  coinbase : Evm.Address

structure BringupBlock where
  number     : Nat
  coinbase   : Evm.Address
  difficulty : Nat
  gasLimit   : Nat
  timestamp  : Nat
  stateRoot  : String  -- hex without 0x
  ommers     : List BringupOmmer
  txs        : List BringupTx

private def getNatField (j : Json) (k : String) : Except String Nat := do
  let v ← j.getObjVal? k
  match v with
  | .num n => .ok n.toFloat.toUInt64.toNat
  | .str s => .ok (decToNat s)
  | _      => .error s!"field {k} not a number"

private def getStrField (j : Json) (k : String) : Except String String := do
  let v ← j.getObjVal? k
  v.getStr?

private def parseHexU256 (s : String) : Evm.U256 :=
  Evm.U256.ofNat (hexToNat s)

private def parseDecU256 (s : String) : Evm.U256 :=
  Evm.U256.ofNat (decToNat s)

private def parseAddrStr (s : String) : Evm.Address :=
  Evm.Address.ofNat (hexToNat s)

private def parseBringupTx (j : Json) : Except String BringupTx := do
  let fromStr ← getStrField j "from"
  let toJson  ← j.getObjVal? "to"
  let toAddr  : Option Evm.Address := match toJson with
    | .null  => none
    | .str s => some (parseAddrStr s)
    | _      => none
  let valStr  ← getStrField j "value"
  let gas     ← getNatField j "gas"
  let gpStr   ← getStrField j "gas_price"
  let nonce   ← getNatField j "nonce"
  let inputStr ← getStrField j "input"
  return {
    fromAddr := parseAddrStr fromStr
    toAddr   := toAddr
    value    := parseDecU256 valStr
    gas      := Evm.U256.ofNat gas
    gasPrice := parseDecU256 gpStr
    nonce    := Evm.U256.ofNat nonce
    data     := hexToBytes inputStr
  }

private def parseBringupOmmer (j : Json) : Except String BringupOmmer := do
  let n   ← getNatField j "number"
  let cbS ← getStrField j "coinbase"
  return { number := n, coinbase := parseAddrStr cbS }

private def parseBringupBlock (j : Json) : Except String BringupBlock := do
  let n        ← getNatField j "number"
  let cbStr    ← getStrField j "coinbase"
  let diffStr  ← getStrField j "difficulty"
  let glim     ← getNatField j "gas_limit"
  let ts       ← getNatField j "timestamp"
  let srStr    ← getStrField j "state_root"
  let txsJ     ← j.getObjVal? "txs"
  let omJ      ← j.getObjVal? "uncles"
  let txsArr   ← txsJ.getArr?
  let omArr    ← omJ.getArr?
  let txs ← txsArr.toList.mapM parseBringupTx
  let ommers ← omArr.toList.mapM parseBringupOmmer
  return {
    number     := n
    coinbase   := parseAddrStr cbStr
    difficulty := decToNat diffStr
    gasLimit   := glim
    timestamp  := ts
    stateRoot  := stripHex srStr
    ommers     := ommers
    txs        := txs
  }

/-- Loop the per-tx state transition without going through
    `recoverSender`; we trust the pre-recovered `from` field from
    BigQuery. Mirrors `Evm.Frontier.processAll` line-for-line. -/
private partial def processAllWithSenders
    (state : Evm.Frontier.State)
    (blk   : BringupBlock)
    (txs   : List BringupTx)
    (gasAcc : Nat) :
    Except String (Evm.Frontier.State × Nat) :=
  match txs with
  | [] => .ok (state, gasAcc)
  | t :: rest => do
    let tx : Evm.Frontier.Transaction :=
      { nonce := t.nonce, gasPrice := t.gasPrice, gas := t.gas,
        to := t.toAddr, value := t.value, data := t.data,
        v := 0, r := 0, s := 0 }
    let r ← Evm.Frontier.processTransaction state ([] : List Evm.Hash32)
              blk.coinbase blk.number blk.difficulty blk.gasLimit blk.timestamp
              t.fromAddr tx
    processAllWithSenders r.state blk rest (gasAcc + r.gasUsed)

/-- Apply one bring-up block: txs first, then miner/uncle rewards per the
    Frontier spec formula (NOT from BigQuery reward values, so a spec
    bug shows up as a state-root mismatch). -/
def applyBringupBlock (state : Evm.Frontier.State) (blk : BringupBlock) :
    Except String Evm.Frontier.State := do
  let (state, _gasUsed) ← processAllWithSenders state blk blk.txs 0
  return Evm.Frontier.Vm.Block.payRewards 0 state blk.coinbase blk.number
    (blk.ommers.map fun om => (om.coinbase, om.number))

/-- Stream `jsonlPath`, applying each block on top of the genesis state
    loaded from `genesisPath`, verifying the state root after each block.
    Stops on first mismatch and reports it. -/
def replayBringup (genesisPath jsonlPath : String) (maxBlocks : Nat) : IO Unit := do
  -- Load + verify genesis
  let gContents ← IO.FS.readFile genesisPath
  let gJson ← IO.ofExcept (Lean.Json.parse gContents)
  let alloc ← IO.ofExcept (gJson.getObjVal? "alloc")
  let mut state ← IO.ofExcept (loadGenesisState alloc)
  let preRoot := bytesHex (Evm.Frontier.stateRootBytes state)
  if preRoot ≠ mainnetGenesisStateRoot then
    IO.println s!"genesis state root mismatch: got 0x{preRoot}"
    return
  IO.println s!"genesis: ✓ ({state.accounts.length} accounts)"

  let raw ← IO.FS.readFile jsonlPath
  let mut nProcessed : Nat := 0
  let mut nChecked   : Nat := 0
  let mut nMatched   : Nat := 0
  let mut stopped := false
  for line in raw.splitOn "\n" do
    if stopped then continue
    if line.length = 0 then continue
    if nProcessed ≥ maxBlocks then
      stopped := true
      continue
    match Lean.Json.parse line with
    | .error e =>
      IO.println s!"  json parse error: {e}"
      stopped := true
    | .ok j =>
      match parseBringupBlock j with
      | .error e =>
        IO.println s!"  block parse error: {e}"
        stopped := true
      | .ok blk =>
        match applyBringupBlock state blk with
        | .error e =>
          IO.println s!"block {blk.number}: APPLY ERROR: {e}"
          stopped := true
        | .ok newState =>
          state := newState
          nProcessed := nProcessed + 1
          -- Check root on every tx-bearing block, and every 1000th
          -- empty block (to keep the run survey-able without
          -- spending all our time in stateRootBytes).
          let hasTxs := !blk.txs.isEmpty
          let isCheckpoint := hasTxs ∨ blk.number % 1000 = 0
          if isCheckpoint then
            nChecked := nChecked + 1
            let got := bytesHex (Evm.Frontier.stateRootBytes state)
            if got = blk.stateRoot then
              nMatched := nMatched + 1
              if blk.number % 1000 = 0 then
                IO.println s!"block {blk.number}: ✓ (checked={nChecked} matched={nMatched})"
            else
              IO.println s!"block {blk.number}: STATE ROOT MISMATCH (txs={blk.txs.length})"
              IO.println s!"  expected: 0x{blk.stateRoot}"
              IO.println s!"  got:      0x{got}"
              stopped := true
  IO.println "---"
  IO.println s!"processed {nProcessed} blocks, checked {nChecked} roots, matched {nMatched}"

end Mainnet

def main (args : List String) : IO Unit := do
  match args with
  | ["genesis", path] => Mainnet.checkGenesis path
  | ["headers", g, h, n] =>
    Mainnet.replayHeaders g h (n.toNat?.getD 100)
  | ["bringup", g, j, n] =>
    Mainnet.replayBringup g j (n.toNat?.getD 1000)
  | _ =>
    IO.println "usage:"
    IO.println "  mainnet genesis <path-to-genesis.json>"
    IO.println "  mainnet headers <genesis.json> <blocks-NNN.json> <max-blocks>"
    IO.println "  mainnet bringup <genesis.json> <bringup.jsonl> <max-blocks>"
