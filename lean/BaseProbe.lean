/-
  BaseProbe — fetch a Base mainnet block and dump a summary.

  Usage:
      # default: probe the latest finalized block via $BASE_RPC_URL
      $ BASE_RPC_URL=http://127.0.0.1:8545 .lake/build/bin/baseProbe

      # probe a specific block number (hex or decimal)
      $ .lake/build/bin/baseProbe 0x2c86525
      $ .lake/build/bin/baseProbe 46654757

  Doesn't execute anything yet — just fetches + parses + summarises.
  Used while reth-op is syncing to verify the fetch+cache path and
  characterise live Base traffic.
-/

import Lean.Data.Json
import Evm.Optimism.Replay.Fetch
import Evm.Optimism.Replay.Parse
import Evm.Optimism.Forks

open Lean (Json)

/-- Decimal → hex helper, with the 0x prefix. -/
def decToHex (n : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- Parse a user-supplied block number (either hex `0x...` or decimal). -/
def parseBlockArg (arg : String) : String :=
  if arg.startsWith "0x" then arg
  else
    match arg.toNat? with
    | some n => decToHex n
    | none   => arg   -- pass through; RPC error will surface

/-- Hex digit → value (0..15), or none. -/
def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

/-- Hex → Nat (drop optional 0x prefix). Bad digits collapse to 0. -/
def hexToNat (hex : String) : Nat :=
  let s := if hex.startsWith "0x" then hex.drop 2 else hex
  s.foldl (init := 0) fun acc c => acc * 16 + (hexDigit? c).getD 0

/-- One-line summary of a tx. -/
def summariseTx (j : Json) : String :=
  let ty := (j.getObjValAs? String "type").toOption.getD "0x0"
  let to := (j.getObjValAs? String "to").toOption.getD "<create>"
  let from_ := (j.getObjValAs? String "from").toOption.getD "?"
  let value := (j.getObjValAs? String "value").toOption.getD "0x0"
  let gas   := (j.getObjValAs? String "gas").toOption.getD "0x0"
  let kind := match ty with
    | "0x0"  => "legacy"
    | "0x1"  => "accessList"
    | "0x2"  => "feeMarket"
    | "0x3"  => "blob"
    | "0x4"  => "setCode"
    | "0x7e" => "DEPOSITED"
    | _      => s!"type={ty}"
  s!"  [{kind}] {from_} → {to}  value={value}  gas={gas}"

def main (args : List String) : IO Unit := do
  let url ← Evm.Optimism.Replay.Fetch.rpcUrl
  IO.println s!"endpoint: {url}"
  let blockHex ← (
    match args with
    | []     => Evm.Optimism.Replay.Fetch.fetchBlockNumber
    | a :: _ => pure (parseBlockArg a) : IO String)
  IO.println s!"block:    {blockHex}  (= {hexToNat blockHex})"

  let block ← Evm.Optimism.Replay.Fetch.fetchBlock blockHex
  let result : Json ←
    match block.getObjVal? "result" with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"no `result` field: {e}"

  -- Header fields
  let hash      := (result.getObjValAs? String "hash").toOption.getD "?"
  let parent    := (result.getObjValAs? String "parentHash").toOption.getD "?"
  let stateRoot := (result.getObjValAs? String "stateRoot").toOption.getD "?"
  let timestamp := (result.getObjValAs? String "timestamp").toOption.getD "0x0"
  let coinbase  := (result.getObjValAs? String "miner").toOption.getD "?"
  let baseFee   := (result.getObjValAs? String "baseFeePerGas").toOption.getD "0x0"
  let gasUsed   := (result.getObjValAs? String "gasUsed").toOption.getD "0x0"
  let withdrawalsRoot := (result.getObjValAs? String "withdrawalsRoot").toOption
  let extraData := (result.getObjValAs? String "extraData").toOption.getD "0x"

  -- OP fork dispatch
  let ts := hexToNat timestamp
  let opFork := Evm.Optimism.OpFork.baseMainnetAt ts

  IO.println s!"hash:            {hash}"
  IO.println s!"parentHash:      {parent}"
  IO.println s!"stateRoot:       {stateRoot}"
  IO.println s!"coinbase:        {coinbase}"
  IO.println s!"baseFeePerGas:   {baseFee}"
  IO.println s!"gasUsed:         {gasUsed}"
  IO.println s!"timestamp:       {timestamp}  ({ts})"
  IO.println s!"extraData:       {extraData}"
  IO.println s!"withdrawalsRoot: {withdrawalsRoot}"
  IO.println s!"OP fork:         {repr opFork}"

  -- Tx list
  match result.getObjValAs? (Array Json) "transactions" with
  | .ok txs =>
    IO.println s!"\ntxs: {txs.size}"
    -- Tally by type.
    let mut byType : Std.HashMap String Nat := {}
    for tx in txs do
      let ty := (tx.getObjValAs? String "type").toOption.getD "0x0"
      byType := byType.insert ty ((byType.getD ty 0) + 1)
    IO.println "by type:"
    for (ty, n) in byType.toList do
      IO.println s!"  {ty} = {n}"
    IO.println ""
    -- First few txs (first one is always the L1Block prologue deposit).
    for tx in txs.toList.take 3 do
      IO.println (summariseTx tx)
    if txs.size > 3 then
      IO.println s!"  ... ({txs.size - 3} more)"
    -- Parse + display the deposited tx (sanity check that
    -- Evm.Optimism.Replay.Parse handles real Base JSON).
    IO.println ""
    let deposited := txs.toList.filter Evm.Optimism.Replay.Parse.isDeposited
    IO.println s!"deposited txs in block: {deposited.length}"
    for tx in deposited do
      match Evm.Optimism.Replay.Parse.parseDepositedTx tx with
      | .ok d =>
        let fromHex := String.ofList (Nat.toDigits 16 d.from_.toNat)
        let toHex   := match d.to with
                       | some a => "0x" ++ String.ofList (Nat.toDigits 16 a.toNat)
                       | none   => "<create>"
        IO.println s!"  parsed: from=0x{fromHex} to={toHex} mint={d.mint.toNat} value={d.value.toNat} gas={d.gas.toNat} system={d.isSystemTx} dataLen={d.data.size}"
        IO.println s!"  isL1Attributes: {d.isL1AttributesCall}"
      | .error e =>
        IO.println s!"  parse FAILED: {e}"

    -- Parse the header.
    IO.println ""
    match Evm.Optimism.Replay.Parse.parseHeader result with
    | .ok h =>
      IO.println s!"header parsed OK: number={h.number} extraData.size={h.extraData.size} bytes ({h.extraData.size * 2} hex chars)"
      IO.println s!"  withdrawalsRoot present: {h.withdrawalsRoot.isSome}"
      IO.println s!"  blobGasUsed present:     {h.blobGasUsed.isSome}"
    | .error e =>
      IO.println s!"header parse FAILED: {e}"
  | .error e =>
    IO.println s!"no `transactions` field: {e}"
