/-
  Evm.Optimism.Replay.Fetch — Base-mainnet block fetcher with
  on-disk cache.

  Hits an RPC endpoint (default `http://127.0.0.1:8545` so a local
  reth-op node Just Works, override via `$BASE_RPC_URL` env var)
  and caches each response under `external/base-cache/<key>.json`.
  Subsequent calls for the same key read from disk; the network is
  only touched once.

  Shells out to `curl` rather than linking a Lean HTTP client. The
  one-shot, low-frequency use case doesn't justify a native dep.
-/

import Lean.Data.Json

namespace Evm.Optimism.Replay.Fetch

open Lean (Json)

/-- Cache directory under the Lean project. Created on first use. -/
def cacheDir : System.FilePath := "external/base-cache"

/-- Default RPC endpoint — assumes the user is running reth-op
    locally with `--http`. Override via `$BASE_RPC_URL` for any
    other endpoint (Alchemy, QuickNode, mainnet.base.org for
    capability-limited probing). -/
def defaultRpc : String := "http://127.0.0.1:8545"

/-- Resolve the RPC endpoint from env or fallback to default. -/
def rpcUrl : IO String := do
  match (← IO.getEnv "BASE_RPC_URL") with
  | some u => return u
  | none   => return defaultRpc

/-- Ensure the cache directory exists. Idempotent. -/
def ensureCacheDir : IO Unit := do
  IO.FS.createDirAll cacheDir

/-- POST a JSON-RPC payload to the configured endpoint and return
    the response body as a string. Shells out to `curl`. -/
def rpcRequest (payload : String) : IO String := do
  let url ← rpcUrl
  let out ← IO.Process.output {
    cmd := "curl"
    args := #[
      "-sS",                       -- silent, show errors
      "-X", "POST",
      "-H", "Content-Type: application/json",
      "--data", payload,
      url
    ]
  }
  if out.exitCode ≠ 0 then
    throw <| IO.userError s!"curl failed (exit {out.exitCode}): {out.stderr}"
  return out.stdout

/-- A cache key for one request — typically the method + a salient
    parameter (block number, etc.). Used as the on-disk filename. -/
def cachePath (key : String) : System.FilePath :=
  cacheDir / (key ++ ".json")

/-- Read a cached response, or `none` if absent. -/
def readCache (key : String) : IO (Option String) := do
  let path := cachePath key
  if (← path.pathExists) then
    let s ← IO.FS.readFile path
    return some s
  else
    return none

/-- Write a response to cache. Caller-supplied key. -/
def writeCache (key : String) (body : String) : IO Unit := do
  ensureCacheDir
  IO.FS.writeFile (cachePath key) body

/-- Cached request: check cache, else fetch + write + return. -/
def cachedRpc (key : String) (payload : String) : IO String := do
  match (← readCache key) with
  | some s => return s
  | none =>
    let s ← rpcRequest payload
    writeCache key s
    return s

/-! ## High-level helpers -/

/-- Fetch the chain head via `eth_blockNumber`. NOT cached — head
    advances every second. -/
def fetchBlockNumber : IO String := do
  let body ← rpcRequest "{\"jsonrpc\":\"2.0\",\"method\":\"eth_blockNumber\",\"params\":[],\"id\":1}"
  match Json.parse body with
  | .ok j =>
    match j.getObjValAs? String "result" with
    | .ok hex => return hex
    | .error e => throw <| IO.userError s!"bad eth_blockNumber response: {e}"
  | .error e => throw <| IO.userError s!"bad JSON: {e}"

/-- Fetch a block by hex number (with full tx bodies). Cached by
    block number. -/
def fetchBlock (blockNumberHex : String) : IO Json := do
  let payload :=
    "{\"jsonrpc\":\"2.0\",\"method\":\"eth_getBlockByNumber\",\"params\":[\""
      ++ blockNumberHex ++ "\",true],\"id\":1}"
  let key := s!"block_{blockNumberHex.replace "0x" ""}"
  let body ← cachedRpc key payload
  match Json.parse body with
  | .ok j => return j
  | .error e => throw <| IO.userError s!"bad block JSON: {e}"

/-- Fetch a block's hash (and only its hash) via the lightweight
    `eth_getBlockByNumber(false)` form (full=false strips out tx
    bodies — 100x smaller payload than `fetchBlock`). Used to
    populate `env.blockHashes` for BLOCKHASH opcode lookups. -/
def fetchBlockHash (blockNumberHex : String) : IO String := do
  let payload :=
    "{\"jsonrpc\":\"2.0\",\"method\":\"eth_getBlockByNumber\",\"params\":[\""
      ++ blockNumberHex ++ "\",false],\"id\":1}"
  let key := s!"hdr_{blockNumberHex.replace "0x" ""}"
  let body ← cachedRpc key payload
  match Json.parse body with
  | .ok j =>
    match j.getObjVal? "result" with
    | .ok res =>
      match res.getObjValAs? String "hash" with
      | .ok h => return h
      | .error _ => return "0x0000000000000000000000000000000000000000000000000000000000000000"
    | _ => return "0x0000000000000000000000000000000000000000000000000000000000000000"
  | _ => return "0x0000000000000000000000000000000000000000000000000000000000000000"

/-- Fetch the block's prestate via `debug_traceBlockByNumber`. Will
    fail on RPC endpoints that don't expose `debug_*` (e.g. the
    public mainnet.base.org). Requires reth-op or an archive-node
    plan from Alchemy / QuickNode. Cached by block number. -/
def fetchPrestate (blockNumberHex : String) : IO Json := do
  let payload :=
    "{\"jsonrpc\":\"2.0\",\"method\":\"debug_traceBlockByNumber\",\"params\":[\""
      ++ blockNumberHex
      ++ "\",{\"tracer\":\"prestateTracer\"}],\"id\":1}"
  let key := s!"prestate_{blockNumberHex.replace "0x" ""}"
  let body ← cachedRpc key payload
  match Json.parse body with
  | .ok j => return j
  | .error e => throw <| IO.userError s!"bad prestate JSON: {e}"

/-- Fetch an account's nonce + code at a given block. Used to
    fill in EIP-7702 authority accounts that the prestate-tracer
    doesn't include (because the EVM never reads them directly). -/
def fetchNonce (addrHex blockHex : String) : IO Nat := do
  let payload :=
    "{\"jsonrpc\":\"2.0\",\"method\":\"eth_getTransactionCount\",\"params\":[\""
      ++ addrHex ++ "\",\"" ++ blockHex ++ "\"],\"id\":1}"
  let key := s!"nonce_{blockHex.replace "0x" ""}_{addrHex.replace "0x" ""}"
  let body ← cachedRpc key payload
  match Json.parse body with
  | .ok j =>
    match j.getObjValAs? String "result" with
    | .ok hex =>
      let s := hex.replace "0x" ""
      return s.foldl (init := 0) fun acc c =>
        let d := if c.isDigit then c.toNat - '0'.toNat
                 else if 'a' ≤ c ∧ c ≤ 'f' then 10 + c.toNat - 'a'.toNat
                 else if 'A' ≤ c ∧ c ≤ 'F' then 10 + c.toNat - 'A'.toNat
                 else 0
        acc * 16 + d
    | _ => return 0
  | _ => return 0

/-- Fetch an account's code at a given block. Same use case as
    `fetchNonce`. Returns empty bytes on failure or absent code. -/
def fetchCode (addrHex blockHex : String) : IO ByteArray := do
  let payload :=
    "{\"jsonrpc\":\"2.0\",\"method\":\"eth_getCode\",\"params\":[\""
      ++ addrHex ++ "\",\"" ++ blockHex ++ "\"],\"id\":1}"
  let key := s!"code_{blockHex.replace "0x" ""}_{addrHex.replace "0x" ""}"
  let body ← cachedRpc key payload
  match Json.parse body with
  | .ok j =>
    match j.getObjValAs? String "result" with
    | .ok hex =>
      let s := (hex.replace "0x" "").replace "0X" ""
      let chars := s.toList
      let hd (c : Char) : Nat :=
        if c.isDigit then c.toNat - '0'.toNat
        else if 'a' ≤ c ∧ c ≤ 'f' then 10 + c.toNat - 'a'.toNat
        else if 'A' ≤ c ∧ c ≤ 'F' then 10 + c.toNat - 'A'.toNat
        else 0
      let rec go : List Char → ByteArray → ByteArray
        | a :: b :: tl, acc => go tl (acc.push (UInt8.ofNat (hd a * 16 + hd b)))
        | _, acc => acc
      return go chars ByteArray.empty
    | _ => return ByteArray.empty
  | _ => return ByteArray.empty

/-- Fetch the receipts for a block. Each receipt carries op-geth's
    own view of `l1Fee` per tx, which we plumb into the user-tx
    processor to sidestep re-deriving the formula (used to close
    the L1-data-fee gap end-to-end first; a cross-check against
    the in-tree formula in `Replay.l1FeeWei` is a follow-up). -/
def fetchReceipts (blockNumberHex : String) : IO Json := do
  let payload :=
    "{\"jsonrpc\":\"2.0\",\"method\":\"eth_getBlockReceipts\",\"params\":[\""
      ++ blockNumberHex ++ "\"],\"id\":1}"
  let key := s!"receipts_{blockNumberHex.replace "0x" ""}"
  let body ← cachedRpc key payload
  match Json.parse body with
  | .ok j => return j
  | .error e => throw <| IO.userError s!"bad receipts JSON: {e}"

/-- Fetch the block's state-diff via the prestate tracer's
    `diffMode`. Returns per-tx `{pre, post}` objects — `pre` is the
    accounts/slots that changed, with their VALUES BEFORE THE TX;
    `post` is the same keys with values AFTER. Used for per-account
    correctness checks (vs. a full state-root match, which would
    require the gigabyte-scale full world state). -/
def fetchStateDiff (blockNumberHex : String) : IO Json := do
  let payload :=
    "{\"jsonrpc\":\"2.0\",\"method\":\"debug_traceBlockByNumber\",\"params\":[\""
      ++ blockNumberHex
      ++ "\",{\"tracer\":\"prestateTracer\",\"tracerConfig\":{\"diffMode\":true}}],\"id\":1}"
  let key := s!"diff_{blockNumberHex.replace "0x" ""}"
  let body ← cachedRpc key payload
  match Json.parse body with
  | .ok j => return j
  | .error e => throw <| IO.userError s!"bad diff JSON: {e}"

end Evm.Optimism.Replay.Fetch
