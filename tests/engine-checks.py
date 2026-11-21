#!/usr/bin/env python3
"""engine-checks.py — the Engine API's checks against a running `eita engine` (the edge,
rust/engine-api, and the engine thread behind it, src/engine/engine.lisp), on a fresh state of
a geth --dev chain this script drives as the consensus client.

  bin/eita engine --chain devnet --genesis GENESIS --state FRESH-DIR --jwt FILE --engine-listen 127.0.0.1:8553
  tests/engine-checks.py --geth http://127.0.0.1:8545 --engine http://127.0.0.1:8553 --jwt FILE [--blocks 20]

Needs geth's HTTP RPC with the debug API (debug_getRawTransaction) and foundry's `cast` (keccak).
Each check is a rule of ethereum/execution-apis src/engine/ (authentication, identification,
paris, shanghai, cancun, prague, osaka) for the methods the node implements; one line per check,
exit 1 if any fails. The node must be at genesis: the script replays blocks 1..N from geth,
then tests block N+1 in corrupted forms (each INVALID, the head unchanged) before the real one
(VALID: the verdict is per block), then a child of an INVALID block, then forkchoiceUpdated.
"""
import argparse, base64, hashlib, hmac, json, subprocess, sys, time, urllib.request, urllib.error

FAILS = []

def check(name, ok, detail=""):
    print(f"{'ok  ' if ok else 'FAIL'} {name}" + (f"  ({detail})" if detail and not ok else ""), flush=True)
    if not ok: FAILS.append(name)

def b64(b): return base64.urlsafe_b64encode(b).rstrip(b"=")

def jwt(secret, iat=None, alg="HS256", sign=True, claims=None):
    h = b64(json.dumps({"alg": alg, "typ": "JWT"}).encode())
    c = b64(json.dumps({"iat": int(time.time()) if iat is None else iat} if claims is None else claims).encode())
    s = b64(hmac.new(secret, h + b"." + c, hashlib.sha256).digest()) if sign else b""
    return (h + b"." + c + b"." + s).decode()

def post(url, body, auth=None, timeout=15):
    req = urllib.request.Request(url, json.dumps(body).encode(), {"Content-Type": "application/json"})
    if auth is not None: req.add_header("Authorization", auth)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r: return r.status, json.loads(r.read())
    except urllib.error.HTTPError as e: return e.code, None

class Node:
    def __init__(self, url, secret): self.url, self.secret = url, secret
    def call(self, method, params):
        st, out = post(self.url, {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}, "Bearer " + jwt(self.secret))
        assert st == 200, f"{method}: HTTP {st}"
        return out

def geth(url, method, params):
    return post(url, {"jsonrpc": "2.0", "id": 1, "method": method, "params": params})[1]["result"]

# --- a header as geth gives it, RLP-encoded and hashed (keccak: foundry's cast) ------------------
HEADER = ["parentHash", "sha3Uncles", "miner", "stateRoot", "transactionsRoot", "receiptsRoot", "logsBloom",
          "difficulty", "number", "gasLimit", "gasUsed", "timestamp", "extraData", "mixHash", "nonce",
          "baseFeePerGas", "withdrawalsRoot", "blobGasUsed", "excessBlobGas", "parentBeaconBlockRoot", "requestsHash"]
QUANT = {"difficulty", "number", "gasLimit", "gasUsed", "timestamp", "baseFeePerGas", "blobGasUsed", "excessBlobGas"}

def rlp(x):
    if isinstance(x, list):
        body = b"".join(rlp(i) for i in x)
        return (bytes([0xc0 + len(body)]) if len(body) < 56 else bytes([0xf7 + len(L := length(len(body)))]) + L) + body
    if len(x) == 1 and x[0] < 0x80: return x
    return (bytes([0x80 + len(x)]) if len(x) < 56 else bytes([0xb7 + len(L := length(len(x)))]) + L) + x

def length(n): return n.to_bytes((n.bit_length() + 7) // 8, "big")

def field_bytes(k, v):
    if k in QUANT: return length(int(v, 16))
    return bytes.fromhex(v[2:])

def keccak(b): return subprocess.run(["cast", "keccak", "0x" + b.hex()], capture_output=True, text=True, check=True).stdout.strip()

def block_hash(b): return keccak(rlp([field_bytes(k, b[k]) for k in HEADER if k in b]))

def payload_of(gurl, n):
    b = geth(gurl, "eth_getBlockByNumber", [hex(n), True])
    raws = [geth(gurl, "debug_getRawTransaction", [t["hash"]]) for t in b["transactions"]]
    vh = [h for t in b["transactions"] for h in (t.get("blobVersionedHashes") or [])]
    p = {"parentHash": b["parentHash"], "feeRecipient": b["miner"], "stateRoot": b["stateRoot"],
         "receiptsRoot": b["receiptsRoot"], "logsBloom": b["logsBloom"], "prevRandao": b["mixHash"],
         "blockNumber": b["number"], "gasLimit": b["gasLimit"], "gasUsed": b["gasUsed"], "timestamp": b["timestamp"],
         "extraData": b["extraData"], "baseFeePerGas": b["baseFeePerGas"], "blockHash": b["hash"],
         "transactions": raws, "withdrawals": b.get("withdrawals") or [],
         "blobGasUsed": b["blobGasUsed"], "excessBlobGas": b["excessBlobGas"]}
    return b, p, vh

def rehashed(b, p, **changes):
    """P with header fields changed (geth names) and blockHash recomputed: a well-formed
    payload whose content is wrong."""
    b2 = dict(b, **changes); p2 = dict(p)
    names = {"miner": "feeRecipient", "mixHash": "prevRandao", "number": "blockNumber"}
    for k, v in changes.items(): p2[names.get(k, k)] = v
    p2["blockHash"] = block_hash(b2)
    return b2, p2

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--geth", default="http://127.0.0.1:8545")
    ap.add_argument("--engine", default="http://127.0.0.1:8553")
    ap.add_argument("--jwt", required=True)
    ap.add_argument("--blocks", type=int, default=20)
    a = ap.parse_args()
    secret = bytes.fromhex(open(a.jwt).read().strip().removeprefix("0x"))
    node = Node(a.engine, secret)
    body = {"jsonrpc": "2.0", "id": 1, "method": "eth_chainId", "params": []}

    # --- authentication.md --------------------------------------------------------------
    check("jwt: valid token accepted", post(a.engine, body, "Bearer " + jwt(secret))[0] == 200)
    check("jwt: no Authorization refused", post(a.engine, body)[0] == 401)
    check("jwt: other secret refused", post(a.engine, body, "Bearer " + jwt(b"\x01" * 32))[0] == 401)
    check("jwt: alg none refused", post(a.engine, body, "Bearer " + jwt(secret, alg="none", sign=False))[0] == 401)
    check("jwt: alg HS512 refused", post(a.engine, body, "Bearer " + jwt(secret, alg="HS512"))[0] == 401)
    check("jwt: iat 61 s old refused", post(a.engine, body, "Bearer " + jwt(secret, int(time.time()) - 61))[0] == 401)
    check("jwt: iat 61 s ahead refused", post(a.engine, body, "Bearer " + jwt(secret, int(time.time()) + 61))[0] == 401)
    check("jwt: iat 55 s old accepted", post(a.engine, body, "Bearer " + jwt(secret, int(time.time()) - 55))[0] == 200)
    check("jwt: malformed token refused", post(a.engine, body, "Bearer abc.def")[0] == 401)
    check("jwt: not Bearer refused", post(a.engine, body, "Basic " + jwt(secret))[0] == 401)
    check("jwt: no iat refused", post(a.engine, body, "Bearer " + jwt(secret, claims={"id": "cl"}))[0] == 401)
    check("jwt: unknown claims ignored", post(a.engine, body, "Bearer " + jwt(secret, claims={"iat": int(time.time()), "id": "cl", "clv": "x"}))[0] == 200)

    # --- identification.md, common.md, the eth_ subset ------------------------------------
    caps = node.call("engine_exchangeCapabilities", [["engine_newPayloadV4", "engine_forkchoiceUpdatedV3", "engine_getPayloadV5"]])["result"]
    check("exchangeCapabilities: lists the implemented methods only, not itself (common.md)",
          sorted(caps) == sorted({"engine_getClientVersionV1", "engine_newPayloadV4", "engine_forkchoiceUpdatedV3"}), caps)
    v = node.call("engine_getClientVersionV1", [{"code": "XX", "name": "checks", "version": "0", "commit": "0x00000000"}])["result"]
    check("getClientVersionV1: one ClientVersionV1", isinstance(v, list) and len(v) >= 1
          and {"code", "name", "version", "commit"} <= set(v[0]) and len(v[0]["commit"]) == 10, v)
    check("eth_chainId = geth's", node.call("eth_chainId", [])["result"] == geth(a.geth, "eth_chainId", []))
    g0 = geth(a.geth, "eth_getBlockByNumber", ["0x0", False])
    e0 = node.call("eth_getBlockByNumber", ["0x0", False])["result"]
    check("genesis: block 0 from genesis.json = the chain's block 0 (hash)", e0 and e0["hash"] == g0["hash"], (e0 or {}).get("hash"))
    check("genesis: same state root", e0 and e0["stateRoot"] == g0["stateRoot"])
    head0 = int(node.call("eth_blockNumber", [])["result"], 16)
    check("the node starts at genesis", head0 == 0, head0)
    if head0 != 0: return 1
    check("unknown method: -32601", node.call("engine_getPayloadV5", ["0x0000000000000000"])["error"]["code"] == -32601)
    check("older version newPayloadV3: -32601 (not implemented)", node.call("engine_newPayloadV3", [{}, [], "0x" + "00" * 32])["error"]["code"] == -32601)
    st, out = post(a.engine, [body, dict(body, id=2, method="eth_blockNumber")], "Bearer " + jwt(secret))
    check("batch: answered in order", st == 200 and [r["id"] for r in out] == [1, 2])

    # --- replay 1..N as a CL would -----------------------------------------------------------
    lat = []
    for n in range(1, a.blocks + 1):
        b, p, vh = payload_of(a.geth, n)
        t0 = time.time()
        r = node.call("engine_newPayloadV4", [p, vh, b["parentBeaconBlockRoot"], []])["result"]
        lat.append((time.time() - t0) * 1000)
        if r["status"] != "VALID":
            check(f"block {n} VALID", False, r); return 1
        f = node.call("engine_forkchoiceUpdatedV3", [{"headBlockHash": b["hash"], "safeBlockHash": g0["hash"], "finalizedBlockHash": g0["hash"]}, None])["result"]
        if f["payloadStatus"]["status"] != "VALID":
            check(f"fcU {n} VALID", False, f); return 1
    check(f"blocks 1..{a.blocks} VALID (newPayload p50 {sorted(lat)[len(lat)//2]:.0f} ms, max {max(lat):.0f} ms)", True)

    N = a.blocks + 1
    b, p, vh = payload_of(a.geth, N)
    parent = b["parentHash"]; beacon = b["parentBeaconBlockRoot"]
    check("the test's header encoder reproduces geth's hash", block_hash(b) == b["hash"])
    np = lambda pp, vv=vh, bb=beacon, rr=[]: node.call("engine_newPayloadV4", [pp, vv, bb, rr])
    head = lambda: node.call("eth_blockNumber", [])["result"]

    # --- params (cancun.md 1, prague.md) ---------------------------------------------------------
    check("3 params: -32602", node.call("engine_newPayloadV4", [p, vh, beacon]).get("error", {}).get("code") == -32602)
    check("executionRequests null: -32602", np(p, rr=None).get("error", {}).get("code") == -32602)
    check("execution request of 1 byte: -32602", np(p, rr=["0x00"]).get("error", {}).get("code") == -32602)
    check("execution requests not ascending: -32602", np(p, rr=["0x0101", "0x0001"]).get("error", {}).get("code") == -32602)
    check("execution requests with a repeated type: -32602", np(p, rr=["0x0001", "0x0002"]).get("error", {}).get("code") == -32602)
    check("payload field missing: -32602", np({k: v for k, v in p.items() if k != "excessBlobGas"}).get("error", {}).get("code") == -32602)
    check("payload field null: -32602", np(dict(p, blobGasUsed=None)).get("error", {}).get("code") == -32602)
    check("payload field not of V3: -32602", np(dict(p, blockAccessList="0x")).get("error", {}).get("code") == -32602)

    # --- structural INVALID, lvh null (shanghai/cancun/prague.md) ----------------------------------
    def invalid(name, r, lvh):
        res = r.get("result") or {}
        check(name, res.get("status") == "INVALID" and res.get("latestValidHash") == lvh and head() == hex(N - 1),
              json.dumps(r)[:300])
    invalid("a zero-length transaction: INVALID, lvh null (paris.md 1)", np(dict(p, transactions=p["transactions"] + ["0x"])), None)
    invalid("blockHash not the header's: INVALID, lvh null", np(dict(p, gasUsed=hex(int(p["gasUsed"], 16) + 1))), None)
    invalid("blob versioned hashes not the txs': INVALID, lvh null", np(p, vh + ["0x01" + "ab" * 31]), None)
    invalid("execution requests not the header's commitment: INVALID, lvh null", np(p, rr=["0x00" + "11" * 192]), None)
    invalid("beacon root not the header's: INVALID, lvh null", np(p, bb="0x" + "11" * 32), None)
    # --- executed INVALID, lvh = parent; each rolled back ----------------------------------------
    _, bad_root = rehashed(b, p, stateRoot="0x" + "22" * 32)
    invalid("wrong stateRoot (rehashed): executed, root mismatch: INVALID, lvh parent", np(bad_root), parent)
    _, bad_rcpt = rehashed(b, p, receiptsRoot="0x" + "33" * 32)
    invalid("wrong receiptsRoot (rehashed): the verifier refuses: INVALID, lvh parent", np(bad_rcpt), parent)
    _, bad_gas = rehashed(b, p, gasUsed=hex(int(b["gasUsed"], 16) + 1))
    invalid("wrong gasUsed (rehashed): INVALID, lvh parent", np(bad_gas), parent)
    _, bad_ts = rehashed(b, p, timestamp=geth(a.geth, "eth_getBlockByNumber", [hex(N - 1), False])["timestamp"])
    invalid("timestamp = parent's (rehashed): the header gate refuses: INVALID, lvh parent", np(bad_ts), parent)
    _, bad_base = rehashed(b, p, baseFeePerGas=hex(int(b["baseFeePerGas"], 16) + 1))
    invalid("wrong base fee (rehashed): INVALID, lvh parent", np(bad_base), parent)
    invalid("the same INVALID payload again: the recorded verdict", np(bad_root), parent)
    # --- non-sticky: the real block now ------------------------------------------------------------
    t0 = time.time(); r = np(p)["result"]
    check(f"the real block {N} after five INVALID ones: VALID ({(time.time() - t0) * 1000:.0f} ms)",
          r["status"] == "VALID" and r["latestValidHash"] == b["hash"] and head() == hex(N), r)
    check("the same VALID payload again: VALID", np(p)["result"]["status"] == "VALID")
    # --- a child of an INVALID block (paris.md: invalid ancestry) ----------------------------------
    b2, p2, vh2 = payload_of(a.geth, N + 1)
    _, child = rehashed(b2, p2, parentHash=bad_root["blockHash"])
    r = node.call("engine_newPayloadV4", [child, vh2, b2["parentBeaconBlockRoot"], []])["result"]
    check("a child of an INVALID block: INVALID, lvh = the parent's lvh", r["status"] == "INVALID" and r["latestValidHash"] == parent, r)
    # --- unknown parent: SYNCING, stored; it runs once its parent is VALID ------------------------
    b3, p3, vh3 = payload_of(a.geth, N + 2)
    r = node.call("engine_newPayloadV4", [p3, vh3, b3["parentBeaconBlockRoot"], []])["result"]
    check("parent unknown: SYNCING, lvh null", r["status"] == "SYNCING" and r["latestValidHash"] is None, r)
    r = node.call("engine_newPayloadV4", [p2, vh2, b2["parentBeaconBlockRoot"], []])["result"]
    check("its parent arrives: VALID, and the stored child runs", r["status"] == "VALID" and head() == hex(N + 2), (r, head()))

    # --- forkchoiceUpdatedV3 (paris.md, cancun.md) -------------------------------------------------
    fc = lambda h, s, f, attrs=None: node.call("engine_forkchoiceUpdatedV3", [{"headBlockHash": h, "safeBlockHash": s, "finalizedBlockHash": f}, attrs])
    r = fc(b3["hash"], b["hash"], b["hash"])["result"]
    check("fcU to the head: VALID, payloadId null", r["payloadStatus"]["status"] == "VALID" and r["payloadId"] is None, r)
    check("eth_getBlockByNumber(finalized) = the finalized block", node.call("eth_getBlockByNumber", ["finalized", False])["result"]["hash"] == b["hash"])
    check("eth_getBlockByHash", node.call("eth_getBlockByHash", [b2["hash"], False])["result"]["number"] == b2["number"])
    r = fc(b3["hash"], b["hash"], "0x" + "44" * 32)
    check("fcU finalized not on the chain: -38002", r.get("error", {}).get("code") == -38002, r)
    r = fc("0x" + "55" * 32, g0["hash"], g0["hash"])["result"]
    check("fcU to an unknown head: SYNCING", r["payloadStatus"]["status"] == "SYNCING", r)
    r = fc(bad_root["blockHash"], g0["hash"], g0["hash"])["result"]
    check("fcU to an INVALID head: INVALID", r["payloadStatus"]["status"] == "INVALID", r)
    attrs = {"timestamp": hex(int(b3["timestamp"], 16) + 12), "prevRandao": "0x" + "00" * 32,
             "suggestedFeeRecipient": "0x" + "00" * 20, "withdrawals": [], "parentBeaconBlockRoot": "0x" + "00" * 32}
    r = fc(b3["hash"], b["hash"], b["hash"], attrs)
    check("fcU with payload attributes (validate-only node): -38003", r.get("error", {}).get("code") == -38003, r)
    check("fcU malformed state: -32602", node.call("engine_forkchoiceUpdatedV3", [{"headBlockHash": b3["hash"]}, None]).get("error", {}).get("code") == -32602)

    print(f"{'PASS' if not FAILS else 'FAIL'}: {len(FAILS)} failed", flush=True)
    return 1 if FAILS else 0

if __name__ == "__main__":
    sys.exit(main())
