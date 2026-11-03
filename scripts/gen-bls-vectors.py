#!/usr/bin/env python3
"""gen-bls-vectors.py — build an EIP-2537 conformance oracle from the chain itself.

The BLS12-381 precompiles (0x0b..0x11) are not in our implementation yet, and the
local `ethereum/tests` checkout predates Prague, so there are no vectors to build
against. The chain IS a reference implementation: `eth_call` to a precompile
address returns exactly what the canonical client computes, and a failing input
comes back as an error. So we ask it.

Seed points are real: they come from `lean/c/testdata/bls12381-vectors.json`,
captured from the execution of Arc block 21 142 242 tx 34 (two MAP_FP_TO_G1
outputs, a G1ADD, and a 2-pair PAIRING_CHECK whose input carries two valid G2
points). Everything else is derived from those, so every "valid" case is a point
that genuinely lies in the right subgroup.

Usage: gen-bls-vectors.py <rpc-url> [-o lean/c/testdata/bls12381-vectors.json]
The file is rewritten with the seed vectors plus the generated ones.
"""
import argparse, json, os, ssl, sys, urllib.request
import certifi

P = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

ap = argparse.ArgumentParser()
ap.add_argument("rpc")
ap.add_argument("-o", "--out", default=os.path.join(os.path.dirname(__file__), "..", "lean", "c", "testdata", "bls12381-vectors.json"))
a = ap.parse_args()
ctx = ssl.create_default_context(cafile=certifi.where())


def rpc(method, params):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    req = urllib.request.Request(a.rpc, body, {"content-type": "application/json"})
    return json.load(urllib.request.urlopen(req, timeout=120, context=ctx))


def call(addr, data_hex):
    """eth_call a precompile. Returns (output_hex, error_message).
    `to` must be a full 20-byte address — "0x0b" is rejected at the JSON-RPC layer
    as Invalid params, which looks exactly like a precompile rejecting the input."""
    full = "0x" + format(int(addr, 16), "040x")
    r = rpc("eth_call", [{"to": full, "data": data_hex, "gas": hex(20_000_000)}, "latest"])
    if "error" in r:
        return None, r["error"].get("message", "error")
    return r["result"], None


def h(b):  # bytes -> 0x hex
    return "0x" + b.hex()


def ub(s):  # 0x hex -> bytes
    return bytes.fromhex(s[2:] if s.startswith("0x") else s)


def fp(x):  # integer -> EIP-2537 64-byte field element (16 zero bytes || 48 BE)
    return b"\x00" * 16 + x.to_bytes(48, "big")


seed_path = a.out
seed = json.load(open(seed_path))
# idempotent: the trace-captured seeds are the ones carrying gas_used; drop any
# previously generated rows so a re-run regenerates them instead of appending.
seed["vectors"] = [v for v in seed["vectors"] if "gas_used" in v]
seeds = {v["op"]: v for v in seed["vectors"]}

G1_A = ub(seeds["MAP_FP_TO_G1"]["output"])                     # 128 B, in subgroup
G1_SUM = ub(seeds["G1ADD"]["output"])                          # 128 B
PAIR_IN = ub(seeds["PAIRING_CHECK"]["input"])                  # 2 x (128 G1 + 256 G2)
G2_A = PAIR_IN[128:384]                                        # 256 B, in subgroup
G2_B = PAIR_IN[512:768]
G1_INF = b"\x00" * 128
G2_INF = b"\x00" * 256
SC_1 = (1).to_bytes(32, "big")
SC_2 = (2).to_bytes(32, "big")

cases = [
    # --- the three operations the seed transaction never exercised -------------
    ("G1MSM", "0x0c", G1_A + SC_1, "one pair, scalar 1 (identity on a subgroup point)"),
    ("G1MSM", "0x0c", G1_A + SC_2 + G1_SUM + SC_1, "two pairs"),
    ("G2ADD", "0x0d", G2_A + G2_B, "two subgroup points"),
    ("G2ADD", "0x0d", G2_A + G2_INF, "point plus infinity"),
    ("G2MSM", "0x0e", G2_A + SC_1, "one pair, scalar 1"),
    ("G2MSM", "0x0e", G2_A + SC_2 + G2_B + SC_1, "two pairs"),
    ("MAP_FP2_TO_G2", "0x11", fp(0) + fp(0), "map of zero"),
    ("MAP_FP2_TO_G2", "0x11", fp(1) + fp(2), "map of (1, 2)"),
    ("MAP_FP_TO_G1", "0x10", fp(0), "map of zero"),
    ("MAP_FP_TO_G1", "0x10", fp(P - 1), "map of p-1, the largest valid element"),
    # --- identities and infinity ---------------------------------------------
    ("G1ADD", "0x0b", G1_INF + G1_INF, "infinity plus infinity"),
    ("G1ADD", "0x0b", G1_A + G1_INF, "point plus infinity"),
    ("PAIRING_CHECK", "0x0f", b"", "empty input is the empty product, which is 1"),
    ("PAIRING_CHECK", "0x0f", G1_INF + G2_A, "infinity pairs to 1"),
    ("G1MSM", "0x0c", G1_A + (0).to_bytes(32, "big"), "scalar zero"),
    # --- invalid encodings: every one of these must FAIL ----------------------
    ("G1ADD", "0x0b", G1_A, "input half the required length"),
    ("G1ADD", "0x0b", G1_A + G1_A + b"\x00", "one byte too long"),
    ("G1ADD", "0x0b", bytes(16 * [1]) + G1_A[16:] + G1_A, "non-zero top padding byte"),
    ("G1ADD", "0x0b", fp(P) + G1_A[64:] + G1_A, "x coordinate equal to p"),
    ("G1ADD", "0x0b", fp(1) + fp(1) + G1_A, "point not on the curve"),
    ("MAP_FP_TO_G1", "0x10", fp(P), "field element equal to p"),
    ("MAP_FP_TO_G1", "0x10", fp(1)[:63], "input one byte short"),
    ("G1MSM", "0x0c", b"", "empty input is invalid for MSM"),
    ("G1MSM", "0x0c", G1_A + SC_1[:31], "trailing partial pair"),
    ("G1MSM", "0x0c", fp(1) + fp(1) + SC_1, "point not on the curve"),
    ("PAIRING_CHECK", "0x0f", G1_A + G2_A[:255], "input not a multiple of 384"),
    ("G2ADD", "0x0d", G2_A, "input half the required length"),
    ("MAP_FP2_TO_G2", "0x11", fp(1), "input half the required length"),
]

out = list(seed["vectors"])
for v in out:
    v.setdefault("note", "captured from the chain's own execution of the seed tx")
    v.setdefault("expect", "ok")

ok = bad = 0
for op, addr, data, note in cases:
    res, err = call(addr, h(data))
    rec = {"op": op, "addr": addr, "input": h(data), "note": note}
    if err is None:
        rec["output"] = res
        rec["expect"] = "ok"
        ok += 1
    else:
        rec["output"] = None
        rec["expect"] = "fail"
        rec["chain_error"] = err
        bad += 1
    out.append(rec)
    print(f"{op:14s} {len(data):4d}B  {'OK  ' + str((len(res) - 2) // 2) + 'B' if err is None else 'FAIL: ' + err[:60]}   ({note})")

seed["vectors"] = out
seed["note"] = ("inputs with CANONICAL outputs: the first four captured from the chain's own "
                "execution of the seed tx, the rest answered by eth_call against the same chain. "
                "`expect` is ok|fail; a fail case must make our precompile fail (consuming all gas).")
json.dump(seed, open(a.out, "w"), indent=1)
print(f"\nwrote {a.out}: {len(out)} vectors ({ok} new ok, {bad} new fail)")
