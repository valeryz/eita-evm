#!/usr/bin/env python3
"""gen-bls-gas-table.py — measure the canonical EIP-2537 gas schedule from the chain.

The MSM costs depend on a 128-entry discount table. Reciting that table from
memory is exactly how a silent gas bug gets written, so we measure it instead:
`debug_traceCall` to a precompile address reports the frame's `gasUsed`, which IS
the precompile's gas. Points come from the oracle in
`lean/c/testdata/bls12381-vectors.json` (real subgroup elements captured from the
chain), repeated k times — MSM accepts repeated points.

Output: `lean/c/testdata/bls12381-gas.json`, plus the Lean-shaped discount lists
on stdout for pasting into Evm.CL.GasEmit.

Usage: gen-bls-gas-table.py <rpc-url> [--kmax 130]
"""
import argparse, json, os, ssl, urllib.request
import certifi

ap = argparse.ArgumentParser()
ap.add_argument("rpc")
ap.add_argument("--kmax", type=int, default=130)
ap.add_argument("-o", "--out", default=os.path.join(os.path.dirname(__file__), "..", "lean", "c", "testdata", "bls12381-gas.json"))
a = ap.parse_args()
ctx = ssl.create_default_context(cafile=certifi.where())


def rpc(method, params):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    req = urllib.request.Request(a.rpc, body, {"content-type": "application/json"})
    return json.load(urllib.request.urlopen(req, timeout=120, context=ctx))


# A probe contract, so we read the PRECOMPILE's frame and never the transaction's.
# Subtracting the tx intrinsic from a top-level call works but dies on the cheap
# operations, where the EIP-7623 calldata floor swallows the execution gas (G1ADD
# costs 375 against ~24k of calldata). Instead, deploy this by state override and
# read the inner frame's gasUsed, which is exactly the precompile cost:
#
#   CALLDATASIZE PUSH0 PUSH0 CALLDATACOPY        copy the input to memory
#   PUSH2 0x1000 PUSH0 CALLDATASIZE PUSH0        retSize retOff argsSize argsOff
#   PUSH1 <addr> GAS STATICCALL STOP             to gas, then call
PROBE = "0xdeadbeef00000000000000000000000000000001"


def probe_code(addr):
    return "0x" + "365f5f37" + "611000" + "5f" + "36" + "5f" + "60" + format(int(addr, 16), "02x") + "5afa00"


def gas_of(addr, data):
    """Canonical gas of ONE precompile call, read off the inner frame."""
    r = rpc("debug_traceCall", [{"to": PROBE, "data": "0x" + data.hex(), "gas": hex(500_000_000)},
                                "latest",
                                {"tracer": "callTracer",
                                 "stateOverrides": {PROBE: {"code": probe_code(addr)}}}])
    if "error" in r:
        return None, r["error"].get("message", "error")
    res = r["result"]
    inner = res.get("calls") or []
    if not inner:
        return None, "no inner frame (probe did not call)" + (": " + res["error"] if res.get("error") else "")
    f = inner[0]
    if f.get("error"):
        return None, f["error"]
    return int(f.get("gasUsed", "0x0"), 16), None


def recover_discount(gas, k, base):
    """The chain computes gas = (k * base * d) // 1000, so d is not gas*1000/(k*base).
    Return the integer d consistent with the floor, or None if ambiguous."""
    kb = k * base
    lo = -(-gas * 1000 // kb)                      # ceil(gas*1000/kb)
    cands = [d for d in range(max(1, lo - 2), lo + 3) if (kb * d) // 1000 == gas]
    return cands[0] if len(cands) == 1 else (cands if cands else None)


def ub(s):
    return bytes.fromhex(s[2:] if s.startswith("0x") else s)


vec = json.load(open(os.path.join(os.path.dirname(a.out), "bls12381-vectors.json")))["vectors"]
by = {}
for v in vec:
    by.setdefault(v["op"], []).append(v)
G1 = ub(by["MAP_FP_TO_G1"][0]["output"])                 # 128 B subgroup point
PAIR = ub(by["PAIRING_CHECK"][0]["input"])               # 2 x (G1 128 + G2 256)
G2 = PAIR[128:384]                                       # 256 B subgroup point
SC = (3).to_bytes(32, "big")

out = {"source": "debug_traceCall against the chain; gasUsed of the precompile frame",
       "fixed": {}, "msm": {"g1": {}, "g2": {}}, "pairing": {}}

print("-- fixed-cost operations")
for op, addr, data in [("G1ADD", "0x0b", G1 + G1),
                       ("G2ADD", "0x0d", G2 + G2),
                       ("MAP_FP_TO_G1", "0x10", G1[:64]),
                       ("MAP_FP2_TO_G2", "0x11", G2[:128])]:
    g, err = gas_of(addr, data)
    out["fixed"][op] = g
    print(f"  {op:14s} {g if g is not None else 'FAIL ' + str(err)}")

print("-- pairing, k = 1..4  (expect a + b*k)")
for k in range(1, 5):
    g, err = gas_of("0x0f", PAIR[:384] * k)
    out["pairing"][k] = g
    print(f"  k={k:3d}  {g if g is not None else 'FAIL ' + str(err)}")
ks = sorted(int(k) for k, v in out["pairing"].items() if v)
if len(ks) >= 2:
    per = out["pairing"][ks[1]] - out["pairing"][ks[0]]
    base = out["pairing"][ks[0]] - per * ks[0]
    print(f"  => pairing gas = {base} + {per}*k")
    out["pairing_formula"] = {"base": base, "per_pair": per}

for fam, addr, pt, sz in [("g1", "0x0c", G1, 160), ("g2", "0x0e", G2, 288)]:
    print(f"-- {fam.upper()}MSM, k = 1..{a.kmax}")
    for k in range(1, a.kmax + 1):
        g, err = gas_of(addr, (pt + SC) * k)
        out["msm"][fam][k] = g
        if g is None:
            print(f"  k={k:3d}  FAIL {err}")
            break
    one = out["msm"][fam].get(1)
    if one:
        print(f"  base (k=1, discount 1000) = {one}")
        disc = {}
        for k, g in sorted(out["msm"][fam].items()):
            if g is None: continue
            d = recover_discount(g, k, one)
            if not isinstance(d, int):
                print(f"  !! k={k}: gas {g} gives no unique discount (candidates {d})")
                continue
            disc[k] = d
        out["msm"][fam + "_discount"] = disc
        vals = [disc[k] for k in sorted(disc)]
        print(f"  discounts: {vals[:8]} … {vals[-4:]}")
        print(f"  Lean list ({len(vals)} entries):")
        for i in range(0, len(vals), 16):
            print("    " + ", ".join(str(x) for x in vals[i:i + 16]) + ",")

json.dump(out, open(a.out, "w"), indent=1)
print(f"\nwrote {a.out}")
