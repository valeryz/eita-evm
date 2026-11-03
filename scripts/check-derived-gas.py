#!/usr/bin/env python3
"""check-derived-gas.py — no gas schedule in hand-written replay code.

Gas formulas and constants come from Lean (Evm.CL.GasEmit / HostEmit, emitted to
src/generated/host.lisp by `lake exe emitHostCL`). The CL around them is a SEAM: it
reads inputs (byte counts, warmth, fork) and calls a `spec-*` function. A gas-schedule
number written straight into that code is a second, unproved copy of the schedule; the
EIP-7623 floor and the refund cap lived that way in evm/run-tx.lisp (now src/evm/run-tx.lisp) until 2026-10-20.

This scans the hand-written runtime Lisp with comments and string literals stripped, and
fails on any of the distinctive EVM gas-schedule constants below unless the line is
listed in scripts/derived-gas-allow.txt with a reason. Run by scripts/verify-host-emit.sh.

  check-derived-gas.py [--list]     --list prints every hit, allowed or not
"""
import glob, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# Distinctive schedule values (base, create, new account, refunds, cold/warm access,
# access lists, stipend, call value, SSTORE set/reset, 7702 auth). Small ones (3, 100,
# 200, …) are too common in ordinary code to police this way.
SCHEDULE = [21000, 32000, 25000, 24000, 22100, 20000, 15000, 12500, 9000, 4800, 2900,
            2600, 2400, 2300, 2100, 1900]
NUM = re.compile(r"(?<![\w.#-])(%s)(?![\w.])" % "|".join(map(str, SCHEDULE)))
# The hand-written execution path: the EVM host and its native/core/state underpinnings, block
# input, the block pipeline and the chains (src/generated/ is Lean's; the snapshot, trie and
# fixture code compute no gas).
FILES = sorted(os.path.relpath(p, ROOT) for d in ("native", "core", "evm", "input", "chains")
               for p in glob.glob(os.path.join(ROOT, "src", d, "*.lisp"))) + ["src/state/world.lisp"]


def code_only(text):
    """The text with ; comments, #| |# blocks and "strings" blanked (newlines kept)."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == ";":
            j = text.find("\n", i); j = n if j < 0 else j
            i = j; continue
        if text.startswith("#|", i):
            j = text.find("|#", i + 2); j = n if j < 0 else j + 2
            out.append("".join(ch if ch == "\n" else " " for ch in text[i:j])); i = j; continue
        if c == "#" and text.startswith("#\\", i):            # character literal #\;  #\"
            out.append(text[i:i + 3]); i += 3; continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append("".join(ch if ch == "\n" else " " for ch in text[i:j + 1])); i = j + 1; continue
        out.append(c); i += 1
    return "".join(out)


def load_allow(path):
    allow = []
    for ln in open(path):
        ln = ln.strip()
        if not ln or ln.startswith("#"):
            continue
        m = re.match(r"(\S+)\s+(\S.*?)\s+--\s+(.+)$", ln)
        if not m:
            sys.exit(f"derived-gas-allow.txt: bad line (want `file  regex  -- reason`): {ln}")
        allow.append((m.group(1), re.compile(m.group(2)), m.group(3)))
    return allow


def main():
    allow = load_allow(os.path.join(ROOT, "scripts", "derived-gas-allow.txt"))
    used, bad = set(), []
    for rel in FILES:
        path = os.path.join(ROOT, rel)
        if not os.path.exists(path):
            sys.exit(f"check-derived-gas: {rel} is missing")
        for no, line in enumerate(code_only(open(path, encoding="utf-8").read()).split("\n"), 1):
            for m in NUM.finditer(line):
                hit = next((k for k, (f, rx, _) in enumerate(allow) if f == rel and rx.search(line)), None)
                if "--list" in sys.argv:
                    print(f"{'ok  ' if hit is not None else 'BAD '}{rel}:{no}: {line.strip()}")
                if hit is None:
                    bad.append(f"{rel}:{no}: {m.group(1)} in: {line.strip()}")
                else:
                    used.add(hit)
    stale = [f"{allow[k][0]}  {allow[k][1].pattern}" for k in range(len(allow)) if k not in used]
    if bad or stale:
        for b in bad:
            print("GAS LITERAL in hand-written code:", b)
        for s in stale:
            print("stale allow entry (matches nothing; delete it):", s)
        print("fix: compute it in Lean (Evm.CL.GasEmit), emit it (lake exe emitHostCL), call the spec-* function;"
              " or, if the number is not a gas charge, allow it in scripts/derived-gas-allow.txt with a reason")
        sys.exit(1)
    print(f"no hand-written gas schedule in {len(FILES)} replay files OK ({len(used)} allowed non-charge uses)")


if __name__ == "__main__":
    main()
