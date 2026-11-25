#!/usr/bin/env python3
"""check-rv32-alignment.py — no misaligned 32-bit access in the emitted rv32.

bao1x's VexRiscv TRAPS misaligned loads and stores: exception 4
(LoadAddressMisaligned) or 6 (StoreAddressMisaligned), raised from
`io_cpu_writeBack_unalignedAccess` in VexRiscv_CramSoC.sv. The RISC-V ISA
allows an implementation to do that, so an `lw` on a byte-granular address is
a lowering bug, not a chip quirk. One of them — `PUSH1` reading its immediate
with `lw code + pc` — terminated the first board run before any output.

`Evm.CL.RV32.Lower` answers this with a FORWARD analysis over the instruction
stream, and emits a byte-wise sequence wherever it cannot justify an address.
This script answers the same question from the other end: over the emitted
TEXT, by resolving each access's base BACKWARD to a root it can classify. Two
implementations of one claim, so a mistake in either shows up as disagreement
rather than as a trap on hardware.

Aligned roots, and why:
  sp        our own frame: `eita_run` enters 16-byte aligned, every `spSub`
            in the gadgets is a multiple of 16
  s0        `EvmState *`, whose 64-bit fields are at 8-byte offsets
  s3        the stack, an array of `u256_t` (32-byte stride, `_Static_assert`ed
            8-byte aligned)
  s2        a byte offset into the stack: always a multiple of 32

Byte-granular roots, both of which must reach the byte-wise sequences:
  s4        `codeBase`; `codeBase + pc` is where PUSH reads its immediate
  a pointer loaded out of EvmState (memory/code/calldata/returndata), which
            then has an EVM byte offset added to it

Exit 1 on any access that is byte-granular or that cannot be classified at
all: an unclassifiable base is not evidence of alignment.
"""
import re
import sys

# EvmState offsets whose contents are BYTE pointers (c/evm_state.h).
BYTE_PTR_FIELDS = {40: "memory", 64: "code", 80: "calldata",
                   96: "returndata", 136: "jumpdests"}
# ...and the ones whose contents are pointers to ALIGNED things, with the
# reason each one is aligned. These are host contracts: they hold because of
# the C types in evm_state.h, not because of anything the emitter did.
ALIGNED_PTR_FIELDS = {
    600: "EvmState.cont_table, a `const void *const *` (4-byte entries)",
    504: "EvmState.cb_ctx, which the host must align to 8 "
         "(the emitted code reads 64-bit fields off it)",
    32:  "EvmState.stack, a `u256_t *` (_Static_assert: 8-byte aligned)",
    496: "EvmState.cb, an `EvmCallbacks *` whose slots the EITA_PTR union "
         "pins to 8 bytes (asserted in evm_state.h)",
}
# A function's entry state. `eita_run` takes `EvmState *` in a0 per the C ABI,
# so it is aligned by its type; `eita_set_fork` takes a fork ordinal, which is
# scaled by four before it reaches an address.
ENTRY_ALIGNED = {
    "eita_run": {"a0": "incoming `EvmState *` (aligned by its C type)"},
}
ALIGNED_ROOTS = {"sp": "frame", "s0": "EvmState", "s3": "stack base",
                 "s2": "stack byte offset", "zero": "zero"}

ACCESS = re.compile(r"^\s{4}(lw|sw)\s+(\w+),\s*(-?\d+)\((\w+)\)\s*$")
INSN = re.compile(r"^\s{4}(\S+)\s*(.*)$")
LABEL = re.compile(r"^([A-Za-z_.][\w.]*):\s*$")
# a destination is the first operand of these; everything else we treat as
# opaque, which makes an unknown base a failure rather than a pass
DEFINES = {"add", "addi", "mv", "lw", "lbu", "la", "li", "sub", "slli",
           "srli", "or", "and", "xor", "sltu", "sltiu", "neg", "not", "snez",
           "mul", "mulhu", "div", "divu", "rem", "remu", "lui"}


def blocks(path):
    """The emitted file, split into top-level symbol bodies."""
    out, name, body = [], None, []
    for line in open(path):
        line = line.rstrip("\n")
        m = LABEL.match(line)
        if m and not m.group(1).startswith("."):
            if name:
                out.append((name, body))
            name, body = m.group(1), []
        else:
            body.append(line)
    if name:
        out.append((name, body))
    return out


def last_def(body, i, reg):
    """The last instruction before `i` that writes `reg`, linearly."""
    for j in range(i - 1, -1, -1):
        m = INSN.match(body[j])
        if not m:
            continue
        op, ops = m.group(1), m.group(2)
        if op not in DEFINES:
            continue
        parts = [p.strip() for p in ops.split(",")]
        if parts and parts[0] == reg:
            return j, op, parts
    return None


def classify(body, i, base, depth=0, sym=None):
    """(aligned, why) for the address in `base` at instruction `i`."""
    if depth > 8:
        return None, "chain too deep to resolve"
    if base in ALIGNED_ROOTS:
        return True, ALIGNED_ROOTS[base]
    if base == "s4":
        return False, "codeBase (code + pc is byte-granular)"
    d = last_def(body, i, base)
    if d is None:
        entry = ENTRY_ALIGNED.get(sym or "", {})
        if base in entry:
            return True, entry[base]
        return None, f"no definition of {base} in this body"
    j, op, parts = d
    if op == "la":
        # every datum this emitter defines is `.p2align 2`
        return True, f"&{parts[1]} (emitted .p2align 2)"
    if op == "lw":
        m = re.match(r"^(-?\d+)\((\w+)\)$", parts[1])
        if m and m.group(2) == "s0":
            off = int(m.group(1))
            if off in BYTE_PTR_FIELDS:
                return False, f"EvmState.{BYTE_PTR_FIELDS[off]} (a byte pointer)"
            if off in ALIGNED_PTR_FIELDS:
                return True, ALIGNED_PTR_FIELDS[off]
            return None, f"pointer loaded from EvmState+{off}"
        return None, f"loaded from {parts[1]}"
    if op in ("add", "sub"):
        # a sum is aligned only if both addends are
        for r in parts[1:]:
            ok, why = classify(body, j, r, depth + 1, sym)
            if ok is not True:
                return ok, f"{base} = {op} {','.join(parts[1:])} -> {why}"
        return True, f"sum of aligned ({','.join(parts[1:])})"
    if op == "addi":
        off = int(parts[2]) if re.match(r"^-?\d+$", parts[2]) else None
        if off is None or off % 4 != 0:
            return None, f"{base} = addi {parts[1]},{parts[2]} (offset not a multiple of 4)"
        return classify(body, j, parts[1], depth + 1, sym)
    if op == "mv":
        return classify(body, j, parts[1], depth + 1, sym)
    if op == "slli":
        sh = int(parts[2]) if re.match(r"^-?\d+$", parts[2]) else 0
        return (True, f"<< {sh}") if sh >= 2 else (None, f"{base} = slli by {sh}")
    if op == "li":
        v = int(parts[1], 0) if re.match(r"^-?(0x)?[0-9a-fA-F]+$", parts[1]) else None
        if v is not None and v % 4 == 0:
            return True, f"constant {v}"
        return None, f"{base} = li {parts[1]}"
    return None, f"{base} = {op} {','.join(parts[1:])}"


def main(path):
    bad, unknown, ok = [], [], 0
    for name, body in blocks(path):
        for i, line in enumerate(body):
            m = ACCESS.match(line)
            if not m:
                continue
            op, _dst, off, base = m.group(1), m.group(2), int(m.group(3)), m.group(4)
            aligned, why = classify(body, i, base, 0, name)
            if aligned is True and off % 4 != 0:
                aligned, why = False, f"offset {off} is not a multiple of 4"
            entry = (name, line.strip(), why)
            if aligned is True:
                ok += 1
            elif aligned is False:
                bad.append(entry)
            else:
                unknown.append(entry)

    print(f"{ok} aligned 32-bit accesses")
    for label, group in (("MISALIGNED", bad), ("UNCLASSIFIED", unknown)):
        if group:
            print(f"\n{label}: {len(group)}")
            for name, line, why in group[:40]:
                print(f"  {name}: {line}    [{why}]")
            if len(group) > 40:
                print(f"  … and {len(group) - 40} more")
    if bad or unknown:
        print("\nFAIL: every 32-bit access must be provably 4-aligned "
              "(the chip traps the rest)", file=sys.stderr)
        return 1
    print("no misaligned 32-bit access in the emitted rv32 OK")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "c/handlers-rv32.S"))
