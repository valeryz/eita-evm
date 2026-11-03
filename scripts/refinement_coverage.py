#!/usr/bin/env python3
"""refinement_coverage.py — generate the refinement coverage matrix.

The ledger for the fork-delta spec methodology (lean/Evm/SPEC-METHODOLOGY.md).
Deterministic output (no timestamps); scripts/verify-coverage.sh diffs the
matrix against the committed copy and enforces the debt ceiling, which is
stored SEPARATELY (scripts/generated/refinement-debt-ceiling.txt) so that
regenerating the matrix can never raise it.

Honesty bounds (also stated in the emitted header):

- PROVED is a TEXTUAL classification: the proof body contains no literal
  `sorry` (comments stripped). It is NOT an axiom check — admitted
  dependencies, unsound axioms, or `native_decide` are not detected here.
  The axiom-clean subset is scripts/verify-axioms.sh.
- "Resolves a relation" means an OBLIGATION theorem concludes it.
  Obligations are identified EXPLICITLY: the `*_sound` / `*_sound_shape`
  naming convention (regardless of binder style), or any theorem with an
  implementation-execution hypothesis (impl-side reference in hypotheses
  or named binders) concluding the relation. Anything else is not allowed
  to discharge: structural lemmas (relation in hypothesis position),
  instance/spec facts (`code = [] → IsValidDeployedCode code` proves
  something ABOUT the relation, not that the implementation refines it),
  and table-extension facts are listed in notes / FACTS-ONLY /
  STRUCTURAL-ONLY rows, never as PROVED.
- Resolution matches fully qualified names via the file's per-declaration
  namespace/open scope (files may contain several `namespace` blocks);
  bare mentions resolve through opens/imports, qualified mentions
  (`Evm.F.Spec.R`) directly. Unresolvable mentions are AMBIGUOUS, never
  guessed; same-name relations in other forks SHADOW a mention and are
  reported explicitly.
- Identity-shaped statements (`P → P`) without the mandated `_shape`
  suffix are classified SHAPE-UNSUFFIXED (a convention violation).

Section A (budget-enforced): every theorem mentioning a registered
relation, classified per fork. Section B (informational): every
registered relation, fully qualified, with its resolving theorem, its
structural-only lemmas, or its gap status.

Relation registry: Prop-style declarations in Spec files — names
starting with `Is`, plus any Spec-declared name concluded by a
`*_sound`/`*_sound_shape` theorem (catches non-Is names like
InitcodeWithinCap). Generic scaffolding (IsBinaryStep and friends) is
excluded.
"""

import glob
import os
import re
import sys

LEAN = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                     "..", "lean", "Evm"))

# Files outside Evm/*/Spec/ that state spec-relation theorems — the
# composition layer (IR compile_sound theorems conclude IsFrameRun /
# per-fork relations). Curated and explicit; extend deliberately.
EXTRA_FILES = [os.path.join(LEAN, "IR", "Soundness.lean")]

DECL_RE = re.compile(r"^(theorem|def|abbrev|inductive) (\w+)\b")
NS_RE = re.compile(r"^namespace ([A-Za-z0-9_.]+)\s*$")
END_RE = re.compile(r"^end(?:\s+([A-Za-z0-9_.]+))?\s*$")
OPEN_RE = re.compile(r"^open ([A-Za-z0-9_. ]+)$")
IMPORT_RE = re.compile(r"^import ([A-Za-z0-9_.]+)")
BARE_MENTION_RE = re.compile(r"(?<![\w.])(Is[A-Za-z0-9]+|[A-Z][A-Za-z0-9]+)\b")
QUAL_MENTION_RE = re.compile(r"(Evm\.[A-Za-z0-9_.]+)\b")

# Generic scaffolding relations, not per-opcode obligations.
EXCLUDED = {"IsAnyStep", "IsBinaryStep", "IsUnaryStep", "IsTernaryStep"}


def strip_comments(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def split_top_level(prop, sep="→"):
    """Split `prop` at top-level (depth-0) `sep` occurrences."""
    parts, depth, cur = [], 0, []
    i = 0
    while i < len(prop):
        ch = prop[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        if depth == 0 and prop.startswith(sep, i):
            parts.append("".join(cur))
            cur = []
            i += len(sep)
            continue
        cur.append(ch)
        i += 1
    parts.append("".join(cur))
    return parts


def prop_of(statement):
    """The proposition after the binders' top-level colon."""
    parts = split_top_level(statement, sep=":")
    if len(parts) >= 2:
        return ":".join(parts[1:]).strip()
    return statement.strip()


def conclusion_of(prop):
    parts = split_top_level(prop, sep="→")
    return parts[-1]


def hypothesis_part(prop):
    parts = split_top_level(prop, sep="→")
    return "→".join(parts[:-1])


class Decl:
    def __init__(self, kind, name, qual, statement, body,
                 ns, opens, line):
        self.kind, self.name, self.qual = kind, name, qual
        self.statement, self.body = statement, body
        self.ns, self.opens, self.line = ns, opens, line
        self.prop = prop_of(statement)


class SpecFile:
    """Parse a Lean file: declarations with their per-declaration
    namespace scope. Implemented as an event walk over the
    comment-stripped text: `namespace` / `end` / declaration events in
    source order, so files with several namespace blocks (e.g.
    Evm/IR/Soundness.lean) resolve each declaration's namespace
    correctly."""

    EVENT_RE = re.compile(
        r"^(theorem|def|abbrev|inductive|structure) ([A-Za-z0-9_.']+)\b"
        r"|^namespace ([A-Za-z0-9_.]+)\s*$"
        r"|^end(?:\s+([A-Za-z0-9_.]+))?\s*$"
        r"|^open ([A-Za-z0-9_. ]+)$"
        r"|^import ([A-Za-z0-9_.]+)", re.M)

    def __init__(self, path, fork=None, base=None):
        self.path = path
        parts = path.split(os.sep)
        self.fork = fork or parts[-3]
        self.base = base or parts[-1]
        self.code = strip_comments(open(path).read())
        self.lines = self.code.splitlines()
        self.decls = self._parse()

    def _parse(self):
        events = []  # (pos, kind, arg)
        for m in self.EVENT_RE.finditer(self.code):
            if m.group(1):
                events.append((m.start(), "decl",
                               (m.group(1), m.group(2), m.end(2))))
            elif m.group(3):
                events.append((m.start(), "ns", m.group(3)))
            elif m.group(4) is not None or m.group(0).startswith("end"):
                events.append((m.start(), "end", m.group(4)))
            elif m.group(5):
                events.append((m.start(), "open", m.group(5)))
            elif m.group(6):
                events.append((m.start(), "import", m.group(6)))
        events.sort(key=lambda e: e[0])

        decls = []
        ns_stack = []
        open_scopes = []  # (block_depth, ns); expire when their block pops
        imports = []
        n = len(events)
        for i, (pos, kind, arg) in enumerate(events):
            if kind == "ns":
                ns_stack.append(arg)
            elif kind == "end":
                if ns_stack:
                    ns_stack.pop()
                open_scopes = [o for o in open_scopes if o[0] <= len(ns_stack)]
            elif kind == "open":
                for ns in arg.split():
                    open_scopes.append((len(ns_stack), ns))
            elif kind == "import":
                imports.append(arg)
            else:
                dkind, name, name_end = arg
                next_pos = events[i + 1][0] if i + 1 < n else len(self.code)
                seg = self.code[name_end:next_pos]
                sig_at = seg.find(":=")
                if sig_at != -1:
                    statement = seg[:sig_at]
                    body = seg[sig_at + 2:]
                else:
                    statement = seg
                    body = ""
                ns = ".".join(ns_stack) if ns_stack else None
                opens = [o[1] for o in open_scopes]
                decls.append(Decl(dkind, name,
                                  f"{ns}.{name}" if ns else name,
                                  statement, body, ns, opens, 0))
        self.imports = imports
        return decls


def classify(decl):
    """Textual status (see module docstring for bounds)."""
    name, prop = decl.name, decl.prop
    if re.search(r"\bsorry\b", decl.body):
        return "SORRY"
    norm = re.sub(r"\s+", " ", prop).strip()
    parts = [p.strip() for p in split_top_level(norm, sep="→")]
    identity = len(parts) == 2 and parts[0] == parts[1] and parts[0] != ""
    if identity and not name.endswith("_shape"):
        return "SHAPE-UNSUFFIXED"
    if identity or name.endswith("_shape"):
        # NOTE: a *_shape theorem whose proof closes by defeq (e.g. the
        # relation is DEFINED as the implementation's equation) is still
        # debt: nothing independent was proved. Section B flags such
        # relations as SPEC-IS-IMPL.
        return "SHAPE"
    return "PROVED"


# --- shape-based obligation test -------------------------------------------------
#
# Decided from the statement's SHAPE, never its spelling. A theorem can
# discharge a relation's obligation iff:
#   1. its conclusion applies the relation to universally-bound
#      arguments — no constants (0, [], "…", Evm.Bytes.empty), and any
#      compound term (record updates, applications) has only bound free
#      identifiers. An instance fact therefore never discharges,
#      whatever it is named;
#   2. it has a real execution hypothesis: an equation headed by an
#      implementation application (per-fork VM Instructions/Effect or
#      the IR layer) — not the mere occurrence of a keyword.
# The one convention exception: an identity statement (P → P) named
# *_shape IS the methodology's explicitly-stated open obligation; it
# counts as an (unproved) obligation by convention, not by shape.
# The *_sound naming convention is REPORTED (deviations noted) but is
# never evidence that discharges anything.

EXEC_HEAD = re.compile(
    r"((?:\bInstructions\.\w+|Effect\.\w+|IR\.\w+|"
    r"runBinary|runUnary|runTernary|runNullaryPush|liftPure|"
    r"do[A-Z]\w*|runFrame\w*|applyMessage|processTransaction|resume\w*|"
    r"compileLoop|compile_sound|compileProgram|toCL|denote\w*|"
    r"(?:[A-Z][\w']*\.){2,}[\w']+))\s+[^\s:=]")

IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
SHAPE_KW = {"with", "fun", "if", "then", "else", "let", "in", "match",
            "where", "by", "forall", "exists"}


def bound_names(d):
    """Variables bound at the statement: paren/curly binders before the
    top-level colon, plus ∀/∃ binders inside the proposition."""
    names = set()
    bseg = split_top_level(d.statement, sep=":")[0]
    for m in re.finditer(r"[( {]([^():{}]*?)[:}]", bseg):
        for nm in m.group(1).split():
            if re.fullmatch(r"[a-z_][\w']*", nm):
                names.add(nm)
    for m in re.finditer(r"[∀∃]\s*([a-z][\w']*(?:\s+[a-z][\w']*)*)\s*,",
                         d.prop):
        names.update(m.group(1).split())
    for m in re.finditer(r"[∀∃]\s*((?:\([a-z][\w']*[^()]*\)\s*)+)", d.prop):
        for g in re.finditer(r"\(([a-z][\w']*(?:\s+[a-z][\w']*)*)\s*:",
                             m.group(1)):
            names.update(g.group(1).split())
    return names


def mention_args(concl, name):
    """Argument substring following `name`'s mention in `concl`."""
    idx = concl.find(name)
    if idx == -1:
        return None
    i = idx + len(name)
    depth = 0
    out = []
    while i < len(concl):
        ch = concl[i]
        if depth == 0 and ch in "∧∨→,|)":
            break
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            if depth == 0:
                break
            depth -= 1
        out.append(ch)
        i += 1
    return "".join(out)


QUAL_APP = re.compile(r"^\(?\s*([A-Z][\w'.]*(?:\.[A-Za-z][\w'.]*)+)"
                      r"\s+(.+)$")


def args_general(argstr, bound, pinned=frozenset()):
    """True iff every top-level argument term is general: all its free
    identifiers bound, or a qualified implementation application whose
    own arguments are bound (the `IsSweepEmptyStep state touched
    (Impl.sweepEmptyAccounts state touched)` shape). Ground constants
    (0, [], Evm.Bytes.empty) are never general. Returns
    (general, saw_impl_app)."""
    if not argstr:
        return False, False
    if re.search(r"(?<![\w'])\d", argstr) or "[]" in argstr:
        return False, False
    s = re.sub(r"\bwith\b[^{}]*", "", argstr)  # record-update field tails
    saw_impl = False
    for term in split_top_level(s, sep=" "):
        term = term.strip()
        if not term:
            continue
        ids = IDENT_RE.findall(term)
        if all(i in bound or i in SHAPE_KW for i in ids):
            if any(i in pinned for i in ids):
                return False, saw_impl
            continue
        m = QUAL_APP.match(term)
        if m:
            arg_ids = IDENT_RE.findall(m.group(2))
            if all(i in bound or i in SHAPE_KW for i in arg_ids):
                if any(i in pinned for i in arg_ids):
                    return False, saw_impl
                saw_impl = True
                continue
        return False, saw_impl
    return True, saw_impl


def execution_hypothesis(d, spec_defined):
    """A hypothesis equation headed by an implementation application —
    where "implementation" means the head is defined OUTSIDE the Spec
    modules (a Spec-tree helper is still spec)."""
    pre = split_top_level(d.statement, sep=":")[0] + " " \
        + hypothesis_part(d.prop)
    if "=" not in pre:
        return False
    for m in EXEC_HEAD.finditer(pre):
        head = m.group(1)
        if head in spec_defined:
            continue
        bare = head.rsplit(".", 1)[-1]
        if bare in spec_defined:
            continue
        return True
    return False


GROUND_EQ = re.compile(
    r"\b([a-z][\w']*)\s*=\s*(\d+|\[\]|[A-Z][\w'.]*\.[\w'.]+)")


def pinned_vars(d, bound):
    """Conclusion variables pinned to constants by a hypothesis
    (`d = 0`): formally bound, but the theorem is an instance fact."""
    pinned = set()
    segs = split_top_level(d.prop, sep="→")[:-1]
    segs.append(split_top_level(d.statement, sep=":")[0])
    for seg in segs:
        for m in GROUND_EQ.finditer(seg):
            lhs, rhs = m.group(1), m.group(2)
            if lhs in bound and (rhs[0].isdigit() or rhs == "[]"
                                 or rhs.split(".")[0] not in bound):
                pinned.add(lhs)
    return pinned


def discharges(d, relname, spec_defined=frozenset()):
    """Shape rule: can theorem d discharge relname's obligation?"""
    concl = conclusion_of(d.prop)
    if relname not in concl:
        return False
    bound = bound_names(d)
    general, saw_impl = args_general(mention_args(concl, relname),
                                     bound, pinned_vars(d, bound))
    if not general:
        return False
    norm = re.sub(r"\s+", " ", d.prop).strip()
    parts = [p.strip() for p in split_top_level(norm, sep="→")]
    identity = len(parts) == 2 and parts[0] == parts[1] and parts[0] != ""
    if identity and d.name.endswith("_shape"):
        return True
    # condition 2, either form: a real execution hypothesis, or the
    # conclusion itself applies the relation to an implementation
    # application (output-equality shape).
    return execution_hypothesis(d, spec_defined) or saw_impl


def is_obligation(d, spec_defined=frozenset()):
    """Obligation for SOME relation (selftest helper): any registered
    relation mention — bare or qualified — in the conclusion with
    general arguments and an execution hypothesis (or the _shape
    identity convention)."""
    concl = conclusion_of(d.prop)
    names = set(BARE_MENTION_RE.findall(concl))
    names |= {q.rsplit(".", 1)[1] for q in QUAL_MENTION_RE.findall(concl)}
    for m in names:
        if discharges(d, m, spec_defined):
            return True
    return False


def spec_is_impl(body, spec_defined):
    """A relation defined as the implementation's OWN equation
    (recoverSender-style): the LHS of its defining equation is headed
    by an application defined outside the Spec modules. Discharging it
    is circular — nothing independent is proved. Detected
    conservatively: only when the definition's equation LHS is such an
    application."""
    b = body.strip()
    if "=" not in b:
        return False
    # conservative: the WHOLE definition is one equation whose LHS starts
    # with an application headed outside the Spec modules (a `let … :=`
    # or an independent conjunct first means the spec has real content).
    m = re.match(
        r"^\(?\s*((?:[A-Z][\w']*\.){2,}[\w']+)\s+[^=]*=", b, re.S)
    if not m:
        return False
    head = m.group(1)
    return head not in spec_defined \
        and head.rsplit(".", 1)[-1] not in spec_defined


def main():
    lean_root = os.environ.get("REFCOV_ROOT", LEAN)
    files = [SpecFile(p) for p in sorted(
        glob.glob(os.path.join(lean_root, "*", "Spec", "*.lean")))]
    files += [SpecFile(p, fork="IR (composition)", base="IR/Soundness.lean")
              for p in [os.path.join(lean_root, "IR", "Soundness.lean")]
              if os.path.exists(p)]

    # Per-declaration namespace resolution index.
    rel_by_qual = {}   # qualified relation -> (fork, bare, file, body)
    definers = {}      # bare -> set of namespaces declaring it
    spec_defined = set()  # names/quals declared in Spec modules
    all_decls = []
    for f in files:
        for d in f.decls:
            all_decls.append((f, d))
            in_spec = "/Spec/" in f.path.replace(os.sep, "/")
            if d.kind in ("def", "abbrev", "inductive") and in_spec:
                spec_defined.add(d.qual)
                spec_defined.add(d.name)
            if d.kind in ("def", "abbrev", "inductive") and in_spec and \
                    "." not in d.name and \
                    (d.name.startswith("Is") or d.name in EXCLUDED):
                rel_by_qual.setdefault(
                    d.qual, (f.fork, d.name, f.base, d.body))

    definers = {}      # bare -> set of namespaces declaring it
    for qual, (fork, bare, base, _b) in rel_by_qual.items():
        definers.setdefault(bare, set()).add(qual.rsplit(".", 1)[0])

    # Bootstrap: any Spec-declared name (non-Is too) concluded by a
    # *_sound / *_sound_shape theorem is a refinement target (e.g.
    # InitcodeWithinCap). Extend the registry with those.
    def mentions(decl):
        bare = set(BARE_MENTION_RE.findall(decl.prop))
        qual = set(q for q in QUAL_MENTION_RE.findall(decl.prop)
                   if q.split(".")[-1][0].isupper())
        return bare, qual

    declared_in_spec = {}  # bare -> (qual, fork, base, decl)
    for f, d in all_decls:
        if d.kind in ("def", "abbrev", "inductive") and f.base != "IR/Soundness.lean" \
                and "/Spec/" in f.path.replace(os.sep, "/"):
            if "." not in d.name:
                declared_in_spec.setdefault(d.name, (d.qual, f.fork, f.base, d))
    for f, d in all_decls:
        if d.kind == "theorem" and d.name.endswith("_sound_shape"):
            bare, _ = mentions(d)
            for b in bare:
                if b in declared_in_spec and b not in definers:
                    q, fork, base, dcl = declared_in_spec[b]
                    rel_by_qual[q] = (fork, b, base, dcl.body)
                    definers.setdefault(b, set()).add(q.rsplit(".", 1)[0])

    # --- classify every theorem mentioning a registered relation ---
    inv = []
    for f, d in all_decls:
        if d.kind != "theorem":
            continue
        bare, qual = mentions(d)
        hit = bool(bare & set(definers)) or \
            bool(qual & set(rel_by_qual))
        if not hit:
            continue
        inv.append((f.fork, f.base, d.name, d.qual, classify(d)))

    # --- candidate index: only CONCLUSION-position mentions resolve ---
    # An OBLIGATION theorem (one that can discharge a relation) is:
    #   top-level arrow + relation in conclusion + (named *_sound[/_shape]
    #   OR an implementation-execution hypothesis).
    # Instance/spec facts (e.g. `code = [] → IsValidDeployedCode code`)
    # conclude the relation but never qualify; they are listed as facts.
    cand, cand_facts, cand_struct = {}, {}, {}
    cand_qual = {}
    cand_qual_facts = {}
    for f, d in all_decls:
        if d.kind != "theorem":
            continue
        bare, quals = mentions(d)
        concl_bare = set(BARE_MENTION_RE.findall(conclusion_of(d.prop)))
        concl_qual = set(QUAL_MENTION_RE.findall(conclusion_of(d.prop)))
        hyp_bare = bare - concl_bare
        for b in concl_bare & set(definers):
            (cand if discharges(d, b, spec_defined) else cand_facts)\
                .setdefault(b, []).append((f, d))
        for b in hyp_bare & set(definers):
            cand_struct.setdefault(b, []).append((f, d))
        for q in concl_qual & set(rel_by_qual):
            (cand_qual if discharges(d, q.rsplit(".", 1)[1], spec_defined)
             else cand_qual_facts).setdefault(q, []).append((f, d))

    def resolve_ns(f, d, bare):
        """Namespace the bare mention `bare` resolves to at the theorem's
        position: its own namespace's declarations first, then its opens
        (which shadow suffix matches), then imports, then global
        uniqueness. None = ambiguous/invisible."""
        defs = definers.get(bare, set())
        if d.ns and d.ns in defs:
            return d.ns
        if d.ns:
            local = [q for q in defs if q.startswith(d.ns + ".")]
            if local:
                return local[0]
        for ns in d.opens:
            if ns in defs:
                return ns
            hit = [q for q in defs if q.startswith(ns + ".")]
            if hit:
                return hit[0]
        visible = [q for q in defs
                   if any(q == imp or q.startswith(imp + ".")
                          or imp.startswith(q + ".") for imp in f.imports)]
        if len(visible) == 1:
            return visible[0]
        if not visible and len(defs) == 1:
            return next(iter(defs))
        return None

    # --- Section B: per qualified relation ---
    rows = []
    for qual, (fork, bare, base, rel_body) in sorted(rel_by_qual.items()):
        if bare in EXCLUDED:
            continue
        status, via, note = "MISSING", None, ""
        if rel_body and spec_is_impl(rel_body, spec_defined):
            note = ("SPEC-IS-IMPL: this relation is defined as the "
                    "implementation's own equation — a discharge here is "
                    "circular and nothing independent is proved; the "
                    "independent obligation lives at clause level")
        hits = list(cand_qual.get(qual, []))
        for f, d in cand.get(bare, []):
            ns = resolve_ns(f, d, bare)
            if ns and ns == qual.rsplit(".", 1)[0]:
                hits.append((f, d))
        struct = [d for _, d in cand_struct.get(bare, [])]
        if hits:
            order = {"PROVED": 0, "SORRY": 1, "SHAPE": 2, "SHAPE-UNSUFFIXED": 3}
            best = min(hits, key=lambda h: order[classify(h[1])])
            status = classify(best[1])
            via = best[1].qual
            if len(hits) > 1:
                status += f" (+{len(hits) - 1} more)"
            facts = [d for f2, d in cand_facts.get(bare, [])
                     if resolve_ns(f2, d, bare) == qual.rsplit(".", 1)[0]]
            facts += [d for _, d in cand_qual_facts.get(qual, [])]
            if facts:
                note = ("instance/spec facts (do not discharge the general "
                        "obligation): "
                        + ", ".join(f"`{d.qual}`" for d in facts[:2])
                        + (", …" if len(facts) > 2 else ""))
        elif cand_facts.get(bare) or cand_qual_facts.get(qual):
            status = "FACTS-ONLY"
            facts = [d for f2, d in cand_facts.get(bare, [])
                     if resolve_ns(f2, d, bare) == qual.rsplit(".", 1)[0]]
            facts += [d for _, d in cand_qual_facts.get(qual, [])]
            if facts:
                note = ("only instance/spec facts conclude this relation; "
                        "the general implementation obligation is unproved: "
                        + ", ".join(f"`{d.qual}`" for d in facts[:2])
                        + (", …" if len(facts) > 2 else ""))
        elif struct:
            status = "STRUCTURAL-ONLY"
            via = None
            note = ("concluded nowhere; only structural lemmas assume it: "
                    + ", ".join(f"`{d.qual}`" for d in struct[:3])
                    + (", …" if len(struct) > 3 else ""))
        else:
            mentions_anywhere = cand.get(bare, []) or \
                [(f, d) for f, d in all_decls
                 if bare in BARE_MENTION_RE.findall(d.prop)]
            if mentions_anywhere:
                note = ("no theorem concludes this relation; mentions exist "
                        "but resolve elsewhere or ambiguously")
        rows.append((fork, qual, base, status, via, note))

    tot = {}
    for _, _, _, _, status in inv:
        key = status.split(" ")[0]
        tot[key] = tot.get(key, 0) + 1
    debt = tot.get("SORRY", 0) + tot.get("SHAPE", 0) \
        + tot.get("SHAPE-UNSUFFIXED", 0)

    out = []
    out.append("# Refinement coverage matrix")
    out.append("")
    out.append("Generated by `scripts/refinement_coverage.py` — do not edit")
    out.append("by hand; `scripts/verify-coverage.sh` fails CI on drift and")
    out.append("enforces the debt ceiling in")
    out.append("`scripts/generated/refinement-debt-ceiling.txt` (stored")
    out.append("separately, so regenerating this file can never raise it).")
    out.append("")
    out.append("Honesty bounds: **PROVED is textual** — no literal `sorry` in")
    out.append("the body (comments stripped); it is NOT an axiom check, and")
    out.append("identity-shaped statements without the `_shape` suffix are")
    out.append("flagged SHAPE-UNSUFFIXED. A relation is RESOLVED only by a")
    out.append("theorem concluding it (impl→spec direction); theorems merely")
    out.append("ASSUMING it are listed as structural lemmas and do not count.")
    out.append("For axiom-clean verification of the derived-code layer see")
    out.append("`scripts/verify-axioms.sh`. Relation resolution is by")
    out.append("statement mention + namespace (open/import), never bare-name")
    out.append("matching across forks.")
    out.append("")
    out.append("Reconciliation with the repo-wide 19 sorries: Section A counts")
    out.append("spec-relation theorems in `Evm/*/Spec/*.lean` plus the curated")
    out.append("composition layer in `Evm/IR/Soundness.lean` — 12 of the 13")
    out.append("`Spec/Refinement` sorries are relation theorems counted here;")
    out.append("the 13th is Frontier's `runFrame_gas_monotonic`, a frame-level")
    out.append("lemma that concludes no relation (not counted). The remaining")
    out.append("sorries live in `Trie/Stack` (3), `CL/AsmCore` (1),")
    out.append("`CL/StorageCache` (1), and `Frontier/Spec/StorageStep` (1, a")
    out.append("relation-internal lemma, not counted here).")
    out.append("")

    # Section A
    out.append("## A. Spec-relation theorem inventory (budget-enforced)")
    out.append("")
    by_fork = {}
    for fork, basefile, name, qual, status in inv:
        by_fork.setdefault(fork, []).append((basefile, name, qual, status))
    out.append("| fork | proved | sorry | shape | unsuffixed | total |")
    out.append("|---|---:|---:|---:|---:|---:|")
    gtot = {}
    for fork in sorted(by_fork):
        c = {}
        for _, _, _, status in by_fork[fork]:
            k = status.split(" ")[0]
            c[k] = c.get(k, 0) + 1
            gtot[k] = gtot.get(k, 0) + 1
        n = sum(c.values())
        out.append(f"| {fork} | {c.get('PROVED', 0)} | {c.get('SORRY', 0)} "
                   f"| {c.get('SHAPE', 0)} "
                   f"| {c.get('SHAPE-UNSUFFIXED', 0)} | {n} |")
    out.append(f"| **total** | **{gtot.get('PROVED', 0)}** "
               f"| **{gtot.get('SORRY', 0)}** | **{gtot.get('SHAPE', 0)}** "
               f"| **{gtot.get('SHAPE-UNSUFFIXED', 0)}** "
               f"| **{sum(gtot.values())}** |")
    out.append("")
    out.append(f"Debt (SORRY+SHAPE+SHAPE-UNSUFFIXED): {debt}.")
    out.append("")
    for fork in sorted(by_fork):
        out.append(f"### {fork}")
        out.append("")
        for basefile, name, qual, status in sorted(by_fork[fork]):
            out.append(f"- {status} `{name}` ({basefile})")
        out.append("")

    # Section B
    out.append("## B. Relation coverage, fully qualified (informational)")
    out.append("")
    sc = {}
    for _, _, _, status, _, _ in rows:
        k = status.split(" ")[0]
        sc[k] = sc.get(k, 0) + 1
    si = sum(1 for r in rows if "SPEC-IS-IMPL" in (r[5] or ""))
    out.append(f"{len(rows)} qualified relations: "
               + ", ".join(f"{k.lower()} {v}" for k, v in sorted(sc.items()))
               + f", spec-is-impl {si}.")
    out.append("")
    out.append("| relation | status | resolving theorem |")
    out.append("|---|---|---|")
    for fork, qual, base, status, via, note in rows:
        cell = f"`{qual}`"
        if note:
            cell += f"<br>{note}"
        out.append(f"| {cell} | {status} | {('`' + via + '`') if via else '—'} |")
    out.append("")
    print("\n".join(out))




SELFTEST_TREE = {
    "FakeFork/Spec/Step.lean": """
namespace Evm.FakeFork.Spec

def IsValidDeployedCode : Nat → Prop := fun _ => True

def IsSelfdestructEntry : Nat → Nat → Prop := fun _ _ => True

def Evm.FakeDeep.Thing.field : Nat := 0

end Evm.FakeFork.Spec
""",
    "FakeFork/Spec/SelfdestructRefinement.lean": """
import Evm.FakeFork.Spec.Step

namespace Evm.FakeFork.Spec

/-- Hypothesis in a NAMED BINDER, not a top-level arrow: must still be
    an obligation (impl-execution reference). -/
theorem doSelfdestruct_yield_isSelfdestructEntry
    {evm frame : Nat} {b : Nat}
    (h : Effect.doSelfdestruct evm = frame) :
    IsSelfdestructEntry evm frame := by
  trivial

end Evm.FakeFork.Spec
""",
    "FakeFork/Spec/Refinement.lean": """
import Evm.FakeFork.Spec.Step

namespace Evm.FakeFork.Spec

/-- Reviewer repro (PR #45): a QUALIFIED instance fact must not
    discharge the general obligation. -/
theorem empty_code_valid :
    Evm.FakeFork.Spec.IsValidDeployedCode 0 := by
  trivial

/-- The real obligation: still a placeholder. -/
theorem validDeployedCode_sound_shape (code : Nat) :
    IsValidDeployedCode code →
    IsValidDeployedCode code := by
  intro h; exact h

end Evm.FakeFork.Spec
""",
}


def selftest():
    """Regression checks for the ledger's classification rules, run on a
    synthetic spec tree. Exits nonzero on failure. Invoked with
    --selftest (also run by scripts/verify-coverage.sh)."""
    import shutil
    import subprocess
    import tempfile

    fails = []

    def check(name, cond):
        print(("PASS " if cond else "FAIL ") + name)
        if not cond:
            fails.append(name)

    # classify / is_obligation unit checks
    stmt = """ (evm evm' : Evm) :
    IsG1AddStep evm evm' →
    IsG1AddStep evm evm'"""
    d = Decl("theorem", "g1Add_sound", "Q", stmt, "  intro h; exact h",
             None, [], 0)
    d.prop = prop_of(d.statement)
    check("renamed identity -> SHAPE-UNSUFFIXED",
          classify(d) == "SHAPE-UNSUFFIXED")
    d.name = "g1Add_sound_shape"
    check("proper suffix -> SHAPE", classify(d) == "SHAPE")
    stmt2 = """ (evm evm' : Evm) :
    Evm.X.Instructions.revert evm = .ok evm' →
    IsRevertStep evm evm'"""
    d2 = Decl("theorem", "revert_sound", "Q", stmt2, "  intro _; sorry",
              None, [], 0)
    d2.prop = prop_of(d2.statement)
    check("real obligation -> SORRY", classify(d2) == "SORRY")
    stmt3 = """ {evm frame : Nat} {b : Nat}
    (h : Effect.doSelfdestruct evm = frame) :
    IsSelfdestructEntry evm frame"""
    d3 = Decl("theorem", "doSelfdestruct_yield_isSelfdestructEntry", "Q",
              stmt3, "  trivial", None, [], 0)
    d3.prop = prop_of(d3.statement)
    check("named-binder impl hypothesis -> obligation",
          is_obligation(d3))
    stmt4 = """ (code : Nat) :
    IsValidDeployedCode 0"""
    d4 = Decl("theorem", "empty_code_valid", "Q", stmt4, "  trivial",
              None, [], 0)
    d4.prop = prop_of(d4.statement)
    check("qualified instance fact -> NOT an obligation",
          not is_obligation(d4))

    # Shape-rule cases from the third review: instance facts must never
    # discharge, whatever they are named or contain.
    shape_cases = [
        ("real obligation shape", "t",
         """ (evm evm' : Evm) :
    Instructions.and_ evm = .ok evm' →
    IsAddStep evm evm'""", "IsAddStep", True),
        ("renamed instance fact (_sound)", "empty_code_sound",
         """ :
    IsValidDeployedCode 0""", "IsValidDeployedCode", False),
        ("binder containing 'opcode'", "t",
         """ (opcodeCount code : Nat)
    (h : opcodeCount = 0) :
    IsValidDeployedCode code""", "IsValidDeployedCode", False),
        ("arrow hypothesis containing 'execute'", "t",
         """ (code : Nat) :
    execute = 0 →
    IsValidDeployedCode code""", "IsValidDeployedCode", False),
        ("placeholder identity + _shape", "x_sound_shape",
         """ (evm evm' : Evm) :
    IsAddStep evm evm' →
    IsAddStep evm evm'""", "IsAddStep", True),
        ("bound conclusion + non-impl equation", "t",
         """ (code : Nat) :
    code = [] →
    IsValidDeployedCode code""", "IsValidDeployedCode", False),
        ("qualified constant argument", "t",
         """ :
    IsValidDeployedCode Evm.Bytes.empty""", "IsValidDeployedCode", False),
        ("output-equality shape (impl app in conclusion)", "sweep_sound",
         """ (state : Nat) (touched : List Nat) :
    IsSweepEmptyStep state touched
      (Evm.Fake.sweepEmptyAccounts state touched)""",
         "IsSweepEmptyStep", True),
        ("impl-equation hypothesis, dotted fn", "recover_sound_shape",
         """ (tx sender : Nat) :
    Evm.Fake.Utils.recoverSender tx = some sender →
    IsRecoverSenderStep tx sender""", "IsRecoverSenderStep", True),
        ("record-update conclusion over primed forall binders", "ir_sound",
         """ (code : Nat) :
    IR.compileLoop code = .ok 1 →
    ∀ (i i2 i' : Nat),
      IsFrameRun { i with gas := i' } i2""", "IsFrameRun", True),
    ]
    # Fourth review: spec-tree helpers are not implementation; pinning a
    # conclusion variable to a constant makes an instance fact.
    spec_names = {"Evm.FakeFork.Spec.Helper.check",
                  "Evm.FakeFork.Spec.Step.IsPinnedStep"}
    pin_cases = [
        ("spec-helper-headed hypothesis", "helper_sound",
         """ (x y : Nat) :
    Evm.FakeFork.Spec.Helper.check x = .ok y →
    IsPinnedStep x y""",
         {"Evm.FakeFork.Spec.Helper.check", "Helper.check",
          "Evm.FakeFork.Spec.Step.IsPinnedStep", "IsPinnedStep"}, False),
        ("conclusion variable pinned to a constant", "t",
         """ (d e : Nat) :
    Evm.Fake.Impl.run d = .ok e →
    d = 0 →
    IsPinnedStep d e""",
         set(), False),
    ]
    for name, tname, tstmt, sdef, want in pin_cases:
        dd = Decl("theorem", tname, "Q", tstmt, "  trivial", None, [], 0)
        dd.prop = prop_of(dd.statement)
        check(f"shape: {name}", discharges(dd, "IsPinnedStep", sdef) == want)
    for name, tname, tstmt, rel, want in shape_cases:
        dd = Decl("theorem", tname, "Q", tstmt, "  trivial", None, [], 0)
        dd.prop = prop_of(dd.statement)
        check(f"shape: {name}", discharges(dd, rel) == want)

    # end-to-end: reviewer repro on the synthetic tree
    root = tempfile.mkdtemp(prefix="refcov-selftest-")
    try:
        for rel, content in SELFTEST_TREE.items():
            p = os.path.join(root, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            open(p, "w").write(content)
        env = dict(os.environ, REFCOV_ROOT=root)
        out = subprocess.run(
            [sys.executable, os.path.abspath(__file__)],
            env=env, capture_output=True, text=True)
        md = out.stdout
        row = next((l for l in md.splitlines()
                    if "`Evm.FakeFork.Spec.IsValidDeployedCode`" in l), "")
        check("e2e: qualified fact does not discharge (SHAPE via placeholder)",
              "SHAPE" in row and "validDeployedCode_sound_shape" in md)
        check("e2e: qualified fact listed as fact, not PROVED",
              "empty_code_valid" in row and "PROVED" not in row)
        check("e2e: dotted decl not registered as relation",
              "FakeFork.Spec.Evm" not in md)
        row_sd = next((l for l in md.splitlines()
                       if "`Evm.FakeFork.Spec.IsSelfdestructEntry`" in l), "")
        check("e2e: named-binder obligation resolves PROVED",
              "PROVED" in row_sd and "doSelfdestruct_yield" in row_sd)
    finally:
        shutil.rmtree(root, ignore_errors=True)

    if fails:
        print(f"\n{len(fails)} selftest(s) FAILED")
        return 1
    print("\nselftest: all checks passed")
    return 0


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    sys.exit(main())
