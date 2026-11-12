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

With --stats-md PATH it also writes the per-component Lean statistics
(scripts/generated/verification-stats.md: statement / proof lines,
theorems, sorry, native_decide, axiom closure; counting rules in
STATS_RULES, printed with the table); verify-coverage.sh drift-checks both.

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
                # the signature ends at the first `:=` outside brackets (a
                # record update `{ e with f := v }` in the statement is not it)
                sig_at, depth = -1, 0
                for j, ch in enumerate(seg):
                    if ch in "([{":
                        depth += 1
                    elif ch in ")]}":
                        depth = max(0, depth - 1)
                    elif depth == 0 and seg.startswith(":=", j):
                        sig_at = j
                        break
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
PROJ_RE = re.compile(r"(?<=[\w')])\.[A-Za-z_][\w']*")
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
    s = re.sub(r"\s+", " ", argstr)  # a multi-line argument is one term
    s = re.sub(r"\bwith\b[^{}]*", "", s)  # record-update field tails
    saw_impl = False
    for term in split_top_level(s, sep=" "):
        term = term.strip()
        if not term:
            continue
        # a field projection of a bound variable (`tx.data.size`) is as
        # general as the variable: drop the `.field` tails before the
        # bound-name test (a qualified constant `Evm.Bytes.empty` keeps
        # its head `Evm`, which is never bound)
        ids = IDENT_RE.findall(PROJ_RE.sub("", term))
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
        if d.kind != "theorem":
            continue
        if d.name.endswith("_sound_shape"):
            bare, _ = mentions(d)
        elif d.name.endswith("_sound"):
            # a proved obligation registers its target the same way (once
            # the placeholder is gone) — conclusion mentions only
            bare = set(BARE_MENTION_RE.findall(conclusion_of(d.prop)))
        else:
            continue
        if True:
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
    # Reconciliation with the repo-wide `sorry` count, computed from the
    # tree (comment-stripped, every Evm/**/*.lean): Section A's SORRY rows,
    # then every other file that has one.
    per_file = {}
    for pth in sorted(glob.glob(os.path.join(lean_root, "**", "*.lean"),
                                recursive=True)):
        n_s = len(re.findall(r"\bsorry\b", strip_comments(open(pth).read())))
        if n_s:
            per_file[os.path.relpath(pth, lean_root)] = n_s
    n_all = sum(per_file.values())
    if "--stats-md" in sys.argv:
        with open(sys.argv[sys.argv.index("--stats-md") + 1], "w") as fh:
            fh.write(stats_markdown(lean_stats(n_all)))
    n_rel = tot.get("SORRY", 0)
    rest = ", ".join(f"`{k[:-5]}` ({v})" for k, v in sorted(per_file.items()))
    out.append(f"Reconciliation with the repo-wide {n_all} sorries: Section A")
    out.append(f"counts {n_rel} (relation theorems in `Evm/*/Spec/*.lean` and the")
    out.append("curated composition layer `Evm/IR/Soundness.lean`). By file,")
    out.append(f"all of them: {rest}.")
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



# ---------------------------------------------------------------------------
# Lean statistics (--stats-md PATH): per-component statement / proof line
# counts, theorems, sorry, native_decide and axiom closure
# (scripts/generated/verification-stats.md). Same comment stripping as the matrix's sorry
# reconciliation, so the two sorry counts agree by construction (asserted).

REPO = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
GH_TREE = "https://github.com/valeryz/eita-evm/tree/main/"

ETH_FORKS = ("Frontier Homestead DaoFork TangerineWhistle SpuriousDragon Byzantium "
             "Constantinople Petersburg Istanbul MuirGlacier Berlin London ArrowGlacier "
             "GrayGlacier Paris Shanghai Cancun Prague Osaka Amsterdam").split()
_CL = "lean/Evm/CL/"
# (id, title, link path, fnmatch patterns over repo-relative paths; `<Fork>` = each of
# ETH_FORKS, `CL/` = lean/Evm/CL/). First match wins; a .lean file no component claims
# fails the generator, so a new file is assigned deliberately.
COMPONENTS = [
    ("chains", "Chain specs (Arc, OP Stack)", "lean/Evm/Optimism",
     "lean/Evm/Arc/* lean/Evm/Optimism/*"),
    ("refinement", "Opcode refinement relations", "lean/Evm/Frontier/Spec",
     "lean/Evm/<Fork>/Spec/*"),
    ("spec", "EVM spec, Frontier to Osaka (Amsterdam staged)", "lean/Evm",
     "lean/Evm/<Fork>/* lean/Evm/BaseTypes.lean lean/Evm/Forks.lean"),
    ("effect", "Effect layer (callbacks, apply-tx, settlement, journal)", "lean/Evm/CL",
     "CL/Effect* CL/Journal* CL/StorageCache.lean CL/WordOps.lean CL/LimbC.lean"),
    ("ir", "IR compiler (chunks, symbolic execution)", "lean/Evm/IR", "lean/Evm/IR/*"),
    ("x86", "x86-64 backend", "lean/Evm/CL/X86", "CL/X86* CL/X86/* CL/OpInstrs.lean"),
    ("emit", "Gas, header and host emitters", "lean/Evm/CL",
     "CL/GasEmit* CL/HostEmit.lean CL/HeaderEmit.lean CL/ForkEmit.lean CL/RepriceEmit.lean "
     "CL/Extract.lean CL/MacroSpec.lean"),
    ("slots", "Native slot table (Velvet)", "verify/velvet-slots",
     "verify/velvet-slots/* CL/WorldSlotsModel.lean"),
    ("arm64", "ARM64 backend and shared lowering", "lean/Evm/CL/ARM64",
     "CL/ARM64.lean CL/ARM64/* CL/Asm* CL/OpSem.lean CL/CacheSound.lean CL/Arena.lean CL/CodeArena.lean "
     "CL/Boundary.lean CL/DispatchTable.lean CL/Fetch.lean CL/Flags.lean CL/Frame.lean "
     "CL/JumpDest.lean CL/Lowering.lean CL/MemExpandSpec.lean CL/ChunkMemExpand.lean "
     "CL/Pressure.lean CL/PushWide.lean CL/Relax.lean CL/StackOps.lean CL/StaticGuard.lean "
     "CL/Target.lean CL/BlobEnv.lean"),
    ("parallel", "Block-STM", "lean/Evm/Parallel", "lean/Evm/Parallel/*"),
    ("persist", "Persistence (layered state, recovery)", "lean/Evm/Persist",
     "lean/Evm/Persist/*"),
    ("crypto", "Crypto oracles and precompile contracts", "lean/Evm/Crypto",
     "lean/Evm/Crypto/*"),
    ("trie", "Trie and RLP", "lean/Evm/Trie", "lean/Evm/Trie/* lean/Evm/Trie.lean lean/Evm/Rlp.lean"),
    ("protocols", "State-layer protocols (Veil)", "verify/protocols", "verify/protocols/*"),
    ("tooling", "Tools: emitter drivers, test vectors, replay executables", "lean",
     "lean/*.lean"),
]


def _claims(rel, pats):
    """A pattern ending in /* claims a subtree; elsewhere * stays within one path segment."""
    for p in pats.split():
        p = p.replace("CL/", _CL, 1) if p.startswith("CL/") else p
        for q in ([p.replace("<Fork>", f) for f in ETH_FORKS] if "<Fork>" in p else [p]):
            rx = re.escape(q[:-2]) + "/.*" if q.endswith("/*") else \
                re.escape(q).replace(r"\*", "[^/]*")
            if re.fullmatch(rx, rel):
                return True
    return False


PAGE_ORDER = ("spec refinement effect ir arm64 x86 emit parallel persist crypto chains trie "
              "slots protocols tooling").split()

STATS_RULES = {   # printed under "Counting rules" (markdown)
    "Files": "every `.lean` file under `lean/Evm`, `lean/*.lean`, `verify/velvet-slots` and "
             "`verify/protocols` (no `.lake`); each belongs to exactly one component (first "
             "matching path pattern; an unclaimed file fails the generator)",
    "Lines": "physical lines after removing comments (`--`, `/- -/`, docstrings) and blank "
             "lines; each line counted once",
    "Declarations": "a declaration starts at a column-0 command keyword (attributes and "
                    "modifiers allowed) and runs to the next one; column-0 continuations "
                    "(`|` arms, `where`, `termination_by`, `deriving`) stay with it",
    "Theorem statement lines": "`theorem`/`lemma` from the keyword to the line holding the "
                               "first `:=` outside brackets (a `let`/`have` inside the "
                               "statement skipped), or to the line before a leading `|` arm; "
                               "a line shared with the proof counts here",
    "Proof lines": "the rest of a theorem; a Velvet `prove_correct` block entirely; `example` "
                   "blocks split like theorems",
    "Definition lines": "`def`, `abbrev`, `structure`, `inductive`, `instance`, `class`, "
                        "`opaque`, `axiom`, macros and notation, Velvet `method`, and in "
                        "`verify/protocols` the Veil model text (`veil module`, `action`, "
                        "`invariant`, `safety`, ...)",
    "Statement lines": "definition lines + theorem statement lines: the statements and the "
                       "definitions they rely on",
    "Other lines": "`import`, `namespace`/`section`/`end`, `open`, `variable`, `set_option`, "
                   "`attribute`, `#` commands: in neither column",
    "Theorems": "`theorem`/`lemma` declarations plus Velvet `prove_correct` blocks; `example` "
                "blocks are not counted",
    "Totals": "the claim rows only; the tools row (`lean/*.lean` executables) is listed but "
              "not totalled",
    "sorry": "`\\bsorry\\b` in the comment-stripped text (the coverage matrix's rule)",
    "native_decide": "occurrences in the comment-stripped text",
    "Axioms": "`lean/Evm` theorems: their closures in `scripts/generated/axiom-audit.txt` "
              "(`scripts/verify-axioms.sh`); standard = only `propext`, `Classical.choice`, "
              "`Quot.sound`; with `native_decide` = the closure has a "
              "`._native.native_decide` auxiliary axiom. `verify/velvet-slots`: the "
              "`#print axioms` of `Slots/Axioms.lean`, which `verify-velvet-slots.sh` requires "
              "to be standard. `verify/protocols`: the axiom checks `verify-protocols.sh` "
              "requires to be standard",
    "veil": "Veil's verification conditions are generated by `#gen_theorems` when a model is "
            "checked and are not in the source: the row counts the model text as definition "
            "lines and reports the number of models (`veil module`) and the written "
            "`invariant`/`safety` clauses (shared ones counted once, where written)",
}

_MODS = r"(?:(?:@\[[^\]]*\]|private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|set_option\s+\S+\s+\S+\s+in)\s+)*"
_DEF_KW = ("def abbrev structure inductive instance class opaque axiom method macro_rules "
           "macro syntax elab notation infixl infixr infix prefix postfix").split()
_VEIL_KW = ("veil action invariant safety relation individual function type procedure "
            "after_init ghost instantiate assumption immutable enum").split()
_OTHER_RE = re.compile(r"^(import|namespace|end|section|noncomputable\s+section|open|variable|"
                       r"universe|set_option|attribute|export|initialize|builtin_initialize|"
                       r"omit|include|mutual|run_cmd|run_meta|#\w+)\b")
_HEAD_RE = re.compile(r"^" + _MODS + r"(theorem|lemma|example|prove_correct|"
                      + "|".join(_DEF_KW) + r")\b(.*)")
_VEIL_RE = re.compile(r"^(" + "|".join(_VEIL_KW) + r")\b")
_ATTR_ONLY = re.compile(r"^" + _MODS + r"$")
_NAME_RE = re.compile(r"\s*([^\s:({\[⦃⟨]+)")


def strip_comments_keep_lines(text):
    """strip_comments, keeping line structure (a block comment becomes its newlines)."""
    text = re.sub(r"/-.*?-/", lambda m: "\n" * m.group().count("\n"), text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def _statement_end(lines):
    """Index of the last statement line of a theorem block (see STATS_RULES)."""
    depth, lets = 0, 0   # lets: open depth-0 `let`/`have` binders inside the statement
    for i, ln in enumerate(lines):
        if i > 0 and depth == 0 and ln.lstrip().startswith("| "):
            return i - 1
        j = 0
        while j < len(ln):
            c = ln[j]
            if c in "([{⟨⦃":
                depth += 1
            elif c in ")]}⟩⦄":
                depth = max(0, depth - 1)
            elif depth == 0 and re.match(r"(?<![\w.'])(let|have)\s", ln[j:]) and \
                    (j == 0 or not (ln[j - 1].isalnum() or ln[j - 1] in "_.'")):
                lets += 1
            elif depth == 0 and ln.startswith(":=", j):
                if lets == 0:
                    return i
                lets -= 1
            j += 1
    return len(lines) - 1


def lean_file_stats(path, rel):
    """Per-file counts and the qualified names of its theorems."""
    text = strip_comments_keep_lines(open(path, encoding="utf-8").read())
    protocols = rel.startswith("verify/protocols/")
    st = dict(definition_lines=0, theorem_statement_lines=0, proof_lines=0,
              other_lines=0, theorems=0, examples=0,
              sorry=len(re.findall(r"\bsorry\b", text)),
              native_decide=len(re.findall(r"\bnative_decide\b", text)))
    quals, ns = [], []
    blocks, cur, pending = [], None, []   # cur = [kind, lines]
    for ln in text.split("\n"):
        if not ln.strip():
            continue
        if ln[0] not in " \t":
            m = _HEAD_RE.match(ln)
            if ln.startswith("@[") and _ATTR_ONLY.match(ln.rstrip() + " "):
                pending.append(ln)
                continue
            if m:
                kind = {"lemma": "theorem"}.get(m.group(1), m.group(1))
                kind = kind if kind in ("theorem", "example", "prove_correct") else "def"
                cur = [kind, pending + [ln]]
                blocks.append(cur)
                pending = []
                if kind == "theorem":
                    nm = _NAME_RE.match(m.group(2))
                    if nm:
                        n = nm.group(1)
                        quals.append(n[len("_root_."):] if n.startswith("_root_.")
                                     else ".".join([x for e in ns for x in e] + [n]))
                continue
            if protocols and _VEIL_RE.match(ln):
                cur = ["def", pending + [ln]]
                blocks.append(cur)
                pending = []
                continue
            o = _OTHER_RE.match(ln)
            if o:
                w = ln.split()
                if w[0] == "namespace" and len(w) > 1:
                    ns.append(w[1].split("."))
                elif w[0] == "section":
                    ns.append([])
                elif w[0] == "end" and ns:
                    ns.pop()
                cur = ["other", pending + [ln]]
                blocks.append(cur)
                pending = []
                continue
        if cur is None:
            cur = ["other", []]
            blocks.append(cur)
        cur[1].append(ln)
    if pending:
        blocks.append(["other", pending])
    for kind, lines in blocks:
        if kind == "def":
            st["definition_lines"] += len(lines)
        elif kind == "other":
            st["other_lines"] += len(lines)
        elif kind == "prove_correct":
            st["proof_lines"] += len(lines)
            st["theorems"] += 1
        else:
            k = _statement_end(lines) + 1
            st["theorem_statement_lines"] += k
            st["proof_lines"] += len(lines) - k
            st["theorems" if kind == "theorem" else "examples"] += 1
    return st, quals


def parse_axiom_audit(path):
    """[(qualified theorem, [axioms])] from the committed audit."""
    t = open(path, encoding="utf-8").read()
    out = []
    for m in re.finditer(r"^'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",
                         t, re.M | re.S):
        axs = [a.strip() for a in (m.group(2) or "").split(",") if a.strip()]
        out.append((m.group(1), axs))
    return out


STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STAT_KEYS = ["files", "statement_lines", "definition_lines", "theorem_statement_lines",
             "proof_lines", "other_lines", "theorems", "examples", "sorry", "native_decide"]


def lean_stats(matrix_sorry):
    files = []
    for top in ("lean/Evm", "verify/velvet-slots", "verify/protocols"):
        for p in glob.glob(os.path.join(REPO, top, "**", "*.lean"), recursive=True):
            if "/.lake/" not in p:
                files.append(p)
    files += glob.glob(os.path.join(REPO, "lean", "*.lean"))
    comps = {c[0]: dict(id=c[0], title=c[1], paths=c[3].split(), link=GH_TREE + c[2],
                        **{k: 0 for k in STAT_KEYS},
                        axioms=dict(audited=0, standard_only=0, native_decide=0, other=0))
             for c in COMPONENTS}
    owner, unassigned, evm_sorry = {}, [], 0
    for p in sorted(set(files)):
        rel = os.path.relpath(p, REPO).replace(os.sep, "/")
        cid = next((c[0] for c in COMPONENTS if _claims(rel, c[3])), None)
        if cid is None:
            unassigned.append(rel)
            continue
        st, quals = lean_file_stats(p, rel)
        if rel.startswith("lean/Evm/"):
            evm_sorry += st["sorry"]
        c = comps[cid]
        c["files"] += 1
        for k, v in st.items():
            c[k] += v
        for q in quals:
            owner.setdefault(q, cid)
        if rel == "verify/velvet-slots/Slots/Axioms.lean":
            n = len(re.findall(r"^#print axioms", open(p).read(), re.M))
            c["axioms"]["audited"] += n
            c["axioms"]["standard_only"] += n
        if rel.startswith("verify/protocols/EitaVeil/"):
            src = strip_comments(open(p).read())
            n = len(re.findall(r"^(?:#print axioms|report_axioms)\b", src, re.M))
            c["axioms"]["audited"] += n
            c["axioms"]["standard_only"] += n
            c.setdefault("veil", dict(models=0, written_clauses=0))
            c["veil"]["models"] += len(re.findall(r"^veil module\b", src, re.M))
            c["veil"]["written_clauses"] += len(re.findall(r"^\s*(?:invariant|safety)\s*\[", src, re.M))
    if unassigned:
        sys.exit("lean-stats: no component claims " + ", ".join(unassigned)
                 + " (assign it in COMPONENTS, scripts/refinement_coverage.py)")
    if evm_sorry != matrix_sorry:
        sys.exit(f"lean-stats: lean/Evm sorry {evm_sorry} != matrix {matrix_sorry}")
    unmapped = []
    for name, axs in parse_axiom_audit(os.path.join(REPO, "scripts", "generated",
                                                    "axiom-audit.txt")):
        cid = owner.get(name)
        if cid is None:
            unmapped.append(name)
            continue
        a = comps[cid]["axioms"]
        a["audited"] += 1
        if all(x in STANDARD_AXIOMS for x in axs):
            a["standard_only"] += 1
        elif all(x in STANDARD_AXIOMS or "._native.native_decide." in x for x in axs):
            a["native_decide"] += 1
        else:
            a["other"] += 1
    if unmapped:
        sys.exit("lean-stats: audited theorems with no declaring file: " + ", ".join(unmapped))
    rows = [comps[c] for c in PAGE_ORDER]
    for r in rows:
        r["statement_lines"] = r["definition_lines"] + r["theorem_statement_lines"]
    claim = [r for r in rows if r["id"] != "tooling"]   # tools are not part of the claim
    total = {k: sum(r[k] for r in claim) for k in STAT_KEYS}
    total["axioms"] = {k: sum(r["axioms"][k] for r in claim)
                       for k in ("audited", "standard_only", "native_decide", "other")}
    readme = os.path.join(REPO, "verify", "protocols", "README.md")
    if "veil" in comps["protocols"] and os.path.exists(readme):
        # the measured results, quoted from the README's model table
        comps["protocols"]["veil"]["readme_results"] = {
            m.group(1): m.group(2).strip()
            for m in re.finditer(r"^\| `(\w+)` \|[^|\n]*\|([^|\n]*)\|\s*$",
                                 open(readme).read(), re.M)}
    tc = open(os.path.join(REPO, "lean", "lean-toolchain")).read().strip()
    return dict(
        lean_toolchain=tc, rules=STATS_RULES, components=rows, total=total,
        reconciliation=dict(
            sorry_lean_evm=evm_sorry, sorry_coverage_matrix=matrix_sorry,
            sorry_outside_lean_evm=sum(r["sorry"] for r in rows) - evm_sorry,
            axiom_audit_entries=total["axioms"]["audited"]
            - comps["slots"]["axioms"]["audited"] - comps["protocols"]["axioms"]["audited"]))


def stats_markdown(d):
    """docs for the stats: the table, the rules, the reconciliation (deterministic)."""
    n = "{:,}".format
    t, rows = d["total"], d["components"]
    claim = [r for r in rows if r["id"] != "tooling"]
    tools = [r for r in rows if r["id"] == "tooling"]

    def ax(a):
        if not a["audited"]:
            return "—"
        return (f"{a['audited']}: {a['standard_only']} standard"
                + (f", {a['native_decide']} with `native_decide`" if a["native_decide"] else ""))

    def line(r, name):
        th = ("— (" + n(r["veil"]["models"]) + " models)") if "veil" in r else n(r["theorems"])
        return (f"| {name} | {n(r['statement_lines'])} ({n(r['definition_lines'])} + "
                f"{n(r['theorem_statement_lines'])}) | {n(r['proof_lines'])} | {th} | "
                f"{r['sorry']} | {n(r['native_decide'])} | {ax(r['axioms'])} |")

    def comp(r):
        return (f"[{r['title']}]({r['link']})<br>"
                + ", ".join(f"`{p}`" for p in r["paths"]))
    rec = d["reconciliation"]
    out = ["# Verification statistics", "",
           "GENERATED by `scripts/refinement_coverage.py --stats-md` — do not edit by hand;",
           "`scripts/verify-coverage.sh` regenerates it in CI and fails on drift. Lean "
           + d["lean_toolchain"].split(":")[-1] + ". Overview: [`docs/VERIFIED.md`]"
           "(../../docs/VERIFIED.md).", "",
           "Statement lines are what a reader has to trust: the theorem statements and the "
           "definitions they rely on (shown as definitions + theorem statements). Proof lines "
           "are machine-checked. The axiom column covers the audited theorems only: "
           f"{n(t['axioms']['audited'])} of the {n(t['theorems'])} theorems.", "",
           "| Component | Statement lines (definitions + theorem statements) | Proof lines "
           "| Theorems | `sorry` | `native_decide` | Axioms (audited theorems only: "
           f"{n(t['axioms']['audited'])} of {n(t['theorems'])}) |",
           "|---|---:|---:|---:|---:|---:|---|"]
    out += [line(r, comp(r)) for r in claim]
    out.append(line(t, "**Total**"))
    out += ["", "Tools, not part of the claim and not in the totals:", "",
            "| Component | Statement lines | Proof lines | Theorems | `sorry` | `native_decide` "
            "| Axioms |", "|---|---:|---:|---:|---:|---:|---|"]
    out += [line(r, comp(r)) for r in tools]
    out += ["", "`native_decide` trusts the Lean compiler's evaluation of a decision "
            "procedure (an extra axiom per use): see "
            "[`docs/trusted-surface.md`](../../docs/trusted-surface.md#native_decide).", ""]
    v = next((r["veil"] for r in rows if "veil" in r), None)
    if v:
        out += ["**State-layer protocols (Veil).** " + rules_text(d, "veil")
                + f" {v['models']} models, {v['written_clauses']} written clauses. Results "
                "(quoted from `verify/protocols/README.md`):", ""]
        out += [f"- `{k}`: {val}" for k, val in v.get("readme_results", {}).items()]
        out.append("")
    out += ["## Counting rules", ""]
    out += [f"- **{k}**: {rules_text(d, k)}" for k in d["rules"] if k != "veil"]
    sor = ", ".join(f"{r['title'].split(' (')[0]} {r['sorry']}" for r in rows if r["sorry"])
    ex = sum(r["examples"] for r in rows)
    out += ["", "## Reconciliation", "",
            f"- `sorry`: {rec['sorry_lean_evm']} in `lean/Evm`, equal to the "
            f"{rec['sorry_coverage_matrix']} of `scripts/generated/refinement-coverage.md` "
            f"(the generator fails otherwise); {rec['sorry_outside_lean_evm']} elsewhere. "
            f"By component: {sor}.",
            f"- Axioms: all {rec['axiom_audit_entries']} entries of "
            "`scripts/generated/axiom-audit.txt` map to their declaring file (the generator "
            "fails otherwise); the Velvet and Veil rows count their own gates' checks.",
            f"- Theorems: {n(t['theorems'])} in the claim rows, plus "
            f"{n(sum(r['theorems'] for r in tools))} in the tools; {n(ex)} `example` blocks "
            "are counted as statement/proof lines but not as theorems.",
            f"- Files: {n(t['files'])} in the claim rows, "
            f"{n(sum(r['files'] for r in tools))} tools; other lines (imports, namespaces, "
            f"`#` commands): {n(t['other_lines'])}.", ""]
    return "\n".join(out)


def rules_text(d, k):
    return d["rules"][k][0].upper() + d["rules"][k][1:] + "." if k == "veil" \
        else d["rules"][k] + "."


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
        ("projection of a bound variable", "t",
         """ (k : Nat) (tx : Tx) :
    Evm.Fake.Tx.invalid k tx = none →
    InitcodeWithinCap tx.data.size""", "InitcodeWithinCap", True),
        ("projection of a constant", "t",
         """ (k : Nat) :
    Evm.Fake.Tx.invalid k = none →
    InitcodeWithinCap Evm.Bytes.empty.size""", "InitcodeWithinCap", False),
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

    # lean-stats line classification
    import tempfile as _tf
    src = """import Foo
namespace A.B
/-- doc
spanning -/
@[simp]
theorem t1 (x : Nat) :
    let y := x  -- a let in the statement
    y = x := by
  intro y
  rfl
def d : Nat := 1
  -- comment only
theorem t2 : ∀ n : Nat, n = n
  | 0 => rfl
  | _ + 1 => rfl
example : 1 = 1 := rfl
end A.B
theorem _root_.C.t3 : True := trivial
"""
    with _tf.NamedTemporaryFile("w", suffix=".lean", delete=False) as fh:
        fh.write(src)
    st, quals = lean_file_stats(fh.name, "lean/Evm/X.lean")
    os.unlink(fh.name)
    check("stats: statement lines (attr + let-binder + pattern theorem + one-liners)",
          st["theorem_statement_lines"] == 4 + 1 + 1 + 1)
    check("stats: proof lines", st["proof_lines"] == 2 + 2)
    check("stats: definition / other lines",
          st["definition_lines"] == 1 and st["other_lines"] == 3)
    check("stats: theorems / examples", st["theorems"] == 3 and st["examples"] == 1)
    check("stats: qualified names", quals == ["A.B.t1", "A.B.t2", "C.t3"])

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
