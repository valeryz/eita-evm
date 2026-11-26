#!/usr/bin/env python3
"""tests/factlog-blooms.py — blooms.idx (`scripts/factlog.py <dir> index`) and the lookups through it.

  python3 -I tests/factlog-blooms.py      (or: pytest tests/factlog-blooms.py)

A fact log of one real storage_diff shard (the Lean-emitted vector: a group and its index)
behind many decoy shards whose index sections hold large all-zero filters. The decoys make
blooms.idx far larger than anything a lookup may hold: building it and answering state_at
through it must stay bounded in memory (the filters are read in place, one at a time — a
whole-file read of a full chain's blooms.idx is gigabytes), and the answers must equal the
rows' own and those of the lookup without blooms.idx. Also: a torn tail is cut before the
next build appends; src/factlog/format.lisp's state-at gives the same answers, also bounded.
Exit 1 on a failure.
"""
import os, struct, subprocess, sys, tempfile, tracemalloc

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HERE = os.path.join(ROOT, "scripts")
sys.path.insert(0, HERE)
import factlog

VECTORS = os.path.join(HERE, "generated", "factlog-vectors.sexp")
TABLE = "storage_diff"
DECOYS, BLOOM_BYTES = 1500, 32768           # blooms.idx ~49 MB; a lookup may hold ~1 filter
BOUND = 4 * 1024 * 1024
REAL_LO = 5900000                           # the vector's blocks; the decoys below it


def write_shard(d, lo, data, rows, index_at):
    base = os.path.join(d, TABLE, factlog.shard_name(lo))
    with open(base + ".fct", "wb") as fh:
        fh.write(data)
    with open(base + ".sealed", "w") as fh:
        fh.write(f'(:KIND :STORAGE_DIFF :LO {lo} :HI {lo + factlog.SHARD - 1} :ROWS {len(rows)} '
                 f':FIRST-BLOCK {lo} :LAST-BLOCK {lo + factlog.SHARD - 1} :BYTES {len(data)} '
                 f':INDEX {index_at} :BLOOM-BITS {8 * BLOOM_BYTES} :BLOOM-K 7 :VERSION "v1" :VERSIONS (({lo} . "v1")))')


def make_log(d):
    """The log; the real shard's rows (blocks moved into its range)."""
    os.makedirs(os.path.join(d, TABLE))
    text = "\n".join(ln for ln in open(VECTORS).read().split("\n") if not ln.startswith(";"))
    v = next(m for m in ({str(k).lstrip(":"): x for k, x in zip(v[::2], v[1::2])}
                         for v in factlog.parse_sexp("(" + text + ")")) if m["table"] == TABLE and "index" in m)
    group, index = bytes.fromhex(v["group"]), bytes.fromhex(v["index"])
    rows = factlog._rows_of(factlog.decode_group(group, 0, TABLE)[0])
    # an empty index section (no rows, a zero filter): every key ruled out
    decoy = factlog.schema.INDEX_MAGIC + struct.pack("<IIBI", 17 + BLOOM_BYTES, 0, 7, BLOOM_BYTES) + bytes(BLOOM_BYTES)
    for i in range(DECOYS):
        write_shard(d, REAL_LO - (i + 1) * factlog.SHARD, decoy, [], 0)
    write_shard(d, REAL_LO, group + index, rows, len(group))
    return rows


def expected(rows, key, block):
    ch = [r for r in rows if (r[2], r[3]) == key]
    before = [r for r in ch if r[0] <= block]
    return before[-1][5] if before else (ch[0][4] if ch else None)


def peak(fn):
    tracemalloc.start()
    try:
        out = fn()
        return out, tracemalloc.get_traced_memory()[1]
    finally:
        tracemalloc.stop()


def queries(rows):
    """(key, block) pairs: every key of the real shard at its blocks and around them, and a
    key no shard holds."""
    out = []
    for r in rows:
        out += [((r[2], r[3]), r[0]), ((r[2], r[3]), r[0] - 1), ((r[2], r[3]), REAL_LO + 5000)]
    return out + [((0xdead, 7), REAL_LO + 10)]


def test_build_and_lookup_bounded():
    with tempfile.TemporaryDirectory() as d:
        rows = make_log(d)
        added, mem = peak(lambda: factlog.build_blooms(d, TABLE))
        assert added == DECOYS + 1, added
        size = os.path.getsize(factlog.blooms_path(d, TABLE))
        assert size > 10 * BOUND and mem < BOUND, (size, mem)
        have, end = factlog.read_blooms(d, TABLE)
        assert len(have) == DECOYS + 1 and end == size
        assert factlog.build_blooms(d, TABLE) == 0 and os.path.getsize(factlog.blooms_path(d, TABLE)) == size
        for key, block in queries(rows):
            want = expected(rows, key, block)
            got, mem = peak(lambda: factlog.state_at(d, TABLE, key, block))
            assert got == want == factlog.state_at(d, TABLE, key, block, use_blooms=False), (key, block, got, want)
            assert mem < BOUND, mem


def test_torn_tail_cut_before_append():
    with tempfile.TemporaryDirectory() as d:
        rows = make_log(d)
        factlog.build_blooms(d, TABLE)
        p = factlog.blooms_path(d, TABLE); size = os.path.getsize(p)
        os.truncate(p, size - 1)                         # the last record torn
        have, end = factlog.read_blooms(d, TABLE)
        assert len(have) == DECOYS and end < size - 1, (len(have), end, size)
        assert factlog.build_blooms(d, TABLE) == 1 and os.path.getsize(p) == size
        key, block = queries(rows)[0]
        assert factlog.state_at(d, TABLE, key, block) == expected(rows, key, block)


LISP = r"""
(load (merge-pathnames "factlog/format.lisp" (second sb-ext:*posix-argv*)))
(in-package :eita-factlog)
(let ((dir (third sb-ext:*posix-argv*)))
  (with-open-file (q (fourth sb-ext:*posix-argv*))
    (loop for (addr slot block) = (list (read q nil) (read q nil) (read q nil)) while addr
          do (let ((v (state-at dir :storage_diff (list addr slot) block)))
               (format t "~A~%" (if (eq v :unknown) "None" v)))))
  ;; what the table holds: the bytes it keeps live (not the filters)
  (sb-ext:gc :full t)
  (let* ((u0 (sb-kernel:dynamic-usage)) (tb (read-blooms dir :storage_diff)))
    (sb-ext:gc :full t)
    (format t "held ~D ~D~%" (- (sb-kernel:dynamic-usage) u0) (hash-table-count tb))))
"""


def test_lisp_state_at_same_answers_bounded():
    with tempfile.TemporaryDirectory() as d:
        rows = make_log(d)
        factlog.build_blooms(d, TABLE)
        qs = queries(rows)[:12] + queries(rows)[-1:]
        with open(os.path.join(d, "q"), "w") as fh:
            fh.write("".join(f"{k[0]} {k[1]} {b}\n" for k, b in qs))
        with open(os.path.join(d, "t.lisp"), "w") as fh:
            fh.write(LISP)
        out = subprocess.run(["sbcl", "--script", os.path.join(d, "t.lisp"), os.path.join(ROOT, "src") + "/", d + "/", os.path.join(d, "q")],
                             capture_output=True, text=True, check=True).stdout.split("\n")
        assert out[:len(qs)] == [str(expected(rows, k, b)) for k, b in qs], out
        _, held, n = out[len(qs)].split()
        assert int(n) == DECOYS + 1 and int(held) < BOUND, (held, n)


if __name__ == "__main__":
    bad = 0
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            try:
                fn(); print(f"{name} OK")
            except Exception as e:                       # noqa: BLE001 — report every test
                bad += 1; print(f"{name} FAIL: {e!r}"[:2000])
    sys.exit(1 if bad else 0)
