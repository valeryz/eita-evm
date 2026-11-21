#!/usr/bin/env python3
"""factlog.py — the one Python reader of Eita's fact log (docs/fact-log.md); the Lisp one is
src/factlog/format.lisp.

Every Python consumer (status pages, gates, maintenance and crash-test scripts) reads the
log through this module, so the layout, the footer and the commit protocol are decided in
one place:

  <dir>/<table>/<lo>-<hi>.fct         rows: columnar groups, then (storage_diff,
                                      account_diff) the history index section
  <dir>/<table>/<lo>-<hi>.sexp[.gz]   the text form (pre-cutover logs; read, never written)
  <dir>/<table>/<lo>-<hi>.sealed      the footer: rows, first/last/min/max block, file
                                      digest (:bytes :fnv), :content (hash of the rows),
                                      :index (offset of the index section), bloom params
  <dir>/<table>/blooms.idx            the top-level index: every sealed shard's Bloom
                                      filter (a cache rebuilt by `factlog.py <dir> index`)
  <dir>/committed                     the highest block whose rows are all in the files
  <dir>/anchors.sexp, rewrites.sexp   root-check verdicts; rewritten-range verdicts

The binary layout is lean/Evm/FactLog/Format.lean and History.lean; the column types and
constants come from scripts/generated/factlog_schema.py, emitted from them. A range is
COMPLETE when its footer says first_block = lo and last_block = hi. Rows of a block are
consumable once `committed` >= block (a lagging marker is safe; the rows of a block above
it may be half written). The row model is one tuple per row, typed:

  block        (block, timestamp, coinbase, base_fee, gas_used, gas_limit, prev_randao)
  tx           (block, tx, hash, from, to|None, value, type, gas_used, status, egp)
  call         (block, tx, frame, parent, depth, kind, from, to, value, selector,
                input_len, gas, gas_used, status)
  log          (block, tx, log_index, addr, topics: tuple[int], data: bytes)
  transfer     (block, tx, kind, depth, from, to, value)
  storage_diff (block, tx, addr, slot, pre, post)
  account_diff (block, tx, addr, nonce_pre, nonce_post, bal_pre, bal_post, code_pre, code_post)

Integers are Python ints (addresses and hashes included); `tx` is -1 for pre-block
system effects and 10**9 for post-block ones (block-system.lisp).

State at a block is a lookup, not a replay: state_at(d, "storage_diff", (addr, slot), N)
walks the shards' history indexes (History.lean `lookup`, proved equal to the fold).

CLI:  factlog.py <dir> status
      factlog.py <dir> rows <table> [--block B | --lo L --hi H]     rows as the writer prints them
      factlog.py <dir> footer <table> <lo>
      factlog.py <dir> state <table> <addr> [<slot>] <block>          value at the end of <block>
      factlog.py <dir> index [<table>]                                 (re)build blooms.idx
      factlog.py <dir> vectors <factlog-vectors.sexp>                  decode the Lean-emitted vectors
"""
import array, bisect, ctypes, ctypes.util, gzip, os, re, struct, sys, time
from collections import namedtuple

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "generated"))
import factlog_schema as schema

SHARD = 1000
TABLES = tuple(schema.TABLES)
FORMS = (".fct", ".sexp", ".sexp.gz")               # rows files, in the order a lookup prefers them
INDEXED = schema.INDEXED

Shard = namedtuple("Shard", "lo hi path sealed")    # path: the rows file (any form) or None


def range_lo(block, shard=SHARD):
    return block // shard * shard


def shard_name(lo, shard=SHARD):
    return f"{lo}-{lo + shard - 1}"


def rows_path(d, table, lo, shard=SHARD):
    """The rows file of TABLE's range starting at LO in whichever form exists, else None."""
    base = os.path.join(d, table, shard_name(lo, shard))
    for ext in FORMS:
        if os.path.exists(base + ext):
            return base + ext
    return None


def sealed_path(d, table, lo, shard=SHARD):
    return os.path.join(d, table, shard_name(lo, shard) + ".sealed")


_NAME = re.compile(r"^(\d+)-(\d+)\.(fct|sexp|sexp\.gz|sealed)$")


def shards(d, table):
    """Every range of TABLE on disk, sorted: (lo, hi, rows path or None, footer path or None)."""
    found = {}
    try:
        names = os.listdir(os.path.join(d, table))
    except OSError:
        return []
    for nm in names:
        m = _NAME.match(nm)
        if not m:
            continue
        key = (int(m.group(1)), int(m.group(2)))
        e = found.setdefault(key, {})
        p = os.path.join(d, table, nm)
        if m.group(3) == "sealed":
            e["sealed"] = p
        elif "rows" not in e or FORMS.index("." + m.group(3)) < FORMS.index("." + e["form"]):
            e["rows"] = p; e["form"] = m.group(3)
    return [Shard(lo, hi, e.get("rows"), e.get("sealed")) for (lo, hi), e in sorted(found.items())]


# ---- the small s-expressions beside the rows: footers, anchors, rewrites -----------------

def parse_sexp(text):
    """Ints, strings, NIL -> None, T -> True, :keywords/symbols -> lower-case str, lists ->
    list, `(a . b)` -> [a, b]. Enough for every control file the writer prints."""
    toks = re.findall(r'\(|\)|"[^"]*"|[^\s()]+', text)
    pos = 0

    def node():
        nonlocal pos
        t = toks[pos]; pos += 1
        if t == "(":
            out = []
            while toks[pos] != ")":
                if toks[pos] == ".":
                    pos += 1; continue
                out.append(node())
            pos += 1
            return out
        if t.startswith('"'):
            return t[1:-1]
        if re.fullmatch(r"-?\d+", t):
            return int(t)
        if t == "NIL":
            return None
        if t == "T":
            return True
        return t.lower()
    return node()


def footer(path):
    """A `.sealed` footer (or a `.at-N` prefix record) as a dict with lower-case keys:
    kind, lo, hi, rows, first_block, last_block, min_block, max_block, bytes, fnv, version,
    versions, content, index, bloom_bits, bloom_k, keys. None when absent or torn."""
    try:
        with open(path) as fh:
            lst = parse_sexp(fh.read())
    except (OSError, IndexError, ValueError):
        return None
    if not isinstance(lst, list) or len(lst) % 2:
        return None
    return {str(k).lstrip(":").replace("-", "_"): v for k, v in zip(lst[::2], lst[1::2])}


def complete(ft, lo, hi):
    """Does footer FT say the range [lo, hi] is covered entirely? Block 0 is the genesis, which
    no replay runs: a from-genesis log's first range starts at block 1 (format.lisp, the same)."""
    return bool(ft) and ft.get("first_block") in (lo, max(lo, 1)) and ft.get("last_block") == hi


def top_sealed(d, table="block"):
    """The highest block any sealed range of TABLE ends at, 0 when none."""
    return max([s.hi for s in shards(d, table) if s.sealed] or [0])


def committed(d, strict=False):
    """The frontier marker: every row of a block <= it is in the files. None when absent;
    with STRICT a torn or non-numeric marker raises ValueError (invariant I5)."""
    try:
        with open(os.path.join(d, "committed"), "rb") as fh:
            txt = fh.read()
    except OSError:
        return None
    if strict and not re.fullmatch(rb"\d+\n", txt):
        raise ValueError(f"committed marker is not a number: {txt[:40]!r}")
    try:
        return int(txt.strip())
    except ValueError:
        if strict:
            raise
        return None


def anchors(d):
    """[(block, ok, content_hash or None, state_root)] from anchors.sexp in file order (the
    root is the header's, 0x hex); a torn line is skipped. Whether a verdict can be resumed
    from is recovery.lisp's decision."""
    out = []
    try:
        with open(os.path.join(d, "anchors.sexp"), "rb") as fh:
            lines = fh.read().split(b"\n")
    except OSError:
        return out
    for ln in lines:
        m = re.fullmatch(rb'\((\d+) "([^"]*)" (?:"([^"]*)"|NIL) (T|NIL)(?: "([^"]*)")?\)\x00*', ln)
        if m:
            out.append((int(m.group(1)), m.group(4) == b"T", m.group(5).decode() if m.group(5) else None,
                        m.group(2).decode()))
    return out


def rewrites(d):
    """[(table, lo, hi, identical)] from rewrites.sexp (`factlog-record-rewrite!`): identical
    is True, False, or None when the replaced rows carried no digest to compare against."""
    out = []
    try:
        with open(os.path.join(d, "rewrites.sexp"), "rb") as fh:
            lines = fh.read().split(b"\n")
    except OSError:
        return out
    for ln in lines:
        m = re.match(rb"^\(:KIND :?(\S+) :LO (\d+) :HI (\d+) :IDENTICAL (T|NIL|:UNKNOWN)", ln)
        if not m:
            continue
        v = m.group(4)
        same = None if (v == b":UNKNOWN" or b":OLD-FNV NIL" in ln) else v == b"T"
        out.append((m.group(1).decode().lower(), int(m.group(2)), int(m.group(3)), same))
    return out


# ---- rows: the text form ---------------------------------------------------------------------

_LOG = re.compile(rb'\((\d+) (-?\d+) (\d+) (\d+) \(([^)]*)\) "([0-9a-f]*)"\)')


def _atom(f):
    return None if f == b"NIL" else int(f) if f.lstrip(b"-").isdigit() else f.decode("latin-1")


def parse_row(table, line):
    """One text row (bytes, with or without the newline) as its typed tuple, or None when
    the line is not a complete row (a torn tail)."""
    line = line.strip()
    if not line.startswith(b"(") or not line.endswith(b")"):
        return None
    if table == "log":
        m = _LOG.match(line)
        if not m:
            return None
        return (int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4)),
                tuple(int(t) for t in m.group(5).split()), bytes.fromhex(m.group(6).decode()))
    try:
        return tuple(_atom(f) for f in line[1:-1].split())
    except ValueError:
        return None


def format_row(table, row):
    """The row as the text writer printed it (one line, no newline): the inverse of parse_row,
    and the binary->text direction for debugging."""
    def atom(v):
        if v is None:
            return "NIL"
        if isinstance(v, bytes):
            return '"' + v.hex() + '"'
        if isinstance(v, tuple):
            return "(" + " ".join(str(x) for x in v) + ")"
        return str(v)
    return "(" + " ".join(atom(v) for v in row) + ")"


def _open_rows(path):
    return gzip.open(path, "rb") if path.endswith(".gz") else open(path, "rb")


def iter_lines(path):
    """The complete lines (bytes, no newline) of one text rows file, in file order; a torn
    last line — no newline after it — is not one of them."""
    with _open_rows(path) as fh:
        data = fh.read()
    return data.split(b"\n")[:-1]


# ---- rows: the binary form (Format.lean) ----------------------------------------------------

_WIDTH = {"u8": 1, "u16": 2, "u32": 4, "u64": 8, "i64": 8, "addr": 20, "optaddr": 21, "optu64": 9, "u256": 32}
_OPTIONAL = ("optaddr", "optu64")


def cols_at(table, k):
    """The column types a group (or row) of K columns of TABLE is read with (Format.lean
    colsAt): the table's first K, when every column past K is optional; None otherwise. A
    table only gains optional columns at its end, so an older group is narrower and its
    rows have fewer fields (block rows without the blob-gas columns: 7)."""
    types = schema.TABLES[table]
    return types[:k] if k <= len(types) and all(t in _OPTIONAL for t in types[k:]) else None
_zstd = None


def _libzstd():
    """libzstd through ctypes: no Python package to install (the system library is enough)."""
    global _zstd
    if _zstd is None:
        for cand in (ctypes.util.find_library("zstd"), "/opt/homebrew/lib/libzstd.dylib", "libzstd.so.1", "libzstd.dylib"):
            if not cand:
                continue
            try:
                _zstd = ctypes.CDLL(cand); break
            except OSError:
                continue
        if _zstd is None:
            raise RuntimeError("libzstd not found (brew install zstd / apt install libzstd1)")
        _zstd.ZSTD_decompress.restype = ctypes.c_size_t
        _zstd.ZSTD_decompress.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_void_p, ctypes.c_size_t]
        _zstd.ZSTD_isError.restype = ctypes.c_uint
        _zstd.ZSTD_isError.argtypes = [ctypes.c_size_t]
    return _zstd


def zstd_decompress(payload, raw_len):
    z = _libzstd()
    out = ctypes.create_string_buffer(raw_len)
    src = (ctypes.c_char * len(payload)).from_buffer_copy(payload)
    n = z.ZSTD_decompress(out, raw_len, src, len(payload))
    if z.ZSTD_isError(n) or n != raw_len:
        raise ValueError(f"zstd: bad column payload ({n} of {raw_len} bytes)")
    return out.raw


def _decode_column(t, raw, n):
    """The N values of one column from its raw bytes (Format.lean decodeColumn)."""
    if t in _WIDTH:
        w = _WIDTH[t]
        if len(raw) != n * w:
            raise ValueError(f"column {t}: {len(raw)} bytes for {n} rows")
        if t == "i64":
            return list(struct.unpack(f"<{n}q", raw))
        if t == "u8":
            return list(raw)
        if t in ("u16", "u32", "u64"):
            return list(struct.unpack("<%d%s" % (n, {"u16": "H", "u32": "I", "u64": "Q"}[t]), raw))
        if t in _OPTIONAL:
            return [None if raw[i] == 0 else int.from_bytes(raw[i + 1:i + w], "little") for i in range(0, len(raw), w)]
        return [int.from_bytes(raw[i:i + w], "little") for i in range(0, len(raw), w)]
    out, off = [], 0
    if t == "u256list":
        for _ in range(n):
            k = raw[off]; off += 1
            out.append(tuple(int.from_bytes(raw[off + 32 * j:off + 32 * j + 32], "little") for j in range(k)))
            off += 32 * k
    elif t == "bytes":
        for _ in range(n):
            ln = int.from_bytes(raw[off:off + 4], "little"); off += 4
            out.append(bytes(raw[off:off + ln])); off += ln
    else:
        raise ValueError(f"unknown column type {t}")
    if off != len(raw):
        raise ValueError(f"column {t}: {len(raw) - off} trailing bytes")
    return out


def decode_group(buf, off, table, cols=None):
    """The group at OFF in BUF (Format.lean decodeGroupAny): (columns, next_off) with columns a
    dict {i: values} for the requested column positions the group has (all when COLS is
    None; an older group lacks the columns its table gained since, cols_at). None when BUF holds no complete group
    there (a torn tail); ("index", next_off) at the history index section."""
    if len(buf) < off + 4:
        return None
    magic = bytes(buf[off:off + 4])
    if magic == schema.INDEX_MAGIC:
        if len(buf) < off + 8:
            return None
        ln = int.from_bytes(buf[off + 4:off + 8], "little")
        return ("index", off + ln) if len(buf) >= off + ln else None
    if magic != schema.MAGIC:
        raise ValueError(f"not a fact-log group at offset {off}: {magic!r}")
    if len(buf) < off + schema.HEADER_FIXED:
        return None
    total, n = struct.unpack_from("<II", buf, off + 4)
    if len(buf) < off + total:
        return None
    ncols = buf[off + 28]
    types = cols_at(table, ncols)
    if types is None:
        raise ValueError(f"{table}: group has {ncols} columns, the table {len(schema.TABLES[table])}")
    dir_off = off + schema.HEADER_FIXED
    pay = dir_off + schema.DIR_ENTRY * ncols
    out = {}
    for i, t in enumerate(types):
        codec, raw_len, enc_len = struct.unpack_from("<BII", buf, dir_off + schema.DIR_ENTRY * i)
        if cols is None or i in cols:
            payload = buf[pay:pay + enc_len]
            raw = payload if codec == schema.CODEC_RAW else zstd_decompress(payload, raw_len)
            if len(raw) != raw_len:
                raise ValueError(f"{table} column {i}: {len(raw)} raw bytes, directory says {raw_len}")
            out[i] = _decode_column(t, raw, n)
        pay += enc_len
    if pay != off + total:
        raise ValueError(f"{table}: group payloads end at {pay}, header says {off + total}")
    return out, off + total


def iter_groups(buf, table, off=0, cols=None):
    """Every complete group's columns from OFF on; stops at the index section or a torn tail.
    Yields (columns, group_end)."""
    while True:
        g = decode_group(buf, off, table, cols)
        if g is None or g[0] == "index":
            return
        yield g
        off = g[1]


def _rows_of(columns):
    """Rows (tuples, as wide as the group) from a group decoded whole."""
    return list(zip(*(columns[i] for i in range(len(columns)))))


def iter_rows(path, table):
    """The complete rows of one rows file (either form), in file order."""
    if path.endswith(".fct"):
        with open(path, "rb") as fh:
            buf = fh.read()
        for columns, _ in iter_groups(buf, table):
            yield from _rows_of(columns)
        return
    for ln in iter_lines(path):
        r = parse_row(table, ln)
        if r is not None:
            yield r


def rows(d, table, lo=None, hi=None):
    """Every row of TABLE with lo <= block <= hi (either bound optional), in shard order
    then file order — which is (block, tx, ordinal) order."""
    for s in shards(d, table):
        if s.path is None or (lo is not None and s.hi < lo) or (hi is not None and s.lo > hi):
            continue
        for r in iter_rows(s.path, table):
            if (lo is None or r[0] >= lo) and (hi is None or r[0] <= hi):
                yield r


# ---- the canonical row bytes and the content hash (Format.lean encodeRow, contentHash) ----

def encode_value(t, v):
    if t in ("u8", "u16", "u32", "u64", "addr", "u256"):
        return v.to_bytes(_WIDTH[t], "little")
    if t == "i64":
        return struct.pack("<q", v)
    if t in _OPTIONAL:
        w = _WIDTH[t] - 1
        return b"\x00" + bytes(w) if v is None else b"\x01" + v.to_bytes(w, "little")
    if t == "u256list":
        return bytes([len(v)]) + b"".join(x.to_bytes(32, "little") for x in v)
    if t == "bytes":
        return len(v).to_bytes(4, "little") + v
    raise ValueError(t)


def fnv1a(data, h=0xcbf29ce484222325):
    for b in data:
        h = ((h ^ b) * 0x100000001b3) & 0xffffffffffffffff
    return h


def content_hash(table, rows_iter):
    """FNV-1a 64 over the canonical row bytes, as hex: the footer's :content. A row's bytes are
    its own fields (Format.lean encodeRowAt): an older, narrower row hashes as written."""
    types = schema.TABLES[table]
    h = 0xcbf29ce484222325
    for r in rows_iter:
        h = fnv1a(b"".join(encode_value(t, v) for t, v in zip(types, r)), h)
    return "%016x" % h


# ---- the history index (History.lean) ---------------------------------------------------------

def key_bytes(table, *key):
    """The canonical key: big-endian address, then (storage) big-endian slot."""
    return b"".join(k.to_bytes(32 if i else 20, "big") for i, k in enumerate(key))


def bloom_positions(m, k, key):
    h = fnv1a(key)
    h1, h2 = h & 0xffffffff, (h >> 32) | 1
    return [(h1 + i * h2) % m for i in range(k)]


def bloom_may_contain(bloom, k, key):
    m = len(bloom) * 8
    return all(bloom[p >> 3] & (1 << (p & 7)) for p in bloom_positions(m, k, key))


def read_index(buf, off):
    """The index section at OFF: (perm: array('I'), bloom_k, bloom: bytes)."""
    if bytes(buf[off:off + 4]) != schema.INDEX_MAGIC:
        raise ValueError(f"no index section at {off}")
    _tot, n = struct.unpack_from("<II", buf, off + 4)
    k = buf[off + 12]
    bl = int.from_bytes(buf[off + 13:off + 17], "little")
    p0 = off + schema.INDEX_HEADER
    perm = array.array("I"); perm.frombytes(bytes(buf[p0:p0 + 4 * n]))
    if sys.byteorder != "little":
        perm.byteswap()
    bloom = bytes(buf[p0 + 4 * n:p0 + 4 * n + bl])
    return perm, k, bloom


_KEYCOLS = {"storage_diff": (2, 3), "account_diff": (2,)}
_VALCOLS = {"storage_diff": ((4,), (5,)), "account_diff": ((3, 5, 7), (4, 6, 8))}


def _shard_changes(path, ft, table, key):
    """The changes of KEY in one binary shard, in file order: [(block, tx, pre, post)], pre
    and post being the value (storage) or the (nonce, balance, code_hash) triple (account).
    None when the shard has no index (a text shard: the caller folds instead)."""
    if not path.endswith(".fct") or not ft or ft.get("index") is None:
        return None
    with open(path, "rb") as fh:
        buf = fh.read()
    # trust the index only on bytes that match the footer's digest: a corrupt filter would
    # otherwise answer "never changed" silently (a footer without a digest is taken at its word)
    if ft.get("fnv") and (len(buf) != ft["bytes"] or "%016x" % fnv1a(buf) != ft["fnv"]):
        raise ValueError(f"{path} does not match its footer's digest: refusing its index")
    perm, k, bloom = read_index(buf, ft["index"])
    kb = key_bytes(table, *key)
    if not bloom_may_contain(bloom, k, kb):
        return []
    kc = _KEYCOLS[table]; pre_c, post_c = _VALCOLS[table]
    want = set((0, 1) + kc + pre_c + post_c)
    cols = {i: [] for i in want}
    for columns, _ in iter_groups(buf, table, cols=want):
        for i in want:
            cols[i].extend(columns[i])
    keys = cols[kc[0]] if len(kc) == 1 else list(zip(cols[kc[0]], cols[kc[1]]))
    want_key = key[0] if len(kc) == 1 else tuple(key)
    # perm sorts positions by key then file order: binary search the key's run
    sorted_keys = _PermKeys(perm, keys)
    lo = bisect.bisect_left(sorted_keys, want_key); hi = bisect.bisect_right(sorted_keys, want_key)
    out = []
    for j in range(lo, hi):
        p = perm[j]
        pre = cols[pre_c[0]][p] if len(pre_c) == 1 else tuple(cols[c][p] for c in pre_c)
        post = cols[post_c[0]][p] if len(post_c) == 1 else tuple(cols[c][p] for c in post_c)
        out.append((cols[0][p], cols[1][p], pre, post))
    return out


class _PermKeys:
    """keys[perm[j]] as a sequence, for bisect."""
    def __init__(self, perm, keys): self.perm = perm; self.keys = keys
    def __len__(self): return len(self.perm)
    def __getitem__(self, j): return self.keys[self.perm[j]]


def _fold_changes(path, table, key):
    """The same list from a text shard, by scanning (the reference the index is checked against)."""
    kc = _KEYCOLS[table]; pre_c, post_c = _VALCOLS[table]
    out = []
    for r in iter_rows(path, table):
        if tuple(r[c] for c in kc) == tuple(key):
            pre = r[pre_c[0]] if len(pre_c) == 1 else tuple(r[c] for c in pre_c)
            post = r[post_c[0]] if len(post_c) == 1 else tuple(r[c] for c in post_c)
            out.append((r[0], r[1], pre, post))
    return out


def blooms_path(d, table):
    return os.path.join(d, table, "blooms.idx")


def read_blooms(d, table):
    """({lo: (k, offset, nbytes)}, end) from blooms.idx, read in place: the 13-byte record headers
    only, the filters stay on disk (`bloom_at`), so memory is one entry per shard however large
    the history; END is where its whole records stop (a torn tail of an interrupted build
    after it). ({}, 0) when absent."""
    out = {}; off = 0
    try:
        fd = os.open(blooms_path(d, table), os.O_RDONLY)
    except OSError:
        return out, off
    try:
        size = os.fstat(fd).st_size
        while off + 13 <= size:
            lo, m = struct.unpack("<QI", os.pread(fd, 12, off)); k = os.pread(fd, 1, off + 12)[0]
            bl = m // 8
            if off + 13 + bl > size:
                break                                  # torn tail of an interrupted build
            out[lo] = (k, off + 13, bl); off += 13 + bl
    finally:
        os.close(fd)
    return out, off


def bloom_at(fd, entry):
    """(k, filter bytes) of a read_blooms ENTRY, from the open blooms.idx FD."""
    k, off, n = entry
    return k, os.pread(fd, n, off)


def build_blooms(d, table):
    """Append every sealed binary shard's Bloom filter not yet in blooms.idx (the one owner of
    that file), one filter in memory at a time; a torn tail is cut first, so the records
    appended after it are readable. Returns the number added."""
    have, end = read_blooms(d, table)
    added = 0
    with open(blooms_path(d, table), "ab") as out:
        out.truncate(end)
        for s in shards(d, table):
            if s.lo in have or not s.sealed or not s.path or not s.path.endswith(".fct"):
                continue
            ft = footer(s.sealed)
            if not ft or ft.get("index") is None:
                continue
            with open(s.path, "rb") as fh:
                fh.seek(ft["index"]); head = fh.read(schema.INDEX_HEADER)
                n = int.from_bytes(head[8:12], "little"); k = head[12]
                bl = int.from_bytes(head[13:17], "little")
                fh.seek(ft["index"] + schema.INDEX_HEADER + 4 * n); bloom = fh.read(bl)
            out.write(struct.pack("<QIB", s.lo, bl * 8, k) + bloom); added += 1
    return added


def state_at(d, table, key, block, use_blooms=True):
    """The value of KEY (an (addr, slot) tuple for storage_diff, (addr,) for account_diff) at
    the end of BLOCK: the last change at or before it gives its post, else the first change
    after it gives its pre (History.lean `lookup`); None when the log never changed the key.
    Text shards are folded; binary shards are looked up through their index, skipping shards
    whose Bloom filter rules the key out (blooms.idx when present, else each footer)."""
    key = tuple(key)
    sh = shards(d, table)
    blooms = read_blooms(d, table)[0] if use_blooms else {}
    fd = os.open(blooms_path(d, table), os.O_RDONLY) if blooms else None
    kb = key_bytes(table, *key)

    def changes(s):
        if s.lo in blooms:
            k, bloom = bloom_at(fd, blooms[s.lo])
            if not bloom_may_contain(bloom, k, kb):
                return []
        if s.path is None:
            return []
        if s.path.endswith(".fct"):
            c = _shard_changes(s.path, footer(s.sealed) if s.sealed else None, table, key)
            if c is not None:
                return c
        return _fold_changes(s.path, table, key)

    try:
        return _lookup(sh, changes, block)
    finally:
        if fd is not None:
            os.close(fd)


def _lookup(sh, changes, block):
    """History.lean `lookup` over the shards SH, CHANGES giving a shard's changes of the key."""
    at = [i for i, s in enumerate(sh) if s.lo <= block]
    here = at[-1] if at else -1
    if here >= 0 and sh[here].hi >= block:          # the shard holding BLOCK
        c = changes(sh[here])
        before = [x for x in c if x[0] <= block]
        if before:
            return before[-1][3]
        if c:
            return c[0][2]
        here -= 1
    for i in range(here, -1, -1):                   # shards wholly before BLOCK: the last change
        c = changes(sh[i])
        if c:
            return c[-1][3]
    for s in sh:                                    # shards wholly after BLOCK: the first change
        if s.lo <= block:
            continue
        c = changes(s)
        if c:
            return c[0][2]
    return None


# ---- following the live shards -------------------------------------------------------------

def first_block_at(d, ts, head):
    """The first block with timestamp >= TS, by bisecting the block shards (one row each)."""
    def first(lo):
        p = rows_path(d, "block", lo)
        if p is None:
            return None
        for r in iter_rows(p, "block"):
            return (r[0], r[1])
        return None
    lo, hi = 0, head // SHARD
    while lo < hi:                                     # first shard whose first block is >= ts
        mid = (lo + hi) // 2; r = first(mid * SHARD)
        if r and r[1] < ts: lo = mid + 1
        else: hi = mid
    # the block is in the shard before that one, or (when the window starts inside the
    # newest shard) in that shard itself
    for s in (max(0, (lo - 1) * SHARD), lo * SHARD):
        p = rows_path(d, "block", s)
        for r in (iter_rows(p, "block") if p else ()):
            if r[1] >= ts:
                return r[0]
    return head


class Tailer:
    """Incremental reader of the live shards. poll() returns {table: [rows]} for the blocks
    that became consumable since the last call: those at or below `committed` (read BEFORE
    the rows, so every row of such a block is already in the files). Absent a marker (an
    older log) the row of the next block is the completeness signal.
    KEEP(table, row) filters rows before they are buffered (e.g. one contract's slots).
    A binary shard is read group by group (a torn group waits for its remaining bytes);
    a text shard line by line."""
    def __init__(self, d, start, tables=TABLES, keep=None):
        self.d = d; self.tables = tuple(tables); self.keep = keep
        self.pos = {k: [range_lo(start), 0, b""] for k in self.tables}
        self.pending = {k: [] for k in self.tables}
        self.complete = start - 1
        self.emitted = start - 1           # highest block ever handed out: never re-emitted

    def _take(self, k, rows):
        for r in rows:
            if self.keep is None or self.keep(k, r):
                self.pending[k].append(r)

    def _split(self, k, path, buf):
        """Complete records off the front of BUF: (rows, remainder)."""
        if path.endswith(".fct"):
            rows, off = [], 0
            while True:
                g = decode_group(buf, off, k)
                if g is None:
                    break
                if g[0] == "index":
                    off = g[1]; continue
                rows.extend(_rows_of(g[0])); off = g[1]
            return rows, buf[off:]
        lines = buf.split(b"\n"); rest = lines.pop()
        return [r for r in (parse_row(k, ln) for ln in lines) if r is not None], rest

    def _read(self, k):
        while True:
            lo, off, buf = self.pos[k]
            p = rows_path(self.d, k, lo)
            if p is None:
                return
            if p.endswith(".gz"):
                # Compacted since we started on it (pre-cutover logs): sealed and immutable, so
                # take the rest whole and roll on. OFF counts bytes of the plain rows taken.
                with gzip.open(p, "rb") as f:
                    data = f.read()
                rows, _ = self._split(k, p[:-3], buf + data[off:]) if off <= len(data) else ([], b"")
                self._take(k, rows)
                self.pos[k] = [lo + SHARD, 0, b""]; continue
            size = os.path.getsize(p)
            if size < off:                      # the replay restarted from an anchor and superseded this shard
                off = 0; buf = b""
                # Rows of this shard still pending (read, not yet folded) are read again from
                # offset 0: drop them, or a block the dead replay had half written is folded
                # twice (live.eita.run counted 5 and 6 extra txs at 26,606,3xx and 26,615,0xx).
                self.pending[k] = [r for r in self.pending[k] if not lo <= r[0] < lo + SHARD]
            with open(p, "rb") as f:
                f.seek(off); chunk = f.read()
            rows, buf = self._split(k, p, buf + chunk); off += len(chunk)
            self._take(k, rows)
            self.pos[k] = [lo, off, buf]
            # Roll forward once this shard is sealed, read to the end, and the next one exists.
            if not chunk and os.path.exists(sealed_path(self.d, k, lo)) and rows_path(self.d, k, lo + SHARD):
                self.pos[k] = [lo + SHARD, 0, b""]; continue
            return

    def poll(self):
        c = committed(self.d)
        for k in self.tables:
            self._read(k)
        if c is not None:
            self.complete = max(self.complete, c)
        elif self.pending.get("block"):
            self.complete = max(self.complete, max(r[0] for r in self.pending["block"]) - 1)
        out = {}
        for k in self.tables:
            keep, take = [], []
            for r in self.pending[k]:
                if r[0] <= self.emitted:
                    continue                                  # re-read after a shard was superseded
                (take if r[0] <= self.complete else keep).append(r)
            self.pending[k] = keep; out[k] = take
        if out.get("block"):
            self.emitted = max(self.emitted, max(r[0] for r in out["block"]))
        return out


# ---- CLI ------------------------------------------------------------------------------------

def _status(d):
    print(f"committed {committed(d)}")
    for t in TABLES:
        sh = shards(d, t)
        if not sh:
            continue
        sealed = [s for s in sh if s.sealed]
        forms = {}
        for s in sh:
            if s.path:
                f = s.path.rsplit("-", 1)[1].split(".", 1)[1]; forms[f] = forms.get(f, 0) + 1
        print(f"{t:13s} {len(sh):6d} ranges  {len(sealed):6d} sealed  {sh[0].lo}..{sh[-1].hi}  "
              + " ".join(f"{v} {k}" for k, v in sorted(forms.items())))
    an = anchors(d)
    print(f"anchors {len(an)} ({sum(1 for _, ok, *_ in an if ok)} verified)")


def check_vectors(path):
    """Decode the Lean-emitted vectors: each table's group must give exactly its rows and
    its content hash; each index section must give its perm and bloom."""
    text = "\n".join(ln for ln in open(path).read().split("\n") if not ln.startswith(";"))
    bad = 0
    for v in parse_sexp("(" + text + ")"):
        d = {str(k).lstrip(":").replace("-", "_"): val for k, val in zip(v[::2], v[1::2])}
        table = d["table"]
        want = [parse_row(table, format_row(table, tuple(
            None if x is None else bytes.fromhex(x) if isinstance(x, str) else tuple(x) if isinstance(x, list) else x
            for x in r)).encode()) for r in d["rows"]]
        buf = bytes.fromhex(d["group"]) + b"\xaa"
        g = decode_group(buf, 0, table)
        got = _rows_of(g[0]) if g else None
        ok = got == want and g[1] == len(buf) - 1
        ok = ok and content_hash(table, want) == d["content"]
        if "index" in d:
            perm, k, bloom = read_index(bytes.fromhex(d["index"]), 0)
            ok = ok and list(perm) == d["perm"] and k == schema.BLOOM_K and bloom.hex() == d["bloom"] \
                and len(bloom) * 8 == d["bloom_bits"]
            kc = _KEYCOLS[table]
            ok = ok and all(bloom_may_contain(bloom, k, key_bytes(table, *(r[c] for c in kc))) for r in want)
        print(f"{table:13s} {'OK' if ok else 'MISMATCH'} ({len(want)} rows)")
        bad += not ok
    return bad


def main(argv):
    if len(argv) < 2:
        sys.exit(__doc__)
    d, cmd = argv[0], argv[1]
    if cmd == "status":
        _status(d)
    elif cmd == "rows":
        table = argv[2]; lo = hi = None
        if "--block" in argv:
            lo = hi = int(argv[argv.index("--block") + 1])
        if "--lo" in argv: lo = int(argv[argv.index("--lo") + 1])
        if "--hi" in argv: hi = int(argv[argv.index("--hi") + 1])
        for r in rows(d, table, lo, hi):
            print(format_row(table, r))
    elif cmd == "footer":
        print(footer(sealed_path(d, argv[2], int(argv[3]))))
    elif cmd == "state":
        table = argv[2]; nums = [int(x, 0) for x in argv[3:]]
        t0 = time.time(); v = state_at(d, table, nums[:-1], nums[-1])
        print(v, f"({(time.time() - t0) * 1000:.1f} ms)")
    elif cmd == "index":
        for t in ([argv[2]] if len(argv) > 2 else INDEXED):
            print(f"{t}: {build_blooms(d, t)} shards added to blooms.idx")
    elif cmd == "vectors":
        sys.exit(1 if check_vectors(argv[2]) else 0)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
