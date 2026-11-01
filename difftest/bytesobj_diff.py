"""Differential test: Lean model of tuple, list, bytes, bytearray and memoryview
vs. the running CPython.

Usage: python3 difftest/bytesobj_diff.py [--cases N] [--seed S] [--family F]

Each family below supplies `gen_<family>(rng)` and `run_<family>(case)`. Cases
carry "mod": "bytesobj" and a `fn` starting with the family prefix.
"""

import sys

import common


def choose_family():
    """`--family seq|bytes|mem` restricts the run; the option is removed from argv."""
    if "--family" not in sys.argv:
        return None
    i = sys.argv.index("--family")
    family = sys.argv[i + 1]
    del sys.argv[i:i + 2]
    return family


# ===== family seq: tuple and list =====================================


def gen_seq(rng):
    return None


def run_seq(case):
    raise NotImplementedError(case["fn"])


# ===== end of family seq ==============================================


# ===== family bytes: bytes and bytearray ==============================


def gen_bytes(rng):
    return None


def run_bytes(case):
    raise NotImplementedError(case["fn"])


# ===== end of family bytes ============================================


# ===== family mem: memoryview =========================================

import ctypes as _ct
import struct
from array import array

try:
    import _testbuffer as _tb
except ImportError:
    _tb = None

_M = sys.maxsize
_NATIVE = "cbBhHiIlLqQnNfde?P"
_ND_FORMATS = list(_NATIVE) + ["@B", "@i", "@d", "<i", ">h", "=q", "!H", "<d", ">f", "<e", ">?",
                               "2B", "<2h", "3s", "bB", "hb", "2x", "xB", "5p"]
_CAST_FORMATS = list(_NATIVE) * 2 + ["@B", "@i", "@c", "@", "", "x", "BB", "<i", "B\0x", "@B\0",
                                     "\xe9", "s", " B"]
_KEY_INTS = [0, 1, -1, 2, -2, 3, -3, 4, 7, -8, 100, -100, _M, -_M, -_M - 1, _M + 1, 2 ** 64,
             -2 ** 64, 2 ** 100]
_VAL_INTS = [0, 1, -1, 2, 127, 128, -128, -129, 255, 256, 32767, 32768, -32768, -32769, 65535,
             65536, 2 ** 31 - 1, 2 ** 31, -2 ** 31, -2 ** 31 - 1, 2 ** 32 - 1, 2 ** 32, _M, _M + 1,
             -_M - 1, -_M - 2, 2 ** 64 - 1, 2 ** 64, -2 ** 64, 2 ** 100, 2 ** 1024, 2 ** 53 + 1]
_FLOATS = [0.0, -0.0, 1.0, -1.5, 1e-40, 1e39, 1e308, 5e-324, 65504.0, 65520.0, 65519.99,
           6.1e-5, 5.96e-8, 2.98e-8, 1e-10, float("inf"), -float("inf"), float("nan"),
           1.17549435e-38, 3.4028235677973366e+38, 3.4028234e38, 0.1]
_BUF_FLAGS = [0, 1, 4, 5, 8, 9, 12, 13, 24, 25, 28, 29, 56, 57, 60, 88, 92, 152, 156, 280, 281, 284, 285]
_ATTRS = ["obj", "nbytes", "readonly", "itemsize", "format", "ndim", "shape", "strides",
          "suboffsets", "c_contiguous", "f_contiguous", "contiguous"]


def _fbits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def _unfbits(b):
    return struct.unpack("<d", struct.pack("<Q", b))[0]


def _rand_bytes(rng, n):
    mode = rng.randrange(4)
    if mode == 0:
        return [rng.choice([0, 1, 0xff, 0x7f, 0x80]) for _ in range(n)]
    if mode == 1:
        return [rng.randrange(4) for _ in range(n)]
    return [rng.randrange(256) for _ in range(n)]


def _rand_item(rng, c):
    """One element for `struct.pack(fmt)`, for a single native or standard code."""
    if c in "fde":
        return rng.choice([0.0, -0.0, 1.0, -1.5, 0.5, 2.0, 0.25, 3.5])
    if c == "?":
        return rng.random() < 0.5
    if c == "c":
        return bytes([rng.randrange(256)])
    bits = struct.calcsize("@" + c) * 8
    if c.isupper():
        return rng.choice([0, 1, 2, 2 ** bits - 1, rng.randrange(2 ** bits)])
    return rng.choice([0, 1, -1, 2, 2 ** (bits - 1) - 1, -2 ** (bits - 1), rng.randrange(-5, 5)])


def _nd_items(rng, fmt, n):
    """`n` packed elements of `fmt`, as flat bytes."""
    size = struct.calcsize(fmt)
    out = []
    code = fmt.lstrip("@<>=!")
    if code in tuple(_NATIVE):
        for _ in range(n):
            out.extend(struct.pack(fmt, _rand_item(rng, code)))
    else:
        for _ in range(n):
            vals = struct.unpack(fmt, bytes(_rand_bytes(rng, size)))
            out.extend(struct.pack(fmt, *vals))
    return out


def _gen_exporter(rng, store):
    """Lay one exporter out in `store` and return its spec."""
    kind = rng.choice(["bytes", "bytearray", "bytearray", "array", "nd", "nd", "nd", "nd"])
    if _tb is None and kind == "nd":
        kind = "bytes"
    b = len(store)
    if kind in ("bytes", "bytearray"):
        data = _rand_bytes(rng, rng.choice([0, 1, 2, 3, 4, 6, 7, 8, 12, 16, 24, 32]))
        store.extend(data)
        unhash = None if kind == "bytes" else {"cls": "TypeError", "msg": "unhashable type: 'bytearray'"}
        return {"kind": kind, "data": data, "buf": b, "len": len(data), "itemsize": 1,
                "readonly": kind == "bytes", "ndim": 1, "format": "B", "shape": [len(data)],
                "strides": [1], "suboffsets": None, "unhash": unhash}
    if kind == "array":
        tc = rng.choice("bBhHiIlLqQfd")
        size = array(tc).itemsize
        n = rng.choice([0, 1, 2, 3, 4, 6])
        data = _nd_items(rng, tc, n)
        store.extend(data)
        return {"kind": "array", "tc": tc, "data": data, "buf": b, "len": len(data), "itemsize": size,
                "readonly": False, "ndim": 1, "format": tc, "shape": [n], "strides": [size],
                "suboffsets": None,
                "unhash": {"cls": "TypeError", "msg": "unhashable type: 'array.array'"}}

    fmt = rng.choice(_ND_FORMATS)
    itemsize = struct.calcsize(fmt)
    if rng.random() < 0.02:
        ndim = 65
        shape = [1] * 65
    else:
        ndim = rng.choice([0, 1, 1, 1, 2, 2, 2, 3])
        shape = [rng.choice([0, 1, 1, 2, 2, 3, 4]) for _ in range(ndim)]
    writable = rng.random() < 0.6
    fortran = rng.random() < 0.25 and 2 <= ndim <= 3
    pil = rng.random() < 0.3 and 1 <= ndim <= 3
    flags = (_tb.ND_WRITABLE if writable else 0) | (_tb.ND_PIL if pil else 0)
    if ndim == 0:
        flags |= _tb.ND_SCALAR
    # C or Fortran strides of the logical array, then random multipliers
    strides = [0] * ndim
    sd = itemsize
    for i in (range(ndim) if fortran else reversed(range(ndim))):
        strides[i] = sd
        sd *= max(shape[i], 1)
    custom = not fortran and 1 <= ndim <= 3 and rng.random() < 0.6
    if custom:
        extra = 1
        for i in reversed(range(ndim)):
            m = rng.choice([1, 1, 2, 3, -1, -2])
            strides[i] = strides[i] * extra * m
            extra *= abs(m)
    if fortran:
        if rng.random() < 0.5:
            custom = True    # the same strides given explicitly
        else:
            flags |= _tb.ND_FORTRAN
    imin = imax = 0
    if 0 not in shape:
        for s, st in zip(shape, strides):
            if st < 0:
                imin += (s - 1) * st
            else:
                imax += (s - 1) * st
    offset = -imin
    nitems = (imax - imin) // itemsize + 1
    data = _nd_items(rng, fmt, nitems)
    spec = {"kind": "nd", "fmt": fmt, "data": data, "nd_shape": shape, "nd_flags": flags,
            "nd_strides": strides if custom else None, "nd_offset": offset if custom else 0,
            "itemsize": itemsize, "readonly": not writable, "ndim": ndim, "format": fmt,
            "shape": shape if ndim else None, "len": 0}
    try:
        ex = _build_exporter(spec)
    except (ValueError, TypeError, NotImplementedError, struct.error, OverflowError):
        return None
    spec["len"] = ex.nbytes
    spec["unhash"] = None if not writable else {"cls": "ValueError",
                                                "msg": "cannot hash writable ndarray object"}
    if ndim == 0:
        store.extend(data)
        spec.update(buf=b, strides=None, suboffsets=None)
        return spec
    actual = list(ex.strides)
    if not pil:
        store.extend(data)
        spec.update(buf=b + spec["nd_offset"], strides=actual, suboffsets=None)
        return spec
    # init_suboffsets, Modules/_testbuffer.c:1030-1104
    addsize = 8 * ((shape[0] * 8 + 7) // 8)
    imin = sub0 = 0
    for n in range(ndim):
        if shape[n] == 0:
            break
        if strides[n] <= 0:
            x = (shape[n] - 1) * strides[n]
            imin += x
            sub0 += -x if n >= 1 else 0
    start = addsize + spec["nd_offset"] + imin
    step = abs(strides[0])
    table = []
    for n in range(shape[0]):
        table.extend(struct.pack("<Q", (b + start + n * step) % 2 ** 64))
    table.extend([0] * (addsize - len(table)))
    store.extend(table + data)
    buf = b
    if strides[0] < 0 and shape[0] > 0:
        buf = b + (shape[0] - 1) * 8
    spec.update(buf=buf, strides=actual, suboffsets=[sub0] + [-1] * (ndim - 1))
    return spec


def _build_exporter(spec):
    kind = spec["kind"]
    data = bytes(spec["data"])
    if kind == "bytes":
        return data
    if kind == "bytearray":
        return bytearray(data)
    if kind == "array":
        a = array(spec["tc"])
        a.frombytes(data)
        return a
    fmt = spec["fmt"]
    size = spec["itemsize"]
    items = []
    for i in range(0, len(data), size):
        v = struct.unpack(fmt, data[i:i + size])
        items.append(v[0] if len(v) == 1 else v)
    kw = {}
    if spec["nd_strides"] is not None:
        kw = {"strides": spec["nd_strides"], "offset": spec["nd_offset"]}
    if spec["ndim"] == 0:
        return _tb.ndarray(items[0], shape=[], format=fmt, flags=spec["nd_flags"])
    return _tb.ndarray(items, shape=spec["nd_shape"], format=fmt, flags=spec["nd_flags"], **kw)


def _gen_rel(rng):
    return rng.randrange(4) if rng.random() < 0.3 else None


def _gen_obj(rng, n_exp):
    """An argument object."""
    r = rng.random()
    if r < 0.45:
        return rng.choice(_VAL_INTS)
    if r < 0.5:
        return {"bool": rng.random() < 0.5}
    if r < 0.62:
        return {"float": _fbits(rng.choice(_FLOATS))}
    if r < 0.72:
        return {"bytes": _rand_bytes(rng, rng.choice([0, 1, 1, 1, 2, 3, 4, 8]))}
    if r < 0.75:
        return {"str": rng.choice(["", "a", "ab", "\xe9", "Δ"])}
    if r < 0.77:
        return None
    if r < 0.79:
        return {"list": rng.randrange(3)}
    if r < 0.86:
        return {"mv": rng.randrange(6)}
    if r < 0.9:
        return {"exp": rng.randrange(n_exp), "rel": _gen_rel(rng)}
    if r < 0.95:
        return {"idx": rng.choice(_VAL_INTS), "rel": _gen_rel(rng)}
    if r < 0.98:
        return {"flt": _fbits(rng.choice(_FLOATS)), "rel": _gen_rel(rng)}
    return {"bln": rng.random() < 0.5, "rel": _gen_rel(rng)}


def _gen_slice(rng):
    def part():
        return rng.choice([None, None, 0, 1, 2, 3, -1, -2, -3, 4, 100, -100, _M, -_M - 1, 2 ** 64, -2 ** 64])
    step = rng.choice([None, None, 1, 1, 2, 3, -1, -2, 0, _M, -_M, -_M - 1, _M - 1, 2 ** 64])
    a, b = part(), part()
    rel = _gen_rel(rng) if step != 0 and (a is not None or b is not None or step is not None) else None
    return {"slice": [a, b, step], "rel": rel}


def _gen_key_elem(rng):
    r = rng.random()
    if r < 0.55:
        return rng.choice(_KEY_INTS)
    if r < 0.8:
        return _gen_slice(rng)
    if r < 0.9:
        return {"idx": rng.choice(_KEY_INTS), "rel": _gen_rel(rng)}
    if r < 0.95:
        return {"bool": rng.random() < 0.5}
    return rng.choice([{"float": _fbits(1.0)}, {"str": "a"}, None, {"bytes": [1]}])


def _gen_key(rng):
    r = rng.random()
    if r < 0.7:
        return _gen_key_elem(rng)
    if r < 0.93:
        return {"tuple": [_gen_key_elem(rng) for _ in range(rng.choice([0, 1, 2, 2, 2, 3, 4]))]}
    return {"ellipsis": True}


def _gen_cast_shape(rng):
    r = rng.random()
    if r < 0.55:
        return None
    if r < 0.6:
        return "notseq"
    if r < 0.65:
        return [rng.choice([1, 2, {"bool": True}, None, {"idx": 2}, 2 ** 64, -2 ** 64, 0, -1, _M, 2 ** 62])
                for _ in range(rng.choice([1, 2, 3]))]
    if r < 0.67:
        return [1] * 65
    return [rng.choice([1, 1, 2, 2, 3, 4, 6, 8]) for _ in range(rng.choice([0, 1, 2, 2, 3]))]


def _gen_op(rng, specs):
    n_exp = len(specs)
    h = rng.randrange(8)
    k = rng.choice(["get"] * 6 + ["set"] * 6 + ["cast"] * 6 + ["tolist"] * 4 + ["tobytes"] * 3 + ["hex"] * 2
                   + ["del", "len", "toreadonly", "release", "enter", "exit", "repr", "drop"]
                   + ["cmp"] * 4 + ["hash"] * 3 + ["count"] * 2 + ["index"] * 3 + ["iter"] * 2 + ["next"] * 4
                   + ["attr"] * 5 + ["view"] * 2 + ["fromflags", "buffer", "buffer", "toc", "iscontig", "contig",
                                                     "resize", "frommem", "frombuffer", "restricted"])
    if k == "get":
        return [k, h, _gen_key(rng)]
    if k == "set":
        return [k, h, _gen_key(rng), _gen_obj(rng, n_exp)]
    if k == "del":
        return [k, h, _gen_key(rng)]
    if k == "cast":
        return [k, h, rng.choice(_CAST_FORMATS), _gen_cast_shape(rng)]
    if k == "tobytes":
        return [k, h, rng.choice([None, "C", "F", "A", "", "X", "CC"])]
    if k == "hex":
        return [k, h, rng.choice([None, None, {"str": ":"}, {"str": "ab"}, {"str": "\xe9"}, {"str": "Δ"},
                                  {"str": ""}, {"bytes": [45]}, {"bytes": [200]}, {"bytes": [1, 2]},
                                  {"list": 1}, {"list": 2}, 5]),
                rng.choice([None, 1, 2, 3, -1, -2, -3, 0, 100, -100, 2 ** 31 - 1, -2 ** 31])]
    if k == "cmp":
        return [k, h, _gen_obj(rng, n_exp), rng.choice(["eq", "eq", "ne", "lt"])]
    if k in ("count", "index"):
        v = rng.choice([rng.choice([0, 1, 2, 255, -1]), _gen_obj(rng, n_exp)])
        if isinstance(v, dict) and ("mv" in v or "exp" in v or "idx" in v or "flt" in v or "bln" in v):
            v = 0
        if k == "count":
            return [k, h, v]
        return [k, h, v, rng.choice([None, 0, 1, -1, 2, -2, 5, -5, _M, -_M - 1, 2 ** 64, -2 ** 64]),
                rng.choice([None, 0, 1, -1, 2, -2, 5, -5, _M, -_M - 1, 2 ** 64, -2 ** 64])]
    if k == "next":
        return [k, rng.randrange(4)]
    if k == "attr":
        return [k, h, rng.choice(_ATTRS)]
    if k == "view":
        return [k, rng.choice([{"mv": h}, {"exp": rng.randrange(n_exp), "rel": None}, {"bytes": [1, 2]},
                               5, None, {"str": "a"}])]
    if k == "fromflags":
        e = rng.randrange(n_exp)
        if specs[e]["kind"] == "nd":
            return ["fromflags", {"mv": h}, rng.choice(_BUF_FLAGS)]
        return ["fromflags", {"exp": e, "rel": None}, rng.choice(_BUF_FLAGS)]
    if k == "buffer":
        return [k, h, rng.choice(_BUF_FLAGS)]
    if k in ("toc", "iscontig"):
        return [k, h, rng.choice("CFA")]
    if k == "contig":
        return [k, {"mv": h}, rng.random() < 0.3, rng.choice("CFA")]
    if k == "resize":
        ids = [i for i, s in enumerate(specs) if s["kind"] == "bytearray"]
        return [k, rng.choice(ids)] if ids else ["len", h]
    if k == "frommem":
        ids = [i for i, s in enumerate(specs) if s["kind"] == "bytearray" and s["len"] > 0]
        return [k, rng.choice(ids), rng.random() < 0.5] if ids else ["len", h]
    if k == "restricted":
        ids = [i for i, s in enumerate(specs) if s["kind"] in ("bytes", "bytearray")]
        return [k, rng.choice(ids)] if ids else ["len", h]
    if k == "frombuffer":
        e = rng.randrange(n_exp)
        return [k, e, 284 if specs[e]["kind"] == "nd" else rng.choice([b for b in _BUF_FLAGS if not b & 1])]
    return [k, h]


_LOW_FNS = ["mem.narrow32", "mem.widen32", "mem.pack2", "mem.unpack2", "mem.long2d", "mem.deqint",
            "mem.fmtchar", "mem.fmtstr"]


def _gen_low(rng):
    fn = rng.choice(_LOW_FNS)
    case = {"mod": "bytesobj", "fn": fn}
    if fn in ("mem.narrow32", "mem.pack2"):
        r = rng.random()
        if r < 0.3:
            case["d"] = _fbits(rng.choice(_FLOATS))
        elif r < 0.5:
            case["d"] = rng.getrandbits(64)
        else:
            e = rng.randrange(1023 - 160, 1023 + 136)
            frac = rng.choice([0, 1, 2 ** 52 - 1, 2 ** 28, 2 ** 29, 2 ** 29 + 1, 2 ** 41, 2 ** 42 - 1,
                               2 ** 41 + 2 ** 42, rng.getrandbits(52), 2 ** 52 - 2 ** 28, 2 ** 52 - 2 ** 41])
            case["d"] = (rng.getrandbits(1) << 63) | (e << 52) | frac
    elif fn in ("mem.widen32", "mem.unpack2"):
        n = 32 if fn == "mem.widen32" else 16
        case["x"] = rng.choice([rng.getrandbits(n), rng.getrandbits(n) & ((1 << (n - 9)) - 1)])
    elif fn == "mem.long2d":
        bits = rng.choice([1, 8, 53, 54, 55, 64, 65, 100, 1023, 1024, 1025])
        case["n"] = rng.choice([1, -1]) * rng.choice([rng.getrandbits(bits), 2 ** bits - 1, 2 ** bits + 1,
                                                       2 ** bits, (2 ** 53 + 1) << max(bits - 54, 0)])
    elif fn == "mem.deqint":
        n = rng.choice([0, 1, -1, 3, 2 ** 53, 2 ** 53 + 1, 2 ** 100, -2 ** 100, 10 ** 400, rng.getrandbits(60)])
        d = rng.choice([float(n) if abs(n) < 2 ** 1000 else 1.0, 0.5, -0.0, 1.5, float("inf"), float("nan")])
        case.update(d=_fbits(d), n=n)
    else:
        case["fmt"] = rng.choice(_CAST_FORMATS + ["@@B", "BB", "@BB", "\0", "B\0", "@\0B", "\xe9"])
    return case


def _gen_script(rng):
    store = []
    specs = []
    for _ in range(rng.choice([1, 1, 2, 3])):
        s = _gen_exporter(rng, store)
        if s is None:
            return None
        specs.append(s)
    exps = [{k: s[k] for k in ("buf", "len", "itemsize", "readonly", "ndim", "format", "shape", "strides",
                               "suboffsets", "unhash")} for s in specs]
    ops = [["view", {"exp": rng.randrange(len(specs)), "rel": None}]]
    ops += [_gen_op(rng, specs) for _ in range(rng.choice([2, 3, 5, 8, 12]))]
    return {"mod": "bytesobj", "fn": "mem.script", "mem": store, "exps": exps, "specs": specs, "ops": ops}


def gen_mem(rng):
    return _gen_low(rng) if rng.random() < 0.15 else _gen_script(rng)


def _item_json(x):
    if x is True or x is False:
        return {"bool": x}
    if isinstance(x, int):
        return x
    if isinstance(x, float):
        return {"float": _fbits(x)}
    if isinstance(x, bytes):
        return {"bytes": list(x)}
    if isinstance(x, list):
        return [_item_json(y) for y in x]
    raise TypeError(type(x))


class _Gone:
    pass


class _PyBuffer(_ct.Structure):
    _fields_ = [("buf", _ct.c_void_p), ("obj", _ct.c_void_p), ("len", _ct.c_ssize_t),
                ("itemsize", _ct.c_ssize_t), ("readonly", _ct.c_int), ("ndim", _ct.c_int),
                ("format", _ct.c_char_p), ("shape", _ct.c_void_p), ("strides", _ct.c_void_p),
                ("suboffsets", _ct.c_void_p), ("internal", _ct.c_void_p)]


class Idx:
    def __init__(self, n, fire):
        self.n, self.fire = n, fire

    def __index__(self):
        self.fire()
        return self.n


class Flt:
    def __init__(self, x, fire):
        self.x, self.fire = x, fire

    def __float__(self):
        self.fire()
        return self.x


class Bln:
    def __init__(self, b, fire):
        self.b, self.fire = b, fire

    def __bool__(self):
        self.fire()
        return self.b


class Exporter:
    def __init__(self, ex, fire):
        self.ex, self.fire = ex, fire

    def __buffer__(self, flags):
        self.fire()
        return memoryview(self.ex)


class _Script:
    """Runs one script against the real objects."""

    def __init__(self, case):
        self.specs = case["specs"]
        self.exps = [_build_exporter(s) for s in self.specs]
        self.handles = []
        self.dropped = set()
        self.iters = []
        self.hashed = {}
        self.pinned = set()

    def pick(self, h):
        if not self.handles:
            return None
        i = h % len(self.handles)
        return None if i in self.dropped else i

    def reg(self, m):
        for i, x in enumerate(self.handles):
            if x is m:
                return {"mv": i}
        self.handles.append(m)
        return {"mv": len(self.handles) - 1}

    def rel(self, j):
        """The callback of an object spec: `m.release()`, ignoring BufferError."""
        r = j.get("rel")
        i = None if r is None else self.pick(r)
        if i is None:
            return lambda: None
        m = self.handles[i]

        def fire():
            try:
                m.release()
            except BufferError:
                pass
        return fire

    def obj(self, j, raw=False):
        """Returns (object,) or None for a dead handle. With `raw`, an exporter is the
        object itself, not the `Exporter` wrapper."""
        if j is None or isinstance(j, int):
            return (j,)
        if "bool" in j:
            return (j["bool"],)
        if "float" in j:
            return (_unfbits(j["float"]),)
        if "bytes" in j:
            return (bytes(j["bytes"]),)
        if "str" in j:
            return (j["str"],)
        if "list" in j:
            return ([0] * j["list"],)
        if "mv" in j:
            i = self.pick(j["mv"])
            return None if i is None else (self.handles[i],)
        fire = self.rel(j)
        if "exp" in j:
            ex = self.exps[j["exp"]]
            return (ex if raw else Exporter(ex, fire),)
        if "idx" in j:
            return (Idx(j["idx"], fire),)
        if "flt" in j:
            return (Flt(_unfbits(j["flt"]), fire),)
        return (Bln(j["bln"], fire),)

    def key_elem(self, j):
        if isinstance(j, dict) and "slice" in j:
            a, b, c = j["slice"]
            if j.get("rel") is not None:
                fire = self.rel(j)
                if a is not None:
                    a = Idx(a, fire)
                elif b is not None:
                    b = Idx(b, fire)
                else:
                    c = Idx(c, fire)
            return (slice(a, b, c),)
        return self.obj(j)

    def key(self, j):
        if isinstance(j, dict) and "ellipsis" in j:
            return (...,)
        if isinstance(j, dict) and "tuple" in j:
            es = [self.key_elem(e) for e in j["tuple"]]
            if any(e is None for e in es):
                return None
            return (tuple(e[0] for e in es),)
        return self.key_elem(j)

    def step(self, op):
        name = op[0]
        skip = {"skip": True}
        py = common.py_result
        if name == "view":
            o = self.obj(op[1], raw=True)
            return skip if o is None else py(lambda: self.reg(memoryview(o[0])))
        if name == "fromflags":
            o = self.obj(op[1], raw=True)
            return skip if o is None else py(lambda: self.reg(memoryview._from_flags(o[0], op[2])))
        if name == "resize":
            ba = self.exps[op[1]]
            if op[1] in self.pinned:    # a raw view of its memory exists
                return skip
            try:
                ba.append(0)
                ba.pop()
                return {"ok": {"bool": True}}
            except BufferError:
                return {"ok": {"bool": False}}
        if name == "contig":
            o = self.obj(op[1])
            if o is None:
                return skip
            buffertype = _tb.PyBUF_WRITE if op[2] else _tb.PyBUF_READ
            return py(lambda: self.reg(_tb.get_contiguous(o[0], buffertype, op[3])))
        if name == "frommem":
            ba = self.exps[op[1]]
            self.pinned.add(op[1])
            holder = (_ct.c_char * len(ba)).from_buffer(ba)
            f = _ct.pythonapi.PyMemoryView_FromMemory
            f.restype = _ct.py_object
            f.argtypes = [_ct.c_void_p, _ct.c_ssize_t, _ct.c_int]
            m = f(_ct.addressof(holder), len(ba), 0x200 if op[2] else 0x100)
            del holder
            return {"ok": self.reg(m)}
        if name == "frombuffer":
            ex = self.exps[op[1]]
            self.pinned.add(op[1])
            info = _PyBuffer()
            get = _ct.pythonapi.PyObject_GetBuffer
            get.argtypes = [_ct.py_object, _ct.POINTER(_PyBuffer), _ct.c_int]
            get(ex, _ct.byref(info), op[2])
            f = _ct.pythonapi.PyMemoryView_FromBuffer
            f.restype = _ct.py_object
            f.argtypes = [_ct.POINTER(_PyBuffer)]
            res = py(lambda: self.reg(f(_ct.byref(info))))
            rel = _ct.pythonapi.PyBuffer_Release
            rel.argtypes = [_ct.POINTER(_PyBuffer)]
            rel(_ct.byref(info))
            return res
        if name == "restricted":
            return {"ok": _run_restricted(self.exps[op[1]])}
        if name == "next":
            if not self.iters:
                return skip
            it = self.iters[op[1] % len(self.iters)]

            def nxt():
                try:
                    return _item_json(next(it))
                except StopIteration:
                    return {"stop": True}
            return py(nxt)
        i = self.pick(op[1])
        if i is None:
            return skip
        m = self.handles[i]
        if name == "get":
            k = self.key(op[2])
            if k is None:
                return skip

            def get():
                r = m[k[0]]
                return self.reg(r) if isinstance(r, memoryview) else _item_json(r)
            return py(get)
        if name == "set":
            k = self.key(op[2])
            v = self.obj(op[3])
            if k is None or v is None:
                return skip

            def st():
                m[k[0]] = v[0]
            return py(st)
        if name == "del":
            k = self.key(op[2])
            if k is None:
                return skip

            def de():
                del m[k[0]]
            return py(de)
        if name == "len":
            return py(lambda: len(m))
        if name == "tolist":
            return py(lambda: _item_json(m.tolist()))
        if name == "tobytes":
            return py(lambda: {"bytes": list(m.tobytes(op[2]))})
        if name == "hex":
            sep = None if op[2] is None else self.obj(op[2])[0]

            def hx():
                if op[2] is None:
                    return m.hex() if op[3] is None else m.hex(bytes_per_sep=op[3])
                return m.hex(sep) if op[3] is None else m.hex(sep, op[3])
            return py(hx)
        if name == "cast":
            sh = op[3]
            if sh == "notseq":
                sh_arg = (5,)
            elif sh is None:
                sh_arg = ()
            else:
                sh_arg = ([self.obj(x)[0] for x in sh],)
            return py(lambda: self.reg(m.cast(op[2], *sh_arg)))
        if name == "toreadonly":
            return py(lambda: self.reg(m.toreadonly()))
        if name == "release":
            return py(lambda: m.release())
        if name == "enter":
            return py(lambda: (m.__enter__(), None)[1])
        if name == "exit":
            return py(lambda: m.__exit__(None, None, None))
        if name == "cmp":
            w = self.obj(op[2])
            if w is None:
                return skip

            def cmp():
                f = {"eq": m.__eq__, "ne": m.__ne__, "lt": m.__lt__}[op[3]]
                r = f(w[0])
                return {"notimpl": True} if r is NotImplemented else {"bool": r}
            return py(cmp)
        if name == "hash":
            def hs():
                h = hash(m)
                if h not in self.hashed:
                    b = m.tobytes()
                    assert hash(b) == h
                    self.hashed[h] = list(b)
                return {"hash": self.hashed[h]}
            return py(hs)
        if name == "count":
            v = self.obj(op[2])
            return py(lambda: m.count(v[0]))
        if name == "index":
            v = self.obj(op[2])
            a = 0 if op[3] is None else op[3]
            b = _M if op[4] is None else op[4]
            return py(lambda: m.index(v[0], a, b))
        if name == "iter":
            def mk():
                self.iters.append(iter(m))
            return py(mk)
        if name == "attr":
            def at():
                r = getattr(m, op[2])
                if op[2] == "obj":
                    for x, e in enumerate(self.exps):
                        if r is e:
                            return {"exp": x}
                    for x, e in enumerate(self.handles):
                        if r is e:
                            return {"mv": x}
                    if isinstance(r, bytes):
                        return {"exp": 1000000}    # a temporary bytes object
                    return None if r is None else {"unknown": repr(r)}
                if isinstance(r, bool):
                    return {"bool": r}
                return list(r) if isinstance(r, tuple) else r
            return py(at)
        if name == "repr":
            return py(lambda: repr(m).split(" at ")[0])
        if name == "drop":
            del m
            if sys.getrefcount(self.handles[i]) != 2:
                return skip
            self.handles[i] = _Gone()
            self.dropped.add(i)
            return {"ok": None}
        if name == "buffer":
            return py(lambda: self.reg(m.__buffer__(op[2])))
        if name == "toc":
            return py(lambda: {"bytes": list(_tb.py_buffer_to_contiguous(m, op[2], _tb.PyBUF_FULL_RO))})
        if name == "iscontig":
            return py(lambda: {"bool": bool(_tb.is_contiguous(m, op[2]))})
        raise KeyError(name)


def _run_restricted(ex):
    """What `__release_buffer__` of a subclass of a C exporter can do with its view, which
    is restricted when no Python `__buffer__` made it (Objects/typeobject.c:10820-10833)."""
    out = []

    def probe(f):
        def run():
            f()
            return True
        out.append(common.py_result(run))

    class R(bytearray):
        def __release_buffer__(self, view):
            probe(lambda: view.cast("B"))
            probe(view.toreadonly)
            probe(lambda: memoryview(view))
            probe(lambda: view[:])
            probe(lambda: view.__buffer__(0))
            out.append(common.py_result(lambda: len(view)))

    m = memoryview(R(bytes(ex)))
    m.release()
    return out


def run_mem(case):
    fn = case["fn"]
    if fn == "mem.script":
        s = _Script(case)
        out = [s.step(op) for op in case["ops"]]
        for r in out:
            if r.get("exc") == "UnicodeEncodeError":
                r["msg"] = "~'ascii' codec can't encode"
        return {"ok": out}
    if fn == "mem.narrow32":
        return {"ok": struct.unpack("<I", bytes(_ct.c_float(_unfbits(case["d"]))))[0]}
    if fn == "mem.widen32":
        return {"ok": _fbits(_ct.c_float.from_buffer_copy(struct.pack("<I", case["x"])).value)}
    if fn == "mem.pack2":
        try:
            return {"ok": struct.unpack("<H", struct.pack("<e", _unfbits(case["d"])))[0]}
        except OverflowError:
            return {"exc": "OverflowError", "msg": "float too large to pack with 'e' format"}
    if fn == "mem.unpack2":
        return {"ok": _fbits(struct.unpack("<e", struct.pack("<H", case["x"]))[0])}
    if fn == "mem.long2d":
        return common.py_result(lambda: _fbits(float(case["n"])))
    if fn == "mem.deqint":
        return {"ok": _unfbits(case["d"]) == case["n"]}
    return _run_mem_fmt(fn, case["fmt"])


def _run_mem_fmt(fn, fmt):
    """`get_native_fmtchar` and `get_native_fmtstr` as `cast` shows them; 2 bytes of an
    8-byte buffer would fail on length, so the buffer has 8."""
    m = memoryview(bytes(8))
    try:
        c = m.cast(fmt)
    except (ValueError, UnicodeEncodeError):
        return {"ok": None}
    return {"ok": [c.format.lstrip("@"), c.itemsize] if fn == "mem.fmtchar" else c.format}


# ===== end of family mem ==============================================


FAMILIES = {"seq": (gen_seq, run_seq), "bytes": (gen_bytes, run_bytes), "mem": (gen_mem, run_mem)}
PREFIXES = {"tuple": "seq", "list": "seq", "bytes": "bytes", "bytearray": "bytes", "mem": "mem"}


def main():
    only = choose_family()
    names = [only] if only else list(FAMILIES)

    def gen_case(rng):
        return FAMILIES[rng.choice(names)][0](rng)

    def run_python(case):
        return FAMILIES[PREFIXES[case["fn"].split(".")[0]]][1](case)

    common.main(gen_case, run_python)


if __name__ == "__main__":
    main()
