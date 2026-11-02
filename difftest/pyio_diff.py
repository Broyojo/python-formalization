"""Differential test: Lean models of BytesIO/StringIO (C `_io` and `_pyio` twins) vs. the running CPython.

Usage: python3 difftest/pyio_diff.py [--cases N] [--seed S]

A case is a constructor plus a list of operations; "fn" names the twin
(bytesio_c, bytesio_py, stringio_c, stringio_py). Every operation's value or
exception (class and message) is compared; the generator always ends with
getvalue/tell (and newlines for StringIO). Bytes and str travel as lists of
ints. Positions are kept either small or within a few thousand of a multiple
of 2**62, so no case ever asks the allocator for a size between 2**24 and
2**60 bytes (the model's MemoryError bound is 2**48). Exception messages that
embed formatted objects are normalized to the model's "~" form (see `norm`).
"fn": "ratio" checks the binary64 emulation used by TextIOWrapper.tell().
Exits non-zero on any mismatch. See difftest/common.py.
"""

import gc
import io
import sys
import warnings

import _pyio

import common

warnings.simplefilter("ignore")
M = sys.maxsize
BIG = [M, M - 1, M + 1, -M, -M - 1, -M - 2, 2**62, -2**62, 2**63, -2**63, 2**64, -2**64,
       2**64 + 1, 2**64 + 5, 2**65, 2**128, 2**128 + 3, 2**192, 2**192 + 1, 2**256, 2**63 - 2,
       M - 2, M - 3, M - 4, M - 6, 2**62 + 1]
CLASSES = {"bytesio_c": io.BytesIO, "bytesio_py": _pyio.BytesIO,
           "stringio_c": io.StringIO, "stringio_py": _pyio.StringIO}
assert io.BytesIO.__module__ in ("_io", "io") and _pyio.BytesIO.__module__ == "_pyio"
assert type(io.BytesIO.read).__name__ == "method_descriptor"

BYTES = [97, 98, 10, 10, 13, 0, 255]
CHARS = [ord(c) for c in "ab\n\n\r\r\x00é€😀"] + [0xD800]
NEWLINES = [None, [], [10], [13], [13, 10]] * 6 + [
    [120], [10, 0], [0], [13, 0], [13, 10, 0], [0, 10], [10, 13], [0xD800], [233], [13, 10, 120]]


def small_int(rng, n=8):
    return rng.choice([0, 0, 1, 1, 2, 3, -1, -1, -2, rng.randint(-3, n + 3), rng.randint(0, n + 3)])


def an_int(rng, n=8):
    return rng.choice(BIG) if rng.random() < 0.2 else small_int(rng, n)


def opt_int(rng, n=8):
    return None if rng.random() < 0.2 else an_int(rng, n)


def gen_bytes(rng, maxn=6):
    return [rng.choice(BYTES) for _ in range(rng.randint(0, maxn))]


def gen_text(rng, maxn=6, alphabet=CHARS):
    r = rng.random()
    if r < 0.04:
        # chunk boundaries of TextIOWrapper (_CHUNK_SIZE = 2048 bytes)
        k = rng.choice([2046, 2047, 2048, 2049, 700, 1023, 1024, 682, 683])
        unit = rng.choice([[97], [233], [8364], [128512], [97, 13, 10]])
        s = (unit * (k // len(unit) + 1))[:k]
        return s + [rng.choice(alphabet) for _ in range(rng.randint(0, 4))]
    return [rng.choice(alphabet) for _ in range(rng.randint(0, maxn))]


def seek_args(rng, n):
    whence = rng.choice([0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 3, -1, 2**31, -2**31 - 1, 2**31 - 1])
    pos = rng.choice([0, 0, an_int(rng, n), small_int(rng, n), n, n + 1, n + 3])
    return pos, whence


def gen_bytesio(rng, fn):
    init = gen_bytes(rng, rng.choice([0, 3, 8, 20]))
    ops, views = [], 0
    n = len(init)
    for _ in range(rng.randint(1, 12)):
        k = rng.choice(["read", "read1", "readline", "readline", "readlines", "readinto", "write", "write",
                        "write", "seek", "seek", "seek", "tell", "truncate", "truncate", "getvalue",
                        "getbuffer", "release", "close", "next", "closed"])
        if k in ("read", "read1", "readline", "truncate", "readlines"):
            ops.append({"op": k, "n": opt_int(rng, n)})
        elif k == "readinto":
            ops.append({"op": k, "n": rng.randint(0, 6)})
        elif k == "write":
            ops.append({"op": k, "b": gen_bytes(rng)})
        elif k == "seek":
            pos, whence = seek_args(rng, n)
            ops.append({"op": k, "pos": pos, "whence": whence})
        elif k == "getbuffer":
            views += 1
            ops.append({"op": k})
        elif k == "release":
            if views == 0:
                continue
            views -= 1
            ops.append({"op": k})
        elif k == "close":
            if rng.random() < 0.5:
                continue
            ops.append({"op": k})
        else:
            ops.append({"op": k})
    ops += [{"op": "release"}] * views
    ops += [{"op": "getvalue"}, {"op": "tell"}, {"op": "closed"}]
    if rng.random() < 0.06:
        # a write that cannot fit, on a buffer shared or private, and what survives it
        pos = rng.choice([M, M - 1, M - 2, M - 33, M - 34, M - 35, 2**62, 2**62 + 1])
        # a view unshares the buffer, unless the stream is empty
        ops = [{"op": "write", "b": [97, 98, 99]}] * rng.randint(0, 1) + \
            [{"op": "getbuffer"}, {"op": "release"}] * rng.randint(0, 1) + [
            {"op": "seek", "pos": pos, "whence": 0}, {"op": "write", "b": [120]}, {"op": "closed"},
            {"op": "getvalue"}, {"op": "tell"}, {"op": "seek", "pos": 0, "whence": 0}] + ops
    return {"init": init, "ops": ops}


def gen_stringio(rng, fn):
    nl = rng.choice(NEWLINES) if rng.random() < 0.97 else [rng.choice(CHARS)]
    init = None if rng.random() < 0.2 else gen_text(rng, rng.choice([0, 3, 8, 16]))
    n = len(init or [])
    ops = []
    for _ in range(rng.randint(1, 16)):
        k = rng.choice(["read", "read", "readline", "readline", "readlines", "write", "write", "write",
                        "seek", "seek", "tell", "tell", "seektell", "truncate", "getvalue", "next", "next",
                        "newlines", "close", "closed"])
        if k in ("read", "readline", "truncate", "readlines"):
            ops.append({"op": k, "n": opt_int(rng, n)})
        elif k == "write":
            ops.append({"op": k, "b": gen_text(rng)})
        elif k == "seek":
            pos, whence = seek_args(rng, n)
            ops.append({"op": k, "pos": pos, "whence": whence})
        elif k == "close":
            if rng.random() < 0.7:
                continue
            ops.append({"op": k})
        else:
            ops.append({"op": k})
    ops += [{"op": "getvalue"}, {"op": "tell"}, {"op": "newlines"}, {"op": "closed"}]
    return {"init": init, "newline": nl, "ops": ops}


def gen_case(rng):
    r = rng.random()
    if r < 0.02:
        b = rng.randint(1, 3000)
        return {"mod": "pyio", "fn": "ratio", "a": rng.randint(0, 4 * b), "b": b, "c": rng.randint(0, b)}
    fn = rng.choice(["bytesio_c", "bytesio_py", "stringio_c", "stringio_py", "stringio_py"])
    c = {"mod": "pyio", "fn": fn}
    c.update(gen_bytesio(rng, fn) if fn.startswith("bytes") else gen_stringio(rng, fn))
    return c


def enc(v):
    if v is None or isinstance(v, (bool, int)):
        return v
    if isinstance(v, (bytes, bytearray)):
        return {"b": list(v)}
    if isinstance(v, str):
        return {"s": [ord(ch) for ch in v]}
    if isinstance(v, (list, tuple)):
        return [enc(x) for x in v]
    raise TypeError(type(v))


def norm(e):
    """Messages embedding formatted objects become the model's `~` text."""
    cls, msg = type(e).__name__, str(e)
    if cls == "UnicodeDecodeError":
        msg = "~utf-8 decode error"
    elif cls == "UnicodeEncodeError":
        msg = "~utf-8 encode error"
    elif cls == "ValueError" and msg.startswith("illegal newline value: ") and any(
            ord(ch) >= 0x7F for ch in msg):
        msg = "~illegal newline value"
    return {"exc": cls, "msg": msg}


def position(f, fn):
    if fn == "bytesio_py":
        return f._pos
    if fn == "stringio_py":
        return f.buffer._pos
    return None if f.closed else f.tell()


def apply(f, op, fn, views):
    k = op["op"]
    if k in ("read", "read1", "readline", "readlines", "truncate"):
        return getattr(f, k)(op["n"])
    if k == "readinto":
        b = bytearray(b"\xff" * op["n"])
        return [f.readinto(b), bytes(b)]
    if k == "write":
        p = position(f, fn) if not f.closed else None
        assert p is None or p < 2**24 or p > 2**60, ("unsafe allocation", p)
        data = bytes(op["b"]) if fn.startswith("bytes") else "".join(map(chr, op["b"]))
        return f.write(data)
    if k == "seek":
        return f.seek(op["pos"], op["whence"])
    if k == "seektell":
        return f.seek(f.tell())
    if k == "getbuffer":
        views.append(f.getbuffer())
        return None
    if k == "release":
        # the model's export count saturates at 0, like a release with no live view
        if views:
            views.pop().release()
        return None
    if k == "next":
        return next(f)
    if k == "closed":
        return f.closed
    return getattr(f, k)() if k != "newlines" else f.newlines


class Deadlock(BaseException):
    """Blocking forever on `_pyio.BytesIO._lock`, which is not re-entrant."""


class WatchLock:
    """Stands in for the stream's `Lock` around a re-entrant call: where the real
    lock would block this thread forever, it raises instead."""

    def __init__(self):
        self.held = False

    def __enter__(self):
        if self.held:
            raise Deadlock
        self.held = True

    def __exit__(self, *exc):
        self.held = False


def run_hook(f, h, views):
    k = h["h"]
    if k == "close":
        f.close()
    elif k == "getbuffer":
        views.append(f.getbuffer())
    elif k == "tell":
        f.tell()
    elif k == "seekabs":
        f.seek(h["p"])
    elif k == "seekcur":
        f.seek(0, 1)
    else:
        f.write(bytes(h["b"]) if isinstance(f, (io.BytesIO, _pyio.BytesIO)) else "".join(map(chr, h["b"])))


class Idx:
    """The argument of `truncate`: `__index__` acts on the stream, swallowing what
    those actions raise, then returns `v` or raises."""

    def __init__(self, f, a, views):
        self.f, self.a, self.views = f, a, views

    def __index__(self):
        for h in self.a["hook"]:
            try:
                run_hook(self.f, h, self.views)
            except Exception:
                pass
        if self.a["v"] is None:
            raise ValueError("boom")
        return self.a["v"]


def gen_hook(rng):
    k = rng.choice(["close", "getbuffer", "tell", "seekabs", "seekcur", "write"])
    h = {"h": k}
    if k == "seekabs":
        h["p"] = rng.randint(0, 8)
    if k == "write":
        h["b"] = rng.choice([[], [97], [97, 98, 10]])
    return h


def gen_targ(rng, n):
    r = rng.random()
    if r < 0.1:
        return {"kind": "str"}
    if r < 0.2:
        return {"kind": "float"}
    return {"kind": "index", "hook": [gen_hook(rng) for _ in range(rng.choice([0, 0, 1, 1, 2]))],
            "v": None if rng.random() < 0.1 else an_int(rng, n)}


def make_targ(f, a, views):
    return {"str": "a", "float": 1.5}[a["kind"]] if a["kind"] != "index" else Idx(f, a, views)


def run_python(c):
    fn = c["fn"]
    if fn == "ratio":
        return {"ok": int(c["a"] / c["b"] * c["c"])}
    cls = CLASSES[fn]
    try:
        if fn.startswith("bytes"):
            f = cls(bytes(c["init"]))
        else:
            init = None if c["init"] is None else "".join(map(chr, c["init"]))
            nl = None if c["newline"] is None else "".join(map(chr, c["newline"]))
            f = cls(init, nl)
    except Exception as e:
        return norm(e)
    out, views = [], []
    for op in c["ops"]:
        try:
            out.append({"ok": enc(apply(f, op, fn, views))})
        except StopIteration:
            out.append({"exc": "StopIteration", "msg": ""})
        except AssertionError as e:
            if e.args and e.args[0] == "unsafe allocation":
                raise
            out.append(norm(e))
        except Exception as e:
            out.append(norm(e))
    for v in views:
        v.release()
    try:
        f.close()
    except Exception:
        pass
    del f
    gc.collect(0) if rng_gc() else None
    return {"ok": out}


_n = [0]


def rng_gc():
    _n[0] += 1
    return _n[0] % 500 == 0


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=20000)
