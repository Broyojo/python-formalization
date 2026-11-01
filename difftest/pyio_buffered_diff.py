"""Differential test: BufferedReader/Writer/Random (C and _pyio) over a scripted raw stream.

Usage: python3 difftest/pyio_buffered_diff.py [--cases N] [--seed S]

The raw stream is a RawIOBase subclass holding bytes and a position; scripts
force short reads and writes, None (would block), invalid counts and exceptions.
Each operation's result, the raw call log, and the raw's final contents and
position are compared with the Lean models (`buf_c`, `buf_py`).
"""

import builtins
import errno
import sys
import warnings

import _pyio
import io

import common
import pyio_diff

warnings.simplefilter("ignore")
sys.unraisablehook = lambda u: None
M = sys.maxsize
MODS = {"c": io, "py": _pyio}
EXC = [("ValueError", "boom"), ("OSError", "bad"), ("InterruptedError", "[Errno 4] x")]


def raised(r):
    cls = r["raise"]
    if cls == "InterruptedError":
        raise InterruptedError(errno.EINTR, "x")
    raise getattr(builtins, cls)(r["msg"])


def make_raw_class(mod):
    class Raw(mod.RawIOBase):
        def setup(self, c):
            self.d, self.p = bytearray(c["data"]), 0
            self.rs, self.ws, self.ss = list(c["rs"]), list(c["ws"]), list(c["ss"])
            self.fl, self.cf, self.calls = c["flags"], c["closeFail"], []

        def readable(self):
            return bool(self.fl[0])

        def writable(self):
            return bool(self.fl[1])

        def seekable(self):
            return bool(self.fl[2])

        def readinto(self, b):
            self.calls.append(["readinto", len(b)])
            if self.closed:
                raise ValueError("raw closed")
            k = len(b)
            if self.rs:
                s = self.rs.pop(0)
                if s is None:
                    return None
                if "raise" in s:
                    raised(s)
                if "bad" in s:
                    return s["bad"]
                k = min(k, s["short"])
            d = bytes(self.d[self.p:self.p + k])
            b[:len(d)] = d
            self.p += len(d)
            return len(d)

        def write(self, b):
            b = bytes(b)
            self.calls.append(["write", list(b)])
            if self.closed:
                raise ValueError("raw closed")
            k = len(b)
            if self.ws:
                s = self.ws.pop(0)
                if s is None:
                    return None
                if "raise" in s:
                    raised(s)
                if "bad" in s:
                    return s["bad"]
                k = min(k, s["short"])
            d = b[:k]
            if d:
                if self.p > len(self.d):
                    self.d.extend(bytes(self.p - len(self.d)))
                self.d[self.p:self.p + len(d)] = d
            self.p += len(d)
            return len(d)

        def seek(self, p, w=0):
            self.calls.append(["seek", p, w])
            if self.closed:
                raise ValueError("raw closed")
            if self.ss:
                s = self.ss.pop(0)
                if s is not None:
                    if "raise" in s:
                        raised(s)
                    return s["bad"]
            if not self.fl[2]:
                raise OSError("unseekable")
            n = p if w == 0 else self.p + p if w == 1 else len(self.d) + p if w == 2 else -1
            if n < 0:
                raise ValueError("bad seek")
            self.p = n
            return n

        def tell(self):
            self.calls.append(["tell"])
            if self.closed:
                raise ValueError("raw closed")
            if self.ss:
                s = self.ss.pop(0)
                if s is not None:
                    if "raise" in s:
                        raised(s)
                    return s["bad"]
            if not self.fl[2]:
                raise OSError("unseekable")
            return self.p

        def truncate(self, p=None):
            self.calls.append(["truncate", p])
            if self.closed:
                raise ValueError("raw closed")
            n = self.p if p is None else p
            if n < 0:
                raise ValueError("bad truncate")
            if n > 2**24:
                raise OverflowError("too big")
            del self.d[n:]
            self.d.extend(bytes(n - len(self.d)))
            return n

        def flush(self):
            self.calls.append(["flush"])
            return super().flush()

        def close(self):
            self.calls.append(["close"])
            if self.cf:
                c, self.cf = self.cf, None
                raise getattr(builtins, c[0])(c[1])
            return super().close()
    return Raw


RAWS = {k: make_raw_class(m) for k, m in MODS.items()}
CLS = {("c", 0): io.BufferedReader, ("c", 1): io.BufferedWriter, ("c", 2): io.BufferedRandom,
       ("py", 0): _pyio.BufferedReader, ("py", 1): _pyio.BufferedWriter, ("py", 2): _pyio.BufferedRandom}


def rbytes(rng, n=8):
    return [rng.choice([97, 98, 10, 0, 120]) for _ in range(rng.randint(0, n))]


def rstep(rng, key):
    r = rng.random()
    if r < 0.55:
        return {"short": rng.choice([0, 1, 1, 2, 3, 5, 8])}
    if r < 0.75:
        return None
    if r < 0.88:
        return {"bad": rng.choice([10**6, 2**64] + ([-1] if key == "c" else []))}
    c, m = rng.choice(EXC)
    return {"raise": c, "msg": m}


def sstep(rng):
    r = rng.random()
    if r < 0.6:
        return None
    if r < 0.8:
        return {"bad": rng.choice([-1, -5, 2**64])}
    c, m = rng.choice(EXC[:2])
    return {"raise": c, "msg": m}


def gen_case(rng):
    fn = rng.choice(["buf_c", "buf_py"])
    key = fn.split("_")[1]
    kind = rng.choice([0, 1, 2, 2])
    size = rng.choice([1, 2, 3, 4, 5, 8, 16, 16, 32])
    if rng.random() < 0.03:
        size = rng.choice([0, -1])
    data = [rng.choice([97, 98, 10, 0]) for _ in range(rng.choice([0, 3, 10, 40, 70]))]
    flags = [1, 1, 1]
    if rng.random() < 0.12:
        flags[rng.randrange(3)] = 0
    c = {"mod": "pyio", "fn": fn, "kind": kind, "size": size, "data": data, "flags": flags,
         "rs": [rstep(rng, key) for _ in range(rng.choice([0, 0, 2, 5]))],
         "ws": [rstep(rng, key) for _ in range(rng.choice([0, 0, 2, 5]))],
         "ss": [sstep(rng) for _ in range(rng.choice([0, 0, 0, 2]))],
         "closeFail": ["ValueError", "cl"] if rng.random() < 0.1 else None}
    names = ["seek", "seek", "tell", "tell", "flush", "closed", "readable", "writable", "seekable",
             "isatty", "fileno", "name", "mode", "getstate", "truncate"]
    if kind != 1:
        names += ["read"] * 4 + ["read1", "read1", "peek", "peek", "readinto", "readinto", "readinto1",
                                 "readline", "readline", "next"]
    if kind != 0:
        names += ["write"] * 5
    ops = []
    for _ in range(rng.randint(1, 10)):
        k = rng.choice(names)
        op = {"op": k}
        if k in ("read", "readline"):
            op["n"] = rng.choice([None, -1, -2, 0, 1, 2, 3, size, size + 1, 2 * size, 3 * size + 1, 30])
            if key == "c" and rng.random() < 0.05:
                op["n"] = rng.choice([M + 1, -M - 2])
        if k == "read1":
            op["n"] = rng.choice([-1, 0, 1, 2, size, 2 * size])
        if k == "peek":
            op["n"] = rng.choice([0, 1, 2, size])
        if k in ("readinto", "readinto1"):
            op["n"] = rng.choice([0, 1, 2, size, size + 1, 2 * size + 1, 20])
        if k == "write":
            op["b"] = [rng.choice([97, 98, 10]) for _ in range(rng.choice([0, 1, 2, 3, size - 1 if size > 1 else 1, size, size + 1, 2 * size, 3 * size + 2]))]
        if k == "seek":
            op["pos"] = rng.choice([0, 0, 1, 2, -1, -2, 5, 20, len(data), len(data) + 3] + ([M + 1, 2**64] if key == "c" else []))
            op["whence"] = rng.choice([0, 0, 0, 1, 1, 2, 2, 3, 5, -1])
        if k == "truncate":
            op["n"] = rng.choice([None, 0, 1, 5, 20, -1])
        ops.append(op)
    if rng.random() < 0.3:
        ops.append({"op": "close"})
    if rng.random() < 0.3:
        ops += [{"op": rng.choice(["read", "tell", "flush", "peek", "write", "seek", "closed"]), "n": 1, "b": [97], "pos": 0, "whence": 0}]
    if rng.random() < 0.12:
        ops.append({"op": "detach"})
    ops.append({"op": "closed"})
    c["ops"] = ops
    return c


def apply(f, op):
    k = op["op"]
    if k in ("read", "readline"):
        return getattr(f, k)(op["n"])
    if k == "read1":
        return f.read1(op["n"])
    if k == "peek":
        return f.peek(op["n"])
    if k in ("readinto", "readinto1"):
        b = bytearray(b"\xff" * op["n"])
        r = getattr(f, k)(b)
        return [r, bytes(b)]
    if k == "write":
        return f.write(bytes(op["b"]))
    if k == "seek":
        return f.seek(op["pos"], op["whence"])
    if k == "truncate":
        return f.truncate(op["n"])
    if k == "next":
        return next(f)
    if k == "closed":
        return f.closed
    if k == "detach":
        return None if f.detach() is f.__dict__.get("?") else None
    if k == "name":
        return f.name
    if k == "mode":
        return f.mode
    if k == "getstate":
        return f.__getstate__()
    return getattr(f, k)()


def norm(e):
    if isinstance(e, BlockingIOError):
        return {"exc": "BlockingIOError", "msg": f"{e.strerror}|{e.characters_written}"}
    return pyio_diff.norm(e)


def run_python(c):
    key = c["fn"].split("_")[1]
    raw = RAWS[key]()
    raw.setup(c)
    try:
        f = CLS[key, c["kind"]](raw, c["size"])
    except Exception as e:
        return norm(e)
    out = []
    for op in c["ops"]:
        try:
            out.append({"ok": pyio_diff.enc(apply(f, op))})
        except StopIteration:
            out.append({"exc": "StopIteration", "msg": ""})
        except Exception as e:
            out.append(norm(e))
    res = {"ok": out, "log": pyio_diff.enc(raw.calls), "data": list(raw.d), "pos": raw.p}
    raw.cf = None
    return res


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=20000)
