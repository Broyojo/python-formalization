"""Differential test: the abstract io base classes over scripted subclasses.

Usage: python3 difftest/pyio_base_diff.py [--cases N] [--seed S]

A case builds a subclass of IOBase/RawIOBase/BufferedIOBase/TextIOBase whose
read, peek, readinto, write and flush replay a script and log their arguments.
Every operation's result and the final call log are compared against the Lean
model (`base_c`/`base_py`), which tests what the base classes do with those
callbacks. Also covers the remaining BytesIO methods (`bytesx_c`/`bytesx_py`),
including `truncate` of an object whose `__index__` acts on the stream.
"""

import builtins
import errno
import struct
import sys
import warnings

import _pyio
import io

import common
import pyio_diff

warnings.simplefilter("ignore")
sys.unraisablehook = lambda u: None
M = sys.maxsize
BIG = [M, M + 1, -M - 1, -M - 2, 2**64, -2**64]
EXC = [("ValueError", "boom"), ("OSError", "bad"), ("KeyError", "'k'"), ("InterruptedError", "[Errno 4] x")]
MODS = {"c": io, "py": _pyio}
# hints for readlines: around 0, between line lengths, huge, infinite, NaN, subnormal
FLOATS = [0.5, -0.5, 0.0, -0.0, 1.0, 1.5, 2.0, 2.5, 3.0, 4.5, 7.5, 1e300, -1e300, float("inf"), float("-inf"),
          float("nan"), 5e-324, -5e-324, 2.0 ** 53, 2.0 ** 63, 0.9999999999999999]
# objects without the buffer interface, by type name
WOBJ = {"int": 1, "NoneType": None, "float": 1.5, "list": [1]}


def raised(r):
    cls, msg = r["raise"], r["msg"]
    if cls == "InterruptedError":
        raise InterruptedError(errno.EINTR, "x")
    if cls == "KeyError":
        raise KeyError("k")
    raise getattr(builtins, cls)(msg)


def ret(r):
    if isinstance(r, dict):
        if "raise" in r:
            raised(r)
        return bytes(r["b"])
    return r


class Mix:
    def setup(self, c):
        self.reads, self.intos = list(c["reads"]), list(c["intos"])
        self.writes, self.flushes, self.calls = list(c["writes"]), list(c["flushes"]), []
        self.keep, self.views = c["keep"], []

    def flush(self):
        self.calls.append(["flush"])
        if self.flushes:
            r = self.flushes.pop(0)
            if isinstance(r, dict) and "raise" in r:
                raised(r)
            return None
        return super().flush()

    def write(self, b):
        self.calls.append(["write", list(bytes(b))])
        return ret(self.writes.pop(0)) if self.writes else None


class ReadMix:
    def read(self, n=-1):
        self.calls.append(["read", n])
        return ret(self.reads.pop(0)) if self.reads else b""

    def read1(self, n=-1):
        self.calls.append(["read1", n])
        return ret(self.reads.pop(0)) if self.reads else b""


class SeekMix:
    def seek(self, pos, whence=0):
        self.calls.append(["seek", pos, whence])
        return ret(self.seeks.pop(0)) if self.seeks else 0


def iret(r):
    if isinstance(r, dict):
        raised(r)
    return r


class InqMix:
    def _inq(self, name):
        self.calls.append(["inquiry", name])
        return iret(self.inqs.pop(0)) if self.inqs else False

    def seekable(self):
        return self._inq("seekable")

    def readable(self):
        return self._inq("readable")

    def writable(self):
        return self._inq("writable")


class ClosedMix:
    @property
    def closed(self):
        return iret(self.closed_prop)


class PeekMix:
    def peek(self, n=0):
        self.calls.append(["peek", n])
        return ret(self.peeks.pop(0)) if self.peeks else b""


class IntoMix:
    def readinto(self, b):
        self.calls.append(["readinto", len(b)])
        if self.keep:
            self.views.append(memoryview(b))
        if not self.intos:
            return 0
        d, r = self.intos.pop(0)
        m = min(len(d), len(b))
        # C RawIOBase.read hands readinto an uninitialised bytearray and _pyio a
        # zeroed one, so a count above what was written is not comparable
        b[:] = bytes(len(b))
        b[:m] = bytes(d[:m])
        return ret(r)


CLASSES = {}
for key, mod in MODS.items():
    bases = {"io": mod.IOBase, "raw": mod.RawIOBase, "buf": mod.BufferedIOBase, "text": mod.TextIOBase}
    for kind, base in bases.items():
        for peek in (False, True):
            for raw in (False, True):
                for seek in (False, True):
                    for inq in (False, True):
                        for cl in (False, True):
                            mix = ([Mix] + ([PeekMix] if peek else []) + ([] if raw else [ReadMix]) + [IntoMix]
                                   + ([SeekMix] if seek else []) + ([InqMix] if inq else [])
                                   + ([ClosedMix] if cl else []))
                            CLASSES[key, kind, peek, raw, seek, inq, cl] = type("S", tuple(mix) + (base,), {})
# what an overridden inquiry or `closed` answers
IRETS = [True, False, True, False, 1, 0, 2, None, {"raise": "AttributeError", "msg": "nope"}] + [
    {"raise": c, "msg": m} for c, m in EXC]


def small(rng):
    return rng.choice([None, 0, 1, 2, 3, 5, -1, -2, rng.randint(0, 8)] + ([rng.choice(BIG)] if rng.random() < .1 else []))


def rbytes(rng, n=6):
    return [rng.choice([97, 98, 10, 0]) for _ in range(rng.randint(0, n))]


def script_ret(rng, ints=True):
    r = rng.random()
    if r < 0.68:
        return {"b": rbytes(rng)}
    if r < 0.78:
        return None
    if r < 0.86 and ints:
        return rng.choice([0, 1, 3, 5, -1, 9, 2**64, M + 1])
    c, m = rng.choice(EXC)
    return {"raise": c, "msg": m}


def gen_case(rng):
    r = rng.random()
    if r < 0.2:
        fn = rng.choice(["bytesx_c", "bytesx_py"])
        c = {"mod": "pyio", "fn": fn}
        c.update(pyio_diff.gen_bytesio(rng, fn))
        for _ in range(rng.randint(1, 6)):
            k = rng.choice(["readable", "writable", "seekable", "flush", "isatty", "writelines", "getstate", "setstate",
                            "getstate", "setstate", "readinto_self", "readinto_self", "reinit", "reinit",
                            "reinit_obj", "truncobj", "truncobj", "truncobj", "readobj", "readobj",
                            "readlineobj", "seekobj", "seekobj", "readlinesf", "readlinesf", "writeobj"])
            op = {"op": k}
            if k == "writelines":
                op["ls"] = [pyio_diff.gen_bytes(rng) for _ in range(rng.randint(0, 4))]
            if k == "setstate":
                # _pyio.BytesIO keeps whatever it is given: only a position it could hold
                op.update(b=pyio_diff.gen_bytes(rng),
                          pos=rng.randint(0, 12) if fn == "bytesx_py" else pyio_diff.an_int(rng))
            if k == "readinto_self":
                op.update(off=rng.randint(0, 8), n=rng.randint(0, 8))
            if k in ("reinit", "reinit_obj"):
                op["b"] = None if rng.random() < 0.3 else pyio_diff.gen_bytes(rng)
            if k in ("truncobj", "readobj", "readlineobj", "seekobj"):
                op["a"] = pyio_diff.gen_targ(rng, 8)
            if k == "seekobj":
                op["whence"] = rng.choice([0, 0, 0, 1, 1, 2, 2, 3])
            if k == "readlinesf":
                op["bits"] = struct.unpack("<Q", struct.pack("<d", rng.choice(FLOATS)))[0]
            if k == "writeobj":
                op["w"] = {"s": pyio_diff.gen_bytes(rng)} if rng.random() < 0.4 else {"t": rng.choice(list(WOBJ))}
            c["ops"].insert(rng.randint(0, len(c["ops"])), op)
        return c
    fn = rng.choice(["base_c", "base_py"])
    kind = rng.choice(["io", "io", "raw", "raw", "buf", "text"])
    peek = rng.random() < 0.4
    raw = kind == "raw" and rng.random() < 0.6
    c = {"mod": "pyio", "fn": fn, "kind": kind, "peek": peek, "raw": raw,
         "reads": [script_ret(rng) for _ in range(rng.randint(0, 8))],
         "peeks": [script_ret(rng) for _ in range(rng.randint(0, 8))],
         "intos": [[rbytes(rng), script_ret(rng)] for _ in range(rng.randint(0, 5))],
         "writes": [script_ret(rng) for _ in range(rng.randint(0, 3))],
         "flushes": [rng.choice([None, script_ret(rng)]) for _ in range(rng.randint(0, 2))],
         "keep": rng.random() < 0.06}
    if rng.random() < 0.3:
        c["seeks"] = [script_ret(rng) for _ in range(rng.randint(0, 3))]
    if rng.random() < 0.4:
        c["inqs"] = [rng.choice(IRETS) for _ in range(rng.randint(0, 4))]
    if rng.random() < 0.25:
        c["closedprop"] = {"v": rng.choice(IRETS)}
    names = ["seek", "tell", "truncate", "flush", "close", "closed", "seekable", "readable", "writable",
             "checkClosed", "checkSeekable", "checkReadable", "checkWritable", "enter", "exit", "fileno",
             "isatty", "readline", "readline", "readline", "iter", "next", "next", "readlines", "writelines", "del"]
    if kind == "raw":
        names += ["rawRead", "rawRead", "rawReadall", "rawReadall", "rawReadinto", "rawWrite"]
    if kind == "buf":
        names += ["bRead", "bRead1", "bReadinto", "bReadinto", "bReadinto1", "bReadinto1", "bWrite", "bDetach"]
    if kind == "text":
        names = [n for n in names if n not in ("next", "readlines")]
        names += ["tRead", "tReadline", "tWrite", "tTruncate", "tDetach", "tEncoding", "tNewlines", "tErrors"]
    ops = []
    for _ in range(rng.randint(1, 8)):
        k = rng.choice(names)
        op = {"op": k}
        if k in ("exit", "close", "del") and rng.random() < 0.6:
            continue
        if k in ("readline", "readlines", "rawRead"):
            op["n"] = small(rng)
        if k in ("bReadinto", "bReadinto1"):
            op["n"] = rng.randint(0, 6)
        if k == "writelines":
            op["ls"] = [rbytes(rng) for _ in range(rng.randint(0, 3))]
            if rng.random() < 0.3:
                cls, msg = rng.choice(EXC)
                op["stop"] = {"raise": cls, "msg": msg}
        if k.startswith("check") and rng.random() < 0.3:
            op["msg"] = rng.choice(["m", "peek of closed file", ""])
        ops.append(op)
    ops.append({"op": "closed"})
    c["ops"] = ops
    return c


def apply(f, op, mod):
    k = op["op"]
    if k in ("seek", "tell", "truncate", "flush", "close", "seekable", "readable", "writable", "fileno", "isatty"):
        return {"seek": lambda: mod.IOBase.seek(f, 0), "tell": lambda: mod.IOBase.tell(f),
                "truncate": lambda: mod.IOBase.truncate(f)}.get(k, getattr(f, k))()
    if k == "closed":
        return f.closed
    if k in ("checkClosed", "checkSeekable", "checkReadable", "checkWritable"):
        if op.get("msg") is None:
            return getattr(f, "_" + k)()
        # a method call, as the library writes it: C then reports the descriptor's
        # qualified name ('_IOBase._checkClosed'), not the instance's class
        m = op["msg"]
        return {"checkClosed": lambda: f._checkClosed(m), "checkSeekable": lambda: f._checkSeekable(m),
                "checkReadable": lambda: f._checkReadable(m), "checkWritable": lambda: f._checkWritable(m)}[k]()
    if k == "enter":
        return None if f.__enter__() is f else "?"
    if k == "exit":
        return f.__exit__(None, None, None)
    if k == "readline":
        return mod.IOBase.readline(f, op["n"])
    if k == "iter":
        return None if iter(f) is f else "?"
    if k == "next":
        return next(f)
    if k == "readlines":
        return mod.IOBase.readlines(f, op["n"])
    if k == "writelines":
        def lines():
            yield from (bytes(x) for x in op["ls"])
            if op.get("stop"):
                raised(op["stop"])
        return mod.IOBase.writelines(f, lines())
    if k == "del":
        return f.__del__()
    if k == "rawRead":
        return mod.RawIOBase.read(f, op["n"]) if op["n"] is not None else mod.RawIOBase.read(f)
    if k == "rawReadall":
        return mod.RawIOBase.readall(f)
    if k == "rawReadinto":
        return mod.RawIOBase.readinto(f, bytearray(1))
    if k == "rawWrite":
        return mod.RawIOBase.write(f, b"")
    if k in ("bRead", "bRead1", "bWrite", "bDetach"):
        return {"bRead": lambda: mod.BufferedIOBase.read(f), "bRead1": lambda: mod.BufferedIOBase.read1(f),
                "bWrite": lambda: mod.BufferedIOBase.write(f, b""), "bDetach": lambda: mod.BufferedIOBase.detach(f)}[k]()
    if k in ("bReadinto", "bReadinto1"):
        b = bytearray(b"\xff" * op["n"])
        r = getattr(mod.BufferedIOBase, k[1:].lower().replace("into", "into"))(f, b)
        return [r, bytes(b)]
    if k in ("tRead", "tReadline", "tWrite", "tTruncate", "tDetach"):
        return {"tRead": lambda: mod.TextIOBase.read(f), "tReadline": lambda: mod.TextIOBase.readline(f),
                "tWrite": lambda: mod.TextIOBase.write(f, ""), "tTruncate": lambda: mod.TextIOBase.truncate(f),
                "tDetach": lambda: mod.TextIOBase.detach(f)}[k]()
    return {"tEncoding": lambda: mod.TextIOBase.encoding.__get__(f), "tNewlines": lambda: mod.TextIOBase.newlines.__get__(f),
            "tErrors": lambda: mod.TextIOBase.errors.__get__(f)}[k]()


def run_base(c):
    key = c["fn"].split("_")[1]
    mod = MODS[key]
    cls = CLASSES[key, c["kind"], c["peek"], c["raw"], "seeks" in c, "inqs" in c, "closedprop" in c]
    f = cls()
    f.setup(c)
    f.peeks = list(c["peeks"])
    f.seeks = list(c.get("seeks", []))
    f.inqs = list(c.get("inqs", []))
    if "closedprop" in c:
        f.closed_prop = c["closedprop"]["v"]
    out = []
    for op in c["ops"]:
        try:
            out.append({"ok": pyio_diff.enc(apply(f, op, mod))})
        except StopIteration:
            out.append({"exc": "StopIteration", "msg": ""})
        except BaseException as e:
            out.append(pyio_diff.norm(e))
    calls = list(f.calls)
    f.flushes = []
    for v in f.views:
        v.release()
    return {"ok": out, "log": calls}


def readinto_self(f, op):
    with f.getbuffer() as v, v[op["off"]:op["off"] + op["n"]] as w:
        return f.readinto(w)


def run_extra(c):
    fn = c["fn"]
    key = fn.split("_")[1]
    f = MODS[key].BytesIO(bytes(c["init"]))
    views, out = [], []
    for op in c["ops"]:
        k = op["op"]
        try:
            if k == "writelines":
                v = f.writelines([bytes(x) for x in op["ls"]])
            elif k == "getstate":
                st = f.__getstate__()
                if key == "py":
                    assert set(st) == {"_buffer", "_pos"}, st
                v = [st[0], st[1], st[2]] if key == "c" else [bytes(st["_buffer"]), st["_pos"]]
                st = None
            elif k == "setstate":
                st = (bytes(op["b"]), op["pos"], None) if key == "c" else {"_buffer": bytearray(op["b"]), "_pos": op["pos"]}
                v = f.__setstate__(st)
                st = None
            elif k == "readinto_self":
                v = readinto_self(f, op)
            elif k == "reinit":
                v = f.__init__() if op["b"] is None else f.__init__(bytes(op["b"]))
            elif k == "reinit_obj":
                v = f.__init__(1 if op["b"] is None else bytearray(op["b"]))
            elif k == "truncobj":
                if key == "py":
                    f._lock = pyio_diff.WatchLock()
                v = f.truncate(pyio_diff.make_targ(f, op["a"], views))
            elif k == "readobj":
                v = f.read(pyio_diff.make_targ(f, op["a"], views))
            elif k == "readlineobj":
                v = f.readline(pyio_diff.make_targ(f, op["a"], views))
            elif k == "seekobj":
                v = f.seek(pyio_diff.make_targ(f, op["a"], views), op["whence"])
            elif k == "readlinesf":
                v = f.readlines(struct.unpack("<d", struct.pack("<Q", op["bits"]))[0])
            elif k == "writeobj":
                w = op["w"]
                v = f.write("".join(map(chr, w["s"])) if "s" in w else WOBJ[w["t"]])
            elif k in ("readable", "writable", "seekable", "flush", "isatty"):
                v = getattr(f, k)()
            else:
                v = pyio_diff.apply(f, op, "bytesio_" + key, views)
            out.append({"ok": pyio_diff.enc(v)})
            v = None  # a live getvalue() result would keep the buffer shared
        except StopIteration:
            out.append({"exc": "StopIteration", "msg": ""})
        except pyio_diff.Deadlock:
            out.append({"exc": "Deadlock", "msg": ""})
        except Exception as e:
            out.append(pyio_diff.norm(e))
    for v in views:
        v.release()
    return {"ok": out}


def run_python(c):
    return run_base(c) if c["fn"].startswith("base") else run_extra(c)


def agree(py, lean):
    return py == lean


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=20000)
