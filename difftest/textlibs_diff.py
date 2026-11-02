"""Differential test: Lean models of the text and binary format modules vs. the running CPython.

Usage: python3 difftest/textlibs_diff.py [--cases N] [--seed S]
Set TEXTLIBS_ONLY=struct,binascii,... to restrict the areas.

Each area adds a generator and a runner to AREAS. The case's "fn" starts with the
area's name. Bytes and str travel as lists of ints; see the area's docstring.
"""

import os
import struct
import sys
import warnings

import common

warnings.simplefilter("ignore")
M = sys.maxsize
AREAS = {}


def area(name, weight):
    def deco(cls):
        AREAS[name] = (cls, weight)
        return cls
    return deco


# ---- struct ----------------------------------------------------------------

class Idx:
    def __init__(self, v):
        self.v = v

    def __index__(self):
        return self.v


def bits_float(b):
    return struct.unpack("<d", b.to_bytes(8, "little"))[0]


def float_bits(x):
    return int.from_bytes(struct.pack("<d", x), "little")


STRUCT_EXCS = {"ValueError": ValueError, "TypeError": TypeError, "OverflowError": OverflowError,
               "ZeroDivisionError": ZeroDivisionError, "OSError": OSError}


def s_res(r, conv=lambda x: x):
    def call(self, *a):
        if "raise" in r:
            raise STRUCT_EXCS[r["raise"][0]](r["raise"][1])
        return conv(r["ok"])
    return call


def struct_obj(v):
    ns = {"__bool__": s_res(v["truth"])}
    if v.get("index") is not None:
        ns["__index__"] = s_res(v["index"])
    if v.get("float") is not None:
        ns["__float__"] = s_res(v["float"], bits_float)
    if v.get("cplx") is not None:
        ns["__complex__"] = s_res(v["cplx"], lambda x: complex(bits_float(x[0]), bits_float(x[1])))
    return type("O", (), ns)()


class RaisingBuffer:
    def __init__(self, x):
        self.x = x

    def __buffer__(self, flags):
        raise STRUCT_EXCS[self.x[0]](self.x[1])


RaisingBuffer.__name__ = RaisingBuffer.__qualname__ = "BF"


def buf_dec(b):
    if "bytes" in b:
        return bytes(b["bytes"])
    if "ba" in b:
        return bytearray(b["ba"])
    if "raises" in b:
        return RaisingBuffer(b["raises"])
    return {"int": 1, "list": [], "NoneType": None}[b["ty"]]


def off_dec(o):
    if "i" in o:
        return o["i"]
    if "idx" in o:
        return type("O", (), {"__index__": s_res(o["idx"])})()
    return {"str": "x", "list": [], "NoneType": None}[o["ty"]]


def sv_dec(a):
    t, v = a["t"], a["v"]
    if t == "i":
        return v
    if t == "idx":
        return Idx(v)
    if t == "b":
        return bytes(v)
    if t == "ba":
        return bytearray(v)
    if t == "f":
        return bits_float(v)
    if t == "c":
        return complex(bits_float(v[0]), bits_float(v[1]))
    if t == "obj":
        return struct_obj(v)
    return "x" if v else ""


def sv_enc(x):
    if isinstance(x, bool):
        return {"t": "B", "v": x}
    if isinstance(x, int):
        return {"t": "i", "v": x}
    if isinstance(x, bytes):
        return {"t": "b", "v": list(x)}
    if isinstance(x, float):
        return {"t": "f", "v": float_bits(x)}
    if isinstance(x, complex):
        return {"t": "c", "v": [float_bits(x.real), float_bits(x.imag)]}
    raise TypeError(type(x))


class RaisingHash:
    def __init__(self, x):
        self.x = x

    def __hash__(self):
        raise STRUCT_EXCS[self.x[0]](self.x[1])


RaisingHash.__name__ = RaisingHash.__qualname__ = "H"


def fmt_dec(f):
    if "hr" in f:
        return RaisingHash(f["hr"])
    if "s" in f:
        return "".join(map(chr, f["s"]))
    if "b" in f:
        return bytes(f["b"])
    return {"int": 3, "float": 1.5, "NoneType": None}.get(f["o"], [])


@area("struct", 6)
class StructArea:
    CODES = list("xbBcspsphHiIlLnNqQ?efdFDP") + ["Zf", "Zd", "Zf", "Zd"]
    INTS = [0, 1, -1, 127, 128, -128, -129, 255, 256, 32767, 32768, -32768, -32769, 65535, 65536,
            2**31 - 1, 2**31, -2**31, -2**31 - 1, 2**32 - 1, 2**32, 2**63 - 1, 2**63, -2**63,
            -2**63 - 1, 2**64 - 1, 2**64, -2**64, 2**100, -2**100]
    FLOATS = [0, 1 << 63, 0x3FF0000000000000, 0xBFF0000000000000, 0x7FF0000000000000,
              0xFFF0000000000000, 0x7FF8000000000000, 0x7FF0000000000001, 0xFFF8000000000123,
              0x7FF0000020000000, 0x7FF4000000000000, 1, 0x000FFFFFFFFFFFFF, 0x0010000000000000,
              0x7FEFFFFFFFFFFFFF, 0x47EFFFFFE0000000, 0x47EFFFFFF0000000, 0x47EFFFFFD0000000,
              0x36A0000000000000, 0x36A0000000000001, 0x3690000000000000, 0x3810000000000000,
              0x380FFFFFFFFFFFFF, 0x40EFFE0000000000, 0x40EFFC0000000000, 0x40EFFDFFFFFFFFFF,
              0x3E70000000000000, 0x3E60000000000000, 0x3E78000000000000, 0x3F10000000000000,
              0x3F0FFC0000000000, 0x3F0FFE0000000000, 0x3FF0040000000000, 0x3FF0060000000000]

    @classmethod
    def fmt(cls, r):
        prefix = r.choice(["", "", "@", "<", ">", "=", "!"])
        parts = []
        for _ in range(r.choice([0, 1, 1, 2, 3, 5])):
            c = r.choice(cls.CODES)
            if prefix and prefix != "@" and c in "nNP" and r.random() < 0.9:
                c = "i"
            n = r.choice(["", "", "", "0", "1", "2", "3", "5", "7", "10"])
            sp = r.choice(["", "", "", " ", "\t", "\n "])
            parts.append(n + c + sp)
        s = prefix + "".join(parts)
        roll = r.random()
        if roll < 0.03:
            s += r.choice(["3", "0", "9" * 20, "z", "\0", "<", "@", "3 i", "\x0b", "!", "1e", "Z", "Zi", "3Z", "ZF", "Z f", "Zfd", "fZ", "2Zd3"])
        elif roll < 0.06:
            s = r.choice(["9223372036854775807x", "9223372036854775808x", "9223372036854775807xb",
                          "b9223372036854775807h", "4611686018427387904h", "4611686018427387903h",
                          "2305843009213693952i", "b2305843009213693951i", "1152921504606846975q",
                          "9223372036854775807sb", "9223372036854775807s9223372036854775807s",
                          "9223372036854775807b9223372036854775807b", "9223372036854775807pp",
                          "9223372036854775808s", "1b9223372036854775806xh", "@b9223372036854775806xq",
                          "=9223372036854775807xh", "<9223372036854775806xh", "bh9223372036854775805x"])
        return {"s": [ord(c) for c in s]} if roll < 0.95 else {"b": [ord(c) for c in s]}

    @classmethod
    def value(cls, r, code):
        code = {"Zf": "F", "Zd": "D"}.get(code, code)
        roll = r.random()
        if roll < 0.08:
            return r.choice([{"t": "o", "v": True}, {"t": "o", "v": False},
                             {"t": "b", "v": [1, 2]}, {"t": "b", "v": [65]}, {"t": "ba", "v": [65]},
                             {"t": "f", "v": 0x3FF8000000000000}, {"t": "i", "v": 5},
                             {"t": "c", "v": [0x3FF0000000000000, 0]}])
        if code in "bBhHiIlLnNqQP?":
            n = r.choice(cls.INTS) + r.choice([0, 0, 0, -1, 1])
            return {"t": "idx" if r.random() < 0.1 else "i", "v": n}
        if code == "c":
            return {"t": "b", "v": [r.randrange(256)]}
        if code in "sp":
            k = r.choice([0, 1, 2, 3, 5, 7, 10, 256, 300])
            return {"t": r.choice(["b", "ba"]), "v": [r.randrange(256) for _ in range(k)]}
        if code in "efFD":
            def fl():
                roll = r.random()
                if roll < 0.75:
                    return r.choice(cls.FLOATS)
                if roll < 0.9:
                    return r.getrandbits(64)
                return (r.randrange(0x3D0, 0x4F0) << 52) + r.getrandbits(52)
            if code in "FD":
                if r.random() < 0.8:
                    return {"t": "c", "v": [fl(), fl()]}
            if r.random() < 0.15:
                return {"t": "i", "v": r.choice([0, 1, -3, 2**70, 10**400, 2**1024, 2**1024 - 2**970,
                                                 2**1024 - 2**970 - 1, 2**53 + 1, -2**53 - 3])}
            return {"t": "f", "v": fl()}
        if code == "f" or code == "d":
            pass
        return {"t": "f", "v": r.choice(cls.FLOATS)}

    @classmethod
    def obj_arg(cls, r, code):
        x = lambda: {"raise": [r.choice(["ValueError", "TypeError", "OverflowError", "ZeroDivisionError"]), "boom"]}
        ok = lambda v: {"ok": v}
        return {"t": "obj", "v": {
            "truth": r.choice([ok(True), ok(False), x()]),
            "index": r.choice([None, ok(r.choice([0, 1, -1, 300, 2**70])), x()]),
            "float": r.choice([None, None, ok(r.choice(cls.FLOATS)), x()]),
            "cplx": r.choice([None, None, ok([r.choice(cls.FLOATS), r.choice(cls.FLOATS)]), x()])}}

    @classmethod
    def args_for(cls, r, fmt):
        try:
            s = struct.Struct(fmt_dec(fmt))
        except Exception:
            return []
        if s.size > 4096:
            return []
        import re
        out = []
        text = s.format.lstrip("@<>=!")
        for num, c in re.findall(r"(\d*)(Z[fd]|[a-zA-Z?])", text):
            n = int(num) if num else 1
            if c == "x":
                continue
            if c in "sp":
                n = 1
            out.extend(cls.value(r, c) for _ in range(n))
        if r.random() < 0.05:
            out = out[:-1] if out and r.random() < 0.5 else out + [{"t": "i", "v": 0}]
        if out and r.random() < 0.25:
            out[r.randrange(len(out))] = cls.obj_arg(r, "")
        return out

    @classmethod
    def buf_for(cls, r, fmt):
        try:
            n = struct.Struct(fmt_dec(fmt)).size
        except Exception:
            n = 4
        if n > 4096:
            n = 16
        m = r.choice([n, n, n, n * 2, n * 3, n + 1, max(n - 1, 0), 0, 7])
        special = [0, 0xFF, 0x7F, 0x80, 0xC0, 0x7C, 1, 2]
        return [r.choice(special) if r.random() < 0.7 else r.randrange(256) for _ in range(m)]

    @classmethod
    def life(cls, r):
        f = lambda: r.choice([{"s": [105]}, {"s": [105]}, {"b": [105]}, {"s": [104]}, {"b": [104]}, {"s": [122]}, {"b": [255]}, {"s": [0xe9]}, {"s": [105, 0, 105]},
                              {"o": "int", "h": True}, {"s": []}])

        def call():
            k = r.random()
            if k < 0.6:
                return {"pos": [f()], "kw": []}
            if k < 0.75:
                return {"pos": [], "kw": [["format", f()]]}
            if k < 0.82:
                return {"pos": [], "kw": []}
            if k < 0.9:
                return {"pos": [f(), f()], "kw": []}
            if k < 0.95:
                return {"pos": [f()], "kw": [["format", f()]]}
            return {"pos": [], "kw": [["fmt", f()]]}
        kind = r.choice(["plain", "plain", "init", "new"])
        return {"mod": "textlibs", "fn": "struct.life", "kind": kind, "newis": kind != "new", "initis": kind != "init", "new": call(),
                "inits": [call() for _ in range(r.choice([0, 0, 1, 2, 3]))]}

    @classmethod
    def gen(cls, r):
        fn = r.choice(["calcsize", "info", "pack", "pack", "pack", "Struct.pack", "unpack", "unpack",
                       "unpack_from", "iter_unpack", "iter_hint", "pack_into", "uninit", "pack_into2", "unpack2",
                       "unpack_from2", "iter2", "iter2", "mod2", "life", "life"])
        if fn == "life":
            return cls.life(r)
        fmt = cls.fmt(r)
        if r.random() < 0.01:
            fmt = r.choice([{"o": "int", "h": True}, {"o": "list", "h": False}, {"o": "float", "h": True},
                            {"o": "NoneType", "h": True}, {"s": [0xff]}, {"b": [0xff]}, {"s": [0x105, 0x69]},
                            {"o": "H", "hr": ["ValueError", "boom"]}, {"o": "H", "hr": ["TypeError", "boom"]}])
        try:
            if struct.calcsize(fmt_dec(fmt)) > 4096:  # would only test the allocator
                fn = r.choice(["calcsize", "info"])
        except Exception:
            pass
        c = {"mod": "textlibs", "fn": "struct." + fn, "fmt": fmt}
        if fn in ("pack_into2", "unpack2", "unpack_from2", "iter2", "mod2"):
            try:
                n = struct.calcsize(fmt_dec(fmt))
            except Exception:
                n = 0
            if n > 4096:
                c["fn"] = "struct.calcsize"
                return c
            k = r.choice([n, n, n, 2 * n, n + 1, max(n - 1, 0), 0])
            blob = [r.randrange(256) for _ in range(k)]
            bad = r.choice([{"ty": "int"}, {"ty": "list"}, {"raises": ["ValueError", "boom"], "ty": "BF"},
                            {"raises": ["TypeError", "boom"], "ty": "BF"}])
            if fn == "pack_into2":
                c["n"] = r.choice([0, 1, 2, 2, 2, 2, 2, 2])
                c["args"] = cls.args_for(r, fmt)
                c["buf"] = r.choice([{"ba": blob}, {"ba": blob}, {"ba": blob}, {"bytes": blob}, bad])
                c["off"] = r.choice([{"i": 0}, {"i": 0}, {"idx": {"ok": 0}}, {"idx": {"ok": 1}}, {"idx": {"raise": ["ValueError", "boom"]}},
                                     {"idx": {"ok": 2**70}}, {"ty": "str"}, {"i": -1},
                                     {"idx": {"ok": 0}, "reinit": [cc for cc in r.choice(["b", "bb", "2b", "i", "0s"]).encode()]}])
                if c["n"] != 2:
                    c.pop("args")
                    c["args"] = []
                return c
            c["buf"] = r.choice([{"bytes": blob}, {"bytes": blob}, {"ba": blob}, bad])
            if fn == "mod2":
                c["op"] = r.choice(["unpack", "unpack", "unpack_from", "iter", "pack0", "pack_into0", "pack_into1", "pack_into2", "pack_into"])
                c["args"] = cls.args_for(r, fmt)
                c["off"] = r.choice([{"i": 0}, {"idx": {"ok": 0}}, {"idx": {"raise": ["ValueError", "boom"]}}, {"ty": "str"}])
            if fn == "unpack_from2":
                c["off"] = r.choice([{"i": 0}, {"idx": {"ok": 0}}, {"idx": {"ok": 1}}, {"idx": {"raise": ["ValueError", "boom"]}},
                                     {"idx": {"ok": 2**70}}, {"ty": "str"}, {"i": -1}])
            if fn == "iter2":
                # re-init only while the next read stays inside the buffer: anything else is undefined
                idx, size, ops = 0, n, []
                for _ in range(r.choice([1, 2, 3, 5, 8])):
                    roll = r.random()
                    if roll < 0.55:
                        if size and idx < k and (idx + size > k or k % n if n else True):
                            break
                        ops.append("next")
                        idx += size
                    elif roll < 0.8:
                        if size == 0:
                            break
                        ops.append("len")
                    else:
                        g = r.choice(["b", "h", "bb", "i", "0s", "2b"])
                        ops.append({"s": [ord(x) for x in g]})
                        size = struct.calcsize(g)
                c["ops"] = ops
            return c
        if fn in ("pack", "Struct.pack", "pack_into"):
            c["args"] = cls.args_for(r, fmt)
        if fn in ("unpack", "unpack_from", "iter_unpack", "iter_hint", "pack_into"):
            c["buf"] = cls.buf_for(r, fmt)
        if fn == "iter_hint":
            try:
                hint = struct.iter_unpack(fmt_dec(fmt), bytes(c["buf"])).__length_hint__()
            except Exception:
                hint = 0
            c["k"] = min(r.choice([0, 0, 1, 2]), hint)
        if fn in ("unpack_from", "pack_into"):
            n = len(c["buf"])
            c["off"] = r.choice([0, 0, 1, 2, -1, -2, n, -n, n + 1, -n - 1, n // 2, M, -M, -M - 1, M + 1,
                                 -M - 2, 2**70])
        return c

    @classmethod
    def run_life(cls, c):
        class I(struct.Struct):
            def __init__(self, *a, **k):
                super().__init__(*a, **k)

        class N(struct.Struct):
            def __new__(cls, *a, **k):
                return super().__new__(cls, *a, **k)
        ty = {"plain": struct.Struct, "init": I, "new": N}[c["kind"]]

        def fm(x):
            return fmt_dec(x)

        def wlist(w):
            return [[x.category.__name__, str(x.message)] for x in w]

        def show(s):
            try:
                return [s.size, list(s.format.encode())]
            except AttributeError:
                return None

        def do(f):
            with warnings.catch_warnings(record=True) as w:
                warnings.simplefilter("always")
                try:
                    return f(), None, wlist(w)
                except Exception as e:
                    return None, {"exc": type(e).__name__, "msg": str(e)}, wlist(w)

        def args(x):
            return [fm(a) for a in x["pos"]], {k: fm(v) for k, v in x["kw"]}
        a, k = args(c["new"])
        s, e, w = do(lambda: ty(*a, **k))
        if e is not None:
            return {"ok": {"new": e, "w": w, "ops": []}}
        out = []
        first = show(s)
        for x in c["inits"]:
            a, k = args(x)
            _, e, w2 = do(lambda: s.__init__(*a, **k))
            out.append([show(s) if e is None else e, w2])
        return {"ok": {"new": first, "w": w, "ops": out}}

    @classmethod
    def run(cls, c):
        fn = c["fn"][len("struct."):]
        if fn == "pack_into2":
            def body():
                s = struct.Struct(fmt_dec(c["fmt"]))
                b = buf_dec(c["buf"]) if c["n"] else None
                a = [sv_dec(x) for x in c["args"]]
                if c["n"] == 0:
                    s.pack_into()
                elif c["n"] == 1:
                    s.pack_into(b)
                else:
                    o = off_dec(c["off"])
                    if "reinit" in c["off"]:
                        class R:
                            def __index__(self):
                                with warnings.catch_warnings():
                                    warnings.simplefilter("ignore")
                                    s.__init__(bytes(c["off"]["reinit"]).decode())
                                return c["off"]["idx"]["ok"]
                        o = R()
                    s.pack_into(b, o, *a)
                return list(b)
            return common.py_result(body)
        if fn == "mod2":
            def body():
                op = c["op"]
                if op == "pack0":
                    return list(struct.pack())
                if op == "pack_into0":
                    return struct.pack_into()
                f = fmt_dec(c["fmt"])
                if op == "pack_into1":
                    return struct.pack_into(f)
                if op == "pack_into2":
                    return struct.pack_into(f, buf_dec(c["buf"]))
                b = buf_dec(c["buf"])
                if op == "pack_into":
                    struct.pack_into(f, b, off_dec(c["off"]), *[sv_dec(a) for a in c["args"]])
                    return list(b)
                if op == "unpack":
                    return [sv_enc(x) for x in struct.unpack(f, b)]
                if op == "unpack_from":
                    return [sv_enc(x) for x in struct.unpack_from(f, b, off_dec(c["off"]))]
                struct.iter_unpack(f, b)
                return None
            return common.py_result(body)
        if fn == "unpack2":
            return common.py_result(lambda: [sv_enc(x) for x in struct.Struct(fmt_dec(c["fmt"])).unpack(buf_dec(c["buf"]))])
        if fn == "unpack_from2":
            return common.py_result(lambda: [sv_enc(x) for x in struct.Struct(fmt_dec(c["fmt"])).unpack_from(buf_dec(c["buf"]), off_dec(c["off"]))])
        if fn == "iter2":
            def body():
                s = struct.Struct(fmt_dec(c["fmt"]))
                it = s.iter_unpack(buf_dec(c["buf"]))
                out = []
                for op in c["ops"]:
                    if op == "next":
                        try:
                            out.append({"ok": [sv_enc(x) for x in next(it)]})
                        except StopIteration:
                            out.append({"ok": []})
                            out.append(None)
                    elif op == "len":
                        out.append({"ok": it.__length_hint__()})
                    else:
                        with warnings.catch_warnings():
                            warnings.simplefilter("ignore")
                            s.__init__("".join(map(chr, op["s"])))
                return out
            return common.py_result(body)
        if fn == "life":
            return cls.run_life(c)
        if fn == "uninit":
            s = struct.Struct.__new__(struct.Struct)
            return {"ok": {"size": s.size, "pack": common.py_result(lambda: list(s.pack())),
                           "unpack": _none(lambda: s.unpack(b"")),
                           "format": common.py_result(lambda: list(s.format.encode()))}}
        f = fmt_dec(c["fmt"])

        def pack_args():
            return [sv_dec(a) for a in c["args"]]

        def tup(t):
            return [sv_enc(x) for x in t]

        def body():
            if fn == "calcsize":
                return struct.calcsize(f)
            if fn == "info":
                s = struct.Struct(f)
                return {"size": s.size, "len": len(s.unpack(bytes(s.size))) if s.size < 4096 else
                        _item_count(s), "sizeof": s.__sizeof__(), "repr": repr(s)}
            if fn == "pack":
                return list(struct.pack(f, *pack_args()))
            if fn == "Struct.pack":
                return list(struct.Struct(f).pack(*pack_args()))
            if fn == "unpack":
                return tup(struct.unpack(f, bytes(c["buf"])))
            if fn == "unpack_from":
                return tup(struct.unpack_from(f, bytes(c["buf"]), c["off"]))
            if fn == "iter_unpack":
                return [tup(t) for t in struct.iter_unpack(f, bytes(c["buf"]))]
            if fn == "iter_hint":
                it = struct.iter_unpack(f, bytes(c["buf"]))
                for _ in range(c["k"]):
                    next(it)
                return it.__length_hint__()
            if fn == "pack_into":
                b = bytearray(c["buf"])
                struct.pack_into(f, b, c["off"], *pack_args())
                return list(b)
            raise KeyError(fn)

        return common.py_result(body)


def _none(f):
    try:
        f()
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}
    return {"ok": None}


def _item_count(s):
    """Item count of a huge-size format without materialising it."""
    import re
    n = 0
    for num, ch in re.findall(r"(\d*)(Z[fd]|[a-zA-Z?])", s.format.lstrip("@<>=!")):
        if ch in "sp":
            n += 1
        elif ch != "x":
            n += int(num) if num else 1
    return n


# ---- binascii and base64 ---------------------------------------------------

import array
import base64
import binascii
import io
import tempfile


def data_dec(d):
    """{"b": [...]} is bytes, {"s": [...]} is a str by code points."""
    if d is None:
        return None
    if "nb" in d:
        return {"int": 1, "list": [], "NoneType": None, "float": 1.5}[d["nb"]]
    if "rz" in d:
        return RaisingBuffer(d["rz"])
    return bytes(d["b"]) if "b" in d else "".join(map(chr, d["s"]))


def flag_dec(f):
    if isinstance(f, bool):
        return f
    return type("O", (), {"__bool__": s_res(f)})()


def int_dec(f):
    if isinstance(f, int):
        return f
    return type("O", (), {"__index__": s_res(f)})()


def bad_data(r):
    return r.choice([{"nb": "int"}, {"nb": "list"}, {"nb": "NoneType"}, {"rz": ["ValueError", "boom"]}, {"rz": ["TypeError", "boom"]},
                     {"s": [97, 98]}, {"s": [233]}, {"b": [97, 98, 99, 100]}])


def file_read(c):
    class F:
        def __init__(self):
            self.d, self.pos, self.i = bytes(c.get("d", [])), 0, 0
            self.lines = list(c.get("lines", []))
            self.written, self.w = [], 0

        def read(self, n):
            st = c["reads"][self.i] if self.i < len(c["reads"]) else None
            self.i += 1
            if st is not None and "raise" in st:
                raise STRUCT_EXCS[st["raise"][0]](st["raise"][1])
            m = n if st is None else min(st["give"], n)
            out = self.d[self.pos:self.pos + m]
            self.pos += len(out)
            return out

        def readline(self):
            if not self.lines:
                return b""
            l = self.lines.pop(0)
            if isinstance(l, dict):
                raise STRUCT_EXCS[l["raise"][0]](l["raise"][1])
            return bytes(l)

        def write(self, b):
            self.written.append(list(b))
            if self.w < len(c["writes"]):
                x = c["writes"][self.w]
                self.w += 1
                if x is not None:
                    raise STRUCT_EXCS[x["raise"][0]](x["raise"][1])

    return F()


def r_hex(c):
    g = int_dec(c["group"])
    sep = c.get("sep")
    if sep is None:
        return lambda x: binascii.hexlify(x, bytes_per_sep=g)
    if "len" in sep:
        o = [0] * sep["len"]
    elif "raise" in sep:
        o = type("O", (), {"__len__": s_res(sep)})()
    else:
        o = data_dec(sep)
    return lambda x: binascii.b2a_hex(x, o, g)


class Codec:
    B64 = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
    B32 = b"ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"
    B32H = b"0123456789ABCDEFGHIJKLMNOPQRSTUV"
    ODD = [0, 10, 13, 32, 45, 95, 61, 43, 47, 48, 49, 79, 73, 76, 97, 122, 128, 255]

    @staticmethod
    def raw(r):
        return [r.randrange(256) for _ in range(r.choice([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 20, 40]))]

    @classmethod
    def corrupt(cls, r, b, alpha):
        """Valid-looking text with the padding and alphabet edges hit often."""
        b = list(b)
        for _ in range(r.choice([0, 0, 1, 1, 2, 3])):
            i = r.randint(0, len(b))
            op = r.random()
            if op < 0.4:
                b.insert(i, 61)
            elif op < 0.7:
                b.insert(i, r.choice(cls.ODD))
            elif op < 0.85 and b:
                b.pop(min(i, len(b) - 1))
            elif b:
                b[min(i, len(b) - 1)] = r.choice(alpha + bytes(cls.ODD))
        if r.random() < 0.2:
            b += [61] * r.randint(1, 5)
        if r.random() < 0.1:
            b = [61] * r.randint(1, 4) + b
        return b

    @classmethod
    def wrap(cls, r, b):
        b = list(b)
        if r.random() < 0.3 and all(x < 128 for x in b):
            return {"s": b}
        if r.random() < 0.03:
            return {"s": b + [0xe9]}
        return {"b": b}


def alpha_dec(x):
    if x is None:
        return None
    return bytes(x["b"]) if "b" in x else 3


def kw_of(c, names):
    """The optional arguments the case gives: `strict`, `alpha` and `ig` have their own encodings."""
    kw = {}
    for k in names:
        if c.get(k) is None:
            continue
        if k == "alpha":
            kw["alphabet"] = alpha_dec(c[k])
        elif k == "ig":
            kw["ignorechars"] = data_dec(c[k])
        elif k == "strict":
            kw["strict_mode"] = c[k]
        else:
            kw[k] = c[k]
    return kw


@area("binascii", 3)
class BinasciiArea(Codec):
    WRAP = [0, 0, 0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 16, 76, 77, 2**64 - 1, 2**64, -1]

    @classmethod
    def perm(cls, r, a):
        a = list(a)
        r.shuffle(a)
        return a

    @classmethod
    def alpha_arg(cls, r, n, base, std=None):
        k = r.random()
        if k < 0.5:
            return None
        if k < 0.65:
            return {"b": list(base)}
        if k < 0.8:
            return {"b": cls.perm(r, base)}
        if k < 0.85:
            a = list(base)
            a[r.randrange(n)] = 61
            return {"b": a}
        if k < 0.9:
            a = list(base)
            a[0] = a[1]
            return {"b": a}
        if k < 0.95:
            return {"b": list(base)[:r.choice([0, 1, n - 1])] + list(base)[:r.choice([0, 0, 2])]}
        return {"ty": "int"}

    @classmethod
    def ig_arg(cls, r):
        return r.choice([None, None, {"b": []}, {"b": [10]}, {"b": [10, 13, 32]}, {"b": [61]}, {"b": [61, 10]}, {"b": [97, 98]}, {"b": [255, 0]}, {"nb": "int"},
                         {"rz": ["ValueError", "boom"]}])

    @classmethod
    def enc(cls, f, d, **kw):
        kw = {k: v for k, v in kw.items() if v is not None}
        try:
            return f(bytes(d), **kw)
        except Exception:
            return b""

    @classmethod
    def new_codec(cls, r, c, fn, d):
        pad_opts = r.random() < 0.5
        if fn == "a2b_base64":
            c.update(strict=r.choice([None, True, False]), padded=r.choice([True, True, False]), canonical=r.random() < 0.3,
                     alpha=cls.alpha_arg(r, 64, cls.B64), ig=cls.ig_arg(r))
            a = alpha_dec(c["alpha"])
            t = cls.enc(binascii.b2a_base64, d, alphabet=a if isinstance(a, bytes) else None, newline=False, padded=r.random() < 0.7,
                        wrapcol=r.choice([0, 0, 4, 8]))
            c["d"] = cls.wrap(r, cls.corrupt(r, t, cls.B64) if r.random() < 0.7 else t)
        elif fn == "b2a_base64":
            c.update(padded=r.random() < 0.7, wrapcol=r.choice(cls.WRAP), newline=r.random() < 0.5, alpha=cls.alpha_arg(r, 64, cls.B64))
            c["d"] = d
            if isinstance(c["alpha"], dict) and "ty" in c["alpha"]:
                c["alpha"] = {"nb": "int"}
        elif fn == "a2b_base32":
            c.update(padded=r.choice([True, True, False]), canonical=r.random() < 0.3, alpha=cls.alpha_arg(r, 32, cls.B32), ig=cls.ig_arg(r))
            a = alpha_dec(c["alpha"])
            t = cls.enc(binascii.b2a_base32, d, alphabet=a if isinstance(a, bytes) else None, padded=r.random() < 0.7, wrapcol=r.choice([0, 0, 8, 16]))
            c["d"] = cls.wrap(r, cls.corrupt(r, t, cls.B32) if r.random() < 0.7 else t)
        elif fn == "b2a_base32":
            c.update(padded=r.random() < 0.7, wrapcol=r.choice(cls.WRAP), alpha=cls.alpha_arg(r, 32, cls.B32))
            c["d"] = d + [r.randrange(256) for _ in range(r.choice([0, 0, 1, 2, 3, 4, 5, 6]))]
            if isinstance(c["alpha"], dict) and "ty" in c["alpha"]:
                c["alpha"] = {"nb": "int"}
        elif fn == "a2b_ascii85":
            c.update(foldspaces=r.random() < 0.5, adobe=r.random() < 0.3, canonical=r.random() < 0.4, ig=cls.ig_arg(r))
            t = cls.enc(binascii.b2a_ascii85, cls.spacey(r, d), foldspaces=c["foldspaces"], adobe=c["adobe"], pad=r.random() < 0.3,
                        wrapcol=r.choice([0, 0, 3, 7]))
            c["d"] = cls.wrap(r, cls.corrupt(r, t, b"!uvzyxs~<> \t\n") if r.random() < 0.6 else list(t))
        elif fn == "b2a_ascii85":
            c.update(foldspaces=r.random() < 0.5, adobe=r.random() < 0.4, pad=r.random() < 0.3, wrapcol=r.choice(cls.WRAP))
            c["d"] = cls.spacey(r, d)
        elif fn == "a2b_base85":
            c.update(canonical=r.random() < 0.4, alpha=cls.alpha_arg(r, 85, base64.binascii.BASE85_ALPHABET), ig=cls.ig_arg(r))
            a = alpha_dec(c["alpha"])
            t = cls.enc(binascii.b2a_base85, d, alphabet=a if isinstance(a, bytes) else None, pad=r.random() < 0.3, wrapcol=r.choice([0, 0, 5, 10]))
            c["d"] = cls.wrap(r, cls.corrupt(r, t, b"~}|0Az ,.") if r.random() < 0.6 else list(t))
            if r.random() < 0.1:
                c["d"] = {"b": r.choice([[126] * 5, [124, 78, 115, 67, 48], [124, 78, 115, 67, 47], [48], [0]])}
        elif fn == "b2a_base85":
            c.update(pad=r.random() < 0.4, wrapcol=r.choice(cls.WRAP), alpha=cls.alpha_arg(r, 85, base64.binascii.BASE85_ALPHABET))
            c["d"] = d
            if isinstance(c["alpha"], dict) and "ty" in c["alpha"]:
                c["alpha"] = {"nb": "int"}

    @staticmethod
    def spacey(r, d):
        if r.random() < 0.4:
            return r.choice([[0, 0, 0, 0], [32, 32, 32, 32], [0, 0, 0, 0, 1], [32, 32, 32, 32, 0, 0], [1, 2, 3], [0], [0, 0], [0, 0, 0]]) + d[:r.choice([0, 4, 8])]
        return d

    @classmethod
    def gen(cls, r):
        d = cls.raw(r)
        fn = r.choice(["a2b_base64", "a2b_base64", "a2b_base64", "b2a_base64", "a2b_hex", "b2a_hex",
                       "a2b_uu", "a2b_uu", "a2b_uu", "b2a_uu", "crc_hqx", "a2b_qp", "a2b_qp", "b2a_qp",
                       "b2a_qp", "b2a_qp", "qp_bound", "qp_bound", "api", "flag", "hex", "hex",
                       "a2b_base64", "b2a_base64", "a2b_base32", "a2b_base32", "b2a_base32", "a2b_ascii85", "a2b_ascii85", "b2a_ascii85",
                       "a2b_base85", "a2b_base85", "b2a_base85", "a2b_hex"])
        c = {"mod": "textlibs", "fn": "binascii." + fn}
        if fn in ("a2b_base32", "b2a_base32", "a2b_ascii85", "b2a_ascii85", "a2b_base85", "b2a_base85") or \
                (fn in ("a2b_base64", "b2a_base64") and r.random() < 0.7):
            cls.new_codec(r, c, fn, d)
            return c
        if fn == "api":
            c["op"] = r.choice(["b2a_base64", "a2b_base64", "a2b_hex", "a2b_uu", "b2a_uu", "crc_hqx", "a2b_qp", "b2a_qp"])
            c["d"] = bad_data(r)
            return c
        if fn == "flag":
            c["op"] = r.choice(["b2a_base64", "a2b_base64", "b2a_uu", "a2b_qp", "b2a_qp1", "b2a_qp2", "b2a_qp3"])
            c["d"] = {"b": [97, 98, 99, 100]} if r.random() < 0.8 else bad_data(r)
            c["f"] = r.choice([True, False, {"raise": ["ValueError", "boom"]}, {"raise": ["TypeError", "boom"]}])
            return c
        if fn == "hex":
            c["d"] = {"b": d} if r.random() < 0.9 else bad_data(r)
            c["sep"] = r.choice([None, {"s": [58]}, {"b": [58]}, {"s": [97]}, {"s": [233]}, {"s": [0x20ac]}, {"b": [200]}, {"s": []}, {"b": []},
                                 {"s": [58, 59]}, {"b": [58, 59]}, {"len": 1}, {"len": 2}, {"len": 0}, {"raise": ["ValueError", "boom"]}])
            c["group"] = r.choice([0, 1, 2, 3, 4, 5, -1, -2, -3, -4, 7, 100, -100, 2**31 - 1, -2**31, 2**31, -2**31 - 1, 2**70,
                                   {"raise": ["ValueError", "boom"]}])
            return c
        if fn in ("b2a_qp", "qp_bound"):
            c.update(cls.qp_input(r))
            return c
        if fn == "a2b_qp":
            c["header"] = r.random() < 0.3
            t = binascii.b2a_qp(bytes(cls.qp_input(r)["d"]), quotetabs=r.random() < 0.5,
                                istext=r.random() < 0.5)
            pool = b"=_ \t\r\n0aFgZ"
            c["d"] = cls.wrap(r, cls.corrupt(r, t, pool) + r.choice([[], [], [61], [61, 13], [61, 65]]))
            return c
        if fn == "crc_hqx":
            c["d"] = d
            c["crc"] = r.choice([0, 1, 0xffff, 0x10000, 2**32 - 1, 2**32, 2**70 + 5, -1, -2**40, r.getrandbits(16)])
            return c
        if fn == "b2a_uu":
            c["d"] = [r.randrange(256) for _ in range(r.choice([0, 1, 2, 3, 44, 45, 46, 60]))]
            c["backtick"] = r.random() < 0.5
            return c
        if fn == "a2b_uu":
            n = min(len(d), 45)
            t = binascii.b2a_uu(bytes(d[:n]), backtick=r.random() < 0.5)
            b = list(t)
            roll = r.random()
            if roll < 0.2:
                b = b[:r.randint(0, len(b))]
            elif roll < 0.5:
                b = cls.corrupt(r, b, bytes(range(32, 97)))
            elif roll < 0.6:
                b = b + [r.choice([32, 96, 10, 13, 65, 0])]
            c["d"] = cls.wrap(r, b)
            return c
        if fn == "a2b_base64":
            c["strict"] = r.random() < 0.5
            t = binascii.b2a_base64(bytes(d), newline=False)
            c["d"] = cls.wrap(r, cls.corrupt(r, t, cls.B64))
        elif fn == "a2b_hex":
            t = binascii.hexlify(bytes(d))
            c["d"] = cls.wrap(r, cls.corrupt(r, t, b"0123456789abcdefABCDEFgG"))
            c["ig"] = cls.ig_arg(r)
        elif fn == "b2a_base64":
            c["d"], c["newline"] = d, r.random() < 0.5
        else:
            c["d"] = d
        return c

    @classmethod
    def qp_input(cls, r):
        n = r.choice([0, 1, 2, 5, 20, 74, 75, 76, 77, 78, 150, 160])
        pool = [97, 98, 32, 9, 10, 13, 61, 95, 46, 0, 127, 200, 126, 33]
        weights = [40, 10, 6, 3, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1]
        d = r.choices(pool, weights, k=n)
        if r.random() < 0.3 and n >= 2:
            d[-2:] = r.choice([[32, 10], [9, 10], [32, 13], [13, 10], [10, 10], [46, 10], [46, 0], [46, 13]])
        if r.random() < 0.3 and n > 3:
            i = r.randrange(n - 2)
            d[i:i + 2] = r.choice([[13, 10], [10, 46], [32, 10], [9, 13], [32, 9]])
        return {"d": d, "quotetabs": r.random() < 0.3, "istext": r.random() < 0.7, "header": r.random() < 0.3}

    @classmethod
    def run(cls, c):
        fn = c["fn"].split(".")[1]

        def body():
            if fn == "api":
                x = data_dec(c["d"])
                op = c["op"]
                if op == "crc_hqx":
                    return [binascii.crc_hqx(x, 0)]
                if op == "b2a_qp":
                    return list(binascii.b2a_qp(x))
                return list(getattr(binascii, op)(x))
            if fn == "flag":
                x, f, op = data_dec(c["d"]), flag_dec(c["f"]), c["op"]
                if op == "b2a_base64":
                    return list(binascii.b2a_base64(x, newline=f))
                if op == "a2b_base64":
                    return list(binascii.a2b_base64(x, strict_mode=f))
                if op == "b2a_uu":
                    return list(binascii.b2a_uu(x, backtick=f))
                if op == "a2b_qp":
                    return list(binascii.a2b_qp(x, header=f))
                k = {"b2a_qp1": "quotetabs", "b2a_qp2": "istext", "b2a_qp3": "header"}[op]
                return list(binascii.b2a_qp(x, **{k: f}))
            if fn == "hex":
                x = data_dec(c["d"])
                f = r_hex(c)
                return list(f(x))
            if fn == "qp_bound":
                return True
            if fn == "a2b_uu":
                return list(binascii.a2b_uu(data_dec(c["d"])))
            if fn == "b2a_uu":
                return list(binascii.b2a_uu(bytes(c["d"]), backtick=c["backtick"]))
            if fn == "crc_hqx":
                return [binascii.crc_hqx(bytes(c["d"]), c["crc"])]
            if fn == "a2b_qp":
                return list(binascii.a2b_qp(data_dec(c["d"]), header=c["header"]))
            if fn == "b2a_qp":
                return list(binascii.b2a_qp(bytes(c["d"]), quotetabs=c["quotetabs"], istext=c["istext"],
                                            header=c["header"]))
            if fn == "a2b_base64":
                return list(binascii.a2b_base64(data_dec(c["d"]), **kw_of(c, ["strict", "padded", "alpha", "ig", "canonical"])))
            if fn == "b2a_base64":
                kw = kw_of(c, ["padded", "wrapcol", "newline"])
                if c.get("alpha") is not None:
                    kw["alphabet"] = data_dec(c["alpha"])
                return list(binascii.b2a_base64(bytes(c["d"]), **kw))
            if fn == "a2b_base32":
                return list(binascii.a2b_base32(data_dec(c["d"]), **kw_of(c, ["padded", "alpha", "ig", "canonical"])))
            if fn in ("b2a_base32", "b2a_base85"):
                kw = kw_of(c, ["padded", "wrapcol", "pad"])
                if c.get("alpha") is not None:
                    kw["alphabet"] = data_dec(c["alpha"])
                return list(getattr(binascii, fn)(bytes(c["d"]), **kw))
            if fn == "a2b_ascii85":
                return list(binascii.a2b_ascii85(data_dec(c["d"]), **kw_of(c, ["foldspaces", "adobe", "ig", "canonical"])))
            if fn == "b2a_ascii85":
                return list(binascii.b2a_ascii85(bytes(c["d"]), **kw_of(c, ["foldspaces", "wrapcol", "pad", "adobe"])))
            if fn == "a2b_base85":
                return list(binascii.a2b_base85(data_dec(c["d"]), **kw_of(c, ["alpha", "ig", "canonical"])))
            if fn == "a2b_hex":
                return list(binascii.a2b_hex(data_dec(c["d"]), **kw_of(c, ["ig"])))
            return list(binascii.b2a_hex(bytes(c["d"])))

        return common.py_result(body)


@area("base64", 3)
class Base64Area(Codec):
    @classmethod
    def gen(cls, r):
        d = cls.raw(r)
        fn = r.choice(["b64encode", "b64decode", "b64decode", "urlsafe_b64encode", "urlsafe_b64decode", "b32encode",
                       "b32hexencode", "b32decode", "b32decode", "b32decode", "b32hexdecode",
                       "b32hexdecode", "b16encode", "b16decode", "b16decode", "a85encode", "a85decode",
                       "a85decode", "b85encode", "b85decode", "b85decode", "z85encode", "z85decode", "z85decode",
                       "encodebytes", "decodebytes", "encode_file", "encode_file", "decode_file", "decode_file",
                       "standard_b64encode", "standard_b64decode", "input_check", "main_select", "any", "any"])
        c = {"mod": "textlibs", "fn": "base64." + fn}
        raw = bytes(d)
        if r.random() < 0.3:
            d = [r.choice([0, 0, 32, 32, 255]) for _ in range(r.choice([1, 2, 3, 4, 5, 7, 8, 9]))]
            raw = bytes(d)
        ig = r.choice([None, None, {"b": []}, {"b": [10]}, {"b": [10, 32]}, {"b": [61]}, {"b": [97, 98]}])
        if fn == "b64encode":
            c.update(d=d, alt=r.choice([None, None, {"b": [45, 95]}, {"b": [42, 33]}, {"b": [45]}, {"b": []}]), padded=r.random() < 0.7,
                     wrapcol=r.choice([0, 0, 0, 1, 3, 4, 5, 8, 76, -1, 2**64]))
            return c
        if fn == "a85encode":
            c.update(d=d, foldspaces=r.random() < 0.5, pad=r.random() < 0.3, adobe=r.random() < 0.4,
                     wrapcol=r.choice([0, 0, 1, 2, 3, 5, 7, 76, -1, -5]))
            return c
        if fn == "a85decode":
            fold, adobe = r.random() < 0.5, r.random() < 0.4
            t = base64.a85encode(raw, foldspaces=fold, adobe=r.random() < 0.8 if adobe else False,
                                 wrapcol=r.choice([0, 0, 3, 7]))
            b = list(t) if r.random() < 0.4 else cls.corrupt(r, t, b"!uvzyxs~<> \t\n")
            if r.random() < 0.1:
                b = r.choice([[60, 126, 62], [126, 62], [60, 126, 126, 62], [117] * 5, [115, 56, 87, 45, 34], [33]])
            c.update(d=cls.wrap(r, b), foldspaces=fold, adobe=adobe, canonical=r.random() < 0.3,
                     ignore=r.choice([[32, 9, 10, 13, 11], [32, 9, 10, 13, 11], [], [122], [117, 10]]))
            return c
        if fn == "b85encode":
            c.update(d=d, pad=r.random() < 0.4, wrapcol=r.choice([0, 0, 1, 5, 7, 10, -1]))
            return c
        if fn == "z85encode":
            c.update(d=d, pad=r.random() < 0.4, wrapcol=r.choice([0, 0, 1, 5, 7, 10, -1]))
            return c
        if fn == "b85decode":
            b = list(base64.b85encode(raw, pad=r.random() < 0.3))
            b = b if r.random() < 0.4 else cls.corrupt(r, b, b"~}|0Az ,.")
            if r.random() < 0.1:
                b = r.choice([[126] * 5, [124, 78, 115, 67, 48], [124, 78, 115, 67, 47], [48], [0]])
            c["d"] = cls.wrap(r, b)
            c.update(ig=ig, canonical=r.random() < 0.3)
            return c
        if fn == "z85decode":
            b = list(base64.z85encode(raw))
            c["d"] = cls.wrap(r, b if r.random() < 0.4 else cls.corrupt(r, b, b";_`|~#%0 "))
            c.update(ig=ig, canonical=r.random() < 0.3)
            return c
        if fn == "any":
            c["name"] = r.choice(["b64encode", "standard_b64encode", "urlsafe_b64encode", "b32encode", "b32hexencode", "b16encode",
                                  "a85encode", "b85encode", "z85encode", "encodebytes", "decodebytes"])
            c["d"] = bad_data(r)
            return c
        if fn == "encode_file":
            c["d"] = [r.randrange(256) for _ in range(r.choice([0, 1, 10, 56, 57, 58, 113, 114, 115, 200]))]
            c["reads"] = []
            for _ in range(r.choice([0, 0, 1, 2, 4, 8])):
                c["reads"].append(r.choice([{"give": r.choice([0, 1, 2, 10, 56, 57, 100])}, {"give": 3}, {"give": 20},
                                            {"raise": ["ValueError", "boom"]}]))
            c["writes"] = [r.choice([None, None, None, {"raise": ["OSError", "boom"]}]) for _ in range(r.choice([0, 0, 1, 2]))]
            return c
        if fn == "decode_file":
            t = base64.encodebytes(bytes(r.randrange(256) for _ in range(r.choice([0, 3, 57, 60, 120]))))
            lines = [list(x) for x in t.splitlines(True)]
            if r.random() < 0.3 and lines:
                lines[r.randrange(len(lines))] = [33, 61]
            if r.random() < 0.2:
                lines.insert(r.randint(0, len(lines)), {"raise": ["ValueError", "boom"]})
            if r.random() < 0.15:
                lines.insert(r.randint(0, len(lines)), [])
            c["lines"] = lines
            c["writes"] = [r.choice([None, None, {"raise": ["OSError", "boom"]}]) for _ in range(r.choice([0, 0, 1, 2]))]
            return c
        if fn == "encodebytes":
            c["d"] = [r.randrange(256) for _ in range(r.choice([0, 1, 56, 57, 58, 113, 114, 115, 200]))]
            return c
        if fn == "decodebytes":
            t = base64.encodebytes(bytes(r.randrange(256) for _ in range(r.choice([0, 3, 57, 60, 120]))))
            c["d"] = list(t) if r.random() < 0.5 else cls.corrupt(r, t, cls.B64 + b"\n")
            c["d"] = [x if x < 256 else 0 for x in c["d"]]
            return c
        if fn == "standard_b64encode":
            c["d"] = d
            return c
        if fn == "standard_b64decode":
            c["d"] = cls.wrap(r, cls.corrupt(r, base64.b64encode(raw), cls.B64))
            return c
        if fn == "input_check":
            c.update(r.choice([{"kind": "none", "cls": "str"}, {"kind": "none", "cls": "int"},
                               {"kind": "view", "format": "i", "ndim": 1, "cls": "array"},
                               {"kind": "view", "format": "B", "ndim": 2, "cls": "memoryview"},
                               {"kind": "view", "format": "B", "ndim": 1, "cls": "bytes"},
                               {"kind": "view", "format": "b", "ndim": 1, "cls": "memoryview"},
                               {"kind": "view", "format": "c", "ndim": 1, "cls": "memoryview"}]))
            return c
        if fn == "main_select":
            c["flags"] = [r.choice(["-e", "-d", "-u", "-h"]) for _ in range(r.randrange(0, 4))]
            return c
        if fn == "b64decode":
            c["validate"] = r.random() < 0.5
            alt = r.choice([None, None, {"b": [45, 95]}, {"s": [45, 95]}, {"b": [42, 33]}, {"b": [45]}])
            t = base64.b64encode(raw)
            if alt is not None and len(data_dec(alt)) == 2:
                a = data_dec(alt)
                a = a.encode() if isinstance(a, str) else a
                t = base64.b64encode(raw, a)
            c["alt"] = alt
            c["d"] = cls.wrap(r, cls.corrupt(r, t, cls.B64))
            if r.random() < 0.5:
                c.update(validate=r.choice([None, True, False]), padded=r.random() < 0.7, ig=ig, canonical=r.random() < 0.3)
        elif fn == "urlsafe_b64encode":
            c.update(d=d, padded=r.random() < 0.7)
        elif fn == "urlsafe_b64decode":
            c["d"] = cls.wrap(r, cls.corrupt(r, base64.urlsafe_b64encode(raw), cls.B64 + b"-_"))
            c["padded"] = r.random() < 0.3
        elif fn in ("b32encode", "b32hexencode"):
            c.update(d=d, padded=r.random() < 0.7, wrapcol=r.choice([0, 0, 1, 8, 9, 16, -1]))
        elif fn in ("b32decode", "b32hexdecode"):
            hexa = fn == "b32hexdecode"
            t = (base64.b32hexencode if hexa else base64.b32encode)(raw)
            if r.random() < 0.3:
                t = t.lower()
            c["casefold"] = r.random() < 0.5
            alpha = cls.B32H if hexa else cls.B32
            c["d"] = cls.wrap(r, t if r.random() < 0.3 else cls.corrupt(r, t, alpha))
            if not hexa:
                c["map01"] = r.choice([None, None, None, {"b": [76]}, {"s": [73]}, {"b": [76, 76]}])
            c.update(padded=r.random() < 0.7, ig=ig, canonical=r.random() < 0.3)
        elif fn == "b16encode":
            c.update(d=d, wrapcol=r.choice([0, 0, 1, 2, 3, 4, 5, 8, -1, 2**64]))
        elif fn == "b16decode":
            t = base64.b16encode(raw)
            if r.random() < 0.3:
                t = t.lower()
            c["casefold"] = r.random() < 0.5
            c["d"] = cls.wrap(r, t if r.random() < 0.3 else cls.corrupt(r, t, b"0123456789ABCDEFabcdef"))
            c["ig"] = ig
        else:
            c["d"] = d
        return c

    @classmethod
    def run(cls, c):
        fn = c["fn"].split(".")[1]

        def body():
            if fn == "input_check":
                return _type_check_probe(c)
            if fn == "main_select":
                return _main_probe(c["flags"])
            if fn == "any":
                return list(getattr(base64, c["name"])(data_dec(c["d"])))
            if fn in ("encode_file", "decode_file"):
                f = file_read(c)
                try:
                    (base64.encode if fn == "encode_file" else base64.decode)(f, f)
                    res = {"ok": None}
                except Exception as e:
                    res = {"exc": type(e).__name__, "msg": str(e)}
                return {"written": f.written, "res": res}
            f = getattr(base64, fn)
            if fn == "b64encode":
                return list(f(bytes(c["d"]), altchars=data_dec(c.get("alt")), padded=c["padded"], wrapcol=c["wrapcol"]))
            if fn == "urlsafe_b64encode":
                return list(f(bytes(c["d"]), padded=c["padded"]))
            if fn in ("b32encode", "b32hexencode"):
                return list(f(bytes(c["d"]), padded=c["padded"], wrapcol=c["wrapcol"]))
            if fn == "b16encode":
                return list(f(bytes(c["d"]), wrapcol=c["wrapcol"]))
            if fn == "z85encode":
                return list(f(bytes(c["d"]), pad=c["pad"], wrapcol=c["wrapcol"]))
            if fn == "a85encode":
                return list(f(bytes(c["d"]), foldspaces=c["foldspaces"], wrapcol=c["wrapcol"], pad=c["pad"],
                              adobe=c["adobe"]))
            if fn == "a85decode":
                return list(f(data_dec(c["d"]), foldspaces=c["foldspaces"], adobe=c["adobe"],
                              ignorechars=bytes(c["ignore"]), canonical=c["canonical"]))
            if fn == "b85encode":
                return list(f(bytes(c["d"]), pad=c["pad"], wrapcol=c["wrapcol"]))
            if fn in ("b85decode", "z85decode"):
                return list(f(data_dec(c["d"]), **kw_of(c, ["ig", "canonical"])))
            if fn == "standard_b64decode":
                return list(f(data_dec(c["d"])))
            if fn == "decodebytes":
                return list(f(bytes(c["d"])))
            if fn == "b64decode":
                return list(f(data_dec(c["d"]), altchars=data_dec(c.get("alt")), **kw_of(c, ["validate", "padded", "ig", "canonical"])))
            if fn == "urlsafe_b64decode":
                return list(f(data_dec(c["d"]), padded=c["padded"]))
            if fn == "b32decode":
                return list(f(data_dec(c["d"]), casefold=c["casefold"], map01=data_dec(c.get("map01")), **kw_of(c, ["padded", "ig", "canonical"])))
            if fn == "b32hexdecode":
                return list(f(data_dec(c["d"]), casefold=c["casefold"], **kw_of(c, ["padded", "ig", "canonical"])))
            if fn == "b16decode":
                return list(f(data_dec(c["d"]), casefold=c["casefold"], **kw_of(c, ["ig"])))
            return list(f(bytes(c["d"])))

        return common.py_result(body)


def _type_check_probe(c):
    if c["kind"] == "none":
        arg = "x" if c["cls"] == "str" else 3
    elif c["format"] == "i":
        arg = array.array("i", [1])
    elif c["ndim"] == 2:
        arg = memoryview(bytes(4)).cast("B", (2, 2))
    elif c["cls"] == "bytes":
        arg = b"a"
    else:
        arg = memoryview(b"a").cast(c["format"])
    base64._input_type_check(arg)
    return None


def _main_probe(flags):
    """Which function `main` runs, with the two callees replaced by recorders."""
    seen = []
    saved = base64.encode, base64.decode, sys.argv, sys.stdin, sys.stdout
    with tempfile.NamedTemporaryFile() as tf:
        base64.encode = lambda i, o: seen.append("encode")
        base64.decode = lambda i, o: seen.append("decode")
        sys.argv = ["base64"] + flags + [tf.name]
        sys.stdout = io.TextIOWrapper(io.BytesIO())
        try:
            base64.main()
        finally:
            base64.encode, base64.decode, sys.argv, sys.stdin, sys.stdout = saved
    return seen[0] if seen else None


# ---- csv -------------------------------------------------------------------

import csv
import _csv
import json


def cps(t):
    return [ord(c) for c in t]


def txt(l):
    return "".join(map(chr, l))


class NotNum:
    def __init__(self, t):
        self.t = t

    def __str__(self):
        return self.t


class CsvCtx:
    reader = None
    writer = None


EXCS = {"ValueError": ValueError, "TypeError": TypeError, "ZeroDivisionError": ZeroDivisionError,
        "AttributeError": AttributeError, "OSError": OSError}


def mk_exc(x):
    return EXCS[x[0]](x[1])


def run_eff(e, ctx):
    try:
        if e["e"] == "advance":
            next(ctx.reader)
        elif e["e"] == "limit":
            csv.field_size_limit(csv_obj(e["n"], ctx))
        else:
            ctx.writer.writerow(csv_obj(e["row"], ctx))
    except Exception:
        pass


class Scripted:
    def __init__(self, steps, ctx):
        self.steps, self.ctx, self.i = steps, ctx, 0

    def __iter__(self):
        return self

    def __next__(self):
        while self.i < len(self.steps):
            st = self.steps[self.i]
            self.i += 1
            if "s" in st:
                return txt(st["s"])
            k = st.get("k")
            if k == "eff":
                run_eff(st["e"], self.ctx)
            elif k == "ret":
                return csv_obj(st["o"], self.ctx)
            elif k == "raise":
                raise mk_exc(st["x"])
            elif k == "stop":
                raise StopIteration
            else:
                return 7
        raise StopIteration


def key_hash(k):
    if k is None:
        return 12345
    if "hash" in k:
        raise mk_exc(k["hash"])
    if "eq" in k:
        return hash("excel")
    return hash(txt(k["k"]))


def key_eq(k, other):
    if k is None:
        return False
    if "eq" in k:
        raise mk_exc(k["eq"])
    return isinstance(other, str) and txt(k["k"]) == other


class Other:
    __module__ = "m"

    def __init__(self, spec, ctx):
        self.__dict__["_spec"], self.__dict__["_ctx"] = spec, ctx

    def __bool__(self):
        t = self._spec["truth"]
        if "raise" in t:
            raise mk_exc(t["raise"])
        return t["ok"]

    def __hash__(self):
        return key_hash(self._spec["key"])

    def __eq__(self, other):
        return key_eq(self._spec["key"], other)

    def __getattr__(self, n):
        for k, v in self._spec["attrs"]:
            if k == n:
                if "raise" in v:
                    raise mk_exc(v["raise"])
                return csv_obj(v["ok"], self._ctx)
        raise AttributeError(n)

    def __str__(self):
        st = self._spec["str"]
        for e in st["effs"]:
            run_eff(e, self._ctx)
        if "raise" in st["res"]:
            raise mk_exc(st["res"]["raise"])
        return txt(st["res"]["ok"])

    def __iter__(self):
        it = self._spec["iter"]
        if "raise" in it:
            raise mk_exc(it["raise"])
        return Scripted(it["ok"], self._ctx)


class OtherNum(Other):
    def __float__(self):
        return 1.0


OtherNum.__qualname__ = OtherNum.__name__ = "Other"
OtherNum.__module__ = "m"


class Sub(str):
    __module__ = "m"

    def __new__(cls, t, key):
        o = super().__new__(cls, t)
        o.key = key
        return o

    def __hash__(self):
        return key_hash(self.key)

    def __eq__(self, other):
        return key_eq(self.key, other)


class WriteFn:
    def __init__(self, calls, ctx):
        self.calls, self.ctx, self.i = calls, ctx, 0

    def __call__(self, line):
        self.ctx.written.append(cps(line))
        if self.i >= len(self.calls):
            return None
        c = self.calls[self.i]
        self.i += 1
        for e in c["effs"]:
            run_eff(e, self.ctx)
        if "raise" in c["res"]:
            raise mk_exc(c["res"]["raise"])
        return csv_obj(c["res"]["ok"], self.ctx)


def csv_obj(j, ctx=None):
    if j is None:
        return None
    if "s" in j:
        return txt(j["s"])
    if "i" in j:
        return j["i"]
    if "big" in j:
        return 10**4400
    if "b" in j:
        return j["b"]
    if "sub" in j:
        return Sub(txt(j["sub"]), j["key"])
    if "dsub" in j:
        return mk_dsub(j["dsub"], ctx)
    if "d" in j:
        return csv.get_dialect(txt(j["d"]))
    if "cls" in j:
        return getattr(csv, j["cls"])
    if "func" in j:
        return WriteFn(j["func"], ctx)
    if "spec" in j:
        return (OtherNum if j["spec"]["num"] else Other)(j["spec"], ctx)
    return {"list": [], "float": 1.5, "bytes": b"x"}.get(j["o"], [])


def in_child(fn):
    """Run fn in a forked child: a segfault is a result here, not the end of the run."""
    rd, wr = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(rd)
        try:
            out = fn()
        except BaseException as e:
            out = {"exc": type(e).__name__, "msg": str(e)}
        os.write(wr, json.dumps(out).encode())
        os._exit(0)
    os.close(wr)
    buf = b""
    while True:
        chunk = os.read(rd, 65536)
        if not chunk:
            break
        buf += chunk
    os.close(rd)
    _, status = os.waitpid(pid, 0)
    if os.WIFSIGNALED(status) or not buf:
        return {"exc": "SegmentationFault", "msg": ""}
    return json.loads(buf)


def enc_ret(x):
    if x is None:
        return None
    if type(x) is str:
        return {"s": cps(x)}
    if type(x) is bool:
        return {"b": x}
    if type(x) is int:
        return {"i": x}
    return {"obj": None}


def csv_kw(c, ctx=None):
    return {k: csv_obj(v, ctx) for k, v in c["args"].items()}


def csv_src(c, ctx=None):
    v = c.get("src")
    if v is None:
        return ()
    return (txt(v),) if isinstance(v, list) else (csv_obj(v, ctx),)


def mk_dsub(spec, ctx):
    """An instance of a `_csv.Dialect` subclass: its class attributes, and what `__init__` does when
    `type_call` runs it again."""
    ns = {"__module__": "m"}

    def raiser(exc):
        def f(self, *a):
            raise mk_exc(exc)
        return f
    for name, res in spec["attrs"]:
        if name.startswith("__reduce"):
            ns[name] = raiser(res["raise"]) if "raise" in res else (lambda self, *a: None)
        elif "raise" in res:
            ns[name] = property(raiser(res["raise"]))
        else:
            ns[name] = csv_obj(res["ok"], ctx)
    init = spec["init"]

    def __init__(self, *a, **k):
        if getattr(self, "_ready", False) and "raise" in init:
            raise mk_exc(init["raise"])
    ns["__init__"] = __init__
    inst = type("DSub", (_csv.Dialect,), ns)(**{k: csv_obj(v, ctx) for k, v in spec["base"]})
    inst._ready = True
    return inst


class Hook:
    """An object whose `__bool__` changes the registry, inside `_call_dialect`."""

    def __init__(self, ops, ctx):
        self.ops, self.ctx = ops, ctx

    def __bool__(self):
        for d in self.ops:
            try:
                n = csv_obj(d["name"], self.ctx)
                if d["op"] == "reg":
                    csv.register_dialect(n, delimiter=";")
                else:
                    csv.unregister_dialect(n)
            except Exception:
                pass
        return True


def enc_dialect(d):
    """The C fields, through `_csv.Dialect`'s own descriptors, whatever a subclass shadows."""
    ch = lambda x: None if x is None else cps(x)
    g = lambda n: getattr(_csv.Dialect, n).__get__(d)
    return {"delimiter": ch(g("delimiter")), "doublequote": bool(g("doublequote")), "escapechar": ch(g("escapechar")),
            "lineterminator": cps(g("lineterminator")), "quotechar": ch(g("quotechar")), "quoting": int(g("quoting")),
            "skipinitialspace": bool(g("skipinitialspace")), "strict": bool(g("strict"))}


def enc_field(x):
    if x is None:
        return None
    if isinstance(x, str):
        return {"s": cps(x)}
    return {"f": float_bits(x)}


def norm_msg(m):
    if m.startswith("could not convert"):
        return "~could not convert string to float: "
    if "unexpected keyword argument" in m:
        return "~this function got an unexpected keyword argument"
    if m.startswith("dict contains fields"):
        return "~dict contains fields not in fieldnames"
    if m.startswith("extrasaction"):
        return "~extrasaction must be 'raise' or 'ignore'"
    if m.startswith("zip("):
        return "~zip() argument must support iteration"
    return m


def norm_exc(e):
    return [type(e).__name__, norm_msg(str(e))]


def spec_obj(r, depth=0):
    """A random object with fallible behaviour; the Lean side builds the same thing."""
    x = lambda: [r.choice(["ValueError", "TypeError", "ZeroDivisionError", "OSError"]), "boom"]
    res = lambda ok, p=0.25: {"raise": x()} if r.random() < p else {"ok": ok}
    attrs = []
    return {"o": "Other", "spec": {
        "truth": res(r.random() < 0.5),
        "key": r.choice([None, None, {"hash": x()}, {"eq": x()}, {"k": cps("excel")}]),
        "attrs": attrs, "num": r.random() < 0.3,
        "str": {"effs": [], "res": res(cps(r.choice(["", "s", "a,b", '"', "12"])))},
        "iter": res([], 0.5)}}


@area("csv", 6)
class CsvArea:
    CHARS = [",", ";", "\t", " ", "|", "x", "'", '"', "\\", "\r", "\n", "=", "\xe9", "€", "\U0001f600"]
    TEXT = 'ab, "\'\\\t|;x1 \r\n'

    @classmethod
    def jchar(cls, r):
        return {"s": cps(r.choice(cls.CHARS))}

    @classmethod
    def args(cls, r, valid):
        a = {}
        if r.random() < 0.6:
            a["delimiter"] = {"s": cps(r.choice([",", ";", "\t", " ", "|", "x"]))}
        if r.random() < 0.5:
            a["quotechar"] = r.choice([None, {"s": cps('"')}, {"s": cps("'")}, {"s": cps("|")}])
        if r.random() < 0.5:
            a["escapechar"] = r.choice([None, {"s": cps("\\")}, {"s": cps("x")}, {"s": cps("|")}])
        if r.random() < 0.5:
            a["doublequote"] = {"b": r.random() < 0.5}
        if r.random() < 0.5:
            a["skipinitialspace"] = {"b": r.random() < 0.5}
        if r.random() < 0.5:
            a["strict"] = {"b": r.random() < 0.5}
        if r.random() < 0.6:
            a["quoting"] = {"i": r.randrange(6)}
        if r.random() < 0.4:
            a["lineterminator"] = {"s": cps(r.choice(["\r\n", "\n", "\r", "|", "", "xy", "\r\r"]))}
        if not valid and r.random() < 0.7:
            k = r.choice(["delimiter", "quotechar", "escapechar", "lineterminator", "quoting", "doublequote"])
            a[k] = r.choice([None, {"s": []}, {"s": cps("ab")}, {"i": 3}, {"i": 7}, {"i": -1}, {"i": 2**40}, {"b": True},
                             {"o": "list", "t": False}, {"o": "float", "t": True}, {"o": "bytes", "t": True},
                             {"s": cps("\r")}, {"s": cps("\n")}, {"s": cps(" ")}, {"s": cps(",")}, {"s": cps('"')}])
        return a

    @classmethod
    def valid_args(cls, r):
        for _ in range(40):
            a = cls.args(r, True)
            try:
                csv.reader([], **csv_kw({"args": a}))
                return a
            except Exception:
                pass
        return {}

    @classmethod
    def text(cls, r, numeric):
        if numeric and r.random() < 0.6:
            return r.choice(["1", "2.5", "-3", "1e5", "0", " 4", "5 ", ".5", "5.", "1_000", "inf", "-Infinity", "nan",
                             "1e400", "1e-400", "0.1", "abc", "", "1__0", "_1", "1_", "+7", "e5", ".", "1e", "1e+2",
                             "9007199254740993", "123456789012345678901234567890", "\U00010d40", "\U000116da", "\U00010d41\U00010d42"])
        pool = cls.TEXT if numeric else cls.TEXT + "\xe9€"
        return "".join(r.choice(pool) for _ in range(r.choice([0, 0, 1, 1, 2, 3, 5, 8])))

    SNIFF = ['a', 'b', '1', ',', ';', '\t', ' ', '"', "'", '\n', '\n', '\r\n', '\r', '|', ':', 'x y', '""', '1.5', ',"', '",', ';"',
             '";', "'\n", "\n'", '\n"', '"\n', ', "', '\xe9', "''", '\\', ', ']

    @classmethod
    def gen_sniff(cls, r):
        if r.random() < 0.3:
            # rows with a common shape, over more than one chunk
            row = "".join(r.choice(cls.SNIFF) for _ in range(r.randint(1, 8))).replace("\n", "").replace("\r", "")
            alt = "".join(r.choice(cls.SNIFF) for _ in range(r.randint(1, 8))).replace("\n", "").replace("\r", "")
            s = "\n".join(r.choice([row, row, row, alt]) for _ in range(r.choice([2, 3, 9, 10, 11, 12, 25])))
        else:
            s = "".join(r.choice(cls.SNIFF) for _ in range(r.randint(0, 16)))
        return {"mod": "textlibs", "fn": "csv.sniff", "s": cps(s),
                "delims": r.choice([None, None, None, cps(",;"), cps(","), cps("\t"), cps("abc"), cps(":|"), cps('"'), []])}

    @classmethod
    def dsub(cls, r):
        exc = r.choice([["ValueError", "boom"], ["TypeError", "DSub.__init__() takes 1 positional argument but 2 were given"]])
        base = r.choice([[], [], [["delimiter", {"s": cps(";")}]], [["lineterminator", {"s": cps("\n")}]],
                         [["lineterminator", {"sub": cps("\r"), "key": None}]], [["quotechar", None]], [["quoting", {"i": 1}]]])
        pool = [["delimiter", {"ok": {"s": cps("|")}}], ["delimiter", {"raise": ["ValueError", "boom"]}], ["quotechar", {"ok": None}],
                ["strict", {"ok": {"b": True}}], ["quoting", {"ok": {"i": 3}}], ["lineterminator", {"ok": {"s": cps("\n")}}],
                ["doublequote", {"raise": ["TypeError", "boom"]}], ["delimiter", {"ok": {"i": 1}}], ["__reduce__", {"ok": None}],
                ["__reduce_ex__", {"raise": ["ValueError", "boom"]}]]
        attrs = {}
        for x in r.sample(pool, r.choice([0, 0, 1, 2, 3])):
            attrs[x[0]] = x[1]
        return {"dsub": {"base": base, "attrs": [[k, v] for k, v in attrs.items()],
                         "init": r.choice([{"ok": None}, {"ok": None}, {"raise": exc}])}}

    @classmethod
    def gen_dobj(cls, r):
        names = [{"s": cps("mine")}, {"s": cps("excel")}, {"s": cps("zz")}, {"sub": cps("mine"), "key": None},
                 {"sub": cps("mine"), "key": {"k": cps("mine")}}, {"sub": cps("q"), "key": {"k": cps("excel")}},
                 {"sub": cps("e"), "key": {"eq": ["ValueError", "boom"]}}, {"sub": cps("h"), "key": {"hash": ["ValueError", "boom"]}},
                 {"sub": cps("t"), "key": {"hash": ["TypeError", "boom"]}}]
        k = r.choice(["regseq", "regseq", "pickle", "ltget", "readerd", "writerd", "dialect"])
        c = {"mod": "textlibs", "fn": "csv." + k}
        if k == "regseq":
            ops = []
            for _ in range(r.randint(1, 5)):
                op = r.choice(["register", "register", "get", "unregister"])
                o = {"op": op, "name": r.choice(names)}
                if op == "register":
                    o["during"] = [{"op": r.choice(["reg", "unreg"]), "name": r.choice(names)} for _ in range(r.choice([0, 0, 1, 2]))]
                ops.append(o)
            c["ops"] = ops
        elif k == "pickle":
            c["obj"] = r.choice([cls.dsub(r), cls.dsub(r), {"d": cps("excel")}])
            c["method"] = r.choice(["__reduce__", "__reduce_ex__"])
        elif k == "ltget":
            c["obj"] = cls.dsub(r)
        else:
            c["src"] = r.choice([cls.dsub(r), cls.dsub(r), {"d": cps("excel")}, cps("unix"), None])
            c["args"] = r.choice([{}, {}, cls.args(r, True), {"delimiter": {"s": cps(";")}}])
        return c

    @classmethod
    def gen(cls, r):
        if os.environ.get("CSV_SNIFF") == "1" or r.random() < 0.1:
            return cls.gen_sniff(r)
        if os.environ.get("CSV_DOBJ") == "1" or r.random() < 0.15:
            return cls.gen_dobj(r)
        fn = r.choice(["dialect", "dialect", "reader", "reader", "reader", "reader", "script", "script", "script", "writer",
                       "writer", "writer", "roundtrip", "roundtrip", "field_size_limit", "registry", "get_dialect", "unpack",
                       "dictreader", "dictwriter", "dictwriterows", "writeheader", "extrasaction", "classvalidate"])
        c = {"mod": "textlibs", "fn": "csv." + fn}
        if fn == "dialect":
            c["args"] = r.choice([{}, {}, cls.args(r, False), cls.args(r, True)])
            c["src"] = r.choice([None, None, cps("excel"), cps("unix"), cps("excel-tab"), cps("nope"), {"d": cps("excel")}, {"d": cps("unix")},
                                 {"cls": "excel"}, {"cls": "unix_dialect"}, None, {"i": 1}, spec_obj(r)])
            if c["src"] is None and "None" == r.choice(["None", "x", "x", "x"]):
                c["src"] = {"o": "float", "t": True}
            if r.random() < 0.05:
                c["args"]["bogus"] = {"i": 1}
            if r.random() < 0.05 and c["src"] is not None:
                c["args"]["dialect"] = {"s": cps("excel")}
            if r.random() < 0.15:
                k = r.choice(["doublequote", "skipinitialspace", "strict"])
                c["args"][k] = spec_obj(r)
        elif fn in ("reader", "roundtrip"):
            c["fn"] = "csv.reader"
            a = cls.valid_args(r) if r.random() < 0.9 else cls.args(r, False)
            c["args"], c["src"] = a, r.choice([None, None, None, cps("excel"), cps("unix")])
            q = a.get("quoting", {}).get("i", 0) if isinstance(a.get("quoting"), dict) else 0
            numeric = q in (2, 4)
            if fn == "roundtrip" and r.random() < 0.9:
                d = dict(a)
                try:
                    buf = io.StringIO(newline="")
                    w = csv.writer(buf, *csv_src(c), **csv_kw(c))
                    for _ in range(r.choice([1, 1, 2, 3])):
                        w.writerow([cls.text(r, numeric) for _ in range(r.choice([0, 1, 1, 2, 3]))])
                    text = buf.getvalue()
                except Exception:
                    text = "a,b\r\n"
                lines = text.splitlines(True) if r.random() < 0.8 else [text]
            else:
                lines = []
                for _ in range(r.choice([0, 1, 1, 2, 3])):
                    t = cls.text(r, numeric)
                    if r.random() < 0.7:
                        t += r.choice(["\n", "\r\n", "\r"])
                    lines.append(t)
            c["lines"] = [{"s": cps(l)} for l in lines]
            if r.random() < 0.02:
                c["lines"].insert(r.randint(0, len(c["lines"])), {"o": "int"})
            c["limit"] = r.choice([131072, 131072, 131072, 3, 1, 0, -1])
        elif fn == "script":
            c["fn"] = "csv.reader"
            a = cls.valid_args(r)
            c["args"], c["src"] = a, None
            q = a.get("quoting", {}).get("i", 0)

            def step():
                roll = r.random()
                if roll < 0.5:
                    t = r.choice(['"abc', 'a,b', '"q"', 'x"', '', '1', 'a"b,c', '"a\n', 'b"\n', 'abcd,efgh', '\n'])
                    return {"s": cps(t)}
                if roll < 0.68:
                    return {"k": "eff", "e": {"e": "advance"}}
                if roll < 0.76:
                    return {"k": "eff", "e": {"e": "limit", "n": r.choice([{"i": 2}, {"i": 131072}, {"s": cps("x")}, {"i": 2**70}])}}
                if roll < 0.86:
                    return {"k": "raise", "x": [r.choice(["ValueError", "TypeError", "OSError"]), "boom"]}
                if roll < 0.96:
                    return {"k": "stop"}
                return {"o": "int"}

            c["lines"] = [step() for _ in range(r.choice([1, 2, 3, 4, 6, 8]))]
            c["limit"] = r.choice([131072, 131072, 3])
        elif fn == "writer":
            a = cls.valid_args(r) if r.random() < 0.9 else cls.args(r, False)
            c["args"], c["src"] = a, None

            def eff(depth):
                return {"e": "row", "row": row_obj(depth + 1)}

            def field(depth):
                roll = r.random()
                if roll < 0.55:
                    return {"s": cps(cls.text(r, False))}
                if roll < 0.68:
                    return None
                if roll < 0.78:
                    return r.choice([{"i": 0}, {"i": -5}, {"i": 123}, {"big": 1}, {"b": True}])
                if roll < 0.84:
                    return {"sub": cps(cls.text(r, False)), "key": None}
                o = spec_obj(r)
                if r.random() < 0.3 and depth < 1:
                    o["spec"]["str"]["effs"] = [eff(depth)]
                return o

            def row_obj(depth):
                roll = r.random()
                n = r.choice([0, 1, 1, 2, 3, 4])
                if roll < 0.5:
                    return {"o": "Other", "spec": {"truth": {"ok": True}, "key": None, "attrs": [], "num": False,
                                                   "str": {"effs": [], "res": {"ok": []}},
                                                   "iter": {"ok": [{"k": "ret", "o": field(depth)} for _ in range(n)]}}}
                steps = []
                for _ in range(n + 1):
                    k = r.random()
                    if k < 0.65:
                        steps.append({"k": "ret", "o": field(depth)})
                    elif k < 0.75 and depth < 1:
                        steps.append({"k": "eff", "e": eff(depth)})
                    elif k < 0.85:
                        steps.append({"k": "raise", "x": [r.choice(["ValueError", "OSError"]), "boom"]})
                    else:
                        steps.append({"k": "stop"})
                res = {"raise": [r.choice(["TypeError", "ValueError"]), "boom"]} if r.random() < 0.1 else {"ok": steps}
                return {"o": "Other", "spec": {"truth": {"ok": True}, "key": None, "attrs": [], "num": False,
                                               "str": {"effs": [], "res": {"ok": []}}, "iter": res}}

            calls = []
            for _ in range(r.choice([0, 1, 2])):
                res = r.choice([{"ok": None}, {"ok": {"i": 42}}, {"ok": {"s": cps("x")}}, {"raise": ["OSError", "boom"]}, {"ok": {"b": False}}])
                calls.append({"effs": [eff(0)] if r.random() < 0.2 else [], "res": res})
            c["file"] = {"o": "Other", "spec": {"truth": {"ok": True}, "key": None, "num": False, "str": {"effs": [], "res": {"ok": []}},
                                                "iter": {"ok": []}, "attrs": [["write", {"ok": {"func": calls}}]]}}
            if r.random() < 0.05:
                c["file"] = r.choice([{"i": 1}, {"o": "Other", "spec": {"truth": {"ok": True}, "key": None, "num": False,
                                                                       "str": {"effs": [], "res": {"ok": []}}, "iter": {"ok": []},
                                                                       "attrs": r.choice([[["write", {"raise": ["OSError", "boom"]}]],
                                                                                          [["write", {"ok": {"i": 1}}]], []])}}])
            ops = []
            for _ in range(r.choice([1, 1, 2, 3])):
                if r.random() < 0.7:
                    ops.append(["row", row_obj(0) if r.random() < 0.95 else r.choice([{"i": 1}, None, {"s": cps("ab")}])])
                else:
                    rows = [{"k": "ret", "o": row_obj(0)} for _ in range(r.choice([0, 1, 2, 3]))]
                    if r.random() < 0.3:
                        rows.append({"k": "raise", "x": ["ValueError", "boom"]})
                    if r.random() < 0.2:
                        rows.insert(0, {"k": "eff", "e": eff(0)})
                    ops.append(["rows", {"o": "Other", "spec": {"truth": {"ok": True}, "key": None, "attrs": [], "num": False,
                                                                "str": {"effs": [], "res": {"ok": []}}, "iter": {"ok": rows}}}])
            c["ops"] = ops
        elif fn == "field_size_limit":
            c["cur"] = 131072
            c["new"] = r.choice([{"i": 5}, {"i": 0}, {"i": -1}, {"i": 2**70}, {"o": "float", "t": True}, {"b": True}, None])
            if c["new"] is None:
                del c["new"]
        elif fn == "registry":
            c["op"] = r.choice(["register", "unregister"])
            c["name"] = r.choice([{"s": cps("mine")}, {"s": cps("excel")}, {"s": cps("nope")}, {"s": cps("unix")}, {"i": 1}, None,
                                  {"sub": cps("mine"), "key": r.choice([None, {"k": cps("excel")}, {"hash": ["ValueError", "boom"]},
                                                                        {"hash": ["TypeError", "boom"]}, {"eq": ["TypeError", "boom"]}])},
                                  spec_obj(r), {"o": "list", "t": False}])
            c["args"] = cls.args(r, r.random() < 0.8)
            c["src"] = r.choice([None, None, {"d": cps("excel")}, cps("unix"), cps("nope")])
        elif fn == "get_dialect":
            c["name"] = r.choice([{"s": cps("excel")}, {"s": cps("excel-tab")}, {"s": cps("unix")}, {"s": cps("nope")}, {"i": 1}, None,
                                  {"o": "list", "t": False}, spec_obj(r),
                                  {"sub": cps("zz"), "key": r.choice([None, {"k": cps("unix")}, {"hash": ["TypeError", "boom"]}])}])
        elif fn == "unpack":
            c["f"] = r.choice(["reader", "writer", "register_dialect"])
            c["pos"] = [r.choice([{"i": 1}, {"s": cps("a")}, None, {"s": cps("excel")}]) for _ in range(r.choice([0, 0, 1, 2, 3, 4]))]
        elif fn == "classvalidate":
            attrs = []
            for k, v in [("delimiter", {"s": cps(",")}), ("quotechar", {"s": cps('"')}), ("quoting", {"i": 0}), ("doublequote", {"b": True})]:
                roll = r.random()
                if roll < 0.5:
                    attrs.append([k, {"ok": v}])
                elif roll < 0.7:
                    attrs.append([k, {"ok": r.choice([{"s": cps("ab")}, {"i": 9}, None, {"s": cps("\n")}])}])
                elif roll < 0.85:
                    attrs.append([k, {"raise": ["ZeroDivisionError", "boom"]}])
            c["obj"] = {"o": "Other", "spec": {"truth": {"ok": True}, "key": None, "num": False, "str": {"effs": [], "res": {"ok": []}},
                                               "iter": {"ok": []}, "attrs": attrs}}
        elif fn == "dictreader":
            c["lines"] = [{"s": cps(r.choice(["a,b\r\n", "1,2,3\n", "\n", "x\r\n", ",\n", "", "a,a\n", "p,q,r,s\n"]))}
                          for _ in range(r.choice([0, 1, 2, 3, 4]))]
            c["names"] = r.choice([None, None, [cps("k"), cps("v")], [cps("k")], [], [cps("k"), cps("k")]])
            c["restkey"] = r.choice([None, None, cps("rest"), cps("k")])
        elif fn == "dictwriter":
            c["names"] = r.choice([[cps("a"), cps("b")], [cps("b")], []])
            c["raises"] = r.random() < 0.5
            c["row"] = [[cps(k), {"s": cps(v)}] for k, v in
                        r.choice([[("a", "1")], [("a", "1"), ("b", "x,y")], [("c", "3")], [], [("a", "1"), ("c", "3")]])]
        elif fn == "dictwriterows":
            c["names"] = r.choice([[cps("a"), cps("b")], [cps("b")], []])
            c["raises"] = r.random() < 0.5
            c["rows"] = [[[cps(k), {"s": cps(v)}] for k, v in
                          r.choice([[("a", "1")], [("a", "1"), ("b", "x,y")], [("c", "3")], [], [("a", "1"), ("c", "3")]])]
                         for _ in range(r.choice([0, 1, 2, 3]))]
        elif fn == "writeheader":
            c["names"] = r.choice([[cps("a"), cps("b")], [cps("x,y")], [], [cps("a"), cps("a")]])
        else:
            c["s"] = cps(r.choice(["raise", "RAISE", "ignore", "Ignore", "other", ""]))
        return c

    @classmethod
    def run(cls, c):
        fn = c["fn"].split(".")[1]
        if fn in ("reader", "writer"):
            return in_child(lambda: cls.run_io(c, fn))
        if fn == "sniff":
            def sniff_body():
                ds = c["delims"]
                d = csv.Sniffer().sniff(txt(c["s"]), None if ds is None else txt(ds))
                return {"d": cps(d.delimiter), "q": cps(d.quotechar), "dq": bool(d.doublequote),
                        "skip": bool(d.skipinitialspace)}
            return common.py_result(sniff_body)
        if fn == "regseq":
            return cls.run_regseq(c)

        def body():
            ctx = CsvCtx()
            if fn == "pickle":
                getattr(csv_obj(c["obj"], ctx), c["method"])(*([2] if c["method"] == "__reduce_ex__" else []))
                return None
            if fn == "ltget":
                x = csv_obj(c["obj"], ctx).lineterminator
                return [cps(x), isinstance(x, Sub)]
            if fn == "readerd":
                return enc_dialect(csv.reader([], *csv_src(c, ctx), **csv_kw(c, ctx)).dialect)
            if fn == "writerd":
                return enc_dialect(csv.writer(io.StringIO(), *csv_src(c, ctx), **csv_kw(c, ctx)).dialect)
            if fn == "dialect":
                src = csv_src(c, ctx)
                d = _csv.Dialect(*src, **csv_kw(c, ctx))
                return {"d": enc_dialect(d), "same": bool(src) and d is src[0] or (bool(src) and isinstance(src[0], str) and d is csv.get_dialect(src[0]))}
            if fn == "field_size_limit":
                old = csv.field_size_limit()
                try:
                    if "new" in c:
                        was = csv.field_size_limit(csv_obj(c["new"]))
                        return [was, csv.field_size_limit()]
                    return [old, old]
                finally:
                    csv.field_size_limit(old)
            if fn == "registry":
                saved = {n: csv.get_dialect(n) for n in csv.list_dialects()}
                try:
                    name = csv_obj(c["name"], ctx)
                    if c["op"] == "register":
                        csv.register_dialect(name, *csv_src(c, ctx), **csv_kw(c, ctx))
                    else:
                        csv.unregister_dialect(name)
                    return [cps(n) for n in csv.list_dialects()]
                finally:
                    for n in list(csv.list_dialects()):
                        csv.unregister_dialect(n)
                    for n, d in saved.items():
                        csv.register_dialect(n, d)
            if fn == "get_dialect":
                return enc_dialect(csv.get_dialect(csv_obj(c["name"], ctx)))
            if fn == "unpack":
                pos = [csv_obj(x, ctx) for x in c["pos"]]
                saved = list(csv.list_dialects())
                if c["f"] == "reader":
                    csv.reader(*pos)
                    return None
                if c["f"] == "writer":
                    csv.writer(*pos)
                    return None
                try:
                    csv.register_dialect(*pos)
                    return [cps(n) for n in csv.list_dialects()]
                finally:
                    for n in list(csv.list_dialects()):
                        if n not in saved:
                            csv.unregister_dialect(n)
            if fn == "dictreader":
                names = None if c["names"] is None else [txt(n) for n in c["names"]]
                rk = None if c["restkey"] is None else txt(c["restkey"])
                sentinel = object()
                rd = csv.DictReader(Scripted(c["lines"], ctx), fieldnames=names, restkey=rk, restval=sentinel)
                ctx.reader = rd.reader
                rows, exc = [], None
                try:
                    for d in rd:
                        row = []
                        for k, v in d.items():
                            jk = enc_field(k)
                            if v is sentinel:
                                row.append([jk, {"restval": None}])
                            elif k == rk and isinstance(v, list):
                                row.append([jk, {"rest": [enc_field(x) for x in v]}])
                            else:
                                row.append([jk, enc_field(v)])
                        rows.append(row)
                except Exception as e:
                    exc = norm_exc(e)
                return {"rows": rows, "exc": exc, "n": rd.line_num}
            if fn in ("dictwriter", "dictwriterows", "writeheader"):
                ctx.written = []
                f = type("F", (), {"write": WriteFn([], ctx)})()
                names = [txt(n) for n in c["names"]]
                w = csv.DictWriter(f, names, extrasaction="raise" if c.get("raises", True) else "ignore")
                try:
                    if fn == "dictwriter":
                        r = {"ok": enc_ret(w.writerow({txt(k): csv_obj(v, ctx) for k, v in c["row"]}))}
                    elif fn == "dictwriterows":
                        r = {"ok": enc_ret(w.writerows([{txt(k): csv_obj(v, ctx) for k, v in row} for row in c["rows"]]))}
                    else:
                        r = {"ok": enc_ret(w.writeheader())}
                except Exception as e:
                    r = {"exc": type(e).__name__, "msg": norm_msg(str(e))}
                return {"res": r, "written": ctx.written}
            if fn == "classvalidate":
                obj = csv_obj(c["obj"], ctx)
                try:
                    _csv.Dialect(obj)
                except TypeError as e:
                    raise csv.Error(str(e)) from None
                return None
            csv.DictWriter(io.StringIO(), ["a"], extrasaction=txt(c["s"]))
            return txt(c["s"]).lower() == "raise"

        res = common.py_result(body)
        if "exc" in res:
            res["msg"] = norm_msg(res["msg"])
        return res

    @classmethod
    def run_regseq(cls, c):
        ctx = CsvCtx()
        saved = {n: csv.get_dialect(n) for n in csv.list_dialects()}

        def one(o):
            name = csv_obj(o["name"], ctx)
            if o["op"] == "register":
                kw = {"delimiter": ";"}
                if o["during"]:
                    kw["doublequote"] = Hook(o["during"], ctx)
                csv.register_dialect(name, **kw)
                return None
            if o["op"] == "get":
                return cps(csv.get_dialect(name).delimiter)
            csv.unregister_dialect(name)
            return None
        try:
            out = [common.py_result(lambda o=o: one(o)) for o in c["ops"]]
            keys = csv.list_dialects()
            res = {"out": out, "keys": [cps(n) for n in keys], "sub": [isinstance(n, Sub) for n in keys]}
        finally:
            for n in list(csv.list_dialects()):
                csv.unregister_dialect(n)
            for n, d in saved.items():
                csv.register_dialect(n, d)
        return {"ok": res}

    @classmethod
    def run_io(cls, c, fn):
        ctx = CsvCtx()
        ctx.written = []
        if fn == "reader":
            rd = csv.reader(Scripted(c["lines"], ctx), *csv_src(c), **csv_kw(c, ctx))
            ctx.reader = rd
            csv.field_size_limit(c["limit"])
            rows, exc = [], None
            try:
                for row in rd:
                    rows.append([enc_field(x) for x in row])
            except Exception as e:
                exc = norm_exc(e)
            return {"ok": {"rows": rows, "exc": exc, "n": rd.line_num, "limit": csv.field_size_limit()}}
        wr = csv.writer(csv_obj(c["file"], ctx), *csv_src(c), **csv_kw(c, ctx))
        ctx.writer = wr
        out = []
        for k, o in c["ops"]:
            try:
                x = (wr.writerow if k == "row" else wr.writerows)(csv_obj(o, ctx))
                out.append({"ok": enc_ret(x)})
            except Exception as e:
                out.append({"exc": type(e).__name__, "msg": norm_msg(str(e))})
        return {"ok": {"res": out, "written": ctx.written}}


# ---- re --------------------------------------------------------------------

import re
import _sre
import json
from re import _parser as sre_parse


def re_item(op, av):
    n = str(op)
    if n == "LITERAL":
        return ["l", av]
    if n == "RANGE":
        return ["r", av[0], av[1]]
    if n == "CATEGORY":
        return ["c", str(av)]
    return ["n"]


def re_nodes(seq):
    return [re_node(op, av) for op, av in seq]


def re_node(op, av):
    n = str(op)
    if n == "LITERAL":
        return ["lit", av]
    if n == "NOT_LITERAL":
        return ["nlit", av]
    if n == "ANY":
        return ["any"]
    if n == "IN":
        return ["in", [re_item(o, a) for o, a in av]]
    if n == "AT":
        return ["at", str(av)]
    if n == "GROUPREF":
        return ["gref", av]
    if n == "GROUPREF_EXISTS":
        return ["gex", av[0], re_nodes(av[1]), None if av[2] is None else re_nodes(av[2])]
    if n == "BRANCH":
        return ["br", [re_nodes(x) for x in av[1]]]
    if n == "SUBPATTERN":
        return ["sub", av[0], av[1], av[2], re_nodes(av[3])]
    if n in ("MAX_REPEAT", "MIN_REPEAT", "POSSESSIVE_REPEAT"):
        return ["rep", n, int(av[0]), int(av[1]), re_nodes(av[2])]
    if n == "ATOMIC_GROUP":
        return ["atom", re_nodes(av)]
    if n == "ASSERT":
        return ["as", av[0], re_nodes(av[1])]
    if n == "ASSERT_NOT":
        return ["nas", av[0], re_nodes(av[1])]
    if n == "FAILURE":
        return ["fail"]
    raise TypeError(n)


def re_src(c):
    if c["text"]:
        return "".join(map(chr, c["pat"]))
    return bytes(c["pat"])


def _sre_parse(pat):
    from re import _parser
    return _parser.parse(pat, 0)


def _sre_code(p):
    from re import _compiler
    return _compiler._code(p, 0)


@area("re", 8)
class ReArea:
    ATOMS = ["a", "b", "c", "x", "1", "_", " ", "-", ".", "^", "$", r"\d", r"\w", r"\s", r"\D", r"\W", r"\S", r"\b",
             r"\B", r"\A", r"\Z", r"\z", r"\n", r"\t", r"\\", r"\x41", r"\101", r"\0", r"\07", r"\377", r"\400",
             r"A", r"\U00000041", r"\U00110000", r"\q", r"\_", r"\.", r"\8", r"\1", r"\2", r"\12", r"\123", "é"]
    SETS = ["[a]", "[^a]", "[ab]", "[^ab]", "[a-c]", "[a-c0]", "[]a]", "[^]a]", "[a-]", "[-a]", "[\\d]", "[^\\s]", "[\\w-]",
            "[\\d-a]", "[a-\\d]", "[c-a]", "[", "[a", "[a-", "[\\", "[\\x4]", "[\\400]", "[\\8]", "[\\q]", "[\\b]",
            "[\\x41-\\x43]", "[a-a]", "[aa]", "[--a]", "[[a]", "[a&&b]"]
    QUANT = ["*", "+", "?", "*?", "+?", "??", "*+", "++", "?+", "{2}", "{1,3}", "{,3}", "{2,}", "{,}", "{}", "{a}", "{1",
             "{1,", "{3,1}", "{0}", "{0,0}", "{1,3}?", "{1,3}+", "{4294967295}", "{4294967294}", "{4294967296}", "**",
             "*?+", "{" + "9" * 5000 + "}", "{1," + "9" * 4400 + "}", "{" + "9" * 4300 + "}"]
    FLAGS = ["(?i)", "(?m)", "(?s)", "(?x)", "(?a)", "(?L)", "(?u)", "(?i:", "(?-i:", "(?i-s:", "(?a:", "(?-a:", "(?L:",
             "(?u:", "(?ia:", "(?iz)", "(?-z:", "(?i-:", "(?-:", "(?-i)", "(?i-i:", "(?1)", "(?i", "(?-", "(?i-", "(?i-s"]

    @classmethod
    def gen_pat(cls, r, depth=0):
        out = []
        for _ in range(r.choice([0, 1, 1, 2, 2, 3, 4])):
            roll = r.random()
            if roll < 0.32:
                out.append(r.choice(cls.ATOMS))
            elif roll < 0.42:
                out.append(r.choice(cls.SETS))
            elif roll < 0.52:
                out.append(r.choice(cls.QUANT))
            elif roll < 0.57:
                out.append(r.choice(cls.FLAGS))
            elif roll < 0.62:
                out.append("|")
            elif depth < 3:
                inner = cls.gen_pat(r, depth + 1)
                n = r.choice(["g", "g", "g", "nc", "name", "ref", "la", "nla", "lb", "nlb", "atomic", "cond", "condname",
                              "comment", "open", "close", "badext"])
                out.append({"g": f"({inner})", "nc": f"(?:{inner})", "name": f"(?P<n{r.randrange(3)}>{inner})",
                            "ref": r.choice(["(?P=n0)", "(?P=n1)", "(?P=)", "(?P=1a)", "(?P<>a)", "(?P<1a>a)", "(?P<a", "(?P"]),
                            "la": f"(?={inner})", "nla": f"(?!{inner})", "lb": f"(?<={inner})", "nlb": f"(?<!{inner})",
                            "atomic": f"(?>{inner})",
                            "cond": f"(?({r.choice('0123')}){inner}|{cls.gen_pat(r, depth + 1)})",
                            "condname": f"(?(n{r.randrange(2)}){inner})",
                            "comment": r.choice(["(?#x)", "(?#", "(?#)"]), "open": "(", "close": ")",
                            "badext": r.choice(["(?", "(?P>a)", "(?<a)", "(?<", "(?Z)", "(?P", "(?(", "(?()", "(?(a", "(?(1)a|b|c)"])}[n])
        return "".join(out)

    CHARS = ["a", "b", "k", "s", "i", "K", "S", "I", "z", "0", "9", "_", " ", "-", "é", "É", "ſ", "K", "ı", "İ", "µ", "Μ", "ß",
             "σ", "ς", "Σ", "中", "€", "\U00010400", "\U00010428", "ǅ"]

    @classmethod
    def cset(cls, r):
        parts = []
        for _ in range(r.choice([1, 1, 2, 3, 4, 6, 20])):
            roll = r.random()
            if roll < 0.45:
                parts.append(r.choice(cls.CHARS))
            elif roll < 0.75:
                a = r.choice([0x30, 0x41, 0x61, 0xc0, 0x100, 0x370, 0x400, 0x4e00, 0xa7c0, 0xfb00, 0xff00, 0xffe0, 0x10400, 0x16ea0, 0x1f600])
                # only ranges that start near the top of the BMP may cross it: one starting low
                # costs 65536 table lookups and reaches no other branch
                b = a + r.choice([0, 1, 2, 5, 25, 26, 100, 300] + ([70000] if a >= 0xff00 else []))
                parts.append(chr(a) + "-" + chr(min(b, 0x10ffff)))
            else:
                parts.append(r.choice(["\\d", "\\D", "\\s", "\\S", "\\w", "\\W"]))
        return "[" + r.choice(["", "", "", "^"]) + "".join(parts) + "]"

    @classmethod
    def compile_pat(cls, r):
        def atom():
            roll = r.random()
            if roll < 0.35:
                return r.choice(cls.CHARS)
            if roll < 0.7:
                return cls.cset(r)
            if roll < 0.8:
                return r.choice([".", "\\d", "\\w", "\\s", "\\b", "\\B", "^", "$", "\\A", "\\Z"])
            return "(" + r.choice(["", "?:", "?i:", "?a:", "?P<x>", "?>", "?-i:", "?s:", "?m:"]).replace("?P<x>", "?P<x%d>" % r.randrange(10**6)) + atom() + atom() + ")"

        def item():
            a = atom()
            if a[0] in "^$\\" and len(a) < 3 or a in ("^", "$"):
                return a
            return a + r.choice(["", "", "", "*", "+", "?", "*?", "+?", "*+", "{2,3}", "{2}?", "{1,4}+"])

        n = r.choice([0, 1, 1, 2, 3, 5])
        body = "".join(item() for _ in range(n))
        roll = r.random()
        if roll < 0.15:
            return body + "|" + "".join(item() for _ in range(2))
        if roll < 0.25:
            return "(?=" + body + ")" + item()
        if roll < 0.35:
            return "(?<=" + r.choice(cls.CHARS) + cls.cset(r) + ")" + body
        if roll < 0.42:
            return "(?<!" + r.choice(cls.CHARS) + "*)" + body
        if roll < 0.5:
            return "ab|ac|" + item()
        if roll < 0.6:
            return r.choice(["abcabd", "(ab)c", "(a)(b)c", "(?:ab)c", "(?i)ab", "ab(?i:c)d", "1(2)3", "aa", "aba", "abab"]) + body
        return body

    @classmethod
    def gen(cls, r):
        pat = cls.gen_pat(r)
        if r.random() < 0.05:
            pat += "\n" + cls.gen_pat(r)
        if r.random() < 0.1:
            pat = "(?x) " + pat.replace("a", " a # c\n")
        if r.random() < 0.35:
            # groups first, so backreferences and conditionals parse
            refs = [r"\1", r"\2", "(?P=n0)", "(?(1)x|y)", "(?(n0)x)", "(?(2)x)", "(?(n0)|y)", r"(?<=\1)", r"(?<=(?P=n0))",
                    "(?(1)x|y|z)", "(?<=(a)\\1)", "(?(3)x)", r"[\1]", "(?(1)(?(2)x|y)|z)"]
            pat = ("(?P<n0>" + r.choice(["a", "ab", "a|bc", "a*", "(?:a)"]) + ")(" + r.choice(["b", "", "b?"]) + ")"
                   + cls.gen_pat(r, 2) + r.choice(refs) + r.choice(cls.QUANT[:8] + ["", "", ""]))
        text = r.random() < 0.8
        flags = r.choice([0, 0, 0, 0, 0, 2, 8, 16, 64, 256] + ([32, 4, 256 | 32, 4 | 256] if r.random() < 0.3 else [0]))
        if not text:
            pat = pat.replace("é", "\xe9")
        c = {"mod": "textlibs", "fn": "re.parse", "pat": [ord(x) for x in pat], "text": text, "flags": flags}
        if os.environ.get("RE_SEM") == "1" or r.random() < 0.1:
            return cls.gen_sem(r)
        if os.environ.get("RE_EXEC") == "1" or r.random() < 0.5:
            return cls.gen_exec(r)
        if r.random() < 0.45:
            c["fn"] = "re.code"
            # charsets, case folding and literal prefixes
            if r.random() < 0.6:
                pat = cls.compile_pat(r)
                c["pat"] = [ord(x) for x in pat]
                c["text"] = text = all(ord(x) < 256 for x in pat) is False or r.random() < 0.85
                c["flags"] = r.choice([0, 2, 2, 2, 8, 16, 256, 2 | 256, 2 | 8] + ([4, 2 | 4] if not text else []))
        elif r.random() < 0.4:
            c["fn"] = "re.template"
            c["repl"] = [ord(x) for x in "".join(r.choice(
                ["a", "\\1", "\\2", "\\0", "\\07", "\\123", "\\400", "\\g<1>", "\\g<0>", "\\g<n0>", "\\g<zz>", "\\g<", "\\g", "\\g<>",
                 "\\g<1", "\\g<1a>", "\\8", "\\12", "\\n", "\\\\", "\\q", "\\_", "\\.", "\\g<" + "9" * 5000 + ">",
                 "\\g<2147483647>", "\\g<99>"]) for _ in range(r.choice([0, 1, 2, 3])))]
        return c

    SEM_ATOMS = ["a", "b", "c", "a", "b", "A", "s", "k", ".", "[ab]", "[^a]", "[a-c]", "\\w", "\\W", "\\d", "\\s", "\\b",
                 "\\B", "^", "$", "\\A", "\\Z", ""]

    @classmethod
    def gen_tree(cls, r, d, st):
        """A pattern as text. st is [groups opened, groups closed]: a conditional or a backreference
        names a closed group, since one that tests its own open group is a recorded refutation."""
        c = r.random()
        if d <= 0 or c < 0.3:
            return r.choice(cls.SEM_ATOMS)
        if c < 0.45:
            return cls.gen_tree(r, d - 1, st) + cls.gen_tree(r, d - 1, st)
        if c < 0.58:
            return "(?:" + cls.gen_tree(r, d - 1, st) + "|" + cls.gen_tree(r, d - 1, st) + ")"
        if c < 0.73:
            st[0] += 1
            g = st[0]
            inner = cls.gen_tree(r, d - 1, st)
            st[1].append(g)
            return "(" + inner + ")"
        if c < 0.88:
            q = r.choice(["*", "+", "?", "{2}", "{1,2}", "{0,2}", "{2,3}", "{2,}"]) + r.choice(["", "", "?", "+"])
            return "(?:" + cls.gen_tree(r, d - 1, st) + ")" + q
        if c < 0.91:
            return "(?>" + cls.gen_tree(r, d - 1, st) + ")"
        if c < 0.94:
            return r.choice(["(?=", "(?!"]) + cls.gen_tree(r, d - 1, st) + ")"
        if c < 0.96:
            st[0] += 2
            st[1].extend([st[0] - 1])
            st[1].append(st[0])
            body = r.choice(["(a)()", "(.)()", "(a)()b", "(a|b)()", "(?:(a)|b)()"])
            return r.choice(["(?<=", "(?<!"]) + body + ")"
        if st[1]:
            g = r.choice(st[1])
            if r.random() < 0.5:
                return "\\%d" % g
            return "(?(%d)%s|%s)" % (g, cls.gen_tree(r, d - 1, st), cls.gen_tree(r, d - 1, st))
        return "b"

    @classmethod
    def gen_sem(cls, r):
        flags = r.choice([0, 0, 0, 2, 2, 8, 16, 256, 2 | 256, 2 | 16])
        while True:
            pat = cls.gen_tree(r, r.choice([2, 3, 3, 4]), [0, []])
            try:
                re.compile(pat, flags)
                break
            except Exception:
                continue
        alpha = "aabbcAskK _\n\xe9\xc9\u017f\u212a"
        subj = "".join(r.choice(alpha) for _ in range(r.randint(0, 6)))
        return {"mod": "textlibs", "fn": "re.sem", "pat": [ord(x) for x in pat], "flags": flags,
                "s": [ord(x) for x in subj], "full": r.random() < 0.4}

    @classmethod
    def run_sem(cls, c):
        pat = "".join(map(chr, c["pat"]))
        subj = "".join(map(chr, c["s"]))

        def body():
            m = (re.fullmatch if c["full"] else re.match)(pat, subj, c["flags"])
            if m is None:
                return None
            gs = [None if m.span(i) == (-1, -1) else list(m.span(i)) for i in range(1, m.re.groups + 1)]
            return {"stop": m.end(), "groups": gs, "last": m.lastindex}
        return common.py_result(body)

    @classmethod
    def gen_validate(cls, r):
        pat = cls.compile_pat(r) if r.random() < 0.7 else cls.gen_pat(r)
        try:
            p = _sre_parse(pat)
            code = _sre_code(p)
            groups = p.state.groups - 1
        except Exception:
            code, groups = [1], 0
        code = list(code)
        for _ in range(r.choice([0, 1, 1, 2, 3])):
            i = r.randrange(len(code))
            code[i] = r.choice([0, 1, 2, 3, 4, 5, 8, 13, 14, 15, 16, 17, 18, 19, 23, 24, 27, 28, 29, code[i] + 1, code[i] - 1 if code[i] else 0,
                                len(code), 2**32 - 1])
        if r.random() < 0.1:
            code = code[:r.randrange(len(code) + 1)]
        # A skip below these bounds makes the validator itself read outside the array, which is
        # undefined behaviour, not an outcome to compare. The model reports it as a separate case.
        if any((w in (13, 31, 35, 39) and code[i + 1:i + 2] and code[i + 1] < 2) or (w == 14 and code[i + 1:i + 2] and code[i + 1] < 5)
               for i, w in enumerate(code)):
            code = [1]
        return {"mod": "textlibs", "fn": "re.validate", "text": True, "pat": [], "flags": 0, "code": code,
                "groups": r.choice([groups, groups, groups, 0, groups + 1, -1])}

    @classmethod
    def run_validate(cls, c):
        rd, wr = os.pipe()
        pid = os.fork()
        if pid == 0:
            os.close(rd)
            try:
                _sre.compile(None, 0, c["code"], c["groups"], {}, ())
                out = {"ok": True}
            except Exception as e:
                out = {"exc": type(e).__name__, "msg": str(e)}
            os.write(wr, json.dumps(out).encode())
            os._exit(0)
        os.close(wr)
        buf = b""
        while True:
            chunk = os.read(rd, 4096)
            if not chunk:
                break
            buf += chunk
        os.close(rd)
        _, status = os.waitpid(pid, 0)
        if os.WIFSIGNALED(status) or not buf:
            return {"exc": "SegmentationFault", "msg": ""}
        return json.loads(buf)

    @classmethod
    def gen_scanner(cls, r):
        pool = ["a", "b+", "[a-c]", r"\\w+", r"\\d", r"\\s", "é", "(?i)a", "(?x) a b", "(a)", "(a)(b)", "x|y", "", "a*", r"(a)\\1", "(?i:b)", "."]
        n = r.choice([0, 1, 2, 3])
        phrases = [r.choice(pool).replace("\\\\", "\\") for _ in range(n)]
        flags = r.choice([0, 0, 2, 8, 16, 256, 32])
        s = "".join(r.choice("abcxyAB é1 ٣") for _ in range(r.choice([0, 1, 2, 3, 5, 8])))
        return {"mod": "textlibs", "fn": "re.scanner", "text": True, "pat": [], "phrases": [[ord(x) for x in ph] for ph in phrases],
                "flags": flags, "s": [ord(x) for x in s]}

    @classmethod
    def run_scanner(cls, c):
        phrases = ["".join(map(chr, ph)) for ph in c["phrases"]]
        lex = [(ph, None if i % 3 == 2 else i) for i, ph in enumerate(phrases)]

        def body():
            r, rest = re.Scanner(lex, c["flags"]).scan("".join(map(chr, c["s"])))
            return [r, [ord(x) for x in rest]]

        return common.py_result(body)

    @classmethod
    def gen_exec(cls, r):
        k = r.random()
        if k < 0.04:
            return cls.gen_validate(r)
        if k < 0.08:
            return cls.gen_scanner(r)
        if k < 0.10:
            s = "".join(r.choice("ab.*()[]{}?+-|^$\\&~# \t\n\r\x0b\x0c/é_%") for _ in range(r.choice([0, 1, 3, 8])))
            return {"mod": "textlibs", "fn": "re.escape", "text": True, "pat": [], "flags": 0, "s": [ord(x) for x in s]}
        if k < 0.12:
            f = r.choice(["sub", "subn", "split"])
            c = {"mod": "textlibs", "fn": "re.args", "text": True, "pat": [], "flags": 0, "f": f,
                 "args": [r.choice([0, 1, 2]) for _ in range(r.choice([0, 0, 1, 1, 2, 3, 4]))]}
            if r.random() < 0.3:
                c["kw1"] = r.choice([0, 1, 2])
            if r.random() < 0.3:
                c["kw2"] = r.choice([0, 2])
            return c
        for _ in range(50):
            pat = cls.compile_pat(r) if r.random() < 0.8 else cls.gen_pat(r)
            flags = r.choice([0, 0, 0, 2, 2, 8, 16, 256, 2 | 256, 2 | 8])
            if r.random() < 0.2:
                pat = r.choice(["(a)|b", "(a)|(b)", "(a|b)*", "(a|(b))+", "((a)|b)*c", "(a*)*", "(a*)+", "(?:(a)|b)*", "(a)?b",
                                "(a)*?b", "(?P<x>a)(?P=x)", "(a)\\1", "(a*)\\1", "(?:(a)|(b))+\\1", "(a)(?(1)b|c)",
                                "(?:(a)|b)(?(1)c|d)", "(?=(a))a", "(?!(a))b", "(?<=(a))b", "(?>a+)a", "a*+a", "(?>(a)|b)+",
                                "(?:a|ab)+?c", "(a|ab)(c|bcd)", "\\bfoo\\b", "(?m)^a$", "a$", "^", "$", "\\Z", "", "(?:)", "()",
                                "()*", "(a|)*", "(|a)+", "(?:a?)*", "(?:a?)*?b", "(?:(a)?)*", "(a?)+?b", "(?i)aB", "[a-c]+", "a{2,3}",
                                "(ab){2}", "(a){0}", "(a){0}b", "a{0}", "(?:a|b){2,}?", "(?:ab)*+a", "(a)++", "(a|b)*+b"])
            try:
                re.compile(pat, flags)
                break
            except Exception:
                continue
        else:
            pat, flags = "a", 0
        chars = [ch for ch in pat if ch not in "()[]{}?*+|^$.\\-:=!<>"] or ["a"]
        alpha = (chars + ["a", "b", "c", "\n", " ", "A", "é"]) if r.random() < 0.8 else ["a", "b"]
        subj = "".join(r.choice(alpha) for _ in range(r.choice([0, 1, 2, 3, 4, 5, 6, 8])))
        mode = r.choice(["match", "fullmatch", "search", "search", "findall", "finditer", "scanmatch", "split", "sub", "subcall",
                         "subcall", "expand", "groups", "matchop", "matchop", "prepr", "peq"])
        n = len(subj)
        text = True
        if r.random() < 0.15 and all(ord(x) < 128 for x in pat) and flags & 32 == 0:
            try:
                re.compile(pat.encode(), flags & ~256)
                text, flags = False, flags & ~256
            except Exception:
                pass
        if not text:
            subj = "".join(ch for ch in subj if ord(ch) < 256)
        c = {"mod": "textlibs", "fn": "re.exec", "pat": [ord(x) for x in pat], "text": text, "flags": flags, "mode": mode,
             "s": [ord(x) for x in subj], "pos": 0, "endpos": 2**63 - 1, "count": 0,
             "stext": text if (r.random() < 0.96 or any(ord(x) > 255 for x in subj)) else not text}
        if mode == "matchop":
            c["op"] = r.choice(["group", "group", "getitem", "start", "end", "span", "regs", "repr"])
            pool = [0, 1, 2, 3, -1, 10**30, -10**30, [120], [97], [121], {}]
            c["gs"] = [r.choice(pool) for _ in range(r.choice([0, 1, 1, 1, 2, 3]))]
            if c["op"] not in ("group",) and not c["gs"]:
                c["gs"] = [0]
        if mode == "peq":
            q = r.choice([pat, pat, pat + "a", ""])
            c["pat2"] = [ord(x) for x in q]
            c["flags2"] = r.choice([flags, flags, flags ^ 2])
        if r.random() < 0.25:
            c["pos"] = r.choice([0, 1, 2, n, n + 1, -1, -(2**62)])
            c["endpos"] = r.choice([0, 1, 2, n, n + 1, -1, 2**62, n - 1])
        if mode in ("split", "sub", "subcall"):
            c["count"] = r.choice([0, 0, 0, 1, 2, -1])
        if mode == "subcall":
            c["script"] = [r.choice([[97], [], [120, 121], None, None, {"other": "int"}, {"other": "float"}, {"raise": "boom"}])
                           for _ in range(r.randint(0, 6))]
        if mode in ("sub", "expand"):
            c["repl"] = [ord(x) for x in r.choice(["", "x", "\\g<0>", "[\\g<0>]", "\\1", "\\g<1>", "a\\1b", "\\n", "\\\\", "\\2"])]
        return c

    @classmethod
    def run_exec(cls, c):
        src, flags, mode = re_src(c), c["flags"], c["mode"]
        s = "".join(map(chr, c["s"]))
        if not c["stext"]:
            s = bytes(c["s"])
        pos, endpos = c["pos"], c["endpos"]

        def unval(x):
            return x if isinstance(x, list) else None

        def enc_m(m):
            if m is None:
                return None
            spans = []
            for g in range(m.re.groups + 1):
                sp = m.span(g)
                spans.append(None if sp == (-1, -1) else list(sp))
            return {"spans": spans, "lastindex": m.lastindex}

        def val(x):
            if x is None:
                return None
            return list(x) if isinstance(x, bytes) else [ord(ch) for ch in x]

        def item(x):
            return [val(y) for y in x] if isinstance(x, tuple) else val(x)

        def body():
            p = re.compile(src, flags)
            if mode == "prepr":
                return [ord(ch) for ch in repr(p)]
            if mode == "peq":
                q = re.compile(type(src)().join([]) if False else (("".join(map(chr, c["pat2"])) if c["text"] else bytes(c["pat2"]))), c["flags2"])
                return [p == q, hash(p) == hash(q)]
            if mode in ("match", "fullmatch", "search"):
                return enc_m(getattr(p, mode)(s, pos, endpos))
            if mode == "findall":
                return [item(x) for x in p.findall(s, pos, endpos)]
            if mode == "finditer":
                return [enc_m(m) for m in p.finditer(s, pos, endpos)]
            if mode == "scanmatch":
                sc = p.scanner(s, pos, endpos)
                return [enc_m(m) for m in iter(sc.match, None)]
            if mode == "split":
                return [val(x) for x in p.split(s, c["count"])]
            repl = "".join(map(chr, c.get("repl", [])))
            if not c["text"]:
                repl = bytes(c.get("repl", []))
            if mode == "sub":
                r, n = p.subn(repl, s, c["count"])
                return [val(r), n]
            if mode == "subcall":
                calls = [0]

                def f(m):
                    i = calls[0]
                    calls[0] += 1
                    x = c["script"][i] if i < len(c["script"]) else []
                    if isinstance(x, dict) and "raise" in x:
                        raise ValueError(x["raise"])
                    if isinstance(x, dict):
                        return {"int": 5, "float": 1.5}[x["other"]]
                    if x is None:
                        return None
                    return bytes(x) if isinstance(s, (bytes, bytearray)) else "".join(map(chr, x))
                r, n = p.subn(f, s, c["count"])
                return [val(r), n]
            m = p.search(s, pos, endpos)
            if m is None:
                return None
            if mode == "matchop":
                gs = [("".join(map(chr, g)) if isinstance(g, list) else ([] if isinstance(g, dict) else g)) for g in c["gs"]]
                op = c["op"]
                if op == "group":
                    x = m.group(*gs)
                    return [val(y) for y in x] if isinstance(x, tuple) else val(x)
                if op == "getitem":
                    return val(m[gs[0]])
                if op == "start":
                    return m.start(gs[0])
                if op == "end":
                    return m.end(gs[0])
                if op == "span":
                    return list(m.span(gs[0]))
                if op == "regs":
                    return [list(x) for x in m.regs]
                return [ord(ch) for ch in repr(m)]
            if mode == "expand":
                return val(m.expand(repl))
            return {"groups": [val(x) for x in m.groups()],
                    "gd": [[[ord(ch) for ch in k], val(v)] for k, v in m.groupdict().items()],
                    "lastgroup": None if m.lastgroup is None else [ord(ch) for ch in m.lastgroup]}

        return common.py_result(body)

    @classmethod
    def run_args(cls, c):
        first = "maxsplit" if c["f"] == "split" else "count"
        kw = {}
        if "kw1" in c:
            kw[first] = c["kw1"]
        if "kw2" in c:
            kw["flags"] = c["kw2"]
        seen = []

        class P:
            pass

        def body():
            import warnings
            real = re._compile

            class Rec:
                def sub(self, repl, string, count):
                    seen.append(count)

                def subn(self, repl, string, count):
                    seen.append(count)

                def split(self, string, maxsplit):
                    seen.append(maxsplit)

            def fake(pattern, flags):
                seen.append(int(flags))
                return Rec()

            re._compile = fake
            try:
                with warnings.catch_warnings():
                    warnings.simplefilter("ignore")
                    if c["f"] == "split":
                        re.split("a", "b", *c["args"], **kw)
                    else:
                        getattr(re, c["f"])("a", "b", "c", *c["args"], **kw)
            finally:
                re._compile = real
            return [seen[1], seen[0]]

        return common.py_result(body)

    @classmethod
    def run(cls, c):
        if c["fn"] == "re.sem":
            return cls.run_sem(c)
        if c["fn"] == "re.exec":
            return cls.run_exec(c)
        if c["fn"] == "re.validate":
            return cls.run_validate(c)
        if c["fn"] == "re.scanner":
            return cls.run_scanner(c)
        if c["fn"] == "re.args":
            return cls.run_args(c)
        if c["fn"] == "re.escape":
            s = "".join(map(chr, c["s"]))
            return {"ok": [ord(x) for x in re.escape(s)]}
        src = re_src(c)

        def body():
            if c["fn"] == "re.code":
                return [int(x) for x in re._compiler._code(sre_parse.parse(src, c["flags"]), c["flags"])]
            if c["fn"] == "re.parse":
                p = sre_parse.parse(src, c["flags"])
                return {"p": re_nodes(p), "flags": p.state.flags, "groups": p.state.groups,
                        "width": list(p.getwidth()), "gd": [[[ord(x) for x in k], v] for k, v in p.state.groupdict.items()]}
            p = sre_parse.parse(src, c["flags"])

            class P:
                groups = p.state.groups - 1
                groupindex = p.state.groupdict
            repl = "".join(map(chr, c["repl"]))
            if not c["text"]:
                if max(c["repl"], default=0) > 255:
                    return None
                repl = bytes(c["repl"])
            res = sre_parse.parse_template(repl, P)
            return [{"g": x} if isinstance(x, int) else (x if isinstance(x, list) else
                    (list(x) if isinstance(x, bytes) else [ord(ch) for ch in x])) for x in res]

        res = common.py_result(body)
        return res

    @staticmethod
    def norm(lean_exc_msg):
        return lean_exc_msg


# ---- driver ----------------------------------------------------------------

@area("path", 8)
class PathArea:
    PARTS = ["a", "b", ".", "..", "/", "//", "///", "\\", "\\\\", "C:", "c:", ":", "\\\\?\\", "\\\\?\\UNC\\", "\\\\h\\s", "//h/s", "UNC",
             "x.y", ".z", "..w", "...", " ", "\xe9", "\x00", ""]

    @classmethod
    def val(cls, r):
        t = "".join(r.choice(cls.PARTS) for _ in range(r.choice([0, 1, 1, 2, 3, 3, 4, 5, 6, 8])))
        return {"b": list(t.encode("latin-1"))} if r.random() < 0.2 else {"s": cps(t)}

    @classmethod
    def arg(cls, r):
        x = r.random()
        if x < 0.82:
            return cls.val(r)
        if x < 0.92:
            return {"pl": cls.val(r)}
        if x < 0.95:
            return {"pl": {"raise": r.choice([["ValueError", "boom"], ["TypeError", "boom"], ["AttributeError", "boom"]])}}
        if x < 0.97:
            return {"pl": {"bad": "int"}}
        return {"o": r.choice(["int", "NoneType"])}

    @classmethod
    def gen(cls, r):
        f = r.choice(["pisabs", "psplit", "psplitext", "pbasename", "pdirname", "pjoin", "pjoin", "psplitroot", "pnormpath", "pnormpath",
                      "nisabs", "nsplit", "nsplitext", "nsplitroot", "njoin", "njoin", "njoin", "nnormpath", "nnormpath"])
        c = {"mod": "textlibs", "fn": "path." + f}
        if f in ("pjoin", "njoin"):
            k = r.choice([1, 2, 2, 2, 3, 4])
            if r.random() < 0.8:
                c["args"] = [cls.val(r) if r.random() < 0.9 else cls.arg(r) for _ in range(k)]
                if r.random() < 0.9:
                    b = "b" in c["args"][0]
                    c["args"] = [({"b": a.get("b", a.get("s"))} if b else {"s": a.get("b", a.get("s"))}) if ("b" in a or "s" in a) else a for a in c["args"]]
            else:
                c["args"] = [cls.arg(r) for _ in range(k)]
        elif f in ("pnormpath", "psplitroot"):
            c["args"] = [cls.val(r)]
        else:
            c["args"] = [cls.arg(r)]
        return c

    @staticmethod
    def obj(j):
        class PL:
            def __init__(self, v):
                self.v = v

            def __fspath__(self):
                v = self.v
                if "raise" in v:
                    raise mk_exc(v["raise"])
                if "bad" in v:
                    return 5
                return bytes(v["b"]) if "b" in v else txt(v["s"])
        PL.__qualname__ = "PL"
        if "pl" in j:
            return PL(j["pl"])
        if "o" in j:
            return {"int": 1, "NoneType": None}[j["o"]]
        return bytes(j["b"]) if "b" in j else txt(j["s"])

    @staticmethod
    def enc(x):
        if isinstance(x, tuple):
            return [PathArea.enc(y) for y in x]
        if isinstance(x, bool):
            return x
        return [isinstance(x, bytes), list(x) if isinstance(x, bytes) else cps(x)]

    @classmethod
    def run(cls, c):
        import ntpath
        import posixpath
        f = c["fn"].split(".")[1]
        mod = posixpath if f[0] == "p" else ntpath
        args = [cls.obj(j) for j in c["args"]]

        def body():
            if warnings:
                warnings.simplefilter("ignore")
            r = getattr(mod, f[1:])(*args)
            if f == "pnormpath":
                return [cls.enc(r), cls.enc(r)]
            return cls.enc(r)
        return common.py_result(body)


@area("shlex", 6)
class ShlexArea:
    PARTS = ["a", "b", " ", "  ", "'", '"', "\\", "#", "\n", "\t", "\r", "$", "\xe9", "(", ")", ";", "&", "|", "<", ">", "=", "*", "~", "-", ".",
             "/", "''", '""', "\\'", '\\"', "\\\\", "\u0100", "ab c"]

    @classmethod
    def text(cls, r, n=12):
        return "".join(r.choice(cls.PARTS) for _ in range(r.randint(0, n)))

    @classmethod
    def gen(cls, r):
        f = r.choice(["split", "split", "lex", "lex", "lex", "quote", "join"])
        c = {"mod": "textlibs", "fn": "shlex." + f}
        if f == "split":
            c.update(s=cps(cls.text(r)), comments=r.random() < 0.3, posix=r.random() < 0.7)
        elif f == "lex":
            c.update(s=cps(cls.text(r)), posix=r.random() < 0.6, wsplit=r.random() < 0.4)
            if r.random() < 0.4:
                c["punct"] = cps(r.choice(["();<>|&", "();", "|", "<>"]))
            if r.random() < 0.2:
                c["commenters"] = cps(r.choice(["", "#;", "a"]))
            if r.random() < 0.15:
                c["quotes"] = cps(r.choice(["'", '"', "'a"]))
            if r.random() < 0.15:
                c["escape"] = cps(r.choice(["", "^", "\\^"]))
            if r.random() < 0.2:
                c["fail"] = r.randint(0, 10)
        elif f == "quote":
            if r.random() < 0.8:
                c["s"] = cps(cls.text(r, 5))
            elif r.random() < 0.3:
                c["raise"] = True
            else:
                c["truth"] = r.random() < 0.5
        else:
            c["args"] = [cps(cls.text(r, 4)) for _ in range(r.randint(0, 4))]
        return c

    @classmethod
    def run(cls, c):
        import shlex
        f = c["fn"].split(".")[1]

        def body():
            if f == "split":
                return [cps(x) for x in shlex.split(txt(c["s"]), comments=c["comments"], posix=c["posix"])]
            if f == "lex":
                inner = io.StringIO(txt(c["s"]))

                class S:
                    n = c.get("fail")

                    def tick(self):
                        if S.n is not None:
                            if S.n == 0:
                                raise ValueError("boom")
                            S.n -= 1

                    def read(self, k):
                        self.tick()
                        return inner.read(k)

                    def readline(self):
                        self.tick()
                        return inner.readline()
                pc = txt(c["punct"]) if "punct" in c else False
                lx = shlex.shlex(S(), posix=c["posix"], punctuation_chars=pc)
                lx.whitespace_split = c["wsplit"]
                for k in ("commenters", "quotes", "escape"):
                    if k in c:
                        setattr(lx, k, txt(c[k]))
                return [cps(x) for x in lx]
            if f == "quote":
                if "s" in c:
                    return cps(shlex.quote(txt(c["s"])))

                class Obj:
                    def __bool__(self):
                        if "raise" in c:
                            raise ValueError("boom")
                        return c["truth"]
                return cps(shlex.quote(Obj()))
            return cps(shlex.join([txt(a) for a in c["args"]]))
        return common.py_result(body)


@area("textwrap", 5)
class TextwrapArea:
    CHUNKS = ["a", "bb", "ccc", "dddd", "eeeeeeee", "aaaaaaaaaaaaaaaaaa", " ", "  ", "\t", "\u00a0", "-", "--", "ab-", "a-b-c", "--a", "a--b-cc-dd-eee",
              "", "\u3000", "\xe9\xe9", ".", "x y", "-----"]

    @classmethod
    def gen(cls, r):
        c = {"mod": "textlibs", "fn": "textwrap.chunks", "chunks": [cps(r.choice(cls.CHUNKS)) for _ in range(r.randint(0, 12))],
             "width": r.choice([-1, 0, 1, 2, 3, 4, 5, 6, 8, 10, 20]), "initial": cps(r.choice(["", "", "", ">", "> ", "    ", "      "])),
             "subsequent": cps(r.choice(["", "", "", "  ", ">>>", "       "])), "drop": r.random() < 0.7, "blw": r.random() < 0.7,
             "boh": r.random() < 0.7, "ph": cps(r.choice([" [...]", "...", " ", "", "   x"]))}
        if r.random() < 0.4:
            c["max"] = r.choice([-1, 0, 1, 2, 3, 5])
        return c

    @classmethod
    def run(cls, c):
        import textwrap

        def body():
            kw = dict(width=c["width"], initial_indent=txt(c["initial"]), subsequent_indent=txt(c["subsequent"]),
                      drop_whitespace=c["drop"], break_long_words=c["blw"], break_on_hyphens=c["boh"], placeholder=txt(c["ph"]),
                      max_lines=c.get("max"))
            chunks = [txt(x) for x in c["chunks"]]
            # Only a pass through _handle_long_word can leave the chunks as they were, so counting
            # those calls is an exact hang test. The bound is far above any terminating run.
            calls = [10 * (sum(map(len, chunks)) + len(chunks)) + 100]

            class Hang(Exception):
                pass

            class W(textwrap.TextWrapper):
                def _handle_long_word(self, *a):
                    calls[0] -= 1
                    if calls[0] < 0:
                        raise Hang
                    return super()._handle_long_word(*a)
            try:
                return [cps(x) for x in W(**kw)._wrap_chunks(chunks)]
            except Hang:
                return "hang"
        return common.py_result(body)


@area("quopri", 4)
class QuopriArea:
    A = [b" ", b"\t", b"\r", b"\n", b"=", b".", b"_", b"a", b"\x00", b"\xff", b"\r\n", b"=\n", b"=41", b"=4", b"=g", b"~", b"\x7f", b"=ab", b"=AB", b"= \n"]

    @classmethod
    def data(cls, r):
        k = r.random()
        if k < 0.25:
            return b"a" * r.choice([1, 70, 73, 74, 75, 76, 77, 78, 150, 151, 152, 153]) + b"".join(r.choice(cls.A) for _ in range(r.randint(0, 3)))
        if k < 0.4:
            return bytes(r.randrange(256) for _ in range(r.randint(0, 100)))
        return b"".join(r.choice(cls.A) for _ in range(r.randint(0, 12)))

    @classmethod
    def gen(cls, r):
        fn = r.choice(["encodestring", "decodestring", "py_encodestring", "py_decodestring", "encode_c", "decode_c", "encode_py", "decode_py",
                       "helpers"])
        c = {"mod": "textlibs", "fn": "quopri." + fn, "q": r.random() < 0.5, "h": r.random() < 0.5}
        d = cls.data(r)
        boom = {"raise": ["ValueError", "boom"]}
        if fn == "helpers":
            c["c"] = r.randrange(256)
        elif fn.endswith("string"):
            c["d"] = list(d)
        elif fn.endswith("_c"):
            c["rd"] = boom if r.random() < 0.15 else list(d)
            c["writes"] = [r.choice([None, None, {"raise": ["OSError", "boom"]}]) for _ in range(r.choice([0, 0, 1]))]
        else:
            lines = [list(x) for x in d.splitlines(True) if b"\r" not in x[:-1]] if r.random() < 0.5 else [list(x) for x in cls.nlsplit(d)]
            if r.random() < 0.2:
                lines.insert(r.randint(0, len(lines)), boom)
            if r.random() < 0.1:
                lines.insert(r.randint(0, len(lines)), [])
            c["lines"] = lines
            c["writes"] = [r.choice([None, None, {"raise": ["OSError", "boom"]}]) for _ in range(r.choice([0, 0, 1, 2, 3]))]
        return c

    @staticmethod
    def nlsplit(d):
        return [x for x in __import__("re").findall(b"[^\n]*\n|[^\n]+", d)]

    @classmethod
    def run(cls, c):
        import quopri
        fn = c["fn"].split(".")[1]

        class F:
            def __init__(self):
                self.written, self.i, self.w = [], 0, list(c.get("writes", []))

            def read(self):
                if isinstance(c["rd"], dict):
                    raise ValueError("boom")
                return bytes(c["rd"])

            def readline(self):
                if self.i >= len(c["lines"]):
                    return b""
                x = c["lines"][self.i]
                self.i += 1
                if isinstance(x, dict):
                    raise ValueError("boom")
                return bytes(x)

            def write(self, b):
                self.written.append(list(b))
                if self.w:
                    if self.w.pop(0) is not None:
                        raise OSError("boom")

        def body():
            saved = quopri.a2b_qp, quopri.b2a_qp
            if fn.endswith("_py") or fn.startswith("py_"):
                quopri.a2b_qp = quopri.b2a_qp = None
            try:
                if fn == "helpers":
                    b = bytes([c["c"]])
                    x = quopri.ishex(b)
                    return [1 if quopri.needsquoting(b, c["q"], c["h"]) else 0, 1 if x else 0] + list(quopri.quote(b)) + \
                        ([quopri.unhex(b + b)] if x else [])
                if fn in ("encodestring", "py_encodestring"):
                    return list(quopri.encodestring(bytes(c["d"]), c["q"], c["h"]))
                if fn in ("decodestring", "py_decodestring"):
                    return list(quopri.decodestring(bytes(c["d"]), c["h"]))
                f = F()
                try:
                    if fn.startswith("encode"):
                        quopri.encode(f, f, c["q"], c["h"])
                    else:
                        quopri.decode(f, f, c["h"])
                    res = {"ok": None}
                except Exception as e:
                    res = {"exc": type(e).__name__, "msg": str(e)}
                return {"written": f.written, "res": res}
            finally:
                quopri.a2b_qp, quopri.b2a_qp = saved
        return common.py_result(body)


@area("html", 4)
class HtmlArea:
    NAMES = ["amp", "amp;", "lt;", "gt", "quot;", "notin;", "notit;", "not", "no", "n", "nsubE;", "AElig", "AElig;", "AEligx", "CounterClockwiseContourIntegral;",
             "CounterClockwiseContourIntegra", "xx", "x;", ";", "a" * 31, "a" * 32, "a" * 33, "a" * 32 + ";", "amp" + "b" * 29 + ";", "amp" + "b" * 30 + ";"]
    NUMS = [0, 1, 8, 9, 10, 11, 12, 13, 14, 31, 32, 38, 60, 126, 127, 128, 129, 0x8d, 0x9b, 0x9f, 0xa0, 0xd7ff, 0xd800, 0xdfff, 0xe000, 0xfdcf, 0xfdd0, 0xfdef, 0xfdf0,
            0xfffd, 0xfffe, 0xffff, 0x10000, 0x1fffe, 0x10fffd, 0x10fffe, 0x10ffff, 0x110000, 2**32, 2**64, 10**40]

    @classmethod
    def piece(cls, r):
        k = r.random()
        if k < 0.3:
            return "&" + r.choice(cls.NAMES) + r.choice(["", "", ";", " ", "x", "&"])
        if k < 0.55:
            n = r.choice(cls.NUMS)
            return "&#" + str(n) + r.choice(["", ";", ";;", "x"])
        if k < 0.75:
            n = r.choice(cls.NUMS)
            return "&#" + r.choice("xX") + r.choice(["%x", "%X"]) % n + r.choice(["", ";", "g"])
        if k < 0.8:
            return "&#" + r.choice(["0", "1", "9"]) * r.choice([4299, 4300, 4301, 5000]) + r.choice(["", ";"])
        if k < 0.83:
            return "&#x" + r.choice(["0", "1", "f"]) * 5000
        return r.choice(["&", "&&", "&#", "&#;", "&#x", "&#x;", "&#X;", "&#xg", "& ", "&;", "<", ">", '"', "\'", "a", " ", "\t", "\n", "\f", "\u0660", "&\u0660;",
                         "\xe9", "&\xe9", "&#\u0661;", "\ud800", "#", ";"])

    @classmethod
    def gen(cls, r):
        fn = r.choice(["escape", "unescape", "unescape", "unescape"])
        c = {"mod": "textlibs", "fn": "html." + fn, "s": cps("".join(cls.piece(r) for _ in range(r.randint(0, 5))))}
        if fn == "escape":
            c["quote"] = r.random() < 0.5
        return c

    @classmethod
    def run(cls, c):
        import html

        def body():
            s = txt(c["s"])
            if c["fn"] == "html.escape":
                return cps(html.escape(s, c["quote"]))
            return cps(html.unescape(s))
        return common.py_result(body)


@area("difflib", 5)
class DifflibArea:
    @staticmethod
    def seq(r):
        k = r.random()
        if k < 0.1:
            # long enough for the popular test
            n = r.choice([199, 200, 201, 250, 300, 400])
            return [r.choice([1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, r.randrange(300)]) for _ in range(n)]
        m = r.choice([2, 3, 4, 8])
        return [r.randrange(m) for _ in range(r.randint(0, 14))]

    @classmethod
    def gen_ops(cls, r, a, b, seq):
        ops = []
        for _ in range(r.randint(1, 6)):
            k = r.random()
            if k < 0.25:
                ops.append({"op": "opcodes"})
            elif k < 0.4:
                ops.append({"op": "blocks"})
            elif k < 0.55:
                ops.append({"op": "grouped", "n": r.choice([0, 1, 2, 3])})
            elif k < 0.7:
                ops.append({"op": r.choice(["ratio", "quick", "real"])})
            elif k < 0.87:
                la, lb = len(a), len(b)
                x = sorted([r.randint(0, la), r.randint(0, la)])
                y = sorted([r.randint(0, lb), r.randint(0, lb)])
                ops.append({"op": "longest", "alo": x[0], "ahi": x[1], "blo": y[0], "bhi": y[1]})
            elif k < 0.93:
                ops.append({"op": "seqs", "x": seq(), "y": seq(), "same": r.random() < 0.3, "same2": r.random() < 0.3})
            else:
                ops.append({"op": r.choice(["seq1", "seq2"]), "x": seq(), "same": r.random() < 0.3})
        return ops

    @classmethod
    def gen_obj(cls, r):
        """Objects of a class of ours: equal objects that are not identical, hash collisions, a __hash__ or
        __eq__ that raises, and the same object in several places."""
        kinds = r.choice(["lawful", "lawful", "collide", "hashraise", "eqraise", "unlawful"])
        n = r.randint(1, 8)
        elems = []
        for i in range(n):
            v = r.randrange(5)
            if kinds == "collide":
                h = r.choice([1, 2, 9])
            elif kinds == "unlawful":
                h = r.randrange(6)
            else:
                h = v % 3 + 1 if r.random() < 0.5 else v + 8
            if kinds != "unlawful":
                h = v + 8 if kinds != "collide" else h
            e = {"v": v, "h": h, "bad": []}
            elems.append(e)
        if kinds == "collide":
            for e in elems:
                e["h"] = e["v"] % 2 + 1
        if kinds == "hashraise":
            for _ in range(r.randint(1, 2)):
                elems[r.randrange(n)]["h"] = None
        if kinds == "eqraise":
            for _ in range(r.randint(1, 3)):
                e = elems[r.randrange(n)]
                e["bad"].append(r.randrange(n))
                if r.random() < 0.5:
                    e["h"] = 1
                    elems[r.randrange(n)]["h"] = 1

        def seq():
            return [r.randrange(n) for _ in range(r.randint(0, 9))]
        a, b = seq(), seq()
        if r.random() < 0.3:
            b = list(a)
        if r.random() < 0.05:
            b = [r.randrange(n) for _ in range(r.choice([199, 200, 201, 300]))]
        return {"mod": "textlibs", "fn": "difflib.obj", "elems": elems, "a": a, "b": b, "auto": r.random() < 0.6,
                "hasjunk": r.random() < 0.3, "junk": [r.randrange(5) for _ in range(r.randint(0, 2))],
                "boom": [r.randrange(n)] if r.random() < 0.2 else [], "ops": cls.gen_ops(r, a, b, seq)}

    @classmethod
    def run_obj(cls, c):
        import difflib

        class El:
            __slots__ = ("i", "v", "h", "bad")

            def __init__(self, i, d):
                self.i, self.v, self.h, self.bad = i, d["v"], d["h"], d["bad"]

            def __hash__(self):
                if self.h is None:
                    raise ValueError(f"hash {self.i}")
                return self.h

            def __eq__(self, o):
                if o.i in self.bad:
                    raise ValueError(f"eq {self.i} {o.i}")
                return self.v == o.v

        els = [El(i, d) for i, d in enumerate(c["elems"])]

        def junk(x):
            if x.i in c["boom"]:
                raise ValueError("boom")
            return x.v in c["junk"]

        def conv(l):
            return [els[i] for i in l]

        def body():
            s = difflib.SequenceMatcher(junk if c["hasjunk"] else None, conv(c["a"]), conv(c["b"]), c["auto"])
            out = []
            for o in c["ops"]:
                try:
                    out.append(cls.op(s, o, conv))
                except Exception as e:
                    out.append(["exc", {"exc": type(e).__name__, "msg": str(e)}])
            return out
        return common.py_result(body)

    @classmethod
    def op(cls, s, o, conv):
        k = o["op"]
        if k == "blocks":
            return [list(t) for t in s.get_matching_blocks()]
        if k == "opcodes":
            return [list(t) for t in s.get_opcodes()]
        if k == "grouped":
            return [[list(t) for t in g] for g in s.get_grouped_opcodes(o["n"])]
        if k in ("ratio", "quick", "real"):
            f = {"ratio": s.ratio, "quick": s.quick_ratio, "real": s.real_quick_ratio}[k]()
            length = len(s.a) + len(s.b)
            if length == 0:
                return [0, 0] if f == 1.0 else ["bad", f]
            m = round(f * length / 2)
            return [m, length] if 2.0 * m / length == f else ["bad", f]
        if k == "longest":
            return list(s.find_longest_match(o["alo"], o["ahi"], o["blo"], o["bhi"]))
        if k == "seqs":
            s.set_seqs(s.a if o["same"] else conv(o["x"]), s.b if o["same2"] else conv(o["y"]))
            return None
        f = s.set_seq1 if k == "seq1" else s.set_seq2
        cur = s.a if k == "seq1" else s.b
        f(cur if o["same"] else conv(o["x"]))
        return None

    LINES = ["a\n", "b\n", "abc\n", "abd\n", "  x\n", "\n", "#\n", " # \n", "hello world\n", "hello wurld\n", "abcdefghij\n",
             "abcdefghix\n", "\tab\n", "ab \n", "one two three\n", "one tree three\n", "x", "", "- y\n", "? z\n", "+ q\n", "  w\n"]
    OBJS = [1, b"x", None, [1]]

    @classmethod
    def txt(cls, r):
        return r.choice(cls.LINES)

    @classmethod
    def strs(cls, r, m=8):
        return [[ord(c) for c in cls.txt(r)] for _ in range(r.randint(0, m))]

    @classmethod
    def gen_text(cls, r):
        k = r.choice(["unified", "unified", "context", "context", "ndiff", "ndiff", "ndiff", "restore", "range", "junk", "keepws", "close"])
        c = {"mod": "textlibs", "fn": "difflib.text", "op": k}

        def seq():
            base = cls.strs(r)
            if r.random() < 0.3:
                # close to another sequence, so the matcher finds something
                base = [[ord(ch) for ch in cls.LINES[i % 6]] for i in range(r.randint(0, 12))]
            return base

        def edited(a):
            b = list(a)
            for _ in range(r.randint(0, 3)):
                if b:
                    i = r.randrange(len(b))
                    b[i] = [ord(ch) for ch in cls.txt(r)]
            if r.random() < 0.3:
                b.insert(r.randint(0, len(b)), [ord(ch) for ch in cls.txt(r)])
            return b

        if k in ("unified", "context"):
            a = seq()
            b = edited(a) if r.random() < 0.6 else seq()
            bad = r.random() < 0.2

            def wrap(l):
                x = list(l)
                if bad and r.random() < 0.7:
                    x.insert(r.randint(0, len(x)), {"o": r.randrange(4)})
                if r.random() < 0.03:
                    return {"str": [97, 10]}
                return x

            def text(v):
                if r.random() < 0.03:
                    return {"bad": 1}
                return [ord(ch) for ch in v]
            c.update({"a": wrap(a), "b": wrap(b), "f": text(r.choice(["", "x.py"])), "t": text(r.choice(["", "y.py"])),
                      "fd": text(r.choice(["", "2026"])), "td": text(r.choice(["", "2027"])), "n": r.choice([0, 1, 2, 3, 3, 5]),
                      "lt": text(r.choice(["\n", "", "\r\n"]))})
        elif k == "ndiff":
            a = seq()
            b = edited(a) if r.random() < 0.7 else seq()
            lj, cj = None, "default"
            if r.random() < 0.3:
                lj = {"junk": cls.strs(r, 2), "boom": cls.strs(r, 1) if r.random() < 0.3 else []}
            x = r.random()
            if x < 0.2:
                cj = None
            elif x < 0.4:
                cj = {"junk": [32], "boom": [r.choice([97, 98, 104, 120])] if r.random() < 0.5 else []}
            c.update({"a": a, "b": b, "lj": lj, "cj": cj})
        elif k == "restore":
            c.update({"d": cls.strs(r), "which": r.choice([1, 2, 2, 1, 0, 3, -1])})
        elif k == "range":
            s = r.randint(0, 5)
            c.update({"s": s, "e": s + r.choice([0, 0, 1, 1, 2, 3, 10])})
        elif k == "junk":
            c["s"] = [ord(ch) for ch in r.choice(cls.LINES + [" \t", "##", "#x", "\u00a0#\u2003"])]
        elif k == "keepws":
            c.update({"s": [ord(ch) for ch in cls.txt(r)], "tags": [r.choice([32, 94, 45, 43]) for _ in range(r.randint(0, 12))]})
        else:
            import struct
            cut = r.choice([0.0, 0.3, 0.5, 0.6, 0.75, 0.8, 1.0, -0.1, 1.5, float("nan")])
            c.update({"w": [ord(ch) for ch in cls.txt(r)], "ps": cls.strs(r, 6), "n": r.choice([1, 2, 3, 10, 0, -1]),
                      "cut": struct.unpack(">Q", struct.pack(">d", cut))[0]})
        return c

    @classmethod
    def run_text(cls, c):
        import difflib
        import struct

        def s(l):
            return "".join(map(chr, l))

        def lines(a):
            if isinstance(a, dict):
                return s(a["str"])
            return [cls.OBJS[x["o"]] if isinstance(x, dict) else s(x) for x in a]

        def text(v):
            return b"x" if isinstance(v, dict) else s(v)

        def nats(l):
            return [[ord(ch) for ch in x] for x in l]

        def drain(g):
            out = []
            try:
                for x in g:
                    out.append(x)
            except Exception as e:
                return out, ["exc", {"exc": type(e).__name__, "msg": str(e)}]
            return out, None

        k = c["op"]

        def body():
            if k in ("unified", "context"):
                f = difflib.unified_diff if k == "unified" else difflib.context_diff
                g = f(lines(c["a"]), lines(c["b"]), text(c["f"]), text(c["t"]), text(c["fd"]), text(c["td"]), c["n"], text(c["lt"]))
                if k == "unified":
                    return nats(list(g))
                out, e = drain(g)
                return [nats(out), e]
            if k == "ndiff":
                def lj(x):
                    if [ord(ch) for ch in x] in c["lj"]["boom"]:
                        raise ValueError("boom")
                    return [ord(ch) for ch in x] in c["lj"]["junk"]

                def cj(x):
                    if ord(x) in c["cj"]["boom"]:
                        raise ValueError("boom")
                    return ord(x) in c["cj"]["junk"]
                cjf = None if c["cj"] is None else difflib.IS_CHARACTER_JUNK if isinstance(c["cj"], str) else cj
                a, b = [s(x) for x in c["a"]], [s(x) for x in c["b"]]
                out, e = drain(difflib.ndiff(a, b, lj if c["lj"] is not None else None, cjf))
                r1 = r2 = []
                if e is None:
                    r1, r2 = list(difflib.restore(out, 1)), list(difflib.restore(out, 2))
                return [[nats(out), e], {"ok": nats(r1)}, {"ok": nats(r2)}]
            if k == "restore":
                return nats(list(difflib.restore([s(x) for x in c["d"]], c["which"])))
            if k == "range":
                return nats([difflib._format_range_unified(c["s"], c["e"]), difflib._format_range_context(c["s"], c["e"])])
            if k == "junk":
                x = s(c["s"])
                return [difflib.IS_LINE_JUNK(x), [difflib.IS_CHARACTER_JUNK(ch) for ch in x]]
            if k == "keepws":
                return nats([difflib._keep_original_ws(s(c["s"]), s(c["tags"]))])
            cut = struct.unpack(">d", struct.pack(">Q", c["cut"]))[0]
            return nats(difflib.get_close_matches(s(c["w"]), [s(x) for x in c["ps"]], c["n"], cut))
        return common.py_result(body)

    @classmethod
    def gen(cls, r):
        x = r.random()
        if x < 0.35:
            return cls.gen_text(r)
        if x < 0.7:
            return cls.gen_obj(r)
        a, b = cls.seq(r), cls.seq(r)
        if r.random() < 0.3:
            b = list(a)
            for _ in range(r.randint(0, 3)):
                if b:
                    b[r.randrange(len(b))] = r.randrange(9)
        ops = []
        for _ in range(r.randint(1, 6)):
            k = r.random()
            if k < 0.2:
                ops.append({"op": "opcodes"})
            elif k < 0.35:
                ops.append({"op": "blocks"})
            elif k < 0.6:
                ops.append({"op": "grouped", "n": r.choice([0, 1, 2, 3, 3, 5])})
            elif k < 0.67:
                ops.append({"op": r.choice(["ratio", "quick", "real"])})
            elif k < 0.87:
                la, lb = len(a), len(b)
                x = sorted([r.randint(0, la), r.randint(0, la)])
                y = sorted([r.randint(0, lb), r.randint(0, lb)])
                if r.random() < 0.1:
                    x[1] += r.choice([1, 5])
                if r.random() < 0.1:
                    y[1] += r.choice([1, 5])
                ops.append({"op": "longest", "alo": x[0], "ahi": x[1], "blo": y[0], "bhi": y[1]})
            elif k < 0.93:
                ops.append({"op": "seqs", "x": cls.seq(r), "y": cls.seq(r), "same": r.random() < 0.3, "same2": r.random() < 0.3})
            else:
                w = r.choice(["seq1", "seq2"])
                ops.append({"op": w, "x": cls.seq(r), "same": r.random() < 0.3})
        return {"mod": "textlibs", "fn": "difflib.seq", "a": a, "b": b, "auto": r.random() < 0.6, "hasjunk": r.random() < 0.3,
                "junk": [r.randrange(9) for _ in range(r.randint(0, 2))], "boom": [r.randrange(9)] if r.random() < 0.1 else [], "ops": ops}

    @classmethod
    def run(cls, c):
        import difflib
        if c["fn"] == "difflib.obj":
            return cls.run_obj(c)
        if c["fn"] == "difflib.text":
            return cls.run_text(c)

        def junk(x):
            if x in c["boom"]:
                raise ValueError("boom")
            return x in c["junk"]

        def body():
            s = difflib.SequenceMatcher(junk if c["hasjunk"] else None, list(c["a"]), list(c["b"]), c["auto"])
            out = []
            for o in c["ops"]:
                try:
                    out.append(cls.op(s, o, list))
                except Exception as e:
                    out.append(["exc", {"exc": type(e).__name__, "msg": str(e)}])
            return out
        return common.py_result(body)


@area("etree", 4)
class EtreeArea:
    """Element children as a sequence, C accelerator vs pure-Python twin (EtreeModel.lean)."""
    VALS = [None, 0, 1, 2, -1, -2, 3, 4, 5, 7, 8, 9, 10, -8, -9, -10, 100, -100,
            2**63 - 1, 2**63, -2**63, -2**63 - 1, 2**64]
    STEPS = [None, 1, 1, 1, 2, 3, -1, -1, -2, -3, 0, 5, -7, 2**63, -2**63, 2**63 - 1]

    @classmethod
    def gen(cls, r):
        f = r.choice(["get", "set", "set", "set", "del", "append", "insert", "extend"])
        c = {"mod": "textlibs", "fn": "etree." + f, "impl": r.choice(["c", "py"]),
             "kids": list(range(r.randint(0, 9)))}
        if f in ("append", "insert", "extend"):
            c["obj"] = r.choice([60, 61, 1000])
            if f == "insert":
                c["idx"] = r.choice(cls.VALS[1:])
            if f == "extend":
                xs = [60 + i for i in range(r.randint(0, 5))]
                if xs and r.random() < 0.15:
                    xs[r.randrange(len(xs))] = 1000
                c["arg"] = {"kind": r.choice(["seq", "seq", "iter", "noniter"]), "xs": xs,
                            "raise": r.random() < 0.3, "eff": r.choice([0, 0, 1, 2, 3])}
            return c
        if r.random() < 0.3:
            c["idx"] = r.choice(cls.VALS[1:])
            if f == "set":
                c["obj"] = r.choice([60, 61, 1000])
        else:
            c["slice"] = [r.choice(cls.VALS), r.choice(cls.VALS), r.choice(cls.STEPS)]
            if f == "set":
                xs = [60 + i for i in range(r.randint(0, 5))]
                if xs and r.random() < 0.1:
                    xs[r.randrange(len(xs))] = 1000
                c["arg"] = {"kind": r.choice(["seq", "seq", "iter", "noniter"]), "xs": xs,
                            "raise": r.random() < 0.2, "eff": r.choice([0, 0, 1, 2, 3])}
        return c

    @classmethod
    def run(cls, c):
        if not hasattr(cls, "pymod"):
            # import_fresh_module rebinds xml.etree.ElementTree on the package, so take the
            # C-accelerated module first and keep both.
            import xml.etree.ElementTree as cmod
            from test.support import import_helper
            cls.cmod = cmod
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                cls.pymod = import_helper.import_fresh_module("xml.etree.ElementTree", blocked=["_elementtree"])
            assert cls.cmod.Element is not cls.pymod.Element and cls.cmod.Element.__module__ == "xml.etree.ElementTree"
            import _elementtree
            assert cls.cmod.Element is _elementtree.Element
        mod = cls.cmod if c["impl"] == "c" else cls.pymod
        e = mod.Element("r")
        e.extend([mod.Element("e%d" % n) for n in c["kids"]])

        def num(k):
            return int(k.tag[1:])

        def mk(n):
            return mod.Element("e%d" % n) if n < 1000 else n

        key = c["idx"] if "idx" in c else slice(*c["slice"]) if "slice" in c else None
        f = c["fn"].split(".")[1]
        if f == "get":
            return common.py_result(lambda: [num(k) for k in e[key]] if isinstance(key, slice) else num(e[key]))

        def arg():
            a = c["arg"]
            items = [mk(n) for n in a["xs"]]
            if a["kind"] == "seq":
                return items
            if a["kind"] == "noniter":
                return 1000

            def g():
                eff = a["eff"]
                if eff == 1:
                    e.clear()
                elif eff == 2:
                    e.append(mod.Element("e50"))
                elif eff == 3 and len(e):
                    del e[-1]
                yield from items
                if a["raise"]:
                    raise ValueError("boom")
            return g()

        def body():
            if f == "append":
                e.append(mk(c["obj"]))
            elif f == "insert":
                e.insert(c["idx"], mk(c["obj"]))
            elif f == "extend":
                e.extend(arg())
            elif f == "del":
                del e[key]
            elif "idx" in c:
                e[key] = mk(c["obj"])
            else:
                e[key] = arg()
        out = common.py_result(lambda: (body(), None)[1])
        return {"ok": {"kids": [num(k) for k in e], "out": out}}


@area("etreepath", 5)
class EtreePathArea:
    """ElementPath compile and the C find fast path (EtreePath.lean)."""
    PARTS = ["a", "b", "/", "//", ".", "..", "*", "[", "]", "@", "=", "!=", "(", ")", "()", "::", ":", "'v'", '"w"',
             " ", "1", "-1", "0", "2", "last", "-", "{ns}", "{*}", "{}", "{", "}", "!", "x:y", "'", '"', "\t", "{x}b",
             "a", "b", "/", "*", "[", "]", "@k", "text()", "١", "é", "　", "-2"]
    TAGS = ["a", "b", "{ns}a", "{x}b", "", "a:b", "c d", "{ns}b", "{x}a"]
    NS = [None, [], [["x", "ns"]], [["", "ns"]], [["x", "ns"], ["", "d"]], [["a", "u"]]]

    @classmethod
    def tree(cls, r, n=[0], depth=0):
        n[0] += 1
        return {"tag": cps(r.choice(cls.TAGS)), "text": cps("t%d" % n[0]) if r.random() < 0.8 else None,
                "kids": [cls.tree(r, n, depth + 1) for _ in range(r.randint(0, 3 if depth < 2 else 0))]}

    @classmethod
    def gen(cls, r):
        f = r.choice(["iterfind", "findall", "findall", "find", "findtext"])
        path = "".join(r.choice(cls.PARTS) for _ in range(r.randint(0, 5)))
        if r.random() < 0.25:
            path = r.choice(cls.TAGS + ["a", "b", "x:y", "{*}a", "{ns}*", "{*}*", "{}*", "{}a", ".//{*}a", "a/", ""])
        c = {"mod": "textlibs", "fn": "etreepath." + f, "impl": r.choice(["c", "py"]), "path": cps(path)}
        ns = r.choice(cls.NS)
        c["ns"] = None if ns is None else [[cps(k), cps(v)] for k, v in ns]
        if f != "iterfind":
            c["tree"] = cls.tree(r, [0])
            if f == "findtext":
                c["dflt"] = r.choice([None, cps("D")])
        return c

    @staticmethod
    def enc_sel(f):
        import inspect
        q = f.__qualname__
        owner, name = q.split(".<locals>.")[0], q.split(".")[-1]
        out = {}
        for k, v in inspect.getclosurevars(f).nonlocals.items():
            if isinstance(v, str):
                out[k] = cps(v)
            elif isinstance(v, int) and not isinstance(v, bool):
                out[k] = v
            elif callable(v) and "<locals>" in getattr(v, "__qualname__", ""):
                out[k] = EtreePathArea.enc_sel(v)
        return [owner, name, out]

    @classmethod
    def compile(cls, path, ns):
        """iterfind's own outcome, and whether its selectors include ones the model does not run."""
        from xml.etree import ElementPath as EP
        EP._cache.clear()
        nsd = None if ns is None else dict(ns)
        try:
            it = EP.iterfind(cls.cmod.Element("r"), path, nsd)
        except Exception as e:
            return {"exc": type(e).__name__, "msg": str(e)}, False
        if it is None:
            return {"ok": {"none": True}}, False
        p = path + "*" if path[-1:] == "/" else path
        key = (p,) + (tuple(sorted(nsd.items())) if nsd else ())
        sels = [cls.enc_sel(s) for s in EP._cache[key]]
        unmodelled = any(s[0] in ("prepare_parent", "prepare_predicate") for s in sels)
        return {"ok": {"sels": sels}}, unmodelled

    @classmethod
    def build(cls, mod, d):
        e = mod.Element(txt(d["tag"]))
        e.text = None if d["text"] is None else txt(d["text"])
        for k in d["kids"]:
            e.append(cls.build(mod, k))
        return e

    @classmethod
    def run(cls, c):
        from xml.etree import ElementPath as EP
        if not hasattr(cls, "pymod"):
            import xml.etree.ElementTree as cmod
            from test.support import import_helper
            cls.cmod = cmod
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                cls.pymod = import_helper.import_fresh_module("xml.etree.ElementTree", blocked=["_elementtree"])
        path, ns = txt(c["path"]), c["ns"]
        nsd = None if ns is None else {txt(k): txt(v) for k, v in ns}
        nsl = None if ns is None else [(txt(k), txt(v)) for k, v in ns]
        compiled, unmodelled = cls.compile(path, nsl)
        f = c["fn"].split(".")[-1]
        if f == "iterfind":
            return compiled
        mod = cls.cmod if c["impl"] == "c" else cls.pymod
        root = cls.build(mod, c["tree"])
        used = [False]
        saved = {n: getattr(EP, n) for n in ("find", "findall", "findtext")}

        def wrap(fn):
            def w(*a, **k):
                used[0] = True
                return fn(*a, **k)
            return w
        for n, fn in saved.items():
            setattr(EP, n, wrap(fn))
        EP._cache.clear()
        try:
            def enc(e):
                return [cps(e.tag), None if e.text is None else cps(e.text)]
            if f == "findall":
                res = common.py_result(lambda: [enc(x) for x in root.findall(path, nsd)])
            elif f == "find":
                res = common.py_result(lambda: (lambda x: None if x is None else enc(x))(root.find(path, nsd)))
            else:
                d = None if c.get("dflt") is None else txt(c["dflt"])
                res = common.py_result(lambda: (lambda x: None if x is None else cps(x))(root.findtext(path, d, nsd)))
        finally:
            for n, fn in saved.items():
                setattr(EP, n, fn)
        if used[0] and unmodelled:
            return {"ok": {"skip": True}}
        return res


only = os.environ.get("TEXTLIBS_ONLY")
names = [n for n in AREAS if not only or n in only.split(",")]
weights = [AREAS[n][1] for n in names]


def gen_case(rng):
    cls = AREAS[rng.choices(names, weights)[0]][0]
    return cls.gen(rng)


def run_python(case):
    return AREAS[case["fn"].split(".", 1)[0]][0].run(case)


if __name__ == "__main__":
    common.main(gen_case, run_python)
