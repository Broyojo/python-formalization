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


def fmt_dec(f):
    if "s" in f:
        return "".join(map(chr, f["s"]))
    if "b" in f:
        return bytes(f["b"])
    return {"int": 3, "float": 1.5, "NoneType": None}.get(f["o"], [])


@area("struct", 6)
class StructArea:
    CODES = "xbBcspsphHiIlLnNqQ?efdFDP"
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
            s += r.choice(["3", "0", "9" * 20, "z", "\0", "<", "@", "3 i", "\x0b", "!", "1e"])
        elif roll < 0.06:
            s = r.choice(["9223372036854775807x", "9223372036854775808x", "9223372036854775807xb",
                          "b9223372036854775807h", "4611686018427387904h", "4611686018427387903h",
                          "2305843009213693952i", "b2305843009213693951i", "1152921504606846975q",
                          "9223372036854775807sb", "9223372036854775807s9223372036854775807s",
                          "9223372036854775807b9223372036854775807b", "9223372036854775807pp",
                          "9223372036854775808s", "1b9223372036854775806xh", "@b9223372036854775806xq",
                          "=9223372036854775807xh", "<9223372036854775806xh", "bh9223372036854775805x"])
        return {"s": [ord(c) for c in s]} if roll < 0.98 else {"b": [ord(c) for c in s]}

    @classmethod
    def value(cls, r, code):
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
        for num, c in re.findall(r"(\d*)([a-zA-Z?])", text):
            n = int(num) if num else 1
            if c == "x":
                continue
            if c in "sp":
                n = 1
            out.extend(cls.value(r, c) for _ in range(n))
        if r.random() < 0.05:
            out = out[:-1] if out and r.random() < 0.5 else out + [{"t": "i", "v": 0}]
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
    def gen(cls, r):
        fn = r.choice(["calcsize", "info", "pack", "pack", "pack", "Struct.pack", "unpack", "unpack",
                       "unpack_from", "iter_unpack", "iter_hint", "pack_into", "uninit"])
        fmt = cls.fmt(r)
        if r.random() < 0.01:
            fmt = r.choice([{"o": "int", "h": True}, {"o": "list", "h": False}, {"o": "float", "h": True},
                            {"o": "NoneType", "h": True}, {"s": [0xff]}, {"b": [0xff]}, {"s": [0x105, 0x69]}])
        try:
            if struct.calcsize(fmt_dec(fmt)) > 4096:  # would only test the allocator
                fn = r.choice(["calcsize", "info"])
        except Exception:
            pass
        c = {"mod": "textlibs", "fn": "struct." + fn, "fmt": fmt}
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
    def run(cls, c):
        fn = c["fn"][len("struct."):]
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
    for num, ch in re.findall(r"(\d*)([a-zA-Z?])", s.format.lstrip("@<>=!")):
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
    return bytes(d["b"]) if "b" in d else "".join(map(chr, d["s"]))


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


@area("binascii", 3)
class BinasciiArea(Codec):
    @classmethod
    def gen(cls, r):
        d = cls.raw(r)
        fn = r.choice(["a2b_base64", "a2b_base64", "a2b_base64", "b2a_base64", "a2b_hex", "b2a_hex",
                       "a2b_uu", "a2b_uu", "a2b_uu", "b2a_uu", "crc_hqx", "a2b_qp", "a2b_qp", "b2a_qp",
                       "b2a_qp", "b2a_qp", "qp_bound", "qp_bound"])
        c = {"mod": "textlibs", "fn": "binascii." + fn}
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
                return list(binascii.a2b_base64(data_dec(c["d"]), strict_mode=c["strict"]))
            if fn == "b2a_base64":
                return list(binascii.b2a_base64(bytes(c["d"]), newline=c["newline"]))
            if fn == "a2b_hex":
                return list(binascii.a2b_hex(data_dec(c["d"])))
            return list(binascii.b2a_hex(bytes(c["d"])))

        return common.py_result(body)


@area("base64", 3)
class Base64Area(Codec):
    @classmethod
    def gen(cls, r):
        d = cls.raw(r)
        fn = r.choice(["b64decode", "b64decode", "urlsafe_b64encode", "urlsafe_b64decode", "b32encode",
                       "b32hexencode", "b32decode", "b32decode", "b32decode", "b32hexdecode",
                       "b32hexdecode", "b16encode", "b16decode", "b16decode", "a85encode", "a85decode",
                       "a85decode", "b85encode", "b85decode", "b85decode", "z85encode", "z85decode", "z85decode",
                       "encodebytes", "decodebytes", "encode", "decode", "standard_b64encode",
                       "standard_b64decode", "input_check", "main_select"])
        c = {"mod": "textlibs", "fn": "base64." + fn}
        raw = bytes(d)
        if r.random() < 0.3:
            d = [r.choice([0, 0, 32, 32, 255]) for _ in range(r.choice([1, 2, 3, 4, 5, 7, 8, 9]))]
            raw = bytes(d)
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
            c.update(d=cls.wrap(r, b), foldspaces=fold, adobe=adobe,
                     ignore=r.choice([[32, 9, 10, 13, 11], [32, 9, 10, 13, 11], [], [122], [117, 10]]))
            return c
        if fn == "b85encode":
            c.update(d=d, pad=r.random() < 0.4)
            return c
        if fn == "b85decode":
            b = list(base64.b85encode(raw, pad=r.random() < 0.3))
            b = b if r.random() < 0.4 else cls.corrupt(r, b, b"~}|0Az ,.")
            if r.random() < 0.1:
                b = r.choice([[126] * 5, [124, 78, 115, 67, 48], [124, 78, 115, 67, 47], [48], [0]])
            c["d"] = cls.wrap(r, b)
            return c
        if fn == "z85decode":
            b = list(base64.z85encode(raw))
            c["d"] = cls.wrap(r, b if r.random() < 0.4 else cls.corrupt(r, b, b";_`|~#%0 "))
            return c
        if fn in ("encodebytes", "encode"):
            c["d"] = [r.randrange(256) for _ in range(r.choice([0, 1, 56, 57, 58, 113, 114, 115, 200]))]
            return c
        if fn in ("decodebytes", "decode"):
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
        elif fn == "urlsafe_b64decode":
            c["d"] = cls.wrap(r, cls.corrupt(r, base64.urlsafe_b64encode(raw), cls.B64 + b"-_"))
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
        elif fn == "b16decode":
            t = base64.b16encode(raw)
            if r.random() < 0.3:
                t = t.lower()
            c["casefold"] = r.random() < 0.5
            c["d"] = cls.wrap(r, t if r.random() < 0.3 else cls.corrupt(r, t, b"0123456789ABCDEFabcdef"))
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
            f = getattr(base64, fn)
            if fn == "a85encode":
                return list(f(bytes(c["d"]), foldspaces=c["foldspaces"], wrapcol=c["wrapcol"], pad=c["pad"],
                              adobe=c["adobe"]))
            if fn == "a85decode":
                return list(f(data_dec(c["d"]), foldspaces=c["foldspaces"], adobe=c["adobe"],
                              ignorechars=bytes(c["ignore"])))
            if fn == "b85encode":
                return list(f(bytes(c["d"]), pad=c["pad"]))
            if fn in ("b85decode", "z85decode", "standard_b64decode"):
                return list(f(data_dec(c["d"])))
            if fn == "decodebytes":
                return list(f(bytes(c["d"])))
            if fn in ("encode", "decode"):
                out = io.BytesIO()
                f(io.BytesIO(bytes(c["d"])), out)
                return list(out.getvalue())
            if fn == "b64decode":
                return list(f(data_dec(c["d"]), altchars=data_dec(c.get("alt")), validate=c["validate"]))
            if fn == "urlsafe_b64decode":
                return list(f(data_dec(c["d"])))
            if fn == "b32decode":
                return list(f(data_dec(c["d"]), casefold=c["casefold"], map01=data_dec(c.get("map01"))))
            if fn in ("b32hexdecode", "b16decode"):
                return list(f(data_dec(c["d"]), casefold=c["casefold"]))
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


def cps(t):
    return [ord(c) for c in t]


def txt(l):
    return "".join(map(chr, l))


class NotNum:
    def __init__(self, t):
        self.t = t

    def __str__(self):
        return self.t


def csv_obj(j):
    if j is None:
        return None
    if "s" in j:
        return txt(j["s"])
    if "i" in j:
        return j["i"]
    if "b" in j:
        return j["b"]
    return {"list": [], "float": 1.5, "bytes": b"x"}.get(j["o"], [])


def csv_kw(c):
    return {k: csv_obj(v) for k, v in c["args"].items()}


def csv_src(c):
    return () if c.get("src") is None else (txt(c["src"]),)


def enc_dialect(d):
    ch = lambda x: None if x is None else cps(x)
    return {"delimiter": ch(d.delimiter), "doublequote": bool(d.doublequote), "escapechar": ch(d.escapechar),
            "lineterminator": cps(d.lineterminator), "quotechar": ch(d.quotechar), "quoting": int(d.quoting),
            "skipinitialspace": bool(d.skipinitialspace), "strict": bool(d.strict)}


def enc_field(x):
    if x is None:
        return None
    if isinstance(x, str):
        return {"s": cps(x)}
    return {"f": float_bits(x)}


def norm_exc(e):
    m = str(e)
    if isinstance(e, ValueError) and m.startswith("could not convert"):
        m = "~could not convert string to float"
    return [type(e).__name__, m]


def csv_line(j):
    return txt(j["s"]) if "s" in j else 7


def wfield(j):
    if j is None:
        return None
    if "s" in j:
        return txt(j["s"])
    return (int(txt(j["t"])) if j["num"] else NotNum(txt(j["t"])))


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
                             "9007199254740993", "123456789012345678901234567890"])
        pool = cls.TEXT if numeric else cls.TEXT + "\xe9€"
        return "".join(r.choice(pool) for _ in range(r.choice([0, 0, 1, 1, 2, 3, 5, 8])))

    @classmethod
    def gen(cls, r):
        fn = r.choice(["dialect", "reader", "reader", "reader", "reader", "writerow", "writerow", "writerows",
                       "roundtrip", "roundtrip", "field_size_limit", "registry", "get_dialect", "dictreader",
                       "dictwriter", "writeheader", "extrasaction"])
        c = {"mod": "textlibs", "fn": "csv." + fn}
        if fn == "dialect":
            c["args"] = cls.args(r, False)
            c["src"] = r.choice([None, None, cps("excel"), cps("unix"), cps("excel-tab"), cps("nope")])
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
        elif fn in ("writerow", "writerows"):
            a = cls.valid_args(r) if r.random() < 0.9 else cls.args(r, False)
            c["args"], c["src"] = a, None

            def row():
                out = []
                for _ in range(r.choice([0, 1, 1, 2, 3, 4])):
                    roll = r.random()
                    if roll < 0.7:
                        out.append({"s": cps(cls.text(r, False))})
                    elif roll < 0.85:
                        out.append(None)
                    elif roll < 0.95:
                        out.append({"t": cps(str(r.choice([0, 1, -5, 123]))), "num": True})
                    else:
                        out.append({"t": cps(cls.text(r, False)), "num": False})
                return out

            if fn == "writerow":
                c["row"] = row()
            else:
                c["rows"] = [row() for _ in range(r.choice([0, 1, 2, 3]))]
        elif fn == "field_size_limit":
            c["cur"] = 131072
            c["new"] = r.choice([{"i": 5}, {"i": 0}, {"i": -1}, {"i": 2**70}, {"o": "float", "t": True}, {"b": True}, None])
            if c["new"] is None:
                del c["new"]
        elif fn == "registry":
            c["op"] = r.choice(["register", "unregister"])
            c["name"] = r.choice([cps("mine"), cps("excel"), cps("nope"), cps("unix")])
            c["args"] = cls.args(r, r.random() < 0.8)
        elif fn == "get_dialect":
            c["name"] = r.choice([cps("excel"), cps("excel-tab"), cps("unix"), cps("nope")])
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
        elif fn == "writeheader":
            c["names"] = r.choice([[cps("a"), cps("b")], [cps("x,y")], [], [cps("a"), cps("a")]])
        else:
            c["s"] = cps(r.choice(["raise", "RAISE", "ignore", "Ignore", "other", ""]))
        return c

    @classmethod
    def run(cls, c):
        fn = c["fn"].split(".")[1]

        def body():
            if fn == "dialect":
                return enc_dialect(csv.reader([], *csv_src(c), **csv_kw(c)).dialect)
            if fn == "reader":
                rd = csv.reader([csv_line(l) for l in c["lines"]], *csv_src(c), **csv_kw(c))
                old = csv.field_size_limit(c["limit"])
                rows, exc = [], None
                try:
                    for row in rd:
                        rows.append([enc_field(x) for x in row])
                except Exception as e:
                    exc = norm_exc(e)
                finally:
                    csv.field_size_limit(old)
                return {"rows": rows, "exc": exc, "n": rd.line_num}
            if fn == "writerow":
                buf = io.StringIO(newline="")
                csv.writer(buf, *csv_src(c), **csv_kw(c)).writerow([wfield(x) for x in c["row"]])
                return cps(buf.getvalue())
            if fn == "writerows":
                buf = io.StringIO(newline="")
                w = csv.writer(buf, *csv_src(c), **csv_kw(c))
                exc = None
                try:
                    w.writerows([[wfield(x) for x in row] for row in c["rows"]])
                except Exception as e:
                    exc = norm_exc(e)
                return {"text": cps(buf.getvalue()), "exc": exc}
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
                    if c["op"] == "register":
                        csv.register_dialect(txt(c["name"]), **csv_kw(c))
                    else:
                        csv.unregister_dialect(txt(c["name"]))
                    return [cps(n) for n in csv.list_dialects()]
                finally:
                    for n in list(csv.list_dialects()):
                        csv.unregister_dialect(n)
                    for n, d in saved.items():
                        csv.register_dialect(n, d)
            if fn == "get_dialect":
                return enc_dialect(csv.get_dialect(txt(c["name"])))
            if fn == "dictreader":
                names = None if c["names"] is None else [txt(n) for n in c["names"]]
                rk = None if c["restkey"] is None else txt(c["restkey"])
                sentinel = object()
                rd = csv.DictReader([txt(l["s"]) for l in c["lines"]], fieldnames=names, restkey=rk, restval=sentinel)
                rows, exc = [], None
                try:
                    for d in rd:
                        row = []
                        for k, v in d.items():
                            jk = None if k is None else cps(k)
                            if v is sentinel:
                                row.append([jk, {"restval": None}])
                            elif k == rk and isinstance(v, list):
                                row.append([jk, {"rest": [enc_field(x) for x in v]}])
                            else:
                                row.append([jk, enc_field(v)])
                        rows.append(row)
                except Exception as e:
                    exc = norm_exc(e)
                return {"rows": rows, "exc": exc}
            if fn == "dictwriter":
                buf = io.StringIO(newline="")
                w = csv.DictWriter(buf, [txt(n) for n in c["names"]], extrasaction="raise" if c["raises"] else "ignore")
                w.writerow({txt(k): wfield(v) for k, v in c["row"]})
                return cps(buf.getvalue())
            if fn == "writeheader":
                buf = io.StringIO(newline="")
                csv.DictWriter(buf, [txt(n) for n in c["names"]]).writeheader()
                return cps(buf.getvalue())
            csv.DictWriter(io.StringIO(), ["a"], extrasaction=txt(c["s"]))
            return txt(c["s"]).lower() == "raise"

        res = common.py_result(body)
        if "exc" in res and (res["msg"].startswith("dict contains fields") or res["msg"].startswith("extrasaction")):
            res["msg"] = {"d": "~dict contains fields not in fieldnames", "e": "~extrasaction must be 'raise' or 'ignore'"}[res["msg"][0]]
        return res


# ---- driver ----------------------------------------------------------------

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
