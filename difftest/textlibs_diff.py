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
                       "unpack_from", "iter_unpack", "pack_into"])
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
        if fn in ("unpack", "unpack_from", "iter_unpack", "pack_into"):
            c["buf"] = cls.buf_for(r, fmt)
        if fn in ("unpack_from", "pack_into"):
            n = len(c["buf"])
            c["off"] = r.choice([0, 0, 1, 2, -1, -2, n, -n, n + 1, -n - 1, n // 2, M, -M, -M - 1, M + 1,
                                 -M - 2, 2**70])
        return c

    @classmethod
    def run(cls, c):
        fn = c["fn"][len("struct."):]
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
                fm = s.format
                r = repr(s)
                if "'" in fm or "\\" in fm or any(ord(ch) < 32 for ch in fm):
                    r = "Struct('" + fm + "')"
                return {"size": s.size, "len": len(s.unpack(bytes(s.size))) if s.size < 4096 else
                        _item_count(s), "sizeof": s.__sizeof__(), "repr": r}
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
            if fn == "pack_into":
                b = bytearray(c["buf"])
                struct.pack_into(f, b, c["off"], *pack_args())
                return list(b)
            raise KeyError(fn)

        return common.py_result(body)


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

import base64
import binascii


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
        fn = r.choice(["a2b_base64", "a2b_base64", "a2b_base64", "b2a_base64", "a2b_hex", "b2a_hex"])
        c = {"mod": "textlibs", "fn": "binascii." + fn}
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
    def run(cls, c):
        fn = c["fn"].split(".")[1]

        def body():
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
                       "b32hexdecode", "b16encode", "b16decode", "b16decode"])
        c = {"mod": "textlibs", "fn": "base64." + fn}
        raw = bytes(d)
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
            f = getattr(base64, fn)
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
