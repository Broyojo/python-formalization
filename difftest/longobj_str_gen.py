"""Case generator for the int/str conversions of Objects/longobject.c and Lib/_pylong.py."""

import ctypes
import _pylong
import sys

from common import py_result

MOD = "longobj"
LIMITS = [0, 0, 640, 641, 1000, 4300, 4300, 4300, 6000, 8999, 9000, 9001, 9030, 9100,
          10000, 20000, 100000]
UNI_DIGITS = [0x660, 0x6f0, 0x966, 0xff10, 0x104a0, 0x1d7ce, 0x1fbf0, 0x11de0]  # 0x11de0 is new in Unicode 17
SPACES_C = [9, 10, 11, 12, 13, 32]
SPACES_U = [0x1c, 0x1d, 0x1e, 0x1f, 0x85, 0xa0, 0x1680, 0x2000, 0x2028, 0x2029, 0x202f, 0x3000]
JUNK = [0, 0, 63, 95, 95, 43, 45, 46, 120, 88, 98, 111, 127, 128, 255, 0xe9, 0x2212, 0xd800]
DIGIT_CHARS = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"


def hx(i):
    return hex(i)


def rand_int(rng):
    k = rng.random()
    if k < 0.15:
        return rng.choice([0, 1, -1, 2, 9, 10, 99, 100, 10**9 - 1, 10**9, 10**9 + 1, 2**30 - 1,
                           2**30, 2**30 + 1, 2**31, 2**60 - 1, 2**60, 2**63 - 1, 2**63, 2**64 - 1,
                           2**64, sys.maxsize, -2**63, -2**64, 10**18, 10**19, 10**27])
    if k < 0.35:
        return rng.getrandbits(rng.randrange(1, 200)) * rng.choice([1, -1])
    if k < 0.5:
        e = rng.choice([1, 8, 9, 10, 17, 18, 19, 27, 100, 639, 640, 641, 642, 4299, 4300, 4301])
        return (10 ** e + rng.randrange(-2, 3)) * rng.choice([1, -1])
    if k < 0.7:
        bits = rng.choice([30, 60, 90, 720, 2100, 2160, 2190, 2220, 2400, 2430, 14280, 14340,
                           14400, 14430, 14460])
        return ((1 << bits) + rng.randrange(-2, 3)) * rng.choice([1, -1])
    if k < 0.85:
        return rng.getrandbits(rng.randrange(1, 15000)) * rng.choice([1, -1])
    # Around the `_pylong` switch (size_a > 1000).
    if k < 0.97:
        s = rng.choice([999, 1000, 1001, 1002, 1020, 1100, 2000])
        e = rng.choice([-2, -1, 0, 1, 2])
        if rng.random() < 0.5:
            return ((1 << (30 * s)) + e) * rng.choice([1, -1])
        return (rng.getrandbits(30 * s - rng.randrange(0, 29)) | 1) * rng.choice([1, -1])
    if k < 0.995:
        e = rng.choice([8999, 9000, 9001, 9030, 9031, 9100, 10000, 20000, 30000, 100000])
        return (10 ** e + rng.randrange(-1, 2)) * rng.choice([1, -1])
    # Past the `_decimal` switch (bit_length > 450000).
    return ((1 << rng.choice([450000, 450001, 460000])) + rng.randrange(-1, 2)) * rng.choice([1, -1])


def rand_digits(rng, base, n):
    ds = DIGIT_CHARS[:min(base, 36)]
    return "".join(rng.choice(ds) for _ in range(n))


def digit_len(rng):
    k = rng.random()
    if k < 0.75:
        return rng.randrange(0, 45)
    if k < 0.85:
        return rng.choice([638, 639, 640, 641, 642, 999, 1000, 1001])
    if k < 0.97:
        return rng.choice([4299, 4300, 4301, 5000, 5999, 6000, 6001, 6002, 8999, 9000, 9001])
    return rng.choice([2047, 2048, 2049, 4096, 4097, 8193, 10000, 12000, 20000])


def sprinkle(rng, s):
    """Insert underscores, mostly legally."""
    k = rng.random()
    if k < 0.6 or not s:
        return s
    p = rng.choice([0.05, 0.2, 0.5])
    out = []
    for i, c in enumerate(s):
        out.append(c)
        if i + 1 < len(s) and rng.random() < p:
            out.append("_")
    r = "".join(out)
    if k > 0.9:
        i = rng.randrange(0, len(r) + 1)
        r = r[:i] + rng.choice(["_", "__", " ", "\0"]) + r[i:]
    return r


def to_unicode_digits(rng, s):
    if rng.random() < 0.9:
        return s
    z = rng.choice(UNI_DIGITS)
    return "".join(chr(z + ord(c) - 48) if "0" <= c <= "9" and rng.random() < 0.7 else c for c in s)


def rand_space(rng):
    k = rng.random()
    if k < 0.75:
        return ""
    pool = SPACES_C if k < 0.9 else SPACES_C + SPACES_U
    return "".join(chr(rng.choice(pool)) for _ in range(rng.randrange(1, 4)))


def rand_prefix(rng, base):
    k = rng.random()
    if k < 0.6:
        return ""
    return rng.choice(["0x", "0X", "0o", "0O", "0b", "0B", "0x_", "0b_", "0o_", "0_", "00", "0",
                       "0__", "x", "b", "o", "0 x"])


def rand_string(rng, base):
    b = base if base != 0 else rng.choice([2, 8, 10, 10, 16])
    body = rand_digits(rng, b, digit_len(rng))
    if rng.random() < 0.1:
        body = "0" * rng.randrange(1, 8) + body
    if rng.random() < 0.08:
        body = "0" * rng.choice([3, 640, 641, 4300, 4301, 6000, 6001, 7000])
    s = rand_prefix(rng, base) + sprinkle(rng, body)
    s = to_unicode_digits(rng, s)
    sign = rng.choice(["", "", "", "+", "-", "+-", "--", "- "])
    tail = ""
    if rng.random() < 0.05:
        tail = chr(rng.choice(JUNK)) + (rand_digits(rng, b, rng.randrange(0, 3)) if rng.random() < 0.5 else "")
    return rand_space(rng) + sign + s + rand_space(rng) + tail


def rand_base(rng):
    k = rng.random()
    if k < 0.4:
        return 10
    if k < 0.65:
        return 0
    if k < 0.85:
        return rng.choice([2, 4, 8, 16, 32])
    return rng.randrange(2, 37)


def int_case(rng, fn):
    base = rand_base(rng)
    s = rand_string(rng, base)
    lim = rng.choice(LIMITS)
    if fn != "intstr":
        s = "".join(c for c in s if ord(c) < 256 and not 0xd800 <= ord(c) < 0xe000)
    if fn == "intcstr":
        s = s.split("\0")[0]
        s = "".join(c for c in s if ord(c) < 128)
        if rng.random() < 0.1:
            base = rng.choice([-5, -1, 1, 37, 100])
    return {"mod": MOD, "fn": fn, "u": [ord(c) for c in s], "base": base, "lim": lim}


def digit_string(rng, n):
    return [48 + rng.randrange(0, 10) for _ in range(n)]


def bz_args(rng):
    """Arguments meeting the docstring of `_div2n1n`."""
    n = rng.choice([1, 2, 3, 30, 100, 3999, 4000, 4001, 4002, 4100, 8000, 8001, 9000, 16000, 16001,
                    32000, rng.randrange(1, 20000)])
    if rng.random() < 0.3:
        b = (1 << n) - 1 - rng.randrange(0, 3 if n > 2 else 1)
    elif rng.random() < 0.3:
        b = (1 << (n - 1)) + rng.randrange(0, 3 if n > 2 else 1)
    else:
        b = rng.getrandbits(n) | (1 << (n - 1))
    if rng.random() < 0.3:
        a = (b << n) - 1 - rng.randrange(0, 5)
    else:
        a = rng.getrandbits(2 * n) % (b << n)
    return max(a, 0), b, n


def gen_case(rng):
    k = rng.random()
    lim = rng.choice(LIMITS)
    if k < 0.22:
        return {"mod": MOD, "fn": "str", "v": hx(rand_int(rng)), "lim": lim}
    if k < 0.27:
        return {"mod": MOD, "fn": "fmtbin", "v": hx(rand_int(rng)), "base": rng.choice([2, 8, 16]),
                "alt": rng.random() < 0.5}
    if k < 0.31:
        return {"mod": MOD, "fn": "fmt", "v": hx(rand_int(rng)), "base": rng.choice([2, 8, 10, 16]),
                "lim": lim}
    if k < 0.37:
        return {"mod": MOD, "fn": "fmtw", "v": hx(rand_int(rng)), "base": rng.choice([2, 8, 10, 16]),
                "alt": rng.random() < 0.5, "lim": lim, "via": rng.choice(["format", "percent", "bytes"])}
    if k < 0.65:
        return int_case(rng, "intstr")
    if k < 0.73:
        return int_case(rng, "intbytes")
    if k < 0.79:
        return int_case(rng, "intcstr")
    if k < 0.83:
        w = rng.choice([0, 1, 2, 3, 7, 8, 9, 100, 1000, 1001, 2048, 2049, 4097, 65536,
                        rng.randrange(0, 3000), rng.randrange(0, 200000)])
        more = rng.choice([0, 1, 2, 10, 100, 1000, 2048])
        hi = rng.random() < 0.5
        if rng.random() < 0.3:
            return {"mod": MOD, "fn": "consumer", "w": w, "more": more, "hi": hi}
        b = rng.choice([2, 3, 5, 7])
        if w > 5000:
            b = rng.choice([2, 5])
        return {"mod": MOD, "fn": "cp", "w": w, "b": b, "more": more, "hi": hi}
    if k < 0.85:
        v = rand_int(rng)
        return {"mod": MOD, "fn": "itd", "v": hx(v)}
    if k < 0.875:
        v = rand_int(rng)
        return {"mod": MOD, "fn": "itds", "v": hx(v), "lim": lim}
    if k < 0.89:
        u = digit_string(rng, rng.choice([1, 10, 639, 2048, 2049, 4096, 4097, 5000, 8193, 12000]))
        return {"mod": MOD, "fn": rng.choice(["sti", "ifs"]), "u": u, "lim": 0}
    if k < 0.905:
        pool = [" ", "\t", "\xa0", "\x1c", "+", "-", "_", "0", "1", "9", "a", "\0", "٣"]
        s = "".join(rng.choice(pool) for _ in range(rng.randrange(0, 12)))
        return {"mod": MOD, "fn": rng.choice(["s2i", "ifs"]), "u": [ord(c) for c in s], "lim": rng.choice([0, 4300])}
    if k < 0.91:
        n = rng.choice([1, 100, 2000, 241000, 245000, 300000]) if rng.random() < 0.02 else rng.randrange(1, 3000)
        return {"mod": MOD, "fn": "dsi", "u": digit_string(rng, n), "lim": rng.choice([0, 0, 4300]), "guard": rng.choice([8, 8, 3, 1])}
    if k < 0.94:
        a, b, n = bz_args(rng)
        return {"mod": MOD, "fn": "div2", "a": hx(a), "b": hx(b), "n": n}
    if k < 0.95:
        a, b, n = bz_args(rng)
        n2 = n + (n & 1)
        a <<= n & 1
        b <<= n & 1
        half = n2 >> 1
        mask = (1 << half) - 1
        return {"mod": MOD, "fn": "div3", "a12": hx(a >> n2), "a3": hx((a >> half) & mask),
                "b": hx(b), "b1": hx(b >> half), "b2": hx(b & mask), "n": half}
    if k < 0.965:
        a = rng.getrandbits(rng.randrange(1, 3000)) if rng.random() < 0.9 else 0
        return {"mod": MOD, "fn": "i2d", "a": hx(a), "n": rng.randrange(1, 70)}
    if k < 0.98:
        n = rng.randrange(1, 70)
        ds = [rng.getrandbits(n) for _ in range(rng.randrange(0, 30))]
        return {"mod": MOD, "fn": "d2i", "digits": [hx(d) for d in ds], "n": n}
    a = rng.getrandbits(rng.choice([1, 100, 3000, 20000, 50000]))
    b = rng.getrandbits(rng.choice([1, 100, 3000, 10000])) | 1
    return {"mod": MOD, "fn": "dmp", "a": hx(a), "b": hx(b)}


def from_cstring(data, base):
    """`PyLong_FromString` through ctypes; returns the value and bytes consumed."""
    buf = ctypes.create_string_buffer(data)
    end = ctypes.c_void_p(0)
    fn = ctypes.PYFUNCTYPE(ctypes.py_object, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int)(
        ("PyLong_FromString", ctypes.pythonapi))
    start = ctypes.addressof(buf)
    try:
        r = {"ok": hx(fn(start, ctypes.addressof(end), base))}
    except Exception as e:
        r = {"exc": type(e).__name__, "msg": str(e)}
    return r, None if end.value is None else end.value - start


def consumer(w, limit, need_hi):
    """The body of `consumer`, _pylong.py:706-720 (dead code under `if 0`)."""
    seen = set()
    need = set()
    def inner(w):
        if w <= limit:
            return
        if w in seen:
            return
        seen.add(w)
        lo = w >> 1
        hi = w - lo
        need.add(hi if need_hi else lo)
        inner(lo)
        inner(hi)
    inner(w)
    return sorted(need)


def run_python(c):
    fn = c["fn"]
    sys.set_int_max_str_digits(c.get("lim", 0))
    v = int(c["v"], 16) if "v" in c else None
    if fn == "str":
        return py_result(lambda: str(v))
    if fn == "fmtbin":
        spec = {2: "b", 8: "o", 16: "x"}[c["base"]]
        if c["alt"]:
            return py_result(lambda: {2: bin, 8: oct, 16: hex}[c["base"]](v))
        return py_result(lambda: format(v, spec))
    if fn == "fmt":
        spec = {2: bin, 8: oct, 16: hex, 10: repr}[c["base"]]
        return py_result(lambda: spec(v))
    if fn == "fmtw":
        ch = {2: "b", 8: "o", 16: "x", 10: "d"}[c["base"]]
        alt = "#" if c["alt"] else ""
        via = c["via"]
        if via == "format" or (ch == "b"):
            return py_result(lambda: format(v, alt + ch))
        if via == "percent":
            return py_result(lambda: ("%" + alt + ch) % v)
        return py_result(lambda: (("%" + alt + ch).encode() % v).decode())
    if fn == "intstr":
        s = "".join(map(chr, c["u"]))
        return py_result(lambda: hx(int(s, c["base"])))
    if fn == "intbytes":
        s = bytes(c["u"])
        return py_result(lambda: hx(int(s, c["base"])))
    if fn == "intcstr":
        r, consumed = from_cstring(bytes(c["u"]), c["base"])
        return {"ok": [r, consumed]}
    if fn == "cp":
        d = _pylong.compute_powers(c["w"], c["b"], c["more"], need_hi=c["hi"])
        return {"ok": [[k, hx(d[k])] for k in sorted(d)]}
    if fn == "consumer":
        return {"ok": consumer(c["w"], c["more"], c["hi"])}
    if fn == "itd":
        sys.set_int_max_str_digits(0)
        return py_result(lambda: hx(int(_pylong.int_to_decimal(v))))
    if fn == "itds":
        return py_result(lambda: _pylong.int_to_decimal_string(v))
    if fn == "sti":
        s = "".join(map(chr, c["u"]))
        return py_result(lambda: hx(_pylong._str_to_int_inner(s)))
    if fn == "dsi":
        s = "".join(map(chr, c["u"]))
        return py_result(lambda: hx(_pylong._dec_str_to_int_inner(s, GUARD=c["guard"])))
    if fn == "ifs":
        s = "".join(map(chr, c["u"]))
        return py_result(lambda: hx(_pylong.int_from_string(s)))
    if fn == "s2i":
        s = "".join(map(chr, c["u"]))
        return py_result(lambda: hx(_pylong.str_to_int(s)))
    if fn == "div2":
        q, r = _pylong._div2n1n(int(c["a"], 16), int(c["b"], 16), c["n"])
        return {"ok": [hx(q), hx(r)]}
    if fn == "div3":
        q, r = _pylong._div3n2n(*(int(c[k], 16) for k in ("a12", "a3", "b", "b1", "b2")), c["n"])
        return {"ok": [hx(q), hx(r)]}
    if fn == "i2d":
        return {"ok": [hx(d) for d in _pylong._int2digits(int(c["a"], 16), c["n"])]}
    if fn == "d2i":
        return {"ok": hx(_pylong._digits2int([int(d, 16) for d in c["digits"]], c["n"]))}
    if fn == "dmp":
        q, r = _pylong._divmod_pos(int(c["a"], 16), int(c["b"], 16))
        return {"ok": [hx(q), hx(r)]}
    raise ValueError(fn)
