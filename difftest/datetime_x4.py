"""Cases for the datetime models added after review cbc4b092 (`"fn": "x4_..."`), used by
datetime_diff.py: the class and identity of C timedeltas (zero_delta, __reduce__),
microseconds_to_delta on what an int subclass's __mul__ returns (checked_divmod), the
dispatch of timedelta * and /, timezone(0, name) identity, str() through isoformat, replace()
on a subclass without a fold keyword, and date.fromtimestamp on ints, floats and others."""

import math
import struct

import common

X4_FNS = ["x4_tdobj", "x4_reduce", "x4_mulsub", "x4_mul", "x4_div", "x4_tzzero", "x4_str", "x4_replsub",
          "x4_fromts"]
BIG = [0, 1, -1, 2, 7, -7, 86399, 86400, 10**6, -10**6, 999999999, -999999999, 10**9, 2**31, 2**63, -2**63,
       10**20, -10**20]
FLOATS = [0.0, -0.0, 0.5, -0.5, 1.5, -1.5, 2.5, 0.1, 1e-7, 1e6, 1e9, 1.7e9 + 0.25, -1.7e9 - 0.75, 1e300,
          -1e300, 2.0 ** 63, -2.0 ** 63, float("inf"), float("-inf"), float("nan"), 5e-324]


def bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def small(rng):
    return rng.choice([0, 0, 1, -1, rng.randint(-10**6, 10**6), rng.randint(-10**12, 10**12), rng.choice(BIG)])


def rand_td(rng):
    return [rng.randint(-999999999, 999999999), rng.randrange(86400), rng.randrange(10**6)] if rng.random() < 0.7 \
        else rng.choice([[0, 0, 0], [999999999, 86399, 999999], [-999999999, 0, 0], [0, 0, 1], [-1, 86399, 999999]])


def operand(rng):
    k = rng.random()
    if k < 0.3:
        return ["td", rand_td(rng)]
    if k < 0.6:
        return ["i", rng.choice([0, 1, -1, 2, -3, 1000, 10**6, rng.randint(-10**9, 10**9), 2**40])]
    if k < 0.9:
        x = rng.choice(FLOATS) if rng.random() < 0.4 else rng.uniform(-10, 10) * 10 ** rng.randint(-6, 6)
        return ["f", bits(x)]
    return ["o"]


def gen_x4(rng, d):
    fn = rng.choice(X4_FNS)
    c = {"mod": "datetime", "fn": fn, "impl": rng.choice(["py", "c"])}
    if fn == "x4_tdobj":
        c.update(args=[small(rng) if rng.random() < 0.4 else 0 for _ in range(7)], sub=rng.random() < 0.4)
    elif fn == "x4_reduce":
        c.update(a=rand_td(rng), sub=rng.random() < 0.5)
    elif fn == "x4_mulsub":
        # what I.__mul__ returns: an int, a float, an object whose divmod is a non-tuple, a
        # 3-tuple, a pair out of range, a pair of ints, a pair whose remainder is a float
        kind = rng.choice(["int", "float", "nontuple", "tuple3", "range", "pair", "pairf"])
        c.update(a=rand_td(rng), kind=kind, n=rng.choice([0, 1, 2, -5, 10**6, rng.randint(-10**15, 10**15)]),
                 q=rng.choice([0, 1, -1, 10**9, 2**40]), r=rng.choice([0, 5, 999999, 10**6, -1, 2**31]))
        c["impl"] = "c" if rng.random() < 0.7 else "py"
    elif fn in ("x4_mul", "x4_div"):
        left, right = operand(rng), operand(rng)
        if left[0] != "td" and right[0] != "td":
            right = ["td", rand_td(rng)]
        if fn == "x4_div" and left[0] == "td" and right[0] == "td":
            right = ["i", rng.choice([1, 2, -7])]
        c.update(l=left, r=right)
    elif fn == "x4_tzzero":
        c.update(td=rng.choice([[0, 0, 0], [0, 3600, 0], [-1, 86399, 999999]]), name=rng.choice([None, "UTC", "", "X"]))
    elif fn == "x4_str":
        c.update(kind=rng.choice(["date", "time"]), override=rng.random() < 0.5, date=d.rand_date(rng),
                 time=d.rand_time(rng))
    elif fn == "x4_replsub":
        c.update(kind=rng.choice(["dt", "tm"]), date=d.rand_date(rng), time=d.rand_time(rng),
                 day=rng.choice([None, 1, 2, 28, 31, 0, 32]), fold=rng.choice([None, 0, 1]),
                 accepts=rng.random() < 0.3)
    else:
        k = rng.random()
        if k < 0.3:
            t = ["i", rng.choice([0, 1, -1, 86399, 10**9, -10**9, 253402214400, -62135510400, 2**63, -2**63 - 1,
                                  10**30, rng.randint(-62135510400, 253402214400)])]
        elif k < 0.85:
            x = rng.choice([0.0, -0.0, 0.5, -0.5, 1.5, -1.5, 86399.9, 1e9 + 0.5, -1e9 - 0.5, float("inf"),
                            float("-inf"), float("nan"), 1e300, 9.3e18, -9.3e18]) if rng.random() < 0.3 \
                else rng.uniform(-6.2e10, 2.5e11)
            t = ["f", bits(x)]
        else:
            t = ["s"]
        c.update(t=t)
    return c


def run_x4(c, d):
    fn, impl = c["fn"], c["impl"]
    m = d.IMPL[impl]

    def enc_td(t):
        return [t.days, t.seconds, t.microseconds]

    def dec(o):
        if o[0] == "td":
            return m.timedelta(*o[1])
        if o[0] == "i":
            return o[1]
        if o[0] == "f":
            return struct.unpack("<d", struct.pack("<Q", o[1]))[0]
        return object()

    def enc_res(v):
        if v is NotImplemented:
            return None
        if isinstance(v, m.timedelta):
            return ["td", enc_td(v)]
        if isinstance(v, float):
            return ["f", bits(v)]
        return ["?", repr(v)]

    def thunk():
        if fn == "x4_tdobj":
            class TD(m.timedelta):
                pass
            cls = TD if c["sub"] else m.timedelta
            a = c["args"]
            v = cls(days=a[0], seconds=a[1], microseconds=a[2], milliseconds=a[3], minutes=a[4], hours=a[5],
                    weeks=a[6])
            return [enc_td(v), v is m.timedelta(0), type(v) is TD]
        if fn == "x4_reduce":
            class TD(m.timedelta):
                pass
            cls = TD if c["sub"] else m.timedelta
            t = cls(*c["a"])
            k, args = t.__reduce__()
            back = k(*args)
            return [k is TD, list(args), enc_td(back), type(back) is TD, back is m.timedelta(0)]
        if fn == "x4_mulsub":
            kind, n, q, r = c["kind"], c["n"], c["q"], c["r"]

            class R:
                def __divmod__(self, o):
                    if kind == "nontuple":
                        return 5
                    if kind == "tuple3":
                        return (1, 2, 3)
                    if kind == "range":
                        return (q, 10**6 + abs(r))
                    if kind == "pairf":
                        return (q, 2.5)
                    return (q, abs(r) % 10**6)

            def mul(s, o):
                if kind == "int":
                    return int(s) * o
                if kind == "float":
                    return 2.5
                return R()

            I = type("I", (int,), {"__mul__": mul})
            return enc_td(m.timedelta(*c["a"]) * I(n))
        if fn in ("x4_mul", "x4_div"):
            a, b = dec(c["l"]), dec(c["r"])
            op = (lambda: a * b) if fn == "x4_mul" else (lambda: a / b)
            try:
                return enc_res(op())
            except TypeError as e:
                if "unsupported operand" in str(e):
                    return None
                raise
        if fn == "x4_tzzero":
            off = m.timedelta(*c["td"])
            tz = m.timezone(off) if c["name"] is None else m.timezone(off, c["name"])
            return [tz is m.timezone.utc, d.common_us(tz.utcoffset(None))]
        if fn == "x4_str":
            if c["kind"] == "date":
                ns = {"isoformat": lambda self: "X"} if c["override"] else {}
                D = type("D", (m.date,), ns)
                return str(D(*c["date"]))
            ns = {"isoformat": lambda self, timespec="auto": "X"} if c["override"] else {}
            T = type("T", (m.time,), ns)
            return str(T(*c["time"]))
        if fn == "x4_replsub":
            accepts = c["accepts"]
            base = m.datetime if c["kind"] == "dt" else m.time

            def new(cls, *a, **kw):
                if kw and not accepts:
                    raise TypeError("__new__() got an unexpected keyword argument 'fold'")
                return base.__new__(cls, *a, **kw)
            S = type("S", (base,), {"__new__": new})
            kw = {}
            if c["day"] is not None and c["kind"] == "dt":
                kw["day"] = c["day"]
            if c["fold"] is not None:
                kw["fold"] = c["fold"]
            if c["kind"] == "dt":
                v = S(*c["date"], *c["time"]).replace(**kw)
                return [v.year, v.month, v.day, v.hour, v.minute, v.second, v.microsecond, v.fold]
            v = S(*c["time"]).replace(**kw)
            return [v.hour, v.minute, v.second, v.microsecond, v.fold]
        if fn == "x4_fromts":
            t = c["t"]
            a = t[1] if t[0] == "i" else struct.unpack("<d", struct.pack("<Q", t[1]))[0] if t[0] == "f" else "x"
            v = m.date.fromtimestamp(a)
            return [v.year, v.month, v.day]
        raise AssertionError(fn)

    return common.py_result(thunk)
