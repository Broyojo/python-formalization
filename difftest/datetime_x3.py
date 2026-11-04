"""Cases for the datetime models added after review 0506b7c0 (`"fn": "x3_..."`), used by
datetime_diff.py: timedelta(...) on int and float arguments, astimezone and _local_timezone
with the fixed local zone of the process (TZ=XXX-2), repr with a tzinfo whose __repr__
raises or returns a non-str, and time/datetime from a str pickle state."""

import math
import struct

import common

X3_FNS = ["x3_td", "x3_td", "x3_td", "x3_astz", "x3_astz", "x3_localtz", "x3_repr", "x3_new_str"]
TD_NAMES = ["days", "seconds", "microseconds", "milliseconds", "minutes", "hours", "weeks"]
EDGE_FLOATS = [0.0, -0.0, 0.5, -0.5, 1.5, 2.5, -2.5, 0.1, 1 / 3, 1e-7, 5e-7, 4.9999999e-7, 1e9, 1e15, 1e16,
               1e17, 1e300, 5e-324, 86399.9999995, 0.0000005, 1.0000005, 999999.5, 12345678.9, 100000.1,
               10000000.1, 2.0 ** 53, 2.0 ** 63, 1e10 + 0.5, float("inf"), float("-inf"), float("nan")]


def float_bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def rand_float(rng):
    k = rng.random()
    if k < 0.25:
        x = rng.choice(EDGE_FLOATS)
        return -x if rng.random() < 0.3 else x
    if k < 0.35:
        return struct.unpack("<d", struct.pack("<Q", rng.getrandbits(64)))[0]
    if k < 0.75:
        return rng.uniform(-1, 1) * 10 ** rng.randint(-9, 13)
    return (rng.randint(-10**7, 10**7) + rng.choice([0.5, 0.25, 0.75, 0.4999999999, 0.5000000001])) * \
        10 ** rng.randint(-7, 3)


def td_arg(rng):
    k = rng.random()
    if k < 0.6:
        return ["f", float_bits(rand_float(rng))]
    if k < 0.93:
        return ["i", rng.choice([0, 1, -1, 7, 86399, 86400, 10**6, -10**6, 999999999, 2**63, 10**30, 10**400,
                                 rng.randint(-10**9, 10**9)])]
    return ["o", rng.choice(["str", "complex"])]


def gen_x3(rng, d):
    fn = rng.choice(X3_FNS)
    c = {"mod": "datetime", "fn": fn, "impl": rng.choice(["py", "c"])}
    if fn == "x3_td":
        n = rng.randint(1, 3)
        given = set(rng.sample(range(7), n))
        c["args"] = [td_arg(rng) if i in given else None for i in range(7)]
    elif fn in ("x3_astz", "x3_localtz"):
        v = [rng.randint(1901, 2099), rng.randint(1, 12), rng.randint(1, 28)] + d.rand_time(rng) + \
            [rng.choice([0, 0, 1]), d.rand_tz_spec(rng, 1)]
        c["a"] = v
        if fn == "x3_localtz":
            c["impl"] = "py"
        else:
            k = rng.random()
            c["tz"] = None if k < 0.5 else "other" if k < 0.55 else \
                (v[-1] if (k < 0.6 and v[-1] is not None) else d.rand_tz_spec(rng, 2) or ["tz", 0, [0, 0, 0], None])
    elif fn == "x3_repr":
        kind = rng.choice(["tm", "dt"])
        spec = rng.choice([None, ["tz", 0, [0, 0, 0], None], ["tz", 1, rng.choice(d.OFFSETS), rng.choice(d.NAMES)],
                           ["cu", 1, 0], ["cu", 1, 1], ["cu", 1, 2], ["cu", 1, 3]])
        if kind == "tm":
            a = d.rand_time(rng) + [rng.choice([0, 1]), spec]
        else:
            a = d.rand_date(rng) + d.rand_time(rng) + [rng.choice([0, 1]), spec]
        c.update(kind=kind, a=a, cls=rng.choice([0, 1, 2]))
    else:
        kind = rng.choice(["tm", "dt"])
        n = 6 if kind == "tm" else 10
        if rng.random() < 0.15:
            n = rng.choice([0, 1, 5, 7, 9, 11])
        cs = [rng.randrange(256) for _ in range(n)]
        if kind == "tm" and n and rng.random() < 0.8:
            cs[0] = rng.choice([rng.randrange(24), 128 + rng.randrange(24)])
        if kind == "dt" and n > 2 and rng.random() < 0.8:
            cs[2] = rng.choice([1 + rng.randrange(12), 129 + rng.randrange(12)])
        if n and rng.random() < 0.15:
            cs[rng.randrange(n)] = rng.choice([256, 0x20ac, 0x1f600, 0x100])
        c.update(kind=kind, s=cs, tz=rng.choice([None, None, ["tz", 0, [0, 0, 0], None], ["tz", 1, rng.choice(d.OFFSETS), "X"],
                                                 ["cu", 1, 2]]))
    return c


def gen_strp_z(rng, c, compile_fmt):
    """A `%z` parse with an offset of up to 99 hours, which the regex accepts and `_parse_tz`
    may refuse (strp_time / strp_dt cases)."""
    fmt = rng.choice(["%z", "%H:%M %z", "%Y %z", "%:z", "%z %Y"])
    hh, mm = rng.choice([rng.randint(0, 99), 23, 24, 25, 99, 0]), rng.randint(0, 59)
    off = rng.choice("+-") + "%02d" % hh + (":" if fmt == "%:z" or rng.random() < 0.3 else "") + "%02d" % mm
    if rng.random() < 0.2:
        off += (":" if ":" in off else "") + "%02d" % rng.randint(0, 59)
    if rng.random() < 0.05:
        off = "Z"
    data = fmt.replace("%H:%M", "12:30").replace("%Y", "2020").replace("%:z", off).replace("%z", off)
    try:
        rx = compile_fmt(fmt)
    except Exception:
        return None
    found = rx.fullmatch(data)
    if not found:
        return None
    c.update(fn=rng.choice(["strp_time", "strp_dt"]), format=fmt, data=data,
             found=[[k, v] for k, v in found.groupdict().items()])
    return c


def iso_midnight(rng):
    """`YYYY-MM-DDT24:00` on dates valid or not, for the rollover guard."""
    y = rng.choice([1, 2020, 2021, 2000, 1900, 9999, rng.randint(1, 9999), 0])
    mo = rng.choice([1, 2, 12, 13, 0, rng.randint(1, 12)])
    dd = rng.choice([0, 1, 28, 29, 30, 31, 32, rng.randint(1, 31)])
    return "%04d-%02d-%02dT24:00%s" % (y, mo, dd, rng.choice(["", ":00", ":00.000000", "+01:00", "Z", ":01"]))


def make_repr_tz(m):
    class SS(str):
        pass

    class R(m.tzinfo):
        def __init__(self, mode):
            self.mode = mode

        def __repr__(self):
            if self.mode == 0:
                return "R()"
            if self.mode == 1:
                raise KeyError("boom")
            if self.mode == 2:
                return 5
            return SS("S")
    return R


def run_x3(c, d):
    fn, impl = c["fn"], c["impl"]
    m = d.IMPL[impl]
    pool = {}
    T = lambda s: d.build_tz(impl, s, pool)

    def desc(t):
        if t is None:
            return None
        if isinstance(t, m.timezone):
            a = t.__getinitargs__()
            return ["tz", d.common_us(a[0]), a[1] if len(a) == 2 else None]
        return ["cu", next(k for k, x in pool.items() if x is t)]

    def encdt(v):
        return [v.year, v.month, v.day, v.hour, v.minute, v.second, v.microsecond, v.fold, desc(v.tzinfo)]

    def thunk():
        if fn == "x3_td":
            kw = {}
            for name, a in zip(TD_NAMES, c["args"]):
                if a is None:
                    continue
                if a[0] == "i":
                    kw[name] = a[1]
                elif a[0] == "f":
                    kw[name] = struct.unpack("<d", struct.pack("<Q", a[1]))[0]
                else:
                    kw[name] = "x" if a[1] == "str" else 1j
            t = m.timedelta(**kw)
            return [t.days, t.seconds, t.microseconds]
        if fn in ("x3_astz", "x3_localtz"):
            v = c["a"]
            x = m.datetime(*v[:7], tzinfo=T(v[8]), fold=v[7])
            if fn == "x3_localtz":
                return desc(x._local_timezone())
            tz = c["tz"]
            arg = None if tz is None else 5 if tz == "other" else T(tz)
            return encdt(x.astimezone(arg))
        if fn == "x3_repr":
            R = make_repr_tz(m)
            v = c["a"]
            spec = v[-1]
            tz = None if spec is None else R(spec[2]) if spec[0] == "cu" else T(spec)
            base = m.time if c["kind"] == "tm" else m.datetime
            cls = base
            k = c["cls"]
            if k:
                name = "TSub" if base is m.time else "DTSub"
                cls = type(name, (base,), {"__module__": "__main__"})
                cls.__qualname__ = ("Outer." + name) if k == 2 else name
            if base is m.time:
                x = cls(*v[:4], tzinfo=tz, fold=v[4])
            else:
                x = cls(*v[:7], tzinfo=tz, fold=v[7])
            return repr(x)
        if fn == "x3_new_str":
            s = "".join(map(chr, c["s"]))
            cls = m.time if c["kind"] == "tm" else m.datetime
            x = cls(s) if c["tz"] is None else cls(s, T(c["tz"]))
            oid = lambda t: None if t is None else 0 if t is m.timezone.utc else next(k for k, y in pool.items() if y is t)
            if c["kind"] == "tm":
                return [x.hour, x.minute, x.second, x.microsecond, x.fold, oid(x.tzinfo)]
            return [x.year, x.month, x.day, x.hour, x.minute, x.second, x.microsecond, x.fold, oid(x.tzinfo)]
        raise AssertionError(fn)

    return common.py_result(thunk)
