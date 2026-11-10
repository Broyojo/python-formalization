"""Cases for the datetime models added after review 50b4b958 (`"fn": "x2_..."`), used by
datetime_diff.py: tzinfo.__reduce__, isoformat(sep), replace/combine on any argument, the
timezone argument checks, __getinitargs__, pickling round trips, repr with the class,
IsoCalendarDate, fromisoformat/__format__/astimezone argument checks, and _mktime over the
fixed local zone of the process."""

import struct

import _datetime
import _pydatetime

import common

X2_FNS = ["x2_reduce", "x2_iso_sep", "x2_tm_replace", "x2_dt_replace", "x2_combine", "x2_tz_meth", "x2_tz_new_arg",
          "x2_tz_initargs", "x2_tm_reduce", "x2_dt_reduce", "x2_tm_repr_cls", "x2_dt_repr_cls", "x2_isocal",
          "x2_fromiso_arg", "x2_tm_format", "x2_astz_arg", "x2_mktime"]


def gen_x2(rng, d):
    """`d` is the datetime_diff module (generators and constants)."""
    def repl():
        k = rng.random()
        if k < 0.45:
            return "omit"
        if k < 0.55:
            return None
        if k < 0.85:
            return ["i", d.small_field(rng) or 0]
        return d.rand_arg(rng, 6)

    def tzp():
        k = rng.random()
        if k < 0.4:
            return "O"
        if k < 0.55:
            return "T"
        if k < 0.65:
            return None
        if k < 0.9:
            return ["tz", d.rand_tz_spec(rng, 2)]
        return ["o"]

    fn = rng.choice(X2_FNS)
    c = {"mod": "datetime", "fn": fn, "impl": rng.choice(["py", "c"])}
    if fn == "x2_reduce":
        c["kind"] = rng.choice(["absent", "none", "zero", "method", "falsy", "raises", "boolraises"])
    elif fn == "x2_iso_sep":
        k = rng.random()
        sep = (["s", [rng.choice([84, 32, 120, 0x20ac, 0x1f600, 0])]] if k < 0.35 else
               ["s", [rng.randrange(128) for _ in range(rng.choice([0, 2, 3]))]] if k < 0.45 else
               ["i", rng.choice([65, 0, 32, 0x10ffff, 0x110000, -1, 2**63, 2**64, 84, 1])] if k < 0.75 else
               d.rand_index_arg(rng) if k < 0.85 else rng.choice([None, ["o"], ["b", [65]]]))
        c.update(a=d.rand_dt(rng), sep=sep)
    elif fn in ("x2_tm_replace", "x2_dt_replace"):
        c.update(a=d.rand_tm(rng) if fn == "x2_tm_replace" else d.rand_dt(rng), tzp=tzp())
        keys = ("nh", "nmi", "ns", "nus", "nfold") if fn == "x2_tm_replace" else \
            ("ny", "nm", "nd", "nh", "nmi", "ns", "nus", "nfold")
        for key in keys:
            v = repl()
            if v != "omit":
                c[key] = v
    elif fn == "x2_combine":
        k = rng.random()
        dd = ["d", d.rand_date(rng)] if k < 0.6 else ["dt", d.rand_dt(rng, 3)] if k < 0.85 else ["o"]
        t = ["t", d.rand_tm(rng, 1)] if rng.random() < 0.85 else ["o"]
        c.update(d=dd, t=t, tzp=tzp())
    elif fn == "x2_tz_meth":
        spec = ["tz", 1, rng.choice(d.OFFSETS + [[0, 0, 0]]), rng.choice(d.NAMES)]
        if spec[2] == [0, 0, 0] and spec[3] is None:
            # timezone(timedelta(0)) is timezone.utc itself (identity 0)
            spec = ["tz", 0, [0, 0, 0], None]
        if rng.random() < 0.2:
            spec = ["tz", 0, [0, 0, 0], None]
        k = rng.random()
        if k < 0.5:
            v = d.rand_dt(rng, 2)
            if rng.random() < 0.6:
                v[-1] = spec
            arg = ["dt", v]
        elif k < 0.75:
            arg = ["none"]
        else:
            arg = ["other", rng.choice(["date", "int", "time"])]
        c.update(tz=spec, arg=arg, meth=rng.choice(["utcoffset", "dst", "tzname", "fromutc"]))
    elif fn == "x2_tz_new_arg":
        c["td"] = None if rng.random() < 0.3 else rng.choice(d.OFFSETS + [[0, 0, 0], [1, 0, 0], [-1, 0, 0]])
        if c["td"] is not None and rng.random() < 0.6:
            # an instance of a timedelta subclass: __bool__, __ge__, __le__ are inherited ("inh"),
            # return True ("t") or False ("f"), or raise ("r")
            c["sub"] = [rng.choice(["inh", "inh", "t", "f", "r"]) for _ in range(3)]
        k = rng.random()
        if k < 0.4:
            c["name"] = rng.choice(["X", "", "UTC"])
        elif k < 0.6:
            c["name"] = 5
    elif fn == "x2_tz_initargs":
        c["tz"] = rng.choice([["tz", 0, [0, 0, 0], None], ["tz", 1, rng.choice(d.OFFSETS), rng.choice(d.NAMES)],
                              ["tz", 1, [0, 0, 0], rng.choice(["UTC", "X"])]])
    elif fn in ("x2_tm_reduce", "x2_dt_reduce"):
        c["a"] = d.rand_tm(rng) if fn == "x2_tm_reduce" else d.rand_dt(rng)
        p = rng.choice([None, 0, 1, 2, 3, 4, 5])
        if p is not None:
            c["proto"] = p
    elif fn in ("x2_tm_repr_cls", "x2_dt_repr_cls"):
        c.update(a=d.rand_tm(rng) if fn == "x2_tm_repr_cls" else d.rand_dt(rng), cls=rng.choice([0, 1, 2]))
    elif fn == "x2_isocal":
        c["args"] = [["i", rng.choice([2020, 1, -5, 0, 53, 99, 2**31 - 1, 2**31, -2**31 - 1])] if rng.random() < 0.7
                     else d.rand_arg(rng, 3) for _ in range(3)]
    elif fn == "x2_fromiso_arg":
        cls = rng.choice(["time", "datetime"])
        # a surrogate in a datetime string is out of the model's scope (where it sits matters)
        c.update(cls=cls, arg=rng.choice("bnu" if cls == "time" else "bn"), s=[ord(ch) for ch in d.iso_string(rng)])
    elif fn == "x2_tm_format":
        c.update(a=d.rand_tm(rng), f=rng.choice([None, [], [37, 72], [120]]))
    elif fn == "x2_astz_arg":
        c.update(a=d.rand_dt(rng), o=rng.choice([1.5, 5, "x"]))
    else:
        y = rng.randint(1901, 2099)
        v = [y, rng.randint(1, 12), rng.randint(1, 28)] + d.rand_time(rng)[:3] + [0, rng.choice([0, 1]), None]
        c.update(a=v, off=d.LOCAL_OFF)
    return c


def run_x2(c, d):
    fn, impl = c["fn"], c["impl"]
    m = d.IMPL[impl]
    pool = {}
    T = lambda s: d.build_tz(impl, s, pool)
    mkdt = lambda v, cls=None: (cls or m.datetime)(*v[:7], tzinfo=T(v[8]), fold=v[7])
    mktm = lambda v, cls=None: (cls or m.time)(*v[:4], tzinfo=T(v[5]), fold=v[4])
    oid = lambda t: None if t is None else 0 if t is m.timezone.utc else next(k for k, x in pool.items() if x is t)
    encdt = lambda v: [v.year, v.month, v.day, v.hour, v.minute, v.second, v.microsecond, v.fold, oid(v.tzinfo)]
    enctm = lambda v: [v.hour, v.minute, v.second, v.microsecond, v.fold, oid(v.tzinfo)]

    def arg(a):
        if a is None:
            return None
        if a[0] == "i":
            return a[1]
        if a[0] == "b":
            return bytes(a[1])
        if a[0] == "s":
            return "".join(map(chr, a[1]))
        if a[0] == "tz":
            return T(a[1])
        if a[0] == "x":
            return d.Idx(a[1])
        if a[0] == "f":
            return struct.unpack("<d", struct.pack("<Q", a[1]))[0]
        return 1.5

    def tzp(k):
        v = c["tzp"]
        if v == "O":
            return
        k["tzinfo"] = True if v == "T" else arg(v)

    def thunk():
        if fn == "x2_reduce":
            kind = c["kind"]

            class R(m.tzinfo):
                pass
            if kind == "none":
                R.__getinitargs__ = None
            elif kind == "zero":
                R.__getinitargs__ = 0
            elif kind == "method":
                R.__getinitargs__ = lambda self: [5]
            elif kind in ("falsy", "boolraises"):
                class F:
                    def __call__(self):
                        return [5]

                    def __bool__(self):
                        if kind == "boolraises":
                            raise ValueError("bool")
                        return False
                R.__getinitargs__ = F()
            elif kind == "raises":
                def g(self):
                    raise ValueError("gi")
                R.__getinitargs__ = g
            return list(R().__reduce__()[1])
        if fn == "x2_iso_sep":
            return [ord(ch) for ch in mkdt(c["a"]).isoformat(sep=arg(c["sep"]))]
        if fn in ("x2_tm_replace", "x2_dt_replace"):
            names = ([("ny", "year"), ("nm", "month"), ("nd", "day")] if fn == "x2_dt_replace" else []) + \
                [("nh", "hour"), ("nmi", "minute"), ("ns", "second"), ("nus", "microsecond"), ("nfold", "fold")]
            k = {py: arg(c[key]) for key, py in names if key in c}
            tzp(k)
            if fn == "x2_tm_replace":
                return enctm(mktm(c["a"]).replace(**k))
            return encdt(mkdt(c["a"]).replace(**k))
        if fn == "x2_combine":
            dd = c["d"]
            date = m.date(*dd[1]) if dd[0] == "d" else mkdt(dd[1]) if dd[0] == "dt" else 5
            t = mktm(c["t"][1]) if c["t"][0] == "t" else m.datetime(2020, 1, 1)
            k = {}
            tzp(k)
            return encdt(m.datetime.combine(date, t, **k))
        if fn == "x2_tz_meth":
            tz = T(c["tz"])
            a = c["arg"]
            x = (mkdt(a[1]) if a[0] == "dt" else None if a[0] == "none" else
                 {"date": m.date(2020, 1, 1), "int": 5, "time": m.time(1)}[a[1]])
            meth = c["meth"]
            r = getattr(tz, meth)(x)
            if meth in ("utcoffset", "dst"):
                return None if r is None else [r.days, r.seconds, r.microseconds]
            if meth == "fromutc":
                return encdt(r)
            return r
        if fn == "x2_tz_new_arg":
            if c["td"] is None:
                off = 5
            elif "sub" in c:
                def override(tag, kind):
                    def f(self, *args):
                        if kind == "r":
                            raise RuntimeError(tag)
                        return kind == "t"
                    return f
                ns = {dunder: override(tag, kind)
                      for tag, dunder, kind in zip(("bool", "ge", "le"), ("__bool__", "__ge__", "__le__"), c["sub"])
                      if kind != "inh"}
                off = type("Sub", (m.timedelta,), ns)(*c["td"])
            else:
                off = m.timedelta(*c["td"])
            t = m.timezone(off, c["name"]) if "name" in c else m.timezone(off)
            if t is m.timezone.utc:
                return [0, [0, 0, 0], None]
            o = t.utcoffset(None)
            r = repr(t)
            return [1, [o.days, o.seconds, o.microseconds], t.tzname(None) if r.endswith("')") or r.endswith('")') else None]
        if fn == "x2_tz_initargs":
            tz = T(c["tz"])
            a = tz.__getinitargs__()
            enc = [[a[0].days, a[0].seconds, a[0].microseconds]] + list(a[1:])
            rt = m.timezone(*a)
            same = rt == tz and rt.tzname(None) == tz.tzname(None) and repr(rt) == repr(tz)
            return [enc, hash(tz) == hash(tz.utcoffset(None)), same]
        if fn in ("x2_tm_reduce", "x2_dt_reduce"):
            x = mktm(c["a"]) if fn == "x2_tm_reduce" else mkdt(c["a"])
            r = x.__reduce__() if "proto" not in c else x.__reduce_ex__(c["proto"])
            st = r[1]
            enc = [list(st[0]), oid(st[1]) if len(st) == 2 else None]
            back = common.py_result(lambda: (enctm if fn == "x2_tm_reduce" else encdt)(r[0](*st)))
            return [enc, back]
        if fn in ("x2_tm_repr_cls", "x2_dt_repr_cls"):
            base = m.time if fn == "x2_tm_repr_cls" else m.datetime
            k = c["cls"]
            cls = base
            if k:
                name = "TSub" if base is m.time else "DTSub"
                cls = type(name, (base,), {"__module__": "__main__"})
                cls.__qualname__ = ("Outer." + name) if k == 2 else name
            return repr(mktm(c["a"], cls) if base is m.time else mkdt(c["a"], cls))
        if fn == "x2_isocal":
            ICD = type(m.date(2020, 1, 1).isocalendar())
            r = ICD(*map(arg, c["args"]))
            return [["i", v] if type(v) is int else ["x"] for v in r]
        if fn == "x2_fromiso_arg":
            s = "".join(map(chr, c["s"]))
            a = {"b": s.encode("utf-8", "surrogatepass"), "n": None, "u": s + "\ud800"}[c["arg"]]
            (m.time if c["cls"] == "time" else m.datetime).fromisoformat(a)
            return None
        if fn == "x2_tm_format":
            class TS(m.time):
                def strftime(self, f):
                    return "S"
            v = c["a"]
            t = TS(*v[:4], tzinfo=T(v[5]), fold=v[4])
            return t.__format__(1 if c["f"] is None else "".join(map(chr, c["f"])))
        if fn == "x2_astz_arg":
            mkdt(c["a"]).astimezone(c["o"])
            return None
        if fn == "x2_mktime":
            v = c["a"]
            if impl == "py":
                return _pydatetime.datetime(*v[:6], fold=v[7])._mktime()
            return int(_datetime.datetime(*v[:6], fold=v[7]).timestamp())
        raise AssertionError(fn)

    return common.py_result(thunk)
