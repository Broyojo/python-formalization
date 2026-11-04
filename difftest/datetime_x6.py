"""Cases for the models of the datetime twins follow-up (`"fn": "x6_..."`), used by datetime_diff.py:
parse_isoformat_date's non-W forms (through date.fromisoformat), strftime's %z/%:z/%Z replacements
with the inherited methods and with a subclass's utcoffset()/tzname() override, __reduce__ with a
subclass __reduce_ex__ override, date.fromtimestamp with its class, timedelta with integral floats,
time.fromisoformat at hour 24, and astimezone on a subclass whose __new__ may return a cached
instance."""

import struct

import common

X6_FNS = ["x6_isodate", "x6_strfz", "x6_strfz", "x6_reduce", "x6_fromts", "x6_fromts", "x6_td", "x6_iso24",
          "x6_astz", "x6_astz"]
OFFS = [0, 3600 * 10**6, -3600 * 10**6, 1, -1, 86399999999, -86399999999, 5 * 10**6, 19800 * 10**6,
        -19800 * 10**6, 60 * 10**6, 1800 * 10**6]
NAMES = [None, None, "EST", "", "Zone A", "€", "UTC"]
TS_FLOATS = [0.0, -0.0, 0.5, -0.5, 1.5, -1.5, 2.5, 0.1, 1e-7, -1e-7, -1e-300, 5e-324, -5e-324, 1e6, 1e9,
             1.7e9 + 0.25, -1.7e9 - 0.75, 86399.999999, -86400.5, 2.0 ** 52 + 0.5, 2.0 ** 63, -2.0 ** 63,
             253402300799.0, 253402300800.0, -62135596800.0, -62135596801.0, 1e300, float("inf"),
             float("-inf"), float("nan")]


class Rec(Exception):
    pass


def bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def unbits(b):
    return struct.unpack("<d", struct.pack("<Q", b))[0]


def digits(rng, n):
    return "".join(rng.choice("0123456789") for _ in range(n))


def isodate_string(rng):
    y = digits(rng, 4)
    m = rng.choice([digits(rng, 2), "00", "01", "12", "13", "99", "0x", "x1", "1", "W1", "-1", " 1", "١٢"])
    dd = rng.choice([digits(rng, 2), "00", "01", "10", "28", "31", "32", "99", "9", "x0", "0x", "\x00\x00"])
    sep = rng.random() < 0.5
    s = y + ("-" if sep else "") + m + (rng.choice(["-", "-", "/", "x", ""]) if sep else "") + dd
    return s + rng.choice(["", "", "", "T00", "x", "\x00", "5"])


def gen_x6(rng, d):
    fn = rng.choice(X6_FNS)
    impl = rng.choice(["py", "c"])
    if fn == "x6_isodate":
        return {"mod": "datetime", "fn": "date_fromiso_" + impl, "s": [ord(ch) for ch in isodate_string(rng)]}
    if fn == "x6_iso24":
        s = rng.choice(["24:00", "24:00:00", "24:00:00.000000", "24:00:00.000001", "24:01", "24:00:01", "24",
                        "2400", "240000", "24:00Z", "24:00+01:00", "24:00:00-05:30", "24:00:00.5+00:00",
                        "24:00:00+24:00", "24:30+99:00", "25:00", "23:59:59.999999"])
        if rng.random() < 0.3:
            s = "T" + s
        return {"mod": "datetime", "fn": "x5_fromiso", "impl": "c", "sub": rng.random() < 0.4, "kind": "time",
                "s": [ord(ch) for ch in s]}
    c = {"mod": "datetime", "fn": fn, "impl": impl}
    if fn == "x6_strfz":
        c["kind"] = rng.choice(["date", "time", "datetime"])
        c["v"] = d.rand_date(rng) + [rng.randint(0, 23), rng.randint(0, 59), rng.randint(0, 59),
                                     rng.choice([0, rng.randrange(10**6)])]
        c["tz"] = None if rng.random() < 0.35 else rng.choice(OFFS)
        c["name"] = rng.choice(NAMES)
        c["fmt"] = rng.choice(["%z", "%:z", "%Z"])
        c["ov_off"] = rng.choice(["inherit", "inherit", "none", rng.choice(OFFS), 30 * 3600 * 10**6])
        c["ov_name"] = rng.choice(["inherit", "inherit", "none", "OV", "x y"])
    elif fn == "x6_reduce":
        c["kind"] = rng.choice(["time", "datetime"])
        c["v"] = d.rand_date(rng) + [rng.randint(0, 23), rng.randint(0, 59), rng.randint(0, 59),
                                     rng.choice([0, rng.randrange(10**6)]), rng.choice([0, 1])]
        c["tz"] = None if rng.random() < 0.5 else rng.choice(OFFS[:5])
        c["override"] = rng.random() < 0.5
    elif fn == "x6_fromts":
        c["cls"] = rng.choice(["date", "datetime", "sub"])
        k = rng.random()
        if k < 0.5:
            x = rng.choice(TS_FLOATS) if rng.random() < 0.5 else rng.uniform(-2e10, 2e10) * rng.choice([1, 1e-6, 1e3])
            c["t"] = ["f", bits(x)]
        elif k < 0.9:
            c["t"] = ["i", rng.choice([0, 1, -1, 86399, 86400, -86401, 2**31, -2**31, 2**63 - 1, -2**63, 2**63,
                                       10**20, 253402300799, 253402300800, -62135596800, -62135596801,
                                       rng.randint(-10**11, 10**11)])]
        else:
            c["t"] = ["x"] if rng.random() < 0.5 else ["n"]
    elif fn == "x6_td":
        n = rng.randint(1, 4)
        given = set(rng.sample(range(7), n))

        def arg():
            v = rng.choice([0, 1, -1, 7, 59, 60, 3600, 86399, 86400, 999999, 10**6, 2**31 - 1, -(2**31 - 1),
                            rng.randint(-2**31 + 1, 2**31 - 1), rng.randint(-10**6, 10**6)])
            return ["f", bits(float(v))] if rng.random() < 0.6 else ["i", v]
        return {"mod": "datetime", "fn": "x3_td", "impl": impl, "args": [arg() if i in given else None for i in range(7)]}
    elif fn == "x6_astz":
        c["v"] = [rng.randint(1901, 2099), rng.randint(1, 12), rng.randint(1, 28), rng.randint(0, 23),
                  rng.randint(0, 59), rng.randint(0, 59), rng.choice([0, rng.randrange(10**6)])]
        c["self_off"] = rng.choice(OFFS[1:])
        c["target"] = rng.choice(OFFS)
        c["cached"] = rng.random() < 0.5
        c["cache"] = [rng.randint(1901, 2099), rng.randint(1, 12), rng.randint(1, 28), rng.randint(0, 23),
                      0, 0, 0]
        c["cache_off"] = rng.choice([None, 0, 3600 * 10**6])
    return c


def run_x6(c, d):
    fn, impl = c["fn"], c["impl"]
    m = d.IMPL[impl]

    def us(td):
        return (td.days * 86400 + td.seconds) * 10**6 + td.microseconds

    def tz(off, name=None):
        if off is None:
            return None
        return m.timezone(m.timedelta(microseconds=off)) if name is None else \
            m.timezone(m.timedelta(microseconds=off), name)

    def off(v):
        return None if v.tzinfo is None else us(v.utcoffset())

    def thunk():
        if fn == "x6_strfz":
            ns = {}
            if c["ov_off"] != "inherit":
                o = c["ov_off"]
                ns["utcoffset"] = (lambda self: None) if o == "none" else (lambda self, o=o: m.timedelta(microseconds=o))
            if c["ov_name"] != "inherit":
                nm = c["ov_name"]
                ns["tzname"] = (lambda self: None) if nm == "none" else (lambda self, nm=nm: nm)
            v, kind = c["v"], c["kind"]
            base = {"date": m.date, "time": m.time, "datetime": m.datetime}[kind]
            S = type("S", (base,), ns) if ns else base
            z = tz(c["tz"], c["name"])
            if kind == "date":
                obj = S(*v[:3])
            elif kind == "time":
                obj = S(*v[3:7], tzinfo=z)
            else:
                obj = S(*v[:7], tzinfo=z)
            return obj.strftime(c["fmt"])
        if fn == "x6_reduce":
            ns = {"__reduce_ex__": lambda self, p: (str, ("custom", p))} if c["override"] else {}
            v = c["v"]
            if c["kind"] == "time":
                S = type("S", (m.time,), ns)
                obj = S(*v[3:7], tzinfo=tz(c["tz"]), fold=v[7])
            else:
                S = type("S", (m.datetime,), ns)
                obj = S(*v[:7], tzinfo=tz(c["tz"]), fold=v[7])
            r = obj.__reduce__()
            if r[0] is str:
                return list(r[1])
            st = r[1]
            return [list(st[0])] if len(st) == 1 else [list(st[0]), us(st[1].utcoffset(None))]
        if fn == "x6_fromts":
            t = c["t"]
            a = t[1] if t[0] == "i" else unbits(t[1]) if t[0] == "f" else "x" if t[0] == "x" else None
            if c["cls"] == "sub":
                def new(cls, *args, **kw):
                    raise Rec(",".join(str(x) for x in args) + ";" + ",".join(sorted(kw)))
                cls = type("S", (m.date,), {"__new__": new})
                r = cls.fromtimestamp(a)
            else:
                cls = m.date if c["cls"] == "date" else m.datetime
                r = vars(m.date)["fromtimestamp"].__get__(None, cls)(a)
            if isinstance(r, m.datetime):
                return [r.year, r.month, r.day, r.hour, r.minute, r.second, r.microsecond]
            return [r.year, r.month, r.day]
        if fn == "x6_td":
            names = ["days", "seconds", "microseconds", "milliseconds", "minutes", "hours", "weeks"]
            kw = {}
            for nm, a in zip(names, c["args"]):
                if a is not None:
                    kw[nm] = a[1] if a[0] == "i" else unbits(a[1])
            r = m.timedelta(**kw)
            return [r.days, r.seconds, r.microseconds]
        if fn == "x6_astz":
            cache_holder = [None]
            armed = [False]

            def new(cls, *a, **k):
                if armed[0] and c["cached"] and len(a) == 8:
                    return cache_holder[0]
                return m.datetime.__new__(cls, *a, **k)
            D = type("D", (m.datetime,), {"__new__": new})
            cache_holder[0] = D(*c["cache"], tzinfo=tz(c["cache_off"]))
            self = D(*c["v"], tzinfo=tz(c["self_off"]))
            armed[0] = True
            try:
                r = self.astimezone(tz(c["target"]))
                res = [r.year, r.month, r.day, r.hour, r.minute, r.second, r.microsecond, off(r)]
                err = None
            except Exception as e:
                res = None
                err = type(e).__name__ + ": " + str(e)
            armed[0] = False
            k = cache_holder[0]
            return [res, err, [k.year, k.month, k.day, k.hour, k.minute, k.second, k.microsecond, off(k)]]
        raise AssertionError(fn)

    return common.py_result(thunk)
