"""Cases for the models of review b666ff1d's rows (`"fn": "x5_..."`), used by datetime_diff.py:
the class argument of replace, combine, fromisoformat, utctimetuple and astimezone (a subclass
whose __new__ raises Rec with its arguments, so the call shape is the result), __reduce_ex__
with the clinic int converter, the separator search (C model against _pydatetime), timezone
comparison on every operator, IsoCalendarDate, str() through isoformat, datetime.now's tz check
and the class attributes."""

import common

X5_FNS = ["x5_repl", "x5_repl", "x5_combine", "x5_fromiso", "x5_fromiso", "x5_reduce", "x5_sep", "x5_tzcmp",
          "x5_utctt", "x5_astz", "x5_isocal", "x5_str", "x5_now", "x5_init"]
BIG = [2**31 - 1, 2**31, -2**31, -2**31 - 1, 2**63, 10**20]
OFFS = [None, 0, 3600 * 10**6, -3600 * 10**6, 1, -1, 86399999999, -86399999999, 5 * 10**6, 19800 * 10**6]


class Rec(Exception):
    pass


def field(rng, lo, hi):
    return rng.choice([lo, hi, rng.randint(lo, hi), rng.randint(lo, hi), lo - 1, hi + 1, rng.choice(BIG)])


def rand_dt(rng, d):
    return d.rand_date(rng) + [rng.choice([0, 1, 12, 23, rng.randint(0, 23)]), rng.choice([0, 59, rng.randint(0, 59)]),
                               rng.choice([0, 59, rng.randint(0, 59)]), rng.choice([0, 999999, rng.randrange(10**6)]),
                               rng.choice([0, 0, 1])]


def rand_tm(rng):
    return [rng.choice([0, 23, rng.randint(0, 23)]), rng.choice([0, 59, rng.randint(0, 59)]),
            rng.choice([0, 59, rng.randint(0, 59)]), rng.choice([0, 999999, rng.randrange(10**6)]),
            rng.choice([0, 0, 1])]


def surrogate_iso(rng, d):
    s = list(d.iso_string(rng)) if rng.random() < 0.6 else list(d.valid_iso(rng))
    for _ in range(rng.choice([1, 1, 2])):
        pos = rng.choice([7, 8, 10, 7, 8, 10, rng.randrange(len(s) + 1)])
        ch = chr(rng.choice([0xD800, 0xDBFF, 0xDC00, 0xDFFF, 0xDABC]))
        if pos < len(s) and rng.random() < 0.7:
            s[pos] = ch
        else:
            s.insert(min(pos, len(s)), ch)
    return "".join(s)


def gen_x5(rng, d):
    fn = rng.choice(X5_FNS)
    c = {"mod": "datetime", "fn": fn, "impl": "c", "sub": rng.random() < 0.5}
    if fn == "x5_repl":
        kind = rng.choice(["date", "time", "datetime"])
        c["kind"] = kind
        if kind == "time":
            c["v"], c["v_tz"] = rand_tm(rng), rng.choice(OFFS[:6])
            names = [("hour", 0, 23), ("minute", 0, 59), ("second", 0, 59), ("microsecond", 0, 999999), ("fold", 0, 1)]
        else:
            c["v"], c["v_tz"] = rand_dt(rng, d), rng.choice(OFFS[:6])
            names = [("year", 1, 9999), ("month", 1, 12), ("day", 1, 31)]
            if kind == "datetime":
                names += [("hour", 0, 23), ("minute", 0, 59), ("second", 0, 59), ("microsecond", 0, 999999),
                          ("fold", 0, 1)]
        for n, lo, hi in names:
            if rng.random() < 0.3:
                c[n] = field(rng, lo, hi)
    elif fn == "x5_combine":
        c.update(date=d.rand_date(rng), time=rand_tm(rng), time_tz=rng.choice(OFFS[:6]),
                 tzk=rng.choice(["omit", "none", "tz"]), tzv=rng.choice(OFFS[1:6]))
    elif fn == "x5_fromiso":
        kind = rng.choice(["time", "datetime", "datetime"])
        c["kind"] = kind
        if kind == "time":
            s = d.iso_string(rng)
            if rng.random() < 0.5:
                s = s.split("T", 1)[-1]
        else:
            s = surrogate_iso(rng, d) if rng.random() < 0.4 else d.iso_string(rng)
        c["s"] = [ord(ch) for ch in s]
    elif fn == "x5_reduce":
        kind = rng.choice(["time", "datetime"])
        c["kind"], c["impl"] = kind, rng.choice(["c", "py"])
        if kind == "time":
            c["v"], c["v_tz"] = rand_tm(rng), rng.choice(OFFS[:6])
        else:
            c["v"], c["v_tz"] = rand_dt(rng, d), rng.choice(OFFS[:6])
        c["p"] = rng.choice([None, 0, 1, 2, 3, 4, 5, -1, 2**31 - 1] + BIG)
    elif fn == "x5_sep":
        c["impl"] = rng.choice(["c", "py"])
        while True:
            s = d.iso_string(rng)
            if len(s) >= 7 and s.isascii():
                break
            s = "".join(rng.choice("0123456789-WT:") for _ in range(rng.randint(7, 14)))
            if rng.random() < 0.5:
                break
        c["s"] = [ord(ch) for ch in s]
    elif fn == "x5_tzcmp":
        c.update(impl=rng.choice(["c", "py"]), a=rng.choice(OFFS[1:]), b=rng.choice(OFFS),
                 op=rng.choice(["lt", "le", "eq", "ne", "gt", "ge"]))
    elif fn == "x5_utctt":
        c["v"], c["v_tz"] = rand_dt(rng, d), rng.choice(OFFS)
    elif fn == "x5_astz":
        c["v"], c["v_tz"] = rand_dt(rng, d), rng.choice(OFFS[1:])
        c["target"] = rng.choice(OFFS[1:])
    elif fn == "x5_isocal":
        c["args"] = [field(rng, 1, 9999), field(rng, 1, 53), field(rng, 1, 7)]
    elif fn == "x5_str":
        c.update(impl=rng.choice(["c", "py"]), v=rand_dt(rng, d), v_tz=rng.choice(OFFS[:6]),
                 override=rng.random() < 0.5)
    return c


def run_x5(c, d):
    fn, impl = c["fn"], c["impl"]
    m = d.IMPL[impl]

    def us(td):
        return (td.days * 86400 + td.seconds) * 10**6 + td.microseconds

    def tz(off):
        return None if off is None else m.timezone(m.timedelta(microseconds=off))

    def enc_arg(a):
        if a is None:
            return "N"
        if isinstance(a, int) and not isinstance(a, bool):
            return str(a)
        if isinstance(a, m.tzinfo):
            return "tz" + str(us(a.utcoffset(None)))
        return "?"

    armed = [False]

    def sub_of(base):
        def new(cls, *a, **k):
            if armed[0]:
                raise Rec(",".join(enc_arg(x) for x in a) + ";" + ("f%d" % k["fold"] if "fold" in k else "-"))
            return base.__new__(cls, *a, **k)
        return type("S", (base,), {"__new__": new}) if c.get("sub") else base

    def off(v):
        return None if v.tzinfo is None else us(v.utcoffset())

    def enc_dt(v):
        return [v.year, v.month, v.day, v.hour, v.minute, v.second, v.microsecond, v.fold, off(v)]

    def enc_tm(v):
        return [v.hour, v.minute, v.second, v.microsecond, v.fold, off(v)]

    def mk_dt(cls, key="v"):
        f = c[key]
        return cls(*f[:7], tzinfo=tz(c.get(key + "_tz")), fold=f[7])

    def mk_tm(cls, key="v"):
        f = c[key]
        return cls(*f[:4], tzinfo=tz(c.get(key + "_tz")), fold=f[4])

    def thunk():
        if fn == "x5_repl":
            kind = c["kind"]
            base = {"date": m.date, "time": m.time, "datetime": m.datetime}[kind]
            S = sub_of(base)
            if kind == "date":
                v = S(*c["v"][:3])
            elif kind == "time":
                v = mk_tm(S)
            else:
                v = mk_dt(S)
            kw = {k: c[k] for k in ("year", "month", "day", "hour", "minute", "second", "microsecond", "fold") if k in c}
            armed[0] = True
            r = v.replace(**kw)
            armed[0] = False
            return [r.year, r.month, r.day] if kind == "date" else enc_tm(r) if kind == "time" else enc_dt(r)
        if fn == "x5_combine":
            S = sub_of(m.datetime)
            t = mk_tm(m.time, "time")
            dd = m.date(*c["date"])
            armed[0] = True
            if c["tzk"] == "omit":
                r = S.combine(dd, t)
            elif c["tzk"] == "none":
                r = S.combine(dd, t, None)
            else:
                r = S.combine(dd, t, tz(c["tzv"]))
            armed[0] = False
            return enc_dt(r)
        if fn == "x5_fromiso":
            s = "".join(map(chr, c["s"]))
            if c["kind"] == "time":
                S = sub_of(m.time)
                armed[0] = True
                r = S.fromisoformat(s)
                return [r.hour, r.minute, r.second, r.microsecond, off(r)]
            S = sub_of(m.datetime)
            armed[0] = True
            r = S.fromisoformat(s)
            return [r.year, r.month, r.day, [r.hour, r.minute, r.second, r.microsecond, off(r)]]
        if fn == "x5_reduce":
            v = mk_tm(m.time) if c["kind"] == "time" else mk_dt(m.datetime)
            r = v.__reduce__() if c["p"] is None else v.__reduce_ex__(c["p"])
            st = r[1]
            return [list(st[0])] if len(st) == 1 else [list(st[0]), us(st[1].utcoffset(None))]
        if fn == "x5_sep":
            return d._pydatetime._find_isoformat_datetime_separator("".join(map(chr, c["s"])))
        if fn == "x5_tzcmp":
            a = m.timezone(m.timedelta(microseconds=c["a"]))
            b = object() if c["b"] is None else m.timezone(m.timedelta(microseconds=c["b"]))
            r = getattr(a, "__%s__" % c["op"])(b)
            return None if r is NotImplemented else r
        if fn == "x5_utctt":
            S = sub_of(m.datetime)
            v = mk_dt(S)
            armed[0] = True
            return list(v.utctimetuple())
        if fn == "x5_astz":
            S = sub_of(m.datetime)
            v = mk_dt(S)
            armed[0] = True
            r = v.astimezone(tz(c["target"]))
            armed[0] = False
            return enc_dt(r)
        if fn == "x5_isocal":
            T = type(m.date(2000, 1, 1).isocalendar())
            r = T(*c["args"])
            return [r.year, r.week, r.weekday, list(r.__reduce__()[1][0])]
        if fn == "x5_str":
            ns = {"isoformat": lambda self, *a, **k: "P" + ",".join(str(x) for x in a) + "K" + ",".join(k)} \
                if c["override"] else {}
            S = type("S", (m.datetime,), ns)
            return str(mk_dt(S))
        if fn == "x5_now":
            m.datetime.now(tz=1)
            return None
        if fn == "x5_init":
            def td(t):
                return [t.days, t.seconds, t.microseconds]
            return [td(m.timedelta.min), td(m.timedelta.max), td(m.timedelta.resolution),
                    [m.date.min.year, m.date.min.month, m.date.min.day],
                    [m.date.max.year, m.date.max.month, m.date.max.day], td(m.date.resolution),
                    enc_tm(m.time.min), enc_tm(m.time.max), td(m.time.resolution),
                    enc_dt(m.datetime.min), enc_dt(m.datetime.max), td(m.datetime.resolution),
                    us(m.timezone.utc.utcoffset(None)), us(m.timezone.min.utcoffset(None)),
                    us(m.timezone.max.utcoffset(None))]
        raise AssertionError(fn)

    return common.py_result(thunk)
