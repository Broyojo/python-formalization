"""Differential test: Lean model of datetime (both twins) vs. the running CPython.

Usage: python3 difftest/datetime_diff.py [--cases N] [--seed S]

Every case names the implementation it is compared with: `..._py` cases run
`_pydatetime`, `..._c` cases run `_datetime`. Exits non-zero on any mismatch.
See difftest/common.py.
"""

import _datetime
import _pydatetime

import common

IMPL = {"py": _pydatetime, "c": _datetime}

# Non-ASCII characters the generator mixes into ISO strings: Unicode decimal
# digits, Unicode and ASCII white space, NUL, multi-byte UTF-8 of every length.
UNI = ["٠", "١", "٩", "۵", "०", "１", "\U0001d7ce", "\U0001d7d9",
       "\U00011066", "\x85", "\xa0", " ", "　", "é", "€", "\U0001f600",
       "\x00", "\t", "\n", "\x0b", "\x1c", " ", "_", "+", "-", "²", "①", "\x7f"]
ASCII = list("0123456789") * 6 + list("-:T tWZz+.,_") * 2


def edge_int(rng):
    return rng.choice([0, 1, -1, 2, 7, 24, 59, 60, 1000, 86399, 86400, -86400, 10**6, 10**6 - 1,
                       -10**6, 999999999, 10**9, -999999999, -10**9, 2**31 - 1, 2**31, -2**31,
                       -2**31 - 1, 2**63, -2**63, 2**64, 2**100, -2**100, 3652059, 3652060,
                       9999, 10000, 52, 53, rng.randint(-10**6, 10**6), rng.randint(-10**12, 10**12),
                       rng.randint(-10**20, 10**20), rng.randint(-100, 100)])


def rand_delta(rng):
    return [rng.choice([-999999999, 999999999, 0, -1, 1, rng.randint(-999999999, 999999999),
                        rng.randint(-1000, 1000)]),
            rng.choice([0, 86399, rng.randrange(86400)]),
            rng.choice([0, 999999, rng.randrange(10**6)])]


def rand_date(rng):
    y = rng.choice([1, 2, 4, 100, 400, 1600, 2000, 2004, 2020, 2021, 9998, 9999, rng.randint(1, 9999)])
    m = rng.randint(1, 12)
    dim = [31, 29 if (y % 4 == 0 and (y % 100 != 0 or y % 400 == 0)) else 28, 31, 30, 31, 30,
           31, 31, 30, 31, 30, 31][m - 1]
    d = rng.choice([1, dim, rng.randint(1, dim)])
    return [y, m, d]


def digits(rng, n):
    return "".join(rng.choice("0123456789") for _ in range(n))


def valid_iso(rng):
    """The output of isoformat() for a random value."""
    tz = None if rng.random() < 0.4 else _datetime.timezone(_datetime.timedelta(microseconds=rng.choice(
        [0, 1, -1, 3600 * 10**6, -19800 * 10**6, 86399999999, rng.randint(-86399999999, 86399999999)])))
    dt = _datetime.datetime(*rand_date(rng), rng.randint(0, 23), rng.randint(0, 59), rng.randint(0, 59),
                            rng.choice([0, 1, 999999, rng.randrange(10**6)]), tzinfo=tz)
    spec = rng.choice(["auto", "hours", "minutes", "seconds", "milliseconds", "microseconds"])
    k = rng.random()
    if k < 0.3:
        return dt.date().isoformat()
    if k < 0.6:
        return dt.timetz().isoformat(spec)
    return dt.isoformat(rng.choice("T T x\u20ac"), spec)


def iso_string(rng):
    """Structured ISO-like strings, then random mutations."""
    if rng.random() < 0.2:
        s = valid_iso(rng)
        return s if rng.random() < 0.7 else s + rng.choice(["\x00", "Z", "0", "\x00junk", " "])
    if rng.random() < 0.15:
        return "".join(rng.choice(ASCII + UNI) for _ in range(rng.randint(0, 14)))
    y = rng.choice(["2020", "2021", "0001", "9999", "2004", "2015", "1900", "0000", digits(rng, 4)])
    m = "%02d" % rng.randint(0, 13)
    d = "%02d" % rng.randint(0, 32)
    w = "%02d" % rng.randint(0, 54)
    wd = str(rng.randint(0, 8))
    ds = rng.choice([f"{y}-{m}-{d}", f"{y}{m}{d}", f"{y}-W{w}", f"{y}W{w}", f"{y}-W{w}-{wd}",
                     f"{y}W{w}{wd}", f"{y}-{m}", f"{y}{m}", f"{y}-{digits(rng, 3)}", f"{y}{digits(rng, 3)}"])
    s = ds
    if rng.random() < 0.65:
        hh = "%02d" % rng.choice([0, 12, 23, 24, 25, rng.randint(0, 99)])
        mm = "%02d" % rng.choice([0, 30, 59, 60, rng.randint(0, 99)])
        ss = "%02d" % rng.choice([0, 30, 59, 60, rng.randint(0, 99)])
        frac = digits(rng, rng.choice([0, 1, 2, 3, 5, 6, 7, 9]))
        ts = rng.choice([hh, f"{hh}:{mm}", f"{hh}{mm}", f"{hh}:{mm}:{ss}", f"{hh}{mm}{ss}",
                         f"{hh}:{mm}:{ss}.{frac}", f"{hh}:{mm}:{ss},{frac}", f"{hh}{mm}{ss}.{frac}",
                         f"{hh}{mm}{ss}{frac}", f"{hh}:{mm}.{frac}", f"{hh}.{frac}", "00:00", "24:00", "24:00:00"])
        if rng.random() < 0.5:
            oh = "%02d" % rng.choice([0, 5, 23, 24, rng.randint(0, 99)])
            om = "%02d" % rng.choice([0, 30, 59, 60, rng.randint(0, 99)])
            os_ = "%02d" % rng.choice([0, 1, 59, 60, rng.randint(0, 99)])
            ofr = digits(rng, rng.choice([1, 3, 6, 7]))
            sg = rng.choice("+-")
            ts += rng.choice(["Z", "z", f"{sg}{oh}", f"{sg}{oh}:{om}", f"{sg}{oh}{om}", f"{sg}{oh}:{om}:{os_}",
                              f"{sg}{oh}{om}{os_}", f"{sg}{oh}:{om}:{os_}.{ofr}", f"{sg}{oh}{om}{os_}.{ofr}",
                              f"{sg}{oh}:{om}.{ofr}", "+", "-", "Z0", "Z\x00x", "+00:00\x00"])
        if rng.random() < 0.1:
            ts += rng.choice(["\x00", "\x00junk", "x", " "])
        sep = rng.choice(["T", "T", " ", "t", "x", "5", "-", "W", "é", "€", "\U0001f600", "\x00"])
        s = ds + sep + ts if rng.random() < 0.9 else ts
    if rng.random() < 0.25:
        s = list(s)
        for _ in range(rng.randint(1, 3)):
            op, i = rng.random(), rng.randrange(len(s) + 1)
            ch = rng.choice(ASCII + UNI)
            if op < 0.35 and s:
                del s[min(i, len(s) - 1)]
            elif op < 0.7:
                s.insert(i, ch)
            elif s:
                s[min(i, len(s) - 1)] = ch
        s = "".join(s)
    return s


ISO_FNS = ["date_fromiso", "time_fromiso", "datetime_fromiso"]
OPS = ["add", "sub", "neg", "abs", "mul", "floordiv_int", "truediv_int", "floordiv", "mod", "divmod"]


def gen_case(rng):
    impl = rng.choice(["py", "c"])
    kind = rng.random()
    if kind < 0.55:
        fn = rng.choice(ISO_FNS)
        return {"mod": "datetime", "fn": f"{fn}_{impl}", "s": [ord(ch) for ch in iso_string(rng)]}
    fn = rng.choice(["td", "td_op", "td_str", "fromordinal", "toordinal", "isocalendar",
                     "fromisocalendar", "date_add", "timezone", "date_isoformat", "time_isoformat",
                     "datetime_isoformat"])
    c = {"mod": "datetime"}
    if fn == "td":
        c.update(fn=f"td_{impl}", args=[edge_int(rng) if rng.random() < 0.4 else 0 for _ in range(7)])
    elif fn == "td_op":
        b = rand_delta(rng)
        if rng.random() < 0.05:
            b = [0, 0, 0]
        c.update(fn=f"td_op_{impl}", op=rng.choice(OPS), a=rand_delta(rng), b=b,
                 k=rng.choice([0, 1, -1, 2, -3, 1000, 10**6, edge_int(rng)]))
    elif fn == "td_str":
        c.update(fn="td_str", a=rand_delta(rng))
    elif fn == "fromordinal":
        c.update(fn=f"fromordinal_{impl}", n=rng.choice([edge_int(rng), rng.randint(-10, 3652070),
                                                          rng.randint(1, 3652059)]))
    elif fn == "toordinal":
        c.update(fn="toordinal", date=rand_date(rng))
    elif fn == "isocalendar":
        c.update(fn="isocalendar", date=rand_date(rng))
    elif fn == "fromisocalendar":
        c.update(fn=f"fromisocalendar_{impl}",
                 args=[rng.choice([rng.randint(-1, 10001), edge_int(rng), 2020, 2015, 9999, 1]),
                       rng.choice([rng.randint(-1, 55), 52, 53, edge_int(rng)]),
                       rng.choice([rng.randint(-1, 9), edge_int(rng)])])
    elif fn == "date_add":
        c.update(fn=f"date_add_{impl}", date=rand_date(rng), td=rand_delta(rng))
    elif fn == "timezone":
        t = rng.choice([[0, rng.randrange(86400), rng.randrange(10**6)], [-1, rng.randrange(86400), rng.randrange(10**6)],
                        [-1, 0, 0], [-1, 0, 1], [0, 86399, 999999], [1, 0, 0], [-2, 86399, 999999], [0, 0, 0],
                        rand_delta(rng)])
        c.update(fn=f"timezone_{impl}", td=t)
    else:
        spec = rng.choice(["auto", "hours", "minutes", "seconds", "milliseconds", "microseconds"])
        tz = None if rng.random() < 0.3 else rng.choice([0, 1, -1, 999999, -999999, 86399999999, -86399999999,
                                                        3600 * 10**6, -19800 * 10**6, rng.randint(-86399999999, 86399999999)])
        t = [rng.randint(0, 23), rng.randint(0, 59), rng.randint(0, 59), rng.choice([0, 1, 999, 1000, 999999, rng.randrange(10**6)])]
        c.update(spec=spec, tz=tz)
        if fn == "date_isoformat":
            c.update(fn=fn, date=rand_date(rng))
        elif fn == "time_isoformat":
            c.update(fn=fn, time=t)
        else:
            c.update(fn=fn, dt=rand_date(rng) + t, sep=ord(rng.choice(["T", " ", "x", "€"])))
        c["impl"] = impl
    return c


def enc_delta(t):
    return [t.days, t.seconds, t.microseconds]


def enc_off(tz):
    if tz is None:
        return None
    return common_us(tz.utcoffset(None))


def common_us(td):
    return (td.days * 86400 + td.seconds) * 10**6 + td.microseconds


def enc_time(t):
    return [t.hour, t.minute, t.second, t.microsecond, None if t.tzinfo is None else common_us(t.utcoffset())]


def enc_dt(v):
    return [v.year, v.month, v.day, v.hour, v.minute, v.second, v.microsecond,
            None if v.tzinfo is None else common_us(v.utcoffset())]


def run_python(c):
    fn = c["fn"]
    base, _, impl = fn.rpartition("_")
    if impl not in IMPL:
        base, impl = fn, c.get("impl", "c")
    m = IMPL[impl]
    try:
        if base == "td":
            a = c["args"]
            v = enc_delta(m.timedelta(days=a[0], seconds=a[1], microseconds=a[2], milliseconds=a[3],
                                      minutes=a[4], hours=a[5], weeks=a[6]))
        elif base == "td_op":
            a, b, k = m.timedelta(*c["a"]), m.timedelta(*c["b"]), c["k"]
            op = c["op"]
            if op == "add": v = enc_delta(a + b)
            elif op == "sub": v = enc_delta(a - b)
            elif op == "neg": v = enc_delta(-a)
            elif op == "abs": v = enc_delta(abs(a))
            elif op == "mul": v = enc_delta(a * k)
            elif op == "floordiv_int": v = enc_delta(a // k)
            elif op == "truediv_int": v = enc_delta(a / k)
            elif op == "floordiv": v = a // b
            elif op == "mod": v = enc_delta(a % b)
            else:
                q, r = divmod(a, b)
                v = [q, enc_delta(r)]
        elif base == "td_str":
            a = _datetime.timedelta(*c["a"])
            pa = _pydatetime.timedelta(*c["a"])
            assert (str(a), repr(a)) == (str(pa), repr(pa))
            v = [str(a), repr(a)]
        elif base == "fromordinal":
            d = m.date.fromordinal(c["n"])
            v = [d.year, d.month, d.day]
        elif base == "toordinal":
            v = m.date(*c["date"]).toordinal()
        elif base == "isocalendar":
            v = list(m.date(*c["date"]).isocalendar())
        elif base == "fromisocalendar":
            d = m.date.fromisocalendar(*c["args"])
            v = [d.year, d.month, d.day]
        elif base == "date_add":
            d = m.date(*c["date"]) + m.timedelta(*c["td"])
            v = [d.year, d.month, d.day]
        elif base == "timezone":
            v = common_us(m.timezone(m.timedelta(*c["td"])).utcoffset(None))
        elif base in ("date_fromiso", "time_fromiso", "datetime_fromiso"):
            s = "".join(map(chr, c["s"]))
            cls = {"date_fromiso": m.date, "time_fromiso": m.time, "datetime_fromiso": m.datetime}[base]
            r = cls.fromisoformat(s)
            v = [r.year, r.month, r.day] if base == "date_fromiso" else enc_time(r) if base == "time_fromiso" else enc_dt(r)
        elif base == "date_isoformat":
            v = m.date(*c["date"]).isoformat()
        elif base == "time_isoformat":
            tz = None if c["tz"] is None else m.timezone(m.timedelta(microseconds=c["tz"]))
            v = m.time(*c["time"], tzinfo=tz).isoformat(c["spec"])
        elif base == "datetime_isoformat":
            tz = None if c["tz"] is None else m.timezone(m.timedelta(microseconds=c["tz"]))
            v = m.datetime(*c["dt"], tzinfo=tz).isoformat(chr(c["sep"]), c["spec"])
        else:
            raise AssertionError(fn)
        return {"ok": v}
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}


if __name__ == "__main__":
    common.main(gen_case, run_python)
