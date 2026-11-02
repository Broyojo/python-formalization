"""Differential test: Lean model of datetime (both twins) vs. the running CPython.

Usage: python3 difftest/datetime_diff.py [--cases N] [--seed S]

Every case names the implementation it is compared with: `..._py` cases run
`_pydatetime`, `..._c` cases run `_datetime`. Exits non-zero on any mismatch.
See difftest/common.py.
"""

import os
import time
import warnings

os.environ["TZ"] = "XXX-2"  # a fixed local zone, UTC+2, for `_mktime`
time.tzset()
LOCAL_OFF = 7200

import _datetime
import _pydatetime
import _strptime

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
                              f"{sg}{oh}:{om}.{ofr}", "+", "-", "Z0", "Z\x00x", "+00:00\x00",
                              # the range check of parse_isoformat_time runs even if the offset failed to parse
                              f"{sg}{oh}x", f"{sg}{oh}:{om}x", f"{sg}{oh}:{om}:{os_}x", f"{sg}{oh}{om}x",
                              f"{sg}{oh}:{om}:{os_}.{ofr}x", f"{sg}{oh}:", f"{sg}{oh}:{om}:", f"{sg}9", f"{sg}{oh}:9"])
        if rng.random() < 0.1:
            ts += rng.choice(["\x00", "\x00junk", "x", " "])
        sep = rng.choice(["T", "T", " ", "t", "x", "5", "-", "W", "é", "€", "\U0001f600", "\x00"])
        s = ds + sep + ts if rng.random() < 0.9 else rng.choice([ts, ts, "T" + ts])
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


# ---------------------------------------------------------------------------
# Object layer: tzinfo subclasses, comparison, hash, pickle, repr, strftime.

_pydatetime._need_normalize_century()
NORM = bool(_pydatetime._need_normalize_century())
REAL_STRFTIME = time.strftime


def make_tz_class(m):
    H = m.timedelta(hours=1)

    def rule(dt):
        if 4 <= dt.month <= 9 or (dt.month == 10 and dt.day < 15):
            return H
        if dt.month == 10 and dt.day == 15 and dt.hour == 1 and dt.fold == 0:
            return H
        return m.timedelta(0)

    class TZ(m.tzinfo):
        def __init__(self, impl):
            self.impl = impl

        def __repr__(self):
            return f"TZ({self.impl})"

        def utcoffset(self, dt):
            i = self.impl
            if i == 1: return None
            if i == 2: return H
            if i == 3: return None if dt is None else m.timedelta(hours=-5) + rule(dt)
            if i == 4: return 5
            if i == 5: return m.timedelta(1)
            if i == 6: raise ValueError("boom")
            if i == 7: return m.timedelta(seconds=30, microseconds=5)
            if i == 8: return m.timedelta(seconds=-90)
            return None

        def dst(self, dt):
            i = self.impl
            if i == 1: return None
            if i == 2: return m.timedelta(0)
            if i == 3: return None if dt is None else rule(dt)
            if i == 4: return "x"
            if i == 5: return m.timedelta(-1)
            if i == 6: raise ValueError("boom")
            if i == 7: return m.timedelta(seconds=-1)
            if i == 8: return m.timedelta(0)
            return None

        def tzname(self, dt):
            i = self.impl
            if i == 1: return None
            if i == 2: return "ONE"
            if i == 3: return None if dt is None else ("EST" if not rule(dt) else "EDT")
            if i == 4: return 5
            if i == 5: return None
            if i == 6: raise ValueError("boom")
            if i == 7: return "a%b"
            if i == 8: return "it's"
            return None

    class Base(m.tzinfo):
        def __repr__(self):
            return "TZ(0)"

    return TZ, Base


TZCLASS = {k: make_tz_class(v) for k, v in IMPL.items()}
OFFSETS = [[0, 3600, 0], [-1, 82800, 0], [0, 19800, 0], [0, 30, 0], [-1, 86370, 0], [0, 0, 500000],
           [0, 0, 250000], [0, 0, 1], [-1, 86399, 999999], [0, 86399, 999999], [-1, 0, 1], [0, 60, 0], [0, 1, 0]]
NAMES = [None, None, "X", "UTC+1", "it's", 'a"b', "q'\"", "a\\b", "a%b"]


def rand_tz_spec(rng, oid):
    k = rng.random()
    if k < 0.2:
        return None
    if k < 0.35:
        return ["tz", 0, [0, 0, 0], None]
    if k < 0.7:
        return ["tz", oid, rng.choice(OFFSETS), rng.choice(NAMES)]
    return ["cu", oid, rng.choice([0, 1, 2, 2, 3, 3, 3, 4, 5, 6, 7, 8])]


def build_tz(impl, spec, pool):
    m = IMPL[impl]
    if spec is None:
        return None
    oid = spec[1]
    if oid in pool:
        return pool[oid]
    if spec[0] == "tz":
        if oid == 0:
            t = m.timezone.utc
        elif spec[3] is None:
            t = m.timezone(m.timedelta(*spec[2]))
        else:
            t = m.timezone(m.timedelta(*spec[2]), spec[3])
    else:
        TZ, Base = TZCLASS[impl]
        t = Base() if spec[2] == 0 else TZ(spec[2])
    pool[oid] = t
    return t


def rand_time(rng):
    return [rng.choice([0, 1, 12, 23, rng.randint(0, 23)]), rng.choice([0, 30, 59, rng.randint(0, 59)]),
            rng.choice([0, 0, 1, 30, 59, rng.randint(0, 59)]), rng.choice([0, 0, 1, 500000, 999999, rng.randrange(10**6)])]


def rand_dt(rng, oid=1):
    return rand_date(rng) + rand_time(rng) + [rng.choice([0, 0, 1])] + [rand_tz_spec(rng, oid)]


def rand_tm(rng, oid=1):
    return rand_time(rng) + [rng.choice([0, 0, 1])] + [rand_tz_spec(rng, oid)]


def near(rng, v, oid=2):
    """A second operand often related to the first one."""
    w = list(v)
    n = len(w)
    if rng.random() < 0.5:
        w[n - 1] = rand_tz_spec(rng, oid) if rng.random() < 0.7 else w[n - 1]
        if rng.random() < 0.3:
            w[n - 2] = 1 - w[n - 2]
        return w
    return None


def strf_format(rng):
    toks = ["%f", "%z", "%:z", "%Z", "%Y", "%G", "%F", "%C", "%%", "%:", "%m", "%d", "x", ":", "%:%Z", "%:x", "%H", "z", "%"]
    return "".join(rng.choice(toks) for _ in range(rng.randint(0, 5)))


def rand_arg(rng, n):
    k = rng.random()
    if k < 0.5:
        return ["i", rng.choice([0, 1, 2, 12, 13, 24, 31, 59, 60, 999999, 10**6, 2020, 9999, 10000, -1,
                                 2**31 - 1, 2**31, -2**31 - 1, 2**64])]
    if k < 0.75:
        b = [rng.randrange(256) for _ in range(rng.choice([n, n, n, 1, 0, 11]))]
        if len(b) > 2 and rng.random() < 0.7:
            b[2] = rng.choice([1, 12, 129, 140])
            b[0] = rng.choice([7, 23, 24, 151, 152, 0])
        return [rng.choice("bs"), b]
    if k < 0.8:
        return ["s", [rng.randrange(256) for _ in range(n - 1)] + [0x1234]]
    if k < 0.9:
        return None
    if k < 0.95:
        return ["o"]
    return ["tz", rand_tz_spec(rng, 3)]


def small_field(rng):
    return rng.choice([None, None, None, 0, 1, 2, 12, 13, 23, 24, 31, 59, 60, -1, 1999, 9999, 10000, 999999, 10**6,
                       2**31 - 1, 2**31, -2**31, -2**31 - 1])


def rand_delta_small(rng):
    return rng.choice([rand_delta(rng), [0, rng.randrange(86400), rng.randrange(10**6)], [rng.randint(-3, 3), 0, 0],
                       [rng.randint(-4000000, 4000000), rng.randrange(86400), rng.randrange(10**6)]])


MORE_FNS = {"td_str2", "tz_new", "tz_cmp", "utc_seconds", "mktime", "strp_pattern", "strp_core", "strp_tail", "strp_date",
            "strp_time", "strp_dt", "strp_julian", "strp_findall", "strp_seq"}
OPS2 = ["lt", "le", "eq", "ne", "gt", "ge"]
OBJ_FNS = ["td_cmp", "td_bool", "td_pos", "td_rsub", "td_hash", "td_state", "date_cmp", "date_hash", "date_weekday",
           "date_sub_date", "date_sub_delta", "date_replace", "date_timetuple", "date_ctime", "date_repr", "date_state",
           "iso_repr", "date_strftime", "tz_str", "tz_repr", "tm_off", "dt_off", "tm_cmp", "tm_cmp", "tm_hash", "tm_repr",
           "tm_iso", "tm_state", "tm_strftime", "tm_replace", "dt_cmp", "dt_cmp", "dt_hash", "dt_repr", "dt_iso", "dt_ctime",
           "dt_add", "dt_sub_delta", "dt_sub", "dt_sub", "dt_timetuple", "dt_utctimetuple", "dt_parts", "dt_combine",
           "dt_replace", "dt_fromutc", "dt_astimezone", "dt_state", "dt_strftime", "ctor_date", "ctor_time", "ctor_datetime"]


def locale_json():
    lt = _strptime._TimeRE_cache.locale_time
    return {"fw": list(lt.f_weekday), "aw": list(lt.a_weekday), "fm": list(lt.f_month), "am": list(lt.a_month),
            "ap": list(lt.am_pm), "tz": [list(x) for x in lt.timezone], "dt": lt.LC_date_time, "d": lt.LC_date,
            "t": lt.LC_time, "ta": lt.LC_time_ampm, "alt": None if lt.LC_alt_digits is None else list(lt.LC_alt_digits),
            "amb": bool(time.tzname[0] == time.tzname[1] and time.daylight)}


LOCALE = locale_json()
STRP = ["%Y", "%y", "%m", "%d", "%H", "%I", "%p", "%M", "%S", "%f", "%a", "%A", "%b", "%B", "%j", "%U", "%W", "%w", "%u",
        "%G", "%V", "%z", "%Z", "%%", "%e", "%k", "%l", "%D", "%T", "%R", "%c", "%x", "%X", "%r", "%C", "%Oy", "%Od", "%OH",
        "%:z", "%n", "%t", "%F", "%P", "%Oe"]
# The year and day directives alone, so that the checks of TimeRE.pattern see every combination.
STRP_YD = ["%d", "%e", "%Y", "%y", "%G", "%Oy", "%Od", "%Oe", "%D", "%F", "%c", "%x", "%m", "%H"]
SEPS = ["", " ", "-", ":", "/", "T", ".", "  ", "\t", "(", "'", "+"]


def strp_format(rng):
    n = rng.randint(1, 7)
    return "".join(rng.choice(STRP) + rng.choice(SEPS) for _ in range(n))


def strp_format_yd(rng):
    return " ".join(rng.choice(STRP_YD) for _ in range(rng.randint(1, 3)))


def strp_input(rng, fmt):
    """A string for `fmt`: the strftime of a random datetime, with noise."""
    d = _datetime.datetime(rng.randint(1, 9999), rng.randint(1, 12), rng.randint(1, 28), rng.randint(0, 23),
                           rng.randint(0, 59), rng.randint(0, 59), rng.randrange(10**6),
                           tzinfo=rng.choice([None, _datetime.timezone.utc,
                                              _datetime.timezone(_datetime.timedelta(minutes=rng.randint(-1439, 1439)))]))
    try:
        s = d.strftime(fmt.replace("%k", "%H").replace("%l", "%I").replace("%Oy", "%y").replace("%Od", "%d").replace("%OH", "%H"))
    except Exception:
        s = ""
    return s


def gen_strptime(rng):
    c = {"mod": "datetime", "impl": "py", "lt": LOCALE}
    k = rng.random()
    if k < 0.15:
        fmt = strp_format(rng) if rng.random() < 0.5 else rng.choice(["%", "% d", "%Q", "%E", "%Ez", "%-d", "%\\", "a%", "%%%", "%5Y", "%_d", "%^a"])
        if rng.random() < 0.4:
            fmt = rng.choice([strp_format_yd(rng), "%:", "%:x", "%::z", "%E:z", "%O:z", "%:%", "%-5Y", "%0d", "%#d",
                              "%:\\", "%\\:", "%-:z", "%Y%", "%n%t", "% n", "%\n", "%d\n%Y", "%Y %-"])
        c.update(fn="strp_pattern", format=fmt)
        return c
    if k < 0.2:
        c.update(fn="strp_julian", y=rng.choice([1, 2000, 1999, 9999, rng.randint(1, 9999), 0]), w=rng.randint(0, 53),
                 d=rng.randint(0, 6), mon=rng.random() < 0.5)
        return c
    if k < 0.25:
        h = [rng.choice([97, 98]) for _ in range(rng.randint(0, 12))]
        n = [rng.choice([97, 98]) for _ in range(rng.randint(0, 3))]
        c.update(fn="strp_findall", h=h, n=n)
        return c
    if k < 0.3:
        c.update(fn="strp_seq", xs=[rng.choice(["", "a", "abc", "a.b", "x y", "bb", "q-r"]) for _ in range(rng.randint(0, 5))], d="X")
        return c
    if k < 0.45:
        return gen_strp_tail(rng, c)
    # A real match, so that `found` is what `re` produces.
    for _ in range(50):
        fmt = strp_format(rng)
        s = strp_input(rng, fmt)
        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                rx = _strptime._TimeRE_cache.compile(fmt)
        except Exception:
            continue
        found = rx.fullmatch(s) if s else None
        if found:
            gd = found.groupdict()
            c.update(fn=rng.choice(["strp_core", "strp_core", "strp_date", "strp_time", "strp_dt"]), format=fmt, data=s,
                     found=[[k, v] for k, v in gd.items()])
            return c
    return None


def gen_strp_tail(rng, c):
    """A match that may stop short of the end of the string, for the check on `found.end()`."""
    for _ in range(50):
        fmt = rng.choice(["%Y", "%Y-%m-%d", "%H:%M", strp_format(rng)]) + rng.choice(["%:z", "%:z", "%z", " %:z", ""])
        s = strp_input(rng, fmt) + rng.choice(["", "x", ":", ":30", "00", " ", "+05", "Z", "é", "+05:30", ":x"])
        if rng.random() < 0.3:
            s = rng.choice(["2020", "2020-01-02", "12:30", "2020+05:30", "2020+05:3000", "2020Z", "2020Zx"]) + \
                rng.choice(["", "00", ":", ":00", " +05:30", "x"])
        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                rx = _strptime._TimeRE_cache.compile(fmt)
        except Exception:
            continue
        found = rx.match(s)
        if found:
            c.update(fn="strp_tail", format=fmt, s=s, data=[ord(x) for x in s], end=found.end(),
                     found=[[k, v] for k, v in found.groupdict().items()])
            return c
    return None


def gen_obj_case(rng):
    if rng.random() < 0.15:
        return gen_strptime(rng)
    if rng.random() < 0.1:
        impl = rng.choice(["py", "c"])
        k = rng.choice(["td_str2", "tz_new", "tz_cmp", "utc_seconds", "mktime"])
        c = {"mod": "datetime", "fn": k, "impl": impl}
        if k == "td_str2":
            c.update(a=rand_delta(rng))
        elif k == "tz_new":
            c.update(td=rng.choice(OFFSETS + [[0, 0, 0], [1, 0, 0], [-1, 0, 0], [2, 3, 4], rand_delta(rng)]),
                     name=rng.choice([None, "X", "", 5, "UTC"]))
        elif k == "tz_cmp":
            a = rng.choice(OFFSETS)
            c.update(a=a, b=a if rng.random() < 0.4 else rng.choice(OFFSETS), op=rng.choice(OPS2))
        elif k == "utc_seconds":
            c.update(a=rand_date(rng) + rand_time(rng)[:3])
        else:
            c.update(off=LOCAL_OFF, t=rng.randint(10**9, 6 * 10**10), fold=rng.choice([0, 1]))
        return c
    fn = rng.choice(OBJ_FNS)
    impl = rng.choice(["py", "c"])
    c = {"mod": "datetime", "fn": fn, "impl": impl, "norm": NORM}
    if fn in ("td_cmp", "td_rsub"):
        a = rand_delta(rng)
        c.update(a=a, b=a if rng.random() < 0.2 else rand_delta(rng), op=rng.choice(OPS2))
    elif fn in ("td_bool", "td_pos", "td_hash", "td_state"):
        c.update(a=rng.choice([rand_delta(rng), [0, 0, 0]]))
    elif fn in ("date_cmp", "date_sub_date"):
        a = rand_date(rng)
        c.update(a=a, b=a if rng.random() < 0.2 else rand_date(rng), op=rng.choice(OPS2))
    elif fn == "date_sub_delta":
        c.update(a=rand_date(rng), td=rand_delta_small(rng))
    elif fn == "date_replace":
        c.update(a=rand_date(rng), ny=small_field(rng), nm=small_field(rng), nd=small_field(rng))
    elif fn == "date_strftime":
        c.update(a=rng.choice([rand_date(rng), [rng.randint(1, 1100), 1, 1], [rng.randint(1, 1100), 12, 31]]),
                 f=[ord(x) for x in strf_format(rng)])
    elif fn.startswith("date_") or fn == "iso_repr":
        c.update(a=rand_date(rng))
    elif fn in ("tz_str", "tz_repr"):
        spec = None
        while spec is None or (fn == "tz_str" and spec[0] != "tz"):
            spec = rand_tz_spec(rng, 1)
        c.update(tz=spec)
    elif fn == "tm_off":
        c.update(t=rand_tm(rng))
    elif fn == "dt_off":
        c.update(t=rand_dt(rng))
    elif fn == "tm_cmp":
        a = rand_tm(rng, 1)
        b = near(rng, a) or rand_tm(rng, 2)
        c.update(a=a, b=b, op=rng.choice(OPS2))
    elif fn == "dt_cmp" or fn == "dt_sub":
        a = rand_dt(rng, 1)
        b = near(rng, a) or rand_dt(rng, 2)
        c.update(a=a, b=b, op=rng.choice(OPS2))
    elif fn in ("tm_hash", "tm_repr", "tm_state"):
        c.update(a=rand_tm(rng), proto=rng.choice([2, 3, 4, 5]))
    elif fn == "tm_iso":
        c.update(a=rand_tm(rng), spec=rng.choice(["auto", "hours", "minutes", "seconds", "milliseconds", "microseconds",
                                                  "", "Auto", "minute", "bogus"]))
    elif fn == "tm_strftime":
        c.update(a=rand_tm(rng), f=[ord(x) for x in strf_format(rng)])
    elif fn == "tm_replace":
        c.update(a=rand_tm(rng), nh=small_field(rng), nmi=small_field(rng), ns=small_field(rng), nus=small_field(rng),
                 nfold=rng.choice([None, None, 0, 1, 2, 2**31]))
        if rng.random() < 0.3:
            c["tzarg"] = rand_tz_spec(rng, 2)
    elif fn in ("dt_hash", "dt_repr", "dt_ctime", "dt_timetuple", "dt_utctimetuple", "dt_parts", "dt_state"):
        c.update(a=rand_dt(rng), proto=rng.choice([2, 3, 4, 5]))
    elif fn == "dt_iso":
        c.update(a=rand_dt(rng), spec=rng.choice(["auto", "hours", "minutes", "seconds", "milliseconds", "microseconds",
                                                  "", "Auto", "minute", "bogus"]),
                 sep=ord(rng.choice("T x")))
    elif fn in ("dt_add", "dt_sub_delta"):
        c.update(a=rand_dt(rng), td=rand_delta_small(rng))
    elif fn == "dt_combine":
        c.update(ymd=rand_date(rng), t=rand_tm(rng))
        if rng.random() < 0.5:
            c["tzarg"] = rand_tz_spec(rng, 2)
    elif fn == "dt_replace":
        c.update(a=rand_dt(rng), ny=small_field(rng), nm=small_field(rng), nd=small_field(rng), nh=small_field(rng),
                 nmi=small_field(rng), ns=small_field(rng), nus=small_field(rng), nfold=rng.choice([None, None, 0, 1, 2, 2**31]))
        if rng.random() < 0.3:
            c["tzarg"] = rand_tz_spec(rng, 2)
    elif fn == "dt_fromutc":
        a = rand_dt(rng)
        spec = a[-1]
        if spec is None or rng.random() < 0.1:
            spec = rand_tz_spec(rng, 2) or ["cu", 2, 2]
        c.update(a=a, tz=spec)
    elif fn == "dt_astimezone":
        a = rand_dt(rng)
        spec = rand_tz_spec(rng, 2) or ["cu", 2, 3]
        if a[-1] is not None and rng.random() < 0.2:
            spec = a[-1]
        c.update(a=a, tz=spec)
    elif fn == "dt_strftime":
        d = rng.choice([rand_date(rng), [rng.randint(1, 1100), rng.randint(1, 12), 1]])
        c.update(a=d + rand_dt(rng)[3:], f=[ord(x) for x in strf_format(rng)])
    elif fn == "ctor_date":
        # 0 and 4 reach the arity checks of the clinic wrapper
        n = rng.choice([1, 1, 3, 3, 2, 0, 4])
        c.update(args=[rand_arg(rng, 4) for _ in range(n)])
        if n == 3 and rng.random() < 0.5:
            c["args"] = [["i", x] for x in rand_date(rng)]
    elif fn == "ctor_time":
        n = rng.choice([0, 1, 1, 2, 2, 4, 5, 6])
        c.update(args=[rand_arg(rng, 6) for _ in range(n)], fold=rng.choice([0, 0, 1, 2, 2**31]))
    else:
        n = rng.choice([1, 1, 2, 2, 3, 3, 7, 8, 0, 9])
        c.update(args=[rand_arg(rng, 10) for _ in range(n)], fold=rng.choice([0, 0, 1, 2, 2**31]))
        if n >= 3 and rng.random() < 0.5:
            c["args"][:3] = [["i", x] for x in rand_date(rng)]
    return c


def run_more(c):
    fn, impl = c["fn"], c["impl"]
    m = IMPL[impl]

    def thunk():
        if fn == "td_str2":
            a = m.timedelta(*c["a"])
            return [str(a), repr(a)]
        if fn == "tz_new":
            off = m.timedelta(*c["td"])
            t = m.timezone(off) if c["name"] is None else m.timezone(off, c["name"])
            if t is m.timezone.utc:
                return [0, [0, 0, 0], None]
            nm = t.tzname(None) if c["name"] is not None else None
            return [1, [off.days, off.seconds, off.microseconds], nm]
        if fn == "tz_cmp":
            a, b = m.timezone(m.timedelta(*c["a"])), m.timezone(m.timedelta(*c["b"]))
            r = {"lt": a.__lt__, "le": a.__le__, "eq": a.__eq__, "ne": a.__ne__, "gt": a.__gt__, "ge": a.__ge__}[c["op"]](b)
            return None if r is NotImplemented else r
        if fn == "utc_seconds":
            a = c["a"]
            # `utc_to_seconds` through the fixed local zone of this process
            d = _pydatetime.datetime(*a)
            return (d.toordinal() * 24 + a[3]) * 3600 + a[4] * 60 + a[5]
        if fn == "mktime":
            epoch_ord = 719163
            d = _pydatetime.datetime(1970, 1, 1) + _pydatetime.timedelta(seconds=c["t"])
            if impl == "py":
                return _pydatetime.datetime(d.year, d.month, d.day, d.hour, d.minute, d.second, fold=c["fold"])._mktime()
            return int(_datetime.datetime(d.year, d.month, d.day, d.hour, d.minute, d.second, fold=c["fold"]).timestamp())
        if fn == "strp_pattern":
            fmt = c["format"]
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                try:
                    return _strptime._TimeRE_cache.pattern(fmt)
                except KeyError:
                    pass
                _strptime._regex_cache.clear()
                _strptime._strptime("", fmt)
            raise AssertionError("no error")
        if fn == "strp_julian":
            return _strptime._calc_julian_from_U_or_W(c["y"], c["w"], c["d"], c["mon"])
        if fn == "strp_findall":
            return list(_strptime._findall("".join(map(chr, c["h"])), "".join(map(chr, c["n"]))))
        if fn == "strp_seq":
            return _strptime._TimeRE_cache._TimeRE__seqToRE(c["xs"], c["d"])
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            if fn == "strp_core":
                tt, fr, gf = _strptime._strptime(c["data"], c["format"])
                return [list(tt), fr, gf]
            if fn == "strp_tail":
                tt, fr, gf = _strptime._strptime(c["s"], c["format"])
                return [list(tt), fr, gf]
            if fn == "strp_date":
                v = _strptime._strptime_datetime_date(_datetime.date, c["data"], c["format"])
                return [v.year, v.month, v.day]
            if fn == "strp_time":
                v = _strptime._strptime_datetime_time(_datetime.time, c["data"], c["format"])
                return [enc_strp_tm(v), enc_strp_tz(v)]
            v = _strptime._strptime_datetime_datetime(_datetime.datetime, c["data"], c["format"])
            return [[v.year, v.month, v.day] + enc_strp_tm(v), enc_strp_tz(v)]
        raise AssertionError(fn)

    return common.py_result(thunk)


def enc_strp_tm(v):
    o = None if v.tzinfo is None else 0 if v.tzinfo is _datetime.timezone.utc else 1
    return [v.hour, v.minute, v.second, v.microsecond, v.fold, o]


def enc_strp_tz(v):
    t = v.tzinfo
    if t is None:
        return None
    if t is _datetime.timezone.utc:
        return [0, [0, 0, 0], None]
    off = t.utcoffset(None)
    r = repr(t)
    return [1, [off.days, off.seconds, off.microseconds], t.tzname(None) if r.endswith("')") or r.endswith('")') else None]


def run_obj(c):
    fn, impl = c["fn"], c["impl"]
    m = IMPL[impl]
    pool = {}
    T = lambda s: build_tz(impl, s, pool)
    mkdt = lambda v: m.datetime(*v[:7], tzinfo=T(v[8]), fold=v[7])
    mktm = lambda v: m.time(*v[:4], tzinfo=T(v[5]), fold=v[4])
    oid = lambda t: None if t is None else 0 if t is m.timezone.utc else next(k for k, x in pool.items() if x is t)
    encdt = lambda v: [v.year, v.month, v.day, v.hour, v.minute, v.second, v.microsecond, v.fold, oid(v.tzinfo)]
    enctm = lambda v: [v.hour, v.minute, v.second, v.microsecond, v.fold, oid(v.tzinfo)]
    ymd = lambda v: [v.year, v.month, v.day]
    deltaenc = lambda t: None if t is None else [t.days, t.seconds, t.microseconds]

    def rich(a, b, op):
        return {"lt": lambda: a < b, "le": lambda: a <= b, "eq": lambda: a == b, "ne": lambda: a != b,
                "gt": lambda: a > b, "ge": lambda: a >= b}[op]()

    def state(x, proto):
        return list(x.__reduce_ex__(proto)[1][0])

    def hash_key(x, cands):
        h = hash(x)
        for tag, payload in cands:
            k = bytes(payload) if tag == "b" else (bytes(payload),) if tag == "t1" else tuple(payload)
            if hash(k) == h:
                return [tag, list(payload)]
        return ["nomatch"]

    def tm_cands(t):
        data = [t.hour, t.minute, t.second, t.microsecond >> 16, (t.microsecond >> 8) & 255, t.microsecond & 255]
        out = [("b", data)]
        o = t.replace(fold=0).utcoffset()
        if o is not None:
            d = m.timedelta(0, t.hour * 3600 + t.minute * 60 + t.second, t.microsecond) - o
            out.append(("i", [d.days, d.seconds, d.microseconds]))
            x = m.timedelta(hours=t.hour, minutes=t.minute) - o
            h, r = divmod(x, m.timedelta(hours=1))
            mm = r // m.timedelta(minutes=1)
            out.append(("i", [h, mm, t.second, t.microsecond]))
            if 0 <= h < 24:
                out.append(("b", [h, mm, t.second, t.microsecond >> 16, (t.microsecond >> 8) & 255, t.microsecond & 255]))
        return out

    def dt_cands(t):
        data = [t.year >> 8, t.year & 255, t.month, t.day, t.hour, t.minute, t.second,
                t.microsecond >> 16, (t.microsecond >> 8) & 255, t.microsecond & 255]
        out = [("b", data)]
        o = t.replace(fold=0).utcoffset()
        if o is not None:
            d = m.timedelta(t.toordinal(), t.hour * 3600 + t.minute * 60 + t.second, t.microsecond) - o
            out.append(("i", [d.days, d.seconds, d.microseconds]))
        return out

    def capture(thunk):
        rec = []

        def fake(fmt, tt=None):
            rec.append((fmt, list(tt)))
            return REAL_STRFTIME(fmt, tt) if fmt == "%G" else "X"

        time.strftime = fake
        try:
            thunk()
        finally:
            time.strftime = REAL_STRFTIME
        f, tt = rec[-1]
        return [[ord(x) for x in f], tt]

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
        return 1.5

    def kw(c, *names):
        return {py: c[k] for k, py in names if c.get(k) is not None}

    def thunk():
        if fn == "td_cmp": return rich(m.timedelta(*c["a"]), m.timedelta(*c["b"]), c["op"])
        if fn == "td_bool": return bool(m.timedelta(*c["a"]))
        if fn == "td_pos": return deltaenc(+m.timedelta(*c["a"]))
        if fn == "td_rsub": return deltaenc(m.timedelta(*c["a"]).__rsub__(m.timedelta(*c["b"])))
        if fn == "td_hash":
            a = m.timedelta(*c["a"])
            return hash_key(a, [("i", c["a"])])
        if fn == "td_state": return list(m.timedelta(*c["a"]).__reduce__()[1])
        if fn == "date_cmp": return rich(m.date(*c["a"]), m.date(*c["b"]), c["op"])
        if fn == "date_hash":
            a = c["a"]
            data = [a[0] >> 8, a[0] & 255, a[1], a[2]]
            return hash_key(m.date(*a), [("b", data), ("t1", data)])
        if fn == "date_weekday":
            d = m.date(*c["a"])
            return [d.weekday(), d.isoweekday()]
        if fn == "date_sub_date": return deltaenc(m.date(*c["a"]) - m.date(*c["b"]))
        if fn == "date_sub_delta": return ymd(m.date(*c["a"]) - m.timedelta(*c["td"]))
        if fn == "date_replace":
            return ymd(m.date(*c["a"]).replace(**kw(c, ("ny", "year"), ("nm", "month"), ("nd", "day"))))
        if fn == "date_timetuple": return list(m.date(*c["a"]).timetuple())
        if fn == "date_ctime": return m.date(*c["a"]).ctime()
        if fn == "date_repr": return repr(m.date(*c["a"]))
        if fn == "date_state": return state(m.date(*c["a"]), 2)
        if fn == "iso_repr": return repr(m.date(*c["a"]).isocalendar())
        if fn == "date_strftime":
            d = m.date(*c["a"])
            return capture(lambda: d.strftime("".join(map(chr, c["f"]))))
        if fn == "tz_str": return str(T(c["tz"]))
        if fn == "tz_repr": return repr(T(c["tz"]))
        if fn in ("tm_off", "dt_off"):
            t = mktm(c["t"]) if fn == "tm_off" else mkdt(c["t"])

            def tilde(r):
                if r.get("msg", "").startswith("offset must"):
                    r["msg"] = "offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24)"
                return r
            return [tilde(common.py_result(lambda: deltaenc(t.utcoffset()))), tilde(common.py_result(lambda: deltaenc(t.dst()))),
                    common.py_result(lambda: t.tzname())]
        if fn == "tm_cmp": return rich(mktm(c["a"]), mktm(c["b"]), c["op"])
        if fn == "tm_hash":
            t = mktm(c["a"])
            return hash_key(t, tm_cands(t))
        if fn == "tm_repr": return repr(mktm(c["a"]))
        if fn == "tm_iso": return mktm(c["a"]).isoformat(c["spec"])
        if fn == "tm_state": return state(mktm(c["a"]), c["proto"])
        if fn == "tm_strftime":
            t = mktm(c["a"])
            return capture(lambda: t.strftime("".join(map(chr, c["f"]))))
        if fn == "tm_replace":
            k = kw(c, ("nh", "hour"), ("nmi", "minute"), ("ns", "second"), ("nus", "microsecond"), ("nfold", "fold"))
            t = mktm(c["a"])
            if "tzarg" in c:
                k["tzinfo"] = T(c["tzarg"])
            return enctm(t.replace(**k))
        if fn == "dt_cmp": return rich(mkdt(c["a"]), mkdt(c["b"]), c["op"])
        if fn == "dt_hash":
            t = mkdt(c["a"])
            return hash_key(t, dt_cands(t))
        if fn == "dt_repr": return repr(mkdt(c["a"]))
        if fn == "dt_iso": return mkdt(c["a"]).isoformat(chr(c["sep"]), c["spec"])
        if fn == "dt_ctime": return mkdt(c["a"]).ctime()
        if fn == "dt_add": return encdt(mkdt(c["a"]) + m.timedelta(*c["td"]))
        if fn == "dt_sub_delta": return encdt(mkdt(c["a"]) - m.timedelta(*c["td"]))
        if fn == "dt_sub": return deltaenc(mkdt(c["a"]) - mkdt(c["b"]))
        if fn == "dt_timetuple": return list(mkdt(c["a"]).timetuple())
        if fn == "dt_utctimetuple": return list(mkdt(c["a"]).utctimetuple())
        if fn == "dt_parts":
            t = mkdt(c["a"])
            return [ymd(t.date()), enctm(t.time()), enctm(t.timetz())]
        if fn == "dt_combine":
            d, t = m.date(*c["ymd"]), mktm(c["t"])
            r = m.datetime.combine(d, t, T(c["tzarg"])) if "tzarg" in c else m.datetime.combine(d, t)
            return encdt(r)
        if fn == "dt_replace":
            k = kw(c, ("ny", "year"), ("nm", "month"), ("nd", "day"), ("nh", "hour"), ("nmi", "minute"),
                   ("ns", "second"), ("nus", "microsecond"), ("nfold", "fold"))
            t = mkdt(c["a"])
            if "tzarg" in c:
                k["tzinfo"] = T(c["tzarg"])
            return encdt(t.replace(**k))
        if fn == "dt_fromutc":
            a = mkdt(c["a"])
            return encdt(T(c["tz"]).fromutc(a))
        if fn == "dt_astimezone":
            a = mkdt(c["a"])
            tz = T(c["tz"])
            try:
                local_path = a.tzinfo is None or a.tzinfo.utcoffset(a) is None
            except Exception:
                local_path = False
            if local_path and not (impl == "c" and a.tzinfo is tz):
                return None
            return encdt(a.astimezone(tz))
        if fn == "dt_state": return state(mkdt(c["a"]), c["proto"])
        if fn == "dt_strftime":
            t = mkdt(c["a"])
            return capture(lambda: t.strftime("".join(map(chr, c["f"]))))
        if fn == "ctor_date": return ymd(m.date(*map(arg, c["args"])))
        if fn == "ctor_time":
            return enctm(m.time(*map(arg, c["args"]), fold=c["fold"]))
        if fn == "ctor_datetime":
            return encdt(m.datetime(*map(arg, c["args"]), fold=c["fold"]))
        raise AssertionError(fn)

    return common.py_result(thunk)


ISO_FNS = ["date_fromiso", "time_fromiso", "datetime_fromiso"]
OPS = ["add", "sub", "neg", "abs", "mul", "floordiv_int", "truediv_int", "floordiv", "mod", "divmod"]


def gen_case(rng):
    if rng.random() < 0.5:
        return gen_obj_case(rng)
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
    if c["fn"] in OBJ_FNS:
        return run_obj(c)
    if c["fn"] in MORE_FNS:
        return run_more(c)
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
