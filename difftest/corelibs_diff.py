"""Differential test for CoreLibs: Lean model vs the running CPython.

One section per area. `CORELIBS_AREA=coll,rand` restricts the run to those areas;
the default is every area that has a generator:
  scripts/r env CORELIBS_AREA=coll python3 difftest/corelibs_diff.py --cases 50000 --seed 1
"""

import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import main, py_result  # noqa: E402

# ====== BEGIN AREA coll (Lib/collections/__init__.py (everything except OrderedDict)) ======
# Everything for this area stays between these two markers; prefix top-level names with coll_.
coll_gen = None  # replace with def coll_gen(rng) -> case dict with "fn": "coll.<name>"
coll_run = None  # replace with def coll_run(case) -> common.py_result-style dict
# ====== END AREA coll ======

# ====== BEGIN AREA collabc (Lib/_collections_abc.py, Lib/collections/abc.py) ======
# Everything for this area stays between these two markers; prefix top-level names with collabc_.
collabc_gen = None  # replace with def collabc_gen(rng) -> case dict with "fn": "collabc.<name>"
collabc_run = None  # replace with def collabc_run(case) -> common.py_result-style dict
# ====== END AREA collabc ======

# ====== BEGIN AREA functools (Lib/functools.py, Modules/_functoolsmodule.c) ======
# Everything for this area stays between these two markers; prefix top-level names with functools_.
functools_gen = None  # replace with def functools_gen(rng) -> case dict with "fn": "functools.<name>"
functools_run = None  # replace with def functools_run(case) -> common.py_result-style dict
# ====== END AREA functools ======

# ====== BEGIN AREA operator (Lib/operator.py, Modules/_operator.c, Lib/copy.py, Lib/abc.py) ======
# Everything for this area stays between these two markers; prefix top-level names with operator_.
operator_gen = None  # replace with def operator_gen(rng) -> case dict with "fn": "operator.<name>"
operator_run = None  # replace with def operator_run(case) -> common.py_result-style dict
# ====== END AREA operator ======

# ====== BEGIN AREA enumdc (Lib/enum.py, Lib/dataclasses.py) ======
# Everything for this area stays between these two markers; prefix top-level names with enumdc_.
enumdc_gen = None  # replace with def enumdc_gen(rng) -> case dict with "fn": "enumdc.<name>"
enumdc_run = None  # replace with def enumdc_run(case) -> common.py_result-style dict
# ====== END AREA enumdc ======

# ====== BEGIN AREA misc (Lib/contextlib.py, Lib/numbers.py, Lib/keyword.py, Lib/types.py, Lib/weakref.py, Lib/graphlib.py, Lib/sched.py, Lib/queue.py) ======
# Everything for this area stays between these two markers; prefix top-level names with misc_.
misc_gen = None  # replace with def misc_gen(rng) -> case dict with "fn": "misc.<name>"
misc_run = None  # replace with def misc_run(case) -> common.py_result-style dict
# ====== END AREA misc ======

# ====== BEGIN AREA calstat (Lib/calendar.py, Lib/statistics.py) ======
# Everything for this area stays between these two markers; prefix top-level names with calstat_.
# --- calendar ---------------------------------------------------------------
import calendar as calstat_calendar
import contextlib as calstat_ctx
import datetime as calstat_dt
import io as calstat_io
import locale as calstat_locale
import os as calstat_os
import types as calstat_types
import warnings as calstat_warnings
import _colorize as calstat_colorize

calstat_YEARS = [0, 1, 2, 3, 4, -1, -2, -3, -4, 100, 400, -100, -400, 399, 401, 1582, 1900, 1970,
                 2000, 2001, 2023, 2024, 2100, 2400, 9996, 9998, 9999, 10000, 10001, 10400,
                 2 ** 31, -2 ** 31, 2 ** 63, -2 ** 63, 2 ** 64, -2 ** 64, 10 ** 30]
calstat_ANSI = calstat_types.SimpleNamespace(BLACK="\x1b[30m", BACKGROUND_YELLOW="\x1b[43m",
                                             RESET="\x1b[0m")
calstat_LOCALES = ["C", "C.utf8", "bogus_XX"]


def calstat_year(rng):
    r = rng.random()
    if r < 0.5:
        return rng.choice(calstat_YEARS)
    if r < 0.9:
        return rng.randint(-3000, 12000)
    return rng.randint(-10 ** 12, 10 ** 12)


def calstat_month(rng):
    r = rng.random()
    if r < 0.9:
        return rng.randint(1, 12)
    return rng.choice([0, 13, -1, -12, 100, 2 ** 31, -2 ** 31 - 1, 2 ** 63, -2 ** 64])


def calstat_fw(rng):
    r = rng.random()
    if r < 0.8:
        return rng.randint(0, 6)
    return rng.choice([-1, -6, -7, -8, 7, 8, 13, 14, 700, 2 ** 31, -2 ** 63, 2 ** 64 + 3])


def calstat_small(rng):
    return rng.choice([-3, -1, 0, 1, 2, 2, 3, 3, 4, 5, 6, 7, 9, 10, 12, 13, 15])


def calstat_week(rng):
    n = rng.choice([0, 1, 7, 7, 7, 3])
    return [[rng.choice([0, 0, 1, 9, 10, 28, 31, 100, -5]), rng.randint(0, 6)] for _ in range(n)]


def calstat_hl(rng, y, m):
    r = rng.random()
    if r < 0.2:
        return None
    if r < 0.7 and 1 <= y <= 9999 and isinstance(m, int) and 1 <= m <= 12:
        return [y, m, rng.randint(1, 28)]
    return [rng.randint(1, 9999), rng.randint(1, 12), rng.randint(1, 28)]


def calstat_ymfw(rng):
    return {"y": calstat_year(rng), "m": calstat_month(rng), "fw": calstat_fw(rng)}


def calstat_gen_cal(rng):
    k = rng.randrange(66)
    c = {}
    names = ["isleap", "leapdays", "weekday", "weekday", "monthrange", "monthrange", "_monthlen",
             "_prevmonth", "_nextmonth", "getfirstweekday", "iterweekdays", "itermonthdates",
             "itermonthdays", "itermonthdays2", "itermonthdays3", "itermonthdays4",
             "monthdatescalendar", "monthdays2calendar", "monthdayscalendar", "yeardatescalendar",
             "yeardays2calendar", "yeardayscalendar", "setfirstweekday", "exc_month", "exc_weekday",
             "__getattr__", "loc_get", "loc_slice", "loc_len", "formatstring", "format", "timegm",
             "t.formatday", "t.formatweek", "t.prweek", "t.formatweekday", "t.formatweekheader",
             "t.formatmonthname", "t.formatmonth", "t.prmonth", "t.formatyear", "t.pryear",
             "h.formatday", "h.formatweek", "h.formatweekday", "h.formatweekheader",
             "h.formatmonthname", "h.formatmonth", "h.formatyear", "h.formatyearpage",
             "l.default", "l.init", "l.enter_exit", "lt.formatweekday", "lt.formatmonthname",
             "lh.formatweekday", "lh.formatmonthname", "d.formatweek", "d.formatmonth",
             "d.formatmonth", "d.formatyear", "d.formatyear", "main", "main", "main", "main"]
    fn = names[k]
    c = calstat_ymfw(rng)
    if fn == "leapdays":
        c = {"a": calstat_year(rng), "b": calstat_year(rng)}
    elif fn == "weekday":
        c["d"] = rng.choice([1, 15, 28, 29, 30, 31, 0, 32, -1, 2 ** 31, -2 ** 31 - 1, 2 ** 63,
                             rng.randint(1, 31)])
    elif fn in ("yeardatescalendar", "yeardays2calendar", "yeardayscalendar", "h.formatyear",
                "h.formatyearpage"):
        c["y"] = rng.choice([calstat_year(rng), rng.randint(1, 9999), 1, 9999])
        c["width"] = calstat_small(rng)
        if fn == "h.formatyearpage":
            c["css"] = rng.choice([None, "calendar.css", "a&b.css", "café.css", "€.css"])
            c["encoding"] = rng.choice([None, "utf-8", "ascii", "latin-1", "nope"])
    elif fn in ("exc_month", "exc_weekday"):
        c = {"m": rng.choice([0, 13, -1, 7, 2 ** 70])}
    elif fn == "__getattr__":
        c = {"name": rng.choice(["January", "February", "March", "xyz"])}
    elif fn in ("loc_get", "loc_slice", "loc_len"):
        c = {"table": rng.choice(["day_name", "day_abbr", "month_name", "month_abbr"]),
             "i": rng.randint(-15, 15), "start": rng.choice([None, 0, 1, -1, 5, 20, -20]),
             "stop": rng.choice([None, 0, 3, -2, 20, -20]), "step": rng.choice([1, 1, 2, -1, -3, 0])}
    elif fn in ("formatstring", "format"):
        c = {"cols": [rng.choice(["", "a", "abc", "January", "12345678"])
                      for _ in range(rng.randint(0, 4))],
             "colwidth": calstat_small(rng), "spacing": calstat_small(rng)}
    elif fn == "timegm":
        c = {"t": [rng.choice([1970, 1, 9999, 0, 10000, 2000, 2024, rng.randint(1, 9999)]),
                   calstat_month(rng), rng.randint(-40, 400), rng.randint(-30, 30),
                   rng.randint(-100, 100), rng.randint(-100, 100), 1, 2, 3]}
    elif fn == "t.formatday":
        c = {"d": rng.choice([0, 1, 9, 10, 31, -5, 100]), "wd": rng.randint(0, 6),
             "width": calstat_small(rng)}
    elif fn in ("t.formatweek", "t.prweek"):
        c = {"week": calstat_week(rng), "width": calstat_small(rng)}
    elif fn == "t.formatweekday":
        c = {"d": rng.randint(-9, 9), "width": calstat_small(rng)}
    elif fn == "t.formatweekheader":
        c["width"] = calstat_small(rng)
    elif fn == "t.formatmonthname":
        c["width"] = calstat_small(rng) * 3
        c["withyear"] = rng.random() < 0.7
    elif fn in ("t.formatmonth", "t.prmonth", "d.formatmonth"):
        c["w"] = calstat_small(rng)
        c["l"] = rng.choice([-1, 0, 1, 2, 3])
    elif fn in ("t.formatyear", "t.pryear", "d.formatyear"):
        c["w"] = calstat_small(rng)
        c["l"] = rng.choice([-1, 0, 1, 2])
        c["c"] = calstat_small(rng)
        c["m"] = rng.choice([-1, 0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 3, 3])
    elif fn == "h.formatday":
        c = {"d": rng.choice([0, 1, 31, -5]), "wd": rng.randint(-9, 9)}
    elif fn == "h.formatweek":
        c = {"week": calstat_week(rng)}
    elif fn == "h.formatweekday":
        c = {"d": rng.randint(-9, 9)}
    elif fn in ("h.formatmonthname", "h.formatmonth"):
        c["withyear"] = rng.random() < 0.7
    elif fn in ("l.default", "l.init", "l.enter_exit"):
        c = {"cur": rng.choice(["C", "C.utf8"]), "user": rng.choice(["C", "C.utf8", "bogus_XX"]),
             "locale": rng.choice(calstat_LOCALES + [""])}
        if fn == "l.init" and rng.random() < 0.5:
            c["locale"] = None
    elif fn in ("lt.formatweekday", "lh.formatweekday"):
        c = {"d": rng.randint(-9, 9), "width": calstat_small(rng),
             "locale": rng.choice(calstat_LOCALES)}
    elif fn in ("lt.formatmonthname", "lh.formatmonthname"):
        c["width"] = calstat_small(rng) * 3
        c["withyear"] = rng.random() < 0.7
        c["locale"] = rng.choice(calstat_LOCALES)
    elif fn == "d.formatweek":
        c = {"week": calstat_week(rng), "width": calstat_small(rng),
             "hd": rng.choice([None, 0, 1, 9, 31])}
    elif fn == "main":
        c = {"width": rng.choice([2, 2, 3, 0, -1, 5]), "lines": rng.choice([1, 1, 2, 0, -1]),
             "spacing": rng.choice([6, 6, 0, 1, 3, -2]), "months": rng.choice([3, 3, 1, 2, 4, 0, -1, 12]),
             "css": rng.choice(["calendar.css", "x.css", "café.css"]),
             "locale": rng.choice([None, None, None, "", "C"]),
             "encoding": rng.choice([None, None, "utf-8", "ascii", "latin-1", "nope"]),
             "type": rng.choice(["text", "text", "html"]), "fw": rng.choice([0, 0, 6, 1, 7, -1, 9]),
             "year": rng.choice([None, 2000, 2024, rng.randint(1, 9999), 0, 10000, 9999, 1]),
             "today": [rng.choice([2024, 2000, rng.randint(1, 9999)]), rng.randint(1, 12),
                       rng.randint(1, 28)]}
        c["month"] = None if c["year"] is None or rng.random() < 0.4 else rng.choice(
            [0, 13, -1, rng.randint(1, 12), rng.randint(1, 12), rng.randint(1, 12)])
        if c["locale"] == "C" and c["encoding"] is not None:
            c["encoding"] = "utf-8"
    c["fn"] = "calstat." + fn
    if "fw" not in c:
        c["fw"] = calstat_fw(rng)
    return c


def calstat_lists(v):
    if isinstance(v, (list, tuple)):
        return [calstat_lists(x) for x in v]
    if isinstance(v, calstat_dt.date):
        return [v.year, v.month, v.day]
    if isinstance(v, int) and not isinstance(v, bool):
        return int(v)
    return v


def calstat_out(f):
    buf = calstat_io.StringIO()
    with calstat_ctx.redirect_stdout(buf):
        f()
    return buf.getvalue()


class calstat_Stop(Exception):
    pass


def calstat_main(c):
    args = [f"--width={c['width']}", f"--lines={c['lines']}", f"--spacing={c['spacing']}",
            f"--months={c['months']}", f"--css={c['css']}", f"--type={c['type']}",
            f"--first-weekday={c['fw']}"]
    if c["locale"] is not None:
        args.append(f"--locale={c['locale']}")
    if c["encoding"] is not None:
        args.append(f"--encoding={c['encoding']}")
    if c["year"] is not None:
        args.append(f"--")
        args.append(str(c["year"]))
        if c["month"] is not None:
            args.append(str(c["month"]))
    today = c["today"]

    class D(calstat_dt.date):
        @classmethod
        def today(cls):
            return cls(*today)
    saved = calstat_calendar.datetime
    calstat_calendar.datetime = calstat_types.SimpleNamespace(
        date=D, MINYEAR=calstat_dt.MINYEAR, MAXYEAR=calstat_dt.MAXYEAR)
    raw = calstat_io.BytesIO()
    out = calstat_io.TextIOWrapper(raw, encoding="utf-8", write_through=True)
    try:
        with calstat_ctx.redirect_stdout(out), calstat_ctx.redirect_stderr(calstat_io.StringIO()):
            try:
                calstat_calendar.main(args)
            except SystemExit as e:
                raise calstat_Stop(str(e.code))
    finally:
        calstat_calendar.datetime = saved
    return raw.getvalue().decode("latin-1")


def calstat_table(c):
    return getattr(calstat_calendar, c["table"])


def calstat_with_locale(c, f):
    calstat_os.environ["LC_ALL"] = c["user"]
    calstat_locale.setlocale(calstat_locale.LC_TIME, c["cur"])
    try:
        return f()
    finally:
        calstat_locale.setlocale(calstat_locale.LC_TIME, "C")


def calstat_enter_exit(c):
    cur = c["cur"]

    def body():
        d = calstat_calendar.different_locale(c["locale"])
        d.__enter__()
        try:
            inner = calstat_locale.setlocale(calstat_locale.LC_TIME, None)
        finally:
            d.__exit__()
        return [inner, calstat_locale.setlocale(calstat_locale.LC_TIME, None)]
    return calstat_with_locale(c, body)


def calstat_run_cal_inner(c, fn):
    cal = calstat_calendar
    C = cal.Calendar(c["fw"])
    T = cal.TextCalendar(c["fw"])
    H = cal.HTMLCalendar(c["fw"])
    y, m = c.get("y"), c.get("m")
    if fn == "isleap":
        return bool(cal.isleap(y))
    if fn == "leapdays":
        return cal.leapdays(c["a"], c["b"])
    if fn == "weekday":
        return cal.weekday(y, m, c["d"])
    if fn == "monthrange":
        return list(cal.monthrange(y, m))
    if fn == "_monthlen":
        return cal._monthlen(y, m)
    if fn == "_prevmonth":
        return list(cal._prevmonth(y, m))
    if fn == "_nextmonth":
        return list(cal._nextmonth(y, m))
    if fn == "getfirstweekday":
        return C.getfirstweekday()
    if fn == "iterweekdays":
        return list(C.iterweekdays())
    if fn == "itermonthdates":
        return list(C.itermonthdates(y, m))
    if fn == "itermonthdays":
        return list(C.itermonthdays(y, m))
    if fn == "itermonthdays2":
        return list(C.itermonthdays2(y, m))
    if fn == "itermonthdays3":
        return list(C.itermonthdays3(y, m))
    if fn == "itermonthdays4":
        return list(C.itermonthdays4(y, m))
    if fn in ("monthdatescalendar", "monthdays2calendar", "monthdayscalendar"):
        return getattr(C, fn)(y, m)
    if fn in ("yeardatescalendar", "yeardays2calendar", "yeardayscalendar"):
        return getattr(C, fn)(y, c["width"])
    if fn == "setfirstweekday":
        old = cal.firstweekday()
        try:
            cal.setfirstweekday(c["fw"])
            return cal.firstweekday()
        finally:
            cal.c.firstweekday = old
    if fn == "exc_month":
        return {"msg": str(cal.IllegalMonthError(m))}
    if fn == "exc_weekday":
        return {"msg": str(cal.IllegalWeekdayError(m))}
    if fn == "__getattr__":
        with calstat_warnings.catch_warnings(record=True) as w:
            calstat_warnings.simplefilter("always")
            v = getattr(cal, c["name"])
        return [v, str(w[0].message)]
    if fn == "loc_get":
        return calstat_table(c)[c["i"]]
    if fn == "loc_slice":
        return calstat_table(c)[c["start"]:c["stop"]:c["step"]]
    if fn == "loc_len":
        return len(calstat_table(c))
    if fn == "formatstring":
        return cal.formatstring(c["cols"], c["colwidth"], c["spacing"])
    if fn == "format":
        return calstat_out(lambda: cal.format(c["cols"], c["colwidth"], c["spacing"]))
    if fn == "timegm":
        return cal.timegm(tuple(c["t"]))
    if fn == "t.formatday":
        return T.formatday(c["d"], c["wd"], c["width"])
    if fn == "t.formatweek":
        return T.formatweek(c["week"], c["width"])
    if fn == "t.prweek":
        return calstat_out(lambda: T.prweek(c["week"], c["width"]))
    if fn == "t.formatweekday":
        return T.formatweekday(c["d"], c["width"])
    if fn == "t.formatweekheader":
        return T.formatweekheader(c["width"])
    if fn == "t.formatmonthname":
        return T.formatmonthname(y, m, c["width"], c["withyear"])
    if fn == "t.formatmonth":
        return T.formatmonth(y, m, c["w"], c["l"])
    if fn == "t.prmonth":
        return calstat_out(lambda: T.prmonth(y, m, c["w"], c["l"]))
    if fn == "t.formatyear":
        return T.formatyear(y, c["w"], c["l"], c["c"], c["m"])
    if fn == "t.pryear":
        return calstat_out(lambda: T.pryear(y, c["w"], c["l"], c["c"], c["m"]))
    if fn == "h.formatday":
        return H.formatday(c["d"], c["wd"])
    if fn == "h.formatweek":
        return H.formatweek(c["week"])
    if fn == "h.formatweekday":
        return H.formatweekday(c["d"])
    if fn == "h.formatweekheader":
        return H.formatweekheader()
    if fn == "h.formatmonthname":
        return H.formatmonthname(y, m, c["withyear"])
    if fn == "h.formatmonth":
        return H.formatmonth(y, m, c["withyear"])
    if fn == "h.formatyear":
        return H.formatyear(y, c["width"])
    if fn == "h.formatyearpage":
        return H.formatyearpage(y, c["width"], c["css"], c["encoding"]).decode("latin-1")
    if fn == "l.default":
        return calstat_with_locale(c, cal._get_default_locale)
    if fn == "l.init":
        return calstat_with_locale(c, lambda: cal.LocaleTextCalendar(0, c["locale"]).locale)
    if fn == "l.enter_exit":
        return calstat_enter_exit(c)
    if fn == "lt.formatweekday":
        return cal.LocaleTextCalendar(0, c["locale"]).formatweekday(c["d"], c["width"])
    if fn == "lt.formatmonthname":
        return cal.LocaleTextCalendar(0, c["locale"]).formatmonthname(y, m, c["width"], c["withyear"])
    if fn == "lh.formatweekday":
        return cal.LocaleHTMLCalendar(0, c["locale"]).formatweekday(c["d"])
    if fn == "lh.formatmonthname":
        return cal.LocaleHTMLCalendar(0, c["locale"]).formatmonthname(y, m, c["withyear"])
    if fn == "d.formatweek":
        return cal._CLIDemoCalendar(None).formatweek(c["week"], c["width"], highlight_day=c["hd"])
    if fn in ("d.formatmonth", "d.formatyear"):
        hl = c.get("hl")
        d = cal._CLIDemoCalendar(calstat_dt.date(*hl) if hl else None, c["fw"])
        if fn == "d.formatmonth":
            return d.formatmonth(y, m, c["w"], c["l"])
        return d.formatyear(y, c["w"], c["l"], c["c"], c["m"])
    if fn == "main":
        return calstat_main(c)
    raise KeyError(fn)


def calstat_run_cal(c):
    fn = c["fn"].split(".", 1)[1]
    saved = calstat_colorize.get_colors
    calstat_colorize.get_colors = lambda **k: calstat_ANSI

    def thunk():
        return calstat_lists(calstat_run_cal_inner(c, fn))
    try:
        r = py_result(thunk)
    except BaseException:
        raise
    finally:
        calstat_colorize.get_colors = saved
    if r.get("exc") == "calstat_Stop":
        r["exc"] = "SystemExit"
    return r


calstat_locale.setlocale(calstat_locale.LC_TIME, "C")

# --- statistics -------------------------------------------------------------
import enum as calstat_enum
import math as calstat_math
import random as calstat_random
import statistics as calstat_st
from decimal import Decimal as calstat_D
from fractions import Fraction as calstat_F


class calstat_MyInt(int):
    pass


class calstat_MyFloat(float):
    pass


class calstat_MyFrac(calstat_F):
    pass


class calstat_MyDec(calstat_D):
    pass


class calstat_Lvl(calstat_enum.IntEnum):
    LOW = 1
    MID = 2
    HIGH = 3
    TOP = 5


class calstat_Abc:
    def __init__(self, n, d):
        self.numerator, self.denominator = n, d


calstat_USER_CLASSES = {
    "MyInt": (calstat_MyInt, ["MyInt", "int"], None),
    "MyFloat": (calstat_MyFloat, ["MyFloat", "float"], None),
    "MyFrac": (calstat_MyFrac, ["MyFrac", "Fraction"], None),
    "MyDec": (calstat_MyDec, ["MyDec", "Decimal"], None),
    "Lvl": (calstat_Lvl, ["Lvl", "IntEnum", "int"], [1, 2, 3, 5]),
}


for calstat_k, calstat_v in calstat_USER_CLASSES.items():
    calstat_v[0].__name__ = calstat_k


def calstat_ratio_str(x):
    n, d = x.as_integer_ratio()
    return f"{n}/{d}"


def calstat_fstr(x):
    if x != x:
        return "nan"
    if x in (calstat_math.inf, -calstat_math.inf):
        return "inf" if x > 0 else "-inf"
    if x == 0:
        return "-0" if calstat_math.copysign(1.0, x) < 0 else "0"
    return calstat_ratio_str(float(x))


def calstat_dstr(x):
    if x.is_snan():
        return "snan"
    if x.is_nan():
        return "nan"
    if x.is_infinite():
        return "inf" if x > 0 else "-inf"
    return calstat_ratio_str(x)


def calstat_enc(x):
    """Encode a Python value the way the Lean handler prints one."""
    if isinstance(x, bool):
        return "i:" + str(int(x))
    if isinstance(x, int):
        return "i:" + str(int(x))
    if isinstance(x, float):
        return "f:" + calstat_fstr(x)
    if isinstance(x, calstat_F):
        return "q:" + calstat_ratio_str(x)
    if isinstance(x, calstat_D):
        return "d:" + calstat_dstr(x)
    if isinstance(x, str):
        return "s:" + x
    if x is None:
        return "n:"
    return "o:" + type(x).__name__


def calstat_res(x):
    return [type(x).__name__, calstat_enc(x)]


def calstat_spec(x):
    """The JSON spec of a value for the case; bool keeps its class."""
    if isinstance(x, bool):
        return "b:" + str(int(x))
    return calstat_enc(x)


def calstat_obj(spec):
    """Build the Python object of a spec."""
    if isinstance(spec, dict):
        base = calstat_obj(spec["v"])
        return calstat_USER_CLASSES[spec["c"]][0](base)
    tag, body = spec[:2], spec[2:]
    if tag == "i:":
        return int(body)
    if tag == "b:":
        return body == "1"
    if tag == "q:":
        return calstat_F(body)
    if tag == "f:":
        if body in ("nan", "inf", "-inf"):
            return float(body)
        if body == "0":
            return 0.0
        if body == "-0":
            return -0.0
        n, d = body.split("/")
        return float(calstat_F(int(n), int(d)))
    if tag == "d:":
        if body == "nan":
            return calstat_D("NaN")
        if body == "snan":
            return calstat_D("sNaN")
        if body == "inf":
            return calstat_D("Infinity")
        if body == "-inf":
            return calstat_D("-Infinity")
        n, d = body.split("/")
        # value-exact construction of a terminating decimal
        with calstat_D_ctx():
            return calstat_D(int(n)) / calstat_D(int(d))
    if tag == "s:":
        return body
    if tag == "n:":
        return None
    if tag == "a:":
        n, d = body.split("/")
        return calstat_Abc(int(n), int(d))
    raise KeyError(spec)


def calstat_D_ctx():
    import decimal
    ctx = decimal.Context(prec=400)
    return decimal.localcontext(ctx)


def calstat_user(name, spec):
    cls, mro, members = calstat_USER_CLASSES[name]
    return {"c": name, "mro": mro, "m": members, "v": spec}


calstat_FLOATS = [0.0, -0.0, 1.0, -1.0, 0.5, 0.25, 1.5, 2.0, 3.0, 0.1, 0.2, 0.3, 1e-3, 1e10, 1e16, 2.0 ** 53,
                  1e308, -1e308, 1.7976931348623157e308, 5e-324, 2.2250738585072014e-308, 1e-300, 1e300]
calstat_INTS = [0, 1, -1, 2, 3, 4, 5, 7, 10, -3, 100, 2 ** 31, 2 ** 53 + 1, 2 ** 63, -2 ** 63, 2 ** 64,
                10 ** 30, 10 ** 400, -10 ** 400]


def calstat_float(rng):
    r = rng.random()
    if r < 0.45:
        return rng.choice(calstat_FLOATS)
    if r < 0.8:
        return rng.uniform(-10, 10)
    return rng.uniform(-1, 1) * 10.0 ** rng.randint(-300, 300)


def calstat_int(rng):
    return rng.choice(calstat_INTS) if rng.random() < 0.3 else rng.randint(-20, 20)


def calstat_frac(rng):
    return calstat_F(rng.randint(-30, 30), rng.randint(1, 12))


def calstat_dec(rng):
    return calstat_D(rng.randint(-2000, 2000)).scaleb(-rng.randint(0, 4))


def calstat_value_spec(rng, kind):
    if kind == "int":
        return calstat_spec(calstat_int(rng))
    if kind == "smallint":
        return calstat_spec(rng.randint(-6, 9))
    if kind == "posint":
        return calstat_spec(rng.randint(1, 30))
    if kind == "bool":
        return calstat_spec(rng.random() < 0.5)
    if kind == "float":
        return calstat_spec(calstat_float(rng))
    if kind == "unitfloat":
        return calstat_spec(rng.uniform(-3, 3))
    if kind == "posfloat":
        return calstat_spec(rng.uniform(0.001, 50))
    if kind == "frac":
        return calstat_spec(calstat_frac(rng))
    if kind == "posfrac":
        return calstat_spec(calstat_F(rng.randint(1, 30), rng.randint(1, 12)))
    if kind == "dec":
        return calstat_spec(calstat_dec(rng))
    if kind == "specialf":
        return calstat_spec(rng.choice([calstat_math.inf, -calstat_math.inf, float("nan")]))
    if kind == "speciald":
        return "d:" + rng.choice(["nan", "inf", "-inf", "snan"])
    if kind == "str":
        return "s:" + rng.choice(["red", "blue", "x"])
    if kind == "none":
        return "n:"
    if kind == "myint":
        return calstat_user("MyInt", calstat_spec(rng.randint(-9, 9)))
    if kind == "myfloat":
        return calstat_user("MyFloat", calstat_spec(rng.uniform(-9, 9)))
    if kind == "myfrac":
        return calstat_user("MyFrac", calstat_spec(calstat_frac(rng)))
    if kind == "mydec":
        return calstat_user("MyDec", calstat_spec(calstat_dec(rng)))
    if kind == "lvl":
        return calstat_user("Lvl", calstat_spec(rng.choice([1, 2, 3, 5])))
    raise KeyError(kind)


calstat_MIXES = [["smallint"], ["smallint"], ["int"], ["posint"], ["float"], ["unitfloat"], ["unitfloat"],
                 ["posfloat"], ["frac"], ["frac"], ["posfrac"], ["dec"], ["smallint", "frac"], ["smallint", "float"],
                 ["frac", "unitfloat"], ["smallint", "dec"], ["bool", "smallint"], ["bool"], ["myint"],
                 ["myint", "smallint"], ["myfloat", "unitfloat"], ["myfrac", "frac"], ["mydec", "dec"], ["lvl"],
                 ["unitfloat", "specialf"], ["dec", "speciald"], ["frac", "dec"], ["unitfloat", "dec"],
                 ["smallint", "str"], ["str"], ["none", "smallint"], ["myfloat", "myint"], ["myint", "frac"]]


def calstat_data(rng, mixes=calstat_MIXES, maxn=9):
    mix = rng.choice(mixes)
    n = rng.choice([0, 1, 2, 2, 3, 3, 4, 5, 6, 7, maxn])
    return [calstat_value_spec(rng, rng.choice(mix)) for _ in range(n)]


calstat_NUMMIX = [["smallint"], ["int"], ["posint"], ["float"], ["unitfloat"], ["unitfloat"], ["posfloat"], ["frac"],
                  ["posfrac"], ["smallint", "frac"], ["smallint", "unitfloat"], ["bool", "smallint"],
                  ["unitfloat", "specialf"]]
calstat_SIMPLE = [["smallint"], ["int"], ["float"], ["unitfloat"], ["unitfloat"], ["frac"], ["dec"],
                  ["smallint", "frac"], ["smallint", "unitfloat"], ["frac", "unitfloat"], ["bool", "smallint"],
                  ["unitfloat", "specialf"], ["str"], ["none", "smallint"], ["myint"], ["myfloat"]]
calstat_KERNELS = ["normal", "gauss", "logistic", "sigmoid", "rectangular", "uniform", "triangular", "parabolic",
                   "epanechnikov", "quartic", "biweight", "triweight", "cosine"]
calstat_ERFC_NAMES = ("erfc",)


def calstat_nd(rng):
    mu = rng.choice([0.0, 1.0, -2.5, rng.uniform(-10, 10), 1e300, 0.1])
    sigma = rng.choice([1.0, 0.5, 2.0, 0.0, rng.uniform(0.01, 10), 3.0, 1e-300])
    return [calstat_fstr(mu), calstat_fstr(sigma)]


def calstat_ndobj(l):
    return calstat_st.NormalDist(calstat_obj("f:" + l[0]), calstat_obj("f:" + l[1]))


def calstat_const(rng):
    return calstat_value_spec(rng, rng.choice(["smallint", "unitfloat", "frac", "float", "bool"]))


def calstat_gen_stat(rng):
    fns = ["s._exact_ratio", "s._isfinite", "s._coerce", "s._sum", "s._ss", "s._ss", "s._convert", "s._fail_neg", "s._rank", "s._rank",
           "s._integer_sqrt_of_frac_rto", "s._float_sqrt_of_frac", "s._float_sqrt_of_frac",
           "s._decimal_sqrt_of_frac", "s._mean_stdev", "s._sqrtprod",
           "s.mean", "s.mean", "s.fmean", "s.fmean", "s.geometric_mean", "s.harmonic_mean", "s.harmonic_mean", "s.median", "s.median_low",
           "s.median_high", "s.median_grouped", "s.mode", "s.multimode", "s.variance", "s.variance", "s.pvariance",
           "s.stdev", "s.pstdev", "s.covariance", "s.correlation", "s.correlation", "s.linear_regression",
           "s.linear_regression", "s.quantiles", "s.quantiles", "s.kde", "s.kde", "s.kde_random", "s.kernel", "s.kernel",
           "s.nd.init", "s.nd.from_samples", "s.nd.samples", "s.nd.pdf", "s.nd.cdf", "s.nd.inv_cdf",
           "s.nd.quantiles", "s.nd.overlap", "s.nd.zscore", "s.nd.props", "s.nd.add", "s.nd.sub", "s.nd.addc",
           "s.nd.subc", "s.nd.mulc", "s.nd.divc", "s.nd.rsubc", "s.nd.pos", "s.nd.neg", "s.nd.eq", "s.nd.hash",
           "s.nd.repr", "s.nd.state"]
    fn = rng.choice(fns)
    c = {}
    if fn == "s._isfinite":
        c["x"] = calstat_value_spec(rng, rng.choice(["int", "float", "frac", "dec", "bool", "specialf", "speciald", "str", "none"]))
    elif fn == "s._exact_ratio":
        kind = rng.choice(["smallint", "float", "frac", "dec", "bool", "specialf", "speciald", "str", "none"])
        c["x"] = calstat_value_spec(rng, kind)
        if rng.random() < 0.1:
            c["x"] = f"a:{rng.randint(-9, 9)}/{rng.randint(1, 9)}"
    elif fn == "s._coerce":
        names = ["int", "bool", "float", "Fraction", "Decimal", "MyInt", "MyFloat", "MyFrac", "MyDec"]
        pick2 = [rng.choice(names), rng.choice(names)]
        c["T"], c["S"] = [calstat_cls_spec(n) for n in pick2]
    elif fn == "s._sum":
        c["data"] = calstat_data(rng)
    elif fn == "s._ss":
        c["data"] = calstat_data(rng)
        c["c"] = None
        if rng.random() < 0.4:
            c["c"] = calstat_value_spec(rng, rng.choice(["smallint", "frac", "unitfloat", "dec"]))
    elif fn == "s._convert":
        c["T"] = calstat_cls_spec(rng.choice(["int", "float", "Fraction", "Decimal", "MyInt", "MyFloat", "MyFrac", "Lvl"]))
        c["x"] = calstat_spec(calstat_F(rng.randint(-9, 9), rng.choice([1, 1, 2, 3])))
    elif fn == "s._fail_neg":
        c["data"] = calstat_data(rng, [["smallint"], ["frac"], ["unitfloat"]])
    elif fn == "s._rank":
        c["data"] = calstat_data(rng, [["smallint"], ["unitfloat"], ["frac"], ["smallint", "frac"],
                                       ["unitfloat", "specialf"], ["str"]], 12)
        c["reverse"] = rng.random() < 0.3
        c["ties"] = rng.choice(["average", "average", "average", "min"])
        c["start"] = calstat_spec(rng.choice([1, 0, 2, -1.5, 0.5, 1.0]))
    elif fn == "s._integer_sqrt_of_frac_rto":
        c["n"] = rng.choice([0, 1, 2, 3, 4, 15, 16, 17, rng.randint(0, 10 ** 30), 10 ** 40])
        c["m"] = rng.choice([1, 1, 2, 3, 4, rng.randint(1, 10 ** 10)])
    elif fn == "s._float_sqrt_of_frac":
        c["n"] = rng.choice([0, 1, 2, 3, rng.randint(1, 10 ** 30), rng.randint(1, 10 ** 700), 2 ** 2100])
        c["m"] = rng.choice([1, 2, 3, rng.randint(1, 10 ** 30), rng.randint(1, 10 ** 700)])
    elif fn == "s._decimal_sqrt_of_frac":
        c["n"] = rng.choice([0, 1, 2, 3, rng.randint(1, 10 ** 30), rng.randint(1, 10 ** 60), -rng.randint(1, 100)])
        c["m"] = rng.choice([1, 2, 3, rng.randint(1, 10 ** 30)])
        if c["n"] < 0:
            c["m"] = -c["m"]
    elif fn == "s._mean_stdev":
        c["data"] = calstat_data(rng, calstat_NUMMIX)
    elif fn == "s._sqrtprod":
        pool = [0.0, 1.0, 2.0, 1e308, 1e-308, 5e-324, 1e200, 1e-200, 3.0, calstat_math.inf, float("nan")]
        c["x"] = calstat_fstr(rng.choice(pool + [rng.uniform(0, 10)]))
        c["y"] = calstat_fstr(rng.choice(pool + [rng.uniform(0, 10)]))
    elif fn in ("s.mean", "s.variance", "s.pvariance", "s.stdev", "s.pstdev"):
        c["data"] = calstat_data(rng)
        if fn != "s.mean":
            c["c"] = None
            if rng.random() < 0.3:
                c["c"] = calstat_value_spec(rng, rng.choice(["smallint", "frac", "unitfloat", "dec"]))
    elif fn == "s.fmean":
        c["data"] = calstat_data(rng, calstat_NUMMIX)
        c["weights"] = None
        c["iter"] = rng.random() < 0.3
        if rng.random() < 0.5:
            n = len(c["data"]) if rng.random() < 0.9 else rng.randint(0, 4)
            c["weights"] = [calstat_value_spec(rng, rng.choice(["smallint", "unitfloat", "frac"])) for _ in range(n)]
    elif fn == "s.geometric_mean":
        c["data"] = calstat_data(rng, [["posint"], ["posfloat"], ["posfrac"], ["posint", "posfrac"], ["smallint"], ["unitfloat"],
                                       ["posfloat", "specialf"], ["int"], ["float"], ["none"]])
    elif fn == "s.harmonic_mean":
        mix = rng.choice([["posint"], ["posint"], ["smallint"], ["posfloat"], ["posfrac"], ["frac"], ["dec"], ["posfrac", "posint"],
                          ["float"], ["unitfloat", "specialf"], ["str"]])
        c["data"] = calstat_data(rng, [mix])
        c["weights"] = None
        if rng.random() < 0.5:
            n = len(c["data"]) if rng.random() < 0.9 else rng.randint(0, 4)
            wmix = rng.choice([["posint"], ["smallint"], ["posfrac"], ["posfloat"]])
            c["weights"] = [calstat_value_spec(rng, rng.choice(wmix)) for _ in range(n)]
    elif fn in ("s.median", "s.median_low", "s.median_high"):
        c["data"] = calstat_data(rng, calstat_SIMPLE + [["dec"], ["unitfloat", "specialf"]], 12)
    elif fn == "s.median_grouped":
        c["data"] = calstat_data(rng, [["smallint"], ["unitfloat"], ["frac"], ["smallint", "unitfloat"], ["unitfloat", "specialf"]], 12)
        c["interval"] = rng.choice(["f:1/1", "i:1", "i:2", "i:10", "f:1/2", "q:1/3", "s:abc", "n:", "f:0", "i:0"])
    elif fn in ("s.mode", "s.multimode"):
        c["data"] = calstat_data(rng, [["smallint"], ["bool", "smallint"], ["str"], ["smallint", "frac"], ["smallint", "str"]], 14)
        if rng.random() < 0.5:
            c["data"] = [calstat_value_spec(rng, "bool") if rng.random() < 0.5 else calstat_spec(rng.randint(0, 3))
                         for _ in range(rng.randint(0, 10))]
    elif fn in ("s.covariance", "s.correlation", "s.linear_regression"):
        mix = rng.choice([["smallint"], ["unitfloat"], ["posfloat"], ["frac"], ["smallint", "unitfloat"], ["float"], ["int"],
                          ["unitfloat", "specialf"], ["dec"]])
        c["x"] = calstat_data(rng, [mix])
        n = len(c["x"]) if rng.random() < 0.93 else rng.randint(0, 5)
        c["y"] = [calstat_value_spec(rng, rng.choice(mix)) for _ in range(n)]
        if rng.random() < 0.2 and c["x"]:
            c["x"] = [c["x"][0]] * len(c["x"])
        if fn == "s.correlation":
            c["method"] = rng.choice(["linear", "linear", "ranked", "ranked", "bogus"])
        if fn == "s.linear_regression":
            c["proportional"] = rng.random() < 0.4
    elif fn == "s.quantiles":
        c["data"] = calstat_data(rng, calstat_NUMMIX + [["str"], ["dec"]], 12)
        c["n"] = rng.choice([1, 2, 3, 4, 4, 5, 7, 10, 20, 0, -1])
        c["method"] = rng.choice(["exclusive", "exclusive", "inclusive", "inclusive", "bogus"])
    elif fn in ("s.kde", "s.kde_random"):
        mix = rng.choice([["smallint"], ["unitfloat"], ["smallint", "unitfloat"], ["frac"]])
        c["data"] = calstat_data(rng, [mix])
        c["h"] = calstat_spec(rng.choice([1, 1.5, 0.5, 2, 0, -1, 0.25, 3.0]))
        c["kernel"] = rng.choice(calstat_KERNELS + ["bogus"])
        if fn == "s.kde":
            c["cumulative"] = rng.random() < 0.5
            c["x"] = calstat_spec(rng.choice([0, 1, -1, 0.5, rng.uniform(-6, 6), rng.uniform(-6, 6), 100.0, -100.0]))
            c["data2"] = list(c["data"])
            if rng.random() < 0.15 and c["data2"]:
                c["data2"].append(calstat_spec(rng.randint(-3, 3)))
        else:
            c["draws"] = [[rng.randrange(max(len(c["data"]), 1)), calstat_fstr(rng.random())]
                          for _ in range(rng.randint(0, 3))]
    elif fn == "s.kernel":
        c["kernel"] = rng.choice(calstat_KERNELS)
        c["which"] = rng.choice(["pdf", "cdf", "invcdf"])
        if c["which"] == "invcdf":
            c["t"] = calstat_fstr(rng.choice([0.5, 0.25, 0.75, 0.1, 0.9, 1e-3, 0.999, 0.0106, 0.499, rng.uniform(0.0001, 0.9999)]))
        else:
            c["t"] = calstat_fstr(rng.choice([0.0, -0.0, 1.0, -1.0, 0.5, -0.5, rng.uniform(-1, 1), rng.uniform(-1, 1)]))
    elif fn == "s.nd.init":
        c["mu"] = rng.choice([calstat_const(rng), "s:x", "n:", "i:" + str(10 ** 400)])
        c["sigma"] = rng.choice([calstat_const(rng), calstat_const(rng), "s:x"])
    elif fn == "s.nd.from_samples":
        c["data"] = calstat_data(rng, calstat_NUMMIX)
    elif fn == "s.nd.samples":
        c["X"] = calstat_nd(rng)
        c["seed"] = rng.randint(0, 10 ** 6)
        r2 = calstat_random.Random(c["seed"])
        c["us"] = [calstat_fstr(r2.random()) for _ in range(rng.randint(0, 3))]
    elif fn in ("s.nd.pdf", "s.nd.cdf", "s.nd.zscore"):
        c["X"] = calstat_nd(rng)
        c["x"] = calstat_spec(rng.choice([0, 1, -1, 0.5, rng.uniform(-6, 6), calstat_F(1, 3), 2.5]))
    elif fn == "s.nd.inv_cdf":
        c["X"] = calstat_nd(rng)
        c["x"] = calstat_spec(rng.choice([0.5, 0.0, 1.0, -1, 2, 0.1, 0.9, rng.random(), rng.random(), 1e-10, 1 - 1e-10, 1e-300]))
    elif fn == "s.nd.quantiles":
        c["X"] = calstat_nd(rng)
        c["n"] = rng.choice([0, 1, 2, 3, 4, 10])
    elif fn in ("s.nd.overlap", "s.nd.add", "s.nd.sub", "s.nd.eq"):
        c["X"] = calstat_nd(rng)
        c["Y"] = c["X"] if rng.random() < 0.15 else calstat_nd(rng)
    elif fn in ("s.nd.addc", "s.nd.subc", "s.nd.mulc", "s.nd.divc", "s.nd.rsubc"):
        c["X"] = calstat_nd(rng)
        c["x"] = rng.choice([calstat_const(rng), calstat_const(rng), "s:x", "i:0", "i:" + str(10 ** 400)])
    else:
        c["X"] = calstat_nd(rng)
    c["fn"] = "calstat." + fn
    if fn in ("s.kde", "s.kernel", "s.nd.cdf", "s.nd.overlap"):
        c["erfc"] = calstat_record_erfc(c, fn)
    return c


def calstat_cls_spec(name):
    if name in calstat_USER_CLASSES:
        return {"c": name, "mro": calstat_USER_CLASSES[name][1], "m": calstat_USER_CLASSES[name][2]}
    return {"c": name, "mro": {"bool": ["bool", "int"]}.get(name, [name])}


calstat_BUILTIN = {"int": int, "bool": bool, "float": float, "Fraction": calstat_F, "Decimal": calstat_D}


def calstat_cls(spec):
    n = spec["c"]
    return calstat_USER_CLASSES[n][0] if n in calstat_USER_CLASSES else calstat_BUILTIN[n]


def calstat_record_erfc(c, fn):
    table = []
    real = calstat_math.erfc

    def rec(x):
        r = real(x)
        table.append([calstat_fstr(x), calstat_fstr(r)])
        return r
    calstat_st.erfc = rec
    try:
        py_result(lambda: calstat_stat_call(c, fn[2:]))
    finally:
        calstat_st.erfc = real
    return table


def calstat_L(k):
    return [calstat_obj(s) for s in k]


class calstat_Script:
    """What `_random.Random(seed)` is replaced by in `kde_random`: scripted draws."""

    def __init__(self, draws, data):
        self.draws = list(draws)
        self.data = data
        self.cur = None

    def choice(self, data):
        self.cur = self.draws.pop(0)
        return data[self.cur[0]]

    def random(self):
        return calstat_obj("f:" + self.cur[1])


def calstat_nds(c):
    return calstat_ndobj(c["X"])


def calstat_ndpair(n):
    return [calstat_fstr(n.mean), calstat_fstr(n.stdev)]


def calstat_stat_call(c, fn):
    st = calstat_st
    if fn == "_exact_ratio":
        r = st._exact_ratio(calstat_obj(c["x"]))
        return [r[0], r[1]] if r[1] is not None else [calstat_res(r[0]), None]
    if fn == "_isfinite":
        return bool(st._isfinite(calstat_obj(c["x"])))
    if fn == "_coerce":
        return st._coerce(calstat_cls(c["T"]), calstat_cls(c["S"])).__name__
    if fn == "_sum":
        T, total, n = st._sum(calstat_L(c["data"]))
        return [T.__name__, calstat_res(total), n]
    if fn == "_ss":
        d = calstat_L(c["data"])
        T, ss, cc, n = st._ss(d, None if c["c"] is None else calstat_obj(c["c"]))
        return [T.__name__, calstat_res(ss), calstat_res(cc), n]
    if fn == "_convert":
        return calstat_res(st._convert(calstat_obj(c["x"]), calstat_cls(c["T"])))
    if fn == "_fail_neg":
        return [calstat_res(x) for x in st._fail_neg(calstat_L(c["data"]))]
    if fn == "_rank":
        r = st._rank(calstat_L(c["data"]), reverse=c["reverse"], ties=c["ties"], start=calstat_obj(c["start"]))
        return [calstat_res(x) for x in r]
    if fn == "_integer_sqrt_of_frac_rto":
        return st._integer_sqrt_of_frac_rto(c["n"], c["m"])
    if fn == "_float_sqrt_of_frac":
        return calstat_fstr(st._float_sqrt_of_frac(c["n"], c["m"]))
    if fn == "_decimal_sqrt_of_frac":
        return calstat_res(st._decimal_sqrt_of_frac(c["n"], c["m"]))
    if fn == "_mean_stdev":
        a, b = st._mean_stdev(calstat_L(c["data"]))
        return [calstat_fstr(a), calstat_fstr(b)]
    if fn == "_sqrtprod":
        return calstat_fstr(st._sqrtprod(calstat_obj("f:" + c["x"]), calstat_obj("f:" + c["y"])))
    if fn == "mean":
        return calstat_res(st.mean(calstat_L(c["data"])))
    if fn == "fmean":
        w = c["weights"]
        d = calstat_L(c["data"])
        return calstat_res(st.fmean(iter(d) if c["iter"] else d, None if w is None else calstat_L(w)))
    if fn == "geometric_mean":
        return calstat_fstr(st.geometric_mean(calstat_L(c["data"])))
    if fn == "harmonic_mean":
        w = c["weights"]
        return calstat_res(st.harmonic_mean(calstat_L(c["data"]), None if w is None else calstat_L(w)))
    if fn in ("median", "median_low", "median_high", "mode"):
        return calstat_res(getattr(st, fn)(calstat_L(c["data"])))
    if fn == "median_grouped":
        return calstat_fstr(st.median_grouped(calstat_L(c["data"]), calstat_obj(c["interval"])))
    if fn == "multimode":
        return [calstat_res(x) for x in st.multimode(calstat_L(c["data"]))]
    if fn in ("variance", "pvariance", "stdev", "pstdev"):
        return calstat_res(getattr(st, fn)(calstat_L(c["data"]), None if c["c"] is None else calstat_obj(c["c"])))
    if fn == "covariance":
        return calstat_res(st.covariance(calstat_L(c["x"]), calstat_L(c["y"])))
    if fn == "correlation":
        return calstat_res(st.correlation(calstat_L(c["x"]), calstat_L(c["y"]), method=c["method"]))
    if fn == "linear_regression":
        r = st.linear_regression(calstat_L(c["x"]), calstat_L(c["y"]), proportional=c["proportional"])
        return [calstat_res(r.slope), calstat_res(r.intercept)]
    if fn == "quantiles":
        return [calstat_res(x) for x in st.quantiles(calstat_L(c["data"]), n=c["n"], method=c["method"])]
    if fn == "kde":
        d = calstat_L(c["data"])
        f = st.kde(d, calstat_obj(c["h"]), c["kernel"], cumulative=c["cumulative"])
        d[:] = calstat_L(c["data2"])
        return calstat_res(f(calstat_obj(c["x"])))
    if fn == "kde_random":
        script = calstat_Script(c["draws"], None)
        saved = st._random
        st._random = calstat_types.SimpleNamespace(Random=lambda seed: script)
        try:
            f = st.kde_random(calstat_L(c["data"]), calstat_obj(c["h"]), c["kernel"])
            return [calstat_res(f()) for _ in c["draws"]]
        finally:
            st._random = saved
    if fn == "kernel":
        return calstat_fstr(st._kernel_specs[c["kernel"]][c["which"]](calstat_obj("f:" + c["t"])))
    if fn == "nd.init":
        return calstat_ndpair(st.NormalDist(calstat_obj(c["mu"]), calstat_obj(c["sigma"])))
    if fn == "nd.from_samples":
        return calstat_ndpair(st.NormalDist.from_samples(calstat_L(c["data"])))
    if fn == "nd.samples":
        return [calstat_fstr(x) for x in calstat_nds(c).samples(len(c["us"]), seed=c["seed"])]
    if fn in ("nd.pdf", "nd.cdf", "nd.zscore"):
        return calstat_res(getattr(calstat_nds(c), fn[3:])(calstat_obj(c["x"])))
    if fn == "nd.inv_cdf":
        return calstat_fstr(calstat_nds(c).inv_cdf(calstat_obj(c["x"])))
    if fn == "nd.quantiles":
        return [calstat_fstr(x) for x in calstat_nds(c).quantiles(c["n"])]
    if fn == "nd.overlap":
        return calstat_fstr(calstat_nds(c).overlap(calstat_ndobj(c["Y"])))
    if fn == "nd.props":
        X = calstat_nds(c)
        return [calstat_fstr(v) for v in (X.mean, X.median, X.mode, X.stdev, X.variance)]
    if fn == "nd.add":
        return calstat_ndpair(calstat_nds(c) + calstat_ndobj(c["Y"]))
    if fn == "nd.sub":
        return calstat_ndpair(calstat_nds(c) - calstat_ndobj(c["Y"]))
    if fn == "nd.addc":
        v = calstat_obj(c["x"])
        return calstat_ndpair(calstat_nds(c) + v)
    if fn == "nd.subc":
        return calstat_ndpair(calstat_nds(c) - calstat_obj(c["x"]))
    if fn == "nd.mulc":
        return calstat_ndpair(calstat_nds(c) * calstat_obj(c["x"]))
    if fn == "nd.divc":
        return calstat_ndpair(calstat_nds(c) / calstat_obj(c["x"]))
    if fn == "nd.rsubc":
        return calstat_ndpair(calstat_obj(c["x"]) - calstat_nds(c))
    if fn == "nd.pos":
        return calstat_ndpair(+calstat_nds(c))
    if fn == "nd.neg":
        return calstat_ndpair(-calstat_nds(c))
    if fn == "nd.eq":
        return calstat_nds(c) == calstat_ndobj(c["Y"])
    if fn == "nd.hash":
        X = calstat_nds(c)
        return hash(X)
    if fn == "nd.repr":
        return repr(calstat_nds(c))
    if fn == "nd.state":
        X = calstat_nds(c)
        s = X.__getstate__()
        Y = st.NormalDist()
        Y.__setstate__(s)
        return [calstat_fstr(s[0]), calstat_fstr(s[1]), calstat_ndpair(Y)]
    raise KeyError(fn)


def calstat_run_stat(c):
    fn = c["fn"].split(".", 2)[2]
    real = calstat_math.erfc
    table = c.get("erfc")
    return py_result(lambda: calstat_stat_call(c, fn))

def calstat_gen(rng):
    if rng.random() < calstat_CAL_SHARE:
        return calstat_gen_cal(rng)
    return calstat_gen_stat(rng)


def calstat_run(c):
    if c["fn"].startswith("calstat.s."):
        return calstat_run_stat(c)
    return calstat_run_cal(c)


calstat_CAL_SHARE = 0.25
# ====== END AREA calstat ======

# ====== BEGIN AREA rand (Lib/random.py, Modules/_randommodule.c) ======
# Everything for this area stays between these two markers; prefix top-level names with rand_.
rand_gen = None  # replace with def rand_gen(rng) -> case dict with "fn": "rand.<name>"
rand_run = None  # replace with def rand_run(case) -> common.py_result-style dict
# ====== END AREA rand ======


AREAS = {name: (globals()[name + "_gen"], globals()[name + "_run"])
         for name in ['coll', 'collabc', 'functools', 'operator', 'enumdc', 'misc', 'calstat', 'rand']}
selected = os.environ.get("CORELIBS_AREA")
ACTIVE = [a for a in (selected.split(",") if selected else AREAS) if AREAS[a][0] is not None]


def gen_case(rng):
    case = AREAS[rng.choice(ACTIVE)][0](rng)
    if case is not None:
        case["mod"] = "corelibs"
    return case


def run_python(case):
    return AREAS[case["fn"].split(".")[0]][1](case)


if __name__ == "__main__":
    main(gen_case, run_python)
