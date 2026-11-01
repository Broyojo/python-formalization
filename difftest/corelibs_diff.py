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

def calstat_gen(rng):
    return calstat_gen_cal(rng)


def calstat_run(c):
    return calstat_run_cal(c)
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
