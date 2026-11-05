<!-- title: datetime.astimezone() crashes when a subclass __new__ returns a non-datetime -->
# Bug report

### Bug description

add_datetime_timedelta() ends in new_datetime_subclass_ex(..., Py_TYPE(date)) (Modules/_datetimemodule.c:6262-6265), which for a subclass is cls(y, m, d, hh, mm, ss, us, tzinfo) and returns whatever that call returns. Two more callers than the one gh-145166 reports (tzinfo_fromutc) then use that object as a PyDateTime_DateTime without a type check: - datetime_datetime_astimezone_impl reads HASTZINFO(result) (:6964), and either rebuilds the object through new_datetime_ex2(..., Py_TYPE(result)) (:6965-6977: the foreign type's own tp_alloc, then datetime fields written into it) or does Py_SETREF(result->tzinfo, utc) (:6983); it then writes result->tzinfo again (:6996). With `class D(datetime)` whose __new__ returns `1` (or `b'\x00'*3`, sometimes `object()`) for eight positional arguments, `D(2000, 1, 1, 12, tzinfo=timezone(timedelta(hours=1))).astimezone(timezone.utc)` is a segfault on 3.15.2 (for object() it varies between runs); with bytearray(200) it writes a pointer into the bytearray's header and then raises "fromutc: argument must be a datetime". - datetime_utctimetuple reads GET_YEAR(utcself)..DATE_GET_SECOND(utcself) (:7182-7187) and returns a struct_time of whatever bytes sit there: tm_year=0, tm_mon=0, tm_wday=-2 for a bytearray, tm_year=65535, tm_mon=255 for object() on 3.15.2. It calls the constructor for every non-None offset, timedelta(0) included (`D(..., tzinfo=timezone.utc).utctimetuple()` is affected), where _pydatetime's `if offset:` (Lib/_pydatetime.py:2075) skips zero. _pydatetime has no crash: `self - offset` goes through type(self).combine(...) and the next attribute access (`.year`, `.replace`) raises AttributeError or reads the object's own attributes. Same root cause as gh-145166 (open; tzinfo_fromutc only). Its open PR #145181 (current diff, last updated 2026-09-22, read 2026-11-04) adds a PyDateTime_Check to add_datetime_timedelta itself, so it fixes every caller that reads the result as a struct (tzinfo_fromutc, astimezone, utctimetuple); its tests and NEWS entry name fromutc and utctimetuple only, so astimezone is the one caller new relative to the PR. This belongs upstream as an addition to gh-145166 (a test for astimezone in PR #145181), not as a separate issue. A related astimezone defect the PR does not fix (a subclass returning an existing instance is mutated in place) is datetime-astimezone-mutates-subclass-result.

```python
import subprocess, sys
head = ("from datetime import datetime, timezone, timedelta\n"
        "class D(datetime):\n"
        "    def __new__(cls, *a, **k):\n"
        "        if len(a) == 8:\n"
        "            return PAYLOAD\n"
        "        return super().__new__(cls, *a, **k)\n"
        "d = D(2000, 1, 1, 12, tzinfo=timezone(timedelta(hours=1)))\n")
crashed = []
for payload in ("1", "object()", "b'\\x00' * 3"):
    code = head.replace("PAYLOAD", payload) + "d.astimezone(timezone.utc)\n"
    p = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True)
    print("astimezone, __new__ returns", payload, "-> returncode", p.returncode)
    if p.returncode < 0:
        crashed.append(payload)
code = head.replace("PAYLOAD", "bytearray(200)") + "print(tuple(d.utctimetuple()))\n"
p = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True)
print("utctimetuple, __new__ returns bytearray(200) ->", p.returncode, p.stdout.strip(), p.stderr.strip()[-200:])
garbage = p.returncode < 0
if p.returncode == 0:
    t = eval(p.stdout)
    garbage = not (1 <= t[1] <= 12 and 1 <= t[2] <= 31 and 0 <= t[6] <= 6)
```

**Expected:** TypeError (as PR #145181 proposes in add_datetime_timedelta), or the Python twin's behaviour; never a crash or a struct_time read from a non-datetime.

**Actual:** 

**Cause:** Modules/_datetimemodule.c:6262-6265 return the subclass call's result unchecked; :6957-6996 (astimezone) and :7174-7187 (utctimetuple) cast it to PyDateTime_DateTime *.

**Possible fix:** Check PyDateTime_Check(result) in add_datetime_timedelta (PR #145181), or in each caller; utctimetuple could also skip the subtraction for a zero offset as Python does.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/datetime-subclass-arith-result-type-confusion.yaml
