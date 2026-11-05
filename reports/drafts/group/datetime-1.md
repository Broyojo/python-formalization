<!-- title: Small inconsistencies in datetime found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. datetime.astimezone() writes tzinfo in place into whatever datetime a subclass's __new__ returned (a cached instance changes, its hash goes stale)

datetime_datetime_astimezone_impl computes `result = self - offset` with add_datetime_timedelta (Modules/_datetimemodule.c:6957-6961), which for a subclass calls cls(y, m, d, hh, mm, ss, us, tzinfo) through new_datetime_subclass_ex (:6262-6265) and returns what that call returns. For an aware result it then does Py_SETREF(result->tzinfo, utc) (:6981-6984) and Py_SETREF(result->tzinfo, tzinfo) (:6996) on that object, treating it as a fresh object it owns. When the subclass's __new__ hands back an existing instance (an interning or flyweight cache, `if len(args) == 8: return D.cache`), the cached datetime is mutated: with `D.cache = D(2000, 1, 1, 11, tzinfo=timezone.utc)`, `D(2000, 1, 1, 12, tzinfo=timezone(timedelta(hours=1))).astimezone(timezone(timedelta(hours=2)))` leaves `D.cache` as `D(2000, 1, 1, 11, 0, tzinfo=timezone(timedelta(seconds=7200)))`; it now compares equal to `datetime(2000, 1, 1, 11, tzinfo=+02:00)` but keeps the hash it cached at UTC, so `hash(D.cache) != hash(datetime(2000, 1, 1, 11, tzinfo=+02:00))` and dicts and sets that hold it are inconsistent. _pydatetime never writes: `(self - myoffset).replace(tzinfo=tz)` (Lib/_pydatetime.py:2157) gets the cached object back twice, and `tz.fromutc` raises ValueError('fromutc: dt.tzinfo is not self'). A naive result is rebuilt with new_datetime_ex2 (:6964-6980) and not affected. Related to datetime-subclass-arith-result-type-confusion (same call, same writes), but not fixed by PR #145181: its PyDateTime_Check in add_datetime_timedelta passes for a real D instance.

<details><summary>Reproducer</summary>

```python
from datetime import datetime, timezone, timedelta
utc = timezone.utc
plus1 = timezone(timedelta(hours=1))
plus2 = timezone(timedelta(hours=2))
class D(datetime):
    cache = None
    def __new__(cls, *args, **kwargs):
        if len(args) == 8 and D.cache is not None:
            return D.cache
        return super().__new__(cls, *args, **kwargs)
shared = D(2000, 1, 1, 11, tzinfo=utc)
before = repr(shared)
hash(shared)
D.cache = shared
D(2000, 1, 1, 12, tzinfo=plus1).astimezone(plus2)
twin = datetime(2000, 1, 1, 11, tzinfo=plus2)
print("before:", before)
print("after: ", repr(shared), "== twin:", shared == twin, "hash equal:", hash(shared) == hash(twin))
if repr(shared) != before:
    print("Observed the reported behavior.")
```

</details>

#### 2. C fromisoformat() ignores everything after 'Z' when the next character is NUL

After the UTC designator 'Z', the C parser checks that the next byte is the C string terminator (`*(tzinfo_pos + 1) != '\0'`) instead of checking that 'Z' is the last character of the argument. A Python str can contain '\x00', so a NUL right after 'Z' hides the rest of the string: datetime.fromisoformat('2020-01-01T12:00Z\x00junk') and time.fromisoformat('12:00Z\x00anything') return 12:00 UTC. The pure-Python implementation rejects both, as does C without the NUL ('...Zjunk'). This is still the case on main. On 3.15.2 the NUL also ends the time in other positions ('2020-01-01T12\x00', '12:00:00.123456\x00 trailing text'), which gh-159224 fixed on main as a side effect of rejecting stray text before an offset.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def parse(f, s):
    try:
        return repr(f(s))
    except ValueError as e:
        return 'ValueError'
s = '2020-01-01T12:00Z\x00junk'
c = parse(datetime.datetime.fromisoformat, s)
py = parse(_pydatetime.datetime.fromisoformat, s)
nonul = parse(datetime.datetime.fromisoformat, '2020-01-01T12:00Zjunk')
t = parse(datetime.time.fromisoformat, '12:00Z\x00anything')
print('C      :', c)
print('Python :', py)
print('C without NUL:', nonul)
print('C time :', t)
if c.startswith('datetime.datetime(2020, 1, 1, 12, 0') and py == 'ValueError' and nonul == 'ValueError':
    print("Observed the reported behavior.")
```

</details>

#### 3. datetime.fromisoformat() accepts day 00 and year 0000 when the time is 24:00

The 24:00 ("end of day") rollover in datetime.fromisoformat() moves the date forward one day before the date is validated, and the guard in front of it checks `1 <= month <= 12 and day <= days_in_month` but not `day >= 1` or the year range. So an invalid date becomes a valid one: '2020-01-00T24:00' parses as 2020-01-01 00:00, and '0000-12-31T24:00' (year 0) parses as 0001-01-01 00:00, while '2020-01-00', '2020-01-00T00:00' and '0000-12-31T00:00' all raise ValueError. Both the C and the pure-Python implementation behave this way, on 3.15.2 and on main.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def parse(mod, s):
    try:
        v = mod.datetime.fromisoformat(s)
        return (v.year, v.month, v.day, v.hour, v.minute)
    except ValueError as e:
        return 'ValueError: %s' % e
for s in ['2020-01-00T24:00', '2020-01-00T00:00', '2020-01-00', '0000-12-31T24:00', '0000-12-31T00:00']:
    print(repr(s), 'C:', parse(datetime, s), ' Python:', parse(_pydatetime, s))
if (parse(datetime, '2020-01-00T24:00') == parse(_pydatetime, '2020-01-00T24:00') == (2020, 1, 1, 0, 0)
        and parse(datetime, '0000-12-31T24:00') == (1, 1, 1, 0, 0)
        and str(parse(datetime, '2020-01-00T00:00')).startswith('ValueError')):
    print("Observed the reported behavior.")
```

</details>

#### 4. _pydatetime date - datetime returns a timedelta where C raises TypeError

`_pydatetime.date(2020, 1, 2) - _pydatetime.datetime(2020, 1, 1)` returns `timedelta(days=1)`: date.__sub__ tests `isinstance(other, date)`, which is true for a datetime, and subtracts the ordinals, dropping the datetime's time and tzinfo. The C date_subtract returns NotImplemented whenever either operand is a datetime, and datetime has no reflected method for a date left operand, so the C module raises `TypeError: unsupported operand type(s) for -: 'datetime.date' and 'datetime.datetime'`. The Python comparisons of date already exclude datetime (`isinstance(other, date) and not isinstance(other, datetime)`, Lib/_pydatetime.py:1199), the subtraction does not. The result is also wrong on its own terms: date(2020, 1, 2) - datetime(2020, 1, 1, 23, 59) gives one day.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def run(m):
    try:
        return repr(m.date(2020, 1, 2) - m.datetime(2020, 1, 1))
    except TypeError as e:
        return 'TypeError'
c, p = run(datetime), run(_pydatetime)
print('C:', c, ' Python:', p)
if c == 'TypeError' and p.endswith('timedelta(days=1)'):
    print("Observed the reported behavior.")
```

</details>

#### 5. zoneinfo: from_file() raises struct.error or AssertionError for truncated TZif data

The docs of ZoneInfo.from_file say "ValueError is raised if the data read from file_obj is not a valid TZif file", and both twins use _common.load_data. A header cut short makes `struct.unpack(">6l", stream.read(24))` (Lib/zoneinfo/_common.py:166) raise struct.error, as do short transition, index and type records (:66-69, :81); a version 2+ file whose footer does not start with a newline fails `assert c == b"\n", c` (:122-123) with AssertionError, and under `python -O` that check is skipped and the first byte of the footer is dropped. Neither exception is a ValueError, so `except ValueError` around from_file() misses them.

<details><summary>Reproducer</summary>

```python
import io, struct, warnings
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])
short = b'TZif2' + bytes(38)
body = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 1, 4) + struct.pack('>lBB', 0, 0, 0) + b'UTC\x00'
nonl = body + body + b'UTC0\n'
res = []
for Z in (Cz.ZoneInfo, Pz.ZoneInfo):
    for data in (short, nonl):
        try:
            Z.from_file(io.BytesIO(data))
            res.append('ok')
        except ValueError:
            res.append('ValueError')
        except Exception as e:
            res.append(type(e).__name__)
print(res)
if res == ['error', 'AssertionError'] * 2:
    print("Observed the reported behavior.")
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
AI tools (Claude and Codex) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
