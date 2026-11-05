<!-- title: datetime: 45 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. datetime.astimezone() writes tzinfo in place into whatever datetime a subclass's __new__ returned (a cached instance changes, its hash goes stale)

datetime_datetime_astimezone_impl computes `result = self - offset` with
add_datetime_timedelta (Modules/_datetimemodule.c:6957-6961), which for a subclass calls
cls(y, m, d, hh, mm, ss, us, tzinfo) through new_datetime_subclass_ex (:6262-6265) and returns
what that call returns. For an aware result it then does Py_SETREF(result->tzinfo, utc)
(:6981-6984) and Py_SETREF(result->tzinfo, tzinfo) (:6996) on that object, treating it as a
fresh object it owns. When the subclass's __new__ hands back an existing instance (an interning
or flyweight cache, `if len(args) == 8: return D.cache`), the cached datetime is mutated: with
`D.cache = D(2000, 1, 1, 11, tzinfo=timezone.utc)`,
`D(2000, 1, 1, 12, tzinfo=timezone(timedelta(hours=1))).astimezone(timezone(timedelta(hours=2)))`
leaves `D.cache` as `D(2000, 1, 1, 11, 0, tzinfo=timezone(timedelta(seconds=7200)))`; it now
compares equal to `datetime(2000, 1, 1, 11, tzinfo=+02:00)` but keeps the hash it cached at UTC,
so `hash(D.cache) != hash(datetime(2000, 1, 1, 11, tzinfo=+02:00))` and dicts and sets that hold
it are inconsistent. _pydatetime never writes: `(self - myoffset).replace(tzinfo=tz)`
(Lib/_pydatetime.py:2157) gets the cached object back twice, and `tz.fromutc` raises
ValueError('fromutc: dt.tzinfo is not self'). A naive result is rebuilt with new_datetime_ex2
(:6964-6980) and not affected.
Related to datetime-subclass-arith-result-type-confusion (same call, same writes), but not fixed
by PR #145181: its PyDateTime_Check in add_datetime_timedelta passes for a real D instance.

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
```

</details>

#### 2. C time/datetime.fromisoformat() reads digits after HHMMSS as a fraction with no decimal mark

In the basic (no colon) time format, when the loop in parse_hh_mm_ss_ff() has read
HHMMSS it backs up one character and falls through to the fraction parser without
checking for '.' or ','. So time.fromisoformat('12345678') is 12:34:56.780000 and
'12:00:00+0000000001' gets a 100-microsecond offset. The pure-Python parser raises
ValueError for both. Still present on main. DUPLICATE of gh-155175 (open, PR gh-155177).

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def parse(f, s):
    try:
        return repr(f(s))
    except ValueError:
        return 'ValueError'
c = parse(datetime.time.fromisoformat, '12345678')
py = parse(_pydatetime.time.fromisoformat, '12345678')
print('C:', c, ' Python:', py)
print('offset:', parse(datetime.time.fromisoformat, '12:00:00+0000000001'))
```

</details>

#### 3. C fromisoformat() ignores everything after 'Z' when the next character is NUL

After the UTC designator 'Z', the C parser checks that the next byte is the C string
terminator (`*(tzinfo_pos + 1) != '\0'`) instead of checking that 'Z' is the last
character of the argument. A Python str can contain '\x00', so a NUL right after 'Z'
hides the rest of the string: datetime.fromisoformat('2020-01-01T12:00Z\x00junk') and
time.fromisoformat('12:00Z\x00anything') return 12:00 UTC. The pure-Python
implementation rejects both, as does C without the NUL ('...Zjunk'). This is still the
case on main. On 3.15.2 the NUL also ends the time in other positions
('2020-01-01T12\x00', '12:00:00.123456\x00 trailing text'), which gh-159224 fixed on
main as a side effect of rejecting stray text before an offset.

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
```

</details>

#### 4. time() and datetime() raise OverflowError in C and ValueError in Python for fold outside C int

With every other field a C int, time(fold=2**31) and datetime(1, 1, 1, fold=2**31) raise
OverflowError('Python int too large to convert to C int') in C and ValueError('fold must be
either 0 or 1, not 2147483648') in _pydatetime. fold has only two valid values, and both twins
refuse the argument, so the only difference is which exception class the caller gets. C
converts fold to int before any field is checked, so time(25, fold=2**31) is OverflowError in
C too, where Python raises ValueError for the hour.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def outcome(f, *a, **k):
    try:
        return repr(f(*a, **k))
    except Exception as e:
        return type(e).__name__
c = outcome(datetime.time, fold=2**31), outcome(datetime.datetime, 1, 1, 1, fold=2**31)
py = outcome(_pydatetime.time, fold=2**31), outcome(_pydatetime.datetime, 1, 1, 1, fold=2**31)
print('C:', c, ' Python:', py)
```

</details>

#### 5. date.fromisoformat() ignores the last two characters of a 10-character basic-format string

Both parsers read fixed-width fields and never check that the whole string was
consumed. A 10-character string without '-' at index 4 is parsed as YYYYMMDD or
YYYYWwwD and the rest is dropped: date.fromisoformat('2020010112') == date(2020, 1, 1)
and '2020W011xy' == date(2019, 12, 30), in both twins. The C version takes the length
in UTF-8 bytes, so it also accepts '20040509٠' (9 characters, 10 bytes), which
Python rejects as non-ASCII: that is the witness of the C/Python twin property too, now
that '2020-+1-01' is gone. Still present on main. DUPLICATE of gh-158500 (open;
PR gh-160737 open, gh-158557 closed).

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
c = datetime.date.fromisoformat('2020010112')
py = _pydatetime.date.fromisoformat('2020010112')
print('C:', c, ' Python:', py)
try:
    print('C 9 chars / 10 bytes:', datetime.date.fromisoformat('20040509٠'))
except ValueError as e:
    print('C 9 chars / 10 bytes:', repr(e))
```

</details>

#### 6. date(state, None) unpickles in _pydatetime and is a TypeError in C

`date(b'\x07\xd0\x01\x01', None)` unpickles date(2000, 1, 1) in Python, whose pickle test
is `month is None`; C's test is "exactly one positional argument", so the state goes to
the int converter and the call raises `TypeError: date() missing required argument 'day'`.
`date(year=b'\x07\xd0\x01\x01')` behaves the same way. Split from
datetime-pydatetime-none-as-omitted, which has the same cause (None as the "omitted"
default) in date.replace.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def run(f):
    try:
        return repr(f())
    except TypeError:
        return 'TypeError'
s = [run(lambda: m.date(b'\x07\xd0\x01\x01', None)) for m in (datetime, _pydatetime)]
print('ctor C/Python:', s)
```

</details>

#### 7. date.fromisocalendar raises OverflowError in C and ValueError in Python for components outside C int

Until 3.14 date_fromisocalendar turned the OverflowError of its "iii" conversion into
ValueError('ISO calendar component out of range'), so the twins raised the same class.
The Argument Clinic conversion in 3.15 dropped that, so date.fromisocalendar(2**31, 1, 1)
raises OverflowError from the generated wrapper in C and ValueError in _pydatetime.
This is recorded because it refutes a twin property that held on 3.14.7. It is DELIBERATE:
Misc/NEWS.d/3.15.0a1.rst says fromisocalendar "can now raise OverflowError for out of range
arguments", and Lib/test/datetimetester.py:2187 accepts either class. Do not file it. It is
the same class of difference as the constructors, rejected in gh-158778.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def outcome(f, *a):
    try:
        return repr(f(*a))
    except Exception as e:
        return type(e).__name__
c = outcome(datetime.date.fromisocalendar, 2**31, 1, 1)
py = outcome(_pydatetime.date.fromisocalendar, 2**31, 1, 1)
print('C:', c, ' Python:', py)
```

</details>

#### 8. datetime.fromisoformat() accepts day 00 and year 0000 when the time is 24:00

The 24:00 ("end of day") rollover in datetime.fromisoformat() moves the date forward
one day before the date is validated, and the guard in front of it checks
`1 <= month <= 12 and day <= days_in_month` but not `day >= 1` or the year range.
So an invalid date becomes a valid one: '2020-01-00T24:00' parses as 2020-01-01 00:00,
and '0000-12-31T24:00' (year 0) parses as 0001-01-01 00:00, while '2020-01-00',
'2020-01-00T00:00' and '0000-12-31T00:00' all raise ValueError. Both the C and the
pure-Python implementation behave this way, on 3.15.2 and on main.

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
```

</details>

#### 9. _pydatetime astimezone() takes the target local zone from self before converting, C from the UTC result

With `tz=None`, `_pydatetime`'s `datetime.astimezone` computes the target zone first,
`tz = self._local_timezone()` (Lib/_pydatetime.py:2138-2139), from `self` as it is. C's
`datetime_datetime_astimezone_impl` converts `self` to UTC first and only then takes the zone
of the UTC result, `local_timezone(result)` (Modules/_datetimemodule.c:6987-6993). Two
observable differences follow:
- A naive `self` in a spring-forward gap: Python's `_local_timezone` uses the `_mktime`
  timestamp of the wall time and its offset, so `datetime(2021, 3, 14, 2, 30).astimezone()`
  with `TZ=EST5EDT,M3.2.0,M11.1.0` is `2021-03-14 02:30-05:00` (a wall time that does not
  exist, labelled EST) in Python and `2021-03-14 03:30-04:00` (EDT) in C; with `fold=1`
  Python gives `02:30-04:00` and C `01:30-05:00`. The instants agree, the wall time and the
  tzinfo do not.
- An aware `self` whose tzinfo's `utcoffset()` returns `None`: Python's
  `self._local_timezone()` takes the aware branch, `(self - _EPOCH) // timedelta(seconds=1)`,
  which raises `TypeError: cannot mix naive and timezone-aware time`; C treats `self` as
  naive (`goto naive`, :6946-6949) and returns the local time.
- An aware `self` at the edge of the range whose `self - offset` overflows, under a local
  zone whose `tm_gmtoff` no `timezone` accepts (POSIX `TZ='XXX-24:30'`, 24h30 ahead of UTC):
  `datetime(1, 1, 1, tzinfo=timezone(timedelta(hours=1))).astimezone()` raises `ValueError`
  in Python (`_local_timezone()` builds `timezone(timedelta(seconds=88200))` before the
  subtraction) and `OverflowError: date value out of range` in C, which subtracts first
  (:6957) and never reaches `local_timezone`. A raising `localtime` gives the same split.
`astimezone(tz)` with an explicit tz, and aware datetimes with an offset, agree (proven in
Lean, AstimezoneLocal).

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime, os, time
os.environ['TZ'] = 'EST5EDT,M3.2.0,M11.1.0'
time.tzset()
def run(f):
    try:
        return f()
    except Exception as e:
        return type(e).__name__
def gap(m, fold):
    r = m.datetime(2021, 3, 14, 2, 30, fold=fold).astimezone()
    return (r.hour, r.minute, r.utcoffset().total_seconds() / 3600, r.tzname())
def none_offset(m):
    class T(m.tzinfo):
        def utcoffset(self, dt): return None
        def dst(self, dt): return None
    r = m.datetime(2021, 1, 2, 3, tzinfo=T()).astimezone()
    return (r.hour, r.utcoffset().total_seconds() / 3600)
out = {k: (run(lambda: f(datetime)), run(lambda: f(_pydatetime))) for k, f in [
    ('gap fold=0', lambda m: gap(m, 0)), ('gap fold=1', lambda m: gap(m, 1)),
    ('utcoffset None', none_offset)]}
os.environ['TZ'] = 'XXX-24:30'
time.tzset()
out['aware edge'] = tuple(run(lambda m=m: m.datetime(1, 1, 1, tzinfo=m.timezone(m.timedelta(hours=1))).astimezone())
                          for m in (datetime, _pydatetime))
for k, (c, p) in out.items():
    print(k, ' C:', c, ' Python:', p)
if out['gap fold=0'] == ((3, 30, -4.0, 'EDT'), (2, 30, -5.0, 'EST')) and \
   out['gap fold=1'] == ((1, 30, -5.0, 'EST'), (2, 30, -4.0, 'EDT')) and \
   out['utcoffset None'] == ((3, -5.0), 'TypeError') and \
   out['aware edge'] == ('OverflowError', 'ValueError'):
```

</details>

#### 10. _pydatetime datetime.astimezone() does not validate tzinfo.utcoffset() and calls it before the identity shortcut

`datetime.astimezone` in _pydatetime calls `mytz.utcoffset(self)` directly, so the result
skips `_check_utc_offset`, and it does so before the `tz is mytz` shortcut. C uses
`call_utcoffset`, after the identity check. With a tzinfo whose utcoffset returns
timedelta(days=1), _pydatetime converts and C raises ValueError. With a tzinfo whose utcoffset
raises, d.astimezone(d.tzinfo) raises in _pydatetime and returns d in C.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def run(m):
    class Big(m.tzinfo):
        def utcoffset(self, dt): return m.timedelta(1)
        def dst(self, dt): return None
    class Boom(m.tzinfo):
        def utcoffset(self, dt): raise KeyError('boom')
        def dst(self, dt): return None
    out = []
    try:
        out.append(m.datetime(2020, 1, 2, 12, tzinfo=Big()).astimezone(m.timezone.utc).isoformat())
    except ValueError:
        out.append('ValueError')
    d = m.datetime(2020, 1, 2, 12, tzinfo=Boom())
    try:
        out.append(d.astimezone(d.tzinfo) is d)
    except KeyError:
        out.append('KeyError')
    return out
c, p = run(datetime), run(_pydatetime)
print(c, p)
```

</details>

#### 11. _pydatetime date - datetime returns a timedelta where C raises TypeError

`_pydatetime.date(2020, 1, 2) - _pydatetime.datetime(2020, 1, 1)` returns
`timedelta(days=1)`: date.__sub__ tests `isinstance(other, date)`, which is true for a
datetime, and subtracts the ordinals, dropping the datetime's time and tzinfo. The C
date_subtract returns NotImplemented whenever either operand is a datetime, and
datetime has no reflected method for a date left operand, so the C module raises
`TypeError: unsupported operand type(s) for -: 'datetime.date' and 'datetime.datetime'`.
The Python comparisons of date already exclude datetime (`isinstance(other, date) and
not isinstance(other, datetime)`, Lib/_pydatetime.py:1199), the subtraction does not.
The result is also wrong on its own terms: date(2020, 1, 2) - datetime(2020, 1, 1, 23, 59)
gives one day.

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
```

</details>

#### 12. _pydatetime does not apply operator.index to fold and to date.fromordinal's argument, unlike C

`_check_date_fields` and `_check_time_fields` pass every field through `operator.index`
(as C's `PyLong_AsInt` does), but two integer arguments are used without it:
- `fold`: `_check_time_fields` tests `fold not in (0, 1)` (Lib/_pydatetime.py:605), which
  compares with `==`. So `time(fold=1.0)`, `datetime(2020, 1, 1, fold=1.0)` and
  `time(1).replace(fold=1.0)` succeed in Python, store the float (`time(fold=1.0).fold` is
  `1.0`, and `time(fold=True).fold` is `True`), while C raises `TypeError: 'float' object
  cannot be interpreted as an integer` (and returns `1` for `True`). Conversely
  `time(fold=obj)` with `obj.__index__()` returning 1 is accepted by C and refused by Python
  with `ValueError: fold must be either 0 or 1, not <obj>`.
- `date.fromordinal(n)`: `_ord2ymd(n)` starts with `n -= 1`, so an object with only
  `__index__` raises `TypeError: unsupported operand type(s) for -=` in Python, while C
  converts it and returns the date (`date.fromordinal(obj)` with `obj.__index__()` returning
  5 is `date(1, 1, 5)`).
- `IsoCalendarDate.__new__(cls, year, week, weekday)` (Lib/_pydatetime.py:1381-1382) stores
  the three objects as they are, while C's `iso_calendar_date_new_impl` takes clinic `int`
  arguments (Modules/_datetimemodule.c:3843-3870): `type(d.isocalendar())('a', 2, 3)` is
  `IsoCalendarDate(year=a, week=2, weekday=3)` in Python and `TypeError` in C (and 2**40 is an
  OverflowError in C). The signatures differ the other way for keywords: Python's `__new__`
  has the positional-only marker `/` (:1381), C's clinic signature
  (Modules/_datetimemodule.c:3836-3839) has none, so `IsoCalendarDate(year=2020, week=1,
  weekday=3)` is a TypeError (`got some positional-only arguments passed as keyword
  arguments`) in Python and builds the tuple in C. The class is not public;
  `date.isocalendar()` always passes three ints positionally.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
class Idx:
    def __init__(self, v): self.v = v
    def __index__(self): return self.v
def run(f):
    try:
        return repr(f())
    except Exception as e:
        return type(e).__name__
r = {name: (run(lambda: f(datetime)), run(lambda: f(_pydatetime))) for name, f in [
    ('time(fold=1.0).fold', lambda m: m.time(fold=1.0).fold),
    ('time(fold=Idx(1)).fold', lambda m: m.time(fold=Idx(1)).fold),
    ('date.fromordinal(Idx(5))', lambda m: m.date.fromordinal(Idx(5))),
    ('IsoCalendarDate("a", 2, 3)', lambda m: tuple(type(m.date(2020, 1, 1).isocalendar())('a', 2, 3))),
    ('IsoCalendarDate(year=2020, week=1, weekday=3)',
     lambda m: tuple(type(m.date(2020, 1, 1).isocalendar())(year=2020, week=1, weekday=3)))]}
for k, (c, p) in r.items():
    print(k, ' C:', c, ' Python:', p)
if r['time(fold=1.0).fold'] == ('TypeError', '1.0') and \
   r['time(fold=Idx(1)).fold'] == ('1', 'ValueError') and \
   r['date.fromordinal(Idx(5))'] == ('datetime.date(1, 1, 5)', 'TypeError') and \
   r['IsoCalendarDate("a", 2, 3)'] == ('TypeError', "('a', 2, 3)") and \
   r['IsoCalendarDate(year=2020, week=1, weekday=3)'] == ('(2020, 1, 3)', 'TypeError'):
```

</details>

#### 13. Pure-Python datetime.fromisoformat() accepts a date followed by a bare separator

_pydatetime.datetime.fromisoformat('2009-04-19T') returns midnight: the time part after
the separator is empty and `if tstr:` treats it as absent. The C implementation raises
ValueError. Also '2020W0112' (the separator is the last digit). DUPLICATE of gh-160850
(closed as completed on 2026-10-28; the vendored main snapshot predates the fix).

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
try:
    datetime.datetime.fromisoformat('2009-04-19T'); c = 'accepted'
except ValueError:
    c = 'ValueError'
py = _pydatetime.datetime.fromisoformat('2009-04-19T')
print('C:', c, ' Python:', py)
```

</details>

#### 14. _pydatetime's datetime.isoformat accepts an int sep ('%c' % sep), C requires a one-character str

`datetime.isoformat(sep)` formats the separator with `"%04d-%02d-%02d%c" % (..., sep)`
(Lib/_pydatetime.py:2190), and `%c` also takes an integer code point (anything with
`__index__`). So `datetime(2020, 1, 1).isoformat(sep=65)` is `'2020-01-01A00:00:00'` and
`isoformat(sep=True)` is `'2020-01-01\x0100:00:00'` in Python, while C's argument clinic
converter accepts only a str of length 1 and raises `TypeError: isoformat() argument 'sep'
must be a unicode character, not int` (Modules/clinic/_datetimemodule.c.h:1798-1811).
An int outside range(0x110000) is `OverflowError` in Python and `TypeError` in C. Strings of
other lengths and other objects are `TypeError` in both (different messages).

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def run(m):
    try:
        return m.datetime(2020, 1, 1).isoformat(sep=65)
    except TypeError:
        return 'TypeError'
r = [run(m) for m in (datetime, _pydatetime)]
print('isoformat(sep=65) C/Python:', r)
```

</details>

#### 15. In a leap-second time zone, _pydatetime's naive timestamp()/astimezone() raise ValueError where C returns a value

`datetime._mktime` solves `t = local(u)` with `local(u)` defined as
`(datetime(*time.localtime(u)[:6]) - epoch) // timedelta(0, 1)` (Lib/_pydatetime.py:2034-2036).
Under a time zone with leap seconds (a TZif file with leap records, such as the `right/`
zones), `time.localtime` returns `tm_sec == 60` for the leap second, and
`datetime(y, m, d, hh, mm, 60)` raises `ValueError: second must be in 0..59, not 60`. C's
`local()` (Modules/_datetimemodule.c:5588-5607) feeds the fields to `utc_to_seconds`, which
checks only the year. So with TZ set to such a zone, `datetime(1972, 7, 1).timestamp()`
(naive, the second right after the first leap second) is `78796800.0` in C and raises
ValueError in Python, and `datetime(1972, 7, 1).astimezone()` returns an aware datetime in C
and raises in Python. Naive datetimes whose `_mktime` search does not pass through a leap
second agree.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime, os, struct, tempfile, time
LEAP = 78796800  # 1972-07-01T00:00:00 POSIX, the first leap second
hdr = b'TZif' + b'\0' * 16 + struct.pack('>6l', 0, 0, 1, 0, 1, 4)
data = hdr + struct.pack('>lBB', 0, 0, 0) + b'UTC\0' + struct.pack('>ll', LEAP, 1)
path = os.path.join(tempfile.mkdtemp(), 'leapUTC')
with open(path, 'wb') as f:
    f.write(data)
os.environ['TZ'] = path
time.tzset()
print('localtime(LEAP)[:6] =', tuple(time.localtime(LEAP))[:6])
def run(m):
    try:
        return repr(m.datetime(1972, 7, 1).timestamp())
    except ValueError:
        return 'ValueError'
r = [run(m) for m in (datetime, _pydatetime)]
print('timestamp() C/Python:', r)
```

</details>

#### 16. _pydatetime treats an explicit None (or tzinfo=True) as an omitted argument in replace and combine

_pydatetime uses None as the "not given" default and tests `is None`, so an explicit None
behaves like an omitted argument; C uses Argument Clinic defaults and treats None as an
object to convert.
`date(2020, 1, 1).replace(year=None)` returns date(2020, 1, 1) in Python and raises
`TypeError: 'NoneType' object cannot be interpreted as an integer` in C (same for month
and day). time.replace and datetime.replace share the pattern for every field and for
fold (Lib/_pydatetime.py:1735-1746 and :2097-2116): `time(1, 2, 3).replace(hour=None)` and
`datetime(2020, 2, 3).replace(year=None, fold=None)` keep the fields in Python and raise the
same TypeError in C (the clinic `int` converters of datetime_time_replace and
datetime_datetime_replace, Modules/clinic/_datetimemodule.c.h:1089-1191 and :1853-1985).
`tzinfo=None` is a real value in both (it removes the tzinfo), but the tzinfo default is
the object True in Python (`if tzinfo is True`, :1743-1744, :2111-2112, :1957-1958), so
`t.replace(tzinfo=True)`, `d.replace(tzinfo=True)` and
`datetime.combine(d, t, tzinfo=True)` keep the tzinfo in Python and raise `TypeError:
tzinfo argument must be None or of a tzinfo subclass, not type 'bool'` in C, whose default
is a clinic `unchanged`/NULL (Modules/_datetimemodule.c:5891-5911 for combine). (The related pickle test
`date(state, None)` is recorded separately, at P5, as datetime-date-pickle-test-month-none.)

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def run(f):
    try:
        return repr(f())
    except TypeError:
        return 'TypeError'
r = [run(lambda: m.date(2020, 1, 1).replace(year=None)) for m in (datetime, _pydatetime)]
t = [run(lambda: m.time(1, 2, 3).replace(hour=None)) for m in (datetime, _pydatetime)]
d = [run(lambda: m.datetime(2020, 2, 3).replace(year=None, fold=None)) for m in (datetime, _pydatetime)]
c = [run(lambda: m.datetime.combine(m.date(2020, 1, 1), m.time(1), tzinfo=True)) for m in (datetime, _pydatetime)]
print('date.replace C/Python:', r)
print('time.replace C/Python:', t)
print('datetime.replace C/Python:', d)
print('combine(tzinfo=True) C/Python:', c)
if (r[0] == 'TypeError' and r[1].endswith('date(2020, 1, 1)') and t[0] == 'TypeError'
        and t[1].endswith('time(1, 2, 3)') and d[0] == 'TypeError'
        and d[1].endswith('datetime(2020, 2, 3, 0, 0)') and c[0] == 'TypeError'
        and c[1].endswith('datetime(2020, 1, 1, 1, 0)')):
```

</details>

#### 17. _pydatetime asks for the flipped-fold utcoffset on every inter-zone ==, so an exception there breaks comparisons C answers

For `==` and `!=` between aware datetimes with different tzinfo objects, `datetime._cmp`
(allow_mixed=True) calls `self.replace(fold=not self.fold).utcoffset()` and the same for
`other` before it looks at the operands (Lib/_pydatetime.py:2315-2318), to implement the
PEP 495 rule that a datetime in a fold or gap never compares equal across zones. C's
`datetime_richcompare` asks for the flipped-fold offsets only when the operands are
otherwise equal (`pep495_eq_exception`, Modules/_datetimemodule.c:6560-6586, called at
:6619-6626 and :6640-6647).
So a tzinfo whose `utcoffset` raises for the other fold (for example one that refuses an
ambiguous or nonexistent time, or one that only implements fold=0) makes
`datetime(2020, 1, 1, tzinfo=TZ()) == datetime(2020, 1, 2, tzinfo=TZ())` (two TZ instances)
raise in Python and return False in C; `!=` likewise raises in Python and returns True in C.
Ordering (`<`) does not ask for the flipped offsets in either twin and agrees.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def run(m):
    class TZ(m.tzinfo):
        def utcoffset(self, dt):
            if dt.fold:
                raise RuntimeError('fold=1 not supported')
            return m.timedelta(hours=1)
        def dst(self, dt):
            return None
    a = m.datetime(2020, 1, 1, tzinfo=TZ())
    b = m.datetime(2020, 1, 2, tzinfo=TZ())
    try:
        return repr(a == b)
    except RuntimeError:
        return 'RuntimeError'
r = [run(m) for m in (datetime, _pydatetime)]
print('== C/Python:', r)
```

</details>

#### 18. time/datetime.__reduce__(): _pydatetime calls self.__reduce_ex__(2), so a subclass override runs; C does not look it up

_pydatetime defines `time.__reduce__` and `datetime.__reduce__` as `return
self.__reduce_ex__(2)` (Lib/_pydatetime.py:1782-1783, :2435-2436), an attribute lookup on the
instance, so a subclass's own `__reduce_ex__` runs. C's datetime_time___reduce___impl and
datetime_datetime___reduce___impl (Modules/_datetimemodule.c:5308-5312, :7241-7246) return
`(Py_TYPE(self), time_getstate(self, 2))` / `datetime_getstate(self, 2)` directly. So for a
subclass whose `__reduce_ex__` returns `(str, ('custom', proto))`, `T(1, 2, 3).__reduce__()` is
`(str, ('custom', 2))` in Python and `(T, (b'\x01\x02\x03\x00\x00\x00',))` in C; and a subclass
whose `__reduce_ex__` delegates with `return self.__reduce__()` (which works with the C class,
and makes `pickle.dumps` work there) recurses until RecursionError in _pydatetime, in
`__reduce__()` and in `pickle.dumps(obj, 2)` alike. date.__reduce__ is `(self.__class__,
self._getstate())` in both twins and does not differ.

<details><summary>Reproducer</summary>

```python
import pickle
import datetime as C
import _pydatetime as P
out = {}
for name, m in (("C", C), ("Python", P)):
    class T(m.time):
        def __reduce_ex__(self, proto):
            return (str, ("custom", proto))
    class T2(m.time):
        def __reduce_ex__(self, proto):
            return self.__reduce__()
    r = T(1, 2, 3).__reduce__()[0].__name__
    try:
        pickle.dumps(T2(1, 2, 3), 2)
        r2 = "pickled"
    except RecursionError:
        r2 = "RecursionError"
    out[name] = (r, r2)
    print(name, out[name])
```

</details>

#### 19. _pydatetime replace() always passes fold= to a subclass constructor; C passes it only when nonzero

For a datetime or time subclass whose constructor does not take a `fold` keyword
(`def __new__(cls, *args): return super().__new__(cls, *args)`), `replace()` works in C and
raises in _pydatetime. C's `call_subclass_fold` (Modules/_datetimemodule.c:1254-1285) adds
`fold=` to the call only when the fold is nonzero (gh-89039 made replace call the subclass);
Python's replace calls `type(self)(..., fold=fold)` (Lib/_pydatetime.py:1747, :2116-2117)
always. `D(2000, 1, 1).replace(day=2)` is `D(2000, 1, 2, 0, 0)` in C and
`TypeError: D.__new__() got an unexpected keyword argument 'fold'` in Python; the same for
`time`.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def run(f):
    try:
        return repr(f())
    except Exception as e:
        return type(e).__name__
out = []
for m in (datetime, _pydatetime):
    class D(m.datetime):
        def __new__(cls, *a):
            return super().__new__(cls, *a)
    class T(m.time):
        def __new__(cls, *a):
            return super().__new__(cls, *a)
    out.append((run(lambda: D(2000, 1, 1).replace(day=2)), run(lambda: T(1).replace(hour=2))))
print('C:', out[0], ' Python:', out[1])
```

</details>

#### 20. _pydatetime timedelta.__rsub__ negates first and overflows where C does not

`timedelta.max.__rsub__(timedelta.max)` is `timedelta(0)` in C, whose reflected slot
computes `other - self` (delta_subtract), and raises `OverflowError: timedelta # of days is
too large: -1000000000` in _pydatetime, which computes `-self + other` and `-timedelta.max`
is out of range. Every self with days == 999999999 and a nonzero seconds or microseconds
field overflows the same way, whatever `other` is.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def run(m):
    try:
        return repr(m.timedelta.max.__rsub__(m.timedelta.max))
    except OverflowError:
        return 'OverflowError'
c, p = run(datetime), run(_pydatetime)
print('C:', c, ' Python:', p)
```

</details>

#### 21. str() of a date or time subclass overriding isoformat: C calls the override, _pydatetime does not

`_pydatetime` defines `__str__ = isoformat` in `date` (Lib/_pydatetime.py:1150) and `time`
(:1642), which binds the base class's function, so a subclass's own `isoformat` is not used
by `str()`. C's `date_str` and `time_str` (Modules/_datetimemodule.c:3637-3640, :4880-4883)
call `self.isoformat()` through the object's class. With
`class D(date): def isoformat(self): return 'X'`, `str(D(2000, 1, 1))` is `'X'` in C and
`'2000-01-01'` in Python; the same for `time`. `datetime.__str__` dispatches in both, but
differently: C's `datetime_str` (Modules/_datetimemodule.c:6416-6425) calls
`self.isoformat(' ')` with the separator positional, `_pydatetime` (Lib/_pydatetime.py:2220-2222)
calls `self.isoformat(sep=' ')`, so an override whose signature differs from the base one sees
different calls: with `def isoformat(self, *a, **k): return repr((a, k))`, `str(dt)` is
`"((' ',), {})"` in C and `"((), {'sep': ' '})"` in Python, and with
`def isoformat(self, timespec='auto')` Python's `str()` is a TypeError.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
out = []
for m in (datetime, _pydatetime):
    class D(m.date):
        def isoformat(self):
            return 'X'
    class T(m.time):
        def isoformat(self, timespec='auto'):
            return 'Y'
    class DT(m.datetime):
        def isoformat(self, *a, **k):
            return repr((a, k))
    out.append((str(D(2000, 1, 1)), str(T(1, 2)), str(DT(2000, 1, 1))))
print('C:', out[0], ' Python:', out[1])
```

</details>

#### 22. _pydatetime's tzinfo.__reduce__ tests __getinitargs__ for truth; C calls whatever it finds

`tzinfo.__reduce__` looks up `__getinitargs__` with `getattr(self, "__getinitargs__",
None)` and calls it only `if getinitargs:` (Lib/_pydatetime.py:1371-1375). C's
`tzinfo_reduce` calls any attribute `PyObject_GetOptionalAttr` found
(Modules/_datetimemodule.c:4261-4266). So a tzinfo subclass that sets
`__getinitargs__ = None` (the usual way to switch an inherited method off) pickles as
`(cls, (), state)` in Python and raises `TypeError: 'NoneType' object is not callable` in C;
a falsy callable is not called in Python and is called in C. For a method (always true) the
twins agree.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def run(m):
    class TZ(m.tzinfo):
        __getinitargs__ = None
    try:
        return repr(TZ().__reduce__()[1])
    except TypeError:
        return 'TypeError'
r = [run(m) for m in (datetime, _pydatetime)]
print('__reduce__ args C/Python:', r)
```

</details>

#### 23. time/datetime.__reduce_ex__(protocol): C rejects a protocol outside C int or without __index__, _pydatetime accepts it

The C methods declare `proto: int` (Modules/_datetimemodule.c:5290-5292, :7222-7224), so the
clinic wrapper converts it with PyLong_AsInt (clinic/_datetimemodule.c.h:1239, :2068):
`time(1).__reduce_ex__(2**31)` and `datetime(2000, 1, 1).__reduce_ex__(2**31)` raise
OverflowError("Python int too large to convert to C int"), and `__reduce_ex__(2.5)` raises
TypeError. _pydatetime's `__reduce_ex__(self, protocol)` (Lib/_pydatetime.py:1779-1780,
:2432-2433) passes the object to `_getstate`, which compares `protocol > 3` only when fold is
set (:1757, :2407), so both calls return the state tuple.

<details><summary>Reproducer</summary>

```python
import datetime as C, _pydatetime as P
out = []
for m in (C, P):
    row = []
    for v in (m.time(1), m.datetime(2000, 1, 1)):
        for p in (2**31, 2.5):
            try:
                v.__reduce_ex__(p)
                row.append("ok")
            except (OverflowError, TypeError) as e:
                row.append(type(e).__name__)
    out.append(row)
print("C:", out[0], "Python:", out[1])
```

</details>

#### 24. repr(datetime) with fold=1 and a tzinfo: C prints fold before tzinfo, _pydatetime after

`repr(datetime(2020, 1, 1, fold=1, tzinfo=timezone.utc))` is
`datetime.datetime(2020, 1, 1, 0, 0, fold=1, tzinfo=datetime.timezone.utc)` in C and
`datetime.datetime(2020, 1, 1, 0, 0, tzinfo=datetime.timezone.utc, fold=1)` in _pydatetime:
`datetime_repr` appends the fold keyword before the tzinfo (Modules/_datetimemodule.c:6406-6410),
`datetime.__repr__` the tzinfo first (Lib/_pydatetime.py:2212-2217). `time` appends tzinfo then
fold in both twins (Modules/_datetimemodule.c:4872-4875), so C is also inconsistent with itself.
Both strings evaluate back to the same datetime.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
r = [repr(m.datetime(2020, 1, 1, fold=1, tzinfo=m.timezone.utc)) for m in (datetime, _pydatetime)]
print('C:', r[0])
print('Python:', r[1])
```

</details>

#### 25. repr of a nested date subclass: _pydatetime prints __qualname__, C prints tp_name

For a date subclass defined inside a class (`class Outer: class D(date): pass`, or any
class whose __qualname__ differs from __name__), `repr(D(2020, 1, 1))` is
`Outer.D(2020, 1, 1)` with _pydatetime and `D(2020, 1, 1)` with the C module: Python uses
`self.__class__.__qualname__`, C uses `Py_TYPE(self)->tp_name`, which for a heap type is
`__name__`. A subclass defined in a module named `datetime` also differs (Python prefixes
`datetime.`). gh-107773 made the two agree for top-level subclasses (gh-130308 added
_get_class_module); the qualname part remained. The same pattern is in the other reprs
(time, datetime, timedelta: `Outer.TD(days=1)` against `TD(days=1)`).

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
out = []
for m in (datetime, _pydatetime):
    class Outer:
        class D(m.date):
            pass
        class TD(m.timedelta):
            pass
        class T(m.time):
            pass
        class DT(m.datetime):
            pass
    out.append((repr(Outer.D(2020, 1, 1)), repr(Outer.TD(1)), repr(Outer.T(1, 2)),
                repr(Outer.DT(2020, 1, 1))))
print('C:', out[0], ' Python:', out[1])
if out[0] == ('D(2020, 1, 1)', 'TD(days=1)', 'T(1, 2)', 'DT(2020, 1, 1, 0, 0)') and \
   out[1] == ('Outer.D(2020, 1, 1)', 'Outer.TD(days=1)', 'Outer.T(1, 2)', 'Outer.DT(2020, 1, 1, 0, 0)'):
```

</details>

#### 26. strftime: a %: not followed by z differs between the C and Python implementations

`%:z` is the only directive with a colon, and the two format scanners treat a `%:` that
does not start it differently. At the end of the format Python drops it and C copies it:
date(2020, 1, 1).strftime('abc%:') is 'abc' in _pydatetime and 'abc%:' in C. Before another
directive Python consumes the next character as part of the unknown directive and C rescans
it, so '%:%Z' keeps the %Z in C and loses it in Python.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
c = datetime.date(2020, 1, 1).strftime('abc%:')
p = _pydatetime.date(2020, 1, 1).strftime('abc%:')
c2 = datetime.datetime(2020, 1, 1, tzinfo=datetime.timezone.utc).strftime('%:%Z')
p2 = _pydatetime.datetime(2020, 1, 1, tzinfo=_pydatetime.timezone.utc).strftime('%:%Z')
print(repr(c), repr(p), repr(c2), repr(p2))
```

</details>

#### 27. strftime %z/%:z/%Z: _pydatetime calls a subclass's utcoffset()/tzname() override, C reads the tzinfo member

_wrap_strftime builds the %z and %:z text from `object.utcoffset()` when
`hasattr(object, "utcoffset")` (Lib/_pydatetime.py:240-247, :252-259) and %Z from
`object.tzname()` (:264-272), so a date, time or datetime subclass that overrides those
methods gets its override's result. C's wrap_strftime takes the tzinfo from the struct with
get_tzinfo_member (Modules/_datetimemodule.c:1505-1515: PyDateTime_Check or PyTime_Check, then
HASTZINFO) and calls that tzinfo's utcoffset/tzname directly (make_somezreplacement
:1799-1817 through format_utcoffset :1740; make_Zreplacement :1820-1860 through call_tzname),
so the override is never consulted: for `class D(datetime)` with `def utcoffset(self): return
timedelta(hours=5)` and `def tzname(self): return "FIVE"`, `D(2000, 1, 1).strftime('%z|%:z|%Z')`
is '+0500|+05:00|FIVE' in _pydatetime and '||' in C; a time subclass the same; a date subclass
defining utcoffset() gets '+0500' in Python, '' in C. For the inherited methods the twins agree
(StrftimeZTwins). isoformat() shows the same pattern (Python's _tzstr/isoformat call
self.utcoffset(), C reads the member), not modelled here.

<details><summary>Reproducer</summary>

```python
import sys
import datetime as C
import _pydatetime as P
out = {}
for name, m in (("C", C), ("Python", P)):
    class D(m.datetime):
        def utcoffset(self):
            return m.timedelta(hours=5)
        def tzname(self):
            return "FIVE"
    class T(m.time):
        def utcoffset(self):
            return m.timedelta(hours=5)
    out[name] = (D(2000, 1, 1).strftime("%z|%:z|%Z"), T(1).strftime("%z"))
    print(name, out[name])
```

</details>

#### 28. strptime rejects %d with %Oy as 'without a year directive', though %Oy is the year

3.15 made %d without a year a ValueError. TimeRE.pattern decides that by comparing each
directive with exactly 'Y', 'y' and 'G', so %Oy, the alternative-digits spelling of %y, does
not count, although it fills group `y` and _strptime reads that group as the year. In a
locale with alternative digits, or where locale.ALT_DIGITS is unavailable (LC_alt_digits is
None), strptime(s, '%d/%m/%Oy') raises "Day of month directive '%d' may not be used without
a year directive". On 3.14 the same format parsed, with a DeprecationWarning from the
same check. '%Od/%m/%Oy' parses, because %Od does not count as a day either, so '%Od' alone
also escapes the new error, the opposite way round.

<details><summary>Reproducer</summary>

```python
import _strptime
class Stand_in:
    def __init__(self):
        real = _strptime.LocaleTime()
        for k in ('f_weekday', 'a_weekday', 'f_month', 'a_month', 'am_pm', 'timezone',
                  'LC_date_time', 'LC_date', 'LC_time', 'LC_time_ampm', 'lang', 'tzname', 'daylight'):
            setattr(self, k, getattr(real, k))
        self.LC_alt_digits = None
regexes = _strptime.TimeRE(Stand_in())
print('%Oy is', regexes['Oy'])
try:
    regexes.pattern('%d/%m/%Oy')
    raised = False
except ValueError as e:
    print(e)
    raised = 'without a year' in str(e)
print(regexes.compile('%Od/%m/%Oy').match('01/02/03').groupdict())
```

</details>

#### 29. _pydatetime time(state, tzinfo) accepts any falsy tzinfo where C raises TypeError

The pickle form of the time constructor passes `minute or None` as the tzinfo, so a falsy
second argument (0, '', ...) becomes None and is accepted. C passes the argument itself to
time_from_pickle and raises TypeError('bad tzinfo state arg').

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
state = b'\x01\x00\x00\x00\x00\x00'
def run(m):
    try:
        return repr(m.time(state, 0))
    except TypeError as e:
        return 'TypeError: %s' % e
c, p = run(datetime), run(_pydatetime)
print(c, p)
```

</details>

#### 30. timedelta * float subclass: _pydatetime unpacks any as_integer_ratio() result, C demands a 2-tuple of ints

For `t * x` and `t / x` with a float `x`, both implementations call
`x.as_integer_ratio()`, so a float subclass can override it. _pydatetime unpacks the result
with `a, b = ...`; C's `get_float_as_integer_ratio` requires a tuple of size 2 and
`divide_nearest` requires int parts. So for `class F(float)` whose `as_integer_ratio`
returns:
- the list `[3, 2]`: `timedelta(1) * F(1.5)` is `timedelta(days=1, seconds=43200)` in
  Python and `TypeError: unexpected return type from as_integer_ratio(): expected tuple, not
  'list'` in C (any non-tuple iterable, e.g. an iterator, behaves like the list);
- a list of another length: ValueError (unpacking) in Python, TypeError in C;
- the tuple `(3.0, 2)`: a float computation in Python, `TypeError: non-integer arguments in
  division` in C.
A tuple of the wrong length is a ValueError in both, with different messages.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def mk(ret):
    class F(float):
        def as_integer_ratio(self):
            return ret
    return F(1.5)
def run(m, ret):
    try:
        r = m.timedelta(1) * mk(ret)
        return (r.days, r.seconds, r.microseconds)
    except Exception as e:
        return type(e).__name__
r = {repr(ret): (run(datetime, ret), run(_pydatetime, ret)) for ret in ([3, 2], (3.0, 2))}
for k, (c, p) in r.items():
    print(k, ' C:', c, ' Python:', p)
```

</details>

#### 31. timedelta * n for an int subclass: C runs n.__mul__ on the microseconds, _pydatetime uses int arithmetic

`timedelta * n` with `n` an instance of an int subclass that overrides `__mul__`: C's
`multiply_int_timedelta` computes `PyNumber_Multiply(intobj, pyus_in)`, the int on the left
(Modules/_datetimemodule.c:2299), so the subclass's `__mul__` runs on the microsecond count
and its result goes to `microseconds_to_delta`, whose `checked_divmod` then rejects it.
`_pydatetime` computes `self._days * other` etc. (Lib/_pydatetime.py:862-864), the timedelta's
ints on the left, so `int.__mul__` runs and the override is ignored. With
`class I(int): __mul__ = lambda s, o: 2.5`, `timedelta(1) * I(2)` is `timedelta(days=2)` in
Python and `TypeError: 'float' object cannot be interpreted as an integer` in C; an override
returning an object whose `divmod` is not a 2-tuple gives `divmod() returned non-tuple` or
`divmod() returned a tuple of size 3`, one returning a remainder out of range
`divmod() returned a value out of range`. `I(2) * timedelta(1)` calls `I.__mul__` first in
both and agrees.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def run(f):
    try:
        return repr(f())
    except Exception as e:
        return type(e).__name__ + ': ' + str(e)
class I(int):
    __mul__ = lambda s, o: 2.5
c = run(lambda: datetime.timedelta(1) * I(2))
p = run(lambda: _pydatetime.timedelta(1) * I(2))
print('C:', c, ' Python:', p)
```

</details>

#### 32. isoformat(timespec=...) refuses non-str, NUL and surrogate timespecs differently in _pydatetime and C

C's Argument Clinic `str` converter for `timespec` runs before the impl's lookup of the
spec, and refuses three kinds of argument that _pydatetime simply fails to find in its
`specs` dict (ValueError: Unknown timespec value):
- a non-str, e.g. `time(1).isoformat(timespec=1)`: C raises `TypeError: isoformat()
  argument 'timespec' must be str, not int` (an unhashable timespec, a list, is a
  TypeError in both);
- a str with a NUL, e.g. `timespec='auto\0'`: C raises `ValueError: embedded null
  character` (same class, other message);
- a str with a lone surrogate, e.g. `timespec='\ud800'`: C raises `UnicodeEncodeError:
  'utf-8' codec can't encode character ... surrogates not allowed`, a ValueError subclass.
The same holds for `datetime.isoformat`.

<details><summary>Reproducer</summary>

```python
import datetime, _pydatetime
def run(m, ts):
    try:
        m.time(1).isoformat(timespec=ts)
        return 'ok'
    except Exception as e:
        return type(e).__name__ + ': ' + str(e)
r = {ts: (run(datetime, ts), run(_pydatetime, ts)) for ts in (1, 'auto\0', '\ud800')}
for ts, (c, p) in r.items():
    print(repr(ts), ' C:', c, ' Python:', p)
if r[1][0].startswith('TypeError') and r[1][1].startswith('ValueError') and \
   r['auto\0'] == ('ValueError: embedded null character', 'ValueError: Unknown timespec value') and \
   r['\ud800'][0].startswith('UnicodeEncodeError') and r['\ud800'][1] == 'ValueError: Unknown timespec value':
```

</details>

#### 33. zoneinfo: with a key whose __eq__ raises, C ZoneInfo(key) and clear_cache(only_keys=...) raise while the pure-Python twin succeeds

C looks a key up in its strong cache by comparing it with every node,
`PyObject_RichCompareBool(key, node->key, Py_EQ)` (Modules/_zoneinfo.c:2441), and returns the
error when a comparison raises (:2442-2444); `zoneinfo_ZoneInfo_impl` then returns it
(:320-321) and `clear_cache(only_keys=...)` stops on `eject_from_strong_cache`'s -1
(:2475-2477, :542-545). Python keeps its caches in dicts (Lib/zoneinfo/_zoneinfo.py:40-56,
:95-103), which compare a key only with stored keys of the same hash. So for a `str`
subclass key whose `__eq__` raises, while the strong cache holds any other key,
`ZoneInfo.clear_cache(only_keys=[key])` and `ZoneInfo(key)` raise the `__eq__` exception in C
and succeed in Python (once the key itself is cached, Python's lookups compare it too and
raise as well).
Same cause, the hash side: a `str` subclass with `__hash__ = None` that equals a cached key
gets the cached zone from C `ZoneInfo(key)` (the strong cache compares without hashing),
while Python's `_weak_cache.get` hashes it and raises `TypeError`.
`clear_cache(only_keys=[that key])` raises `TypeError` in both, but C has already ejected
the strong node (eject runs before the weak-cache `pop` that hashes), so the zone is no
longer kept alive in C while Python's strong cache still holds it.
And on empty caches, `clear_cache(only_keys=[that key])` succeeds in C (the weak cache's
`dict.pop` returns at once on an empty dict without hashing, Objects/dictobject.c:3295-3300)
and raises `TypeError` in Python (`OrderedDict.pop` always hashes).
The same happens with a cached zone once nothing but the strong cache holds it:
`z = ZoneInfo('k'); del z; ZoneInfo.clear_cache(only_keys=[NoHash('k'), 'UTC'])`. C's eject
compares without hashing, finds `'k'`'s node and frees it (`strong_cache_node_free`); the
zone's last reference goes, its `KeyedRef` callback removes its weak entry, the weak cache's
`dict.pop` then sees an empty dict and does not hash, and C goes on to clear the later keys
and returns `None`. Python's weak-cache `pop` hashes first and raises `TypeError`.

<details><summary>Reproducer</summary>

```python
import os, struct, tempfile, warnings
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])
assert Cz.ZoneInfo is not Pz.ZoneInfo
h = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 1, 4)
blob = h + struct.pack('>lBB', 0, 0, 0) + b'UTC\x00'
T = tempfile.mkdtemp()
for n in ('a', 'b'):
    with open(os.path.join(T, n), 'wb') as f:
        f.write(blob + blob + b'\nUTC0\n')
class Key(str):
    def __eq__(self, other):
        raise RuntimeError('eq')
    __hash__ = str.__hash__
out = []
for M in (Cz, Pz):
    M.reset_tzpath([T])
    M.ZoneInfo.clear_cache()
    held = M.ZoneInfo('a')
    k = Key('b')
    res = []
    for f in (lambda: M.ZoneInfo.clear_cache(only_keys=[k]), lambda: str.__str__(M.ZoneInfo(k).key)):
        try:
            res.append(('ok', f()))
        except RuntimeError as e:
            res.append(('RuntimeError', str(e)))
    out.append(res)
    M.ZoneInfo.clear_cache()
class NoHash(str):
    __hash__ = None
import weakref
out2 = []
for M in (Cz, Pz):
    M.reset_tzpath([T])
    M.ZoneInfo.clear_cache()
    held = M.ZoneInfo('a')
    res = []
    try:
        res.append(M.ZoneInfo(NoHash('a')) is held)
    except TypeError:
        res.append('TypeError')
    try:
        M.ZoneInfo.clear_cache(only_keys=[NoHash('a')])
        res.append('cleared')
    except TypeError:
        res.append('TypeError')
    r = weakref.ref(held)
    del held
    res.append(r() is not None)
    out2.append(res)
    M.ZoneInfo.clear_cache()
out3 = []
for M in (Cz, Pz):
    M.ZoneInfo.clear_cache()
    try:
        M.ZoneInfo.clear_cache(only_keys=[NoHash('x')])
        out3.append('cleared')
    except TypeError:
        out3.append('TypeError')
with open(os.path.join(T, 'UTC'), 'wb') as f:
    f.write(blob + blob + b'\nUTC0\n')
out4 = []
for M in (Cz, Pz):
    M.ZoneInfo.clear_cache()
    z = M.ZoneInfo('a'); del z
    try:
        out4.append(M.ZoneInfo.clear_cache(only_keys=[NoHash('a'), 'UTC']))
    except TypeError:
        out4.append('TypeError')
print('C', out[0], out2[0], out3[0], out4[0], 'Py', out[1], out2[1], out3[1], out4[1])
if (out[0] == [('RuntimeError', 'eq')] * 2 and out[1] == [('ok', None), ('ok', 'b')]
        and out2[0] == [True, 'TypeError', False] and out2[1] == ['TypeError', 'TypeError', True]
        and out3 == ['cleared', 'TypeError'] and out4 == [None, 'TypeError']):
```

</details>

#### 34. _zoneinfo: load_timedelta() narrows a long DST offset to int

utcoff_to_dstoff() computes a DST offset as the difference of two 32-bit UTC offsets in
a `long` (Modules/_zoneinfo.c:2085-2102), which can reach 2**32 - 1 in magnitude.
build_ttinfo() passes it to load_timedelta(state, long seconds) (:1150, :911), which calls
`PyDateTimeAPI->Delta_FromDelta(0, seconds, 0, 1, ...)` (:880-881), whose parameters are `int`
(Include/datetime.h:174). The value is silently truncated: a standard type at 2**31 - 1 and
a DST type at -(2**31 - 1), both allowed by RFC 9636 3.2, give dst() == timedelta(seconds=2) in C
and timedelta(seconds=-4294967294) in Python. The timedelta cache is keyed by the untruncated value.

<details><summary>Reproducer</summary>

```python
import io, struct, datetime as dt, warnings
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])
assert Cz.ZoneInfo.__module__ == 'zoneinfo' and Cz.ZoneInfo is not Pz.ZoneInfo
def tzif(trans, idx, types, abbr, footer=b''):
    v1 = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 0, 0)
    h = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, len(trans), len(types), len(abbr))
    body = b''.join(struct.pack('>q', t) for t in trans) + bytes(idx)
    body += b''.join(struct.pack('>lBB', *t) for t in types) + abbr
    return v1 + h + body + b'\n' + footer + b'\n'
def both(data, f):
    out = []
    for Z in (Cz.ZoneInfo, Pz.ZoneInfo):
        try:
            out.append(f(Z.from_file(io.BytesIO(data), key='k')))
        except Exception as e:
            out.append(type(e).__name__)
    return out
data = tzif([0, 1000], [0, 1], [(2**31 - 1, 0, 0), (-(2**31 - 1), 1, 4)], b'AAA\x00BBB\x00')
c, py = both(data, lambda z: z.dst(dt.datetime(2100, 1, 1)))
print('C', repr(c), 'Py', repr(py))
```

</details>

#### 35. _zoneinfo: a TZ footer with an embedded NUL is cut at the NUL

The footer of a version 2+ file is the bytes up to the next newline (_common.py:125-128),
which may contain NUL bytes. C parse_tz_str() takes `PyBytes_AsString(tz_str_obj)`
(Modules/_zoneinfo.c:1626) and walks it as a C string, so it stops at the first NUL:
the footer `EST5\0junk` is read as `EST5` and accepted. Python decodes the whole footer and
its pattern refuses it (ValueError "... is not a valid TZ string").

<details><summary>Reproducer</summary>

```python
import io, struct, datetime as dt, warnings
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])
assert Cz.ZoneInfo.__module__ == 'zoneinfo' and Cz.ZoneInfo is not Pz.ZoneInfo
def tzif(trans, idx, types, abbr, footer=b''):
    v1 = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 0, 0)
    h = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, len(trans), len(types), len(abbr))
    body = b''.join(struct.pack('>q', t) for t in trans) + bytes(idx)
    body += b''.join(struct.pack('>lBB', *t) for t in types) + abbr
    return v1 + h + body + b'\n' + footer + b'\n'
def both(data, f):
    out = []
    for Z in (Cz.ZoneInfo, Pz.ZoneInfo):
        try:
            out.append(f(Z.from_file(io.BytesIO(data), key='k')))
        except Exception as e:
            out.append(type(e).__name__)
    return out
data = tzif([], [], [(0, 0, 0)], b'AAA\x00', b'EST5\x00junk')
c, py = both(data, lambda z: z.utcoffset(dt.datetime(2000, 1, 1)))
print('C', repr(c), 'Py', repr(py))
```

</details>

#### 36. zoneinfo: pure-Python fromutc() misses the fold of the last explicit transition

After the last explicit transition Python's fromutc() asks only the footer rule for the
fold (Lib/zoneinfo/_zoneinfo.py:132-137). C also checks whether that last transition lowered
the offset (Modules/_zoneinfo.c:681-694). For a transition from +03 to +02 on 2001-11-15 and
the footer BBB-2CCC-3,M3.5.0,M10.5.0/3, 00:30 UTC is 02:30 local with fold=1 in C and fold=0
in Python, whose result converts back to 23:30 UTC. DUPLICATE of gh-159707 (open).

<details><summary>Reproducer</summary>

```python
import io, struct, datetime as dt, warnings
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])
assert Cz.ZoneInfo.__module__ == 'zoneinfo' and Cz.ZoneInfo is not Pz.ZoneInfo
def tzif(trans, idx, types, abbr, footer=b''):
    v1 = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 0, 0)
    h = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, len(trans), len(types), len(abbr))
    body = b''.join(struct.pack('>q', t) for t in trans) + bytes(idx)
    body += b''.join(struct.pack('>lBB', *t) for t in types) + abbr
    return v1 + h + body + b'\n' + footer + b'\n'
def both(data, f):
    out = []
    for Z in (Cz.ZoneInfo, Pz.ZoneInfo):
        try:
            out.append(f(Z.from_file(io.BytesIO(data), key='k')))
        except Exception as e:
            out.append(type(e).__name__)
    return out
T = int(dt.datetime(2001, 11, 15, tzinfo=dt.timezone.utc).timestamp())
data = tzif([T], [1], [(10800, 0, 0), (7200, 0, 4)], b'AAA\x00BBB\x00', b'BBB-2CCC-3,M3.5.0,M10.5.0/3')
def f(z):
    u = dt.datetime(2001, 11, 15, 0, 30, tzinfo=z)
    r = z.fromutc(u)
    return (r.fold, r.astimezone(dt.timezone.utc) == u.replace(tzinfo=dt.timezone.utc))
c, py = both(data, f)
print('C', c, 'Py', py)
```

</details>

#### 37. zoneinfo: pure-Python fromutc() adds the last transition's offset instead of the footer's after the last transition (two or more transitions, fixed-offset footer)

After the last explicit transition, when the footer is a fixed offset (`_tz_after` is a
`_ttinfo`), Python's fromutc() falls through to the bisect branch
(Lib/zoneinfo/_zoneinfo.py:141-155). With two or more transitions and `timestamp >=
self._trans_utc[1]` it takes `tti_prev, tti = self._ttinfos[idx - 2 : idx]` (:144-145) before
the `timestamp > self._trans_utc[-1]` case (:146-148) that would use `self._tz_after`, so `tti`
is the last transition's type, not the footer's. C uses the footer
(`find_tzrule_ttinfo_fromutc` on the static rule, Modules/_zoneinfo.c:671-674). With
transitions at 0 s (to +01:00) and 1000 s (to +02:00) and the footer `XXX0`, 2000-01-01 00:00
UTC becomes 00:00 in C and 02:00 in Python, although Python's own utcoffset() of that result is
+00:00, so the UTC round trip loses two hours.

<details><summary>Reproducer</summary>

```python
import io, struct, datetime as dt, warnings
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])
assert Cz.ZoneInfo is not Pz.ZoneInfo
def tzif(trans, idx, types, abbr, footer=b''):
    v1 = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 0, 0)
    h = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, len(trans), len(types), len(abbr))
    body = b''.join(struct.pack('>q', t) for t in trans) + bytes(idx)
    body += b''.join(struct.pack('>lBB', *t) for t in types) + abbr
    return v1 + h + body + b'\n' + footer + b'\n'
data = tzif([0, 1000], [1, 2], [(0, 0, 0), (3600, 0, 4), (7200, 0, 8)], b'AAA\x00BBB\x00CCC\x00', b'XXX0')
out = []
for Z in (Cz.ZoneInfo, Pz.ZoneInfo):
    z = Z.from_file(io.BytesIO(data), key='k')
    u = dt.datetime(2000, 1, 1, tzinfo=z)
    r = z.fromutc(u)
    out.append((r.replace(tzinfo=None) - dt.datetime(2000, 1, 1), r.utcoffset(),
                r.astimezone(dt.timezone.utc) == u.replace(tzinfo=dt.timezone.utc)))
print('C', out[0], 'Py', out[1])
```

</details>

#### 38. zoneinfo: a deleted or replaced Sub._weak_cache makes C Sub(key) raise (AttributeError, RuntimeError) where the pure-Python twin falls back or returns the stored object

For a subclass, C `get_weak_cache` reads `PyObject_GetAttrString(type, "_weak_cache")`
(Modules/_zoneinfo.c:299-301). The C base type keeps its weak cache in module state and has no
`_weak_cache` attribute, so after `del Sub._weak_cache` the lookup fails and `Sub(key)` and
`Sub.clear_cache()` raise `AttributeError` (:324-327, :512-515). In Python `cls._weak_cache`
(Lib/zoneinfo/_zoneinfo.py:41-43, :97-102) finds the class attribute
`ZoneInfo._weak_cache` through the MRO, so `Sub(key)` works and stores the subclass instance
in the base class's cache, and `Sub.clear_cache()` clears the base class's weak cache.
Same family: after `Sub._weak_cache = {'a': 1}`, C's `PyObject_TypeCheck` on the cached value
(:352-358, added for gh-142781) raises `RuntimeError: Unexpected instance of int in Sub weak
cache for key 'a'`, while Python's `__new__` (no such check) returns `1`.

<details><summary>Reproducer</summary>

```python
import os, struct, tempfile, warnings
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])
assert Cz.ZoneInfo is not Pz.ZoneInfo
h = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 1, 4)
blob = h + struct.pack('>lBB', 0, 0, 0) + b'UTC\x00'
T = tempfile.mkdtemp()
with open(os.path.join(T, 'a'), 'wb') as f:
    f.write(blob + blob + b'\nUTC0\n')
out = []
for M in (Cz, Pz):
    M.reset_tzpath([T])
    class Sub(M.ZoneInfo):
        pass
    del Sub._weak_cache
    try:
        out.append(type(Sub('a')).__name__)
    except AttributeError:
        out.append('AttributeError')
    class Sub2(M.ZoneInfo):
        pass
    Sub2._weak_cache = {'a': 1}
    try:
        out.append(repr(Sub2('a')))
    except RuntimeError:
        out.append('RuntimeError')
    M.ZoneInfo.clear_cache()
print('C', out[:2], 'Py', out[2:])
```

</details>

#### 39. zoneinfo: C ZoneInfo.__init_subclass__ silently accepts class keywords and imports weakref anew; the pure-Python twin rejects keywords and uses its bound weakref

C registers `__init_subclass__` as `METH_VARARGS | METH_KEYWORDS | METH_CLASS`
(Modules/_zoneinfo.c:2654-2656) and `zoneinfo_init_subclass` (:2622-2637) ignores its
arguments, so `class S(ZoneInfo, foo=1): pass` is accepted and `foo` is silently dropped.
Python's `def __init_subclass__(cls)` (Lib/zoneinfo/_zoneinfo.py:36-38) takes no keywords,
so the same class statement raises `TypeError: ZoneInfo.__init_subclass__() got an
unexpected keyword argument 'foo'`; `object.__init_subclass__` would raise too.
Second difference in the same function: C's `new_weak_cache` (:2592-2603) imports `weakref`
at each subclass creation (`PyImport_ImportModuleAttrString`, through `sys.modules`), while
Python uses the `weakref` module it bound at import. With `sys.modules["weakref"]` replaced by
a module lacking `WeakValueDictionary`, subclassing raises `AttributeError` in C only.

<details><summary>Reproducer</summary>

```python
import sys, types, warnings
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])
assert Cz.ZoneInfo is not Pz.ZoneInfo
def kw(M):
    class S(M.ZoneInfo, foo=1):
        pass
    return 'accepted'
def swapped(M):
    saved = sys.modules['weakref']
    sys.modules['weakref'] = types.ModuleType('weakref')
    try:
        class S(M.ZoneInfo):
            pass
        return 'accepted'
    finally:
        sys.modules['weakref'] = saved
out = []
for f in (kw, swapped):
    for M in (Cz, Pz):
        try:
            out.append(f(M))
        except Exception as e:
            out.append(type(e).__name__)
print(out)
```

</details>

#### 40. zoneinfo: pure-Python dst() is 0 for DST types when an isdst byte is neither 0 nor 1

Both twins infer each DST type's offset from neighbouring transitions and stop early
once every DST type has one. Python counts the DST types with `dst_cnt = sum(isdsts)`
(Lib/zoneinfo/_zoneinfo.py:314), but `struct` read the flags as signed bytes (`">lbb"`,
_common.py:81), so a flag byte 0xff counts as -1. With flags (0, 1, 0xff) the sum is 0, the
loop breaks before its first step (:318-319), and the `for ... else` fallback to 3600 is
skipped, so both DST types report dst() == 0. C counts every type (:2066-2070) and treats
each flag by truthiness, so it gives 1h and 2h. utcoffset() and tzname() agree.

<details><summary>Reproducer</summary>

```python
import io, struct, datetime as dt, warnings
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])
assert Cz.ZoneInfo.__module__ == 'zoneinfo' and Cz.ZoneInfo is not Pz.ZoneInfo
def tzif(trans, idx, types, abbr, footer=b''):
    v1 = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 0, 0)
    h = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, len(trans), len(types), len(abbr))
    body = b''.join(struct.pack('>q', t) for t in trans) + bytes(idx)
    body += b''.join(struct.pack('>lBB', *t) for t in types) + abbr
    return v1 + h + body + b'\n' + footer + b'\n'
def both(data, f):
    out = []
    for Z in (Cz.ZoneInfo, Pz.ZoneInfo):
        try:
            out.append(f(Z.from_file(io.BytesIO(data), key='k')))
        except Exception as e:
            out.append(type(e).__name__)
    return out
data = tzif([0, 1000, 2000, 3000], [0, 1, 0, 2], [(0, 0, 0), (3600, 1, 4), (7200, 255, 8)],
            b'AAA\x00BBB\x00CCC\x00')
probe = [dt.datetime(1970, 1, 1) + dt.timedelta(seconds=s) for s in (5000, 11000)]
c, py = both(data, lambda z: [z.dst(p) for p in probe])
print('C', c, 'Py', py)
```

</details>

#### 41. zoneinfo: from_file() raises struct.error or AssertionError for truncated TZif data

The docs of ZoneInfo.from_file say "ValueError is raised if the data read from file_obj
is not a valid TZif file", and both twins use _common.load_data. A header cut short makes
`struct.unpack(">6l", stream.read(24))` (Lib/zoneinfo/_common.py:166) raise struct.error, as do
short transition, index and type records (:66-69, :81); a version 2+ file whose footer does not
start with a newline fails `assert c == b"\n", c` (:122-123) with AssertionError, and under
`python -O` that check is skipped and the first byte of the footer is dropped. Neither
exception is a ValueError, so `except ValueError` around from_file() misses them.

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
```

</details>

#### 42. zoneinfo: for datetime subclasses C narrows toordinal() to int, so utcoffset()/fromutc() pick a different offset than the pure-Python twin

For an exact datetime, C `get_local_timestamp` (Modules/_zoneinfo.c:2291-2298) reads the struct
fields. For a subclass it calls `toordinal()` and the `hour`/`minute`/`second` attributes
(:2300-2341), as Python's `_get_local_timestamp` does (Lib/zoneinfo/_zoneinfo.py:189-195), but
stores `PyLong_AsLong(num)` in `int ord` (:2290, :2307): a `long` result outside `int` is
silently truncated. A subclass whose `toordinal()` returns its ordinal plus 2**32 gets the
2021-01-01 timestamp in C and one about 2**32 days later in Python. With a single transition at
2**40 s (from +00:00 to +07:00), C answers +00:00 and Python +07:00, for `utcoffset()`, `dst()`,
`tzname()` and `fromutc()`. `hour`, `minute` and `second` are narrowed the same way.

<details><summary>Reproducer</summary>

```python
import io, struct, datetime as dt, warnings
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])
assert Cz.ZoneInfo is not Pz.ZoneInfo
def tzif(trans, idx, types, abbr, footer=b''):
    v1 = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 0, 0)
    h = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, len(trans), len(types), len(abbr))
    body = b''.join(struct.pack('>q', t) for t in trans) + bytes(idx)
    body += b''.join(struct.pack('>lBB', *t) for t in types) + abbr
    return v1 + h + body + b'\n' + footer + b'\n'
data = tzif([2**40], [1], [(0, 0, 0), (25200, 0, 4)], b'AAA\x00BBB\x00')
class Big(dt.datetime):
    def toordinal(self):
        return super().toordinal() + 2**32
out = []
for Z in (Cz.ZoneInfo, Pz.ZoneInfo):
    z = Z.from_file(io.BytesIO(data), key='k')
    d = Big(2021, 1, 1, tzinfo=z)
    out.append((z.utcoffset(d), z.fromutc(d).replace(tzinfo=None) - dt.datetime(2021, 1, 1)))
print('C', out[0], 'Py', out[1])
```

</details>

#### 43. zoneinfo: a ZoneInfo subclass has a strong LRU cache in the pure-Python twin and none in C

Python's `ZoneInfo.__init_subclass__` gives every subclass its own `_strong_cache` (an
OrderedDict) and `_weak_cache` (Lib/zoneinfo/_zoneinfo.py:36-38), and `__new__` keeps the last
8 keys alive through it (:40-56). C `zoneinfo_init_subclass` (Modules/_zoneinfo.c:2622-2637)
creates only the weak cache (`new_weak_cache`, :2592-2603); `zone_from_strong_cache` and
`update_strong_cache` return at once for any type but the base class (:2520-2522,
:2547-2549, "Strong cache currently only implemented for base class"). So for
`class Sub(ZoneInfo): pass`, `Sub("k")` stays alive after its last reference is dropped in
Python and is collected in C: `Sub("k") is Sub("k")` across a dropped reference, and the cost of
repeated construction, differ between the twins.

<details><summary>Reproducer</summary>

```python
import os, struct, tempfile, gc, weakref, warnings
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])
assert Cz.ZoneInfo is not Pz.ZoneInfo
h = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 1, 4)
blob = h + struct.pack('>lBB', 0, 0, 0) + b'UTC\x00'
T = tempfile.mkdtemp()
with open(os.path.join(T, 'k'), 'wb') as f:
    f.write(blob + blob + b'\nUTC0\n')
out = []
for M in (Cz, Pz):
    M.reset_tzpath([T])
    class Sub(M.ZoneInfo):
        pass
    w = weakref.ref(Sub('k'))
    gc.collect()
    out.append(w() is not None)
print('C alive', out[0], 'Py alive', out[1])
```

</details>

#### 44. _zoneinfo: ts_to_local() and fromutc() wrap int64_t for transition times near the ends of the range

ts_to_local() adds the UTC offset to each transition time in place,
`trans_local[0][i] += offset_0` (Modules/_zoneinfo.c:2179-2191), in `int64_t`. A version 2+
file may give any 64-bit transition time, so a transition at 2**63 - 1 into a +1h type wraps
to a large negative local time (CPython builds with -fwrapv). find_ttinfo() then sees every
datetime as after the last transition and uses the rule for after it: utcoffset() of
2000-01-01 is +01:00 BBB in C and +00:00 AAA (the type before the first transition) in
Python. fromutc() has the same `int64_t` arithmetic at :691 and :712: with transitions at
-2**63 and 2**60 (all +00:00), 2000-01-01 00:00 UTC lies between them, and
`timestamp - self->trans_list_utc[idx - 1]` (:712) wraps to a negative number, so C sets
fold=1 where Python's exact difference gives fold=0.

<details><summary>Reproducer</summary>

```python
import io, struct, datetime as dt, warnings
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])
assert Cz.ZoneInfo.__module__ == 'zoneinfo' and Cz.ZoneInfo is not Pz.ZoneInfo
def tzif(trans, idx, types, abbr, footer=b''):
    v1 = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 0, 0)
    h = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, len(trans), len(types), len(abbr))
    body = b''.join(struct.pack('>q', t) for t in trans) + bytes(idx)
    body += b''.join(struct.pack('>lBB', *t) for t in types) + abbr
    return v1 + h + body + b'\n' + footer + b'\n'
def both(data, f):
    out = []
    for Z in (Cz.ZoneInfo, Pz.ZoneInfo):
        try:
            out.append(f(Z.from_file(io.BytesIO(data), key='k')))
        except Exception as e:
            out.append(type(e).__name__)
    return out
data = tzif([2**63 - 1], [1], [(0, 0, 0), (3600, 0, 4)], b'AAA\x00BBB\x00')
c, py = both(data, lambda z: (z.utcoffset(dt.datetime(2000, 1, 1)), z.tzname(dt.datetime(2000, 1, 1))))
print('lookup: C', c, 'Py', py)
data2 = tzif([-2**63, 2**60], [0, 0], [(0, 0, 0)], b'UTC\x00')
def fu(z):
    r = z.fromutc(dt.datetime(2000, 1, 1, tzinfo=z))
    return (r.replace(tzinfo=None), r.fold)
c2, py2 = both(data2, fu)
print('fromutc: C', c2, 'Py', py2)
if (c == (dt.timedelta(hours=1), 'BBB') and py == (dt.timedelta(0), 'AAA')
        and c2 == (dt.datetime(2000, 1, 1), 1) and py2 == (dt.datetime(2000, 1, 1), 0)):
```

</details>

#### 45. zoneinfo: the zero-based TZ rule `n` is evaluated one day early in both twins

POSIX defines the rule `n` as the zero-based day of the year (0 is January 1). Both twins
start from the day before January 1 (Lib/zoneinfo/_zoneinfo.py:535, :541;
Modules/_zoneinfo.c:1425, :1443) and add n, which is right for the one-based `Jn` but puts `n`
a day early: with STD0DST-1,10/0,J100/0, DST starts on January 10 instead of January 11.
glibc's tzset() gives January 11. DUPLICATE of gh-159712 (open).

<details><summary>Reproducer</summary>

```python
import io, struct, datetime as dt, warnings
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])
assert Cz.ZoneInfo.__module__ == 'zoneinfo' and Cz.ZoneInfo is not Pz.ZoneInfo
def tzif(trans, idx, types, abbr, footer=b''):
    v1 = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 0, 0)
    h = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, len(trans), len(types), len(abbr))
    body = b''.join(struct.pack('>q', t) for t in trans) + bytes(idx)
    body += b''.join(struct.pack('>lBB', *t) for t in types) + abbr
    return v1 + h + body + b'\n' + footer + b'\n'
def both(data, f):
    out = []
    for Z in (Cz.ZoneInfo, Pz.ZoneInfo):
        try:
            out.append(f(Z.from_file(io.BytesIO(data), key='k')))
        except Exception as e:
            out.append(type(e).__name__)
    return out
data = tzif([], [], [(0, 0, 0)], b'STD\x00', b'STD0DST-1,10/0,J100/0')
c, py = both(data, lambda z: [dt.datetime(2021, 1, d, 12, tzinfo=z).tzname() for d in (10, 11)])
print('C', c, 'Py', py)
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
