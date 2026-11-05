<!-- title: datetime == crashes when utcoffset() is None for one fold only -->
# Bug report

### Bug description

pep495_eq_exception (Modules/_datetimemodule.c:6560-6586) tests `flip_offset != offset_self && delta_cmp(flip_offset, offset_self)` (:6569-6570, again at :6580-6581). Both offsets come from datetime_utcoffset, so each is a timedelta or Py_None, and there is no PyDelta_Check: when one of them is None and the other a timedelta, delta_cmp (:2536-2546) reads GET_TD_DAYS/SECONDS/MICROSECONDS of Py_None, 12 bytes at offsets 24..35 of the 16-byte _Py_NoneStruct (Objects/object.c:2400), i.e. whatever static data follows it. This is reached from datetime == / != (datetime_richcompare, :6622 and :6643) for two datetimes with different tzinfo objects whose utcoffset() is None for one fold and a timedelta for the other: both offsets None takes the `offset1 == offset2` branch (:6615) with offset_self None and the flip offset a timedelta; both offsets timedelta and the flip None reads None the other way. On 3.15.2 and main (Linux x86-64 release builds) the bytes after _Py_NoneStruct are zero, so C reads None as timedelta(0): with `utcoffset` = None for fold 0 and timedelta(0) for fold 1, `datetime(2000,1,1,tzinfo=Z()) == datetime(2000,1,1,tzinfo=Z())` is True in C and False in _pydatetime (whose `myoff != self.replace(fold=...).utcoffset()`, Lib/_pydatetime.py:2316, compares a timedelta with None as unequal). With a non-zero timedelta for the other fold, C happens to agree with Python because the zero bytes differ from it. The answer depends on the memory layout of the build.

```python
import ctypes
import datetime as C
import _pydatetime as P
print("bytes 24..36 after id(None):", ctypes.string_at(id(None) + 24, 12).hex())
res = []
for m in (C, P):
    class Z(m.tzinfo):
        def utcoffset(self, dt):
            return m.timedelta(0) if dt.fold else None
        def dst(self, dt):
            return None
    a = m.datetime(2000, 1, 1, tzinfo=Z())
    b = m.datetime(2000, 1, 1, tzinfo=Z())
    res.append((a == b, a != b))
print("C:", res[0], "Python:", res[1])
```

**Expected:** (False, True) in both implementations: the offset changes with fold, so PEP 495 makes the datetimes unequal.

**Actual:** 

**Cause:** Modules/_datetimemodule.c:6569-6570 and :6580-6581 call delta_cmp without PyDelta_Check on either argument; delta_cmp (:2536-2546) assumes timedeltas.

**Possible fix:** Treat a None/timedelta mix as "exception applies": e.g. `if (flip_offset != offset_self && (flip_offset == Py_None || offset_self == Py_None || delta_cmp(flip_offset, offset_self)))`, likewise for other.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/datetime-pep495-delta-cmp-none.yaml
