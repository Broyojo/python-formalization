<!-- title: datetime == reads None as a timedelta when utcoffset() is None for only one fold -->
### Bug report

For two aware datetimes with different `tzinfo` objects, `==` checks whether the UTC offset changes with `fold` (PEP 495). The C code compares the two offsets with `delta_cmp` without checking that both are timedeltas. When `utcoffset()` returns `None` for one fold and a timedelta for the other, `delta_cmp` reads `Py_None` as a timedelta, from memory past the end of the `None` object. The C and pure-Python versions then disagree:

```python
import datetime as C
import _pydatetime as P

for label, m in (("datetime", C), ("_pydatetime", P)):
    class Z(m.tzinfo):
        def utcoffset(self, dt):
            return m.timedelta(0) if dt.fold else None
        def dst(self, dt):
            return None
    a = m.datetime(2000, 1, 1, tzinfo=Z())
    b = m.datetime(2000, 1, 1, tzinfo=Z())
    print(label, a == b, a != b)
```

Output on 3.15.2 and main (Linux x86-64):

```
datetime True False
_pydatetime False True
```

The C result depends on whatever bytes follow `_Py_NoneStruct` in the binary; on this build they are zero, so `None` reads as `timedelta(0)`. I'd expect `False True` from both, as in `_pydatetime`.

Cause: Modules/_datetimemodule.c:6569-6570 and :6580-6581 (`pep495_eq_exception`) call `delta_cmp` (:2536-2546) on offsets that can be `None`.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. The code blocks were rerun on 3.15.2 and main during technical review; the human submitter must review the report before filing. Record: [datetime-pep495-delta-cmp-none](https://github.com/Broyojo/python-formalization/blob/main/bugs/datetime-pep495-delta-cmp-none.yaml)
