<!-- title: _zoneinfo: utcoffset()/dst()/tzname() read the fold byte of a … -->
# Bug report

### Bug description

get_local_timestamp() accepts any object with toordinal(), hour, minute and second
(Modules/_zoneinfo.c:2301-2342), but find_ttinfo() then reads `PyDateTime_DATE_GET_FOLD(dt)`
(:2238) and `PyDateTime_GET_YEAR(dt)` (:2248) from the struct of a datetime the object is not,
and indexes the two-element `trans_list_wall[fold]` (:2240) with that byte. A bytes subclass
whose fourth data byte is 7 makes fold 7, the pointer read lands on `utcoff_seconds`, and the
dereference segfaults. The Python twin raises AttributeError on dt.fold. DUPLICATE of gh-125318
(open; see also gh-111306).

```python
import io, struct
from zoneinfo import ZoneInfo
v1 = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 0, 0)
data = (v1 + b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 1, 1, 4) + struct.pack('>q', 0)
        + b'\x00' + struct.pack('>lBB', 0, 0, 0) + b'UTC\x00' + b'\n\n')
zi = ZoneInfo.from_file(io.BytesIO(data))
class D(bytes):
    hour = minute = second = 0
    def toordinal(self): return 738000
print(zi.utcoffset(D(bytes([0, 0, 0, 7] + [0] * 8))))
```

**Expected:** A TypeError, or the duck-typed lookup of the Python twin (gh-139132 proposes attribute lookups).

**Actual:** 

**Cause:** Modules/_zoneinfo.c:2238-2240 read datetime fields of an object only checked by PyDateTime_CheckExact in get_local_timestamp.

**Possible fix:** Check PyDateTime_Check(dt) in find_ttinfo, or read fold and year through attributes for non-datetimes (gh-139132).

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
