<!-- title: zoneinfo: ZoneInfo.from_file() raises struct.error or AssertionError for malformed TZif data -->
### Bug report

The documentation of `ZoneInfo.from_file()` says that `ValueError` is raised if the data is not a valid TZif file, but `zoneinfo._common.load_data()`, which both the C and pure-Python implementations use, lets other exceptions escape. A truncated header, transition list or local time type record raises `struct.error`, and a version 2+ footer that does not start with a newline fails an `assert` with `AssertionError`. Under `python -O` that check is skipped and the first byte of the footer is dropped, so a footer of `EST5` without the newline loads as the zone `ST5` (abbreviation `ST`, UTC-5).

```python
import io, struct
from zoneinfo import ZoneInfo

header = b"TZif2" + bytes(15) + struct.pack(">6l", 0, 0, 0, 0, 1, 4)
block = header + struct.pack(">lbB", 0, 0, 0) + b"UTC\0"

for data in (
    header[:30],                    # truncated header
    block + block + b"UTC0\n",      # footer without its leading newline
):
    try:
        ZoneInfo.from_file(io.BytesIO(data))
    except Exception as e:
        print(f"{type(e).__name__}: {e}")
```

Actual:

```
error: unpack requires a buffer of 24 bytes
AssertionError: b'U'
```

Expected: `ValueError` in both cases, as already raised for a bad magic number or a footer without a trailing newline. Code that wraps `from_file()` in `except ValueError` does not catch these.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Record: [datetime-zoneinfo-load-data-not-valueerror](https://github.com/Broyojo/python-formalization/blob/main/bugs/datetime-zoneinfo-load-data-not-valueerror.yaml)
