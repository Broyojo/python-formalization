<!-- title: memoryview item assignment writes through a view released by __index__ -->
# Bug report

### Bug description

gh-92888 added CHECK_RELEASED_INT_AGAIN after every conversion in pack_single, because a conversion can run Python code that releases the view and frees the buffer. The arm for the format 'c' converts nothing, so it got no check. But memory_ass_sub also runs Python code before it calls pack_single: PyNumber_AsSsize_t(key, ...) calls key.__index__. So ba = bytearray(N); m = memoryview(ba).cast('c') class K: def __index__(self): m.release(); ba.clear(); return 0 m[K()] = b'x' stores into freed memory. With a large buffer the process dies with SIGSEGV; with a small one the freed block is silently corrupted. Every other format raises ValueError "operation forbidden on released memoryview object" here, and reading (m[K()]) is safe because unpack_single starts with the check. Lean: ReleasedKeyNoWrite is refuted on a 2-byte 'c' view; ReleasedKeyNoWriteNotC (the same for every format but 'c', every item, every callback) is proven, and pack_released_nowrite shows that the 'c' arm is the only write in pack_single not behind the check.

```python
import subprocess, sys
crash = '''
N = 1 << 27
ba = bytearray(b"a" * N)
m = memoryview(ba).cast("c")
class K:
    def __index__(self):
        m.release()
        ba.clear()
        return N // 2
m[K()] = b"x"
print("survived")
'''
r = subprocess.run([sys.executable, "-I", "-c", crash], capture_output=True, text=True)
print("freed buffer: exit status", r.returncode, r.stdout.strip())
def attempt(fmt, value):
    ba = bytearray(b"abcdefgh")
    m = memoryview(ba).cast(fmt)
    class K:
        def __index__(self):
            m.release()
            return 4
    try:
        m[K()] = value
        return "no exception", bytes(ba)
    except ValueError as e:
        return str(e), bytes(ba)
c = attempt("c", b"x")
b = attempt("B", 120)
print("format c:", c)
print("format B:", b)
```

**Expected:** ValueError("operation forbidden on released memoryview object"), as for every other format, and no write.

**Actual:** python3 3.15.2: format c: no exception, b'abcdxfgh'; format B: ValueError; with a 128 MB buffer freed in __index__ the process exits with SIGSEGV (status -11). main (python.exe 3.16.0a1+dev): identical, SIGSEGV included.

**Cause:** Objects/memoryobject.c:2758-2772: memory_ass_sub calls PyNumber_AsSsize_t(key) at :2765, then ptr_from_index, then pack_single, with no check in between. pack_single's arm for 'c' at :2071-2077 writes *ptr with no CHECK_RELEASED_INT_AGAIN. The multi-index path at :2800-2810 has the same shape: ptr_from_tuple runs __index__ at :2519. main has the same arm at Objects/memoryobject.c:2182-2189.

**Possible fix:** Add CHECK_RELEASED_INT_AGAIN(self) to the 'c' arm of pack_single, or at the top of pack_single as unpack_single has it (the per-arm checks are still needed after the conversions), and add m[MyIndex()] = b'x' with format 'c' to test_use_released_memory.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/bytesobj-memoryview-setitem-c-released.yaml
