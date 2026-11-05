<!-- title: Use-after-free in bytearray.strip() when __release_buffer__ mutates self -->
# Bug report

### Bug description

bytearray_strip_impl_helper takes the argument's buffer (:2440), reads `myptr = PyByteArray_AS_STRING(self)` and `mysize` (:2445-2446), finds `left` and `right`, then calls PyBuffer_Release(&vbytes) (:2460-2461) and only then copies `right - left` bytes from `myptr + left` (:2462). For an argument whose class defines __release_buffer__ (PEP 688) the release runs Python code while `self` is not exported, so it can resize `self`: `self.clear()` frees the storage `myptr` points into, and the copy reads freed memory. With a large bytearray the process dies with SIGSEGV. Without a resize, an in-place write in __release_buffer__ changes the bytes that are copied after the bounds were computed, so the result is not stripped: `bytearray(b" a ").strip(B())` gives `bytearray(b" ")`. The other methods of this file that take a buffer of their argument either raise ob_exports first (find, split, join, hex, %) or release only after the copy (translate, setslice, +=, +, comparison). Lean: StripCopiesScanned (the copy reads the bytes the loops scanned) is refuted on `b" a "` with an in-place write in __release_buffer__ (strip_rewritten), and strip_freed shows the read of freed storage for `self.clear()`. StripNoRelAgrees, for arguments whose release runs no Python code, is proven: the result is then the strip of the contents as __buffer__ left them.

```python
import subprocess, sys
crash = '''
ba = bytearray(b"x" * (1 << 22))
class S:
    def __buffer__(self, flags):
        return memoryview(b" ")
    def __release_buffer__(self, view):
        ba.clear()
ba.strip(S())
'''
codes = []
for m in ("strip", "lstrip", "rstrip"):
    r = subprocess.run([sys.executable, "-I", "-c", crash.replace(".strip(", "." + m + "(")],
                       capture_output=True, text=True)
    codes.append(r.returncode)
print("clear() in __release_buffer__: exit status", codes)
s = bytearray(b" a ")
class B:
    def __buffer__(self, flags):
        return memoryview(b" ")
    def __release_buffer__(self, view):
        s[1] = 0x20
r = s.strip(B())
print("in-place write in __release_buffer__:", r)
```

**Expected:** The bytes are copied before the argument's buffer is released (or ob_exports is raised around the helper), so `b" a ".strip(B())` is `bytearray(b"a")` and nothing reads freed memory.

**Actual:** python3 3.15.2: exit status [-11, -11, -11] (SIGSEGV for strip, lstrip and rstrip), and the in-place case gives bytearray(b' '). main (python.exe 3.16.0a1+dev heads/main:ef1fce0): the same.

**Cause:** Objects/bytearrayobject.c:2460-2462: PyBuffer_Release(&vbytes), which can run __release_buffer__, comes before PyByteArray_FromStringAndSize(myptr + left, right - left), which reads through the pointer taken at :2445.

**Possible fix:** Create the result before releasing the argument's buffer (swap :2460-2461 and :2462), or raise self->ob_exports around the helper as bytearray_split_impl does.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/bytesobj-bytearray-strip-release-uaf.yaml
