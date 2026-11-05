<!-- title: Calling Struct.__init__ on a live Struct reaches freed and … -->
# Bug report

### Bug description

Struct.__init__ can be called again on a Struct that is in use. prepare_s frees s_codes and replaces
s_size and s_len (Modules/_struct.c:1786-1791), and no method or iterator guards against it. A
conversion such as __index__ can do this in the middle of a method, and any code can do it between
two next() calls of an iterator. This has one root cause and these consequences:
1. s_pack_internal keeps walking the freed s_codes after the conversion returns (:2342, :2409).
   This use-after-free segfaults with allocator churn on 3.15.2 and on main.
2. iter_unpack, after a larger format: unpackiter_iternext reads past the buffer, because the only
   bound is an assert (:2245). This returns heap contents as bytes on 3.15.2 and on main.
3. iter_unpack, after a zero-sized format: unpackiter_len divides by zero (:2220). SIGFPE on
   3.15.2 and on main. next() on such an iterator also never ends.
4. iter_unpack itself, when the buffer's __buffer__ installs a zero-sized format: the zero test
   (:2291) runs before PyObject_GetBuffer (:2303), and the % at :2307 divides by zero. SIGFPE on
   3.15.2 and on main (python/cpython#158695).
Struct.pack finishes with the new s_size (:2457), which 3.15.2 refuses for a larger format with
ValueError "size larger than allocated size", so that path no longer discloses memory. pack_into
converts the offset before it compares the count (Modules/clinic/_struct.c.h), so an offset can no
longer install a longer format; a packed value's __index__ still can, which is case 1.

```python
import struct, warnings
warnings.simplefilter('ignore')
s = struct.Struct('b')
it = s.iter_unpack(bytes(8))
s.__init__('0s')
it.__length_hint__()
```

**Expected:** An exception, or a Struct that cannot be changed while in use. No read outside the buffer, no crash.

**Actual:** python3 3.15.2: 64 bytes read from an 8-byte buffer, length hint exit status -8, iter_unpack exit status -8 (SIGFPE). REPRODUCED. main 3.16.0a1+dev (ef1fce0): the same. REPRODUCED.

**Cause:** prepare_s frees s_codes at Modules/_struct.c:1787-1788 with no check that a method or iterator is using the object. s_pack_internal holds a pointer into it across e->pack (:2342, :2402, :2409). unpackiter_iternext and unpackiter_len read so->s_size afresh (:2245-2249, :2220). Struct_iter_unpack_impl tests s_size before the buffer conversion and divides by it after (:2291, :2303, :2307).

**Possible fix:** Refuse __init__ on an initialised Struct, as the FutureWarning announces. Failing that: make the iterator keep its own copy of the size, and take a private reference to the codes in s_pack_internal.

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
