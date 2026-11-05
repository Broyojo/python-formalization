<!-- title: Reinitializing an active Struct lets iter_unpack read past its buffer or divide by zero -->
<!-- form: crash -->
<!-- records: textlibs-struct-reinit-memory-safety -->
An `iter_unpack()` iterator keeps the Struct object, but reads its current size on each iteration. Calling `Struct.__init__()` again changes the size without revalidating the iterator's buffer. A larger format reads beyond the buffer; a zero-sized format makes the length hint divide by zero. Reinitialization emits a warning in 3.15.2 but is still allowed.

```python
import struct, subprocess, sys, warnings
warnings.simplefilter('ignore')
s = struct.Struct('b')
it = s.iter_unpack(bytes(8))
next(it)
s.__init__('64s')
leaked = next(it)[0]
print('read', len(leaked), 'bytes from an 8-byte buffer')
code = """
import struct, warnings
warnings.simplefilter('ignore')
s = struct.Struct('b')
it = s.iter_unpack(bytes(8))
s.__init__('0s')
it.__length_hint__()
"""
p = subprocess.run([sys.executable, '-c', code], capture_output=True)
print('length hint exit status', p.returncode)
code2 = """
import struct, warnings
warnings.simplefilter('ignore')
s = struct.Struct('b')
class B:
    def __buffer__(self, flags):
        s.__init__('0s')
        return memoryview(bytes(8))
s.iter_unpack(B())
"""
q = subprocess.run([sys.executable, '-c', code2], capture_output=True)
print('iter_unpack exit status', q.returncode)
```

Recorded on 3.15.2 and main:

```text
read 64 bytes from an 8-byte buffer
length hint exit status -8
iter_unpack exit status -8
```

Both `-8` exits are SIGFPE on the tested build. Expected: an exception or a stable format for the active operation, with no out-of-bounds read or crash. The code deliberately reports only the length of the out-of-bounds result.

Cause: Modules/_struct.c:1786-1791 frees the old format codes and replaces the size and field count. `unpackiter_iternext` (:2245-2249) uses the new size with only an assertion for the buffer bound; `unpackiter_len` (:2220) divides by it. `Struct_iter_unpack_impl` checks for zero before `PyObject_GetBuffer`, which can run Python, and then uses the possibly changed size for `%` (:2291-2307).

The record also identifies a pack-time use-after-free: `s_pack_internal` retains a format-code pointer across a value conversion that can reinitialize the Struct (:2342, :2402-2409). That variant is not exercised above. Refusing reinitialization of an initialized Struct would address the shared cause; supporting it requires stable codes and sizes for active operations.

The buffer-callback division case was previously reported as gh-158695 and closed with a batch of automated filings. The record also notes related bugforge entries. Review those before filing so that this is presented as related paths rather than wholly new behavior.
