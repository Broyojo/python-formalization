<!-- title: array.tofile() reads past the array (NULL + 65536 after clear()) when … -->
# Bug report

### Bug description

tofile computes nbytes and nblocks from Py_SIZE(self) once (Modules/arraymodule.c:1807-1811),
then for each 64 KiB block reads self->ob_item + i*BLOCKSIZE again and copies `size` bytes
computed from the old nbytes (:1822-1828), calling f.write(bytes) in between (:1831). A write()
that clears or shrinks the array frees or reallocates the buffer, so the next block reads freed
memory, past the new buffer, or from NULL + 65536 after clear(). A write that only grows the
array is safe. No buffer is exported during the call, so nothing stops the resize.
Lean (lean/PyLean/Sequences/ArrayFile.lean): ArrayToFileSafe (tofile never reads outside the
items, for every write callback) is refuted by a 'Zd' array of 4097 items and a write that
clears it; ArrayToFile states the exact calls for every write that leaves the array alone.

```python
import subprocess, sys
code = (
    "import array\n"
    "class W:\n"
    "    def __init__(self, a): self.a = a\n"
    "    def write(self, b): self.a.clear()\n"
    "a = array.array('Zd', [0j] * 4097)\n"
    "a.tofile(W(a))\n"
    "print('no crash')\n")
p = subprocess.run([sys.executable, '-I', '-c', code], capture_output=True, text=True)
print(p.returncode, p.stdout.strip())
```

**Expected:** Either the remaining blocks of the current (empty) array, i.e. nothing more, or BufferError for resizing during tofile; never a read outside the buffer.

**Actual:** python3 3.15.2: -11 (SIGSEGV). REPRODUCED. main (python.exe 3.16.0a1+dev ef1fce0): identical. REPRODUCED.

**Cause:** Modules/arraymodule.c:1807-1811 (nbytes, nblocks computed once), :1822 (`ptr = self->ob_item + i*BLOCKSIZE` with the current, possibly NULL, ob_item), :1826-1827 (size from the stale nbytes), :1831 (the write call that can resize the array).

**Possible fix:** Increment self->ob_exports around the loop (resizes then raise BufferError), or recompute the size from Py_SIZE(self) on every iteration and stop when the block starts past the end.

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
