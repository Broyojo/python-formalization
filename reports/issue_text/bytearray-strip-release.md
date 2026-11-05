<!-- title: bytearray.strip() reads freed memory if the argument's __release_buffer__ resizes the bytearray -->
<!-- form: crash -->
<!-- records: bytesobj-bytearray-strip-release-uaf -->
`bytearray.strip(chars)` (and `lstrip`/`rstrip`) takes a pointer into the bytearray, finds the bounds, then releases the argument's buffer, and only then copies the bytes. If the argument's class defines `__release_buffer__` (PEP 688), that release runs Python code, which can resize the bytearray and free the storage the pointer refers to.

```python
ba = bytearray(b"x" * (1 << 22))

class S:
    def __buffer__(self, flags):
        return memoryview(b" ")
    def __release_buffer__(self, view):
        ba.clear()

ba.strip(S())   # segfault
```

Output: `Segmentation fault`, the same for `lstrip` and `rstrip`. With a small bytearray and an in-place write instead of `clear()`, the result is built from the modified bytes, not the ones the bounds were computed on.

Cause: Objects/bytearrayobject.c:2460-2462 calls `PyBuffer_Release(&vbytes)` before `PyByteArray_FromStringAndSize(myptr + left, right - left)`. Copying first and releasing after would fix it.
