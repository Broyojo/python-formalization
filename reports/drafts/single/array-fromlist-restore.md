<!-- title: array.fromlist() regrows a callback-cleared array on its error path, exposing uninitialized items -->
### Bug report

If an item's `__index__` clears the array during `fromlist()`, the store fails its bounds check. The error path then resizes the cleared array back to its old length without restoring its old contents. For a sufficiently large array, clearing freed the buffer, so the restored items contain uninitialized memory.

```python
from array import array
a = array('q', range(100, 164))
class V:
    def __index__(self):
        a.clear()
        return 7
try:
    a.fromlist([V()])
except IndexError as e:
    print("IndexError:", e)
print("len", len(a), "first items", list(a[:4]))
```

Recorded on 3.15.2 and main: `IndexError: array assignment index out of range`, followed by length 64 and heap-dependent item values. Under `PYTHONMALLOC=debug`, every restored item is `-3617008641903833651`, the allocator's `0xCD` fill. The array should not expose never-written cells: either preserve the old contents or leave the state produced by the callback.

Cause: Modules/arraymodule.c:1871 calls `array_resize(self, old_size)` after a failing conversion/store, regardless of callback mutations. For this input, `clear()` freed the buffer; `array_resize` (:140-199) allocates new storage without initializing it. The list-size error path at :1877 has the same unconditional restore. Preventing resize during conversions, or converting into temporary storage before committing, would avoid rebuilding lost contents from an old length alone.

The record relates this to gh-152166, which concerns the successful-store path in the same function. Its recorded review of PR gh-152167 found that the error-path resize remains. This case may belong with that issue; recheck its current fix before filing.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. The code blocks were rerun on 3.15.2 and main during technical review; the human submitter must review the report before filing. Record: [sequences-array-fromlist-restore-stale](https://github.com/Broyojo/python-formalization/blob/main/bugs/sequences-array-fromlist-restore-stale.yaml)
