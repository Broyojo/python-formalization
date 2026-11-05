<!-- title: dict.setdefault() segfaults on an instance __dict__ with a str-subclass key -->
# Bug report

### Bug description

Plain Python crashes the interpreter with SIGSEGV. An instance __dict__ is a split table: its keys are shared by every instance of the class, so a key can be present in the shared keys with no value in this dict. _Py_dict_lookup then returns ix >= 0 with *value_addr == NULL. Every other caller allows for that (`ix == DKIX_EMPTY || value == NULL`). The generic branch of dict_setdefault_ref_lock_held does not: it tests `ix == DKIX_EMPTY` only, falls through with value == NULL, and `Py_NewRef(value)` dereferences NULL.

```python
class C:
    pass
a = C()
a.x = 1            # 'x' is now in the shared keys
b = C()
b.y = 2
d = b.__dict__     # split table; 'x' has no value here
class S(str):
    pass
print('get', d.get(S('x'), 'default'), flush=True)
print('setdefault', d.setdefault(S('x'), 5), flush=True)
```

**Expected:** d.setdefault(S('x'), 5) returns 5 and d gains the key, as for any key that dict.get reports absent.

**Actual:** python3 3.15.2: `d.get(S('x'), 'default')` -> 'default', then SIGSEGV in setdefault, exit -11. main (3.16.0a1+dev, ef1fce0): identical.

**Cause:** Objects/dictobject.c:4817-4841: the split branch is taken only for exact str keys; otherwise :4834 calls _Py_dict_lookup, which on a split table sets *value_addr = mp->ma_values->values[ix] (:1367), possibly NULL. :4843 `if (ix == DKIX_EMPTY)` misses that case, and :4865-4869 runs `*result = incref_result ? Py_NewRef(value) : value`. Compare :2961, :3002, :3256, :3765, :4765, which all test `ix == DKIX_EMPTY || value == NULL`. With incref_result == 0 (PyDict_SetDefault) NULL is returned with no exception, and merge_from_seq2_lock_held (override == 0) silently drops the pair.

**Possible fix:** Treat a NULL value as absent: `if (ix == DKIX_EMPTY || value == NULL)` at :4843. insert_combined_dict already converts a split table when the key is not an exact str, so the insertion that follows is correct (insertdict relies on this at :1915-1925).

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/dictset-setdefault-split-null.yaml
