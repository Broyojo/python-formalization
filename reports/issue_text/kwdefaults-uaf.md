<!-- title: Use-after-free when a __kwdefaults__ key's __eq__ replaces __kwdefaults__ during a call -->
<!-- form: crash -->
<!-- records: bytecode-kwonly-defaults-borrowed-dict -->
When a call leaves a keyword-only parameter unbound, `initialize_locals` looks up its default in `func.__kwdefaults__` without holding a reference to the dict. `__kwdefaults__` can be any dict, so a key whose hash matches the parameter name runs its `__eq__` during the lookup. If that `__eq__` sets `f.__kwdefaults__ = None`, the dict is freed and the lookup goes on reading it.

```python
# run with PYTHONMALLOC=debug to make the use-after-free visible
class K:
    def __hash__(self):
        return hash('b')
    def __eq__(self, other):
        f.__kwdefaults__ = None
        return False

def f(*, b):
    return b

f.__kwdefaults__ = {K(): 1}
f()
```

With `PYTHONMALLOC=debug`: `Segmentation fault` in `_Py_dict_lookup` (called from `PyDict_GetItemRef` in `initialize_locals`). Without it, the freed dict is read silently and the call raises the expected `TypeError`.

Cause: Python/ceval.c:1949-1951 passes the borrowed `func->func_kwdefaults` to `PyDict_GetItemRef`. Taking a strong reference around the lookup would fix it.
