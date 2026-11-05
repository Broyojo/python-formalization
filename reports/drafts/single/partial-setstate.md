<!-- title: functools.partial.__setstate__ with a tuple subclass as args miscounts placeholders, then crashes when called -->
### Crash report

`partial.__setstate__` counts the `Placeholder`s in the state's `args` by reading the tuple's storage, and only then converts a tuple subclass to a plain tuple with `PySequence_Tuple`, which runs the subclass's `__iter__`. The stored args and the stored placeholder count then describe two different tuples, and the call trusts the count.

```python
from functools import Placeholder, partial

class T(tuple):
    def __iter__(self):
        return iter((Placeholder,) * 40 + (1,))

def f(*a):
    return a

p = partial(f)
p.__setstate__((f, T((Placeholder, 1)), {}, None))
p(10)   # segfault in partial_vectorcall
```

With `__iter__` returning `iter((1, 2))` instead, `p(10)` returns `(1, 2)` and silently drops the argument. A state with keywords crashes through `partial_call` the same way.

I'd expect the count to be taken from the tuple that is stored, or a `TypeError` for an args tuple that changes on iteration.

Cause: Modules/_functoolsmodule.c:821-832 count placeholders in the raw tuple, and :834-838 call `PySequence_Tuple` afterwards. `partial_vectorcall` (:535-548) and `partial_call` (:645-660) index and copy by that count.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

### Output from running 'python -VV' on the command line:

Python 3.15.2 (tags/v3.15.2:5e58eaa, Nov  5 2026, 20:20:36) [GCC 11.4.0]

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. The code blocks were rerun on 3.15.2 and main during technical review; the human submitter must review the report before filing. Record: [corelibs-partial-setstate-phcount](https://github.com/Broyojo/python-formalization/blob/main/bugs/corelibs-partial-setstate-phcount.yaml)
