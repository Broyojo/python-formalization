<!-- title: partial.__setstate__ counts placeholders on a tuple subclass's storage … -->
# Bug report

### Bug description

partial_setstate walks the storage of the state's args tuple with PyTuple_GET_ITEM to check for a
trailing Placeholder and to count placeholders (:821-832), and only then turns a tuple subclass into a
real tuple with PySequence_Tuple (:834-838), which runs the subclass's __iter__. The stored args and
the stored phcount then describe two different tuples. partial_call and partial_vectorcall trust
phcount: with more placeholders in args than phcount they read past the end of the call's argument
array, and with fewer they size the stack by phcount while the memcpy at :546-548 copies from j, so it
writes past the end. Both crash the interpreter from pure Python, with no threads and no re-entrancy. The
write needs nothing large: a tuple of four items, phcount 2 and three call arguments overrun small_stack,
and glibc stops with "stack smashing detected". A smaller form of the same defect is
silent: raw (Placeholder, 1), iteration (1, 2) gives p(10) == f(1, 2), dropping the argument.

```python
import functools
import subprocess
import sys
from functools import Placeholder, partial
class T(tuple):
    def __iter__(self):
        return iter((1, 2))
def f(*a):
    return a
p = partial(f)
p.__setstate__((f, T((Placeholder, 1)), {}, None))
silent = p(10)
print('argument dropped:', silent)
crash = """
from functools import Placeholder, partial
class T(tuple):
    def __iter__(self):
        return iter((Placeholder,) * 40 + (1,))
def f(*a):
    return a
p = partial(f)
p.__setstate__((f, T((Placeholder, 1)), {}, None))
print(len(p(10)))
"""
r = subprocess.run([sys.executable, '-c', crash], capture_output=True, text=True, timeout=60)
print('subprocess exit', r.returncode)
```

**Expected:** phcount describes the stored args in every path: either the count is taken after the conversion, or the state is rejected. No out-of-bounds access.

**Actual:** python3 3.14.7: argument dropped: (1, 2); subprocess exit -11 (SIGSEGV), faulthandler points into partial_vectorcall. A kw-carrying state crashes through partial_call as well, and a third form, raw (Placeholder,) * 100000 + (1,) with iteration (1,) and 100001 call arguments, makes the memcpy at :547 overflow small_stack (exit -11); raw (Placeholder, Placeholder, 1), iteration (1, 2, 3, 4) and three call arguments abort with stack smashing detected (exit -6). REPRODUCED. main (python 3.16.0a1+dev): REPRODUCED, the same code order at Modules/_functoolsmodule.c:916-938. python3 3.15.2: REPRODUCED. main (3.16.0a1+dev): REPRODUCED.

**Cause:** Modules/_functoolsmodule.c:821-832 read the raw tuple, :834-838 call PySequence_Tuple after that. partial_call :645-660 and partial_vectorcall :535-548 then index args with j and copy by phcount.

**Possible fix:** Do the PySequence_Tuple conversion first, and run the trailing-Placeholder check and the count on the converted tuple. The same change to Lib/functools.py:415-419 keeps the twins together.

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
