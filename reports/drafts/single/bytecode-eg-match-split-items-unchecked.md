<!-- title: except* trusts the items returned by an overridden split() -->
# Bug report

### Bug description

For an exception group that does not match the except* type as a whole, _PyEval_ExceptionGroupMatch (Python/ceval.c:2313-2340) calls the group's split attribute with PyObject_CallMethod, so a subclass's own split() runs. Since gh-128049 the result is checked to be an exact tuple of at least two items (:2321-2337), but the two items are taken as they are: *match = PyTuple_GET_ITEM(pair, 0), *rest = PyTuple_GET_ITEM(pair, 1) (:2339-2340). CHECK_EG_MATCH (Python/bytecodes.c:3415-3439) then calls PyErr_SetHandledException(match_o) for any match that is not None (:3434-3436), and _PyErr_SetHandledException (Python/errors.c:619-622) stores it in tstate->exc_info->exc_value without a type check. With split() returning (1, None) the handler body runs with `as e` bound to 1 and sys.exception() returning 1. The next exception raised in the handler goes through _PyErr_SetObject, which reads the topmost handled exception as a PyBaseExceptionObject to chain __context__ (PyException_GetContext), and the interpreter dies with SIGSEGV (C stack: PyException_GetContext <- _PyErr_SetObject <- _PyEval_EvalFrameDefault). A non-exception `rest`, as in split() returning (None, 1), reaches the re-raise and the top level then reports "print_exception(): Exception expected for value, int found": an int was raised. The Lean model states the body (CheckEgMatchRules, ExceptionGroupMatchRules, proven) and refutes "CHECK_EG_MATCH keeps the handled exception an exception instance" with split() returning (1, None).

```python
import subprocess, sys
body = (
    "import sys\n"
    "class EG(ExceptionGroup):\n"
    "    def split(self, t):\n"
    "        return (1, None)\n"
    "try:\n"
    "    raise EG('x', [ValueError()])\n"
    "except* TypeError as e:\n"
    "    print('handled:', repr(sys.exception()), flush=True)\n"
    "    MODE\n"
)
r1 = subprocess.run([sys.executable, '-c', body.replace('MODE', 'pass')], capture_output=True, text=True)
print(r1.returncode, r1.stdout.strip())
r2 = subprocess.run([sys.executable, '-c', body.replace('MODE', "raise KeyError('k')")],
                    capture_output=True, text=True)
print(r2.returncode, r2.stdout.strip())
```

**Expected:** A TypeError from CHECK_EG_MATCH (or from _PyEval_ExceptionGroupMatch) when the items split() returned are not exception instances or None, as for a non-tuple or a short tuple; the handler does not run with a non-exception as the handled exception.

**Actual:** 

**Cause:** Python/ceval.c:2339-2340 takes PyTuple_GET_ITEM(pair, 0) and (pair, 1) without checking that each is None or an exception instance (PyExceptionInstance_Check); Python/bytecodes.c:3434-3436 passes the match to PyErr_SetHandledException, which stores any object.

**Possible fix:** In _PyEval_ExceptionGroupMatch, after the size check, raise TypeError("%.200s.split must return a tuple of exceptions or None") unless each of the two items is Py_None or PyExceptionInstance_Check passes (and the group check, _PyBaseExceptionGroup_Check, for a non-None match, which is what PyErr_SetHandledException and the handler's `as e` assume).

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/bytecode-eg-match-split-items-unchecked.yaml
