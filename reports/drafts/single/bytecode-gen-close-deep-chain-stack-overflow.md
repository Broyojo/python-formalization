<!-- title: Closing a deep yield-from chain overflows the C stack -->
# Bug report

### Bug description

gen_close (:463-541) closes the sub-iterator of a suspended `yield from` through gen_close_iter (:424-449), which calls gen_close directly for an exact generator or coroutine; _gen_throw (:624-726) calls itself at :683 in the same way. Neither has a recursion check: the walk down the chain runs no Python code, so nothing reaches _Py_EnterRecursiveCall or the eval loop's limit. A chain does not need deep Python recursion to build, because a delegation link is formed by one short resume of the outer generator while the inner one is suspended at a plain `yield`:

```python
import sys
assert sys.getrecursionlimit() == 1000
def link():
    sub = yield
    while sub is None:
        sub = yield
    yield from sub
first = g = link(); next(g)
for i in range(1000000):
    h = link(); next(h)
    g.send(h)
    g = h
first.close()
print("survived")
```

**Expected:** A RecursionError, or an iterative walk down the chain; no crash, as for other recursion in C such as repr() or comparison of deeply nested containers.

**Actual:** python3 3.15.2: SIGSEGV (returncode -11) for close(). python3 3.14.7: the same for close(), for throw(ValueError) and for dropping the last reference; the faulthandler C stack is two frames repeated. main (python.exe 3.16.0a1+dev ef1fce0): SIGSEGV for all three.

**Cause:** Objects/genobject.c:430 (gen_close_iter calls gen_close) and :495 (gen_close calls gen_close_iter), and :683 (_gen_throw calls itself), with no _Py_EnterRecursiveCall or _Py_ReachedRecursionLimit on the path. Main has the same recursion (Objects/genobject.c gen_close_iter:432, gen_close).

**Possible fix:** In gen_close_iter and in _gen_throw's generator branch, call _Py_EnterRecursiveCallTstate(tstate, " while closing a generator") / _Py_LeaveRecursiveCallTstate around the recursive call, so the chain ends in a RecursionError. Better for close(): walk the chain with an explicit loop, so that finalizing a long chain still closes every link; gen_finalize runs from dealloc, where a RecursionError would be unraisable and the chain would stay unclosed.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/bytecode-gen-close-deep-chain-stack-overflow.yaml
