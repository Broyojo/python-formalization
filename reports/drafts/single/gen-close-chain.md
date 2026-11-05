<!-- title: Closing a long chain of yield-from generators overflows the C stack -->
### Crash report

`gen_close` closes a suspended `yield from` sub-generator by calling `gen_close` on it directly, and `_gen_throw` calls itself the same way. Neither checks the recursion limit, and no Python code runs on the way down, so a long delegation chain overflows the C stack. Building the chain needs no deep Python recursion: each link is made by one `send()`.

```python
def link():
    sub = yield
    while sub is None:
        sub = yield
    yield from sub

first = g = link(); next(g)
for i in range(1_000_000):
    h = link(); next(h)
    g.send(h)
    g = h

first.close()   # segfault
```

On main, `first.throw(ValueError)` and `del first` (with no other references) crash the same way.

I'd expect `RecursionError`, as for other deep recursion.

Cause: Objects/genobject.c:430 (`gen_close_iter` calls `gen_close`), :495 (`gen_close` calls `gen_close_iter`) and :683 (`_gen_throw` calls itself), with no `_Py_EnterRecursiveCall` on the path.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

### Output from running 'python -VV' on the command line:

Python 3.15.2 (tags/v3.15.2:5e58eaa, Nov  5 2026, 20:20:36) [GCC 11.4.0]

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. Results in the body are taken from the bug records; final interpreter reruns and human review are pending. Record: [bytecode-gen-close-deep-chain-stack-overflow](https://github.com/Broyojo/python-formalization/blob/main/bugs/bytecode-gen-close-deep-chain-stack-overflow.yaml)
