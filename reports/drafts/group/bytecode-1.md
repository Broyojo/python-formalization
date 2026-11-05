<!-- title: Small inconsistencies in the bytecode interpreter found by a formal model -->
# Bug report

### Bug description

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped here so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. LOAD_ATTR_PROPERTY and LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN push the getter's frame with no recursion check, so a recursive property or __getattribute__ passes the recursion limit once its site has specialized

The generic `LOAD_ATTR` reaches a Python property getter through `property.__get__`, and an overriding `__getattribute__` through `slot_tp_getattr_hook`; both call it from C, so the recursion limit is enforced when its frame starts (`_Py_EnterRecursivePy`). The specialized forms inline the call. `LOAD_ATTR_PROPERTY` (Python/bytecodes.c:3070-3077) and `LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN` (:3098-3105) are `_GUARD_TYPE_VERSION + _CHECK_PEP_523 + _LOAD_ATTR_*_FRAME + _SAVE_RETURN_OFFSET + _PUSH_FRAME`. `_PUSH_FRAME` (:4628-4642) decrements `py_recursion_remaining` (:4637) and tests nothing, and neither macro contains `_CHECK_RECURSION_REMAINING` (:4611-4613), which `CALL_PY_GENERAL`, `CALL_PY_EXACT_ARGS`, `CALL_BOUND_METHOD_*` and `CALL_KW_PY` carry before their `_PUSH_FRAME`. So a property (or `__getattribute__`) whose body reads the same attribute again keeps descending past the limit once the `self.p` site has specialized. It stops only when the data-stack chunk is full: `_PyThreadState_HasStackSpace` fails (:3062, :3087), the site exits to the generic form, and the C call raises `RecursionError` because the counter has long gone below zero. How far past the limit it gets depends on where the chunk boundary falls.

<details><summary>Reproducer</summary>

```python
import os, sys
LIMIT, DEPTH = 200, 1000
sys.setrecursionlimit(LIMIT)
state = {"d": 0, "max": 0}
BODY = ("        state['d'] += 1\n        state['max'] = max(state['max'], state['d'])\n"
        "        try:\n            return {nxt}\n        finally:\n            state['d'] -= 1\n")
KINDS = {
    "LOAD_ATTR_PROPERTY": "class {cls}:\n    @property\n    def p(self):\n" + BODY,
    "LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN": "class {cls}:\n    def __getattribute__(self, n):\n" + BODY,
}
def depth(f):
    state["d"] = state["max"] = 0
    try:
        f()
        return None
    except RecursionError:
        return state["max"]
hit = False
for kind, tmpl in KINDS.items():
    # Each level its own class and code object: every attribute site runs once, generic.
    src = "".join(tmpl.format(cls=f"A{i}", nxt=(f"A{i + 1}().p" if i + 1 < DEPTH else "1"))
                  for i in range(DEPTH))
    ns = {"state": state}
    exec(compile(src, "<generic>", "exec"), ns)
    generic = depth(lambda: ns["A0"]().p)
    # One class whose `self.p` site recurses into itself: it specializes after a few runs.
    ns2 = {"state": state}
    exec(compile(tmpl.format(cls="B", nxt="self.p"), "<shared>", "exec"), ns2)
    specialized = depth(lambda: ns2["B"]().p)
    print(kind, "levels before RecursionError: generic", generic, "specialized", specialized, flush=True)
    if generic is not None and specialized is not None and generic <= LIMIT < specialized:
        hit = True
if hit:
os._exit(0)
```

</details>

#### 2. SEND_GEN and FOR_ITER_GEN push a generator frame with no recursion check, so a chain of delegating generators passes the recursion limit once its site has specialized

The generic path enforces the recursion limit when it enters a generator frame. `_SEND` (Python/bytecodes.c:1676) inlines a generator with `DISPATCH_INLINED` (:1694), which goes through the `start_frame` label, where `_Py_EnterRecursivePy` (:6580) raises `RecursionError`. Generic `FOR_ITER` reaches the same check through `tp_iternext` and the evaluation loop. The specialized forms do not. `SEND_GEN` (:1740-1745) and `FOR_ITER_GEN` (:4118-4123) are `_CHECK_PEP_523` + a frame op + `_PUSH_FRAME`. `_PUSH_FRAME` (:4628) decrements `py_recursion_remaining` (:4637) and tests nothing, and neither macro contains `_CHECK_RECURSION_REMAINING` (:4611), which `CALL_PY_GENERAL`, `CALL_PY_EXACT_ARGS`, `CALL_BOUND_METHOD_GENERAL` and `CALL_KW_PY` do contain. So one `yield from` or `for` site that has specialized descends a chain of generators of any depth without a `RecursionError`, while the same chain on unspecialized code stops at the limit. Whether `next(g)` raises depends on whether the site has warmed up.

<details><summary>Reproducer</summary>

```python
import os, sys
SEND = "def link(inner):\n    yield from inner\n"
FOR = "def link(inner):\n    for x in inner:\n        yield x\n"
def fresh(src):
    ns = {}
    exec(compile(src, "<chain>", "exec"), ns)
    return ns["link"]
def leaf():
    yield 1
keep = []
def run(links):
    g = leaf()
    for link in links:
        g = link(g)
    keep.append(g)
    try:
        return next(g)
    except RecursionError:
        return "RecursionError"
LIMIT, DEPTH = 200, 1000
sys.setrecursionlimit(LIMIT)
out = {}
for name, src in (("SEND", SEND), ("FOR_ITER", FOR)):
    # Own code object per level: each site runs once and stays generic.
    generic = run([fresh(src) for _ in range(DEPTH)])
    # One code object: its site specializes after a few executions.
    shared = fresh(src)
    specialized = run([shared] * DEPTH)
    out[name] = (generic, specialized)
    print(name, "generic:", generic, "specialized:", specialized, flush=True)
if any(g == "RecursionError" and s == 1 for g, s in out.values()):
os._exit(0)
```

</details>

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Drafted with AI assistance (Claude); each case was reproduced on 3.15.2 and on main and the report reviewed before filing. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
