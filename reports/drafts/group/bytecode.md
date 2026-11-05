<!-- title: bytecode: 5 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. LOAD_ATTR_PROPERTY and LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN push the getter's frame with no recursion check, so a recursive property or __getattribute__ passes the recursion limit once its site has specialized

The generic `LOAD_ATTR` reaches a Python property getter through `property.__get__`, and an
overriding `__getattribute__` through `slot_tp_getattr_hook`; both call it from C, so the
recursion limit is enforced when its frame starts (`_Py_EnterRecursivePy`).
The specialized forms inline the call. `LOAD_ATTR_PROPERTY` (Python/bytecodes.c:3070-3077)
and `LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN` (:3098-3105) are `_GUARD_TYPE_VERSION +
_CHECK_PEP_523 + _LOAD_ATTR_*_FRAME + _SAVE_RETURN_OFFSET + _PUSH_FRAME`. `_PUSH_FRAME`
(:4628-4642) decrements `py_recursion_remaining` (:4637) and tests nothing, and neither macro
contains `_CHECK_RECURSION_REMAINING` (:4611-4613), which `CALL_PY_GENERAL`,
`CALL_PY_EXACT_ARGS`, `CALL_BOUND_METHOD_*` and `CALL_KW_PY` carry before their `_PUSH_FRAME`.
So a property (or `__getattribute__`) whose body reads the same attribute again keeps descending
past the limit once the `self.p` site has specialized. It stops only when the data-stack chunk is
full: `_PyThreadState_HasStackSpace` fails (:3062, :3087), the site exits to the generic form,
and the C call raises `RecursionError` because the counter has long gone below zero. How far past
the limit it gets depends on where the chunk boundary falls.

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

#### 2. CALL_ALLOC_AND_ENTER_INIT instantiates an abstract class, bypassing object.__new__'s ABC check

Calling a class whose `tp_new is object.__new__` and whose `__init__` is a simple Python
function specializes the CALL to `CALL_ALLOC_AND_ENTER_INIT`. The specialized opcode's
`_ALLOCATE_OBJECT` uop (Python/bytecodes.c:4766; 3.14 had one `_CHECK_AND_ALLOCATE_OBJECT`) allocates the instance directly with
`PyType_GenericAlloc` and then runs `__init__`; it never calls `tp_new`/`object_new`. But
`object_new` (Objects/typeobject.c:7462-7477) is where `Py_TPFLAGS_IS_ABSTRACT` is enforced:
it raises `TypeError: Can't instantiate abstract class ... without an implementation for
abstract method ...`. So a class with a non-empty `__abstractmethods__` that reaches this
specialization can be instantiated once it is hot, even though the first (generic) call
correctly raised `TypeError`. `specialize_class_call` / `get_init_for_simple_managed_python_class`
(Python/specialize.c:1626-1705) check `tp_new == object.__new__`, `tp_alloc ==
PyType_GenericAlloc`, heap type, and a simple-function `__init__`, but never
`Py_TPFLAGS_IS_ABSTRACT`.

<details><summary>Reproducer</summary>

```python
class C:
    def __init__(self):
        pass
C.__abstractmethods__ = frozenset({'f'})
def mk():
    return C()
created = 0
errors = 0
for _ in range(40):
    try:
        mk()
        created += 1
    except TypeError:
        errors += 1
print('created', created, 'errors', errors)
# The first (generic) call raises; once specialized, instantiation succeeds.
```

</details>

#### 3. CALL_EX_PY and CALL_KW_BOUND_METHOD push the callee's frame with no recursion check, so f(*args) and m(k=v) recursion passes the recursion limit once the site has specialized (duplicate of python/cpython#155151)

Already reported upstream as python/cpython#155151 (open), with an open fix,
python/cpython#156346. Recorded here because the Lean model refutes "CALL_EX_PY refines
CALL_FUNCTION_EX" and "CALL_KW_BOUND_METHOD refines CALL_KW", and a refutation needs a record.
The generic CALL_FUNCTION_EX (Python/bytecodes.c:5637-5711) and CALL_KW (:5419-5472) inline a
Python function with DISPATCH_INLINED, whose start_frame runs _Py_EnterRecursivePy and raises
RecursionError at the limit. Their specializations CALL_EX_PY (:5763-5771, new in 3.15) and
CALL_KW_BOUND_METHOD (:5542-5551) end in _PUSH_FRAME (:4628-4642), which decrements
py_recursion_remaining (:4637) and tests nothing, and neither macro has
_CHECK_RECURSION_REMAINING (:4611-4613), which CALL_PY_GENERAL, CALL_PY_EXACT_ARGS,
CALL_BOUND_METHOD_* and CALL_KW_PY carry before their frame op. So a recursion through
f(*args) or a bound method called with keywords goes past the limit once its site has
specialized.

<details><summary>Reproducer</summary>

```python
import os, sys

LIMIT, DEPTH = 50, 100
state = {"max": 0}

def recurse_star_args(depth, level=1):
    # CALL_FUNCTION_EX on a Python function specializes to CALL_EX_PY
    state["max"] = max(state["max"], level)
    if depth:
        recurse_star_args(*(depth - 1, level + 1))

class Recurse:
    def recurse(self, depth, level=1):
        # CALL_KW on a bound method specializes to CALL_KW_BOUND_METHOD
        state["max"] = max(state["max"], level)
        if depth:
            recurse_bound_method(depth=depth - 1, level=level + 1)

recurse_bound_method = Recurse().recurse

def recurse_plain(depth, level=1):
    # CALL_KW on a plain function specializes to CALL_KW_PY, which checks
    state["max"] = max(state["max"], level)
    if depth:
        recurse_plain(depth=depth - 1, level=level + 1)

def deepest(f):
    state["max"] = 0
    try:
        f(DEPTH)
        return state["max"], "no RecursionError"
    except RecursionError:
        return state["max"], "RecursionError"

for f in (recurse_star_args, recurse_bound_method, recurse_plain):
    for _ in range(5):  # warm the call sites up so that they specialize
        f(3)

sys.setrecursionlimit(LIMIT)
res = {"recurse_star_args": deepest(recurse_star_args), "recurse_bound_method": deepest(recurse_bound_method),
       "recurse_plain": deepest(recurse_plain)}
for name, (lvl, how) in res.items():
    print(f"{name}: {lvl} levels, {how} (limit {LIMIT})", flush=True)
if (res["recurse_plain"][1] == "RecursionError" and
        res["recurse_star_args"][1] == "no RecursionError" and
        res["recurse_bound_method"][1] == "no RecursionError"):
os._exit(0)
```

</details>

#### 4. throw() with an invalid argument leaves a plain generator alone but kills a delegating one: the arguments are validated only at the end of the yield-from chain

_gen_throw validates tb and typ only at throw_here (:719-725, through gen_set_exception :546-601).
With a `yield from` in progress (:651-717) the arguments are passed down first, so the check runs in the innermost generator. It
returns NULL with a TypeError and no effect there, and the delegating generator then treats this
as a failure of the sub-iterator: :712-714 throws the TypeError into its own frame at the `yield
from`. So g.throw(42) leaves a suspended plain generator suspended, but ends a delegating one
while its sub-generator stays suspended. A foreign sub-iterator with a `throw` method is handed
the bad arguments outright.

<details><summary>Reproducer</summary>

```python
def sub():
    yield 1
    yield 2
def outer(s):
    yield from s
def plain():
    yield 1
    yield 2
p = plain(); next(p)
try:
    p.throw(42)
except TypeError as e:
    print("plain:", e, "suspended", p.gi_suspended)
s = sub(); g = outer(s); next(g)
try:
    g.throw(42)
except TypeError as e:
    print("delegating:", e, "suspended", g.gi_suspended, "sub suspended", s.gi_suspended)
```

</details>

#### 5. SEND_GEN and FOR_ITER_GEN push a generator frame with no recursion check, so a chain of delegating generators passes the recursion limit once its site has specialized

The generic path enforces the recursion limit when it enters a generator frame. `_SEND`
(Python/bytecodes.c:1676) inlines a generator with `DISPATCH_INLINED` (:1694), which goes
through the `start_frame` label, where `_Py_EnterRecursivePy` (:6580) raises
`RecursionError`. Generic `FOR_ITER` reaches the same check through `tp_iternext` and the
evaluation loop.
The specialized forms do not. `SEND_GEN` (:1740-1745) and `FOR_ITER_GEN` (:4118-4123) are
`_CHECK_PEP_523` + a frame op + `_PUSH_FRAME`. `_PUSH_FRAME` (:4628) decrements
`py_recursion_remaining` (:4637) and tests nothing, and neither macro contains
`_CHECK_RECURSION_REMAINING` (:4611), which `CALL_PY_GENERAL`, `CALL_PY_EXACT_ARGS`,
`CALL_BOUND_METHOD_GENERAL` and `CALL_KW_PY` do contain.
So one `yield from` or `for` site that has specialized descends a chain of generators of
any depth without a `RecursionError`, while the same chain on unspecialized code stops at
the limit. Whether `next(g)` raises depends on whether the site has warmed up.

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

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
