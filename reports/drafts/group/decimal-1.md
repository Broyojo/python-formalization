<!-- title: Small inconsistencies in decimal found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. _decimal's Context() copies the flags set on DefaultContext, although flags=None is documented to clear them

The Context constructor documents that with no flags argument all flags are cleared. In _decimal it starts from a copy of the whole DefaultContext template, status word included, and flags=None then leaves that word alone. So any flag set on DefaultContext appears in every later Context(): decimal.DefaultContext.divide(Decimal(1), Decimal(3)) # sets Inexact and Rounded on the template decimal.Context().flags[decimal.Inexact] -> True (_pydecimal: 0) decimal.Context(prec=5).flags[decimal.Rounded] -> True (_pydecimal: 0) A program that creates a context, computes, and then reads flags[Inexact] to decide whether a result is exact gets a wrong answer for an exact computation. The other paths from the template all clear the word: a new thread's context (init_current_context) and setcontext(DefaultContext).

<details><summary>Reproducer</summary>

```python
import _decimal as C, _pydecimal as P
def stale(M):
    D = M.DefaultContext
    D.clear_flags()
    try:
        D.divide(M.Decimal(1), M.Decimal(3))
        n = M.Context()
        return bool(n.flags[M.Inexact]), bool(n.flags[M.Rounded])
    finally:
        D.clear_flags()
c, p = stale(C), stale(P)
print('_decimal   Context() after DefaultContext.divide: Inexact, Rounded =', c)
print('_pydecimal Context() after DefaultContext.divide: Inexact, Rounded =', p)
if c == (True, True) and p == (False, False):
    print("Observed the reported behavior.")
```

</details>

#### 2. _decimal's Decimal.__format__ ignores everything after an embedded NUL in the format spec

_decimal_Decimal___format___impl hands the spec's UTF-8 buffer to libmpdec as a NUL-terminated C string and has the length in hand but does not check it, so a spec with an embedded NUL is cut there and the rest is never validated. An invalid spec is accepted and formatted with its prefix: format(_decimal.Decimal('1234.5'), '10\x00xyz') -> ' 1234.5' format(_decimal.Decimal('1234.5'), '.2f\x00') -> '1234.50' format(_pydecimal.Decimal('1234.5'), '10\x00xyz') -> ValueError format(1234.5, '10\x00xyz'), format(1234, '10\x00xyz'), format(Fraction(3, 2), '10\x00xyz') -> ValueError It does know about NUL: it special-cases a NUL fill character at position 0, but only there. A neighbouring, separate oddity: float and complex accept exactly one trailing NUL, because Objects/unicode_formatter.c:558 reads it as the type character and :576 treats '\0' as "no type". So format(1234.5, '10\x00') works there, while int, str, Fraction and _pydecimal raise ValueError. _decimal differs in discarding any tail after the NUL, of any length, so the specs in the reproducer are the ones every other numeric type rejects.

*May be intended:* Not intended: the NUL-fill special case at _decimal.c:3791-3800 shows NUL was considered, and the fallback path through _pydecimal already rejects these specs when libmpdec's parser fails first. Same class as other embedded-NUL fixes in CPython's C code.

<details><summary>Reproducer</summary>

```python
import _decimal as C, _pydecimal as P
def fmt(x, spec):
    try:
        return repr(format(x, spec))
    except ValueError:
        return 'ValueError'
hits = 0
for spec, want in [('10\x00xyz', "'    1234.5'"), ('.2f\x00', "'1234.50'"), ('x>10\x00z', "'xxxx1234.5'")]:
    c = fmt(C.Decimal('1234.5'), spec)
    p = fmt(P.Decimal('1234.5'), spec)
    f = fmt(1234.5, spec)
    print(ascii(spec), '_decimal:', c, ' _pydecimal:', p, ' float:', f)
    hits += (c == want and p == 'ValueError' and f == 'ValueError')
if hits == 3:
    print("Observed the reported behavior.")
```

</details>

#### 3. _decimal's Context.flags compares unequal to its own copy after InvalidOperation: SignalDict == compares raw status bits, not items

ctx.flags is a MutableMapping from signals to bools, but its == compares the underlying libmpdec status words. One signal, InvalidOperation, covers seven status bits: an operation sets the one bit for its condition, while assigning the signal or converting a dict sets all seven. So two flag mappings with identical items can compare unequal: c = decimal.Context(traps=[]) c.divide(Decimal(0), Decimal(0)) c.flags[decimal.InvalidOperation] -> True c.flags == c.flags.copy() -> False (_pydecimal: True) c.flags == dict(c.flags) -> False (_pydecimal: True) c.flags != c.flags.copy() -> True d = decimal.Context(traps=[]); d.create_decimal('xyz') c.flags == d.flags -> False, though c.flags[s] == d.flags[s] for every s (_pydecimal: True) The usual way to ask whether a computation raised any new flag is to snapshot the flags and compare them afterwards, and that comparison reports a change that did not happen.

<details><summary>Reproducer</summary>

```python
import _decimal as C, _pydecimal as P
def probe(M):
    a = M.Context(traps=[])
    a.divide(M.Decimal(0), M.Decimal(0))
    b = M.Context(traps=[])
    b.create_decimal('xyz')
    same_items = all(a.flags[s] == b.flags[s] for s in a.flags)
    return same_items, bool(a.flags[M.InvalidOperation]), a.flags == a.flags.copy(), a.flags == b.flags
c, p = probe(C), probe(P)
print('_decimal   same items, InvalidOperation, flags == copy, a.flags == b.flags:', c)
print('_pydecimal same items, InvalidOperation, flags == copy, a.flags == b.flags:', p)
if c == (True, True, False, False) and p == (True, True, True, True):
    print("Observed the reported behavior.")
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
AI tools (Claude and Codex) helped investigate these findings and prepare the draft. The code blocks were rerun on 3.15.2 and main during technical review; the human submitter must review the report before filing. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
