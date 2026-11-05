<!-- title: decimal: 11 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. _decimal's Context() and IEEEContext() ignore DefaultContext.capitals and always use 1

A field not given to Context() is documented to come from DefaultContext. In _decimal every field
does except capitals, which context_new sets to 1 after copying the template:
  decimal.DefaultContext.capitals = 0
  decimal.Context().capitals        -> 1   (_pydecimal: 0)
  decimal.IEEEContext(128).capitals -> 1   (_pydecimal: 0)
  decimal.DefaultContext.clamp = 1
  decimal.Context().clamp           -> 1   (the same pattern, working)
_decimal disagrees with itself as well: a new thread's context does take capitals from the
template, because that path uses context_copy, so with capitals = 0 on the template a thread
prints 1E+3 as 1e+3 while Context() in the same thread prints 1E+3.

<details><summary>Reproducer</summary>

```python
import threading
import _decimal as C, _pydecimal as P
def caps(M):
    D = M.DefaultContext
    old = D.capitals
    seen = {}
    try:
        D.capitals = 0
        seen['Context()'] = M.Context().capitals
        seen['IEEEContext(128)'] = M.IEEEContext(128).capitals
        t = threading.Thread(target=lambda: seen.__setitem__('new thread', M.getcontext().capitals))
        t.start()
        t.join()
    finally:
        D.capitals = old
    return seen
c, p = caps(C), caps(P)
print('_decimal  ', c)
print('_pydecimal', p)
```

</details>

#### 2. _decimal's Context() copies the flags set on DefaultContext, although flags=None is documented to clear them

The Context constructor documents that with no flags argument all flags are cleared. In _decimal
it starts from a copy of the whole DefaultContext template, status word included, and flags=None
then leaves that word alone. So any flag set on DefaultContext appears in every later Context():
  decimal.DefaultContext.divide(Decimal(1), Decimal(3))     # sets Inexact and Rounded on the template
  decimal.Context().flags[decimal.Inexact]                  -> True    (_pydecimal: 0)
  decimal.Context(prec=5).flags[decimal.Rounded]            -> True    (_pydecimal: 0)
A program that creates a context, computes, and then reads flags[Inexact] to decide whether a
result is exact gets a wrong answer for an exact computation. The other paths from the template
all clear the word: a new thread's context (init_current_context) and setcontext(DefaultContext).

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
```

</details>

#### 3. _decimal's Decimal.__format__ ignores everything after an embedded NUL in the format spec

_decimal_Decimal___format___impl hands the spec's UTF-8 buffer to libmpdec as a NUL-terminated C string and has the
length in hand but does not check it, so a spec with an embedded NUL is cut there and the rest
is never validated. An invalid spec is accepted and formatted with its prefix:
  format(_decimal.Decimal('1234.5'), '10\x00xyz')   -> '    1234.5'
  format(_decimal.Decimal('1234.5'), '.2f\x00')     -> '1234.50'
  format(_pydecimal.Decimal('1234.5'), '10\x00xyz') -> ValueError
  format(1234.5, '10\x00xyz'), format(1234, '10\x00xyz'), format(Fraction(3, 2), '10\x00xyz') -> ValueError
It does know about NUL: it special-cases a NUL fill character at position 0, but only
there.
A neighbouring, separate oddity: float and complex accept exactly one trailing NUL, because
Objects/unicode_formatter.c:558 reads it as the type character and :576 treats '\0' as "no type".
So format(1234.5, '10\x00') works there, while int, str, Fraction and _pydecimal raise
ValueError. _decimal differs in discarding any tail after the NUL, of any length, so the specs in
the reproducer are the ones every other numeric type rejects.

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
```

</details>

#### 4. _decimal's Decimal.__format__ raises UnicodeEncodeError for a lone surrogate fill character

_decimal_Decimal___format___impl encodes the whole spec as UTF-8 before parsing it, so a spec containing a lone
surrogate raises UnicodeEncodeError, whether or not the surrogate would be valid there:
  format(_decimal.Decimal('1.5'), '\ud800<5')   -> UnicodeEncodeError
  format(_pydecimal.Decimal('-0.5'), '\ud800<5') -> '-0.5\ud800'
  format(1.5, '\ud800<5')                       -> '1.5\ud800\ud800'
  format(15, '\ud800<5')                        -> '15\ud800\ud800\ud800'
  format(Fraction(3, 2), '\ud800<5')            -> '3/2\ud800\ud800'
A surrogate outside the fill position is an invalid spec, where the other types raise
ValueError and _decimal raises UnicodeEncodeError (a subclass of ValueError).

<details><summary>Reproducer</summary>

```python
import _decimal as C, _pydecimal as P
from fractions import Fraction
def fmt(x):
    try:
        return ascii(format(x, '\ud800<5'))
    except Exception as e:
        return type(e).__name__
c = fmt(C.Decimal('1.5'))
others = [fmt(P.Decimal('1.5')), fmt(1.5), fmt(15), fmt(Fraction(3, 2))]
print('_decimal:', c)
print('_pydecimal, float, int, Fraction:', others)
```

</details>

#### 5. _decimal's Context.flags compares unequal to its own copy after InvalidOperation: SignalDict == compares raw status bits, not items

ctx.flags is a MutableMapping from signals to bools, but its == compares the underlying libmpdec
status words. One signal, InvalidOperation, covers seven status bits: an operation sets the one bit
for its condition, while assigning the signal or converting a dict sets all seven. So two flag
mappings with identical items can compare unequal:
  c = decimal.Context(traps=[])
  c.divide(Decimal(0), Decimal(0))
  c.flags[decimal.InvalidOperation]     -> True
  c.flags == c.flags.copy()             -> False   (_pydecimal: True)
  c.flags == dict(c.flags)              -> False   (_pydecimal: True)
  c.flags != c.flags.copy()             -> True
  d = decimal.Context(traps=[]); d.create_decimal('xyz')
  c.flags == d.flags                    -> False, though c.flags[s] == d.flags[s] for every s
                                           (_pydecimal: True)
The usual way to ask whether a computation raised any new flag is to snapshot the flags and compare
them afterwards, and that comparison reports a change that did not happen.

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
```

</details>

#### 6. _pydecimal's // and divmod return the quotient without _fix, so it can exceed Emax with no Overflow, unlike _decimal

__floordiv__ and __divmod__ return the quotient of _divide directly. Every other arithmetic result
in the module goes through _fix, and libmpdec finalizes this one too, so in a context whose Emax is
below prec - 1 the twins differ:
  c = Context(prec=28, Emax=10, Emin=-10)
  c.divide_int(Decimal(10)**20, Decimal(1))
      _pydecimal -> Decimal('100000000000000000000'), adjusted exponent 20 > Emax, no flags
      _decimal   -> raises Overflow (untrapped: Infinity with Overflow, Inexact, Rounded)
  c = Context(prec=9, Emax=5, clamp=1, traps=[])
  c.divide_int(Decimal('3E+3'), Decimal(-10))
      _pydecimal -> Decimal('-300')       no flags
      _decimal   -> Decimal('-300.000')   Clamped
The same value appears as the first item of divmod(). The remainder is finalized by both twins.

<details><summary>Reproducer</summary>

```python
import _pydecimal as P, _decimal as C
def probe(M):
    c = M.Context(prec=28, Emax=10, Emin=-10, traps=[])
    q = c.divide_int(M.Decimal(10) ** 20, M.Decimal(1))
    over = bool(c.flags[M.Overflow])
    d = M.Context(prec=9, Emax=5, Emin=-30, clamp=1, traps=[])
    r = d.divide_int(M.Decimal('3E+3'), M.Decimal(-10))
    return str(q), over, str(r), bool(d.flags[M.Clamped])
p, c = probe(P), probe(C)
print('_pydecimal', p)
print('_decimal  ', c)
```

</details>

#### 7. _pydecimal raises ValueError (int string-conversion limit) for decimals with more than 4300 digits: constructor, hash, floor/ceil/round, as_integer_ratio, +, -, *

The pure-Python decimal keeps the coefficient as a digit string `_int` and converts it with
int()/str() in many places. Since the int<->str conversion limit (default 4300 digits) these
conversions raise ValueError("Exceeds the limit (4300 digits) for integer string conversion")
for any coefficient (or intermediate) longer than 4300 digits, although decimal is an
arbitrary-precision type and the C implementation handles all of these:
  _pydecimal.Decimal('1' * 4301)                      -> ValueError   (_decimal: works)
  _pydecimal.Decimal(10 ** 4300)                      -> ValueError   (_decimal: works)
  hash(_pydecimal.Decimal((0, (1,) * 4301, 0)))       -> ValueError
  math.floor(_pydecimal.Decimal('1E+4300'))           -> ValueError   (int() of the same works)
  _pydecimal.Decimal((0, (1,) * 4301, 0)).as_integer_ratio() -> ValueError
  _pydecimal.Decimal(5) == 10 ** 4300                 -> ValueError   (a comparison raising)
  x = _pydecimal.Decimal('1' * 2200); x * x          -> ValueError at the default precision 28:
      __mul__ formats the exact 4400-digit product with str() before rounding it to 28 digits.
  x = _pydecimal.Decimal('9' * 4300); x + x          -> ValueError at the default precision 28:
      each operand is under the limit, but Decimal(result) formats the exact 4301-digit sum with
      str() before rounding it. x - (-x) fails the same way.
str(d) of such a value works, so Decimal(str(d)) does not round-trip.

<details><summary>Reproducer</summary>

```python
import math
import _pydecimal as P, _decimal as C
def kind(f):
    try:
        f()
        return 'ok'
    except Exception as e:
        return type(e).__name__
checks = {
    "Decimal('1'*4301)": lambda M: M.Decimal('1' * 4301),
    "Decimal(10**4300)": lambda M: M.Decimal(10 ** 4300),
    "hash(Decimal((0,(1,)*4301,0)))": lambda M: hash(M.Decimal((0, (1,) * 4301, 0))),
    "math.floor(Decimal('1E+4300'))": lambda M: math.floor(M.Decimal('1E+4300')),
    "Decimal('1'*2200)**2 via *": lambda M: M.Decimal('1' * 2200) * M.Decimal('1' * 2200),
    "Decimal(5) == 10**4300": lambda M: M.Decimal(5) == 10 ** 4300,
    "Decimal('9'*4300) + same": lambda M: M.Decimal('9' * 4300) + M.Decimal('9' * 4300),
    "Decimal('9'*4300) - (-same)": lambda M: M.Decimal('9' * 4300) - M.Decimal('-' + '9' * 4300),
}
bad = 0
for name, f in checks.items():
    p, c = kind(lambda: f(P)), kind(lambda: f(C))
    print(f'{name:36s} _pydecimal: {p:10s} _decimal: {c}')
    bad += (p == 'ValueError' and c == 'ok')
```

</details>

#### 8. _pydecimal.Decimal accepts 'ınf', 'İnfinity' and 'ſNaN' through re.IGNORECASE Unicode case folding; _decimal rejects them

The numeric-string regex is compiled with re.IGNORECASE on a str pattern, so its letters match
by Unicode case folding. U+0130 (İ) and U+0131 (ı) match the `i` of Inf/Infinity, and U+017F
(ſ, long s) matches the `s` of sNaN:
  _pydecimal.Decimal('ınf')      -> Decimal('Infinity')
  _pydecimal.Decimal('İnfinity') -> Decimal('Infinity')
  _pydecimal.Decimal('ſNaN')     -> Decimal('sNaN')
  _decimal.Decimal(any of them)  -> InvalidOperation (ConversionSyntax)
float('ınf') rejects the string too. A scan over every code point substituted into the letters
of Inf, Infinity, NaN, sNaN and 1E5 in both cases found exactly these three characters. The
other non-ASCII acceptances agree between the twins (Unicode digits, Unicode whitespace at the ends).

<details><summary>Reproducer</summary>

```python
import _pydecimal as P, _decimal as C
def kind(M, s):
    try:
        return repr(M.Decimal(s))
    except M.InvalidOperation:
        return 'InvalidOperation'
hits = 0
for s, want in [('ınf', "Decimal('Infinity')"), ('İnfinity', "Decimal('Infinity')"),
                ('ſNaN', "Decimal('sNaN')")]:
    p, c = kind(P, s), kind(C, s)
    print(ascii(s), '_pydecimal:', p, ' _decimal:', c)
    hits += (p == want and c == 'InvalidOperation')
```

</details>

#### 9. _pydecimal's _is_less_than_pow10a_use_str (new in 3.15) calls a quotient that fits too large, so //, % and divmod raise DivisionImpossible at prec 355861594

3.15 replaced `q < 10**context.prec` in _divide by _is_less_than_pow10a_use_str(q, prec)
(gh-140036), which first tries two float tests on q.bit_length(). The second,
    elif q.bit_length() >= 1 + a * _LOG_10_BASE_2_HI:   # "then q > 10**a"
is justified by "If z > log2(10) and q.bit_length() >= 1 + a*z, then q > 10**a", which holds
for the exact product, but `1 + a * _LOG_10_BASE_2_HI` is rounded to a double (twice). When
a*log2(10) is just above an integer N, the rounded value can be exactly N+1, and every q of bit
length N+1 with q < 10**a is called too large. Searching every a <= 4*10**9 with exact
arithmetic (log2(10) to 80 digits, the products evaluated in IEEE doubles), the first such a is
355861594:
    355861594 * log2(10)              = 1182146627.0000000155687...
    1 + 355861594 * _LOG_10_BASE_2_HI = 1182146628.0   (the double)
so for every q with 2**1182146627 <= q < 10**355861594 (q has 355861594 digits) the helper
returns (False, None). There are 131 such a below 4*10**9 (727115501 is another); the test with
_LOG_10_BASE_2_LO (:478), which errs in the other, more harmful direction (accepting a quotient
with prec+1 digits), never misfires in that range.
Consequence, with sys.set_int_max_str_digits(0):
    c = _pydecimal.Context(prec=355861594, Emax=MAX_EMAX, Emin=MIN_EMIN, traps=[])
    c.divide_int(_pydecimal.Decimal(2**1182146627), 1)   -> Decimal('NaN'), InvalidOperation
    c.remainder(same, 1)                                 -> Decimal('NaN'), InvalidOperation
    _decimal with the same context                       -> the operand itself, and 0
The quotient has 355861594 = prec digits, so the spec (and _decimal) returns it.

<details><summary>Reproducer</summary>

```python
import sys
import _pydecimal as P
sys.set_int_max_str_digits(0)
prec = 355861594
q = 1 << 1182146627
verdict = P._is_less_than_pow10a_use_str(q, prec)
digits = len(str(q))          # about a minute: 355861594 digits
print('helper:', verdict, 'digits of q:', digits, 'prec:', prec)
```

</details>

#### 10. _pydecimal formats a tuple operand with '%s' % x in its TypeError messages, so Context().plus(()), Context().traps = (), Context().rounding = () and Decimal.from_number(()) report a format-string error

Five error messages in _pydecimal format the offending object with a bare `%`:
    _convert_other:      raise TypeError("Unable to convert %s to Decimal" % other)   (:6112)
    Context.add & co.:   raise TypeError("Unable to convert %s to Decimal" % b)       (:4248, :4474,
                         :4497, :4518, :5054, :5300, :5404, :5595)
    _set_signal_dict:    raise TypeError("%s must be a signal dict" % d)              (:4021)
    Context.__setattr__: raise TypeError("%s: invalid rounding mode" % value)         (:4045)
    Decimal.from_number: raise TypeError("Cannot convert %r to Decimal" % number)     (:715)
When the object is a tuple, `%` takes it as its argument tuple, so the intended message is
replaced by a formatting error, or by the wrong text:
    _pydecimal.Context().plus(())                -> TypeError: not enough arguments for format string (got 0)
    _pydecimal.Context().compare_total(1, (1, 2)) -> TypeError: not all arguments converted during string formatting (required 1, got 2)
    _pydecimal.Decimal(1).compare_total(())      -> TypeError: not enough arguments for format string (got 0)
    _pydecimal.Context().traps = ()              -> TypeError: not enough arguments for format string (got 0)
    _pydecimal.Context().traps = (1,)            -> TypeError: 1 must be a signal dict
    _pydecimal.Context().traps = [1]             -> TypeError: [1] must be a signal dict
    _pydecimal.Context().rounding = ()           -> TypeError: not enough arguments for format string (got 0)
    _pydecimal.Context().rounding = (1, 2)       -> TypeError: not all arguments converted during string formatting (required 1, got 2)
    _pydecimal.Context().rounding = (1,)         -> TypeError: 1: invalid rounding mode
    _pydecimal.Decimal.from_number(())           -> TypeError: not enough arguments for format string (got 0)
    _decimal.Context().plus(())                  -> TypeError: conversion from tuple to Decimal is not supported
    _decimal.Context().traps = ()                -> TypeError: argument must be a signal dict
    _decimal.Context().rounding = ()             -> TypeError: valid values for rounding are: [ROUND_CEILING, ...]
    _decimal.Decimal.from_number(())             -> TypeError: conversion from tuple to Decimal is not supported
The exception class is right (TypeError) in every case; only the message is wrong. Every
Context method that converts an operand with raiseit=True, and every Decimal method that does
(compare_total, quantize, fma, rotate, ...), is affected, as are the rounding attribute (also
through Context(rounding=()) and localcontext(rounding=())) and Decimal.from_number.

<details><summary>Reproducer</summary>

```python
import _pydecimal as P
msgs = []
try:
    P.Context().plus(())
except TypeError as e:
    msgs.append(str(e))
c = P.Context()
try:
    c.traps = ()
except TypeError as e:
    msgs.append(str(e))
try:
    c.rounding = ()
except TypeError as e:
    msgs.append(str(e))
try:
    P.Decimal.from_number(())
except TypeError as e:
    msgs.append(str(e))
print('messages:', msgs)
if (len(msgs) == 4 and 'Unable to convert' not in msgs[0] and 'signal dict' not in msgs[1]
        and 'invalid rounding mode' not in msgs[2] and 'Cannot convert' not in msgs[3]):
```

</details>

#### 11. _pydecimal.Decimal((0, (True,), 0)) builds a corrupt Decimal('True'); the tuple constructor also ignores the coefficient of an infinity

The tuple branch of _pydecimal.Decimal.__new__ validates digits with
`isinstance(digit, int) and 0 <= digit <= 9`, which a bool passes, then builds the coefficient
with `''.join(map(str, digits))`. str(True) is 'True', so the coefficient string holds letters:
  _pydecimal.Decimal((0, (True,), 0))     -> Decimal('True')
  _pydecimal.Decimal((0, (1, False), 0))  -> Decimal('1False')
  _decimal.Decimal((0, (True,), 0))       -> Decimal('1')
  _decimal.Decimal((0, (1, False), 0))    -> Decimal('10')
The object is corrupt: every later use reads letters as digits, for instance
int(_pydecimal.Decimal((0, (True,), 0))) raises ValueError from int('True'), and
_pydecimal.Context(prec=3).create_decimal((0, (True,), 0)) prints 'T.ruE+3'.
Second difference in the same branch: for an exponent of 'F' the coefficient is not looked at,
so _pydecimal.Decimal((0, None, 'F')) and Decimal((0, (10,), 'F')) return Infinity, while
_decimal raises ValueError (its source comment says it accepts "any well-formed coefficient
for compatibility with decimal.py").

<details><summary>Reproducer</summary>

```python
import _pydecimal as P, _decimal as C
def show(f):
    try:
        return repr(f())
    except Exception as e:
        return type(e).__name__
p = show(lambda: P.Decimal((0, (True,), 0)))
c = show(lambda: C.Decimal((0, (True,), 0)))
p2 = show(lambda: P.Decimal((0, (1, False), 0)))
c2 = show(lambda: C.Decimal((0, (1, False), 0)))
p3 = show(lambda: int(P.Decimal((0, (True,), 0))))
c3 = show(lambda: int(C.Decimal((0, (True,), 0))))
p4 = show(lambda: P.Decimal((0, None, 'F')))
c4 = show(lambda: C.Decimal((0, None, 'F')))
print('(0,(True,),0)    _pydecimal:', p, ' _decimal:', c)
print('(0,(1,False),0)  _pydecimal:', p2, ' _decimal:', c2)
print('int(...)         _pydecimal:', p3, ' _decimal:', c3)
print("(0,None,'F')     _pydecimal:", p4, ' _decimal:', c4)
if p == "Decimal('True')" and c == "Decimal('1')" and p2 == "Decimal('1False')" and c2 == "Decimal('10')" \
        and p3 == 'ValueError' and c3 == '1' and p4 == "Decimal('Infinity')" and c4 == 'ValueError':
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
