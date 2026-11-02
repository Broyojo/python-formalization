import PyLean.Core

/-!
`Lib/numbers.py`, CPython 3.15.2.

The classes are abstract: each method is either a stub or a mixin over primitives that a concrete
subclass supplies. A stub is one line here, under the class and method name of the source, raising
`NotImplementedError` or, for `Complex.__complex__` whose body is only a docstring, returning
`None`. A mixin takes `Prims`, the operators as the expression in the source evaluates them: `self +
x` is `p.add self x` whatever `__add__`/`__radd__` dispatch did. `α` is the universe of values, `F`
the `float` type, `C` the `complex` type, so nothing here depends on one concrete number type.
-/

namespace PyLean.CoreLibs.Misc.Numbers

open PyLean

/-- `raise NotImplementedError`. -/
def notImpl {β : Type} : Py β := .error (.named "NotImplementedError" "")

/-- What the mixins of `Lib/numbers.py` use from a concrete subclass. -/
structure Prims (α F C : Type) where
  /-- The int literals `0` and `1`. -/
  zero : α
  one : α
  eq : α → α → Py Bool
  add : α → α → Py α
  neg : α → Py α
  pos : α → Py α
  floordiv : α → α → Py α
  mod : α → α → Py α
  /-- `float(self)` -/
  float : α → Py F
  /-- `complex(x)` for a float `x` -/
  complexOf : F → Py C
  /-- `int(self)` -/
  toInt : α → Py Int
  /-- `self.numerator`, `self.denominator` -/
  numerator : α → Py α
  denominator : α → Py α
  /-- `a / b` for two ints, `long_true_divide` -/
  intDiv : Int → Int → Py F
  /-- `float(n)` for an int -/
  intFloat : Int → Py F

variable {α F C : Type}

namespace Complex
/-- Lib/numbers.py:70-72: the body is a docstring, so the abstract method returns `None`. -/
def __complex__ (_self : α) : Py Unit := .ok ()
/-- Mixin, Lib/numbers.py:74-76. `!=` is the default `object.__ne__`, the negation of `__eq__`. -/
def __bool__ (p : Prims α F C) (self : α) : Py Bool := do
  return !(← p.eq self p.zero)
/-- Lib/numbers.py:78-85. -/
def real (_self : α) : Py α := notImpl
/-- Lib/numbers.py:87-94. -/
def imag (_self : α) : Py α := notImpl
/-- Lib/numbers.py:96-99. -/
def __add__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:101-104. -/
def __radd__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:106-109. -/
def __neg__ (_self : α) : Py α := notImpl
/-- Lib/numbers.py:111-114. -/
def __pos__ (_self : α) : Py α := notImpl
/-- Mixin, Lib/numbers.py:116-118: `self + -other`. -/
def __sub__ (p : Prims α F C) (self other : α) : Py α := do
  let n ← p.neg other
  p.add self n
/-- Mixin, Lib/numbers.py:120-122: `-self + other`. -/
def __rsub__ (p : Prims α F C) (self other : α) : Py α := do
  let n ← p.neg self
  p.add n other
/-- Lib/numbers.py:124-127. -/
def __mul__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:129-132. -/
def __rmul__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:134-137. -/
def __truediv__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:139-142. -/
def __rtruediv__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:144-147. -/
def __pow__ (_self _exponent : α) : Py α := notImpl
/-- Lib/numbers.py:149-152. -/
def __rpow__ (_self _base : α) : Py α := notImpl
/-- Lib/numbers.py:154-157. -/
def __abs__ (_self : α) : Py α := notImpl
/-- Lib/numbers.py:159-162. -/
def conjugate (_self : α) : Py α := notImpl
/-- Lib/numbers.py:164-167. -/
def __eq__ (_self _other : α) : Py Bool := notImpl
end Complex

namespace Real
/-- Lib/numbers.py:183-188. -/
def __float__ (_self : α) : Py F := notImpl
/-- Lib/numbers.py:190-201. -/
def __trunc__ (_self : α) : Py α := notImpl
/-- Lib/numbers.py:203-206. -/
def __floor__ (_self : α) : Py α := notImpl
/-- Lib/numbers.py:208-211. -/
def __ceil__ (_self : α) : Py α := notImpl
/-- Lib/numbers.py:213-220. -/
def __round__ (_self : α) (_ndigits : Option α := none) : Py α := notImpl
/-- Mixin, Lib/numbers.py:222-228: `(self // other, self % other)`. -/
def __divmod__ (p : Prims α F C) (self other : α) : Py (α × α) := do
  let q ← p.floordiv self other
  let r ← p.mod self other
  return (q, r)
/-- Mixin, Lib/numbers.py:230-236: `(other // self, other % self)`. -/
def __rdivmod__ (p : Prims α F C) (self other : α) : Py (α × α) := do
  let q ← p.floordiv other self
  let r ← p.mod other self
  return (q, r)
/-- Lib/numbers.py:238-241. -/
def __floordiv__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:243-246. -/
def __rfloordiv__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:248-251. -/
def __mod__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:253-256. -/
def __rmod__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:258-263. -/
def __lt__ (_self _other : α) : Py Bool := notImpl
/-- Lib/numbers.py:265-268. -/
def __le__ (_self _other : α) : Py Bool := notImpl
/-- Mixin, Lib/numbers.py:271-273: `complex(float(self))`. -/
def __complex__ (p : Prims α F C) (self : α) : Py C := do
  p.complexOf (← p.float self)
/-- Mixin, Lib/numbers.py:275-278: `+self`. -/
def real (p : Prims α F C) (self : α) : Py α := p.pos self
/-- Mixin, Lib/numbers.py:280-283: the int `0`. -/
def imag (p : Prims α F C) (_self : α) : Py α := .ok p.zero
/-- Mixin, Lib/numbers.py:285-287: `+self`. -/
def conjugate (p : Prims α F C) (self : α) : Py α := p.pos self
end Real

namespace Rational
/-- Lib/numbers.py:301-305. -/
def numerator (_self : α) : Py α := notImpl
/-- Lib/numbers.py:307-314. -/
def denominator (_self : α) : Py α := notImpl
/-- Mixin, Lib/numbers.py:317-325: `int(self.numerator) / int(self.denominator)`. -/
def __float__ (p : Prims α F C) (self : α) : Py F := do
  let n ← p.toInt (← p.numerator self)
  let d ← p.toInt (← p.denominator self)
  p.intDiv n d
end Rational

namespace Integral
/-- Lib/numbers.py:337-340. -/
def __int__ (_self : α) : Py Int := notImpl
/-- Mixin, Lib/numbers.py:342-344: `int(self)`. -/
def __index__ (p : Prims α F C) (self : α) : Py Int := p.toInt self
/-- Lib/numbers.py:346-355. -/
def __pow__ (_self _exponent : α) (_modulus : Option α := none) : Py α := notImpl
/-- Lib/numbers.py:357-360. -/
def __lshift__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:362-365. -/
def __rlshift__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:367-370. -/
def __rshift__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:372-375. -/
def __rrshift__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:377-380. -/
def __and__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:382-385. -/
def __rand__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:387-390. -/
def __xor__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:392-395. -/
def __rxor__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:397-400. -/
def __or__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:402-405. -/
def __ror__ (_self _other : α) : Py α := notImpl
/-- Lib/numbers.py:407-410. -/
def __invert__ (_self : α) : Py α := notImpl
/-- Mixin, Lib/numbers.py:413-415: `float(int(self))`. -/
def __float__ (p : Prims α F C) (self : α) : Py F := do
  p.intFloat (← p.toInt self)
/-- Mixin, Lib/numbers.py:417-420: `+self`. -/
def numerator (p : Prims α F C) (self : α) : Py α := p.pos self
/-- Mixin, Lib/numbers.py:422-425: the int `1`. -/
def denominator (p : Prims α F C) (_self : α) : Py α := .ok p.one
end Integral

end PyLean.CoreLibs.Misc.Numbers
