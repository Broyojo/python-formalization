import PyLean.Datetime.Twins

/-!
C `timedelta` objects (Modules/_datetimemodule.c, CPython 3.15.2): the class an object is
made with and the `zero_delta` singleton (`new_delta_ex`, `look_up_delta`), the object-level
`microseconds_to_delta_ex` with `checked_divmod`, the number-method dispatch of
`delta_multiply` and `delta_truedivide`, and `delta_reduce`; with the pure-Python
counterparts in `Lib/_pydatetime.py` (Py).

Classes are compared by identity (`TdCls`), a stated scope: a metaclass overriding `__eq__`
is out of scope. An allocation failure (`tp_alloc` returning NULL) is not modelled.
-/

namespace PyLean.Datetime

open PyLean

/-! ### Objects -/

/-- The class a C `timedelta` is made with (the `type` argument of `new_delta_ex`, the
`Py_TYPE(self)` of `delta_reduce`): `timedelta` itself, or a subclass named by an id. -/
inductive TdCls where
  | base
  | sub (id : Nat)
  deriving DecidableEq, Repr

/-- A C `timedelta` object: the static `zero_delta` (:3166-3170), or a new object of the
given class holding the value. -/
inductive TdObjC where
  | zeroSingleton
  | fresh (cls : TdCls) (v : Delta)
  deriving DecidableEq, Repr

/-- The value (`days`, `seconds`, `microseconds`) of a C timedelta. -/
def TdObjC.val : TdObjC → Delta
  | .zeroSingleton => ⟨0, 0, 0⟩
  | .fresh _ v => v

/-- `Py_TYPE(self)` of a C timedelta. -/
def TdObjC.cls : TdObjC → TdCls
  | .zeroSingleton => .base
  | .fresh c _ => c

/-- `look_up_delta`, :3173-3181: the static `zero_delta` for a zero value of exactly its
type (`type == Py_TYPE(&zero_delta)`), `NULL` (`none`) otherwise. -/
def lookUpDeltaC (d s us : Int) (ty : TdCls) : Option TdObjC :=
  if d = 0 ∧ s = 0 ∧ us = 0 ∧ ty = .base then some .zeroSingleton else none

/-- The rest of `new_delta_ex` once the fields are normalized, :1394-1410:
`check_delta_day_range`, then the `look_up_delta` singleton or a new object of `type`. -/
def newDeltaExTail (d s us : Int) (ty : TdCls) : Py TdObjC := do
  checkDeltaDayRange d
  match lookUpDeltaC d s us ty with
  | some o => return o
  | none => return .fresh ty ⟨d, s, us⟩

/-- `new_delta_ex(days, seconds, microseconds, normalize, type)`, :1384-1411:
`normalize_d_s_us` when `normalize` is true (:1390-1391), then `newDeltaExTail`. The
arguments are C `int`s. -/
def newDeltaExC (d s us : Int) (normalize : Bool) (ty : TdCls) : Py TdObjC :=
  let (d, s, us) := if normalize then normalizeDSUsC d s us else (d, s, us)
  newDeltaExTail d s us ty

/-- What C hands back for a value made with class `ty`. -/
def tdObjOf (ty : TdCls) (v : Delta) : TdObjC :=
  if v = ⟨0, 0, 0⟩ ∧ ty = .base then .zeroSingleton else .fresh ty v

/-! ### `microseconds_to_delta_ex` on any object -/

mutual
/-- A Python object as `microseconds_to_delta_ex` sees it: an exact `int` (`PyNumber_Divmod`
of two ints is `long_divmod`), or another object, given by its type name, what
`operator.index` returns for it (`none`: it has no `__index__`; `PyLong_AsInt` reads an int
subclass's value, which is `some (.ok n)`), and what `divmod(obj, n)` gives for each `n`
(the binary operator's `__divmod__`/`__rdivmod__` dispatch, abstracted). Such an object
reaches `microseconds_to_delta` as the product an int subclass's `__mul__` returns in
`multiply_int_timedelta` (:2290-2308). -/
inductive PObj where
  | int (n : Int)
  | other (tpName : String) (index : Option (Py Int)) (divmod : Int → DmOut)

/-- What `divmod(obj, n)` gives: an exception, a non-tuple of the named type, a 2-tuple, or
a tuple of `size` items for some `size ≠ 2` (its items play no part). -/
inductive DmOut where
  | raise (e : PyExc)
  | nontuple (tpName : String)
  | pair (q r : PObj)
  | tupleOf (size : Nat)
end

/-- `checked_divmod(a, b)`, :2193-2213: `PyNumber_Divmod(a, b)`, then a non-tuple
(:2197-2203) and a tuple whose size is not 2 (:2204-2210) are `TypeError`s. `b` is a
positive constant (`us_per_second`, `seconds_per_day`) in both calls. -/
def checkedDivmodC (a : PObj) (b : Int) : Py (PObj × PObj) :=
  match a with
  | .int n => do
    let (q, r) ← pyDivmod n b
    return (.int q, .int r)
  | .other _ _ dm =>
    match dm b with
    | .raise e => .error e
    | .nontuple tp => .error (.typeError s!"~divmod() returned non-tuple (type {tp})")
    | .pair q r => .ok (q, r)
    | .tupleOf n => .error (.typeError s!"divmod() returned a tuple of size {n}")

/-- `PyLong_AsInt(obj)`: an int's value narrowed to C `int`; another object goes through
`__index__` (`_PyNumber_Index`), `TypeError` without one. -/
def pyLongAsIntC : PObj → Py Int
  | .int n => asCInt n
  | .other _ (some r) _ => do asCInt (← r)
  | .other tp none _ => .error (.typeError s!"~'{tp}' object cannot be interpreted as an integer")

/-- The `BadDivmod` exit of `microseconds_to_delta_ex`, :2279-2282. -/
def badDivmod : PyExc := .typeError "divmod() returned a value out of range"

/-- `microseconds_to_delta_ex(pyus, type)`, :2218-2284: `checked_divmod` by `10**6`, the
remainder narrowed (`PyLong_AsInt`) and range-checked, `checked_divmod` of the quotient by
`86400`, its remainder narrowed and checked, the quotient narrowed, then
`new_delta_ex(d, s, us, 0, type)`. -/
def usToDeltaExC (pyus : PObj) (ty : TdCls) : Py TdObjC := do
  let (q1, r1) ← checkedDivmodC pyus 1000000
  let us ← pyLongAsIntC r1
  if ¬(0 ≤ us ∧ us < 1000000) then Except.error badDivmod
  let (q2, r2) ← checkedDivmodC q1 86400
  let s ← pyLongAsIntC r2
  if ¬(0 ≤ s ∧ s < 24 * 3600) then Except.error badDivmod
  let d ← pyLongAsIntC q2
  newDeltaExC d s us false ty

/-- `delta_new_impl` with int arguments and class `ty`, :2832-2932: the exact microsecond
sum of `accum` (the order of `deltaC`), then `microseconds_to_delta_ex(x, type)` (:2925). -/
def deltaObjC (ty : TdCls) (days seconds microseconds milliseconds minutes hours weeks : Int) :
    Py TdObjC :=
  usToDeltaExC (.int (microseconds + milliseconds * 1000 + seconds * 1000000 + minutes * 60000000 +
    hours * 3600000000 + days * 86400000000 + weeks * 604800000000)) ty

/-! ### `timedelta * int` with an int subclass -/

/-- The int operand `n` of `timedelta * n` and `n * timedelta`: its value, and what
`PyNumber_Multiply(n, us)` returns (the exact product for an `int`; whatever its
`__mul__` returns for an int subclass that overrides it). An int subclass overriding
`__rmul__` is out of scope (Python's `self._days * other` would call it). -/
structure IntOperand where
  n : Int
  mul : Int → Py PObj

/-- An `int` (or an int subclass that keeps `int.__mul__`). -/
def IntOperand.exact (n : Int) : IntOperand := ⟨n, fun u => .ok (.int (n * u))⟩

/-- `multiply_int_timedelta(intobj, delta)`, :2290-2308: `delta_to_microseconds`, then
`PyNumber_Multiply(intobj, pyus_in)` with the int on the left, then `microseconds_to_delta`
(class `timedelta`). -/
def multiplyIntTimedeltaC (k : IntOperand) (a : Delta) : Py TdObjC := do
  let pyusIn := a.toUs
  let pyusOut ← k.mul pyusIn
  usToDeltaExC pyusOut .base

/-! ### Number-method dispatch -/

/-- An operand of `*` or `/` next to a timedelta: a timedelta (any class; its value), an
int, a float (`float` itself or a subclass keeping `as_integer_ratio`), or another object. -/
inductive TdOperand where
  | td (t : Delta)
  | int (k : IntOperand)
  | float (x : Binary64.F64)
  | other

/-- `delta_multiply(left, right)`, :2579-2602: a timedelta left operand takes an int
(`multiply_int_timedelta`) or a float (`multiply_truedivide_timedelta_float(.., 0)`); an
int or float left operand multiplies the right one, which is then the timedelta; anything
else is `NotImplemented` (`none`). -/
def deltaMultiplyC : TdOperand → TdOperand → Py (Option TdObjC)
  | .td a, .int k => some <$> multiplyIntTimedeltaC k a
  | .td a, .float x => some <$> (tdObjOf .base <$> a.mulFloatC x)
  | .td _, _ => .ok none
  | .int k, .td a => some <$> multiplyIntTimedeltaC k a
  | .float x, .td a => some <$> (tdObjOf .base <$> a.mulFloatC x)
  | _, _ => .ok none

/-- `timedelta.__mul__`, Py:858-869 (`__rmul__ = __mul__`, :871): an int gives
`timedelta(self._days * other, ...)`, a float the rounded ratio, anything else
`NotImplemented`. -/
def tdMulPy (a : Delta) : TdOperand → Py (Option Delta)
  | .int k => some <$> a.mulPy k.n
  | .float x => some <$> a.mulFloatPy x
  | _ => .ok none

/-- `left * right` in Python, with a timedelta on at least one side: `left.__mul__(right)`;
for an int or float on the left, `int.__mul__` and `float.__mul__` return `NotImplemented`
for a timedelta and `right.__rmul__(left)` runs; two timedeltas, or another object, give
`NotImplemented` from the timedelta's side. -/
def deltaMultiplyPy : TdOperand → TdOperand → Py (Option Delta)
  | .td a, r => tdMulPy a r
  | l, .td a => tdMulPy a l
  | _, _ => .ok none

/-- A truediv result: a timedelta, or the float of `timedelta / timedelta`. -/
abbrev TdDivRes := Sum TdObjC LongObj.Cplx.Dbl

/-- `delta_truedivide(left, right)`, :2627-2647: only a timedelta left operand; a timedelta
right operand gives `truedivide_timedelta_timedelta` (a float), then a float
`multiply_truedivide_timedelta_float(.., 1)`, then an int `truedivide_timedelta_int`, in
that order; anything else is `NotImplemented`. -/
def deltaTruedivideC : TdOperand → TdOperand → Py (Option TdDivRes)
  | .td a, .td b => (some ∘ Sum.inr) <$> a.truedivDeltaC b
  | .td a, .float x => (some ∘ Sum.inl ∘ tdObjOf .base) <$> a.truedivFloatC x
  | .td a, .int k => (some ∘ Sum.inl ∘ tdObjOf .base) <$> a.truedivIntC k.n
  | _, _ => .ok none

/-- `timedelta.__truediv__`, Py:886-896: `NotImplemented` unless the operand is an int,
float or timedelta; then a timedelta divisor gives `usec / other._to_microseconds()`, an int
`_divide_and_round(usec, other)`, a float `_divide_and_round(b * usec, a)`. There is no
`__rtruediv__`, so a timedelta right operand under a non-timedelta left one is
`NotImplemented`. -/
def deltaTruedividePy : TdOperand → TdOperand → Py (Option (Sum Delta LongObj.Cplx.Dbl))
  | .td a, .td b => (some ∘ Sum.inr) <$> a.truedivDeltaPy b
  | .td a, .int k => (some ∘ Sum.inl) <$> a.truedivIntPy k.n
  | .td a, .float x => (some ∘ Sum.inl) <$> a.truedivFloatPy x
  | _, _ => .ok none

/-! ### `__reduce__` -/

/-- `timedelta.__reduce__`, Py:962-963: `(self.__class__, self._getstate())`. -/
def Delta.reducePy (cls : TdCls) (t : Delta) : TdCls × List Int := (cls, t.getstate)

/-- `delta_reduce`, :3056-3060: `Py_BuildValue("ON", Py_TYPE(self), delta_getstate(self))`. -/
def TdObjC.reduceC (o : TdObjC) : TdCls × List Int := (o.cls, o.val.getstateC)

end PyLean.Datetime
