import PyLean.Core

/-!
Model of the exact (integer and rational) core of CPython `Lib/fractions.py`
(3.15.2): construction from ints, normalization, the arithmetic operators with `Fraction` and `int`
operands, `**` with an int exponent, comparisons, `__floor__`, `__ceil__`,
`__trunc__`, `__int__`, `__round__`, `__hash__` and `limit_denominator`.

String parsing is in `Parse.lean`, `__str__` and `__format__` in `Format.lean`.

A `Fraction` object is modelled by its two attributes `_numerator` and
`_denominator`; Python `int` operands are passed as `⟨n, 1⟩`, which is exactly
what `Fraction(n)` builds (fractions.py:240-243) and what
`_operator_fallbacks` converts them to (fractions.py:697-722).

Python's `//` and `%` are floor division and floor modulo (`Int.fdiv`,
`Int.fmod`). Every place where the source formats an int into a message goes
through `strInt`, which models CPython's `int_max_str_digits` limit (default
4300 digits): `str(i)` raises `ValueError` when `i` has more than 4300 decimal
digits (Objects/longobject.c:2120-2134 and :2207-2216).
-/

namespace PyLean.Fractions

open PyLean

/-- A `Fraction` object: `(_numerator, _denominator)`. -/
structure Frac where
  num : Int
  den : Int
  deriving Repr, DecidableEq, Inhabited

/-- The class invariant every `Fraction` built by the public constructors
satisfies (docs: "in lowest terms", "Guaranteed to be positive"). -/
def Frac.Normal (x : Frac) : Prop := 0 < x.den ∧ Int.gcd x.num x.den = 1

instance (x : Frac) : Decidable x.Normal := inferInstanceAs (Decidable (_ ∧ _))

/-- Python `a // b` (floor division). Callers check `b ≠ 0` first. -/
def pyDiv (a b : Int) : Int := Int.fdiv a b

/-- Python `a % b` (floor modulo). -/
def pyMod (a b : Int) : Int := Int.fmod a b

/-! ## `int` to `str` with the digit limit -/

/-- `sys.flags.int_max_str_digits` default, Include/internal/pycore_long.h:29. -/
def maxStrDigits : Nat := 4300

/-- Number of decimal digits of a natural number (`len(str(n))`). -/
def numDigits (n : Nat) : Nat := (Nat.toDigits 10 n).length

/-- `_MAX_STR_DIGITS_ERROR_FMT_TO_STR`, Objects/longobject.c:33. -/
def limitToStrMsg : String :=
  "Exceeds the limit (4300 digits) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit"

/-- `str(i)` for an int, Objects/longobject.c:2116-2216: the pre-check at
:2149-2158 only fires for values that also fail the exact check at
:2207-2216, which compares the digit count without the sign to the limit. -/
def strInt (i : Int) : Py (List Char) :=
  if numDigits i.natAbs > maxStrDigits then .error (.valueError limitToStrMsg)
  else .ok ((if i < 0 then ['-'] else []) ++ Nat.toDigits 10 i.natAbs)

/-- `'Fraction(%s, 0)' % x`, the message of the `ZeroDivisionError`s raised at
fractions.py:303, :847 and :905. Formatting `x` can itself raise. -/
def zeroDivMsg (x : Int) : Py PyExc := do
  let s ← strInt x
  return .zeroDivisionError (String.ofList ("Fraction(".toList ++ s ++ ", 0)".toList))

/-- The message of `ZeroDivisionError` from int `//`, `%` and `divmod`. -/
def intDivZeroMsg : String := "division by zero"

/-! ## Construction -/

/-- The common tail of `Fraction.__new__`, fractions.py:302-311: zero check,
gcd reduction and sign normalization. -/
def normalize (n d : Int) : Py Frac := do
  if d = 0 then throw (← zeroDivMsg n)
  let g : Int := Int.gcd n d
  let g := if d < 0 then -g else g
  return ⟨pyDiv n g, pyDiv d g⟩

/-- `Fraction(numerator, denominator)` with two ints, fractions.py:289-290
then :302-311. -/
def ofInts (n d : Int) : Py Frac := normalize n d

/-- `Fraction(n)` for an int, fractions.py:240-243. -/
def ofInt (n : Int) : Frac := ⟨n, 1⟩

/-- `is_integer`, fractions.py:373-375. -/
def isInteger (x : Frac) : Bool := x.den == 1

/-- `as_integer_ratio`, fractions.py:377-382. -/
def asIntegerRatio (x : Frac) : Int × Int := (x.num, x.den)

/-! ## Arithmetic, fractions.py:794-883 -/

/-- `_add`, fractions.py:794-806. -/
def add (a b : Frac) : Frac :=
  let g : Int := Int.gcd a.den b.den
  if g = 1 then ⟨a.num * b.den + a.den * b.num, a.den * b.den⟩
  else
    let s := pyDiv a.den g
    let t := a.num * pyDiv b.den g + b.num * s
    let g2 : Int := Int.gcd t g
    if g2 = 1 then ⟨t, s * b.den⟩
    else ⟨pyDiv t g2, s * pyDiv b.den g2⟩

/-- `_sub`, fractions.py:810-822. -/
def sub (a b : Frac) : Frac :=
  let g : Int := Int.gcd a.den b.den
  if g = 1 then ⟨a.num * b.den - a.den * b.num, a.den * b.den⟩
  else
    let s := pyDiv a.den g
    let t := a.num * pyDiv b.den g - b.num * s
    let g2 : Int := Int.gcd t g
    if g2 = 1 then ⟨t, s * b.den⟩
    else ⟨pyDiv t g2, s * pyDiv b.den g2⟩

/-- `_mul`, fractions.py:826-838. -/
def mul (a b : Frac) : Frac :=
  let g1 : Int := Int.gcd a.num b.den
  let (na, db) := if g1 > 1 then (pyDiv a.num g1, pyDiv b.den g1) else (a.num, b.den)
  let g2 : Int := Int.gcd b.num a.den
  let (nb, da) := if g2 > 1 then (pyDiv b.num g2, pyDiv a.den g2) else (b.num, a.den)
  ⟨na * nb, db * da⟩

/-- `_div`, fractions.py:842-860. -/
def div (a b : Frac) : Py Frac := do
  if b.num = 0 then throw (← zeroDivMsg b.den)
  let g1 : Int := Int.gcd a.num b.num
  let (na, nb) := if g1 > 1 then (pyDiv a.num g1, pyDiv b.num g1) else (a.num, b.num)
  let g2 : Int := Int.gcd b.den a.den
  let (da, db) := if g2 > 1 then (pyDiv a.den g2, pyDiv b.den g2) else (a.den, b.den)
  let n := na * db
  let d := nb * da
  if d < 0 then return ⟨-n, -d⟩ else return ⟨n, d⟩

/-- `_floordiv`, fractions.py:864-866 (returns an int). -/
def floordiv (a b : Frac) : Py Int :=
  let q := a.den * b.num
  if q = 0 then .error (.zeroDivisionError intDivZeroMsg)
  else .ok (pyDiv (a.num * b.den) q)

/-- `_divmod`, fractions.py:870-874. -/
def divmod (a b : Frac) : Py (Int × Frac) := do
  let q := a.den * b.num
  if q = 0 then throw (.zeroDivisionError intDivZeroMsg)
  let div := pyDiv (a.num * b.den) q
  let nMod := pyMod (a.num * b.den) q
  return (div, ← ofInts nMod (a.den * b.den))

/-- `_mod`, fractions.py:878-881. -/
def mod (a b : Frac) : Py Frac := do
  let q := b.num * a.den
  if q = 0 then throw (.zeroDivisionError intDivZeroMsg)
  ofInts (pyMod (a.num * b.den) q) (a.den * b.den)

/-- `a ** b` for an int (or integral Rational) exponent `b`,
fractions.py:885-917. -/
def pow (a : Frac) (power : Int) : Py Frac :=
  if power ≥ 0 then .ok ⟨a.num ^ power.toNat, a.den ^ power.toNat⟩
  else if a.num > 0 then .ok ⟨a.den ^ (-power).toNat, a.num ^ (-power).toNat⟩
  else if a.num = 0 then
    match zeroDivMsg (a.den ^ (-power).toNat) with
    | .ok e => .error e
    | .error e => .error e
  else .ok ⟨(-a.den) ^ (-power).toNat, (-a.num) ^ (-power).toNat⟩

/-- `__neg__`, fractions.py:939-941. -/
def neg (a : Frac) : Frac := ⟨-a.num, a.den⟩

/-- `__abs__`, fractions.py:943-945. -/
def abs (a : Frac) : Frac := ⟨a.num.natAbs, a.den⟩

/-! ## Comparisons, fractions.py:1000-1058 -/

/-- `a == b` for a Fraction or int `b`, fractions.py:1000-1005. -/
def eq (a b : Frac) : Bool := a.num == b.num && a.den == b.den

/-- `_richcmp` with a Rational `other`, fractions.py:1031-1033:
`op(self._numerator * other.denominator, self._denominator * other.numerator)`. -/
def lt (a b : Frac) : Bool := decide (a.num * b.den < a.den * b.num)
def le (a b : Frac) : Bool := decide (a.num * b.den ≤ a.den * b.num)
def gt (a b : Frac) : Bool := decide (a.num * b.den > a.den * b.num)
def ge (a b : Frac) : Bool := decide (a.num * b.den ≥ a.den * b.num)

/-! ## Integer conversions and rounding, fractions.py:947-994 -/

/-- `__int__`, fractions.py:947-952. -/
def toInt (a : Frac) : Int :=
  if a.num < 0 then -(pyDiv (-a.num) a.den) else pyDiv a.num a.den

/-- `__trunc__`, fractions.py:954-959. -/
def trunc (a : Frac) : Int :=
  if a.num < 0 then -(pyDiv (-a.num) a.den) else pyDiv a.num a.den

/-- `__floor__`, fractions.py:961-963. -/
def floor (a : Frac) : Int := pyDiv a.num a.den

/-- `__ceil__`, fractions.py:965-968. -/
def ceil (a : Frac) : Int := -(pyDiv (-a.num) a.den)

/-- `round(self)`, fractions.py:970-985. -/
def round (a : Frac) : Int :=
  let d := a.den
  let fl := pyDiv a.num d
  let r := pyMod a.num d
  if r * 2 < d then fl
  else if r * 2 > d then fl + 1
  else if pyMod fl 2 = 0 then fl
  else fl + 1

/-- `round(self, ndigits)`, fractions.py:986-994. `self * shift` and
`self / shift` go through `_operator_fallbacks.forward` with an int operand. -/
def roundTo (a : Frac) (ndigits : Int) : Py Frac := do
  let shift : Int := 10 ^ ndigits.natAbs
  if ndigits > 0 then ofInts (round (mul a (ofInt shift))) shift
  else return ofInt (round (← div a (ofInt shift)) * shift)

/-! ## Hashing, fractions.py:16-54 and :996-998 -/

/-- `sys.hash_info.modulus` on 64-bit builds, `2**61 - 1`. -/
def hashModulus : Nat := 2305843009213693951

/-- `sys.hash_info.inf`. -/
def hashInf : Int := 314159

/-- Extended Euclid: `egcd fuel a b = (g, x, y)` with `a*x + b*y = g`. -/
def egcd : Nat → Int → Int → Int × Int × Int
  | 0, a, _ => (a, 1, 0)
  | fuel + 1, a, b =>
    if b = 0 then (a, 1, 0)
    else
      let r := egcd fuel b (a % b)
      (r.1, r.2.2, r.2.1 - (a / b) * r.2.2)

/-- `pow(d, -1, m)` for `d > 0`, `m > 1` (Objects/longobject.c `long_invmod`):
the inverse of `d` modulo `m` in `[0, m)`, or `none` where Python raises
`ValueError("base is not invertible for the given modulus")`. Any algorithm
returning the (unique) inverse is faithful; this one is extended Euclid. -/
def modInv (d : Int) (m : Nat) : Option Int :=
  let r := egcd (m + 1) (d % m) m
  if r.1 = 1 then some (r.2.1 % m) else none

/-- `hash(i)` for an int, Objects/longobject.c:3673-3743: `|i| mod P` with
the sign of `i`, and `-1` replaced by `-2`. -/
def intHash (i : Int) : Int :=
  let h : Int := (i.natAbs % hashModulus : Nat)
  let r := if i < 0 then -h else h
  if r = -1 then -2 else r

/-- `_hash_algorithm(numerator, denominator)`, fractions.py:23-54. -/
def hashAlgorithm (n d : Int) : Int :=
  let h : Int := match modInv d hashModulus with
    | none => hashInf
    | some dinv => intHash (intHash n.natAbs * dinv)
  let r := if n ≥ 0 then h else -h
  if r = -1 then -2 else r

/-- `Fraction.__hash__`, fractions.py:996-998. -/
def hash (a : Frac) : Int := hashAlgorithm a.num a.den

/-! ## `limit_denominator`, fractions.py:384-439 -/

/-- The `while True` loop of `limit_denominator`, fractions.py:423-429, on
the state `(p0, q0, p1, q1, n, d)`. `n // d` raises for `d == 0`. -/
def ldLoop (maxDen : Int) : Nat → Int × Int × Int × Int × Int × Int →
    Py (Int × Int × Int × Int × Int × Int)
  | 0, _ => .error .modelFuel
  | fuel + 1, (p0, q0, p1, q1, n, d) =>
    if d = 0 then .error (.zeroDivisionError intDivZeroMsg)
    else
      let a := pyDiv n d
      let q2 := q0 + a * q1
      if q2 > maxDen then .ok (p0, q0, p1, q1, n, d)
      else ldLoop maxDen fuel (p1, q1, p0 + a * p1, q2, d, n - a * d)

/-- `self.limit_denominator(max_denominator)` for an int argument,
fractions.py:384-439. The loop fuel `den + 1` suffices: `d` strictly
decreases on every iteration and starts at `self._denominator`. -/
def limitDenominator (x : Frac) (maxDen : Int) : Py Frac := do
  if maxDen < 1 then throw (.valueError "max_denominator should be at least 1")
  if x.den ≤ maxDen then return x
  let (p0, q0, p1, q1, _, d) ← ldLoop maxDen (x.den.toNat + 1) (0, 1, 1, 0, x.num, x.den)
  if q1 = 0 then throw (.zeroDivisionError intDivZeroMsg)
  let k := pyDiv (maxDen - q0) q1
  if 2 * d * (q0 + k * q1) ≤ x.den then return ⟨p1, q1⟩
  else return ⟨p0 + k * p1, q0 + k * q1⟩

/-! ## `decimal.Decimal` values (oracle for the hash and format properties)

A finite `Decimal` is `(-1)**sign * coefficient * 10**exponent`. Its hash is
`Decimal.__hash__`, Lib/_pydecimal.py:988-1012 (the C `_decimal` computes the
same function, Modules/_decimal/_decimal.c `_dec_hash`). -/

/-- `_PyHASH_10INV = pow(10, P - 2, P)`, Lib/_pydecimal.py:6505. -/
def tenInv : Nat := Nat.powMod 10 (hashModulus - 2) hashModulus

/-- `hash(Decimal((sign, digits, exponent)))` for a finite Decimal. -/
def decimalHash (neg : Bool) (coeff : Nat) (exp : Int) : Int :=
  let expHash : Nat :=
    if exp ≥ 0 then Nat.powMod 10 exp.toNat hashModulus
    else Nat.powMod tenInv (-exp).toNat hashModulus
  let h : Int := ((coeff * expHash) % hashModulus : Nat)
  -- `self >= 0` is false only for a negative non-zero value
  let ans := if neg ∧ coeff ≠ 0 then -h else h
  if ans = -1 then -2 else ans

/-- `Fraction(Decimal((sign, digits, exponent)))` through
`Decimal.as_integer_ratio()` (fractions.py:245-250), which returns the ratio in
lowest terms with a positive denominator, i.e. the normalized pair. -/
def ofDecimal (neg : Bool) (coeff : Nat) (exp : Int) : Frac :=
  let n : Int := if neg then -(coeff : Int) else coeff
  let (n, d) : Int × Int := if exp ≥ 0 then (n * 10 ^ exp.toNat, 1) else (n, 10 ^ (-exp).toNat)
  let g : Int := Int.gcd n d
  ⟨n / g, d / g⟩

end PyLean.Fractions
