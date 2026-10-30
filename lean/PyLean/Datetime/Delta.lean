import PyLean.Core

/-!
`timedelta` with integer arguments: the pure-Python class
(`Lib/_pydatetime.py:616-976`) and the C type (`Modules/_datetimemodule.c`,
`delta_new` :2803-2921, `microseconds_to_delta_ex` :2207-2274, `new_delta_ex`
:1375-1403 and the number methods).

Float arguments are out of scope. Python's `divmod` and `//`, `%` by a positive
constant are Lean's `/`, `%` on `Int` (Euclidean division agrees with floor
division for a positive divisor); for a divisor of either sign we use
`Int.fdiv` / `Int.fmod`.
-/

namespace PyLean.Datetime

open PyLean

/-- A `timedelta` object: `(days, seconds, microseconds)`. -/
structure Delta where
  days : Int
  seconds : Int
  us : Int
  deriving Repr, DecidableEq, Inhabited

def MAX_DELTA_DAYS : Int := 999999999

/-- `timedelta._to_microseconds`, _pydatetime.py:854-856; C
`delta_to_microseconds`, :2128-2180. -/
def Delta.toUs (t : Delta) : Int := (t.days * 86400 + t.seconds) * 1000000 + t.us

/-- The field invariant every constructed `timedelta` satisfies. -/
def Delta.Valid (t : Delta) : Prop :=
  0 ≤ t.seconds ∧ t.seconds < 86400 ∧ 0 ≤ t.us ∧ t.us < 1000000 ∧
  -MAX_DELTA_DAYS ≤ t.days ∧ t.days ≤ MAX_DELTA_DAYS

instance (t : Delta) : Decidable t.Valid := by unfold Delta.Valid; infer_instance

/-! ### Pure Python -/

/-- `timedelta(days, seconds, microseconds, milliseconds, minutes, hours,
weeks)` with int arguments, _pydatetime.py:638-748. The float branches are not
taken; `round(microseconds + usdouble)` (:723) is the identity because
`usdouble == 0.0` and `|microseconds| < 10**6` there. -/
def deltaPy (days seconds microseconds milliseconds minutes hours weeks : Int) : Py Delta :=
  -- :662-668
  let days := days + weeks * 7
  let seconds := seconds + minutes * 60 + hours * 3600
  let microseconds := microseconds + milliseconds * 1000
  -- :682-683 (int branch)
  let d := days
  let s : Int := 0
  -- :699-702
  let d := d + seconds / 86400
  let s := s + seconds % 86400
  -- :717-723 (int branch)
  let sec2 := microseconds / 1000000
  let microseconds := microseconds % 1000000
  let d := d + sec2 / 86400
  let s := s + sec2 % 86400
  -- :731-735
  let s := s + microseconds / 1000000
  let us := microseconds % 1000000
  let d := d + s / 86400
  let s := s % 86400
  -- :741-742
  if d.natAbs > 999999999 then .error (.overflowError s!"timedelta # of days is too large: {d}")
  else .ok ⟨d, s, us⟩

/-- `timedelta(0, 0, us)`. -/
def usToDeltaPy (us : Int) : Py Delta := deltaPy 0 0 us 0 0 0 0

/-- Python `divmod(a, b)` / `a // b` / `a % b` on ints. -/
def pyDivmod (a b : Int) : Py (Int × Int) :=
  if b = 0 then .error (.zeroDivisionError "division by zero")
  else .ok (a.fdiv b, a.fmod b)

/-- `_divide_and_round`, _pydatetime.py:592-611 (round half to even). -/
def divideAndRound (a b : Int) : Py Int := do
  let (q, r) ← pyDivmod a b
  let r := r * 2
  let greaterThanHalf := if b > 0 then r > b else r < b
  if greaterThanHalf ∨ (r = b ∧ q % 2 = 1) then return q + 1 else return q

namespace Delta

/-- `__add__`, _pydatetime.py:798-805. -/
def addPy (a b : Delta) : Py Delta := deltaPy (a.days + b.days) (a.seconds + b.seconds) (a.us + b.us) 0 0 0 0
/-- `__sub__`, :809-816. -/
def subPy (a b : Delta) : Py Delta := deltaPy (a.days - b.days) (a.seconds - b.seconds) (a.us - b.us) 0 0 0 0
/-- `__neg__`, :823-828. -/
def negPy (a : Delta) : Py Delta := deltaPy (-a.days) (-a.seconds) (-a.us) 0 0 0 0
/-- `__abs__`, :833-837. -/
def absPy (a : Delta) : Py Delta := if a.days < 0 then a.negPy else .ok a
/-- `__mul__` with an int, :839-845. -/
def mulPy (a : Delta) (k : Int) : Py Delta := deltaPy (a.days * k) (a.seconds * k) (a.us * k) 0 0 0 0
/-- `__floordiv__` with an int, :858-865. -/
def floordivIntPy (a : Delta) (k : Int) : Py Delta := do
  let (q, _) ← pyDivmod a.toUs k
  usToDeltaPy q
/-- `__floordiv__` with a timedelta. -/
def floordivPy (a b : Delta) : Py Int := do return (← pyDivmod a.toUs b.toUs).1
/-- `__truediv__` with an int, :867-877. -/
def truedivIntPy (a : Delta) (k : Int) : Py Delta := do usToDeltaPy (← divideAndRound a.toUs k)
/-- `__mod__`, :879-883. -/
def modPy (a b : Delta) : Py Delta := do usToDeltaPy (← pyDivmod a.toUs b.toUs).2
/-- `__divmod__`, :885-890. -/
def divmodPy (a b : Delta) : Py (Int × Delta) := do
  let (q, r) ← pyDivmod a.toUs b.toUs
  return (q, ← usToDeltaPy r)

end Delta

/-! ### C -/

/-- `PyLong_AsInt` on a Python int. -/
def asCInt (x : Int) : Py Int :=
  if -2 ^ 31 ≤ x ∧ x ≤ 2 ^ 31 - 1 then .ok x
  else .error (.overflowError "Python int too large to convert to C int")

/-- `check_delta_day_range`, _datetimemodule.c:641-650. -/
def checkDeltaDayRange (d : Int) : Py Unit :=
  if -MAX_DELTA_DAYS ≤ d ∧ d ≤ MAX_DELTA_DAYS then .ok ()
  else .error (.overflowError s!"days={d}; must have magnitude <= 999999999")

/-- `microseconds_to_delta_ex`, :2207-2274. The `BadDivmod` branches are dead
for int `divmod`. -/
def usToDeltaC (x : Int) : Py Delta := do
  let us := x % 1000000
  let num := x / 1000000
  let s := num % 86400
  let d ← asCInt (num / 86400)
  checkDeltaDayRange d
  return ⟨d, s, us⟩

/-- `delta_new` with int arguments, :2803-2921: the arguments are accumulated
into an exact microsecond count (`accum`, :2723-2802) in the order
microseconds, milliseconds, seconds, minutes, hours, days, weeks. -/
def deltaC (days seconds microseconds milliseconds minutes hours weeks : Int) : Py Delta :=
  usToDeltaC (microseconds + milliseconds * 1000 + seconds * 1000000 + minutes * 60000000 +
    hours * 3600000000 + days * 86400000000 + weeks * 604800000000)

/-- `normalize_pair`, :721-732, using the C `divmod` helper (:370-383), which
rounds towards minus infinity. The callers' inputs are within a few times the
field ranges, so the C `int` arithmetic does not overflow. -/
def normalizePair (hi lo factor : Int) : Int × Int :=
  if lo < 0 ∨ lo ≥ factor then (hi + lo / factor, lo % factor) else (hi, lo)

/-- `new_delta(d, s, us, 1)`: `normalize_d_s_us` (:741-764) then the day range
check, :1375-1403. -/
def newDeltaNormC (d s us : Int) : Py Delta := do
  let (s, us) := if us < 0 ∨ us ≥ 1000000 then normalizePair s us 1000000 else (s, us)
  let (d, s) := if s < 0 ∨ s ≥ 86400 then normalizePair d s 86400 else (d, s)
  checkDeltaDayRange d
  return ⟨d, s, us⟩

namespace Delta

/-- `delta_add`, :2445-2465. -/
def addC (a b : Delta) : Py Delta := newDeltaNormC (a.days + b.days) (a.seconds + b.seconds) (a.us + b.us)
/-- `delta_subtract`, :2504-2524. -/
def subC (a b : Delta) : Py Delta := newDeltaNormC (a.days - b.days) (a.seconds - b.seconds) (a.us - b.us)
/-- `delta_negative`, :2467-2474. -/
def negC (a : Delta) : Py Delta := newDeltaNormC (-a.days) (-a.seconds) (-a.us)
/-- `delta_abs`, :2488-2502 (`delta_positive` copies without normalizing). -/
def absC (a : Delta) : Py Delta := if a.days < 0 then a.negC else .ok a
/-- `multiply_int_timedelta`, :2280-2300. -/
def mulC (a : Delta) (k : Int) : Py Delta := usToDeltaC (k * a.toUs)
/-- `divide_timedelta_int`, :2360-2379 (`PyNumber_FloorDivide`). -/
def floordivIntC (a : Delta) (k : Int) : Py Delta := do usToDeltaC (← pyDivmod a.toUs k).1
/-- `delta_divide` with a timedelta, :2595-2615 and `divide_timedelta_timedelta`, :2381-2405. -/
def floordivC (a b : Delta) : Py Int := do return (← pyDivmod a.toUs b.toUs).1
/-- `truedivide_timedelta_int`, :2427-2443 (`divide_nearest`, :389-400, i.e.
`_PyLong_DivmodNear`, which also rounds half to even). -/
def truedivIntC (a : Delta) (k : Int) : Py Delta := do usToDeltaC (← divideAndRound a.toUs k)
/-- `delta_remainder`, :2640-2673. -/
def modC (a b : Delta) : Py Delta := do usToDeltaC (← pyDivmod a.toUs b.toUs).2
/-- `delta_divmod`, :2675-2716. -/
def divmodC (a b : Delta) : Py (Int × Delta) := do
  let (q, r) ← pyDivmod a.toUs b.toUs
  return (q, ← usToDeltaC r)

end Delta

/-! ### `str` and `repr` -/

/-- Decimal digits of `n`, with `fuel` bounding the recursion depth. -/
def natDigitsAux : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, n => (if n < 10 then [] else natDigitsAux fuel (n / 10)) ++ [Char.ofNat (48 + n % 10)]

/-- Decimal digits of a natural number (`n + 1` levels always suffice). -/
def natDigits (n : Nat) : List Char := natDigitsAux (n + 1) n

/-- `'%0*d' % (width, n)` for `n >= 0`: zero padded to at least `width`. -/
def padNat (width n : Nat) : List Char :=
  let ds := natDigits n
  List.replicate (width - ds.length) '0' ++ ds

/-- `'%0*d' % (width, n)` for any int (the sign counts towards the width). -/
def padInt (width : Nat) (n : Int) : List Char :=
  if n < 0 then '-' :: padNat (width - 1) n.natAbs else padNat width n.toNat

/-- `'%d' % n`. -/
def showInt (n : Int) : List Char := padInt 0 n

/-- `timedelta.__str__`, _pydatetime.py:765-775; C `delta_str`, :2980-3007. -/
def Delta.str (t : Delta) : String :=
  let mm := t.seconds / 60
  let ss := t.seconds % 60
  let hh := mm / 60
  let mm := mm % 60
  let s := showInt hh ++ [':'] ++ padInt 2 mm ++ [':'] ++ padInt 2 ss
  let s := if t.days ≠ 0 then
      showInt t.days ++ " day".toList ++ (if t.days.natAbs ≠ 1 then ['s'] else []) ++ ", ".toList ++ s
    else s
  let s := if t.us ≠ 0 then s ++ ['.'] ++ padInt 6 t.us else s
  String.ofList s

/-- `timedelta.__repr__`, _pydatetime.py:751-763; C `delta_repr`, :2931-2978. -/
def Delta.repr (t : Delta) : String :=
  let args := (if t.days ≠ 0 then ["days=" ++ String.ofList (showInt t.days)] else []) ++
    (if t.seconds ≠ 0 then ["seconds=" ++ String.ofList (showInt t.seconds)] else []) ++
    (if t.us ≠ 0 then ["microseconds=" ++ String.ofList (showInt t.us)] else [])
  let args := if args.isEmpty then ["0"] else args
  "datetime.timedelta(" ++ ", ".intercalate args ++ ")"

end PyLean.Datetime
