import PyLean.Core

/-!
`timedelta` with integer arguments: the pure-Python class
(`Lib/_pydatetime.py:635-995`) and the C type (`Modules/_datetimemodule.c`,
`delta_new_impl` :2832-2932, `microseconds_to_delta_ex` :2218-2284, `new_delta_ex`
:1383-1411 and the number methods).

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

/-- `timedelta._to_microseconds`, _pydatetime.py:873-875; C
`delta_to_microseconds`, :2139-2190. -/
def Delta.toUs (t : Delta) : Int := (t.days * 86400 + t.seconds) * 1000000 + t.us

/-- The field invariant every constructed `timedelta` satisfies. -/
def Delta.Valid (t : Delta) : Prop :=
  0 ≤ t.seconds ∧ t.seconds < 86400 ∧ 0 ≤ t.us ∧ t.us < 1000000 ∧
  -MAX_DELTA_DAYS ≤ t.days ∧ t.days ≤ MAX_DELTA_DAYS

instance (t : Delta) : Decidable t.Valid := by unfold Delta.Valid; infer_instance

/-! ### Pure Python -/

/-- `timedelta(days, seconds, microseconds, milliseconds, minutes, hours,
weeks)` with int arguments, _pydatetime.py:657-768. The type loop (:667-679) passes and the
float branches are not taken; `round(microseconds + usdouble)` (:746) is the identity because
`usdouble == 0.0` and `|microseconds| < 10**6` there. -/
def deltaPy (days seconds microseconds milliseconds minutes hours weeks : Int) : Py Delta :=
  -- :686-688
  let days := days + weeks * 7
  let seconds := seconds + minutes * 60 + hours * 3600
  let microseconds := microseconds + milliseconds * 1000
  -- :699-701 (int branch of :692-701: `daysecondsfrac = 0.0`, `d = days`)
  let d := days
  let s : Int := 0
  -- :721-724 (`seconds` is an int: :715-716)
  let d := d + seconds / 86400
  let s := s + seconds % 86400
  -- :740-745 (int branch of :733-746)
  let sec2 := microseconds / 1000000
  let microseconds := microseconds % 1000000
  let d := d + sec2 / 86400
  let s := s + sec2 % 86400
  -- :754-757
  let s := s + microseconds / 1000000
  let us := microseconds % 1000000
  let d := d + s / 86400
  let s := s % 86400
  -- :763-764
  if d.natAbs > 999999999 then .error (.overflowError s!"timedelta # of days is too large: {d}")
  else .ok ⟨d, s, us⟩

/-- `timedelta(0, 0, us)`. -/
def usToDeltaPy (us : Int) : Py Delta := deltaPy 0 0 us 0 0 0 0

/-- Python `divmod(a, b)` / `a // b` / `a % b` on ints. -/
def pyDivmod (a b : Int) : Py (Int × Int) :=
  if b = 0 then .error (.zeroDivisionError "division by zero")
  else .ok (a.fdiv b, a.fmod b)

/-- `_divide_and_round`, _pydatetime.py:615-632 (round half to even). -/
def divideAndRound (a b : Int) : Py Int := do
  let (q, r) ← pyDivmod a b
  let r := r * 2
  let greaterThanHalf := if b > 0 then r > b else r < b
  if greaterThanHalf ∨ (r = b ∧ q % 2 = 1) then return q + 1 else return q

/-- C `divide_nearest`, :392-403, which is `_PyLong_DivmodNear(m, n)[0]`,
Objects/longobject.c:6118-6187: truncating `long_divrem`, then twice the remainder (negated
when the quotient is negative) compared with the divisor, then the quotient moved one away
from zero. The `PyLong_Check` refusals cannot happen: both callers pass ints. -/
def divideNearestC (a b : Int) : Py Int :=
  if b = 0 then .error (.zeroDivisionError "division by zero")
  else
    let quoIsNeg := decide (a < 0) != decide (b < 0)
    let quo := a.tdiv b
    let rem := a.tmod b
    let twiceRem := if quoIsNeg then -(2 * rem) else 2 * rem
    let cmp : Int := if twiceRem < b then -1 else if twiceRem = b then 0 else 1
    let quoIsOdd := quo.natAbs % 2 = 1
    if (if b < 0 then cmp < 0 else cmp > 0) ∨ (cmp = 0 ∧ quoIsOdd) then
      .ok (if quoIsNeg then quo - 1 else quo + 1)
    else .ok quo

namespace Delta

/-- `__add__`, _pydatetime.py:817-824. -/
def addPy (a b : Delta) : Py Delta := deltaPy (a.days + b.days) (a.seconds + b.seconds) (a.us + b.us) 0 0 0 0
/-- `__sub__`, :828-835. -/
def subPy (a b : Delta) : Py Delta := deltaPy (a.days - b.days) (a.seconds - b.seconds) (a.us - b.us) 0 0 0 0
/-- `__neg__`, :842-847. -/
def negPy (a : Delta) : Py Delta := deltaPy (-a.days) (-a.seconds) (-a.us) 0 0 0 0
/-- `__abs__`, :852-856. -/
def absPy (a : Delta) : Py Delta := if a.days < 0 then a.negPy else .ok a
/-- `__mul__` with an int, :858-869. -/
def mulPy (a : Delta) (k : Int) : Py Delta := deltaPy (a.days * k) (a.seconds * k) (a.us * k) 0 0 0 0
/-- `__floordiv__` with an int, :877-884. -/
def floordivIntPy (a : Delta) (k : Int) : Py Delta := do
  let (q, _) ← pyDivmod a.toUs k
  usToDeltaPy q
/-- `__floordiv__` with a timedelta. -/
def floordivPy (a b : Delta) : Py Int := do return (← pyDivmod a.toUs b.toUs).1
/-- `__truediv__` with an int, :886-896. -/
def truedivIntPy (a : Delta) (k : Int) : Py Delta := do usToDeltaPy (← divideAndRound a.toUs k)
/-- `__mod__`, :898-902. -/
def modPy (a b : Delta) : Py Delta := do usToDeltaPy (← pyDivmod a.toUs b.toUs).2
/-- `__divmod__`, :904-909. -/
def divmodPy (a b : Delta) : Py (Int × Delta) := do
  let (q, r) ← pyDivmod a.toUs b.toUs
  return (q, ← usToDeltaPy r)

end Delta

/-! ### C -/

/-- `PyLong_AsInt` on a Python int. -/
def asCInt (x : Int) : Py Int :=
  if -2 ^ 31 ≤ x ∧ x ≤ 2 ^ 31 - 1 then .ok x
  else .error (.overflowError "Python int too large to convert to C int")

/-- `check_delta_day_range`, _datetimemodule.c:645-653. -/
def checkDeltaDayRange (d : Int) : Py Unit :=
  if -MAX_DELTA_DAYS ≤ d ∧ d ≤ MAX_DELTA_DAYS then .ok ()
  else .error (.overflowError s!"days={d}; must have magnitude <= 999999999")

/-- `microseconds_to_delta_ex`, :2218-2284. The `BadDivmod` branches are dead
for int `divmod`. -/
def usToDeltaC (x : Int) : Py Delta := do
  let us := x % 1000000
  let num := x / 1000000
  let s := num % 86400
  let d ← asCInt (num / 86400)
  checkDeltaDayRange d
  return ⟨d, s, us⟩

/-- `delta_new_impl` with int arguments, :2832-2932: the arguments are accumulated
into an exact microsecond count (`accum`, :2733-2811) in the order
microseconds, milliseconds, seconds, minutes, hours, days, weeks. -/
def deltaC (days seconds microseconds milliseconds minutes hours weeks : Int) : Py Delta :=
  usToDeltaC (microseconds + milliseconds * 1000 + seconds * 1000000 + minutes * 60000000 +
    hours * 3600000000 + days * 86400000000 + weeks * 604800000000)

/-- `normalize_pair`, :724-735, using the C `divmod` helper (:373-386), which
rounds towards minus infinity. The callers' inputs are within a few times the
field ranges, so the C `int` arithmetic does not overflow. -/
def normalizePair (hi lo factor : Int) : Int × Int :=
  if lo < 0 ∨ lo ≥ factor then (hi + lo / factor, lo % factor) else (hi, lo)

/-- `new_delta(d, s, us, 1)`: `normalize_d_s_us` (:744-767) then the day range
check, :1383-1411. -/
def newDeltaNormC (d s us : Int) : Py Delta := do
  let (s, us) := if us < 0 ∨ us ≥ 1000000 then normalizePair s us 1000000 else (s, us)
  let (d, s) := if s < 0 ∨ s ≥ 86400 then normalizePair d s 86400 else (d, s)
  checkDeltaDayRange d
  return ⟨d, s, us⟩

namespace Delta

/-- `delta_add`, :2455-2474. -/
def addC (a b : Delta) : Py Delta := newDeltaNormC (a.days + b.days) (a.seconds + b.seconds) (a.us + b.us)
/-- `delta_subtract`, :2514-2533. -/
def subC (a b : Delta) : Py Delta := newDeltaNormC (a.days - b.days) (a.seconds - b.seconds) (a.us - b.us)
/-- `delta_negative`, :2477-2483. -/
def negC (a : Delta) : Py Delta := newDeltaNormC (-a.days) (-a.seconds) (-a.us)
/-- `delta_abs`, :2498-2511 (`delta_positive` copies without normalizing). -/
def absC (a : Delta) : Py Delta := if a.days < 0 then a.negC else .ok a
/-- `multiply_int_timedelta`, :2290-2308. -/
def mulC (a : Delta) (k : Int) : Py Delta := usToDeltaC (k * a.toUs)
/-- `divide_timedelta_int`, :2370-2388 (`PyNumber_FloorDivide`). -/
def floordivIntC (a : Delta) (k : Int) : Py Delta := do usToDeltaC (← pyDivmod a.toUs k).1
/-- `delta_divide` with a timedelta, :2605-2624 and `divide_timedelta_timedelta`, :2391-2411. -/
def floordivC (a b : Delta) : Py Int := do return (← pyDivmod a.toUs b.toUs).1
/-- `truedivide_timedelta_int`, :2437-2452: `divide_nearest`, then `microseconds_to_delta`. -/
def truedivIntC (a : Delta) (k : Int) : Py Delta := do usToDeltaC (← divideNearestC a.toUs k)
/-- `delta_remainder`, :2650-2682. -/
def modC (a b : Delta) : Py Delta := do usToDeltaC (← pyDivmod a.toUs b.toUs).2
/-- `delta_divmod`, :2685-2721. -/
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

/-- `timedelta.__str__`, _pydatetime.py:784-794; C `delta_str`, :2992-3018. -/
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

/-- `timedelta.__repr__`, _pydatetime.py:770-782; C `delta_repr`, :2943-2989. -/
def Delta.repr (t : Delta) : String :=
  let args := (if t.days ≠ 0 then ["days=" ++ String.ofList (showInt t.days)] else []) ++
    (if t.seconds ≠ 0 then ["seconds=" ++ String.ofList (showInt t.seconds)] else []) ++
    (if t.us ≠ 0 then ["microseconds=" ++ String.ofList (showInt t.us)] else [])
  let args := if args.isEmpty then ["0"] else args
  "datetime.timedelta(" ++ ", ".intercalate args ++ ")"

end PyLean.Datetime
