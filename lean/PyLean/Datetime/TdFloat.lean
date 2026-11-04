import PyLean.Datetime.LocalZoneProps
import PyLean.Binary64.Float

/-!
`timedelta(...)` with `int` and `float` arguments: `timedelta.__new__`
(Lib/_pydatetime.py:657-768) and `delta_new_impl` with `accum` (Modules/_datetimemodule.c:
2733-2932), CPython 3.15.2, on exact binary64 floats (`PyLean.Binary64.F64`).

Arguments are exact `int` or `float` objects, or an object of another type (named by its
type's name); `int`/`float` subclasses with overridden arithmetic are out of scope (Python's
`weeks*7` would call their `__mul__`, C reads the value).
-/

namespace PyLean.Datetime
open PyLean PyLean.Binary64

/-- A `timedelta` constructor argument. -/
inductive TdNum where
  | int (n : Int)
  | float (x : F64)
  | other (ty : String)
  deriving DecidableEq, Inhabited

/-- C `modf(x, &intpart)` and Python's `math.modf` (Modules/mathmodule.c:1556-1570, which
returns `(copysign(0., x), x)` for an infinity first): `(fractional part, integral part)`,
both with the sign of `x`; exact. A NaN gives NaN twice. -/
def modfF (x : F64) : F64 × F64 :=
  if x.isNaN then (x, x)
  else if x.isInf then (F64.zero x.sign, x)
  else
    let i := F64.trunc x
    let f := F64.sub x i
    (if f.isZero then F64.zero x.sign else f, i)

/-- `float(n)` for an int operand of a float operation: `PyLong_AsDouble`, the
`OverflowError` past `DBL_MAX` included. -/
def tdToFloat (n : Int) : Py F64 := PyLong_AsDouble n

/-- `a * k` for an argument `a` and an int constant `k` (Py:686-688). -/
def tdMul (a : TdNum) (k : Int) : Py TdNum :=
  match a with
  | .int n => .ok (.int (n * k))
  | .float x => do return .float (F64.mul x (← tdToFloat k))
  | .other _ => .error .modelFuel

/-- `a + b` on ints and floats (`int + float` is `float.__radd__`, converting the int). -/
def tdAdd (a b : TdNum) : Py TdNum :=
  match a, b with
  | .int m, .int n => .ok (.int (m + n))
  | .float x, .int n => do return .float (F64.add x (← tdToFloat n))
  | .int m, .float y => do return .float (F64.add (← tdToFloat m) y)
  | .float x, .float y => .ok (.float (F64.add x y))
  | _, _ => .error .modelFuel

/-- `86400.0` (`24.*3600.`) and `1e6`. -/
def f86400 : F64 := F64.ofBits 0x40f5180000000000
def f1e6 : F64 := F64.ofBits 0x412e848000000000

/-- `timedelta.__new__`, Py:657-768, for every argument. -/
def deltaNumPy (days seconds microseconds milliseconds minutes hours weeks : TdNum) : Py Delta := do
  -- :667-679, in this order
  for (name, v) in [("days", days), ("seconds", seconds), ("microseconds", microseconds),
      ("milliseconds", milliseconds), ("minutes", minutes), ("hours", hours), ("weeks", weeks)] do
    if let .other ty := v then
      throw (.typeError s!"~unsupported type for timedelta {name} component: {ty}")
  -- :686-688
  let days ← tdAdd days (← tdMul weeks 7)
  let seconds ← tdAdd seconds (← tdAdd (← tdMul minutes 60) (← tdMul hours 3600))
  let microseconds ← tdAdd microseconds (← tdMul milliseconds 1000)
  -- :692-701
  let (d, s, daysecondsfrac) ← match days with
    | .float x => do
      let (dayfrac, days) := modfF x
      let (daysecondsfrac, daysecondswhole) := modfF (F64.mul dayfrac f86400)
      let s ← PyLong_FromDouble daysecondswhole
      let d ← PyLong_FromDouble days
      pure (d, s, daysecondsfrac)
    | .int n => pure (n, (0 : Int), F64.zero false)
    | .other _ => throw .modelFuel
  -- :709-724
  let (seconds, secondsfrac) ← match seconds with
    | .float x => do
      let (secondsfrac, seconds) := modfF x
      let seconds ← PyLong_FromDouble seconds
      pure (seconds, F64.add secondsfrac daysecondsfrac)
    | .int n => pure (n, daysecondsfrac)
    | .other _ => throw .modelFuel
  let d := d + seconds / 86400
  let s := s + seconds % 86400
  -- :727
  let usdouble := F64.mul secondsfrac f1e6
  -- :731-746
  let (d, s, microseconds) ← match microseconds with
    | .float x => do
      let m ← float_round_int (F64.add x usdouble)
      let sec := m / 1000000
      let m := m % 1000000
      pure (d + sec / 86400, s + sec % 86400, m)
    | .int n => do
      let sec := n / 1000000
      let m := n % 1000000
      let m ← float_round_int (F64.add (← tdToFloat m) usdouble)
      pure (d + sec / 86400, s + sec % 86400, m)
    | .other _ => throw .modelFuel
  -- :754-757
  let s := s + microseconds / 1000000
  let us := microseconds % 1000000
  let d := d + s / 86400
  let s := s % 86400
  -- :763-764
  if d.natAbs > 999999999 then throw (.overflowError s!"timedelta # of days is too large: {d}")
  return ⟨d, s, us⟩

/-- `accum(tag, sofar, num, factor, &leftover)`, :2733-2811: an int adds `num * factor`
exactly; a float is split by `modf`, its integral part converted exactly
(`PyLong_FromDouble`, which refuses an infinity or NaN), and its fractional part times the
factor split again, the integral part added and the rest added into `leftover` (a double);
another type is `TypeError`. -/
def accumC (tag : String) (sofar : Int) (num : TdNum) (factor : Int) (leftover : F64) : Py (Int × F64) :=
  match num with
  | .int n => .ok (sofar + n * factor, leftover)
  | .float x => do
    let (fracpart, intpart) := modfF x
    let xi ← PyLong_FromDouble intpart
    let sum := sofar + xi * factor
    if F64.eq fracpart (F64.zero false) then return (sum, leftover)
    let dnum := F64.mul (F64.ofInt factor) fracpart
    let (fracpart, intpart) := modfF dnum
    let x2 ← PyLong_FromDouble intpart
    return (sum + x2, F64.add leftover fracpart)
  | .other ty => .error (.typeError s!"~unsupported type for timedelta {tag} component: {ty}")

/-- `delta_new_impl`, :2832-2932: `accum` for each argument given, in the order microseconds,
milliseconds, seconds, minutes, hours, days, weeks; then a nonzero `leftover_us` rounded to
the nearest integer (`round`, halfway away from zero) with the round-half-to-even fix-up when
it is exactly halfway (:2887-2922, using `x & 1`), added in; then
`microseconds_to_delta_ex`. An omitted argument is `none`. -/
def deltaNumC (days seconds microseconds milliseconds minutes hours weeks : Option TdNum) : Py Delta := do
  let step (acc : Int × F64) (a : Option TdNum × String × Int) : Py (Int × F64) :=
    match a.1 with
    | none => .ok acc
    | some v => accumC a.2.1 acc.1 v a.2.2 acc.2
  let (x, leftover) ← [(microseconds, "microseconds", 1), (milliseconds, "milliseconds", 1000),
      (seconds, "seconds", 1000000), (minutes, "minutes", 60000000), (hours, "hours", 3600000000),
      (days, "days", 86400000000), (weeks, "weeks", 604800000000)].foldlM step (0, F64.zero false)
  let x ← if F64.ne leftover (F64.zero false) then do
      let wholeUs := F64.roundAway leftover
      let wholeUs :=
        if F64.eq (F64.sub wholeUs leftover).abs Binary64.dHalf then
          let xIsOdd : Int := x % 2
          F64.sub (F64.mul Binary64.d2 (F64.roundAway (F64.mul (F64.add leftover (F64.ofInt xIsOdd)) Binary64.dHalf)))
            (F64.ofInt xIsOdd)
        else wholeUs
      pure (x + wholeUs.truncInt)
    else pure x
  usToDeltaC x

/-! ### The twins on float arguments -/

/-- `timedelta(...)` agrees between the twins (same value, or the same exception class) for
every combination of int and float arguments, an omitted one being `0` in Python. -/
def TimedeltaFloatCtorTwins : Prop :=
  ∀ (days seconds microseconds milliseconds minutes hours weeks : Option TdNum),
    SameOutcome
      (deltaNumPy (days.getD (.int 0)) (seconds.getD (.int 0)) (microseconds.getD (.int 0))
        (milliseconds.getD (.int 0)) (minutes.getD (.int 0)) (hours.getD (.int 0)) (weeks.getD (.int 0)))
      (deltaNumC days seconds microseconds milliseconds minutes hours weeks)

/-- `timedelta(hours=10000000.1)`: C's `accum` converts the integral part exactly and keeps
`0.1 * 3600000000` µs apart, giving `416666 days, 57959 s, 999999 µs`; Python first forms
`hours * 3600` as a double, whose rounding moves the sum to `416666 days, 57960 s, 0 µs`
(gh-160806, fixed on main, not in 3.15.2). -/
theorem timedeltaFloatCtorTwins_refuted : ¬ TimedeltaFloatCtorTwins := by
  intro h
  have := h none none none none none (some (.float (F64.ofBits 0x416312d003333333))) none
  revert this
  decide +kernel

/-- The exact results of that call in each twin, as CPython 3.15.2 prints them. -/
theorem timedeltaFloatCtor_example :
    deltaNumPy (.int 0) (.int 0) (.int 0) (.int 0) (.int 0) (.float (F64.ofBits 0x416312d003333333)) (.int 0) =
      .ok ⟨416666, 57960, 0⟩ ∧
    deltaNumC none none none none none (some (.float (F64.ofBits 0x416312d003333333))) none =
      .ok ⟨416666, 57959, 999999⟩ := by
  decide +kernel

end PyLean.Datetime
