import PyLean.Core
import PyLean.Binary64.Model

/-!
`queue.SimpleQueue.get(block, timeout)` on a non-empty queue: the C accelerator
(`_queue_SimpleQueue_get_impl`, Modules/_queuemodule.c) against the pure-Python twin
(`queue._PySimpleQueue.get`, Lib/queue.py:338-355). Only the path where an item is already
available is modelled; waiting is not.

A timeout is `None`, an `int`, another finite number of seconds, infinity or NaN. C converts it
first with `_PyTime_FromSecondsObject(..., _PyTime_ROUND_CEILING)` (Python/pytime.c:650-693): an
`int` is multiplied by 10^9 exactly; anything else goes through `PyFloat_AsDouble`, and the double
is multiplied by 1e9, rounded up and range-checked (`pytime_from_double`, Python/pytime.c:625-647).
NaN is a `ValueError`, a value whose nanoseconds leave `PyTime_t` (infinity included) an
`OverflowError`; then a negative timeout is a `ValueError`. The twin only rejects `timeout < 0`
(false for NaN) and then calls `self._count.acquire(block, timeout)`, which returns at once while
the count is positive.
-/

namespace PyLean.TextLibs.SQ

open PyLean.Binary64

/-- The built-in numbers only. `int n` is the `int` `n` (a `bool` is 0 or 1). `num n d`,
`d > 0`, is a finite `float`, or a `Fraction` or `Decimal` in the range of a double, with the exact
value `n / d`; `PyFloat_AsDouble` gives the nearest double. `inf` is `float('inf')` and `nan` is
`float('nan')`. Out of scope: a `Fraction` beyond the range of a double, which raises inside
`__float__` with its own message; `-inf`; `Decimal` NaNs; and subclasses or other objects with
their own `__index__`, `__float__` or `__lt__`. C takes the exact branch for anything with
`__index__` (`PyIndex_Check`, Python/pytime.c:654) and reads the stored value of an `int` or
`float` subclass, while the twin calls the object's `<`. -/
inductive TO where
  | none
  | int (n : Int)
  | num (n : Int) (d : Nat)
  | inf
  | nan

/-- `ceil(n * 10^9 / d)` for `d > 0`, the nanoseconds in exact arithmetic: Lean's `Int` division
floors for a positive divisor. -/
def ceilNs (n : Int) (d : Nat) : Int := -((-n * 1000000000) / (d : Int))

/-- `pytime_overflow`, Python/pytime.c:106-111. -/
def timeOverflow : PyExc := .overflowError "timestamp out of range for C PyTime_t"

/-- `pytime_from_double` with `_PyTime_ROUND_CEILING` and `unit_to_ns = 10^9`,
Python/pytime.c:625-647: `d *= 1e9` in double arithmetic, `ceil`, the test
`(double)PyTime_MIN <= d && d < -(double)PyTime_MIN`, then the cast of an integral double. -/
def fromDouble (x : F64) : Py Int :=
  let d := F64.ceil (F64.mul x (F64.ofInt 1000000000))
  if F64.le (F64.ofInt (-(2 ^ 63))) d && F64.lt d (F64.ofInt (2 ^ 63)) then .ok d.truncInt
  else .error timeOverflow

/-- `_PyTime_FromSecondsObject` with ceiling rounding, to nanoseconds: `pytime_from_object`,
Python/pytime.c:650-684. The `int` branch is `PyLong_AsLongLong` and `pytime_mul`, both of which
report the same overflow. -/
def toNs : TO → Py Int
  | .none => .ok 0
  | .nan => .error (.valueError "Invalid value NaN (not a number)")
  | .inf => .error timeOverflow
  | .int n =>
    if -(2 ^ 63) ≤ n * 1000000000 ∧ n * 1000000000 < 2 ^ 63 then .ok (n * 1000000000)
    else .error timeOverflow
  | .num n d => fromDouble (F64.ofRat (mkRat n d))

/-- C: convert (when blocking with a timeout), check the sign, then take the head. -/
def getC {α : Type} (block : Bool) (t : TO) (x : α) : Py α :=
  match block, t with
  | true, .none => .ok x
  | false, _ => .ok x
  | true, t => match toNs t with
    | .error e => .error e
    | .ok ns => if ns < 0 then .error (.valueError "'timeout' must be a non-negative number") else .ok x

/-- The twin: `timeout < 0` raises; otherwise the semaphore is acquired at once. -/
def getPy {α : Type} (block : Bool) (t : TO) (x : α) : Py α :=
  if !block then .ok x
  else match t with
    | .num n _ => if n < 0 then .error (.valueError "'timeout' must be a non-negative number") else .ok x
    | .int n => if n < 0 then .error (.valueError "'timeout' must be a non-negative number") else .ok x
    | _ => .ok x

/-- Whenever the twin returns the waiting item, so does C. -/
def GetTwins : Prop := ∀ (α : Type) (block : Bool) (t : TO) (x : α), getPy block t x = .ok x → getC block t x = .ok x

/-- `q.put(1); q.get(timeout=float('inf'))` raises `OverflowError` in C. -/
theorem getTwins_refuted : ¬ GetTwins := by
  intro h
  have := h Nat true .inf 1 rfl
  simp [getC, toNs] at this

/-- For `None` and for finite timeouts within `PyTime_t` that are non-negative or at most -1 ns,
the twins agree. Just below 0 they do not: for -1e-10 C rounds up to 0 ns and returns the item,
the twin raises `ValueError` (`getTwinsTinyNegative_refuted`). "Within `PyTime_t`" is meant of the
exact nanoseconds, `ceilNs`. False: C does not compute those. It converts a non-`int` timeout to a
double and multiplies by 1e9 in double arithmetic, so `Fraction(2**63 - 1, 10**9)`, whose exact
nanoseconds are `PyTime_MAX`, becomes 2^63 and is out of range. -/
def GetTwinsFinite : Prop :=
  ∀ (α : Type) (block : Bool) (n : Int) (d : Nat) (x : α), 0 < d →
    -(2 ^ 63) ≤ ceilNs n d → ceilNs n d < 2 ^ 63 → (0 ≤ n ∨ n * 1000000000 ≤ -(d : Int)) →
    getC block (.num n d) x = getPy block (.num n d) x ∧ getC block .none x = getPy block .none x

set_option maxRecDepth 100000 in
/-- `q.put(1); q.get(timeout=Fraction(2**63 - 1, 10**9))`: `OverflowError` in C, the item in the
twin. -/
theorem getTwinsFinite_refuted : ¬ GetTwinsFinite := by
  intro h
  have := (h Nat true (2 ^ 63 - 1) 1000000000 1 (by decide) (by decide) (by decide) (by decide)).1
  revert this
  decide +kernel

/-- For `None` and for an `int` timeout whose nanoseconds fit `PyTime_t`, the twins agree: the
`int` branch of the conversion is exact, so the sign C tests is the sign the twin tests.
Hypotheses: the range is where C does not raise `OverflowError`; outside it, with `block` true,
C raises and the twin does not (`getTwins_refuted` is that case for infinity). -/
def GetTwinsInt : Prop :=
  ∀ (α : Type) (block : Bool) (n : Int) (x : α),
    -(2 ^ 63) ≤ n * 1000000000 → n * 1000000000 < 2 ^ 63 →
    getC block (.int n) x = getPy block (.int n) x ∧ getC block .none x = getPy block .none x

theorem getTwinsInt_proven : GetTwinsInt := by
  intro α block n x h1 h2
  cases block
  · simp [getC, getPy]
  · refine ⟨?_, by simp [getC, getPy]⟩
    simp only [getC, getPy, toNs, ite_eq_left (And.intro h1 h2), Bool.not_true]
    by_cases hn : n < 0
    · have : n * 1000000000 < 0 := by omega
      simp [this, hn]
    · have : ¬ n * 1000000000 < 0 := by omega
      simp [this, hn]

/-- `q.get(timeout=-1e-10)` on a non-empty queue: C returns the item, the twin raises. -/
def GetTwinsTinyNegative : Prop := ∀ (α : Type) (n : Int) (d : Nat) (x : α), getC true (.num n d) x = getPy true (.num n d) x

set_option maxRecDepth 100000 in
theorem getTwinsTinyNegative_refuted : ¬ GetTwinsTinyNegative := by
  intro h
  have := h Nat (-1) 10000000000 1
  revert this
  decide +kernel

end PyLean.TextLibs.SQ
