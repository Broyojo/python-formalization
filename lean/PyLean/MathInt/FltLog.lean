import PyLean.MathInt.FltBase

/-!
# `Modules/mathmodule.c`: `log`, `log2`, `log10`

CPython 3.15.2. The C library `log`, `log2` and `log10` are parameters (`CFun1`); the
special values, the `int` path that works for ints beyond the float range, and the
retry through `__index__` are CPython's own.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64

/-- `m_log`, mathmodule.c:628-648, around the C library `log`. -/
def m_log (clog : CFun1) (x : F64) : F64 × Errno :=
  if x.isFinite then
    if F64.lt c0 x then clog x
    else if isZeroC x then (F64.neg cInf, .edom)
    else (cNaN, .edom)
  else if x.isNaN then (x, .zero)
  else if F64.lt c0 x then (x, .zero)
  else (cNaN, .edom)

/-- `m_log2`, mathmodule.c:660-685, around the C library `log2`. -/
def m_log2 (clog2 : CFun1) (x : F64) : F64 × Errno :=
  if !x.isFinite then
    if x.isNaN then (x, .zero)
    else if F64.lt c0 x then (x, .zero)
    else (cNaN, .edom)
  else if F64.lt c0 x then clog2 x
  else if isZeroC x then (F64.neg cInf, .edom)
  else (cNaN, .edom)

/-- `m_log10`, mathmodule.c:687-707, around the C library `log10`. -/
def m_log10 (clog10 : CFun1) (x : F64) : F64 × Errno :=
  if x.isFinite then
    if F64.lt c0 x then clog10 x
    else if isZeroC x then (F64.neg cInf, .edom)
    else (cNaN, .edom)
  else if x.isNaN then (x, .zero)
  else if F64.lt c0 x then (x, .zero)
  else (cNaN, .edom)

/-- `_PyLong_Frexp`, longobject.c:3467-3561, for `n > 0`: `n / 2 ** bits` rounded half to
even to 53 bits, and `bits`; a significand that rounds up to `1.0` becomes `0.5` with the
exponent one higher (:3551-3557). -/
def _PyLong_Frexp (n : Int) : F64 × Int :=
  let b := bitLength n.natAbs
  let x := F64.ofRat ((n : Rat) / ((2 ^ b : Nat) : Rat))
  if F64.eq x c1 then (cHalf, b + 1) else (x, b)

/-- `loghelper_int`, mathmodule.c:1582-1612. `func` is `m_log`, `m_log2` or `m_log10`; the
`errno` it leaves is not looked at. -/
def loghelper_int (n : Int) (func : CFun1) : Py F64 :=
  if n ≤ 0 then .error (.valueError "expected a positive input")
  else
    match PyLong_AsDouble n with
    | .ok x => .ok (func x).1
    | .error _ =>
      -- the conversion overflowed (`PyLong_AsDouble` raises nothing else for an int)
      let (x, e) := _PyLong_Frexp n
      .ok (F64.fma (func c2).1 (F64.ofInt e) (func x).1)

/-- `loghelper`, mathmodule.c:1614-1639. -/
def loghelper (arg : Arg) (func : CFun1) : Py F64 :=
  match arg.intVal with
  | some n => loghelper_int n func
  | none =>
    match math_1 arg func false (some "expected a positive input, got ") with
    | .error (.overflowError m) =>
      if arg.indexCheck then do
        let n ← _PyNumber_Index arg
        loghelper_int n func
      else .error (.overflowError m)
    | r => r

/-- `math_log`, mathmodule.c:1644-1667. `PyNumber_TrueDivide` of two floats is `float_div`
(floatobject.c:572-584). -/
def math_log (clog : CFun1) (args : List Arg) : Py F64 := do
  checkPositional "log" args.length 1 2
  let num ← loghelper (args.getD 0 default) (m_log clog)
  if args.length == 1 then return num
  let den ← loghelper (args.getD 1 default) (m_log clog)
  if F64.eq den c0 then .error (.zeroDivisionError "division by zero")
  else .ok (F64.div num den)

/-- `math_log2`, mathmodule.c:1683-1688. -/
def math_log2 (clog2 : CFun1) (x : Arg) : Py F64 := loghelper x (m_log2 clog2)

/-- `math_log10`, mathmodule.c:1700-1705. -/
def math_log10 (clog10 : CFun1) (x : Arg) : Py F64 := loghelper x (m_log10 clog10)

end PyLean.MathInt
