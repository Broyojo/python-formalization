import PyLean.MathInt.FltBase

/-!
# `Modules/mathmodule.c`: the functions CPython computes itself

`frexp`, `ldexp`, `modf`, `fmod`, `remainder`, `fma`, `pow`, `isclose`, the classification
predicates, `nextafter`, `ulp`, `floor`, `ceil`, `trunc`, `degrees`, `radians`. CPython
3.15.2. Each function takes its arguments as objects and converts them as the Argument
Clinic code in `Modules/clinic/mathmodule.c.h` does, so conversion errors come first and
in argument order.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64

def LONG_MAX : Int := 2 ^ 63 - 1
def LONG_MIN : Int := -(2 ^ 63)
def INT_MAX : Int := 2 ^ 31 - 1
def INT_MIN : Int := -(2 ^ 31)

/-- Raise what `is_error` raises, or return `r`; the common tail
`if (errno && is_error(r, 1)) return NULL; return PyFloat_FromDouble(r);`. -/
def finishErrno (r : F64) (errno : Errno) : Py F64 :=
  if errno != .zero then
    match is_error r errno true with
    | .ok => .ok r
    | .raise e => .error e
    | .silent => .error (.valueError "math domain error")  -- unreachable: raise_edom is 1
  else .ok r

/-! ## `frexp`, `ldexp`, `modf` -/

/-- `math_frexp_impl`, mathmodule.c:1446-1460. `!x` is `x == 0.0`. -/
def math_frexp (o : Arg) : Py (F64 × Int) := do
  let x ← convDouble o
  if x.isNaN || x.isInf || isZeroC x then .ok (x, 0)
  else .ok (F64.frexp x)

/-- `PyLong_AsLongAndOverflow` on an `int`, with the `overflow` replacement of
mathmodule.c:1486-1490: out-of-range values become `LONG_MAX` or `LONG_MIN`. -/
def clampLong (n : Int) : Int :=
  if LONG_MAX < n then LONG_MAX else if n < LONG_MIN then LONG_MIN else n

/-- `math_ldexp_impl`, mathmodule.c:1475-1541 (the `_MSC_VER` block is not compiled). -/
def math_ldexp (ox oi : Arg) : Py F64 := do
  let x ← convDouble ox
  let exp ← match oi.intVal with
    | some n => Except.ok (clampLong n)
    | none => .error (.typeError "Expected an int as second argument to ldexp.")
  let (r, errno) : F64 × Errno :=
    if isZeroC x || !x.isFinite then (x, .zero)
    else if INT_MAX < exp then (F64.copysign cInf x, .erange)
    else if exp < INT_MIN then (F64.copysign c0 x, .zero)
    else
      let r := F64.ldexp x exp
      (r, if r.isInf then .erange else .zero)
  finishErrno r errno

/-- C `modf`: the integral part `trunc(x)` and the fraction `x - trunc(x)`, both with the
sign of `x` (C99 7.12.6.12). -/
def cModf (x : F64) : F64 × F64 :=
  let i := F64.trunc x
  (F64.copysign (F64.sub x i) x, i)

/-- `math_modf_impl`, mathmodule.c:1555-1570. -/
def math_modf (o : Arg) : Py (F64 × F64) := do
  let x ← convDouble o
  if x.isInf then .ok (F64.copysign c0 x, x)
  else if x.isNaN then .ok (x, x)
  else .ok (cModf x)

/-! ## `fmod`, `remainder` -/

/-- `math_fmod_impl`, mathmodule.c:1762-1791 (the `_MSC_VER` block is not compiled). The C
`fmod` is exact; it only leaves `errno` set with a NaN result, which :1781-1786 overwrite. -/
def math_fmod (ox oy : Arg) : Py F64 := do
  let x ← convDouble ox
  let y ← convDouble oy
  if y.isInf && x.isFinite then .ok x
  else
    let r := F64.fmod x y
    let errno : Errno := if r.isNaN then (if !x.isNaN && !y.isNaN then .edom else .zero) else .zero
    finishErrno r errno

/-- `m_remainder`, mathmodule.c:530-618. -/
def m_remainder (x y : F64) : F64 :=
  if x.isFinite && y.isFinite then
    if isZeroC y then cNaN
    else
      let absx := F64.abs x
      let absy := F64.abs y
      let m := F64.fmod absx absy
      let c := F64.sub absy m
      let r :=
        if F64.lt m c then m
        else if F64.lt c m then F64.neg c
        else F64.sub m (F64.mul c2 (F64.fmod (F64.mul cHalf (F64.sub absx m)) absy))
      F64.mul (F64.copysign c1 x) r
  else if x.isNaN then x
  else if y.isNaN then y
  else if x.isInf then cNaN
  else x

/-- `math.remainder`: `FUNC2(remainder, m_remainder, ...)`, mathmodule.c:1131, through
`math_2`. `m_remainder` never writes `errno` (its `fmod` calls are on finite numbers with a
nonzero divisor). -/
def math_remainder (args : List Arg) : Py F64 :=
  math_2 args (fun x y => (m_remainder x y, .zero)) "remainder"

/-! ## `fma` -/

/-- `math_fma_impl`, mathmodule.c:1721-1747, with the C `fma` exact. -/
def math_fma (ox oy oz : Arg) : Py F64 := do
  let x ← convDouble ox
  let y ← convDouble oy
  let z ← convDouble oz
  let r := F64.fma x y z
  if r.isFinite then .ok r
  else if r.isNaN then
    if !x.isNaN && !y.isNaN && !z.isNaN then .error (.valueError "invalid operation in fma")
    else .ok r
  else if x.isFinite && y.isFinite && z.isFinite then .error (.overflowError "overflow in fma")
  else .ok r

/-! ## `pow` -/

/-- The body of `math_pow_impl`, mathmodule.c:2370-2426: the result and `errno`. `cpow` is the
C library `pow`, only called with finite arguments. -/
def math_pow_core (cpow : CFun2) (x y : F64) : F64 × Errno :=
  if !x.isFinite || !y.isFinite then
    let r :=
      if x.isNaN then (if isZeroC y then c1 else x)
      else if y.isNaN then (if F64.eq x c1 then c1 else y)
      else if x.isInf then
        let odd_y := y.isFinite && F64.eq (F64.fmod (F64.abs y) c2) c1
        if F64.lt c0 y then (if odd_y then x else F64.abs x)
        else if isZeroC y then c1
        else (if odd_y then F64.copysign c0 x else c0)
      else
        if F64.eq (F64.abs x) c1 then c1
        else if F64.lt c0 y && F64.lt c1 (F64.abs x) then y
        else if F64.lt y c0 && F64.lt (F64.abs x) c1 then F64.neg y
        else c0
    (r, .zero)
  else
    let (r, e0) := cpow x y
    let errno : Errno :=
      if !r.isFinite then
        (if r.isNaN then .edom else if isZeroC x then .edom else .erange)
      else e0
    (r, errno)

/-- `math_pow_impl`, mathmodule.c:2366-2432. -/
def math_pow (cpow : CFun2) (ox oy : Arg) : Py F64 := do
  let x ← convDouble ox
  let y ← convDouble oy
  let (r, errno) := math_pow_core cpow x y
  finishErrno r errno

/-! ## `isclose` -/

/-- `1e-09`, the default `rel_tol`. -/
def relTolDefault : F64 := F64.ofBits 0x3e112e0be826d695

/-- `math_isclose_impl`, mathmodule.c:2587-2628, after the clinic conversions of
clinic/mathmodule.c.h (`a`, `b`, then `rel_tol` and `abs_tol` when given). -/
def isclose_impl (a b rel_tol abs_tol : F64) : Py Bool :=
  if F64.lt rel_tol c0 || F64.lt abs_tol c0 then
    .error (.valueError "tolerances must be non-negative")
  else if F64.eq a b then .ok true
  else if a.isInf || b.isInf then .ok false
  else
    let diff := F64.abs (F64.sub b a)
    .ok ((F64.le diff (F64.abs (F64.mul rel_tol b)) || F64.le diff (F64.abs (F64.mul rel_tol a)))
      || F64.le diff abs_tol)

def math_isclose (oa ob : Arg) (orel oabs : Option Arg) : Py Bool := do
  let a ← convDouble oa
  let b ← convDouble ob
  let rel_tol ← match orel with | some o => convDouble o | none => .ok relTolDefault
  let abs_tol ← match oabs with | some o => convDouble o | none => .ok c0
  isclose_impl a b rel_tol abs_tol

/-! ## Classification -/

/-- C `isnormal`: finite, nonzero and not subnormal. -/
def cIsNormal (x : F64) : Bool := x.bexp != 0 && x.bexp != 2047

/-- C23 `issubnormal`. -/
def cIsSubnormal (x : F64) : Bool := x.bexp == 0 && x.frac != 0

/-- `math_isfinite_impl`, mathmodule.c:2481-2486. -/
def math_isfinite (o : Arg) : Py Bool := do return (← convDouble o).isFinite
/-- `math_isnan_impl`, mathmodule.c:2536-2541. -/
def math_isnan (o : Arg) : Py Bool := do return (← convDouble o).isNaN
/-- `math_isinf_impl`, mathmodule.c:2554-2559. -/
def math_isinf (o : Arg) : Py Bool := do return (← convDouble o).isInf
/-- `math_isnormal_impl`, mathmodule.c:2498-2503. -/
def math_isnormal (o : Arg) : Py Bool := do return cIsNormal (← convDouble o)
/-- `math_issubnormal_impl`, mathmodule.c:2515-2524, the `#else` branch the 3.15.2 build
compiles (C11): `isfinite(x) && x && !isnormal(x)`. -/
def math_issubnormal (o : Arg) : Py Bool := do
  let x ← convDouble o
  return x.isFinite && !isZeroC x && !cIsNormal x
/-- The C23 branch of `math_issubnormal_impl`, mathmodule.c:2519-2520. -/
def math_issubnormal_c23 (o : Arg) : Py Bool := do return cIsSubnormal (← convDouble o)
/-- `math_signbit_impl`, mathmodule.c:1147-1152. -/
def math_signbit (o : Arg) : Py Bool := do return (← convDouble o).sign

/-- `math.copysign`: `FUNC2(copysign, copysign, ...)`, mathmodule.c:1015, through `math_2`. -/
def math_copysign (args : List Arg) : Py F64 :=
  math_2 args (fun x y => (F64.copysign x y, .zero)) "copysign"

/-! ## `nextafter`, `ulp` -/

def UINT64_MAX : Nat := 2 ^ 64 - 1

/-- `math_nextafter_impl`, mathmodule.c:2853-2965 (the `_AIX` block is not compiled).
`steps = none` is `steps=None`. The C `nextafter` is `F64.nextafter`. -/
def math_nextafter (ox oy : Arg) (osteps : Option Arg) : Py F64 := do
  let x ← convDouble ox
  let y ← convDouble oy
  match osteps with
  | none => .ok (F64.nextafter x y)
  | some s =>
    let n ← _PyNumber_Index s
    if n < 0 then .error (.valueError "steps must be a non-negative integer")
    else
      -- `PyLong_AsUnsignedLongLong`; an `OverflowError` is cleared, :2886-2905
      let usteps : Nat := if (UINT64_MAX : Int) ≤ n then UINT64_MAX else n.toNat
      if usteps == 0 then .ok x
      else if x.isNaN then .ok x
      else if y.isNaN then .ok y
      else if x.bits == y.bits then .ok x
      else
        let signBit : Nat := 2 ^ 63
        let ax := x.bits % signBit
        let ay := y.bits % signBit
        if (x.bits ^^^ y.bits) &&& signBit != 0 then
          if ax + ay ≤ usteps then .ok y
          else if ax < usteps then .ok (F64.ofBits ((y.bits &&& signBit) ||| (usteps - ax)))
          else .ok (F64.ofBits (x.bits - usteps))
        else if ay < ax then
          if usteps ≤ ax - ay then .ok (F64.ofBits (x.bits - usteps)) else .ok y
        else
          if usteps ≤ ay - ax then .ok (F64.ofBits (x.bits + usteps)) else .ok y

/-- `math_ulp_impl`, mathmodule.c:2977-2996. -/
def ulp_impl (x : F64) : F64 :=
  if x.isNaN then x
  else
    let x := F64.abs x
    if x.isInf then x
    else
      let x2 := F64.nextafter x cInf
      if x2.isInf then F64.sub x (F64.nextafter x (F64.neg cInf))
      else F64.sub x2 x

def math_ulp (o : Arg) : Py F64 := do return ulp_impl (← convDouble o)

/-! ## `floor`, `ceil`, `trunc` -/

/-- What `_PyObject_MaybeCallSpecialNoArgs(o, name)` finds and calls for `__floor__`: a
float subclass inherits `float.__floor__` (floatobject.c:874-880) unless it overrides it,
`int.__floor__` returns the int itself, other types have it or not. -/
def floorMethod : Arg → Option (Py Ret)
  | .float x => some ((float_floor x).map .int)
  | .floatSub _ x f _ _ => some (f.getD ((float_floor x).map .int))
  | .int n => some (.ok (.int n))
  | .bool b => some (.ok (.int (if b then 1 else 0)))
  | .other _ _ _ _ f _ _ => f

def ceilMethod : Arg → Option (Py Ret)
  | .float x => some ((float_ceil x).map .int)
  | .floatSub _ x _ c _ => some (c.getD ((float_ceil x).map .int))
  | .int n => some (.ok (.int n))
  | .bool b => some (.ok (.int (if b then 1 else 0)))
  | .other _ _ _ _ _ c _ => c

def truncMethod : Arg → Option (Py Ret)
  | .float x => some ((float_trunc x).map .int)
  | .floatSub _ x _ _ t => some (t.getD ((float_trunc x).map .int))
  | .int n => some (.ok (.int n))
  | .bool b => some (.ok (.int (if b then 1 else 0)))
  | .other _ _ _ _ _ _ t => t

/-- `math_ceil`, mathmodule.c:990-1013. -/
def math_ceil (o : Arg) : Py Ret :=
  match o with
  | .float x => (PyLong_FromDouble (F64.ceil x)).map .int
  | _ =>
    match ceilMethod o with
    | some r => r
    | none => do
      let x ← asDouble o
      (PyLong_FromDouble (F64.ceil x)).map .int

/-- `math_floor`, mathmodule.c:1059-1082. -/
def math_floor (o : Arg) : Py Ret :=
  match o with
  | .float x => (PyLong_FromDouble (F64.floor x)).map .int
  | _ =>
    match floorMethod o with
    | some r => r
    | none => do
      let x ← asDouble o
      (PyLong_FromDouble (F64.floor x)).map .int

/-- `math_trunc`, mathmodule.c:1412-1430. For an exact float, `nb_int` is
`float___trunc___impl` (floatobject.c:1790). -/
def math_trunc (o : Arg) : Py Ret :=
  match o with
  | .float x => (PyLong_FromDouble x).map .int
  | _ =>
    match truncMethod o with
    | some r => r
    | none => .error (.typeError s!"type {o.tpName} doesn't define __trunc__ method")

/-! ## `degrees`, `radians` -/

/-- `Py_MATH_PI` (Include/pymath.h) as a `double`. -/
def piD : F64 := F64.ofBits 0x400921fb54442d18
def c180 : F64 := F64.ofBits 0x4066800000000000

/-- `degToRad` and `radToDeg`, mathmodule.c:2435-2436: constant expressions the compiler
evaluates in `double`. -/
def degToRad : F64 := F64.div piD c180
def radToDeg : F64 := F64.div c180 piD

/-- `math_degrees_impl`, mathmodule.c:2447-2452. -/
def math_degrees (o : Arg) : Py F64 := do return F64.mul (← convDouble o) radToDeg
/-- `math_radians_impl`, mathmodule.c:2464-2469. -/
def math_radians (o : Arg) : Py F64 := do return F64.mul (← convDouble o) degToRad

end PyLean.MathInt
