import PyLean.MathInt.FltFns
import PyLean.MathInt.FltGamma
import PyLean.Binary64.Complex

/-!
# `Modules/cmathmodule.c`: the error glue, `phase`, `polar`, `rect`, the predicates, `isclose`,
the `-i f(iz)` wrappers and `log`

CPython 3.15.2. Complex numbers are `Py_complex` (`Binary64.C`, two `F64`). The C library is a
parameter: `atan2` (a result and the `errno` it leaves), `cos`/`sin` for `rect` (whose `errno`
`rect` overwrites), and `hypot` through `_Py_c_abs` (`Binary64.Libm`). The functions computed by
the C99 Annex G code of this file (`c_log`, `cmath_cosh_impl`, `cmath_sinh_impl`,
`cmath_tanh_impl`, `cmath_asinh_impl`, `cmath_atanh_impl`) are parameters too, each a result and
the `errno` it leaves: the wrappers below are mirrored on top of them.

The argument conversions (`PyComplex_AsCComplex`, the `double` converter) belong to the clinic
glue and are outside the `_impl` functions; a conversion inside an `_impl` (the base of `log`)
is an argument of type `Py C`.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64

/-! ## `special_type`, cmathmodule.c:105-140 -/

inductive ST where
  | ninf | neg | nzero | pzero | pos | pinf | nan
  deriving DecidableEq, Repr

/-- The row or column index of `special_types` (:105-113). -/
def ST.idx : ST → Nat
  | .ninf => 0 | .neg => 1 | .nzero => 2 | .pzero => 3 | .pos => 4 | .pinf => 5 | .nan => 6

/-- `special_type`, cmathmodule.c:117-140. `d != 0` is `!isZeroC d`. -/
def special_type (d : F64) : ST :=
  if d.isFinite then
    if !isZeroC d then
      if F64.eq (F64.copysign c1 d) c1 then .pos else .neg
    else if F64.eq (F64.copysign c1 d) c1 then .pzero else .nzero
  else if d.isNaN then .nan
  else if F64.eq (F64.copysign c1 d) c1 then .pinf else .ninf

/-- `U`, cmathmodule.c:153: the placeholder `-9.5426319407711027e33` of entries never used. -/
def cU : F64 := F64.neg (F64.ofInt (95426319407711027 * 10 ^ 17))

/-- A 7x7 table entry. -/
def tableAt (t : List (List C)) (a b : ST) : C := (t.getD a.idx []).getD b.idx ⟨cU, cU⟩

/-! ## The return conversion and `math_error` -/

/-- The `Py_complex_protected` return converter, cmathmodule.c:36-46 (generated at
clinic/cmathmodule.c.h:37-47): `EDOM` is `ValueError`, `ERANGE` is `OverflowError`, any other
value (`0` included) returns the result. -/
def protectedRet (r : C) (e : Errno) : Py C :=
  if e == .edom then .error (.valueError "math domain error")
  else if e == .erange then .error (.overflowError "math range error")
  else .ok r

/-- The `errno` as an integer, for `PyErr_SetFromErrno`. -/
def Errno.num : Errno → Nat
  | .zero => 0 | .edom => 33 | .erange => 34 | .other n => n

/-- `math_error`, cmathmodule.c:979-989. -/
def cmath_math_error (e : Errno) : PyExc :=
  if e == .edom then .valueError "math domain error"
  else if e == .erange then .overflowError "math range error"
  else .valueError s!"~[Errno {e.num}]"

/-! ## `phase`, `polar` -/

/-- `cmath_phase_impl`, cmathmodule.c:1001-1013: `errno = 0`, then `atan2`. -/
def cmath_phase (atan2 : CFun2) (z : C) : Py F64 :=
  let (phi, e) := atan2 z.im z.re
  if e != .zero then .error (cmath_math_error e) else .ok phi

/-- `cmath_polar_impl`, cmathmodule.c:1026-1039: `atan2` first, then `errno = 0` (3.15 moved it
after `atan2`, so `atan2`'s `errno` is discarded), then `_Py_c_abs`, which leaves `ERANGE` or
`0` (its NaN path leaves `errno` alone, here `0`). -/
def cmath_polar (atan2 : CFun2) (m : Libm) (z : C) : Py (F64 × F64) :=
  let phi := (atan2 z.im z.re).1
  let (r, erange) := _Py_c_abs m false z
  if erange then .error (cmath_math_error .erange) else .ok (r, phi)

/-! ## `rect`, cmathmodule.c:1041-1123 -/

def cN : F64 := F64.qnan
def cNInf : F64 := F64.inf true
def cNZ : F64 := F64.zero true

/-- `rect_special_values`, cmathmodule.c:1050-1058. -/
def rect_special_values : List (List C) := [
  [⟨cInf, cN⟩, ⟨cU, cU⟩, ⟨cNInf, c0⟩, ⟨cNInf, cNZ⟩, ⟨cU, cU⟩, ⟨cInf, cN⟩, ⟨cInf, cN⟩],
  [⟨cN, cN⟩, ⟨cU, cU⟩, ⟨cU, cU⟩, ⟨cU, cU⟩, ⟨cU, cU⟩, ⟨cN, cN⟩, ⟨cN, cN⟩],
  [⟨c0, c0⟩, ⟨cU, cU⟩, ⟨cNZ, c0⟩, ⟨cNZ, cNZ⟩, ⟨cU, cU⟩, ⟨c0, c0⟩, ⟨c0, c0⟩],
  [⟨c0, c0⟩, ⟨cU, cU⟩, ⟨c0, cNZ⟩, ⟨c0, c0⟩, ⟨cU, cU⟩, ⟨c0, c0⟩, ⟨c0, c0⟩],
  [⟨cN, cN⟩, ⟨cU, cU⟩, ⟨cU, cU⟩, ⟨cU, cU⟩, ⟨cU, cU⟩, ⟨cN, cN⟩, ⟨cN, cN⟩],
  [⟨cInf, cN⟩, ⟨cU, cU⟩, ⟨cInf, cNZ⟩, ⟨cInf, c0⟩, ⟨cU, cU⟩, ⟨cInf, cN⟩, ⟨cInf, cN⟩],
  [⟨cN, cN⟩, ⟨cN, cN⟩, ⟨cN, c0⟩, ⟨cN, c0⟩, ⟨cN, cN⟩, ⟨cN, cN⟩, ⟨cN, cN⟩]]

/-- The C `cos` and `sin` `rect` calls; their `errno` is overwritten (:1090-1093, :1100, :1105). -/
structure RectLibm where
  cos : F64 → F64
  sin : F64 → F64

/-- `cmath_rect_impl`, cmathmodule.c:1072-1123. -/
def cmath_rect (L : RectLibm) (r phi : F64) : Py C :=
  if !r.isFinite || !phi.isFinite then
    let z : C :=
      if r.isInf && (phi.isFinite && !isZeroC phi) then
        if F64.lt c0 r then ⟨F64.copysign cInf (L.cos phi), F64.copysign cInf (L.sin phi)⟩
        else ⟨F64.neg (F64.copysign cInf (L.cos phi)), F64.neg (F64.copysign cInf (L.sin phi))⟩
      else tableAt rect_special_values (special_type r) (special_type phi)
    let e : Errno := if !isZeroC r && !r.isNaN && phi.isInf then .edom else .zero
    if e != .zero then .error (cmath_math_error e) else .ok z
  else if isZeroC phi then .ok ⟨r, F64.mul r phi⟩
  else .ok ⟨F64.mul r (L.cos phi), F64.mul r (L.sin phi)⟩

/-! ## Predicates, cmathmodule.c:1132-1163 -/

def cmath_isfinite (z : C) : Bool := z.re.isFinite && z.im.isFinite
def cmath_isnan (z : C) : Bool := z.re.isNaN || z.im.isNaN
def cmath_isinf (z : C) : Bool := z.re.isInf || z.im.isInf

/-! ## `isclose`, cmathmodule.c:1190-1231 -/

/-- `cmath_isclose_impl`. `_Py_c_abs`'s `errno` is not looked at. -/
def cmath_isclose (m : Libm) (a b : C) (rel_tol abs_tol : F64) : Py Bool :=
  if F64.lt rel_tol c0 || F64.lt abs_tol c0 then
    .error (.valueError "tolerances must be non-negative")
  else if F64.eq a.re b.re && F64.eq a.im b.im then .ok true
  else if a.re.isInf || a.im.isInf || b.re.isInf || b.im.isInf then .ok false
  else
    let diff := (_Py_c_abs m false (_Py_c_diff a b)).1
    .ok ((F64.le diff (F64.mul rel_tol (_Py_c_abs m false b).1) ||
      F64.le diff (F64.mul rel_tol (_Py_c_abs m false a).1)) || F64.le diff abs_tol)

/-! ## The `-i f(iz)` wrappers and `log` -/

/-- A function of this file computed by C99 Annex G code: the result and `errno`. -/
abbrev CImpl := C → C × Errno

/-- The functions the wrappers call: `cmath_cosh_impl`, `cmath_sinh_impl`, `cmath_tanh_impl`,
`cmath_asinh_impl`, `cmath_atanh_impl`, `c_log`. -/
structure CmathCore where
  cosh : CImpl
  sinh : CImpl
  tanh : CImpl
  asinh : CImpl
  atanh : CImpl
  clog : CImpl

/-- `iz`: `r.real = -z.imag; r.imag = z.real`. -/
def mulI (z : C) : C := ⟨F64.neg z.im, z.re⟩

/-- `-i s`: `r.real = s.imag; r.imag = -s.real`. -/
def mulNegI (s : C) : C := ⟨s.im, F64.neg s.re⟩

/-- `cmath_cos_impl`, cmathmodule.c:411-421: `cos(z) = cosh(iz)`. -/
def cmath_cos_impl (K : CmathCore) (z : C) : C × Errno := K.cosh (mulI z)
/-- `cmath_sin_impl`, cmathmodule.c:670-682: `sin(z) = -i sinh(iz)`. -/
def cmath_sin_impl (K : CmathCore) (z : C) : C × Errno :=
  let (s, e) := K.sinh (mulI z); (mulNegI s, e)
/-- `cmath_tan_impl`, cmathmodule.c:844-856: `tan(z) = -i tanh(iz)`. -/
def cmath_tan_impl (K : CmathCore) (z : C) : C × Errno :=
  let (s, e) := K.tanh (mulI z); (mulNegI s, e)
/-- `cmath_asin_impl`, cmathmodule.c:260-272: `asin(z) = -i asinh(iz)`. -/
def cmath_asin_impl (K : CmathCore) (z : C) : C × Errno :=
  let (s, e) := K.asinh (mulI z); (mulNegI s, e)
/-- `cmath_atan_impl`, cmathmodule.c:329-341: `atan(z) = -i atanh(iz)`. -/
def cmath_atan_impl (K : CmathCore) (z : C) : C × Errno :=
  let (s, e) := K.atanh (mulI z); (mulNegI s, e)

/-- `M_LN10`, cmathmodule.c:60. -/
def cLN10 : F64 := decLit 2302585092994045684 18

/-- `cmath_log10_impl`, cmathmodule.c:648-661: the divisions keep `errno`. -/
def cmath_log10_impl (K : CmathCore) (z : C) : C × Errno :=
  let (r, e) := K.clog z
  (⟨F64.div r.re cLN10, F64.div r.im cLN10⟩, e)

/-- The Python-visible function of a `Py_complex_protected` `_impl` (`errno = 0` before the
call is the converter's `modify`, :28-29). -/
def protectedCall (f : C → C × Errno) (z : C) : Py C := protectedRet (f z).1 (f z).2

/-- `cmath_log_impl`, cmathmodule.c:955-974. `y` is `none` without a base, or the result of
`PyComplex_AsCComplex(y_obj)`. `c_log` writes `errno` on every path (:605 through
`SPECIAL_VALUE`, :621, :636), so the second call replaces what the first left; `_Py_c_quot`
writes `EDOM` only on a zero divisor (complexobject.c:182, :201). -/
def cmath_log (K : CmathCore) (x : C) (y : Option (Py C)) : Py C := do
  let (lx, e1) := K.clog x
  match y with
  | none => if e1 != .zero then .error (cmath_math_error e1) else .ok lx
  | some yc =>
    let yv ← yc
    let (ly, e2) := K.clog yv
    let (q, zdiv) := _Py_c_quot lx ly
    let e := if zdiv then Errno.edom else e2
    if e != .zero then .error (cmath_math_error e) else .ok q

/-! ## `cmath_exec`, cmathmodule.c:1264-1294 -/

/-- `Py_MATH_PI`, Include/pymath.h:15. -/
def cPi : F64 := decLit 314159265358979323846 20
/-- `Py_MATH_E`, Include/pymath.h:24. -/
def cE : F64 := decLit 27182818284590452354 19
/-- `Py_MATH_TAU`, Include/pymath.h:29, a `long double` literal rounded to `double`. -/
def cTau : F64 := decLit 62831853071795864769252867665590057683943 40

/-- The attributes `cmath_exec` adds, in order: `pi`, `e`, `tau`, `inf` (floats), `infj`
(complex), `nan` (`fabs(Py_NAN)`), `nanj` (complex). -/
def cmath_exec_consts : F64 × F64 × F64 × F64 × C × F64 × C :=
  (cPi, cE, cTau, cInf, ⟨c0, cInf⟩, F64.abs F64.qnan, ⟨c0, F64.abs F64.qnan⟩)

end PyLean.MathInt
