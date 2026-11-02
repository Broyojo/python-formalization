import PyLean.DiffCore
import PyLean.MathInt.FltFns
import PyLean.MathInt.FltLog
import PyLean.MathInt.FltGamma
import PyLean.MathInt.FltSum

/-!
Differential-testing handler for the `Modules/mathmodule.c` cases of `"mod": "mathint"`.

The transcendental C library functions, which every property takes as parameters, are
instantiated here with the platform's own (Lean's `Float` calls the C library). `errno` is
reconstructed the way glibc sets it: `EDOM` for a NaN from a non-NaN argument, `ERANGE` for
an infinity from finite arguments and for a subnormal result (an exact zero, such as
`log(1.0)`, leaves `errno` alone). Nothing but
the difftest uses these instances.
-/

namespace PyLean.MathInt

open Lean PyLean PyLean.Diff PyLean.Binary64

def toFloat (x : F64) : Float := Float.ofBits x.bits.toUInt64
def ofFloat (f : Float) : F64 := F64.ofBits f.toBits.toNat

/-- The `errno` glibc leaves for result `r` of arguments `xs`. -/
def glibcErrno (xs : List F64) (r : F64) : Errno :=
  if r.isNaN && xs.all (fun x => !x.isNaN) then .edom
  else if r.isInf && xs.all (·.isFinite) then .erange
  else if r.isFinite && r.bexp == 0 && !r.isZero && xs.all (fun x => x.isFinite && !x.isZero) then .erange
  else .zero

def platform1 (f : Float → Float) : CFun1 := fun x =>
  let r := ofFloat (f (toFloat x))
  (r, glibcErrno [x] r)

def platform2 (f : Float → Float → Float) : CFun2 := fun x y =>
  let r := ofFloat (f (toFloat x) (toFloat y))
  (r, glibcErrno [x, y] r)

def platformGamma : GammaLibm where
  sin := platform1 Float.sin
  cos := platform1 Float.cos
  exp := platform1 Float.exp
  log := platform1 Float.log
  pow := platform2 Float.pow

/-- The `FUNC1`/`FUNC1D` table, mathmodule.c:946-1171: C function, `can_overflow`, `err_msg`. -/
def func1Table : String → Option (CFun1 × Bool × Option String)
  | "acos" => some (platform1 Float.acos, false, some "expected a number in range from -1 up to 1, got ")
  | "acosh" => some (platform1 Float.acosh, false, some "expected argument value not less than 1, got ")
  | "asin" => some (platform1 Float.asin, false, some "expected a number in range from -1 up to 1, got ")
  | "asinh" => some (platform1 Float.asinh, false, none)
  | "atan" => some (platform1 Float.atan, false, none)
  | "atanh" => some (platform1 Float.atanh, false, some "expected a number between -1 and 1, got ")
  | "cbrt" => some (platform1 Float.cbrt, false, none)
  | "cos" => some (platform1 Float.cos, false, some "expected a finite input, got ")
  | "cosh" => some (platform1 Float.cosh, true, none)
  | "exp" => some (platform1 Float.exp, true, none)
  | "exp2" => some (platform1 Float.exp2, true, none)
  | "fabs" => some (fun x => (F64.abs x, .zero), false, none)
  | "sin" => some (platform1 Float.sin, false, some "expected a finite input, got ")
  | "sinh" => some (platform1 Float.sinh, true, none)
  | "sqrt" => some (fun x => let r := F64.sqrt x; (r, glibcErrno [x] r), false,
      some "expected a nonnegative input, got ")
  | "tan" => some (platform1 Float.tan, false, some "expected a finite input, got ")
  | "tanh" => some (platform1 Float.tanh, false, none)
  | _ => none

/-! ## Decoding objects -/

/-- An exception a user-defined dunder raises, with the built-in classes the model tests
for by constructor. -/
def getExcF (j : Json) : Except String PyExc := do
  let msg ← getStr j "msg"
  match ← getStr j "exc" with
  | "ValueError" => return .valueError msg
  | "TypeError" => return .typeError msg
  | "OverflowError" => return .overflowError msg
  | "ZeroDivisionError" => return .zeroDivisionError msg
  | cls => return .named cls msg

def getRet (j : Json) : Except String Ret := do
  match j.getObjVal? "f", j.getObjVal? "fs", j.getObjVal? "i", j.getObjVal? "is", j.getObjVal? "o" with
  | .ok v, _, _, _, _ => return .float (F64.ofBits (← v.getNat?))
  | _, .ok v, _, _, _ => return .floatSub (← getStr j "fq") (F64.ofBits (← v.getNat?))
  | _, _, .ok v, _, _ => return .int (← v.getInt?)
  | _, _, _, .ok v, _ => return .intSub (← getStr j "fq") (← v.getInt?)
  | _, _, _, _, .ok v => return .other (← v.getStr?)
  | _, _, _, _, _ => throw "bad return value"

/-- An optional dunder: absent, raising (`{"raise": exc}`) or returning (`{"ret": v}`). -/
def getDunder (j : Json) (key : String) : Except String (Option (Py Ret)) := do
  match j.getObjVal? key with
  | .error _ => return none
  | .ok d =>
    match d.getObjVal? "raise" with
    | .ok e => return some (.error (← getExcF e))
    | .error _ => return some (.ok (← getRet (← field d "ret")))

def getArg (j : Json) : Except String Arg := do
  match j.getObjVal? "f", j.getObjVal? "fs", j.getObjVal? "i", j.getObjVal? "b", j.getObjVal? "o" with
  | .ok v, _, _, _, _ => return .float (F64.ofBits (← v.getNat?))
  | _, .ok v, _, _, _ =>
    return .floatSub (← getStr j "fq") (F64.ofBits (← v.getNat?)) (← getDunder j "floor")
      (← getDunder j "ceil") (← getDunder j "trunc")
  | _, _, .ok v, _, _ => return .int (← v.getInt?)
  | _, _, _, .ok v, _ => return .bool (← v.getBool?)
  | _, _, _, _, .ok v =>
    return .other (← v.getStr?) (← getStr j "fq") (← getDunder j "float") (← getDunder j "index")
      (← getDunder j "floor") (← getDunder j "ceil") (← getDunder j "trunc")
  | _, _, _, _, _ => throw "bad argument"

def getArgF (j : Json) (key : String) : Except String Arg := do getArg (← field j key)

def getArgs (j : Json) (key : String) : Except String (List Arg) := do
  let a ← (← field j key).getArr?
  a.toList.mapM getArg

def getIt (j : Json) (key : String) : Except String It := do
  let o ← field j key
  let items ← (← field o "items").getArr?
  let items ← items.toList.mapM getArg
  match o.getObjVal? "err" with
  | .ok e => return { items, err := some (← getExcF e) }
  | .error _ => return { items }

def getOptArg (j : Json) (key : String) : Except String (Option Arg) :=
  match j.getObjVal? key with
  | .ok v => do return some (← getArg v)
  | .error _ => return none

/-! ## Encoding results -/

def encFl (x : F64) : Json := if x.isNaN then Json.str "nan" else toJson x.bits

def encRet : Ret → Json
  | .float x => Json.mkObj [("f", encFl x)]
  | .floatSub t x => Json.mkObj [("fs", encFl x), ("fq", toJson t)]
  | .int n => Json.mkObj [("i", toJson n)]
  | .intSub t n => Json.mkObj [("is", toJson n), ("fq", toJson t)]
  | .other t => Json.mkObj [("o", toJson t)]

def encFlPair (p : F64 × F64) : Json := Json.arr #[encFl p.1, encFl p.2]
def encFrexp (p : F64 × Int) : Json := Json.arr #[encFl p.1, toJson p.2]

def runFlt (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "frexp" => return encPy encFrexp (math_frexp (← getArgF j "x"))
  | "ldexp" => return encPy encFl (math_ldexp (← getArgF j "x") (← getArgF j "i"))
  | "modf" => return encPy encFlPair (math_modf (← getArgF j "x"))
  | "fmod" => return encPy encFl (math_fmod (← getArgF j "x") (← getArgF j "y"))
  | "remainder" => return encPy encFl (math_remainder (← getArgs j "args"))
  | "copysign" => return encPy encFl (math_copysign (← getArgs j "args"))
  | "atan2" => return encPy encFl (math_2 (← getArgs j "args") (platform2 Float.atan2) "atan2")
  | "fma" => return encPy encFl (math_fma (← getArgF j "x") (← getArgF j "y") (← getArgF j "z"))
  | "pow" => return encPy encFl (math_pow (platform2 Float.pow) (← getArgF j "x") (← getArgF j "y"))
  | "isclose" =>
    return encPy toJson (math_isclose (← getArgF j "a") (← getArgF j "b") (← getOptArg j "rel_tol")
      (← getOptArg j "abs_tol"))
  | "isfinite" => return encPy toJson (math_isfinite (← getArgF j "x"))
  | "isnan" => return encPy toJson (math_isnan (← getArgF j "x"))
  | "isinf" => return encPy toJson (math_isinf (← getArgF j "x"))
  | "isnormal" => return encPy toJson (math_isnormal (← getArgF j "x"))
  | "issubnormal" => return encPy toJson (math_issubnormal (← getArgF j "x"))
  | "signbit" => return encPy toJson (math_signbit (← getArgF j "x"))
  | "nextafter" =>
    return encPy encFl (math_nextafter (← getArgF j "x") (← getArgF j "y") (← getOptArg j "steps"))
  | "ulp" => return encPy encFl (math_ulp (← getArgF j "x"))
  | "floor" => return encPy encRet (math_floor (← getArgF j "x"))
  | "ceil" => return encPy encRet (math_ceil (← getArgF j "x"))
  | "trunc" => return encPy encRet (math_trunc (← getArgF j "x"))
  | "degrees" => return encPy encFl (math_degrees (← getArgF j "x"))
  | "radians" => return encPy encFl (math_radians (← getArgF j "x"))
  | "log" => return encPy encFl (math_log (platform1 Float.log) (← getArgs j "args"))
  | "log2" => return encPy encFl (math_log2 (platform1 Float.log2) (← getArgF j "x"))
  | "log10" => return encPy encFl (math_log10 (platform1 Float.log10) (← getArgF j "x"))
  | "gamma" => return encPy encFl (math_gamma platformGamma (← getArgF j "x"))
  | "lgamma" => return encPy encFl (math_lgamma platformGamma (← getArgF j "x"))
  | "fsum" => return encPy encFl (math_fsum (← getIt j "it"))
  | "hypot" => return encPy encFl (math_hypot (← getArgs j "args"))
  | "dist" => return encPy encFl (math_dist (← getIt j "p") (← getIt j "q"))
  | "prod" =>
    return encPy encRet (math_prod (← getIt j "it") (← getOptArg j "start"))
  | f =>
    match func1Table f with
    | some (func, canOv, msg) => return encPy encFl (math_1 (← getArgF j "x") func canOv msg)
    | none => throw s!"unknown fn {f}"

end PyLean.MathInt
