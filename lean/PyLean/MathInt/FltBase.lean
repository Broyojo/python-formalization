import PyLean.Binary64.Float
import PyLean.Binary64.Dtoa

/-!
# `Modules/mathmodule.c`: arguments, `errno` and the libm wrappers

CPython 3.15.2. Floats are the exact binary64 model `F64`.

The C library is split in two, as the C standard splits it:

* Functions whose result IEEE 754 and C99 Annex F pin exactly (`fabs`, `copysign`,
  `floor`, `ceil`, `round`, `fmod`, `frexp`, `ldexp`, `modf`, `sqrt`, `fma`,
  `nextafter`) are the exact `F64` operations. This is the one assumption about the
  platform: those functions are IEEE-conforming, as glibc's are.
* Transcendental functions (`sin`, `exp`, `log`, `pow`, ...) are parameters of type
  `CFun1`/`CFun2`: a result and the `errno` the call leaves. Every property states
  what it assumes about them.

Arguments are Python objects (`Arg`) with fallible `__float__` and `__index__`, so the
conversion failures of `PyFloat_AsDouble` (floatobject.c:247-303) are part of every
function that converts. Scope limit: strict subclasses of `int` other than `bool`
are not modelled.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64

/-! ## Objects -/

/-- An object a user-defined dunder returns, by what the caller checks about it. -/
inductive Ret where
  /-- an exact `float` -/
  | float (x : F64)
  /-- an instance of a strict subclass of `float`; `fq` is what `%T` prints -/
  | floatSub (fq : String) (x : F64)
  /-- an exact `int` -/
  | int (n : Int)
  /-- an instance of a strict subclass of `int` (`bool`, say) -/
  | intSub (fq : String) (n : Int)
  /-- anything else -/
  | other (fq : String)
  deriving Repr, DecidableEq, Inhabited

/-- What `%T` prints for a returned object. -/
def Ret.fq : Ret → String
  | .float _ => "float"
  | .floatSub t _ => t
  | .int _ => "int"
  | .intSub t _ => t
  | .other t => t

/-- An argument. A dunder is `none` when the type does not define it; when it is
defined, calling it either raises or returns a `Ret`. -/
inductive Arg where
  /-- an exact `float` -/
  | float (x : F64)
  /-- a strict subclass of `float`, with its own `__floor__`, `__ceil__`, `__trunc__` when
  it overrides them (`none`: inherited from `float`) -/
  | floatSub (fq : String) (x : F64) (floor ceil trunc : Option (Py Ret))
  /-- an exact `int` -/
  | int (n : Int)
  /-- `True` or `False` -/
  | bool (b : Bool)
  /-- any other type: `tp_name`, the qualified name `%T` prints, and its dunders -/
  | other (ty fq : String) (dfloat dindex floor ceil trunc : Option (Py Ret))
  deriving Inhabited

def Arg.fq : Arg → String
  | .float _ => "float"
  | .floatSub t .. => t
  | .int _ => "int"
  | .bool _ => "bool"
  | .other _ t .. => t

def Arg.tpName : Arg → String
  | .other t .. => t
  | o => o.fq

/-- `PyLong_Check`. -/
def Arg.longCheck : Arg → Bool
  | .int _ | .bool _ => true
  | _ => false

/-- `PyLong_CheckExact`. -/
def Arg.longCheckExact : Arg → Bool
  | .int _ => true
  | _ => false

/-- `PyFloat_CheckExact`. -/
def Arg.floatCheckExact : Arg → Bool
  | .float _ => true
  | _ => false

/-- The value of an `int` (or `bool`) argument. -/
def Arg.intVal : Arg → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | _ => none

/-- `_PyIndex_Check`: the type defines `nb_index`. -/
def Arg.indexCheck : Arg → Bool
  | .int _ | .bool _ => true
  | .other _ _ _ di .. => di.isSome
  | _ => false

/-! ## Conversions -/

/-- `_PyNumber_Index`, abstract.c:1410-1449. A strict `int` subclass result only warns. -/
def _PyNumber_Index (o : Arg) : Py Int :=
  match o.intVal with
  | some n => .ok n
  | none =>
    match o with
    | .other _ fq _ (some call) .. => do
      match ← call with
      | .int n => .ok n
      | .intSub _ n => .ok n
      | r => .error (.typeError s!"{fq}.__index__() must return an int, not {r.fq}")
    | _ => .error (.typeError s!"'{o.tpName}' object cannot be interpreted as an integer")

/-- The longest prefix of `cs` whose UTF-8 encoding fits in `n` bytes. -/
def takeUtf8B : Nat → List Char → List Char
  | _, [] => []
  | n, c :: cs => if c.utf8Size ≤ n then c :: takeUtf8B (n - c.utf8Size) cs else []

/-- `'%.<n>s'` of a `tp_name` in `PyErr_Format` (Objects/unicodeobject.c:2623-2661): the longest
prefix of whole characters whose UTF-8 fits in `n` bytes (`tp_name` has no NUL or surrogate). -/
def tpNameCut (n : Nat) (ty : String) : String := String.ofList (takeUtf8B n ty.toList)

/-- `PyFloat_AsDouble`, floatobject.c:247-303. A `float` (or subclass) gives its value
(:258-260); `int` and `bool` reach `long_float`, which is `PyLong_AsDouble`; a type with
`__index__` but no `__float__` goes through `_PyNumber_Index` (:263-271); otherwise
`__float__` is called and must return a float (:278-298; a strict subclass only warns). -/
def asDouble (o : Arg) : Py F64 :=
  match o with
  | .float x | .floatSub _ x .. => .ok x
  | .int n => PyLong_AsDouble n
  | .bool b => PyLong_AsDouble (if b then 1 else 0)
  | .other ty fq none di .. =>
    match di with
    | some _ => do PyLong_AsDouble (← _PyNumber_Index o)
    | none => .error (.typeError s!"must be real number, not {tpNameCut 50 ty}")
  | .other _ fq (some call) .. => do
    match ← call with
    | .float x | .floatSub _ x => .ok x
    | r => .error (.typeError s!"{fq}.__float__() must return a float, not {r.fq}")

/-- The `double` converter of Argument Clinic (clinic/mathmodule.c.h, e.g. :157-166):
`PyFloat_AS_DOUBLE` for an exact float, else `PyFloat_AsDouble`. -/
def convDouble (o : Arg) : Py F64 :=
  match o with
  | .float x => .ok x
  | _ => asDouble o

/-- `ASSIGN_DOUBLE`, mathmodule.c:205-220: exact float, exact int (`PyLong_AsDouble`), or
`PyFloat_AsDouble`. -/
def assignDouble (o : Arg) : Py F64 :=
  match o with
  | .float x => .ok x
  | .int n => PyLong_AsDouble n
  | _ => asDouble o

/-- `_PyArg_CheckPositional(name, nargs, min, max)`, Python/getargs.c, for the arity
errors of `METH_FASTCALL` functions. -/
def checkPositional (name : String) (nargs min max : Nat) : Py Unit :=
  let plural (n : Nat) := if n == 1 then "" else "s"
  if nargs < min then
    .error (.typeError s!"{name} expected {if min == max then "" else "at least "}{min} argument{plural min}, got {nargs}")
  else if max < nargs then
    .error (.typeError s!"{name} expected {if min == max then "" else "at most "}{max} argument{plural max}, got {nargs}")
  else .ok ()

/-! ## `errno` and the C library -/

/-- `errno` after a call. `other` is any value but `EDOM` and `ERANGE`. -/
inductive Errno where
  | zero
  | edom
  | erange
  | other (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A one-argument C library function: the result and the `errno` it leaves when
`errno` was `0` before the call. -/
abbrev CFun1 := F64 → F64 × Errno

/-- A two-argument C library function. -/
abbrev CFun2 := F64 → F64 → F64 × Errno

/-- Write `errno` the way a C library call does: only a nonzero value is stored. -/
def Errno.after (before now : Errno) : Errno := if now == .zero then before else now

/-! ## Constants -/

def c0 : F64 := F64.zero false
def c1 : F64 := F64.one
def c2 : F64 := F64.ofBits 0x4000000000000000
def cHalf : F64 := F64.ofBits 0x3fe0000000000000
def c1p5 : F64 := F64.ofBits 0x3ff8000000000000
/-- `Py_NAN`: a quiet NaN (its sign is not part of the model). -/
def cNaN : F64 := F64.qnan
/-- `INFINITY`. -/
def cInf : F64 := F64.inf false

/-- `x == 0.0` in C. -/
def isZeroC (x : F64) : Bool := F64.eq x c0

/-- `PyOS_double_to_string(x, 'r', 0, Py_DTSF_ADD_DOT_0, NULL)`, as text. -/
def reprF (x : F64) : String :=
  match float_repr x with
  | some s => String.ofList (s.map Char.ofNat)
  | none => "?"

/-- `PyErr_Format(PyExc_ValueError, err_msg, buf)` for an `err_msg` ending in `%s`:
`err_msg` is stored without its `%s`. -/
def domainMsg (errMsg : String) (x : F64) : PyExc := .valueError (errMsg ++ reprF x)

/-! ## `is_error`, mathmodule.c:714-755 -/

/-- What `is_error` does: return `0` (`ok`), or return `1` having set an exception
(`raise e`), or return `1` without one (`silent`, only for `EDOM` when `raise_edom` is
false). -/
inductive IsErr where
  | ok
  | raise (e : PyExc)
  | silent
  deriving Repr, DecidableEq

/-- `is_error(x, raise_edom)`, mathmodule.c:714-755, called with a nonzero `errno`. -/
def is_error (x : F64) (errno : Errno) (raiseEdom : Bool) : IsErr :=
  match errno with
  | .edom => if raiseEdom then .raise (.valueError "math domain error") else .silent
  | .erange =>
    if F64.lt (F64.abs x) c1p5 then .ok
    else .raise (.overflowError "math range error")
  | .zero => .ok
  | .other n => .raise (.valueError s!"~[Errno {n}]")

/-! ## `math_1`, `math_1a`, `math_2` -/

/-- The `domain_err:` label of `math_1`, mathmodule.c:813-824. -/
def math_1_domainErr (x : F64) (errMsg : Option String) : PyExc :=
  match errMsg with
  | some m => domainMsg m x
  | none => .valueError "math domain error"

/-- `math_1`, mathmodule.c:787-825. `errMsg` is `err_msg` without its trailing `%s`. -/
def math_1 (arg : Arg) (func : CFun1) (canOverflow : Bool) (errMsg : Option String) : Py F64 := do
  let x ← asDouble arg
  let (r, errno) := func x
  if r.isNaN && !x.isNaN then
    .error (math_1_domainErr x errMsg)
  else if r.isInf && x.isFinite then
    if canOverflow then .error (.overflowError "math range error")
    else .error (math_1_domainErr x errMsg)
  else if r.isFinite && errno != .zero then
    match is_error r errno true with
    | .ok => .ok r
    | .raise e => .error e
    | .silent => .error (.valueError "math domain error")  -- unreachable: raise_edom is 1
  else .ok r

/-- `math_1a`, mathmodule.c:831-852. -/
def math_1a (arg : Arg) (func : CFun1) (errMsg : Option String) : Py F64 := do
  let x ← asDouble arg
  let (r, errno) := func x
  if errno != .zero then
    match is_error r errno errMsg.isNone with
    | .ok => .ok r
    | .raise e => .error e
    | .silent =>
      -- `err_msg && errno == EDOM`, :841-848
      match errMsg with
      | some m => .error (domainMsg m x)
      | none => .error (.valueError "math domain error")  -- unreachable
  else .ok r

/-- `math_2`, mathmodule.c:881-914. -/
def math_2 (args : List Arg) (func : CFun2) (funcname : String) : Py F64 := do
  checkPositional funcname args.length 2 2
  let x ← asDouble (args.getD 0 default)
  let y ← asDouble (args.getD 1 default)
  let (r, errno0) := func x y
  let errno :=
    if r.isNaN then (if !x.isNaN && !y.isNaN then Errno.edom else .zero)
    else if r.isInf then (if x.isFinite && y.isFinite then .erange else .zero)
    else errno0
  if errno != .zero then
    match is_error r errno true with
    | .ok => .ok r
    | .raise e => .error e
    | .silent => .error (.valueError "math domain error")  -- unreachable
  else .ok r

end PyLean.MathInt
