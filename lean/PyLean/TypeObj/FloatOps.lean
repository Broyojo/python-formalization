import PyLean.TypeObj.Exceptions
import PyLean.Binary64.Dtoa

/-!
`float` in the object model. The arithmetic, comparison, hashing, `repr` and parsing are the
mirrors of `Objects/floatobject.c` in `PyLean.Binary64`; this file carries values between them
and `Val`.

A `float` is an object with an identity, so an exact float is a heap object holding `.boxed
(.float bits)`, as a subclass instance is, and `Val.is` compares addresses. That is what makes
`x = float('nan'); [x] == [x]` true and `[float('nan')] == [float('nan')]` false.

`Binary64.Obj` has a pure `__float__`, which cannot raise or run Python code, so everything that
calls one stays in `Protocol`, on `Rt`.
-/

namespace PyLean.TypeObj

open PyLean.Binary64 (F64)

/-- The double in a `float` or an instance of a subclass. -/
def floatOf (w : World) (v : Val) : Option F64 :=
  match v with
  | .float b => some (F64.ofBits b)
  | _ =>
    match payloadOf w v with
    | some (.boxed (.float b)) => some (F64.ofBits b)
    | _ => none

/-- `PyFloat_FromDouble`: a new object. -/
def mkFloat (x : F64) : M Val := alloc B.float (.boxed (.float x.bits))

/-- The value `Binary64`'s arithmetic looks at, for what `CONVERT_TO_DOUBLE` accepts. -/
def floatObj (w : World) (v : Val) : Binary64.Obj :=
  match floatOf w v, intOf w v with
  | some x, _ => if typeOf w v == B.float then .float x else .floatSub (typeName w v) x
  | _, some i => .int i
  | _, _ => .other (typeName w v) none none

/-- A result of `Binary64`, as a raised exception here. The `~` that marks a message built from
objects in `PyExc` is not part of the text. -/
def pyToM {α : Type} (r : Py α) : M α :=
  let clean (m : String) : String := if m.startsWith "~" then (m.drop 1).toString else m
  match r with
  | .ok a => pure a
  | .error (.valueError m) => valueErr (clean m)
  | .error (.typeError m) => typeErr (clean m)
  | .error (.overflowError m) => overflowErr (clean m)
  | .error (.zeroDivisionError m) => raiseC B.ZeroDivisionError (clean m)
  | .error _ => gap%

/-- A `NotImplemented` or a double. -/
def floatOpt (r : Py (Option F64)) : M Val := do
  match ← pyToM r with
  | some x => mkFloat x
  | none => pure .notImpl

/-- `float_add` to `float_divmod`, `Objects/floatobject.c:551-690`, by slot. -/
def floatBinary (s : Slot) (a b : Val) : M Val := do
  let w ← getW
  let x := floatObj w a
  let y := floatObj w b
  match s with
  | .nb_add => floatOpt (Binary64.float_add x y)
  | .nb_subtract => floatOpt (Binary64.float_sub x y)
  | .nb_multiply => floatOpt (Binary64.float_mul x y)
  | .nb_true_divide => floatOpt (Binary64.float_div x y)
  | .nb_remainder => floatOpt (Binary64.float_rem x y)
  | .nb_floor_divide => floatOpt (Binary64.float_floor_div x y)
  | .nb_divmod =>
    match ← pyToM (Binary64.float_divmod x y) with
    | some (q, r) =>
      let qv ← mkFloat q
      let rv ← mkFloat r
      pure (.tuple [qv, rv])
    | none => pure .notImpl
  | _ => pure .notImpl

/-- The C library's `pow(x, y)`, which `Binary64` takes as a parameter, for an integer `y` of
ordinary size: the true value, correctly rounded. This is an assumption about the library. C does
not require it, and glibc promises less, but the two agree on every case the difftest has tried. A
fractional exponent has no rational value, so it is left out, and `floatPow` reports a gap. -/
def cpowRounded (x y : F64) : Option F64 :=
  if y.isFinite && F64.eq y (F64.floor y) then
    match Binary64.PyLong_FromDouble y with
    | .ok n =>
      if n.natAbs > 4096 then none
      else some (F64.ofRat (if n ≥ 0 then x.toRat ^ n.toNat else (x.toRat ^ n.natAbs)⁻¹))
    | .error _ => none
  else none

/-- `float_pow`, `Objects/floatobject.c:696`, through `floatPowCore`. A case `cpowRounded` leaves
out is a gap, and so is the complex result of a negative base with a fractional exponent. Overflow
is `PyErr_SetFromErrno(PyExc_OverflowError)`, so the exception's args are `errno` and its text. -/
def floatPow (a b c : Val) : M Val := do
  let w ← getW
  if !c.is .none then
    typeErr "pow() 3rd argument not allowed unless all arguments are integers"
  match Binary64.float_pow (fun x y => (cpowRounded x y).getD F64.qnan)
      (floatObj w a) (floatObj w b) none with
  | .error (.overflowError _) =>
    let x ← alloc B.OverflowError
      (.exc { args := [.int 34, .str "Numerical result out of range"] })
    raise (.exc B.OverflowError "" (some x))
  | .error e => pyToM (.error e)
  | .ok none => pure .notImpl
  | .ok (some (.float r)) =>
    -- NaN from the stand-in above, not from the operands.
    let isNan (v : Val) : Bool := match floatOf w v with
      | some x => x.isNaN
      | none => false
    let nanIn := isNan a || isNan b
    if r.isNaN && !nanIn then gap% else mkFloat r
  | .ok (some _) => gap%

/-- `long_true_divide`, `Objects/longobject.c:4504`, whose result is correctly rounded. Zero keeps
the sign of the quotient of the signs (`:4530`), and an infinite result is the `OverflowError`. -/
def longTrueDivide (a b : Int) : M Val := do
  if b == 0 then raiseC B.ZeroDivisionError "division by zero"
  else if a == 0 then mkFloat (F64.zero (b < 0))
  else
    let r := F64.ofRat ((a : Rat) / (b : Rat))
    if r.isInf then overflowErr "integer division result too large for a float"
    else mkFloat r

/-- The text of `float_repr`, `Objects/floatobject.c:348`. -/
def floatReprStr (x : F64) : M String :=
  match Binary64.float_repr x with
  | some cs => pure (String.ofList (cs.map Char.ofNat))
  | none => gap%

end PyLean.TypeObj
