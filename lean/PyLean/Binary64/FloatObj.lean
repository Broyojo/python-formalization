import PyLean.Binary64.FloatPow

/-!
The object-level paths of `Objects/floatobject.c` (CPython 3.15.2): `PyFloat_AsDouble`,
`PyFloat_FromString`, the constructors (`float_new_impl`, `float_subtype_new`,
`float_vectorcall`, `float_from_number_impl`), the identity methods (`float_float`,
`conjugate`, `real`), `__getnewargs__`, `float.fromhex` at the object level and
`round(x, ndigits)` with its `PyNumber_AsSsize_t`.

An object is `FObj`: what the C type checks see, its two number slots as the results that
calling them gives (an exception included, so a `__float__` that raises is
`some (.error e)`), and an identity `id`. A result says whether it is the argument itself,
an object a slot or a class call returned, or a new float: object identity is part of the
result, never `=` on values.

Scope: classes are modelled by identity, a metaclass overriding `__eq__`, `__hash__` or
`__repr__` is out of scope, and `tp_alloc` and `PyFloat_FromDouble` do not fail (their
`MemoryError` is allocator plumbing). A `DeprecationWarning` that the warnings filter does
not turn into an error has no effect on the result; `warnErr` says whether it does.
-/

namespace PyLean.Binary64

open PyLean F64

/-! ## Objects -/

/-- What the type checks of the float code see: `PyFloat_Check`, `PyLong_Check`,
`PyUnicode_Check`, `PyBytes_Check`, `PyByteArray_Check`, the buffer protocol, or none. -/
inductive FKind where
  | float (x : F64)
  | int (n : Int)
  | str (cps : List Nat)
  | bytes (b : List Nat)
  | bytearray (b : List Nat)
  | buffer (b : List Nat)
  | plain
  deriving Inhabited

/-- An object: its identity, kind, whether its type is exactly the base type of the kind
(`PyFloat_CheckExact` and friends), its `tp_name`, its fully qualified name (what `%T`
prints), and what its `nb_float` and `nb_index` slots return when called (`none`: the slot
is NULL). -/
inductive FObj where
  | mk (id : Nat) (kind : FKind) (exact : Bool) (tp fq : String)
      (nbFloat : Option (Except PyExc FObj)) (nbIndex : Option (Except PyExc FObj))
  deriving Inhabited

namespace FObj
def id : FObj → Nat | mk i .. => i
def kind : FObj → FKind | mk _ k .. => k
def exact : FObj → Bool | mk _ _ e .. => e
def tp : FObj → String | mk _ _ _ t .. => t
def fq : FObj → String | mk _ _ _ _ q .. => q
def nbFloat : FObj → Option (Except PyExc FObj) | mk _ _ _ _ _ f _ => f
def nbIndex : FObj → Option (Except PyExc FObj) | mk _ _ _ _ _ _ i => i
/-- `PyFloat_CheckExact`. -/
def isExactFloat (o : FObj) : Bool := match o.kind with | .float _ => o.exact | _ => false
end FObj

/-- A float subclass, by identity: its name, and what calling it with one new exact float
of value `x` returns (its `__new__` and `__init__`, which may raise). -/
structure FCls where
  name : String
  call : F64 → Py FObj

/-- What a float constructor returns. -/
inductive FRes where
  /-- The argument object itself (`Py_NewRef`), an exact float of value `x`. -/
  | same (x : F64)
  /-- An object a slot returned, passed on as it is (an exact float of value `x`). -/
  | obj (o : FObj) (x : F64)
  /-- A new exact float, `PyFloat_FromDouble(x)`. -/
  | fresh (x : F64)
  /-- A new instance of the subclass `cls` with `ob_fval` `x` (`type->tp_alloc`). -/
  | freshSub (cls : String) (x : F64)
  /-- Whatever `PyObject_CallOneArg(type, result)` returned. -/
  | called (o : FObj)
  deriving Inhabited

/-- The value of a float result, when it is a float. -/
def FRes.val : FRes → Option F64
  | .same x | .obj _ x | .fresh x | .freshSub _ x => some x
  | .called o => match o.kind with | .float x => some x | _ => none

def deprecationMsgFloat (o res : FObj) : String :=
  s!"{o.fq}.__float__() must return a float, not {res.fq}.  The ability to return an instance of a strict subclass of float is deprecated, and may be removed in a future version of Python."

def deprecationMsgIndex (o res : FObj) : String :=
  s!"{o.fq}.__index__() must return an int, not {res.fq}.  The ability to return an instance of a strict subclass of int is deprecated, and may be removed in a future version of Python."

/-! ## `_PyNumber_Index`, `PyNumber_AsSsize_t`, `PyFloat_AsDouble` -/

/-- `_PyNumber_Index`, Objects/abstract.c:1410-1453: an int itself; otherwise `nb_index`,
whose result must be an int, a strict subclass of int being deprecated. -/
def numberIndex (warnErr : Bool) (o : FObj) : Py Int :=
  match o.kind with
  | .int n => .ok n
  | _ =>
    match o.nbIndex with
    | none => .error (.typeError s!"'{o.tp.take 200}' object cannot be interpreted as an integer")
    | some (.error e) => .error e
    | some (.ok res) =>
      match res.kind with
      | .int n =>
        if res.exact then .ok n
        else if warnErr then .error (.named "DeprecationWarning" (deprecationMsgIndex o res))
        else .ok n
      | _ => .error (.typeError s!"{o.fq}.__index__() must return an int, not {res.fq}")

/-- `PyNumber_AsSsize_t(o, NULL)`, Objects/abstract.c:1468-1510: the index, clipped to
`Py_ssize_t` on overflow. -/
def numberAsSsize (warnErr : Bool) (o : FObj) : Py Int := do
  let n ← numberIndex warnErr o
  return clipSsize n

/-- `PyFloat_AsDouble`, floatobject.c:247-303. -/
def asDoubleO (warnErr : Bool) (op : FObj) : Py F64 :=
  match op.kind with
  | .float x => .ok x
  | _ =>
    match op.nbFloat with
    | none =>
      match op.nbIndex with
      | some _ => do
        let n ← numberIndex warnErr op
        PyLong_AsDouble n
      | none => .error (.typeError s!"must be real number, not {op.tp.take 50}")
    | some (.error e) => .error e
    | some (.ok res) =>
      match res.kind with
      | .float x =>
        if res.exact then .ok x
        else if warnErr then .error (.named "DeprecationWarning" (deprecationMsgFloat op res))
        else .ok x
      | _ => .error (.typeError s!"{op.fq}.__float__() must return a float, not {res.fq}")

/-! ## `PyFloat_FromString` and `PyNumber_Float` -/

/-- `PyFloat_FromString`, floatobject.c:180-227: a str through
`_PyUnicode_TransformDecimalAndSpaceToASCII`, bytes, bytearray and any other buffer as
their bytes, and `TypeError` for anything else. -/
def fromStringO (v : FObj) : Py F64 :=
  match v.kind with
  | .str cps => PyFloat_FromString (.str cps)
  | .bytes b | .bytearray b | .buffer b => PyFloat_FromString (.bytes b)
  | _ => .error (.typeError s!"float() argument must be a string or a real number, not '{v.tp.take 200}'")

/-- `PyNumber_Float`, Objects/abstract.c:1602-1657. -/
def numberFloat (warnErr : Bool) (o : FObj) : Py FRes :=
  match o.kind, o.exact with
  | .float x, true => .ok (.same x)
  | _, _ =>
    match o.nbFloat with
    | some (.error e) => .error e
    | some (.ok res) =>
      match res.kind with
      | .float x =>
        if res.exact then .ok (.obj res x)
        else if warnErr then .error (.named "DeprecationWarning" (deprecationMsgFloat o res))
        else .ok (.fresh x)
      | _ => .error (.typeError s!"{o.fq}.__float__() must return a float, not {res.fq}")
    | none =>
      match o.nbIndex with
      | some _ => do
        let n ← numberIndex warnErr o
        let v ← PyLong_AsDouble n
        return .fresh v
      | none =>
        match o.kind with
        | .float x => .ok (.fresh x)
        | _ => do
          let v ← fromStringO o
          return .fresh v

/-! ## The constructors -/

/-- The `int` zero `_PyLong_GetZero()`, with `long_float` as its `nb_float`. -/
def zeroInt : FObj := .mk 0 (.int 0) true "int" "int" (some (.ok (.mk 1 (.float d0) true "float" "float" none none))) none

/-- `float_new_impl`, floatobject.c:1567-1585, for `type == &PyFloat_Type`. -/
def floatNewExact (warnErr : Bool) (x : Option FObj) : Py FRes :=
  match x with
  | none => .ok (.fresh d0)
  | some o =>
    match o.kind with
    | .str cps => if o.exact then (PyFloat_FromString (.str cps)).map .fresh else numberFloat warnErr o
    | _ => numberFloat warnErr o

/-- The value of the float `float_new_impl(&PyFloat_Type, x)` returned. -/
def FRes.floatVal : FRes → F64
  | .same x | .obj _ x | .fresh x | .freshSub _ x => x
  | .called _ => d0

/-- `float_subtype_new`, floatobject.c:1593-1610: a regular float first, then a new
instance of the subclass holding its value. -/
def floatSubtypeNew (warnErr : Bool) (cls : FCls) (x : FObj) : Py FRes := do
  let tmp ← floatNewExact warnErr (some x)
  return .freshSub cls.name tmp.floatVal

/-- `float_new_impl`, floatobject.c:1567-1585: `cls = none` is `float` itself. -/
def floatNew (warnErr : Bool) (cls : Option FCls) (x : Option FObj) : Py FRes :=
  match cls with
  | some c => floatSubtypeNew warnErr c (x.getD zeroInt)
  | none => floatNewExact warnErr x

/-- `float_vectorcall`, floatobject.c:1613-1627. -/
def floatVectorcall (warnErr : Bool) (cls : Option FCls) (args : List FObj) (kwnames : List String) :
    Py FRes :=
  if kwnames ≠ [] then .error (.typeError "float() takes no keyword arguments")
  else
    match args with
    | [] => floatNew warnErr cls none
    | [x] => floatNew warnErr cls (some x)
    | _ => .error (.typeError s!"float expected at most 1 argument, got {args.length}")

/-- `float_from_number_impl`, floatobject.c:1641-1657. -/
def floatFromNumber (warnErr : Bool) (cls : Option FCls) (number : FObj) : Py FRes :=
  match number.kind, cls with
  | .float x, none => if number.exact then .ok (.same x) else .ok (.fresh x)
  | _, _ => do
    let x ← asDoubleO warnErr number
    match cls with
    | none => return .fresh x
    | some c => return .called (← c.call x)

/-! ## Identity methods and `__getnewargs__` -/

/-- `float_float`, floatobject.c:1069-1077: the object itself when it is an exact float,
and a new exact float of its value for a subclass instance. `self` is always a float. -/
def floatFloatO (x : F64) (exact : Bool) : FRes := if exact then .same x else .fresh x

/-- `float_conjugate_impl`, floatobject.c:1086-1090. -/
def floatConjugateO (x : F64) (exact : Bool) : FRes := floatFloatO x exact

/-- `float_getreal`, floatobject.c:1704-1707. -/
def floatGetrealO (x : F64) (exact : Bool) : FRes := floatFloatO x exact

/-- `float___getnewargs___impl`, floatobject.c:1665-1669: `Py_BuildValue("(d)", x)`, a
1-tuple holding a new float. -/
def floatGetnewargsO (x : F64) : List F64 := [x]

/-! ## `float.fromhex` at the object level -/

/-- UTF-8 of one code point; `none` for a surrogate, which `PyUnicode_AsUTF8AndSize`
refuses. -/
def utf8Cp (c : Nat) : Option (List Nat) :=
  if c < 0x80 then some [c]
  else if c < 0x800 then some [0xc0 + c / 64, 0x80 + c % 64]
  else if 0xd800 ≤ c && c < 0xe000 then none
  else if c < 0x10000 then some [0xe0 + c / 4096, 0x80 + (c / 64) % 64, 0x80 + c % 64]
  else some [0xf0 + c / 262144, 0x80 + (c / 4096) % 64, 0x80 + (c / 64) % 64, 0x80 + c % 64]

/-- `PyUnicode_AsUTF8AndSize` on a str: its UTF-8 bytes, or the position of the first
surrogate. -/
def utf8Encode : Nat → List Nat → Except Nat (List Nat)
  | _, [] => .ok []
  | i, c :: cs =>
    match utf8Cp c with
    | none => .error i
    | some b => match utf8Encode (i + 1) cs with
      | .ok r => .ok (b ++ r)
      | .error j => .error j

/-- `float_fromhex_impl`, floatobject.c:1225-1463, with the argument conversion of
:1280-1282 and the subclass call of :1444-1446. -/
def floatFromhexO (cls : Option FCls) (arg : FObj) : Py FRes :=
  match arg.kind with
  | .str cps =>
    match utf8Encode 0 cps with
    | .error i =>
      .error (.named "UnicodeEncodeError"
        s!"~'utf-8' codec can't encode character at position {i}: surrogates not allowed")
    | .ok b => do
      let x ← float_fromhex b
      match cls with
      | none => return .fresh x
      | some c => return .called (← c.call x)
  | _ => .error (.typeError "bad argument type for built-in operation")

/-! ## `round` -/

/-- What `float.__round__` returns: an int, or a float. -/
inductive RoundRes where
  | int (n : Int)
  | float (x : F64)
  deriving DecidableEq, Repr

/-- `float___round___impl`, floatobject.c:1024-1066: `none` is `ndigits=None`. -/
def floatRoundO (warnErr : Bool) (x : F64) (o_ndigits : Option FObj) : Py RoundRes :=
  match o_ndigits with
  | none => (float_round_int x).map .int
  | some o => do
    let ndigits ← numberAsSsize warnErr o
    let r ← float_round_ndigits x ndigits
    return .float r

end PyLean.Binary64
