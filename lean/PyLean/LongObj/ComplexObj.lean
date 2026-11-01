import PyLean.LongObj.ComplexParse

/-!
The object layer of `Objects/complexobject.c`: constructors, conversions and the
number, comparison, hash and repr slots.

A Python object is an `Obj R`, which records exactly what the C code asks of an
object: which of `PyComplex_Check`, `PyFloat_Check`, `PyLong_Check`,
`PyUnicode_Check` hold, whether it is of the exact base type, its type names,
whether `tp_as_number` is set, and what `__complex__`, `nb_float` and `nb_index`
do when called. A user method is a `Slot` with a fixed outcome, so a theorem
quantifying over `Obj R` quantifies over every behaviour of those methods.

Evaluation runs in `M`, which keeps a log of user-visible calls and warnings
even when an exception ends the computation, so check order is observable.
-/

namespace PyLean.LongObj.Cplx

open CDouble

/-- A user-visible event, newest first in the log. -/
inductive Ev where
  /-- A Python-level `__complex__`, `__float__` or `__index__` ran. -/
  | call (name : String)
  /-- A `DeprecationWarning` was issued. -/
  | warn (msg : String)
  deriving DecidableEq, Repr, Inhabited

/-- Evaluation: an exception or a value, and the log either way. -/
abbrev M := EStateM PyExc (List Ev)

/-- What the C code reads off `Py_TYPE(op)`. -/
structure TypeInfo where
  /-- `tp_name`, printed by `%.200s` and `%.50s`. -/
  tpName : String
  /-- The fully qualified name, printed by `%T`. -/
  fqName : String
  /-- `tp_as_number != NULL`. -/
  hasNumber : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The C-level value of an object. -/
inductive Val (R : Type) where
  /-- `PyComplex_Check`. -/
  | cplx (c : Cx R)
  /-- `PyFloat_Check`. -/
  | flt (x : R)
  /-- `PyLong_Check`. -/
  | long (n : Int)
  /-- `PyUnicode_Check`; `repr` is what `%R` prints. -/
  | str (s : List Nat) (repr : String)
  /-- `Py_None`. -/
  | none
  /-- Anything else. -/
  | other

mutual
  /-- What calling a special method or number slot does. -/
  inductive Slot (R : Type) where
    /-- Not defined. -/
    | absent
    /-- The implementation inherited from `complex`, `float` or `int`. -/
    | builtin
    /-- A Python method that raises. -/
    | raises (e : PyExc)
    /-- A Python method that returns. -/
    | returns (o : Obj R)
  /-- A Python object. `exact` says it is not an instance of a subclass. -/
  inductive Obj (R : Type) where
    | mk (ti : TypeInfo) (exact : Bool) (val : Val R)
         (dcomplex nbFloat nbIndex : Slot R)
end

namespace Slot
variable {R : Type}
def isAbsent : Slot R → Bool
  | .absent => true
  | _ => false
end Slot

namespace Obj
variable {R : Type}
def ti : Obj R → TypeInfo | .mk t _ _ _ _ _ => t
def exact : Obj R → Bool | .mk _ e _ _ _ _ => e
def val : Obj R → Val R | .mk _ _ v _ _ _ => v
def dcomplex : Obj R → Slot R | .mk _ _ _ s _ _ => s
def nbFloat : Obj R → Slot R | .mk _ _ _ _ s _ => s
def nbIndex : Obj R → Slot R | .mk _ _ _ _ _ s => s

/-- `PyComplex_Check`. -/
def isComplex (o : Obj R) : Bool := match o.val with | .cplx _ => true | _ => false
/-- `PyComplex_CheckExact`. -/
def isComplexExact (o : Obj R) : Bool := o.isComplex && o.exact
end Obj

/-- `%.200s` and friends. -/
def pct (n : Nat) (s : String) : String := String.ofList (s.toList.take n)

/-- Classes the file refers to. -/
def complexTI : TypeInfo := ⟨"complex", "complex", true⟩
def floatTI : TypeInfo := ⟨"float", "float", true⟩
def intTI : TypeInfo := ⟨"int", "int", true⟩

section obj

variable {R : Type} [CDouble R]

/-- An exact `complex`. Its `__complex__` is `complex.__complex__`. -/
def mkComplex (c : Cx R) : Obj R := .mk complexTI true (.cplx c) .builtin .absent .absent

/-- An exact `float`. -/
def mkFloat (x : R) : Obj R := .mk floatTI true (.flt x) .absent .builtin .absent

/-- An exact `int`. -/
def mkLong (n : Int) : Obj R := .mk intTI true (.long n) .absent .builtin .builtin

/-- The type argument of the constructors. -/
inductive TyArg where
  /-- `&PyComplex_Type`. -/
  | complex
  /-- A subclass, by the fully qualified name of the instance's type. -/
  | sub (fqName : String)
  deriving DecidableEq, Repr, Inhabited

def TyArg.isExact : TyArg → Bool
  | .complex => true
  | .sub _ => false

/-- A constructed `complex` (or subclass) object. `isArg` is the identity case,
`Py_NewRef(arg)`. -/
structure Made (R : Type) where
  type : TyArg
  cval : Cx R
  isArg : Bool := false

/-- `complex_subtype_from_c_complex`, lines 399-408. `tp_alloc` failing is
`MemoryError`, which is not modelled. -/
def complex_subtype_from_c_complex (type : TyArg) (cval : Cx R) : Made R := ⟨type, cval, false⟩

/-- `PyComplex_FromCComplex`, lines 410-421. -/
def PyComplex_FromCComplex (cval : Cx R) : Made R := ⟨.complex, cval, false⟩

/-- `complex_subtype_from_doubles`, lines 423-430. -/
def complex_subtype_from_doubles (type : TyArg) (real imag : R) : Made R :=
  complex_subtype_from_c_complex type ⟨real, imag⟩

/-- `PyComplex_FromDoubles`, lines 432-439. -/
def PyComplex_FromDoubles (real imag : R) : Made R := PyComplex_FromCComplex ⟨real, imag⟩

/-- What the object layer needs from its surroundings. -/
structure Env (R : Type) where
  /-- `DeprecationWarning` is turned into an exception. -/
  warnErr : Bool
  db : UniDB
  sd : Strtod R

/-- `PyErr_WarnFormat(PyExc_DeprecationWarning, 1, ...)`: nonzero when the
warning became an exception. -/
def warnDep (E : Env R) (msg : String) : M Unit :=
  if E.warnErr then throw (.named "DeprecationWarning" msg)
  else modify (Ev.warn msg :: ·)

def intTooLarge : PyExc := .overflowError "int too large to convert to float"

/-- `PyLong_AsDouble`, `Objects/longobject.c:3484-3514`. -/
def longAsDouble (n : Int) : Py R :=
  match ofInt n with
  | some x => .ok x
  | none => .error intTooLarge

/-- Lift a pure step. -/
def liftPy {α : Type} : Py α → M α
  | .ok a => pure a
  | .error e => throw e

/-- Call a slot on `self`. A Python method logs its call. The built-ins are
`complex___complex___impl` (lines 917-927), `float_float` and `long_float`. -/
def callSlot (name : String) (s : Slot R) (self : Obj R) : M (Obj R) :=
  match s with
  | .absent => throw .modelFuel
  | .raises e => do modify (Ev.call name :: ·); throw e
  | .returns o => do modify (Ev.call name :: ·); pure o
  | .builtin =>
    match self.val with
    | .cplx c => pure (if self.exact then self else mkComplex c)
    | .flt x => pure (if self.exact then self else mkFloat x)
    | .long n =>
      if name == "__index__" then pure (mkLong n)
      else do
        let x ← liftPy (longAsDouble n)
        pure (mkFloat x)
    | _ => throw .modelFuel

/-- `_PyNumber_Index`, `Objects/abstract.c:1400-1439`. -/
def _PyNumber_Index (E : Env R) (item : Obj R) : M Int :=
  match item.val with
  | .long n => pure n
  | _ =>
    if !(item.ti.hasNumber && !item.nbIndex.isAbsent) then
      throw (.typeError
        s!"'{pct 200 item.ti.tpName}' object cannot be interpreted as an integer")
    else do
      let result ← callSlot "__index__" item.nbIndex item
      match result.val with
      | .long n =>
        if result.exact then pure n
        else do
          warnDep E (s!"__index__ returned non-int (type {pct 200 result.ti.tpName}).  " ++
            "The ability to return an instance of a strict subclass of int " ++
            "is deprecated, and may be removed in a future version of Python.")
          pure n
      | _ => throw (.typeError
          s!"__index__ returned non-int (type {pct 200 result.ti.tpName})")

/-- `%.50s.__float__ returned non-float (type %.50s)`. -/
def nonFloatMsg (op res : Obj R) : String :=
  s!"{pct 50 op.ti.tpName}.__float__ returned non-float (type {pct 50 res.ti.tpName})"

/-- The longer message of the `__float__` deprecation. -/
def nonFloatDep (op res : Obj R) : String :=
  nonFloatMsg op res ++ ".  " ++
    "The ability to return an instance of a strict subclass of float " ++
    "is deprecated, and may be removed in a future version of Python."

/-- `PyFloat_AsDouble`, `Objects/floatobject.c:257-314`. A `float` subclass is
read directly: its `__float__` is not consulted. -/
def PyFloat_AsDouble (E : Env R) (op : Obj R) : M R :=
  match op.val with
  | .flt x => pure x
  | _ =>
    if !op.ti.hasNumber || op.nbFloat.isAbsent then
      if op.ti.hasNumber && !op.nbIndex.isAbsent then do
        let res ← _PyNumber_Index E op
        liftPy (longAsDouble res)
      else
        throw (.typeError s!"must be real number, not {pct 50 op.ti.tpName}")
    else do
      let res ← callSlot "__float__" op.nbFloat op
      match res.val with
      | .flt x =>
        if res.exact then pure x
        else do
          warnDep E (nonFloatDep op res)
          pure x
      | _ => throw (.typeError (nonFloatMsg op res))

/-- `PyNumber_Float`, `Objects/abstract.c:1592-1646`. A `float` subclass goes
through its `nb_float` here, unlike in `PyFloat_AsDouble`. The final
`PyFloat_FromString` is not reachable from this file, since `complex_new_impl`
only calls this after finding `nb_float` or `nb_index`; its `TypeError` for a
non-string is what is written here. -/
def PyNumber_Float (E : Env R) (o : Obj R) : M R :=
  match o.val, o.exact with
  | .flt x, true => pure x
  | _, _ =>
    if o.ti.hasNumber && !o.nbFloat.isAbsent then do
      let res ← callSlot "__float__" o.nbFloat o
      match res.val with
      | .flt x =>
        if res.exact then pure x
        else do
          warnDep E (nonFloatDep o res)
          pure x
      | _ => throw (.typeError (nonFloatMsg o res))
    else if o.ti.hasNumber && !o.nbIndex.isAbsent then do
      let res ← _PyNumber_Index E o
      liftPy (longAsDouble res)
    else
      match o.val with
      | .flt x => pure x
      | _ => throw (.typeError
          s!"float() argument must be a string or a real number, not '{pct 200 o.ti.tpName}'")

/-- `try_complex_special_method`, lines 488-519. C returns `NULL` both when the
method is absent and when it failed; here those are `none` and an exception. -/
def try_complex_special_method (E : Env R) (op : Obj R) : M (Option (Cx R)) :=
  match op.dcomplex with
  | .absent => pure none
  | s => do
    let res ← callSlot "__complex__" s op
    match res.val with
    | .cplx c =>
      if res.exact then pure (some c)
      else do
        warnDep E (s!"__complex__ returned non-complex (type {pct 200 res.ti.tpName}).  " ++
          "The ability to return an instance of a strict subclass of complex " ++
          "is deprecated, and may be removed in a future version of Python.")
        pure (some c)
    | _ => throw (.typeError
        s!"__complex__ returned non-complex (type {pct 200 res.ti.tpName})")

/-- `PyComplex_RealAsDouble`, lines 443-462. -/
def PyComplex_RealAsDouble (E : Env R) (op : Obj R) : M R :=
  match op.val with
  | .cplx c => pure c.real
  | _ => do
    match ← try_complex_special_method E op with
    | some c => pure c.real
    | none => PyFloat_AsDouble E op

/-- `PyComplex_ImagAsDouble`, lines 464-486. -/
def PyComplex_ImagAsDouble (E : Env R) (op : Obj R) : M R :=
  match op.val with
  | .cplx c => pure c.imag
  | _ => do
    match ← try_complex_special_method E op with
    | some c => pure c.imag
    | none =>
      let _ ← PyFloat_AsDouble E op
      pure zero

/-- `PyComplex_AsCComplex`, lines 521-555. -/
def PyComplex_AsCComplex (E : Env R) (op : Obj R) : M (Cx R) :=
  match op.val with
  | .cplx c => pure c
  | _ => do
    match ← try_complex_special_method E op with
    | some c => pure c
    | none =>
      let x ← PyFloat_AsDouble E op
      pure ⟨x, zero⟩

/-- `complex_repr`, lines 557-612. `ds x sign` is
`PyOS_double_to_string(x, 'r', 0, sign ? Py_DTSF_SIGN : 0, NULL)`. -/
def complex_repr (ds : R → Bool → String) (v : Cx R) : String :=
  if v.real ==. zero && copysign one v.real ==. one then
    "" ++ "" ++ ds v.imag false ++ "j" ++ ""
  else
    "(" ++ ds v.real false ++ ds v.imag true ++ "j" ++ ")"

/-- `(Py_uhash_t)x`. -/
def toUhash (h : Int) : Nat := (h % (2 ^ 64 : Int)).toNat

/-- `(Py_hash_t)x`. -/
def toHash (u : Nat) : Int := if u ≥ 2 ^ 63 then (u : Int) - 2 ^ 64 else u

/-- `_PyHASH_IMAG`, `Include/cpython/pyhash.h:6,20`. -/
def hashImag : Nat := 1000003

/-- `complex_hash`, lines 614-635. `hd` is `_Py_HashDouble(op, ·)`. -/
def complex_hash (hd : R → Int) (v : Cx R) : Int :=
  let hashreal := toUhash (hd v.real)
  if hashreal == 2 ^ 64 - 1 then -1 else
  let hashimag := toUhash (hd v.imag)
  if hashimag == 2 ^ 64 - 1 then -1 else
  let combined := (hashreal + hashImag * hashimag) % 2 ^ 64
  let combined := if combined == 2 ^ 64 - 1 then 2 ^ 64 - 2 else combined
  toHash combined

/-- `real_to_double`, lines 644-656, with `_Py_convert_int_to_double`,
`Objects/floatobject.c:330-346`. `.ok none` is `NotImplemented`. -/
def real_to_double (obj : Obj R) : Py (Option R) :=
  match obj.val with
  | .flt x => .ok (some x)
  | .long n =>
    match longAsDouble (R := R) n with
    | .ok x => .ok (some x)
    | .error e => .error e
  | _ => .ok none

/-- `real_to_complex`, lines 658-663. -/
def real_to_complex (obj : Obj R) : Py (Option (Cx R)) :=
  match real_to_double obj with
  | .ok (some x) => .ok (some ⟨x, zero⟩)
  | .ok none => .ok none
  | .error e => .error e

/-- `TO_COMPLEX`, lines 638-642. -/
def TO_COMPLEX (obj : Obj R) : Py (Option (Cx R)) :=
  match obj.val with
  | .cplx c => .ok (some c)
  | _ => real_to_complex obj

def divZero : PyExc := .zeroDivisionError "division by zero"

/-- `COMPLEX_BINOP`, lines 680-716. `.ok none` is `NotImplemented`. `errno` is
cleared on entry. -/
def complex_binop (cc : Cx R → Cx R → Errno → Cx R × Errno)
    (rc : R → Cx R → Errno → Cx R × Errno)
    (cr : Cx R → R → Errno → Cx R × Errno)
    (v w : Obj R) : Py (Option (Cx R)) :=
  let finish (r : Cx R × Errno) : Py (Option (Cx R)) :=
    if r.2 = Errno.edom then .error divZero else .ok (some r.1)
  match w.val with
  | .cplx b =>
    match v.val with
    | .cplx a => finish (cc a b Errno.ok)
    | _ =>
      match real_to_double v with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some x) => finish (rc x b Errno.ok)
  | _ =>
    match v.val with
    | .cplx a =>
      match real_to_double w with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some x) => finish (cr a x Errno.ok)
    | _ => .ok none

/-- `complex_add`: `COMPLEX_BINOP(add, sum)`, line 718. -/
def complex_add : Obj R → Obj R → Py (Option (Cx R)) :=
  complex_binop (fun a b e => (c_sum a b, e)) (fun a b e => (rc_sum a b, e))
    (fun a b e => (cr_sum a b, e))

/-- `complex_mul`: `COMPLEX_BINOP(mul, prod)`, line 719. -/
def complex_mul : Obj R → Obj R → Py (Option (Cx R)) :=
  complex_binop (fun a b e => (c_prod a b, e)) (fun a b e => (rc_prod a b, e))
    (fun a b e => (cr_prod a b, e))

/-- `complex_sub`: `COMPLEX_BINOP(sub, diff)`, line 720. -/
def complex_sub : Obj R → Obj R → Py (Option (Cx R)) :=
  complex_binop (fun a b e => (c_diff a b, e)) (fun a b e => (rc_diff a b, e))
    (fun a b e => (cr_diff a b, e))

/-- `complex_div`: `COMPLEX_BINOP(div, quot)`, line 721. -/
def complex_div : Obj R → Obj R → Py (Option (Cx R)) :=
  complex_binop c_quot rc_quot cr_quot

/-- The part of `complex_pow` after the operands are complex, lines 735-756. -/
def complex_pow_core (L : Libm R) (a b : Cx R) : Py (Cx R) :=
  let errno := Errno.ok
  let (p, errno) : Cx R × Errno :=
    if b.imag ==. zero && b.real ==. CDouble.floor b.real && le (fabs b.real) hundred then
      let (p, errno) := c_powi a (toLong b.real) errno
      (p, adjustERange2 p.real p.imag errno)
    else
      c_pow L a b errno
  if errno = Errno.edom then
    .error (.zeroDivisionError "zero to a negative or complex power")
  else if errno = Errno.erange then
    .error (.overflowError "complex exponentiation")
  else .ok p

/-- `complex_pow`, lines 723-757. Both operands convert before `z` is looked at. -/
def complex_pow (L : Libm R) (v w z : Obj R) : Py (Option (Cx R)) :=
  match TO_COMPLEX v with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some a) =>
    match TO_COMPLEX w with
    | .error e => .error e
    | .ok none => .ok none
    | .ok (some b) =>
      match z.val with
      | .none =>
        match complex_pow_core L a b with
        | .ok p => .ok (some p)
        | .error e => .error e
      | _ => .error (.valueError "complex modulo")

/-- `complex_neg`, lines 759-767. -/
def complex_neg (v : Cx R) : Cx R := ⟨⊖v.real, ⊖v.imag⟩

/-- `complex_pos`, lines 769-777: an exact complex is returned as is. -/
def complex_pos (v : Obj R) (c : Cx R) : Made R :=
  if v.isComplexExact then ⟨.complex, c, true⟩ else PyComplex_FromCComplex c

/-- `complex_abs`, lines 779-790. `errno` is the value left by whatever ran
before: 3.14.7 does not clear it here. -/
def complex_abs (L : Libm R) (v : Cx R) (errno : Errno) : Py R :=
  let (result, errno) := c_abs L v errno
  if errno = Errno.erange then .error (.overflowError "absolute value too large")
  else .ok result

/-- `complex_bool`, lines 792-797. -/
def complex_bool (v : Cx R) : Bool := ne v.real zero || ne v.imag zero

/-- The six rich comparison opcodes. -/
inductive CmpOp where
  | lt | le | eq | ne | gt | ge
  deriving DecidableEq, Repr, Inhabited

/-- `complex_richcompare`, lines 799-853. `none` is `NotImplemented`. For an int
`w` with a zero imaginary part it defers to `float_richcompare`, here `eqInt`. -/
def complex_richcompare (i : Cx R) (w : Obj R) (op : CmpOp) : Option Bool :=
  if op != CmpOp.eq && op != CmpOp.ne then none
  else
    let isEq := op == CmpOp.eq
    let conclude (equal : Bool) : Option Bool := some (equal == isEq)
    match w.val with
    | .long n =>
      if i.imag ==. zero then
        some (if isEq then eqInt i.real n else !eqInt i.real n)
      else conclude false
    | .flt x => conclude (i.real ==. x && i.imag ==. zero)
    | .cplx j => conclude (i.real ==. j.real && i.imag ==. j.imag)
    | _ => none

/-- `complex_conjugate_impl`, lines 861-868. -/
def complex_conjugate_impl (self : Cx R) : Cx R := ⟨self.real, ⊖self.imag⟩

/-- `complex___getnewargs___impl`, lines 875-881. -/
def complex___getnewargs___impl (self : Cx R) : R × R := (self.real, self.imag)

/-- `complex___format___impl`, lines 893-909, with the empty-spec test of
`_PyComplex_FormatAdvancedWriter`, `Python/formatter_unicode.c:1691-1701`.
`advanced` stands for the rest of that function, which is outside this file. -/
def complex___format___impl (ds : R → Bool → String)
    (advanced : Cx R → List Nat → Py String) (self : Cx R) (spec : List Nat) : Py String :=
  if spec.isEmpty then .ok (complex_repr ds self) else advanced self spec

/-- `complex___complex___impl`, lines 917-927. -/
def complex___complex___impl (self : Obj R) (c : Cx R) : Made R :=
  if self.isComplexExact then ⟨.complex, c, true⟩ else PyComplex_FromCComplex c

/-- `complex_subtype_from_string`, lines 1053-1081. -/
def complex_subtype_from_string (E : Env R) (type : TyArg) (v : Obj R) : M (Made R) :=
  match v.val with
  | .str s repr =>
    match complex_from_str E.db E.sd s repr with
    | .ok c => pure (complex_subtype_from_c_complex type c)
    | .error e => throw e
  | _ => throw (.typeError
      s!"complex() argument must be a string or a number, not {v.ti.fqName}")

/-- The real and imaginary slots of `complex_new_impl` accept this. -/
def realNumberLike (o : Obj R) : Bool :=
  o.ti.hasNumber && (!o.nbFloat.isAbsent || !o.nbIndex.isAbsent || o.isComplex)

/-- The `cval` of a `PyComplex_Check` object. -/
def cvalOf (o : Obj R) : Cx R :=
  match o.val with
  | .cplx c => c
  | _ => ⟨zero, zero⟩

/-- `complex_new_impl`, lines 1168-1297. `none` is a `NULL` argument. -/
def complex_new_impl (E : Env R) (type : TyArg) (r? i? : Option (Obj R)) : M (Made R) := do
  let orig_r : Obj R := r?.getD (mkLong 0)
  let tmp ← try_complex_special_method E orig_r
  let r : Obj R :=
    match tmp with
    | some c => mkComplex c
    | none => orig_r
  if !realNumberLike r then
    throw (.typeError
      s!"complex() argument 'real' must be a real number, not {r.ti.fqName}")
  match i? with
  | some i =>
    if !realNumberLike i then
      throw (.typeError
        s!"complex() argument 'imag' must be a real number, not {i.ti.fqName}")
  | none => pure ()
  let (cr, cr_is_complex) : Cx R × Bool ←
    if r.isComplex then do
      if !orig_r.ti.hasNumber || (orig_r.nbFloat.isAbsent && orig_r.nbIndex.isAbsent) then
        warnDep E s!"complex() argument 'real' must be a real number, not {orig_r.ti.fqName}"
      pure (cvalOf r, true)
    else do
      let x ← PyNumber_Float E r
      pure (⟨x, zero⟩, false)
  let (ciReal, ciImag, ci_is_complex) : R × R × Bool ←
    match i? with
    | none => pure (cr.imag, zero, false)
    | some i =>
      if i.isComplex then do
        warnDep E s!"complex() argument 'imag' must be a real number, not {i.ti.fqName}"
        let ci := cvalOf i
        pure (ci.real, ci.imag, true)
      else do
        let x ← PyNumber_Float E i
        pure (x, zero, false)
  let crReal := if ci_is_complex then cr.real -. ciImag else cr.real
  let ciReal := if cr_is_complex && i?.isSome then ciReal +. cr.imag else ciReal
  pure (complex_subtype_from_doubles type crReal ciReal)

/-- The clinic wrapper `complex_new`, `Objects/clinic/complexobject.c.h`, with the
part of `_PyArg_UnpackKeywords` (`Python/getargs.c`) that two optional keyword
parameters can reach. Keywords are exact `str`, as `complex(**kw)` guarantees
once `keywords must be strings` has been ruled out. The suggestion suffix of the
unexpected-keyword message is not modelled. -/
def complex_new (E : Env R) (type : TyArg) (args : List (Obj R))
    (kwargs : List (String × Obj R)) : M (Made R) :=
  let nargs := args.length
  let nkw := kwargs.length
  let names := ["real", "imag"]
  let look (k : String) : Option (Obj R) := (kwargs.find? (·.1 == k)).map (·.2)
  if nkw == 0 && nargs ≤ 2 then
    complex_new_impl E type args[0]? args[1]?
  else if nargs + nkw > 2 then
    throw (.typeError
      s!"complex() takes at most 2 {if nargs == 0 then "keyword " else ""}arguments ({nargs + nkw} given)")
  else
    -- copy keyword args from position nargs on
    let fromKw := names.drop nargs
    let found := fromKw.filter (fun k => (look k).isSome)
    if found.length < nkw then
      -- something is left over: by name and position, or unknown
      match (names.take nargs).findIdx? (fun k => (look k).isSome) with
      | some i =>
        throw (.typeError
          s!"argument for complex() given by name ('{names.getD i ""}') and position ({i + 1})")
      | none =>
        let bad := (kwargs.find? (fun kv => !names.contains kv.1)).map (·.1)
        throw (.typeError
          s!"complex() got an unexpected keyword argument '{bad.getD ""}'")
    else
      let r? := if nargs ≥ 1 then args[0]? else look "real"
      let i? := if nargs ≥ 2 then args[1]? else look "imag"
      complex_new_impl E type r? i?

/-- `actual_complex_new`, lines 1093-1152, the `tp_new` slot. -/
def actual_complex_new (E : Env R) (type : TyArg) (args : List (Obj R))
    (kwargs : List (String × Obj R)) : M (Made R) :=
  if args.length > 1 || !kwargs.isEmpty then
    complex_new E type args kwargs
  else
    match args with
    | [] => pure (complex_subtype_from_doubles type zero zero)
    | arg :: _ =>
      if arg.isComplexExact && type == TyArg.complex then
        pure ⟨.complex, cvalOf arg, true⟩
      else
        match arg.val with
        | .str _ _ => complex_subtype_from_string E type arg
        | _ => do
          match ← try_complex_special_method E arg with
          | some c => pure (complex_subtype_from_doubles type c.real c.imag)
          | none =>
            if arg.isComplex then
              let c := cvalOf arg
              pure (complex_subtype_from_doubles type c.real c.imag)
            else if arg.ti.hasNumber && (!arg.nbFloat.isAbsent || !arg.nbIndex.isAbsent) then do
              let r ← PyFloat_AsDouble E arg
              pure (complex_subtype_from_doubles type r zero)
            else
              throw (.typeError
                s!"complex() argument must be a string or a number, not {arg.ti.fqName}")

/-- `complex_from_number_impl`, lines 1309-1326. A subclass is built by calling
it on the exact result, which reaches `actual_complex_new` when the subclass
does not override `__new__`, the case modelled here. -/
def complex_from_number_impl (E : Env R) (type : TyArg) (number : Obj R) : M (Made R) :=
  if number.isComplexExact && type == TyArg.complex then
    pure ⟨.complex, cvalOf number, true⟩
  else do
    let cv ← PyComplex_AsCComplex E number
    let result := PyComplex_FromCComplex cv
    if type != TyArg.complex then
      actual_complex_new E type [mkComplex result.cval] []
    else pure result

end obj

end PyLean.LongObj.Cplx
