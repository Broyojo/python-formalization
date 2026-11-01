import PyLean.DiffCore
import PyLean.LongObj.ComplexDbl
import PyLean.LongObj.ComplexObj

/-!
Differential-testing handler for `Objects/complexobject.c`, run on `Dbl`, exact
binary64. libm is Lean's own `Float` functions, which call the same C library;
`hypot` has no `Float` counterpart, so the case carries its value.

Doubles cross JSON as their bit patterns, so signed zeros and infinities survive.
A result that is a NaN encodes as `"nan"`, because its sign and payload depend on
the compiler's operand order and are not part of Python-visible behaviour apart
from `copysign`.
-/

namespace PyLean.LongObj

open Lean PyLean PyLean.Diff Cplx

namespace DiffComplex

def getDbl (j : Json) : Except String Dbl := do
  return ⟨← j.getNat?⟩

def fieldDbl (j : Json) (key : String) : Except String Dbl := do
  getDbl (← field j key)

def encDbl (x : Dbl) : Json := if x.isNaN then toJson "nan" else toJson x.bits

def encCx (c : Cx Dbl) : Json := Json.mkObj [("re", encDbl c.real), ("im", encDbl c.imag)]

def fieldCx (j : Json) (key : String) : Except String (Cx Dbl) := do
  let v ← field j key
  return ⟨← fieldDbl v "re", ← fieldDbl v "im"⟩

def decExc (j : Json) : Except String PyExc := do
  let cls ← getStr j "cls"
  let msg ← getStr j "msg"
  return match cls with
    | "ValueError" => .valueError msg
    | "TypeError" => .typeError msg
    | "OverflowError" => .overflowError msg
    | "ZeroDivisionError" => .zeroDivisionError msg
    | c => .named c msg

/-- Fuel bounds the nesting of objects returned from methods. -/
def decObj : Nat → Json → Except String (Obj Dbl)
  | 0, _ => throw "object nesting too deep"
  | fuel + 1, j => do
    let ti : TypeInfo := ⟨← getStr j "tp", ← getStr j "fq", ← getBool j "num"⟩
    let exact ← getBool j "exact"
    let v ← field j "val"
    let val : Val Dbl ← match ← getStr v "k" with
      | "c" => pure (.cplx ⟨← fieldDbl v "re", ← fieldDbl v "im"⟩)
      | "f" => pure (.flt (← fieldDbl v "x"))
      | "i" => pure (.long (← getInt v "n"))
      | "s" =>
        let cps ← (← field v "s").getArr?
        let cps ← cps.toList.mapM Json.getNat?
        pure (.str cps (← getStr v "r"))
      | "none" => pure .none
      | _ => pure .other
    let slot (key : String) : Except String (Slot Dbl) := do
      let s ← field j key
      match s with
      | .str "a" => pure .absent
      | .str "b" => pure .builtin
      | _ =>
        match s.getObjVal? "raises" with
        | .ok e => pure (.raises (← decExc e))
        | .error _ => pure (.returns (← decObj fuel (← field s "ret")))
    return .mk ti exact val (← slot "dc") (← slot "nf") (← slot "ni")

def fieldObj (j : Json) (key : String) : Except String (Obj Dbl) := do
  decObj 4 (← field j key)

def decDb (j : Json) : Except String UniDB := do
  let sp ← (← field j "sp").getArr?
  let sp ← sp.toList.mapM Json.getNat?
  let dec ← (← field j "dec").getArr?
  let dec ← dec.toList.mapM fun p => do
    let a ← p.getArr?
    return ((← (a.getD 0 .null).getNat?), (← (a.getD 1 .null).getNat?))
  return { isSpace := fun c => sp.contains c
           toDecimal := fun c => (dec.find? (·.1 == c)).map (·.2) }

/-- `Dbl` to `Float` and back, for libm. -/
def toF (x : Dbl) : Float := Float.ofBits x.bits.toUInt64
def ofF (x : Float) : Dbl := ⟨x.toBits.toNat⟩

/-- glibc: `cos` and `sin` of an infinity set `EDOM`. The `ERANGE` that `pow`,
`exp` and `hypot` set is not written here because `_Py_ADJUST_ERANGE2` runs right
after and overrides it from the result, and none of them can follow the `EDOM`. -/
def libm (hy : Dbl) : Libm Dbl where
  hypot := fun _ _ => (hy, none)
  pow := fun x y => (ofF (Float.pow (toF x) (toF y)), none)
  atan2 := fun y x => (ofF (Float.atan2 (toF y) (toF x)), none)
  exp := fun x => (ofF (Float.exp (toF x)), none)
  log := fun x => (ofF (Float.log (toF x)), none)
  cos := fun x => (ofF (Float.cos (toF x)), if x.isInf then some .edom else none)
  sin := fun x => (ofF (Float.sin (toF x)), if x.isInf then some .edom else none)

def errnoNum : Errno → Nat
  | .ok => 0
  | .edom => 33
  | .erange => 34

def decErrno : Nat → Errno
  | 33 => .edom
  | 34 => .erange
  | _ => .ok

def encEv : Ev → Json
  | .call n => toJson s!"call {n}"
  | .warn m => toJson s!"warn {m}"

def encMade (m : Made Dbl) : Json :=
  let t : String := match m.type with
    | .complex => "complex"
    | .sub n => n
  Json.mkObj [("tp", toJson t), ("re", encDbl m.cval.real), ("im", encDbl m.cval.imag),
    ("isarg", toJson m.isArg)]

/-- Run a logged computation, encoding the outcome and the log together, so a
check-order difference shows up even when an exception ends the call. -/
def encM {α : Type} (enc : α → Json) (m : M α) : Json :=
  let wrap (r : Json) (s : List Ev) : Json :=
    Json.mkObj [("ok", Json.mkObj [("r", r), ("log", toJson (s.reverse.map encEv))])]
  match m.run [] with
  | .ok a s => wrap (enc a) s
  | .error e s => wrap (Json.mkObj [("exc", toJson e.className), ("msg", toJson e.message)]) s

/-- A slot's result: `NotImplemented` or a complex. -/
def encBin : Option (Cx Dbl) → Json
  | none => toJson "NotImplemented"
  | some c => encCx c

def encOptBool : Option Bool → Json
  | none => toJson "NotImplemented"
  | some b => toJson b

def getEnv (j : Json) : Except String (Env Dbl) := do
  let db ← match j.getObjVal? "db" with
    | .ok d => decDb d
    | .error _ => pure { isSpace := fun _ => false, toDecimal := fun _ => none }
  let warnErr ← match j.getObjVal? "warnerr" with
    | .ok b => b.getBool?
    | .error _ => pure false
  return { warnErr, db, sd := Dbl.asciiStrtod }

def getType (j : Json) : Except String TyArg := do
  match j.getObjVal? "sub" with
  | .ok (.str n) => pure (.sub n)
  | _ => pure .complex

def getHy (j : Json) : Except String Dbl :=
  match j.getObjVal? "hy" with
  | .ok v => getDbl v
  | .error _ => pure ⟨0⟩

def hashDbl (ptr : Int) (x : Dbl) : Int := if x.isNaN then ptr else Dbl.hashFinite x

/-- `complex.__format__`, past the empty-spec test: a one-character spec, the only
kind the generator sends, is an unknown presentation type. -/
def advanced (_ : Cx Dbl) (spec : List Nat) : Py String :=
  let c := Char.ofNat (spec.getD 0 0)
  .error (.valueError s!"Unknown format code '{c}' for object of type 'complex'")

def encLog (j : Json) : Json := Json.mkObj [("r", j), ("log", toJson ([] : List Json))]

def run (fn : String) (j : Json) : Except String Json := do
  let E ← getEnv j
  match fn with
  | "cx_add" | "cx_sub" | "cx_mul" | "cx_div" =>
    let v ← fieldObj j "v"
    let w ← fieldObj j "w"
    let r := match fn with
      | "cx_add" => complex_add v w
      | "cx_sub" => complex_sub v w
      | "cx_mul" => complex_mul v w
      | _ => complex_div v w
    return encPy encBin r
  | "cx_pow" =>
    let L := libm (← getHy j)
    return encPy encBin (complex_pow L (← fieldObj j "v") (← fieldObj j "w") (← fieldObj j "z"))
  | "cx_neg" => return encPy encCx (.ok (complex_neg (← fieldCx j "z")))
  | "cx_pos" =>
    let o ← fieldObj j "o"
    return encPy encMade (.ok (complex_pos o (cvalOf o)))
  | "cx_dcomplex" =>
    let o ← fieldObj j "o"
    return encPy encMade (.ok (complex___complex___impl o (cvalOf o)))
  | "cx_abs" =>
    let L := libm (← getHy j)
    let e := decErrno (← getNat j "errno")
    return encPy encDbl (complex_abs L (← fieldCx j "z") e)
  | "cx_bool" => return encPy toJson (.ok (complex_bool (← fieldCx j "z")))
  | "cx_conj" => return encPy encCx (.ok (complex_conjugate_impl (← fieldCx j "z")))
  | "cx_getnewargs" =>
    let r := complex___getnewargs___impl (← fieldCx j "z")
    return encPy (fun p => Json.arr #[encDbl p.1, encDbl p.2]) (.ok r)
  | "cx_repr" => return encPy toJson (.ok (complex_repr Dbl.dblToString (← fieldCx j "z")))
  | "cx_format" =>
    let spec ← (← field j "spec").getArr?
    let spec ← spec.toList.mapM Json.getNat?
    return encPy toJson (complex___format___impl Dbl.dblToString advanced (← fieldCx j "z") spec)
  | "cx_hash" =>
    let ptr ← getInt j "ptr"
    return encPy toJson (.ok (complex_hash (hashDbl ptr) (← fieldCx j "z")))
  | "cx_cmp" =>
    let op : CmpOp ← match ← getStr j "op" with
      | "eq" => pure .eq | "ne" => pure .ne | "lt" => pure .lt
      | "le" => pure .le | "gt" => pure .gt | "ge" => pure .ge
      | o => throw s!"bad op {o}"
    return encPy encOptBool (.ok (complex_richcompare (← fieldCx j "z") (← fieldObj j "w") op))
  | "cx_new" =>
    let args ← (← field j "args").getArr?
    let args ← args.toList.mapM (decObj 4)
    let kw ← (← field j "kw").getArr?
    let kw ← kw.toList.mapM fun p => do
      let a ← p.getArr?
      return ((← (a.getD 0 .null).getStr?), (← decObj 4 (a.getD 1 .null)))
    return Json.mkObj [("ok", (encM encMade
      (actual_complex_new E (← getType j) args kw)).getObjValD "ok")]
  | "cx_from_number" =>
    return encM encMade (complex_from_number_impl E (← getType j) (← fieldObj j "o"))
  | "cx_real_as" => return encM encDbl (PyComplex_RealAsDouble E (← fieldObj j "o"))
  | "cx_imag_as" => return encM encDbl (PyComplex_ImagAsDouble E (← fieldObj j "o"))
  | "cx_as_c" => return encM encCx (PyComplex_AsCComplex E (← fieldObj j "o"))
  | "cx_from_c" => return encPy encMade (.ok (PyComplex_FromCComplex (← fieldCx j "z")))
  | "cx_from_d" =>
    let z ← fieldCx j "z"
    return encPy encMade (.ok (PyComplex_FromDoubles z.real z.imag))
  | "cx_parse" =>
    let cps ← (← field j "s").getArr?
    let cps ← cps.toList.mapM Json.getNat?
    return encPy encCx (complex_from_str E.db E.sd cps (← getStr j "repr"))
  | "cx_parse_float" =>
    let cps ← (← field j "s").getArr?
    let cps ← cps.toList.mapM Json.getNat?
    return encPy encDbl (float_from_str E.db E.sd cps (← getStr j "repr"))
  | "cx_c_sum" | "cx_c_diff" | "cx_c_prod" | "cx_c_quot" | "cx_c_pow" =>
    let a ← fieldCx j "a"
    let b ← fieldCx j "b"
    let L := libm (← getHy j)
    let r : Cx Dbl × Errno := match fn with
      | "cx_c_sum" => (c_sum a b, .ok)
      | "cx_c_diff" => (c_diff a b, .ok)
      | "cx_c_prod" => (c_prod a b, .ok)
      | "cx_c_quot" => c_quot a b .ok
      | _ => c_pow L a b .ok
    return encPy (fun p => Json.arr #[encCx p.1, toJson (errnoNum p.2)]) (.ok r)
  | "cx_c_neg" => return encPy encCx (.ok (c_neg (← fieldCx j "z")))
  | "cx_c_abs" =>
    let L := libm (← getHy j)
    let r := c_abs L (← fieldCx j "z") .ok
    return encPy (fun p => Json.arr #[encDbl p.1, toJson (errnoNum p.2)]) (.ok r)
  | "cx_c_powi" =>
    -- `complex_pow` on an integral exponent, kept separate so the report shows it
    let L := libm (← getHy j)
    return encPy encCx (complex_pow_core L (← fieldCx j "a") (← fieldCx j "b"))
  | _ => throw s!"unknown fn {fn}"

end DiffComplex

/-- The complex handler; `none` for a name it does not own. -/
def runComplex (fn : String) (j : Json) : Option (Except String Json) :=
  if fn.startsWith "cx_" then some (DiffComplex.run fn j) else none

end PyLean.LongObj
