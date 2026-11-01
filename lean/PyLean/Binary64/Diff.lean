import PyLean.DiffCore
import PyLean.Binary64.Model
import PyLean.Binary64.Dtoa

/-! Differential-testing handler for `binary64` cases (`"mod": "binary64"`). -/

namespace PyLean.Binary64

open Lean PyLean PyLean.Diff

/-- A float travels as its 64-bit pattern, and a NaN result as the string "nan",
since hardware NaN payloads are not part of the model. -/
def encF (x : F64) : Json :=
  if x.isNaN then Json.str "nan" else toJson x.bits

def getF (j : Json) (key : String) : Except String F64 := do
  return F64.ofBits (← getNat j key)

/-- The platform `pow`, for difftesting `float_pow` only. No property uses it. -/
def libmPow (a b : F64) : F64 :=
  F64.ofBits (Float.pow (Float.ofBits a.bits.toUInt64) (Float.ofBits b.bits.toUInt64)).toBits.toNat

def getObj (j : Json) (key : String) : Except String Obj := do
  let o ← field j key
  match o.getObjVal? "f", o.getObjVal? "i", o.getObjVal? "o" with
  | .ok v, _, _ => return .float (F64.ofBits (← v.getNat?))
  | _, .ok v, _ => return .int (← v.getInt?)
  | _, _, .ok v => return .other (← v.getStr?) none none
  | _, _, _ => throw "bad object"

def getNats (j : Json) (key : String) : Except String (List Nat) := do
  let a ← (← field j key).getArr?
  a.toList.mapM (·.getNat?)

def getOp (j : Json) : Except String CmpOp := do
  match ← getStr j "op" with
  | "lt" => return .lt | "le" => return .le | "eq" => return .eq
  | "ne" => return .ne | "gt" => return .gt | "ge" => return .ge
  | o => throw s!"bad op {o}"

def encOptF : Option F64 → Json
  | none => Json.str "NotImplemented"
  | some x => encF x

def encPair : Option (F64 × F64) → Json
  | none => Json.str "NotImplemented"
  | some (a, b) => Json.arr #[encF a, encF b]

def encPow : Option PowResult → Json
  | none => Json.str "NotImplemented"
  | some (.float x) => encF x
  | some (.complexPow ..) => Json.str "complex"

def encStr (b : List Nat) : Json := Json.str (String.ofList (b.map Char.ofNat))

def fuelOut : Json := Json.mkObj [("harness", toJson "model fuel")]

def runFloat (fn : String) (j : Json) : Except String Json := do
  let v := getObj j "v"
  let w := getObj j "w"
  let x := getF j "x"
  match fn with
  | "f_add" => return encPy encOptF (float_add (← v) (← w))
  | "f_sub" => return encPy encOptF (float_sub (← v) (← w))
  | "f_mul" => return encPy encOptF (float_mul (← v) (← w))
  | "f_div" => return encPy encOptF (float_div (← v) (← w))
  | "f_rem" => return encPy encOptF (float_rem (← v) (← w))
  | "f_floordiv" => return encPy encOptF (float_floor_div (← v) (← w))
  | "f_divmod" => return encPy encPair (float_divmod (← v) (← w))
  | "f_pow" => return encPy encPow (float_pow libmPow (← v) (← w) none)
  | "f_cmp" =>
    let r := float_richcompare (← x) (← w) (← getOp j)
    return Json.mkObj [("ok", match r with | none => Json.str "NotImplemented" | some b => toJson b)]
  | "f_hash" =>
    return Json.mkObj [("ok", match float_hash (← x) with | none => Json.null | some h => toJson h)]
  | "f_is_integer" => return Json.mkObj [("ok", toJson (float_is_integer (← x)))]
  | "f_trunc" => return encPy toJson (float_trunc (← x))
  | "f_floor" => return encPy toJson (float_floor (← x))
  | "f_ceil" => return encPy toJson (float_ceil (← x))
  | "f_round0" => return encPy toJson (float_round_int (← x))
  | "f_round" => return encPy encF (float_round_ndigits (← x) (← getInt j "n"))
  | "f_hex" => return Json.mkObj [("ok", toJson (float_hex (← x)))]
  | "f_fromhex" => return encPy encF (float_fromhex (← getNats j "b"))
  | "f_ratio" =>
    return encPy (fun p => Json.arr #[toJson p.1, toJson p.2]) (float_as_integer_ratio (← x))
  | "pack2" => return encPy toJson (PyFloat_Pack2 (← x) (← getBool j "le"))
  | "pack4" => return encPy toJson (PyFloat_Pack4 (← x) (← getBool j "le"))
  | "pack8" => return encPy toJson (PyFloat_Pack8 (← x) (← getBool j "le"))
  | "unpack2" =>
    return Json.mkObj [("ok", toJson (PyFloat_Unpack2 (← getNats j "b") (← getBool j "le")).bits)]
  | "unpack4" =>
    return Json.mkObj [("ok", toJson (PyFloat_Unpack4 (← getNats j "b") (← getBool j "le")).bits)]
  | "unpack8" =>
    return Json.mkObj [("ok", toJson (PyFloat_Unpack8 (← getNats j "b") (← getBool j "le")).bits)]
  | "repr" =>
    match float_repr (← x) with
    | none => return fuelOut
    | some r => return Json.mkObj [("ok", encStr r)]
  | "fmt" =>
    let c ← getNat j "code"
    let fl : DtsFlags := { sign := ← getBool j "sign", add_dot_0 := ← getBool j "dot0"
                           alt := ← getBool j "alt", no_neg_0 := ← getBool j "z" }
    match PyOS_double_to_string (← x) c (← getInt j "p") fl with
    | none => return fuelOut
    | some r => return Json.mkObj [("ok", encStr (render r.1))]
  | "parse" =>
    let arg : StrArg :=
      match j.getObjVal? "cps" with
      | .ok _ => .str ((getNats j "cps").toOption.getD [])
      | .error _ => .bytes ((getNats j "bytes").toOption.getD [])
    return encPy encF (PyFloat_FromString arg)
  | "getformat" => return encPy toJson (float_getformat (← getStr j "t"))
  | "asdouble" => return encPy encF (PyFloat_AsDouble (← v))
  | "info" =>
    let i := PyFloat_GetInfo
    return Json.mkObj [("ok", Json.arr #[toJson i.max.bits, toJson i.max_exp, toJson i.max_10_exp,
      toJson i.min.bits, toJson i.min_exp, toJson i.min_10_exp, toJson i.dig, toJson i.mant_dig,
      toJson i.epsilon.bits, toJson i.radix, toJson i.rounds])]
  | _ => throw s!"unknown fn {fn}"

def runRaw (fn : String) (j : Json) : Except String Json := do
  let a := getF j "x"
  let b := getF j "y"
  let c := getF j "z"
  let f1 (g : F64 → F64) : Except String Json := do return encF (g (← a))
  let f2 (g : F64 → F64 → F64) : Except String Json := do return encF (g (← a) (← b))
  let p2 (g : F64 → F64 → Bool) : Except String Json := do return toJson (g (← a) (← b))
  match fn with
  | "add" => f2 F64.add
  | "sub" => f2 F64.sub
  | "mul" => f2 F64.mul
  | "div" => f2 F64.div
  | "fma" => return encF (F64.fma (← a) (← b) (← c))
  | "sqrt" => f1 F64.sqrt
  | "fmod" => f2 F64.fmod
  | "eq" => p2 F64.eq
  | "ne" => p2 F64.ne
  | "lt" => p2 F64.lt
  | "le" => p2 F64.le
  | "gt" => p2 F64.gt
  | "ge" => p2 F64.ge
  | "floor" => f1 F64.floor
  | "ceil" => f1 F64.ceil
  | "trunc" => f1 F64.trunc
  | "roundAway" => f1 F64.roundAway
  | "neg" => f1 F64.neg
  | "abs" => f1 F64.abs
  | "copysign" => f2 F64.copysign
  | "nextafter" => f2 F64.nextafter
  | "ulp" => f1 F64.ulp
  | "frexp" =>
    let (m, e) := F64.frexp (← a)
    return Json.arr #[encF m, toJson e]
  | "ldexp" => return encF (F64.ldexp (← a) (← getInt j "n"))
  | "ofInt" => return encF (F64.ofInt (← getInt j "n"))
  | "ratio" =>
    return encF (F64.ofRat ((← getInt j "n") / ((← getInt j "d") : Rat)))
  | _ => throw s!"unknown fn {fn}"

def run (fn : String) (j : Json) : Except String Json := do
  if fn.startsWith "f_" || ["pack2", "pack4", "pack8", "unpack2", "unpack4", "unpack8", "repr",
      "fmt", "parse", "getformat", "asdouble", "info"].contains fn then
    runFloat fn j
  else
    return Json.mkObj [("ok", ← runRaw fn j)]

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Binary64
