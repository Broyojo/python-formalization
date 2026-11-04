import PyLean.DiffCore
import PyLean.Binary64.Model
import PyLean.Binary64.Dtoa
import PyLean.Binary64.Complex
import PyLean.Binary64.FloatObj

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

partial def getObj (j : Json) (key : String) : Except String Obj := do
  let o ← field j key
  match o.getObjVal? "f", o.getObjVal? "i", o.getObjVal? "o" with
  | .ok v, _, _ =>
    let x := F64.ofBits (← v.getNat?)
    match (o.getObjValAs? String "sub").toOption with
    | some t => return .floatSub t x
    | none => return .float x
  | _, .ok v, _ => return .int (← v.getInt?)
  | _, _, .ok v =>
    let t ← v.getStr?
    let fq := (o.getObjValAs? String "fq").toOption.getD t
    let ff : Option Obj ← match o.getObjVal? "ff" with
      | .ok _ => do let r ← getObj o "ff"; pure (some r)
      | .error _ => pure none
    let ix : Option Int ← match o.getObjVal? "ix" with
      | .ok w => do let i ← w.getInt?; pure (some i)
      | .error _ => pure none
    return .other t ff ix fq
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
  | "f_pow" =>
    let z : Option Obj := if (getBool j "z").toOption.getD false then some (.int 5) else none
    return encPy encPow (float_powE (fun a b => (libmPow a b, 0)) (← v) (← w) z)
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
  | "st_unpack" =>
    let b ← getNats j "b"
    let fmt ← getStr j "fmt"
    let r : F64 := match fmt.toList with
      | ['<', 'f'] | ['=', 'f'] | ['@', 'f'] => nu_float b
      | ['<', 'd'] | ['=', 'd'] | ['@', 'd'] => PyFloat_Unpack8 b true
      | [_, 'f'] => PyFloat_Unpack4 b false
      | _ => PyFloat_Unpack8 b false
    return Json.mkObj [("ok", toJson r.bits)]
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
  | "fmt_big" =>
    let fl : DtsFlags := {}
    match PyOS_double_to_string_checked (← x) (← getNat j "code") (← getInt j "p") fl with
    | .ok none => return fuelOut
    | .ok (some r) => return Json.mkObj [("ok", encStr (render r.1))]
    | .error e => return encPy encStr (.error e)
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

/-- `hypot` with correct rounding, for difftesting only. -/
def hypotExact (x y : F64) : F64 :=
  if x.isInf || y.isInf then F64.inf false
  else if x.isNaN || y.isNaN then F64.qnan
  else
    let q := x.toRat * x.toRat + y.toRat * y.toRat
    if q = 0 then F64.zero false
    else F64.sqrtRound q.num.natAbs (-(Nat.log2 q.den : Int))

def toFloat (x : F64) : Float := Float.ofBits x.bits.toUInt64
def ofFloat (x : Float) : F64 := F64.ofBits x.toBits.toNat

/-- The platform C library, for difftesting only. No property uses it. -/
def libm : Libm where
  hypot := hypotExact
  pow := libmPow
  atan2 a b := ofFloat (Float.atan2 (toFloat a) (toFloat b))
  exp a := ofFloat (Float.exp (toFloat a))
  log a := ofFloat (Float.log (toFloat a))
  cos a := ofFloat (Float.cos (toFloat a))
  sin a := ofFloat (Float.sin (toFloat a))
  trigEdom a := a.isInf

def getCObj (j : Json) (key : String) : Except String CObj := do
  let o ← field j key
  match o.getObjVal? "c" with
  | .ok v =>
    let a ← v.getArr?
    return .complex ⟨F64.ofBits (← (a.getD 0 Json.null).getNat?), F64.ofBits (← (a.getD 1 Json.null).getNat?)⟩
  | .error _ => return .real (← getObj j key)

def encC (z : C) : Json := Json.arr #[encF z.re, encF z.im]

def encOptC : Option C → Json
  | none => Json.str "NotImplemented"
  | some z => encC z

/-- A zero's sign can come from the sign of a NaN made inside `_Py_c_prod`, which is a
hardware choice the model does not make, so `**` results compare with zeros unsigned. -/
def encOptCPow : Option C → Json
  | none => Json.str "NotImplemented"
  | some z =>
    let u (x : F64) := if x.isZero then F64.zero false else x
    encC ⟨u z.re, u z.im⟩

def runComplex (fn : String) (j : Json) : Except String Json := do
  let v := getCObj j "v"
  let w := getCObj j "w"
  let z : Except String C := do
    match ← v with
    | .complex c => return c
    | .real _ => throw "complex expected"
  match fn with
  | "c_add" => return encPy encOptC (complex_add (← v) (← w))
  | "c_sub" => return encPy encOptC (complex_sub (← v) (← w))
  | "c_mul" => return encPy encOptC (complex_mul (← v) (← w))
  | "c_div" => return encPy encOptC (complex_div (← v) (← w))
  | "c_pow" => return encPy encOptCPow (complex_pow libm (← v) (← w))
  | "c_abs" => return encPy encF (complex_abs libm false (← z))
  | "c_neg" => return Json.mkObj [("ok", encC (complex_neg (← z)))]
  | "c_conj" => return Json.mkObj [("ok", encC (complex_conjugate (← z)))]
  | "c_bool" => return Json.mkObj [("ok", toJson (complex_bool (← z)))]
  | "c_eq" =>
    let r := complex_richcompare (← z) (← w) (← getOp j)
    return Json.mkObj [("ok", match r with | none => Json.str "NotImplemented" | some b => toJson b)]
  | "c_repr" =>
    match complex_repr (← z) with
    | none => return fuelOut
    | some r => return Json.mkObj [("ok", encStr r)]
  | "c_parse" => return encPy encC (complex_subtype_from_string (← getNats j "cps"))
  | _ => throw s!"unknown fn {fn}"

/-! ## Object-level float paths -/

def getExc (j : Json) : Except String PyExc := do
  let a ← j.getArr?
  let c ← (a.getD 0 Json.null).getStr?
  let m ← (a.getD 1 Json.null).getStr?
  return .named c m

partial def getFObjJ (o : Json) : Except String FObj := do
  let id ← o.getObjValAs? Nat "id"
  let k ← o.getObjVal? "k"
  let kind : FKind ←
    match k.getObjVal? "f", k.getObjVal? "i", k.getObjVal? "s", k.getObjVal? "b", k.getObjVal? "ba",
        k.getObjVal? "mv" with
    | .ok v, _, _, _, _, _ => pure (.float (F64.ofBits (← v.getNat?)))
    | _, .ok v, _, _, _, _ => pure (.int (← v.getInt?))
    | _, _, .ok v, _, _, _ => pure (.str ((← v.getArr?).toList.filterMap (·.getNat?.toOption)))
    | _, _, _, .ok v, _, _ => pure (.bytes ((← v.getArr?).toList.filterMap (·.getNat?.toOption)))
    | _, _, _, _, .ok v, _ => pure (.bytearray ((← v.getArr?).toList.filterMap (·.getNat?.toOption)))
    | _, _, _, _, _, .ok v => pure (.buffer ((← v.getArr?).toList.filterMap (·.getNat?.toOption)))
    | _, _, _, _, _, _ => pure .plain
  let ex ← o.getObjValAs? Bool "ex"
  let tp ← o.getObjValAs? String "tp"
  let fq ← o.getObjValAs? String "fq"
  let slot (key : String) : Except String (Option (Except PyExc FObj)) :=
    match o.getObjVal? key with
    | .error _ => pure none
    | .ok sj =>
      match sj.getObjVal? "err", sj.getObjVal? "ok" with
      | .ok e, _ => do return some (.error (← getExc e))
      | _, .ok r => do return some (.ok (← getFObjJ r))
      | _, _ => throw "bad slot"
  return .mk id kind ex tp fq (← slot "nf") (← slot "ni")

/-- A float subclass as the difftest builds it: `call` says what `cls(x)` does. -/
def getCls (j : Json) : Except String (Option FCls) := do
  match j.getObjVal? "cls" with
  | .error _ => return none
  | .ok c =>
    let name ← c.getObjValAs? String "name"
    let call ← c.getObjValAs? String "call"
    let f : F64 → Py FObj := match call with
      | "str" => fun _ => .ok (.mk 0 (.str [71, 33]) true "str" "str" none none)
      | "err" => fun _ => .error (.named "KeyError" "'new'")
      | _ => fun x => .ok (.mk 0 (.float x) false name ("m." ++ name) none none)
    return some { name, call := f }

def encFKind (o : FObj) : Json :=
  match o.kind with
  | .float x => Json.mkObj [("tp", toJson o.tp), ("f", toJson x.bits)]
  | _ => Json.mkObj [("tp", toJson o.tp)]

/-- A slot result with `id` 0 is an object the slot made itself (the inherited `float_float`
or `long_float`), which the Python side cannot tell from any other new float, so it
travels as `fresh`. -/
def encFRes : FRes → Json
  | .same x => Json.mkObj [("same", toJson x.bits)]
  | .obj o x => if o.id == 0 then Json.mkObj [("fresh", toJson x.bits)] else Json.mkObj [("obj", toJson o.id)]
  | .fresh x => Json.mkObj [("fresh", toJson x.bits)]
  | .freshSub c x => Json.mkObj [("sub", Json.arr #[toJson c, toJson x.bits])]
  | .called o => Json.mkObj [("called", encFKind o)]

def encRound : RoundRes → Json
  | .int n => Json.mkObj [("int", toJson n)]
  | .float x => Json.mkObj [("float", encF x)]

def runObj (fn : String) (j : Json) : Except String Json := do
  let w ← getBool j "warn"
  match fn with
  | "o_asdouble" => return encPy encF (asDoubleO w (← getFObjJ (← field j "v")))
  | "o_new" =>
    let args ← (← field j "args").getArr?
    let args ← args.toList.mapM getFObjJ
    let kw ← (← field j "kw").getArr?
    let kw ← kw.toList.mapM (·.getStr?)
    return encPy encFRes (floatVectorcall w (← getCls j) args kw)
  | "o_from_number" => return encPy encFRes (floatFromNumber w (← getCls j) (← getFObjJ (← field j "v")))
  | "o_fromhex" => return encPy encFRes (floatFromhexO (← getCls j) (← getFObjJ (← field j "v")))
  | "o_round" =>
    let o : Option FObj ← match j.getObjVal? "v" with
      | .ok v => (getFObjJ v).map some
      | .error _ => pure none
    return encPy encRound (floatRoundO w (F64.ofBits (← getNat j "x")) o)
  | "o_float" =>
    let x := F64.ofBits (← getNat j "x")
    let e ← getBool j "exact"
    return Json.mkObj [("ok", Json.arr #[encFRes (floatFloatO x e), encFRes (floatConjugateO x e),
      encFRes (floatGetrealO x e)])]
  | "o_getnewargs" =>
    return Json.mkObj [("ok", Json.arr ((floatGetnewargsO (F64.ofBits (← getNat j "x"))).map (fun y => toJson y.bits)).toArray)]
  | _ => throw s!"unknown fn {fn}"

def run (fn : String) (j : Json) : Except String Json := do
  if fn.startsWith "o_" then runObj fn j
  else if fn.startsWith "c_" then runComplex fn j
  else if fn.startsWith "f_" || ["pack2", "pack4", "pack8", "unpack2", "unpack4", "unpack8", "st_unpack", "repr", "fmt_big",
      "fmt", "parse", "getformat", "asdouble", "info"].contains fn then
    runFloat fn j
  else
    return Json.mkObj [("ok", ← runRaw fn j)]

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Binary64
