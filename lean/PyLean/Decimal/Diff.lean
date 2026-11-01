import PyLean.DiffCore
import PyLean.Decimal.Parse
import PyLean.Decimal.Arith
import PyLean.Decimal.Tuple
import PyLean.Decimal.Format
import PyLean.Decimal.Quantize

/-! Differential-testing handler for `decimal` cases (`"mod": "decimal"`).

A function name ending in `_py` is checked against `_pydecimal`, one ending
in `_c` against `_decimal`; the context operations (`op`) use the
`_pydecimal` model for both (`"impl"` names the twin).

Encodings: a decimal is `["F", neg, "<coeff digits>", exp]`, `["I", neg]` or
`["N", neg, signaling, "<payload digits>"]` (digit strings, because Python's
`json` cannot print ints past 4300 digits); strings and format specs are
lists of code points; a context is
`{"prec", "rounding", "emin", "emax", "clamp", "traps": [names]}`; a tuple
item is `{"i": n}`, `{"b": bool}`, `{"s": str}` or `null` (other object). -/

namespace PyLean.Decimal

open Lean PyLean PyLean.Diff

def natOfStr (s : String) : Nat := s.toList.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

def natOfHex (s : String) : Nat := s.toList.foldl (fun a c =>
  a * 16 + (if c.toNat ≥ 97 then c.toNat - 87 else c.toNat - 48)) 0

/-- An int as `hex(i)` (Python's `json` cannot print ints past 4300 digits). -/
def hexInt (i : Int) : Json :=
  toJson (String.ofList ((if i < 0 then ['-'] else []) ++ ['0', 'x'] ++ Nat.toDigits 16 i.natAbs))

def encDec : Dec → Json
  | .fin n c e => Json.arr #[toJson "F", toJson n, toJson (String.ofList (Nat.toDigits 10 c)), toJson e]
  | .inf n => Json.arr #[toJson "I", toJson n]
  | .nan n s p => Json.arr #[toJson "N", toJson n, toJson s, toJson (String.ofList (Nat.toDigits 10 p))]

def decDec (j : Json) : Except String Dec := do
  let a ← j.getArr?
  let k ← (a.getD 0 Json.null).getStr?
  match k with
  | "F" => return .fin (← (a.getD 1 Json.null).getBool?) (natOfStr (← (a.getD 2 Json.null).getStr?)) (← (a.getD 3 Json.null).getInt?)
  | "I" => return .inf (← (a.getD 1 Json.null).getBool?)
  | "N" => return .nan (← (a.getD 1 Json.null).getBool?) (← (a.getD 2 Json.null).getBool?) (natOfStr (← (a.getD 3 Json.null).getStr?))
  | _ => throw s!"bad dec {k}"

def getDec (j : Json) (key : String) : Except String Dec := do decDec (← field j key)

def getCps (j : Json) (key : String) : Except String (List Nat) := do
  let a ← (← field j key).getArr?
  a.toList.mapM (·.getNat?)

def getChars (j : Json) (key : String) : Except String (List Char) := do
  return (← getCps j key).map Char.ofNat

def encStr (s : List Char) : Json := toJson (s.map Char.toNat)

def roundingOf : String → Except String Rounding
  | "ROUND_UP" => pure .up | "ROUND_DOWN" => pure .down
  | "ROUND_CEILING" => pure .ceiling | "ROUND_FLOOR" => pure .floor
  | "ROUND_HALF_UP" => pure .halfUp | "ROUND_HALF_DOWN" => pure .halfDown
  | "ROUND_HALF_EVEN" => pure .halfEven | "ROUND_05UP" => pure .r05up
  | s => throw s!"bad rounding {s}"

def signalOf : String → Except String Signal
  | "Clamped" => pure .clamped | "InvalidOperation" => pure .invalidOperation
  | "DivisionByZero" => pure .divisionByZero | "Inexact" => pure .inexact
  | "Rounded" => pure .rounded | "Subnormal" => pure .subnormal
  | "Overflow" => pure .overflow | "Underflow" => pure .underflow
  | s => throw s!"bad signal {s}"

def getCtx (j : Json) : Except String Ctx := do
  let c ← field j "ctx"
  let traps ← (← c.getObjVal? "traps").getArr?
  return {
    prec := ← (← c.getObjVal? "prec").getNat?
    rounding := ← roundingOf (← (← c.getObjVal? "rounding").getStr?)
    emin := ← (← c.getObjVal? "emin").getInt?
    emax := ← (← c.getObjVal? "emax").getInt?
    clamp := (← (← c.getObjVal? "clamp").getNat?) == 1
    traps := ← traps.toList.mapM (fun t => do signalOf (← t.getStr?)) }

def flagNames (fl : List Signal) : Json :=
  let names := fl.map Signal.name
  toJson (names.toArray.qsort (· < ·))

def encDM (r : Py (Dec × List Signal)) : Json :=
  encPy (fun (p : Dec × List Signal) => Json.arr #[encDec p.1, flagNames p.2]) r

def getPyVal (j : Json) : Except String PyVal :=
  match j with
  | .null => pure .other
  | _ => do
    match j.getObjVal? "i" with
    | .ok v => return .int (← v.getInt?)
    | .error _ =>
    match j.getObjVal? "b" with
    | .ok v => return .bool (← v.getBool?)
    | .error _ => return .str (← (← j.getObjVal? "s").getStr?)

def encPyVal : PyVal → Json
  | .int v => Json.mkObj [("i", toJson v)]
  | .bool b => Json.mkObj [("b", toJson b)]
  | .str s => Json.mkObj [("s", toJson s)]
  | .other => Json.null

def getTuple (j : Json) : Except String (PyVal × Option (List PyVal) × PyVal) := do
  let s ← getPyVal (← field j "sign")
  let ds ← match ← field j "digits" with
    | .null => pure none
    | d => do pure (some (← (← d.getArr?).toList.mapM getPyVal))
  let e ← getPyVal (← field j "exp")
  return (s, ds, e)

def encOutcome : FmtOutcome → Json
  | .accepted => toJson "ok"
  | .valueError => toJson "ValueError"
  | .unicodeEncodeError => toJson "UnicodeEncodeError"

def roundOf (m : String) : Except String Rounding :=
  match m with
  | "int" => pure .down | "floor" => pure .floor | "ceil" => pure .ceiling
  | "round" => pure .halfEven | _ => throw s!"bad int mode {m}"

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "parse_py" => return encPy encDec (pyParse (← getChars j "s"))
  | "parse_c" => return encPy encDec (cParse (← getChars j "s"))
  | "str_py" => return encPy encStr (pyStr (← getDec j "a"))
  | "str_c" => return encPy encStr (.ok (toSci (← getDec j "a")) : Py (List Char))
  | "tuple_py" =>
    let (s, ds, e) ← getTuple j
    return encPy encStr (pyFromTuple s ds e >>= (pyStrObj ·))
  | "tuple_c" =>
    let (s, ds, e) ← getTuple j
    return encPy encStr ((toSci ·) <$> cFromTuple s ds e)
  | "as_tuple" =>
    let (s, ds, e) := asTuple (← getDec j "a")
    return Json.mkObj [("ok", Json.arr #[encPyVal s, Json.arr (ds.map encPyVal).toArray, encPyVal e])]
  | "hash_py" => return encPy (fun o => match o with | some h => toJson h | none => Json.null) (pyHash (← getDec j "a"))
  | "hash_c" => return encPy (fun o => match o with | some h => toJson h | none => Json.null) (cHash (← getDec j "a"))
  | "int_py" =>
    let m ← getStr j "mode"
    let a ← getDec j "a"
    let r ← if m = "int" then pure (pyInt a) else do pure (pyToInt (← roundOf m) a)
    return encPy (fun i => hexInt i) r
  | "int_c" =>
    let m ← getStr j "mode"
    return encPy (fun i => hexInt i) (cToInt (← roundOf m) (← getDec j "a"))
  | "ratio_py" => return encPy (fun (p : Int × Int) => Json.arr #[hexInt p.1, hexInt p.2]) (pyRatio (← getDec j "a"))
  | "ratio_c" => return encPy (fun (p : Int × Int) => Json.arr #[hexInt p.1, hexInt p.2]) (cRatio (← getDec j "a"))
  | "fromint_py" => return encPy encDec (pyFromInt (Int.ofNat (natOfHex (← getStr j "n")) * (if ← getBool j "neg" then -1 else 1)))
  | "fromint_c" => return encPy encDec (cFromInt (Int.ofNat (natOfHex (← getStr j "n")) * (if ← getBool j "neg" then -1 else 1)))
  | "fmt_py" => return Json.mkObj [("ok", encOutcome (pyFormat (← getCps j "spec")))]
  | "fmt_c" =>
    let lib : LibMpdec := if (← getStr j "libmpdec") == "2" then .bundled251 else .system401
    return Json.mkObj [("ok", encOutcome (cFormat lib (← getCps j "spec")))]
  | "op" =>
    let c ← getCtx j
    let a ← getDec j "a"
    let b ← getDec j "b"
    let op ← getStr j "op"
    let r2 ← match (j.getObjVal? "rounding2") with
      | .ok (.str s) => some <$> roundingOf s
      | _ => pure none
    let n ← getInt j "n"
    let m : DM Dec := match op with
      | "add" => add c a b
      | "sub" => sub c a b
      | "mul" => mul c a b
      | "quantize" => quantize c a b r2
      | "tiv" => toIntegralValue c a r2
      | "tie" => toIntegralExact c a r2
      | "roundn" => roundN c a n
      | "normalize" => normalize c a
      | "fix" => fix c a
      | _ => throw (.named "harness" op)
    return encDM (m.run [])
  | "quantspec" =>
    let m ← roundingOf (← getStr j "rounding")
    let neg ← getBool j "neg"
    let co := natOfStr (← getStr j "c")
    let e ← getInt j "e"
    let qe ← getInt j "qe"
    return Json.mkObj [("ok", toJson (String.ofList (Nat.toDigits 10 (quantSpec m neg co e qe))))]
  | "compare_total" => return Json.mkObj [("ok", toJson (compareTotal (← getDec j "a") (← getDec j "b")))]
  | "copy_sign" => return Json.mkObj [("ok", encDec (copySign (← getDec j "a") (← getDec j "b")))]
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Decimal
