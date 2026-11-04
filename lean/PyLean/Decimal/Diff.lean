import PyLean.DiffCore
import PyLean.Decimal.Parse
import PyLean.Decimal.Arith
import PyLean.Decimal.Tuple
import PyLean.Decimal.Format
import PyLean.Decimal.RoundTrip
import PyLean.Decimal.MulProps
import PyLean.Decimal.Ops
import PyLean.Decimal.Quantize
import PyLean.Decimal.ContextDiff
import PyLean.Decimal.Convert

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
  | "Fh" =>
    let e := intOfHex (← (a.getD 3 Json.null).getStr?)
    return .fin (← (a.getD 1 Json.null).getBool?) (natOfStr (← (a.getD 2 Json.null).getStr?)) e
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
  | "FloatOperation" => pure .floatOperation
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

def jDec {α : Type} (m : DM α) (enc : α → Json) : DM Json := enc <$> m
def jD (m : DM Dec) : DM Json := jDec m encDec
def jB (m : DM Bool) : DM Json := jDec m toJson
def pureJ (v : Json) : DM Json := pure v

/-- The methods checked generically: `Decimal` methods under a context. -/
def evalM (c : Ctx) (name : String) (a b t : Dec) (isC : Bool := false) : Option (DM Json) :=
  match name with
  | "neg" => some (jD (dunderNeg c a))
  | "pos" => some (jD (dunderPos c a))
  | "abs" => some (jD (dunderAbs c a))
  | "copy_abs" => some (pureJ (encDec (copyAbs a)))
  | "copy_negate" => some (pureJ (encDec (copyNegate a)))
  | "bool" => some (pureJ (toJson (decBool a)))
  | "adjusted" => some (pureJ (toJson a.adjusted))
  | "is_nan" => some (pureJ (toJson (isNanP a)))
  | "is_qnan" => some (pureJ (toJson (isQnan a)))
  | "is_snan" => some (pureJ (toJson (isSnan a)))
  | "is_infinite" => some (pureJ (toJson (isInfinite a)))
  | "is_finite" => some (pureJ (toJson (isFinite a)))
  | "is_signed" => some (pureJ (toJson (isSigned a)))
  | "is_zero" => some (pureJ (toJson (isZero a)))
  | "is_canonical" => some (pureJ (toJson (isCanonical a)))
  | "is_normal" => some (pureJ (toJson (isNormal c a)))
  | "is_subnormal" => some (pureJ (toJson (isSubnormal c a)))
  | "number_class" => some (pureJ (toJson (numberClass c a)))
  | "same_quantum" => some (pureJ (toJson (sameQuantum a b)))
  | "radix" => some (pureJ (encDec radixD))
  | "canonical" => some (pureJ (encDec (canonicalD a)))
  | "conjugate" => some (pureJ (encDec (conjugateD a)))
  | "real" => some (pureJ (encDec (realD a)))
  | "imag" => some (pureJ (encDec (imagD a)))
  | "eq" => some (jB (dunderEq c a b))
  | "lt" => some (jB (dunderLt c a b))
  | "le" => some (jB (dunderLe c a b))
  | "gt" => some (jB (dunderGt c a b))
  | "ge" => some (jB (dunderGe c a b))
  | "compare" => some (jD (compareD c a b))
  | "compare_signal" => some (jD (compareSignal c a b))
  | "compare_total_mag" => some (pureJ (toJson (compareTotalMag a b)))
  | "max" => some (jD (maxD c a b))
  | "min" => some (jD (minD c a b))
  | "max_mag" => some (jD (maxMag c a b))
  | "min_mag" => some (jD (minMag c a b))
  | "logb" => some (jD (logb c a))
  | "logical_and" => some (jD (logicalAnd c a b))
  | "logical_or" => some (jD (logicalOr c a b))
  | "logical_xor" => some (jD (logicalXor c a b))
  | "logical_invert" => some (jD (logicalInvert c a))
  | "rotate" => some (jD (rotate c a b))
  | "shift" => some (jD (shift c a b))
  | "scaleb" => some (jD (scaleb c a b))
  | "next_minus" => some (jD (nextMinus c a))
  | "next_plus" => some (jD (nextPlus c a))
  | "next_toward" => some (jD (nextToward c a b))
  | "fma" => some (jD (fma c a b t))
  | "truediv" => some (jD (truediv c a b))
  | "floordiv" => some (jD ((if isC then floordivC else floordivD) c a b))
  | "mod" => some (jD (modD c a b))
  | "divmod" => some (jDec ((if isC then divmodC else divmodD) c a b) (fun p => Json.arr #[encDec p.1, encDec p.2]))
  | "remainder_near" => some (jD (remainderNear c a b))
  | "to_eng_string" => some (if isC then pureJ (encStr (toEng a c.capitals)) else jDec (liftPy (pyEng a c.capitals)) encStr)
  | "repr" => some (if isC then pureJ (encStr (reprD a)) else jDec (liftPy (pyRepr a)) encStr)
  | _ => none

def argOf (j : Json) : Except String Arg := do
  let a ← j.getArr?
  match ← (a[0]!).getStr? with
  | "dec" => return .dec (← decDec a[1]!)
  | "int" => return .int ((← (a[1]!).getStr?).toInt?.getD 0)
  | "tuple" => return .tuple (← (← (a[1]!).getArr?).toList.mapM strKindOf)
  | _ => return .other (← strKindOf (a.getD 1 Json.null))

def jOptD (m : DM (Option Dec)) : DM Json :=
  jDec m (fun o => match o with
    | some d => encDec d
    | none => Json.null)

/-- `Context` methods, by name. `evalC c name a b t` runs `c.name(a, b, t)`. -/
def evalC (c : Ctx) (name : String) (a b t : Arg) (isC : Bool) : Option (DM Json) :=
  match name with
  | "add" => some (jD (contextAdd c a b))
  | "subtract" => some (jD (contextSubtract c a b))
  | "multiply" => some (jD (contextMultiply c a b))
  | "divide" => some (jD (contextDivide c a b))
  | "divide_int" => some (jD (if isC then ctxOp floordivC c a b else contextDivideInt c a b))
  | "divmod" => some (jDec (if isC then ctxOp divmodC c a b else contextDivmod c a b)
      (fun p => Json.arr #[encDec p.1, encDec p.2]))
  | "remainder" => some (jD (contextRemainder c a b))
  | "compare" => some (jD (contextCompare c a b))
  | "compare_signal" => some (jD (contextCompareSignal c a b))
  | "max" => some (jD (contextMax c a b))
  | "max_mag" => some (jD (contextMaxMag c a b))
  | "min" => some (jD (contextMin c a b))
  | "min_mag" => some (jD (contextMinMag c a b))
  | "logical_and" => some (jD (contextLogicalAnd c a b))
  | "logical_or" => some (jD (contextLogicalOr c a b))
  | "logical_xor" => some (jD (contextLogicalXor c a b))
  | "next_toward" => some (jD (contextNextToward c a b))
  | "quantize" => some (jD (contextQuantize c a b))
  | "remainder_near" => some (jD (contextRemainderNear c a b))
  | "rotate" => some (jD (contextRotate c a b))
  | "scaleb" => some (jD (contextScaleb c a b))
  | "shift" => some (jD (contextShift c a b))
  | "compare_total" => some (jD (contextCompareTotal c a b))
  | "compare_total_mag" => some (jD (contextCompareTotalMag c a b))
  | "copy_sign" => some (jD (contextCopySign c a b))
  | "same_quantum" => some (jB (contextSameQuantum c a b))
  | "fma" => some (jD (contextFma c a b t))
  | "abs" => some (jD (contextAbs c a))
  | "logb" => some (jD (contextLogb c a))
  | "logical_invert" => some (jD (contextLogicalInvert c a))
  | "minus" => some (jD (contextMinus c a))
  | "plus" => some (jD (contextPlus c a))
  | "next_minus" => some (jD (contextNextMinus c a))
  | "next_plus" => some (jD (contextNextPlus c a))
  | "normalize" => some (jD (contextNormalize c a))
  | "to_integral_exact" => some (jD (contextToIntegralExact c a))
  | "to_integral_value" => some (jD (contextToIntegralValue c a))
  | "number_class" => some (jDec (contextNumberClass c a) (fun (s : String) => toJson s))
  | "is_normal" => some (jB (contextIsNormal c a))
  | "is_subnormal" => some (jB (contextIsSubnormal c a))
  | "to_eng_string" => some (jDec (if isC then ctxUn (fun c a => (pure (toEng a c.capitals) : DM (List Char))) c a
      else contextToEngString c a) encStr)
  | "to_sci_string" => some (jDec (contextToSciString c a) encStr)
  | "copy_abs" => some (jD (contextCopyAbs c a))
  | "copy_negate" => some (jD (contextCopyNegate c a))
  | "copy_decimal" => some (jD (contextCopyDecimal c a))
  | "is_finite" => some (jB (contextIsFinite c a))
  | "is_infinite" => some (jB (contextIsInfinite c a))
  | "is_nan" => some (jB (contextIsNan c a))
  | "is_qnan" => some (jB (contextIsQnan c a))
  | "is_signed" => some (jB (contextIsSigned c a))
  | "is_snan" => some (jB (contextIsSnan c a))
  | "is_zero" => some (jB (contextIsZero c a))
  | "canonical" => some (jD (liftPy (if isC then ctxCanonicalC a else contextCanonical a)))
  | "is_canonical" => some (jB (liftPy (if isC then ctxIsCanonicalC a else contextIsCanonical a)))
  | "radix" => some (pureJ (encDec contextRadix))
  | _ => none

def evalR (c : Ctx) (name : String) (a : Dec) (b : Arg) (isC : Bool) : Option (DM Json) :=
  match name with
  | "__rsub__" => some (jOptD (rsub c a b))
  | "__rtruediv__" => some (jOptD (rtruediv c a b))
  | "__rmod__" => some (jOptD (rmod c a b))
  | "__rfloordiv__" => some (jOptD (if isC then ropArg floordivC c a b else rfloordiv c a b))
  | "__rdivmod__" => some (jDec (if isC then ropArg divmodC c a b else rdivmod c a b) (fun o => match o with
      | some p => Json.arr #[encDec p.1, encDec p.2]
      | none => Json.null))
  | _ => none

/-- A comparison operand: `["dec", d]`, `["rat", n, d]`, `["float", bits]`,
`["complex", rebits, imbits]` or `["other"]`. -/
def cmpArgOf (j : Json) : Except String CmpArg := do
  let a ← j.getArr?
  match ← (a[0]!).getStr? with
  | "dec" => return .dec (← decDec a[1]!)
  | "rat" => return .rat ((← (a[1]!).getStr?).toInt?.getD 0) (natOfStr (← (a[2]!).getStr?))
  | "float" => return .float (.ofBits (natOfStr (← (a[1]!).getStr?)))
  | "complex" => return .complex (.ofBits (natOfStr (← (a[1]!).getStr?))) (.ofBits (natOfStr (← (a[2]!).getStr?)))
  | _ => return .other

def encObjStr (o : PyObj) : Json :=
  match pyStrObj o with
  | .ok s => encStr s
  | .error _ => Json.null

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "rich" =>
    let c ← getCtx j
    let a ← getDec j "a"
    let b ← cmpArgOf (← field j "b")
    let r := match ← getStr j "op" with
      | "eq" => richEq c a b | "lt" => richLt c a b | "le" => richLe c a b
      | "gt" => richGt c a b | _ => richGe c a b
    return encPy (fun (p : Option Bool × List Signal) =>
      Json.arr #[(match p.1 with | some v => toJson v | none => Json.null), flagNames p.2]) (r.run [])
  | "fromfloat" => return encPy encDec (fromFloat (.ofBits (natOfStr (← getStr j "bits"))))
  | "new_py" =>
    let c ← getCtx j
    let arg ← match ← getStr j "k" with
      | "str" => pure (NewArg.str (← getChars j "s"))
      | "int" => pure (NewArg.int ((← getStr j "n").toInt?.getD 0))
      | "float" => pure (NewArg.float (.ofBits (natOfStr (← getStr j "bits"))))
      | "badrepr" => pure (NewArg.other (some (.named "RuntimeError" "boom")))
      | "hugeset" => pure (NewArg.other (intStrErr (10 ^ 5000)))
      | _ => pure (NewArg.other none)
    return encPy (fun (p : PyObj × List Signal) => Json.arr #[encObjStr p.1, flagNames p.2]) ((pyNew c arg).run [])
  | "pow10" =>
    return encPy (fun (p : Bool × Bool) => Json.arr #[toJson p.1, toJson p.2])
      (isLessThanPow10aUseStr (natOfStr (← getStr j "q")) (natOfStr (← getStr j "a")))
  | "parse_py" => return encPy encDec (pyParse (← getChars j "s"))
  | "parse_c" => return encPy encDec (cParse (← getChars j "s"))
  | "str_py" => return encPy encStr (pyStr (← getDec j "a"))
  | "str_c" => return encPy encStr (.ok (toSci (← getDec j "a")) : Py (List Char))
  | "eng_py" => return encPy encStr (pyEng (← getDec j "a"))
  | "eng_c" => return encPy encStr (.ok (toEng (← getDec j "a")) : Py (List Char))
  | "strrt_c" => return encPy encDec (cParse (toSci (← getDec j "a")))
  | "strrt_py" => return encPy encDec (pyStr (← getDec j "a") >>= pyParse)
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
  | "fmtarg_c" => return encPy toJson (.error (cFormatBadArg (← getStr j "arg")) : Py String)
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
  | "mulspec" =>
    let m ← roundingOf (← getStr j "rounding")
    let neg ← getBool j "neg"
    let co := natOfStr (← getStr j "c1") * natOfStr (← getStr j "c2")
    let r := roundPrec m neg co ((← getInt j "e1") + (← getInt j "e2")) (← getNat j "prec")
    return Json.mkObj [("ok", Json.arr #[toJson (String.ofList (Nat.toDigits 10 r.1)), toJson r.2])]
  | "m" =>
    let c ← getCtx j
    let a ← getDec j "a"
    let b ← getDec j "b"
    let t ← getDec j "t"
    let name ← getStr j "m"
    let isC := (j.getObjValAs? String "impl").toOption == some "c"
    let some r := evalM c name a b t isC | throw s!"unknown method {name}"
    return encPy (fun (p : Json × List Signal) => Json.arr #[p.1, flagNames p.2]) (r.run [])
  | "cm" =>
    let c ← getCtx j
    let a ← argOf (← field j "a")
    let b ← argOf (← field j "b")
    let t ← argOf (← field j "t")
    let name ← getStr j "m"
    let isC := (← getStr j "impl") == "c"
    let some r := evalC c name a b t isC | throw s!"unknown context method {name}"
    return encPy (fun (p : Json × List Signal) => Json.arr #[p.1, flagNames p.2]) (r.run [])
  | "rop" =>
    let c ← getCtx j
    let a ← getDec j "a"
    let b ← argOf (← field j "b")
    let name ← getStr j "m"
    let isC := (← getStr j "impl") == "c"
    let some r := evalR c name a b isC | throw s!"unknown reflected operator {name}"
    return encPy (fun (p : Json × List Signal) => Json.arr #[p.1, flagNames p.2]) (r.run [])
  | "ctxnew" =>
    let (py, cc) ← templateOf (← field j "tmpl")
    let init ← ctxInitOf (← field j "init")
    if (← getStr j "impl") == "py" then return encPy encPyContext (pyContextNew py init)
    else return encPy encCContext (cContextCall cc init)
  | "ctxset" =>
    let (py, cc) ← templateOf (← field j "tmpl")
    let name ← getStr j "name"
    let v ← ctxArgOf (← field j "val")
    if (← getStr j "impl") == "py" then return encPy encPyContext (pySetattr py name v)
    else return encPy encCContext (cSetattr cc name v)
  | "ctxdel" =>
    let name ← getStr j "name"
    if (← getStr j "impl") == "py" then return encPy (fun (_ : Unit) => Json.null) (pyDelattr name)
    else return encPy (fun (_ : Unit) => Json.null) (.error (.named "AttributeError" "context attributes cannot be deleted"))
  | "ctxrepr" =>
    let acts ← (← (← field j "acts").getArr?).toList.mapM (·.getStr?)
    if (← getStr j "impl") == "py" then return Json.mkObj [("ok", toJson (pyContextRepr (flagsAfterPy acts)))]
    else return Json.mkObj [("ok", toJson (contextReprC (noTrapsC (statusOfActs acts))))]
  | "sd" =>
    let acts ← (← (← field j "acts").getArr?).toList.mapM (·.getStr?)
    let bind_ ← (← field j "bound").getBool?
    let sd : SigObj := if bind_ then some (statusOfActs acts) else none
    let key ← sigKeyOf (← field j "key")
    let w : SdOperand ←
      match ← getStr j "w" with
      | "copy" | "copy_frozen" => pure (.dict (keyed (flagsAsDict (statusOfActs acts))))
      | "self" => pure (.sd sd)
      | "unbound" => pure (.sd none)
      | "other_ctx" =>
        let acts2 ← (← (← field j "acts2").getArr?).toList.mapM (·.getStr?)
        pure (.sd (some (statusOfActs acts2)))
      | "bad_dict" | "bad_frozen" => pure (.dict [(.other, { truth := true })])
      | _ => pure .other
    return runSd (← getStr j "op") sd key w
  | "ieee" =>
    let (py, cc) ← templateOf (← field j "tmpl")
    let v ← ctxArgOf (← field j "bits")
    if (← getStr j "impl") == "py" then
      match v with
      | .int n => return encPy encPyContext (ieeeContext py n)
      | _ => throw "ieee py needs an int"
    else return encPy encCContext (ieeeContextC cc v)
  | "local" =>
    let (py, cc) ← templateOf (← field j "tmpl")
    let kw ← (← (← field j "kw").getArr?).toList.mapM (fun p => do
      let q ← p.getArr?
      return ((← (q[0]!).getStr?), (← ctxArgOf q[1]!)))
    if (← getStr j "impl") == "py" then
      return encPy (fun (r : PyContext × Bool) => Json.arr #[encPyContext r.1, toJson r.2]) (do
        let base ← pyContextNew py {}
        let t : ThreadCtx := { current := some base }
        let (m, t1) ← localContext py t none kw
        let (m', t2, nc) ← managerEnter py m t1
        let t3 ← managerExit py m'
        let _ := t2
        return (nc, t3 == t))
    else
      return encPy (fun (r : CContext × Bool) => Json.arr #[encCContext r.1, toJson r.2]) (do
        let base ← cContextCall cc {}
        let t : CThread := { current := some base }
        let init ← cInitOfKwargs kw
        let (localCopy, global, t1) ← ctxmanagerNew cc t .none init
        let (_, nc) := ctxmanagerSetLocal localCopy
        let t3 := ctxmanagerRestoreGlobal global
        let _ := t1
        return (nc, t3 == t))
  | "compare_total" => return Json.mkObj [("ok", toJson (compareTotal (← getDec j "a") (← getDec j "b")))]
  | "copy_sign" => return Json.mkObj [("ok", encDec (copySign (← getDec j "a") (← getDec j "b")))]
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Decimal
