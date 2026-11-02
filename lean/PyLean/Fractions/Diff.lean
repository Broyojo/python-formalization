import PyLean.DiffCore
import PyLean.Fractions.Format
import PyLean.Fractions.CtorOne

/-! Differential-testing handler for `fractions` cases (`"mod": "fractions"`).

A Fraction is `[numerator, denominator]` (built on the Python side with
`Fraction(n, d)`, so the Lean side normalizes with `ofInts` first). Ints with
more than 1000 digits travel as `{"hex": "-0x..."}` because Python's `json`
cannot print them past the int string-conversion limit. -/

namespace PyLean.Fractions

open Lean PyLean PyLean.Diff

def bigThreshold : Nat := 10 ^ 1000

def encInt (i : Int) : Json :=
  if i.natAbs ≥ bigThreshold then
    Json.mkObj [("hex", toJson (String.ofList
      ((if i < 0 then ['-'] else []) ++ ['0', 'x'] ++ Nat.toDigits 16 i.natAbs)))]
  else toJson i

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def decodeInt (j : Json) : Except String Int :=
  match j.getInt? with
  | .ok i => .ok i
  | .error _ => do
    let s ← (← j.getObjVal? "hex").getStr?
    let (neg, body) := match s.toList with
      | '-' :: r => (true, r)
      | r => (false, r)
    let digits := body.drop 2
    let v ← digits.foldlM (fun acc c => match hexVal c with
      | some d => .ok (acc * 16 + d)
      | none => .error s!"bad hex {s}") 0
    return if neg then -(v : Int) else v

def getBig (j : Json) (key : String) : Except String Int := do decodeInt (← j.getObjVal? key)

def encFrac (x : Frac) : Json := Json.arr #[encInt x.num, encInt x.den]

def encStr (s : List Char) : Json := toJson (String.ofList s)

/-- A Fraction argument, normalized as `Fraction(n, d)` would. -/
def getFrac (j : Json) (key : String) : Except String (Py Frac) := do
  let arr ← (← j.getObjVal? key).getArr?
  let some a := arr[0]? | throw s!"{key}: missing numerator"
  let some b := arr[1]? | throw s!"{key}: missing denominator"
  return ofInts (← decodeInt a) (← decodeInt b)

/-- A pair of ints, or `null`. -/
def optPair (j : Json) : Except String (Option (Int × Int)) := do
  match j with
  | .null => return none
  | _ =>
    let arr ← j.getArr?
    let some a := arr[0]? | throw "pair: missing first"
    let some b := arr[1]? | throw "pair: missing second"
    return some (← decodeInt a, ← decodeInt b)

/-- `"ratio"`: `null`, `[n, d]`, or `{"exc": class, "msg": message}`. -/
def getRatio (j : Json) : Except String (Option (Py (Int × Int))) := do
  match j.getObjVal? "exc" with
  | .ok cls => return some (.error (.named (← cls.getStr?) (← (← j.getObjVal? "msg").getStr?)))
  | .error _ => return (optPair j).toOption.join.map .ok

def getCtorArg (j : Json) : Except String CtorArg := do
  let v ← j.getObjVal? "arg"
  let exact ← v.getObjVal? "int"
  return {
    exactInt := if exact.isNull then none else (decodeInt exact).toOption
    isFloat := ← getBool v "float"
    isType := ← getBool v "type"
    ratio := ← getRatio (← v.getObjVal? "ratio")
    str := (getStr v "str").toOption.map String.toList
    rational := ← optPair (← v.getObjVal? "rational") }

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "ctor1" => return encPy encFrac (ofOne (← getCtorArg j))
  | "ctor" => return encPy encFrac (ofInts (← getBig j "n") (← getBig j "d"))
  | "parse" => return encPy encFrac (parse (← getStr j "s").toList)
  | "decimal" =>
    return encPy encFrac (.ok (ofDecimal (← getBool j "neg") (← getNat j "coeff") (← getInt j "exp")))
  | "dechash" =>
    return encPy toJson (.ok (decimalHash (← getBool j "neg") (← getNat j "coeff") (← getInt j "exp")) : Py Int)
  | _ =>
  let x ← getFrac j "a"
  match fn with
  | "str" => return encPy encStr (x >>= str)
  | "format" => do
    let spec := (← getStr j "spec").toList
    return encPy encStr (x >>= (format · spec))
  | "floor" => return encPy encInt (floor <$> x)
  | "ceil" => return encPy encInt (ceil <$> x)
  | "trunc" => return encPy encInt (trunc <$> x)
  | "int" => return encPy encInt (toInt <$> x)
  | "round" => return encPy encInt (round <$> x)
  | "round_nd" => do
    let nd ← getInt j "nd"
    return encPy encFrac (x >>= (roundTo · nd))
  | "hash" => return encPy encInt (hash <$> x)
  | "limit" => do
    let m ← getBig j "m"
    return encPy encFrac (x >>= (limitDenominator · m))
  | "is_integer" => return encPy toJson (isInteger <$> x)
  | "ratio" => return encPy (fun (r : Int × Int) => Json.arr #[encInt r.1, encInt r.2]) (asIntegerRatio <$> x)
  | "pow" => do
    let e ← getInt j "e"
    return encPy encFrac (x >>= (pow · e))
  | "neg" => return encPy encFrac (neg <$> x)
  | "abs" => return encPy encFrac (abs <$> x)
  | _ =>
  let y ← getFrac j "b"
  let bin {α : Type} (f : Frac → Frac → Py α) : Py α := do f (← x) (← y)
  match fn with
  | "add" => return encPy encFrac (bin fun a b => .ok (add a b))
  | "sub" => return encPy encFrac (bin fun a b => .ok (sub a b))
  | "mul" => return encPy encFrac (bin fun a b => .ok (mul a b))
  | "truediv" => return encPy encFrac (bin div)
  | "floordiv" => return encPy encInt (bin floordiv)
  | "mod" => return encPy encFrac (bin mod)
  | "divmod" => return encPy (fun (r : Int × Frac) => Json.arr #[encInt r.1, encFrac r.2]) (bin divmod)
  | "eq" => return encPy toJson (bin fun a b => .ok (eq a b))
  | "lt" => return encPy toJson (bin fun a b => .ok (lt a b))
  | "le" => return encPy toJson (bin fun a b => .ok (le a b))
  | "gt" => return encPy toJson (bin fun a b => .ok (gt a b))
  | "ge" => return encPy toJson (bin fun a b => .ok (ge a b))
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Fractions
