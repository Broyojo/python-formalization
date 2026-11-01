import PyLean.DiffCore
import PyLean.LongObj.BoolObj

/-! Differential-testing handler for `longobj` cases (`"mod": "longobj"`). -/

namespace PyLean.LongObj

open Lean PyLean PyLean.Diff

/-- The Python value of an object, with its normal form checked: `ok` carries the
value only when the digits are the canonical ones for that value. -/
def encLong (x : Long) : Json :=
  if x = Long.ofInt x.toInt then toJson x.toInt else Json.mkObj [("noncanonical", toJson x.toInt)]

def encLongs (p : Long × Long) : Json := Json.arr #[encLong p.1, encLong p.2]

/-- `Py` of a digit-level result, with `cOverflow` reported as a harness failure. -/
def encResult {α : Type} (enc : α → Json) (r : Py α) : Except String Json :=
  match r with
  | .error (.named "COverflow" _) => throw "C overflow in model"
  | .error .modelFuel => throw "model fuel exhausted"
  | r => .ok (encPy enc r)

def getLong (j : Json) (key : String) : Except String Long := do
  return Long.ofInt (← getInt j key)

def bitFn : String → Option BitOp
  | "and" => some .and
  | "or" => some .or
  | "xor" => some .xor
  | _ => none

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "add" => encResult encLong (longAdd (← getLong j "a") (← getLong j "b"))
  | "sub" => encResult encLong (longSub (← getLong j "a") (← getLong j "b"))
  | "mul" => encResult encLong (longMul false (← getLong j "a") (← getLong j "b"))
  | "square" =>
    let a ← getLong j "a"
    encResult encLong (longMul true a a)
  | "divmod" => encResult encLongs (lDivmod (← getLong j "a") (← getLong j "b"))
  | "floordiv" => encResult encLong (longDiv (← getLong j "a") (← getLong j "b"))
  | "mod" => encResult encLong (longMod (← getLong j "a") (← getLong j "b"))
  | "rshift" => encResult encLong (longRshift (← getLong j "a") (← getLong j "b"))
  | "lshift" => encResult encLong (longLshift (← getLong j "a") (← getLong j "b"))
  | "and" | "or" | "xor" =>
    match bitFn fn with
    | some op => encResult encLong (longBit op (← getLong j "a") (← getLong j "b"))
    | none => throw "unreachable"
  | "invert" => encResult encLong (longInvert (← getLong j "a"))
  | "neg" => return encPy encLong (.ok (longNeg (← getLong j "a")))
  | "abs" => return encPy encLong (.ok (longAbs (← getLong j "a")))
  | "bool" => return encPy toJson (.ok (longBool (← getLong j "a")))
  | "pow" =>
    match longPowNone (← getInt j "a") (← getInt j "b") with
    | some r => return encPy toJson (.ok r)
    | none => throw "negative exponent has no integer model"
  | "powmod" =>
    encResult toJson (longPowMod (← getInt j "a") (← getInt j "b") (← getInt j "c"))
  | "from_c" =>
    let a ← getInt j "a"
    return encPy encLong (.ok (if 0 ≤ a then fromCUInt a.toNat else fromCInt a))
  | "as_long_overflow" =>
    let r := asLongAndOverflow (← getLong j "a")
    return encPy (fun (p : Int × Int) => Json.arr #[toJson p.1, toJson p.2]) (.ok r)
  | "as_long" => encResult toJson (asLong (← getLong j "a"))
  | "as_int" => encResult toJson (asCInt (← getLong j "a"))
  | "as_ssize" => encResult toJson (asSsize (← getLong j "a"))
  | "as_ulong" => encResult toJson (asUnsignedLong (← getLong j "a"))
  | "as_size_t" => encResult toJson (asSizeT (← getLong j "a"))
  | "as_mask" => return encPy toJson (.ok (asUnsignedMask (← getLong j "a")))
  | "get_sign" => return encPy toJson (.ok (longSign (← getLong j "a")))
  | "bit_length" => return encPy toJson (.ok (numBits (← getLong j "a")))
  | "bit_count" => return encPy toJson (.ok (bitCount (← getLong j "a")))
  | "hash" => return encPy toJson (.ok (longHash (← getLong j "a")))
  | "bool_repr" => return encPy toJson (.ok (boolRepr (← getBool j "a")))
  | "bool_invert" => encResult toJson (boolInvert false (← getBool j "a"))
  | "bool_op" =>
    let operand (key : String) : Except String BoolOperand := do
      match ← field j key with
      | .bool b => return .b b
      | v => return .i (← v.getInt?)
    let enc : BoolOperand → Json := fun
      | .b x => toJson x
      | .i x => toJson x
    match bitFn (← getStr j "op") with
    | some op => encResult enc (boolOp op (← operand "a") (← operand "b"))
    | none => throw "bad op"
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.LongObj
