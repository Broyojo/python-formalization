import PyLean.DiffCore
import PyLean.LongObj.IntNew
import PyLean.LongObj.DiffComplex
import PyLean.LongObj.LongFloat
import PyLean.LongObj.DiffStr
import PyLean.LongObj.Compare
import PyLean.LongObj.Binop
import PyLean.LongObj.AsByteArray

/-! Differential-testing handler for `longobj` cases (`"mod": "longobj"`). -/

namespace PyLean.LongObj

open Lean PyLean PyLean.Diff

/-- The Python value of an object, with its normal form checked: `ok` carries the
value only when the digits are the canonical ones for that value. -/
def encCanon (x : Long) : Json :=
  if x = Long.ofInt x.toInt then toJson x.toInt else Json.mkObj [("noncanonical", toJson x.toInt)]

def encCanons (p : Long × Long) : Json := Json.arr #[encCanon p.1, encCanon p.2]

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
  | "add" => encResult encCanon (longAdd (← getLong j "a") (← getLong j "b"))
  | "sub" => encResult encCanon (longSub (← getLong j "a") (← getLong j "b"))
  | "mul" => encResult encCanon (longMul false (← getLong j "a") (← getLong j "b"))
  | "compact" =>
    -- What a specialized BINARY_OP does: the compact function, and the generic slot
    -- when that declines.
    let a ← getLong j "a"
    let b ← getLong j "b"
    let (fast, slow) := match (← getStr j "op") with
      | "add" => (compactAdd a b, longAdd a b)
      | "sub" => (compactSub a b, longSub a b)
      | _ => (compactMul a b, longMul false a b)
    match fast with
    | some r => encResult encCanon (.ok r)
    | none => encResult encCanon slow
  | "square" =>
    let a ← getLong j "a"
    encResult encCanon (longMul true a a)
  | "divmod" => encResult encCanons (lDivmod (← getLong j "a") (← getLong j "b"))
  | "floordiv" => encResult encCanon (longDiv (← getLong j "a") (← getLong j "b"))
  | "mod" => encResult encCanon (longMod (← getLong j "a") (← getLong j "b"))
  | "rshift" => encResult encCanon (longRshift (← getLong j "a") (← getLong j "b"))
  | "lshift" => encResult encCanon (longLshift (← getLong j "a") (← getLong j "b"))
  | "and" | "or" | "xor" =>
    match bitFn fn with
    | some op => encResult encCanon (longBit op (← getLong j "a") (← getLong j "b"))
    | none => throw "unreachable"
  | "invert" => encResult encCanon (longInvert (← getLong j "a"))
  | "neg" => return encPy encCanon (.ok (longNeg (← getLong j "a")))
  | "abs" => return encPy encCanon (.ok (longAbs (← getLong j "a")))
  | "bool" => return encPy toJson (.ok (longBool (← getLong j "a")))
  | "pow" =>
    match longPowNone (← getInt j "a") (← getInt j "b") with
    | some r => return encPy toJson (.ok r)
    | none => throw "negative exponent has no integer model"
  | "powmod" =>
    encResult toJson (longPowMod (← getInt j "a") (← getInt j "b") (← getInt j "c"))
  | "as_longlong" => encResult toJson (asLongLong (← getLong j "a"))
  | "as_ulonglong" => encResult toJson (asUnsignedLongLong (← getLong j "a"))
  | "void_ptr" => encResult toJson (asVoidPtr (← getLong j "a"))
  | "native" =>
    let a ← getInt j "a"
    let n ← getNat j "n"
    let r := asNativeRes (Long.ofInt a) n (← getBool j "ub")
    return encPy id (.ok (Json.arr #[toJson r, toJson (a % 2 ^ (8 * n)).toNat]))
  | "fixed" =>
    let a ← getInt j "a"
    let n ← getNat j "n"
    let ub ← getBool j "ub"
    let name := if ub then s!"C uint{8 * n}_t" else s!"C int{8 * n}_t"
    encResult (fun _ => toJson a) (toFixed (Long.ofInt a) n ub name)
  | "int_new" =>
    let ops : IntOps Int := {
      numberLong := fun
        | .str s | .bytes s | .other s => .ok s
      asSsize := fun b => .ok b
      fromUnicode := fun _ _ => .error (.named "Unreached" "~")
      fromBytes := fun _ _ => .error (.named "Unreached" "~") }
    let kind ← getStr j "kind"
    let x : Option (IntArg Int) ← match kind with
      | "none" => pure none
      | "str" => pure (some (.str 0))
      | "other" => pure (some (.other (← getInt j "x")))
      | _ => throw "bad kind"
    encResult toJson (longNew ops x (← getOptInt j "base"))
  | "from_native" =>
    let bs ← (← (← field j "bs").getArr?).toList.mapM (fun v => v.getNat?)
    let flags ← getInt j "flags"
    if ← getBool j "unsigned" then encResult toJson (fromUnsignedNativeBytes bs flags)
    else encResult toJson (fromNativeBytes bs flags)
  | "true_div" =>
    encResult (fun d : Cplx.Dbl => toJson d.bits) (trueDivide (← getLong j "a") (← getLong j "b"))
  | "as_double" => encResult (fun d : Cplx.Dbl => toJson d.bits) (longFloat (← getLong j "a"))
  | "from_double" => encResult toJson (fromDouble ⟨← getNat j "bits"⟩)
  | "true_div_round" =>
    let a ← getInt j "a"
    let b ← getInt j "b"
    return encPy toJson (.ok (Cplx.Dbl.roundQ (decide (a < 0) != decide (b < 0)) a.natAbs b.natAbs).bits)
  | "as_double_round" =>
    let a ← getInt j "a"
    return encPy toJson (.ok (Cplx.Dbl.roundQ (decide (a < 0)) a.natAbs 1).bits)
  | "from_c" =>
    let a ← getInt j "a"
    return encPy encCanon (.ok (if 0 ≤ a then fromCUInt a.toNat else fromCInt a))
  | "as_long_overflow" =>
    let r := asLongAndOverflow (← getLong j "a")
    return encPy (fun (p : Int × Int) => Json.arr #[toJson p.1, toJson p.2]) (.ok r)
  | "as_longlong_overflow" =>
    let r := asLongLongAndOverflow (← getLong j "a")
    return encPy (fun (p : Int × Int) => Json.arr #[toJson p.1, toJson p.2]) (.ok r)
  | "byte_array_w" =>
    let n ← getNat j "n"
    let r := asByteArrayW (← getLong j "a") n true false
    let buf := r.stored ++ List.replicate (n - r.stored.length) 170
    return encPy toJson (.ok (MathInt.bytesVal buf))
  | "richcmp" =>
    let a ← getLong j "a"
    let selfArg : RichArg := .int (if (← getBool j "same") then 1 else 0) a
    let otherArg : RichArg ← if (← getBool j "other") then pure (.other 1) else do
      pure (.int 1 (← getLong j "b"))
    let enc : RichOut → Json := fun
      | .notImplemented => toJson "NI"
      | .bool b => toJson b
    let rs := [RichOp.lt, .le, .eq, .ne, .gt, .ge].map (fun op => enc (longRichcompare selfArg otherArg op))
    return encPy id (.ok (Json.arr rs.toArray))
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
  | "sizeof" => return encPy toJson (.ok (intSizeof (← getLong j "a")))
  | "ratio" =>
    let a ← getLong j "a"
    let r := asIntegerRatio a
    let ints : List Long := [r.1, r.2, longLong a, longGet0, longLong a, longGet1, longLong a]
      ++ getNewArgs a
    let vals : List Json := (ints.map (fun x => toJson x.toInt)) ++ [toJson (isInteger a)]
    return encPy id (.ok (Json.arr vals.toArray))
  | "int_info" => return encPy toJson (.ok intInfo)
  | "bool_repr" => return encPy toJson (.ok (boolRepr (← getBool j "a")))
  | "bool_invert" => encResult toJson (boolInvert false (← getBool j "a"))
  | "bool_op" =>
    let operand (key : String) : Except String BoolOperand := do
      match ← field j key with
      | .bool b => return .b b
      | v => return .i (← v.getInt?)
    let enc : Option BoolOperand → Json := fun
      | some (.b x) => toJson x
      | some (.i x) => toJson x
      | some .other | none => Json.null
    match bitFn (← getStr j "op") with
    | some op => encResult enc (boolOp op (← operand "a") (← operand "b"))
    | none => throw "bad op"
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j =>
  match runComplex fn j with
  | some r => some r
  | none =>
    match runStr fn j with
    | some r => some r
    | none => some (run fn j)

end PyLean.LongObj
