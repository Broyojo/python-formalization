import PyLean.DiffCore
import PyLean.MathInt.Model
import PyLean.MathInt.IntOps

/-! Differential-testing handler for `mathint` cases (`"mod": "mathint"`). -/

namespace PyLean.MathInt

open Lean PyLean PyLean.Diff

def getIntList (j : Json) (key : String) : Except String (List Int) := do
  let arr ← (← field j key).getArr?
  arr.toList.mapM (·.getInt?)

def getNatList (j : Json) (key : String) : Except String (List Nat) := do
  let arr ← (← field j key).getArr?
  arr.toList.mapM (·.getNat?)

def encNat (n : Nat) : Json := toJson n
def encInt (n : Int) : Json := toJson n
def encPair (p : Int × Int) : Json := Json.arr #[toJson p.1, toJson p.2]
def encBytes (bs : List Nat) : Json := Json.arr (bs.map toJson).toArray

/-- An exception described by a case, `{"exc": cls, "msg": m}`. -/
def getExc (j : Json) : Except String PyExc :=
  return .named (← getStr j "exc") (← getStr j "msg")

/-- The `int.from_bytes` argument of a `from_bytes_obj` case: which route of
`int_from_bytes_impl` the Python object takes, and what that step yields. -/
def getBytesObj (j : Json) : Except String BytesObj := do
  let yielded : Py (List Nat) ←
    match j.getObjVal? "fail" with
    | .ok e => do let x ← getExc e; pure (Except.error x)
    | .error _ => do let bs ← getNatList j "bytes"; pure (Except.ok bs)
  match ← getStr j "route" with
  | "exact" => match yielded with
    | .ok bs => return .exact bs
    | .error _ => throw "exact bytes cannot fail"
  | "buffer" => return .buffer yielded
  | "other" => return .other yielded
  | r => throw s!"unknown route {r}"

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "isqrt" => return encPy encNat (isqrt (← getInt j "n"))
  | "comb" => return encPy encNat (comb (← getInt j "n") (← getInt j "k"))
  | "perm" => return encPy encNat (perm (← getInt j "n") (← getOptInt j "k"))
  | "factorial" => return encPy encNat (factorial (← getInt j "n"))
  | "gcd" => return encPy encInt (gcd (← getIntList j "args"))
  | "lcm" => return encPy encInt (lcm (← getIntList j "args"))
  | "pow" => return encPy encInt (powMod (← getInt j "a") (← getInt j "b") (← getInt j "m"))
  | "to_bytes" =>
    return encPy encBytes (toBytes (← getInt j "v") (← getInt j "length")
      (← getStr j "byteorder") (← getBool j "signed"))
  | "from_bytes" =>
    return encPy encInt (fromBytes (← getNatList j "bytes") (← getStr j "byteorder")
      (← getBool j "signed"))
  | "from_bytes_obj" =>
    let ctor : Int → Py Int ←
      match j.getObjVal? "ctor_fail" with
      | .ok e => do let e ← getExc e; pure (fun _ => .error e)
      | .error _ => pure .ok
    return encPy encInt (fromBytesImpl ctor (← getBytesObj j) (← getStr j "byteorder")
      (← getBool j "signed"))
  | "divmod" => return encPy encPair (divmod (← getInt j "a") (← getInt j "b"))
  | "round" => return encPy encInt (.ok (roundInt (← getInt j "x") (← getOptInt j "nd")) : Py Int)
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.MathInt
