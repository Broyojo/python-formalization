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
  | "divmod" => return encPy encPair (divmod (← getInt j "a") (← getInt j "b"))
  | "round" => return encPy encInt (.ok (roundInt (← getInt j "x") (← getOptInt j "nd")) : Py Int)
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.MathInt
