import PyLean.DiffCore
import PyLean.CoreLibs.Coll.Counter

/-! Differential-testing handler for `corelibs` cases with `"fn": "coll.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `coll.` prefix.

Keys in the cases are strings, counts are ints; a dict or a `Counter` is a list of
`[key, value]` pairs in insertion order. -/

namespace PyLean.CoreLibs.Coll

open Lean PyLean PyLean.Diff

/-- `repr` of the short strings the generator uses as keys. -/
def rkStr (s : String) : String := "'" ++ s ++ "'"

def jArr (j : Json) : Except String (List Json) := do
  match j with
  | .arr a => return a.toList
  | _ => throw "expected array"

def decPair (j : Json) : Except String (String × Int) := do
  match ← jArr j with
  | [k, v] => return (← k.getStr?, ← v.getInt?)
  | _ => throw "expected pair"

def getItems (j : Json) (key : String) : Except String (Ctr String) := do
  (← jArr (← field j key)).mapM decPair

def getStrs (j : Json) (key : String) : Except String (List String) := do
  (← jArr (← field j key)).mapM Json.getStr?

def encItems (c : Ctr String) : Json :=
  Json.arr (c.map (fun p => Json.arr #[toJson p.1, toJson p.2])).toArray

def encStrs (l : List String) : Json := Json.arr (l.map toJson).toArray

def okJ (j : Json) : Json := Json.mkObj [("ok", j)]
def okE (c : Ctr String) : Json := okJ (encItems c)
def okI (i : Int) : Json := okJ (toJson i)
def okS (s : String) : Json := okJ (toJson s)

/-- `{"src": "none"|"mapping"|"iter", "items"|"xs": ...}`. -/
def getSrc (j : Json) : Except String (Src String) := do
  match ← getStr j "src" with
  | "none" => return .none
  | "mapping" => return .mapping (← getItems j "items")
  | "iter" => return .iter (← getStrs j "xs")
  | s => throw s!"bad src {s}"

/-- The `b` operand of an in-place operator. -/
def getIOpnd (j : Json) : Except String (IOpnd String) := do
  match ← getStr j "bty" with
  | "Counter" => return .ctr (← getItems j "b")
  | "dict" => return .dict (← getItems j "b")
  | ty => return .nonmapping ty

/-- A binary dunder: a `Counter` right operand, or `b` absent. -/
def binop (j : Json) (opname : String) (f : Ctr String → Ctr String → Ctr String) : Except String Json := do
  let a ← getItems j "a"
  match j.getObjVal? "b" with
  | .ok .null | .error _ =>
    return encPy encItems (.error (.typeError
      s!"unsupported operand type(s) for {opname}: 'Counter' and 'int'"))
  | .ok _ => return encPy encItems (.ok (f a (← getItems j "b")))

/-- A rich comparison. `__eq__`/`__ne__` on a non-`Counter` fall back to identity,
ordering raises. -/
def cmpop (j : Json) (opname : String) (f : Ctr String → Ctr String → Bool) : Except String Json := do
  let a ← getItems j "a"
  match j.getObjVal? "b" with
  | .ok .null | .error _ =>
    if opname == "==" then return encPy toJson (.ok false)
    else if opname == "!=" then return encPy toJson (.ok true)
    else return encPy (fun (b : Bool) => toJson b) (.error (.typeError
      s!"'{opname}' not supported between instances of 'Counter' and 'int'"))
  | .ok _ => return encPy (fun (b : Bool) => toJson b) (.ok (f a (← getItems j "b")))

def runCtr (j : Json) : Except String Json := do
  let op ← getStr j "op"
  match op with
  | "new" => return okE (counterNew (← getSrc j) (← getItems j "kw"))
  | "update" => return okE (update (← getItems j "a") (← getSrc j) (← getItems j "kw"))
  | "subtract" => return okE (subtract (← getItems j "a") (← getSrc j) (← getItems j "kw"))
  | "count_py" => return okE (countElementsPy (← getItems j "a") (← getStrs j "xs"))
  | "count_c" => return okE (countElements (← getItems j "a") (← getStrs j "xs"))
  | "count_slow" => return okE (countElementsCSlow (← getItems j "a") (← getStrs j "xs"))
  | "total" => return okI (total (← getItems j "a"))
  | "most_common" => return encPy encItems (mostCommon (← getItems j "a") (← getOptInt j "n"))
  | "elements" => return encPy encStrs (elements (← getItems j "a"))
  | "copy" => return okE (counterCopy (← getItems j "a"))
  | "reduce" => return okE (counterReduce (← getItems j "a"))
  | "delitem" => return okE (delitem (← getItems j "a") (← getStr j "e"))
  | "getitem" => return okI (cGet (← getItems j "a") (← getStr j "e"))
  | "repr" => return okS (counterRepr "Counter" rkStr (← getItems j "a"))
  | "fromkeys" => return encPy encItems (counterFromkeys (← getStrs j "xs") none)
  | "keep_positive" => return okE (keepPositive (← getItems j "a"))
  | "pos" => return okE (posC (← getItems j "a"))
  | "neg" => return okE (negC (← getItems j "a"))
  | "add" => binop j "+" addC
  | "sub" => binop j "-" subC
  | "or" => binop j "|" orC
  | "and" => binop j "&" andC
  | "eq" => cmpop j "==" eqC
  | "ne" => cmpop j "!=" neC
  | "le" => cmpop j "<=" leC
  | "lt" => cmpop j "<" ltC
  | "ge" => cmpop j ">=" geC
  | "gt" => cmpop j ">" gtC
  | "iadd" => return encPy encItems (dunderIadd (← getItems j "a") (← getIOpnd j))
  | "isub" => return encPy encItems (dunderIsub (← getItems j "a") (← getIOpnd j))
  | "ior" => return encPy encItems (dunderIor (← getItems j "a") (← getIOpnd j))
  | "iand" => return encPy encItems (dunderIand rkStr (← getItems j "a") (← getIOpnd j))
  | _ => throw s!"unknown ctr op {op}"

def run (fn : String) (j : Json) : Except String Json :=
  match fn with
  | "ctr" => runCtr j
  | _ => throw s!"unknown fn coll.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Coll
