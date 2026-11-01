import PyLean.DiffCore
import PyLean.CoreLibs.Coll.UserDict

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

/-! ### `ChainMap` -/

abbrev CM := CMap String Int

def getMaps (j : Json) : Except String CM := do
  let ms ← jArr (← field j "maps")
  return ⟨← ms.mapM (fun m => do (← jArr m).mapM decPair)⟩

def encCM (c : CM) : Json := Json.arr (c.maps.map encItems).toArray

def encPair (p : String × Int) : Json := Json.arr #[toJson p.1, toJson p.2]

def rvInt (v : Int) : String := toString v

/-- `coll_CMMiss.__missing__` returns -1; plain `ChainMap` raises. -/
def cmMiss (j : Json) : String → Py Int :=
  match j.getObjVal? "sub" with
  | .ok (.num 1) => fun _ => .ok (-1)
  | _ => cmMissing rkStr

def optOther (j : Json) : Except String (Option (Ctr String)) :=
  match j.getObjVal? "o" with
  | .ok .null | .error _ => .ok none
  | .ok _ => some <$> getItems j "o"

def runCM (j : Json) : Except String Json := do
  let op ← getStr j "op"
  let c ← getMaps j
  let miss := cmMiss j
  let k := (j.getObjVal? "k" >>= Json.getStr?).toOption.getD ""
  let dflt ← getOptInt j "d"
  match op with
  | "new" => return okJ (encCM (cmNew c.maps))
  | "getitem" => return encPy toJson (cmGetitem miss c k)
  | "get" => return encPy (fun (o : Option Int) => toJson o) (cmGet miss c k dflt)
  | "len" => return okI (cmLen c)
  | "iter" => return okJ (encStrs (cmIter c))
  | "contains" => return okJ (toJson (cmContains c k))
  | "bool" => return okJ (toJson (cmBool c))
  | "repr" => return okS (cmRepr "ChainMap" rkStr rvInt c)
  | "fromkeys" => return okJ (encCM (cmFromkeys (← getStrs j "xs") (dflt.getD 0)))
  | "copy" => return encPy encCM (cmCopy c)
  | "new_child" =>
    let m ← optOther j
    return okJ (encCM (cmNewChild c m (← getItems j "kw")))
  | "parents" => return okJ (encCM (cmParents c))
  | "setitem" => return encPy encCM (cmSetitem c k (dflt.getD 0))
  | "delitem" => return encPy encCM (cmDelitem rkStr c k)
  | "popitem" => return encPy (fun r => Json.arr #[encPair r.1, encCM r.2]) (cmPopitem c)
  | "pop" => return encPy (fun r => Json.arr #[toJson r.1, encCM r.2]) (cmPop rkStr c k dflt)
  | "clear" => return encPy encCM (cmClear c)
  | "ior" => return encPy encCM (cmIor c (← getItems j "o"))
  | "or" =>
    match cmOr c (← optOther j) with
    | some r => return encPy encCM r
    | none => return encPy encCM (.error (.typeError
        "unsupported operand type(s) for |: 'ChainMap' and 'int'"))
  | "ror" =>
    match cmRor c (← optOther j) with
    | some r => return okJ (encCM r)
    | none => return encPy encCM (.error (.typeError
        "unsupported operand type(s) for |: 'int' and 'ChainMap'"))
  | _ => throw s!"unknown cm op {op}"

/-! ### `UserDict` -/

abbrev U := UD String Int

def udClass (j : Json) : Except String (String × Option (String → Int)) := do
  match ← getNat j "sub" with
  | 0 => return ("UserDict", none)
  | 1 => return ("coll_UDPlain", none)
  | _ => return ("coll_UDMiss", some (fun _ => -1))

def encUD (u : U) : Json := Json.arr #[toJson u.cls, encItems u.data]

def getUOpnd (j : Json) : Except String (UOpnd String Int) := do
  match ← getStr j "oty" with
  | "user" => return .user (← getItems j "o")
  | "dict" => return .dict (← getItems j "o")
  | _ => return .other

def runUD (j : Json) : Except String Json := do
  let op ← getStr j "op"
  let (cls, miss) ← udClass j
  let u : U := ⟨cls, ← getItems j "a"⟩
  let k := (j.getObjVal? "k" >>= Json.getStr?).toOption.getD ""
  let dflt ← getOptInt j "d"
  let nop : String → Except String Json := fun sym =>
    return encPy encUD (.error (.typeError s!"unsupported operand type(s) for |: {sym}"))
  match op with
  | "new" =>
    let src ← optOther j
    return okJ (encUD (udNew cls src (← getItems j "kw")))
  | "len" => return okI (udLen u)
  | "getitem" => return encPy toJson (udGetitem rkStr miss u k)
  | "setitem" => return okJ (encUD (udSetitem u k (dflt.getD 0)))
  | "delitem" => return encPy encUD (udDelitem rkStr u k)
  | "iter" => return okJ (encStrs (udIter u))
  | "contains" => return okJ (toJson (udContains u k))
  | "get" => return encPy (fun (o : Option Int) => toJson o) (udGet rkStr miss u k dflt)
  | "repr" => return okS (udRepr rkStr rvInt u)
  | "or" =>
    match udOr u (← getUOpnd j) with
    | some r => return okJ (encUD r)
    | none => nop s!"'{cls}' and 'int'"
  | "ror" =>
    match udRor u (← getUOpnd j) with
    | some r => return okJ (encUD r)
    | none => nop s!"'int' and '{cls}'"
  | "ior" => return okJ (encUD (udIor u (← getItems j "o")))
  | "copy" => return okJ (encUD (udCopy u))
  | "copy_dunder" => return okJ (encUD (udCopyDunder u))
  | "fromkeys" => return okJ (encUD (udFromkeys cls (← getStrs j "xs") (dflt.getD 0)))
  | "pop" => return encPy (fun r => Json.arr #[toJson r.1, encUD r.2]) (udPop rkStr miss u k dflt)
  | "popitem" => return encPy (fun r => Json.arr #[encPair r.1, encUD r.2]) (udPopitem rkStr miss u)
  | "setdefault" =>
    let r := udSetdefault rkStr miss u k (dflt.getD 0)
    return okJ (Json.arr #[toJson r.1, encUD r.2])
  | "clear" => return okJ (encUD (udClear rkStr miss u))
  | "items_contains" => return okJ (toJson (udItemsContains rkStr miss u k (dflt.getD 0)))
  | "dict_getitem" => return encPy toJson (dictGetitem rkStr miss u.data k)
  | "dict_pop" => return encPy (fun r => Json.arr #[toJson r.1, encItems r.2]) (dictPop rkStr u.data k dflt)
  | "dict_popitem" => return encPy (fun r => Json.arr #[encPair r.1, encItems r.2]) (dictPopitem u.data)
  | "dict_setdefault" =>
    let r := dictSetdefault u.data k (dflt.getD 0)
    return okJ (Json.arr #[toJson r.1, encItems r.2])
  | "dict_items_contains" => return okJ (toJson (dictItemsContains u.data k (dflt.getD 0)))
  | _ => throw s!"unknown ud op {op}"

def run (fn : String) (j : Json) : Except String Json :=
  match fn with
  | "ctr" => runCtr j
  | "cm" => runCM j
  | "ud" => runUD j
  | _ => throw s!"unknown fn coll.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Coll
