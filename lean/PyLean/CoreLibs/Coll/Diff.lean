import PyLean.DiffCore
import PyLean.CoreLibs.Coll.UserDict
import PyLean.CoreLibs.Coll.ChainMapG
import PyLean.CoreLibs.Coll.UserDictG
import PyLean.CoreLibs.Coll.ODictG
import PyLean.CoreLibs.Coll.UserListG2
import PyLean.CoreLibs.Coll.UserList
import PyLean.CoreLibs.Coll.UserString
import PyLean.CoreLibs.Coll.Namedtuple

/-! Differential-testing handler for `corelibs` cases with `"fn": "coll.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `coll.` prefix.

Keys in the cases are strings, counts are ints; a dict or a `Counter` is a list of
`[key, value]` pairs in insertion order. -/

namespace PyLean.CoreLibs.Coll

open Lean PyLean PyLean.Diff
open PyLean.StrSearch (Seq)

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

/-- A counter of the cases: string keys, int counts. -/
abbrev Ctr (κ : Type) := D κ Int

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

/-- String keys; `"#L"` stands for the unhashable list `[1]`. -/
def kStr : KOps String :=
  ⟨fun k => if k = "#L" then .error (.typeError "unhashable type: 'list'") else .ok (), fun _ => "list"⟩

/-- An exception as `[class, message]`, without the model's `~` marker. -/
def encExc (e : PyExc) : Json :=
  let m := e.message
  Json.arr #[toJson e.className, toJson (if m.startsWith "~" then m.drop 1 |>.toString else m)]

/-- A mutating method's outcome: `[state, null]` or `[state, [class, message]]`. -/
def encOut {σ : Type} (enc : σ → Json) (r : Out σ) : Json :=
  okJ (Json.arr #[enc r.1, match r.2 with | none => Json.null | some e => encExc e])

/-- An iterator over `xs` that raises `ValueError('boom')` instead of stopping when `fail`. -/
def getIt (j : Json) (key : String) : Except String (Py (FIt String)) := do
  let xs ← getStrs j key
  let fail := (j.getObjVal? "fail" >>= Json.getBool?).toOption.getD false
  return .ok ⟨xs, if fail then some (.valueError "boom") else none⟩

/-- `{"src": "none"|"mapping"|"iter", "mty": "dict"|"mapping"|"bad_items", ...}`. -/
def getSrc (j : Json) : Except String (Src String Int) := do
  match ← getStr j "src" with
  | "none" => return .none
  | "mapping" =>
    let items ← getItems j "items"
    match (j.getObjVal? "mty" >>= Json.getStr?).toOption.getD "dict" with
    | "dict" => return .mapping (dictSrc items)
    | "mapping" => return .mapping ⟨none, .ok (FIt.ofList items), .ok (D.keys items), (dictSrc items).getitem⟩
    | _ => return .mapping ⟨none, .error (.named "RuntimeError" "items"), .ok (D.keys items),
        (dictSrc items).getitem⟩
  | "iter" => return .iter (← getIt j "xs")
  | s => throw s!"bad src {s}"

/-- The `b` operand of an in-place operator. -/
def getIOpnd (j : Json) : Except String (IOpnd String Int) := do
  let b ← getItems j "b"
  match ← getStr j "bty" with
  | "Counter" => return ctrOpnd kStr intNum b
  | "dict" => return dictOpnd kStr rkStr b
  | ty => return ⟨.error (.named "AttributeError" s!"'{ty}' object has no attribute 'items'"),
      fun _ => .error (.typeError s!"'{ty}' object is not subscriptable")⟩

/-- A binary dunder: a `Counter` right operand, or `b` absent. -/
def binop (j : Json) (opname : String) (f : Ctr String → Ctr String → Py (Ctr String)) : Except String Json := do
  let a ← getItems j "a"
  match j.getObjVal? "b" with
  | .ok .null | .error _ =>
    return encPy encItems (.error (.typeError
      s!"unsupported operand type(s) for {opname}: 'Counter' and 'int'"))
  | .ok _ => return encPy encItems (f a (← getItems j "b"))

/-- A rich comparison. `__eq__`/`__ne__` on a non-`Counter` fall back to identity,
ordering raises. -/
def cmpop (j : Json) (opname : String) (f : Ctr String → Ctr String → Py Bool) : Except String Json := do
  let a ← getItems j "a"
  match j.getObjVal? "b" with
  | .ok .null | .error _ =>
    if opname == "==" then return encPy toJson (.ok false)
    else if opname == "!=" then return encPy toJson (.ok true)
    else return encPy (fun (b : Bool) => toJson b) (.error (.typeError
      s!"'{opname}' not supported between instances of 'Counter' and 'int'"))
  | .ok _ => return encPy (fun (b : Bool) => toJson b) (f a (← getItems j "b"))

/-- The target of `_count_elements`: `inst` adds an instance attribute
`get = lambda k, d: dict.get(c, k, d) + 10`; `slow` overrides `get` on the class. -/
def getTarget (j : Json) : CTarget String Int :=
  let inst := (j.getObjVal? "inst" >>= Json.getBool?).toOption.getD false
  let slow := (j.getObjVal? "slow" >>= Json.getBool?).toOption.getD false
  { typeGet := if slow then some (dGet kStr) else none
    instGet := if inst then some (fun d k z => do let v ← dGet kStr d k z; pure (v + 10)) else none }

def sorterN : Accel.Heapq.Sorter Nat := Accel.Heapq.pureSorter Nat

def runCtr (j : Json) : Except String Json := do
  let op ← getStr j "op"
  let rkP : String → Py String := fun k => .ok (rkStr k)
  let rvP : Int → Py String := fun v => .ok (toString v)
  match op with
  | "new" => return encPy encItems (counterNew kStr intNum (← getSrc j) (← getItems j "kw"))
  | "update" => return encOut encItems (update kStr intNum {} (← getItems j "a") (← getSrc j) (← getItems j "kw"))
  | "subtract" => return encOut encItems (subtract kStr intNum {} (← getItems j "a") (← getSrc j) (← getItems j "kw"))
  | "count_py" => return encOut encItems (countPy kStr intNum (getTarget j) (← getItems j "a") (← getIt j "xs"))
  | "count_c" => return encOut encItems (countC kStr intNum (getTarget j) (← getItems j "a") (← getIt j "xs"))
  | "most_common" => return encPy encItems (mostCommon intNum sorterN (← getItems j "a") (← getOptInt j "n"))
  | "elements" =>
    let r := elements intNum (← getItems j "a")
    return encOut encStrs (r.xs, r.stop)
  | "copy" =>
    let c : CObj String Int := ⟨0, "Counter", ← getItems j "a"⟩
    return encPy (fun (o : CObj String Int) => Json.arr #[toJson o.cls, toJson (o.id != c.id), encItems o.data])
      (counterCopy kStr intNum 1 c)
  | "reduce" =>
    let r := counterReduce 1 (⟨0, "Counter", ← getItems j "a"⟩ : CObj String Int)
    return okJ (Json.arr #[toJson r.1, toJson r.2.ty, encItems r.2.data])
  | "delitem" => return encPy encItems (delitem kStr rkStr (← getItems j "a") (← getStr j "e"))
  | "getitem" => return encPy toJson (dGet kStr (← getItems j "a") (← getStr j "e") 0)
  | "repr" => return encPy toJson (counterRepr kStr intNum sorterN Accel.Heapq.builtinHier rkP rvP "Counter"
      (← getItems j "a"))
  | "fromkeys" => return encPy encItems (counterFromkeys (ν := Int) (← getStrs j "xs") none)
  | "keep_positive" => return encOut encItems (keepPositive kStr rkStr intNum (← getItems j "a"))
  | "pos" => return encPy encItems (posC kStr intNum (← getItems j "a"))
  | "neg" => return encPy encItems (negC kStr intNum (← getItems j "a"))
  | "add" => binop j "+" (addC kStr intNum)
  | "sub" => binop j "-" (subC kStr intNum)
  | "or" => binop j "|" (orC kStr intNum)
  | "and" => binop j "&" (andC kStr intNum)
  | "xor" => binop j "^" (xorC kStr intNum)
  | "eq" => cmpop j "==" (eqC kStr intNum)
  | "ne" => cmpop j "!=" (neC kStr intNum)
  | "le" => cmpop j "<=" (leC kStr intNum)
  | "lt" => cmpop j "<" (ltC kStr intNum)
  | "ge" => cmpop j ">=" (geC kStr intNum)
  | "gt" => cmpop j ">" (gtC kStr intNum)
  | "iadd" => return encOut encItems (iaddC kStr rkStr intNum (← getItems j "a") (← getIOpnd j))
  | "isub" => return encOut encItems (isubC kStr rkStr intNum (← getItems j "a") (← getIOpnd j))
  | "ior" => return encOut encItems (iorC kStr rkStr intNum (← getItems j "a") (← getIOpnd j))
  | "iand" => return encOut encItems (iandC kStr rkStr intNum (← getItems j "a") (← getIOpnd j))
  | "ixor" => return encOut encItems (ixorC kStr rkStr intNum (← getItems j "a") (← getIOpnd j))
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
  | _ => cmMissing pyStrRepr

/-- The `ChainMap` object `0` with map objects `10, 11, ...`. -/
def cmObj (c : CM) : CMapO String Int := ⟨0, c.maps.zipIdx.map (fun (m, j) => (10 + j, m))⟩

/-- `[r is not self, r.maps[0] is not self.maps[0], r.maps[1:] are self's objects, maps]`. -/
def encCopy (c : CMapO String Int) (r : CMapO String Int) : Json :=
  Json.arr #[toJson (r.id != c.id), toJson ((r.maps.head?.map (·.1)) != (c.maps.head?.map (·.1))),
    toJson (r.maps.tail.map (·.1) == c.maps.tail.map (·.1)), Json.arr (r.view.map encItems).toArray]

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
  | "repr" =>
    let heap : Nat → Option (String × List (MRef String Int)) := fun i =>
      if i = 0 then some ("ChainMap", c.maps.map .dict) else none
    return encPy toJson (cmReprR (fun d => .ok (reprD pyStrRepr rvInt d)) heap 10 [] 0)
  | "repr_self" =>
    let heap : Nat → Option (String × List (MRef String Int)) := fun i =>
      if i = 0 then some ("ChainMap", c.maps.map .dict ++ [.chain 0]) else none
    return encPy toJson (cmReprR (fun d => .ok (reprD pyStrRepr rvInt d)) heap 10 [] 0)
  | "getitem_dd" =>
    let gm := match c.maps with
      | [] => []
      | m :: t => defaultG m (.ok 0) :: t.map (dictG pyStrRepr)
    return encPy toJson (cmGetitemG Accel.Heapq.builtinHier miss gm k)
  | "contains_dd" =>
    let gm := match c.maps with
      | [] => []
      | m :: t => defaultG m (.ok 0) :: t.map (dictG pyStrRepr)
    return encPy toJson (cmContainsG gm k)
  | "fromkeys" => return encPy encCM (cmFromkeysP kStr (← getIt j "xs") (dflt.getD 0))
  | "copy" => return encPy (encCopy (cmObj c)) (cmCopyO 1 100 (cmObj c))
  | "new_child" =>
    let m ← optOther j
    return okJ (encCM (cmNewChild c m (← getItems j "kw")))
  | "parents" => return okJ (encCM (cmParents c))
  | "setitem" => return encPy encCM (cmSetitem c k (dflt.getD 0))
  | "delitem" => return encPy encCM (cmDelitem pyStrRepr c k)
  | "popitem" => return encPy (fun r => Json.arr #[encPair r.1, encCM r.2]) (cmPopitem c)
  | "pop" => return encPy (fun r => Json.arr #[toJson r.1, encCM r.2]) (cmPop pyStrRepr c k dflt)
  | "clear" => return encPy (fun (r : CMapO String Int) => Json.arr (r.view.map encItems).toArray) (cmClearO (cmObj c))
  | "ior" =>
    let gen := (j.getObjVal? "gen" >>= Json.getBool?).toOption.getD false
    let o : Py (FIt (String × Int)) := match j.getObjVal? "o" with
      | .ok .null | .error _ => .error (.typeError "'int' object is not iterable")
      | .ok _ => .ok ⟨(getItems j "o").toOption.getD [], if gen then some (.valueError "boom") else none⟩
    let r := cmIorO kStr (cmObj c) o
    return okJ (Json.arr #[
      (match r.2 with
       | none => Json.arr #[toJson (r.1.id == 0), toJson ((r.1.maps.head?.map (·.1)) == some 10)]
       | some _ => Json.null),
      Json.arr (r.1.view.map encItems).toArray,
      (match r.2 with | none => Json.null | some e => encExc e)])
  | "or" =>
    match cmOrO kStr 1 100 (cmObj c) ((← optOther j).map (fun o => .ok (FIt.ofList o))) with
    | some r => return encPy (encCopy (cmObj c)) r
    | none => return encPy encCM (.error (.typeError
        "unsupported operand type(s) for |: 'ChainMap' and 'int'"))
  | "ror" =>
    match cmRorP c ((← optOther j).map .ok) with
    | some r => return encPy encCM r
    | none => return encPy encCM (.error (.typeError
        "unsupported operand type(s) for |: 'int' and 'ChainMap'"))
  | "ror_bad" =>
    match cmRorP c (some (.error (.named "LookupError" "gi"))) with
    | some r => return encPy encCM r
    | none => throw "unreachable"
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
  | "frozen" => return .frozen (← getItems j "o")
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
  | "reversed" => return encPy encStrs (udReversed u)
  | "dict_reversed" => return encPy encStrs (dictReversed u.data)
  | "dict_getitem" => return encPy toJson (dictGetitem rkStr miss u.data k)
  | "dict_pop" => return encPy (fun r => Json.arr #[toJson r.1, encItems r.2]) (dictPop rkStr u.data k dflt)
  | "dict_popitem" => return encPy (fun r => Json.arr #[encPair r.1, encItems r.2]) (dictPopitem u.data)
  | "dict_setdefault" =>
    let r := dictSetdefault u.data k (dflt.getD 0)
    return okJ (Json.arr #[toJson r.1, encItems r.2])
  | "dict_items_contains" => return okJ (toJson (dictItemsContains u.data k (dflt.getD 0)))
  | "new_p" =>
    let ps ← getItems j "o"
    let bad := (j.getObjVal? "bad" >>= Json.getBool?).toOption.getD false
    let fail := (j.getObjVal? "fail" >>= Json.getBool?).toOption.getD false
    let items : List (Py (String × Int)) := ps.map .ok ++
      (if bad then [.error (.valueError "not enough values to unpack (expected 2, got 1)")] else [])
    let src : USrc String Int := .pairs (.ok ⟨items, if fail then some (.valueError "boom") else none⟩)
    return encPy encItems (udNewP kStr (some src) (← getItems j "kw"))
  | "getitem_p" =>
    return encPy toJson (udGetitemP kStr pyStrRepr (some (fun _ => .error (.valueError "miss"))) u k)
  | "repr_self" =>
    let heap : Nat → Option (D String (VRef Int)) := fun i =>
      if i = 0 then some (D.set (u.data.map (fun p => (p.1, .plain p.2))) k (.ud 0)) else none
    return encPy toJson (udReprR (fun s => .ok (pyStrRepr s)) (fun v => .ok (toString v)) heap 10 [] 0)
  | "ior_p" =>
    let o ← getItems j "o"
    let r := match ← getStr j "oty" with
      | "user" => udIorP kStr u (.user o)
      | "gen" => udIorP kStr u (.other (.ok ⟨o, some (.valueError "boom")⟩))
      | "int" => udIorP kStr u (.other (.error (.typeError "'int' object is not iterable")))
      | _ => udIorP kStr u (.other (.ok (FIt.ofList o)))
    return encOut encUD r
  | "copy_p" =>
    let raising := (j.getObjVal? "raise" >>= Json.getBool?).toOption.getD false
    let uo : UDO String Int Int := ⟨0, if raising then "coll_UDRaise" else cls, 50, u.data, [("extra", 5)]⟩
    let copyFn : UDO String Int Int → Py (UDO String Int Int) := fun t =>
      if raising then .error (.named "RuntimeError" "nocopy") else .ok (udCopyDunderO 1 51 t)
    let r := udCopyO kStr copyFn 1 51 52 uo
    return okJ (Json.arr #[encItems r.1.data, encPy (fun (c : UDO String Int Int) =>
      Json.arr #[toJson c.cls, toJson (c.id != uo.id), toJson (c.dataId != uo.dataId), encItems c.data,
        toJson (c.attrs.length)]) r.2])
  | "fromkeys_p" =>
    return encPy encUD (udFromkeysP kStr cls (← getIt j "xs") (dflt.getD 0))
  | _ => throw s!"unknown ud op {op}"

/-! ### `UserList` -/

def getInts (j : Json) (key : String) : Except String (List Int) := do
  (← jArr (← field j key)).mapM Json.getInt?

def encInts (l : List Int) : Json := Json.arr (l.map toJson).toArray

def getLOpnd (j : Json) : Except String (LOpnd Int) := do
  match ← getStr j "oty" with
  | "user" => return .user (← getInts j "o")
  | "list" => return .list (← getInts j "o")
  | "tuple" => return .iter "tuple" (← getInts j "o")
  | ty => return .noniter ty

def getSlice (j : Json) : Except String RangeSlice.Slice := do
  return ⟨← getOptInt j "st", ← getOptInt j "sp", ← getOptInt j "se"⟩

def encUL (u : UL Int) : Json := Json.arr #[toJson u.cls, encInts u.data]

def cmpOf : String → Option CmpOp
  | "lt" => some .lt
  | "le" => some .le
  | "eq" => some .eq
  | "gt" => some .gt
  | "ge" => some .ge
  | _ => none

def runUL (j : Json) : Except String Json := do
  let op ← getStr j "op"
  let cls := if (← getNat j "sub") = 0 then "UserList" else "coll_ULPlain"
  let u : UL Int := ⟨cls, ← getInts j "a"⟩
  let x := (← getOptInt j "x").getD 0
  let i := (← getOptInt j "i").getD 0
  let enc := encPy encUL
  if let some c := cmpOf op then
    return encPy (fun (b : Bool) => toJson b) (ulCmp intOps c u (← getLOpnd j))
  match op with
  | "new" =>
    match j.getObjVal? "oty" with
    | .ok _ => return enc (ulNew cls (some (← getLOpnd j)))
    | .error _ => return enc (ulNew cls none)
  | "repr" => return okS (ulRepr intOps u)
  | "contains" => return okJ (toJson (ulContains intOps u x))
  | "len" => return okI (ulLen u)
  | "getitem" => return encPy toJson (ulGetitem intOps u i)
  | "getslice" => return enc (ulGetslice intOps u (← getSlice j))
  | "setitem" => return enc (ulSetitem intOps u i x)
  | "setslice" => return enc (ulSetslice intOps u (← getSlice j) (← getInts j "o"))
  | "delitem" => return enc (ulDelitem intOps u i)
  | "delslice" => return enc (ulDelslice intOps u (← getSlice j))
  | "add" => return enc (ulAdd u (← getLOpnd j))
  | "radd" => return enc (ulRadd u (← getLOpnd j))
  | "iadd" => return enc (ulIadd u (← getLOpnd j))
  | "mul" => return enc (ulMul intOps u i)
  | "imul" => return enc (ulImul intOps u i)
  | "copy" => return enc (ulCopy u)
  | "copy_dunder" => return okJ (encUL (ulCopyDunder u))
  | "append" => return okJ (encUL (ulAppend u x))
  | "insert" => return enc (ulInsert intOps u i x)
  | "pop" => return encPy (fun r => Json.arr #[toJson r.1, encUL r.2]) (ulPop intOps u (← getOptInt j "i"))
  | "remove" => return enc (ulRemove intOps u x)
  | "clear" => return okJ (encUL (ulClear u))
  | "count" => return okI (ulCount intOps u x)
  | "index" => return encPy toJson (ulIndex intOps u x (← getOptInt j "st") (← getOptInt j "sp"))
  | "reverse" => return okJ (encUL (ulReverse intOps u))
  | "sort" => return okJ (encUL (ulSort intOps u (← getBool j "r")))
  | "extend" => return enc (ulExtend u (← getLOpnd j))
  | "gen_iadd" | "gen_extend" | "gen_add" | "gen_radd" | "gen_list_iadd" =>
    let xs ← getInts j "o"
    let fail := (j.getObjVal? "fail" >>= Json.getBool?).toOption.getD false
    let o : LOpndP Int := .other "generator" (.ok ⟨xs, if fail then some (.valueError "boom") else none⟩)
    match op with
    | "gen_iadd" => return encOut encUL (ulIaddP u o)
    | "gen_extend" => return encOut encUL (ulExtendP u o)
    | "gen_list_iadd" => return encOut encInts (listExtendP u.data o)
    | "gen_add" => return enc (ulAddP u o)
    | _ => return enc (ulRaddP u o)
  | "sort_p" =>
    let npos := (← getOptInt j "npos").getD 0
    let rev : Option Json := match j.getObjVal? "rev" with
      | .ok v => some v
      | .error _ => none
    let truth : Json → Py Bool := fun v => match v with
      | .bool b => .ok b
      | _ => .error (.valueError "b")
    let hasKey := (j.getObjVal? "keynone" >>= Json.getBool?).toOption.getD false
    let a : SortArgs Int Int Json := ⟨npos.toNat, if hasKey then some none else none, rev⟩
    return encOut encUL (ulSortP truth (fun x y => .ok (decide (x < y))) (fun x y => .ok (decide (x < y)))
      (fun _ v => v) u a)
  | "init_sub" =>
    let l ← getInts j "o"
    return encPy (fun (r : ULO Int Int) => encUL ⟨r.cls, r.data⟩)
      (ulNewP 1 2 cls (some (.listSub l (.ok (FIt.ofList l.reverse)))))
  | _ => throw s!"unknown ul op {op}"

/-! ### `UserString` -/

def isUp (c : Nat) : Bool := 65 ≤ c && c ≤ 90
def isLo (c : Nat) : Bool := 97 ≤ c && c ≤ 122
def isDig (c : Nat) : Bool := 48 ≤ c && c ≤ 57
def isAl (c : Nat) : Bool := isUp c || isLo c
def toLo (c : Nat) : Nat := if isUp c then c + 32 else c
def toUp (c : Nat) : Nat := if isLo c then c - 32 else c
def asciiWs (c : Nat) : Bool := (9 ≤ c && c ≤ 13) || (28 ≤ c && c ≤ 32)

def asciiTitle (prevCased : Bool) : Seq → Seq
  | [] => []
  | c :: t =>
    (if prevCased then toLo c else toUp c) :: asciiTitle (isAl c) t

def asciiCase : CaseFn → Seq → Seq
  | .lower, s | .casefold, s => s.map toLo
  | .upper, s => s.map toUp
  | .swapcase, s => s.map (fun c => if isUp c then toLo c else toUp c)
  | .capitalize, [] => []
  | .capitalize, c :: t => toUp c :: t.map toLo
  | .title, s => asciiTitle false s

/-- `str.istitle` on ASCII. -/
def asciiIsTitle (s : Seq) : Bool :=
  let rec go (prevCased cased : Bool) : Seq → Bool
    | [] => cased
    | c :: t =>
      if isUp c then !prevCased && go true true t
      else if isLo c then prevCased && go true true t
      else go false cased t
  go false false s

def asciiPred : PredFn → Seq → Bool
  | .isalpha, s => !s.isEmpty && s.all isAl
  | .isalnum, s => !s.isEmpty && s.all (fun c => isAl c || isDig c)
  | .isascii, _ => true
  | .isdecimal, s | .isdigit, s | .isnumeric, s => !s.isEmpty && s.all isDig
  | .isidentifier, [] => false
  | .isidentifier, c :: t =>
    (isAl c || c == 95) && t.all (fun c => isAl c || isDig c || c == 95)
  | .islower, s => s.any isLo && !s.any isUp
  | .isupper, s => s.any isUp && !s.any isLo
  | .isprintable, s => s.all (fun c => 32 ≤ c && c ≤ 126)
  | .isspace, s => !s.isEmpty && s.all asciiWs
  | .istitle, s => asciiIsTitle s

def strOfSeq (s : Seq) : String := String.ofList (s.map Char.ofNat)

/-- `repr(str)` on ASCII. -/
def asciiRepr (s : Seq) : String :=
  let q := if s.contains 39 && !s.contains 34 then "\"" else "'"
  let esc (c : Nat) : String :=
    if c == 92 then "\\\\"
    else if c == 10 then "\\n"
    else if c == 13 then "\\r"
    else if c == 9 then "\\t"
    else if c == 39 && q == "'" then "\\'"
    else if c < 32 || c == 127 then
      "\\x" ++ String.ofList (Nat.toDigits 16 (c + 256)).tail
    else String.singleton (Char.ofNat c)
  q ++ String.join (s.map esc) ++ q

/-- `int(s)` on ASCII, base 10, the digit strings the generator uses. -/
def asciiInt (s : Seq) : Option Int :=
  let t := (s.dropWhile asciiWs).reverse.dropWhile asciiWs |>.reverse
  let (neg, t) := match t with
    | 45 :: r => (true, r)
    | 43 :: r => (false, r)
    | r => (false, r)
  let rec digits (acc : Nat) (prevDigit : Bool) : Seq → Option Nat
    | [] => if prevDigit then some acc else none
    | 95 :: r => if prevDigit then digits acc false r else none
    | c :: r => if isDig c then digits (acc * 10 + (c - 48)) true r else none
  (digits 0 false t).map (fun n => if neg then -(n : Int) else n)

/-- `str.format` for the templates `x`, `{}`, `{}{}`, `{0}`, `{1}`. -/
def asciiFormat (s : Seq) (args : List Int) (kw : List (String × Int)) : Py Seq :=
  let at_ (i : Nat) : Py Seq :=
    match args[i]? with
    | some v => .ok ((toString v).toList.map Char.toNat)
    | none => .error (.indexError
        s!"Replacement index {i} out of range for positional args tuple")
  let rec go (auto : Nat) : Seq → Py Seq
    | [] => .ok []
    | 123 :: 125 :: r => do
      let v ← at_ auto
      let t ← go (auto + 1) r
      return v ++ t
    | 123 :: d :: 125 :: r => do
      let v ← if 48 ≤ d ∧ d ≤ 57 then at_ (d - 48) else
        let key := String.singleton (Char.ofNat d)
        match D.get? kw key with
        | some v => .ok ((toString v).toList.map Char.toNat)
        | none => .error (.keyError (rkStr key))
      let t ← go auto r
      return v ++ t
    | c :: r => do
      let t ← go auto r
      return c :: t
  go 0 s

/-- `str.format_map` for the templates `x`, `{a}`. -/
def asciiFormatMap (s : Seq) (fm : FMap) : Py Seq :=
  let m := fm.items
  let rec go : Seq → Py Seq
    | [] => .ok []
    | 123 :: k :: 125 :: r => do
      let key := String.singleton (Char.ofNat k)
      match D.get? m key with
      | some v =>
        let t ← go r
        return (toString v).toList.map Char.toNat ++ t
      | none =>
        match fm.missing with
        | some f => do
          let v ← f key
          let t ← go r
          return (toString v).toList.map Char.toNat ++ t
        | none => .error (.keyError (rkStr key))
    | c :: r => do
      let t ← go r
      return c :: t
  go s

/-- `s % args` for a tuple of ints, `%d`, `%s`, `%%`. -/
def asciiModTuple (s : Seq) (args : List Int) : Py Seq :=
  let got := args.length
  let rec go (args : List Int) : Seq → Py Seq
    | [] => if args.isEmpty then .ok []
      else .error (.typeError
        s!"not all arguments converted during string formatting (required {got - args.length}, got {got})")
    | 37 :: 37 :: r => do
      let t ← go args r
      return 37 :: t
    | 37 :: _ :: r =>
      match args with
      | [] => .error (.typeError s!"not enough arguments for format string (got {got})")
      | a :: rest => do
        let t ← go rest r
        return (toString a).toList.map Char.toNat ++ t
    | c :: r => do
      let t ← go args r
      return c :: t
  go args s

/-- `template % u` for a `UserString` `u`: one object, which also passes for a mapping, so
leftover arguments are not an error. -/
def asciiModUser (s self : Seq) : Py Seq :=
  let rec go (used : Bool) : Seq → Py Seq
    | [] => .ok []
    | 37 :: 115 :: r =>
      if used then .error (.typeError "not enough arguments for format string (got 1)")
      else do
        let t ← go true r
        return self ++ t
    | c :: r => do
      let t ← go used r
      return c :: t
  go false s

/-- `s % mapping` for the templates `x`, `%(a)s`, `%(a)d`, `%%`. -/
def asciiModMap (s : Seq) (m : List (String × Int)) : Py Seq :=
  let rec go : Seq → Py Seq
    | [] => .ok []
    | 37 :: 37 :: r => do
      let t ← go r
      return 37 :: t
    | 37 :: 40 :: k :: 41 :: _ :: r => do
      let key := String.singleton (Char.ofNat k)
      match D.get? m key with
      | some v =>
        let t ← go r
        return (toString v).toList.map Char.toNat ++ t
      | none => .error (.keyError (rkStr key))
    | c :: r => do
      let t ← go r
      return c :: t
  go s

def asciiMod (s : Seq) : ModArg → Py Seq
  | .tuple l => asciiModTuple s l
  | .single v => asciiModTuple s [v]
  | .mapping m => asciiModMap s m
  | .user u => asciiModUser s u

/-- `str.translate` over a table that answers each code point, keeping the character on a
`LookupError`. -/
def asciiTranslate (s : Seq) (t : TTable) : Py Seq := do
  let parts ← s.mapM (fun c =>
    match t c with
    | .ok .del => .ok []
    | .ok (.cp n) => .ok [n]
    | .ok (.str q) => .ok q
    | .error e =>
      if e.className = "LookupError" ∨ e.className = "KeyError" ∨ e.className = "IndexError" then .ok [c]
      else .error e)
  return parts.flatten

def asciiEncode (s : Seq) (enc err : String) : Py (List Nat) :=
  if enc == "utf-8" || enc == "ascii" then
    if err == "strict" || err == "ignore" then .ok s
    else .ok s
  else .error (.named "LookupError" s!"unknown encoding: {enc}")

def asciiOps : UniOps where
  case := asciiCase
  pred := asciiPred
  encode := asciiEncode
  format := asciiFormat
  formatMap := asciiFormatMap
  mod := asciiMod
  translate := asciiTranslate
  hash _ := 0
  repr := asciiRepr
  toInt s :=
    match asciiInt s with
    | some n => .ok n
    | none => .error (.valueError "~invalid literal")
  toFloat s :=
    match asciiInt s with
    | some n => .ok (toString n ++ ".0")
    | none => .error (.valueError "~could not convert")
  toComplex s :=
    match asciiInt s with
    | some n => .ok ("(" ++ toString n ++ "+0j)")
    | none => .error (.valueError "~malformed")

def decArg (j : Json) : Except String SArg := do
  match ← getStr j "k" with
  | "str" => return .str (← getSeqJ j)
  | "user" => return .user (← getSeqJ j)
  | ty => return .other ty (← getSeqJ j)
where
  getSeqJ (j : Json) : Except String Seq := do
    (← jArr (← field j "s")).mapM Json.getNat?

def getArg (j : Json) (key : String) : Except String SArg := do decArg (← field j key)

def getOptArg (j : Json) (key : String) : Except String (Option SArg) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => .ok none
  | .ok v => some <$> decArg v

def getAffixArg (j : Json) : Except String AffixArg := do
  match j.getObjVal? "tup" with
  | .ok v =>
    let ps ← (← jArr v).mapM (fun p => do (← jArr p).mapM Json.getNat?)
    return .tuple ps
  | .error _ => return .one (← getArg j "a")

def encSeq (s : Seq) : Json := toJson s

def encURes : URes → Json
  | .us u => Json.mkObj [("us", Json.arr #[toJson u.cls, encSeq u.data])]
  | .str s => Json.mkObj [("str", encSeq s)]
  | .bool b => toJson b
  | .int i => toJson i
  | .strs l => Json.mkObj [("strs", Json.arr (l.map encSeq).toArray)]
  | .tup t => Json.mkObj [("tup", Json.arr #[encSeq t.1, encSeq t.2.1, encSeq t.2.2])]
  | .bytes b => Json.mkObj [("bytes", toJson b)]
  | .text s => Json.mkObj [("text", toJson s)]

def caseOf : String → Option CaseFn
  | "capitalize" => some .capitalize
  | "casefold" => some .casefold
  | "lower" => some .lower
  | "upper" => some .upper
  | "swapcase" => some .swapcase
  | "title" => some .title
  | _ => none

def predOf : String → Option PredFn
  | "isalpha" => some .isalpha
  | "isalnum" => some .isalnum
  | "isascii" => some .isascii
  | "isdecimal" => some .isdecimal
  | "isdigit" => some .isdigit
  | "isidentifier" => some .isidentifier
  | "islower" => some .islower
  | "isnumeric" => some .isnumeric
  | "isprintable" => some .isprintable
  | "isspace" => some .isspace
  | "istitle" => some .istitle
  | "isupper" => some .isupper
  | _ => none

def sopOf : String → Option SOp
  | "eq" => some .eq
  | "lt" => some .lt
  | "le" => some .le
  | "gt" => some .gt
  | "ge" => some .ge
  | _ => none

def getCall (op : String) (j : Json) : Except String SCall := do
  if let some f := caseOf op then return .case f
  if let some f := predOf op then return .pred f
  if let some f := sopOf op then return .rich f (← getArg j "a")
  let st ← getOptInt j "st"
  let en ← getOptInt j "en"
  let w := (← getOptInt j "w").getD 0
  match op with
  | "center" => return .center w (← getOptArg j "fill")
  | "ljust" => return .ljust w (← getOptArg j "fill")
  | "rjust" => return .rjust w (← getOptArg j "fill")
  | "zfill" => return .zfill w
  | "expandtabs" => return .expandtabs w
  | "count" => return .count (← getArg j "a") st en
  | "find" => return .find (← getArg j "a") st en true
  | "rfind" => return .find (← getArg j "a") st en false
  | "index" => return .index (← getArg j "a") st en true
  | "rindex" => return .index (← getArg j "a") st en false
  | "startswith" => return .startswith (← getAffixArg j) st en
  | "endswith" => return .endswith (← getAffixArg j) st en
  | "removeprefix" => return .removeprefix (← getArg j "a")
  | "removesuffix" => return .removesuffix (← getArg j "a")
  | "partition" => return .partition (← getArg j "a")
  | "rpartition" => return .rpartition (← getArg j "a")
  | "replace" => return .replace (← getArg j "a") (← getArg j "b") ((← getOptInt j "w").getD (-1))
  | "split" => return .split (← getOptArg j "a") ((← getOptInt j "w").getD (-1))
  | "rsplit" => return .rsplit (← getOptArg j "a") ((← getOptInt j "w").getD (-1))
  | "splitlines" => return .splitlines (← getBool j "keep")
  | "strip" => return .strip (← getOptArg j "a") .both
  | "lstrip" => return .strip (← getOptArg j "a") .left
  | "rstrip" => return .strip (← getOptArg j "a") .right
  | "join" => return .join (← (← jArr (← field j "items")).mapM decArg)
  | "contains" => return .contains (← getArg j "a")
  | "mul" => return .mul w
  | "getitem" => return .getitem w
  | "getslice" => return .getslice ⟨st, en, ← getOptInt j "se"⟩
  | "format" => return .format (← getInts j "args") (← getItems j "kw")
  | "format_map" =>
    let miss := (j.getObjVal? "miss" >>= Json.getBool?).toOption.getD false
    return .formatMap ⟨← getItems j "m", if miss then some (fun _ => .ok (-1)) else none⟩
  | "mod" =>
    match ← getStr j "mk" with
    | "tuple" => return .mod (.tuple (← getInts j "args"))
    | "single" => return .mod (.single ((← getOptInt j "v").getD 0))
    | "mapping" => return .mod (.mapping (← getItems j "m"))
    | _ => return .mod (.user ((← jArr (← field j "us")).filterMap (fun x => (x.getNat?).toOption)))
  | "translate" =>
    let entries ← (← jArr (← field j "t")).mapM (fun p => do
      match ← jArr p with
      | [k, v] =>
        let e : TEntry := match v with
          | .null => .del
          | .str q => .str (q.toList.map Char.toNat)
          | v => .cp ((v.getNat?).toOption.getD 0)
        return ((← k.getNat?), e)
      | _ => throw "bad table")
    let tk ← getStr j "tk"
    let table : TTable := fun c =>
      if tk = "bad" then .error (.valueError "t")
      else if tk = "list" then
        match entries[c]? with
        | some (_, e) => .ok e
        | none => .error (.indexError "list index out of range")
      else
        match entries.find? (·.1 = c) with
        | some (_, e) => .ok e
        | none => .error (.keyError (toString c))
    let n := (← getOptInt j "n").getD 1
    return .translate (List.replicate n.toNat table)
  | "encode" => return .encode (← getStr j "enc") (← getStr j "err")
  | "len" => return .len
  | "hash" => return .hash
  | "repr" => return .repr
  | "toInt" => return .toInt
  | "toFloat" => return .toFloat
  | "toComplex" => return .toComplex
  | _ => throw s!"unknown us op {op}"

def runUS (j : Json) : Except String Json := do
  let op ← getStr j "op"
  let cls := if (← getNat j "sub") = 0 then "UserString" else "coll_USPlain"
  let d ← (← jArr (← field j "s")).mapM Json.getNat?
  let u : US := ⟨cls, d⟩
  match op with
  | "new" => return okJ (encURes (.us (usNew cls (← getArg j "a"))))
  | "str" => return okJ (encURes (.str (usStr u)))
  | "getnewargs" => return okJ (encURes (.str (usGetnewargs u)))
  | "add" => return okJ (encURes (.us (usAdd u (← getArg j "a"))))
  | "radd" => return okJ (encURes (.us (usRadd u (← getArg j "a"))))
  | "rmod" =>
    let t ← (← jArr (← field j "t")).mapM Json.getNat?
    return encPy (fun v => encURes (.us v)) (usRmod asciiOps u t)
  | "replace_kw" =>
    let kw ← getStr j "kw"
    let w := (← getOptInt j "w").getD 0
    return encPy (fun v => encURes (.us v)) (usReplaceKw u (← getArg j "a") (← getArg j "b") kw w)
  | "str_replace_kw" =>
    let kw ← getStr j "kw"
    let w := (← getOptInt j "w").getD 0
    return encPy (fun v => encURes (.str v)) (strReplaceKw u.data (← getArg j "a") (← getArg j "b") kw w)
  | "dformat" => return encPy (fun v => encURes (.str v)) (usDunderFormat u (← getStr j "spec"))
  | "encode_none" => return encPy (fun v => encURes (.bytes v)) (usEncode asciiOps u none none)
  | _ =>
    let c ← getCall op j
    if (← getBool j "plain") then return encPy encURes (strCall asciiOps c u.data)
    else return encPy encURes (usCall asciiOps c u)

/-! ### `namedtuple` -/

/-- The NFKC of the characters the generator uses. -/
def nfkcChar (c : Char) : String :=
  let n := c.toNat
  if n == 0xfb01 then "fi"
  else if n == 0xff3f then "_"
  else if 0x1d400 ≤ n && n ≤ 0x1d419 then String.singleton (Char.ofNat (n - 0x1d400 + 65))
  else if 0x1d41a ≤ n && n ≤ 0x1d433 then String.singleton (Char.ofNat (n - 0x1d41a + 97))
  else String.singleton c

def idStart (c : Char) : Bool :=
  let n := c.toNat
  isAl n || n == 95 || n == 0xfb01 || (0x1d400 ≤ n && n ≤ 0x1d433)

def idCont (c : Char) : Bool := idStart c || isDig c.toNat || c.toNat == 0xff3f

/-- `str.isidentifier` and NFKC on the generator's alphabet. -/
def genU : UniId where
  isidentifier s :=
    match s.toList with
    | [] => false
    | c :: t => idStart c && t.all idCont
  nfkc s := String.join (s.toList.map nfkcChar)

def encNT (T : NT Int) : Json :=
  Json.mkObj [("typename", toJson T.typename), ("fields", encStrs T.fields), ("args", encStrs T.args),
    ("defaults", encInts T.defaults), ("fd", encItems T.fieldDefaults), ("doc", toJson T.doc),
    ("newdoc", toJson T.newDoc)]

def runNT (j : Json) : Except String Json := do
  let op ← getStr j "op"
  let typename ← getStr j "typename"
  let fn : FieldNames ← match j.getObjVal? "fstr" with
    | .ok v => pure (.str (← v.getStr?))
    | .error _ => pure (.list (← getStrs j "fields"))
  let rename ← getBool j "rename"
  let defaults : Option (List Int) ← match j.getObjVal? "defaults" with
    | .ok .null | .error _ => pure none
    | .ok _ => pure (some (← getInts j "defaults"))
  let T? : Py (NT Int) := namedtuple genU typename fn rename defaults
  if op == "create" then return encPy encNT T?
  match T? with
  | .error e => return encPy encNT (.error e)
  | .ok T =>
    let vals ← getInts j "vals"
    match op with
    | "call" => return encPy encInts (ntCall T vals (← getItems j "kw"))
    | "make" => return encPy encInts (ntMake T vals)
    | "replace" => return encPy encInts (ntReplace T vals (← getItems j "kw"))
    | "repr" => return okS (ntRepr rvInt T.typename T vals)
    | "asdict" => return okJ (encItems (ntAsdict T vals))
    | "getnewargs" => return okJ (encInts vals)
    | "getattr" =>
      match ntGetattr T vals (← getStr j "name") with
      | some v => return okI v
      | none => return encPy toJson (.error (.named "AttributeError" "~no attribute") : Py Int)
    | "roundtrip" => return encPy encInts (ntCall T [] (ntAsdict T vals))
    | _ => throw s!"unknown nt op {op}"

/-! ### `OrderedDict` (the pure-Python class) -/

abbrev ODS := OD String Int

def odItems (o : ODS) : List (String × Int) := o.keysList.filterMap (fun k => (D.get? o.d k).map (k, ·))

def odFromItems (items : List (String × Int)) : ODS :=
  (odUpdate kStr OD.new (.pairs (.ok (FIt.ofList (items.map .ok))))).1

/-- `repr` of a key: `"#L"` stands for `[1]`. -/
def rkOD (k : String) : String := if k = "#L" then "[1]" else pyStrRepr k

/-- One operation of the program; the result is `null` for a call returning `None`. -/
def odStep (o : ODS) (op k : String) (v : Int) (flag : Bool) : Out ODS × Json :=
  let unit : Py ODS → Out ODS × Json := fun r => match r with
    | .ok o' => ((o', none), Json.null)
    | .error e => ((o, some e), Json.null)
  match op with
  | "set" => unit (odSet kStr o k v)
  | "del" => unit (odDel kStr rkOD o k)
  | "pop" | "popd" =>
    match odPop kStr rkOD o k (if op = "popd" then some v else none) with
    | .ok (r, o') => ((o', none), toJson r)
    | .error e => ((o, some e), Json.null)
  | "popitem" =>
    match odPopitem rkOD o flag with
    | .ok (p, o') => ((o', none), Json.arr #[toJson p.1, toJson p.2])
    | .error e => ((o, some e), Json.null)
  | "move" => unit (odMoveToEnd kStr rkOD o k flag)
  | "setdefault" =>
    match odSetdefault kStr o k v with
    | .ok (r, o') => ((o', none), toJson r)
    | .error e => ((o, some e), Json.null)
  | "clear" => ((odClear o, none), Json.null)
  | _ => (odUpdate kStr o (.pairs (.ok (FIt.ofList [.ok (k, v), .ok ("b", v + 1)]))), Json.null)

def encODItems (l : List (String × Int)) : Json := Json.arr (l.map encPair).toArray

def runOD (j : Json) : Except String Json := do
  let ops ← jArr (← field j "ops")
  let mut o : ODS := OD.new
  let mut results : Array Json := #[]
  let mut exc : Json := Json.null
  for op in ops do
    match ← jArr op with
    | [a, b, c, d] =>
      let ((o', e), r) := odStep o (← a.getStr?) (← b.getStr?) (← c.getInt?) (← d.getBool?)
      o := o'
      match e with
      | some e =>
        exc := encExc e
        break
      | none => results := results.push r
    | _ => throw "bad op"
  let fin ← getStr j "fin"
  let perm := (j.getObjVal? "perm" >>= Json.getBool?).toOption.getD false
  let finRes : Json ← match fin with
    | "eq_od" =>
      let items := odItems o
      let items := if perm && items.length > 1 then items.drop 1 ++ items.take 1 else items
      pure (encPy toJson (odEq (fun a b => .ok (decide (a = b))) o (.od (odFromItems items))))
    | "eq_dict" =>
      let items := odItems o
      let items := if perm then items.reverse else items
      pure (encPy toJson (odEq (fun a b => .ok (decide (a = b))) o (.dict items)))
    | "repr" => pure (encPy toJson (odRepr (fun s => .ok (pyStrRepr s)) (fun v => .ok (toString v)) "OrderedDict" o))
    | "reduce" =>
      let r := odReduce "OrderedDict" o
      pure (okJ (Json.arr #[toJson r.1, Json.arr #[], Json.null, Json.null, encODItems r.2]))
    | "copy" => pure (encPy (fun (c : ODS) => Json.arr #[toJson true, toJson "OrderedDict", encODItems (odItems c)])
        (odCopy kStr o))
    | "or" =>
      match odOr kStr o (some (dictUSrc [("c", 9), ("a", 8)])) with
      | some r => pure (encPy (fun c => encODItems (odItems c)) r)
      | none => throw "unreachable"
    | "ror" =>
      match odRor kStr o (some (dictUSrc [("c", 9), ("a", 8)])) with
      | some r => pure (encPy (fun c => encODItems (odItems c)) r)
      | none => throw "unreachable"
    | "fromkeys" =>
      pure (encPy (fun c => encODItems (odItems c)) (odFromkeys kStr (.ok (FIt.ofList (← getStrs j "xs"))) (1 : Int)))
    | "iter_del" =>
      match odGenNext o false .fresh with
      | (.ok none, _) => pure (okJ (Json.arr #[Json.arr #[], Json.null]))
      | (.ok (some k), g) =>
        match odDel kStr pyStrRepr o k with
        | .ok o' =>
          o := o'
          match odGenRun o false (o.next + 1) g with
          | .ok rest => pure (okJ (Json.arr #[encStrs (k :: rest), Json.null]))
          | .error e => pure (okJ (Json.arr #[encStrs [k], encExc e]))
        | .error e => throw s!"unexpected {e.message}"
      | (.error e, _) => pure (okJ (Json.arr #[Json.arr #[], encExc e]))
    | "views" =>
      let enc3 (rev : Bool) : Json := Json.arr #[encPy encStrs (odKeysView o rev),
        encPy encODItems (odItemsView rkOD o rev), encPy (fun (l : List Int) => Json.arr (l.map toJson).toArray)
          (odValuesView rkOD o rev)]
      pure (okJ (Json.arr #[enc3 false, enc3 true]))
    | "init_kw" =>
      let ps ← getItems j "ps"
      let kw ← getItems j "kw"
      pure (encPy (fun c => encODItems (odItems c))
        (odInit kStr (some (.pairs (.ok (FIt.ofList (ps.map .ok))))) kw))
    | _ => pure (okJ Json.null)
  let back : Json := match odKeysView o true with
    | .ok l => encStrs l
    | .error e => encExc e
  return okJ (Json.arr #[encStrs o.keysList, back, encODItems (odItems o),
    Json.arr results, exc, finRes])

def run (fn : String) (j : Json) : Except String Json :=
  match fn with
  | "ctr" => runCtr j
  | "od" => runOD j
  | "cm" => runCM j
  | "ud" => runUD j
  | "ul" => runUL j
  | "us" => runUS j
  | "nt" => runNT j
  | _ => throw s!"unknown fn coll.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Coll
