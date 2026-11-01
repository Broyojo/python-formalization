import PyLean.DiffCore
import PyLean.CoreLibs.Operator.Model

/-! Differential-testing handler for `corelibs` cases with `"fn": "operator.<name>"`. The dispatcher in
`CoreLibs/Diff.lean` strips the `operator.` prefix. `"twin"` selects C or Python. -/

namespace PyLean.CoreLibs.Operator

open Lean PyLean PyLean.Diff

def getArr (j : Json) (key : String) : Except String (List Json) := do
  pure (← (← field j key).getArr?).toList

def getIntList (j : Json) (key : String) : Except String (List Int) := do
  (← getArr j key).mapM (·.getInt?)

def okJ (j : Json) : Json := Json.mkObj [("ok", j)]

/-- A scripted slot: absent, returning a tag, returning `NotImplemented`, or raising. -/
def slotOf (s : String) (tag : Int) : Option (Int → Int → Py (Ret Int)) :=
  match s with
  | "none" => none
  | "val" => some fun _ _ => .ok (.val tag)
  | "ni" => some fun _ _ => .ok .notImplemented
  | _ => some fun _ _ => .error (.valueError "slot")

def ternaryOf (s : String) (b : Bool) : Int → Int → Py (Ret Bool) := fun _ _ =>
  match s with
  | "val" => .ok (.val b)
  | "raise" => .error (.valueError "slot")
  | _ => .ok .notImplemented

/-- The objects of the `concat` cases. `tag` is the type name of the result. -/
def concatArgs (a b : String) : ConcatArgs String :=
  let seq (t : String) := t == "list" || t == "tuple" || t == "seqadd" || t == "radd"
  let builtinSeq (t : String) := t == "list" || t == "tuple"
  let builtinConcat : String → String → Py String := fun x y =>
    if x == y then .ok x
    else if x == "list" then .error (.typeError "~can only concatenate list")
    else .error (.typeError "~can only concatenate tuple")
  let nb : String → String → Py (Ret String) := fun x y =>
    if x == "seqadd" || x == "plain" then .ok (.val x)
    else if y == "radd" && x != "radd" then .ok (.val y)
    else .ok .notImplemented
  { hasGetitem := seq a || a == "dict"
    sqConcat := if builtinSeq a then some builtinConcat else none
    sqInplace := if a == "list" then some fun x y =>
        (if y == "plain" || y == "int" then .error (.typeError "~object is not iterable")
         else .ok x) else none
    seqA := seq a
    seqB := seq b
    nbAdd := nb
    nbIAdd := nb }

def getHintObj (j : Json) : Except String HintObj := do
  let len : Py Nat ← match (← field j "len") with
    | .null => pure (.error (.typeError "no len"))
    | .str "raise" => pure (.error (.valueError "len"))
    | v => do pure (.ok (← v.getNat?))
  let hint : Option (Py HintRet) ← match (← field j "hint") with
    | .null => pure none
    | .str "ni" => pure (some (.ok .notImplemented))
    | .str "typeerror" => pure (some (.error (.typeError "hint")))
    | .str "raise" => pure (some (.error (.valueError "hint")))
    | .str "str" => pure (some (.ok (.other "str")))
    | v => do pure (some (.ok (.int (← v.getInt?))))
  pure ⟨len, hint⟩

def getDefault (j : Json) : Except String HintDefault := do
  match ← getStr j "dkind" with
  | "int" => pure (.int (← getInt j "d"))
  | "index" => pure (.indexable (← getInt j "d"))
  | _ => pure (.other "str")

def attrWorld : GetAttr String := fun o n =>
  if n == "" || n == "x" then .error (.named "AttributeError" "~no attribute")
  else .ok (o ++ "." ++ n)

def getDigest (j : Json) : Except String DigestArg := do
  match ← getStr j "k" with
  | "str" => pure (.str (← getBool j "ascii") ((← getIntList j "data").map Int.toNat))
  | "bytes" => pure (.buffer ((← getIntList j "data").map Int.toNat))
  | _ => pure (.other "int")

def getCells (j : Json) : Except String (List Cell) := do
  (← getArr j "cells").mapM fun c => do
    match ← getStr c "k" with
    | "atom" => pure (.atom (← getInt c "n"))
    | "list" => pure (.list ((← getIntList c "items").map Int.toNat))
    | "tuple" => pure (.tuple ((← getIntList c "items").map Int.toNat))
    | _ =>
      let ks ← getIntList c "items"
      pure (.dict ((ks.toArray.toList.zipIdx.filterMap fun p =>
        if p.2 % 2 == 0 then some (p.1.toNat, (ks.getD (p.2 + 1) 0).toNat) else none)))

/-- The result graph, by depth-first search with back references, as the Python side renders it. -/
partial def render (h : Heap) (seen : List Nat) (x : Nat) : List Nat × Json :=
  match h.get x with
  | .atom n => (seen, toJson [toJson "atom", toJson n])
  | c =>
    match seen.idxOf? x with
    | some i => (seen, toJson [toJson "ref", toJson i])
    | none =>
      let seen := seen ++ [x]
      let many (items : List Nat) : List Nat × List Json :=
        items.foldl (fun (acc : List Nat × List Json) i =>
          let (s, j) := render h acc.1 i
          (s, acc.2 ++ [j])) (seen, [])
      match c with
      | .list items =>
        let (s, js) := many items
        (s, toJson [toJson "list", toJson js])
      | .tuple items =>
        let (s, js) := many items
        (s, toJson [toJson "tuple", toJson js])
      | .dict items =>
        let (s, js) := many (items.flatMap fun p => [p.1, p.2])
        (s, toJson [toJson "dict", toJson js])
      | .atom n => (seen, toJson n)

def run (fn : String) (j : Json) : Except String Json := do
  let c := (j.getObjVal? "twin").toOption.bind (·.getStr?.toOption) == some "c"
  match fn with
  | "binop" =>
    let S : BinSlots Int := ⟨slotOf (← getStr j "l") 1, slotOf (← getStr j "r") 2, ← getBool j "sub"⟩
    pure (encPy toJson (binaryOp S (← getStr j "sym") "A" "B" 0 0))
  | "iop" =>
    let S : BinSlots Int := ⟨slotOf (← getStr j "l") 1, slotOf (← getStr j "r") 2, ← getBool j "sub"⟩
    pure (encPy toJson (inplaceOp (slotOf (← getStr j "i") 3) S (← getStr j "sym") "A" "B" 0 0))
  | "cmp" =>
    let S : CmpSlots Int := ⟨ternaryOf (← getStr j "l") true, ternaryOf (← getStr j "r") false,
      ← getBool j "sub"⟩
    let op ← match ← getStr j "op" with
      | "lt" => pure RichOp.lt
      | "le" => pure .le
      | "eq" => pure .eq
      | "ne" => pure .ne
      | "gt" => pure .gt
      | _ => pure .ge
    pure (encPy toJson (richCompare S op false "A" "B" 0 0))
  | "unary" =>
    let has ← getBool j "has"
    pure (encPy toJson (unaryOp (if has then some (fun (_ : Int) => .ok 4) else none)
      (← getStr j "desc") "A" 0))
  | "index" =>
    let s ← match ← getStr j "k" with
      | "int" => pure (IndexSlot.int (← getInt j "n"))
      | "bad" => pure .badResult
      | _ => pure .none
    pure (encPy toJson ((if c then indexC else indexPy) s))
  | "concat" =>
    let a ← getStr j "a"
    let b ← getStr j "b"
    let A := concatArgs a b
    let tn (s : String) := match s with
      | "seqadd" => "SeqAdd"
      | "radd" => "RAdd"
      | "plain" => "Plain"
      | o => o
    pure (encPy toJson ((if ← getBool j "inplace" then
        (if c then iconcatC A (tn a) else iconcatPy A (tn a) (tn b))
      else (if c then concatC A (tn a) else concatPy A (tn a) (tn b))) a b))
  | "count_of" =>
    let bad ← getOptInt j "bad"
    let same : Same Int := fun x y => if some x = bad then .error (.valueError "eq") else .ok (x == y)
    let err : Option PyExc := if ← getBool j "itfail" then some (.valueError "it") else none
    pure (encPy toJson (countOf same (← getInt j "b") (← getIntList j "xs") err))
  | "index_of" =>
    let bad ← getOptInt j "bad"
    let same : Same Int := fun x y => if some x = bad then .error (.valueError "eq") else .ok (x == y)
    let err : Option PyExc := if ← getBool j "itfail" then some (.valueError "it") else none
    pure (encPy toJson (indexOf same (← getInt j "b") 0 (← getIntList j "xs") err))
  | "length_hint" =>
    pure (encPy toJson ((if c then lengthHintC else lengthHintPy) (← getHintObj j) (← getDefault j)))
  | "itemgetter" =>
    let xs ← getIntList j "xs"
    let items ← getIntList j "items"
    pure (encPy toJson (itemgetterPy (tupleGet xs) items))
  | "itemgetter_fast" =>
    let xs ← getIntList j "xs"
    pure (encPy toJson (itemgetterFast xs (← getInt j "i") (tupleGet xs)))
  | "getter_repr" =>
    let items ← (← getArr j "items").mapM (·.getStr?)
    pure (okJ (toJson ((if c then getterReprC else getterReprPy) (← getStr j "cls") items)))
  | "attrgetter" =>
    let args ← (← getArr j "attrs").mapM fun a => match a with
      | .str s => pure (AttrArg.str s)
      | _ => pure .other
    pure (encPy toJson (do attrgetterCall attrWorld "o" (← attrgetterNew args)))
  | "mc_new" =>
    let name : Option AttrArg ← match (← field j "name") with
      | .null => pure none
      | .str "BAD" => pure (some .other)
      | .str s => pure (some (.str s))
      | _ => throw "name"
    pure (encPy toJson ((if c then methodcallerNewC else methodcallerNewPy) name))
  | "mc_call" =>
    let args ← getIntList j "args"
    let kw ← (← getArr j "kw").mapM fun p => do
      pure (← (← p.getArrVal? 0).getStr?, ← (← p.getArrVal? 1).getInt?)
    let (flat, names) := vectorcallArgs args kw
    let call := unflatten "m" flat names
    pure (okJ (toJson [toJson call.args, toJson (call.kw.map fun p => toJson [toJson p.1, toJson p.2])]))
  | "mc_repr" =>
    let args ← (← getArr j "args").mapM (·.getStr?)
    let kw ← (← getArr j "kw").mapM fun p => do
      pure (← (← p.getArrVal? 0).getStr?, ← (← p.getArrVal? 1).getStr?)
    pure (okJ (toJson (methodcallerRepr "operator.methodcaller" "'m'" args kw)))
  | "digest" =>
    pure (encPy toJson (compareDigest (← getDigest (← field j "a")) (← getDigest (← field j "b"))))
  | "deepcopy" =>
    let cells ← getCells j
    let h : Heap := ⟨cells, []⟩
    let x ← getNat j "root"
    match deepcopy (4 * cells.length + 8) h x with
    | .ok (h', y) => pure (okJ (toJson [(render h' [] y).2, toJson (y == x)]))
    | .error _ => throw "deepcopy fuel"
  | "copy_route" =>
    let k ← match ← getStr j "k" with
      | "atomic" => pure CopyKind.atomic
      | "container" => pure .builtinContainer
      | "type" => pure .isType
      | "copy" => pure .hasCopy
      | "str" => pure .reduceStr
      | _ => pure (.reduceTuple (← getNat j "n"))
    pure (encPy toJson (copyRoute k))
  | "replace" =>
    pure (encPy (fun _ => Json.null) (replaceRoute (← getBool j "has") "X"))
  | "deep_method" =>
    let h : Heap := ⟨[.atom 1, .list [0]], []⟩
    match deepMethod 8 h 9 (← getNat j "self") with
    | .ok (_, f, s) => pure (okJ (toJson [f == 9, s == (← getNat j "self")]))
    | .error _ => throw "fuel"
  | "subscript" =>
    let a := (← getIntList j "xs")
    let i ← getInt j "i"
    let get : Int → Int → Py Int := fun _ k => tupleGet a k
    let has : Int → Int → Py Bool := fun _ k => .ok (a.contains k)
    match ← getStr j "op" with
    | "get" => pure (encPy toJson (getitemOp get 0 i))
    | _ => pure (encPy toJson (containsOp has 0 i))
  | "call_op" =>
    let args ← getIntList j "args"
    pure (encPy toJson (callOp (fun _ rest => .ok (rest.length : Int)) args))
  | "update_abstract" =>
    let parents ← (← getArr j "parents").mapM fun p => do (← p.getArr?).toList.mapM (·.getStr?)
    let abstractNames ← (← getArr j "abstract").mapM (·.getStr?)
    let own ← (← getArr j "own").mapM fun p => do
      pure (← (← p.getArrVal? 0).getStr?, ← (← p.getArrVal? 1).getBool?)
    let c : AbcClass := ⟨← getBool j "isabc", parents, fun n => abstractNames.contains n, own⟩
    pure (okJ (toJson ((updateAbstract c).map fun l => l.mergeSort (· ≤ ·) |>.eraseDups)))
  | "abc_check" =>
    let hooks ← (← getArr j "hooks").mapM fun p => do
      pure (← (← p.getArrVal? 0).getNat?, ← (← p.getArrVal? 1).getNat?, ← (← p.getArrVal? 2).getBool?)
    let tbl (key : String) : Except String (List (List Nat)) := do
      (← getArr j key).mapM fun r => do (← r.getArr?).toList.mapM (·.getNat?)
    let mro ← tbl "mro"
    let reg ← tbl "reg"
    let subs ← tbl "subs"
    let W : AbcWorld := ⟨fun a b => (hooks.find? (fun h => h.1 == a && h.2.1 == b)).map (·.2.2),
      fun c => mro.getD c [], fun c => reg.getD c [], fun c => subs.getD c []⟩
    pure (okJ (toJson (abcSubclassCheck W 12 (← getNat j "cls") (← getNat j "sub"))))
  | _ => throw s!"unknown fn operator.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Operator
