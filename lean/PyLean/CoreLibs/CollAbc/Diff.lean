import PyLean.DiffCore
import PyLean.CoreLibs.CollAbc.Builtins

/-! Differential-testing handler for `corelibs` cases with `"fn": "collabc.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `collabc.` prefix.

Elements are ints. A case carries `bad`, an element whose `__eq__`/`__contains__` raises
`ValueError("bad")`, and `fail`, an index or key for which the container's primitive raises
`ValueError("fail")`, so that check order and which exception escapes are compared too. -/

namespace PyLean.CoreLibs.CollAbc

open Lean PyLean PyLean.Diff

def badExc : PyExc := .valueError "bad"
def failExc : PyExc := .valueError "fail"

/-- Element equality with one poisoned value on the left of `==`. -/
def intEq (bad : Option Int) : EqOps Int where
  is_ _ _ := false
  eq a b := if some a = bad then .error badExc else .ok (a == b)

def getIntList (j : Json) (key : String) : Except String (List Int) := do
  let v ← field j key
  let a ← v.getArr?
  a.toList.mapM (·.getInt?)

def getStrList (j : Json) : Except String (List String) := do
  let a ← j.getArr?
  a.toList.mapM (·.getStr?)

def encIntList (xs : List Int) : Json := toJson xs

def encRet {α : Type} (enc : α → Json) : Ret α → Json
  | .val a => Json.mkObj [("val", enc a)]
  | .notImplemented => "NotImplemented"

def getMro (j : Json) : Except String (List ClassDict) := do
  let v ← field j "mro"
  let a ← v.getArr?
  a.toList.mapM fun c => do
    let bs ← c.getArr?
    bs.toList.mapM fun p => do
      let n ← (← p.getArrVal? 0).getStr?
      let b ← (← p.getArrVal? 1).getBool?
      pure (n, b)

def faultSeq (xs : List Int) (fail : Option Int) : Seq Int :=
  ⟨fun i => if some i = fail then .error failExc else listGet xs i, .ok xs.length⟩

def faultMSeq (fail : Option Int) : MSeq (List Int) Int :=
  { listMSeq with getitem := fun s i => if some i = fail then .error failExc else listGet s i }

/-- The exception of an iterator that raises after its items. -/
def tailOf (b : Bool) : Option PyExc := if b then some (.valueError "itail") else none

def faultSet (bad : Option Int) (t : Bool) (xs : List Int) : SetV Int :=
  ⟨.ok xs.length, .ok xs, fun x => if some x = bad then .error badExc else .ok (decide (x ∈ xs)), tailOf t⟩

def faultMake (bad : Option Int) (xs : List Int) : SetV Int := faultSet bad false (dedup [] xs)

def faultMSet (bad : Option Int) (t : Bool) : MSet (List Int) Int :=
  { listMSet with view := faultSet bad t, fromIter := faultMake bad }

def faultMap (fail : Option Int) (t : Bool) (d : List (Int × Int)) : MapV Int Int :=
  ⟨fun k => if some k = fail then .error failExc else dictGet d k, .ok (d.map Prod.fst),
    .ok d.length, tailOf t⟩

def faultMMap (fail : Option Int) (t : Bool) : MMap (List (Int × Int)) Int Int :=
  { dictMMap with view := faultMap fail t }

def getPairs (j : Json) (key : String) : Except String (List (Int × Int)) := do
  let a ← (← field j key).getArr?
  a.toList.mapM fun p => do
    pure (← (← p.getArrVal? 0).getInt?, ← (← p.getArrVal? 1).getInt?)

def encPairs (xs : List (Int × Int)) : Json :=
  toJson (xs.map fun p => toJson [p.1, p.2])

def getOperand (bad : Option Int) (j : Json) : Except String (Operand Int) := do
  match ← getStr j "okind" with
  | "set" => pure (.set (faultSet bad (← getBool j "otail") (← getIntList j "other")))
  | "iter" => pure (.iterable (.ok (← getIntList j "other")) (tailOf (← getBool j "otail")))
  | _ => pure .other

def encSet : Ret (SetV Int) → Except String Json
  | .val s =>
    match s.iter with
    | .ok xs => .ok (Json.mkObj [("val", encIntList xs)])
    | .error _ => .error "result set does not iterate"
  | .notImplemented => .ok "NotImplemented"

def encPyList (r : Py (Ret (SetV Int))) : Except String Json :=
  match r with
  | .ok v => do pure (Json.mkObj [("ok", ← encSet v)])
  | .error e => .ok (encPy (fun (_ : Unit) => Json.null) (.error e))

/-- A `Gen` that plays a script: each resumption consumes one step. -/
def scriptGen : Gen (List (GenStep Int)) Int where
  send s _ := match s with
    | [] => (.stopped 0, [])
    | x :: xs => (x, xs)
  throwExit s := match s with
    | [] => (.raised generatorExit, [])
    | x :: xs => (x, xs)

def getScript (j : Json) : Except String (List (GenStep Int)) := do
  let a ← (← field j "script").getArr?
  a.toList.mapM fun p => do
    let k ← (← p.getArrVal? 0).getStr?
    let v ← (← p.getArrVal? 1).getInt?
    match k with
    | "y" => pure (.yielded v)
    | "r" => pure (.stopped v)
    | "exit" => pure (.raised generatorExit)
    | _ => pure (.raised (.valueError s!"{v}"))

def encStep : GenStep Int → Json
  | .yielded v => Json.mkObj [("y", toJson v)]
  | .stopped v => Json.mkObj [("r", toJson v)]
  | .raised e => Json.mkObj [("exc", toJson e.className), ("msg", toJson e.message)]

def getExcArg (j : Json) : Except String ExcArg := do
  match ← getStr j "k" with
  | "cls" => pure (.cls (← getStr j "n"))
  | "inst" => pure (.inst (← getStr j "n"))
  | _ => pure .other

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "check_methods" =>
    let mro ← getMro j
    let ms ← (← field j "methods") |> getStrList
    pure (Json.mkObj [("ok", encRet toJson (checkMethods mro ms))])
  | "hook" =>
    pure (Json.mkObj [("ok", encRet toJson
      (subclasshook (← getStr j "x") (← getStr j "cls") (← getMro j)))])
  | "stub" =>
    match stubBody (← getStr j "name") with
    | some (.returnsInt n) => pure (Json.mkObj [("ok", toJson n)])
    | some (.returnsBool b) => pure (Json.mkObj [("ok", toJson b)])
    | some (.yieldsNones n) => pure (Json.mkObj [("ok", toJson (n : Int))])
    | some (.raises c) => pure (Json.mkObj [("exc", toJson c), ("msg", toJson "~")])
    | none => throw "no stub"
  | "throw" =>
    let typ ← getExcArg (← field j "typ")
    let val ← match (← field j "val") with
      | .null => pure none
      | v => some <$> getExcArg v
    let tb ← getBool j "tb"
    match throwBody typ val tb with
    | .ok r => pure (Json.mkObj [("ok", Json.mkObj [("raised", toJson r.name),
        ("tb", toJson r.tracebackSet)])])
    | .error c => pure (Json.mkObj [("ok", Json.mkObj [("wrong", toJson c)])])
  | "gen_close" =>
    let script ← getScript j
    let kind ← getStr j "kind"
    let msg := match kind with
      | "gen" => genCloseMsg
      | "coro" => coroCloseMsg
      | _ => asyncCloseMsg
    let (r, s) := scriptGen.close msg script
    pure (Json.mkObj [("ok", Json.mkObj [("r", encPy (fun _ => Json.null) r),
      ("left", toJson s.length)])])
  | "gen_next" =>
    let script ← getScript j
    let (r, s) := scriptGen.next 0 script
    pure (Json.mkObj [("ok", Json.mkObj [("r", encStep r), ("left", toJson s.length)])])
  | "builtin_close" =>
    let script ← getScript j
    let (r, s) := builtinClose scriptGen script
    pure (Json.mkObj [("ok", Json.mkObj [("r", encPy (fun v => toJson v) r),
      ("left", toJson (0 : Nat))])])
  | "callable_new" =>
    let a ← field j "a"
    let r ← getStr j "r"
    let arg ← match (← getStr a "k") with
      | "seq" => pure (some (CallArg.tupleOrList ((← (← field a "items") |> getStrList)), r))
      | "ell" => pure (some (CallArg.ellipsis, r))
      | "param" => pure (some (CallArg.paramExpr (← getStr a "repr"), r))
      | "other" => pure (some (CallArg.other (← getStr a "repr"), r))
      | _ => pure none
    let pe := match arg with
      | some (.tupleOrList _, _) => false
      | _ => true
    let encRed : CallArg × String → Json := fun p => match p.1 with
      | .tupleOrList items => toJson items
      | .ellipsis => toJson "..."
      | .paramExpr r => toJson r
      | .other r => toJson r
    pure <| encPy (fun args => Json.mkObj [("args", toJson args),
        ("repr", toJson (callableRepr args pe)),
        ("reduce", encRed (callableReduceArgs args pe))]) (callableNew arg)
  | "callable_getitem" =>
    let a ← getStr j "a"
    let b ← getStr j "b"
    let new := match (← getStr j "shape") with
      | "tv" => [SubstArg.typ a, .typ "int", .typ b]
      | _ => [SubstArg.seq [a, b], .typ "int"]
    pure (encPy toJson (callableGetitem new))
  | "seq_iter" =>
    let xs ← getIntList j "xs"
    pure (encPy encIntList ((faultSeq xs (← getOptInt j "fail")).iterFrom (xs.length + 2) 0))
  | "seq_reversed" =>
    let xs ← getIntList j "xs"
    pure (encPy encIntList ((faultSeq xs (← getOptInt j "fail")).reversed))
  | "seq_contains" =>
    let xs ← getIntList j "xs"
    pure (encPy toJson ((faultSeq xs (← getOptInt j "fail")).containsFrom
      (intEq (← getOptInt j "bad")) (← getInt j "v") (xs.length + 2) 0))
  | "seq_count" =>
    let xs ← getIntList j "xs"
    pure (encPy (fun n => toJson n) ((faultSeq xs (← getOptInt j "fail")).countFrom
      (intEq (← getOptInt j "bad")) (← getInt j "v") (xs.length + 2) 0))
  | "seq_index" =>
    let xs ← getIntList j "xs"
    pure (encPy toJson ((faultSeq xs (← getOptInt j "fail")).index
      (intEq (← getOptInt j "bad")) (← getInt j "v") (← getInt j "start")
      (← getOptInt j "stop") (xs.length + 2)))
  | "list_index" =>
    let xs ← getIntList j "xs"
    pure (Json.mkObj [("ok", toJson ((listIndex (intEq none) xs (← getInt j "v")
      (← getInt j "start") ((← getOptInt j "stop").getD ssizeMax) (xs.length + 2)).toOption.join))])
  | "mseq_append" =>
    pure (encPy encIntList ((listMSeq).append (← getIntList j "xs") (← getInt j "v")))
  | "mseq_pop" =>
    let fail ← getOptInt j "fail"
    pure (encPy (fun (p : Int × List Int) => toJson [toJson p.1, encIntList p.2])
      ((faultMSeq fail).pop (← getIntList j "xs") (← getInt j "i")))
  | "mseq_clear" =>
    let xs ← getIntList j "xs"
    pure (encPy encIntList ((faultMSeq (← getOptInt j "fail")).clear (xs.length + 2) xs))
  | "mseq_reverse" =>
    pure (encPy encIntList ((faultMSeq (← getOptInt j "fail")).reverse (← getIntList j "xs")))
  | "mseq_extend" =>
    let xs ← getIntList j "xs"
    let vs ← match (← field j "vs") with
      | .null => pure none
      | _ => some <$> getIntList j "vs"
    pure (encPy encIntList ((faultMSeq (← getOptInt j "fail")).extend xs vs (xs.length + 2)))
  | "mseq_remove" =>
    let xs ← getIntList j "xs"
    pure (encPy encIntList ((faultMSeq (← getOptInt j "fail")).remove
      (intEq (← getOptInt j "bad")) xs (← getInt j "v") (xs.length + 2)))
  | "list_remove" =>
    let r := listRemove (intEq (← getOptInt j "bad")) (← getInt j "v") (← getIntList j "xs")
    pure (encPy (fun o => toJson o) r)
  | "bytestring_new" =>
    pure (Json.mkObj [("ok", toJson (byteStringMetaWarns (← getStr j "name")))])
  | "bytestring_check" =>
    let (w, a) := byteStringInstanceCheck (← getBool j "answer")
    pure (Json.mkObj [("ok", toJson [w, a])])
  | "view_repr" =>
    pure (Json.mkObj [("ok", toJson (viewRepr (← getStr j "cls") (← getStr j "r")))])
  | "set_cmp" =>
    let bad ← getOptInt j "bad"
    let s := faultSet bad (← getBool j "selftail") (← getIntList j "xs")
    let o ← getOperand bad j
    let r := match (← getStr j "op") with
      | "le" => s.le o
      | "lt" => s.lt o
      | "ge" => s.ge o
      | "gt" => s.gt o
      | _ => s.eq o
    pure (encPy (encRet toJson) r)
  | "set_op" =>
    let bad ← getOptInt j "bad"
    let s := faultSet bad (← getBool j "selftail") (← getIntList j "xs")
    let o ← getOperand bad j
    let f := faultMake bad
    encPyList (match (← getStr j "op") with
      | "and" => s.and f o
      | "or" => s.or f o
      | "sub" => s.sub f o
      | "rsub" => s.rsub f o
      | _ => s.xor f o)
  | "set_isdisjoint" =>
    let bad ← getOptInt j "bad"
    let s := faultSet bad (← getBool j "selftail") (← getIntList j "xs")
    pure (encPy toJson (s.isdisjoint (← getOperand bad j)))
  | "set_hash" =>
    let hs ← getIntList j "hashes"
    pure (Json.mkObj [("ok", toJson (setHash hs.length hs))])
  | "frozenset_hash" =>
    let hs ← getIntList j "hashes"
    let table := hs.map Slot.active ++ List.replicate (← getNat j "nulls") Slot.null
      ++ List.replicate (← getNat j "dummies") Slot.dummy
    pure (Json.mkObj [("ok", toJson (frozensetHash table))])
  | "mset_op" =>
    let bad ← getOptInt j "bad"
    let M := faultMSet bad (← getBool j "selftail")
    let xs ← getIntList j "xs"
    let o ← getOperand bad j
    let selfIt ← getBool j "selfit"
    let fuel := xs.length + 2
    let v ← match (← getStr j "op") with
      | "ior" => pure (M.ior xs o)
      | "iand" => pure (M.iand xs o)
      | "ixor" => pure (M.ixor xs (if selfIt then none else some o) fuel)
      | "isub" => pure (M.isub xs (if selfIt then none else some o) fuel)
      | "clear" => pure (M.clear fuel xs)
      | "remove" => pure (M.remove xs (← getInt j "v"))
      | "pop" => pure ((M.pop xs).map Prod.snd)
      | _ => throw "mset op"
    pure (encPy encIntList v)
  | "map_op" =>
    let fail ← getOptInt j "fail"
    let d ← getPairs j "d"
    let m := faultMap fail (← getBool j "selftail") d
    let k ← getInt j "k"
    let E := intEq (← getOptInt j "bad")
    match (← getStr j "op") with
    | "get" => pure (encPy toJson (m.get k (← getInt j "default")))
    | "contains" => pure (encPy toJson (m.contains k))
    | "items" => pure (encPy encPairs m.items)
    | "values" => pure (encPy encIntList m.values)
    | "valuecontains" => pure (encPy toJson (m.valuesContain E k))
    | "keyscontain" => pure (encPy toJson (m.keysView.contains k))
    | "itemcontains" =>
      let it : ItemArg Int Int ← match (← getStr j "ikind") with
        | "tuple" => pure (.pair k (← getInt j "v") true)
        | "list" => pure (.pair k (← getInt j "v") false)
        | "short" => pure (.wrongLen 1 true)
        | "long" => pure (.wrongLen 3 true)
        | _ => pure .notIterable
      match (← getStr j "who") with
      | "abc" => pure (encPy toJson (m.itemsContain (intEq none) it))
      | _ => pure (encPy toJson (dictItemsContain (dictMap d) (intEq none) it))
    | _ => throw "map op"
  | "mmap_op" =>
    let fail ← getOptInt j "fail"
    let M := faultMMap fail (← getBool j "selftail")
    let d ← getPairs j "d"
    let k ← getInt j "k"
    let enc := fun (p : Int × List (Int × Int)) => toJson [toJson p.1, encPairs p.2]
    match (← getStr j "op") with
    | "pop" => pure (encPy enc (M.pop d k none))
    | "popd" => pure (encPy enc (M.pop d k (some (← getInt j "default"))))
    | "popitem" =>
      pure (encPy (fun (p : (Int × Int) × List (Int × Int)) =>
        toJson [toJson [p.1.1, p.1.2], encPairs p.2]) (M.popitem d))
    | "clear" => pure (encPy encPairs (M.clear (d.length + 2) d))
    | "setdefault" => pure (encPy enc (M.setdefault d k (← getInt j "default")))
    | "update_map" =>
      pure (encPy encPairs (M.update d (.mapping (dictMap (← getPairs j "other")))
        (← getPairs j "kw")))
    | "update_pairs" =>
      pure (encPy encPairs (M.update d (.pairs (← getPairs j "other")) (← getPairs j "kw")))
    | _ => throw "mmap op"
  | _ => throw s!"unknown fn collabc.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.CollAbc
