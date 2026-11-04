import PyLean.DiffCore
import PyLean.CoreLibs.CollAbc.Builtins

/-! Differential-testing handler for `corelibs` cases with `"fn": "collabc.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `collabc.` prefix.

Elements are ints. A case carries `bad`, an element whose `__eq__`/`__contains__` raises
`ValueError("bad")`, `fail`, an index or key for which the container's primitive raises
`ValueError("fail")` (or `KeyError` when `failkey`), and `uh`, an element the set constructor refuses with
`TypeError("unhashable")`, so that check order and which exception escapes are compared too. -/

namespace PyLean.CoreLibs.CollAbc

open Lean PyLean PyLean.Diff

def badExc : PyExc := .valueError "bad"
def failExc : PyExc := .valueError "fail"
def lenExc : PyExc := .valueError "len"

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

def getOptStr (j : Json) (key : String) : Option String :=
  match j.getObjVal? key with
  | .ok (.str s) => some s
  | _ => none

/-- The exception of a `__len__` that raises, by class name. -/
def lenFail (k : Option String) : Option PyExc :=
  match k with
  | some "TypeError" => some (.typeError "len")
  | some _ => some lenExc
  | none => none

def faultSeq (xs : List Int) (fail : Option Int) (badlen : Bool := false) : Seq Int :=
  ⟨fun i => if some i = fail then .error failExc else listGet xs i,
    if badlen then .error lenExc else .ok xs.length⟩

def faultMSeq (fail : Option Int) (lenexc : Option PyExc) : MSeq (List Int) Int :=
  { listMSeq with
    getitem := fun s i => if some i = fail then .error failExc else listGet s i
    len := fun s => match lenexc with | some e => .error e | none => .ok s.length }

/-- The exception of an iterator that raises after its items. -/
def tailOf (b : Bool) : Option PyExc := if b then some (.valueError "itail") else none

def faultSet (bad : Option Int) (t : Bool) (xs : List Int) : SetV Int :=
  ⟨.ok xs.length, .ok xs, fun x => if some x = bad then .error badExc else .ok (decide (x ∈ xs)), tailOf t⟩

/-- The class's constructor: insertion in order, refusing `uh`. -/
def faultBuilder (bad uh : Option Int) : FromIter (List Int) Int (SetV Int) :=
  ⟨.ok [], fun r x => if some x = uh then .error (.typeError "unhashable") else .ok (listAdd r x),
    fun r => .ok (faultSet bad false r)⟩

def faultMSet (bad uh : Option Int) (t : Bool) : MSet (List Int) (List Int) Int :=
  { view := faultSet bad t, add := fun s x => .ok (listAdd s x), discard := fun s x => .ok (s.erase x),
    fromIter := faultBuilder bad uh }

def faultMap (fail : Option Int) (failKey : Bool) (t : Bool) (d : List (Int × Int)) (ovr : Bool := false) :
    MapV Int Int :=
  { getitem := fun k => if some k = fail then .error (if failKey then .keyError "~k" else failExc) else dictGet d k
    iter := .ok (d.map Prod.fst), len := .ok d.length, tail := tailOf t
    containsOverride := if ovr then some (fun k => .ok (k % 2 == 0)) else none }

def faultMMap (fail : Option Int) (t : Bool) : MMap (List (Int × Int)) Int Int :=
  { dictMMap with view := fun d => faultMap fail false t d }

def getPairs (j : Json) (key : String) : Except String (List (Int × Int)) := do
  let a ← (← field j key).getArr?
  a.toList.mapM fun p => do
    pure (← (← p.getArrVal? 0).getInt?, ← (← p.getArrVal? 1).getInt?)

def encPairs (xs : List (Int × Int)) : Json :=
  toJson (xs.map fun p => toJson [p.1, p.2])

def getOperand (bad : Option Int) (j : Json) : Except String (Operand Int) := do
  let t := tailOf (← getBool j "otail")
  match ← getStr j "okind" with
  | "set" => pure (.set (faultSet bad (← getBool j "otail") (← getIntList j "other")))
  | "iter" => pure (.iterable true (.ok (← getIntList j "other")) t)
  | "gi" => pure (.iterable false (.ok (← getIntList j "other")) t)
  | "rsub" => pure (.iterable false (.error (.typeError "~'collabc_R' object is not iterable")))
  | _ => pure (.iterable false (.error (.typeError "'int' object is not iterable")))

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

/-- The objects of the `throw` cases, as the harness builds them. -/
def getTObj (j : Json) : Except String TObj := do
  match ← getStr j "k" with
  | "cls" => let n ← getStr j "n"; pure (.excClass n (.obj (.excInst n false)))
  | "cls_ude" => pure (.excClass "UnicodeDecodeError"
      (.raises (.typeError "function takes exactly 5 arguments (0 given)")))
  | "cls_bad" => pure (.excClass "collabc_X" (.obj (.other "int" none none)))
  | "inst" => pure (.excInst (← getStr j "n") false)
  | "func" => pure (.other "function" (some (.obj (.excInst "KeyError" false))) none)
  | "wtb" => pure (.other "collabc_W" none (some (.obj (.excInst "KeyError" false))))
  | _ => pure (.other "int" none none)

def getTb (j : Json) : Except String TbArg := do
  match ← getStr j "tb" with
  | "tb" => pure .traceback
  | "bad" => pure .other
  | _ => pure .absent

/-- A `Callable` argument as the harness spells it. -/
partial def getCArg (j : Json) : Except String CArg := do
  match j with
  | .str "..." => pure .ellipsis
  | .str "~P" => pure (.obj "typing" "ParamSpec" "~P")
  | .str "C" => pure (.obj "typing" "_ConcatenateGenericAlias" "typing.Concatenate[int, ~P]")
  | .str n => pure (.obj "builtins" "type" n)
  | .arr a => pure (.list (← a.toList.mapM getCArg))
  | _ => match j.getObjVal? "t" with
    | .ok (.arr a) => pure (.tuple (← a.toList.mapM getCArg))
    | _ => throw "carg"

partial def encCArg : CArg → Json
  | .ellipsis => toJson "..."
  | .obj _ "_ConcatenateGenericAlias" _ => toJson "C"
  | .obj _ _ r => toJson r
  | .list items => Json.arr (items.map encCArg).toArray
  | .tuple items => Json.mkObj [("t", Json.arr (items.map encCArg).toArray)]

/-- `repr()` of an argument inside a list, as `type_repr` shows a list. -/
partial def pyRepr : CArg → String
  | .ellipsis => "Ellipsis"
  | .obj "builtins" _ r => s!"<class '{r}'>"
  | .obj _ _ r => r
  | .list items => "[" ++ ", ".intercalate (items.map pyRepr) ++ "]"
  | .tuple items => "(" ++ ", ".intercalate (items.map pyRepr) ++ (if items.length = 1 then ",)" else ")")

/-- `annotationlib.type_repr`. -/
def typeRepr : CArg → String
  | .ellipsis => "..."
  | .obj _ _ r => r
  | a => pyRepr a

/-- `GenericAlias.__repr__` of `collections.abc.Callable[args]`. -/
partial def gaItem : CArg → String
  | .ellipsis => "..."
  | .obj _ _ r => r
  | .list items => "[" ++ ", ".intercalate (items.map gaItem) ++ "]"
  | a => pyRepr a

def gaRepr (args : List CArg) : String := s!"collections.abc.Callable[{", ".intercalate (args.map gaItem)}]"

def encArgs (args : List CArg) : Json := Json.arr (args.map encCArg).toArray

def dictEqInt (a b : List (Int × Int)) : Py Bool :=
  .ok (decide (a.length = b.length ∧ ∀ p ∈ a, b.lookup p.1 = some p.2))

/-- `key, value = item` for the harness's item kinds. -/
def getItemArg (k v : Int) (kind : String) : ItemArg Int Int :=
  match kind with
  | "tuple" | "list" => .two k v none
  | "short" => .one 1 none
  | "empty" => .zero none
  | "long" => .many 1 2 (some 3)
  | "dict3" => .many 1 3 (some 3)
  | "str3" | "iter3" | "sublist3" => .many 0 0 none
  | "gen2t" => .two k v (some (.valueError "itail"))
  | "gen1t" => .one k (some (.valueError "itail"))
  | _ => .notIterable "int"

def getAct : String → WarnAction
  | "error" => .error
  | "always" => .always
  | _ => .ignore

def encWarned (ws : List Warned) : Json := toJson (ws.map fun w => toJson [w.category, w.message])

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
    | some (.gen n) => pure (Json.mkObj [("ok", toJson (n : Int))])
    | some (.raises e) | some (.awaitRaises e) => pure (encPy (fun (_ : Unit) => Json.null) (.error e))
    | none => throw "no stub"
  | "throw" =>
    let typ ← getTObj (← field j "typ")
    let val ← match (← field j "val") with
      | .null => pure none
      | v => some <$> getTObj v
    match throwBody typ val (← getTb j) with
    | .ok r => pure (Json.mkObj [("ok", Json.mkObj [("raised", toJson r.name), ("tb", toJson r.tracebackSet)])])
    | .error e => pure (encPy (fun (_ : Unit) => Json.null) (.error e))
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
  | "gen_next" | "agen_next" =>
    let script ← getScript j
    let (r, s) := scriptGen.next 0 script
    pure (Json.mkObj [("ok", Json.mkObj [("r", encStep r), ("left", toJson s.length)])])
  | "builtin_close" =>
    let script ← getScript j
    let msg := if (← getStr j "kind") == "coro" then builtinCoroCloseMsg else builtinGenCloseMsg
    let (r, _) := builtinClose scriptGen msg script
    pure (Json.mkObj [("ok", Json.mkObj [("r", encPy (fun v => toJson v) r),
      ("left", toJson (0 : Nat))])])
  | "builtin_aclose" =>
    let script ← getScript j
    let (r, _) := builtinAclose scriptGen script
    pure (Json.mkObj [("ok", Json.mkObj [("r", encPy (fun _ => Json.null) r), ("left", toJson (0 : Nat))])])
  | "callable_new" =>
    let a ← field j "a"
    let r ← getCArg (← field j "r")
    let arg ← match a with
      | .str "notpair" => pure none
      | _ => pure (some (← getCArg a, r))
    pure <| encPy (fun args =>
      Json.mkObj [("args", encArgs args),
        ("repr", encPy toJson (callableRepr typeRepr gaRepr args)),
        ("reduce", encPy encArgs (callableReduce args)),
        ("rt", encPy encArgs (callableReduce args >>= fun a => callableNew (asPair a)))]) (callableNew arg)
  | "callable_getitem" =>
    let args ← (← field j "new").getArr?
    let new ← args.toList.mapM getCArg
    pure (encPy encArgs (callableGetitem new))
  | "seq_iter" =>
    let xs ← getIntList j "xs"
    pure (encPy encIntList ((faultSeq xs (← getOptInt j "fail")).iterFrom (xs.length + 2) 0))
  | "seq_reversed" =>
    let xs ← getIntList j "xs"
    pure (encPy encIntList ((faultSeq xs (← getOptInt j "fail") (← getBool j "badlen")).reversed))
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
    pure (encPy toJson ((faultSeq xs (← getOptInt j "fail") (← getBool j "badlen")).index
      (intEq (← getOptInt j "bad")) (← getInt j "v") (← getInt j "start")
      (← getOptInt j "stop") (xs.length + 2)))
  | "list_index" =>
    let xs ← getIntList j "xs"
    pure (Json.mkObj [("ok", toJson ((listIndex (intEq none) xs (← getInt j "v")
      (← getInt j "start") ((← getOptInt j "stop").getD ssizeMax) (xs.length + 2)).toOption.join))])
  | "mseq_append" =>
    pure (encPy encIntList ((faultMSeq none (lenFail (getOptStr j "lenexc"))).append (← getIntList j "xs")
      (← getInt j "v")))
  | "mseq_pop" =>
    let fail ← getOptInt j "fail"
    pure (encPy (fun (p : Int × List Int) => toJson [toJson p.1, encIntList p.2])
      ((faultMSeq fail none).pop (← getIntList j "xs") (← getInt j "i")))
  | "mseq_clear" =>
    let xs ← getIntList j "xs"
    pure (encPy encIntList ((faultMSeq (← getOptInt j "fail") none).clear (xs.length + 2) xs))
  | "mseq_reverse" =>
    pure (encPy encIntList ((faultMSeq (← getOptInt j "fail") none).reverse (← getIntList j "xs")))
  | "mseq_extend" =>
    let xs ← getIntList j "xs"
    let vs ← match (← field j "vs") with
      | .null => pure .self_
      | _ => pure (.iter (.ok (← getIntList j "vs")) (tailOf (← getBool j "vtail")))
    let M := faultMSeq (← getOptInt j "fail") (lenFail (getOptStr j "lenexc"))
    let r := if (← getBool j "iadd") then MSeq.iadd (fun s a => M.extend (fun _ => true) s a (xs.length + 2)) xs vs
      else M.extend (fun _ => true) xs vs (xs.length + 2)
    pure (encPy encIntList r)
  | "mseq_remove" =>
    let xs ← getIntList j "xs"
    pure (encPy encIntList ((faultMSeq (← getOptInt j "fail") none).remove
      (intEq (← getOptInt j "bad")) xs (← getInt j "v") (xs.length + 2)))
  | "list_remove" =>
    let r := listRemove (intEq (← getOptInt j "bad")) (← getInt j "v") (← getIntList j "xs")
    pure (encPy (fun o => toJson o) r)
  | "bytestring_new" =>
    let (ws, r) := byteStringMetaNew (getAct (← getStr j "act")) (← getStr j "name") (.ok ())
    pure (Json.mkObj [("ok", toJson [encWarned ws, encPy (fun _ => Json.null) r])])
  | "module_getattr" =>
    let act ← match (← getStr j "act") with
      | "error" => pure WarnAction.error
      | "always" => pure .always
      | _ => pure .ignore
    let name ← getStr j "name"
    let (ws, loaded, r) := moduleGetattr act false name
    pure (Json.mkObj [("ok", toJson [toJson (ws.map fun w => toJson [w.category, w.message]), toJson loaded,
      encPy (fun _ => Json.null) r])])
  | "bytestring_check" =>
    let (ws, r) := byteStringInstanceCheck (getAct (← getStr j "act")) (.ok (← getBool j "answer"))
    pure (Json.mkObj [("ok", toJson [encWarned ws, encPy toJson r])])
  | "view_repr" =>
    let mr : Py String := match (← getStr j "kind") with
      | "raise" => .error (.valueError "repr")
      | "notstr" => .error (.typeError "~__repr__() must return a str, not int")
      | _ => .ok "{1: 2}"
    pure (encPy toJson (viewRepr (← getStr j "cls") mr))
  | "from_iterable" =>
    let elems : List (Option Int) ← (← (← field j "xs").getArr?).toList.mapM fun h => match h with
      | .null => pure none
      | v => some <$> v.getInt?
    let t := tailOf (← getBool j "tail")
    match (← getStr j "kind") with
    | "set" =>
      let uh ← getOptInt j "uh"
      let r := build (faultBuilder none uh) (.ok (elems.filterMap id)) t
      pure (encPy (fun (s : SetV Int) => match s.iter with | .ok xs => encIntList xs | .error _ => Json.null) r)
    | _ =>
      let hash : Option Int → Py Unit := fun
        | none => .error (.typeError "cannot use 'list' as a set element (unhashable type: 'list')")
        | some _ => .ok ()
      let r := viewFromIterable hash () (.ok elems) t
      pure (encPy (fun (xs : List (Option Int)) => encIntList ((xs.filterMap id).mergeSort (· ≤ ·))) r)
  | "set_cmp" =>
    let bad ← getOptInt j "bad"
    let s0 := faultSet bad (← getBool j "selftail") (← getIntList j "xs")
    let s := if (← getBool j "badlen") then { s0 with len := .error lenExc } else s0
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
    let B := faultBuilder bad (← getOptInt j "uh")
    let minus : SetV Int → SetV Int → Py (SetV Int) := fun a b =>
      retOr (a.sub B (.set b)) (.error (.typeError "~unsupported operand type(s) for -"))
    let bor : SetV Int → SetV Int → Py (SetV Int) := fun a b =>
      retOr (a.or B (.set b)) (.error (.typeError "~unsupported operand type(s) for |"))
    encPyList (match (← getStr j "op") with
      | "and" => s.and B o
      | "or" => s.or B o
      | "sub" => s.sub B o
      | "rsub" => s.rsub B o
      | _ => s.xor B minus bor o)
  | "set_isdisjoint" =>
    let bad ← getOptInt j "bad"
    let s := faultSet bad (← getBool j "selftail") (← getIntList j "xs")
    pure (encPy toJson (s.isdisjoint (← getOperand bad j)))
  | "set_hash" =>
    let hs ← (← field j "hashes").getArr?
    let elems : List (Option Int) ← hs.toList.mapM fun h => match h with
      | .null => pure none
      | v => some <$> v.getInt?
    let badlen ← getBool j "badlen"
    let len : Py Nat := if badlen then .error lenExc else .ok elems.length
    let s : SetV (Option Int) := { len := len, iter := .ok elems, contains := fun _ => .ok false }
    let hash : Option Int → Py Int := fun
      | none => .error (.typeError "unhashable type: 'list'")
      | some h => .ok (if h = -1 then -2 else h)
    pure (encPy toJson (s.hash hash))
  | "frozenset_hash" =>
    let hs ← getIntList j "hashes"
    let table := hs.map Slot.active ++ List.replicate (← getNat j "nulls") Slot.null
      ++ List.replicate (← getNat j "dummies") Slot.dummy
    pure (Json.mkObj [("ok", toJson (frozensetHash table))])
  | "mset_op" =>
    let bad ← getOptInt j "bad"
    let M := faultMSet bad (← getOptInt j "uh") (← getBool j "selftail")
    let xs ← getIntList j "xs"
    let o ← getOperand bad j
    let selfIt ← getBool j "selfit"
    let fuel := xs.length + 2
    let rs : Option (Py (Ret (SetV Int))) ← match ← getStr j "okind" with
      | "rsub" => pure (some (.ok (.val (faultSet bad false (← getIntList j "other")))))
      | "set" => pure (some (.ok .notImplemented))
      | _ => pure none
    let v ← match (← getStr j "op") with
      | "ior" => pure (M.ior xs o)
      | "iand" => pure (M.iand xs o rs false)
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
    let m := faultMap fail (← getBool j "failkey") (← getBool j "selftail") d (← getBool j "ovr")
    let k ← getInt j "k"
    let E := intEq (← getOptInt j "bad")
    match (← getStr j "op") with
    | "get" => pure (encPy toJson (m.get k (← getInt j "default")))
    | "contains" => pure (encPy toJson (m.contains k))
    | "items" => pure (encPy encPairs m.items)
    | "values" => pure (encPy encIntList m.values)
    | "valuecontains" => pure (encPy toJson (m.valuesContain E k))
    | "keyscontain" => pure (encPy toJson (m.keyIn k))
    | "eq" =>
      let o := faultMap none false (← getBool j "otail") (← getPairs j "d2")
      pure (encPy (encRet toJson) (mappingEq (fun _ => .ok ()) dictEqInt m (some o)))
    | "itemcontains" =>
      let kind ← getStr j "ikind"
      let it := getItemArg k (← getInt j "v") kind
      match (← getStr j "who") with
      | "abc" => pure (encPy toJson (m.itemsContain (intEq none) it))
      | _ => pure (encPy toJson (dictItemsContain (dictMap d) (intEq none) (kind == "tuple") it))
    | _ => throw "map op"
  | "mmap_op" =>
    let fail ← getOptInt j "fail"
    let M := faultMMap fail (← getBool j "selftail")
    let d ← getPairs j "d"
    let k ← getInt j "k"
    let ot := tailOf (← getBool j "otail")
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
      let o := faultMap (← getOptInt j "ofail") false (← getBool j "otail") (← getPairs j "other")
      pure (encPy encPairs (M.update d (.mapping o) (← getPairs j "kw")))
    | "update_keys" =>
      let o ← getPairs j "other"
      let gi := (faultMap (← getOptInt j "ofail") false false o).getitem
      pure (encPy encPairs (M.update d (.other (.ok true) (.ok (o.map Prod.fst)) ot gi (.ok []) none)
        (← getPairs j "kw")))
    | "update_hasattr" =>
      pure (encPy encPairs (M.update d (.other (.error (.valueError "ga")) (.ok []) none (fun _ => .ok 0) (.ok [])
        none) (← getPairs j "kw")))
    | "update_pairs" =>
      let items ← (← field j "items").getArr?
      let args ← items.toList.mapM fun it => do
        match it with
        | .str kind => pure (getItemArg 0 0 kind)
        | p => pure (.two (← (← p.getArrVal? 0).getInt?) (← (← p.getArrVal? 1).getInt?) none)
      pure (encPy encPairs (M.update d (.other (.ok false) (.ok []) none (fun _ => .ok 0) (.ok args) ot)
        (← getPairs j "kw")))
    | _ => throw "mmap op"
  | _ => throw s!"unknown fn collabc.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.CollAbc
