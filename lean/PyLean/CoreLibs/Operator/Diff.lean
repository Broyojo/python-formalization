import PyLean.DiffCore
import PyLean.CoreLibs.Operator.Getters
import PyLean.CoreLibs.Operator.Copy
import PyLean.CoreLibs.Operator.Abc

/-! Differential-testing handler for `corelibs` cases with `"fn": "operator.<name>"`. The dispatcher in
`CoreLibs/Diff.lean` strips the `operator.` prefix. `"twin"` selects C or Python. -/

namespace PyLean.CoreLibs.Operator

open Lean PyLean PyLean.Diff

def getArr (j : Json) (key : String) : Except String (List Json) := do
  pure (← (← field j key).getArr?).toList

def getIntList (j : Json) (key : String) : Except String (List Int) := do
  (← getArr j key).mapM (·.getInt?)

def getNatList (j : Json) (key : String) : Except String (List Nat) := do
  (← getArr j key).mapM (·.getNat?)

def okJ (j : Json) : Json := Json.mkObj [("ok", j)]

def valueErr (m : String) : PyExc := .valueError m

/-- A scripted dunder: absent, returning a tag, returning `NotImplemented`, raising, or set to `None`. -/
def dunderOf (s : String) (tag : Int) : Int → Int → Py (Ret Int) := fun _ _ =>
  match s with
  | "val" => .ok (.val tag)
  | "raise" => .error (valueErr "slot")
  | "noneattr" => .error (.typeError "'NoneType' object is not callable")
  | _ => .ok .notImplemented

/-- Two instances of Python classes `A` and `B`, with `__op__` on `A` and `__rop__` on `B`: every class has the
one slot function, so `binary_op1` sees one slot, or one on one side. -/
def heapArgs (l r : String) (sub : Bool) : BinArgs Int :=
  let selfHeap := l != "none"
  let otherHeap := r != "none" || (sub && selfHeap)
  let P : HeapPair Int :=
    ⟨selfHeap, otherHeap, false, sub, .ok (r != "none"), dunderOf l 1, dunderOf r 2⟩
  let slot : Slot Int := ⟨1, slotBinary P⟩
  ⟨if selfHeap then some slot else none, if otherHeap then some slot else none, false, sub, "A", "B"⟩

def noSeq : SeqArgs Int :=
  ⟨none, none, none, none, none, true, true, fun _ => none, fun _ => "B"⟩

def islotOf (s : String) : Option (Int → Int → Py (Ret Int)) :=
  if s == "none" then none else some (dunderOf s 3)

/-- A value of the real-object `+` and `*` cases. -/
inductive V where
  | int (n : Int)
  | seq (k : String) (n : Nat)
  | obj (k : String)
  deriving Repr, DecidableEq, BEq

def vJ : V → Json
  | .int n => toJson [toJson "int", toJson n]
  | .seq k n => toJson [toJson k, toJson n]
  | .obj k => toJson [toJson k, toJson (0 : Nat)]

def vOf (k : String) (n : Int) : V :=
  match k with
  | "list" | "tuple" => .seq k n.toNat
  | "int" | "i" => .int n
  | k => .obj k

def vTn : V → String
  | .int _ => "int"
  | .seq k _ => k
  | .obj k => k

def tnOf (k : String) : String :=
  match k with
  | "i" => "I"
  | "idx" => "Idx"
  | "plain" => "Plain"
  | k => k

def vKind (x : V) (k : String) : String := if k == "" then vTn x else k

def seqRepeat (x : V) (n : Int) : Py V :=
  match x with
  | .seq k m => .ok (.seq k (m * n.toNat))
  | v => .ok v

def seqConcat (kv kw : String) : V → V → Py V
  | .seq k m, .seq k2 n =>
    if k == k2 then .ok (.seq k (m + n))
    else .error (.typeError s!"can only concatenate {k} (not \"{tnOf k2}\") to {k}")
  | .seq k _, _ =>
    .error (.typeError s!"can only concatenate {k} (not \"{tnOf kw}\") to {k}")
  | _, _ => .error (.typeError (toString (kv.length)))

/-- `+=` on a list extends from an iterable. -/
def listExtend (kw : String) : V → V → Py V
  | .seq k m, .seq _ n => .ok (.seq k (m + n))
  | _, _ => .error (.typeError s!"'{tnOf kw}' object is not iterable")

def realArgs (kv kw : String) (add : Bool) : BinArgs V × SeqArgs V :=
  let intLike (k : String) := k == "int" || k == "i"
  let nb : Slot V := ⟨2, fun x y =>
    match x, y with
    | .int a, .int b => .ok (.val (.int (if add then a + b else a * b)))
    | _, _ => .ok .notImplemented⟩
  let A : BinArgs V :=
    ⟨if intLike kv then some nb else none, if intLike kw then some nb else none,
      kv == kw, kw == "i" && kv == "int", tnOf kv, tnOf kw⟩
  let isSeq (k : String) := k == "list" || k == "tuple"
  let Q : SeqArgs V :=
    { concat := if isSeq kv then some (seqConcat kv kw) else none
      iconcat := if kv == "list" then some (listExtend kw) else none
      repeatV := if isSeq kv then some seqRepeat else none
      irepeatV := if kv == "list" then some seqRepeat else none
      repeatW := if isSeq kw then some seqRepeat else none
      hasV := kv != "int"
      hasW := kw != "int"
      index := fun x => match x with
        | .int n => some (.ok n)
        | .obj "idx" => some (.ok 2)
        | _ => none
      tn := fun x => match x with
        | .int _ => "int"
        | .seq k _ => k
        | .obj k => tnOf k }
  (A, Q)

/-- The comparison method of a class in the cases: scripted, or `object`'s. -/
def cmpSlot (s : String) (tag : Int) (identical : Bool) : RichOp → Int → Int → Py (Ret Int) :=
  match s with
  | "val" => fun _ _ _ => .ok (.val tag)
  | "raise" => fun _ _ _ => .error (valueErr "slot")
  | "ni" => fun _ _ _ => .ok .notImplemented
  | _ => fun op _ _ =>
    objectRichcompare identical (fun b => if b then 101 else 100)
      (if identical then .ok (.val 101) else .ok .notImplemented) (fun v => .ok (v == 101)) op

def parseOp (s : String) : RichOp :=
  match s with
  | "lt" => .lt
  | "le" => .le
  | "eq" => .eq
  | "ne" => .ne
  | "gt" => .gt
  | _ => .ge

def parseTruth (j : Json) : Except String TruthObj := do
  match ← getStr j "k" with
  | "true" => pure .tru
  | "false" => pure .fals
  | "none" => pure .none
  | "booltrue" => pure (.bool (.ok true))
  | "boolfalse" => pure (.bool (.ok false))
  | "boolraise" => pure (.bool (.error (valueErr "bool")))
  | "badbool" => pure (.badBool "T" "int")
  | "nonebool" => pure (.noneBool "T")
  | "len" => pure (.len (.ok (← getInt j "n")))
  | "lenraise" => pure (.len (.error (valueErr "len")))
  | _ => pure .plain

def parseIndexRet (s : String) (n : Int) : Py IndexRet :=
  match s with
  | "exact" => .ok (.exact n)
  | "sub" => .ok (.sub n)
  | "other" => .ok (.other "str")
  | _ => .error (valueErr "index")

def indexRetJ : IndexRet → Json
  | .exact n => toJson [toJson "int", toJson n]
  | .sub n => toJson [toJson "sub", toJson n]
  | .other tn => toJson [toJson "other", toJson tn]

/-- The keys of the subscript cases. -/
def keyOf (k : String) (n : Int) : Option (Py Int) × String :=
  match k with
  | "int" => (some (.ok n), "int")
  | "idx" => (some (.ok 3), "Idx")
  | "bad" => (some (.error (valueErr "index")), "Bad")
  | _ => (none, "str")

def dequeLen : Int := 3

def getArgsOf (o k : String) (n : Int) : GetArgs Int :=
  let (keyIndex, keyTn) := keyOf k n
  let item : Int → Py Int := fun i =>
    if i < 0 ∨ i ≥ dequeLen then .error (.indexError "deque index out of range") else .ok i
  { mp := if o == "user" then some (.ok 7) else if o == "userraise" then some (.error (valueErr "get")) else none
    sqItem := if o == "deque" then some item else none
    sqLen := if o == "deque" then some (.ok dequeLen) else none
    asType := match o with
      | "cls" => some (.ok none)
      | "cg" => some (.ok (some 9))
      | "cgraise" => some (.error (valueErr "cg"))
      | _ => none
    keyIndex, tn := if o == "cls" then "C" else if o == "int" then "int" else "deque", keyTn }

def setArgsOf (o k : String) (n : Int) (del : Bool) : SetArgs Int :=
  let (keyIndex, keyTn) := keyOf k n
  let item : Int → Py Int := fun i =>
    if i < 0 ∨ i ≥ dequeLen then
      .error (.indexError "deque index out of range")
    else .ok 0
  { mp := if o == "user" then some (.ok 0) else if o == "userraise" then some (.error (valueErr "set")) else none
    hasSeq := o == "deque" || o == "tuple"
    sqAss := if o == "deque" then some item else none
    sqLen := if o == "deque" then some (.ok dequeLen) else none
    keyIndex, tn := o, keyTn }

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
    | .str "raise" => pure (.error (valueErr "len"))
    | v => do pure (.ok (← v.getNat?))
  let hint : Option (Py HintRet) ← match (← field j "hint") with
    | .null => pure none
    | .str "ni" => pure (some (.ok .notImplemented))
    | .str "typeerror" => pure (some (.error (.typeError "hint")))
    | .str "raise" => pure (some (.error (valueErr "hint")))
    | .str "str" => pure (some (.ok (.other "str")))
    | v => do pure (some (.ok (.int (← v.getInt?))))
  pure ⟨len, hint, "O"⟩

def getDefault (j : Json) : Except String HintDefault := do
  match ← getStr j "dkind" with
  | "int" => pure (.int (← getInt j "d"))
  | "index" => pure (.indexable (← getInt j "d"))
  | _ => pure (.other "str")

def getDigest (j : Json) : Except String DigestArg := do
  match ← getStr j "k" with
  | "str" => pure (.str (← getBool j "ascii") ((← getIntList j "data").map Int.toNat))
  | "bytes" => pure (.buffer ((← getIntList j "data").map Int.toNat))
  | _ => pure (.other "int")

/-- Attribute reads on the `N` objects of the cases: `x` and the empty name fail. -/
def attrWorld : GetAttr String := fun o n =>
  if n == [] || n == ['x'] then .error (.named "AttributeError" "~no attribute")
  else .ok (o ++ "." ++ String.ofList n)

def outJ (e : String → Json) : Out String → Json
  | .one v => toJson [toJson "one", e v]
  | .many vs => toJson [toJson "many", toJson (vs.map e)]

def parseAttr (j : Json) : AttrArg :=
  match j with
  | .str s => .str s.toList
  | .arr a =>
    match a.toList with
    | [.str s, .str sp] => .strSub s.toList [sp.toList]
    | _ => .other
  | _ => .other

def mcOf (j : Json) : Except String (Mc Int) := do
  let args ← getIntList j "args"
  let kw ← (← getArr j "kw").mapM fun p => do
    pure (← (← p.getArrVal? 0).getStr?, ← (← p.getArrVal? 1).getInt?)
  pure ⟨['m'], args, kw⟩

def intRep : Int → Py String := fun v =>
  if v == -9 then .error (valueErr "repr") else .ok (toString v)

def getRv (j : Json) : Except String RvSpec := do
  match ← getStr j "rv" with
  | "str" => pure .str
  | "raise" => pure (.raises (valueErr "reduce"))
  | _ =>
    let fail : Option PyExc := if ← getBool j "ctorfail" then some (valueErr "ctor") else none
    let kind ← match ← getStr j "kind" with
      | "list" => pure BuildKind.list
      | "dict" => pure .dict
      | _ => pure .inst
    let state ← match (← field j "state") with
      | .null => pure none
      | v => some <$> v.getNat?
    let tag ← getStr j "tag"
    let failOf (k : String) : Except String (Option PyExc) := do
      match j.getObjVal? k with
      | .ok (.bool true) => pure (some (valueErr ((if k == "listfail" then "listiter" else "dictiter") ++ tag)))
      | _ => pure none
    let li ← match (← field j "listiter") with
      | .null => pure none
      | v => pure (some ⟨← (← v.getArr?).toList.mapM (·.getNat?), ← failOf "listfail"⟩)
    let di ← match (← field j "dictiter") with
      | .null => pure none
      | v => do
        let ps ← (← v.getArr?).toList.mapM fun p => do
          pure (← (← p.getArrVal? 0).getNat?, ← (← p.getArrVal? 1).getNat?)
        pure (some ⟨ps, ← failOf "dictfail"⟩)
    let ss : Option (Option PyExc) ← match ← getStr j "setstate" with
      | "ok" => pure (some none)
      | "raise" => pure (some (some (valueErr "setstate")))
      | _ => pure none
    pure (.tuple (← getNat j "size") fail kind (← getNatList j "args") state li di ss)

def getCells (j : Json) : Except String (List Cell) := do
  (← getArr j "cells").mapM fun c => do
    match ← getStr c "k" with
    | "atom" => pure (.atom (← getInt c "n"))
    | "str" => pure (.str (← getStr c "s"))
    | "list" => pure (.list ((← getIntList c "items").map Int.toNat))
    | "tuple" => pure (.tuple ((← getIntList c "items").map Int.toNat))
    | "dict" =>
      let ks ← getIntList c "items"
      pure (.dict ((ks.toArray.toList.zipIdx.filterMap fun p =>
        if p.2 % 2 == 0 then some (p.1.toNat, (ks.getD (p.2 + 1) 0).toNat) else none)))
    | "inst" =>
      let ps ← (← getArr c "attrs").mapM fun p => do
        pure (← (← p.getArrVal? 0).getStr?, ← (← p.getArrVal? 1).getNat?)
      pure (.inst (ps.map fun p => (.name p.1, p.2)))
    | "method" =>
      let fn : Nat := match c.getObjVal? "fn" with
        | .ok v => (v.getNat?).toOption.getD 0
        | .error _ => 0
      pure (.method fn (← getNat c "self"))
    | "cls" => pure (.cls 0)
    | "meta" => pure (.metaCls 0)
    | "fdict" =>
      let ks ← getIntList c "items"
      pure (.fdict ((ks.toArray.toList.zipIdx.filterMap fun p =>
        if p.2 % 2 == 0 then some (p.1.toNat, (ks.getD (p.2 + 1) 0).toNat) else none)))
    | _ =>
      let tag ← getStr c "tag"
      let mk (k : String) : Except String (Option (Option PyExc)) := do
        match ← getStr c k with
        | "ok" => pure (some none)
        | "raise" => pure (some (some (valueErr (k ++ tag))))
        | _ => pure none
      let rv ← match ← getStr c "rv" with
        | "absent" => pure none
        | _ => some <$> getRv c
      let via : String := match c.getObjVal? "via" with
        | .ok (.str v) => v
        | _ => "ex"
      let table : Bool := match c.getObjVal? "table" with
        | .ok (.bool true) => true
        | _ => false
      -- the Python side's class: `__reduce_ex__`, `__reduce__` and a `copyreg.dispatch_table` entry
      let reduce : Reductor := match rv with
        | none => ⟨none, if via == "falsyex" then .falsy else .none, if via == "falsy" then .falsy else .none⟩
        | some r =>
          if table then ⟨some r, .fn (.raises (valueErr "shadowed")), .none⟩
          else if via == "plain" then ⟨none, .none, .fn r⟩
          else ⟨none, .fn r, .none⟩
      pure (.hooked (← mk "copier") (← mk "deepcopier") reduce)

/-- The result graph, by depth-first search with back references, as the Python side renders it. -/
partial def render (h : Heap) (seen : List Nat) (x : Nat) : List Nat × Json :=
  match h.get x with
  | .atom n => (seen, toJson [toJson "atom", toJson n])
  | .str t => (seen, toJson [toJson "str", toJson t])
  | .cls _ => (seen, toJson [toJson "cls"])
  | .metaCls _ => (seen, toJson [toJson "meta"])
  | .hooked _ _ _ => (seen, toJson [toJson "hooked"])
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
      | .fdict items =>
        let (s, js) := many (items.flatMap fun p => [p.1, p.2])
        (s, toJson [toJson "fdict", toJson js])
      | .inst attrs =>
        -- the `__dict__` in insertion order, each key before its value, as the Python side walks it
        let (s, js) := attrs.foldl (fun (acc : List Nat × List Json) p =>
          let (s1, kj) := match p.1 with
            | .name n => (acc.1, toJson n)
            | .obj k => render h acc.1 k
          let (s2, vj) := render h s1 p.2
          (s2, acc.2 ++ [toJson [kj, vj]])) (seen, [])
        (s, toJson [toJson "inst", toJson js])
      | .method f self =>
        let (s, js) := many [self]
        (s, toJson [toJson "method", toJson (methName f), toJson js])
      | _ => (seen, toJson [toJson "other"])

/-- The `_keep_alive` list after `render` of the copy, with its `seen` list: an object as `render` gives it, an
instance's `__dict__` as the dict it is (a new entry of `seen`, at a number no cell has). -/
partial def renderKeep (h : Heap) (seen : List Nat) : List KeepItem → List Json
  | [] => []
  | .obj i :: rest =>
    let (s, j) := render h seen i
    j :: renderKeep h s rest
  | .dictOf i :: rest =>
    let attrs := match h.get i with
      | .inst a => a
      | _ => []
    let s0 := seen ++ [1000000 + i]
    let (s, js) := attrs.foldl (fun (acc : List Nat × List Json) p =>
      let (s1, kj) := match p.1 with
        | .name n => (acc.1, toJson [toJson "str", toJson n])
        | .obj k => render h acc.1 k
      let (s2, vj) := render h s1 p.2
      (s2, acc.2 ++ [kj, vj])) (s0, [])
    toJson [toJson "dict", toJson js] :: renderKeep h s rest

def getHooks (j : Json) : Except String (List (Nat × Nat × String)) := do
  (← getArr j "hooks").mapM fun p => do
    pure (← (← p.getArrVal? 0).getNat?, ← (← p.getArrVal? 1).getNat?, ← (← p.getArrVal? 2).getStr?)

def run (fn : String) (j : Json) : Except String Json := do
  let c := (j.getObjVal? "twin").toOption.bind (·.getStr?.toOption) == some "c"
  match fn with
  | "binop" =>
    let A := heapArgs (← getStr j "l") (← getStr j "r") (← getBool j "sub")
    let sym ← getStr j "sym"
    match sym with
    | "**" => pure (encPy toJson (numberPow A 0 0))
    | "+" => pure (encPy toJson (numberAdd A noSeq 0 0))
    | "*" => pure (encPy toJson (numberMul A noSeq 0 0))
    | s => pure (encPy toJson (binaryOp A s 0 0))
  | "iop" =>
    let A := heapArgs (← getStr j "l") (← getStr j "r") (← getBool j "sub")
    let f := islotOf (← getStr j "i")
    let sym ← getStr j "sym"
    match sym with
    | "**" => pure (encPy toJson (inplacePow f A 0 0))
    | "+" => pure (encPy toJson (inplaceAdd f A {noSeq with hasV := true} 0 0))
    | "*" => pure (encPy toJson (inplaceMul f A noSeq 0 0))
    | s => pure (encPy toJson (inplaceOp f A (s ++ "=") 0 0))
  | "seqop" =>
    let kv ← getStr j "kv"
    let kw ← getStr j "kw"
    let name ← getStr j "name"
    let (A, Q) := realArgs kv kw (name == "add" || name == "iadd")
    let v := vOf kv (← getInt j "a")
    let w := vOf kw (← getInt j "b")
    let r := match name with
      | "add" => numberAdd A Q v w
      | "mul" => numberMul A Q v w
      | "iadd" => inplaceAdd none A Q v w
      | _ => inplaceMul none A Q v w
    pure (encPy vJ r)
  | "cmp" =>
    let identical ← getBool j "same"
    let l ← getStr j "l"
    let op := parseOp (← getStr j "op")
    -- one object: its own class on both sides, so the reflected method is the same one or absent
    let r ← if identical then pure (if op == .eq || op == .ne then l else "none") else getStr j "r"
    let tagR : Int := if identical then 1 else 2
    let A : CmpArgs Int := ⟨some (cmpSlot l 1 identical), some (cmpSlot r tagR identical), identical,
      ← getBool j "sub", identical, fun b => if b then 101 else 100, "A", if identical then "A" else "B"⟩
    pure (encPy toJson (richCompare A op 0 0))
  | "truth" =>
    let o ← parseTruth j
    pure (encPy toJson (if (← getStr j "name") == "truth" then truthOp o else notOp o))
  | "unary" =>
    let op : UnOp := match ← getStr j "name" with
      | "neg" => .neg
      | "pos" => .pos
      | "abs" => .abs
      | _ => .inv
    let k ← getStr j "has"
    let slot : Option (Int → Py Int) := match k with
      | "val" => some fun _ => .ok 4
      | "raise" => some fun _ => .error (valueErr "slot")
      | _ => none
    pure (encPy toJson (unaryOp slot op "A" 0))
  | "index" =>
    let n ← getInt j "n"
    let o : IndexObj :=
      { isInt := if (← getBool j "isint") then some n else none
        slot := match ← getStr j "slot" with
          | "none" => none
          | s => some (parseIndexRet s n)
        inst := match ← getStr j "inst" with
          | "none" => none
          | s => some (parseIndexRet s (n + 1))
        tn := "O"
        warn := none }
    pure (encPy indexRetJ ((if c then indexC else indexPy) o))
  | "getitem" =>
    pure (encPy toJson (getItem (getArgsOf (← getStr j "o") (← getStr j "k") (← getInt j "n"))))
  | "setitem" =>
    let A := setArgsOf (← getStr j "o") (← getStr j "k") (← getInt j "n") false
    pure (encPy (fun _ => Json.null) (setItem A))
  | "delitem" =>
    let A := setArgsOf (← getStr j "o") (← getStr j "k") (← getInt j "n") true
    pure (encPy (fun _ => Json.null) (delItem A))
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
  | "search" =>
    let bad ← getOptInt j "bad"
    let same : Same Int := fun x y => if some x = bad then .error (valueErr "eq") else .ok (x == y)
    let err : Option PyExc := if ← getBool j "itfail" then some (valueErr "it") else none
    let xs ← getIntList j "xs"
    let b ← getInt j "b"
    let notIter ← getStr j "notiter"
    let a : IterArg Int := match notIter with
      | "type" => .fail (.typeError "'int' object is not iterable")
      | "value" => .fail (valueErr "iter")
      | _ => .items xs err
    match ← getStr j "name" with
    | "countOf" => pure (encPy toJson ((if c then countOfC same "int" b a else countOfPy same b a)))
    | "indexOf" => pure (encPy toJson ((if c then indexOfC same "int" b a else indexOfPy same b a)))
    | _ =>
      let slot : Option (Py Bool) := match ← getStr j "slot" with
        | "true" => some (.ok true)
        | "raise" => some (.error (valueErr "contains"))
        | _ => none
      pure (encPy toJson (containsOp slot same "int" b a))
  | "length_hint" =>
    pure (encPy toJson ((if c then lengthHintC else lengthHintPy) (← getHintObj j) (← getDefault j)))
  | "itemgetter" =>
    let xs ← getIntList j "xs"
    let items ← (← getIntList j "items").mapM fun i => pure (⟨i, some i⟩ : ItemKey Int)
    let kind ← getStr j "obj"
    let get : Int → Py Int := fun i =>
      let n : Int := xs.length
      let k := if i < 0 then i + n else i
      if i > ssizeMax ∨ i < ssizeMin then .error (.indexError "cannot fit 'int' into an index-sized integer")
      else if k < 0 ∨ k ≥ n then
        .error (.indexError (if kind == "list" then "list index out of range" else "tuple index out of range"))
      else .ok (xs.getD k.toNat 0)
    let o : ItemObj Int Int := ⟨if kind == "tuple" then some xs else none, get⟩
    let e : Out Int → Json := fun r => match r with
      | .one v => toJson [toJson "one", toJson v]
      | .many vs => toJson [toJson "many", toJson vs]
    pure (encPy e ((if c then itemCallC else itemCallPy) items o))
  | "getter_repr" =>
    let items ← getIntList j "items"
    let cls := "operator.itemgetter"
    if c then pure (encPy toJson (reprC intRep false cls items))
    else pure (encPy toJson (reprPy intRep cls items))
  | "arity" =>
    let nargs ← getNat j "nargs"
    let nkw ← getNat j "nkw"
    let name ← getStr j "cls"
    let call ← getBool j "call"
    let vec := name == "methodcaller"
    let r : Option PyExc :=
      if c then
        if call then (if vec then oneArgVectorC name nargs nkw else oneArgC name nargs nkw)
        else if name == "methodcaller" then none else newArgC name nargs nkw
      else
        if call then oneArgPy nargs nkw
        else if name == "methodcaller" then newArgPy nargs 0
        else newArgPy nargs nkw
    pure (match r with
      | some e => encPy toJson (.error e : Py Int)
      | none => okJ Json.null)
  | "attrgetter" =>
    let args := (← getArr j "attrs").map parseAttr
    let e := outJ toJson
    if c then pure (encPy (fun n => toJson [e ((attrCall attrWorld n "o").toOption.getD (.one "fail")),
        toJson ((attrArgsC n).map String.ofList)]) (attrgetterNewC args))
    else pure (encPy (fun g => toJson [e ((attrCall attrWorld g.names "o").toOption.getD (.one "fail")),
        toJson ((attrArgsPy g).map String.ofList)]) (attrgetterNewPy args))
  | "attr_call" =>
    let args := (← getArr j "attrs").map parseAttr
    let e := outJ toJson
    match (if c then attrgetterNewC args else (attrgetterNewPy args).map (·.names)) with
    | .error x => pure (encPy toJson (.error x : Py Int))
    | .ok n => pure (encPy e (attrCall attrWorld n "o"))
  | "mc_new" =>
    let name : Option AttrArg ← match (← field j "name") with
      | .null => pure none
      | .str "BAD" => pure (some .other)
      | .str s => pure (some (.str s.toList))
      | _ => throw "name"
    pure (encPy (fun (m : Mc Int) => toJson (String.ofList m.name))
      ((if c then mcNewC else mcNewPy) name [] []))
  | "mc_call" =>
    let mc ← mcOf j
    let bad ← getStr j "bad"
    let m : Meth Int Json := fun _ _ =>
      match bad with
      | "getattr" => .error (valueErr "getattr")
      | "call" => .ok fun _ _ => .error (valueErr "call")
      | _ => .ok fun a k =>
        .ok (toJson [toJson a, toJson (k.map fun p => toJson [toJson p.1, toJson p.2])])
    pure (encPy id ((if c then mcCallC else mcCall) m mc 0))
  | "mc_repr" =>
    let mc ← mcOf j
    let cls := "operator.methodcaller"
    if c then pure (encPy toJson (mcReprC intRep false cls "'m'" mc))
    else pure (encPy toJson (mcReprPy intRep cls "'m'" mc))
  | "mc_reduce" =>
    let mc ← mcOf j
    match mcReduce mc with
    | .plain _ a => pure (okJ (toJson [toJson "plain", toJson a]))
    | .viaPartial _ k a =>
      pure (okJ (toJson [toJson "partial", toJson (k.map fun p => toJson [toJson p.1, toJson p.2]), toJson a]))
  | "digest" =>
    pure (encPy toJson (compareDigest (← getDigest (← field j "a")) (← getDigest (← field j "b"))))
  | "deepcopy" =>
    let cells ← getCells j
    let memo ← (← getArr j "memo").mapM fun p => do
      pure (← (← p.getArrVal? 0).getNat?, ← (← p.getArrVal? 1).getNat?)
    -- a later entry of the Python `memo` overwrites an earlier one, and `lookup` reads the front of the list
    let h : Heap := ⟨cells, memo.reverse, none⟩
    let x ← getNat j "root"
    let fuel := 12 * cells.length + 16
    -- the copy, whether it is `x`, and `memo[id(memo)]`, the `_keep_alive` list, rendered after the copy
    let out (p : Heap × Nat) : Json :=
      let (seen, yj) := render p.1 [] p.2
      let keepJ : Json := match p.1.keep with
        | none => Json.null
        | some ks => toJson (renderKeep p.1 seen ks)
      toJson [yj, toJson (p.2 == x), keepJ]
    if ← getBool j "shallow" then
      pure (encPy out (copyShallow h x))
    else
      pure (encPy out (deepcopy fuel h x))
  | "replace" =>
    let k ← getStr j "has"
    let changes ← (← getArr j "changes").mapM fun p => do
      pure (← (← p.getArrVal? 0).getStr?, ← (← p.getArrVal? 1).getInt?)
    -- `__replace__(s, **k)` answers from both of its arguments, so the call is observed, not assumed
    let f : Int → List (String × Int) → Py Int := fun o ch =>
      if k == "raise" then .error (valueErr "replace")
      else .ok (o * 1000 + 10 * ch.length + (ch.map (·.2)).sum)
    let attr : Option (Option (Int → List (String × Int) → Py Int)) := match k with
      | "none" => none
      | "null" => some none
      | _ => some (some f)
    let obj ← getInt j "obj"
    pure (encPy toJson (replaceOp (fun _ => ⟨"X", attr⟩) obj changes))
  | "call_op" =>
    let args ← getIntList j "args"
    let bad ← getBool j "bad"
    let f : Int → List Int → List (String × Int) → Py Int := fun _ rest kw =>
      if bad then .error (valueErr "call") else .ok ((rest.length + kw.length : Nat) : Int)
    let kw : List (String × Int) := if ← getBool j "kw" then [("k", 1)] else []
    pure (encPy toJson ((if c then callC else callPy) f args kw))
  | "abstract" =>
    let parents ← (← getArr j "parents").mapM fun p => do (← p.getArr?).toList.mapM (·.getStr?)
    let table ← (← getArr j "table").mapM fun p => do
      pure (← (← p.getArrVal? 0).getStr?, ← (← p.getArrVal? 1).getStr?)
    let test (s : String) : IsAbs := match s with
      | "abs" => .ok true
      | "raise" => .error (valueErr "abs")
      | _ => .ok false
    let own ← (← getArr j "own").mapM fun p => do
      pure (← (← p.getArrVal? 0).getStr?, test (← (← p.getArrVal? 1).getStr?))
    let lookup (n : String) : Option IsAbs := (own.lookup n) <|> ((table.lookup n).map test)
    let C : AbsClass := ⟨own, parents, lookup⟩
    let sortJ : List String → Json := fun l => toJson (l.mergeSort (· ≤ ·)).eraseDups
    if ← getBool j "update" then
      pure (encPy (fun o => (o.map sortJ).getD Json.null) (updateAbstract true C))
    else pure (encPy sortJ (computeAbstract C))
  | "abc" =>
    let hooks ← getHooks j
    let tbl (key : String) : Except String (List (List Nat)) := do
      (← getArr j key).mapM fun r => do (← r.getArr?).toList.mapM (·.getNat?)
    let mro ← tbl "mro"
    let subs ← tbl "subs"
    let n ← getNat j "n"
    let hook : Nat → Nat → Py HookRet := fun a b =>
      match (hooks.find? (fun h => h.1 == a && h.2.1 == b)).map (·.2.2) with
      | some "true" => .ok .tru
      | some "false" => .ok .fals
      | some "other" => .ok .other
      | some "raise" => .error (valueErr "hook")
      | _ => .ok .notImplemented
    let W : AbcWorld := ⟨hook, fun c => mro.getD c [], fun c => subs.getD c [], fun c => decide (c < n)⟩
    let mut st : AbcState := {}
    let mut out : List Json := []
    for op in (← getArr j "ops") do
      let a ← getNat op "cls"
      let b ← getNat op "sub"
      match ← getStr op "op" with
      | "reg" =>
        let (r, s) := register W 30 a (some b) st
        st := s
        out := out ++ [encPy toJson r]
      | "isinst" =>
        let (r, s) := instanceCheck W 30 a (.ok b) b st
        st := s
        out := out ++ [encPy toJson r]
      | "isinst_noclass" =>
        let err : PyExc := if ← getBool op "attr" then .named "AttributeError" "no" else valueErr "no"
        let (r, s) := instanceCheck W 30 a (.error err) b st
        st := s
        out := out ++ [encPy toJson r]
      | _ =>
        let (r, s) := subclassCheck W 30 a (some b) st
        st := s
        out := out ++ [encPy toJson r]
    pure (okJ (toJson out))
  | _ => throw s!"unknown fn operator.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Operator
