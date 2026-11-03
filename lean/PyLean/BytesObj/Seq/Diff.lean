import PyLean.DiffCore
import PyLean.ListSort.Model
import PyLean.BytesObj.Seq.Repr
import PyLean.BytesObj.Seq.SortAux
import PyLean.BytesObj.Seq.Release

/-! Differential-testing handler for tuple and list: `fn` names start with `tuple.` or `list.`.

The element type `DEl` stands for the objects built by `difftest/bytesobj_diff.py`:
ints, tuples of those, and instances of its class `El`, whose `kind` picks the
comparison behaviour:

* `nan`: every comparison is false (`!=` true), hash `1000 + id`, repr `<nan7>`.
* `bad`: comparisons, `__hash__` and `__repr__` raise `ValueError`.
* `weird`: comparisons return an object whose `__bool__` raises `TypeError`.
* `pop`, `clear`, `add`: like `nan`, but a comparison or repr also changes the
  list under test (`pop()` if non-empty; `clear()`; `append(0)` up to 12 items).

A case's result is compared as JSON. See the docstrings of the Python twins for
the shapes. -/

namespace PyLean.BytesObj.Seq

open Lean PyLean PyLean.Diff
open PyLean.RangeSlice (Slice)

inductive DEl where
  | int (n : Int)
  | obj (kind : String) (id : Nat)
  | tup (xs : List DEl)
  deriving Repr, Inhabited, BEq

/-- `PyObject_RichCompare` results: a bool, or an object whose truth value raises. -/
inductive Res where
  | bool (b : Bool)
  | weird
  deriving Repr, BEq

partial def jEl (j : Json) : Except String DEl :=
  match j with
  | .arr xs => do return .tup (← xs.toList.mapM jEl)
  | .obj _ => do return .obj (← getStr j "k") (← getNat j "id")
  | v => do return .int (← v.getInt?)

partial def enEl : DEl → Json
  | .int n => toJson n
  | .obj k i => Json.mkObj [("k", toJson k), ("id", toJson i)]
  | .tup xs => Json.arr (xs.map enEl).toArray

def jEls (j : Json) : Except String (List DEl) := do
  (← j.getArr?).toList.mapM jEl

def enEls (l : List DEl) : Json := Json.arr (l.map enEl).toArray

def kindOf : DEl → Option String
  | .obj k _ => some k
  | _ => none

/-- The object whose method runs first: the left operand unless it is an int, in
which case `int.__eq__` returns `NotImplemented` and the right operand's reflected
method runs. -/
def driver (a b : DEl) : Option String := (kindOf a) <|> (kindOf b)

def dSame : DEl → DEl → Bool
  | .obj k i, .obj k' i' => k == k' && i == i'
  | _, _ => false

def cmpTrue (op : CmpOp) (x y : Int) : Bool := cmpSizes op x y

def dRich (op : CmpOp) (a b : DEl) : Py Res :=
  match driver a b with
  | some "bad" => .error (.valueError "bad")
  | some "weird" => .ok .weird
  | some _ => .ok (.bool (op == .ne))
  | none =>
    match a, b with
    | .int x, .int y => .ok (.bool (cmpTrue op x y))
    -- Only `dict.items()` tuples of ints get here, and only under `==` and `!=`.
    | .tup _, .tup _ => .ok (.bool (if op == .ne then a != b else a == b))
    | _, _ => .ok (.bool (op == .ne))

def dTruth : Res → Py Bool
  | .bool b => .ok b
  | .weird => .error (.typeError "weird")

def E : ElemOps DEl Res where
  same := dSame
  rich := dRich
  truth := dTruth
  ofBool := .bool

def mayTrack : DEl → Bool
  | .int _ => false
  | _ => true

/-- The `__hash__` of an int: `Objects/longobject.c:long_hash`. -/
def intHash (x : Int) : Int :=
  let p : Nat := 2 ^ 61 - 1
  let r : Int := (x.natAbs % p : Nat)
  let r := if x < 0 then -r else r
  if r = -1 then -2 else r

def dHash : DEl → Py Int
  | .int x => .ok (intHash x)
  | .obj "bad" _ => .error (.valueError "badhash")
  | .obj _ i => .ok (1000 + i)
  | .tup _ => .ok 0

def dReprLeaf : DEl → Py String
  | .int x => .ok (toString x)
  | .obj "bad" _ => .error (.valueError "badrepr")
  | .obj k i => .ok s!"<{k}{i}>"
  | .tup _ => .ok "()"

def dRepr : DEl → Py String
  | .tup xs => tupleRepr dReprLeaf false xs
  | x => dReprLeaf x

abbrev St := LObj DEl

/-- What `El.__eq__` and `El.__repr__` do to the target list. -/
def applyEff (k : Option String) (o : St) : St :=
  match k with
  | some "pop" =>
    match o.items with
    | [] => o
    | _ =>
      match listPopK o (-1) with
      | .ok (_, o') => o'
      | .error _ => o
  | some "clear" => listClear o
  | some "add" =>
    if o.items.length < 12 then
      match listAppend o (.int 0) with
      | .ok o' => o'
      | .error _ => o
    else o
  | _ => o

/-- `PyObject_RichCompareBool(a, b, Py_EQ)` with the side effect of the method that runs. -/
def effCmp : Cmp DEl := fun o a b =>
  if dSame a b then (.ok true, o)
  else (richBool E .eq a b, applyEff (driver a b) o)

def effRepr (o : St) (x : DEl) : Py String × St := (dRepr x, applyEff (kindOf x) o)

/-- The `Cmp2` of the difftest: effects hit the left list. -/
def effCmp2 : Cmp2 DEl := fun st a b =>
  let (r, o') := effCmp (LObj.prealloc st.1) a b
  (r, (o'.items, st.2))

/-- The closing comparison runs the same method, with the same effect. -/
def effFinal : Final DEl Res := fun op st a b =>
  (dRich op a b, ((applyEff (driver a b) (LObj.prealloc st.1)).items, st.2))

def okJ (v : Json) : Json := Json.mkObj [("ok", v)]
def errJ (e : PyExc) : Json := Json.mkObj [("exc", toJson e.className), ("msg", toJson e.message)]
def unitJ : Json := Json.null

def jOptI : Json → Except String (Option Int)
  | .null => .ok none
  | v => some <$> v.getInt?

def jSlice (j : Json) : Except String Slice := do
  let arr ← j.getArr?
  let some a := arr[0]? | throw "slice"
  let some b := arr[1]? | throw "slice"
  let some c := arr[2]? | throw "slice"
  return ⟨← jOptI a, ← jOptI b, ← jOptI c⟩

def argAt (op : Array Json) (k : Nat) : Except String Json :=
  match op[k]? with
  | some v => .ok v
  | none => .error s!"missing argument {k}"

def optAt (op : Array Json) (k : Nat) : Except String (Option Int) :=
  match op[k]? with
  | some v => jOptI v
  | none => .ok none

def stateJ (o : St) : Json :=
  Json.arr #[enEls o.items, toJson (listSizeof o)]

def enRes : Res → Json
  | .bool b => toJson b
  | .weird => toJson "weird"

/-- `PyObject_LengthHint` of the iterable classes in the Python twin. -/
def jHint (j : Json) : Except String (Py Int) :=
  match j with
  | .null => .ok (.ok 8)
  | .str "raise" => .ok (.error (.valueError "hint"))
  | v => do
    let h ← v.getInt?
    if h > ssizeMax then
      return .error (.overflowError "Python int too large to convert to C ssize_t")
    if h < 0 then return .error (.valueError "Hinted.__length_hint__() must return a non-negative int")
    return .ok h

/-- An iterator over `items` that leaves the list alone. -/
def pureFx (items : List DEl) (hint : Py Int := .ok 8) (err : Option PyExc := none) : IterFx DEl :=
  IterSrc.fx { hint := hint, items := items, err := err }

/-- The twin's `mut_items(items)`: a generator that appends `0` to the list under test before it
yields each item. A generator has no length, so the hint is the default 8. -/
def mutFx (items : List DEl) : IterFx DEl where
  getIter o := (.ok (), o)
  hint o := (.ok 8, o)
  next k o :=
    match items[k]? with
    | some x => (some (.ok x), match listAppend o (.int 0) with | .ok o' => o' | .error _ => o)
    | none => (none, o)

/-- The twin's `clear_items(items)`: a generator that clears the list under test before its
second item. -/
def clearFx (items : List DEl) : IterFx DEl where
  getIter o := (.ok (), o)
  hint o := (.ok 8, o)
  next k o :=
    match items[k]? with
    | some x => (some (.ok x), if k = 1 then listClear o else o)
    | none => (none, o)

def unpair : DEl → DEl × DEl
  | .tup [a, b] => (a, b)
  | x => (x, x)

def jExt (j : Json) : Except String (ExtArg DEl) := do
  match ← getStr j "k" with
  | "self" => return classifyExt 0 .same
  | "fast" =>
    let items ← jEls (← field j "items")
    if (← getStr j "as") == "tuple" then return classifyExt 0 (.tuple true items (pureFx items))
    else return classifyExt 0 (.list true items (pureFx items))
  | "sized" =>
    let items ← jEls (← field j "items")
    let ones := items.map (fun _ => DEl.int 1)
    match ← getStr j "as" with
    | "set" => return classifyExt 0 (.set true items (pureFx items))
    | "frozenset" => return classifyExt 0 (.set true items (pureFx items))
    | "dict" => return classifyExt 0 (.dict true items ones (pureFx items))
    | "keys" => return classifyExt 0 (.keys items ones)
    | "values" => return classifyExt 0 (.values ((List.range items.length).map (fun (i : Nat) => DEl.int (i : Int))) items)
    | "items" =>
      let ps := items.map unpair
      return classifyExt 0 (.items (ps.map (·.1)) (ps.map (·.2)) (fun k v => .ok (.tup [k, v])))
    | a => throw s!"sized {a}"
  | "iter" =>
    let hint ← jHint (← field j "hint")
    let err := (j.getObjValAs? Bool "err").toOption.getD false
    let items ← jEls (← field j "items")
    return classifyExt (items.length + 1)
      (.other (pureFx items hint (if err then some (.valueError "gen") else none)))
  | "sub" =>
    let items ← jEls (← field j "items")
    return classifyExt (items.length + 1) (.list false items (pureFx items.reverse (.ok items.length)))
  | "mutiter" =>
    let items ← jEls (← field j "items")
    return classifyExt (items.length + 1) (.other (mutFx items))
  | "cleariter" =>
    let items ← jEls (← field j "items")
    return classifyExt (items.length + 1) (.other (clearFx items))
  | "noniter" => return classifyExt 0 (.notIterable "int")
  | k => throw s!"ext {k}"

def fuelOf (o : St) : Nat := o.items.length + 64

/-- The twin's `Ix(v, eff).__index__`: raise `ValueError("idx")` for `bad`, otherwise apply `eff` to
the list under test as `El` does, then return `v`. -/
def ixFn (v : Int) (eff : String) : St → Py Int × St := fun o =>
  if eff = "bad" then (.error (.valueError "idx"), o) else (.ok v, applyEff (some eff) o)

/-- An index argument as a subscript: `{"ix": "int"|"obj"|"str"|"float", "v": n, "eff": e}`. -/
def jSubItem (j : Json) : Except String (SubItem DEl) := do
  match ← getStr j "ix" with
  | "int" => return .int (← (← field j "v").getInt?)
  | "obj" => return .index "Ix" (ixFn (← (← field j "v").getInt?) (← getStr j "eff"))
  | k => return .other k

/-- An index argument of `l.index`. -/
def jIdxArg (j : Json) : Except String (IdxArg DEl) := do
  match ← getStr j "ix" with
  | "int" => return .int (← (← field j "v").getInt?)
  | "obj" => return .index "Ix" (ixFn (← (← field j "v").getInt?) (← getStr j "eff"))
  | k => return .notIndex k

def jOptIdxArg (j : Option Json) : Except String (Option (IdxArg DEl)) :=
  match j with
  | none | some Json.null => .ok none
  | some v => some <$> jIdxArg v

/-- `PySequence_List(it)` on one of the twin's generators: `next` until it ends, collecting the items,
with the generator's effects on the list under test. -/
def collectFx (src : IterFx DEl) : Nat → Nat → List DEl → St → Py (List DEl) × St
  | 0, _, _, o => (.error .modelFuel, o)
  | fuel + 1, k, acc, o =>
    match src.next k o with
    | (none, o') => (.ok acc, o')
    | (some (.error e), o') => (.error e, o')
    | (some (.ok x), o') => collectFx src fuel (k + 1) (acc ++ [x]) o'

/-- The generators the twin passes to `l[s] = it`: `{"k": "iter"|"mutiter"|"cleariter", ...}`. -/
def jGenView (j : Json) : Except String (SeqView DEl) := do
  let items ← jEls (← field j "items")
  let src ← match ← getStr j "k" with
    | "iter" =>
      let err := (j.getObjValAs? Bool "err").toOption.getD false
      pure (pureFx items (.ok 8) (if err then some (.valueError "gen") else none))
    | "mutiter" => pure (mutFx items)
    | "cleariter" => pure (clearFx items)
    | k => throw s!"gen view {k}"
  return .iter (fun o => collectFx src (items.length + 2) 0 [] o)

def lresJ : LRes DEl → Json × St
  | (o', none) => (okJ unitJ, o')
  | (o', some e) => (errJ e, o')

def resJ (o : St) : LRes DEl → Json × St
  | (o', none) => let _ := o; (okJ unitJ, o')
  | (o', some e) => (errJ e, o')

def stepList (o : St) (op : Array Json) : Except String (Json × St) := do
  let name ← (← argAt op 0).getStr?
  let keep (r : Py St) : Json × St :=
    match r with
    | .ok o' => (okJ unitJ, o')
    | .error e => (errJ e, o)
  match name with
  | "append" => return keep (listAppend o (← jEl (← argAt op 1)))
  | "insert" => return keep (listInsert o (← (← argAt op 1).getInt?) (← jEl (← argAt op 2)))
  | "pop" =>
    match listPop o (← optAt op 1) with
    | .ok (v, o') => return (okJ (enEl v), o')
    | .error e => return (errJ e, o)
  | "remove" =>
    let (r, o') := listRemove effCmp (fuelOf o) o (← jEl (← argAt op 1))
    match r with
    | .ok () => return (okJ unitJ, o')
    | .error e => return (errJ e, o')
  | "index" =>
    let (r, o') := listIndex effCmp (fuelOf o) o (← jEl (← argAt op 1)) (← optAt op 2) (← optAt op 3)
    return (encPy toJson r, o')
  | "count" =>
    let (r, o') := listCount dSame effCmp (fuelOf o) o (← jEl (← argAt op 1))
    return (encPy toJson r, o')
  | "contains" =>
    let (r, o') := listContains effCmp (fuelOf o) o (← jEl (← argAt op 1))
    return (encPy toJson r, o')
  | "repr" =>
    let (r, o') := listRepr effRepr (fuelOf o) false o
    return (encPy toJson r, o')
  | "clear" => return (okJ unitJ, listClear o)
  | "copy" => return (okJ (stateJ (listSliceLH o.items 0 o.items.length)), o)
  | "reverse" => return (okJ unitJ, listReverse o)
  | "getitem" => return (encPy enEl (listGetItem o.items (← (← argAt op 1).getInt?)), o)
  | "getitemx" =>
    let (r, o') := listSubscriptAny o (← jSubItem (← argAt op 1))
    match r with
    | .ok (.inl v) => return (okJ (enEl v), o')
    | .ok (.inr r) => return (okJ (stateJ r), o')
    | .error e => return (errJ e, o')
  | "setitemx" =>
    let v ← jEl (← argAt op 2)
    return lresJ (listAssSubscriptAny o (← jSubItem (← argAt op 1)) (some (v, .notIterable)))
  | "delitemx" => return lresJ (listAssSubscriptAny o (← jSubItem (← argAt op 1)) none)
  | "setslice_gen" =>
    return lresJ (listAssSubscriptAny o (.slice (← jSlice (← argAt op 1)))
      (some (.int 0, ← jGenView (← argAt op 2))))
  | "indexx" =>
    let (r, o') := listIndexCall effCmp (fuelOf o) o (← jEl (← argAt op 1))
      (← jOptIdxArg op[2]?) (← jOptIdxArg op[3]?)
    return (encPy toJson r, o')
  | "getslice" => return (encPy stateJ (listGetSlice o.items (← jSlice (← argAt op 1))), o)
  | "binslice" =>
    let arr ← (← argAt op 1).getArr?
    let some a := arr[0]? | throw "binslice"
    let some b := arr[1]? | throw "binslice"
    return (okJ (stateJ (listBinarySlice o.items ⟨← jOptI a, ← jOptI b, none⟩)), o)
  | "forloop" =>
    return (okJ (enEls o.items), o)
  | "setitem" => return keep (listSetItem o (← (← argAt op 1).getInt?) (some (← jEl (← argAt op 2))))
  | "delitem" => return keep (listSetItem o (← (← argAt op 1).getInt?) none)
  | "setslice" =>
    return keep (listAssSubscript o (← jSlice (← argAt op 1)) (.seq (← jEls (← argAt op 2))))
  | "setslice_self" => return keep (listAssSubscript o (← jSlice (← argAt op 1)) .selfCopy)
  | "setslice_bad" => return keep (listAssSubscript o (← jSlice (← argAt op 1)) .notIterable)
  | "delslice" => return keep (listAssSubscript o (← jSlice (← argAt op 1)) .del)
  | "imul" => return keep (listIMul o (← (← argAt op 1).getInt?))
  | "mul" => return (encPy stateJ (listMul o.items (← (← argAt op 1).getInt?)), o)
  | "add" => return (encPy stateJ (listConcatAny o.items (.inl (← jEls (← argAt op 1)))), o)
  | "add_bad" => return (encPy stateJ (listConcatAny o.items (.inr (← (← argAt op 1).getStr?))), o)
  | "extend" => return resJ o (listExtend o (← jExt (← argAt op 1)))
  | "iadd" => return resJ o (listIConcat o (← jExt (← argAt op 1)))
  | "init" =>
    match (op[1]? : Option Json) with
    | some Json.null => return resJ o (listInit o none)
    | some j => return resJ o (listInit o (some (← jExt j)))
    | none => return resJ o (listInit o none)
  | other => throw s!"unknown list op {other}"

def initList (j : Json) : Except String St := do
  let items ← jEls (← field j "items")
  match ← getStr j "how" with
  | "display" => return listFromStack items
  | "tuple" =>
    match listVectorcall [.fast items] 0 with
    | .ok o => return o
    | .error _ => throw "init"
  | "gen" =>
    match listVectorcall [.iter { items := items }] 0 with
    | .ok o => return o
    | .error _ => throw "init"
  | h => throw s!"init {h}"

/-- `{"init": ..., "ops": [...]}`: `[result, state]` after each operation. -/
def runOps (j : Json) : Except String Json := do
  let mut o ← initList (← field j "init")
  let mut out : Array Json := #[]
  for op in (← (← field j "ops").getArr?) do
    let (r, o') ← stepList o (← op.getArr?)
    out := out.push (Json.arr #[r, stateJ o'])
    o := o'
  return okJ (Json.arr out)

/-! ## Iterators -/

def itJ (it : ListIter) : Json := Json.arr #[toJson it.index, toJson it.alive]

/-- `for _ in it: pass`: `next` until it reports the end. -/
def exhaustIt (forward : Bool) (l : List DEl) : Nat → ListIter → ListIter
  | 0, it => it
  | n + 1, it =>
    match (if forward then listIterNext it l else listRevIterNext it l) with
    | .ok (some _, it') => exhaustIt forward l n it'
    | .ok (none, it') => it'
    | .error _ => it

/-- `it.__reduce__()` with the builtins lookup `g`: `[seq, index or null, callable's __name__]`. -/
def reduceJ (forward : Bool) (g : String → ListIter × List DEl → Py String × (ListIter × List DEl))
    (it : ListIter) (l : List DEl) : Json × ListIter × List DEl :=
  match listIterReduceGen g forward (it, l) with
  | (.ok (.live c seq i), (it', l')) => (okJ (Json.arr #[enEls seq, toJson i, toJson c]), it', l')
  | (.ok (.empty c), (it', l')) => (okJ (Json.arr #[enEls [], Json.null, toJson c]), it', l')
  | (.error e, (it', l')) => (errJ e, it', l')

/-- `[r, list]` after each of `next`, `hint`, `reduce`, `setstate`, `pop`, `add`, `clear`. -/
def stepIter (forward : Bool) (it : ListIter) (l : List DEl) (op : Array Json) :
    Except String (Json × ListIter × List DEl) := do
  match ← (← argAt op 0).getStr? with
  | "next" =>
    let r := if forward then listIterNext it l else listRevIterNext it l
    match r with
    | .ok (v, it') =>
      return (okJ (match v with | some x => enEl x | none => toJson "stop"), it', l)
    | .error e => return (errJ e, it, l)
  | "hint" => return (okJ (toJson (if forward then listIterLen it l else listRevIterLen it l)), it, l)
  | "reduce" => return reduceJ forward (fun name st => (.ok name, st)) it l
  | "reduce_exhaust" =>
    return reduceJ forward (fun name st => (.ok name, (exhaustIt forward st.2 (st.2.length + 2) st.1, st.2))) it l
  | "reduce_add" => return reduceJ forward (fun name st => (.ok name, (st.1, st.2 ++ [.int 0]))) it l
  | "reduce_missing" => return reduceJ forward (fun name st => (.error (.named "AttributeError" name), st)) it l
  | "setstate" =>
    let s : Option Int := ((← argAt op 1).getInt?).toOption
    let r := if forward then listIterSetstateObj it l s else listRevIterSetstateObj it l s
    match r with
    | .ok it' => return (okJ unitJ, it', l)
    | .error e => return (errJ e, it, l)
  | "refs" => return (okJ (toJson (listIterTraverse it l).length), it, l)
  | "pop" => return (okJ unitJ, it, l.dropLast)
  | "add" => return (okJ unitJ, it, l ++ [.int 0])
  | "clear" => return (okJ unitJ, it, [])
  | k => throw s!"iter op {k}"

def runIter (j : Json) : Except String Json := do
  let l0 ← jEls (← field j "items")
  let forward ← getBool j "forward"
  let mut l := l0
  let mut it : ListIter := if forward then listIter else listReversed l0
  let mut out : Array Json := #[]
  for op in (← (← field j "ops").getArr?) do
    let (r, it', l') ← stepIter forward it l (← op.getArr?)
    out := out.push (Json.arr #[r, enEls l'])
    it := it'
    l := l'
  return okJ (Json.arr out)

/-- Tuple iterators: `next`, `hint`, `reduce`, `setstate`. -/
def runTupleIter (j : Json) : Except String Json := do
  let t ← jEls (← field j "items")
  let mut it := tupleIter t
  let mut out : Array Json := #[]
  for op in (← (← field j "ops").getArr?) do
    let op ← op.getArr?
    match ← (← argAt op 0).getStr? with
    | "next" =>
      let (v, it') := tupleIterNext it
      it := it'
      out := out.push (okJ (match v with | some x => enEl x | none => toJson "stop"))
    | "hint" => out := out.push (okJ (toJson (tupleIterLen it)))
    | "refs" => out := out.push (okJ (toJson (tupleIterTraverse it).length))
    | "reduce" =>
      let (a, st) := tupleIterReduce it
      out := out.push (okJ (Json.arr #[enEls a, match st with | some i => toJson i | none => Json.null]))
    | "setstate" =>
      match tupleIterSetstate it (← (← argAt op 1).getInt?) with
      | .ok it' => it := it'; out := out.push (okJ unitJ)
      | .error e => out := out.push (errJ e)
    | k => throw s!"tuple iter op {k}"
  return okJ (Json.arr out)

/-! ## Tuples -/

/-- A tuple argument: `{"items": [...], "sub": bool}`. -/
def jTup (j : Json) : Except String (Tup DEl) := do
  let items ← jEls (← field j "items")
  let sub := (j.getObjValAs? Bool "sub").toOption.getD false
  return { items := items, exact := !sub,
           tracked := if sub then true else items.any mayTrack }

def tupOutJ (r : String) (items : List DEl) (tracked : Bool) : Json :=
  Json.mkObj [("r", toJson r), ("items", enEls items), ("tracked", toJson tracked)]

def enTRes (a b : Tup DEl) : TRes DEl → Json
  | .arg 0 =>
    if a.exact && a.items.isEmpty then tupOutJ "empty" [] false else tupOutJ "arg0" a.items a.tracked
  | .arg _ =>
    if b.exact && b.items.isEmpty then tupOutJ "empty" [] false else tupOutJ "arg1" b.items b.tracked
  | .empty => tupOutJ "empty" [] false
  | .fresh t => tupOutJ "fresh" t.items t.tracked

def noTup : Tup DEl := { items := [] }

def jSrc (j : Json) : Except String (TupleSrc DEl × Tup DEl) := do
  let items ← jEls (← field j "items")
  match ← getStr j "k" with
  | "tuple" => let t := { items := items, tracked := items.any mayTrack : Tup DEl }
               return (.exactTuple t, t)
  | "list" => return (.exactList items, noTup)
  | "iter" => return (.iterable items, noTup)
  | k => throw s!"src {k}"

def cmpOpOf : String → Except String CmpOp
  | "lt" => .ok .lt | "le" => .ok .le | "eq" => .ok .eq
  | "ne" => .ok .ne | "gt" => .ok .gt | "ge" => .ok .ge
  | s => .error s!"cmp op {s}"

def cntHash (call : Nat) : DEl → Py Int
  | .obj "cnt" i => .ok (100 * call + i)
  | .obj "flaky" _ => if call = 1 then .error (.valueError "flaky") else .ok 5
  | x => dHash x

def enOpt : Option DEl → Json
  | some x => enEl x
  | none => Json.null

def enOptNat : Option Nat → Json
  | some x => toJson x
  | none => Json.null

def runTuple (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "tuple.hash" =>
    let t ← jTup (← field j "t")
    return encPy (fun p => toJson p.1) (tupleHash dHash t)
  | "tuple.hash2" =>
    let t ← jTup (← field j "t")
    let r1 := tupleHash (cntHash 1) t
    let t' := match r1 with | .ok p => p.2 | .error _ => t
    let r2 := tupleHash (cntHash 2) t'
    return okJ (Json.arr #[encPy (fun p => toJson p.1) r1, encPy (fun p => toJson p.1) r2])
  | "tuple.hashdeep" =>
    let t ← jTup (← field j "t")
    return encPy (fun p => toJson p.1) (tupleHashGuarded dHash t true)
  | "tuple.repr" =>
    return encPy toJson (tupleRepr dRepr false (← jEls (← field j "items")))
  | "tuple.getitem" =>
    return encPy enEl (tupleGetItem (← jEls (← field j "items")) (← getInt j "i"))
  | "tuple.getslice" =>
    let t ← jTup (← field j "t")
    return encPy (enTRes t noTup) (tupleGetSlice t (← jSlice (← field j "s")))
  | "tuple.binslice" =>
    let t ← jTup (← field j "t")
    let s ← jSlice (← field j "s")
    if t.exact then
      return encPy (enTRes t noTup) (tupleBinarySlice mayTrack t ⟨s.start, s.stop, none⟩)
    else
      return encPy (enTRes t noTup) (tupleGetSlice t ⟨s.start, s.stop, none⟩)
  | "tuple.add" =>
    let a ← jTup (← field j "a")
    match j.getObjVal? "other" with
    | .ok (.str name) => return encPy (enTRes a noTup) (tupleConcat a (.other name))
    | _ =>
      let b ← jTup (← field j "b")
      return encPy (enTRes a b) (tupleConcat a (.tuple b))
  | "tuple.mul" =>
    let t ← jTup (← field j "t")
    return encPy (enTRes t noTup) (tupleMul t (← getInt j "n"))
  | "tuple.index" =>
    let v ← jEl (← field j "x")
    return encPy toJson (tupleIndex E (← jEls (← field j "items")) v
      (← jOptI (← field j "start")) (← jOptI (← field j "stop")))
  | "tuple.count" =>
    return encPy toJson (tupleCount E (← jEl (← field j "x")) (← jEls (← field j "items")) 0)
  | "tuple.contains" =>
    return encPy toJson (tupleContains E (← jEl (← field j "x")) (← jEls (← field j "items")))
  | "tuple.cmp" =>
    let op ← cmpOpOf (← getStr j "op")
    return encPy enRes (tupleRichcompare E op (← jEls (← field j "a")) (← jEls (← field j "b")))
  | "tuple.new" =>
    let (src, t) ← jSrc (← field j "src")
    return encPy (enTRes t noTup) (tupleNew mayTrack (some src))
  | "tuple.sub_new" =>
    let (src, _) ← jSrc (← field j "src")
    return encPy (fun (t : Tup DEl) => Json.arr #[enEls t.items, toJson t.exact]) (tupleSubtypeNew mayTrack (some src))
  | "tuple.call" =>
    let nargs ← getNat j "nargs"
    let nkw ← getNat j "nkw"
    let args := List.replicate nargs (TupleSrc.exactTuple noTup)
    return encPy (fun _ => Json.null) (tupleVectorcall mayTrack args nkw)
  | "tuple.getnewargs" =>
    let t ← jTup (← field j "t")
    return encPy (enTRes t noTup) (tupleGetnewargs mayTrack t)
  | "tuple.iter" => runTupleIter j
  | "tuple.referents" =>
    return okJ (Json.arr ((tupleTraverse (← jEls (← field j "items"))).map enOpt).toArray)
  | "tuple.release" =>
    let n ← getNat j "n"
    return okJ (Json.arr ((tupleDeallocOrder (List.range n)).map enOptNat).toArray)
  | "tuple.c_size" =>
    let op := (jEls (← field j "items")).toOption
    return encPy toJson (pyTupleSize op)
  | "tuple.c_getitem" =>
    let op := (jEls (← field j "items")).toOption
    return encPy enEl (pyTupleGetItem op (← getInt j "i"))
  | "tuple.c_setitem" =>
    let op := (jEls (← field j "items")).toOption
    return encPy enEls (pyTupleSetItem op (← getBool j "unique") (← getInt j "i") (← jEl (← field j "x")))
  | "tuple.c_getslice" =>
    let items ← jEls (← field j "items")
    let t : Tup DEl := { items := items, tracked := items.any mayTrack }
    return encPy (enTRes t noTup) (pyTupleGetSlice mayTrack (some t) (← getInt j "i") (← getInt j "j"))
  | "tuple.c_new" =>
    return encPy (fun (r : TRes (Option DEl)) => toJson (r.items [] []).length) (pyTupleNew (← getInt j "n"))
  | "tuple.c_pack" =>
    let items ← jEls (← field j "items")
    return encPy (enTRes noTup noTup) (tuplePack mayTrack items.length items)
  | "tuple.c_resize" =>
    let items ← jEls (← field j "items")
    let enO : Option DEl → Json := fun x => match x with | some v => enEl v | none => Json.null
    return encPy (fun (l : List (Option DEl)) => Json.arr (l.map enO).toArray)
      (tupleResize (some (items.map some)) true true (← getInt j "n"))
  | "tuple.untrack" =>
    let items ← jEls (← field j "items")
    return okJ (toJson (tupleMaybeUntrack mayTrack true true (items.map some)))
  | _ => throw s!"unknown fn {fn}"

/-! ## Lists: everything but `list.ops` -/

/-- `{"heap": [{"list": b, "items": [...]}, ...], "root": k}`; an item that is a
string is an atom, a number a heap reference. -/
def jHeap (j : Json) : Except String RHeap := do
  let cells ← j.getArr?
  cells.toList.mapM fun c => do
    let isList ← getBool c "list"
    let items ← (← field c "items").getArr?
    let items ← items.toList.mapM fun (x : Json) =>
      match x with
      | .str s => Except.ok (RObj.atom s)
      | v => do return RObj.ref (← v.getNat?)
    return { isList := isList, items := items }

def elIntPair : Json → Except String (List Nat)
  | j => do
    let a ← j.getArr?
    a.toList.mapM (·.getNat?)

def runList (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "list.ops" => runOps j
  | "list.iter" => runIter j
  | "list.cmp" =>
    let op ← cmpOpOf (← getStr j "op")
    let a ← jEls (← field j "a")
    let b ← jEls (← field j "b")
    let fuel := a.length + b.length + 64
    let (r, st) := listRichcompare E effCmp2 effFinal fuel op a b
    return okJ (Json.arr #[encPy enRes r, enEls st.1])
  | "list.repr" =>
    let h ← jHeap (← field j "heap")
    return encPy toJson (reprObj h (h.length + 2) [] (.ref (← getNat j "root")))
  | "list.call" =>
    let nargs ← getNat j "nargs"
    let nkw ← getNat j "nkw"
    let args := List.replicate nargs (ExtArg.fast ([] : List DEl))
    return encPy (fun _ => Json.null) (listVectorcall args nkw)
  | "list.referents" =>
    return okJ (Json.arr ((listTraverse (← jEls (← field j "items"))).map enOpt).toArray)
  | "list.release" =>
    let n ← getNat j "n"
    let o := LObj.prealloc (List.range n)
    return okJ (Json.arr ((listDeallocOrder o).map enOptNat).toArray)
  | "list.clear_release" =>
    let n ← getNat j "n"
    let o := listFromStack (List.range n)
    return okJ (Json.arr ((listClearOrder o).map enOptNat).toArray)
  | "list.sort_sizeof" => return okJ (toJson (listSizeof (listDuringSort : St)))
  | "list.sizeof_sub" =>
    -- `type_new` lays out `k` `__slots__` after the `PyListObject` (40 bytes): `40 + 8 * k`.
    let k ← getNat j "k"
    let items ← jEls (← field j "items")
    let o := (listInit (LObj.empty : St) (some (.fast items))).1
    return okJ (toJson (listSizeof o (40 + 8 * (k : Int))))
  | "list.latin_lt" =>
    let v ← elIntPair (← field j "v")
    let w ← elIntPair (← field j "w")
    return okJ (Json.arr #[toJson (unsafeLatinCompare v w), toJson (strLt v w)])
  | "list.tuple_sort" =>
    let keys ← (← field j "keys").getArr?
    let keys ← keys.toList.mapM (fun k => jEls k)
    let lt : List DEl → List DEl → Bool := fun v w =>
      match unsafeTupleCompare E (fun x y => richBool E .lt x y) v w with
      | .ok b => b
      | .error _ => false
    return okJ (Json.arr (((PyLean.ListSort.listSort lt keys).map enEls).toArray))
  | "list.c_size" => return encPy toJson (pyListSize (jEls (← field j "items")).toOption)
  | "list.c_getitem" =>
    return encPy enEl (pyListGetItem (jEls (← field j "items")).toOption (← getInt j "i"))
  | "list.c_getitemref" =>
    return encPy enEl (pyListGetItemRef (jEls (← field j "items")).toOption (← getInt j "i"))
  | "list.c_setitem" =>
    let o : Option St := (jEls (← field j "items")).toOption.map LObj.prealloc
    return encPy stateJ (pyListSetItem o (← getInt j "i") (← jEl (← field j "x")))
  | "list.c_insert" =>
    let o : Option St := (jEls (← field j "items")).toOption.map LObj.prealloc
    let v := (jEl (← field j "x")).toOption
    let v := match j.getObjVal? "null" with | .ok _ => none | _ => v
    return encPy stateJ (pyListInsert o (← getInt j "i") v)
  | "list.c_append" =>
    let o : Option St := (jEls (← field j "items")).toOption.map LObj.prealloc
    let v := (jEl (← field j "x")).toOption
    let v := match j.getObjVal? "null" with | .ok _ => none | _ => v
    return encPy stateJ (pyListAppend o v)
  | "list.c_getslice" =>
    return encPy stateJ (pyListGetSlice (jEls (← field j "items")).toOption (← getInt j "i") (← getInt j "j"))
  | "list.c_setslice" =>
    let o : Option St := (jEls (← field j "items")).toOption.map LObj.prealloc
    let vj ← field j "v"
    let v : AssVal DEl :=
      if (← getBool j "self") then .selfCopy
      else if vj == Json.str "noniter" then .notIterable
      else match jEls vj with
        | .ok items => .seq items
        | .error _ => .del
    return encPy stateJ (pyListSetSlice o (← getInt j "i") (← getInt j "j") v)
  | "list.c_clear" =>
    return encPy stateJ (pyListClear ((jEls (← field j "items")).toOption.map LObj.prealloc))
  | "list.c_reverse" =>
    return encPy stateJ (pyListReverse ((jEls (← field j "items")).toOption.map LObj.prealloc))
  | "list.c_astuple" =>
    return encPy (enTRes noTup noTup) (pyListAsTuple mayTrack (jEls (← field j "items")).toOption)
  | "list.c_new" =>
    return encPy (fun (o : LObj (Option DEl)) => Json.arr #[toJson o.items.length, toJson (listSizeof o)])
      (pyListNew (← getInt j "n"))
  | "list.c_extend" =>
    let o : Option St := (jEls (← field j "items")).toOption.map LObj.prealloc
    let ((r, e), ok) := pyListExtend o (← jExt (← field j "arg"))
    match ok, e with
    | none, some e => return errJ e
    | _, some e => return errJ e
    | _, none => return okJ (stateJ r)
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j =>
  if fn.startsWith "tuple." then some (runTuple fn j)
  else if fn.startsWith "list." then some (runList fn j)
  else none

end PyLean.BytesObj.Seq
