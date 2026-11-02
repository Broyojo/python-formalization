import PyLean.DiffCore
import PyLean.Sequences.ArrayModel
import PyLean.Sequences.DequeModel
import PyLean.Sequences.DefaultDict

/-! Differential-testing handler for `sequences` cases (`"mod": "sequences"`).

A case is `{"fn": kind, "init": [...], "ops": [[name, args...], ...]}` plus what the
kind needs. The result is `{"ok": [[r, state], ...]}` with one entry per operation,
where `r` is the operation's `{"ok": v}`/`{"exc", "msg"}` and `state` the object
afterwards; construction errors are returned directly. A slice is
`[start|null, stop|null, step|null]`.

Deque elements (`DElem`) are ints and two kinds of object with an `__eq__` that
misbehaves: `"B"` raises, `"M<k>"` mutates the deque under test. They exercise the
exception and mutation checks of the comparison loops. -/

namespace PyLean.Sequences

open Lean PyLean PyLean.Diff
open PyLean.RangeSlice (Slice)

def jInt (j : Json) : Except String Int := j.getInt?
def jInts (j : Json) : Except String (List Int) := do
  let arr ← j.getArr?
  arr.toList.mapM jInt
def jOptInt : Json → Except String (Option Int)
  | .null => .ok none
  | v => some <$> v.getInt?
def jSlice (j : Json) : Except String Slice := do
  let arr ← j.getArr?
  let some a := arr[0]? | throw "slice"
  let some b := arr[1]? | throw "slice"
  let some c := arr[2]? | throw "slice"
  return ⟨← jOptInt a, ← jOptInt b, ← jOptInt c⟩

def arg (op : Array Json) (k : Nat) : Except String Json :=
  match op[k]? with
  | some v => .ok v
  | none => .error s!"missing argument {k}"
def optArg (op : Array Json) (k : Nat) : Except String (Option Int) :=
  match op[k]? with
  | some v => jOptInt v
  | none => .ok none

def unitJ : Json := Json.null
def errJ (e : PyExc) : Json := encPy (fun (_ : Unit) => Json.null) (.error e)
def okJ (v : Json) : Json := Json.mkObj [("ok", v)]
def pyJ {β : Type} (enc : β → Json) (r : Py β) : Json :=
  match r with
  | .ok v => okJ (enc v)
  | .error e => errJ e
def intJ (i : Int) : Json := toJson i
def natsJ (l : List Nat) : Json := toJson l

/-! ### Elements of deques -/

inductive DElem where
  | int (n : Int)
  | bomb
  | mut (k : Nat)
  deriving Repr, DecidableEq, Inhabited

instance : Inhabited DElem := ⟨.int 0⟩

def DElem.toJ : DElem → Json
  | .int n => toJson n
  | .bomb => toJson "B"
  | .mut k => toJson s!"M{k}"

def jElem (j : Json) : Except String DElem :=
  match j with
  | .str "B" => .ok .bomb
  | .str s =>
    match (s.drop 1).toString.toNat? with
    | some k => .ok (.mut k)
    | none => .error "element"
  | v => DElem.int <$> v.getInt?

def jElems (j : Json) : Except String (List DElem) := do
  let arr ← j.getArr?
  arr.toList.mapM jElem

def DElem.repr : DElem → Py String
  | .int n => .ok (toString n)
  | .bomb => .ok "B"
  | .mut k => .ok s!"M{k}"

/-- What the `__eq__` of the mutator `M<k>` does to the deque under test. -/
def mutate (k : Nat) (d : Deque DElem) : Py Bool × Deque DElem :=
  match k with
  | 0 => (.ok false, d.append (.int 0))
  | 1 => (.ok false, d.clear)
  | 2 =>
    match d.setitem 0 (some (.int 7)) with
    | .ok d' => (.ok false, d')
    | .error _ => (.ok false, d)
  | 3 =>
    match d.rotateC 1 with
    | .ok d' => (.ok false, d')
    | .error _ => (.ok false, d)
  | _ => (.ok true, d.append (.int 0))

/-- `PyObject_RichCompareBool(a, b, Py_EQ)`: identity first, then the left
operand's `__eq__`, then the reflected one. -/
def dCmp : Cmp DElem := fun d a b =>
  if a = b then (.ok true, d)
  else
    match a, b with
    | .int _, .int _ => (.ok false, d)
    | .bomb, _ => (.error (.valueError "boom"), d)
    | .mut k, _ => mutate k d
    | _, .bomb => (.error (.valueError "boom"), d)
    | _, .mut k => mutate k d

def dEq (a b : DElem) : Py Bool := (dCmp default a b).1

def dRich (op : CmpOp) (a b : DElem) : Py Bool :=
  match a, b with
  | .int x, .int y => .ok (opHolds op (compare x y))
  | _, _ => .error (.typeError "unorderable")

def jOp (j : Json) : Except String CmpOp := do
  match ← j.getStr? with
  | "lt" => pure .lt | "le" => pure .le | "eq" => pure .eq
  | "ne" => pure .ne | "gt" => pure .gt | "ge" => pure .ge
  | s => throw s!"op {s}"

/-! ### Lists -/

/-- Run one op: `(result, new state)`; a raising op keeps the old state
unless the model says otherwise. -/
def stepList (l : List Int) (op : Array Json) : Except String (Json × List Int) := do
  let name ← (← arg op 0).getStr?
  let f : Int → Int → Bool := fun a b => a == b
  let keep {α} (r : Py α) (enc : α → Json) (st : α → List Int) : Json × List Int :=
    match r with
    | .ok v => (okJ (enc v), st v)
    | .error e => (errJ e, l)
  match name with
  | "append" => return (okJ unitJ, listAppend l (← jInt (← arg op 1)))
  | "insert" => return keep (listInsert l (← jInt (← arg op 1)) (← jInt (← arg op 2))) (fun _ => unitJ) id
  | "pop" => return keep (listPop l (← optArg op 1)) (fun p => toJson p.1) (·.2)
  | "index" => return keep (listIndexBy f l (← jInt (← arg op 1)) (← optArg op 2) (← optArg op 3)) toJson (fun _ => l)
  | "count" => return (okJ (toJson (listCountBy f l (← jInt (← arg op 1)))), l)
  | "remove" => return keep (listRemoveBy f l (← jInt (← arg op 1))) (fun _ => unitJ) id
  | "getitem" => return keep (listGetItem l (← jInt (← arg op 1))) toJson (fun _ => l)
  | "setitem" => return keep (listAssItem l (← jInt (← arg op 1)) (some (← jInt (← arg op 2)))) (fun _ => unitJ) id
  | "delitem" => return keep (listAssItem l (← jInt (← arg op 1)) none) (fun _ => unitJ) id
  | "setslice" => return keep (listAssSubscript l (← jSlice (← arg op 1)) (some (← jInts (← arg op 2)))) (fun _ => unitJ) id
  | "setslice_self" => return keep (listAssSubscript l (← jSlice (← arg op 1)) (some l)) (fun _ => unitJ) id
  | "delslice" => return keep (listAssSubscript l (← jSlice (← arg op 1)) none) (fun _ => unitJ) id
  | "imul" => return keep (listIRepeat l (← jInt (← arg op 1))) (fun _ => unitJ) id
  | "mul" => return keep (listRepeat l (← jInt (← arg op 1))) toJson (fun _ => l)
  | "init" => return (okJ unitJ, listInit l (← jInts (← arg op 1)))
  | "init_self" => return (okJ unitJ, listInit l [])
  | "extend" => return (okJ unitJ, l ++ (← jInts (← arg op 1)))
  | other => throw s!"unknown list op {other}"

/-! ### Deques -/

def dequeJ (d : Deque DElem) : Json :=
  Json.arr #[toJson (d.items.map DElem.toJ), (match d.getMaxlen with | none => Json.null | some m => toJson m),
    toJson d.blocks]

def jMaxlen (op : Array Json) (k : Nat) : Except String MaxlenArg := do
  match op[k]? with
  | none | some .null => return .absent
  | some (.str _) => return .other
  | some v => return .int (← v.getInt?)

/-- A deque under test and its iterators (`true`: reversed). -/
structure DState where
  d : Deque DElem
  its : Array (Deque.Iter × Bool)

def stepDeque (s : DState) (op : Array Json) : Except String (Json × DState) := do
  let d := s.d
  let name ← (← arg op 0).getStr?
  let keep {α} (r : Py α) (enc : α → Json) (st : α → Deque DElem) : Json × DState :=
    match r with
    | .ok v => (okJ (enc v), { s with d := st v })
    | .error e => (errJ e, s)
  let pair {α} (r : Py α × Deque DElem) (enc : α → Json) : Json × DState :=
    (pyJ enc r.1, { s with d := r.2 })
  let same (j : Json) : Json × DState := (j, s)
  let its (k : Nat) : Except String (Deque.Iter × Bool) :=
    match s.its[k]? with
    | some v => .ok v
    | none => .error "iterator"
  match name with
  | "append" => return (okJ unitJ, { s with d := d.append (← jElem (← arg op 1)) })
  | "appendleft" => return (okJ unitJ, { s with d := d.appendleft (← jElem (← arg op 1)) })
  | "pop" => return keep d.pop (fun p => p.1.toJ) (·.2)
  | "popleft" => return keep d.popleft (fun p => p.1.toJ) (·.2)
  | "extend" => return pair (d.extendIter (.iter (← jElems (← arg op 1)) none)) (fun _ => unitJ)
  | "extendleft" => return pair (d.extendleftIter (.iter (← jElems (← arg op 1)) none)) (fun _ => unitJ)
  | "iadd" => return pair (d.iadd (.iter (← jElems (← arg op 1)) none)) (fun _ => unitJ)
  | "extend_raise" => return pair (d.extendIter (.iter (← jElems (← arg op 1)) (some (.valueError "iter")))) (fun _ => unitJ)
  | "extendleft_raise" => return pair (d.extendleftIter (.iter (← jElems (← arg op 1)) (some (.valueError "iter")))) (fun _ => unitJ)
  | "extend_stop" => return pair (d.extendIter (.iter (← jElems (← arg op 1)) (some .stopIteration))) (fun _ => unitJ)
  | "extend_bad" => return pair (d.extendIter (.notIterable "int")) (fun _ => unitJ)
  | "extendleft_bad" => return pair (d.extendleftIter (.notIterable "int")) (fun _ => unitJ)
  | "iadd_bad" => return pair (d.iadd (.notIterable "int")) (fun _ => unitJ)
  | "extend_self" | "iadd_self" => return (okJ unitJ, { s with d := d.extendSelf })
  | "extendleft_self" => return (okJ unitJ, { s with d := d.extendleftSelf })
  | "rotate" => return keep (d.rotate ((← optArg op 1).getD 1)) (fun _ => unitJ) id
  | "index" => return pair (d.index dCmp (← jElem (← arg op 1)) (← optArg op 2) (← optArg op 3)) toJson
  | "insert" => return keep (d.insert (← jInt (← arg op 1)) (← jElem (← arg op 2))) (fun _ => unitJ) id
  | "remove" => return pair (d.remove dCmp (← jElem (← arg op 1))) (fun _ => unitJ)
  | "count" => return pair (d.count dCmp (← jElem (← arg op 1))) toJson
  | "contains" => return pair (d.contains dCmp (← jElem (← arg op 1))) toJson
  | "reverse" => return keep d.reverse (fun _ => unitJ) id
  | "getitem" => return keep (d.getitem (← jInt (← arg op 1))) (·.toJ) (fun _ => d)
  | "setitem" => return keep (d.setitem (← jInt (← arg op 1)) (some (← jElem (← arg op 2)))) (fun _ => unitJ) id
  | "delitem" => return keep (d.setitem (← jInt (← arg op 1)) none) (fun _ => unitJ) id
  | "copy" => return same (pyJ dequeJ d.copy)
  | "imul" => return keep (d.irepeat (← jInt (← arg op 1))) (fun _ => unitJ) id
  | "mul" => return same (pyJ dequeJ (d.mul (← jInt (← arg op 1))))
  | "add" =>
    let other ← match Deque.make (← jElems (← arg op 1)) (← jMaxlen op 2) with
      | .ok o => pure o
      | .error _ => throw "add: bad other deque"
    return same (pyJ dequeJ (d.concat (.inl other)))
  | "add_self" => return same (pyJ dequeJ (d.concat (.inl d)))
  | "add_bad" => return same (pyJ dequeJ (d.concat (.inr "list")))
  | "clear" => return (okJ unitJ, { s with d := d.clear })
  | "init" => return pair (d.init (.iter (← jElems (← arg op 1)) none) (← jMaxlen op 2)) (fun _ => unitJ)
  | "init_self" => return pair (d.init (.iter [] none) (← jMaxlen op 1)) (fun _ => unitJ)
  | "len" => return same (okJ (toJson d.len))
  | "maxlen" => return same (okJ (match d.getMaxlen with | none => Json.null | some m => toJson m))
  | "repr" => return same (pyJ toJson (d.repr DElem.repr false))
  | "repr_nested" =>
    -- repr(d) of a deque holding itself as the last item
    let inner ← match d.repr DElem.repr true with
      | .ok v => pure v
      | .error _ => throw "repr"
    let r : DElem → Py String := fun e => if e = .mut 99 then .ok inner else e.repr
    return same (pyJ toJson ((d.append (.mut 99)).repr r false))
  | "reduce" =>
    let (m, _) := d.reduce
    return same (okJ (Json.arr #[(match m with | none => Json.null | some v => toJson v),
      toJson (d.items.map DElem.toJ)]))
  | "cmp" =>
    let o ← jOp (← arg op 1)
    let other ← match Deque.make (← jElems (← arg op 2)) .absent with
      | .ok o => pure o
      | .error _ => throw "cmp: bad other deque"
    return same (pyJ toJson (Deque.richcompare dEq (dRich o) o false d other))
  | "cmp_self" =>
    let o ← jOp (← arg op 1)
    return same (pyJ toJson (Deque.richcompare dEq (dRich o) o true d d))
  | "it_new" =>
    let rev ← (← arg op 1).getBool?
    return ((okJ unitJ), { s with its := s.its.push ((if rev then d.reviter else d.iter), rev) })
  | "it_make" =>
    let rev ← (← arg op 1).getBool?
    match (if rev then d.reviterNew else d.iterNew) (← jInt (← arg op 2)) with
    | .ok it => return ((okJ unitJ), { s with its := s.its.push (it, rev) })
    | .error e => return (errJ e, s)
  | "it_next" =>
    let k ← (← arg op 1).getNat?
    let (it, rev) ← its k
    let (r, it') := (if rev then d.reviterNext else d.iterNext) it
    return (pyJ (fun o => match o with | some x => x.toJ | none => toJson "STOP") r,
      { s with its := s.its.set! k (it', rev) })
  | "it_len" => return same (okJ (toJson (Deque.iterLen (← its (← (← arg op 1).getNat?)).1)))
  | "it_reduce" => return same (okJ (toJson (d.iterReduce (← its (← (← arg op 1).getNat?)).1)))
  | other => throw s!"unknown deque op {other}"

/-! ### Arrays -/

def PyVal.toJ : PyVal → Json
  | .int n => toJson n
  | .float b => Json.mkObj [("f", toJson b)]
  | .complex re im => Json.mkObj [("c", toJson [re, im])]
  | .str c => Json.mkObj [("s", toJson c)]
  | .obj t _ => Json.mkObj [("o", toJson t)]

def jVal (j : Json) : Except String PyVal :=
  match j with
  | .obj _ =>
    match j.getObjVal? "f", j.getObjVal? "s", j.getObjVal? "o", j.getObjVal? "c" with
    | .ok b, _, _, _ => PyVal.float <$> b.getNat?
    | _, .ok c, _, _ => do
      let arr ← c.getArr?
      return .str (← arr.toList.mapM (·.getNat?))
    | _, _, .ok t, _ => do
      let i ← jOptInt ((j.getObjVal? "i").toOption.getD .null)
      return .obj (← t.getStr?) i
    | _, _, _, .ok c => do
      let arr ← c.getArr?
      let some re := arr[0]? | throw "complex"
      let some im := arr[1]? | throw "complex"
      return .complex (← re.getNat?) (← im.getNat?)
    | _, _, _, _ => .error "value"
  | v => PyVal.int <$> v.getInt?

def jVals (j : Json) : Except String (List PyVal) := do
  let arr ← j.getArr?
  arr.toList.mapM jVal

def jNats (j : Json) : Except String (List Nat) := do
  let arr ← j.getArr?
  arr.toList.mapM (·.getNat?)

def jTC (j : Json) : Except String TC := do
  let s ← j.getStr?
  match TC.all.find? (fun t => t.code == s) with
  | some t => pure t
  | none => throw s!"typecode {s}"

/-- The object of a comparison argument: `{"o": "Bomb"}` raises. -/
def eqOf (x : PyVal) : PyVal → Py Bool := fun v =>
  match x with
  | .obj "Bomb" _ => .error (.valueError "boom")
  | x => .ok (pvEq v x)

def arrJ (a : Arr) : Json :=
  Json.arr #[natsJ (arrToBytes a), toJson a.allocated, toJson a.hasBuf]

def strRepr (s : List Nat) : String := "<str " ++ toString s ++ ">"
def floatRepr (b : Nat) : String := s!"<float {b}>"

/-- An array of the typecode of `tcj` holding the C values of `vs`. -/
def arrOf (tc : TC) (vs : List PyVal) : Except String Arr :=
  match arrNew "array" tc.code (.list vs) with
  | .ok a => .ok a
  | .error _ => .error "bad array operand"

def reducedJ : Reduced → Json
  | .asList t c vs => Json.arr #[toJson t, toJson c, toJson (vs.map PyVal.toJ)]
  | .asBytes t c m b => Json.arr #[toJson t, toJson c, toJson m, natsJ b]

structure AState where
  a : Arr
  its : Array ArrIter

def stepArr (s : AState) (op : Array Json) : Except String (Json × AState) := do
  let a := s.a
  let name ← (← arg op 0).getStr?
  let keep {α} (r : Py α) (enc : α → Json) (st : α → Arr) : Json × AState :=
    match r with
    | .ok v => (okJ (enc v), { s with a := st v })
    | .error e => (errJ e, s)
  let same (j : Json) : Json × AState := (j, s)
  let optE (r : Arr × Option PyExc) : Json × AState :=
    ((match r.2 with | none => okJ unitJ | some e => errJ e), { s with a := r.1 })
  let its (k : Nat) : Except String ArrIter :=
    match s.its[k]? with
    | some v => .ok v
    | none => .error "iterator"
  match name with
  | "append" => return optE (arrAppendS a (← jVal (← arg op 1)))
  | "insert" => return optE (arrInsertS a (← jInt (← arg op 1)) (← jVal (← arg op 2)))
  | "pop" => return keep (arrPop a (← optArg op 1)) (fun p => p.1.toJ) (·.2)
  | "index" => return same (pyJ toJson (arrIndex a (eqOf (← jVal (← arg op 1))) (← optArg op 2) (← optArg op 3)))
  | "count" => return same (pyJ toJson (arrCount a (eqOf (← jVal (← arg op 1)))))
  | "contains" => return same (pyJ toJson (arrContains a (eqOf (← jVal (← arg op 1)))))
  | "remove" => return keep (arrRemove a (eqOf (← jVal (← arg op 1)))) (fun _ => unitJ) id
  | "getitem" => return same (pyJ (·.toJ) (arrGetItem a (← jInt (← arg op 1))))
  | "sqitem" =>
    let i ← jInt (← arg op 1)
    return same (pyJ (·.toJ) (arrItem a (if i < 0 then i + a.items.length else i)))
  | "setitem" => return keep (arrAssIndex a (← jInt (← arg op 1)) (some (← jVal (← arg op 2)))) (fun _ => unitJ) id
  | "delitem" => return keep (arrAssIndex a (← jInt (← arg op 1)) none) (fun _ => unitJ) id
  | "sqsetitem" =>
    let i ← jInt (← arg op 1)
    return keep (arrAssItem a (if i < 0 then i + a.items.length else i) (some (← jVal (← arg op 2)))) (fun _ => unitJ) id
  | "sqdelitem" =>
    let i ← jInt (← arg op 1)
    return keep (arrAssItem a (if i < 0 then i + a.items.length else i) none) (fun _ => unitJ) id
  | "getslice" => return same (pyJ arrJ (arrGetSlice a (← jSlice (← arg op 1))))
  | "setslice" =>
    let tc ← jTC (← arg op 2)
    let o ← arrOf tc (← jVals (← arg op 3))
    return keep (arrAssSlice a (← jSlice (← arg op 1)) (.arr o false)) (fun _ => unitJ) id
  | "setslice_self" => return keep (arrAssSlice a (← jSlice (← arg op 1)) (.arr a true)) (fun _ => unitJ) id
  | "setslice_bad" => return keep (arrAssSlice a (← jSlice (← arg op 1)) (.other "list")) (fun _ => unitJ) id
  | "delslice" => return keep (arrAssSlice a (← jSlice (← arg op 1)) .delete) (fun _ => unitJ) id
  | "imul" => return keep (arrIRepeat a (← jInt (← arg op 1))) (fun _ => unitJ) id
  | "mul" => return same (pyJ arrJ (arrRepeat a (← jInt (← arg op 1))))
  | "add" => return same (pyJ arrJ (arrConcat a (.inl (← arrOf (← jTC (← arg op 1)) (← jVals (← arg op 2))))))
  | "add_bad" => return same (pyJ arrJ (arrConcat a (.inr "list")))
  | "iadd" => return keep (arrIConcat a (.inl (← arrOf (← jTC (← arg op 1)) (← jVals (← arg op 2))))) (fun _ => unitJ) id
  | "iadd_bad" => return keep (arrIConcat a (.inr "list")) (fun _ => unitJ) id
  | "iadd_self" => return keep (arrIConcat a (.inl a)) (fun _ => unitJ) id
  | "extend" => return optE (arrExtend a (.inr (.iter (← jVals (← arg op 1)) none)))
  | "extend_raise" => return optE (arrExtend a (.inr (.iter (← jVals (← arg op 1)) (some (.valueError "iter")))))
  | "extend_bad" => return optE (arrExtend a (.inr (.notIterable "int")))
  | "extend_arr" => return optE (arrExtend a (.inl (← arrOf (← jTC (← arg op 1)) (← jVals (← arg op 2)))))
  | "extend_self" => return optE (arrExtend a (.inl a))
  | "fromlist" =>
    let (r, a') := arrFromList a (.inl (← jVals (← arg op 1)))
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "fromlist_bad" =>
    let (r, a') := arrFromList a (.inr "tuple")
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "tolist" => return same (pyJ (fun vs => toJson (vs.map PyVal.toJ)) (arrToList a))
  | "frombytes" => return keep (arrFromBytes a (← jNats (← arg op 1)) 1) (fun _ => unitJ) id
  | "frombytes_wide" => return keep (arrFromBytes a (← jNats (← arg op 1)) 2) (fun _ => unitJ) id
  | "tobytes" => return same (okJ (natsJ (arrToBytes a)))
  | "fromfile" =>
    let bs ← jNats (← arg op 1)
    let (r, a') := arrFromFile a (fun n => .bytes (bs.take n.toNat)) (← jInt (← arg op 2))
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "fromfile_notbytes" =>
    let (r, a') := arrFromFile a (fun _ => .notBytes) (← jInt (← arg op 1))
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "fromfile_raise" =>
    let (r, a') := arrFromFile a (fun _ => .raises (.valueError "read")) (← jInt (← arg op 1))
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "tofile" => return same (okJ (toJson ((arrToFile a).map natsJ)))
  | "fromunicode" => return keep (arrFromUnicode a (← jNats (← arg op 1))) (fun _ => unitJ) id
  | "tounicode" => return same (pyJ natsJ (arrToUnicode a))
  | "byteswap" => return (okJ unitJ, { s with a := arrByteswap a })
  | "reverse" => return (okJ unitJ, { s with a := arrReverse a })
  | "clear" => return keep (arrClear a) (fun _ => unitJ) id
  | "copy" => return same (pyJ arrJ (arrCopy a))
  | "buffer_info" =>
    let (nz, n) := arrBufferInfo a
    return same (okJ (Json.arr #[toJson nz, toJson n]))
  | "typecode" => return same (okJ (toJson a.tc.code))
  | "itemsize" => return same (okJ (toJson a.tc.itemsize))
  | "len" => return same (okJ (toJson (arrLength a)))
  | "reduce_ex" => return same (pyJ reducedJ (arrReduceEx a (← jVal (← arg op 1))))
  | "repr" => return same (pyJ toJson (arrRepr floatRepr strRepr a))
  | "mv_open" =>
    let ((f, i, n, b), a') := arrGetBuf a
    return (okJ (Json.arr #[toJson f, toJson i, toJson n, toJson b]), { s with a := a' })
  | "mv_close" => return (okJ unitJ, { s with a := arrRelBuf a })
  | "cmp" =>
    let o ← jOp (← arg op 1)
    let other ← arrOf (← jTC (← arg op 2)) (← jVals (← arg op 3))
    return same (pyJ toJson (arrRich o a other))
  | "it_new" => return (okJ unitJ, { s with its := s.its.push arrIter })
  | "it_next" =>
    let k ← (← arg op 1).getNat?
    let (r, it') := arrIterNext a (← its k)
    return (pyJ (fun o => match o with | some x => x.toJ | none => toJson "STOP") r,
      { s with its := s.its.set! k it' })
  | "it_reduce" =>
    let it ← its (← (← arg op 1).getNat?)
    return same (okJ (match arrIterReduce it with | some i => toJson i | none => Json.null))
  | "it_setstate" =>
    let k ← (← arg op 1).getNat?
    match arrIterSetstate a (← its k) (← jInt (← arg op 2)) with
    | .ok it' => return (okJ unitJ, { s with its := s.its.set! k it' })
    | .error e => return (errJ e, s)
  | other => throw s!"unknown array op {other}"

def jInit (j : Json) : Except String Init := do
  let k ← (← field j "kind").getStr?
  match k with
  | "none" => return .none
  | "list" => return .list (← jVals (← field j "v"))
  | "tuple" => return .tuple (← jVals (← field j "v"))
  | "bytes" | "bytearray" => return .bytes (← jNats (← field j "v"))
  | "str" => return .str (← jNats (← field j "v"))
  | "iter" => return .iter (.iter (← jVals (← field j "v")) none)
  | "iter_raise" => return .iter (.iter (← jVals (← field j "v")) (some (.valueError "iter")))
  | "bad" => return .iter (.notIterable "int")
  | "array" =>
    match arrNew "array" (← getStr j "tc") (.list (← jVals (← field j "v"))) with
    | .ok a => return .arr a
    | .error _ => throw "init array"
  | k => throw s!"init {k}"

/-! ### defaultdict, `_count_elements`, `_tuplegetter` -/

/-- The factories the difftest uses (`F0` ... `F3`). -/
def facOf (name : String) : Factory Int Int :=
  match name with
  | "null" => .null
  | "none" => .none
  | "F1" => .call "F1" (fun d => (.error (.valueError "fac"), d))
  | "F2" => .call "F2" (fun d => (.ok 1, dictSet d 100 7))
  | "F3" => .call "F3" (fun d => (.ok 1, dictSet d 1 5))
  | _ => .call "F0" (fun d => (.ok 0, d))

def itemsJ (d : PyDict Int Int) : Json := toJson (d.map (fun kv => [kv.1, kv.2]))

def jItems (j : Json) : Except String (PyDict Int Int) := do
  let arr ← j.getArr?
  arr.toList.mapM (fun p => do
    let q ← p.getArr?
    let some a := q[0]? | throw "pair"
    let some b := q[1]? | throw "pair"
    return ((← a.getInt?), (← b.getInt?)))

def baseRepr (d : PyDict Int Int) : String :=
  "{" ++ ", ".intercalate (d.map (fun kv => s!"{kv.1}: {kv.2}")) ++ "}"

def stepDD (dd : DefDict Int Int) (op : Array Json) : Except String (Json × DefDict Int Int) := do
  let name ← (← arg op 0).getStr?
  let pair (r : Py Int × DefDict Int Int) : Json × DefDict Int Int := (pyJ toJson r.1, r.2)
  let dj (x : DefDict Int Int) : Json := Json.arr #[toJson x.tname, itemsJ x.items,
    toJson (DefDict.repr x baseRepr false)]
  match name with
  | "getitem" => return pair (dd.getitem toString (← jInt (← arg op 1)))
  | "missing" => return pair (dd.missing toString (← jInt (← arg op 1)))
  | "copy" => return (okJ (dj dd.copy), dd)
  | "reduce" =>
    let (f, items) := dd.reduce
    return (okJ (Json.arr #[(match f with | some r => toJson r | none => Json.null), itemsJ items]), dd)
  | "repr" => return (okJ (toJson (dd.repr baseRepr false)), dd)
  | "repr_nested" =>
    let inner := ({ dd with factory := facOf "F0" }).repr baseRepr true
    let outer := ({ dd with factory := .call inner (fun d => (.ok 0, d)) }).repr baseRepr false
    return (okJ (toJson outer), dd)
  | "or_dict" =>
    let r := DefDict.orOp (.dd dd) (.plain (dictUpdate [] (← jItems (← arg op 1))))
    return (okJ (match r with | some x => dj x | none => toJson "NI"), dd)
  | "ror_dict" =>
    let r := DefDict.orOp (.plain (dictUpdate [] (← jItems (← arg op 1)))) (.dd dd)
    return (okJ (match r with | some x => dj x | none => toJson "NI"), dd)
  | "or_dd" =>
    let o : DefDict Int Int := ⟨dictUpdate [] (← jItems (← arg op 1)), facOf (← (← arg op 2).getStr?), "defaultdict"⟩
    let r := DefDict.orOp (.dd dd) (.dd o)
    return (okJ (match r with | some x => dj x | none => toJson "NI"), dd)
  | "or_frozen" =>
    let r := DefDict.orOp (.dd dd) (.frozen (dictUpdate [] (← jItems (← arg op 1))))
    return (okJ (match r with | some x => dj x | none => toJson "NI"), dd)
  | "ror_frozen" =>
    let r := DefDict.orOp (.frozen (dictUpdate [] (← jItems (← arg op 1)))) (.dd dd)
    return (okJ (match r with | some x => dj x | none => toJson "NI"), dd)
  | "or_bad" =>
    let r := DefDict.orOp (.dd dd) .notDict
    return (okJ (match r with | some x => dj x | none => toJson "NI"), dd)
  | "init" =>
    let f ← (← arg op 1).getStr?
    let first : DefDict.FactoryArg Int Int := if f == "absent" then .absent else if f == "bad" then .bad
      else .given (facOf f)
    let (r, d') := dd.init first (.ok (← jItems (← arg op 2)))
    return (pyJ (fun _ => unitJ) r, d')
  | "init_toomany" =>
    let f ← (← arg op 1).getStr?
    let (r, d') := dd.init (.given (facOf f)) (.error (.typeError "dict expected at most 1 argument, got 2"))
    return (pyJ (fun _ => unitJ) r, d')
  | "set" => return (okJ unitJ, { dd with items := dictSet dd.items (← jInt (← arg op 1)) (← jInt (← arg op 2)) })
  | other => throw s!"unknown defdict op {other}"

/-- Keys of the `_count_elements` difftest: ints, and an unhashable object. -/
inductive CKey where
  | int (n : Int)
  | unhash
  deriving Repr, DecidableEq, Inhabited

/-- Values: ints, and a str (whose `+ 1` raises). -/
inductive CVal where
  | int (n : Int)
  | str
  deriving Repr, DecidableEq, Inhabited

def cHash : CKey → Py Unit
  | .int _ => .ok ()
  | .unhash => .error (.typeError "unhashable type: 'list'")

def cAdd : CVal → Py CVal
  | .int n => .ok (.int (n + 1))
  | .str => .error (.typeError "can only concatenate str (not \"int\") to str")

/-- `dict.get` reports an unhashable key differently from `_PyObject_HashFast`. -/
def cHashGet : CKey → Py Unit
  | .int _ => .ok ()
  | .unhash => .error (.typeError "cannot use 'list' as a dict key (unhashable type: 'list')")

def jCKey (j : Json) : Except String CKey :=
  match j with
  | .str _ => .ok .unhash
  | v => CKey.int <$> v.getInt?

def jCVal (j : Json) : Except String CVal :=
  match j with
  | .str _ => .ok .str
  | v => CVal.int <$> v.getInt?

def cItemsJ (d : PyDict CKey CVal) : Json :=
  toJson (d.map (fun kv =>
    Json.arr #[(match kv.1 with | .int n => toJson n | .unhash => toJson "U"),
               (match kv.2 with | .int n => toJson n | .str => toJson "S")]))

def jCItems (j : Json) : Except String (PyDict CKey CVal) := do
  let arr ← j.getArr?
  arr.toList.mapM (fun p => do
    let q ← p.getArr?
    let some a := q[0]? | throw "pair"
    let some b := q[1]? | throw "pair"
    return ((← jCKey a), (← jCVal b)))

def runCount (j : Json) : Except String Json := do
  let d ← jCItems (← field j "init")
  let ks ← (← (← field j "keys").getArr?).toList.mapM jCKey
  let raises ← getBool j "raises"
  let bad ← getBool j "bad"
  let src : PyIterable CKey := if bad then .notIterable "int"
    else .iter ks (if raises then some (.valueError "iter") else none)
  let (r, d') ←
    match ← getStr j "mapping" with
    | "dict" => pure (countDict cHash cAdd (.int 1) src d)
    | _ => pure (countMapping (dictMget cHashGet (.int 0)) dictMset (· == .int 0) cAdd (.int 1) src d)
  return okJ (Json.arr #[pyJ (fun _ => unitJ) r, cItemsJ d'])

def runTG (j : Json) : Except String Json := do
  match tuplegetterNew (← getInt j "index") (← getInt j "doc") with
  | .error e => return errJ e
  | .ok g =>
    let xs ← jInts (← field j "tuple")
    let g' : TupleGetter Int := g
    let r1 : Py (Option Int) := tuplegetterGet g' (.tuple xs)
    let r2 : Py (Option Int) := tuplegetterGet g' (.none)
    let r3 : Py (Option Int) := tuplegetterGet g' (.null)
    let r4 : Py (Option Int) := tuplegetterGet g' (.other "int")
    let enc : Option Int → Json := fun o => match o with | some x => toJson x | none => toJson "SELF"
    let (i, d) := tuplegetterReduce g'
    return okJ (Json.arr #[pyJ enc r1, pyJ enc r2, pyJ enc r3, pyJ enc r4,
      errJ (tuplegetterSet (some (0 : Int))), errJ (tuplegetterSet (none : Option Int)),
      Json.arr #[toJson i, toJson d], toJson (tuplegetterRepr g' toString)])

def runOps {σ : Type} (step : σ → Array Json → Except String (Json × σ)) (enc : σ → Json)
    (s : σ) (ops : List Json) : Except String Json := do
  let mut out : Array Json := #[]
  let mut s := s
  for op in ops do
    let (r, s') ← step s (← op.getArr?)
    s := s'
    out := out.push (Json.arr #[r, enc s])
  return okJ (Json.arr out)

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "count" => return ← runCount j
  | "tuplegetter" => return ← runTG j
  | "defdict" =>
    let dd : DefDict Int Int := ⟨dictUpdate [] (← jItems (← field j "init")), facOf (← getStr j "factory"), ← getStr j "tname"⟩
    let ops := (← (← field j "ops").getArr?).toList
    return ← runOps stepDD (fun d => Json.arr #[itemsJ d.items]) dd ops
  | "array_new" =>
    let c ← jVal (← field j "typecode")
    let tn ← getStr j "tname"
    let i ← jInit (← field j "init")
    return pyJ arrJ (arrCtorCheck c >>= (fun ch => arrNew tn ch i))
  | "reconstruct" =>
    let tc ← jVal (← field j "typecode")
    let tn ← getStr j "tname"
    let m ← getInt j "mformat"
    let items ← jNats (← field j "items")
    let r := reconstructArg tc >>= (fun s => reconstruct tn s m items)
    return pyJ (fun a => Json.arr #[toJson a.tc.code, natsJ (arrToBytes a)]) r
  | _ => pure ()
  let ops := (← (← field j "ops").getArr?).toList
  match fn with
  | "list" => runOps stepList toJson (← jInts (← field j "init")) ops
  | "array" =>
    let tc ← jTC (← field j "tc")
    match arrNew (← getStr j "tname") tc.code (.list (← jVals (← field j "init"))) with
    | .ok a => runOps stepArr (fun s => arrJ s.a) ⟨a, #[]⟩ ops
    | .error e => return errJ e
  | "deque" =>
    let t := (← getStr j "tname")
    let ml := (j.getObjVal? "maxlen").toOption.getD .null
    match Deque.makeOf t (← jElems (← field j "init")) (← jMaxlen #[ml] 0) with
    | .ok d => runOps stepDeque (fun s => Json.arr #[toJson (s.d.items.map DElem.toJ), toJson s.d.blocks]) ⟨d, #[]⟩ ops
    | .error e => return errJ e
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Sequences
