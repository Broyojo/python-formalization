import PyLean.DiffCore
import PyLean.Sequences.ArrayReModel
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

/-- `PyObject_RichCompareBool(a, b, op)` for the elements, on the deque `M<k>` acts on: for
`==` the `__eq__` again (identity first), for `!=` the inverted `__eq__` (`object.__ne__`),
for an ordering two ints compare and anything else raises `TypeError`. -/
def dRichRe (op : CmpOp) : Cmp DElem := fun d a b =>
  match op with
  | .eq => dCmp d a b
  | .ne =>
    if a = b then (.ok false, d)
    else
      match dCmp d a b with
      | (.ok c, d) => (.ok !c, d)
      | (.error e, d) => (.error e, d)
  | _ =>
    match a, b with
    | .int x, .int y => (.ok (opHolds op (compare x y)), d)
    | _, _ => (.error (.typeError "~not supported"), d)

/-- The object `d += ...` returns: the deque itself or `None`. -/
def slotJ : SlotRef → Json
  | .self => toJson "SELF"
  | .none => Json.null

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

/-- What a re-entrant iterator of the difftest does to the deque under test before
yielding (or instead of yielding): nothing, `d.append(0)`, `d.clear()`,
`d.__init__(maxlen=m)`, `d.pop()`, raise `ValueError('it')`, raise `StopIteration`. -/
inductive ReAct where
  | nop | app | clr | init (m : MaxlenArg) | pop | raise | stop

def ReAct.run (a : ReAct) (d : Deque DElem) : Py Unit × Deque DElem :=
  match a with
  | .nop => (.ok (), d)
  | .app => (.ok (), d.append (.int 0))
  | .clr => (.ok (), d.clear)
  | .init m => d.initRe none m
  | .pop =>
    match d.pop with
    | .ok (_, d') => (.ok (), d')
    | .error e => (.error e, d)
  | .raise => (.error (.valueError "it"), d)
  | .stop => (.error .stopIteration, d)

def jReAct (a : Array Json) : Except String ReAct := do
  match ← (← arg a 0).getStr? with
  | "n" | "y" => pure .nop
  | "a" => pure .app
  | "c" => pure .clr
  | "i" => pure (.init (← jMaxlen a 1))
  | "p" => pure .pop
  | "r" => pure .raise
  | "s" => pure .stop
  | k => throw s!"react {k}"

/-- A step `[act, ..., x]`: act, then yield `x` (the last entry); `["r"]` and `["s"]`
raise. For `"i"` the entry before `x` is the `maxlen` (`null`: none). -/
def jReStep (j : Json) : Except String (NextFn DElem) := do
  let a ← j.getArr?
  let act ← jReAct a
  let x ← if a.size ≥ 2 then jElem a[a.size - 1]! else pure (DElem.int 0)
  return fun d =>
    match act.run d with
    | (.error e, d) => (.error e, d)
    | (.ok (), d) => (.ok x, d)

/-- `[pre, steps]`: `__iter__` runs `pre` (and raises if it raises), then the steps. -/
def jReIter (pre steps : Json) : Except String (ReIter DElem) := do
  let act ← jReAct (← pre.getArr?)
  let nexts ← (← steps.getArr?).toList.mapM jReStep
  return ⟨act.run, nexts⟩

/-- The right operand of `d + other` in the difftest. -/
def jConcatArg (op : Array Json) : Except String (Deque.ConcatArg DElem) := do
  match ← (← arg op 1).getStr? with
  | "fake" =>
    let xs ← jElems (← arg op 2)
    let e : Option PyExc := if op.size > 3 then some (.valueError "it") else none
    pure (.inst (.iter xs e))
  | "fake_noiter" => pure (.inst (.notIterable "F2"))
  | "cls_raise" => pure (.raises (.valueError "cls"))
  | "cls_attr" => pure (.notInst "H")
  | k => throw s!"concat arg {k}"

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
  | "iadd" => return pair (d.iadd (.iter (← jElems (← arg op 1)) none)) slotJ
  | "extend_raise" => return pair (d.extendIter (.iter (← jElems (← arg op 1)) (some (.valueError "iter")))) (fun _ => unitJ)
  | "extendleft_raise" => return pair (d.extendleftIter (.iter (← jElems (← arg op 1)) (some (.valueError "iter")))) (fun _ => unitJ)
  | "extend_stop" => return pair (d.extendIter (.iter (← jElems (← arg op 1)) (some .stopIteration))) (fun _ => unitJ)
  | "extend_bad" => return pair (d.extendIter (.notIterable "int")) (fun _ => unitJ)
  | "extendleft_bad" => return pair (d.extendleftIter (.notIterable "int")) (fun _ => unitJ)
  | "iadd_bad" => return pair (d.iadd (.notIterable "int")) slotJ
  | "extend_re" => return pair (d.extendRe (← jReIter (← arg op 1) (← arg op 2))) (fun _ => unitJ)
  | "extendleft_re" => return pair (d.extendleftRe (← jReIter (← arg op 1) (← arg op 2))) (fun _ => unitJ)
  | "iadd_re" => return pair (d.iaddRe (← jReIter (← arg op 1) (← arg op 2))) slotJ
  | "init_re" => return pair (d.initRe (some (← jReIter (← arg op 1) (← arg op 2))) (← jMaxlen op 3)) (fun _ => unitJ)
  | "init_noarg" => return pair (d.initRe none (← jMaxlen op 1)) (fun _ => unitJ)
  | "add_odd" => return same (pyJ dequeJ (d.concat (← jConcatArg op)))
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
    return same (pyJ dequeJ (d.concat (.ofDeque other)))
  | "add_self" => return same (pyJ dequeJ (d.concat (.ofDeque d)))
  | "add_bad" => return same (pyJ dequeJ (d.concat (.notInst "list")))
  | "clear" => return (okJ unitJ, { s with d := d.clear })
  | "init" => return pair (d.init (.iter (← jElems (← arg op 1)) none) (← jMaxlen op 2)) (fun _ => unitJ)
  | "init_self" => return pair (d.init (.iter [] none) (← jMaxlen op 1)) (fun _ => unitJ)
  | "len" => return same (okJ (toJson d.len))
  | "maxlen" => return same (okJ (match d.getMaxlen with | none => Json.null | some m => toJson m))
  | "repr" => return same (pyJ toJson (d.repr DElem.repr false))
  | "repr_nested" =>
    -- `c = d.copy(); c.append(c); repr(c)`: a deque holding itself as the last item
    let inner ← match d.repr DElem.repr true with
      | .ok v => pure v
      | .error _ => throw "repr"
    let r : DElem → Py String := fun e => if e = .mut 99 then .ok inner else e.repr
    match d.copy with
    | .ok c => return same (pyJ toJson ((c.append (.mut 99)).repr r false))
    | .error e => return same (errJ e)
  | "reduce" =>
    match d.reduceRe (.ok ()) with
    | .ok (_, m, _, it) =>
      -- the harness drains the returned iterator over the unchanged deque
      let xs ← match d.drain Deque.iterNext (d.items.length + 1) it with
        | .ok xs => pure (xs.map DElem.toJ)
        | .error _ => throw "reduce: iterator"
      return same (okJ (Json.arr #[(match m with | none => Json.null | some v => toJson v), toJson xs]))
    | .error e => return same (errJ e)
  | "reduce_raise" =>
    return same (pyJ (fun _ => Json.null) (d.reduceRe (σ := Unit) (.error (.valueError "gs"))))
  | "cmp" | "cmp_rev" =>
    let o ← jOp (← arg op 1)
    let other ← match Deque.make (← jElems (← arg op 2)) .absent with
      | .ok o => pure o
      | .error _ => throw "cmp: bad other deque"
    if name == "cmp" then
      -- `d OP other`: the `M` elements' `__eq__` acts on `d`, the left operand
      let lift : Cmp DElem → Deque.RCmp (Deque DElem × Deque DElem) DElem := fun c s a b =>
        let (r, d') := c s.1 a b
        (r, (d', s.2))
      let (r, s') := Deque.richcompareRe Prod.fst Prod.snd (lift dCmp) (lift (dRichRe o)) o false (d, other)
      return (pyJ toJson r, { s with d := s'.1 })
    else
      -- `other OP d`: `d` is the right operand
      let lift : Cmp DElem → Deque.RCmp (Deque DElem × Deque DElem) DElem := fun c s a b =>
        let (r, d') := c s.2 a b
        (r, (s.1, d'))
      let (r, s') := Deque.richcompareRe Prod.fst Prod.snd (lift dCmp) (lift (dRichRe o)) o false (other, d)
      return (pyJ toJson r, { s with d := s'.2 })
  | "cmp_self" =>
    let o ← jOp (← arg op 1)
    let (r, d') := Deque.richcompareRe id id dCmp (dRichRe o) o true d
    return (pyJ toJson r, { s with d := d' })
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
  | "it_kw" =>
    let rev ← (← arg op 1).getBool?
    let idx ← match ← arg op 2 with
      | .null => pure none
      | j => some <$> jInt j
    match (if rev then d.reviterNewArgs else d.iterNewArgs) idx ["index"] with
    | .ok it => return ((okJ unitJ), { s with its := s.its.push (it, rev) })
    | .error e => return (errJ e, s)
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
  | .user t _ _ _ _ => Json.mkObj [("o", toJson t)]

/-- The exception a `DeprecationWarning` turned into an error raises; its message embeds
`%T` names, so only the class is compared. -/
def warnErr (w : Bool) : Option PyExc :=
  if w then some (.named "DeprecationWarning" "~deprecated subclass result") else none

/-- A user method's result: `{"f": bits}`, `{"fs": [cls, bits, warn]}`, `{"i": n}`,
`{"is": [cls, n, warn]}`, `{"c": [re, im]}`, `{"cs": [cls, re, im, warn]}`, `{"o": cls}` or
`{"r": msg}` (raises `ValueError(msg)`). -/
def jRet (j : Json) : Except String Ret := do
  let at_ (a : Array Json) (k : Nat) : Except String Json :=
    match a[k]? with | some v => .ok v | none => .error "ret"
  match j.getObjVal? "f", j.getObjVal? "fs", j.getObjVal? "i", j.getObjVal? "is" with
  | .ok b, _, _, _ => return .float (← b.getNat?)
  | _, .ok a, _, _ =>
    let a ← a.getArr?
    return .floatSub (← (← at_ a 0).getStr?) (← (← at_ a 1).getNat?) (warnErr (← (← at_ a 2).getBool?))
  | _, _, .ok n, _ => return .int (← n.getInt?)
  | _, _, _, .ok a =>
    let a ← a.getArr?
    return .intSub (← (← at_ a 0).getStr?) (← (← at_ a 1).getInt?) (warnErr (← (← at_ a 2).getBool?))
  | _, _, _, _ =>
    match j.getObjVal? "c", j.getObjVal? "cs", j.getObjVal? "o", j.getObjVal? "r" with
    | .ok c, _, _, _ =>
      let a ← c.getArr?
      return .complex (← (← at_ a 0).getNat?) (← (← at_ a 1).getNat?)
    | _, .ok a, _, _ =>
      let a ← a.getArr?
      return .complexSub (← (← at_ a 0).getStr?) (← (← at_ a 1).getNat?) (← (← at_ a 2).getNat?)
        (warnErr (← (← at_ a 3).getBool?))
    | _, _, .ok o, _ => return .other (← o.getStr?)
    | _, _, _, .ok m => return .raises (.valueError (← m.getStr?))
    | _, _, _, _ => throw "ret"

def jOptRet (j : Option Json) : Except String (Option Ret) :=
  match j with
  | none | some .null => .ok none
  | some r => some <$> jRet r

def jBase (j : Json) : Except String UBase :=
  match j with
  | .null => .ok .plain
  | j =>
    match j.getObjVal? "f", j.getObjVal? "c", j.getObjVal? "i" with
    | .ok b, _, _ => UBase.float <$> b.getNat?
    | _, .ok c, _ => do
      let a ← c.getArr?
      let some re := a[0]? | throw "base"
      let some im := a[1]? | throw "base"
      return .complex (← re.getNat?) (← im.getNat?)
    | _, _, .ok n => UBase.int <$> n.getInt?
    | _, _, _ => .error "base"

def jPlainObj (j : Json) : Except String PyVal :=
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

def jVal (j : Json) : Except String PyVal :=
  match j with
  | .obj _ =>
    match j.getObjVal? "u" with
    | .ok u => do
      return .user (← u.getStr?) (← jBase ((j.getObjVal? "b").toOption.getD .null))
        (← jOptRet (j.getObjVal? "fl").toOption) (← jOptRet (j.getObjVal? "ix").toOption)
        (← jOptRet (j.getObjVal? "cx").toOption)
    | .error _ => jPlainObj j
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

/-- What the scripted `read` of the difftest does to the array before it returns (`k`):
nothing, append a zero item (`a.frombytes(bytes(a.itemsize))`), clear it, or open a
`memoryview` of it that stays open. A failure is raised from `read`. -/
def readMut (k : Nat) (a : Arr) : Option PyExc × Arr :=
  match k with
  | 1 =>
    match arrFromBytes a (List.replicate a.tc.itemsize.toNat 0) 1 with
    | .ok a' => (none, a')
    | .error e => (some e, a)
  | 2 =>
    match arrClear a with
    | .ok a' => (none, a')
    | .error e => (some e, a)
  | 3 => (none, { a with exports := a.exports + 1 })
  | _ => (none, a)

/-- What the scripted `__release_buffer__` of the difftest does (`k`): 7 clears the array
(`del a[:]`), 8 appends a zero item, 9 raises `ValueError`, which is only reported. A failure
of the change itself is reported the same way. -/
def relMut (k : Nat) (a : Arr) : Arr :=
  match k with
  | 7 =>
    match arrClear a with
    | .ok a' => a'
    | .error _ => a
  | 8 =>
    match arrFromBytes a (List.replicate a.tc.itemsize.toNat 0) 1 with
    | .ok a' => a'
    | .error _ => a
  | _ => a

/-- `io.BytesIO(bs).read(n)` (`n >= 0`) after `readMut k`. For `k` = 4, 5, 6 the data comes
back as an instance of a `bytes` subclass whose `__buffer__` returns `memoryview(b'')`,
`memoryview(bytes(4)).cast('I')` (item size 4), or raises `ValueError("buf")`; for `k` = 7, 8, 9
as one with the `__release_buffer__` of `relMut k`. -/
def scriptRead (bs : List Nat) (k : Nat) : ReadFn := fun n a =>
  let d := bs.take n.toNat
  match k with
  | 4 => (.bytesSub d.length ⟨fun a => (.ok ([], 1), a), id⟩, a)
  | 5 => (.bytesSub d.length ⟨fun a => (.ok ([0, 0, 0, 0], 4), a), id⟩, a)
  | 6 => (.bytesSub d.length ⟨fun a => (.error (.valueError "buf"), a), id⟩, a)
  | 7 | 8 | 9 => (.bytesSub d.length ⟨fun a => (.ok (d, 1), a), relMut k⟩, a)
  | k =>
    match readMut k a with
    | (some e, a) => (.raises e, a)
    | (none, a) => (.bytes d, a)

/-- The scripted `write` of the difftest: mode 1 raises `ValueError("write")` at call `k`,
mode 2 appends a zero item at each call (the array only grows, so every block stays inside
it), anything else just records. -/
def scriptWrite (mode k : Nat) : WriteFn := fun i _ a =>
  match mode with
  | 1 => if i = k then (.error (.valueError "write"), a) else (.ok (), a)
  | 2 =>
    match arrFromBytes a (List.replicate a.tc.itemsize.toNat 0) 1 with
    | .ok a' => (.ok (), a')
    | .error e => (.error e, a)
  | _ => (.ok (), a)

/-- An array of the typecode of `tcj` holding the C values of `vs`. -/
def arrOf (tc : TC) (vs : List PyVal) : Except String Arr :=
  match arrNew "array" tc.code (.list vs) with
  | .ok a => .ok a
  | .error _ => .error "bad array operand"

def reducedJ : Reduced → Json
  | .asList t c vs => Json.arr #[toJson t, toJson c, toJson (vs.map PyVal.toJ)]
  | .asBytes t c m b => Json.arr #[toJson t, toJson c, toJson m, natsJ b]

/-- A value whose conversion raised `e`: every conversion method raises it. -/
def raisingVal (e : PyExc) : PyVal := .user "M" .plain (some (.raises e)) (some (.raises e)) (some (.raises e))

/-- What the first conversion call of a difftest `M` object does to the array (`k`): 1 clears
it, 2 appends one zero item (`a.frombytes(bytes(a.itemsize))`), 3 appends twenty, 4 opens a
`memoryview` of it that stays open. A failure raises out of the conversion method. -/
def mutArr (k : Nat) (a : Arr) (inner : PyVal) : Arr × PyVal :=
  let res : Py Arr :=
    match k with
    | 1 => arrClear a
    | 2 => arrFromBytes a (List.replicate a.tc.itemsize.toNat 0) 1
    | 3 => arrFromBytes a (List.replicate (20 * a.tc.itemsize.toNat) 0) 1
    | 4 => .ok { a with exports := a.exports + 1 }
    | _ => .ok a
  match res with
  | .ok a' => (a', inner)
  | .error e => (a, raisingVal e)

/-- `{"m": k, "v": inner}`: an item whose first conversion call runs `mutArr k`; anything else
is a plain value. -/
def jReVal (j : Json) : Except String ReVal :=
  match j.getObjVal? "m" with
  | .ok m => do
    let k ← m.getNat?
    let inner ← jVal (← field j "v")
    return fun c a => if c = 0 then mutArr k a inner else (a, inner)
  | .error _ => ReVal.pure <$> jVal j

/-- A `fromlist` item: plain, or an `M` object; `k = 5` appends `0` to the list being read. -/
def FItem := PyVal ⊕ (Nat × PyVal)

def fConv (x : FItem) (s : Arr × List FItem) : (Arr × List FItem) × PyVal :=
  match x with
  | .inl v => (s, v)
  | .inr (5, inner) => ((s.1, s.2 ++ [.inl (.int 0)]), inner)
  | .inr (k, inner) =>
    let (a', pv) := mutArr k s.1 inner
    ((a', s.2), pv)

def jFItem (j : Json) : Except String FItem :=
  match j.getObjVal? "m" with
  | .ok m => do return .inr (← m.getNat?, ← jVal (← field j "v"))
  | .error _ => Sum.inl <$> jVal j

/-- What call `k` of the difftest's `EqScript.__eq__` does to the array (`act`): 1 clears it, 2
appends a zero item (`a.frombytes(bytes(a.itemsize))`), 3 deletes the last item, 4 the first
(`del a[-1]`, `del a[0]`, when there is one). A failure raises out of `__eq__`. -/
def eqAct (act : Nat) (a : Arr) : Py Arr :=
  match act with
  | 1 => arrClear a
  | 2 => arrFromBytes a (List.replicate a.tc.itemsize.toNat 0) 1
  | 3 => if a.items.length > 0 then arrAssIndex a (-1) none else .ok a
  | 4 => if a.items.length > 0 then arrAssIndex a 0 none else .ok a
  | _ => .ok a

/-- The comparison of the difftest's `EqScript`: call `i` (the loops start at 0) runs
`eqAct` and returns False (0), True (1) or raises `ValueError("eq")` (2); past the script it
returns False. -/
def scriptCmp (sc : List (Nat × Nat)) : ReCmp := fun i a _ =>
  match sc[i.toNat]? with
  | none => (a, .ok false)
  | some (act, res) =>
    match eqAct act a with
    | .error e => (a, .error e)
    | .ok a' => (a', match res with
        | 1 => .ok true
        | 2 => .error (.valueError "eq")
        | _ => .ok false)

def jScript (j : Json) : Except String (List (Nat × Nat)) := do
  let arr ← j.getArr?
  arr.toList.mapM fun e => do
    let p ← e.getArr?
    let some x := p[0]? | throw "script"
    let some y := p[1]? | throw "script"
    return (← x.getNat?, ← y.getNat?)

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
  | "index" =>
    let (a', r) := arrIndexRe (ReCmp.pure (eqOf (← jVal (← arg op 1)))) a (← optArg op 2) (← optArg op 3)
    return (pyJ toJson r, { s with a := a' })
  | "count" =>
    let (a', r) := arrCountRe (ReCmp.pure (eqOf (← jVal (← arg op 1)))) a
    return (pyJ toJson r, { s with a := a' })
  | "contains" =>
    let (a', r) := arrContainsRe (ReCmp.pure (eqOf (← jVal (← arg op 1)))) a
    return (pyJ toJson r, { s with a := a' })
  | "remove" =>
    let (a', r) := arrRemoveRe (ReCmp.pure (eqOf (← jVal (← arg op 1)))) a
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "index_eq" =>
    let (a', r) := arrIndexRe (scriptCmp (← jScript (← arg op 1))) a none none
    return (pyJ toJson r, { s with a := a' })
  | "count_eq" =>
    let (a', r) := arrCountRe (scriptCmp (← jScript (← arg op 1))) a
    return (pyJ toJson r, { s with a := a' })
  | "contains_eq" =>
    let (a', r) := arrContainsRe (scriptCmp (← jScript (← arg op 1))) a
    return (pyJ toJson r, { s with a := a' })
  | "remove_eq" =>
    let (a', r) := arrRemoveRe (scriptCmp (← jScript (← arg op 1))) a
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
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
  | "getitem_bad" =>
    return same (pyJ (fun r => match r with | .inl v => v.toJ | .inr b => arrJ b) (arrSubscr a .other))
  | "append_m" => return optE (arrAppendRe a (← jReVal (← arg op 1)))
  | "insert_m" => return optE (arrInsertRe a (← jInt (← arg op 1)) (← jReVal (← arg op 2)))
  | "setitem_m" =>
    let (a', r) := arrAssIndexRe a (← jInt (← arg op 1)) (← jReVal (← arg op 2))
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "extend_m" =>
    let vs ← (← (← arg op 1).getArr?).toList.mapM jReVal
    return optE (arrIterExtendRe a (.iter vs none))
  | "fromlist_m" =>
    let xs ← (← (← arg op 1).getArr?).toList.mapM jFItem
    let (r, a') := arrFromListRe fConv a (.inl xs)
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "fromlist_bad" =>
    let (r, a') := arrFromList a (.inr "tuple")
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "tolist" => return same (pyJ (fun vs => toJson (vs.map PyVal.toJ)) (arrToList a))
  | "frombytes" => return keep (arrFromBytes a (← jNats (← arg op 1)) 1) (fun _ => unitJ) id
  | "frombytes_rel" =>
    let bs ← jNats (← arg op 1)
    let k ← (← arg op 2).getNat?
    let (r, a') := arrFromBytesCall a ⟨fun a => (.ok (bs, 1), a), relMut k⟩
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "frombytes_wide" => return keep (arrFromBytes a (← jNats (← arg op 1)) 2) (fun _ => unitJ) id
  | "tobytes" => return same (okJ (natsJ (arrToBytes a)))
  | "fromfile" =>
    let bs ← jNats (← arg op 1)
    let (r, a', _) := arrFromFile a (scriptRead bs 0) (← jVal (← arg op 2))
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "fromfile_mut" =>
    let bs ← jNats (← arg op 1)
    let (r, a', _) := arrFromFile a (scriptRead bs (← (← arg op 3).getNat?)) (← jVal (← arg op 2))
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "fromfile_notbytes" =>
    let (r, a', _) := arrFromFile a (fun _ a => (.notBytes, a)) (← jVal (← arg op 1))
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "fromfile_raise" =>
    let (r, a', _) := arrFromFile a (fun _ a => (.raises (.valueError "read"), a)) (← jVal (← arg op 1))
    return (pyJ (fun _ => unitJ) r, { s with a := a' })
  | "tofile" =>
    let (r, a', out) := arrToFile a (scriptWrite (← (← arg op 1).getNat?) (← (← arg op 2).getNat?))
    return (okJ (Json.arr #[pyJ (fun _ => unitJ) r, toJson (out.map natsJ)]), { s with a := a' })
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
  | "repr" => return same (pyJ toJson (arrRepr a))
  | "mv_open" =>
    let ((f, i, n, b), a') := arrGetBuf a
    return (okJ (Json.arr #[toJson f, toJson i, toJson n, toJson b]), { s with a := a' })
  | "mv_close" => return (okJ unitJ, { s with a := arrRelBuf a })
  | "cmp" =>
    let o ← jOp (← arg op 1)
    let other ← arrOf (← jTC (← arg op 2)) (← jVals (← arg op 3))
    return same (pyJ toJson (arrRich o a other))
  | "cmp_bad" =>
    let o ← jOp (← arg op 1)
    return same (pyJ (fun r => match r with | some b => toJson b | none => toJson "NotImplemented")
      (arrRichcompare o (.inl a) (.inr "list")))
  | "it_new" => return (okJ unitJ, { s with its := s.its.push arrIter })
  | "it_next" =>
    let k ← (← arg op 1).getNat?
    let (r, it') := arrIterNext a (← its k)
    return (pyJ (fun o => match o with | some x => x.toJ | none => toJson "STOP") r,
      { s with its := s.its.set! k it' })
  | "it_reduce" =>
    let it ← its (← (← arg op 1).getNat?)
    return same (okJ (match arrIterReduce a it with
      | .live f arr i => Json.arr #[toJson "live", toJson (f == "iter"), toJson (decide (arr = a)), toJson i]
      | .exhausted f => Json.arr #[toJson "exhausted", toJson (f == "iter"), toJson true]))
  | "it_roundtrip" =>
    let it ← its (← (← arg op 1).getNat?)
    match arrIterReduce a it with
    | .exhausted _ => return same (okJ (Json.arr #[]))
    | .live _ _ i =>
      match arrIterSetstate a arrIter (.int i) with
      | .error e => return same (errJ e)
      | .ok it2 => return same (okJ (Json.arr ((arrDrain a (a.items.length + 1) it2).map
          (fun r => pyJ (·.toJ) r)).toArray))
  | "it_setstate" =>
    let k ← (← arg op 1).getNat?
    match arrIterSetstate a (← its k) (← jVal (← arg op 2)) with
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
  | "F1" => .call (.ok "F1") (fun d => (.error (.valueError "fac"), d))
  | "F2" => .call (.ok "F2") (fun d => (.ok 1, dictSet d 100 7))
  | "F3" => .call (.ok "F3") (fun d => (.ok 1, dictSet d 1 5))
  | "FR" => .call (.error (.valueError "frepr")) (fun d => (.ok 0, d))
  | _ => .call (.ok "F0") (fun d => (.ok 0, d))

def itemsJ (d : PyDict Int Int) : Json := toJson (d.map (fun kv => [kv.1, kv.2]))

def jItems (j : Json) : Except String (PyDict Int Int) := do
  let arr ← j.getArr?
  arr.toList.mapM (fun p => do
    let q ← p.getArr?
    let some a := q[0]? | throw "pair"
    let some b := q[1]? | throw "pair"
    return ((← a.getInt?), (← b.getInt?)))

def baseRepr (d : PyDict Int Int) : Py String :=
  .ok ("{" ++ ", ".intercalate (d.map (fun kv => s!"{kv.1}: {kv.2}")) ++ "}")

/-- The repr of a factory as an argument of `__reduce__`. -/
def facJ : Factory Int Int → Json
  | .null | .none => toJson "None"
  | .call r _ => match r with | .ok s => toJson s | .error _ => toJson "<repr raises>"

def redJ : DefDict.RedItem Int Int → Json
  | .type t => toJson t
  | .args fs => Json.arr (fs.map facJ).toArray
  | .none => Json.null
  | .iter xs _ => itemsJ xs

def stepDD (dd : DefDict Int Int) (op : Array Json) : Except String (Json × DefDict Int Int) := do
  let name ← (← arg op 0).getStr?
  let pair (r : Py Int × DefDict Int Int) : Json × DefDict Int Int := (pyJ toJson r.1, r.2)
  let dj (x : DefDict Int Int) : Py Json := do
    let r ← DefDict.repr x baseRepr (.ok false)
    return Json.arr #[toJson x.tname, itemsJ x.items, toJson r]
  let djr (r : Option (DefDict Int Int)) : Json :=
    match r with | some x => pyJ id (dj x) | none => okJ (toJson "NI")
  match name with
  | "getitem" => return pair (dd.getitem toString (← jInt (← arg op 1)))
  | "missing" => return pair (dd.missing toString (← jInt (← arg op 1)))
  | "copy" => return (pyJ id (dj dd.copy), dd)
  | "reduce" => return (pyJ (fun l => Json.arr (l.map redJ).toArray) (dd.reduce (.ok (.iter dd.items none))), dd)
  | "reduce_raise" =>
    return (pyJ (fun l => Json.arr (l.map redJ).toArray)
      ({ dd with tname := "DDI" }.reduce (.error (.valueError "items"))), dd)
  | "reduce_bad" =>
    return (pyJ (fun l => Json.arr (l.map redJ).toArray)
      ({ dd with tname := "DDJ" }.reduce (.ok (.notIterable "int"))), dd)
  | "repr" => return (pyJ toJson (dd.repr baseRepr (.ok false)), dd)
  | "repr_base_raise" =>
    return (pyJ toJson (dd.repr (fun _ => .error (.valueError "vrepr")) (.ok false)), dd)
  | "repr_nested" =>
    let inner := ({ dd with factory := facOf "F0" }).repr baseRepr (.ok true)
    let outer := ({ dd with factory := .call inner (fun d => (.ok 0, d)) }).repr baseRepr (.ok false)
    return (pyJ toJson outer, dd)
  | "or_dict" =>
    let r := DefDict.orOp (.dd dd) (.plain (dictUpdate [] (← jItems (← arg op 1))))
    return (djr r, dd)
  | "ror_dict" =>
    let r := DefDict.orOp (.plain (dictUpdate [] (← jItems (← arg op 1)))) (.dd dd)
    return (djr r, dd)
  | "or_dd" =>
    let o : DefDict Int Int := ⟨dictUpdate [] (← jItems (← arg op 1)), facOf (← (← arg op 2).getStr?), "defaultdict"⟩
    let r := DefDict.orOp (.dd dd) (.dd o)
    return (djr r, dd)
  | "or_frozen" =>
    let r := DefDict.orOp (.dd dd) (.frozen (dictUpdate [] (← jItems (← arg op 1))))
    return (djr r, dd)
  | "ror_frozen" =>
    let r := DefDict.orOp (.frozen (dictUpdate [] (← jItems (← arg op 1)))) (.dd dd)
    return (djr r, dd)
  | "or_bad" =>
    let r := DefDict.orOp (.dd dd) .notDict
    return (djr r, dd)
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

/-- Values: ints, a str (whose `+ 1` raises), and an object whose `__add__` clears the
mapping and returns 99. -/
inductive CVal where
  | int (n : Int)
  | str
  | clr
  deriving Repr, DecidableEq, Inhabited

def cHash : CKey → Py Unit
  | .int _ => .ok ()
  | .unhash => .error (.typeError "unhashable type: 'list'")

def cAdd (d : PyDict CKey CVal) : CVal → Py CVal × PyDict CKey CVal
  | .int n => (.ok (.int (n + 1)), d)
  | .str => (.error (.typeError "can only concatenate str (not \"int\") to str"), d)
  | .clr => (.ok (.int 99), [])

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
  | .str "C" => .ok .clr
  | .str _ => .ok .str
  | v => CVal.int <$> v.getInt?

def cItemsJ (d : PyDict CKey CVal) : Json :=
  toJson (d.map (fun kv =>
    Json.arr #[(match kv.1 with | .int n => toJson n | .unhash => toJson "U"),
               (match kv.2 with | .int n => toJson n | .str => toJson "S" | .clr => toJson "C")]))

def jCItems (j : Json) : Except String (PyDict CKey CVal) := do
  let arr ← j.getArr?
  arr.toList.mapM (fun p => do
    let q ← p.getArr?
    let some a := q[0]? | throw "pair"
    let some b := q[1]? | throw "pair"
    return ((← jCKey a), (← jCVal b)))

/-- A key of the iterator: `"X"` clears the mapping, then yields 0. -/
def jCNext (j : Json) : Except String (KeyNext CKey (PyDict CKey CVal)) :=
  match j with
  | .str "X" => .ok (fun _ => (.ok (.int 0), []))
  | v => do let k ← jCKey v; pure (fun d => (.ok k, d))

def runCount (j : Json) : Except String Json := do
  let d ← jCItems (← field j "init")
  let ks ← (← (← field j "keys").getArr?).toList.mapM jCNext
  let raises ← getBool j "raises"
  let bad ← getBool j "bad"
  let src : KeySrc CKey (PyDict CKey CVal) := if bad then .notIterable "int"
    else .iter (ks ++ (if raises then [fun d => (.error (.valueError "iter"), d)] else []))
  let (r, d') ←
    match ← getStr j "mapping" with
    | "dict" => pure (countDict cHash cAdd (.int 1) src d)
    | _ => pure (countMapping (.ok ()) (dictMget cHashGet (.int 0)) dictMset (· == .int 0) cAdd (.int 1) src d)
  return okJ (Json.arr #[pyJ (fun _ => unitJ) r, cItemsJ d'])

def runTG (j : Json) : Except String Json := do
  let doc : Option Int ← match ← field j "doc" with
    | .str _ => pure none
    | v => some <$> v.getInt?
  match tuplegetterNew (← getInt j "index") doc with
  | .error e => return errJ e
  | .ok g =>
    let xs ← jInts (← field j "tuple")
    let g' : TupleGetter (Option Int) := g
    let docJ : Option Int → Json := fun o => match o with | some v => toJson v | none => toJson "R"
    let docRepr : Option Int → Py String := fun o => match o with
      | some v => .ok (toString v)
      | none => .error (.valueError "vrepr")
    let r1 : Py (Option Int) := tuplegetterGet g' (.tuple xs)
    let r2 : Py (Option Int) := tuplegetterGet g' (.none)
    let r3 : Py (Option Int) := tuplegetterGet g' (.null)
    let r4 : Py (Option Int) := tuplegetterGet g' (.other "int")
    let enc : Option Int → Json := fun o => match o with | some x => toJson x | none => toJson "SELF"
    let (i, d) := tuplegetterReduce g'
    return okJ (Json.arr #[pyJ enc r1, pyJ enc r2, pyJ enc r3, pyJ enc r4,
      errJ (tuplegetterSet (some (0 : Int))), errJ (tuplegetterSet (none : Option Int)),
      Json.arr #[toJson i, docJ d], pyJ toJson (tuplegetterRepr g' docRepr)])

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
  | "array_tofile" =>
    -- an array of `n` items holding the bytes `(7k + 3) % 256`, written with `scriptWrite`
    let tc ← jTC (← field j "tc")
    let n ← getInt j "n"
    let bs := (List.range (n.toNat * tc.itemsize.toNat)).map (fun k => (k * 7 + 3) % 256)
    let blockSum (blk : List Nat) : Json :=
      Json.arr #[toJson blk.length,
        toJson ((blk.zipIdx.map (fun (b, i) => b * (i + 1))).foldl (· + ·) 0 % 1000000007)]
    match arrNew "array" tc.code .none with
    | .error e => return errJ e
    | .ok a0 =>
      match arrFromBytes a0 bs 1 with
      | .error e => return errJ e
      | .ok a =>
        let (r, a', out) := arrToFile a (scriptWrite (← getInt j "mode").toNat (← getInt j "k").toNat)
        return okJ (Json.arr #[pyJ (fun _ => unitJ) r, toJson (out.map blockSum), toJson a'.items.length])
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
    let noinit := (j.getObjVal? "noinit").toOption.isSome
    let made : Py (Deque DElem) ← if noinit then pure (Deque.makeEmpty t (← jMaxlen #[ml] 0))
      else pure (Deque.makeOf t (← jElems (← field j "init")) (← jMaxlen #[ml] 0))
    match made with
    | .ok d => runOps stepDeque (fun s => Json.arr #[toJson (s.d.items.map DElem.toJ), toJson s.d.blocks]) ⟨d, #[]⟩ ops
    | .error e => return errJ e
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Sequences
