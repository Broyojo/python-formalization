import PyLean.DiffCore
import PyLean.Sequences.ArrayModel
import PyLean.Sequences.DequeModel

/-! Differential-testing handler for `sequences` cases (`"mod": "sequences"`).

A case is `{"fn": "list" | "array" | "deque", "init": [...], "ops": [[name, args...], ...]}`
(plus `"tc"` for arrays and `"maxlen"` for deques). The result is
`{"ok": [[r, state], ...]}` with one entry per operation, where `r` is the
operation's `{"ok": v}`/`{"exc", "msg"}` and `state` the contents afterwards
(for deques, `[items, blocks]`); construction errors are returned directly.
A slice is `[start|null, stop|null, step|null]`. -/

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

/-- Run one op: `(result, new state)`; a raising op keeps the old state
unless the model says otherwise. -/
def stepList (l : List Int) (op : Array Json) : Except String (Json × List Int) := do
  let name ← (← arg op 0).getStr?
  let keep {α} (r : Py α) (enc : α → Json) (st : α → List Int) : Json × List Int :=
    match r with
    | .ok v => (okJ (enc v), st v)
    | .error e => (errJ e, l)
  match name with
  | "append" => return (okJ unitJ, listAppend l (← jInt (← arg op 1)))
  | "insert" => return keep (listInsert l (← jInt (← arg op 1)) (← jInt (← arg op 2))) (fun _ => unitJ) id
  | "pop" => return keep (listPop l (← optArg op 1)) (fun p => toJson p.1) (·.2)
  | "index" => return keep (listIndex l (← jInt (← arg op 1)) (← optArg op 2) (← optArg op 3)) toJson (fun _ => l)
  | "count" => return (okJ (toJson (listCount l (← jInt (← arg op 1)))), l)
  | "remove" => return keep (listRemove l (← jInt (← arg op 1))) (fun _ => unitJ) id
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

def tcOf (s : String) : Except String TC :=
  match s with
  | "b" => .ok .b | "B" => .ok .B | "h" => .ok .h | "i" => .ok .i | "q" => .ok .q
  | _ => .error s!"typecode {s}"

def stepArr (a : Arr) (op : Array Json) : Except String (Json × Arr) := do
  let name ← (← arg op 0).getStr?
  let keep {α} (r : Py α) (enc : α → Json) (st : α → Arr) : Json × Arr :=
    match r with
    | .ok v => (okJ (enc v), st v)
    | .error e => (errJ e, a)
  match name with
  | "append" => return keep (arrAppend a (← jInt (← arg op 1))) (fun _ => unitJ) id
  | "insert" => return keep (arrInsert a (← jInt (← arg op 1)) (← jInt (← arg op 2))) (fun _ => unitJ) id
  | "pop" => return keep (arrPop a (← optArg op 1)) (fun p => toJson p.1) (·.2)
  | "index" => return keep (arrIndex a (← jInt (← arg op 1)) (← optArg op 2) (← optArg op 3)) toJson (fun _ => a)
  | "count" => return (okJ (toJson (arrCount a (← jInt (← arg op 1)))), a)
  | "remove" => return keep (arrRemove a (← jInt (← arg op 1))) (fun _ => unitJ) id
  | "getitem" => return keep (arrGetItem a (← jInt (← arg op 1))) toJson (fun _ => a)
  | "setitem" => return keep (arrAssSubscr a (.inl (← jInt (← arg op 1))) (some [← jInt (← arg op 2)])) (fun _ => unitJ) id
  | "delitem" => return keep (arrAssSubscr a (.inl (← jInt (← arg op 1))) none) (fun _ => unitJ) id
  | "setslice" => return keep (arrAssSubscr a (.inr (← jSlice (← arg op 1))) (some (← jInts (← arg op 2)))) (fun _ => unitJ) id
  | "setslice_self" => return keep (arrAssSubscr a (.inr (← jSlice (← arg op 1))) (some a.items)) (fun _ => unitJ) id
  | "delslice" => return keep (arrAssSubscr a (.inr (← jSlice (← arg op 1))) none) (fun _ => unitJ) id
  | "imul" => return keep (arrIRepeat a (← jInt (← arg op 1))) (fun _ => unitJ) id
  | "mul" => return keep (arrRepeat a (← jInt (← arg op 1))) (fun b => toJson b.items) (fun _ => a)
  | "extend" =>
    let (a', e) := arrIterExtend a (← jInts (← arg op 1))
    return (match e with | none => okJ unitJ | some e => errJ e, a')
  | "extend_arr" => return (okJ unitJ, { a with items := a.items ++ (← jInts (← arg op 1)) })
  | other => throw s!"unknown array op {other}"

def dequeJ (d : Deque) : Json := Json.arr #[toJson d.items, toJson (if d.maxlen < 0 then Json.null else toJson d.maxlen), toJson d.blocks]

def stepDeque (d : Deque) (op : Array Json) : Except String (Json × Deque) := do
  let name ← (← arg op 0).getStr?
  let keep {α} (r : Py α) (enc : α → Json) (st : α → Deque) : Json × Deque :=
    match r with
    | .ok v => (okJ (enc v), st v)
    | .error e => (errJ e, d)
  match name with
  | "append" => return (okJ unitJ, d.append (← jInt (← arg op 1)))
  | "appendleft" => return (okJ unitJ, d.appendleft (← jInt (← arg op 1)))
  | "pop" => return keep d.pop (fun p => toJson p.1) (·.2)
  | "popleft" => return keep d.popleft (fun p => toJson p.1) (·.2)
  | "extend" => return (okJ unitJ, d.extend (← jInts (← arg op 1)))
  | "extendleft" => return (okJ unitJ, d.extendleft (← jInts (← arg op 1)))
  | "iadd" => return (okJ unitJ, d.extend (← jInts (← arg op 1)))
  | "extend_self" | "iadd_self" => return (okJ unitJ, d.extendSelf)
  | "extendleft_self" => return (okJ unitJ, d.extendleftSelf)
  | "rotate" => return keep (d.rotate ((← optArg op 1).getD 1)) (fun _ => unitJ) id
  | "index" => return keep (d.index (← jInt (← arg op 1)) (← optArg op 2) (← optArg op 3)) toJson (fun _ => d)
  | "insert" => return keep (d.insert (← jInt (← arg op 1)) (← jInt (← arg op 2))) (fun _ => unitJ) id
  | "remove" => return keep (d.remove (← jInt (← arg op 1))) (fun _ => unitJ) id
  | "count" => return keep (d.count (← jInt (← arg op 1))) toJson (fun _ => d)
  | "reverse" => return keep d.reverse (fun _ => unitJ) id
  | "getitem" => return keep (d.getitem (← jInt (← arg op 1))) toJson (fun _ => d)
  | "setitem" => return keep (d.setitem (← jInt (← arg op 1)) (some (← jInt (← arg op 2)))) (fun _ => unitJ) id
  | "delitem" => return keep (d.setitem (← jInt (← arg op 1)) none) (fun _ => unitJ) id
  | "copy" => return (okJ (dequeJ d.copy), d)
  | "imul" => return keep (d.irepeat (← jInt (← arg op 1))) (fun _ => unitJ) id
  | "mul" => return keep (d.mul (← jInt (← arg op 1))) dequeJ (fun _ => d)
  | "add" =>
    let other ← match Deque.make (← jInts (← arg op 1)) (← optArg op 2) with
      | .ok o => pure o
      | .error _ => throw "add: bad other deque"
    return (okJ (dequeJ (d.concat other)), d)
  | "add_self" => return (okJ (dequeJ (d.concat d)), d)
  | "clear" => return (okJ unitJ, d.clear)
  | "init" => return keep (d.init (← jInts (← arg op 1)) (← optArg op 2)) (fun _ => unitJ) id
  | "init_self" => return keep (d.init [] (← optArg op 1)) (fun _ => unitJ) id
  | other => throw s!"unknown deque op {other}"

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
  let init ← jInts (← field j "init")
  let ops := (← (← field j "ops").getArr?).toList
  match fn with
  | "list" => runOps stepList toJson init ops
  | "array" =>
    let tc ← tcOf (← getStr j "tc")
    match arrNew tc init with
    | .ok a => runOps stepArr (fun a => toJson a.items) a ops
    | .error e => return errJ e
  | "deque" =>
    match Deque.make init (← getOptInt j "maxlen") with
    | .ok d => runOps stepDeque (fun d => Json.arr #[toJson d.items, toJson d.blocks]) d ops
    | .error e => return errJ e
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Sequences
