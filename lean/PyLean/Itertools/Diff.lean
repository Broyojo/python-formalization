import PyLean.DiffCore
import PyLean.Itertools.Simple
import PyLean.Itertools.Combinatorics
import PyLean.Itertools.CountRepeat
import PyLean.Itertools.GroupbyTee

/-!
Differential-testing handler for `itertools` cases (`"mod": "itertools"`).

* `"impl"` is `"c"` (the C model, compared with `itertools`) or `"doc"` (the
  doc-equivalent model, compared with the rst code run as Python).
* A drained iterator is `[items, null]` or `[items, [class, message]]`; islice
  appends the number of input items consumed; ops-driven objects return one
  entry per op.
* Callbacks are named (`difftest/itertools_diff.py` has the Python side).
-/

namespace PyLean.Itertools

open Lean PyLean PyLean.Diff

def predFn : String → Except String (Int → Bool)
  | "lt5" => .ok (fun x => decide (x < 5))
  | "even" => .ok (fun x => x % 2 == 0)
  | "pos" => .ok (fun x => decide (x > 0))
  | "nz" => .ok truthy
  | p => .error s!"unknown predicate {p}"

def keyFnI : String → Except String (Int → Int)
  | "id" => .ok id
  | "div3" => .ok (fun x => Int.fdiv x 3)
  | "mod2" => .ok (fun x => x % 2)
  | "abs" => .ok (fun x => (x.natAbs : Int))
  | "neg" => .ok (fun x => -x)
  | k => .error s!"unknown key {k}"

def binopFn : String → Except String (Int → Int → Int)
  | "add" => .ok (· + ·)
  | "mul" => .ok (· * ·)
  | "max" => .ok max
  | "min" => .ok min
  | "sub" => .ok (· - ·)
  | f => .error s!"unknown binop {f}"

def starFn : String → Except String (List Int → Int)
  | "sum" => .ok List.sum
  | "len" => .ok (fun a => a.length)
  | f => .error s!"unknown starmap func {f}"

def getIntList (j : Json) (k : String) : Except String (List Int) := do
  (← (← field j k).getArr?).toList.mapM (·.getInt?)

def getIntLists (j : Json) (k : String) : Except String (List (List Int)) := do
  (← (← field j k).getArr?).toList.mapM (fun v => do (← v.getArr?).toList.mapM (·.getInt?))

def getOptIntList (j : Json) (k : String) : Except String (List (Option Int)) := do
  (← (← field j k).getArr?).toList.mapM (fun v => match v with
    | .null => .ok none
    | v => some <$> v.getInt?)

def encExc (e : Option PyExc) : Json :=
  match e with
  | none => Json.null
  | some e => Json.arr #[toJson e.className, toJson e.message]

def encRun {α : Type} (enc : α → Json) (r : Run α) : Json :=
  Json.arr #[Json.arr (r.1.map enc).toArray, encExc r.2]

def encInts (l : List Int) : Json := Json.arr (l.map toJson).toArray

def encOptInt : Option Int → Json
  | none => Json.null
  | some v => toJson v

def encOpRes : OpRes → Json
  | .int v => toJson v
  | .str s => toJson s
  | .stop => Json.null
  | .exc e => Json.arr #[toJson "exc", toJson e.className, toJson e.message]

def getOps (j : Json) : Except String (List Op) := do
  (← (← field j "ops").getArr?).toList.mapM (fun v => do
    match ← v.getStr? with
    | "n" => pure Op.next
    | "r" => pure Op.repr
    | "h" => pure Op.hint
    | o => throw s!"unknown op {o}")

def encPyPair (r : Py (List (Option Int) × Nat)) : Json :=
  match r with
  | .ok (rs, pulled) => Json.mkObj [("ok", Json.arr #[Json.arr (rs.map encOptInt).toArray, toJson pulled])]
  | .error e => Json.mkObj [("exc", toJson e.className), ("msg", toJson e.message)]

def run (fn : String) (j : Json) : Except String Json := do
  let isC := (getStr j "impl").toOption == some "c"
  let ok (v : Json) : Json := Json.mkObj [("ok", v)]
  match fn with
  | "islice" =>
    let l ← getIntList j "l"
    let args ← getOptIntList j "args"
    let (r, consumed) := if isC then cIslice l args else docIslice l args
    return ok (Json.arr #[Json.arr (r.1.map toJson).toArray, encExc r.2, toJson consumed])
  | "batched" =>
    let l ← getIntList j "l"
    let n ← getInt j "n"
    let strict ← getBool j "strict"
    return ok (encRun encInts (if isC then cBatched l n strict else docBatched l n strict))
  | "accumulate" =>
    let l ← getIntList j "l"
    let f ← binopFn (← getStr j "f")
    let init ← getOptInt j "initial"
    return ok (encRun toJson (if isC then cAccumulate f init l else docAccumulate f init l))
  | "chain" =>
    let ls ← getIntLists j "ls"
    return ok (encRun toJson (if isC then cChain ls else docChain ls))
  | "compress" =>
    let d ← getIntList j "data"
    let s ← getIntList j "sel"
    return ok (encRun toJson (if isC then cCompress d s else docCompress d s))
  | "cycle" =>
    let l ← getIntList j "l"
    let k ← getNat j "k"
    return ok (encRun toJson (if isC then cCycle l k else docCycle l k))
  | "dropwhile" | "takewhile" | "filterfalse" =>
    let l ← getIntList j "l"
    let pname ← getStr j "pred"
    let p ← if pname == "none" then pure none else some <$> predFn pname
    let r := match fn, isC with
      | "dropwhile", true => cDropwhile (p.getD truthy) l
      | "dropwhile", false => docDropwhile (p.getD truthy) l
      | "takewhile", true => cTakewhile (p.getD truthy) l
      | "takewhile", false => docTakewhile (p.getD truthy) l
      | _, true => cFilterfalse p l
      | _, false => docFilterfalse p l
    return ok (encRun toJson r)
  | "pairwise" =>
    let l ← getIntList j "l"
    return ok (encRun (fun (a, b) => Json.arr #[toJson a, toJson b])
      (if isC then cPairwise l else docPairwise l))
  | "starmap" =>
    let ls ← getIntLists j "ls"
    let f ← starFn (← getStr j "f")
    return ok (encRun toJson (if isC then cStarmap f ls else docStarmap f ls))
  | "zip_longest" =>
    let ls ← getIntLists j "ls"
    let fill ← getOptInt j "fill"
    return ok (encRun (fun row => Json.arr (row.map encOptInt).toArray)
      (if isC then cZipLongest ls fill else docZipLongest ls fill))
  | "product" =>
    let ls ← getIntLists j "ls"
    let rep ← getOptInt j "repeat"
    return ok (encRun encInts (if isC then cProduct ls rep else docProduct ls rep))
  | "combinations" | "cwr" =>
    let l ← getIntList j "l"
    let r ← getInt j "r"
    let res := match fn, isC with
      | "combinations", true => cCombinations l r
      | "combinations", false => docCombinations l r
      | _, true => cCwr l r
      | _, false => docCwr l r
    return ok (encRun encInts res)
  | "permutations" =>
    let l ← getIntList j "l"
    let r ← getOptInt j "r"
    return ok (encRun encInts (if isC then cPermutations l r else docPermutations l r))
  | "count" =>
    let start ← getOptInt j "start"
    let step ← getOptInt j "step"
    let ops ← getOps j
    if isC then return ok (Json.arr ((cCount start step ops).map encOpRes).toArray)
    else return ok (encInts (docCountValues start step (ops.filter (· == .next)).length))
  | "repeat" =>
    let elem ← getInt j "elem"
    let times ← getOptInt j "times"
    let ops ← getOps j
    if isC then return ok (Json.arr ((cRepeat elem times ops).map encOpRes).toArray)
    else return ok (encInts (docRepeatValues elem times (ops.filter (· == .next)).length))
  | "groupby" =>
    let l ← getIntList j "l"
    let key ← keyFnI (← getStr j "key")
    let ops ← (← (← field j "ops").getArr?).toList.mapM (fun v => match v with
      | .str "o" => pure GbOp.outer
      | v => GbOp.group <$> v.getNat?)
    let rs := if isC then cGroupby key l ops else docGroupby key l ops
    return ok (Json.arr (rs.map encOptInt).toArray)
  | "tee" =>
    let l ← getIntList j "l"
    let n ← getInt j "n"
    let ops ← (← (← field j "ops").getArr?).toList.mapM (fun v => do
      let a ← v.getArr?
      match ← (a.getD 0 Json.null).getStr? with
      | "n" => TeeOp.next <$> (a.getD 1 Json.null).getNat?
      | "t" => return TeeOp.tee (← (a.getD 1 Json.null).getNat?) (← (a.getD 2 Json.null).getNat?)
      | "c" => TeeOp.copy <$> (a.getD 1 Json.null).getNat?
      | o => throw s!"unknown tee op {o}")
    return encPyPair (if isC then cTee l n ops else docTee l n ops)
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Itertools
