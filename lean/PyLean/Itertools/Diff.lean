import PyLean.DiffCore
import PyLean.Itertools.Simple
import PyLean.Itertools.Combinatorics
import PyLean.Itertools.CountRepeat
import PyLean.Itertools.GroupbyTee
import PyLean.Itertools.GroupbyRaising
import PyLean.Itertools.TeeReentry
import PyLean.Itertools.PairwiseReentry
import PyLean.Itertools.CountFloat

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

/-- `boom` is what the difftest's callbacks raise for the value 3. -/
def boom (m : String) : PyExc := .valueError m

def predFn : String → Except String (Int → Py Bool)
  | "lt5" => .ok (fun x => .ok (decide (x < 5)))
  | "even" => .ok (fun x => .ok (x % 2 == 0))
  | "pos" => .ok (fun x => .ok (decide (x > 0)))
  | "nz" => .ok (fun x => .ok (truthy x))
  | "r3" => .ok (fun x => if x = 3 then .error (boom "pred") else .ok (decide (x < 5)))
  | p => .error s!"unknown predicate {p}"

def truthI (x : Int) : Py Bool := .ok (truthy x)

def keyFnI : String → Except String (Int → Int)
  | "id" => .ok id
  | "div3" => .ok (fun x => Int.fdiv x 3)
  | "mod2" => .ok (fun x => x % 2)
  | "abs" => .ok (fun x => (x.natAbs : Int))
  | "neg" => .ok (fun x => -x)
  | k => .error s!"unknown key {k}"

/-- The key function with its raising variant, for the C side. -/
def keyFnPy : String → Except String (Int → Py Int)
  | "r3" => .ok (fun x => if x = 3 then .error (boom "key") else .ok x)
  | k => do
    let f ← keyFnI k
    return (fun x => .ok (f x))

def binopFn : String → Except String (Int → Int → Py Int)
  | "add" => .ok (fun a b => .ok (a + b))
  | "mul" => .ok (fun a b => .ok (a * b))
  | "max" => .ok (fun a b => .ok (max a b))
  | "min" => .ok (fun a b => .ok (min a b))
  | "sub" => .ok (fun a b => .ok (a - b))
  | "r3" => .ok (fun a b => if b = 3 then .error (boom "binop") else .ok (a + b))
  | f => .error s!"unknown binop {f}"

def starFn : String → Except String (List Int → Py Int)
  | "sum" => .ok (fun a => .ok a.sum)
  | "len" => .ok (fun a => .ok a.length)
  | "r3" => .ok (fun a => if 3 ∈ a then .error (boom "star") else .ok a.sum)
  | f => .error s!"unknown starmap func {f}"

def getIntList (j : Json) (k : String) : Except String (List Int) := do
  (← (← field j k).getArr?).toList.mapM (·.getInt?)

def getOptIntList (j : Json) (k : String) : Except String (List (Option Int)) := do
  (← (← field j k).getArr?).toList.mapM (fun v => match v with
    | .null => .ok none
    | v => some <$> v.getInt?)

def decErr (j : Json) : Except String (Option PyExc) :=
  match j.getObjVal? "err" with
  | .ok .null | .error _ => .ok none
  | .ok v => do return some (boom (← v.getStr?))

/-- `{"l": [...], "err": msg-or-null}` or `{"bad": "int"}`. -/
def decObj (j : Json) : Except String (Obj Int) :=
  match j.getObjVal? "bad" with
  | .ok v => do return .notIterable (← v.getStr?)
  | .error _ => do return .iter (← getIntList j "l") (← decErr j)

/-- `{"ls": [objs], "err": ...}` or `{"bad": ...}`: an iterable of objects. -/
def decObjObj (j : Json) : Except String (Obj (Obj Int)) :=
  match j.getObjVal? "bad" with
  | .ok v => do return .notIterable (← v.getStr?)
  | .error _ => do
    let ls ← (← (← field j "ls").getArr?).toList.mapM decObj
    return .iter ls (← decErr j)

def getObj (j : Json) (k : String) : Except String (Obj Int) := do decObj (← field j k)

def getObjs (j : Json) (k : String) : Except String (List (Obj Int)) := do
  (← (← field j k).getArr?).toList.mapM decObj

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

def encOpRes : OpRes Int → Json
  | .val v => toJson v
  | .str s => toJson s
  | .stop => Json.null
  | .exc e => Json.arr #[toJson "exc", toJson e.className, toJson e.message]

def encNext : NextRes Int → Json
  | .val v => toJson v
  | .stop => Json.null
  | .exc e => Json.arr #[toJson "exc", toJson e.className, toJson e.message]

def encGb : GbRes Int → Json
  | .val v => toJson v
  | .stop => Json.null
  | .exc e => Json.arr #[toJson "exc", toJson e.className, toJson e.message]
  | .crash => toJson "CRASH"

def encPairRes : NextRes (Int × Int) → Json
  | .val (a, b) => Json.arr #[toJson a, toJson b]
  | .stop => Json.null
  | .exc e => Json.arr #[toJson "exc", toJson e.className, toJson e.message]

/-- A value for `count`: an int, `true`/`false`, `{"f": bits}`, `"bad"` for a
`Raising` object, `"str"` for a non-number. -/
def decVal (v : Json) : Except String (CVal PyNum) :=
  match v with
  | .str "bad" => .ok (.num .raising)
  | .str "str" => .ok (.nonNum .str)
  | .bool b => .ok (.intSub (if b then 1 else 0) (.bool b))
  | .obj _ => do return .num (.float (Binary64.F64.ofBits (← (← v.getObjVal? "f").getNat?)))
  | v => do return .int (← v.getInt?)

def getOptVal (j : Json) (k : String) : Except String (Option (CVal PyNum)) :=
  match j.getObjVal? k with
  | .ok v => some <$> decVal v
  | .error _ => .ok none

def encVal : CVal PyNum → Json
  | .int i => toJson i
  | .intSub _ (.bool b) => Json.bool b
  | .num (.float x) => if x.isNaN then toJson "nan" else Json.mkObj [("f", toJson x.bits)]
  | .num .raising => toJson "bad"
  | _ => toJson "?"

def encValRes : OpRes (CVal PyNum) → Json
  | .val v => encVal v
  | .str s => toJson s
  | .stop => Json.null
  | .exc e => Json.arr #[toJson "exc", toJson e.className, toJson e.message]

def decGbOp (v : Json) : Except String (GbOp Int) :=
  match v with
  | .str "o" => pure .outer
  | .arr a => do return GbOp.direct (← (a.getD 1 Json.null).getInt?)
  | v => GbOp.group <$> v.getNat?

def decTeeOp (v : Json) : Except String TeeOp := do
  let a ← v.getArr?
  match ← (a.getD 0 Json.null).getStr? with
  | "n" => TeeOp.next <$> (a.getD 1 Json.null).getNat?
  | "t" => return TeeOp.tee (← (a.getD 1 Json.null).getNat?) (← (a.getD 2 Json.null).getNat?)
  | "c" => TeeOp.copy <$> (a.getD 1 Json.null).getNat?
  | "k" => TeeOp.ctor <$> (a.getD 1 Json.null).getNat?
  | o => throw s!"unknown tee op {o}"

def getHooks {β : Type} (dec : Json → Except String β) (j : Json) : Except String (List (List β)) :=
  match j.getObjVal? "hooks" with
  | .error _ => .ok []
  | .ok v => do
    (← v.getArr?).toList.mapM (fun h => do (← h.getArr?).toList.mapM dec)

/-- The keys the difftest compares with `__eq__`: interned, so equal values are
the same object, and distinct objects are unequal; `eqr` raises on 3. -/
def keyEqFor (kname : String) : KeyEq Int :=
  if kname == "eqr" then
    ⟨fun a b => a == b, fun a b => if a = 3 ∨ b = 3 then .error (boom "eq") else .ok false⟩
  else if kname == "eqh" then ⟨fun a b => a == b, fun _ _ => .ok false⟩
  else decEq Int

def getOps (j : Json) : Except String (List Op) := do
  (← (← field j "ops").getArr?).toList.mapM (fun v => do
    match ← v.getStr? with
    | "n" => pure Op.next
    | "r" => pure Op.repr
    | "h" => pure Op.hint
    | o => throw s!"unknown op {o}")

def run (fn : String) (j : Json) : Except String Json := do
  let isC := (getStr j "impl").toOption == some "c"
  let ok (v : Json) : Json := Json.mkObj [("ok", v)]
  match fn with
  | "islice" =>
    let o ← getObj j "obj"
    let args ← getOptIntList j "args"
    let (r, consumed) := if isC then cIslice o args else docIslice o args
    return ok (Json.arr #[Json.arr (r.1.map toJson).toArray, encExc r.2, toJson consumed])
  | "islice_arity" =>
    let nargs ← getNat j "nargs"
    let kw ← getBool j "kw"
    return encPy (fun _ => Json.null) (cIsliceArity nargs kw ((getBool j "sub").toOption == some true))
  | "batched" =>
    let o ← getObj j "obj"
    let n ← getInt j "n"
    let strict ← getBool j "strict"
    return ok (encRun encInts (if isC then cBatched o n strict else docBatched o n strict))
  | "accumulate" =>
    let o ← getObj j "obj"
    let f ← binopFn (← getStr j "f")
    let init ← getOptInt j "initial"
    return ok (encRun toJson (if isC then cAccumulate f init o else docAccumulate f init o))
  | "chain" =>
    let ls ← getObjs j "objs"
    if (getBool j "kw").toOption == some true then
      if (getBool j "sub").toOption == some true then
        return ok (encRun toJson (cChainSubKw ls))
      return encPy (fun _ => Json.null) (cChainNew ls true)
    return ok (encRun toJson (if isC then cChain ls else docChain ls))
  | "chain_from" =>
    let o ← decObjObj (← field j "src")
    return ok (encRun toJson (if isC then cChainFrom o else docChainFrom o))
  | "compress" =>
    let d ← getObj j "data"
    let s ← getObj j "sel"
    return ok (encRun toJson (if isC then cCompress truthI d s else docCompress truthI d s))
  | "cycle" =>
    let o ← getObj j "obj"
    let k ← getNat j "k"
    return ok (encRun toJson (if isC then cCycle o k else docCycle o k))
  | "dropwhile" | "takewhile" | "filterfalse" =>
    let o ← getObj j "obj"
    let pname ← getStr j "pred"
    let p ← if pname == "none" then pure none else some <$> predFn pname
    let r := match fn, isC with
      | "dropwhile", true => cDropwhile (p.getD truthI) o
      | "dropwhile", false => docDropwhile (p.getD truthI) o
      | "takewhile", true => cTakewhile (p.getD truthI) o
      | "takewhile", false => docTakewhile (p.getD truthI) o
      | _, true => cFilterfalse truthI p o
      | _, false => docFilterfalse truthI p o
    return ok (encRun toJson r)
  | "pairwise" =>
    let o ← getObj j "obj"
    return ok (encRun (fun (a, b) => Json.arr #[toJson a, toJson b])
      (if isC then cPairwise o else docPairwise o))
  | "starmap" =>
    let o ← decObjObj (← field j "src")
    let f ← starFn (← getStr j "f")
    return ok (encRun toJson (if isC then cStarmap f o else docStarmap f o))
  | "zip_longest" =>
    let ls ← getObjs j "objs"
    let kwArr ← (← field j "kw").getArr?
    let kw ← kwArr.toList.mapM (fun v => do
      let a ← v.getArr?
      let k ← (a.getD 0 Json.null).getStr?
      let f : Option Int ← match a.getD 1 Json.null with
        | .null => pure none
        | v => some <$> v.getInt?
      return (k, f))
    let r := if isC then cZipLongest ls kw
      else docZipLongest ls (match zipFill kw with | .ok f => f | .error _ => none)
    return ok (encRun (fun row => Json.arr (row.map encOptInt).toArray) r)
  | "product" =>
    let ls ← getObjs j "objs"
    let rep ← getOptInt j "repeat"
    return ok (encRun encInts (if isC then cProduct ls rep else docProduct ls rep))
  | "combinations" | "cwr" =>
    let o ← getObj j "obj"
    let r ← getInt j "r"
    let res := match fn, isC with
      | "combinations", true => cCombinations o r
      | "combinations", false => docCombinations o r
      | _, true => cCwr o r
      | _, false => docCwr o r
    return ok (encRun encInts res)
  | "permutations" =>
    let o ← getObj j "obj"
    if (getBool j "badr").toOption == some true then
      return ok (encRun encInts (cPermutations o none true))
    let r ← getOptInt j "r"
    return ok (encRun encInts (if isC then cPermutations o r else docPermutations o r))
  | "sizeof" =>
    let o ← getObj j "obj"
    let basic ← getNat j "basic"
    let enc (r : Py Nat) : Json := encPy toJson r
    match ← getStr j "kind" with
    | "combinations" => return enc ((cCombSizeof basic) <$> cCombinationsNew o (← getInt j "r"))
    | "cwr" => return enc ((cCombSizeof basic) <$> cCwrNew o (← getInt j "r"))
    | "permutations" => return enc ((cPermSizeof basic) <$> cPermutationsNew o (← getOptInt j "r"))
    | _ => return enc ((cProductSizeof basic) <$> cProductNew (← getObjs j "objs") (← getOptInt j "r"))
  | "count" =>
    let start ← getOptVal j "start"
    let step ← getOptVal j "step"
    let ops ← getOps j
    if isC then
      let ty := if (getBool j "sub").toOption == some true then "SubCount" else "count"
      return ok (Json.arr ((cCount numOps start step ops ty).map encValRes).toArray)
    else
      let r := docCountRun numOps (step.getD (.int 1)) (ops.filter (· == .next)).length (start.getD (.int 0))
      return ok (encRun encVal r)
  | "repeat" =>
    let elem ← getInt j "elem"
    let times ← getOptInt j "times"
    let ops ← getOps j
    if isC then
      let rs := cRepeat (fun (x : Int) => toString x) elem times ops
      return ok (Json.arr (rs.map (fun r => match r with
        | .inl a => encOpRes a
        | .inr b => encOpRes b)).toArray)
    else return ok (encInts (docRepeatValues elem times (ops.filter (· == .next)).length))
  | "groupby" =>
    let o ← getObj j "obj"
    let kname ← getStr j "key"
    let ops ← (← (← field j "ops").getArr?).toList.mapM decGbOp
    if isC then
      let hooks ← getHooks decGbOp j
      let key ← if kname == "eqr" || kname == "eqh" then pure (fun x => .ok x) else keyFnPy kname
      let r := cGroupbyR (keyEqFor kname) key o hooks ops
      return encPy (fun (rs, crashed) =>
        if crashed then toJson "CRASH"
        else Json.arr (rs.map (fun r => match r with
          | .inl a => encGb a
          | .inr b => encGb b)).toArray) r
    else
      return encPy (fun rs => Json.arr (rs.map (fun r => match r with
        | .inl a => encOptInt a
        | .inr b => encOptInt b)).toArray) (docGroupby (← keyFnI kname) o ops)
  | "tee" | "tee_wrap" =>
    let o ← getObj j "obj"
    let ops ← (← (← field j "ops").getArr?).toList.mapM decTeeOp
    let hooks ← getHooks decTeeOp j
    let enc := fun (r : List (NextRes Int) × Nat) =>
      Json.arr #[Json.arr (r.1.map encNext).toArray, toJson r.2]
    if fn == "tee_wrap" then return encPy enc (cTeeWrap o hooks ops)
    let n ← getInt j "n"
    return encPy enc (if isC then cTeeR o n hooks ops else docTee o n ops)
  | "pairwise_r" =>
    let o ← getObj j "obj"
    let hooks ← (← (← field j "hooks").getArr?).toList.mapM (·.getNat?)
    let n ← getNat j "calls"
    return encPy (fun rs => Json.arr (rs.map encPairRes).toArray) (cPairwiseR o hooks n)
  | "teeweak" =>
    let refs ← (← (← field j "refs").getArr?).toList.mapM (fun v => match v with
      | .str "b" => pure WRef.basic
      | v => WRef.cb <$> v.getNat?)
    let bad ← (← (← field j "raising").getArr?).toList.mapM (·.getNat?)
    let cb := fun (i : Nat) => if i ∈ bad then (.error (boom "cb") : Py Unit) else .ok ()
    let t : TeeObj Unit := ⟨some (), refs.foldl (fun acc w => wrInsert w acc) []⟩
    return ok (Json.arr ((teeDealloc cb t).map (fun ev => match ev with
      | .called i => Json.arr #[toJson "called", toJson i]
      | .unraisable i e => Json.arr #[toJson "unraisable", toJson i, toJson e.className, toJson e.message])).toArray)
  | "teedata" =>
    let k ← getNat j "len"
    let next := match (getStr j "next").toOption with
      | some "none" => TeeNextArg.none
      | some "data" => .dataobject
      | _ => .other
    return encPy (fun _ => Json.null) (cTeeDataNew (List.replicate k (0 : Int)) next)
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Itertools
