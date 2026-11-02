import PyLean.DiffCore
import PyLean.TextLibs.DifflibText

/-! `difflib.*` difftest cases; see `difftest/textlibs_diff.py`. -/

namespace PyLean.TextLibs.Difflib

open Lean PyLean PyLean.Diff

def nats (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def tagS : Tag → String
  | .replace => "replace" | .delete => "delete" | .insert => "insert" | .equal => "equal"

def opJ (o : Op) : Json :=
  Json.arr #[toJson (tagS o.1), toJson o.2.1, toJson o.2.2.1, toJson o.2.2.2.1, toJson o.2.2.2.2]

def tJ (t : T) : Json := Json.arr #[toJson t.1, toJson t.2.1, toJson t.2.2]

def excJ (e : PyExc) : Json := Json.arr #[toJson "exc", encPy (fun (_ : Unit) => Json.null) (.error e)]

/-- Run a list of method calls; a raising call is reported and the rest are still run. -/
def step (s : SM) (c : Json) : Except String (SM × Json) := do
  let op ← getStr c "op"
  match op with
  | "blocks" =>
    match getBlocks s with
    | .ok (s, r) => return (s, Json.arr (r.map tJ).toArray)
    | .error e => return (s, excJ e)
  | "opcodes" =>
    match getOpcodes s with
    | .ok (s, r) => return (s, Json.arr (r.map opJ).toArray)
    | .error e => return (s, excJ e)
  | "grouped" =>
    match getGrouped s (← getNat c "n") with
    | .ok (s, r) => return (s, Json.arr (r.map fun g => Json.arr (g.map opJ).toArray).toArray)
    | .error e => return (s, excJ e)
  | "ratio" =>
    match ratioPair s with
    | .ok (s, m, l) => return (s, Json.arr #[toJson m, toJson l])
    | .error e => return (s, excJ e)
  | "quick" =>
    let (s, m, l) := quickPair s
    return (s, Json.arr #[toJson m, toJson l])
  | "real" =>
    let (m, l) := realQuickPair s
    return (s, Json.arr #[toJson m, toJson l])
  | "longest" =>
    match findLongest s (← getNat c "alo") (← getNat c "ahi") (← getNat c "blo") (← getNat c "bhi") with
    | .ok r => return (s, tJ r)
    | .error e => return (s, excJ e)
  | "seq1" => return (setSeq1 s (← nats (← field c "x")) (← getBool c "same"), Json.null)
  | "seq2" =>
    match setSeq2 s (← nats (← field c "x")) (← getBool c "same") with
    | (s, .ok ()) => return (s, Json.null)
    | (s, .error e) => return (s, excJ e)
  | "seqs" =>
    match setSeqs s (← nats (← field c "x")) (← nats (← field c "y")) (← getBool c "same") (← getBool c "same2") with
    | (s, .ok ()) => return (s, Json.null)
    | (s, .error e) => return (s, excJ e)
  | _ => throw s!"unknown op {op}"

/-- An element of `difflib.obj`: its value, its `__hash__`, which raises if `none`, and the elements its
`__eq__` raises on. An element is its index in the table, so `is` is equality of indices. -/
structure El where
  v : Nat
  h : Option Nat
  bad : List Nat

def elOps (t : Array El) : Ops Nat where
  hash i :=
    match (t.getD i ⟨0, none, []⟩).h with
    | some h => .ok h
    | none => .error (.valueError s!"hash {i}")
  eq i j :=
    let x := t.getD i ⟨0, none, []⟩
    if x.bad.contains j then .error (.valueError s!"eq {i} {j}")
    else .ok (x.v == (t.getD j ⟨0, none, []⟩).v)
  same i j := i == j

def stepO (o : Ops Nat) (s : SMO Nat) (c : Json) : Except String (SMO Nat × Json) := do
  let op ← getStr c "op"
  match op with
  | "blocks" =>
    match getBlocksO o s with
    | .ok (s, r) => return (s, Json.arr (r.map tJ).toArray)
    | .error e => return (s, excJ e)
  | "opcodes" =>
    match getOpcodesO o s with
    | (s, .ok r) => return (s, Json.arr (r.map opJ).toArray)
    | (s, .error e) => return (s, excJ e)
  | "grouped" =>
    match getGroupedO o s (← getNat c "n") with
    | (s, .ok r) => return (s, Json.arr (r.map fun g => Json.arr (g.map opJ).toArray).toArray)
    | (s, .error e) => return (s, excJ e)
  | "ratio" =>
    match ratioPairO o s with
    | .ok (s, m, l) => return (s, Json.arr #[toJson m, toJson l])
    | .error e => return (s, excJ e)
  | "quick" =>
    match quickPairO o s with
    | (s, .ok (m, l)) => return (s, Json.arr #[toJson m, toJson l])
    | (s, .error e) => return (s, excJ e)
  | "real" => return (s, Json.arr #[toJson (min s.a.length s.b.length), toJson (s.a.length + s.b.length)])
  | "longest" =>
    match findLongestO o s (← getNat c "alo") (← getNat c "ahi") (← getNat c "blo") (← getNat c "bhi") with
    | .ok r => return (s, tJ r)
    | .error e => return (s, excJ e)
  | "seq1" => return (setSeq1O s (← nats (← field c "x")) (← getBool c "same"), Json.null)
  | "seq2" =>
    match setSeq2O o s (← nats (← field c "x")) (← getBool c "same") with
    | (s, .ok ()) => return (s, Json.null)
    | (s, .error e) => return (s, excJ e)
  | "seqs" =>
    match setSeqsO o s (← nats (← field c "x")) (← nats (← field c "y")) (← getBool c "same") (← getBool c "same2") with
    | (s, .ok ()) => return (s, Json.null)
    | (s, .error e) => return (s, excJ e)
  | _ => throw s!"unknown op {op}"

def elOf (j : Json) : Except String El := do
  let v ← getNat j "v"
  let h : Option Nat ← match j.getObjVal? "h" with
    | .ok Json.null => pure none
    | .ok x => pure (some (← x.getNat?))
    | .error _ => pure none
  return ⟨v, h, ← nats (← field j "bad")⟩

/-- The objects `difflib.text` puts among its lines. -/
def otherLine : Nat → LineO
  | 0 => .other "int" (toStr "1") true
  | 1 => .other "bytes" (toStr "b'x'") true
  | 2 => .other "NoneType" (toStr "None") true
  | _ => .other "list" (toStr "[1]") false

def lineOf (j : Json) : Except String LineO := do
  match j.getObjVal? "o" with
  | .ok k => return otherLine (← k.getNat?)
  | .error _ => return .str (← nats j)

def seqOf (j : Json) : Except String SeqArg := do
  match j.getObjVal? "str" with
  | .ok x => return .str (← nats x)
  | .error _ => return .lines ((← (← j.getArr?).mapM lineOf).toList)

def textArg (j : Json) (k : String) : Except String TextArg := do
  let x ← field j k
  match x.getObjVal? "bad" with
  | .ok _ => return .other "b'x'"
  | .error _ => return .str (← nats x)

def strsJ (l : List Str) : Json := Json.arr (l.map fun s => Json.arr (s.map toJson).toArray).toArray

def emitJ (e : Emit) : Json :=
  match e.2 with
  | .ok () => Json.arr #[strsJ e.1, Json.null]
  | .error x => Json.arr #[strsJ e.1, excJ x]

def strsOf (j : Json) : Except String (List Str) := do
  return (← (← j.getArr?).mapM nats).toList

/-- `null`, or the junk and the raising items of a callback. -/
def lineFn (j : Json) : Except String (Option (Str → Py Bool)) := do
  if j.isNull then return none
  let junk ← strsOf (← field j "junk")
  let boom ← strsOf (← field j "boom")
  return some fun x => if boom.contains x then .error (.valueError "boom") else .ok (junk.contains x)

def charFn (j : Json) : Except String (Option (Nat → Py Bool)) := do
  if j.isNull then return none
  match j.getStr? with
  | .ok _ => return some fun c => .ok (isCharJunk c)
  | .error _ =>
    let junk ← nats (← field j "junk")
    let boom ← nats (← field j "boom")
    return some fun x => if boom.contains x then .error (.valueError "boom") else .ok (junk.contains x)

def runText (j : Json) : Except String Json := do
  let op ← getStr j "op"
  match op with
  | "unified" =>
    let r := unifiedDiff (← seqOf (← field j "a")) (← seqOf (← field j "b")) (← textArg j "f") (← textArg j "t")
      (← textArg j "fd") (← textArg j "td") (← getNat j "n") (← textArg j "lt")
    return encPy strsJ r
  | "context" =>
    let r := contextDiff (← seqOf (← field j "a")) (← seqOf (← field j "b")) (← textArg j "f") (← textArg j "t")
      (← textArg j "fd") (← textArg j "td") (← getNat j "n") (← textArg j "lt")
    return encPy (fun (x : Json) => x) (.ok (emitJ r))
  | "ndiff" =>
    let e := compareO (← lineFn (← field j "lj")) (← charFn (← field j "cj")) (← strsOf (← field j "a")) (← strsOf (← field j "b"))
    let r1 := if e.2 matches .ok () then restoreO e.1 1 else .ok []
    let r2 := if e.2 matches .ok () then restoreO e.1 2 else .ok []
    return encPy (fun (x : Json) => x) (.ok (Json.arr #[emitJ e, encPy strsJ r1, encPy strsJ r2]))
  | "restore" => return encPy strsJ (restoreO (← strsOf (← field j "d")) (← getInt j "which"))
  | "range" =>
    return encPy (fun (x : Json) => x) (.ok (strsJ [fmtRangeU (← getNat j "s") (← getNat j "e"), fmtRangeC (← getNat j "s") (← getNat j "e")]))
  | "junk" =>
    let l ← nats (← field j "s")
    return encPy (fun (x : Json) => x) (.ok (Json.arr #[toJson (isLineJunk l), toJson (l.map isCharJunk)]))
  | "keepws" =>
    return encPy strsJ (.ok [keepWs (← nats (← field j "s")) (← nats (← field j "tags"))])
  | "close" =>
    return encPy strsJ (closeMatches (← nats (← field j "w")) (← strsOf (← field j "ps")) (← getInt j "n") (PyLean.Binary64.F64.ofBits (← getNat j "cut")))
  | _ => throw s!"unknown op {op}"

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "difflib.text" => runText j
  | "difflib.obj" =>
    let t ← ((← (← field j "elems").getArr?).mapM elOf)
    let o := elOps t
    let junk ← nats (← field j "junk")
    let boom ← nats (← field j "boom")
    let f : Nat → Py Bool := fun x =>
      if boom.contains x then .error (.valueError "boom") else .ok (junk.contains (t.getD x ⟨0, none, []⟩).v)
    let isjunk := if ← getBool j "hasjunk" then some f else none
    match makeO o isjunk (← nats (← field j "a")) (← nats (← field j "b")) (← getBool j "auto") with
    | .error e => return encPy (fun (x : Json) => x) (.error e)
    | .ok s =>
      let mut s := s
      let mut out : Array Json := #[]
      for c in (← (← field j "ops").getArr?) do
        let (s', r) ← stepO o s c
        s := s'
        out := out.push r
      return encPy (fun (x : Json) => x) (.ok (Json.arr out))
  | "difflib.seq" =>
    let junk ← nats (← field j "junk")
    let boom ← nats (← field j "boom")
    let hasJunk ← getBool j "hasjunk"
    let f : Nat → Py Bool := fun x =>
      if boom.contains x then .error (.valueError "boom") else .ok (junk.contains x)
    let isjunk := if hasJunk then some f else none
    match make isjunk (← nats (← field j "a")) (← nats (← field j "b")) (← getBool j "auto") with
    | .error e => return encPy (fun (x : Json) => x) (.error e)
    | .ok s =>
      let mut s := s
      let mut out : Array Json := #[]
      for c in (← (← field j "ops").getArr?) do
        let (s', r) ← step s c
        s := s'
        out := out.push r
      return encPy (fun (x : Json) => x) (.ok (Json.arr out))
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Difflib
