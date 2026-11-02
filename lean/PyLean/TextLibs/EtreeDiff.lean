import PyLean.DiffCore
import PyLean.TextLibs.EtreeModel
import PyLean.TextLibs.EtreePath
import PyLean.TextLibs.EtreeWriters

/-! `etree.*` difftest cases; see `EtreeArea` in `difftest/textlibs_diff.py`. A child is a
number: below 1000 an Element whose tag is `e<n>`, otherwise the int `n` (not an Element). -/

namespace PyLean.TextLibs.Etree

open Lean PyLean PyLean.Diff
open PyLean.RangeSlice (Slice)


def nats (j : Json) : Except String (List Nat) := do (← j.getArr?).toList.mapM Json.getNat?

def optInt (j : Json) : Except String (Option Int) :=
  match j with
  | .null => .ok none
  | v => some <$> v.getInt?

def getSlice (j : Json) : Except String Slice := do
  match (← (← field j "slice").getArr?).toList with
  | [a, b, c] => return { start := ← optInt a, stop := ← optInt b, step := ← optInt c }
  | _ => throw "slice"

/-- Effects a generator runs on the element at its first `__next__`. -/
def effOf : Nat → List Nat → List Nat
  | 1 => fun _ => []
  | 2 => fun l => l ++ [50]
  | 3 => fun l => l.dropLast
  | _ => id

def getArg (j : Json) : Except String (Arg Nat) := do
  let a ← field j "arg"
  let xs ← nats (← field a "xs")
  match ← getStr a "kind" with
  | "seq" => return .seq xs
  | "iter" =>
    let stop := if (← getBool a "raise") then some (.valueError "boom") else none
    return .iter xs stop (effOf (← getNat a "eff"))
  | _ => return .notIter "int"

def encOut (o : Out Nat) : Json :=
  Json.mkObj [("ok", Json.mkObj [("kids", toJson o.1), ("out", encPy (fun (_ : Unit) => Json.null) o.2)])]


/-! ### `etree.path.*`: ElementPath and the C find methods -/

def strJ (s : S) : Json := toJson s

def wildJ (tag : S) : Json :=
  let vars : List (String × Json) :=
    if tag = lit "{*}*" ∨ tag = lit "{}*" then []
    else if tag.take 3 = lit "{*}" then [("tag", strJ (tag.drop 3)), ("suffix", strJ (tag.drop 2))]
    else [("ns", strJ (tag.take (tag.length - 1)))]
  Json.arr #[toJson "_prepare_tag", toJson "select", Json.mkObj vars]

def selJ : Sel → Json
  | .child t => Json.arr #[toJson "prepare_child", toJson "select", Json.mkObj [("tag", strJ t)]]
  | .childW t => Json.arr #[toJson "prepare_child", toJson "select", Json.mkObj [("select_tag", wildJ t)]]
  | .star => Json.arr #[toJson "prepare_star", toJson "select", Json.mkObj []]
  | .self => Json.arr #[toJson "prepare_self", toJson "select", Json.mkObj []]
  | .parent => Json.arr #[toJson "prepare_parent", toJson "select", Json.mkObj []]
  | .desc t => Json.arr #[toJson "prepare_descendant", toJson "select", Json.mkObj [("tag", strJ t)]]
  | .descW t => Json.arr #[toJson "prepare_descendant", toJson "select", Json.mkObj [("select_tag", wildJ t)]]
  | .attrHas k => Json.arr #[toJson "prepare_predicate", toJson "select", Json.mkObj [("key", strJ k)]]
  | .attrEq k v neg => Json.arr #[toJson "prepare_predicate", toJson (if neg then "select_negated" else "select"),
      Json.mkObj [("key", strJ k), ("value", strJ v)]]
  | .hasChild t => Json.arr #[toJson "prepare_predicate", toJson "select", Json.mkObj [("tag", strJ t)]]
  | .textEq t v neg => Json.arr #[toJson "prepare_predicate", toJson (if neg then "select_negated" else "select"),
      Json.mkObj (if t = [] then [("value", strJ v)] else [("tag", strJ t), ("value", strJ v)])]
  | .index i => Json.arr #[toJson "prepare_predicate", toJson "select", Json.mkObj [("index", toJson i)]]

partial def elemOf (j : Json) : Except String Elem := do
  let tag ← nats (← field j "tag")
  let text ← match ← field j "text" with
    | .null => pure none
    | v => some <$> nats v
  let kids ← (← (← field j "kids").getArr?).toList.mapM elemOf
  return .mk tag text kids

def elemJ (e : Elem) : Json := Json.arr #[strJ e.tag, match e.text with | some x => strJ x | none => Json.null]

def nsOf (j : Json) : Except String (Option (List (S × S))) := do
  match ← field j "ns" with
  | .null => return none
  | v => some <$> (← v.getArr?).toList.mapM fun kv => do
      match (← kv.getArr?).toList with
      | [k, x] => return (← nats k, ← nats x)
      | _ => throw "ns"

def runnable : IterOut → Bool
  | .none => true
  | .gen sels => (runSels sels ([], none)).isSome

def pathRun (fn : String) (j : Json) : Except String Json := do
  let path ← nats (← field j "path")
  let ns ← nsOf j
  let c := (← getStr j "impl") == "c"
  let compiled := iterfindPath path (ns.getD [])
  if fn == "etreepath.iterfind" then
    return encPy (fun (o : IterOut) => match o with
      | .none => Json.mkObj [("none", true)]
      | .gen sels => Json.mkObj [("sels", Json.arr (sels.map selJ).toArray)]) compiled
  let skip := match compiled with | .ok o => !runnable o | .error _ => false
  -- the C fast path never compiles, so only skip when ElementPath would run
  let viaC := c && !(checkpath path || ns.isSome)
  if skip && !viaC then return Json.mkObj [("ok", Json.mkObj [("skip", true)])]
  let root ← elemOf (← field j "tree")
  let dflt ← match j.getObjVal? "dflt" with
    | .ok .null | .error _ => pure none
    | .ok v => some <$> nats v
  let orSkip {β : Type} (enc : β → Json) : Option (Py β) → Json
    | some r => encPy enc r
    | none => Json.mkObj [("ok", Json.mkObj [("skip", true)])]
  match fn with
  | "etreepath.findall" =>
    return orSkip (fun (r : List Elem) => Json.arr (r.map elemJ).toArray)
      (if c then findallC root path ns else findallPy root path (ns.getD []))
  | "etreepath.find" =>
    return orSkip (fun (r : Option Elem) => match r with | some e => elemJ e | none => Json.null)
      (if c then findC root path ns else findPy root path (ns.getD []))
  | "etreepath.findtext" =>
    return orSkip (fun (r : Option S) => match r with | some x => strJ x | none => Json.null)
      (if c then findtextC root path dflt ns else findtextPy root path dflt (ns.getD []))
  | _ => throw s!"unknown fn {fn}"

def run (fn : String) (j : Json) : Except String Json := do
  let kids ← nats (← field j "kids")
  let c := (← getStr j "impl") == "c"
  let isIdx := (j.getObjVal? "idx").isOk
  match fn with
  | "etree.get" =>
    if isIdx then
      let i ← getInt j "idx"
      return encPy (fun (n : Nat) => toJson n) (if c then getItemC kids i else getItemPy kids i)
    else
      let s ← getSlice j
      return encPy (fun (r : List Nat) => toJson r) (if c then getSliceC kids s else getSlicePy kids s)
  | "etree.set" =>
    if isIdx then
      let i ← getInt j "idx"
      let x ← getNat j "obj"
      return encOut (if c then assItemC caseTy kids i (some x) else setItemPy caseTy kids i x)
    else
      let s ← getSlice j
      let a ← getArg j
      return encOut (if c then setSliceC caseTy kids s a else setSlicePy caseTy kids s a)
  | "etree.append" => return encOut ((if c then appendC else appendPy) caseTy kids (← getNat j "obj"))
  | "etree.insert" =>
    let i ← getInt j "idx"
    let x ← getNat j "obj"
    return encOut (if c then insertC caseTy kids i x else insertPy caseTy kids i x)
  | "etree.extend" =>
    let a ← getArg j
    return encOut (if c then extendC caseTy kids a else extendPy caseTy kids a)
  | "etree.del" =>
    if isIdx then
      let i ← getInt j "idx"
      return encOut (if c then assItemC caseTy kids i none else delItemPy kids i)
    else
      let s ← getSlice j
      return encOut (if c then delSliceC kids s else delSlicePy kids s)
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Etree
