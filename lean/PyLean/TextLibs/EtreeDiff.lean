import PyLean.DiffCore
import PyLean.TextLibs.EtreeModel
import PyLean.TextLibs.EtreePath
import PyLean.TextLibs.EtreeWriters
import PyLean.TextLibs.EtreeAttrib
import PyLean.TextLibs.EtreeRemove
import PyLean.TextLibs.EtreeCopy

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

/-! ### `etreeattrib.run`: a script of attrib operations on one C Element -/

def pairsOf (j : Json) : Except String (List (S × S)) := do
  (← j.getArr?).toList.mapM fun kv => do
    match (← kv.getArr?).toList with
    | [k, v] => return (← nats k, ← nats v)
    | _ => throw "pair"

def aobjOf (j : Json) : Except String AObj := do
  match ← getStr j "kind" with
  | "dict" => return .dict (← pairsOf (← field j "items"))
  | "frozen" => return .frozen (← pairsOf (← field j "items"))
  | _ => return .other (← getStr j "type")

def pairsJ (l : List (S × S)) : Json := Json.arr (l.map fun (k, v) => Json.arr #[strJ k, strJ v]).toArray

def aobjJ : AObj → Json
  | .dict i => Json.arr #[toJson "dict", pairsJ i]
  | .frozen i => Json.arr #[toJson "frozendict", pairsJ i]
  | .other t => Json.arr #[toJson t]

def attribStep (s : Slot) (op : Json) : Except String (Slot × Json) := do
  match ← getStr op "op" with
  | "setattr" =>
    match setAttribC s (← aobjOf (← field op "v")) with
    | .ok s' => return (s', encPy (fun (_ : Unit) => Json.null) (.ok ()))
    | .error e => return (s, encPy (fun (_ : Unit) => Json.null) (.error e))
  | "getattr" => let (s', a) := getAttribC s; return (s', encPy aobjJ (.ok a))
  | "get" =>
    let d ← match op.getObjVal? "d" with | .ok .null | .error _ => pure none | .ok v => some <$> nats v
    return (s, encPy (fun (r : Option S) => match r with | some x => strJ x | none => Json.null)
      (getC s (← nats (← field op "k")) d))
  | "set" =>
    let (s', r) := setC s (← nats (← field op "k")) (← nats (← field op "v"))
    return (s', encPy (fun (_ : Unit) => Json.null) r)
  | "items" => return (s, encPy pairsJ (itemsC s))
  | "keys" => return (s, encPy (fun (l : List (S × S)) => Json.arr (l.map (strJ ·.1)).toArray) (itemsC s))
  | "setstate" =>
    let attrib ← match op.getObjVal? "attrib" with | .ok v => some <$> aobjOf v | .error _ => pure none
    let children ← match op.getObjVal? "children" with
      | .ok v => match ← v.getStr? with
        | "ok" => pure (some ChildArg.ok) | "notlist" => pure (some .notList) | _ => pure (some .badItem)
      | .error _ => pure none
    let (s', r) := setstateC s ⟨← getBool op "tag", attrib, children, ← getBool op "extra"⟩
    return (s', encPy (fun (_ : Unit) => Json.null) r)
  | o => throw s!"op {o}"

def attribRun (j : Json) : Except String Json := do
  let init ← match ← field j "init" with | .null => pure none | v => some <$> aobjOf v
  match initC init with
  | .error e => return encPy (fun (_ : Unit) => Json.null) (.error e)
  | .ok s0 =>
    let mut s := s0
    let mut out : Array Json := #[]
    for op in (← (← field j "ops").getArr?) do
      let (s', r) ← attribStep s op
      s := s'
      out := out.push r
    return Json.mkObj [("ok", Json.arr out)]

/-! ### `etree.remove`: a scripted `__eq__` -/

def removeEff (eff : Nat) (k : Nat) (l : List Nat) : List Nat :=
  match eff with
  | 1 => l ++ [50 + k]
  | 2 => l.drop 1
  | 3 => (50 + k) :: l
  | 4 => []
  | _ => l

def scriptCmp (script : List (String × Nat)) : Cmp Nat Nat := fun k l _ _ =>
  let (res, eff) := script.getD k ("f", 0)
  let l := removeEff eff k l
  let r : Py Bool :=
    if res == "raiseV" then .error (.valueError "eq")
    else if res == "raiseK" then .error (.keyError "'eq'")
    else .ok (res == "t")
  (r, l, k + 1)

def removeRun (j : Json) : Except String Json := do
  let kids ← nats (← field j "kids")
  let x ← getNat j "x"
  let script ← (← (← field j "script").getArr?).toList.mapM fun e => do
    match (← e.getArr?).toList with
    | [r, f] => return (← r.getStr?, ← f.getNat?)
    | _ => throw "script"
  let c := (← getStr j "impl") == "c"
  let o := (if c then removeC else removePy) (scriptCmp script) 1000 0 kids x
  return Json.mkObj [("ok", Json.mkObj [("kids", toJson o.1), ("out", encPy (fun (_ : Unit) => Json.null) o.2)])]

/-! ### `etreecopy.run`: copy, then set on the copy or the original -/

def copyRun (j : Json) : Except String Json := do
  let c := (← getStr j "impl") == "c"
  let items ← pairsOf (← field j "attrib")
  let sub ← getBool j "sub"
  -- `Element(tag, attrib)`: C keeps no dict for an empty attrib; the twin always has one
  let (h, e) : Heap × CElem :=
    if c && items = [] then ([], ⟨lit "r", sub, none⟩) else ([items], ⟨lit "r", sub, some 0⟩)
  let (h, cp) := (if c then copyC else copyPy) h e
  let k ← nats (← field j "k")
  let v ← nats (← field j "v")
  let onCopy ← getBool j "oncopy"
  let (h, e, cp) := if onCopy then let (h, cp) := setCE h cp k v; (h, e, cp) else let (h, e) := setCE h e k v; (h, e, cp)
  return Json.mkObj [("ok", Json.mkObj [("orig", pairsJ (attrsOf h e)), ("copy", pairsJ (attrsOf h cp)),
    ("sub", toJson cp.sub)])]

def run (fn : String) (j : Json) : Except String Json := do
  if fn == "etree.remove" then return ← removeRun j
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
