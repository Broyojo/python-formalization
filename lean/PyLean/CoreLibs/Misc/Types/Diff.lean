import PyLean.CoreLibs.Misc.Common
import PyLean.CoreLibs.Misc.Types.Model

/-! `misc.types` cases. Objects are data (`Ob`); metaclass 0 is `type`, 1 is `M1(type)`, 2 is
`M2(M1)`, 3 is `M3(type)`, 4 is `M4(M1, M3)`. `Ops` over this data is `dOps`; the Python side builds
the matching real classes. -/

namespace PyLean.CoreLibs.Misc.Types

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Misc

inductive Ob where
  | mta (i : Nat)
  | cls (i : Nat)
  | plain
  | ent (l : List Ob)
  | bad
  | boom
  | fnMeta
  | prepMeta
  deriving Repr, Inhabited

/-- `metas[a]` subclass of `metas[b]`. -/
def metaSub (a b : Nat) : Bool :=
  a == b || b == 0 ||
    match a, b with
    | 2, 1 | 4, 1 | 4, 3 => true
    | _, _ => false

/-- Classes of the objects that are not classes: 100 is `MiscPlain`, 101-103 its subclasses
`MiscE`, `MiscB`, `MiscR`, which define `__mro_entries__`. None is a metaclass. -/
def typeOfOb : Ob → Ob
  | .mta _ => .mta 0
  | .cls i => if i ≥ 100 then .mta 0 else .mta i
  | .ent _ => .cls 101
  | .bad => .cls 102
  | .boom => .cls 103
  | _ => .cls 100

def plainName : Nat → String
  | 101 => "MiscE"
  | 102 => "MiscB"
  | 103 => "MiscR"
  | _ => "MiscPlain"

def dupBase : List Ob → Option Nat
  | [] => none
  | .cls i :: rest =>
    if rest.any (fun o => match o with
        | .cls j => i == j
        | _ => false) then some i
    else dupBase rest
  | _ :: rest => dupBase rest

def issubOb (a b : Ob) : Py Bool :=
  match a, b with
  | .mta x, .mta y => .ok (metaSub x y)
  | .mta _, .cls _ | .cls _, .mta _ => .ok false
  | .cls x, .cls y => .ok (x == y || (y == 100 && x ≥ 100))
  | _, _ => .error (.typeError "issubclass() arg 1 must be a class")

def nsPrep (kwNames : List String) (cls : String) : Json :=
  Json.mkObj [("prep", jStr cls), ("kw", toJson kwNames)]

def metaName : Nat → String
  | 1 => "M1"
  | 2 => "M2"
  | 3 => "M3"
  | 4 => "M4"
  | _ => "type"

partial def obJson : Ob → Json
  | .mta i => Json.arr #["m", toJson i]
  | .cls i => Json.arr #["c", toJson i]
  | .plain => Json.arr #["o"]
  | .ent _ => Json.arr #["e"]
  | .bad => Json.arr #["b"]
  | .boom => Json.arr #["r"]
  | .fnMeta => Json.arr #["f"]
  | .prepMeta => Json.arr #["p"]

/-- The namespace: the keys a `__prepare__` put there, plus body and `__orig_bases__` markers. -/
abbrev Ns := List String

def sortStrs (l : List String) : List String :=
  (l.toArray.qsort (fun a b => a < b)).toList

def dOps : Ops Ob Ns Json where
  isType := fun o => match o with
    | .mta _ | .cls _ => true
    | _ => false
  typeOf := typeOfOb
  issubclass := issubOb
  mroEntries := fun o => match o with
    | .ent l => some (fun _ => .ok (some l))
    | .bad => some (fun _ => .ok none)
    | .boom => some (fun _ => .error (.named "RuntimeError" "entries failed"))
    | _ => none
  typeObj := .mta 0
  prepare := fun m => match m with
    | .mta 0 | .mta 3 => some (fun _ _ _ => .ok [])
    | .mta i => some (fun _ _ kw => .ok (["prep:" ++ metaName i] ++ sortStrs (kw.map (·.1))))
    | .prepMeta => some (fun _ _ kw => .ok (["prep:P"] ++ sortStrs (kw.map (·.1))))
    | .cls _ => some (fun _ _ _ => .ok [])
    | _ => none
  emptyNs := []
  setOrig := fun ns _ => .ok (ns ++ ["__orig_bases__"])
  callMeta := fun m name bases ns kw =>
    match m, kw with
    | .cls i, _ => .error (.typeError s!"{plainName i}() takes no arguments")
    | .mta _, _ =>
      match dupBase bases with
      | some i => .error (.typeError s!"duplicate base class C{i}")
      | none =>
      match m, kw with
      | .mta 0, _ :: _ =>
        .error (.typeError s!"{name}.__init_subclass__() takes no keyword arguments")
      | _, _ =>
      .ok (Json.arr #[obJson m, jStr name, jList obJson bases, toJson (sortStrs ns),
        toJson (sortStrs (kw.map (·.1)))])
    | _, _ =>
      .ok (Json.arr #[obJson m, jStr name, jList obJson bases, toJson (sortStrs ns),
        toJson (sortStrs (kw.map (·.1)))])

partial def parseOb (j : Json) : Except String Ob := do
  match ← jStrAt j 0 with
  | "m" => return .mta (← jNatAt j 1)
  | "c" => return .cls (← jNatAt j 1)
  | "o" => return .plain
  | "e" => return .ent (← (← jArr (← jGetI j 1)).mapM parseOb)
  | "b" => return .bad
  | "r" => return .boom
  | "f" => return .fnMeta
  | "p" => return .prepMeta
  | o => throw s!"bad ob {o}"

def parseObs (j : Json) : Except String (List Ob) := do (← jArr j).mapM parseOb

def parseKwds (j : Json) : Except String (Option (List (String × Ob))) :=
  match j with
  | .null => .ok none
  | v => do
    let items ← jArr v
    return some (← items.mapM (fun kv => do return ((← jStrAt kv 0), (← parseOb (← jGetI kv 1)))))

def jResolved (r : Option (List Ob)) : Json :=
  match r with
  | none => Json.arr #["same"]
  | some l => Json.arr #["new", jList obJson l]

/-- A descriptor function of the difftest: `docs[i]` and `abstract[i]`. -/
def dFn : FnOps Nat where
  docOf := fun i => match i with
    | 1 => some "d1"
    | 2 => some ""
    | 3 => some "a"
    | _ => none
  abstractOf := fun i => i == 3
  noneDoc := some "The type of the None singleton."

def jOptS : Option String → Json
  | some s => jStr s
  | none => Json.null

def dcaDump (d : DCA Nat) : Json :=
  Json.arr #[jOpt (fun (n : Nat) => toJson n) d.fget, jOpt (fun (n : Nat) => toJson n) d.fset,
    jOpt (fun (n : Nat) => toJson n) d.fdel, jOptS d.doc, jBool d.overwriteDoc, jBool d.isAbstract]

def jOptNat (j : Json) : Except String (Option Nat) :=
  match j with
  | .null => .ok none
  | v => some <$> v.getNat?

def jOptStr (j : Json) : Except String (Option String) :=
  match j with
  | .null => .ok none
  | v => some <$> v.getStr?

def runDca (j : Json) : Except String Json := do
  let i ← field j "init"
  let mut d : DCA Nat := DCA.init dFn (← jOptNat (← jGetI i 0)) (← jOptNat (← jGetI i 1))
    (← jOptNat (← jGetI i 2)) (← jOptStr (← jGetI i 3))
  let mut out : Array Json := #[dcaDump d]
  for op in (← jArr (← field j "ops")) do
    match ← jStrAt op 0 with
    | "get" =>
      let inst ← jBoolAt op 1
      let r : Py (GetRes Nat Json) := d.get (fun f _ => .ok (Json.arr #["got", toJson f]))
        (if inst then some () else none)
      out := out.push (encR (fun x => match x with
        | .self => jStr "self"
        | .value v => v) r)
    | "set" =>
      out := out.push (encR jUnit (d.set (fun _ _ (_ : Unit) => .ok ()) () ()))
    | "delete" =>
      out := out.push (encR jUnit (d.delete (fun _ _ => .ok ()) ()))
    | "getter" => d := d.getter dFn (← jNatAt op 1); out := out.push (dcaDump d)
    | "setter" => d := d.setter dFn (← jNatAt op 1); out := out.push (dcaDump d)
    | "deleter" => d := d.deleter dFn (← jNatAt op 1); out := out.push (dcaDump d)
    | o => throw s!"bad op {o}"
  return Json.mkObj [("ok", Json.arr out)]

/-! A generator with a list of values to yield, for `_GeneratorWrapper`. -/

structure MiniGen where
  items : List Int
  started : Bool
  closed : Bool
  deriving Repr

def stopIter : PyExc := .stopIteration

def miniNext (g : MiniGen) : MiniGen × Py Int :=
  let g' := { g with started := true }
  if g.closed then (g', .error stopIter)
  else match g.items with
    | [] => ({ g' with closed := true }, .error stopIter)
    | a :: rest => ({ g' with items := rest }, .ok a)

def miniObj : GenObj MiniGen Int where
  send := fun g v =>
    if !g.started && !g.closed && v != 0 then
      (g, .error (.typeError "can't send non-None value to a just-started generator"))
    else miniNext g
  throw := fun g _ _ =>
    ({ g with closed := true, started := true }, .error (.valueError "thrown"))
  close := fun g => ({ g with closed := true, started := true }, .ok 0)
  next := miniNext
  giCode := fun _ => .ok 1
  giFrame := fun g => .ok (if g.closed then 0 else 1)
  giRunning := fun _ => .ok 0
  giYieldfrom := fun _ => .ok 0
  giSuspended := fun g => .ok (if g.started && !g.closed then 1 else 0)
  giState := fun g => .ok (if g.closed then "GEN_CLOSED" else if g.started then "GEN_SUSPENDED" else "GEN_CREATED")

def runWrapper (j : Json) : Except String Json := do
  let items ← (field j "items") >>= jIntList
  let isgen ← getBool j "isgen"
  let mut w : Wrapper MiniGen :=
    Wrapper.init { items, started := false, closed := false } isgen (some "g") (some "g")
  let mut out : Array Json := #[]
  for op in (← jArr (← field j "ops")) do
    match ← jStrAt op 0 with
    | "next" =>
      let (w', r) := w.next miniObj
      w := w'
      out := out.push (encR jInt r)
    | "send" =>
      let (w', r) := w.send miniObj (← jIntAt op 1)
      w := w'
      out := out.push (encR jInt r)
    | "throw" =>
      let (w', r) := w.throw miniObj 0 []
      w := w'
      out := out.push (encR jInt r)
    | "close" =>
      let (w', r) := w.close miniObj
      w := w'
      out := out.push (encR jInt r)
    | "attrs" =>
      out := out.push (Json.arr #[encR jInt (w.giCode miniObj), encR jInt (w.giFrame miniObj),
        encR jInt (w.giRunning miniObj), encR jInt (w.giYieldfrom miniObj),
        encR jInt (w.giSuspended miniObj), jOptS w.name, jOptS w.qualname,
        encR (fun s => toJson s) (w.giState miniObj), encR (fun s => toJson s) (w.crState miniObj)])
    | "iter" =>
      out := out.push (jStr (match w.iter with
        | .inl _ => "wrapped"
        | .inr _ => "self"))
    | o => throw s!"bad op {o}"
  return Json.mkObj [("ok", Json.arr out)]

/-- The flags of each difftest function, and what calling it returns. -/
def coKind : String → CoFunc × CoValue
  | "notcallable" => (⟨false, false, 0⟩, ⟨false, false, 0, false, false⟩)
  | "gen" => (⟨true, true, 0x23⟩, ⟨false, true, 0x123, true, false⟩)
  | "async" => (⟨true, true, 0x83⟩, ⟨true, false, 0, false, true⟩)
  | "itercoro" => (⟨true, true, 0x123⟩, ⟨false, true, 0x123, true, false⟩)
  | "plain" => (⟨true, true, 0x3⟩, ⟨false, false, 0, false, false⟩)
  | "callable_gen" => (⟨true, false, 0⟩, ⟨false, true, 0x23, true, false⟩)
  | "ret_abc_gen" => (⟨true, true, 0x3⟩, ⟨false, false, 0, true, false⟩)
  | "ret_coro" => (⟨true, true, 0x3⟩, ⟨true, false, 0, false, true⟩)
  | "ret_itercoro" => (⟨true, true, 0x3⟩, ⟨false, true, 0x123, true, false⟩)
  | "ret_abc_both" => (⟨true, true, 0x3⟩, ⟨false, false, 0, true, true⟩)
  | _ => (⟨false, false, 0⟩, ⟨false, false, 0, false, false⟩)

def runCoroutine (j : Json) : Except String Json := do
  let (f, c) := coKind (← getStr j "kind")
  let enc (r : CoResult) : Json := match r with
    | .same => Json.arr #["same"]
    | .flagged fl => Json.arr #["flagged", toJson (fl &&& 0x100 != 0)]
    | .wrapped => Json.arr #["wrapped", jStr (if wrappedWraps c then "wrap" else "pass")]
  return Json.mkObj [("ok", encR enc (coroutine f))]

def runCase (j : Json) : Except String Json := do
  match ← getStr j "k" with
  | "resolve" =>
    return Json.mkObj [("ok", encR jResolved (resolveBases dOps (← parseObs (← field j "bases"))))]
  | "update" =>
    return Json.mkObj [("ok", encR jResolved (updateBases dOps (← parseObs (← field j "bases"))))]
  | "calc" =>
    let r := calculateMeta dOps (← parseOb (← field j "meta")) (← parseObs (← field j "bases"))
    return Json.mkObj [("ok", encR obJson r)]
  | "prepare" =>
    let r := prepareClass dOps (← getStr j "name") (← parseObs (← field j "bases"))
      (← parseKwds (← field j "kwds"))
    return Json.mkObj [("ok", encR (fun t => Json.arr #[obJson t.1, toJson (sortStrs t.2.1),
      toJson (sortStrs (t.2.2.map (·.1)))]) r)]
  | "new" =>
    let body : Option (Ns → Py Ns) :=
      if (← getBool j "body") then some (fun ns => .ok (ns ++ ["body"])) else none
    let r := newClass dOps (← getStr j "name") (← parseObs (← field j "bases"))
      (← parseKwds (← field j "kwds")) body
    return Json.mkObj [("ok", encR id r)]
  | "orig" =>
    let c : ClsLike Int := {
      typeName := ← getStr j "typeName"
      hasDict := ← getBool j "hasDict"
      origBases := ← getOptInt j "orig"
      bases := ← getOptInt j "bases" }
    return Json.mkObj [("ok", encR jInt (getOriginalBases c))]
  | "dca" => runDca j
  | "wrapper" => runWrapper j
  | "coroutine" => runCoroutine j
  | k => throw s!"bad kind {k}"

end PyLean.CoreLibs.Misc.Types
