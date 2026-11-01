import PyLean.CoreLibs.Misc.Common
import PyLean.CoreLibs.Misc.Weakref.Model

/-! `misc.weakref` cases: a script over one object, with `["kill", id]` dropping the last strong
reference to an object. Values are `["o", id]` or `["i", n]`. A script step that names a dead object
is skipped on both sides. -/

namespace PyLean.CoreLibs.Misc.Weakref

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Misc

def jPV : PV → Json
  | .obj i => Json.arr #["o", toJson i]
  | .int n => Json.arr #["i", jInt n]

def pPV (j : Json) : Except String PV := do
  match ← jStrAt j 0 with
  | "o" => return .obj (← jNatAt j 1)
  | "i" => return .int (← jIntAt j 1)
  | o => throw s!"bad pv {o}"

def deadPV (w : World) : PV → Bool
  | .obj i => w.contains i
  | .int _ => false

def rK (k : String) : String := s!"'{k}'"

def pItems (j : Json) : Except String (List (String × PV)) := do
  (← jArr j).mapM (fun kv => do return ((← jStrAt kv 0), (← pPV (← jGetI kv 1))))

def pOptItems (j : Json) : Except String (Option (List (String × PV))) :=
  match j with
  | .null => .ok none
  | v => some <$> pItems v

def jItems (l : List (String × PV)) : Json :=
  jList (fun kv => Json.arr #[jStr kv.1, jPV kv.2]) l

def wvdDump (w : World) (d : WVD String) : Json := jItems (WVD.liveItems w d)

def jKRefs (w : World) (l : List (KRef String)) : Json :=
  jList (fun r => jOpt jPV (deref w r.ob)) l

def anyDead (w : World) (l : List (String × PV)) : Bool := l.any (fun kv => deadPV w kv.2)

/-- Exceptions and results of the script steps. -/
def wvdStep (w : World) (d : WVD String) (op : Json) : Except String (World × WVD String × Json) := do
  let name ← jStrAt op 0
  match name with
  | "set" =>
    let v ← pPV (← jGetI op 2)
    if deadPV w v then return (w, d, jStr "skip")
    match d.setitem (← jStrAt op 1) v with
    | .ok d => return (w, d, encR jUnit (.ok ()))
    | .error e => return (w, d, encR jUnit (.error e))
  | "get_" => return (w, d, encR jPV (d.getitem rK w (← jStrAt op 1)))
  | "del" =>
    match d.delitem rK (← jStrAt op 1) with
    | .ok d => return (w, d, encR jUnit (.ok ()))
    | .error e => return (w, d, encR jUnit (.error e))
  | "len" => return (w, d, toJson d.len)
  | "in" => return (w, d, jBool (d.contains w (← jStrAt op 1)))
  | "repr" => return (w, d, jStr (WVD.repr "WeakValueDictionary" "ADDR"))
  | "copy" => return (w, d, encR (wvdDump w) (d.copy w))
  | "deepcopy" => return (w, d, encR (wvdDump w) (d.deepcopy id w))
  | "get" =>
    let v ← pPV (← jGetI op 2)
    if deadPV w v then return (w, d, jStr "skip")
    return (w, d, jPV (d.get w (← jStrAt op 1) v))
  | "items" => return (w, d, jItems (d.items w))
  | "keys" => return (w, d, toJson (d.keys w))
  | "iter" => return (w, d, toJson (d.keys w))
  | "irefs" => return (w, d, jKRefs w d.itervaluerefs)
  | "vrefs" => return (w, d, jKRefs w d.valuerefs)
  | "values" => return (w, d, jList jPV (d.values w))
  | "popitem" =>
    let (d, r) := d.popitem w
    return (w, d, encR (fun kv => Json.arr #[jStr kv.1, jPV kv.2]) r)
  | "pop" =>
    let args ← (← jArr (← jGetI op 2)).mapM pPV
    if args.any (deadPV w) then return (w, d, jStr "skip")
    let (d, r) := d.pop rK w (← jStrAt op 1) args
    return (w, d, encR jPV r)
  | "setdefault" =>
    let v ← pPV (← jGetI op 2)
    if deadPV w v then return (w, d, jStr "skip")
    let (d, r) := d.setdefault w (← jStrAt op 1) v
    return (w, d, encR jPV r)
  | "update" =>
    let items ← pOptItems (← jGetI op 1)
    if anyDead w (items.getD []) then return (w, d, jStr "skip")
    let (d, r) := d.update items
    return (w, d, encR jUnit r)
  | "update_pairs" =>
    let items ← pItems (← jGetI op 1)
    if anyDead w items then return (w, d, jStr "skip")
    let (d, r) := d.updatePairs items
    return (w, d, encR jUnit r)
  | "ior" =>
    let items ← pItems (← jGetI op 1)
    if anyDead w items then return (w, d, jStr "skip")
    let (d, r) := d.ior items
    return (w, d, encR jUnit r)
  | "or" | "ror" =>
    let items ← pOptItems (← jGetI op 1)
    if anyDead w (items.getD []) then return (w, d, jStr "skip")
    let r := if name == "or" then d.or_ w items else d.ror w items
    match r with
    | none => return (w, d, jStr "NotImplemented")
    | some r => return (w, d, encR (wvdDump w) r)
  | "kill" =>
    let i ← jNatAt op 1
    return (i :: w, d.onDeath i, Json.null)
  | o => throw s!"bad op {o}"

def runWvd (j : Json) : Except String Json := do
  let eager ← getBool j "eager"
  let init ← pItems (← field j "init")
  match WVD.init init with
  | .error e => return Json.mkObj [("ok", Json.arr #[encR jUnit (.error e)])]
  | .ok d0 =>
    let mut d : WVD String := { d0 with eager }
    let mut w : World := []
    let mut out : Array Json := #[]
    for op in (← jArr (← field j "ops")) do
      let (w', d', r) ← wvdStep w d op
      w := w'
      d := d'
      out := out.push r
    let raw := jList (fun kv => Json.arr #[jStr kv.1, jOpt jPV (deref w kv.2.ob)]) d.data
    return Json.mkObj [("ok", Json.arr (out.push raw))]

/-! `WeakKeyDictionary` -/

def pKItems (j : Json) : Except String (List (PV × Int)) := do
  (← jArr j).mapM (fun kv => do return ((← pPV (← jGetI kv 0)), (← jIntAt kv 1)))

def pOptKItems (j : Json) : Except String (Option (List (PV × Int))) :=
  match j with
  | .null => .ok none
  | v => some <$> pKItems v

def jKItems (l : List (PV × Int)) : Json :=
  jList (fun kv => Json.arr #[jPV kv.1, jInt kv.2]) l

def wkdDump (w : World) (d : WKD Int) : Json := jKItems (WKD.liveItems w d)

def anyDeadK (w : World) (l : List (PV × Int)) : Bool := l.any (fun kv => deadPV w kv.1)

def wkdStep (q : Eqv) (w : World) (d : WKD Int) (op : Json) :
    Except String (World × WKD Int × Json) := do
  let name ← jStrAt op 0
  let keyDead : Bool ← (do
    match name with
    | "set" | "get_" | "del" | "get" | "in" | "pop" | "setdefault" =>
      return deadPV w (← pPV (← jGetI op 1))
    | _ => return false)
  if keyDead then return (w, d, jStr "skip")
  match name with
  | "set" =>
    match d.setitem q w (← pPV (← jGetI op 1)) (← jIntAt op 2) with
    | .ok d => return (w, d, encR jUnit (.ok ()))
    | .error e => return (w, d, encR jUnit (.error e))
  | "get_" => return (w, d, encR jInt (d.getitem q w (← pPV (← jGetI op 1))))
  | "del" =>
    match d.delitem q w (← pPV (← jGetI op 1)) with
    | .ok d => return (w, d, encR jUnit (.ok ()))
    | .error e => return (w, d, encR jUnit (.error e))
  | "len" => return (w, d, toJson d.len)
  | "repr" => return (w, d, jStr (WKD.repr "WeakKeyDictionary" "ADDR"))
  | "copy" => return (w, d, encR (wkdDump w) (d.copy q w))
  | "deepcopy" => return (w, d, encR (wkdDump w) (d.deepcopy id q w))
  | "get" => return (w, d, encR jInt (d.get q w (← pPV (← jGetI op 1)) (← jIntAt op 2)))
  | "in" => return (w, d, jBool (d.contains q w (← pPV (← jGetI op 1))))
  | "items" => return (w, d, jKItems (d.items w))
  | "keys" => return (w, d, jList jPV (d.keys w))
  | "iter" => return (w, d, jList jPV (d.keys w))
  | "values" => return (w, d, jList jInt (d.values w))
  | "krefs" => return (w, d, jList (fun r => jOpt jPV (deref w r.ob)) d.keyrefs)
  | "popitem" =>
    let (d, r) := d.popitem w
    return (w, d, encR (fun kv => Json.arr #[jPV kv.1, jInt kv.2]) r)
  | "pop" =>
    let args ← jIntList (← jGetI op 2)
    let (d, r) := d.pop q w (← pPV (← jGetI op 1)) args
    return (w, d, encR jInt r)
  | "setdefault" =>
    let (d, r) := d.setdefault q w (← pPV (← jGetI op 1)) (← jIntAt op 2)
    return (w, d, encR jInt r)
  | "update" =>
    let items ← pOptKItems (← jGetI op 1)
    if anyDeadK w (items.getD []) then return (w, d, jStr "skip")
    let (d, r) := d.update q w items (← jBoolAt op 2)
    return (w, d, encR jUnit r)
  | "update_pairs" =>
    let items ← pKItems (← jGetI op 1)
    if anyDeadK w items then return (w, d, jStr "skip")
    let (d, r) := d.updatePairs q w items
    return (w, d, encR jUnit r)
  | "ior" =>
    let items ← pKItems (← jGetI op 1)
    if anyDeadK w items then return (w, d, jStr "skip")
    let (d, r) := d.ior q w items
    return (w, d, encR jUnit r)
  | "or" | "ror" =>
    let items ← pOptKItems (← jGetI op 1)
    if anyDeadK w (items.getD []) then return (w, d, jStr "skip")
    let r := if name == "or" then d.or_ q w items else d.ror q w items
    match r with
    | none => return (w, d, jStr "NotImplemented")
    | some r => return (w, d, encR (wkdDump w) r)
  | "kill" =>
    let i ← jNatAt op 1
    return (i :: w, d.onDeath i, Json.null)
  | o => throw s!"bad op {o}"

def valsEq (vals : List Int) : Eqv := fun a b => vals.getD a 0 == vals.getD b 0

def runWkd (j : Json) : Except String Json := do
  let eager ← getBool j "eager"
  let vals ← (field j "vals") >>= jIntList
  let q := valsEq vals
  let init ← pKItems (← field j "init")
  match WKD.init q [] (some init) with
  | .error e => return Json.mkObj [("ok", Json.arr #[encR jUnit (.error e)])]
  | .ok d0 =>
    let mut d : WKD Int := { d0 with eager }
    let mut w : World := []
    let mut out : Array Json := #[]
    for op in (← jArr (← field j "ops")) do
      let (w', d', r) ← wkdStep q w d op
      w := w'
      d := d'
      out := out.push r
    let raw := jList (fun kv => Json.arr #[jOpt jPV (deref w kv.1.ob), jInt kv.2]) d.data
    return Json.mkObj [("ok", Json.arr (out.push raw))]

/-! `WeakMethod` and `KeyedRef` -/

instance : Inhabited WM := ⟨⟨0, 0, 0, false, false⟩⟩

def runWm (j : Json) : Except String Json := do
  let vals ← (field j "vals") >>= jIntList
  let q := valsEq vals
  let mut w : World := []
  let mut ms : Array WM := #[]
  let mut out : Array Json := #[]
  for op in (← jArr (← field j "ops")) do
    match ← jStrAt op 0 with
    | "new" =>
      let o ← jNatAt op 1
      let f ← jNatAt op 2
      if w.contains o || w.contains f then out := out.push (jStr "skip")
      else
        match WM.new ms.size (.bound o f) (← jBoolAt op 3) with
        | .ok m =>
          ms := ms.push m
          out := out.push (toJson m.id)
        | .error e => out := out.push (encR jUnit (.error e))
    | "bad" =>
      out := out.push (encR jUnit (match WM.new 0 (.other "<class 'int'>") false with
        | .ok _ => .ok ()
        | .error e => .error e))
    | "call" =>
      let i ← jNatAt op 1
      if h : i < ms.size then
        out := out.push (jOpt (fun p => Json.arr #[toJson p.1, toJson p.2]) (ms[i].call w))
      else out := out.push (jStr "skip")
    | "eq" | "ne" =>
      let i ← jNatAt op 1
      let k ← jNatAt op 2
      let isEq := (← jStrAt op 0) == "eq"
      if h : i < ms.size ∧ k < ms.size then
        have h1 := h.1
        have h2 := h.2
        let r := if isEq then ms[i].eq q w (some ms[k]) else ms[i].ne q w (some ms[k])
        out := out.push (jOpt jBool r)
      else out := out.push (jStr "skip")
    | "eqo" =>
      let i ← jNatAt op 1
      if h : i < ms.size then out := out.push (jOpt jBool (ms[i].eq q w none))
      else out := out.push (jStr "skip")
    | "alive" =>
      let i ← jNatAt op 1
      if h : i < ms.size then out := out.push (jBool ms[i].alive)
      else out := out.push (jStr "skip")
    | "kill" =>
      let i ← jNatAt op 1
      -- Weak-reference callbacks run newest first.
      let mut fired : List Nat := []
      let mut next : Array WM := ms
      for k in (List.range ms.size).reverse do
        let (m, cb) := (next[k]!).onDeath i
        next := next.set! k m
        if cb then fired := fired ++ [k]
      ms := next
      w := i :: w
      out := out.push (toJson fired)
    | o => throw s!"bad op {o}"
  return Json.mkObj [("ok", Json.arr out)]

def runKeyed (j : Json) : Except String Json := do
  let v ← pPV (← field j "v")
  match KRef.new v "k" with
  | .error e => return Json.mkObj [("ok", encR jUnit (.error e))]
  | .ok r =>
    let before := deref [] r.ob
    let dead : World := [r.ob]
    return Json.mkObj [("ok", Json.arr #[jStr r.key, jOpt jPV before, jOpt jPV (deref dead r.ob)])]

/-! `finalize` -/

inductive FS where
  | ret (v : Int)
  | boom
  | base
  | spawn (fid oid : Nat) (f : FS)
  deriving Repr, DecidableEq

partial def jFS : FS → Json
  | .ret v => Json.arr #["ret", jInt v]
  | .boom => Json.arr #["boom"]
  | .base => Json.arr #["base"]
  | .spawn a b f => Json.arr #["spawn", toJson a, toJson b, jFS f]

partial def pFS (j : Json) : Except String FS := do
  match ← jStrAt j 0 with
  | "ret" => return .ret (← jIntAt j 1)
  | "boom" => return .boom
  | "base" => return .base
  | "spawn" =>
    let a ← jNatAt j 1
    let b ← jNatAt j 2
    let f ← pFS (← jGetI j 3)
    return .spawn a b f
  | o => throw s!"bad fs {o}"

structure FW where
  log : List Json
  dead : World

def boomExc : PyExc := .valueError "boom"
def baseExc : PyExc := .named "KeyboardInterrupt" "base"

def runFS : Fin.RunF FW FS := fun f st s =>
  let s := { s with log := s.log ++ [Json.arr #["run", jFS f]] }
  match f with
  | .ret _ => (st, s, none)
  | .boom => (st, s, some (boomExc, true))
  | .base => (st, s, some (baseExc, false))
  | .spawn a b g =>
    if s.dead.contains b then (st, s, none)
    else
      match Fin.init st a (.obj b) g with
      | (st, _) => (st, s, none)

def hook (s : FW) (e : PyExc) : FW :=
  { s with log := s.log ++ [Json.arr #["hook", jStr e.className, jStr e.message]] }

def finCall (st : Fin FS) (s : FW) (fid : Nat) : Fin FS × FW × Json :=
  match st.call fid with
  | (st, none) => (st, s, Json.arr #["ok", Json.null])
  | (st, some f) =>
    match runFS f st s with
    | (st, s, some (e, _)) => (st, s, Json.arr #["exc", jStr e.className, jStr e.message])
    | (st, s, none) =>
      (st, s, Json.arr #["ok", match f with
        | .ret v => jInt v
        | _ => Json.null])

def jPeek : Option (PV × FS) → Json
  | none => Json.null
  | some (o, f) => Json.arr #[jPV o, jFS f]

def runFin (j : Json) : Except String Json := do
  let mut st : Fin FS := Fin.start
  let mut s : FW := { log := [], dead := [] }
  let mut out : Array Json := #[]
  for op in (← jArr (← field j "ops")) do
    match ← jStrAt op 0 with
    | "new" =>
      let fid ← jNatAt op 1
      let o ← pPV (← jGetI op 2)
      let f ← pFS (← jGetI op 3)
      if deadPV s.dead o then out := out.push (jStr "skip")
      else
        let (st', r) := st.init fid o f
        st := st'
        out := out.push (encR jUnit r)
    | "call" =>
      let (st', s', r) := finCall st s (← jNatAt op 1)
      st := st'
      s := s'
      out := out.push r
    | "detach" =>
      let (st', r) := st.detach s.dead (← jNatAt op 1)
      st := st'
      out := out.push (jPeek r)
    | "peek" => out := out.push (jPeek (st.peek s.dead (← jNatAt op 1)))
    | "alive" => out := out.push (jBool (st.isAlive (← jNatAt op 1)))
    | "atexit" => out := out.push (jBool (st.atexit (← jNatAt op 1)))
    | "set_atexit" =>
      st := st.setAtexit (← jNatAt op 1) (← jBoolAt op 2)
      out := out.push Json.null
    | "repr" =>
      out := out.push (jStr (st.repr s.dead (← jNatAt op 1) "ADDR" "OBJ" "MiscW"))
    | "kill" =>
      let o ← jNatAt op 1
      s := { s with dead := o :: s.dead }
      -- Each finalizer's weak reference fires, newest first; exceptions are unraisable.
      let fids := ((st.registry.filter (fun kv => kv.2.obj == o)).reverse).map (·.1)
      for fid in fids do
        let (st', s', _) := finCall st s fid
        st := st'
        s := s'
      out := out.push Json.null
    | "exit" =>
      let (st', s', r) := Fin.exitfunc runFS hook 64 st s
      st := st'
      s := s'
      out := out.push (match r with
        | some e => Json.arr #["exc", jStr e.className, jStr e.message]
        | none => Json.arr #["ok", Json.null])
    | o => throw s!"bad op {o}"
  let reg := toJson (st.registry.map (·.1))
  return Json.mkObj [("ok", Json.arr #[Json.arr out, Json.arr s.log.toArray, reg, jBool st.shutdown,
    jBool st.dirty])]

def runCase (j : Json) : Except String Json := do
  match ← getStr j "k" with
  | "wvd" => runWvd j
  | "wkd" => runWkd j
  | "wm" => runWm j
  | "keyed" => runKeyed j
  | "fin" => runFin j
  | k => throw s!"bad kind {k}"

end PyLean.CoreLibs.Misc.Weakref
