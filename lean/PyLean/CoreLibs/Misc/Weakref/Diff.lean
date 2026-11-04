import PyLean.CoreLibs.Misc.Common
import PyLean.CoreLibs.Misc.Weakref.Model

/-! `misc.weakref` cases: a script over a few objects, with `["kill", id]` dropping the last strong
reference to an object. Values are `["o", id]` or `["i", n]`. A script step that names a dead object
is skipped on both sides, and so is a kill of an object that a suspended generator still holds in its
frame (the last value it yielded).

`WeakValueDictionary` keys are `str`s `a`, `b`, `c` and the special keys of `difftest/corelibs_diff.py`
(`misc_WKEYS`): `U` (a list), `T` (`__hash__` raises `TypeError("custom")`), `HK`/`HV` (`__hash__`
raises `KeyError`/`ValueError`), `EK1`/`EK2`/`EV1`/`EV2` (hash 7, `__eq__` raises
`KeyError`/`ValueError`) and `N1`/`N2` (hash 7, `__eq__` always false). -/

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

def isSpecial (k : String) : Bool := k.length > 1 || k == "U" || k == "T"

/-- `KeyError(key)`'s message: `repr(key)`. -/
def rK (k : String) : String :=
  if k == "U" then "[1]" else if isSpecial k then k else s!"'{k}'"

def wvdOps : KOps String where
  hash := fun k =>
    if k == "U" then .error (.typeError "unhashable type: 'list'")
    else if k == "T" then .error (.typeError "custom")
    else if k == "HK" then .error (.keyError "'h'")
    else if k == "HV" then .error (.valueError "h")
    else if k.startsWith "E" || k.startsWith "N" then .ok 7
    else .ok (1000 + (k.toList.headD 'x').toNat)
  eq := fun a b =>
    if a.startsWith "EK" then .error (.keyError "'eq'")
    else if a.startsWith "EV" then .error (.valueError "eqv")
    else if a.startsWith "N" then .ok false
    else .ok (a == b)
  tn := fun k => if k == "U" then "list" else if k == "T" then "HashTE" else "str"

def pItems (j : Json) : Except String (List (String × PV)) := do
  (← jArr j).mapM (fun kv => do return ((← jStrAt kv 0), (← pPV (← jGetI kv 1))))

def jItems (l : List (String × PV)) : Json :=
  jList (fun kv => Json.arr #[jStr kv.1, jPV kv.2]) l

def wvdDump (w : World) (d : WVD String) : Json := jItems (WVD.liveItems w d)

def anyDead (w : World) (l : List (String × PV)) : Bool := l.any (fun kv => deadPV w kv.2)

/-- Insert `x` at `pos` (clamped). -/
def insertAt {α : Type} (l : List α) (pos : Nat) (x : α) : List α := l.take pos ++ x :: l.drop pos

/-- The `other` of a `WeakValueDictionary` update, and the values it mentions. -/
def pOther (j : Json) : Except String (Other String × List (String × PV)) := do
  match j with
  | .null => return (.none, [])
  | _ =>
    match ← jStrAt j 0 with
    | "map" =>
      let it ← pItems (← jGetI j 1)
      return (.mapping (.ok ⟨it.map Except.ok, none⟩), it)
    | "seq" =>
      let it ← pItems (← jGetI j 1)
      return (.seq (.ok ⟨it.map (fun kv => SeqEl.pair kv.1 kv.2), none⟩), it)
    | "hasattr" => return (.hasattrErr (.valueError "ga"), [])
    | "itemsraise" => return (.mapping (.error (.valueError "items")), [])
    | "itemsmid" =>
      let it ← pItems (← jGetI j 1)
      return (.mapping (.ok ⟨it.map Except.ok, some (.valueError "mid")⟩), it)
    | "notiter" => return (.seq (.error (.typeError "'int' object is not iterable")), [])
    | "badlen" =>
      let it ← pItems (← jGetI j 1)
      let pos ← jNatAt j 2
      return (.seq (.ok ⟨insertAt (it.map (fun kv => SeqEl.pair kv.1 kv.2)) pos (.badLen 3), none⟩), it)
    | "notseq" =>
      let it ← pItems (← jGetI j 1)
      let pos ← jNatAt j 2
      return (.seq (.ok ⟨insertAt (it.map (fun kv => SeqEl.pair kv.1 kv.2)) pos .notSeq, none⟩), it)
    | o => throw s!"bad other {o}"

/-- A generator: its kind, its state, and the object its frame holds. -/
structure Gen (α : Type) where
  kind : String
  st : Option (List α)
  held : Option Nat

def heldBy {α : Type} (gs : List (Gen α)) (i : Nat) : Bool := gs.any (fun g => g.held == some i)

def setGen {α : Type} (gs : List (Gen α)) (i : Nat) (g : Gen α) : List (Gen α) := gs.set i g

structure WvdS where
  w : World
  d : WVD String
  gens : List (Gen (Ent String (KRef String)))

def pvId : PV → Option Nat
  | .obj i => some i
  | .int _ => none

def wvdStep (s : WvdS) (op : Json) : Except String (WvdS × Json) := do
  let w := s.w
  let d := s.d
  let ops := wvdOps
  let name ← jStrAt op 0
  let ret (d : WVD String) (j : Json) : Except String (WvdS × Json) := pure ({ s with d }, j)
  match name with
  | "set" =>
    let v ← pPV (← jGetI op 2)
    if deadPV w v then return (s, jStr "skip")
    match d.setitem ops (← jStrAt op 1) v with
    | .ok d => ret d (encR jUnit (.ok ()))
    | .error e => ret d (encR jUnit (.error e))
  | "get_" => ret d (encR jPV (d.getitem ops rK w (← jStrAt op 1)))
  | "del" =>
    match d.delitem ops rK (← jStrAt op 1) with
    | .ok d => ret d (encR jUnit (.ok ()))
    | .error e => ret d (encR jUnit (.error e))
  | "len" => ret d (toJson d.data.length)
  | "in" => ret d (encR jBool (d.contains ops w (← jStrAt op 1)))
  | "copy" => ret d (encR (wvdDump w) (d.copy ops w))
  | "deepcopy" =>
    ret d (encR (fun p => wvdDump w p.2)
      (d.deepcopy ops (fun (m : Unit) k => .ok (m, k)) (.ok WVD.empty) w ()))
  | "get" =>
    let v ← pPV (← jGetI op 2)
    if deadPV w v then return (s, jStr "skip")
    ret d (encR jPV (d.get ops w (← jStrAt op 1) v))
  | "vrefs" => ret d (jList (fun r => jOpt jPV (deref w r.ob)) d.valuerefs)
  | "popitem" =>
    let (d, r) := d.popitem w
    ret d (encR (fun kv => Json.arr #[jStr kv.1, jPV kv.2]) r)
  | "pop" =>
    let args ← (← jArr (← jGetI op 2)).mapM pPV
    if args.any (deadPV w) then return (s, jStr "skip")
    let (d, r) := d.pop ops rK w (← jStrAt op 1) args
    ret d (encR jPV r)
  | "setdefault" =>
    let v ← pPV (← jGetI op 2)
    if deadPV w v then return (s, jStr "skip")
    let (d, r) := d.setdefault ops w (← jStrAt op 1) v
    ret d (encR jPV r)
  | "update" =>
    let (other, vs) ← pOther (← jGetI op 1)
    let kw ← pItems (← jGetI op 2)
    if anyDead w (vs ++ kw) then return (s, jStr "skip")
    let (d, r) := d.update ops other kw
    ret d (encR jUnit r)
  | "ior" =>
    let (other, vs) ← pOther (← jGetI op 1)
    if anyDead w vs then return (s, jStr "skip")
    let (d, r) := d.ior ops other
    ret d (encR jUnit r)
  | "or" | "ror" =>
    let items ← match ← jGetI op 1 with
      | .null => pure none
      | v => some <$> pItems v
    if anyDead w (items.getD []) then return (s, jStr "skip")
    let r := if name == "or" then d.or_ ops w items else d.ror ops w items
    match r with
    | none => ret d (jStr "NotImplemented")
    | some r => ret d (encR (wvdDump w) r)
  | "gen" =>
    let g : Gen (Ent String (KRef String)) := { kind := ← jStrAt op 1, st := none, held := none }
    return ({ s with gens := s.gens ++ [g] }, Json.null)
  | "next" =>
    let i ← jNatAt op 1
    match s.gens[i]? with
    | none => return (s, jStr "skip")
    | some g =>
      let enc : Option (List (Ent String (KRef String))) × Json × Option Nat :=
        match g.kind with
        | "items" =>
          let (st, y) := d.itemsNext w g.st
          (st, jOpt (fun kv => Json.arr #[jStr kv.1, jPV kv.2]) y, y.bind (fun kv => pvId kv.2))
        | "keys" =>
          let (st, y) := d.keysNext w g.st
          (st, jOpt jStr y, none)
        | "values" =>
          let (st, y) := d.valuesNext w g.st
          (st, jOpt jPV y, y.bind pvId)
        | _ =>
          let (st, y) := d.irefsNext w g.st
          (st, jOpt (fun r => Json.arr #[jOpt jPV (deref w r.ob)]) y, none)
      let (st, j, held) := enc
      let j := if j == Json.null then jStr "stop" else j
      return ({ s with gens := setGen s.gens i { g with st, held } }, j)
  | "kill" =>
    let i ← jNatAt op 1
    if heldBy s.gens i then return (s, jStr "held")
    return ({ s with w := i :: w, d := d.onDeath ops w i }, Json.null)
  | o => throw s!"bad op {o}"

def runWvd (j : Json) : Except String Json := do
  let eager ← getBool j "eager"
  let init ← pItems (← field j "init")
  let other : Other String := .seq (.ok ⟨init.map (fun kv => SeqEl.pair kv.1 kv.2), none⟩)
  let d0 : Py (WVD String) :=
    if eager then WVD.init wvdOps other
    else match ({ (WVD.empty : WVD String) with eager := false }).update wvdOps other with
      | (_, .error e) => .error e
      | (d, .ok ()) => .ok d
  match d0 with
  | .error e => return Json.mkObj [("ok", Json.arr #[encR jUnit (.error e)])]
  | .ok d0 =>
    let mut s : WvdS := { w := [], d := d0, gens := [] }
    let mut out : Array Json := #[]
    for op in (← jArr (← field j "ops")) do
      let (s', r) ← wvdStep s op
      s := s'
      out := out.push r
    let raw := jList (fun e => Json.arr #[jStr e.1, jOpt jPV (deref s.w e.2.2.ob)]) s.d.data
    return Json.mkObj [("ok", Json.arr (out.push raw))]

/-! `WeakKeyDictionary`: objects `0..3` hash and compare by their `val`; `4` has `__eq__` and no
`__hash__`; `5`/`6` raise `KeyError`/`ValueError` from `__hash__`; `7`/`8` hash to 7 and raise
`ValueError` from `__eq__`; `9` hashes to 7 and is never equal. -/

def wkdQ (vals : List Int) : ROps where
  hash := fun o =>
    if o < 4 then .ok (vals.getD o 0)
    else if o == 4 then .error (.typeError "unhashable type: 'MiscU'")
    else if o == 5 then .error (.keyError "'h'")
    else if o == 6 then .error (.valueError "h")
    else .ok 7
  eq := fun a b =>
    if a < 4 then .ok (b < 4 && vals.getD a 0 == vals.getD b 0)
    else if a == 7 || a == 8 then .error (.valueError "eqv")
    else .ok false

def pKItems (j : Json) : Except String (List (PV × Int)) := do
  (← jArr j).mapM (fun kv => do return ((← pPV (← jGetI kv 0)), (← jIntAt kv 1)))

def jKItems (l : List (PV × Int)) : Json :=
  jList (fun kv => Json.arr #[jPV kv.1, jInt kv.2]) l

def wkdDump (w : World) (d : WKD Int) : Json := jKItems (WKD.liveItems w d)

def anyDeadK (w : World) (l : List (PV × Int)) : Bool := l.any (fun kv => deadPV w kv.1)

def badLenE (i : Nat) : PyExc :=
  .valueError s!"dictionary update sequence element #{i} has length 3; 2 is required"

def pKOther (j : Json) : Except String (WKD.KOther Int × List (PV × Int)) := do
  match j with
  | .null => return (.none, [])
  | _ =>
    match ← jStrAt j 0 with
    | "map" =>
      let it ← pKItems (← jGetI j 1)
      return (.mapping (.ok ⟨it.map Except.ok, none⟩), it)
    | "seq" =>
      let it ← pKItems (← jGetI j 1)
      return (.seq (.ok ⟨it.map Except.ok, none⟩), it)
    | "hasattr" => return (.hasattrErr (.valueError "ga"), [])
    | "itemsraise" => return (.mapping (.error (.valueError "items")), [])
    | "itemsmid" =>
      let it ← pKItems (← jGetI j 1)
      return (.mapping (.ok ⟨it.map Except.ok, some (.valueError "mid")⟩), it)
    | "notiter" => return (.seq (.error (.typeError "'int' object is not iterable")), [])
    | "badlen" =>
      let it ← pKItems (← jGetI j 1)
      let pos := min (← jNatAt j 2) it.length
      return (.seq (.ok ⟨insertAt (it.map Except.ok) pos (.error (badLenE pos)), none⟩), it)
    | "notseq" =>
      let it ← pKItems (← jGetI j 1)
      let pos ← jNatAt j 2
      return (.seq (.ok ⟨insertAt (it.map Except.ok) pos
        (.error (.typeError "object is not iterable")), none⟩), it)
    | o => throw s!"bad other {o}"

structure WkdS where
  w : World
  d : WKD Int
  gens : List (Gen (WRef × Int))

def wkdStep (q : ROps) (s : WkdS) (op : Json) : Except String (WkdS × Json) := do
  let w := s.w
  let d := s.d
  let name ← jStrAt op 0
  let ret (d : WKD Int) (j : Json) : Except String (WkdS × Json) := pure ({ s with d }, j)
  let keyDead : Bool ← (do
    match name with
    | "set" | "get_" | "del" | "get" | "in" | "pop" | "setdefault" =>
      return deadPV w (← pPV (← jGetI op 1))
    | _ => return false)
  if keyDead then return (s, jStr "skip")
  match name with
  | "set" =>
    match d.setitem q w (← pPV (← jGetI op 1)) (← jIntAt op 2) with
    | .ok d => ret d (encR jUnit (.ok ()))
    | .error e => ret d (encR jUnit (.error e))
  | "get_" => ret d (encR jInt (d.getitem q w (← pPV (← jGetI op 1))))
  | "del" =>
    match d.delitem q w (← pPV (← jGetI op 1)) with
    | .ok d => ret d (encR jUnit (.ok ()))
    | .error e => ret d (encR jUnit (.error e))
  | "len" => ret d (toJson d.data.length)
  | "copy" => ret d (encR (wkdDump w) (d.copy q w))
  | "deepcopy" =>
    ret d (encR (fun p => wkdDump w p.2)
      (d.deepcopy q (fun (m : Unit) v => .ok (m, v)) (.ok WKD.empty) w ()))
  | "get" => ret d (encR jInt (d.get q w (← pPV (← jGetI op 1)) (← jIntAt op 2)))
  | "in" => ret d (encR jBool (d.contains q w (← pPV (← jGetI op 1))))
  | "krefs" => ret d (jList (fun r => jOpt jPV (deref w r.ob)) d.keyrefs)
  | "popitem" =>
    let (d, r) := d.popitem w
    ret d (encR (fun kv => Json.arr #[jPV kv.1, jInt kv.2]) r)
  | "pop" =>
    let args ← jIntList (← jGetI op 2)
    let (d, r) := d.pop q w (← pPV (← jGetI op 1)) args
    ret d (encR jInt r)
  | "setdefault" =>
    let (d, r) := d.setdefault q w (← pPV (← jGetI op 1)) (← jIntAt op 2)
    ret d (encR jInt r)
  | "update" =>
    let (other, vs) ← pKOther (← jGetI op 1)
    if anyDeadK w vs then return (s, jStr "skip")
    let (d, r) := d.update q w other (← jBoolAt op 2)
    ret d (encR jUnit r)
  | "ior" =>
    let (other, vs) ← pKOther (← jGetI op 1)
    if anyDeadK w vs then return (s, jStr "skip")
    let (d, r) := d.ior q w other
    ret d (encR jUnit r)
  | "or" | "ror" =>
    let items ← match ← jGetI op 1 with
      | .null => pure none
      | v => some <$> pKItems v
    if anyDeadK w (items.getD []) then return (s, jStr "skip")
    let r := if name == "or" then d.or_ q w items else d.ror q w items
    match r with
    | none => ret d (jStr "NotImplemented")
    | some r => ret d (encR (wkdDump w) r)
  | "gen" =>
    let g : Gen (WRef × Int) := { kind := ← jStrAt op 1, st := none, held := none }
    return ({ s with gens := s.gens ++ [g] }, Json.null)
  | "next" =>
    let i ← jNatAt op 1
    match s.gens[i]? with
    | none => return (s, jStr "skip")
    | some g =>
      let enc : Option (List (WRef × Int)) × Json × Option Nat :=
        match g.kind with
        | "items" =>
          let (st, y) := d.itemsNext w g.st
          (st, jOpt (fun kv => Json.arr #[jPV kv.1, jInt kv.2]) y, y.bind (fun kv => pvId kv.1))
        | "keys" =>
          let (st, y) := d.keysNext w g.st
          (st, jOpt jPV y, y.bind pvId)
        | _ =>
          let (st, y) := d.valuesNext w g.st
          (st, jOpt jInt y, none)
      let (st, j, held) := enc
      let j := if j == Json.null then jStr "stop" else j
      return ({ s with gens := setGen s.gens i { g with st, held } }, j)
  | "kill" =>
    let i ← jNatAt op 1
    if heldBy s.gens i then return (s, jStr "held")
    return ({ s with w := i :: w, d := d.onDeath i }, Json.null)
  | o => throw s!"bad op {o}"

def runWkd (j : Json) : Except String Json := do
  let eager ← getBool j "eager"
  let vals ← (field j "vals") >>= jIntList
  let q := wkdQ vals
  let init ← pKItems (← field j "init")
  let other : WKD.KOther Int := .mapping (.ok ⟨init.map Except.ok, none⟩)
  let d0 : Py (WKD Int) :=
    if eager then WKD.init q [] other
    else match ({ (WKD.empty : WKD Int) with eager := false }).update q [] other with
      | (_, .error e) => .error e
      | (d, .ok ()) => .ok d
  match d0 with
  | .error e => return Json.mkObj [("ok", Json.arr #[encR jUnit (.error e)])]
  | .ok d0 =>
    let mut s : WkdS := { w := [], d := d0, gens := [] }
    let mut out : Array Json := #[]
    for op in (← jArr (← field j "ops")) do
      let (s', r) ← wkdStep q s op
      s := s'
      out := out.push r
    let raw := jList (fun kv => Json.arr #[jOpt jPV (deref s.w kv.1.ob), jInt kv.2]) s.d.data
    return Json.mkObj [("ok", Json.arr (out.push raw))]

/-! `WeakMethod` and `KeyedRef`. Object `i < 4` has `eqm[i]` (0: by `val`, 1: raises
`ValueError("eq")`, 2: returns `0`, 3: returns `"yes"`, 4: returns an object whose `__bool__` raises
`ValueError("truth")`) and `nem[i]` (0: the default `__ne__`, 1: returns `"ne"`, 2: returns `0`). -/

instance : Inhabited WM := ⟨⟨0, 0, 0, false, false⟩⟩

inductive RV where
  | b (t : Bool)
  | i (n : Int)
  | s (t : String)
  | bad

def jRV : RV → Json
  | .b t => jBool t
  | .i n => jInt n
  | .s t => jStr t
  | .bad => jStr "BAD"

def truthRV : RV → Py Bool
  | .b t => .ok t
  | .i n => .ok (n != 0)
  | .s t => .ok (t != "")
  | .bad => .error (.valueError "truth")

def wmCmp (vals eqm nem : List Int) : RCmp RV :=
  let eq : Nat → Nat → Py RV := fun a b =>
    if 10 ≤ a then .ok (.b (a == b)) else
    match eqm.getD a 0 with
    | 1 => .error (.valueError "eq")
    | 2 => .ok (.i 0)
    | 3 => .ok (.s "yes")
    | 4 => .ok .bad
    | _ => .ok (.b (vals.getD a 0 == vals.getD b 0))
  { eq
    ne := fun a b =>
      if 10 ≤ a then .ok (.b (a != b)) else
      match nem.getD a 0 with
      | 1 => .ok (.s "ne")
      | 2 => .ok (.i 0)
      | _ =>
        match eq a b with
        | .error e => .error e
        | .ok x =>
          match truthRV x with
          | .error e => .error e
          | .ok t => .ok (.b (!t))
    ofBool := .b
    truth := truthRV }

def badMeth (kind : String) : Meth :=
  match kind with
  | "int" => { self := .ok (.int 5), func := .ok (.obj 10), tp := "TP" }
  | "onlyself" => { self := .ok (.obj 0), func := .error (.named "AttributeError" "x"), tp := "TP" }
  | "raiseself" => { self := .error (.valueError "selfattr"), func := .ok (.obj 10), tp := "TP" }
  | "funcint" => { self := .ok (.obj 0), func := .ok (.int 3), tp := "TP" }
  | _ => { self := .error (.named "AttributeError" "x"), func := .error (.named "AttributeError" "x"),
           tp := "TP" }

def runWm (j : Json) : Except String Json := do
  let vals ← (field j "vals") >>= jIntList
  let eqm ← (field j "eqm") >>= jIntList
  let nem ← (field j "nem") >>= jIntList
  let c := wmCmp vals eqm nem
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
        match WM.new ms.size ⟨.ok (.obj o), .ok (.obj f), "TP"⟩ (← jBoolAt op 3) with
        | .ok m =>
          ms := ms.push m
          out := out.push (toJson m.id)
        | .error e => out := out.push (encR jUnit (.error e))
    | "bad" =>
      let kind ← jStrAt op 1
      if (kind == "onlyself" || kind == "funcint") && w.contains 0 then out := out.push (jStr "skip")
      else
        out := out.push (encR jUnit (match WM.new 0 (badMeth kind) false with
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
        let r := if isEq then ms[i].eq c w (some ms[k]) else ms[i].ne c w (some ms[k])
        out := out.push (jOpt (encR jRV) r)
      else out := out.push (jStr "skip")
    | "eqo" =>
      let i ← jNatAt op 1
      if h : i < ms.size then out := out.push (jOpt (encR jRV) (ms[i].eq c w none))
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
  match KRef.new v true "k" with
  | .error e => return Json.mkObj [("ok", encR jUnit (.error e))]
  | .ok r =>
    let before := deref [] r.ob
    let dead : World := [r.ob]
    return Json.mkObj [("ok", Json.arr #[jStr r.key, jOpt jPV before, jOpt jPV (deref dead r.ob),
      jBool r.cb])]

/-! `finalize` -/

inductive FS where
  | ret (v : Int)
  | boom
  | boom2
  | base
  | spawn (fid oid : Nat) (f : FS)
  deriving Repr, DecidableEq

partial def jFS : FS → Json
  | .ret v => Json.arr #["ret", jInt v]
  | .boom => Json.arr #["boom"]
  | .boom2 => Json.arr #["boom2"]
  | .base => Json.arr #["base"]
  | .spawn a b f => Json.arr #["spawn", toJson a, toJson b, jFS f]

partial def pFS (j : Json) : Except String FS := do
  match ← jStrAt j 0 with
  | "ret" => return .ret (← jIntAt j 1)
  | "boom" => return .boom
  | "boom2" => return .boom2
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
def boom2Exc : PyExc := .valueError "boom2"
def baseExc : PyExc := .named "KeyboardInterrupt" "base"

def runFS : Fin.RunF FW FS := fun f st s =>
  let s := { s with log := s.log ++ [Json.arr #["run", jFS f, jBool st.gc]] }
  match f with
  | .ret _ => (st, s, none)
  | .boom => (st, s, some (boomExc, true))
  | .boom2 => (st, s, some (boom2Exc, true))
  | .base => (st, s, some (baseExc, false))
  | .spawn a b g =>
    if s.dead.contains b then (st, s, none)
    else
      match Fin.init st a (.obj b) g with
      | (st, _) => (st, s, none)

/-- `sys.excepthook` of the test: it logs, and raises `RuntimeError("hook")` for `boom2`. -/
def hook (s : FW) (e : PyExc) : FW × Option PyExc :=
  let s := { s with log := s.log ++ [Json.arr #["hook", jStr e.className, jStr e.message]] }
  if e.message == "boom2" then (s, some (.named "RuntimeError" "hook")) else (s, none)

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
  let mut cls : List (Nat × String) := []
  let mut out : Array Json := #[]
  for op in (← jArr (← field j "ops")) do
    match ← jStrAt op 0 with
    | "new" | "newsub" =>
      let fid ← jNatAt op 1
      let o ← pPV (← jGetI op 2)
      let f ← pFS (← jGetI op 3)
      if deadPV s.dead o then out := out.push (jStr "skip")
      else
        let (st', r) := st.init fid o f
        st := st'
        if r matches .ok () then
          cls := dSet cls fid (if (← jStrAt op 0) == "newsub" then "MyFin" else "finalize")
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
      let v : Py Bool := match ← jGetI op 2 with
        | .bool b => .ok b
        | .str "bad" => .error (.valueError "bool")
        | _ => .ok true
      match st.setAtexit (← jNatAt op 1) v with
      | .ok st' =>
        st := st'
        out := out.push (encR jUnit (.ok ()))
      | .error e => out := out.push (encR jUnit (.error e))
    | "repr" =>
      let fid ← jNatAt op 1
      out := out.push (jStr (st.repr s.dead fid ((dGet cls fid).getD "finalize") "ADDR" "OBJ" "MiscW"))
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
    jBool st.dirty, jBool st.gc])]

def runCase (j : Json) : Except String Json := do
  match ← getStr j "k" with
  | "wvd" => runWvd j
  | "wkd" => runWkd j
  | "wm" => runWm j
  | "keyed" => runKeyed j
  | "fin" => runFin j
  | k => throw s!"bad kind {k}"

end PyLean.CoreLibs.Misc.Weakref
