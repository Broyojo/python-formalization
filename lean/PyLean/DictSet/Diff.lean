import PyLean.DiffCore
import PyLean.DictSet.Objects
import PyLean.DictSet.ODictPy
import PyLean.DictSet.Managed
import PyLean.DictSet.Ops315

/-! Differential-testing handler for `dictset` cases (`"mod": "dictset"`).

A case carries a `pool` of objects and a list of `ops` on three dict slots, three set
slots and four iterator slots. Slots 0 and 1 keep their object for the whole test; slot 2
receives results. The answer is `{"ok": [[result, digest], ...]}`; the digest holds, for
every dict, keys, values and `__sizeof__`, and for every set, the elements in table order
and `__sizeof__`, so table size, entry kind, probe order and iteration order are compared
after every step. -/

namespace PyLean.DictSet

open Lean PyLean PyLean.Diff

inductive It where
  | d (slot : Nat) (di : DictIter)
  | s (slot : Nat) (si : SetIter)
  deriving Inhabited

abbrev OD := ODict DObj DObj
abbrev POD := PyOD DObj DObj

structure St where
  pool : Array DObj
  ds : Array DD
  ss : Array DS
  its : Array (Option It)
  next : Nat
  ods : Array OD := #[]
  oits : Array (Option (ODictIter DObj)) := #[]
  pods : Array POD := #[]
  gens : Array (Option (Nat × IterKind × PyODGen)) := #[]
  keys : Keys DObj Unit := default
  insts : Array (Option (Inst DObj DObj)) := #[]
  touched : Array Bool := #[]
  nextDict : Nat := 1000
  names : List DObj := []
  /-- The dict slot that a mutating `__eq__` acts on, when the test names one. -/
  tgt : Option Nat := none
  /-- The set slot that a mutating `__eq__` acts on. -/
  stgt : Option Nat := none
  deriving Inhabited

def enc : DObj → Json
  | .atom a => toJson a.uid
  | .tuple a b => Json.arr #[enc a, enc b]

def encs (l : List DObj) : Json := Json.arr (l.map enc).toArray

def encDict (d : DD) : Json :=
  Json.arr #[encs (dictKeysList d), encs (dictValuesList d), toJson (dictSizeOf d)]

def encSet (s : DS) : Json :=
  Json.arr #[encs ((setEntries s).map (·.1)), toJson s.sizeOf]

def digestBase (st : St) : Json :=
  Json.arr #[Json.arr (st.ds.map encDict), Json.arr (st.ss.map encSet)]

def okJ (v : Json) : Json := Json.mkObj [("ok", v)]
def errJ (e : PyExc) : Json := Json.mkObj [("exc", toJson e.className), ("msg", toJson e.message)]
def enc1 {α : Type} (f : α → Json) (r : Py α) : Json :=
  match r with
  | .ok v => okJ (f v)
  | .error e => errJ e
def unitJ : Unit → Json := fun _ => Json.null
def encOpt (v : Option DObj) : Json :=
  match v with
  | some x => enc x
  | none => Json.null
def encPair (p : DObj × DObj) : Json := Json.arr #[enc p.1, enc p.2]

def parseAtom (j : Json) : Except String Atom := do
  return { uid := ← getNat j "u", cls := ← getNat j "c", hash := ← getInt j "h"
           hkind := ← getNat j "hk", isStr := ← getBool j "s", isStrLike := ← getBool j "sl"
           raises := ← getBool j "r", act := ← getNat j "a", rep := ← getStr j "rep"
           tname := ← getStr j "t", fs := ← getOptInt j "fs"
           nan := (j.getObjValAs? Bool "nan").toOption.getD false
           ract := (j.getObjValAs? Nat "ra").toOption.getD 0
           rk := (j.getObjValAs? Bool "rk").toOption.getD false
           hact := (j.getObjValAs? Nat "ha").toOption.getD 0
           hres := (j.getObjValAs? Nat "hr").toOption.getD 0
           sbody := (j.getObjValAs? (List Int) "sb").toOption }

def arg (op : Array Json) (k : Nat) : Except String Json :=
  match op[k]? with
  | some v => .ok v
  | none => .error s!"missing argument {k}"
def argN (op : Array Json) (k : Nat) : Except String Nat := do (← arg op k).getNat?
def arrOf (j : Json) : Except String (List Json) := do return (← j.getArr?).toList

/-- A pool index, or `[a, b]` for the tuple `(a, b)`. -/
partial def obj (st : St) (j : Json) : Except String DObj := do
  match j with
  | .arr a =>
    let x := a[0]?.getD Json.null
    let y := a[1]?.getD Json.null
    return .tuple (← obj st x) (← obj st y)
  | _ =>
    let i ← j.getNat?
    match st.pool[i]? with
    | some o => .ok o
    | none => .error "pool index"
def objs (st : St) (j : Json) : Except String (List DObj) := do
  (← arrOf j).mapM (obj st)

/-- `['s', slot]`, `['d', slot]`, `['l', items]`, `['g', items]` (raises at the end),
`['n']` (not iterable). -/
def setArg (st : St) (j : Json) : Except String (SetArg DObj) := do
  let a ← j.getArr?
  let tag ← (← arg a 0).getStr?
  match tag with
  | "s" => return .set st.ss[← argN a 1]!
  | "d" => return .dict (dictAsArg dEnv st.ds[← argN a 1]!)
  | "l" => return .iter { items := ← objs st (← arg a 1) }
  | "h" =>
    -- `['h', items, hook, act, stop]`: a generator that does `act` to the target set before it
    -- yields element `hook`.
    let items ← objs st (← arg a 1)
    let hook ← argN a 2
    let act ← argN a 3
    let stop ← (← arg a 4).getBool?
    let tid := match st.stgt with
      | some t => st.ss[t]!.ident
      | none => 0
    let steps : List (SM DObj (Option DObj)) := items.zipIdx.map fun (x, i) s =>
      (.ok (some x),
       if i == hook && (s.ident == tid || s.peers.any (·.ident == tid)) then
         (evilSet st.pool act (s.swapIn tid)).swapIn s.ident
       else s)
    return .live { steps := steps ++ if stop then [M.throw (.valueError "stop")] else [] }
  | "g" => return .iter { items := ← objs st (← arg a 1), stop := some (.valueError "stop") }
  | "S" =>
    -- `['S', contents, items]`: an instance of a set subclass holding `contents`, whose
    -- `__iter__` yields `items`.
    let body := (setUpdate plainSet (.iter { items := ← objs st (← arg a 1) })
      ({ ident := 900, exact := false, tname := "SSub" } : DS)).2
    return .sub { body with peers := [] } (ReIter.ofIterable { items := ← objs st (← arg a 2) })
  | "n" => return .iter { getIter := some (.typeError "'int' object is not iterable"), items := [] }
  | t => throw s!"set arg {t}"

/-- The operand of a view operation: `['v', kind, slot]` or a `setArg`. -/
def viewOf (st : St) (kind : String) (slot : Nat) : View DObj DObj :=
  { kind := match kind with
      | "k" => .keys
      | "i" => .items
      | _ => .values
    d := st.ds[slot]! }

def viewArg (st : St) (j : Json) : Except String (ViewArg DObj DObj) := do
  let a ← j.getArr?
  let tag ← (← arg a 0).getStr?
  match tag with
  | "v" => return .view (viewOf st (← (← arg a 1).getStr?) (← argN a 2))
  | "s" => return .set st.ss[← argN a 1]!
  | _ => return .other (← setArg st j)

def seq2Item (st : St) (j : Json) : Except String (Seq2Item DObj DObj) := do
  let a ← j.getArr?
  let tag ← (← arg a 0).getStr?
  match tag with
  | "p" => return .pair (← obj st (← arg a 1)) (← obj st (← arg a 2))
  | "b" => return .notSeq (.typeError "object is not iterable") true
  -- An element whose iterator raises a subclass of `TypeError`, which `PySequence_Fast` passes on.
  | "bt" => return .notSeq (.named "TESub" "sub") true
  -- An element whose iterator raises `ValueError`.
  | "bv" => return .notSeq (.valueError "next") false
  | "l" => return .wrongLen (← argN a 1)
  | t => throw s!"seq2 {t}"

/-- A mapping object over `pairs`: `keys()` lists `ks`, `__getitem__` looks in `pairs`
by the uid of the key and raises `KeyError` otherwise. -/
def mapArg (st : St) (ksJ pairsJ : Json) : Except String (MergeArg DObj DObj) := do
  let ks ← objs st ksJ
  let ps ← (← arrOf pairsJ).mapM fun p => do
    let a ← p.getArr?
    return ((← obj st (← arg a 0)), (← obj st (← arg a 1)))
  return .mapping (pure (ReIter.ofKeys ks)) fun k =>
    M.lift (match ps.find? (fun p => p.1 == k) with
      | some p => .ok p.2
      | none => .error (keyErr dProto k))

/-- `['ma', keys, pairs, extra, extraValue]`: `keys()` returns the mapping's own list, and the first
`__getitem__` appends `extra` to it, which the loop of `dict_merge` then reaches. -/
def mapAppendArg (st : St) (a : Array Json) : Except String (MergeArg DObj DObj) := do
  let ks ← objs st (← arg a 1)
  let ps ← (← arrOf (← arg a 2)).mapM fun p => do
    let q ← p.getArr?
    return ((← obj st (← arg q 0)), (← obj st (← arg q 1)))
  let extra ← obj st (← arg a 3)
  let ev ← obj st (← arg a 4)
  let ps := ps ++ [(extra, ev)]
  let all := if ks.isEmpty then [] else ks ++ [extra]
  return .mapping (pure (ReIter.ofKeys all)) fun k =>
    M.lift (match ps.find? (fun p => p.1 == k) with
      | some p => .ok p.2
      | none => .error (keyErr dProto k))

/-- `['mr', keys, pairs, hook, act, keysRaises]`: as `mapArg`, but `__getitem__` of `hook` first
does `act` to the receiver, and `keys()` may raise. -/
def mapHookArg (st : St) (a : Array Json) : Except String (MergeArg DObj DObj) := do
  let m ← mapArg st (← arg a 1) (← arg a 2)
  let hook ← obj st (← arg a 3)
  let act ← argN a 4
  let kr ← (← arg a 5).getBool?
  match m with
  | .mapping keys getitem =>
    return .mapping (if kr then M.throw (.valueError "keys") else keys) fun k s =>
      getitem k (if k == hook then evilAct st.pool act s else s)
  | m => return m

/-- `['d', slot]` exact dict, `['sub', slot]` subclass with `dict.__iter__`,
`['p', items, stop?]` iterable of pairs, `['m', keys, pairs]` mapping, `['n']`. -/
def updArg (st : St) (j : Json) : Except String (UpdateArg DObj DObj) := do
  let a ← j.getArr?
  let tag ← (← arg a 0).getStr?
  match tag with
  | "d" => return .exact st.ds[← argN a 1]!
  | "sub" =>
    -- The test copies the dict into a subclass instance with `dict.update`.
    let (_, c) := dictMerge dProto (.dict st.ds[← argN a 1]!) 1 ({ ident := 77 } : DD)
    return .other (pure true) (.dict c) { steps := [] }
  | "p" =>
    let items ← (← arrOf (← arg a 1)).mapM (seq2Item st)
    let stop ← (← arg a 2).getBool?
    return .other (pure false) (.dict {})
      (ReIter.ofIterable { items, stop := if stop then some (.valueError "stop") else none })
  | "pr" =>
    -- `['pr', items, hook, act, stop]`: the iterator does `act` to the receiver before
    -- yielding element `hook`.
    let items ← (← arrOf (← arg a 1)).mapM (seq2Item st)
    let hook ← argN a 2
    let act ← argN a 3
    let stop ← (← arg a 4).getBool?
    let steps : List (DM DObj DObj (Option (Seq2Item DObj DObj))) :=
      items.zipIdx.map fun (x, i) s =>
        (.ok (some x), if i == hook then evilAct st.pool act s else s)
    return .other (pure false) (.dict {})
      { steps := steps ++ if stop then [M.throw (.valueError "stop")] else [] }
  | "m" => return .other (pure true) (← mapArg st (← arg a 1) (← arg a 2)) { steps := [] }
  | "mr" => return .other (pure true) (← mapHookArg st a) { steps := [] }
  | "ma" => return .other (pure true) (← mapAppendArg st a) { steps := [] }
  | "hr" => return .other (M.throw (.valueError "hasattr")) (.dict {}) { steps := [] }
  | "n" =>
    return .other (pure false) (.dict {})
      (ReIter.ofIterable { getIter := some (.typeError "'int' object is not iterable"), items := [] })
  | t => throw s!"update arg {t}"

/-- The protocol of an operation on slot `i`. -/
def protoAt (st : St) (i : Nat) : Proto DObj DD :=
  match st.tgt with
  | none => dProto
  | some t => if i == t then selfProto st.pool else peerProto st.pool

/-- Run on slot `i`. With a target in another slot, that slot is the object `__eq__` can reach, so
it is lent to the state and taken back: a merge from it leaves its final state in `peer`. -/
def withD {α : Type} (st : St) (i : Nat) (m : DM DObj DObj α) : Py α × St :=
  match st.tgt with
  | some t =>
    if i == t then
      let (r, d) := m st.ds[i]!
      (r, { st with ds := st.ds.set! i { d with peer := none } })
    else
      let (r, d) := m { st.ds[i]! with peer := some st.ds[t]!.toPeer }
      let src := match d.peer with
        | some p => p.toDict
        | none => st.ds[t]!
      (r, { st with ds := (st.ds.set! t src).set! i { d with peer := none } })
  | none =>
    let (r, d) := m st.ds[i]!
    (r, { st with ds := st.ds.set! i { d with peer := none } })

/-- Run on set slot `i`. A target in another slot is lent to the state and taken back. -/
def withS {α : Type} (st : St) (i : Nat) (m : SM DObj α) : Py α × St :=
  match st.stgt with
  | some t =>
    if i == t then
      let (r, s) := m st.ss[i]!
      (r, { st with ss := st.ss.set! i { s with peers := [] } })
    else
      let tb := st.ss[t]!
      let (r, s) := m { st.ss[i]! with peers := [tb.toSetBody] }
      let tb' : DS := { toSetBody := s.live tb.ident }
      (r, { st with ss := (st.ss.set! i { s with peers := [] }).set! t tb' })
  | none =>
    let (r, s) := m st.ss[i]!
    (r, { st with ss := st.ss.set! i s })

def fresh (st : St) : Nat × St := (st.next, { st with next := st.next + 1 })

/-- Store a new set in slot 2. -/
def toSlot2 (st : St) (r : Py DS) : Json × St :=
  match r with
  | .ok s => (okJ Json.null, { st with ss := st.ss.set! 2 s })
  | .error e => (errJ e, st)

/-- Run on set slot `i` and store the new set in slot 2. -/
def toSlot2S (st : St) (i : Nat) (m : SM DObj DS) : Json × St :=
  let (r, st') := withS st i m
  toSlot2 st' r

def toDSlot2 (st : St) (r : Py DD) : Json × St :=
  match r with
  | .ok d => (okJ Json.null, { st with ds := st.ds.set! 2 d })
  | .error e => (errJ e, st)

def resJ {α : Type} (f : α → Json) (p : Py α × St) : Json × St := (enc1 f p.1, p.2)

def cmpOf (s : String) : Except String CmpOp :=
  match s with
  | "lt" => .ok .lt
  | "le" => .ok .le
  | "eq" => .ok .eq
  | "ne" => .ok .ne
  | "gt" => .ok .gt
  | "ge" => .ok .ge
  | t => .error s!"cmp {t}"

/-- An exception's note, as the test reports it. -/
def withNote (n : Option String) (j : Json) : Json :=
  match n with
  | some x => j.mergeObj (Json.mkObj [("note", toJson x)])
  | none => j

/-- Report the note left on slot `i`, and clear it. -/
def takeNote (i : Nat) (p : Json × St) : Json × St :=
  let d := p.2.ds[i]!
  (withNote d.note p.1, { p.2 with ds := p.2.ds.set! i { d with note := none } })

/-- Slot `i` as the peer `p` left it. -/
def fromPeer (st : St) (i : Nat) (p : PeerDict DObj DObj) : St :=
  let d : DD := { st.ds[i]! with ident := p.ident, used := p.used, body := p.body, nextId := p.nextId }
  { st with ds := st.ds.set! i d }

/-- `PyObject_RichCompareBool(aval, bval, Py_EQ)` on values: identity first; a mutating `__eq__`
acts on the target, which is the state itself (`onSelf`) or its peer. -/
def evilVeq (pool : Array DObj) (onSelf : Bool) : DObj → DObj → DM DObj DObj Bool := fun x y s =>
  if x = y then (.ok true, s) else
  match DObj.action x y with
  | 0 => (DObj.eq x y, s)
  | n =>
    (evilAnswer x y,
     if onSelf then evilAct pool n s
     else match s.peer with
       | some p => { s with peer := some (evilAct pool n p.toDict).toPeer }
       | none => s)

/-- `repr(x)`, which may act on the dict being printed. -/
def evilRepr (pool : Array DObj) (acts : Bool) : DObj → DM DObj DObj String := fun x s =>
  (.ok x.reprStr, if acts && x.reprAct != 0 then evilAct pool x.reprAct s else s)

/-- `frozendict(d)` for an exact dict `d`. -/
def frozenOf (d : DD) (id : Nat) : DD :=
  match frozendictVectorcall dProto ({ ident := id, frozen := true } : DD) [.exact d] [] with
  | .ok x => x
  | .error _ => { ident := id, frozen := true }

/-- The iterable of `fromkeys`: `['d', slot]`, `['fd', slot]` (a frozendict of it), `['s', slot]`,
`['l', items]`, `['g', items]` (raises at the end), `['n']` (not iterable). -/
def fkIterOf (st : St) (t : Array Json) (id : Nat) : Except String (FkIter DObj DObj) := do
  match ← (← arg t 0).getStr? with
  | "d" => return { fast := some (.dict st.ds[← argN t 1]!), iter := { steps := [] } }
  | "fd" => return { fast := some (.dict (frozenOf st.ds[← argN t 1]! id)), iter := { steps := [] } }
  | "s" =>
    let s := st.ss[← argN t 1]!
    return { fast := some (.set s.used ((setEntries s).map fun e => pure (some e))), iter := { steps := [] } }
  | "l" => return { fast := none, iter := ReIter.ofIterable { items := ← objs st (← arg t 1) } }
  | "g" =>
    return { fast := none
             iter := ReIter.ofIterable { items := ← objs st (← arg t 1), stop := some (.valueError "stop") } }
  | _ =>
    return { fast := none
             iter := ReIter.ofIterable { getIter := some (.typeError "'int' object is not iterable"), items := [] } }

/-- `dict` or `frozendict` as `cls` of `fromkeys`. -/
def builtinCls (frozen : Bool) (id : Nat) : FkCls DObj DObj :=
  { isFrozendictType := frozen
    call := .ok { d := { ident := id } }
    callWith := fun x => .ok x
    setItem := fun _ _ => M.throw .modelFuel
    instMap := .dict {} }

/-- `fromkeys` into slot 2, the iterable in slot `src` taking back what a callback did to it. -/
def runFromkeys (st : St) (P : Proto DObj DD) (frozen : Bool) (t : Array Json) (v : DObj) :
    Except String (Json × St) := do
  let (id, st) := fresh st
  let it ← fkIterOf st t (id + 7)
  let srcSlot : Option Nat :=
    if (t[0]?.bind fun j => j.getStr?.toOption) == some "d" then
      t[1]?.bind fun j => j.getNat?.toOption
    else none
  match (pyDictFromKeys P (builtinCls frozen id) it v id).1 with
  | .ok x =>
    let st := match srcSlot, x.d.peer with
      | some s, some p => if s == 2 then st else fromPeer st s p
      | _, _ => st
    return (okJ Json.null, { st with ds := st.ds.set! 2 { x.d with peer := none } })
  | .error e => return (errJ e, st)

/-- `str(key)` of a pool object. -/
def strOf : DObj → String
  | .atom a =>
    if a.isStrLike then (((a.rep.drop 1).dropEnd 1).copy) else a.rep
  | x => x.reprStr

/-- The right operand of a C API merge, by its tag. -/
def mergeObj (st : St) (j : Json) : Except String (Option (MergeObj DObj DObj)) := do
  let a ← j.getArr?
  match ← (← arg a 0).getStr? with
  | "d" =>
    return some { isDict := true, iterIsDict := true, asDict := st.ds[← argN a 1]!,
                  keys := pure (ReIter.ofKeys []), getitem := fun _ => M.throw .modelFuel }
  | "m" =>
    match ← mapArg st (← arg a 1) (← arg a 2) with
    | .mapping ks g => return some { isDict := false, iterIsDict := false, asDict := {}, keys := ks,
                                     getitem := g }
    | .dict _ => throw "merge arg"
  | _ => return none

/-- `['c_*', target, ...]`: the C API through `_testlimitedcapi` and `_testcapi`. `target` is a slot,
or `-1` for a list. A slot is what the model runs on; nothing but a no-op or a refusal reaches it
with `-1`. -/
def stepC (st : St) (name : String) (a : Array Json) : Except String (Option (Json × St)) := do
  if !name.startsWith "c_" then return none
  let t ← (← arg a 1).getInt?
  let isAny := decide (0 ≤ t)
  let i := t.toNat
  let k (n : Nat) : Except String DObj := do obj st (← arg a n)
  let P := dProto
  let S := sProto
  let d := st.ds[i]!
  let so := st.ss[i]!
  match name with
  | "c_set" => return some (resJ unitJ (withD st i (dictSetItemChecked P isAny (← k 2) (← k 3))))
  | "c_del" => return some (resJ unitJ (withD st i (dictDelItemChecked P isAny (← k 2))))
  | "c_in" => return some (resJ toJson (withD st i (pyDictContainsChecked P isAny (← k 2))))
  | "c_get" =>
    let (r, st') := withD st i (dictGetitemFull P isKeyErrorTest isAny (← k 2))
    let f : Option DObj × Option PyExc → Json := fun p =>
      Json.arr #[match p.1 with
        | some v => enc v
        | none => Json.null,
        match p.2 with
        | some e => Json.arr #[toJson e.className, toJson e.message]
        | none => Json.null]
    return some (enc1 f r, st')
  | "c_gete" =>
    let enco : Option DObj → Json := fun o => match o with
      | some v => enc v
      | none => Json.null
    return some (resJ enco (withD st i (pyDictGetItemWithError P isAny (← k 2))))
  | "c_getr" =>
    let enco : Option DObj → Json := fun o => match o with
      | some v => enc v
      | none => Json.null
    return some (resJ enco (withD st i (pyDictGetItemRef P isAny (← k 2))))
  | "c_pop" =>
    let enco : Option DObj → Json := fun o => match o with
      | some v => Json.arr #[toJson (1 : Nat), enc v]
      | none => Json.arr #[toJson (0 : Nat), Json.null]
    return some (resJ enco (withD st i (pyDictPop P isAny (← k 2))))
  | "c_sdef" =>
    let enco : Option DObj → Json := fun o => match o with
      | some v => enc v
      | none => Json.null
    return some (resJ enco (withD st i (pyDictSetDefaultC P isAny (← k 2) (← k 3))))
  | "c_sdefr" =>
    let enco : Nat × Option DObj → Json := fun o => match o.2 with
      | some v => enc v
      | none => Json.null
    return some (resJ enco (withD st i (pyDictSetDefaultRef P isAny (← k 2) (← k 3))))
  | "c_pops" =>
    -- `['c_pops', target, key or -1]`: `PyDict_PopString` with the text of a str in the pool,
    -- which makes a new str object, or with bytes that are not UTF-8.
    let kj ← (← arg a 2).getInt?
    let mk : Py DObj :=
      if kj < 0 then .error (.named "UnicodeDecodeError"
        "'utf-8' codec can't decode byte 0xff in position 0: invalid start byte")
      else match st.pool[kj.toNat]! with
        | .atom x => .ok (.atom { x with uid := 1000000 + x.uid })
        | o => .ok o
    let enco : Option DObj → Json := fun o => match o with
      | some v => Json.arr #[toJson (1 : Nat), enc v]
      | none => Json.arr #[toJson (0 : Nat), Json.null]
    return some (resJ enco (withD st i (pyDictPopString P isAny mk)))
  | "c_merge" =>
    let ov ← (← arg a 3).getInt?
    let b ← mergeObj st (← arg a 2)
    return some (resJ unitJ (withD st i (pyDictMerge P isAny b ov)))
  | "c_upd" =>
    let b ← mergeObj st (← arg a 2)
    return some (resJ unitJ (withD st i (pyDictUpdate P isAny b)))
  | "c_seq2" =>
    let items ← (← arrOf (← arg a 2)).mapM (seq2Item st)
    let ov ← (← arg a 3).getBool?
    return some (resJ unitJ (withD st i
      (pyDictMergeFromSeq2C P isAny (ReIter.ofIterable { items }) ov)))
  | "c_clear" =>
    return some (okJ Json.null, { st with ds := st.ds.set! i (dictClearChecked (isAny && !d.frozen) d) })
  | "c_copy" =>
    let (id, st) := fresh st
    return some (toDSlot2 st (pyDictCopyC P isAny d id true (.dict d)))
  | "c_size" =>
    return some ((if isAny then okJ (toJson d.used) else errJ badInternalCall), st)
  | "c_keys" =>
    return some ((if isAny then okJ (encs (dictKeysList d)) else errJ badInternalCall), st)
  | "c_values" =>
    return some ((if isAny then okJ (encs (dictValuesList d)) else errJ badInternalCall), st)
  | "c_items" =>
    return some ((if isAny then okJ (Json.arr ((dictItemsList d).map encPair).toArray)
      else errJ badInternalCall), st)
  | "c_kw" =>
    let j ← argN a 2
    let (r1, s1) := dictMerge P (.dict d) 2 ({ ident := 0 } : DD)
    let (r2, s2) := match r1 with
      | .ok _ => dictMerge P (.dict st.ds[j]!) 2 s1
      | .error e => (.error e, s1)
    match r2 with
    | .ok _ =>
      let ks := dictKeysList s2
      if ks.all (fun x => dProto.isStrLike x) then
        return some (okJ (Json.arr #[toJson "ok", encs ks]), st)
      else return some (errJ (.typeError "keywords must be strings"), st)
    | .error e =>
      if e == mergeDupExc then
        match s2.dupkey with
        | some x => return some (okJ (Json.arr #[toJson "dup", toJson s!"'{strOf x}'"]), st)
        | none => throw "dupkey"
      else return some (errJ e, st)
  | "c_sin" =>
    return some (resJ toJson (withS st i (pySetContains S isAny (← k 2))))
  | "c_sdisc" =>
    return some (resJ toJson (withS st i (pySetDiscard S (isAny && !so.frozen) (← k 2))))
  | "c_sadd" =>
    return some (resJ unitJ (withS st i (pySetAdd S (isAny && !so.frozen) false (← k 2))))
  | "c_spop" =>
    if isAny && !so.frozen then return some (resJ enc (withS st i setPop))
    else return some (errJ setBadInternalCall, st)
  | "c_ssize" =>
    return some ((if isAny then okJ (toJson so.used) else errJ setBadInternalCall), st)
  | "c_sclear" =>
    if isAny && !so.frozen then
      return some (okJ Json.null, { st with ss := st.ss.set! i (setClearInternal so) })
    else return some (errJ setBadInternalCall, st)
  | _ => return none

def encKV (kind : IterKind) (p : DObj × DObj) : Json :=
  match kind.result p with
  | .key k => enc k
  | .value v => enc v
  | .item k v => encPair (k, v)

/-- `frozendict` operations on slot 2. -/
def stepFz (st : St) (name : String) (a : Array Json) : Except String (Option (Json × St)) := do
  let P := dProto
  let d := st.ds[2]!
  let kwOf (j : Json) : Except String (List (DObj × DObj)) := do
    (← arrOf j).mapM fun p => do
      let q ← p.getArr?
      return ((← obj st (← arg q 0)), (← obj st (← arg q 1)))
  let toSlot (r : Py DD) (st : St) : Json × St :=
    match r with
    | .ok x => (okJ Json.null, { st with ds := st.ds.set! 2 x })
    | .error e => (errJ e, st)
  match name with
  | "fz" =>
    let (id, st) := fresh st
    let shell : DD := { ident := id, frozen := true }
    let u ← updArg st (← arg a 1)
    return some (toSlot (frozendictVectorcall P shell [u] (← kwOf (← arg a 2))) st)
  | "fz0" =>
    let (id, st) := fresh st
    return some (toSlot (frozendictVectorcall P ({ ident := id, frozen := true } : DD) [] []) st)
  | "fz2" =>
    let u ← updArg st (← arg a 1)
    return some (toSlot (frozendictVectorcall P ({ frozen := true } : DD) [u, u] []) st)
  | "f_or" =>
    let j ← argN a 1
    let (id, st) := fresh st
    let other := st.ds[j]!
    let r := if d.frozen then
        frozendictOr315 P ⟨true, true, d⟩ ⟨true, true, other⟩ id true (.dict d) (.exact other)
      else pyDictOr P true true d id true (.dict d) (.exact other)
    match r with
    | .ok (some r) => return some (okJ Json.null, { st with ds := st.ds.set! 2 r })
    | .ok none => throw "f_or"
    | .error e => return some (errJ e, st)
  | "f_hash" =>
    if !d.frozen then return some (errJ (.typeError "unhashable type: 'dict'"), st)
    let (r, d') := frozendictHash DObj.hash d
    return some (enc1 toJson r, { st with ds := st.ds.set! 2 d' })
  | "f_fromkeys" =>
    let v ← obj st (← arg a 2)
    let t ← (← arg a 1).getArr?
    return some (← runFromkeys st P true t v)
  | "f_it" =>
    let kind : IterKind ← match ← (← arg a 1).getStr? with
      | "k" => pure .key
      | "v" => pure .value
      | _ => pure .item
    let rev ← (← arg a 2).getBool?
    let (r, _) := dictiterToList d (dictiterNew d kind rev)
    return some (enc1 (fun l => Json.arr (l.map (encKV kind)).toArray) r, st)
  | "m_get" =>
    -- `['m_get', frozen, slot, key, how, value]`: a subclass of dict or frozendict, by `__missing__`.
    let frozen ← (← arg a 1).getBool?
    let slot ← argN a 2
    let key ← obj st (← arg a 3)
    let how ← argN a 4
    let v ← obj st (← arg a 5)
    let look : DM DObj DObj (Option (DObj → DM DObj DObj DObj)) := match how with
      | 0 => pure none
      | 1 => pure (some fun _ => pure v)
      | 2 => pure (some fun _ => M.throw (.valueError "miss"))
      | _ => M.throw (.valueError "look")
    let (r, _) := dictSubscript P (some look) key { st.ds[slot]! with frozen }
    return some (enc1 enc r, st)
  | _ => return none

def stepDict (st : St) (name : String) (a : Array Json) : Except String (Option (Json × St)) := do
  let i := (a[1]?.bind fun j => j.getNat?.toOption).getD 0
  let k (n : Nat) : Except String DObj := do obj st (← arg a n)
  let P := protoAt st i
  match name with
  | "set" => return some (resJ unitJ (withD st i (dictSetItem P (← k 2) (← k 3))))
  | "get" => return some (resJ enc (withD st i (dictSubscript P none (← k 2))))
  | "del" => return some (resJ unitJ (withD st i (dictDelItem P (← k 2))))
  | "in" => return some (resJ toJson (withD st i (pyDictContains P (← k 2))))
  | "getd" => return some (resJ enc (withD st i (dictGet P (← k 2) (← k 3))))
  | "sdef" => return some (resJ enc (withD st i (dictSetdefault P (← k 2) (← k 3))))
  | "pop" => return some (resJ enc (withD st i (dictPopDefault P (← k 2) none)))
  | "popd" => return some (resJ enc (withD st i (dictPopDefault P (← k 2) (some (← k 3)))))
  | "popitem" => return some (resJ encPair (withD st i dictPopitem))
  | "clear" => return some (okJ Json.null, { st with ds := st.ds.set! i (dictClear st.ds[i]!) })
  | "len" => return some (okJ (toJson st.ds[i]!.used), st)
  | "keys" => return some (okJ (encs (dictKeysList st.ds[i]!)), st)
  | "values" => return some (okJ (encs (dictValuesList st.ds[i]!)), st)
  | "items" => return some (okJ (Json.arr ((dictItemsList st.ds[i]!).map encPair).toArray), st)
  | "repr" =>
    let d := st.ds[i]!
    let rp := evilRepr st.pool (st.tgt == some i)
    let fuel := 100000
    let (r, d') := (if d.frozen then frozendictRepr315 "frozendict" (.ok false) rp rp fuel
      else anydictRepr (.ok false) rp rp fuel) d
    return some (enc1 toJson r, { st with ds := st.ds.set! i d' })
  | "upd" =>
    let u ← updArg st (← arg a 2)
    let kw ← (← arrOf (← arg a 3)).mapM fun p => do
      let q ← p.getArr?
      return ((← obj st (← arg q 0)), (← obj st (← arg q 1)))
    let kwd : Option DD :=
      if kw.isEmpty then none
      else match dictFromItems P 0 kw with
        | .ok d => some d
        | .error _ => none
    return some (takeNote i (resJ unitJ (withD st i (dictUpdate P [u] kwd))))
  | "ior" =>
    let u ← updArg st (← arg a 2)
    return some (takeNote i (resJ (fun _ => Json.null) (withD st i (pyDictIOr P u))))
  | "or" =>
    let j ← argN a 2
    let (id, st) := fresh st
    let d := st.ds[i]!
    let other := st.ds[j]!
    let r := if d.frozen then
        frozendictOr315 P ⟨true, true, d⟩ ⟨true, true, other⟩ id true (.dict d) (.exact other)
      else pyDictOr P true true d id true (.dict d) (.exact other)
    match r with
    | .ok (some r) => return some (okJ Json.null, { st with ds := st.ds.set! 2 r })
    | .ok none => throw "or"
    | .error e => return some (errJ e, st)
  | "copy" =>
    let (id, st) := fresh st
    let d := st.ds[i]!
    if d.frozen then return some (toDSlot2 st (frozendictCopyImpl P d true id true (.dict d)))
    return some (toDSlot2 st (dictCopyImpl P d id true (.dict d)))
  | "copy_ks" =>
    -- `['copy_ks', slot]`: `KSub(d).copy()`, a subclass whose `__iter__` and `keys()` are
    -- overridden, so `copy` takes the slow route of `dict_merge` through `keys()` and `o[key]`.
    let (id, st) := fresh st
    let (_, sub) := dictMerge dProto (.dict st.ds[i]!) 1 ({ ident := id } : DD)
    let (id2, st) := fresh st
    let asMap : MergeArg DObj DObj :=
      .mapping (pure (ReIter.ofKeys (dictKeysList sub).reverse)) fun key s =>
        ((dictSubscript dProto none key sub).1, s)
    return some (toDSlot2 st (dictCopyImpl dProto sub id2 false asMap))
  | "eq" =>
    let j ← argN a 2
    let ne ← (← arg a 3).getBool?
    let alias := i == j
    let P := protoAt st j
    let veq : DObj → DObj → DM DObj DObj Bool :=
      if st.tgt.isSome then evilVeq st.pool (st.tgt == some j) else fun x y s => (DObj.eq x y, s)
    let b0 : DD := if alias then st.ds[j]! else { st.ds[j]! with peer := some st.ds[i]!.toPeer }
    let (r, b') := dictRichcompare315 P true true (if ne then .ne else .eq) veq alias 100000 b0
    let st := if alias then st else
      match b'.peer with
      | some p => fromPeer st i p
      | none => st
    let st := { st with ds := st.ds.set! j { b' with peer := none } }
    let encB : Option Bool → Json := fun o => match o with
      | some c => toJson c
      | none => Json.null
    return some (enc1 encB r, st)
  | "fromkeys" =>
    let v ← k 3
    let t ← (← arg a 2).getArr?
    let srcSlot : Option Nat := t[1]?.bind fun j => j.getNat?.toOption
    let P := match st.tgt, srcSlot with
      | some tt, some s => if tt == s then peerProto st.pool else dProto
      | _, _ => dProto
    return some (← runFromkeys st P false t v)
  | "fromitems" =>
    let ps ← (← arrOf (← arg a 2)).mapM fun p => do
      let q ← p.getArr?
      return ((← obj st (← arg q 0)), (← obj st (← arg q 1)))
    let (id, st) := fresh st
    return some (toDSlot2 st (dictFromItems P id ps))
  | "dict" =>
    let (id, st) := fresh st
    let (r, d) := dictVectorcall P [← updArg st (← arg a 2)] [] ({ ident := id } : DD)
    match r with
    | .ok _ => return some (okJ Json.null, { st with ds := st.ds.set! 2 d })
    | .error e => return some (withNote d.note (errJ e), st)
  | _ => return none

def stepIter (st : St) (name : String) (a : Array Json) : Except String (Option (Json × St)) := do
  let setIt (st : St) (n : Nat) (it : It) : St := { st with its := st.its.set! n (some it) }
  match name with
  | "it_new" =>
    let n ← argN a 1
    let slot ← argN a 2
    let kind : IterKind ← match ← (← arg a 3).getStr? with
      | "k" => pure .key
      | "v" => pure .value
      | _ => pure .item
    let rev ← (← arg a 4).getBool?
    return some (okJ Json.null, setIt st n (.d slot (dictiterNew st.ds[slot]! kind rev)))
  | "sit_new" =>
    let n ← argN a 1
    let slot ← argN a 2
    return some (okJ Json.null, setIt st n (.s slot (setIterNew st.ss[slot]!)))
  | "it_next" =>
    let n ← argN a 1
    match st.its[n]! with
    | none => throw "no iterator"
    | some (.d slot di) =>
      let (r, di') := dictiterNext st.ds[slot]! di
      let st := setIt st n (.d slot di')
      match r with
      | .ok (some p) => return some (okJ (encKV di.kind p), st)
      | .ok none => return some (errJ .stopIteration, st)
      | .error e => return some (errJ e, st)
    | some (.s slot si) =>
      let (r, si') := setiterNext st.ss[slot]! si
      let st := setIt st n (.s slot si')
      match r with
      | .ok (some p) => return some (okJ (enc p), st)
      | .ok none => return some (errJ .stopIteration, st)
      | .error e => return some (errJ e, st)
  | "it_hint" =>
    let n ← argN a 1
    match st.its[n]! with
    | none => throw "no iterator"
    | some (.d slot di) => return some (okJ (toJson (dictiterLen st.ds[slot]! di)), st)
    | some (.s slot si) => return some (okJ (toJson (setiterLen st.ss[slot]! si)), st)
  | "it_list" =>
    let n ← argN a 1
    match st.its[n]! with
    | none => throw "no iterator"
    | some (.d slot di) =>
      let (r, di') := dictiterToList st.ds[slot]! di
      return some (enc1 (fun l => Json.arr (l.map (encKV di.kind)).toArray) r, setIt st n (.d slot di'))
    | some (.s slot si) =>
      let (r, si') := setiterToList st.ss[slot]! si
      return some (enc1 encs r, setIt st n (.s slot si'))
  | "it_reduce" =>
    let n ← argN a 1
    match st.its[n]! with
    | none => throw "no iterator"
    | some (.d slot di) =>
      let r := dictiterReduce st.ds[slot]! di
      return some (enc1 (fun l => Json.arr (l.map (encKV di.kind)).toArray) r, st)
    | some (.s slot si) =>
      return some (enc1 encs (setiterReduce st.ss[slot]! si), st)
  | _ => return none

def stepSet (st : St) (name : String) (a : Array Json) : Except String (Option (Json × St)) := do
  let i := (a[1]?.bind fun j => j.getNat?.toOption).getD 0
  let k (n : Nat) : Except String DObj := do obj st (← arg a n)
  let P := match st.stgt with
    | some t => sProtoAt st.pool st.ss[t]!.ident
    | none => sProto
  let sh := testKeySet
  let argsAt (n : Nat) : Except String (List (SetArg DObj)) := do
    (← arrOf (← arg a n)).mapM (setArg st)
  let so := st.ss[i]!
  match name with
  | "sadd" => return some (resJ unitJ (withS st i (setAddKey P (← k 2))))
  | "srem" => return some (resJ unitJ (withS st i (setRemove P sh (← k 2))))
  | "sdisc" => return some (resJ unitJ (withS st i (setDiscard P sh (← k 2))))
  | "sin" => return some (resJ toJson (withS st i (setContains P sh (← k 2))))
  | "fin" =>
    -- `type(s).__contains__(s, key)`.
    if so.frozen then return some (resJ toJson (withS st i (frozensetContains P sh (← k 2))))
    return some (resJ toJson (withS st i (setContains P sh (← k 2))))
  | "spop" => return some (resJ enc (withS st i setPop))
  | "sclear" => return some (okJ Json.null, { st with ss := st.ss.set! i (setClearInternal so) })
  | "slen" => return some (okJ (toJson so.used), st)
  | "srepr" =>
    return some (enc1 toJson (setRepr (fun x => .ok x.reprStr) false so), st)
  | "shash" =>
    return some (okJ (toJson (frozensetHashImpl so)), st)
  | "supd" => return some (resJ unitJ (withS st i (setUpdateMulti P (← argsAt 2))))
  | "sunion" =>
    let (id, st) := fresh st
    return some (toSlot2S st i (setUnion P (← argsAt 2) id))
  | "sinter" =>
    let (id, st) := fresh st
    return some (toSlot2S st i (setIntersectionMulti P (← argsAt 2) id))
  | "sdiff" =>
    let (id, st) := fresh st
    return some (toSlot2S st i (setDifferenceMulti P (← argsAt 2) id))
  | "ssym" =>
    let (id, st) := fresh st
    return some (toSlot2S st i (setSymmetricDifference P (← setArg st (← arg a 2)) id))
  | "scopy" =>
    let (id, st) := fresh st
    return some (toSlot2S st i (setCopy P id))
  | "sinterupd" =>
    let (id, st) := fresh st
    return some (resJ unitJ (withS st i (setIntersectionUpdateMulti P (← argsAt 2) id)))
  | "sdiffupd" =>
    let (id, st) := fresh st
    return some (resJ unitJ (withS st i (setDifferenceUpdateMulti P (← argsAt 2) id)))
  | "ssymupd" =>
    let (id, st) := fresh st
    return some (resJ unitJ (withS st i (setSymmetricDifferenceUpdate P (← setArg st (← arg a 2)) id)))
  | "sdisj" => return some (resJ toJson (withS st i (setIsdisjoint P (← setArg st (← arg a 2)))))
  | "ssubset" =>
    let (id, st) := fresh st
    return some (resJ toJson (withS st i (setIssubset P (← setArg st (← arg a 2)) id)))
  | "ssuper" =>
    let (id, st) := fresh st
    return some (resJ toJson (withS st i (setIssuperset P (← setArg st (← arg a 2)) id)))
  | "scmp" =>
    let j ← argN a 2
    let (id, st) := fresh st
    return some (resJ toJson (withS st i (setRichcompare P st.ss[j]! (← cmpOf (← (← arg a 3).getStr?)) id)))
  | "sor" =>
    let j ← argN a 2
    let (id, st) := fresh st
    return some (toSlot2S st i (setOr P st.ss[j]! id))
  | "sand" =>
    let j ← argN a 2
    let (id, st) := fresh st
    return some (toSlot2S st i (setIntersection P (.set st.ss[j]!) id))
  | "ssub" =>
    let j ← argN a 2
    let (id, st) := fresh st
    return some (toSlot2S st i (setDifference P (.set st.ss[j]!) id))
  | "sxor" =>
    let j ← argN a 2
    let (id, st) := fresh st
    return some (toSlot2S st i (setSymmetricDifference P (.set st.ss[j]!) id))
  | "sior" =>
    let j ← argN a 2
    return some (resJ unitJ (withS st i (setUpdate P (.set st.ss[j]!))))
  | "siand" =>
    let j ← argN a 2
    let (id, st) := fresh st
    return some (resJ unitJ (withS st i (setIntersectionUpdate P (.set st.ss[j]!) id)))
  | "sisub" =>
    let j ← argN a 2
    let (id, st) := fresh st
    return some (resJ unitJ (withS st i (setDifferenceUpdateInternal P (.set st.ss[j]!) id)))
  | "sixor" =>
    let j ← argN a 2
    let (id, st) := fresh st
    return some (resJ unitJ (withS st i (setSymmetricDifferenceUpdate P (.set st.ss[j]!) id)))
  | "sinit" =>
    return some (resJ unitJ (withS st i (setInit P [← setArg st (← arg a 2)] false)))
  | "snew" =>
    let (id, st) := fresh st
    return some (toSlot2 st (setVectorcall P id [← setArg st (← arg a 2)] false))
  | "fnew" =>
    let (id, st) := fresh st
    return some (toSlot2 st (frozensetVectorcall P id [← setArg st (← arg a 2)] false))
  | _ => return none

def stepView (st : St) (name : String) (a : Array Json) : Except String (Option (Json × St)) := do
  let E := dEnv
  match name with
  | "v_sub" | "v_or" | "v_xor" | "v_and" =>
    let v ← viewArg st (← arg a 1)
    let o ← viewArg st (← arg a 2)
    let (id, st) := fresh st
    let r : Py DS := match name, v with
      | "v_sub", _ => dictviewsSub E v o id
      | "v_or", _ => dictviewsOr E v o id
      | "v_xor", _ => dictviewsXor E v o id
      | _, .view self => dictviewIntersect E self o id
      | _, _ => .error .modelFuel
    return some (toSlot2 st r)
  | "v_cmp" =>
    let v ← viewArg st (← arg a 1)
    let o ← viewArg st (← arg a 2)
    let op ← cmpOf (← (← arg a 3).getStr?)
    match v with
    | .view self => return some (enc1 toJson (dictviewRichcompare E self o op), st)
    | _ => throw "v_cmp"
  | "v_disj" =>
    let v ← viewArg st (← arg a 1)
    let o ← viewArg st (← arg a 2)
    let same ← (← arg a 3).getBool?
    match v with
    | .view self => return some (enc1 toJson (dictviewsIsdisjoint E self o same), st)
    | _ => throw "v_disj"
  | "v_in" =>
    let v ← viewArg st (← arg a 1)
    let x ← obj st (← arg a 2)
    match v with
    | .view self => return some (enc1 toJson (viewContains E self x), st)
    | _ => throw "v_in"
  | "v_intup" =>
    -- `(k, v) in d.items()`
    let v ← viewArg st (← arg a 1)
    let x := DObj.tuple (← obj st (← arg a 2)) (← obj st (← arg a 3))
    match v with
    | .view self => return some (enc1 toJson (viewContains E self x), st)
    | _ => throw "v_intup"
  | "v_len" =>
    match ← viewArg st (← arg a 1) with
    | .view self => return some (okJ (toJson (dictviewLen self)), st)
    | _ => throw "v_len"
  | _ => return none

/-- `__map`'s comparison: a plain dict of the same keys. -/
def mapProto : Proto DObj (PyDict DObj Nat) :=
  { dKeyOps with eq := fun a b s => (DObj.eq a b, s) }

def pairItem (twin : Bool) (st : St) (j : Json) : Except String (PairItem DObj DObj) := do
  let a ← j.getArr?
  let tag ← (← arg a 0).getStr?
  match tag with
  | "p" => return .pair (← obj st (← arg a 1)) (← obj st (← arg a 2))
  | "b" =>
    return .notIter (.typeError (if twin then "cannot unpack non-iterable int object"
                                 else "'int' object is not iterable"))
  | "l" => return .wrong (← argN a 1)
  | t => throw s!"pair item {t}"

/-- `['d', slot]`, `['m', keys, pairs]`, `['p', items, stop]`, `['it', items, iter]`, `['n']`. -/
def odArg (twin : Bool) (st : St) (j : Json) : Except String (ODictArg DObj DObj) := do
  let a ← j.getArr?
  let tag ← (← arg a 0).getStr?
  let pitems (x : Json) : Except String (List (PairItem DObj DObj)) := do
    (← arrOf x).mapM (pairItem twin st)
  match tag with
  | "d" | "fd" => return .exact st.ds[← argN a 1]!
  | "m" =>
    let ks ← objs st (← arg a 1)
    let ps ← (← arrOf (← arg a 2)).mapM fun p => do
      let q ← p.getArr?
      return ((← obj st (← arg q 0)), (← obj st (← arg q 1)))
    return .keysObj { items := ks } fun k =>
      match ps.find? (fun p => p.1 == k) with
      | some p => .ok p.2
      | none => .error (keyErr dProto k)
  | "p" =>
    let stop ← (← arg a 2).getBool?
    return .pairs { items := ← pitems (← arg a 1)
                    stop := if stop then some (.valueError "stop") else none }
  | "it" => return .itemsObj { items := ← pitems (← arg a 1) } { items := ← pitems (← arg a 2) }
  | "n" => return .pairs { getIter := some (.typeError "'int' object is not iterable"), items := [] }
  | t => throw s!"od arg {t}"

def withO {α : Type} (st : St) (i : Nat) (m : OM DObj DObj α) : Py α × St :=
  let (r, d) := m st.ods[i]!
  (r, { st with ods := st.ods.set! i d })

def withP {α : Type} (st : St) (i : Nat) (m : PM DObj DObj α) : Py α × St :=
  let (r, d) := m st.pods[i]!
  (r, { st with pods := st.pods.set! i d })

def encKVo (kind : IterKind) (p : DObj × Option DObj) : Json :=
  match kind, p.2 with
  | .value, some v => enc v
  | .item, some v => Json.arr #[enc p.1, enc v]
  | _, _ => enc p.1

def iterKindOf (s : String) : IterKind :=
  match s with
  | "k" => .key
  | "v" => .value
  | _ => .item

def stepOD (st : St) (name : String) (a : Array Json) : Except String (Option (Json × St)) := do
  let i := (a[1]?.bind fun j => j.getNat?.toOption).getD 0
  let k (n : Nat) : Except String DObj := do obj st (← arg a n)
  let P := dProto
  match name with
  | "o_set" => return some (resJ unitJ (withO st i (odictSetItem P (← k 2) (← k 3))))
  | "o_del" => return some (resJ unitJ (withO st i (odictDelItem P (← k 2))))
  | "o_get" => return some (resJ enc (withO st i (onDict (dictSubscript P none (← k 2)))))
  | "o_in" => return some (resJ toJson (withO st i (onDict (pyDictContains P (← k 2)))))
  | "o_pop" => return some (resJ enc (withO st i (odictPop P (← k 2) none)))
  | "o_popd" => return some (resJ enc (withO st i (odictPop P (← k 2) (some (← k 3)))))
  | "o_popitem" =>
    return some (resJ encPair (withO st i (odictPopitem P (← (← arg a 2).getBool?))))
  | "o_sdef" => return some (resJ enc (withO st i (odictSetdefault P (← k 2) (← k 3))))
  | "o_mte" =>
    return some (resJ unitJ (withO st i (odictMoveToEnd P (← k 2) (← (← arg a 3).getBool?))))
  | "o_clear" => return some (okJ Json.null, { st with ods := st.ods.set! i (odictClear st.ods[i]!) })
  | "o_copy" =>
    let (id, st) := fresh st
    match odictCopy P st.ods[i]! id with
    | .ok r => return some (okJ Json.null, { st with ods := st.ods.set! 2 r })
    | .error e => return some (errJ e, st)
  | "o_upd" =>
    let kw ← (← arrOf (← arg a 3)).mapM fun p => do
      let q ← p.getArr?
      return ((← obj st (← arg q 0)), (← obj st (← arg q 1)))
    return some (resJ unitJ (withO st i (mutablemappingUpdate P [← odArg false st (← arg a 2)] kw)))
  | "o_ior" =>
    return some (resJ unitJ (withO st i (odictInplaceOr P (← odArg false st (← arg a 2)))))
  | "o_or" =>
    let (id, st) := fresh st
    let (r, left') := odictOr P st.ods[i]! id (← odArg false st (← arg a 2))
    let st := { st with ods := st.ods.set! i left' }
    match r with
    | .ok r => return some (okJ Json.null, { st with ods := st.ods.set! 2 r })
    | .error e => return some (errJ e, st)
  | "o_eq" =>
    let j ← argN a 2
    let ne ← (← arg a 3).getBool?
    return some (enc1 toJson (odictRichcompare P dEnv.veq st.ods[i]! st.ods[j]! ne), st)
  | "o_eqd" =>
    let j ← argN a 2
    let ne ← (← arg a 3).getBool?
    return some (enc1 toJson (odictEqDict P dEnv.veq st.ods[i]! st.ds[j]! ne), st)
  | "o_fromkeys" =>
    let (id, st) := fresh st
    match odictFromkeys P id { items := ← objs st (← arg a 2) } (← k 3) with
    | .ok r => return some (okJ Json.null, { st with ods := st.ods.set! 2 r })
    | .error e => return some (errJ e, st)
  | "o_repr" =>
    return some (enc1 toJson (odictRepr P (fun x => .ok x.reprStr) (fun x => .ok x.reprStr)
      "OrderedDict" false st.ods[i]!), st)
  | "o_itnew" =>
    let n ← argN a 1
    let slot ← argN a 2
    let kind := iterKindOf (← (← arg a 3).getStr?)
    let rev ← (← arg a 4).getBool?
    return some (okJ Json.null,
      { st with oits := st.oits.set! n (some (odictiterNew st.ods[slot]! kind rev)) })
  | "o_itnext" =>
    let n ← argN a 1
    let slot ← argN a 2
    match st.oits[n]! with
    | none => throw "no iterator"
    | some di =>
      let (r, di', od') := odictiterIternext P st.ods[slot]! di
      let st := { st with oits := st.oits.set! n (some di'), ods := st.ods.set! slot od' }
      match r with
      | .ok (some x) => return some (okJ (encKVo di.kind x), st)
      | .ok none => return some (errJ .stopIteration, st)
      | .error e => return some (errJ e, st)
  -- The underlying dict, bypassing the odict.
  | "r_set" => return some (resJ unitJ (withO st i (onDict (dictSetItem P (← k 2) (← k 3)))))
  | "r_del" => return some (resJ unitJ (withO st i (onDict (dictDelItem P (← k 2)))))
  | "r_popitem" => return some (resJ encPair (withO st i (onDict dictPopitem)))
  | "r_pop" => return some (resJ enc (withO st i (onDict (dictPopDefault P (← k 2) none))))
  | "r_clear" =>
    let od := st.ods[i]!
    return some (okJ Json.null, { st with ods := st.ods.set! i { od with d := dictClear od.d } })
  | _ => return none

def stepPOD (st : St) (name : String) (a : Array Json) : Except String (Option (Json × St)) := do
  let i := (a[1]?.bind fun j => j.getNat?.toOption).getD 0
  let k (n : Nat) : Except String DObj := do obj st (← arg a n)
  let P := dProto
  let Q := mapProto
  match name with
  | "p_set" => return some (resJ unitJ (withP st i (pyodSetItem P Q (← k 2) (← k 3))))
  | "p_del" => return some (resJ unitJ (withP st i (pyodDelItem P Q (← k 2))))
  | "p_get" => return some (resJ enc (withP st i (onD (dictSubscript P none (← k 2)))))
  | "p_in" => return some (resJ toJson (withP st i (onD (pyDictContains P (← k 2)))))
  | "p_pop" => return some (resJ enc (withP st i (pyodPop P Q (← k 2) none)))
  | "p_popd" => return some (resJ enc (withP st i (pyodPop P Q (← k 2) (some (← k 3)))))
  | "p_popitem" =>
    return some (resJ encPair (withP st i (pyodPopitem P Q (← (← arg a 2).getBool?))))
  | "p_sdef" => return some (resJ enc (withP st i (pyodSetdefault P Q (← k 2) (← k 3))))
  | "p_mte" =>
    return some (resJ unitJ (withP st i (pyodMoveToEnd Q (← k 2) (← (← arg a 3).getBool?))))
  | "p_clear" => return some (okJ Json.null, { st with pods := st.pods.set! i (pyodClear st.pods[i]!) })
  | "p_copy" =>
    let (id, st) := fresh st
    match pyodCopy P Q st.pods[i]! id with
    | .ok r => return some (okJ Json.null, { st with pods := st.pods.set! 2 r })
    | .error e => return some (errJ e, st)
  | "p_upd" =>
    let kw ← (← arrOf (← arg a 3)).mapM fun p => do
      let q ← p.getArr?
      return ((← obj st (← arg q 0)), (← obj st (← arg q 1)))
    return some (resJ unitJ (withP st i (pyodUpdate P Q (some (← odArg true st (← arg a 2))) kw)))
  | "p_ior" =>
    return some (resJ unitJ (withP st i (pyodIor P Q (← odArg true st (← arg a 2)))))
  | "p_or" =>
    let (id, st) := fresh st
    match pyodOr P Q st.pods[i]! id (← odArg true st (← arg a 2)) with
    | .ok r => return some (okJ Json.null, { st with pods := st.pods.set! 2 r })
    | .error e => return some (errJ e, st)
  | "p_eq" =>
    let j ← argN a 2
    let ne ← (← arg a 3).getBool?
    let r := pyodEq P dEnv.veq DObj.plainEq st.pods[i]! st.pods[j]!
    return some (enc1 (fun b => toJson (b != ne)) r, st)
  | "p_fromkeys" =>
    let (id, st) := fresh st
    match pyodFromkeys P Q id { items := ← objs st (← arg a 2) } (← k 3) with
    | .ok r => return some (okJ Json.null, { st with pods := st.pods.set! 2 r })
    | .error e => return some (errJ e, st)
  | "p_itnew" =>
    let n ← argN a 1
    let slot ← argN a 2
    let kind := iterKindOf (← (← arg a 3).getStr?)
    let rev ← (← arg a 4).getBool?
    return some (okJ Json.null, { st with gens := st.gens.set! n (some (slot, kind, { rev })) })
  | "p_itnext" =>
    let n ← argN a 1
    match st.gens[n]! with
    | none => throw "no generator"
    | some (slot, kind, g) =>
      let o := st.pods[slot]!
      let (r, g') := pyodGenNext o g
      let st := { st with gens := st.gens.set! n (some (slot, kind, g')) }
      match r with
      | .ok (some x) =>
        match kind with
        | .key => return some (okJ (enc x), st)
        | _ =>
          -- `yield self._mapping[key]`, `yield (key, self._mapping[key])`
          match (dictSubscript P none x o.d).1 with
          | .ok v =>
            return some (okJ (match kind with
              | .value => enc v
              | _ => Json.arr #[enc x, enc v]), st)
          | .error e =>
            return some (errJ e, { st with gens := st.gens.set! n (some (slot, kind, { g' with state := .done })) })
      | .ok none => return some (errJ .stopIteration, st)
      | .error e => return some (errJ e, st)
  | _ => return none

/-- The state of instance `n`, as `Managed.lean` wants it, and writing it back. -/
def objSt (st : St) (n : Nat) : ObjSt DObj DObj :=
  { keys := st.keys, inst := st.insts[n]!.getD default, nextDict := st.nextDict }

def putObj (st : St) (n : Nat) (s : ObjSt DObj DObj) : St :=
  { st with keys := s.keys, insts := st.insts.set! n (some s.inst), nextDict := s.nextDict }

def withI {α : Type} (st : St) (n : Nat) (m : IM DObj DObj α) : Py α × St :=
  let (r, s) := m (objSt st n)
  (r, putObj st n s)

/-- `object.__delattr__`: a `KeyError` from the dict becomes `AttributeError`
(`_PyObject_GenericSetAttrWithDict`). -/
def delAttrErr (st : St) (name : DObj) (r : Json × St) : Json × St :=
  match r.1.getObjVal? "exc" with
  | .ok (.str "KeyError") =>
    (errJ (attributeError s!"'C' object has no attribute {name.reprStr}"), r.2)
  | _ => r

def stepInst (st : St) (name : String) (a : Array Json) : Except String (Option (Json × St)) := do
  let n := (a[1]?.bind fun j => j.getNat?.toOption).getD 0
  let k (i : Nat) : Except String DObj := do obj st (← arg a i)
  let P := dProto
  let touch (st : St) : St := { st with touched := st.touched.set! n true }
  match name with
  | "i_new" =>
    let (keys', inst) := initInlineValues st.keys
    return some (okJ Json.null, { st with
      keys := keys', insts := st.insts.set! n (some inst), touched := st.touched.set! n false })
  | "i_set" =>
    return some (resJ unitJ (withI st n (storeInstanceAttribute P "C" (← k 2) (some (← k 3)))))
  | "i_del" =>
    let nm ← k 2
    let r := resJ unitJ (withI st n (storeInstanceAttribute P "C" nm none))
    return some (delAttrErr st nm r)
  | "i_get" =>
    let nm ← k 2
    let (r, st') := withI st n (genericGetAttr P nm)
    match r with
    | .ok (some v) => return some (okJ (enc v), st')
    | .ok none => return some (errJ (attributeError s!"'C' object has no attribute {nm.reprStr}"), st')
    | .error e => return some (errJ e, st')
  | "i_dict" =>
    return some (resJ (fun _ => Json.null) (withI (touch st) n ensureManagedDict))
  | "i_deldict" =>
    let st' := putObj st n (setManagedDict (objSt st n) none)
    return some (okJ Json.null, { st' with touched := st'.touched.set! n false })
  | "i_setdict" =>
    let ps ← (← arrOf (← arg a 2)).mapM fun p => do
      let q ← p.getArr?
      return ((← obj st (← arg q 0)), (← obj st (← arg q 1)))
    let (id, st) := fresh st
    match dictFromItems P id ps with
    | .error e => return some (errJ e, st)
    | .ok d =>
      let st' := putObj st n (setManagedDict (objSt st n) (some d))
      return some (okJ Json.null, touch st')
  | "i_copy" =>
    let (id, st) := fresh st
    let (r, st') := withI (touch st) n ensureManagedDict
    match r with
    | .error e => return some (errJ e, st')
    | .ok d => return some (toDSlot2 st' (dictCopy P (refreshKeys st'.keys d) id false (.dict d)))
  | "i_d" =>
    -- A dict operation on `o.__dict__`: run the dict handler with the dict in a scratch slot.
    let (r, st') := withI (touch st) n ensureManagedDict
    match r with
    | .error e => return some (errJ e, st')
    | .ok d =>
      let sub := (← arg a 2)
      let b ← sub.getArr?
      let inner ← (← arg b 0).getStr?
      let d' := refreshKeys st'.keys d
      let before := isInlineDict d'
      let st2 := { st' with ds := st'.ds.set! 2 d' }
      match ← stepDict st2 inner (#[Json.str inner, toJson (2 : Nat)] ++ b.extract 1 b.size) with
      | none => throw s!"i_d {inner}"
      | some (res, st3) =>
        let s := objSt st3 n
        let s' := syncDict before st3.ds[2]! s
        return some (res, touch (putObj { st3 with ds := st3.ds.set! 2 st'.ds[2]! } n s'))
  | _ => return none

def step (st : St) (op : Json) : Except String (Json × St) := do
  let a ← op.getArr?
  let name ← (← arg a 0).getStr?
  if let some r := ← stepC st name a then return r
  if let some r := ← stepFz st name a then return r
  if let some r := ← stepDict st name a then return r
  if let some r := ← stepIter st name a then return r
  if let some r := ← stepSet st name a then return r
  if let some r := ← stepView st name a then return r
  if let some r := ← stepOD st name a then return r
  if let some r := ← stepPOD st name a then return r
  if let some r := ← stepInst st name a then return r
  throw s!"unknown op {name}"

/-- `[__sizeof__, dict.keys(od), list(od)]`. `list(od)` can rebuild `od_fast_nodes`, so the
digest threads the state, as the Python side does by running the same code. -/
def digestOD (limit : Nat) (od : OD) : Json × OD :=
  let size := odictSizeOf od
  let ks := dictKeysList od.d
  let (r, _, od') := odictiterTake dProto limit od (odictiterNew od .key false) []
  (Json.arr #[toJson size, encs ks, enc1 (fun l => encs (l.map (·.1))) r], od')

def digestPOD (o : POD) : Json :=
  Json.arr #[encs (dictKeysList o.d), encs (dictValuesList o.d), encs o.keysList]

/-- Digest of instance `n`: every attribute by name; and the dict, if the scenario has looked
at it (a digest must not materialize one). -/
def digestInst (st : St) (n : Nat) : Except String (Json × St) := do
  match st.insts[n]! with
  | none => return (Json.null, st)
  | some _ =>
    let mut st := st
    let mut attrs : Array Json := #[]
    -- `getattr` may materialize a dict, so the state is threaded.
    for nm in st.names do
      let (r, st') := withI st n (genericGetAttr dProto nm)
      st := st'
      attrs := attrs.push (match r with
        | .ok (some v) => enc v
        | _ => Json.null)
    if st.touched[n]! then
      let (r, st') := withI st n ensureManagedDict
      match r with
      | .ok d => return (Json.arr #[Json.arr attrs, encDict (refreshKeys st'.keys d)], st')
      | .error _ => throw "digest"
    else return (Json.arr #[Json.arr attrs, Json.null], st)

def digest (st : St) : Except String (Json × St) := do
  let mut st := st
  let mut ods : Array Json := #[]
  for i in [0:st.ods.size] do
    let (j, od') := digestOD (st.pool.size + 2) st.ods[i]!
    st := { st with ods := st.ods.set! i od' }
    ods := ods.push j
  let mut insts : Array Json := #[]
  for i in [0:st.insts.size] do
    let (j, st') ← digestInst st i
    st := st'
    insts := insts.push j
  -- A copy of a split dict shares the class's keys, which may have moved on.
  let base := digestBase { st with ds := st.ds.map (refreshKeys st.keys) }
  return (Json.arr #[base, Json.arr ods, Json.arr (st.pods.map digestPOD), Json.arr insts], st)

/-- A crash ends the scenario, as it does the process. -/
def isCrash (r : Json) : Bool :=
  match r.getObjVal? "exc" with
  | .ok (.str "<crash>") => true
  | _ => false

/-- `every`: compare the state only on every `every`-th operation and on the last. The growth
scenarios run thousands of operations on large tables. -/
def runOps (every : Nat) (st : St) : List Json → Nat → Array Json → Except String (Array Json)
  | [], _, acc => .ok acc
  | op :: rest, i, acc => do
    let (r, st') ← step st op
    if isCrash r then return acc.push (Json.arr #[r, Json.null])
    if i % every == 0 || rest.isEmpty then
      let (dg, st'') ← digest st'
      runOps every st'' rest (i + 1) (acc.push (Json.arr #[r, dg]))
    else
      runOps every st' rest (i + 1) (acc.push (Json.arr #[r, Json.null]))

def initSt (pool : Array DObj) (names : List DObj) : St :=
  { pool, names
    ds := #[{ ident := 1 }, { ident := 2 }, { ident := 3 }]
    ss := #[{ ident := 11 }, { ident := 12 }, { ident := 13 }]
    its := #[none, none, none, none]
    next := 100
    keys := dictNewKeysForClass dProto [] }

def run (fn : String) (j : Json) : Except String Json := do
  let poolJ ← arrOf (← field j "pool")
  let pool ← poolJ.mapM parseAtom
  let poolA := (pool.map DObj.atom).toArray
  let tgt : Option Nat := match (j.getObjValAs? String "target").toOption with
    | some "d0" => some 0
    | some "d1" => some 1
    | _ => none
  let stgt : Option Nat := match (j.getObjValAs? String "target").toOption with
    | some "s" => some 0
    | some "s0" => some 0
    | some "s1" => some 1
    | _ => none
  let st := { initSt poolA [] with tgt, stgt }
  -- `s1sub`: slot 1 is an instance of `SKeep`, a set subclass that keeps `set`'s `__iter__`.
  let st := if (j.getObjValAs? Bool "s1sub").toOption.getD false then
      { st with ss := st.ss.set! 1 { st.ss[1]! with exact := false, tname := "SKeep" } }
    else st
  let ops ← arrOf (← field j "ops")
  let every := (j.getObjValAs? Nat "every").toOption.getD 1
  let runOps := fun st => runOps every st ops 0 #[]
  match fn with
  | "scenario" =>
    return okJ (Json.arr (← runOps st))
  | "odict" =>
    let st := { st with
      ods := #[odictNew 21, odictNew 22, odictNew 23]
      oits := #[none, none, none, none]
      touched := #[false, false, false, false] }
    return okJ (Json.arr (← runOps st))
  | "pyod" =>
    let st := { st with
      pods := #[pyodNew 31, pyodNew 33, pyodNew 35]
      gens := #[none, none, none, none] }
    return okJ (Json.arr (← runOps st))
  | "instances" =>
    let names ← (← arrOf (← field j "names")).mapM (obj st)
    let st := { st with
      names
      insts := #[none, none, none]
      touched := #[false, false, false] }
    return okJ (Json.arr (← runOps st))
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.DictSet
