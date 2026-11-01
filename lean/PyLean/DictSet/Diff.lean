import PyLean.DiffCore
import PyLean.DictSet.Objects

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

structure St where
  pool : Array DObj
  ds : Array DD
  ss : Array DS
  its : Array (Option It)
  next : Nat
  deriving Inhabited

def enc : DObj → Json
  | .atom a => toJson a.uid
  | .tuple a b => Json.arr #[enc a, enc b]

def encs (l : List DObj) : Json := Json.arr (l.map enc).toArray

def encDict (d : DD) : Json :=
  Json.arr #[encs (dictKeysList d), encs (dictValuesList d), toJson (dictSizeOf d)]

def encSet (s : DS) : Json :=
  Json.arr #[encs ((setEntries s).map (·.1)), toJson s.sizeOf]

def digest (st : St) : Json :=
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
           tname := ← getStr j "t", fs := ← getOptInt j "fs" }

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
  | "g" => return .iter { items := ← objs st (← arg a 1), stop := some (.valueError "stop") }
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
  | "b" => return .notSeq (.typeError "object is not iterable")
  | "l" => return .wrongLen (← argN a 1)
  | t => throw s!"seq2 {t}"

/-- A mapping object over `pairs`: `keys()` lists `ks`, `__getitem__` looks in `pairs`
by the uid of the key and raises `KeyError` otherwise. -/
def mapArg (st : St) (ksJ pairsJ : Json) : Except String (MergeArg DObj DObj) := do
  let ks ← objs st ksJ
  let ps ← (← arrOf pairsJ).mapM fun p => do
    let a ← p.getArr?
    return ((← obj st (← arg a 0)), (← obj st (← arg a 1)))
  return .mapping (.ok ks) fun k =>
    match ps.find? (fun p => p.1 == k) with
    | some p => .ok p.2
    | none => .error (keyErr dProto k)

/-- `['d', slot]` exact dict, `['sub', slot]` subclass with `dict.__iter__`,
`['p', items, stop?]` iterable of pairs, `['m', keys, pairs]` mapping, `['n']`. -/
def updArg (st : St) (j : Json) : Except String (UpdateArg DObj DObj) := do
  let a ← j.getArr?
  let tag ← (← arg a 0).getStr?
  match tag with
  | "d" => return .exact st.ds[← argN a 1]!
  | "sub" => return .other (.ok true) (.dict st.ds[← argN a 1]!) { items := [] }
  | "p" =>
    let items ← (← arrOf (← arg a 1)).mapM (seq2Item st)
    let stop ← (← arg a 2).getBool?
    return .other (.ok false) (.dict {})
      { items, stop := if stop then some (.valueError "stop") else none }
  | "m" => return .other (.ok true) (← mapArg st (← arg a 1) (← arg a 2)) { items := [] }
  | "n" =>
    return .other (.ok false) (.dict {})
      { getIter := some (.typeError "'int' object is not iterable"), items := [] }
  | t => throw s!"update arg {t}"

def withD {α : Type} (st : St) (i : Nat) (m : DM DObj DObj α) : Py α × St :=
  let (r, d) := m st.ds[i]!
  (r, { st with ds := st.ds.set! i d })

def withS {α : Type} (st : St) (i : Nat) (m : SM DObj α) : Py α × St :=
  let (r, s) := m st.ss[i]!
  (r, { st with ss := st.ss.set! i s })

def fresh (st : St) : Nat × St := (st.next, { st with next := st.next + 1 })

/-- Store a new set in slot 2. -/
def toSlot2 (st : St) (r : Py DS) : Json × St :=
  match r with
  | .ok s => (okJ Json.null, { st with ss := st.ss.set! 2 s })
  | .error e => (errJ e, st)

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

def stepDict (st : St) (name : String) (a : Array Json) : Except String (Option (Json × St)) := do
  let i := (a[1]?.bind fun j => j.getNat?.toOption).getD 0
  let k (n : Nat) : Except String DObj := do obj st (← arg a n)
  let P := dProto
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
    return some (enc1 toJson (dictRepr (fun x => .ok x.reprStr) (fun x => .ok x.reprStr) false d), st)
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
    return some (resJ unitJ (withD st i (dictUpdateCommon P [u] kwd "update")))
  | "ior" =>
    let u ← updArg st (← arg a 2)
    return some (resJ unitJ (withD st i (dictIor P u)))
  | "or" =>
    let j ← argN a 2
    let (id, st) := fresh st
    let d := st.ds[i]!
    let other := st.ds[j]!
    match dictOr P d id (some other) (.exact other) with
    | .ok (some r) => return some (okJ Json.null, { st with ds := st.ds.set! 2 r })
    | .ok none => throw "or"
    | .error e => return some (errJ e, st)
  | "copy" =>
    let (id, st) := fresh st
    let d := st.ds[i]!
    return some (toDSlot2 st (dictCopy P d id false (.dict d)))
  | "eq" =>
    let j ← argN a 2
    let ne ← (← arg a 3).getBool?
    let (r, _) := dictRichcompare P dEnv.veq st.ds[i]! ne st.ds[j]!
    return some (enc1 toJson r, st)
  | "fromkeys" =>
    let v ← k 3
    let (id, st) := fresh st
    let start : DD := { ident := id }
    let t ← (← arg a 2).getArr?
    let tag ← (← arg t 0).getStr?
    let src : FromKeysArg DObj DObj ← match tag with
      | "d" => pure (.dict st.ds[← argN t 1]!)
      | "s" =>
        let s := st.ss[← argN t 1]!
        pure (.set s.used (setEntries s))
      | "l" => pure (.iter { items := ← objs st (← arg t 1) })
      | "g" => pure (.iter { items := ← objs st (← arg t 1), stop := some (.valueError "stop") })
      | _ => pure (.iter { getIter := some (.typeError "'int' object is not iterable"), items := [] })
    let (r, d) := dictFromKeys P src v start
    match r with
    | .ok _ => return some (okJ Json.null, { st with ds := st.ds.set! 2 d })
    | .error e => return some (errJ e, st)
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
    | .error e => return some (errJ e, st)
  | _ => return none

def encKV (kind : IterKind) (p : DObj × DObj) : Json :=
  match kind with
  | .key => enc p.1
  | .value => enc p.2
  | .item => encPair p

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
  let P := sProto
  let sh := DObj.setHash
  let argsAt (n : Nat) : Except String (List (SetArg DObj)) := do
    (← arrOf (← arg a n)).mapM (setArg st)
  let so := st.ss[i]!
  match name with
  | "sadd" => return some (resJ unitJ (withS st i (setAddKey P (← k 2))))
  | "srem" => return some (resJ unitJ (withS st i (setRemove P sh (← k 2))))
  | "sdisc" => return some (resJ unitJ (withS st i (setDiscard P sh (← k 2))))
  | "sin" => return some (resJ toJson (withS st i (setContains P sh (← k 2))))
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
    return some (toSlot2 st (setUnion P so (← argsAt 2) id))
  | "sinter" =>
    let (id, st) := fresh st
    return some (toSlot2 st (setIntersectionMulti P so (← argsAt 2) id))
  | "sdiff" =>
    let (id, st) := fresh st
    return some (toSlot2 st (setDifferenceMulti P so (← argsAt 2) id))
  | "ssym" =>
    let (id, st) := fresh st
    return some (toSlot2 st (setSymmetricDifference P so (← setArg st (← arg a 2)) id))
  | "scopy" =>
    let (id, st) := fresh st
    return some (toSlot2 st (setCopy P so id))
  | "sinterupd" =>
    let (id, st) := fresh st
    return some (resJ unitJ (withS st i (setIntersectionUpdateMulti P (← argsAt 2) id)))
  | "sdiffupd" =>
    let (id, st) := fresh st
    return some (resJ unitJ (withS st i (setDifferenceUpdateMulti P (← argsAt 2) id)))
  | "ssymupd" =>
    let (id, st) := fresh st
    return some (resJ unitJ (withS st i (setSymmetricDifferenceUpdate P (← setArg st (← arg a 2)) id)))
  | "sdisj" => return some (enc1 toJson (setIsdisjoint P so (← setArg st (← arg a 2))), st)
  | "ssubset" =>
    let (id, st) := fresh st
    return some (enc1 toJson (setIssubset P so (← setArg st (← arg a 2)) id), st)
  | "ssuper" =>
    let (id, st) := fresh st
    return some (enc1 toJson (setIssuperset P so (← setArg st (← arg a 2)) id), st)
  | "scmp" =>
    let j ← argN a 2
    let (id, st) := fresh st
    return some (enc1 toJson (setRichcompare P so st.ss[j]! (← cmpOf (← (← arg a 3).getStr?)) id), st)
  | "sor" =>
    let j ← argN a 2
    let (id, st) := fresh st
    return some (toSlot2 st (setOr P so st.ss[j]! id))
  | "sand" =>
    let j ← argN a 2
    let (id, st) := fresh st
    return some (toSlot2 st (setIntersection P so (.set st.ss[j]!) id))
  | "ssub" =>
    let j ← argN a 2
    let (id, st) := fresh st
    return some (toSlot2 st (setDifference P so (.set st.ss[j]!) id))
  | "sxor" =>
    let j ← argN a 2
    let (id, st) := fresh st
    return some (toSlot2 st (setSymmetricDifference P so (.set st.ss[j]!) id))
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

def step (st : St) (op : Json) : Except String (Json × St) := do
  let a ← op.getArr?
  let name ← (← arg a 0).getStr?
  if let some r := ← stepDict st name a then return r
  if let some r := ← stepIter st name a then return r
  if let some r := ← stepSet st name a then return r
  if let some r := ← stepView st name a then return r
  throw s!"unknown op {name}"

def runOps (st : St) : List Json → Array Json → Except String (Array Json)
  | [], acc => .ok acc
  | op :: rest, acc => do
    let (r, st') ← step st op
    runOps st' rest (acc.push (Json.arr #[r, digest st']))

def initSt (pool : Array DObj) : St :=
  { pool
    ds := #[{ ident := 1 }, { ident := 2 }, { ident := 3 }]
    ss := #[{ ident := 11 }, { ident := 12 }, { ident := 13 }]
    its := #[none, none, none, none]
    next := 100 }

def run (fn : String) (j : Json) : Except String Json := do
  let poolJ ← arrOf (← field j "pool")
  let pool ← poolJ.mapM parseAtom
  let st := initSt (pool.map DObj.atom).toArray
  match fn with
  | "scenario" =>
    let ops ← arrOf (← field j "ops")
    let r ← runOps st ops #[]
    return okJ (Json.arr r)
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.DictSet
