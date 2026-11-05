import PyLean.DiffCore
import PyLean.RangeSlice.Model
import PyLean.RangeSlice.SliceHash
import PyLean.RangeSlice.Search

/-! Differential-testing handler for `rangeslice` cases (`"mod": "rangeslice"`).
A range is `"r": [start, stop, step|null]` with `"nargs"` 1, 2 or 3; a slice is
`"s": [start|null, stop|null, step|null]`. -/

namespace PyLean.RangeSlice

open Lean PyLean PyLean.Diff

def getRangeAt (j : Json) (key nargsKey : String) : Except String (Py Range) := do
  let arr ← (← j.getObjVal? key).getArr?
  let nargs ← getNat j nargsKey
  let some a := arr[0]? | throw "range: missing start"
  let some b := arr[1]? | throw "range: missing stop"
  let some c := arr[2]? | throw "range: missing step"
  let b ← b.getInt?
  if nargs = 1 then return .ok (range1 b)
  let a ← a.getInt?
  let c ← if nargs = 2 then pure none else some <$> c.getInt?
  return rangeNew a b c

def getRange (j : Json) : Except String (Py Range) := getRangeAt j "r" "nargs"

def optInt : Json → Except String (Option Int)
  | .null => .ok none
  | v => some <$> v.getInt?

def getSlice (j : Json) : Except String Slice := do
  let arr ← (← j.getObjVal? "s").getArr?
  let some a := arr[0]? | throw "slice: missing start"
  let some b := arr[1]? | throw "slice: missing stop"
  let some c := arr[2]? | throw "slice: missing step"
  return ⟨← optInt a, ← optInt b, ← optInt c⟩

def encTriple (t : Int × Int × Int) : Json := Json.arr #[toJson t.1, toJson t.2.1, toJson t.2.2]

def encRange (r : Range) : Json := encTriple (r.start, r.stop, r.step)

/-- The last `k` values of a range: `list(r[-k:])`, computed through the
modelled `compute_slice` and then enumerated (the result has at most `k`
elements). -/
def lastK (r : Range) (k : Nat) : Py (List Int) := do
  let r' ← computeSlice r ⟨some (-(k : Int)), none, none⟩
  return (List.range r'.length.toNat).map (fun (i : Nat) => r'.start + (i : Int) * r'.step)

/-- The `__setstate__` argument: an int, or `{"kind": "subclass", "v": .., "tp": ..}`,
`{"kind": "index", "v": .., "tp": ..}`, `{"kind": "raises", "exc": .., "msg": .., "tp": ..}`,
`{"kind": "other", "tp": ..}`. -/
def getState (j : Json) : Except String StateArg := do
  let v ← j.getObjVal? "state"
  match v.getInt? with
  | .ok i => return .exact i
  | .error _ =>
    let tp ← getStr v "tp"
    match ← getStr v "kind" with
    | "subclass" => return .subclass (← getInt v "v") tp
    | "index" => return .index (.ok (← getInt v "v")) tp
    | "other" => return .other tp
    | "raises" =>
      let e ← getStr v "exc"
      let m ← getStr v "msg"
      return .index (.error (if e = "TypeError" then .typeError m else .named e m)) tp
    | k => throw s!"unknown state kind {k}"

/-- `[type name, first k values, __length_hint__(), reduced range, its last k values]`. -/
def encIterRun (it : RIter) (k : Nat) : Except String Json := do
  let (xs, it') := iterTake k it
  let red := iterReduce it'
  let tail ← match (if k = 0 then .ok [] else lastK red k) with
    | .ok t => pure t
    | .error _ => throw "lastK failed"
  return Json.arr #[toJson it.typeName, toJson xs, toJson it'.lengthHint, encRange red, toJson tail]

/-- `hash(n)` for an int: reduction modulo `2**61 - 1` with the sign kept, `-1` becoming `-2`
(Objects/longobject.c `long_hash`). Only used to feed `sliceHash` in the difftest. -/
def intHash (n : Int) : Int :=
  let p : Int := 2 ^ 61 - 1
  let h := if n ≥ 0 then n % p else -((-n) % p)
  if h = -1 then -2 else h


/-- An object argument (see `difftest/rangeslice_diff.py`, `make_obj`): an int, or
`{"k": "bool"|"sub"|"idx"|"idxsub"|"idxbad"|"idxraise"|"other"|"slice", ...}`. `werr` is the
case's warnings filter (`DeprecationWarning` raised or ignored). -/
def getObj (werr : Bool) (v : Json) : Except String Obj := do
  match v.getInt? with
  | .ok i => return .int i
  | .error _ =>
    match ← getStr v "k" with
    | "bool" => return .bool (← getBool v "v")
    | "sub" => return .intSub (← getInt v "v") (← getStr v "tp")
    | "idx" => return .index (← getStr v "tp") (.ok (.exact (← getInt v "v")))
    | "idxsub" => return .index (← getStr v "tp") (.ok (.subclass (← getInt v "v") (← getStr v "rtp") werr))
    | "idxbad" => return .index (← getStr v "tp") (.ok (.other (← getStr v "rtp")))
    | "idxraise" => return .index (← getStr v "tp") (.error (.named (← getStr v "exc") (← getStr v "msg")))
    | "other" => return .other (← getStr v "tp")
    | "slice" =>
      let arr ← (← v.getObjVal? "s").getArr?
      let some a := arr[0]? | throw "slice: missing start"
      let some b := arr[1]? | throw "slice: missing stop"
      let some c := arr[2]? | throw "slice: missing step"
      return .slice ⟨← optInt a, ← optInt b, ← optInt c⟩
    | k => throw s!"unknown object kind {k}"

/-- The `__eq__` behaviour of a search probe, as a callback counting its calls. -/
def getHook (v : Json) : Except String (EqHook Nat) := do
  match ← getStr v "h" with
  | "eqv" => let t ← getInt v "v"; return fun x n => (.ok (decide (x = t)), n + 1)
  | "never" => return fun _ n => (.ok false, n + 1)
  | "always" => return fun _ n => (.ok true, n + 1)
  | "trueat" => let m ← getNat v "m"; return fun _ n => (.ok (decide (n = m)), n + 1)
  | "raiseat" =>
    let m ← getNat v "m"
    let e ← getStr v "exc"
    let msg ← getStr v "msg"
    return fun _ n => (if n = m then .error (.named e msg) else .ok false, n + 1)
  | h => throw s!"unknown hook {h}"

def encSub : SubRes → Json
  | .item v => Json.mkObj [("item", toJson v)]
  | .range r => Json.mkObj [("range", encRange r)]

def encCmp : CmpRes → Json
  | .notImplemented => toJson "NotImplemented"
  | .bool b => toJson b

def encKey (k : HashKey) : Json :=
  Json.arr #[toJson k.1, (match k.2.1 with | some v => toJson v | none => Json.null),
    (match k.2.2 with | some v => toJson v | none => Json.null)]

def cmpOp : String → Except String CmpOp
  | "lt" => .ok .lt | "le" => .ok .le | "eq" => .ok .eq
  | "ne" => .ok .ne | "gt" => .ok .gt | "ge" => .ok .ge
  | o => .error s!"unknown op {o}"

def optNames (j : Json) (key : String) : Except String (Option (List String)) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => .ok none
  | .ok v => do return some ((← v.getArr?).toList.map fun n => (n.getStr?).toOption.getD "")

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "slicehash" =>
    let ps ← (← (← field j "parts").getArr?).toList.mapM Json.getInt?
    match ps with
    | [a, b, c] => return encPy toJson (SliceHash.sliceHash (fun n => .ok (intHash n)) ⟨0, a, b, c⟩)
    | _ => throw "parts"
  | "indices" =>
    let s ← getSlice j
    return encPy encTriple (sliceIndices s (← getInt j "n"))
  | "listslice" =>
    let s ← getSlice j
    return encPy toJson (listSlicePositions (← getInt j "n") s)
  | "newobj" =>
    let werr ← getBool j "werr"
    let args ← (← (← field j "args").getArr?).toList.mapM (getObj werr)
    let kw ← optNames j "kw"
    let res := if (← getStr j "via") = "new" then rangeNewTp args kw else rangeVectorcall args kw
    return encPy encRange res
  | _ => pure ()
  let r ← getRange j
  match fn with
  | "new" => return encPy encRange r
  | "len" => return encPy toJson (r >>= rangeLength)
  | "getitem" =>
    let i ← getInt j "i"
    return encPy toJson (r >>= (computeRangeItem · i))
  | "slice" =>
    let s ← getSlice j
    return encPy encRange (r >>= (computeSlice · s))
  | "contains" =>
    let x ← getInt j "x"
    return encPy toJson (r >>= fun r => .ok (rangeContainsLong r x))
  | "index" =>
    let x ← getInt j "x"
    return encPy toJson (r >>= (rangeIndex · x))
  | "count" =>
    let x ← getInt j "x"
    return encPy toJson (r >>= fun r => .ok (rangeCount r x))
  | "eq" =>
    let r2 ← getRangeAt j "r2" "nargs2"
    return encPy toJson (do
      let a ← r; let b ← r2
      let e := rangeEquals a b
      return [e, e && rangeHashKey a == rangeHashKey b])
  | "iter" | "iterfor" | "reversed" =>
    let k ← getNat j "k"
    match r with
    | .error e => return encPy id (.error e : Py Json)
    | .ok r => return encPy id (.ok (← encIterRun (if fn = "reversed" then rangeReverse r else rangeIter r) k) : Py Json)
  | "setstate" =>
    let k ← getNat j "k"
    let rev ← getBool j "rev"
    let st ← getInt j "state"
    return encPy id (do
      let r ← r
      let it ← iterSetstate (if rev then rangeReverse r else rangeIter r) st
      let (xs, it') := iterTake k it
      return Json.arr #[toJson it.typeName, toJson xs, toJson it'.lengthHint])
  | "setstate_obj" =>
    let k ← getNat j "k"
    let k0 ← getNat j "k0"
    let rev ← getBool j "rev"
    let st ← getState j
    return encPy id (do
      let r ← r
      let (_, it) := iterTake k0 (if rev then rangeReverse r else rangeIter r)
      let it ← iterSetstateObj it st
      let (xs, it') := iterTake k it
      let red := iterReduce it'
      return Json.arr #[toJson it.typeName, toJson xs, toJson it'.lengthHint, encRange red])
  | "subscript" =>
    let item ← getObj (← getBool j "werr") (← field j "item")
    return encPy encSub (r >>= (rangeSubscript · item))
  | "richcmp" =>
    let op ← cmpOp (← getStr j "op")
    let o ← field j "other"
    let other ← match ← getStr o "k" with
      | "self" => pure (Except.ok CmpOther.self)
      | "range" => do
        let r2 ← getRangeAt o "r" "nargs"
        pure (r2.map CmpOther.range)
      | _ => pure (Except.ok (CmpOther.notRange (← getStr o "tp")))
    return encPy encCmp (do let a ← r; let b ← other; rangeRichcompare a b op)
  | "hashkey" =>
    return encPy id (r >>= fun r => .ok (encKey (rangeHashKey r)))
  | "search" =>
    let ob ← getObj false (← field j "probe")
    let hook ← getHook (← field j "hook")
    let cnt ← getBool j "calls"
    let enc := fun {α : Type} (f : α → Json) (p : Py α × Nat) =>
      Json.arr #[encPy f p.1, if cnt then toJson p.2 else Json.null]
    match r with
    | .error e => return encPy id (.error e : Py Json)
    | .ok r =>
      match ← getStr j "op" with
      | "contains" => return encPy id (.ok (enc toJson (rangeContainsObj r ob hook 0)) : Py Json)
      | "count" => return encPy id (.ok (enc toJson (rangeCountObj r ob hook 0)) : Py Json)
      | "index" => return encPy id (.ok (enc toJson (rangeIndexObj r ob hook 0)) : Py Json)
      | o => throw s!"unknown search op {o}"
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.RangeSlice
