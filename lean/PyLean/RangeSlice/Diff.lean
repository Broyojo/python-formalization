import PyLean.DiffCore
import PyLean.RangeSlice.Model

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

/-- `[type name, first k values, __length_hint__(), reduced range, its last k values]`. -/
def encIterRun (it : RIter) (k : Nat) : Except String Json := do
  let (xs, it') := iterTake k it
  let red := iterReduce it'
  let tail ← match (if k = 0 then .ok [] else lastK red k) with
    | .ok t => pure t
    | .error _ => throw "lastK failed"
  return Json.arr #[toJson it.typeName, toJson xs, toJson it'.lengthHint, encRange red, toJson tail]

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "indices" =>
    let s ← getSlice j
    return encPy encTriple (sliceIndices s (← getInt j "n"))
  | "listslice" =>
    let s ← getSlice j
    return encPy toJson (listSlicePositions (← getInt j "n") s)
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
  | "iter" | "reversed" =>
    let k ← getNat j "k"
    match r with
    | .error e => return encPy id (.error e : Py Json)
    | .ok r => return encPy id (.ok (← encIterRun (if fn = "iter" then rangeIter r else rangeReverse r) k) : Py Json)
  | "setstate" =>
    let k ← getNat j "k"
    let rev ← getBool j "rev"
    let st ← getInt j "state"
    return encPy id (do
      let r ← r
      let it ← iterSetstate (if rev then rangeReverse r else rangeIter r) st
      let (xs, it') := iterTake k it
      return Json.arr #[toJson it.typeName, toJson xs, toJson it'.lengthHint])
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.RangeSlice
