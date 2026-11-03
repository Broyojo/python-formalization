import PyLean.DiffCore
import PyLean.Datetime.ZoneLoad
import PyLean.Datetime.ZoneCache

/-!
Differential-testing runner for `zoneinfo` cases (`fn` starting with `zi_`), dispatched from
`Datetime/Diff.lean`. Bytes travel as lists of ints. A query datetime is
`[y, m, d, h, mi, s, fold, sub]` with `sub = 1` for an instance of a plain `datetime`
subclass (C then takes its non-exact path).
-/

namespace PyLean.Datetime.Zone

open Lean PyLean PyLean.Diff PyLean.Datetime

def getBytes (j : Json) (key : String) : Except String Bytes := do
  let arr ← (← field j key).getArr?
  arr.toList.mapM fun v => do
    let n ← v.getNat?
    pure (UInt8.ofNat n)

def encBytes (b : Bytes) : Json := Json.arr (b.map (fun x => toJson x.toNat)).toArray

def encData (d : TzifData) : Json :=
  Json.arr #[toJson d.transIdx, toJson d.transUtc, toJson d.utcoff, toJson d.isdst,
    Json.arr (d.abbr.map encBytes).toArray, match d.tzStr with | some s => encBytes s | none => .null]

/-- `[utcoffset, dst, tzname]` of a lookup; `null`s for `_NO_TTINFO`. -/
def encTti : Option TTI → Json
  | some t => Json.arr #[toJson t.utcoff, toJson t.dstoff, encBytes t.tzname]
  | none => Json.arr #[.null, .null, .null]

def getQueries (j : Json) (key : String) : Except String (List (List Int)) := do
  let arr ← (← field j key).getArr?
  arr.toList.mapM fun q => do
    let a ← q.getArr?
    a.toList.mapM (·.getInt?)

def dtOf (q : List Int) : DTObj :=
  let o := DTObj.ofFields (q.getD 0 1) (q.getD 1 1) (q.getD 2 1) (q.getD 3 0) (q.getD 4 0)
    (q.getD 5 0) (q.getD 6 0).toNat
  if q.getD 7 0 = 1 then { o with exact := false } else o

/-- `dt + tti.utcoff` in the shared C `datetime` (`add_datetime_timedelta`): the result must
stay within `date.min`..`date.max`. Reports the offset and the fold. -/
def fromutcOut (dt : DTObj) (r : Py (TTI × Bool)) : Json :=
  encPy (fun (p : Int × Bool) => Json.arr #[toJson p.1, toJson p.2]) (do
    let (tti, fold) ← r
    let loc := (ymd2ord dt.y dt.m dt.d - EPOCHORDINAL) * 86400 + dt.h * 3600 + dt.mi * 60 + dt.s
      + tti.utcoff
    let ord := loc / 86400 + EPOCHORDINAL
    if ord < 1 ∨ ord > 3652059 then throw (.overflowError "date value out of range")
    pure (tti.utcoff, fold))

def zoneOut (find : Option DTObj → Option (Py (Option TTI)))
    (fromutc : DTObj → Py (TTI × Bool)) (qs us : List (List Int)) : Json :=
  let one (d : Option DTObj) : Json :=
    match find d with
    | some r => encPy encTti r
    | none => Json.mkObj [("exc", toJson "UB"), ("msg", toJson "")]
  Json.mkObj [("none", one none), ("q", Json.arr (qs.map (fun q => one (some (dtOf q)))).toArray),
    ("u", Json.arr (us.map (fun q => fromutcOut (dtOf q) (fromutc (dtOf q)))).toArray)]

def intList (j : Json) (key : String) : Except String (List Int) := do
  let arr ← (← field j key).getArr?
  arr.toList.mapM (·.getInt?)

def getOps (j : Json) : Except String (List (CacheOp Nat)) := do
  let arr ← (← field j "ops").getArr?
  arr.toList.mapM fun o => do
    let a ← o.getArr?
    let tag ← (a.getD 0 .null).getStr?
    match tag with
    | "get" => pure (.get (← (a.getD 1 .null).getNat?))
    | "clear" => pure .clear
    | "keys" => do
      let ks ← (a.getD 1 .null).getArr?
      let ks ← ks.toList.mapM (·.getNat?)
      pure (.clearKeys ks)
    | t => throw s!"bad op {t}"

def runZone (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "zi_data" => return encPy encData (loadData (← getBytes j "data"))
  | "zi_py" =>
    let qs ← getQueries j "q"
    let us ← getQueries j "u"
    return encPy (fun z => zoneOut (fun d => some (findTransPy z d)) (fun d => fromutcPy z d true) qs us)
      (loadData (← getBytes j "data") >>= loadFilePy)
  | "zi_c" =>
    let qs ← getQueries j "q"
    let us ← getQueries j "u"
    return encPy (fun z => zoneOut (findTtinfoC z) (fun d => fromutcC z d true) qs us)
      (loadData (← getBytes j "data") >>= loadDataC)
  | "zi_cache_py" | "zi_cache_c" =>
    let loads ← intList j "loads"
    let ops ← getOps j
    let l : Nat → Bool := fun k => loads.contains k
    -- refcounting frees an instance as soon as no strong entry holds it, so the weak
    -- cache loses every key the strong cache does not hold after each operation
    let sweep (st : CacheSt Nat) : CacheSt Nat := ⟨st.strong, st.weak.filter (· ∈ st.strong)⟩
    let step := if fn = "zi_cache_py" then stepPy l else stepC l
    let (st, raised) := ops.foldl (fun (st, acc) op =>
      match step st op with
      | some st' => (sweep st', acc ++ [false])
      | none => (st, acc ++ [true])) ((⟨[], []⟩ : CacheSt Nat), ([] : List Bool))
    let keys := if fn = "zi_cache_py" then st.strong.reverse else st.strong.mergeSort (· ≤ ·)
    return Json.mkObj [("ok", Json.arr #[toJson keys, toJson raised])]
  | _ => throw s!"unknown zoneinfo fn {fn}"

end PyLean.Datetime.Zone
