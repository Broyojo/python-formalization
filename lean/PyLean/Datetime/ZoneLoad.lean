import PyLean.Datetime.ZoneRule

/-!
# Loading and querying a `zoneinfo` zone (CPython 3.15.2), both twins

* Python `ZoneInfo._load_file` with `_utcoff_to_dstoff` and `_ts_to_local`
  (Lib/zoneinfo/_zoneinfo.py:229-397), and `_find_trans`, `_get_local_timestamp`,
  `utcoffset`/`dst`/`tzname` and `fromutc` (:109-195);
* C `load_data` after its call of `_common.load_data` (Modules/_zoneinfo.c:966-1308) with
  `utcoff_to_dstoff`, `ts_to_local`, `build_ttinfo` and `load_timedelta` (:871-919,
  :2061-2195), and `find_ttinfo`, `get_local_timestamp`, `_bisect`, the three lookups and
  `zoneinfo_fromutc` (:580-763, :2197-2348).

The datetime a lookup gets is modelled as an object (`DTObj`): Python reads it through
attributes (`dt.toordinal()`, `dt.hour`, ..., `dt.fold`, `dt.year`), C reads the `datetime`
struct for an exact `datetime` and calls the same attributes otherwise, but always takes
`fold` and `year` from the struct. Attribute reads are modelled as fixed results: a zone has
no Python-visible mutator, so code run by an attribute cannot change what the lookup reads.
Values other than ints from those attributes are out of scope.
-/

namespace PyLean.Datetime.Zone

open PyLean PyLean.Datetime

/-! ### Shared helpers -/

/-- `bisect.bisect_right(a, x)`, `internal_bisect_right` (Modules/_bisectmodule.c:62-110):
`mid = (lo + hi) / 2`; go left when `x < a[mid]`. Each round shrinks `hi - lo`, so
`len(a) + 1` rounds of fuel always suffice. -/
def bisectRightPy (a : List Int) (x : Int) : Nat :=
  go (a.length + 1) 0 a.length
where
  go : Nat → Nat → Nat → Nat
    | 0, lo, _ => lo
    | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if x < a.getD mid 0 then go fuel lo mid else go fuel (mid + 1) hi
      else lo

/-- C `_bisect`, Modules/_zoneinfo.c:2197-2216: the same loop; it returns `hi`, which equals
`lo` on exit. -/
def bisectC (value : Int) (arr : List Int) : Nat :=
  go (arr.length + 1) 0 arr.length
where
  go : Nat → Nat → Nat → Nat
    | 0, lo, _ => lo
    | fuel + 1, lo, hi =>
      if lo < hi then
        let m := (lo + hi) / 2
        if arr.getD m 0 > value then go fuel lo m else go fuel (m + 1) hi
      else hi

/-- Python `l[i]` for `-len <= i < len`. -/
def pyGet {α : Type} [Inhabited α] (l : List α) (i : Int) : α :=
  if i < 0 then l.getD (l.length - i.natAbs) default else l.getD i.toNat default

/-! ### Python `_load_file` -/

/-- One iteration of the loop of `_utcoff_to_dstoff`, _zoneinfo.py:321-354, for `i`. -/
def dstStepPy (transIdx utcoffs isdsts : List Int) (typecnt : Int) (i : Nat)
    (dstoffs : List Int) (found : Int) : List Int × Int :=
  let idx := (transIdx.getD i 0).toNat
  let dst := isdsts.getD idx 0
  if dst = 0 then (dstoffs, found)                                   -- :326-327
  else if dstoffs.getD idx 0 ≠ 0 then (dstoffs, found)              -- :330-331
  else
    let utcoff := utcoffs.getD idx 0
    let compIdx := (transIdx.getD (i - 1) 0).toNat
    let dstoff := if isdsts.getD compIdx 0 = 0 then utcoff - utcoffs.getD compIdx 0 else 0
    -- :352-354 `if dstoff: dst_found += 1; dstoffs[idx] = dstoff`
    let record (dstoff : Int) : List Int × Int :=
      if dstoff ≠ 0 then (dstoffs.set idx dstoff, found + 1) else (dstoffs, found)
    if dstoff = 0 ∧ (idx : Int) < typecnt - 1 ∧ i + 1 < transIdx.length then
      let compIdx := (transIdx.getD (i + 1) 0).toNat
      if isdsts.getD compIdx 0 ≠ 0 then (dstoffs, found)             -- :347-348 `continue`
      else record (utcoff - utcoffs.getD compIdx 0)
    else record dstoff

/-- The loop `for i in range(1, len(trans_idx))` with its `break` when `dst_cnt == dst_found`;
`fuel` counts the iterations left. The flag says whether it broke. -/
def dstLoopPy (transIdx utcoffs isdsts : List Int) (typecnt dstCnt : Int) :
    Nat → Nat → List Int → Int → List Int × Bool
  | 0, _, dstoffs, _ => (dstoffs, false)
  | fuel + 1, i, dstoffs, found =>
    if dstCnt = found then (dstoffs, true)
    else
      let (dstoffs, found) := dstStepPy transIdx utcoffs isdsts typecnt i dstoffs found
      dstLoopPy transIdx utcoffs isdsts typecnt dstCnt fuel (i + 1) dstoffs found

/-- The `for ... else` fallback (:355-361): an unassigned DST type gets 3600. -/
def fill3600 (isdsts dstoffs : List Int) : List Int :=
  (dstoffs.zip isdsts).map fun (o, d) => if o = 0 ∧ d ≠ 0 then 3600 else o

/-- `ZoneInfo._utcoff_to_dstoff`, _zoneinfo.py:302-363. `dst_cnt = sum(isdsts)` adds the
`isdst` bytes, which `struct` read as signed. -/
def utcoffToDstoffPy (transIdx utcoffs isdsts : List Int) : List Int :=
  let typecnt := isdsts.length
  let dstoffs := List.replicate typecnt 0
  let dstCnt := isdsts.sum
  let (dstoffs, broke) :=
    dstLoopPy transIdx utcoffs isdsts typecnt dstCnt (transIdx.length - 1) 1 dstoffs 0
  if broke then dstoffs else fill3600 isdsts dstoffs

/-- `_ts_to_local` (_zoneinfo.py:365-397) and C `ts_to_local` (Modules/_zoneinfo.c:2145-2195)
have the same body; C stores each sum in an `int64_t` (`wrap = wrap64`), Python keeps the
int (`wrap = id`). Fold 0 adds the larger of the two offsets around a transition, fold 1 the
smaller; the first transition compares type 0 with its own type when there are two or more
types. -/
def tsToLocal (wrap : Int → Int) (transIdx transUtc utcoffs : List Int) : List Int × List Int :=
  if transUtc = [] then ([], [])
  else
    let first : Int × Int :=
      if utcoffs.length > 1 then
        let o0 := utcoffs.getD 0 0
        let o1 := utcoffs.getD (transIdx.getD 0 0).toNat 0
        if o1 > o0 then (o1, o0) else (o0, o1)
      else (utcoffs.getD 0 0, utcoffs.getD 0 0)
    let offs : List (Int × Int) := (List.range transUtc.length).map fun i =>
      if i = 0 then first
      else
        let o0 := utcoffs.getD (transIdx.getD (i - 1) 0).toNat 0
        let o1 := utcoffs.getD (transIdx.getD i 0).toNat 0
        if o1 > o0 then (o1, o0) else (o0, o1)
    ((transUtc.zip offs).map (fun (t, o) => wrap (t + o.1)),
     (transUtc.zip offs).map (fun (t, o) => wrap (t + o.2)))

/-- A Python zone, the attributes `_load_file` sets. -/
structure PyZone where
  transUtc : List Int
  transLocal : List Int × List Int
  ttinfos : List TTI
  ttiBefore : Option TTI
  tzAfter : After
  fixedOffset : Bool
  deriving Repr

/-- `_ttinfo_list`, _zoneinfo.py:242-247. -/
def ttinfoListPy (utcoff dstoff : List Int) (abbr : List Bytes) : List TTI :=
  ((utcoff.zip dstoff).zip abbr).map fun ((u, ds), n) => ⟨u, ds, n⟩

/-- `self._tti_before`, _zoneinfo.py:254-262: the first non-DST type, else the ttinfo of the
first transition. -/
def ttiBeforePy (isdst : List Int) (ttinfoList ttinfos : List TTI) : Option TTI :=
  match isdst.findIdx? (· == 0) with
  | some i => some (ttinfoList.getD i default)
  | none => ttinfos.head?

/-- `self._tz_after` without a footer, _zoneinfo.py:268-274. -/
def fallbackPy (ttinfos ttinfoList : List TTI) : Py After :=
  if ttinfos = [] ∧ ttinfoList = [] then .error (.valueError "No time zone information found.")
  else if ttinfos ≠ [] then .ok (.tti (ttinfos.getLast?.getD default))
  else .ok (.tti (ttinfoList.getLast?.getD default))

/-- `self._tz_after`, _zoneinfo.py:265-274. -/
def tzAfterPy (tzStr : Option Bytes) (fallback : Py After) : Py After :=
  match tzStr with
  | some s => if s ≠ [] then (if utf8Valid s then parseTzStrPy s else .error decodeError) else fallback
  | none => fallback

/-- `self._fixed_offset`, _zoneinfo.py:295-300. -/
def fixedPy (ttinfoList : List TTI) (tzAfter : After) : Bool :=
  let isTti := match tzAfter with | .tti _ => true | .tzstr _ => false
  if ttinfoList.length > 1 ∨ !isTti then false
  else if ttinfoList = [] then true
  else match tzAfter with
    | .tti t => ttiEq (ttinfoList.getD 0 default) t
    | .tzstr _ => false

/-- `ZoneInfo._load_file`, _zoneinfo.py:229-300, after `_common.load_data`.
`_load_timedelta(s)` is `timedelta(seconds=s)`, which cannot fail for these 33-bit values. -/
def loadFilePy (d : TzifData) : Py PyZone := do
  let dstoff := utcoffToDstoffPy d.transIdx d.utcoff d.isdst                    -- :236
  let transLocal := tsToLocal id d.transIdx d.transUtc d.utcoff                 -- :239
  let ttinfoList := ttinfoListPy d.utcoff dstoff d.abbr                          -- :242-247
  let ttinfos := d.transIdx.map fun i => ttinfoList.getD i.toNat default      -- :251
  let ttiBefore := ttiBeforePy d.isdst ttinfoList ttinfos                       -- :254-262
  let tzAfter ← tzAfterPy d.tzStr (fallbackPy ttinfos ttinfoList)               -- :265-274
  pure ⟨d.transUtc, transLocal, ttinfos, ttiBefore, tzAfter, fixedPy ttinfoList tzAfter⟩

/-! ### C `load_data` -/

/-- C `utcoff_to_dstoff`, Modules/_zoneinfo.c:2061-2121. `dst_count` counts every type
(:2068-2070), and `isdsts` holds `PyObject_IsTrue` of each flag (:1112-1118). -/
def dstStepC (transIdx utcoffs : List Int) (isdsts : List Bool) (numTtinfos : Nat) (i : Nat)
    (dstoffs : List Int) (found : Nat) : List Int × Nat :=
  let idx := (transIdx.getD i 0).toNat
  let compIdx := (transIdx.getD (i - 1) 0).toNat
  if !isdsts.getD idx false || dstoffs.getD idx 0 ≠ 0 then (dstoffs, found)   -- :2081-2083
  else
    let utcoff := utcoffs.getD idx 0
    let dstoff := if !isdsts.getD compIdx false then utcoff - utcoffs.getD compIdx 0 else 0
    -- :2105-2108 `if (dstoff) { dst_found++; dstoffs[idx] = dstoff; }`
    let record (dstoff : Int) : List Int × Nat :=
      if dstoff ≠ 0 then (dstoffs.set idx dstoff, found + 1) else (dstoffs, found)
    if dstoff = 0 ∧ idx < numTtinfos - 1 ∧ i + 1 < transIdx.length then
      let compIdx := (transIdx.getD (i + 1) 0).toNat
      if isdsts.getD compIdx false then (dstoffs, found)            -- :2098-2100 `continue`
      else record (utcoff - utcoffs.getD compIdx 0)
    else record dstoff

def dstLoopC (transIdx utcoffs : List Int) (isdsts : List Bool) (numTtinfos dstCount : Nat) :
    Nat → Nat → List Int → Nat → List Int × Nat
  | 0, _, dstoffs, found => (dstoffs, found)
  | fuel + 1, i, dstoffs, found =>
    if dstCount = found then (dstoffs, found)
    else
      let (dstoffs, found) := dstStepC transIdx utcoffs isdsts numTtinfos i dstoffs found
      dstLoopC transIdx utcoffs isdsts numTtinfos dstCount fuel (i + 1) dstoffs found

def utcoffToDstoffC (transIdx utcoffs : List Int) (isdsts : List Bool) : List Int :=
  let numTtinfos := utcoffs.length
  -- :2066-2070: the loop counts every type, not the DST ones
  let dstCount := numTtinfos
  let (dstoffs, found) := dstLoopC transIdx utcoffs isdsts numTtinfos dstCount
    (transIdx.length - 1) 1 (List.replicate numTtinfos 0) 0
  if found < dstCount then
    (dstoffs.zip isdsts).map fun (o, d) => if d ∧ o = 0 then 3600 else o
  else dstoffs

/-- C `load_timedelta(state, seconds)`, :871-891: `Delta_FromDelta(0, seconds, 0, 1, ...)`,
whose parameters are `int` (Include/datetime.h:174), so the `long` is narrowed first. -/
def loadTimedeltaC (seconds : Int) : Int := wrap32 seconds

/-- C `build_ttinfo`, :897-919. -/
def buildTtinfoC (utcoff dstoff : Int) (tzname : Bytes) : TTI :=
  ⟨loadTimedeltaC utcoff, loadTimedeltaC dstoff, tzname⟩

/-- A C zone, the fields `load_data` sets. -/
structure CZone where
  transUtc : List Int
  transLocal : List Int × List Int
  ttinfos : List TTI
  ttiBefore : Option TTI
  rule : CRule
  fixedOffset : Bool
  deriving Repr

/-- `self->_ttinfos`, Modules/_zoneinfo.c:1137-1155. -/
def ttinfoListC (utcoff dstoff : List Int) (abbr : List Bytes) : List TTI :=
  ((utcoff.zip dstoff).zip abbr).map fun ((u, ds), n) => buildTtinfoC u ds n

/-- `self->ttinfo_before`, :1170-1182: the first non-DST type, else type 0. -/
def ttiBeforeC (isdst : List Bool) (ttinfoList : List TTI) : Option TTI :=
  match isdst.findIdx? (· == false) with
  | some i => some (ttinfoList.getD i default)
  | none => ttinfoList.head?

/-- `self->tzrule_after` without a footer, :1194-1220: an STD-only rule copying the type of
the last transition (or the last type), keeping its DST offset. -/
def fallbackC (transIdx : List Int) (ttinfoList : List TTI) : Py CRule :=
  if ttinfoList = [] then .error (.valueError "No time zone information found.")
  else
    let idx := if transIdx = [] then ttinfoList.length - 1
      else (transIdx.getLast?.getD 0).toNat
    let tti := ttinfoList.getD idx default
    let r := buildTzruleC tti.tzname none tti.utcoff 0 none none
    -- :1216-1219: keep the DST offset of a DST type
    .ok (if tti.dstoff ≠ 0 then { r with std := { r.std with dstoff := tti.dstoff } } else r)

/-- `self->tzrule_after`, :1184-1220 (`PyObject_IsTrue(tz_str)` is false for `None` and `b""`). -/
def ruleC (tzStr : Option Bytes) (fallback : Py CRule) : Py CRule :=
  let hasTzStr : Bool := match tzStr with | some s => !s.isEmpty | none => false
  if hasTzStr then parseTzStrC (tzStr.getD []) else fallback

/-- `self->fixed_offset`, :1240-1255. -/
def fixedC (ttinfoList : List TTI) (rule : CRule) : Bool :=
  if ttinfoList.length > 1 ∨ !rule.stdOnly then false
  else if ttinfoList = [] then true
  else ttiEq (ttinfoList.getD 0 default) rule.std

/-- C `load_data`, Modules/_zoneinfo.c:966-1308, after `_common.load_data` returned `d`.
`PyLong_AsLongLong` and `PyLong_AsLong` cannot fail on the 64- and 32-bit values `struct`
produced, and the index check at :1078-1085 repeats the one `_common.load_data` made. -/
def loadDataC (d : TzifData) : Py CZone := do
  let isdst : List Bool := d.isdst.map (· ≠ 0)                                 -- :1112-1118
  let dstoff := utcoffToDstoffC d.transIdx d.utcoff isdst                       -- :1128-1129
  let transLocal := tsToLocal wrap64 d.transIdx d.transUtc d.utcoff             -- :1131-1135
  let ttinfoList := ttinfoListC d.utcoff dstoff d.abbr                           -- :1137-1155
  let ttinfos := d.transIdx.map fun i => ttinfoList.getD i.toNat default      -- :1157-1168
  let ttiBefore := ttiBeforeC isdst ttinfoList                                  -- :1170-1182
  let rule ← ruleC d.tzStr (fallbackC d.transIdx ttinfoList)                    -- :1184-1220
  pure ⟨d.transUtc, transLocal, ttinfos, ttiBefore, rule, fixedC ttinfoList rule⟩  -- :1240-1255

/-! ### The datetime argument -/

/-- What a lookup can read from its argument. For a `datetime`, `y`..`s` and `fold` are the
struct fields C reads; the `Py` fields are what Python's attribute accesses return. -/
structure DTObj where
  /-- `isinstance(dt, datetime)` (C `PyDateTime_Check`). -/
  isDatetime : Bool
  /-- `type(dt) is datetime` (C `PyDateTime_CheckExact`). -/
  exact : Bool
  y : Int
  m : Int
  d : Int
  h : Int
  mi : Int
  s : Int
  fold : Nat
  toordinal : Py Int
  hour : Py Int
  minute : Py Int
  second : Py Int
  foldAttr : Py Int
  yearAttr : Py Int

/-- A plain `datetime`, whose attributes are its fields. -/
def DTObj.ofFields (y m d h mi s : Int) (fold : Nat) : DTObj :=
  ⟨true, true, y, m, d, h, mi, s, fold, .ok (ymd2ord y m d), .ok h, .ok mi, .ok s, .ok fold, .ok y⟩

/-- `ZoneInfo._get_local_timestamp`, _zoneinfo.py:189-195: `toordinal()`, then `hour`,
`minute`, `second`. -/
def getLocalTsPy (dt : DTObj) : Py Int := do
  let o ← dt.toordinal
  let h ← dt.hour
  let mi ← dt.minute
  let s ← dt.second
  pure ((o - EPOCHORDINAL) * 86400 + h * 3600 + mi * 60 + s)

/-- `PyLong_AsLong`, then the store into an `int` local. -/
def asLongToInt (v : Int) : Py Int :=
  if v < -(2 ^ 63) ∨ v ≥ 2 ^ 63 then .error (.overflowError "Python int too large to convert to C long")
  else .ok (wrap32 v)

/-- C `get_local_timestamp`, Modules/_zoneinfo.c:2284-2348: the struct for an exact
`datetime`, otherwise the same calls as Python, each narrowed to `int`. -/
def getLocalTsC (dt : DTObj) : Py Int :=
  if dt.exact then
    let ord := ymdToOrdZ dt.y dt.m dt.d
    .ok (wrap64 ((ord - EPOCHORDINAL) * 86400 + (dt.h * 3600 + dt.mi * 60 + dt.s)))
  else do
    let ord ← dt.toordinal >>= asLongToInt
    let hour ← dt.hour >>= asLongToInt
    let minute ← dt.minute >>= asLongToInt
    let second ← dt.second >>= asLongToInt
    pure (wrap64 (wrap32 (ord - EPOCHORDINAL) * 86400 +
      wrap64 (hour * 3600 + wrap32 (minute * 60) + second)))

/-! ### Lookups -/

/-- `ZoneInfo._find_trans`, _zoneinfo.py:162-187. `none` for `dt` is `dt is None`; the
`_NO_TTINFO` placeholder, whose fields are all `None`, is the `none` result. -/
def findTransPy (z : PyZone) : Option DTObj → Py (Option TTI)
  | none =>
    if z.fixedOffset then
      match z.tzAfter with
      | .tti t => .ok (some t)
      | .tzstr _ => .error (.named "AttributeError" "~'_TZStr' object has no attribute")
    else .ok none
  | some dt => do
    let ts ← getLocalTsPy dt
    let fold ← dt.foldAttr
    -- `self._trans_local[dt.fold]`, a two-element list
    let lt ← if fold = 0 ∨ fold = -2 then pure z.transLocal.1
      else if fold = 1 ∨ fold = -1 then pure z.transLocal.2
      else throw (.indexError "list index out of range")
    let numTrans := lt.length
    if numTrans ≠ 0 ∧ ts < lt.getD 0 0 then pure z.ttiBefore
    else if numTrans = 0 ∨ ts > lt.getLast?.getD 0 then
      match z.tzAfter with
      | .tzstr r => do
        let y ← dt.yearAttr
        let f ← dt.foldAttr
        pure (some (r.getTransInfo ts y f))
      | .tti t => pure (some t)
    else
      let idx := bisectRightPy lt ts - 1
      pure (some (z.ttinfos.getD idx default))

/-- C `find_ttinfo`, Modules/_zoneinfo.c:2219-2255. The outer `none` is undefined behaviour:
`PyDateTime_DATE_GET_FOLD(dt)` (:2238) reads the fold byte of the `datetime` struct, and for an
object that is not a `datetime` that byte belongs to another object or lies past this one; with
a value of 2 or more, `self->trans_list_wall[fold]` (:2240) reads past the two-element array. -/
def findTtinfoC (z : CZone) : Option DTObj → Option (Py (Option TTI))
  | none => some (.ok (if z.fixedOffset then some z.rule.std else none))
  | some dt =>
    match getLocalTsC dt with
    | .error e => some (.error e)
    | .ok ts =>
      if !dt.isDatetime then none
      else
        let fold := dt.fold
        let lt := if fold = 0 then z.transLocal.1 else z.transLocal.2
        let numTrans := z.transUtc.length
        if numTrans ≠ 0 ∧ ts < lt.getD 0 0 then some (.ok z.ttiBefore)
        else if numTrans = 0 ∨ ts > lt.getD (numTrans - 1) 0 then
          some (.ok (some (z.rule.find ts fold dt.y)))
        else
          let idx := bisectC ts lt - 1
          some (.ok (some (z.ttinfos.getD idx default)))

/-! ### `fromutc` -/

/-- `ZoneInfo.fromutc`, _zoneinfo.py:126-155, from the local timestamp on: the `_ttinfo` whose
offset is added, and whether the result gets `fold=1`. `year` is `dt.year`, read only on the
rule branch. -/
def fromutcCorePy (z : PyZone) (ts : Int) (year : Py Int) : Py (TTI × Bool) := do
  let numTrans := z.transUtc.length
  let tzstr : Option TZStr := match z.tzAfter with | .tzstr r => some r | .tti _ => none
  let afterTti : TTI := match z.tzAfter with | .tti t => t | .tzstr _ => default
  if numTrans ≥ 1 ∧ ts < z.transUtc.getD 0 0 then
    pure (z.ttiBefore.getD default, false)
  else if (numTrans = 0 ∨ ts > z.transUtc.getLast?.getD 0) ∧ tzstr.isSome then do
    let y ← year
    pure ((tzstr.getD default).getTransInfoFromutc ts y)
  else if numTrans = 0 then pure (afterTti, false)
  else do
    let idx := bisectRightPy z.transUtc ts
    let (ttiPrev, tti) ← (if numTrans > 1 ∧ ts ≥ z.transUtc.getD 1 0 then
        -- `tti_prev, tti = self._ttinfos[idx - 2 : idx]`
        match pySlice z.ttinfos ((idx : Int) - 2) idx with
        | [a, b] => pure (a, b)
        | l => throw (.valueError s!"not enough values to unpack (expected 2, got {l.length})")
      else if ts > z.transUtc.getLast?.getD 0 then pure (z.ttiBefore.getD default, afterTti)
      else pure (z.ttiBefore.getD default, z.ttinfos.getD 0 default) : Py (TTI × TTI))
    let shift := ttiPrev.utcoff - tti.utcoff
    pure (tti, decide (shift > ts - pyGet z.transUtc ((idx : Int) - 1)))

/-- `ZoneInfo.fromutc`, _zoneinfo.py:118-160, up to the shared `dt + tti.utcoff`. `isSelf` is
`dt.tzinfo is self`. -/
def fromutcPy (z : PyZone) (dt : DTObj) (isSelf : Bool) : Py (TTI × Bool) := do
  if !dt.isDatetime then throw (.typeError "fromutc() requires a datetime argument")
  if !isSelf then throw (.valueError "dt.tzinfo is not self")
  let ts ← getLocalTsPy dt
  fromutcCorePy z ts dt.yearAttr

/-- C `zoneinfo_fromutc`, Modules/_zoneinfo.c:663-715, from the local timestamp on. -/
def fromutcCoreC (z : CZone) (ts year : Int) : TTI × Bool :=
  let numTrans := z.transUtc.length
  if numTrans ≥ 1 ∧ ts < z.transUtc.getD 0 0 then
    (z.ttiBefore.getD default, false)
  else if numTrans = 0 ∨ ts > z.transUtc.getD (numTrans - 1) 0 then
    let (tti, fold) := z.rule.findFromutc ts year
    -- :681-694: the fold left by the last explicit transition
    let fold := if numTrans ≠ 0 then
        let ttiPrev := if numTrans = 1 then z.ttiBefore.getD default
          else z.ttinfos.getD (numTrans - 2) default
        let diff := wrap64 (ttiPrev.utcoff - tti.utcoff)
        if diff > 0 ∧ ts < wrap64 (z.transUtc.getD (numTrans - 1) 0 + diff) then true else fold
      else fold
    (tti, fold)
  else
    let idx := bisectC ts z.transUtc
    let (ttiPrev, tti) := if idx ≥ 2 then (z.ttinfos.getD (idx - 2) default, z.ttinfos.getD (idx - 1) default)
      else (z.ttiBefore.getD default, z.ttinfos.getD 0 default)
    let shift := wrap64 (ttiPrev.utcoff - tti.utcoff)
    (tti, decide (shift > wrap64 (ts - z.transUtc.getD (idx - 1) 0)))

/-- C `zoneinfo_fromutc`, Modules/_zoneinfo.c:642-763, up to `PyNumber_Add(dt, tti->utcoff)`.
The year is the struct's (:674). -/
def fromutcC (z : CZone) (dt : DTObj) (isSelf : Bool) : Py (TTI × Bool) := do
  if !dt.isDatetime then throw (.typeError "fromutc: argument must be a datetime")
  if !isSelf then throw (.valueError "fromutc: dt.tzinfo is not self")
  let ts ← getLocalTsC dt
  pure (fromutcCoreC z ts dt.y)

end PyLean.Datetime.Zone
