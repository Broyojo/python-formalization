import PyLean.Datetime.Diff5
import PyLean.Datetime.StrfMemberProps
import PyLean.Datetime.ReduceDispatchProps
import PyLean.Datetime.FromtsClsProps
import PyLean.Datetime.Hour24AstzProps

/-!
Differential-testing handler for the datetime twins follow-up (`"fn": "x6_..."`): strftime's
`%z`/`%:z`/`%Z` replacements (with a subclass's `utcoffset()`/`tzname()` override in Python),
`__reduce__` with a subclass `__reduce_ex__` override, `date.fromtimestamp` with its class, and
`astimezone` on a subclass whose `__new__` may return a cached instance. See
difftest/datetime_x6.py.
-/

namespace PyLean.Datetime

open Lean PyLean PyLean.Diff

/-- A `timezone(timedelta(microseconds=us), name)`: `timezone.utc` for a zero offset without a
name. -/
def x6Tz (oid : Nat) (us : Int) (name : Option String) : Tz :=
  if us = 0 ∧ name = none then tzUTC else ⟨oid, .timezone (isoDeltaOfUs us) name⟩

def x6OptTz (oid : Nat) (us : Option Int) (name : Option String) : Option Tz := us.map (x6Tz oid · name)

/-- The recording subclass of `date`: its `__new__` raises `Rec` with the positional arguments
and the sorted keyword names. -/
def x6Rec : SubCall DT := fun args kw =>
  .error (.named "Rec" (",".intercalate (args.map x5EncArg) ++ ";" ++ (match kw with | none => "" | some _ => "fold")))

/-- The cached-instance subclass over the heap: object `0` is the cache; a new object gets the
first free identity from `2`. -/
def x6Call (cached : Bool) : HeapCall := fun h args =>
  if cached then .ok (0, h)
  else
    let f (i : Nat) : Int := match args.getD i .none_ with | .int n => n | _ => 0
    let tz : Option Tz := match args.getD 7 .none_ with | .tz z => some z | _ => none
    let v : DT := ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, 0, tz⟩
    let k := ((List.range 20).find? (fun k => 2 ≤ k && (h k).isNone)).getD 99
    .ok (k, fun j => if j = k then some v else h j)

/-- `timezone_fromutc` (:4507-4523) and `timezone.fromutc` (Py:2544-2551) over the heap, for the
target `timezone` `z`: the identity test on the argument's tzinfo, then `dt + self._offset`, a
call of the subclass with the eight fields. -/
def x6Fromutc (call : HeapCall) (z : Tz) : HeapFromutc := fun h i =>
  match h i with
  | none => .error .modelFuel
  | some v =>
    if v.tz.map (·.oid) ≠ some z.oid then .error (.valueError "fromutc: dt.tzinfo is not self")
    else do
      let o := z.offsetOf
      let r ← normalizeDatetimeC v.y v.m (v.d + o.days) v.h v.mi (v.s + o.seconds) (v.us + o.us)
      call h [.int r.y, .int r.m, .int r.d, .int r.h, .int r.mi, .int r.s, .int r.us, tzArgOf v.tz]

/-- The difftest process's `localtime` (TZ=XXX-2) for every `time_t`: the proleptic Gregorian
date of `floor((t + 7200) / 86400)` days after the epoch (`civil_from_days`, with a year 0),
`OSError` (EOVERFLOW) when `year - 1900` does not fit `tm_year`, and `tm_year + 1900` computed in
C `int` (it wraps for the largest years, in both twins). -/
def x6Clock : Clock where
  otherTimeT _ := .error .modelFuel
  now := .error .modelFuel
  localtime u := do
    let z := (u + 7200) / 86400 + 719468
    let era := z / 146097
    let doe := z - era * 146097
    let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
    let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
    let mp := (5 * doy + 2) / 153
    let d := doy - (153 * mp + 2) / 5 + 1
    let m := if mp < 10 then mp + 3 else mp - 9
    let y := yoe + era * 400 + (if m ≤ 2 then 1 else 0)
    if y - 1900 > 2147483647 ∨ y - 1900 < -2147483648 then
      throw (.named "OSError" "[Errno 75] Value too large for defined data type")
    let w := (y + 2147483648) % 4294967296 - 2147483648
    return (w, m, d)

def x6EncDT7 (v : DT) : Json :=
  Json.arr #[toJson v.y, toJson v.m, toJson v.d, toJson v.h, toJson v.mi, toJson v.s, toJson v.us, x5OffUs v.tz]

def runX6 (fn : String) (j : Json) : Except String Json := do
  let isC := (j.getObjValAs? String "impl").toOption == some "c"
  match fn with
  | "x6_strfz" =>
    let kind ← getStr j "kind"
    let v ← x4Ints j "v"
    let off ← getOptInt j "tz"
    let name : Option String := (j.getObjValAs? String "name").toOption
    let tz := x6OptTz 1 off name
    let obj : StrfObj :=
      if kind = "date" then .date
      else if kind = "time" then .time ⟨v.getD 3 0, v.getD 4 0, v.getD 5 0, v.getD 6 0, 0, tz⟩
      else .dt ⟨v.getD 0 1, v.getD 1 1, v.getD 2 1, v.getD 3 0, v.getD 4 0, v.getD 5 0, v.getD 6 0, 0, tz⟩
    let ovOff : Option (Py (Option Delta)) := match ← field j "ov_off" with
      | .str "inherit" => none
      | .str _ => some (.ok none)
      | n => match n.getInt? with
        | .ok o => some (.ok (some (isoDeltaOfUs o)))
        | .error _ => none
    let ovName : Option (Py (Option String)) := match ← field j "ov_name" with
      | .str "inherit" => none
      | .str "none" => some (.ok none)
      | .str s => some (.ok (some s))
      | _ => none
    let subj : StrfSubj := ⟨obj, ovOff, ovName⟩
    let fmt ← getStr j "fmt"
    let r : Py (List Char) :=
      if fmt = "%Z" then (if isC then makeZreplacementC x5Env obj else subj.ZreplacePy x5Env)
      else
        let sep := if fmt = "%:z" then [':'] else []
        if isC then makeSomezreplacementC x5Env sep obj else subj.zreplacePy x5Env sep
    return encPy (fun (cs : List Char) => toJson (String.ofList cs)) r
  | "x6_reduce" =>
    let kind ← getStr j "kind"
    let v ← x4Ints j "v"
    let tz := x6OptTz 1 (← getOptInt j "tz") none
    let ov ← getBool j "override"
    let custom : Int → Py (Nat × StateTuple) := fun p => .ok (999, .one [p.toNat])
    let enc : Py (Nat × StateTuple) → Json := encPy (fun r =>
      if r.1 = 999 then (match r.2 with
        | .one [p] => Json.arr #[toJson "custom", toJson p]
        | _ => Json.null)
      else x5EncState r.2)
    if kind = "time" then
      let t : TM := ⟨v.getD 3 0, v.getD 4 0, v.getD 5 0, v.getD 6 0, v.getD 7 0, tz⟩
      if isC then return enc (.ok (tmReduceClsC 0 t))
      else return enc (tmReduceDispatchPy (if ov then custom else fun p => .ok (tmReduceExClsPy 0 t p)))
    else
      let d : DT := ⟨v.getD 0 1, v.getD 1 1, v.getD 2 1, v.getD 3 0, v.getD 4 0, v.getD 5 0, v.getD 6 0,
        v.getD 7 0, tz⟩
      if isC then return enc (.ok (dtReduceClsC 0 d))
      else return enc (dtReduceDispatchPy (if ov then custom else fun p => .ok (dtReduceExClsPy 0 d p)))
  | "x6_fromts" =>
    let clsName ← getStr j "cls"
    let cls : DateClsC := if clsName = "date" then .date else if clsName = "datetime" then .datetime else .sub x6Rec
    let a ← (← field j "t").getArr?
    let arg : Arg ← match ← (a.getD 0 .null).getStr? with
      | "i" => pure (.int (← (a.getD 1 .null).getInt?))
      | "f" => pure (.float (Binary64.F64.ofBits (← (a.getD 1 .null).getNat?)))
      | "n" => pure .none_
      | _ => pure (.str [120])
    let r := if isC then datetimeDateFromtimestampImplC x6Clock cls arg else dateFromtimestampClsPy x6Clock cls arg
    return encPy (fun (v : DT) =>
      if clsName = "datetime" then
        Json.arr #[toJson v.y, toJson v.m, toJson v.d, toJson v.h, toJson v.mi, toJson v.s, toJson v.us]
      else Json.arr #[toJson v.y, toJson v.m, toJson v.d]) r
  | "x6_astz" =>
    let v ← x4Ints j "v"
    let cv ← x4Ints j "cache"
    let cached ← getBool j "cached"
    let selfOff ← getInt j "self_off"
    let target ← getInt j "target"
    let cacheOff ← getOptInt j "cache_off"
    let selfTz := x6Tz 1 selfOff none
    let tgt := x6Tz 2 target none
    let cache : DT := ⟨cv.getD 0 1, cv.getD 1 1, cv.getD 2 1, cv.getD 3 0, cv.getD 4 0, cv.getD 5 0, cv.getD 6 0, 0,
      x6OptTz 3 cacheOff none⟩
    let self : DT := ⟨v.getD 0 1, v.getD 1 1, v.getD 2 1, v.getD 3 0, v.getD 4 0, v.getD 5 0, v.getD 6 0, 0,
      some selfTz⟩
    let h0 : DtHeap := fun k => if k = 0 then some cache else none
    let call := x6Call cached
    let fu := x6Fromutc call tgt
    let r := if isC then astzHeapC call fu 50 h0 self (isoDeltaOfUs selfOff) tgt
      else astzHeapPy call fu h0 self (isoDeltaOfUs selfOff) tgt
    let encCache (h : DtHeap) : Json := match h 0 with
      | some c => x6EncDT7 c
      | none => Json.null
    match r with
    | .ok (i, h) =>
      return Json.mkObj [("ok", Json.arr #[(match h i with | some w => x6EncDT7 w | none => Json.null), Json.null,
        encCache h])]
    | .error e =>
      return Json.mkObj [("ok", Json.arr #[Json.null, toJson (e.className ++ ": " ++ e.message), encCache h0])]
  | _ => throw s!"unknown fn {fn}"

end PyLean.Datetime
