import PyLean.DiffCore
import PyLean.Datetime.Ctor
import PyLean.Datetime.Strftime
import PyLean.Datetime.Strptime
import PyLean.Datetime.Misc
import PyLean.Datetime.Twins

/-!
Differential-testing handler for the object layer: `time`, `datetime`, `timezone`,
comparison, hash keys, pickle state, `repr`, `strftime`. `testEnv` mirrors the
`tzinfo` subclasses defined in `difftest/datetime_diff.py`.
-/

namespace PyLean.Datetime

open Lean PyLean PyLean.Diff

def td (d s us : Int) : Delta := ⟨d, s, us⟩

/-- `dst()` of the rule-based zone (impl 3) of the difftest. -/
def ruleDst (dt : DT) : Delta :=
  if 4 ≤ dt.m ∧ dt.m ≤ 9 then td 0 3600 0
  else if dt.m = 10 ∧ dt.d < 15 then td 0 3600 0
  else if dt.m = 10 ∧ dt.d = 15 ∧ dt.h = 1 ∧ dt.fold = 0 then td 0 3600 0
  else td 0 0 0

def boom {α : Type} : Py α := .error (.valueError "boom")

def testUtcoffset : Nat → Option DT → Py OffRet
  | 1, _ => .ok .none
  | 2, _ => .ok (.delta (td 0 3600 0))
  | 3, none => .ok .none
  | 3, some dt => .ok (.delta (if (ruleDst dt).seconds = 0 then td (-1) 68400 0 else td (-1) 72000 0))
  | 4, _ => .ok (.other "int")
  | 5, _ => .ok (.delta (td 1 0 0))
  | 6, _ => boom
  | 7, _ => .ok (.delta (td 0 30 5))
  | 8, _ => .ok (.delta (td (-1) 86310 0))
  | _, _ => .ok .none

def testDst : Nat → Option DT → Py OffRet
  | 1, _ => .ok .none
  | 2, _ => .ok (.delta (td 0 0 0))
  | 3, none => .ok .none
  | 3, some dt => .ok (.delta (ruleDst dt))
  | 4, _ => .ok (.other "str")
  | 5, _ => .ok (.delta (td (-1) 0 0))
  | 6, _ => boom
  | 7, _ => .ok (.delta (td (-1) 86399 0))
  | 8, _ => .ok (.delta (td 0 0 0))
  | _, _ => .ok .none

def testTzname : Nat → Option DT → Py NameRet
  | 1, _ => .ok .none
  | 2, _ => .ok (.str "ONE")
  | 3, none => .ok .none
  | 3, some dt => .ok (.str (if (ruleDst dt).seconds = 0 then "EST" else "EDT"))
  | 4, _ => .ok (.other "int")
  | 5, _ => .ok .none
  | 6, _ => boom
  | 7, _ => .ok (.str "a%b")
  | 8, _ => .ok (.str "it's")
  | _, _ => .ok .none

/-- The difftest zones; impl 0 is the abstract base class. -/
def testEnv (isC : Bool) : TzEnv where
  utcoffset i a := if i = 0 then .error (if isC then tzinfoNogoC "utcoffset" else tzinfoBasePy "utcoffset")
    else testUtcoffset i a
  dst i a := if i = 0 then .error (if isC then tzinfoNogoC "dst" else tzinfoBasePy "dst") else testDst i a
  tzname i a := if i = 0 then .error (if isC then tzinfoNogoC "tzname" else tzinfoBasePy "tzname")
    else testTzname i a
  repr i := s!"TZ({i})"

def decDelta (j : Json) : Except String Delta := do
  let a ← j.getArr?
  let ints ← a.mapM (·.getInt?)
  return ⟨ints.getD 0 0, ints.getD 1 0, ints.getD 2 0⟩

/-- `null`, `["tz", oid, delta, name]` or `["cu", oid, impl]`. -/
def decTz (j : Json) : Except String (Option Tz) := do
  match j with
  | .null => return none
  | _ =>
    let a ← j.getArr?
    let tag ← (a.getD 0 .null).getStr?
    let oid ← (a.getD 1 .null).getNat?
    if tag = "tz" then
      let off ← decDelta (a.getD 2 .null)
      let name ← match a.getD 3 .null with
        | .null => pure none
        | n => some <$> n.getStr?
      return some ⟨oid, .timezone off name⟩
    else return some ⟨oid, .custom (← (a.getD 2 .null).getNat?)⟩

def decDT (j : Json) : Except String DT := do
  let a ← j.getArr?
  let f (i : Nat) : Except String Int := (a.getD i .null).getInt?
  return ⟨← f 0, ← f 1, ← f 2, ← f 3, ← f 4, ← f 5, ← f 6, ← f 7, ← decTz (a.getD 8 .null)⟩

def decTM (j : Json) : Except String TM := do
  let a ← j.getArr?
  let f (i : Nat) : Except String Int := (a.getD i .null).getInt?
  return ⟨← f 0, ← f 1, ← f 2, ← f 3, ← f 4, ← decTz (a.getD 5 .null)⟩

def encOid : Option Tz → Json
  | none => .null
  | some t => toJson t.oid

def encDTv (v : DT) : Json :=
  Json.arr #[toJson v.y, toJson v.m, toJson v.d, toJson v.h, toJson v.mi, toJson v.s, toJson v.us,
    toJson v.fold, encOid v.tz]

def encTMv (v : TM) : Json :=
  Json.arr #[toJson v.h, toJson v.mi, toJson v.s, toJson v.us, toJson v.fold, encOid v.tz]

def encYMD' (v : Int × Int × Int) : Json := Json.arr #[toJson v.1, toJson v.2.1, toJson v.2.2]
def encD (t : Delta) : Json := Json.arr #[toJson t.days, toJson t.seconds, toJson t.us]
def encOffOpt : Option Delta → Json
  | none => .null
  | some o => encD o
def encStrOpt : Option String → Json
  | none => .null
  | some s => toJson s
def encKey : HashKey → Json
  | .bytes b => Json.arr #[toJson "b", toJson b]
  | .tuple1 b => Json.arr #[toJson "t1", toJson b]
  | .ints x => Json.arr #[toJson "i", toJson x]
def encTT (t : TimeTuple) : Json := toJson t
def encStrf (r : List Char × TimeTuple) : Json :=
  Json.arr #[toJson (r.1.map Char.toNat), encTT r.2]

/-- `encPy encOffOpt` with the `~` of the range message removed: the nested result is
compared as plain JSON. -/
def encOffPy (r : Py (Option Delta)) : Json :=
  match r with
  | .ok v => encPy encOffOpt (.ok v)
  | .error e => Json.mkObj [("exc", toJson e.className), ("msg", toJson (e.message.dropPrefix "~").toString)]

def getOp (j : Json) : Except String CmpOp := do
  match ← getStr j "op" with
  | "lt" => pure .lt | "le" => pure .le | "eq" => pure .eq
  | "ne" => pure .ne | "gt" => pure .gt | "ge" => pure .ge
  | s => throw s!"bad op {s}"

def getSpecS (j : Json) : Except String (Py TimeSpec) := do
  return parseTimespec (← getStr j "spec")

def decArg (j : Json) : Except String Arg := do
  match j with
  | .null => return .none_
  | _ =>
    let a ← j.getArr?
    match ← (a.getD 0 .null).getStr? with
    | "i" => return .int (← (a.getD 1 .null).getInt?)
    | "b" => return .bytes ((← (a.getD 1 .null).getArr?).toList.map (fun x => (x.getNat?).toOption.getD 0))
    | "s" => return .str ((← (a.getD 1 .null).getArr?).toList.map (fun x => (x.getNat?).toOption.getD 0))
    | "tz" =>
      match ← decTz (a.getD 1 .null) with
      | some t => return .tz t
      | none => return .none_
    -- an object with `__index__`: `["x", ["i", n]]` returns n, `["x", ["s"]]` a str,
    -- `["x", ["e", msg]]` raises `ValueError(msg)`
    | "x" =>
      let r ← (a.getD 1 .null).getArr?
      match ← (r.getD 0 .null).getStr? with
      | "i" => return .index (.ok (some (← (r.getD 1 .null).getInt?)))
      | "e" => return .index (.error (.valueError (← (r.getD 1 .null).getStr?)))
      | _ => return .index (.ok none)
    | "f" => return .float (Binary64.F64.ofBits (← (a.getD 1 .null).getNat?))
    | _ => return .other

/-- The `fold` argument: a JSON number is an int, anything else an encoded `Arg`. -/
def getFoldArg (j : Json) : Except String Arg := do
  let v ← field j "fold"
  match v.getInt? with
  | .ok n => return .int n
  | .error _ => decArg v

def getArgs (j : Json) (k : String) : Except String (List Arg) := do
  (← (← field j k).getArr?).toList.mapM decArg

def getYMD (j : Json) (k : String) : Except String (Int × Int × Int) := do
  let a ← (← field j k).getArr?
  let f (i : Nat) : Except String Int := (a.getD i .null).getInt?
  return (← f 0, ← f 1, ← f 2)

def getOptField (j : Json) (k : String) : Except String (Option Int) := getOptInt j k

/-- A `replace` argument: absent or `null` is omitted, `["n"]` an explicit `None`, otherwise
an `Arg`. -/
def getReplArg (j : Json) (k : String) : Except String (Option Arg) :=
  match j.getObjVal? k with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok v => match v.getArr? with
    | .ok a => if (a.getD 0 .null).getStr?.toOption == some "n" then .ok (some .none_) else some <$> decArg v
    | .error _ => some <$> decArg v

/-- `tz` field semantics of `replace`/`combine`: absent is the default `tzinfo=True`. -/
def getOptTzArg (j : Json) : Except String (Option (Option Tz)) :=
  match j.getObjVal? "tzarg" with
  | .error _ => .ok none
  | .ok v => some <$> decTz v

def getStrList (j : Json) : Except String (List String) := do
  (← j.getArr?).toList.mapM (·.getStr?)

def decLocale (j : Json) : Except String LocaleTimeV := do
  let f (k : String) : Except String (List String) := do getStrList (← field j k)
  let tz ← (← (← field j "tz").getArr?).toList.mapM getStrList
  let alt ← match ← field j "alt" with
    | .null => pure none
    | v => some <$> getStrList v
  return { fWeekday := ← f "fw", aWeekday := ← f "aw", fMonth := ← f "fm", aMonth := ← f "am",
           amPm := ← f "ap", timezone := tz, lcDateTime := ← getStr j "dt", lcDate := ← getStr j "d",
           lcTime := ← getStr j "t", lcTimeAmpm := ← getStr j "ta", altDigits := alt,
           ambiguousTz := ← getBool j "amb" }

def decFound (j : Json) : Except String StrpFound := do
  (← j.getArr?).toList.mapM fun p => do
    let a ← p.getArr?
    let v ← match a.getD 1 .null with
      | .null => pure none
      | x => some <$> x.getStr?
    return (← (a.getD 0 .null).getStr?, v)

def encStrp (r : StrpResult) : Json :=
  Json.arr #[Json.arr #[toJson r.year, toJson r.month, toJson r.day, toJson r.hour, toJson r.minute,
      toJson r.second, toJson r.weekday, toJson r.julian, toJson r.tz, encStrOpt r.tzname, toJson r.gmtoff],
    toJson r.fraction, toJson r.gmtoffFraction]

def encTzFull (t : Tz) : Json :=
  match t.kind with
  | .timezone o n => Json.arr #[toJson t.oid, encD o, encStrOpt n]
  | .custom i => Json.arr #[toJson t.oid, toJson i]

def encDTz (v : DT) : Json :=
  Json.arr #[encDTv v, match v.tz with | some t => encTzFull t | none => .null]

def encTMz (v : TM) : Json :=
  Json.arr #[encTMv v, match v.tz with | some t => encTzFull t | none => .null]

def runObj (fn : String) (j : Json) : Except String Json := do
  let isC := (j.getObjValAs? String "impl").toOption == some "c"
  let env := testEnv isC
  let norm := (j.getObjValAs? Bool "norm").toOption.getD true
  let chars (k : String) : Except String (List Char) := do
    let a ← (← field j k).getArr?
    return (a.toList.map (fun x => Char.ofNat ((x.getNat?).toOption.getD 0)))
  match fn with
  | "td_cmp" =>
    let a ← decDelta (← field j "a"); let b ← decDelta (← field j "b"); let op ← getOp j
    return toJson (if isC then a.richC op b else a.richPy op b)
  | "td_bool" => return toJson (← decDelta (← field j "a")).bool
  | "td_pos" =>
    let a ← decDelta (← field j "a")
    let enc (r : ObjRes Delta) : Json := Json.arr #[encD (r.value a), toJson (r == .self_)]
    return encPy enc (if isC then a.posC else .ok a.posPy)
  | "td_rsub" =>
    let a ← decDelta (← field j "a"); let b ← decDelta (← field j "b")
    return encPy encD (if isC then a.rsubC b else a.rsubPy b)
  | "td_hash" =>
    let a ← decDelta (← field j "a")
    return encKey (if isC then a.hashKeyC else a.hashKey)
  | "td_state" => return toJson (← decDelta (← field j "a")).getstate
  | "date_cmp" =>
    let a ← getYMD j "a"; let b ← getYMD j "b"; let op ← getOp j
    let r := (if isC then dateRichC else dateRichPy) op a b false
    return toJson r
  | "date_hash" =>
    let a ← getYMD j "a"
    return encKey ((if isC then dateHashKeyC else dateHashKeyPy) a.1 a.2.1 a.2.2)
  | "date_weekday" =>
    let a ← getYMD j "a"
    return toJson #[(if isC then dateWeekdayC else dateWeekdayPy) a.1 a.2.1 a.2.2,
      (if isC then dateIsoweekdayC else dateIsoweekdayPy) a.1 a.2.1 a.2.2]
  | "date_sub_date" =>
    let a ← getYMD j "a"; let b ← getYMD j "b"
    return encPy encD ((if isC then dateSubDateC else dateSubDatePy) a b)
  | "date_sub_delta" =>
    let a ← getYMD j "a"; let t ← decDelta (← field j "td")
    return encPy encYMD' ((if isC then dateSubDeltaC else dateSubDeltaPy) a.1 a.2.1 a.2.2 t)
  | "date_replace" =>
    let a ← getYMD j "a"
    let f := if isC then dateReplaceC else dateReplacePy
    return encPy encYMD' (f a.1 a.2.1 a.2.2 (← getReplArg j "ny") (← getReplArg j "nm") (← getReplArg j "nd"))
  | "date_timetuple" =>
    let a ← getYMD j "a"
    return encTT ((if isC then dateTimetupleC else dateTimetuplePy) a.1 a.2.1 a.2.2)
  | "date_ctime" =>
    let a ← getYMD j "a"
    return toJson ((if isC then ctimeC else ctimePy) a.1 a.2.1 a.2.2 0 0 0)
  | "date_repr" =>
    let a ← getYMD j "a"
    let cls : ReprCls := match (j.getObjValAs? Nat "cls").toOption.getD 0 with
      | 1 => .sub "__main__" "DSub" "DSub"
      | 2 => .sub "__main__" "Outer.DSub" "DSub"
      | _ => .base
    return toJson ((if isC then dateReprClsC else dateReprClsPy) cls a.1 a.2.1 a.2.2)
  | "td_float" =>
    let a ← decDelta (← field j "a")
    let x := Binary64.F64.ofBits (← getNat j "x")
    let r := match (← getStr j "op"), isC with
      | "mul", true => a.mulFloatC x
      | "mul", false => a.mulFloatPy x
      | _, true => a.truedivFloatC x
      | _, false => a.truedivFloatPy x
    return encPy encD r
  | "td_float_sub" =>
    -- a float subclass whose `as_integer_ratio` returns `["t", ints]` (a tuple), `["l", ints]`
    -- (a list), `["n"]` (an int, not iterable) or raises `ValueError(msg)` (`["e", msg]`)
    let a ← decDelta (← field j "a")
    let r ← (← field j "r").getArr?
    let ints : List Int := ((r.getD 1 .null).getArr?.toOption.getD #[]).toList.map
      (fun v => (v.getInt?).toOption.getD 0)
    let rs : Py RatioSeq ← match ← (r.getD 0 .null).getStr? with
      | "t" => pure (.ok (.tuple ints))
      | "l" => pure (.ok (.list ints))
      | "e" => pure (.error (.valueError (← (r.getD 1 .null).getStr?)))
      | _ => pure (.ok .notIter)
    let x : FloatOperand := .sub rs
    let res := match (← getStr j "op"), isC with
      | "mul", true => a.mulFloatObjC x
      | "mul", false => a.mulFloatObjPy x
      | _, true => a.truedivFloatObjC x
      | _, false => a.truedivFloatObjPy x
    return encPy encD res
  | "date_sub_dt" =>
    let a ← getYMD j "a"; let b ← getYMD j "b"
    let r := binarySub ((if isC then dateSubC else dateSubPy) a.1 a.2.1 a.2.2 (.datetime b.1 b.2.1 b.2.2))
    return encPy (fun (v : SubResult) => match v with
      | .delta t => encD t
      | .date y m d => encYMD' (y, m, d)) r
  | "date_format" =>
    let a ← getYMD j "a"
    let fmt : FmtArg := match j.getObjVal? "f" with
      | .ok .null => .other
      | .error _ => .other
      | .ok v => match v.getArr? with
        | .ok arr => .str (arr.toList.map (fun x => Char.ofNat ((x.getNat?).toOption.getD 0)))
        | .error _ => .other
    let str : Py String := .ok (String.ofList ((if isC then dateIsoformatC else dateIsoformat) a.1 a.2.1 a.2.2))
    let strf : List Char → Py String := fun _ => .error .modelFuel
    let r := (if isC then dateFormatC else dateFormatPy) fmt str strf
    return encPy (fun (v : Sum String String) => match v with
      | .inl s => toJson s
      | .inr s => toJson s) r
  | "date_state" =>
    let a ← getYMD j "a"
    return toJson (dateGetstate a.1 a.2.1 a.2.2)
  | "iso_repr" =>
    let a ← getYMD j "a"
    let i := isocalendar a.1 a.2.1 a.2.2
    return toJson ((if isC then isoReprC else isoReprPy) i.1 i.2.1 i.2.2)
  | "date_strftime" =>
    let a ← getYMD j "a"; let f ← chars "f"
    let g := (isocalendar a.1 a.2.1 a.2.2).1
    return encPy encStrf ((if isC then dateStrftimeC else dateStrftimePy) env a.1 a.2.1 a.2.2 f g norm)
  | "tz_str" =>
    let some t := ← decTz (← field j "tz") | throw "tz"
    match t.kind with
    | .timezone o n => return toJson (if isC then timezoneStrC t.oid o n else timezoneStrPy o n)
    | _ => throw "tz"
  | "tz_repr" =>
    let some t := ← decTz (← field j "tz") | throw "tz"
    return toJson (t.repr env)
  | "tm_off" =>
    let t ← decTM (← field j "t")
    let o := if isC then t.utcoffsetC env else t.utcoffsetPy env
    let d := if isC then t.dstC env else t.dstPy env
    let n := if isC then t.tznameC env else t.tznamePy env
    return Json.arr #[encOffPy o, encOffPy d, encPy encStrOpt n]
  | "dt_off" =>
    let t ← decDT (← field j "t")
    let o := if isC then t.utcoffsetC env else t.utcoffsetPy env
    let d := if isC then t.dstC env else t.dstPy env
    let n := if isC then t.tznameC env else t.tznamePy env
    return Json.arr #[encOffPy o, encOffPy d, encPy encStrOpt n]
  | "tm_cmp" =>
    let a ← decTM (← field j "a"); let b ← decTM (← field j "b"); let op ← getOp j
    return encPy toJson ((if isC then tmRichC else tmRichPy) env op a b)
  | "tm_hash" =>
    let a ← decTM (← field j "a")
    return encPy encKey ((if isC then tmHashKeyC else tmHashKeyPy) env a)
  | "tm_repr" =>
    let a ← decTM (← field j "a")
    return toJson ((if isC then timeReprC else timeReprPy) env a)
  | "tm_iso" =>
    let a ← decTM (← field j "a"); let s ← getSpecS j
    return encPy toJson (do (if isC then tmIsoformatC else tmIsoformatPy) env a (← s))
  | "tm_state" =>
    let a ← decTM (← field j "a")
    return toJson (tmGetstate a (← getInt j "proto"))
  | "tm_strftime" =>
    let a ← decTM (← field j "a"); let f ← chars "f"
    return encPy encStrf ((if isC then tmStrftimeC else tmStrftimePy) env a f norm)
  | "tm_replace" =>
    let a ← decTM (← field j "a")
    return encPy encTMv ((if isC then tmReplaceC else tmReplace) a (← getOptField j "nh") (← getOptField j "nmi")
      (← getOptField j "ns") (← getOptField j "nus") (← getOptField j "nfold") (← getOptTzArg j))
  | "dt_cmp" =>
    let a ← decDT (← field j "a"); let b ← decDT (← field j "b"); let op ← getOp j
    return encPy toJson ((if isC then dtRichC else dtRichPy) env op a b)
  | "dt_hash" =>
    let a ← decDT (← field j "a")
    return encPy encKey ((if isC then dtHashKeyC else dtHashKeyPy) env a)
  | "dt_repr" =>
    let a ← decDT (← field j "a")
    return toJson ((if isC then dtReprC else dtReprPy) env a)
  | "dt_iso" =>
    let a ← decDT (← field j "a"); let s ← getSpecS j
    let sep := Char.ofNat (← getNat j "sep")
    return encPy toJson (do (if isC then dtIsoformatC else dtIsoformatPy) env a sep (← s))
  | "dt_ctime" =>
    let a ← decDT (← field j "a")
    return toJson ((if isC then ctimeC else ctimePy) a.y a.m a.d a.h a.mi a.s)
  | "dt_add" =>
    let a ← decDT (← field j "a"); let t ← decDelta (← field j "td")
    return encPy encDTv (if isC then addDatetimeTimedeltaC a t 1 else dtAddPy a t)
  | "dt_sub_delta" =>
    let a ← decDT (← field j "a"); let t ← decDelta (← field j "td")
    return encPy encDTv (if isC then addDatetimeTimedeltaC a t (-1) else dtSubDeltaPy a t)
  | "dt_sub" =>
    let a ← decDT (← field j "a"); let b ← decDT (← field j "b")
    return encPy encD ((if isC then dtSubC else dtSubPy) env a b)
  | "dt_timetuple" =>
    let a ← decDT (← field j "a")
    return encPy encTT ((if isC then dtTimetupleC else dtTimetuplePy) env a)
  | "dt_utctimetuple" =>
    let a ← decDT (← field j "a")
    return encPy encTT ((if isC then dtUtctimetupleC else dtUtctimetuplePy) env a)
  | "dt_parts" =>
    let a ← decDT (← field j "a")
    return Json.arr #[encYMD' (dtDate a), encTMv (dtTime a), encTMv (dtTimetz a)]
  | "dt_combine" =>
    let a ← getYMD j "ymd"; let t ← decTM (← field j "t")
    return encPy encDTv (dtCombine a t (← getOptTzArg j))
  | "dt_replace" =>
    let a ← decDT (← field j "a")
    return encPy encDTv ((if isC then dtReplaceC else dtReplace) a (← getOptField j "ny") (← getOptField j "nm")
      (← getOptField j "nd") (← getOptField j "nh") (← getOptField j "nmi") (← getOptField j "ns")
      (← getOptField j "nus") (← getOptField j "nfold") (← getOptTzArg j))
  | "dt_fromutc" =>
    let a ← decDT (← field j "a")
    let some tz := ← decTz (← field j "tz") | throw "tz"
    return encPy encDTv ((if isC then tzFromutcC else tzFromutcPy) env tz a)
  | "dt_astimezone" =>
    let a ← decDT (← field j "a")
    let some tz := ← decTz (← field j "tz") | throw "tz"
    return encPy (fun o => (o.map encDTv).getD .null) ((if isC then dtAstimezoneC else dtAstimezonePy) env a tz)
  | "dt_state" =>
    let a ← decDT (← field j "a")
    return toJson (dtGetstate a (← getInt j "proto"))
  | "dt_strftime" =>
    let a ← decDT (← field j "a"); let f ← chars "f"
    let g := (isocalendar a.y a.m a.d).1
    return encPy encStrf ((if isC then dtStrftimeC else dtStrftimePy) env a f g norm)
  | "fromordinal_arg" =>
    let a ← decArg (← field j "a")
    return encPy encYMD' (if isC then fromordinalArgC a else fromordinalArgPy a)
  | "ctor_date" =>
    let args ← getArgs j "args"
    return encPy encYMD' (if isC then dateNewC args else dateCallPy args)
  | "ctor_time" =>
    let args ← getArgs j "args"
    let fold ← getFoldArg j
    return encPy encTMv (if isC then timeNewC args fold else timeCallPy args fold)
  | "ctor_datetime" =>
    let args ← getArgs j "args"
    let fold ← getFoldArg j
    return encPy encDTv (if isC then datetimeNewC args fold else datetimeCallPy args fold)
  | "td_str2" =>
    let a ← decDelta (← field j "a")
    return if isC then toJson #[a.strC, a.reprC] else toJson #[a.str, a.repr]
  | "tz_new" =>
    let off ← decDelta (← field j "td")
    let name : TzName ← match ← field j "name" with
      | .null => pure .omitted
      | v => match v.getStr? with
        | .ok s => pure (.str s)
        | .error _ => pure .other
    return encPy encTzFull ((if isC then timezoneNewC else timezoneNewPy) 1 off name)
  | "tz_cmp" =>
    let a ← decDelta (← field j "a"); let b ← decDelta (← field j "b"); let op ← getOp j
    let r : Option Bool := if isC then timezoneRichC op a b
      else if op = .eq then some (timezoneEqPy a b)
      else if op = .ne then some (!timezoneEqPy a b) else none
    return toJson r
  | "strp_pattern" =>
    let lt ← decLocale (← field j "lt")
    return encPy toJson (strptimeCompile lt (← getStr j "format"))
  | "strp_core" =>
    let lt ← decLocale (← field j "lt"); let found ← decFound (← field j "found")
    return encPy encStrp (strptimeCore lt found)
  | "strp_tail" =>
    let lt ← decLocale (← field j "lt"); let found ← decFound (← field j "found")
    let colonZ : Option (Option String) := found.lookup "colon_z"
    return encPy encStrp (strptimeTail lt (← chars "data") (← getNat j "end") found colonZ)
  | "strp_date" =>
    let lt ← decLocale (← field j "lt"); let found ← decFound (← field j "found")
    return encPy encYMD' (strptimeDate lt found)
  | "strp_time" =>
    let lt ← decLocale (← field j "lt"); let found ← decFound (← field j "found")
    return encPy encTMz (strptimeDatetimeTime lt found)
  | "strp_dt" =>
    let lt ← decLocale (← field j "lt"); let found ← decFound (← field j "found")
    return encPy encDTz (strptimeDatetime lt found)
  | "strp_julian" =>
    return encPy toJson (calcJulianFromUorW (← getInt j "y") (← getInt j "w") (← getInt j "d") (← getBool j "mon"))
  | "strp_findall" =>
    return toJson (findall (← chars "h") (← chars "n"))
  | "strp_seq" =>
    return toJson (seqToRE (← getStrList (← field j "xs")) (← getStr j "d"))
  | "utc_seconds" =>
    let a ← (← (← field j "a").getArr?).mapM (·.getInt?)
    return encPy toJson (utcToSecondsC (a.getD 0 0) (a.getD 1 0) (a.getD 2 0) (a.getD 3 0) (a.getD 4 0) (a.getD 5 0))
  | "mktime" =>
    let off ← getInt j "off"; let t ← getInt j "t"; let fold ← getInt j "fold"
    let loc : Int → Py Int := fun u => .ok (u + off)
    return encPy toJson ((if isC then localToSecondsC else mktimePy) loc t fold)
  | other => throw s!"unknown fn {other}"

end PyLean.Datetime
