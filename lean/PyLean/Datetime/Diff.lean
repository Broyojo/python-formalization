import PyLean.DiffCore
import PyLean.Datetime.IsoC
import PyLean.Datetime.Format
import PyLean.Datetime.DiffObj
import PyLean.Datetime.ZoneDiff
import PyLean.Datetime.Diff2
import PyLean.Datetime.Diff3

/-!
Differential-testing handler for `datetime` cases (`"mod": "datetime"`).
Each case names the implementation it is checked against through its `fn`
(`..._py` is `_pydatetime`, `..._c` is `_datetime`). Encodings: a date is
`[y, m, d]`, a timedelta `[days, seconds, us]`, a time
`[h, mi, s, us, offset_us | null]`, a datetime `[y, m, d, h, mi, s, us, offset]`;
strings travel as lists of code points.
-/

namespace PyLean.Datetime

open Lean PyLean PyLean.Diff

def encYMD (v : Int × Int × Int) : Json := Json.arr #[toJson v.1, toJson v.2.1, toJson v.2.2]
def encDelta (t : Delta) : Json := Json.arr #[toJson t.days, toJson t.seconds, toJson t.us]
def encTz : Option Int → Json
  | none => Json.null
  | some o => toJson o
def encTime (t : TimeV) : Json := Json.arr #[toJson t.h, toJson t.mi, toJson t.s, toJson t.us, encTz t.tz]
def encDT (v : DateTimeV) : Json :=
  Json.arr #[toJson v.y, toJson v.m, toJson v.d, toJson v.t.h, toJson v.t.mi, toJson v.t.s,
    toJson v.t.us, encTz v.t.tz]

def getIntArr (j : Json) (key : String) : Except String (Array Int) := do
  let arr ← (← field j key).getArr?
  arr.mapM (·.getInt?)

def getDelta (j : Json) (key : String) : Except String Delta := do
  let a ← getIntArr j key
  return ⟨a.getD 0 0, a.getD 1 0, a.getD 2 0⟩

def getChars (j : Json) (key : String) : Except String (List Char) := do
  let a ← getIntArr j key
  return a.toList.map (fun n => Char.ofNat n.toNat)

def getSpec (j : Json) : Except String TimeSpec := do
  match ← getStr j "spec" with
  | "auto" => pure .auto
  | "hours" => pure .hours
  | "minutes" => pure .minutes
  | "seconds" => pure .seconds
  | "milliseconds" => pure .milliseconds
  | "microseconds" => pure .microseconds
  | s => throw s!"bad spec {s}"

def getOptTz (j : Json) : Except String (Option Int) := getOptInt j "tz"

/-- The `timespec` argument: a string, `{"surrogate": [code points]}` for a `str` with a lone
surrogate, or (a JSON number) a hashable non-`str`. -/
def getSpecArg (j : Json) : Except String SpecArg := do
  let v ← field j "spec"
  match v.getStr? with
  | .ok s => return .str s
  | .error _ =>
    match v.getObjVal? "surrogate" with
    | .ok _ => return .surrogateStr
    | .error _ => return .other true

/-- The valid timedelta of `us` microseconds (an offset from the difftest). -/
def deltaOfUs (us : Int) : Delta := ⟨us / 86400000000, us / 1000000 % 86400, us % 1000000⟩

/-- `time.isoformat(timespec)` in C: the clinic `str` converter and the spec search, the C
time formatter, then `format_utcoffset`. -/
def timeIsoformatC (t : TimeV) (spec : SpecArg) : Py (List Char) := do
  let sp ← parseTimespecArgC spec
  return formatTimeC t.h t.mi t.s t.us sp ++ formatUtcoffsetC [':'] (t.tz.map deltaOfUs)

/-- `time.isoformat(timespec)` in Python, with the spec lookup of `_format_time`. -/
def timeIsoformatPyArg (t : TimeV) (spec : SpecArg) : Py (List Char) := do
  let sp ← parseTimespecArgPy spec
  return timeIsoformat t sp

def run (fn : String) (j : Json) : Except String Json := do
  let ints (k : String) := getIntArr j k
  match fn with
  | "td_py" | "td_c" =>
    let a ← ints "args"
    let f := if fn = "td_py" then deltaPy else deltaC
    return encPy encDelta (f (a.getD 0 0) (a.getD 1 0) (a.getD 2 0) (a.getD 3 0) (a.getD 4 0) (a.getD 5 0) (a.getD 6 0))
  | "td_op_py" | "td_op_c" =>
    let py := fn = "td_op_py"
    let a ← getDelta j "a"
    let b ← getDelta j "b"
    let k ← getInt j "k"
    match ← getStr j "op" with
    | "add" => return encPy encDelta (if py then a.addPy b else a.addC b)
    | "sub" => return encPy encDelta (if py then a.subPy b else a.subC b)
    | "neg" => return encPy encDelta (if py then a.negPy else a.negC)
    | "abs" => return encPy encDelta (if py then a.absPy else a.absC)
    | "mul" => return encPy encDelta (if py then a.mulPy k else a.mulC k)
    | "floordiv_int" => return encPy encDelta (if py then a.floordivIntPy k else a.floordivIntC k)
    | "truediv_int" => return encPy encDelta (if py then a.truedivIntPy k else a.truedivIntC k)
    | "floordiv" => return encPy toJson (if py then a.floordivPy b else a.floordivC b)
    | "mod" => return encPy encDelta (if py then a.modPy b else a.modC b)
    | "divmod" =>
      return encPy (fun (q, r) => Json.arr #[toJson q, encDelta r]) (if py then a.divmodPy b else a.divmodC b)
    | op => throw s!"unknown op {op}"
  | "td_str" =>
    let a ← getDelta j "a"
    return encPy toJson (.ok (Json.arr #[toJson a.str, toJson a.repr]) : Py Json)
  | "fromordinal_py" => return encPy encYMD (fromordinalPy (← getInt j "n"))
  | "fromordinal_c" => return encPy encYMD (fromordinalC (← getInt j "n"))
  | "toordinal" =>
    let a ← ints "date"
    return encPy toJson (.ok (toordinal (a.getD 0 0) (a.getD 1 0) (a.getD 2 0)) : Py Int)
  | "isocalendar" =>
    let a ← ints "date"
    return encPy encYMD (.ok (isocalendar (a.getD 0 0) (a.getD 1 0) (a.getD 2 0)))
  | "fromisocalendar_py" | "fromisocalendar_c" =>
    let a ← ints "args"
    let f := if fn = "fromisocalendar_py" then fromisocalendarPy else fromisocalendarC
    return encPy encYMD (f (a.getD 0 0) (a.getD 1 0) (a.getD 2 0))
  | "date_add_py" | "date_add_c" =>
    let a ← ints "date"
    let t ← getDelta j "td"
    let f := if fn = "date_add_py" then dateAddPy else dateAddC
    return encPy encYMD (f (a.getD 0 0) (a.getD 1 0) (a.getD 2 0) t)
  | "timezone_py" | "timezone_c" =>
    let t ← getDelta j "td"
    return encPy toJson (if fn = "timezone_py" then timezonePy t else newTimezoneC t)
  | "date_fromiso_py" => return encPy encYMD (dateFromIsoPy (← getChars j "s"))
  | "date_fromiso_c" => return encPy encYMD (dateFromIsoC (← getChars j "s"))
  | "date_fromiso_arg_py" | "date_fromiso_arg_c" =>
    -- `"arg"`: `"b"` bytes, `"n"` None, `"u"` a str with a lone surrogate
    let a : IsoArg := match (j.getObjValAs? String "arg").toOption with
      | some "u" => .surrogateStr
      | _ => .other
    return encPy encYMD ((if fn = "date_fromiso_arg_py" then dateFromIsoArgPy else dateFromIsoArgC) a)
  | "time_fromiso_py" => return encPy encTime (timeFromIsoPy (← getChars j "s"))
  | "time_fromiso_c" => return encPy encTime (timeFromIsoC (← getChars j "s"))
  | "datetime_fromiso_py" => return encPy encDT (datetimeFromIsoPy (← getChars j "s"))
  | "datetime_fromiso_c" => return encPy encDT (datetimeFromIsoC (← getChars j "s"))
  | "date_isoformat" =>
    let a ← ints "date"
    let isC := (j.getObjValAs? String "impl").toOption == some "c"
    let f := if isC then dateIsoformatC else dateIsoformat
    return encPy toJson (.ok (String.ofList (f (a.getD 0 0) (a.getD 1 0) (a.getD 2 0))) : Py String)
  | "time_isoformat" =>
    let a ← ints "time"
    let isC := (j.getObjValAs? String "impl").toOption == some "c"
    let t : TimeV := ⟨a.getD 0 0, a.getD 1 0, a.getD 2 0, a.getD 3 0, ← getOptTz j⟩
    let sp ← getSpecArg j
    return encPy (fun cs => toJson (String.ofList cs))
      (if isC then timeIsoformatC t sp else timeIsoformatPyArg t sp)
  | "datetime_isoformat" =>
    let a ← ints "dt"
    let sep ← getInt j "sep"
    let isC := (j.getObjValAs? String "impl").toOption == some "c"
    let v : DateTimeV := ⟨a.getD 0 0, a.getD 1 0, a.getD 2 0,
      ⟨a.getD 3 0, a.getD 4 0, a.getD 5 0, a.getD 6 0, ← getOptTz j⟩⟩
    let sp ← getSpecArg j
    let c := Char.ofNat sep.toNat
    let r : Py (List Char) := if isC then
        (do let t ← timeIsoformatC v.t sp; return dateIsoformatC v.y v.m v.d ++ [c] ++ t)
      else (do let s ← parseTimespecArgPy sp; return datetimeIsoformat v c s)
    return encPy (fun cs => toJson (String.ofList cs)) r
  | other =>
    if other.startsWith "zi_" then Zone.runZone other j
    else if other.startsWith "x2_" then runX2 other j
    else if other.startsWith "x3_" then runX3 other j
    else runObj other j

/-- Results of `runObj` that are not already `{"ok": ...}` or `{"exc": ...}`. -/
def wrapOk (r : Json) : Json :=
  match r.getObjVal? "ok", r.getObjVal? "exc" with
  | .error _, .error _ => Json.mkObj [("ok", r)]
  | _, _ => r

def handler : Handler := fun fn j => some (wrapOk <$> run fn j)

end PyLean.Datetime
