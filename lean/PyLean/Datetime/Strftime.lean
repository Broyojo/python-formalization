import PyLean.Datetime.Objects

/-!
`strftime` preprocessing: `_wrap_strftime`, _pydatetime.py:217-295, and
`wrap_strftime`, _datetimemodule.c:1884-2066. Both rewrite the format and call
`time.strftime(newformat, timetuple)`. That final call belongs to the C library, so
the model stops at the pair `(newformat, timetuple)`.

`norm` is `_need_normalize_century()` / `normalize_century()`, a property of the C
library's `%Y`, and `gyear` is `int(time.strftime('%G', timetuple))`.
-/

namespace PyLean.Datetime

open PyLean

/-- What `strftime` is called on: `date` has no `utcoffset`/`tzname`/`microsecond`
attribute, `time` calls its tzinfo with `None`, `datetime` with itself. -/
inductive StrfObj where
  | date
  | time (t : TM)
  | dt (d : DT)
  deriving Repr, DecidableEq, Inhabited

/-- `getattr(object, 'microsecond', 0)`. -/
def StrfObj.microsecond : StrfObj → Int
  | .date => 0
  | .time t => t.us
  | .dt d => d.us

/-- `_format_offset(object.utcoffset(), sep)` or `""` without the attribute. -/
def StrfObj.zreplacePy (env : TzEnv) (sep : List Char) : StrfObj → Py (List Char)
  | .date => .ok []
  | .time t => do return formatOffsetSep sep ((← t.utcoffsetPy env).map Delta.toUs)
  | .dt d => do return formatOffsetSep sep ((← d.utcoffsetPy env).map Delta.toUs)

/-- `s.replace('%', '%%')`. -/
def escapePercent (s : List Char) : List Char :=
  s.flatMap fun c => if c = '%' then ['%', '%'] else [c]

/-- The `%Z` branch of `_wrap_strftime`. -/
def StrfObj.ZreplacePy (env : TzEnv) : StrfObj → Py (List Char)
  | .date => .ok []
  | .time t => do
    match ← t.tznamePy env with
    | none => return []
    | some s => return escapePercent s.toList
  | .dt d => do
    match ← d.tznamePy env with
    | none => return []
    | some s => return escapePercent s.toList

/-- The scan of `_wrap_strftime`, _pydatetime.py:227-292. The replacement strings are
cached in the source; a tzinfo method is pure here, so caching changes nothing. The
loop is on the remaining format; `fuel` is its length. -/
def wrapScanPy (env : TzEnv) (obj : StrfObj) (tt0 gyear : Int) (mon day : Int) (norm : Bool) :
    Nat → List Char → Py (List Char)
  | 0, _ => .ok []
  | _ + 1, [] => .ok []
  | fuel + 1, ch :: rest =>
    if ch ≠ '%' then do return ch :: (← wrapScanPy env obj tt0 gyear mon day norm fuel rest)
    else match rest with
      | [] => .ok ['%']
      | ch :: rest =>
        if ch = 'f' then do
          return padInt 6 obj.microsecond ++ (← wrapScanPy env obj tt0 gyear mon day norm fuel rest)
        else if ch = 'z' then do
          let z ← obj.zreplacePy env []
          return z ++ (← wrapScanPy env obj tt0 gyear mon day norm fuel rest)
        else if ch = ':' then
          match rest with
          | [] => wrapScanPy env obj tt0 gyear mon day norm fuel []
          | ch2 :: rest =>
            if ch2 = 'z' then do
              let z ← obj.zreplacePy env [':']
              return z ++ (← wrapScanPy env obj tt0 gyear mon day norm fuel rest)
            else do
              return ['%', ch, ch2] ++ (← wrapScanPy env obj tt0 gyear mon day norm fuel rest)
        else if ch = 'Z' then do
          let z ← obj.ZreplacePy env
          return z ++ (← wrapScanPy env obj tt0 gyear mon day norm fuel rest)
        else if (ch = 'Y' ∨ ch = 'G' ∨ ch = 'F' ∨ ch = 'C') ∧ tt0 < 1000 ∧ norm then do
          let year := if ch = 'G' then gyear else tt0
          let out := if ch = 'C' then padInt 2 (year / 100)
            else if ch = 'F' then padInt 4 year ++ ['-'] ++ padInt 2 mon ++ ['-'] ++ padInt 2 day
            else padInt 4 year
          return out ++ (← wrapScanPy env obj tt0 gyear mon day norm fuel rest)
        else do
          return ['%', ch] ++ (← wrapScanPy env obj tt0 gyear mon day norm fuel rest)

/-- `_wrap_strftime(object, format, timetuple)`, _pydatetime.py:217-295: the format
handed to `time.strftime`. -/
def wrapStrftimePy (env : TzEnv) (obj : StrfObj) (format : List Char) (tt : TimeTuple)
    (gyear : Int) (norm : Bool) : Py (List Char) :=
  wrapScanPy env obj (tt.getD 0 0) gyear (tt.getD 1 0) (tt.getD 2 0) norm format.length format

/-! ### C -/

/-- `make_freplacement`, :1863-1874. -/
def makeFreplacementC (obj : StrfObj) : List Char := padInt 6 obj.microsecond

/-- What `get_tzinfo_member` reads of the object `wrap_strftime` was called on:
`PyDateTime_Check(self)`, `PyTime_Check(self)`, the `hastzinfo` byte (`HASTZINFO`) and the
`tzinfo` member (`none`: `Py_None`). -/
structure TzMemberView where
  isDatetime : Bool
  isTime : Bool
  hastzinfo : Bool
  tzinfo : Option Tz
  deriving Repr, DecidableEq

/-- `get_tzinfo_member(self)`, :1505-1515: the `tzinfo` member of a `datetime` with
`HASTZINFO` (:1509-1510), else of a `time` with `HASTZINFO` (:1511-1512), else `NULL` (the outer
`none`). A borrowed reference; no error path. -/
def getTzinfoMemberC (o : TzMemberView) : Option (Option Tz) :=
  if o.isDatetime && o.hastzinfo then some o.tzinfo
  else if o.isTime && o.hastzinfo then some o.tzinfo
  else none

/-- The struct of each object `strftime` runs on: a `date` passes neither check (its
`hastzinfo` byte is 0); `new_time_ex2` and `new_datetime_ex2` set `hastzinfo = aware`, i.e.
`tzinfo != Py_None` (:1333, :1228). A `datetime` is not a `time`. -/
def StrfObj.cView : StrfObj → TzMemberView
  | .date => ⟨false, false, false, none⟩
  | .time t => ⟨false, true, t.tz.isSome, t.tz⟩
  | .dt d => ⟨true, false, d.tz.isSome, d.tz⟩

/-- The `tzinfoarg` `wrap_strftime` is given: `self` from `datetime_date_strftime_impl`
(:3676, which `datetime` inherits), `Py_None` from `datetime_time_strftime_impl` (:4995-4996).
For a `date` it is never used. -/
def StrfObj.tzinfoArg : StrfObj → Option DT
  | .dt d => some d
  | _ => none

/-- `make_somezreplacement(object, sep, tzinfoarg)`, :1799-1817, on the struct: `""` when
`get_tzinfo_member` gives `NULL` or `Py_None` (:1803-1806), else `format_utcoffset` (:1809-1813),
whose `call_utcoffset(tzinfo, tzinfoarg)` (:1740, :1571-1574) is checked by
`call_tzinfo_method`. -/
def makeSomezreplacementViewC (env : TzEnv) (sep : List Char) (o : TzMemberView) (arg : Option DT) :
    Py (List Char) :=
  match getTzinfoMemberC o with
  | none | some none => .ok []
  | some (some tz) => do
    return formatUtcoffsetC sep (← callTzinfoCheckC "utcoffset" (← tzUtcoffsetRaw env tz arg))

/-- `make_somezreplacement` for the object `wrap_strftime` runs on. -/
def makeSomezreplacementC (env : TzEnv) (sep : List Char) (obj : StrfObj) : Py (List Char) :=
  makeSomezreplacementViewC env sep obj.cView obj.tzinfoArg

/-- `make_Zreplacement(object, tzinfoarg)`, :1820-1860, on the struct: `""` for a `NULL` or
`Py_None` member (:1828-1829); `call_tzname(tzinfo, tzinfoarg)` (:1832), `None` giving `""`
(:1835-1838), and a string's `replace('%', '%%')` (:1846; an exact `str`, so the method is
`str.replace` and the `PyUnicode_Check` of :1850-1854 passes). -/
def makeZreplacementViewC (env : TzEnv) (o : TzMemberView) (arg : Option DT) : Py (List Char) :=
  match getTzinfoMemberC o with
  | none | some none => .ok []
  | some (some tz) => do
    match ← callTznameCheckC (← tzTznameRawC env tz arg) with
    | none => return []
    | some s => return escapePercent s.toList

/-- `make_Zreplacement` for the object `wrap_strftime` runs on. -/
def makeZreplacementC (env : TzEnv) (obj : StrfObj) : Py (List Char) :=
  makeZreplacementViewC env obj.cView obj.tzinfoArg

/-- Scan state of `wrap_strftime`: read position, start of the pending literal, output. -/
structure WrapState where
  i : Nat
  start : Nat
  out : List Char

/-- `PyUnicode_FindChar(format, '%', i, flen, 1)`. -/
def findPercent (format : List Char) (i : Nat) : Option Nat :=
  ((format.drop i).findIdx? (· = '%')).map (· + i)

/-- `PyUnicodeWriter_WriteSubstring(writer, format, start, end)`. -/
def substr (format : List Char) (start stop : Nat) : List Char :=
  (format.drop start).take (stop - start)

/-- The `while (i != flen)` loop of `wrap_strftime`, :1884-2066. `fuel` bounds the
iterations; each one advances `i`. -/
def wrapLoopC (env : TzEnv) (obj : StrfObj) (format : List Char) (tt0 gyear : Int) (norm : Bool) :
    Nat → WrapState → Py WrapState
  | 0, st => .ok st
  | fuel + 1, st =>
    let flen := format.length
    if st.i = flen then .ok st
    else match findPercent format st.i with
      | none => .ok st
      | some stop =>
        let i := stop + 1
        if i = flen then .ok { st with i := i }
        else
          let ch := format.getD i ' '
          let i := i + 1
          let next := wrapLoopC env obj format tt0 gyear norm fuel
          let emit (i : Nat) (r : List Char) : Py WrapState :=
            next ⟨i, i, st.out ++ substr format st.start stop ++ r⟩
          if ch = 'z' then do emit i (← makeSomezreplacementC env [] obj)
          else if ch = ':' ∧ i < flen ∧ format.getD i ' ' = 'z' then do
            emit (i + 1) (← makeSomezreplacementC env [':'] obj)
          else if ch = 'Z' then do emit i (← makeZreplacementC env obj)
          else if ch = 'f' then emit i (makeFreplacementC obj)
          else if norm ∧ (ch = 'Y' ∨ ch = 'G' ∨ ch = 'F' ∨ ch = 'C') then
            if tt0 ≥ 1000 then next { st with i := i }
            else
              let year := if ch = 'G' then gyear else tt0
              let buf := padInt 4 year ++ (if ch = 'F' then "-%m-%d".toList else [])
              let buf := if ch = 'C' then buf.take (buf.length - 2) else buf
              emit i buf
          else next { st with i := i }

/-- `wrap_strftime`, :1884-2066: the format handed to `time.strftime`. -/
def wrapStrftimeC (env : TzEnv) (obj : StrfObj) (format : List Char) (tt : TimeTuple)
    (gyear : Int) (norm : Bool) : Py (List Char) := do
  let st ← wrapLoopC env obj format (tt.getD 0 0) gyear norm (format.length + 1) ⟨0, 0, []⟩
  if st.start = 0 then return format
  else return st.out ++ substr format st.start format.length

/-! ### `strftime` and `__format__` of the three classes -/

/-- `date.strftime`, Py:1122-1130, and `datetime_date_strftime_impl`, :3664-3679, up to the
call of `time.strftime`. -/
def dateStrftimePy (env : TzEnv) (y m d : Int) (format : List Char) (gyear : Int) (norm : Bool) :
    Py (List Char × TimeTuple) := do
  let tt := dateTimetuplePy y m d
  return (← wrapStrftimePy env .date format tt gyear norm, tt)

def dateStrftimeC (env : TzEnv) (y m d : Int) (format : List Char) (gyear : Int) (norm : Bool) :
    Py (List Char × TimeTuple) := do
  let tt := dateTimetupleC y m d
  return (← wrapStrftimeC env .date format tt gyear norm, tt)

/-- `datetime.strftime` is `date.strftime` through `self.timetuple()`. -/
def dtStrftimePy (env : TzEnv) (dt : DT) (format : List Char) (gyear : Int) (norm : Bool) :
    Py (List Char × TimeTuple) := do
  let tt ← dtTimetuplePy env dt
  return (← wrapStrftimePy env (.dt dt) format tt gyear norm, tt)

def dtStrftimeC (env : TzEnv) (dt : DT) (format : List Char) (gyear : Int) (norm : Bool) :
    Py (List Char × TimeTuple) := do
  let tt ← dtTimetupleC env dt
  return (← wrapStrftimeC env (.dt dt) format tt gyear norm, tt)

/-- The time tuple of `time.strftime`, Py:1672-1684 and :4926-4955. -/
def tmTimetuple (t : TM) : TimeTuple := [1900, 1, 1, t.h, t.mi, t.s, 0, 1, -1]

/-- `time.strftime`, Py:1672-1684. -/
def tmStrftimePy (env : TzEnv) (t : TM) (format : List Char) (norm : Bool) :
    Py (List Char × TimeTuple) := do
  return (← wrapStrftimePy env (.time t) format (tmTimetuple t) 0 norm, tmTimetuple t)

/-- `datetime_time_strftime_impl`, :4976-4999. -/
def tmStrftimeC (env : TzEnv) (t : TM) (format : List Char) (norm : Bool) :
    Py (List Char × TimeTuple) := do
  return (← wrapStrftimeC env (.time t) format (tmTimetuple t) 0 norm, tmTimetuple t)

/-- `__format__`, Py:1132-1137 and :1686-1691; `datetime_date___format___impl`, :3692-3700: an empty
format is `str(self)`, anything else is `self.strftime(fmt)`. -/
def formatVia {α : Type} (fmt : List Char) (str : Py String) (strf : List Char → Py α) :
    Py (Sum String α) :=
  if fmt.isEmpty then Sum.inl <$> str else Sum.inr <$> strf fmt

end PyLean.Datetime
