import PyLean.Datetime.IsoPy

/-!
`isoformat()` for `date`, `time` and `datetime` (`Lib/_pydatetime.py`; the C
`date_isoformat`, `time_isoformat`, `datetime_isoformat` and `format_utcoffset`
produce the same text, which the differential test checks against both).
-/

namespace PyLean.Datetime

open PyLean

inductive TimeSpec where
  | auto | hours | minutes | seconds | milliseconds | microseconds
  deriving Repr, DecidableEq, Inhabited

/-- `_format_time`, _pydatetime.py:163-185 (an unknown `timespec` string is
rejected before this is reached, with `ValueError('Unknown timespec value')`). -/
def formatTime (hh mm ss us : Int) (spec : TimeSpec) : List Char :=
  let spec : TimeSpec := match spec with
    | .auto => if us ≠ 0 then .microseconds else .seconds
    | s => s
  match spec with
  | .hours => padInt 2 hh
  | .minutes => padInt 2 hh ++ [':'] ++ padInt 2 mm
  | .seconds | .auto => padInt 2 hh ++ [':'] ++ padInt 2 mm ++ [':'] ++ padInt 2 ss
  | .milliseconds => padInt 2 hh ++ [':'] ++ padInt 2 mm ++ [':'] ++ padInt 2 ss ++ ['.'] ++ padInt 3 (us / 1000)
  | .microseconds => padInt 2 hh ++ [':'] ++ padInt 2 mm ++ [':'] ++ padInt 2 ss ++ ['.'] ++ padInt 6 us

/-- `_format_offset(off, sep)`, _pydatetime.py:187-203, for an offset of `off`
microseconds with `|off| < 24h` (C `format_utcoffset`, :1767-1813). -/
def formatOffsetSep (sep : List Char) : Option Int → List Char
  | none => []
  | some off =>
    let sign := if off < 0 then '-' else '+'
    let a := off.natAbs
    let hh := a / 3600000000
    let mm := a % 3600000000 / 60000000
    let ss := a % 60000000
    let s := [sign] ++ padNat 2 hh ++ sep ++ padNat 2 mm
    if ss ≠ 0 then
      let s := s ++ sep ++ padNat 2 (ss / 1000000)
      if ss % 1000000 ≠ 0 then s ++ ['.'] ++ padNat 6 (ss % 1000000) else s
    else s

/-- `_format_offset(off)` with the default `sep=':'`. -/
def formatOffset (off : Option Int) : List Char := formatOffsetSep [':'] off

/-- `date.isoformat()`, _pydatetime.py:1139-1148. -/
def dateIsoformat (y m d : Int) : List Char :=
  padInt 4 y ++ ['-'] ++ padInt 2 m ++ ['-'] ++ padInt 2 d

/-- `time.isoformat(timespec)`, _pydatetime.py:1625-1640. -/
def timeIsoformat (t : TimeV) (spec : TimeSpec) : List Char :=
  formatTime t.h t.mi t.s t.us spec ++ formatOffset t.tz

/-- `datetime.isoformat(sep, timespec)`, _pydatetime.py:2174-2199. -/
def datetimeIsoformat (dt : DateTimeV) (sep : Char) (spec : TimeSpec) : List Char :=
  dateIsoformat dt.y dt.m dt.d ++ [sep] ++ timeIsoformat dt.t spec

end PyLean.Datetime
