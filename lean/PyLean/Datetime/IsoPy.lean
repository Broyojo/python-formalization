import PyLean.Datetime.Calendar

/-!
The pure-Python ISO 8601 parsers of `Lib/_pydatetime.py` (CPython 3.14.7):
`date.fromisoformat`, `time.fromisoformat` and `datetime.fromisoformat`.

Strings are `List Char` (code points). Lean `Char` excludes lone surrogates,
so strings containing them are out of scope.

The 3.14.7 parser converts fixed-width slices with `int()`, which accepts much
more than ASCII digits; `pyInt` models `int(str)` exactly (Unicode 16.0 tables,
as in `unicodedata.unidata_version` of CPython 3.14.7).
-/

namespace PyLean.Datetime

open PyLean

/-! ### `int(str)` -/

/-- Code point of the zero of every run of ten Unicode decimal digits
(`Py_UNICODE_TODECIMAL`), Unicode 16.0. Generated from `int(chr(cp))` over all
non-ASCII code points. -/
def decimalZeros : List Nat :=
  [0x660, 0x6f0, 0x7c0, 0x966, 0x9e6, 0xa66, 0xae6, 0xb66, 0xbe6, 0xc66, 0xce6, 0xd66,
   0xde6, 0xe50, 0xed0, 0xf20, 0x1040, 0x1090, 0x17e0, 0x1810, 0x1946, 0x19d0, 0x1a80,
   0x1a90, 0x1b50, 0x1bb0, 0x1c40, 0x1c50, 0xa620, 0xa8d0, 0xa900, 0xa9d0, 0xa9f0, 0xaa50,
   0xabf0, 0xff10, 0x104a0, 0x10d30, 0x10d40, 0x11066, 0x110f0, 0x11136, 0x111d0, 0x112f0,
   0x11450, 0x114d0, 0x11650, 0x116c0, 0x116d0, 0x116da, 0x11730, 0x118e0, 0x11950, 0x11bf0,
   0x11c50, 0x11d50, 0x11da0, 0x11f50, 0x16130, 0x16a60, 0x16ac0, 0x16b50, 0x16d70, 0x1ccf0,
   0x1d7ce, 0x1d7d8, 0x1d7e2, 0x1d7ec, 0x1d7f6, 0x1e140, 0x1e2f0, 0x1e4f0, 0x1e5f1, 0x1e950,
   0x1fbf0]

/-- Non-ASCII code points with `Py_UNICODE_ISSPACE`, Unicode 16.0. -/
def unicodeSpaces : List Nat :=
  [0x85, 0xa0, 0x1680, 0x2000, 0x2001, 0x2002, 0x2003, 0x2004, 0x2005, 0x2006, 0x2007,
   0x2008, 0x2009, 0x200a, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000]

def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `Py_ISSPACE`: the ASCII white space `\t\n\v\f\r` and space. -/
def isAsciiSpace (c : Char) : Bool := c = ' ' || (9 ≤ c.toNat && c.toNat ≤ 13)

def digitVal (c : Char) : Nat := c.toNat - 48

/-- `_PyUnicode_TransformDecimalAndSpaceToASCII` (Objects/unicodeobject.c) on
one character: ASCII (`< 127`) is kept, Unicode white space becomes `' '`, a
decimal digit becomes its ASCII digit, and anything else makes `int()` fail. -/
def intTransform (c : Char) : Option Char :=
  if c.toNat < 127 then some c
  else if unicodeSpaces.contains c.toNat then some ' '
  else match decimalZeros.find? (fun z => z ≤ c.toNat && c.toNat < z + 10) with
    | some z => some (Char.ofNat (48 + (c.toNat - z)))
    | none => none

/-- Digits with single underscores between them (`long_from_string_base`):
`acc` is the value so far, `und` whether the previous character was `_`. -/
def underscoreDigits : List Char → Nat → Bool → Option Nat
  | [], acc, und => if und then none else some acc
  | c :: cs, acc, und =>
    if isAsciiDigit c then underscoreDigits cs (acc * 10 + digitVal c) false
    else if c = '_' && !und then underscoreDigits cs acc true
    else none

def isDigitOrUnderscore (c : Char) : Bool := isAsciiDigit c || c = '_'

/-- An optional leading sign: whether it is `-`, and the rest. -/
def splitSign : List Char → Bool × List Char
  | '+' :: r => (false, r)
  | '-' :: r => (true, r)
  | r => (false, r)

/-- `PyLong_FromString(s, base=10)` on the transformed ASCII string: leading
white space, an optional sign, digits with underscores, trailing white space. -/
def intAscii (s : List Char) : Option Int :=
  let s := s.dropWhile isAsciiSpace
  let (neg, s) := splitSign s
  let body := s.takeWhile isDigitOrUnderscore
  let rest := s.dropWhile isDigitOrUnderscore
  if !rest.all isAsciiSpace then none
  else match body with
    | c :: _ =>
      if isAsciiDigit c then (underscoreDigits body 0 false).map (fun v => if neg then -(v : Int) else v)
      else none
    | [] => none

/-- `int(s)` for a `str` argument and base 10. -/
def pyInt (s : List Char) : Py Int :=
  match (s.mapM intTransform).bind intAscii with
  | some v => .ok v
  | none => .error (.valueError "~invalid literal for int() with base 10")

/-! ### Helpers -/

/-- `s[a:b]` for `0 <= a, b`. -/
def slice (s : List Char) (a b : Nat) : List Char := (s.drop a).take (b - a)

/-- `s[i]` where the caller knows `i < len(s)`. -/
def charAt (s : List Char) (i : Nat) : Char := s.getD i '\x00'

/-- `s.find(c) + 1`: one plus the first index of `c`, or `0`. -/
def findPlusOne (s : List Char) (c : Char) : Nat :=
  match s.findIdx? (· = c) with
  | some i => i + 1
  | none => 0

/-- A parsed `time`: fields and the UTC offset in microseconds (`none` for a
naive time; `timezone.utc` is `some 0`). -/
structure TimeV where
  h : Int
  mi : Int
  s : Int
  us : Int
  tz : Option Int
  deriving Repr, DecidableEq, Inhabited

/-- A parsed `datetime`. -/
structure DateTimeV where
  y : Int
  m : Int
  d : Int
  t : TimeV
  deriving Repr, DecidableEq, Inhabited

/-- `timezone(offset)` with the name omitted, _pydatetime.py:2407-2420: a zero
offset is `timezone.utc`; otherwise `_minoffset <= offset <= _maxoffset`. -/
def timezonePy (off : Delta) : Py Int :=
  if off.toUs = 0 then .ok 0
  else if -86399999999 ≤ off.toUs ∧ off.toUs ≤ 86399999999 then .ok off.toUs
  else .error (.valueError "~offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24)")

/-! ### Parsers -/

/-- `_find_isoformat_datetime_separator`, _pydatetime.py:301-355. Its
`assert len_dtstr > 7` holds because the only caller rejects strings shorter
than 7 and returns early for length 7. -/
def findSepPy (s : List Char) : Py Nat :=
  let len := s.length
  if len = 7 then .ok 7
  else if charAt s 4 = '-' then
    if charAt s 5 = 'W' then
      if len < 8 then .error (.valueError "Invalid ISO string")
      else if len > 8 ∧ charAt s 8 = '-' then
        if len = 9 then .error (.valueError "Invalid ISO string")
        else if len > 10 ∧ isAsciiDigit (charAt s 10) then .ok 8
        else .ok 10
      else .ok 8
    else .ok 10
  else if charAt s 4 = 'W' then
    let idx := 7 + ((s.drop 7).takeWhile isAsciiDigit).length
    if idx < 9 then .ok idx
    else if idx % 2 = 0 then .ok 7
    else .ok 8
  else .ok 8

/-- `_parse_isoformat_date`, _pydatetime.py:358-393. -/
def parseIsoDatePy (s : List Char) : Py (Int × Int × Int) := do
  let len := s.length
  if ¬(len = 7 ∨ len = 8 ∨ len = 10) then throw (.valueError "Invalid isoformat string")
  let year ← pyInt (slice s 0 4)
  let hasSep := decide (charAt s 4 = '-')
  let pos := 4 + (if hasSep then 1 else 0)
  if slice s pos (pos + 1) = ['W'] then
    let pos := pos + 1
    let weekno ← pyInt (slice s pos (pos + 2))
    let pos := pos + 2
    let dayno ← if len > pos then do
        if decide (slice s pos (pos + 1) = ['-']) != hasSep then
          throw (.valueError "Inconsistent use of dash separator")
        let pos := pos + (if hasSep then 1 else 0)
        pyInt (slice s pos (pos + 1))
      else pure 1
    isoweekToGregorianPy year weekno dayno
  else
    let month ← pyInt (slice s pos (pos + 2))
    let pos := pos + 2
    if decide (slice s pos (pos + 1) = ['-']) != hasSep then
      throw (.valueError "Inconsistent use of dash separator")
    let pos := pos + (if hasSep then 1 else 0)
    let day ← pyInt (slice s pos (pos + 2))
    return (year, month, day)

/-- One `time_comps[comp] = int(tstr[pos:pos+2])` step of `_parse_hh_mm_ss_ff`,
with its length check (:405-408). -/
def timeCompPy (t : List Char) (pos : Nat) : Py Int :=
  if t.length < pos + 2 then .error (.valueError "Incomplete time component")
  else pyInt (slice t pos (pos + 2))

/-- `_FRACTION_CORRECTION[i]`, _pydatetime.py:395. -/
def fractionCorrection (i : Nat) : Int := [100000, 10000, 1000, 100, 10].getD i 0

/-- The fraction tail of `_parse_hh_mm_ss_ff`, _pydatetime.py:425-442. -/
def fractionPy (t : List Char) (pos : Nat) : Py Int := do
  if pos < t.length then
    if charAt t pos ≠ '.' ∧ charAt t pos ≠ ',' then
      throw (.valueError "Invalid microsecond separator")
    let rest := t.drop (pos + 1)
    if !rest.all isAsciiDigit then throw (.valueError "Non-digit values in fraction")
    let toParse := min rest.length 6
    let us ← pyInt (rest.take toParse)
    if toParse < 6 then return us * fractionCorrection (toParse - 1) else return us
  else return 0

/-- `_parse_hh_mm_ss_ff`, _pydatetime.py:398-443: `HH[:?MM[:?SS[{.,}fff[fff]]]]`.
The `for comp in range(3)` loop is unrolled. -/
def parseHHMMSSFFPy (t : List Char) : Py (Int × Int × Int × Int) := do
  let hh ← timeCompPy t 0
  let next := slice t 2 3
  let hasSep := decide (next = [':'])
  if next = [] then return (hh, 0, 0, 0)
  let pos := 2 + (if hasSep then 1 else 0)
  let mm ← timeCompPy t pos
  let pos := pos + 2
  let next := slice t pos (pos + 1)
  if next = [] then return (hh, mm, 0, 0)
  if hasSep ∧ next ≠ [':'] then
    throw (.valueError s!"Invalid time separator: {String.ofList next}")
  let pos := pos + (if hasSep then 1 else 0)
  let ss ← timeCompPy t pos
  let us ← fractionPy t (pos + 2)
  return (hh, mm, ss, us)

/-- `_parse_isoformat_time`, _pydatetime.py:445-500: the time, whether `24:00`
became midnight, and whether hour 24 came with non-zero other fields. -/
def parseIsoTimePy (t : List Char) : Py (TimeV × Bool × Bool) := do
  let len := t.length
  if len < 2 then throw (.valueError "Isoformat time too short")
  let a := findPlusOne t '-'
  let tzPos := if a ≠ 0 then a else
    let b := findPlusOne t '+'
    if b ≠ 0 then b else findPlusOne t 'Z'
  let timestr := if tzPos > 0 then t.take (tzPos - 1) else t
  let (hour, minute, second, us) ← parseHHMMSSFFPy timestr
  let (hour, becameNextDay, errorFromComponents) :=
    if hour = 24 then
      if minute = 0 ∧ second = 0 ∧ us = 0 then ((0 : Int), true, false) else (hour, false, true)
    else (hour, false, false)
  let tzi ← if tzPos = len ∧ t.getLast? = some 'Z' then pure (some 0)
    else if tzPos > 0 then do
      let tzstr := t.drop tzPos
      if tzstr.length = 0 ∨ tzstr.length = 1 ∨ tzstr.length = 3 ∨ charAt t (tzPos - 1) = 'Z' then
        throw (.valueError "Malformed time zone string")
      let (th, tm, ts, tus) ← parseHHMMSSFFPy tzstr
      if th = 0 ∧ tm = 0 ∧ ts = 0 ∧ tus = 0 then pure (some 0)
      else
        let tzsign : Int := if charAt t (tzPos - 1) = '-' then -1 else 1
        let td ← deltaPy 0 ts tus 0 tm th 0
        let off ← td.mulPy tzsign
        some <$> timezonePy off
    else pure none
  return (⟨hour, minute, second, us, tzi⟩, becameNextDay, errorFromComponents)

/-! ### `fromisoformat` -/

/-- `date.fromisoformat`, _pydatetime.py:1040-1055. -/
def dateFromIsoPy (s : List Char) : Py (Int × Int × Int) :=
  if !s.all (fun c => c.toNat < 128) then .error (.valueError "Argument must be an ASCII str")
  else if ¬(s.length = 7 ∨ s.length = 8 ∨ s.length = 10) then
    .error (.valueError "~Invalid isoformat string")
  else match (do let (y, m, d) ← parseIsoDatePy s; checkDate y m d) with
    | .ok v => .ok v
    | .error _ => .error (.valueError "~Invalid isoformat string")

/-- `time.fromisoformat`, _pydatetime.py:1614-1628. The `cls(...)` call checks
the fields; every exception becomes `ValueError`. -/
def timeFromIsoPy (s : List Char) : Py TimeV :=
  let s := match s with
    | 'T' :: r => r
    | r => r
  match (do
      let (t, _, _) ← parseIsoTimePy s
      let _ ← checkTime t.h t.mi t.s t.us
      pure t) with
  | .ok v => .ok v
  | .error _ => .error (.valueError "~Invalid isoformat string")

/-- The `24:00` rollover of `datetime.fromisoformat`, _pydatetime.py:1948-1960. -/
def rolloverPy (y m d : Int) : Int × Int × Int :=
  if 1 ≤ m ∧ m ≤ 12 ∧ d ≤ daysInMonth y m then
    let dim := daysInMonth y m
    let d := d + 1
    if d > dim then
      let m := m + 1
      if m > 12 then (y + 1, 1, 1) else (y, m, 1)
    else (y, m, d)
  else (y, m, d)

/-- `datetime.fromisoformat`, _pydatetime.py:1918-1962. -/
def datetimeFromIsoPy (s : List Char) : Py DateTimeV := do
  if s.length < 7 then throw (.valueError "~Invalid isoformat string")
  let parsed : Py (List Char × (Int × Int × Int)) := do
    let sep ← findSepPy s
    let dc ← parseIsoDatePy (s.take sep)
    return (s.drop (sep + 1), dc)
  let (tstr, (y, m, d)) ← match parsed with
    | .ok v => pure v
    | .error _ => throw (.valueError "~Invalid isoformat string")
  let (t, (y, m, d)) ← if tstr ≠ [] then do
      let (t, becameNextDay, errorFromComponents) ← match parseIsoTimePy tstr with
        | .ok v => pure v
        | .error _ => throw (.valueError "~Invalid isoformat string")
      if errorFromComponents then
        throw (.valueError "minute, second, and microsecond must be 0 when hour is 24")
      pure (t, if becameNextDay then rolloverPy y m d else (y, m, d))
    else pure (⟨0, 0, 0, 0, none⟩, (y, m, d))
  let _ ← checkDate y m d
  let _ ← checkTime t.h t.mi t.s t.us
  return ⟨y, m, d, t⟩

end PyLean.Datetime
