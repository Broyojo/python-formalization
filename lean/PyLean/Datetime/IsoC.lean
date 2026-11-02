import PyLean.Datetime.IsoPy

/-!
The C ISO 8601 parsers of `Modules/_datetimemodule.c` (CPython 3.15.2):
`datetime_date_fromisoformat_impl`, `datetime_time_fromisoformat_impl`,
`datetime_datetime_fromisoformat_impl` and their helpers. The `string: unicode`
conversion of the clinic wrappers is outside this model: arguments are strings here.

The C code works on the UTF-8 encoding of the argument
(`PyUnicode_AsUTF8AndSize`) through `const char *` pointers. A pointer is an
index into the byte list; reading at or past the end yields the terminating NUL
(`byteAt`). The code never reads further than the terminator.

`_sanitize_isoformat_str` only rewrites lone surrogates, which a Lean `String`
cannot contain, so here it reduces to its length check.
-/

namespace PyLean.Datetime

open PyLean

/-- UTF-8 encoding of one code point. -/
def utf8Char (c : Char) : List Nat :=
  let n := c.toNat
  if n < 0x80 then [n]
  else if n < 0x800 then [0xC0 + n / 64, 0x80 + n % 64]
  else if n < 0x10000 then [0xE0 + n / 4096, 0x80 + n / 64 % 64, 0x80 + n % 64]
  else [0xF0 + n / 262144, 0x80 + n / 4096 % 64, 0x80 + n / 64 % 64, 0x80 + n % 64]

/-- `PyUnicode_AsUTF8AndSize`. -/
def utf8 (s : List Char) : List Nat := s.flatMap utf8Char

/-- `*p` for `p = b + i`: the NUL terminator at and after the end. -/
def byteAt (b : List Nat) (i : Nat) : Nat := b.getD i 0

/-- `is_digit`, :923-925 (`char` arithmetic; bytes `>= 0x80` are not digits). -/
def isDigitC (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- `parse_digits`, :928-940, with the target initialised to 0 by every
caller: the value and the new pointer, or `none` (`NULL`). -/
def parseDigitsC (b : List Nat) (p : Nat) : Nat → Option (Nat × Nat)
  | 0 => some (0, p)
  | n + 1 =>
    let c := byteAt b p
    if isDigitC c then
      match parseDigitsC b (p + 1) n with
      | some (v, q) => some ((c - 48) * 10 ^ n + v, q)
      | none => none
    else none

/-- `parse_isoformat_date`, :943-1012: the date fields or the negative return
code. `len` is a `size_t`. -/
def parseIsoDateC (b : List Nat) (len : Nat) : Except Int (Int × Int × Int) :=
  match parseDigitsC b 0 4 with
  | none => .error (-1)
  | some (year, p) =>
    let usesSep := byteAt b p = 45  -- '-'
    let p := if usesSep then p + 1 else p
    if byteAt b p = 87 then  -- 'W'
      match parseDigitsC b (p + 1) 2 with
      | none => .error (-3)
      | some (week, p) =>
        let day : Except Int Int :=
          if p < len then
            if usesSep ∧ byteAt b p ≠ 45 then .error (-2)
            else match parseDigitsC b (if usesSep then p + 1 else p) 1 with
              | none => .error (-4)
              | some (d, _) => .ok d
          else .ok 1
        match day with
        | .error e => .error e
        | .ok day =>
          match isoToYmdC year week day with
          | .error rv => .error (-3 + rv)
          | .ok ymd => .ok ymd
    else
      match parseDigitsC b p 2 with
      | none => .error (-1)
      | some (month, p) =>
        if usesSep ∧ byteAt b p ≠ 45 then .error (-2)
        else match parseDigitsC b (if usesSep then p + 1 else p) 2 with
          | none => .error (-1)
          | some (day, _) => .ok (year, month, day)

/-- Out-parameters and return code of `parse_hh_mm_ss_ff`. -/
structure HHRes where
  h : Int := 0
  mi : Int := 0
  s : Int := 0
  us : Int := 0
  rv : Int
  deriving Repr, DecidableEq, Inhabited

/-- `correction[i]` in `parse_hh_mm_ss_ff`, :1075-1077. -/
def correctionC (i : Nat) : Int := [100000, 10000, 1000, 100, 10].getD i 0

/-- The fractional part of `parse_hh_mm_ss_ff`, :1063-1088, from `p < pEnd`. -/
def fractionC (b : List Nat) (p pEnd : Nat) (h mi s : Int) : HHRes :=
  let lenRemains := pEnd - p
  let toParse := if lenRemains ≥ 6 then 6 else lenRemains
  match parseDigitsC b p toParse with
  | none => { h, mi, s, rv := -3 }
  | some (us, p) =>
    let us : Int := if toParse < 6 then us * correctionC (toParse - 1) else us
    -- `while (is_digit(*p)) ++p;`
    let p := p + ((b.drop p).takeWhile isDigitC).length
    { h, mi, s, us, rv := if byteAt b p ≠ 0 then 1 else 0 }

/-- What one iteration of the `[HH[:?MM[:?SS]]]` loop does. -/
inductive HHStep where
  | ret (rv : Int)
  | next (p : Nat) (hasSep : Bool)
  | frac (p : Nat)

/-- Iteration `i` of the loop in `parse_hh_mm_ss_ff`, :1026-1061, after the
two digits were read into `v`. -/
def hhStep (b : List Nat) (pEnd i p : Nat) (hasSep : Bool) : HHStep :=
  let c := byteAt b p
  let p := p + 1
  let hasSep := if i = 0 then decide (c = 58) else hasSep  -- ':'
  if c = 46 ∨ c = 44 then  -- '.' or ','
    if i < 2 then .ret (-3)
    else if p ≥ pEnd then .ret (-3)
    else .frac p
  else if p ≥ pEnd then .ret (if c ≠ 0 then 1 else 0)
  else if hasSep ∧ c = 58 then
    if i = 2 then .ret (-4) else .next p hasSep
  else if !hasSep then
    if i = 2 then .frac (p - 1) else .next (p - 1) hasSep
  else .ret (-4)

/-- `parse_hh_mm_ss_ff`, :1015-1089, on the bytes `[p, pEnd)` of `b`. The loop
over `i = 0, 1, 2` is unrolled; when it ends without returning, the fraction
is parsed. -/
def parseHHMMSSFFC (b : List Nat) (p pEnd : Nat) : HHRes :=
  match parseDigitsC b p 2 with
  | none => { rv := -3 }
  | some (h, p) =>
    match hhStep b pEnd 0 p true with
    | .ret rv => { h, rv }
    | .frac p => fractionC b p pEnd h 0 0
    | .next p hasSep =>
      match parseDigitsC b p 2 with
      | none => { h, rv := -3 }
      | some (mi, p) =>
        match hhStep b pEnd 1 p hasSep with
        | .ret rv => { h, mi, rv }
        | .frac p => fractionC b p pEnd h mi 0
        | .next p hasSep =>
          match parseDigitsC b p 2 with
          | none => { h, mi, rv := -3 }
          | some (s, p) =>
            match hhStep b pEnd 2 p hasSep with
            | .ret rv => { h, mi, s, rv }
            | .frac p | .next p _ => fractionC b p pEnd h mi s

/-- Out-parameters and return code of `parse_isoformat_time`. -/
structure TimeRes where
  h : Int
  mi : Int
  s : Int
  us : Int
  tzoffset : Int
  tzus : Int
  rv : Int
  /-- The exception `check_time_args` set; present exactly when `rv` is `-6`. -/
  err : Option PyExc
  deriving Repr, DecidableEq, Inhabited

def isTzDesignator (c : Nat) : Bool := c = 90 || c = 43 || c = 45  -- 'Z' '+' '-'

/-- The `do { ... } while (++tzinfo_pos < p_end)` scan of
`parse_isoformat_time` (:1109-1114): the first designator at or after `p`
(`p` itself is always inspected), else where the loop stops. -/
def tzScan (b : List Nat) (p pEnd : Nat) : Nat :=
  match ((b.drop p).take (max 1 (pEnd - p))).findIdx? isTzDesignator with
  | some i => p + i
  | none => max (p + 1) pEnd

/-- `parse_isoformat_time`, :1092-1160, on `dtlen` bytes from `p`. The range check runs
even when the offset failed to parse (`r2.rv < 0`), so `+99x` raises the hour's message,
not `Invalid isoformat string`. A field `parse_digits` left half-read is one digit, or at
most six fraction digits, hence in range: the zeros of `HHRes` do not change this check. -/
def parseIsoTimeC (b : List Nat) (p dtlen : Nat) : TimeRes :=
  let pEnd := p + dtlen
  let tzPos := tzScan b p pEnd
  let r := parseHHMMSSFFC b p tzPos
  let base : TimeRes := ⟨r.h, r.mi, r.s, r.us, 0, 0, 0, none⟩
  if r.rv < 0 then { base with rv := r.rv }
  else if tzPos = pEnd then { base with rv := if r.rv = 1 then -5 else 0 }
  else if byteAt b tzPos = 90 then  -- 'Z'
    { base with rv := if byteAt b (tzPos + 1) ≠ 0 then -5 else 1 }
  else
    let tzsign : Int := if byteAt b tzPos = 45 then -1 else 1
    let r2 := parseHHMMSSFFC b (tzPos + 1) pEnd
    match checkTime r2.h r2.mi r2.s r2.us with
    | .error e => { base with rv := -6, err := some e }
    | .ok _ =>
      { base with tzoffset := tzsign * (r2.h * 3600 + r2.mi * 60 + r2.s), tzus := r2.us * tzsign,
                  rv := if r2.rv ≠ 0 then -5 else 1 }

/-- `new_timezone(delta, NULL)`, :1459-1479, as an offset in microseconds. -/
def newTimezoneC (off : Delta) : Py Int :=
  if off.toUs = 0 then .ok 0
  else if (off.days = -1 ∧ off.seconds = 0 ∧ off.us < 1) ∨ off.days < -1 ∨ off.days ≥ 1 then
    .error (.valueError "~offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24)")
  else .ok off.toUs

/-- `tzinfo_from_isoformat_results`, :1672-1693. -/
def tzinfoFromIsoResults (rv tzoffset tzus : Int) : Py (Option Int) :=
  if rv = 1 then
    if tzoffset = 0 ∧ tzus = 0 then .ok (some 0)
    else do some <$> newTimezoneC (← newDeltaNormC 0 tzoffset tzus)
  else .ok none

/-! ### `fromisoformat` -/

/-- `date.fromisoformat`, `datetime_date_fromisoformat_impl`, :3432-3461. -/
def dateFromIsoC (s : List Char) : Py (Int × Int × Int) :=
  let b := utf8 s
  let len := b.length
  let rv := if len = 7 ∨ len = 8 ∨ len = 10 then parseIsoDateC b len else .error (-1)
  match rv with
  | .error _ => .error (.valueError "~Invalid isoformat string")
  | .ok (y, m, d) => checkDate y m d

/-- `rv < 0` after `parse_isoformat_time`: `-6` keeps the exception `check_time_args` set
(`goto error`, :5216-5218 and :6141-6143), anything else is `invalid_string_error`. -/
def timeResError (r : TimeRes) : PyExc :=
  match r.err with
  | some e => e
  | none => .valueError "~Invalid isoformat string"

/-- `time.fromisoformat`, `datetime_time_fromisoformat_impl`, :5191-5258. -/
def timeFromIsoC (s : List Char) : Py TimeV := do
  let b := utf8 s
  let (p, len) := if byteAt b 0 = 84 then (1, b.length - 1) else (0, b.length)  -- 'T'
  let r := parseIsoTimeC b p len
  if r.rv < 0 then throw (timeResError r)
  let hour ← if r.h = 24 then
      if r.mi = 0 ∧ r.s = 0 ∧ r.us = 0 then pure 0
      else throw (.valueError "minute, second, and microsecond must be 0 when hour is 24")
    else pure r.h
  let tz ← tzinfoFromIsoResults r.rv r.tzoffset r.tzus
  let _ ← checkTime hour r.mi r.s r.us
  return ⟨hour, r.mi, r.s, r.us, tz⟩

/-- `_find_isoformat_datetime_separator`, :5970-6066 (on bytes; `-1` is an
error). Its caller only uses it for strings of at least 7 code points. -/
def findSepC (b : List Nat) : Int :=
  let len := b.length
  if len = 7 then 7
  else if byteAt b 4 = 45 then
    if byteAt b 5 = 87 then
      if len < 8 then -1
      else if len > 8 ∧ byteAt b 8 = 45 then
        if len = 9 then -1
        else if len > 10 ∧ isDigitC (byteAt b 10) then 8
        else 10
      else 8
    else 10
  else if byteAt b 4 = 87 then
    let idx := 7 + (((b.drop 7).take (len - 7)).takeWhile isDigitC).length
    if idx < 9 then idx
    else if idx % 2 = 0 then 7 else 8
  else 8

/-- Bytes taken by the UTF-8 character whose lead byte is `c`, as the
separator skip in `datetime_datetime_fromisoformat_impl` (:6119-6136) computes it. -/
def utf8SkipC (c : Nat) : Nat :=
  if c % 256 < 0x80 then 1
  else if c % 256 / 16 = 0xe then 3
  else if c % 256 / 16 = 0xf then 4
  else 2

/-- `datetime.fromisoformat`, `datetime_datetime_fromisoformat_impl`, :6079-6194. -/
def datetimeFromIsoC (s : List Char) : Py DateTimeV := do
  if s.length < 7 then throw (.valueError "~Invalid isoformat string")
  let b := utf8 s
  let len : Int := b.length
  let sepLoc := findSepC b
  -- `parse_isoformat_date(p, separator_location, ...)`: a `size_t` length
  let dlen : Nat := if sepLoc < 0 then 2 ^ 64 - 1 else sepLoc.toNat
  let date := parseIsoDateC b dlen
  let (ymd, r) ← match date with
    | .error _ => throw (.valueError "~Invalid isoformat string")
    | .ok ymd =>
      if len > sepLoc then
        let p := sepLoc.toNat + utf8SkipC (byteAt b sepLoc.toNat)
        pure (ymd, parseIsoTimeC b p (len - p).toNat)
      else pure (ymd, (⟨0, 0, 0, 0, 0, 0, 0, none⟩ : TimeRes))
  if r.rv < 0 then throw (timeResError r)
  let tz ← tzinfoFromIsoResults r.rv r.tzoffset r.tzus
  let (y, m, d) := ymd
  let (y, m, d, hour) ← if r.h = 24 ∧ 1 ≤ m ∧ m ≤ 12 then
      let dim := daysInMonth y m
      if d ≤ dim then
        if r.mi = 0 ∧ r.s = 0 ∧ r.us = 0 then
          let d := d + 1
          if d > dim then
            let m := m + 1
            if m > 12 then pure (y + 1, 1, 1, 0) else pure (y, m, 1, 0)
          else pure (y, m, d, 0)
        else throw (.valueError "minute, second, and microsecond must be 0 when hour is 24")
      else pure (y, m, d, r.h)
    else pure (y, m, d, r.h)
  let _ ← checkDate y m d
  let _ ← checkTime hour r.mi r.s r.us
  return ⟨y, m, d, ⟨hour, r.mi, r.s, r.us, tz⟩⟩

end PyLean.Datetime
