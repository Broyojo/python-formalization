import PyLean.Datetime.Objects

/-!
`Lib/_strptime.py` (CPython 3.14.7): the format-to-regex translation of `TimeRE`,
and `_strptime` after the regex match.

The `re` engine and the C library's locale are other files' business, so two things
are parameters: `LocaleTimeV` holds what `LocaleTime` computed from the locale, and
`_strptime` takes `found.groupdict()` (group names in pattern order, with their
text). Everything between those two points is mirrored.
-/

namespace PyLean.Datetime

open PyLean

/-- The attributes of `LocaleTime`, _strptime.py:62-337, as far as `TimeRE` and
`_strptime` read them. `timezone` is two lists, each iterated in set order. -/
structure LocaleTimeV where
  fWeekday : List String
  aWeekday : List String
  fMonth : List String
  aMonth : List String
  amPm : List String
  timezone : List (List String)
  lcDateTime : String
  lcDate : String
  lcTime : String
  lcTimeAmpm : String
  /-- `locale_time.LC_alt_digits`. -/
  altDigits : Option (List String)
  /-- `time.tzname[0] == time.tzname[1] and time.daylight`. -/
  ambiguousTz : Bool
  deriving Repr, Inhabited

/-- `str.lower()` for the ASCII text the C locale produces. -/
def lowerAscii (s : String) : String := String.ofList (s.toList.map Char.toLower)

/-- `re.escape(s)`: the special characters of `re._special_chars_map`. -/
def reEscape (s : String) : String :=
  let special := "()[]{}?*+-|^$\\.&~# \t\n\r\x0b\x0c".toList
  String.ofList (s.toList.flatMap fun c => if special.contains c then ['\\', c] else [c])

/-- Insert after every element at least as long, keeping the sort stable. -/
def insertByLen (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if y.length ≥ x.length then y :: insertByLen x ys else x :: y :: ys

/-- `sorted(xs, key=len, reverse=True)`: stable, longest first. -/
def sortByLenDesc (xs : List String) : List String :=
  xs.foldl (fun acc x => insertByLen x acc) []

/-- `TimeRE.__seqToRE`, _strptime.py:433-451. -/
def seqToRE (toConvert : List String) (directive : String) (altregex : Option String := none) : String :=
  let sorted := sortByLenDesc toConvert
  if sorted.all (· == "") then ""
  else
    let regex := "|".intercalate (sorted.map reEscape)
    let regex := match altregex with
      | some a => regex ++ "|" ++ a
      | none => regex
    s!"(?P<{directive}>{regex})"

/-- `_fixmonths(months)`, _strptime.py:45-52 (`'i̇'` to `'İ'`). -/
def fixMonths (months : List String) : List String :=
  months ++ (months.filter (fun s => (s.splitOn "i̇").length > 1)).map
    (fun s => "İ".intercalate (s.splitOn "i̇"))

/-- `_findall(haystack, needle)`, _strptime.py:33-43, as a list; `fuel` bounds the
loop, each round moving past one match. -/
def findallFrom (needle : List Char) : Nat → Nat → List Char → List Nat
  | 0, _, _ => []
  | fuel + 1, i, hay =>
    if hay.length < needle.length then []
    else if needle.isPrefixOf hay then i :: findallFrom needle fuel (i + needle.length) (hay.drop needle.length)
    else findallFrom needle fuel (i + 1) (hay.drop 1)

def findall (haystack needle : List Char) : List Nat :=
  if needle.isEmpty then [] else findallFrom needle (haystack.length + 1) 0 haystack

/-! ### `TimeRE` -/

/-- Characters that `\s` matches in a `str` pattern. -/
def isReSpace (c : Char) : Bool :=
  c = ' ' || (9 ≤ c.toNat && c.toNat ≤ 13) || (28 ≤ c.toNat && c.toNat ≤ 31) ||
    unicodeSpaces.contains c.toNat

/-- `re_sub(r"([\\.^$*+?\(\){}\[\]|])", r"\\\1", format)`, _strptime.py:461. -/
def escapeFormat (s : List Char) : List Char :=
  s.flatMap fun c => if "\\.^$*+?(){}[]|".toList.contains c then ['\\', c] else [c]

/-- `re_sub(r'\s+', r'\\s+', format)`, _strptime.py:462; `fuel` is the length. -/
def spaceFormatF : Nat → List Char → List Char
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, c :: cs =>
    if isReSpace c then "\\s+".toList ++ spaceFormatF fuel (cs.dropWhile isReSpace)
    else c :: spaceFormatF fuel cs

def spaceFormat (s : List Char) : List Char := spaceFormatF s.length s

/-- `re_sub(r"'", "['ʼ]", format)`, _strptime.py:463. -/
def quoteFormat (s : List Char) : List Char :=
  s.flatMap fun c => if c = '\'' then "['ʼ]".toList else [c]

/-- The match of `%[-_0^#]*[0-9]*([OE]?\\?.?)` after the `%`: group 1 and the rest. -/
def directiveAt (s : List Char) : List Char × List Char :=
  let s := s.dropWhile (fun c => "-_0^#".toList.contains c)
  let s := s.dropWhile (fun c => '0' ≤ c && c ≤ '9')
  let (a, s) := match s with
    | c :: r => if c = 'O' ∨ c = 'E' then ([c], r) else ([], s)
    | [] => ([], s)
  let (b, s) := match s with
    | '\\' :: r => (['\\'], r)
    | _ => ([], s)
  let (d, s) := match s with
    | c :: r => if c ≠ '\n' then ([c], r) else ([], s)
    | [] => ([], [])
  (a ++ b ++ d, s)

/-- The directive scan of `TimeRE.pattern`, _strptime.py@3.14.7:470: `re_sub` with `repl`.
A key missing from the mapping is the `KeyError` of `self[format_char]`. `fuel` is the
length of the string. -/
def replaceDirectives (map : String → Option String) : Nat → List Char → Except String (List Char)
  | 0, _ => .ok []
  | fuel + 1, s =>
    match s with
    | [] => .ok []
    | '%' :: r =>
      let (key, rest) := directiveAt r
      let k := String.ofList key
      match map k with
      | some v => do return v.toList ++ (← replaceDirectives map fuel rest)
      | none => .error k
    | c :: r => do return c :: (← replaceDirectives map fuel r)

/-- `TimeRE.pattern(format)`, _strptime.py:453-500, without the `DeprecationWarning`
for a day of month with no year. `Except` carries the `KeyError` argument. -/
def timeREPattern (map : String → Option String) (format : String) : Except String String := do
  let s := quoteFormat (spaceFormat (escapeFormat format.toList))
  return String.ofList (← replaceDirectives map s.length s)

/-- `s.replace(a, b)` on strings. -/
def strReplace (s a b : String) : String := b.intercalate (s.splitOn a)

/-- The `mapping` of `TimeRE.__init__`, _strptime.py:351-422, before `T`, `R`, `r`,
`X`, `x`, `c`. -/
def timeREBase (lt : LocaleTimeV) : List (String × String) :=
  let digit0 := "(?P<U>5[0-3]|[0-4]\\d|\\d)"
  let d := "(?P<d>3[0-1]|[1-2]\\d|0[1-9]|[1-9]| [1-9])"
  let p := seqToRE lt.amPm "p"
  let core : List (String × String) := [
    ("d", d),
    ("f", "(?P<f>[0-9]{1,6})"),
    ("H", "(?P<H>2[0-3]|[0-1]\\d|\\d| \\d)"),
    ("k", "(?P<H>2[0-3]|[0-1]\\d|\\d| \\d)"),
    ("I", "(?P<I>1[0-2]|0[1-9]|[1-9]| [1-9])"),
    ("l", "(?P<I>1[0-2]|0[1-9]|[1-9]| [1-9])"),
    ("G", "(?P<G>\\d\\d\\d\\d)"),
    ("j", "(?P<j>36[0-6]|3[0-5]\\d|[1-2]\\d\\d|0[1-9]\\d|00[1-9]|[1-9]\\d|0[1-9]|[1-9])"),
    ("m", "(?P<m>1[0-2]|0[1-9]|[1-9])"),
    ("M", "(?P<M>[0-5]\\d|\\d)"),
    ("S", "(?P<S>6[0-1]|[0-5]\\d|\\d)"),
    ("U", digit0),
    ("w", "(?P<w>[0-6])"),
    ("u", "(?P<u>[1-7])"),
    ("V", "(?P<V>5[0-3]|0[1-9]|[1-4]\\d|\\d)"),
    ("y", "(?P<y>\\d\\d)"),
    ("Y", "(?P<Y>\\d\\d\\d\\d)"),
    ("z", "(?P<z>[+-]\\d\\d:?[0-5]\\d(:?[0-5]\\d(\\.\\d{1,6})?)?|(?-i:Z))"),
    ("A", seqToRE lt.fWeekday "A"),
    ("a", seqToRE lt.aWeekday "a"),
    ("B", seqToRE (fixMonths (lt.fMonth.drop 1)) "B"),
    ("b", seqToRE (fixMonths (lt.aMonth.drop 1)) "b"),
    ("p", p),
    ("Z", seqToRE lt.timezone.flatten "Z"),
    ("%", "%")]
  let alt : List (String × String) := match lt.altDigits with
    | none =>
      "dmyCHIMS".toList.map (fun c => (String.ofList ['O', c], s!"(?P<{c}>\\d\\d|\\d| \\d)")) ++
        [("Ow", "(?P<w>\\d)")]
    | some ds => [
      ("Od", seqToRE ((ds.drop 1).take 31) "d" (some "3[0-1]|[1-2][0-9]|0[1-9]|[1-9]")),
      ("Om", seqToRE ((ds.drop 1).take 12) "m" (some "1[0-2]|0[1-9]|[1-9]")),
      ("Ow", seqToRE (ds.take 7) "w" (some "[0-6]")),
      ("Oy", seqToRE ds "y" (some "[0-9][0-9]")),
      ("OC", seqToRE ds "C" (some "[0-9][0-9]")),
      ("OH", seqToRE (ds.take 24) "H" (some "2[0-3]|[0-1][0-9]|[0-9]")),
      ("OI", seqToRE ((ds.drop 1).take 12) "I" (some "1[0-2]|0[1-9]|[1-9]")),
      ("OM", seqToRE (ds.take 60) "M" (some "[0-5][0-9]|[0-9]")),
      ("OS", seqToRE (ds.take 62) "S" (some "6[0-1]|[0-5][0-9]|[0-9]"))]
  let od := (alt.lookup "Od").getD ""
  core ++ alt ++ [("e", d), ("Oe", od), ("P", p), ("Op", p), ("W", strReplace digit0 "U" "W")]

/-- The full `TimeRE` mapping: `base.__setitem__` calls of `__init__`, :426-431. -/
def timeREMap (lt : LocaleTimeV) : Except String (List (String × String)) := do
  let add (m : List (String × String)) (k fmt : String) : Except String (List (String × String)) := do
    return (k, ← timeREPattern (fun k => List.lookup k m) fmt) :: m
  let m := timeREBase lt
  let m ← add m "T" "%H:%M:%S"
  let m ← add m "R" "%H:%M"
  let m ← add m "r" lt.lcTimeAmpm
  let m ← add m "X" lt.lcTime
  let m ← add m "x" lt.lcDate
  add m "c" lt.lcDateTime

/-- The `KeyError` handler of `_strptime`, _strptime.py:560-569. -/
def badDirectiveError (bad format : String) : PyExc :=
  let bad := strReplace bad "\\s" ""
  if bad.isEmpty then .valueError s!"stray % in format '{format}'"
  else
    -- `bad_directive.replace('\\', '', 1)`
    let bad := match bad.toList.span (· ≠ '\\') with
      | (before, _ :: after) => String.ofList (before ++ after)
      | (before, []) => String.ofList before
    .valueError s!"'{bad}' is a bad directive in format '{format}'"

/-- `TimeRE.compile`, _strptime.py:502-504, with the `except KeyError` of `_strptime`,
up to the regex compilation: the pattern string or the `ValueError`. -/
def strptimeCompile (lt : LocaleTimeV) (format : String) : Py String :=
  match timeREMap lt with
  | .error k => .error (.named "KeyError" k)
  | .ok m =>
    match timeREPattern (fun k => List.lookup k m) format with
    | .ok p => .ok p
    | .error bad => .error (badDirectiveError bad format)

/-! ### `_strptime` after the match -/

/-- `_calc_julian_from_U_or_W`, _strptime.py:513-531. -/
def calcJulianFromUorW (year weekOfYear dayOfWeek : Int) (weekStartsMon : Bool) : Py Int := do
  let _ ← checkDate year 1 1
  let firstWeekday := dateWeekdayC year 1 1
  let (firstWeekday, dayOfWeek) := if !weekStartsMon then ((firstWeekday + 1) % 7, (dayOfWeek + 1) % 7)
    else (firstWeekday, dayOfWeek)
  let week0Length := (7 - firstWeekday) % 7
  if weekOfYear = 0 then return 1 + dayOfWeek - firstWeekday
  else
    let daysToWeek := week0Length + 7 * (weekOfYear - 1)
    return 1 + daysToWeek + dayOfWeek

/-- The local variables of `_strptime`, :576-599. -/
structure StrpState where
  isoYear : Option Int := none
  year : Option Int := none
  month : Int := 1
  day : Int := 1
  hour : Int := 0
  minute : Int := 0
  second : Int := 0
  fraction : Int := 0
  tz : Int := -1
  gmtoff : Option Int := none
  gmtoffFraction : Int := 0
  isoWeek : Option Int := none
  weekOfYear : Option Int := none
  weekOfYearStart : Option Int := none
  weekday : Option Int := none
  julian : Option Int := none
  deriving Repr, Inhabited

/-- `list.index(x)`. -/
def listIndex (xs : List String) (x : String) : Py Int :=
  match xs.findIdx? (· == x) with
  | some i => .ok i
  | none => .error (.valueError "~is not in list")

/-- `parse_int`, _strptime.py:602-609. -/
def parseIntLt (lt : LocaleTimeV) (s : String) : Py Int :=
  match lt.altDigits with
  | some ds =>
    if ds.isEmpty then pyInt s.toList
    else match ds.findIdx? (· == s) with
      | some i => .ok i
      | none => pyInt s.toList
  | none => pyInt s.toList

/-- The `%z` branch, _strptime.py@3.14.7:666-686: `gmtoff` and `gmtoff_fraction`. -/
def parseZ (found : String) : Py (Int × Option Int) := do
  let z0 := found.toList
  if z0 = ['Z'] then return (0, some 0)
  let z ← if z0.getD 3 ' ' = ':' then do
      let z := z0.take 3 ++ z0.drop 4
      if z.length > 5 then
        if z.getD 5 ' ' ≠ ':' then throw (.valueError s!"Inconsistent use of : in {found}")
        pure (z.take 5 ++ z.drop 6)
      else pure z
    else pure z0
  let hours ← pyInt (slice z 1 3)
  let minutes ← pyInt (slice z 3 5)
  let seconds ← if slice z 5 7 = [] then pure 0 else pyInt (slice z 5 7)
  let gmtoff := hours * 60 * 60 + minutes * 60 + seconds
  let rem := z.drop 8
  let frac ← pyInt (rem ++ List.replicate (6 - rem.length) '0')
  if z.head? = some '-' then return (-frac, some (-gmtoff))
  return (frac, some gmtoff)

/-- One round of `for group_key in found_dict.keys()`, _strptime.py:611-733. -/
def strpStep (lt : LocaleTimeV) (found : List (String × String)) (st : StrpState) (key : String) :
    Py StrpState := do
  let v := (found.lookup key).getD ""
  match key with
  | "y" =>
    let year ← parseIntLt lt v
    match found.lookup "C" with
    | some c =>
      let century ← parseIntLt lt c
      return { st with year := some (year + century * 100) }
    | none => return { st with year := some (if year ≤ 68 then year + 2000 else year + 1900) }
  | "Y" => return { st with year := some (← pyInt v.toList) }
  | "G" => return { st with isoYear := some (← pyInt v.toList) }
  | "m" => return { st with month := ← parseIntLt lt v }
  | "B" => return { st with month := ← listIndex lt.fMonth (lowerAscii v) }
  | "b" => return { st with month := ← listIndex lt.aMonth (lowerAscii v) }
  | "d" => return { st with day := ← parseIntLt lt v }
  | "H" => return { st with hour := ← parseIntLt lt v }
  | "I" =>
    let hour ← parseIntLt lt v
    let ampm := lowerAscii ((found.lookup "p").getD "")
    if ampm == "" ∨ some ampm == lt.amPm.head? then
      return { st with hour := if hour = 12 then 0 else hour }
    else if some ampm == lt.amPm[1]? then
      return { st with hour := if hour ≠ 12 then hour + 12 else hour }
    else return { st with hour := hour }
  | "M" => return { st with minute := ← parseIntLt lt v }
  | "S" => return { st with second := ← parseIntLt lt v }
  | "f" =>
    let s := v.toList ++ List.replicate (6 - v.length) '0'
    return { st with fraction := ← pyInt s }
  | "A" => return { st with weekday := some (← listIndex lt.fWeekday (lowerAscii v)) }
  | "a" => return { st with weekday := some (← listIndex lt.aWeekday (lowerAscii v)) }
  | "w" =>
    let w ← pyInt v.toList
    return { st with weekday := some (if w = 0 then 6 else w - 1) }
  | "u" =>
    let w ← pyInt v.toList
    return { st with weekday := some (w - 1) }
  | "j" => return { st with julian := some (← pyInt v.toList) }
  | "U" => return { st with weekOfYear := some (← pyInt v.toList), weekOfYearStart := some 6 }
  | "W" => return { st with weekOfYear := some (← pyInt v.toList), weekOfYearStart := some 0 }
  | "V" => return { st with isoWeek := some (← pyInt v.toList) }
  | "z" =>
    let (frac, off) ← parseZ v
    return { st with gmtoff := off, gmtoffFraction := if v == "Z" then st.gmtoffFraction else frac }
  | "Z" =>
    let z := lowerAscii v
    let rec go : Nat → List (List String) → Option Int
      | _, [] => none
      | i, vs :: rest =>
        if vs.contains z then
          if lt.ambiguousTz ∧ z ≠ "utc" ∧ z ≠ "gmt" then none else some i
        else go (i + 1) rest
    return { st with tz := (go 0 lt.timezone).getD st.tz }
  | _ => return st

/-- The result of `_strptime`: the eleven-item tuple, `fraction`, `gmtoff_fraction`. -/
structure StrpResult where
  year : Int
  month : Int
  day : Int
  hour : Int
  minute : Int
  second : Int
  weekday : Int
  julian : Int
  tz : Int
  tzname : Option String
  gmtoff : Option Int
  fraction : Int
  gmtoffFraction : Int
  deriving Repr, DecidableEq, Inhabited

/-- `datetime_date(y, m, d)` as `_strptime` uses it. -/
def dateC (y m d : Int) : Py (Int × Int × Int) := checkDate y m d

/-- `_strptime`, _strptime.py:534-807, from `found.groupdict()` on. -/
def strptimeCore (lt : LocaleTimeV) (found : List (String × String)) : Py StrpResult := do
  let st ← (found.map (·.1)).foldlM (strpStep lt found) ({} : StrpState)
  -- :735-753
  if st.isoYear.isSome then
    if st.julian.isSome then
      throw (.valueError "Day of the year directive '%j' is not compatible with ISO year directive '%G'. Use '%Y' instead.")
    else if st.isoWeek.isNone ∨ st.weekday.isNone then
      throw (.valueError "ISO year directive '%G' must be used with the ISO week directive '%V' and a weekday directive ('%A', '%a', '%w', or '%u').")
  else if st.isoWeek.isSome then
    if st.year.isNone ∨ st.weekday.isNone then
      throw (.valueError "ISO week directive '%V' must be used with the ISO year directive '%G' and a weekday directive ('%A', '%a', '%w', or '%u').")
    else
      throw (.valueError "ISO week directive '%V' is incompatible with the year directive '%Y'. Use the ISO year '%G' instead.")
  -- :755-760
  let (year, leapYearFix) : Int × Bool := match st.year with
    | some y => (y, false)
    | none => if st.month = 2 ∧ st.day = 29 then (1904, true) else (1900, false)
  let (year, month, day) := (year, st.month, st.day)
  -- :764-777
  let (year, month, day, julian) ← match st.julian, st.weekday with
    | none, some weekday =>
      let (year, month, day, julian) ← match st.weekOfYear, st.isoYear, st.isoWeek with
        | some w, _, _ => do
          let j ← calcJulianFromUorW year w weekday (st.weekOfYearStart == some 0)
          pure (year, month, day, some j)
        | none, some iy, some iw => do
          let (y, m, d) ← fromisocalendarC iy iw (weekday + 1)
          pure (y, m, d, none)
        | _, _, _ => pure (year, month, day, none)
      match julian with
      | some j =>
        if j ≤ 0 then
          let year := year - 1
          let yday := if isLeap year then 366 else 365
          pure (year, month, day, some (j + yday))
        else pure (year, month, day, some j)
      | none => pure (year, month, day, none)
    | j, _ => pure (year, month, day, j)
  -- :779-791
  let (year, month, day, julian) ← match julian with
    | none => do
      let _ ← dateC year month day
      let _ ← dateC year 1 1
      pure (year, month, day, ymdToOrdC year month day - ymdToOrdC year 1 1 + 1)
    | some j => do
      let _ ← dateC year 1 1
      let (y, m, d) ← fromordinalC ((j - 1) + ymdToOrdC year 1 1)
      pure (y, m, d, j)
  -- :792-793
  let weekday ← match st.weekday with
    | some w => pure w
    | none => do
      let _ ← dateC year month day
      pure (dateWeekdayC year month day)
  let tzname := found.lookup "Z"
  let year := if leapYearFix then 1900 else year
  return ⟨year, month, day, st.hour, st.minute, st.second, weekday, julian, st.tz, tzname, st.gmtoff,
    st.fraction, st.gmtoffFraction⟩

/-- `_strptime_time`, _strptime.py:809-813: the eleven items of the `struct_time`. -/
def strptimeTime (lt : LocaleTimeV) (found : List (String × String)) : Py StrpResult :=
  strptimeCore lt found

/-- `_strptime_datetime_date`, _strptime.py:815-820. -/
def strptimeDate (lt : LocaleTimeV) (found : List (String × String)) : Py (Int × Int × Int) := do
  let r ← strptimeCore lt found
  checkDate r.year r.month r.day

/-- `_parse_tz`, _strptime.py:822-827: a `timezone`, as its offset and name. -/
def parseTz (tzname : Option String) (gmtoff gmtoffFraction : Int) : Py Tz := do
  let tzdelta ← deltaPy 0 gmtoff gmtoffFraction 0 0 0 0
  let named := tzname.filter (· ≠ "")
  if tzdelta.toUs = 0 ∧ named.isNone then return tzUTC
  let _ ← timezonePy tzdelta
  return ⟨1, .timezone tzdelta named⟩

/-- `_strptime_datetime_time`, _strptime.py:829-839. -/
def strptimeDatetimeTime (lt : LocaleTimeV) (found : List (String × String)) : Py TM := do
  let r ← strptimeCore lt found
  match r.gmtoff with
  | none => newTM ⟨r.hour, r.minute, r.second, r.fraction, 0, none⟩
  | some g =>
    let tz ← parseTz r.tzname g r.gmtoffFraction
    newTM ⟨r.hour, r.minute, r.second, r.fraction, 0, some tz⟩

/-- `_strptime_datetime_datetime`, _strptime.py:841-851. -/
def strptimeDatetime (lt : LocaleTimeV) (found : List (String × String)) : Py DT := do
  let r ← strptimeCore lt found
  match r.gmtoff with
  | none => newDT ⟨r.year, r.month, r.day, r.hour, r.minute, r.second, r.fraction, 0, none⟩
  | some g =>
    let tz ← parseTz r.tzname g r.gmtoffFraction
    newDT ⟨r.year, r.month, r.day, r.hour, r.minute, r.second, r.fraction, 0, some tz⟩

end PyLean.Datetime
