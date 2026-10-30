import PyLean.Fractions.Model

/-!
`Fraction(string)`, fractions.py:56-68 (`_RATIONAL_FORMAT`) and :257-287.

The regex is matched by a hand-written scanner that follows the regex's
backtracking to its unique outcome:

* every quantified piece (`\d+(_\d+)*`, `\s*`) is followed by a piece whose
  first character can be neither a digit, an underscore nor whitespace, so
  only the longest match can lead to an overall match;
* the alternation after the numerator tries the `/denominator` branch first,
  then the empty branch, then the `.decimal` / `E` exponent branch.

`\d` is Unicode `Nd` and `\s` is `str.isspace()`. The whitespace table below is
the complete list of `str.isspace()` characters; the digit table covers ASCII
plus four common `Nd` blocks (Arabic-Indic, Extended Arabic-Indic,
Devanagari, Fullwidth), and the differential tester draws digits only from
these.

`int()` on a matched group (fractions.py:263, :266, :273, :277) raises
`ValueError` beyond 4300 digits (Objects/longobject.c:2940-2950).
-/

namespace PyLean.Fractions

open PyLean

/-- The value of a decimal digit character (`\d`), for the modelled blocks. -/
def digitVal (c : Char) : Option Nat :=
  let n := c.toNat
  if 0x30 ≤ n ∧ n ≤ 0x39 then some (n - 0x30)
  else if 0x660 ≤ n ∧ n ≤ 0x669 then some (n - 0x660)
  else if 0x6F0 ≤ n ∧ n ≤ 0x6F9 then some (n - 0x6F0)
  else if 0x966 ≤ n ∧ n ≤ 0x96F then some (n - 0x966)
  else if 0xFF10 ≤ n ∧ n ≤ 0xFF19 then some (n - 0xFF10)
  else none

def isDigit (c : Char) : Bool := (digitVal c).isSome

/-- `str.isspace()` (`\s` in a `str` pattern), Objects/unicodetype_db.h
`_PyUnicode_IsWhitespace`. -/
def isWs (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0D) || (0x1C ≤ n && n ≤ 0x20) || n == 0x85 || n == 0xA0 ||
  n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 ||
  n == 0x202F || n == 0x205F || n == 0x3000

/-- `\s*` -/
def skipWs : List Char → List Char
  | [] => []
  | c :: cs => if isWs c then skipWs cs else c :: cs

/-- The tail of `\d+(_\d+)*` after its first digit: more digits, or `_`
followed by a digit. Returns the matched part and the rest. -/
def runTail : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if isDigit c then
      let r := runTail cs
      (c :: r.1, r.2)
    else if c = '_' then
      match cs with
      | d :: ds =>
        if isDigit d then
          let r := runTail ds
          ('_' :: d :: r.1, r.2)
        else ([], c :: cs)
      | [] => ([], [c])
    else ([], c :: cs)

/-- Greedy `\d+(_\d+)*`, or the empty match when no digit comes first (which
also covers the `\d*` alternative of the numerator and decimal groups). -/
def digitRun : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if isDigit c then
      let r := runTail cs
      (c :: r.1, r.2)
    else ([], c :: cs)

/-- Matched groups of `_RATIONAL_FORMAT`. `decimal` and `exp` are `none` when
the group did not participate. -/
structure Groups where
  neg : Bool
  num : List Char
  denom : Option (List Char)
  decimal : Option (List Char)
  exp : Option (List Char)
  deriving Repr, DecidableEq

/-- `(?:E(?P<exp>[-+]?\d+(_\d+)*))?` on `cs`: the group and the rest. -/
def expGroup (cs : List Char) : Option (List Char) × List Char :=
  match cs with
  | e :: r =>
    if e = 'e' ∨ e = 'E' then
      let (sgn, r') := match r with
        | '+' :: t => (['+'], t)
        | '-' :: t => (['-'], t)
        | t => ([], t)
      let (ds, rest) := digitRun r'
      if ds = [] then (none, cs) else (some (sgn ++ ds), rest)
    else (none, cs)
  | [] => (none, [])

/-- `[-+]?`: whether the sign is `-`, and the rest. -/
def splitSign : List Char → Bool × List Char
  | '-' :: r => (true, r)
  | '+' :: r => (false, r)
  | r => (false, r)

/-- The lookahead `(?=\d|\.\d)`. -/
def lookahead : List Char → Bool
  | c :: r => isDigit c || (c == '.' && match r with | d :: _ => isDigit d | [] => false)
  | [] => false

/-- `_RATIONAL_FORMAT.match(s)`, fractions.py:56-68. -/
def matchRational (s : List Char) : Option Groups :=
  let s1 := skipWs s
  let (neg, s2) := splitSign s1
  if !lookahead s2 then none
  else
    let (num, s3) := digitRun s2
    -- first branch: `(?:\s*/\s*(?P<denom>\d+(_\d+)*))?` then `\s*\z`
    let slash : Option (List Char) := match skipWs s3 with
      | '/' :: r =>
        let (den, r') := digitRun (skipWs r)
        if den ≠ [] ∧ skipWs r' = [] then some den else none
      | _ => none
    match slash with
    | some den => some ⟨neg, num, some den, none, none⟩
    | none =>
      if skipWs s3 = [] then some ⟨neg, num, none, none, none⟩
      else
        -- second branch: `(?:\.(?P<decimal>...))?(?:E(?P<exp>...))?` then `\s*\z`
        let (dec, s4) : Option (List Char) × List Char := match s3 with
          | '.' :: r => let (ds, r') := digitRun r; (some ds, r')
          | r => (none, r)
        let (ex, s5) := expGroup s4
        if skipWs s5 = [] then some ⟨neg, num, none, dec, ex⟩ else none

/-- `_MAX_STR_DIGITS_ERROR_FMT_TO_INT`, Objects/longobject.c:30. -/
def limitToIntMsg (digits : Nat) : String :=
  s!"Exceeds the limit (4300 digits) for integer string conversion: value has {digits} digits; use sys.set_int_max_str_digits() to increase the limit"

/-- One step of reading a digit string (underscores skipped). -/
def digitStep (acc : Nat) (c : Char) : Nat :=
  match digitVal c with
  | some v => acc * 10 + v
  | none => acc

/-- Value of a digit string (underscores skipped). -/
def digitsValue (cs : List Char) : Nat := cs.foldl digitStep 0

/-- `int(s)` for a string matching `[-+]?\d+(_\d+)*` (or empty → not used). -/
def pyIntOfDigits (cs : List Char) : Py Int :=
  let (neg, body) := splitSign cs
  let ndig := (body.filter isDigit).length
  if ndig > maxStrDigits then .error (.valueError (limitToIntMsg ndig))
  else
    let v : Int := digitsValue body
    .ok (if neg then -v else v)

/-- `Fraction(s)` for a string `s`, fractions.py:257-287 then :302-311. -/
def parse (s : List Char) : Py Frac := do
  let some m := matchRational s
    | throw (.valueError "~Invalid literal for Fraction: <repr>")
  let mut numerator ← pyIntOfDigits (if m.num = [] then ['0'] else m.num)
  let mut denominator : Int := 1
  match m.denom with
  | some den => denominator ← pyIntOfDigits den
  | none =>
    if let some dec := m.decimal then
      if dec ≠ [] then
        let dec := dec.filter (· ≠ '_')
        let scale : Int := 10 ^ dec.length
        numerator := numerator * scale + (← pyIntOfDigits dec)
        denominator := denominator * scale
    if let some ex := m.exp then
      let e ← pyIntOfDigits ex
      if e ≥ 0 then numerator := numerator * 10 ^ e.toNat
      else denominator := denominator * 10 ^ (-e).toNat
  if m.neg then numerator := -numerator
  normalize numerator denominator

end PyLean.Fractions
