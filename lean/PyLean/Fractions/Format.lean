import PyLean.Fractions.Parse

/-!
`Fraction.__str__` (fractions.py:454-459) and `Fraction.__format__`
(fractions.py:461-614), with the two spec regexes (fractions.py:142-179) and
the rounding helpers `_round_to_exponent` / `_round_to_figures`
(fractions.py:73-138).

Strings are `List Char`; Python `len` is `List.length`. Every `str(int)` and
int `__format__` goes through `strInt`, which raises past 4300 digits.
-/

namespace PyLean.Fractions

open PyLean

/-- `str(self)`, fractions.py:454-459. -/
def str (x : Frac) : Py (List Char) := do
  if x.den = 1 then strInt x.num
  else return (← strInt x.num) ++ ['/'] ++ (← strInt x.den)

/-! ## Format spec matching -/

def isAlign (c : Char) : Bool := c == '<' || c == '>' || c == '=' || c == '^'
def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `(?:(?P<fill>.)?(?P<align>[<>=^]))?` -/
def fillAlign : List Char → Option Char × Option Char × List Char
  | f :: a :: r => if isAlign a then (some f, some a, r)
                   else if isAlign f then (none, some f, a :: r) else (none, none, f :: a :: r)
  | [a] => if isAlign a then (none, some a, []) else (none, none, [a])
  | [] => (none, none, [])

/-- `[-+ ]?` -/
def signPart : List Char → List Char × List Char
  | c :: r => if c == '-' || c == '+' || c == ' ' then ([c], r) else ([], c :: r)
  | [] => ([], [])

/-- `x?` for a single character. -/
def optChar (x : Char) : List Char → Bool × List Char
  | c :: r => if c = x then (true, r) else (false, c :: r)
  | [] => (false, [])

/-- `[,_]?` -/
def sepPart : List Char → Option Char × List Char
  | c :: r => if c == ',' || c == '_' then (some c, r) else (none, c :: r)
  | [] => (none, [])

/-- `[0-9]*` (ASCII only: the spec regexes spell digits as `[0-9]`), greedy. -/
def asciiDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: r =>
    if isAsciiDigit c then
      let t := asciiDigits r
      (c :: t.1, t.2)
    else ([], c :: r)

structure GenSpec where
  fill : Option Char
  align : Option Char
  sign : List Char
  alt : Bool
  width : Option (List Char)
  sep : Option Char
  deriving Repr, DecidableEq

/-- `_GENERAL_FORMAT_SPECIFICATION_MATCHER` (a `fullmatch`),
fractions.py:142-155. -/
def matchGeneral (s : List Char) : Option GenSpec :=
  let (fill, align, r1) := fillAlign s
  let (sign, r2) := signPart r1
  let (alt, r3) := optChar '#' r2
  -- `(?P<minimumwidth>0|[1-9][0-9]*)?`
  let (width, r4) : Option (List Char) × List Char := match r3 with
    | '0' :: r => (some ['0'], r)
    | c :: r => if isAsciiDigit c then
                  let (ds, r') := asciiDigits r; (some (c :: ds), r')
                else (none, c :: r)
    | [] => (none, [])
  let (sep, r5) := sepPart r4
  if r5 = [] then some ⟨fill, align, sign, alt, width, sep⟩ else none

structure FloatSpec where
  fill : Option Char
  align : Option Char
  sign : List Char
  noNegZero : Bool
  alt : Bool
  zeropad : Bool
  width : Option (List Char)
  sep : Option Char
  precision : Option (List Char)
  fracSep : Option Char
  type : Char
  deriving Repr, DecidableEq

def isFloatType (c : Char) : Bool :=
  c == 'e' || c == 'E' || c == 'f' || c == 'F' || c == 'g' || c == 'G' || c == '%'

/-- `_FLOAT_FORMAT_SPECIFICATION_MATCHER` (a `fullmatch`),
fractions.py:160-179. -/
def matchFloat (s : List Char) : Option FloatSpec :=
  let (fill, align, r1) := fillAlign s
  let (sign, r2) := signPart r1
  let (z, r3) := optChar 'z' r2
  let (alt, r4) := optChar '#' r3
  -- `(?P<zeropad>0(?=[0-9]))?`
  let (zp, r5) : Bool × List Char := match r4 with
    | '0' :: d :: r => if isAsciiDigit d then (true, d :: r) else (false, '0' :: d :: r)
    | r => (false, r)
  let (wd, r6) := asciiDigits r5
  let width := if wd = [] then none else some wd
  let (sep, r7) := sepPart r6
  -- `(?:\.(?=[,_0-9])(?P<precision>[0-9]+)?(?P<frac_separators>[,_])?)?`
  let (prec, fsep, r8) : Option (List Char) × Option Char × List Char := match r7 with
    | '.' :: c :: r =>
      if isAsciiDigit c || c == ',' || c == '_' then
        let (pd, r') := asciiDigits (c :: r)
        let (fs, r'') := sepPart r'
        (if pd = [] then none else some pd, fs, r'')
      else (none, none, '.' :: c :: r)
    | r => (none, none, r)
  match r8 with
  | [t] => if isFloatType t then some ⟨fill, align, sign, z, alt, zp, width, sep, prec, fsep, t⟩
           else none
  | _ => none

/-! ## Helpers -/

/-- `s.zfill(w)` for a string without sign. -/
def zfill (s : List Char) (w : Int) : List Char :=
  List.replicate (w.toNat - s.length) '0' ++ s

/-- `c * k` (string repetition; empty for `k <= 0`). -/
def rep (c : Char) (k : Int) : List Char := List.replicate k.toNat c

/-- Split into chunks of 3 from the left: `[s[pos:pos+3] for pos in range(0, len(s), 3)]`. -/
def chunks3 : List Char → List (List Char)
  | a :: b :: c :: d :: r => [a, b, c] :: chunks3 (d :: r)
  | s => if s = [] then [] else [s]

/-- `sep.join(parts)` -/
def joinWith (sep : List Char) : List (List Char) → List Char
  | [] => []
  | [p] => p
  | p :: ps => p ++ sep ++ joinWith sep ps

/-- Thousands grouping of a digit string from the right, as int `__format__`
with `,` or `_` does and as fractions.py:578-583 does by hand. -/
def groupLeft (sep : Char) (s : List Char) : List Char :=
  let firstPos := 1 + (s.length - 1) % 3
  s.take firstPos ++ (chunks3 (s.drop firstPos)).foldr (fun c acc => sep :: c ++ acc) []

/-- `f"{i:{sep}}"` for an int `i >= 0` and `sep` in `'', ',', '_'`. -/
def fmtIntSep (i : Int) (sep : Option Char) : Py (List Char) := do
  let s ← strInt i
  match sep with
  | none => return s
  | some c => return groupLeft c s

/-- Python string comparison `a <= b` (code point lexicographic). -/
def strLe : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if a = b then strLe as bs else false

/-- Pad and align, the common tail of both formatters. -/
def alignPad (fill align : Char) (width : Int) (sign body : List Char) : List Char :=
  let padding := rep fill (width - sign.length - body.length)
  if align = '>' then padding ++ sign ++ body
  else if align = '<' then sign ++ body ++ padding
  else if align = '^' then
    let half := padding.length / 2
    padding.take half ++ sign ++ body ++ padding.drop half
  else sign ++ padding ++ body

/-- `int(match["minimumwidth"] or "0")` and similar. -/
def specInt (o : Option (List Char)) (dflt : Int) : Py Int :=
  match o with
  | none => .ok dflt
  | some ds => pyIntOfDigits ds

/-! ## Rounding helpers -/

/-- `_round_to_exponent(n, d, exponent, no_neg_zero)`, fractions.py:73-99. -/
def roundToExponent (n d exponent : Int) (noNegZero : Bool) : Bool × Int :=
  let (n, d) := if exponent ≥ 0 then (n, d * 10 ^ exponent.toNat) else (n * 10 ^ (-exponent).toNat, d)
  let q := pyDiv (n + d / 2) d
  let r := pyMod (n + d / 2) d
  let q := if r = 0 ∧ d % 2 = 0 then q - pyMod q 2 else q
  let sign := if noNegZero then decide (q < 0) else decide (n < 0)
  (sign, q.natAbs)

/-- `_round_to_figures(n, d, figures)`, fractions.py:102-138. -/
def roundToFigures (n d : Int) (figures : Nat) : Py (Bool × Int × Int) := do
  if n = 0 then return (false, 0, 1 - (figures : Int))
  let strN ← strInt n.natAbs
  let strD ← strInt d
  let m : Int := (strN.length : Int) - strD.length + (if strLe strD strN then 1 else 0)
  let exponent := m - figures
  let (sign, significand) := roundToExponent n d exponent false
  let ss ← strInt significand
  if ss.length = figures + 1 then return (sign, pyDiv significand 10, exponent + 1)
  return (sign, significand, exponent)

/-! ## `__format__` -/

/-- `_format_general`, fractions.py:461-493. -/
def formatGeneral (x : Frac) (m : GenSpec) : Py (List Char) := do
  let fill := m.fill.getD ' '
  let align := m.align.getD '>'
  let posSign := if m.sign = ['-'] then [] else m.sign
  let width ← specInt m.width 0
  let n := x.num
  let d := x.den
  let nStr ← fmtIntSep n.natAbs m.sep
  let body ← if d > 1 ∨ m.alt then do
      let dStr ← fmtIntSep d m.sep
      pure (nStr ++ ['/'] ++ dStr)
    else pure nStr
  let sign := if n < 0 then ['-'] else posSign
  return alignPad fill align width sign body

/-- `f"{e:+03d}"` for a small int. -/
def fmtExp (e : Int) : Py (List Char) := do
  let s ← strInt e.natAbs
  return (if e < 0 then '-' else '+') :: zfill s 2

/-- `_format_float_style`, fractions.py:495-597. -/
def formatFloat (x : Frac) (m : FloatSpec) : Py (List Char) := do
  let fill := m.fill.getD ' '
  let align := m.align.getD '>'
  let posSign := if m.sign = ['-'] then [] else m.sign
  let width ← specInt m.width 0
  let precision ← specInt m.precision 6
  let t := m.type
  let trimZeros := (t == 'g' || t == 'G') && !m.alt
  let trimPoint := !m.alt
  let expInd := if t == 'E' || t == 'F' || t == 'G' then 'E' else 'e'
  let zeropad := m.zeropad || (align = '=' ∧ fill = '0')
  let (negative, significand, exponent, scientific, pointPos) ←
    if t == 'f' || t == 'F' || t == '%' then do
      let exponent := if t == '%' then -precision - 2 else -precision
      let (neg, sig) := roundToExponent x.num x.den exponent m.noNegZero
      pure (neg, (sig : Int), exponent, false, precision)
    else do
      let figures : Int := if t == 'g' || t == 'G' then max precision 1 else precision + 1
      let (neg, sig, exponent) ← roundToFigures x.num x.den figures.toNat
      let sci := t == 'e' || t == 'E' || decide (exponent > 0) || decide (exponent + figures ≤ -4)
      pure (neg, sig, exponent, sci, if sci then figures - 1 else -exponent)
  let suffix ← if t == '%' then pure ['%']
    else if scientific then do pure (expInd :: (← fmtExp (exponent + pointPos)))
    else pure []
  let digits := zfill (← strInt significand) (pointPos + 1)
  let sign := if negative then ['-'] else posSign
  let pp := pointPos.toNat
  let leading := digits.take (digits.length - pp)
  let frac := digits.drop (digits.length - pp)
  let frac := if trimZeros then (frac.reverse.dropWhile (· = '0')).reverse else frac
  let separator := if trimPoint ∧ frac = [] then [] else ['.']
  let frac := match m.fracSep with
    | some c => joinWith [c] (chunks3 frac)
    | none => frac
  let trailing := separator ++ frac ++ suffix
  let leading := if zeropad then
      let minLeading := width - sign.length - trailing.length
      zfill leading (if m.sep.isSome then pyDiv (3 * minLeading) 4 + 1 else minLeading)
    else leading
  let leading := match m.sep with
    | some c => groupLeft c leading
    | none => leading
  return alignPad fill align width sign (leading ++ trailing)

/-- `__format__`, fractions.py:599-614. The error message embeds
`format_spec!r`, so only its class is compared. -/
def format (x : Frac) (spec : List Char) : Py (List Char) :=
  match matchGeneral spec with
  | some m => formatGeneral x m
  | none =>
    match matchFloat spec with
    | some m =>
      if m.align.isNone || !m.zeropad then formatFloat x m
      else .error (.valueError "~Invalid format specifier")
    | none => .error (.valueError "~Invalid format specifier")

end PyLean.Fractions
