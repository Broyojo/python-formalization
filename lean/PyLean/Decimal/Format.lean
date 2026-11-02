import PyLean.Decimal.Basic

/-!
Which format specifications `Decimal.__format__` accepts, in both twins.

A specification is a list of code points (`List Nat`), so that lone
surrogates, which a Python `str` may contain but a Lean `Char` may not, are
representable.

**`_pydecimal`** (`_parse_format_specifier`, _pydecimal.py:6261-6342): the
regex at :6231-6249

```
\A (?:(?P<fill>.)?(?P<align>[<>=^]))? (?P<sign>[-+ ])? (?P<no_neg_0>z)? (?P<alt>\#)?
   (?P<zeropad>0)? (?P<minimumwidth>\d+)? (?P<thousands_sep>[,_])?
   (?:\.(?=[\d,_])(?P<precision>\d+)?(?P<frac_separators>[,_])?)?
   (?P<type>[eEfFgGn%])? \z          (re.VERBOSE | re.DOTALL)
```

followed by the checks at :6292-6299 (`0` with an explicit fill or alignment),
:6310-6312 (`int()` on the width and the precision, which applies the
4300-digit limit) and :6327-6329 (`n` with a thousands separator). The regex
has a unique match: each optional piece is followed by pieces that cannot
start with the characters it consumes, except
`(?P<zeropad>0)?(?P<minimumwidth>\d+)?`, where both readings leave the same
remainder.

**`_decimal`** (`_decimal_Decimal___format___impl`, _decimal.c:3760-3889): the `str` is
encoded with `PyUnicode_AsUTF8AndSize` (:3778, which fails on a lone surrogate), a NUL
fill character in position 0 is replaced by `'_'` (:3791-3800), and the *C
string* is handed to `mpd_parse_fmt_str`, which stops at the first NUL byte.
If that parser rejects the spec, `pydec_format` (:3710-3744) falls back to
`_pydecimal`'s `__format__` on the full `str`. A spec accepted by
`mpd_parse_fmt_str` is rejected later only if its width exceeds `MPD_MAX_PREC`
(`mpd_qformat_spec`, io.c:1268-1271).

Which `mpd_parse_fmt_str` runs depends on the build. The bundled libmpdec
2.5.1 (Modules/_decimal/libmpdec/io.c:796-915, the line numbers cited here)
does not know `z`, so `z` specs reach the fallback. libmpdec 4.0.1, which a
`--with-system-libmpdec` build such as Homebrew's links, is the same parser
plus an optional `z` after the sign (mpdecimal-4.0.1 libmpdec/io.c:835-839).
The two differ on, for instance, `'zN'`. `LibMpdec` selects the parser, and
the differential test reads it from `decimal.__libmpdec_version__`.
-/

namespace PyLean.Decimal

open PyLean

/-- Outcome of a format call, as far as the spec is concerned. -/
inductive FmtOutcome where
  | accepted
  | valueError
  | unicodeEncodeError
  deriving Repr, DecidableEq

def isAlignCp (c : Nat) : Bool := c == '<'.toNat || c == '>'.toNat || c == '='.toNat || c == '^'.toNat

/-- `\d` on a code point (Unicode `Nd`). Surrogates are not digits. -/
def isDigitCp (c : Nat) : Bool :=
  ndZeros.any (fun z => z ≤ c ∧ c ≤ z + 9)

def isAsciiDigitCp (c : Nat) : Bool := 0x30 ≤ c && c ≤ 0x39

def cp (c : Char) : Nat := c.toNat

/-! ## `_pydecimal` -/

/-- The groups of a successful match that the later checks read. -/
structure PySpec where
  fill : Bool
  align : Bool
  zeropad : Bool
  widthDigits : Nat
  thousands : Bool
  precDigits : Option Nat
  type : Option Nat
  deriving Repr, DecidableEq

def optOne (p : Nat → Bool) : List Nat → Bool × List Nat
  | c :: r => if p c then (true, r) else (false, c :: r)
  | [] => (false, [])

/-- The regex match. -/
def pySpecMatch (s : List Nat) : Option PySpec :=
  let (fill, align, r) := match s with
    | f :: a :: r => if isAlignCp a then (true, true, r)
                     else if isAlignCp f then (false, true, a :: r) else (false, false, f :: a :: r)
    | [a] => if isAlignCp a then (false, true, []) else (false, false, [a])
    | [] => (false, false, [])
  let (_, r) := optOne (fun c => c == cp '-' || c == cp '+' || c == cp ' ') r
  let (_, r) := optOne (· == cp 'z') r
  let (_, r) := optOne (· == cp '#') r
  let (zeropad, r) := optOne (· == cp '0') r
  let width := r.takeWhile isDigitCp
  let r := r.dropWhile isDigitCp
  let (thousands, r) := optOne (fun c => c == cp ',' || c == cp '_') r
  let (prec, r) := match r with
    | d :: r' =>
      let look := match r' with
        | c :: _ => isDigitCp c || c == cp ',' || c == cp '_'
        | [] => false
      if d == cp '.' ∧ look then
        let p := r'.takeWhile isDigitCp
        let r'' := r'.dropWhile isDigitCp
        let (_, r''') := optOne (fun c => c == cp ',' || c == cp '_') r''
        (some p.length, r''')
      else (none, d :: r')
    | [] => (none, [])
  let typeCps := "eEfFgGn%".toList.map cp
  let (ty, r) := match r with
    | c :: r' => if c ∈ typeCps then (some c, r') else (none, c :: r')
    | [] => (none, [])
  if r = [] then
    -- a precision group whose digits are absent reads as None
    let prec := match prec with | some 0 => none | p => p
    some ⟨fill, align, zeropad, width.length, thousands, prec, ty⟩
  else none

/-- `_parse_format_specifier(spec)` succeeds. -/
def pySpecOk (s : List Nat) : Bool :=
  match pySpecMatch s with
  | none => false
  | some m =>
    !(m.zeropad && m.fill) && !(m.zeropad && m.align) &&
    m.widthDigits ≤ maxStrDigits &&
    (match m.precDigits with | some p => p ≤ maxStrDigits | none => true) &&
    !(m.type == some (cp 'n') && m.thousands)

/-- `_pydecimal.Decimal.__format__` on a finite value: the spec decides. -/
def pyFormat (s : List Nat) : FmtOutcome := if pySpecOk s then .accepted else .valueError

/-! ## `_decimal` -/

/-- `strtoll` on a run of ASCII digits: `none` on `ERANGE`. -/
def strtollDigits (ds : List Nat) : Option Nat :=
  let v : Nat := ds.foldl (fun acc c => acc * 10 + (c - 0x30)) 0
  if (v : Int) > mpdSsizeMax then none else some v

/-- Which libmpdec `_decimal` was built with. -/
inductive LibMpdec where
  | bundled251
  | system401
  deriving Repr, DecidableEq, Inhabited

/-- `mpd_parse_fmt_str` on the code points of the C string (already cut at
its first NUL): `some width` on success. -/
def mpdParseFmt (lib : LibMpdec) (s : List Nat) : Option Nat := do
  -- fill (io.c:813-834)
  let (haveAlign, r) := match s with
    | _ :: a :: r => if isAlignCp a then (true, r)
                     else match s with
                       | f :: r' => if isAlignCp f then (true, r') else (false, s)
                       | [] => (false, s)
    | [f] => if isAlignCp f then (true, []) else (false, [f])
    | [] => (false, [])
  -- sign (:837-839)
  let r := match r with
    | c :: r' => if c == cp '+' || c == cp '-' || c == cp ' ' then r' else r
    | [] => []
  -- coerce to positive zero (libmpdec 4.0.1 only, its io.c:835-839)
  let r := match r with
    | c :: r' => if lib == .system401 && c == cp 'z' then r' else r
    | [] => []
  -- zero padding (:842-851)
  let r ← match r with
    | c :: r' => if c == cp '0' then (if haveAlign then none else some r') else some r
    | [] => some []
  -- minimum width (:854-863)
  let (width, r) ← match r with
    | c :: _ =>
      if isAsciiDigitCp c then
        if c == cp '0' then none
        else
          let ds := r.takeWhile isAsciiDigitCp
          match strtollDigits ds with
          | none => none
          | some w => some (w, r.dropWhile isAsciiDigitCp)
      else some (0, r)
    | [] => some (0, [])
  -- thousands separator (:866-871)
  let (sep, r) := match r with
    | c :: r' => if c == cp ',' then (true, r') else (false, r)
    | [] => (false, [])
  -- precision (@3.14.7:874-884)
  let r ← match r with
    | c :: r' =>
      if c == cp '.' then
        match r' with
        | d :: _ =>
          if isAsciiDigitCp d then
            match strtollDigits (r'.takeWhile isAsciiDigitCp) with
            | none => none
            | some _ => some (r'.dropWhile isAsciiDigitCp)
          else none
        | [] => none
      else some r
    | [] => some []
  -- type (:887-907)
  let r ← match r with
    | c :: r' =>
      if ("EeFfGg%".toList.map cp).contains c then some r'
      else if c == cp 'N' || c == cp 'n' then (if sep then none else some r')
      else some r
    | [] => some []
  if r = [] then some width else none

def isSurrogate (c : Nat) : Bool := 0xD800 ≤ c && c ≤ 0xDFFF

/-- A non-`str` spec: the clinic `unicode` converter of `Decimal.__format__`
(clinic/_decimal.c.h) refuses it before the body runs. 3.14 raised `format arg must be
str` from the body. `format()` itself checks the type first, so only a direct call of
`__format__` reaches this. -/
def cFormatBadArg (ty : String) : PyExc :=
  .typeError s!"__format__() argument 1 must be str, not {if ty == "NoneType" then "None" else ty}"

/-- `format(_decimal.Decimal(x), spec)` for a finite `x`: the spec decides. -/
def cFormat (lib : LibMpdec) (s : List Nat) : FmtOutcome :=
  if s.any isSurrogate then .unicodeEncodeError
  else
    -- NUL fill character replaced by '_' (_decimal.c:3791-3800); the C string ends at
    -- the first remaining NUL
    let s' := match s with
      | 0 :: r => cp '_' :: r
      | r => r
    match mpdParseFmt lib (s'.takeWhile (· ≠ 0)) with
    | some w => if (w : Int) > mpdMaxPrec then .valueError else .accepted
    | none => pyFormat s

end PyLean.Decimal
