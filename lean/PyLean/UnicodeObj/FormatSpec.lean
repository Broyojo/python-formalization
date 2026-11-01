import PyLean.UnicodeObj.TextCase

/-!
The format specification mini-language: Python/formatter_unicode.c and
Objects/stringlib/localeutil.h, with `_PyUnicode_InsertThousandsGrouping`,
Objects/unicodeobject.c:9791-9899.

Abstractions:
* `int` and `str` are rendered in full here. `float` and `complex` stop at the
  dispatch; `FormatNumber.lean` carries on with their digits.
* The `'n'` type reads `localeconv()`. The model is the C locale (`decimal_point`
  `.`, no `thousands_sep`, empty `grouping`), which is what a process has unless it
  calls `locale.setlocale(LC_NUMERIC, ...)`.
* `int numdigits` of `get_integer` would wrap only after 2**31 digits.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `enum LocaleType`, formatter_unicode.c:122-128. -/
def LT_NO_LOCALE : Nat := 0
def LT_DEFAULT_LOCALE : Nat := 44
def LT_UNDERSCORE_LOCALE : Nat := 95
def LT_UNDER_FOUR_LOCALE : Nat := 96
def LT_CURRENT_LOCALE : Nat := 97

/-- `InternalFormatSpec`, formatter_unicode.c:130-141. -/
structure FormatSpec where
  fillChar : Nat := 32
  align : Nat
  alternate : Bool := false
  noNeg0 : Bool := false
  sign : Nat := 0
  width : Int := -1
  thousands : Nat := LT_NO_LOCALE
  precision : Int := -1
  fracThousands : Nat := LT_NO_LOCALE
  type : Nat
  deriving Repr, DecidableEq

/-- `\x%x`. -/
def hexPlain (n : Nat) : String :=
  String.ofList (Nat.toDigits 16 n)

/-- `unknown_presentation_type`, formatter_unicode.c:15-31. -/
def unknownPresentationType (t : Nat) (typeName : String) : PyExc :=
  if t > 32 ∧ t < 128 then
    .valueError s!"Unknown format code '{Char.ofNat t}' for object of type '{typeName}'"
  else
    .valueError s!"Unknown format code '\\x{hexPlain t}' for object of type '{typeName}'"

/-- `invalid_thousands_separator_type`, formatter_unicode.c:34-45. -/
def invalidThousandsSeparatorType (specifier t : Nat) : PyExc :=
  if t > 32 ∧ t < 128 then
    .valueError s!"Cannot specify '{Char.ofNat specifier}' with '{Char.ofNat t}'."
  else
    .valueError s!"Cannot specify '{Char.ofNat specifier}' with '\\x{hexPlain t}'."

/-- `invalid_comma_and_underscore`, formatter_unicode.c:48-51. -/
def invalidCommaAndUnderscore : PyExc := .valueError "Cannot specify both ',' and '_'."

/-- `get_integer`, formatter_unicode.c:61-91: value, digits consumed, what is left. -/
def getInteger : List Nat → Int → Nat → Py (Int × Nat × List Nat)
  | [], acc, n => .ok (acc, n, [])
  | c :: cs, acc, n =>
    let digitval := toDecimalDigit c
    if digitval < 0 then .ok (acc, n, c :: cs)
    else if acc > (ssizeMax - digitval) / 10 then
      .error (.valueError "Too many decimal digits in format string")
    else getInteger cs (acc * 10 + digitval) (n + 1)

/-- `is_alignment_token`, formatter_unicode.c:98-107. -/
def isAlignmentToken (c : Nat) : Bool := c == 60 || c == 62 || c == 61 || c == 94
/-- `is_sign_element`, formatter_unicode.c:110-119. -/
def isSignElement (c : Nat) : Bool := c == 32 || c == 43 || c == 45

/-- What the head of `rest` is, when there is one. -/
def headIs (rest : List Nat) (c : Nat) : Bool := rest.head? == some c

/-- The validation at the end of the parser, formatter_unicode.c:331-367. -/
def validateSpec (f : FormatSpec) : Py FormatSpec := do
  let f ←
    if f.thousands != 0 then
      let t := f.type
      if t == 100 || t == 101 || t == 102 || t == 103 || t == 69 || t == 71 || t == 37 ||
          t == 70 || t == 0 then
        pure f
      else if (t == 98 || t == 111 || t == 120 || t == 88) &&
          f.thousands == LT_UNDERSCORE_LOCALE then
        pure { f with thousands := LT_UNDER_FOUR_LOCALE }
      else .error (invalidThousandsSeparatorType f.thousands t)
    else pure f
  if f.type == 110 && f.fracThousands != LT_NO_LOCALE then
    .error (invalidThousandsSeparatorType f.fracThousands f.type)
  else .ok f

/-- The `.precision` part, formatter_unicode.c:258-301. -/
def parsePrecision (f : FormatSpec) (rest : List Nat) : Py (FormatSpec × List Nat) := do
  let (p, consumed0, rest) ← getInteger rest 0 0
  let f := { f with precision := p }
  let (f, consumed, rest) :=
    if headIs rest 44 then
      ({ f with precision := if consumed0 = 0 then -1 else f.precision,
                fracThousands := LT_DEFAULT_LOCALE }, consumed0 + 1, rest.tail)
    else (f, consumed0, rest)
  let (f, consumed, rest) ←
    if headIs rest 95 then
      if f.fracThousands != LT_NO_LOCALE then .error invalidCommaAndUnderscore
      else
        pure ({ f with precision := if consumed = 0 then -1 else f.precision,
                       fracThousands := LT_UNDERSCORE_LOCALE }, consumed + 1, rest.tail)
    else pure (f, consumed, rest)
  if headIs rest 44 && f.fracThousands == LT_UNDERSCORE_LOCALE then
    .error invalidCommaAndUnderscore
  else if consumed = 0 then .error (.valueError "Format specifier missing precision")
  else .ok (f, rest)

/-- Fill and alignment, formatter_unicode.c:182-193: the spec so far,
`align_specified`, `fill_char_specified`, the rest. -/
def parseAlign (f : FormatSpec) (spec : Str) : FormatSpec × Bool × Bool × List Nat :=
  match spec with
  | c :: a :: t =>
    if isAlignmentToken a then ({ f with align := a, fillChar := c }, true, true, t)
    else if isAlignmentToken c then ({ f with align := c }, true, false, a :: t)
    else (f, false, false, c :: a :: t)
  | [c] => if isAlignmentToken c then ({ f with align := c }, true, false, [])
           else (f, false, false, [c])
  | [] => (f, false, false, [])

/-- Sign, `z` and `#`, formatter_unicode.c:196-213. -/
def parseFlags (f : FormatSpec) (rest : List Nat) : FormatSpec × List Nat :=
  let p : FormatSpec × List Nat := match rest with
    | c :: t => if isSignElement c then ({ f with sign := c }, t) else (f, c :: t)
    | [] => (f, [])
  let p := if headIs p.2 122 then ({ p.1 with noNeg0 := true }, p.2.tail) else p
  if headIs p.2 35 then ({ p.1 with alternate := true }, p.2.tail) else p

/-- The first part of `parse_internal_render_format_spec`, formatter_unicode.c:169-222,
which cannot fail. -/
def parseHead (spec : Str) (defaultType defaultAlign : Nat) : FormatSpec × List Nat :=
  let a := parseAlign { align := defaultAlign, type := defaultType } spec
  let p := parseFlags a.1 a.2.2.2
  if !a.2.2.1 && headIs p.2 48 then
    ({ p.1 with fillChar := 48,
                align := if !a.2.1 && defaultAlign == 62 then 61 else p.1.align }, p.2.tail)
  else p

/-- Width and thousands separators, formatter_unicode.c:224-255. -/
def parseWidth (f : FormatSpec) (rest : List Nat) : Py (FormatSpec × List Nat) := do
  let (w, consumed, rest) ← getInteger rest 0 0
  let f := { f with width := if consumed = 0 then -1 else w }
  let p : FormatSpec × List Nat :=
    if headIs rest 44 then ({ f with thousands := LT_DEFAULT_LOCALE }, rest.tail) else (f, rest)
  let p ←
    if headIs p.2 95 then
      if p.1.thousands != LT_NO_LOCALE then .error invalidCommaAndUnderscore
      else pure ({ p.1 with thousands := LT_UNDERSCORE_LOCALE }, p.2.tail)
    else pure p
  if headIs p.2 44 && p.1.thousands == LT_UNDERSCORE_LOCALE then .error invalidCommaAndUnderscore
  else .ok p

/-- The type field, formatter_unicode.c:305-325, and the validation. -/
def parseType (typeName : String) (spec : Str) (f : FormatSpec) (rest : List Nat) :
    Py FormatSpec :=
  match rest with
  | [] => validateSpec f
  | [t] => validateSpec { f with type := t }
  | _ =>
    .error (.valueError
      s!"Invalid format specifier '{toLeanString spec}' for object of type '{typeName}'")

/-- The rest of `parse_internal_render_format_spec`, formatter_unicode.c:224-372. -/
def parseTail (typeName : String) (spec : Str) (f : FormatSpec) (rest : List Nat) :
    Py FormatSpec := do
  let p ← parseWidth f rest
  let q ← if headIs p.2 46 then parsePrecision p.1 p.2.tail else pure p
  parseType typeName spec q.1 q.2

/-- `parse_internal_render_format_spec`, formatter_unicode.c:151-372. -/
def parseFormatSpec (typeName : String) (spec : Str) (defaultType defaultAlign : Nat) :
    Py FormatSpec :=
  let (f, rest) := parseHead spec defaultType defaultAlign
  parseTail typeName spec f rest

/-- `calc_padding`, formatter_unicode.c:376-405: `(lpadding, rpadding, total)`. -/
def calcPadding (nchars : Nat) (width : Int) (align : Nat) : Nat × Nat × Nat :=
  let total := if width ≥ 0 then (if (nchars : Int) > width then nchars else width.toNat) else nchars
  let l := if align == 62 then total - nchars
    else if align == 94 then (total - nchars) / 2
    else 0
  (l, total - nchars - l, total)

/-- `fill_padding`, formatter_unicode.c:410-432, together with the copy of the
content that its callers do. -/
def fillPadding (content : Str) (fill l r : Nat) : Str :=
  List.replicate l fill ++ content ++ List.replicate r fill

/-! ## Grouping -/

/-- `GroupGenerator_next`, localeutil.h:21-40: value, `i`, `previous`. `127` is
`CHAR_MAX`; the end of the list is the terminating NUL. -/
def groupNext (grouping : List Nat) (i prev : Nat) : Nat × Nat × Nat :=
  match grouping[i]? with
  | none | some 0 => (prev, i, prev)
  | some 127 => (0, i, prev)
  | some ch => (ch, i + 1, ch)

/-- One call of `InsertThousandsGrouping_fill` writing backwards: the buffer gets
zeros, digits, separator, in front of what is already there. `digitsRev` holds the
digits not yet consumed, last digit first. -/
def groupPiece (sep : Str) (useSep : Bool) (nChars nZeros : Nat) (digitsRev out : List Nat) :
    List Nat × List Nat :=
  (digitsRev.drop nChars,
   List.replicate nZeros 48 ++ (digitsRev.take nChars).reverse ++ (if useSep then sep else []) ++ out)

/-- The `while` loop of `_PyUnicode_InsertThousandsGrouping`,
unicodeobject.c:9852-9879. Returns `count`, the text and the iterations made. -/
def groupLoop (grouping : List Nat) (sep : Str) :
    Nat → Nat → Nat → Bool → Int → Int → List Nat → Nat → List Nat → Nat →
      Py (Nat × List Nat × Nat)
  | 0, _, _, _, _, _, _, _, _, _ => .error .modelFuel
  | fuel + 1, i, prev, useSep, remaining, minWidth, digitsRev, count, out, iters =>
    let (len0, i, prev) := groupNext grouping i prev
    let finish : Py (Nat × List Nat × Nat) :=
      -- the part after the loop, unicodeobject.c:9881-9892
      let len : Int := max (max remaining minWidth) 1
      let nZeros := max 0 (len - remaining)
      let nChars := max 0 (min remaining len)
      let count := count + (if useSep then sep.length else 0) + nZeros.toNat + nChars.toNat
      let (_, out) := groupPiece sep useSep nChars.toNat nZeros.toNat digitsRev out
      .ok (count, out, iters)
    if len0 > 0 then
      let len : Int := min (len0 : Int) (max (max remaining minWidth) 1)
      let nZeros := max 0 (len - remaining)
      let nChars := max 0 (min remaining len)
      let count := count + (if useSep then sep.length else 0) + nZeros.toNat + nChars.toNat
      let (digitsRev, out) := groupPiece sep useSep nChars.toNat nZeros.toNat digitsRev out
      let remaining := remaining - nChars
      let minWidth := minWidth - len
      if remaining ≤ 0 ∧ minWidth ≤ 0 then .ok (count, out, iters + 1)
      else
        groupLoop grouping sep fuel i prev true remaining (minWidth - sep.length) digitsRev
          count out (iters + 1)
    else finish

/-- `_PyUnicode_InsertThousandsGrouping`, unicodeobject.c:9791-9899, for `forward = 0`
and with the first (counting) and second (writing) calls merged: it returns the
`count` of the first together with the text of the second. The fuel is enough for
every call the model makes: each round lowers `remaining` or `minWidth`. -/
def insertThousandsGrouping (digits : Str) (minWidth : Int) (grouping : List Nat) (sep : Str) :
    Py (Nat × List Nat × Nat) :=
  groupLoop grouping sep (digits.length + (max 0 minWidth).toNat + 2) 0 0 false digits.length
    (max 0 minWidth) digits.reverse 0 [] 0

/-- `LocaleInfo` as `get_locale_info` fills it, formatter_unicode.c:786-846, in the
C locale: `(thousands_sep, grouping)`. -/
def localeInfo (type : Nat) : Str × List Nat :=
  if type == LT_CURRENT_LOCALE then ([], [])
  else if type == LT_DEFAULT_LOCALE then ([44], [3])
  else if type == LT_UNDERSCORE_LOCALE then ([95], [3])
  else if type == LT_UNDER_FOUR_LOCALE then ([95], [4])
  else ([], [127])

/-! ## `int` -/

/-- The digit loop: `acc` holds the lower digits, `fuel` bounds the digits left. -/
def natDigits (b : Nat) : Nat → Nat → Str → Str
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let acc' := hexLower (n % b) :: acc
    if n / b = 0 then acc' else natDigits b fuel (n / b) acc'

/-- The digits of `n` in base `b`, most significant first. -/
def digitsOf (b n : Nat) : Str := natDigits b (n + 1) n []

/-- `_PyLong_Format(value, base)`, Objects/longobject.c: a `-`, the `0b`/`0o`/`0x`
prefix, the digits. In base 10 the int/str limit applies
(`sys.get_int_max_str_digits()`, default 4300). -/
def longFormat (v : Int) (base : Nat) (alternate : Bool := true) : Py Str :=
  let ds := digitsOf base v.natAbs
  if base == 10 && ds.length > 4300 then
    .error (.valueError "Exceeds the limit (4300 digits) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit")
  else
    let pfx :=
      if !alternate then [] else
      if base == 2 then [48, 98] else if base == 8 then [48, 111]
      else if base == 16 then [48, 120] else []
    .ok ((if v < 0 then [45] else []) ++ pfx ++ ds)

/-- `spec` of `calc_number_widths`, formatter_unicode.c:524-666, for numbers with no
fraction or decimal point: `(n_lpadding, sign, n_spadding, n_rpadding, n_min_width,
n_grouped_digits, text of the grouped digits)`. -/
def calcNumberWidths (nPrefix : Nat) (signChar : Nat) (digits : Str) (nRemainder : Nat)
    (sep : Str) (grouping : List Nat) (f : FormatSpec) :
    Py (Nat × Option Nat × Nat × Nat × Str) := do
  let (nSign, sign) : Nat × Option Nat :=
    if f.sign == 43 then (1, some (if signChar == 45 then 45 else 43))
    else if f.sign == 32 then (1, some (if signChar == 45 then 45 else 32))
    else if signChar == 45 then (1, some 45)
    else (0, none)
  let nonDigit : Int := nSign + nPrefix + nRemainder
  let minWidth : Int := if f.fillChar == 48 && f.align == 61 then f.width - nonDigit else 0
  let (nGrouped, text, _) ←
    if digits.length = 0 then pure (0, [], 0)
    else insertThousandsGrouping digits minWidth grouping sep
  let nPadding := f.width - (nonDigit + nGrouped)
  let (l, s, r) : Nat × Nat × Nat :=
    if nPadding > 0 then
      let p := nPadding.toNat
      if f.align == 60 then (0, 0, p)
      else if f.align == 94 then (p / 2, 0, p - p / 2)
      else if f.align == 61 then (0, p, 0)
      else (p, 0, 0)
    else (0, 0, 0)
  .ok (l, sign, s, r, text)

/-- `fill_number`, formatter_unicode.c:672-777, without decimal point or fraction. -/
def fillNumber (l : Nat) (sign : Option Nat) (pfx : Str) (s : Nat) (text remainder : Str)
    (r fill : Nat) (toupper : Bool) : Str :=
  let up (x : Str) := if toupper then x.map pyToUpper else x
  List.replicate l fill ++ sign.toList ++ up pfx ++ List.replicate s fill ++ up text ++
    remainder ++ List.replicate r fill

/-- The fast path `_PyLong_FormatWriter(writer, value, base, alternate)`. -/
def longFormatWriter (v : Int) (base : Nat) (alternate : Bool) : Py Str :=
  longFormat v base alternate

/-- The part of `format_long_internal` after the `_PyLong_FormatWriter` test,
formatter_unicode.c:1056-1130, for the digit types. -/
def formatLongSlow (v : Int) (f : FormatSpec) (base : Nat) (skip : Nat) : Py Str := do
  let nPrefix := if f.alternate then skip else 0
  let tmp ← longFormat v base
  let (signChar, tmp1) := if tmp.head? == some 45 then (45, tmp.tail) else (0, tmp)
  let pfx := tmp1.take nPrefix
  let digits := tmp1.drop skip
  let (sep, grouping) := localeInfo (if f.type == 110 then LT_CURRENT_LOCALE else f.thousands)
  let (l, sign, s, r, text) ← calcNumberWidths nPrefix signChar digits 0 sep grouping f
  .ok (fillNumber l sign pfx s text [] r f.fillChar (f.type == 88))

/-- `format_long_internal`, formatter_unicode.c:960-1130. `exact` is
`PyLong_CheckExact(value)`. -/
def formatLongInternal (v : Int) (f : FormatSpec) (exact : Bool) : Py Str := do
  if f.precision != -1 then
    .error (.valueError "Precision not allowed in integer format specifier")
  else if f.noNeg0 then
    .error (.valueError "Negative zero coercion (z) not allowed in integer format specifier")
  else if f.type == 99 then
    if f.sign != 0 then .error (.valueError "Sign not allowed with integer format specifier 'c'")
    else if f.alternate then
      .error (.valueError "Alternate form (#) not allowed with integer format specifier 'c'")
    else if v > 2 ^ 63 - 1 ∨ v < -(2 ^ 63) then
      .error (.overflowError "Python int too large to convert to C long")
    else if v < 0 ∨ v > 0x10ffff then
      .error (.overflowError "%c arg not in range(0x110000)")
    else
      let (sep, grouping) := localeInfo f.thousands
      let (l, sign, s, r, text) ← calcNumberWidths 0 0 [] 1 sep grouping f
      .ok (fillNumber l sign [] s text [v.toNat] r f.fillChar false)
  else
    let (base, skip) : Nat × Nat :=
      if f.type == 98 then (2, 2) else if f.type == 111 then (8, 2)
      else if f.type == 120 || f.type == 88 then (16, 2) else (10, 0)
    if f.sign != 43 && f.sign != 32 && f.width == -1 && f.type != 88 && f.type != 110 &&
        f.thousands == 0 && exact then
      longFormatWriter v base f.alternate
    else formatLongSlow v f base skip

/-! ## `str` -/

/-- `format_string_internal`, formatter_unicode.c:862-952. -/
def formatStringInternal (value : Str) (f : FormatSpec) : Py Str :=
  if f.sign != 0 then
    if f.sign == 32 then .error (.valueError "Space not allowed in string format specifier")
    else .error (.valueError "Sign not allowed in string format specifier")
  else if f.noNeg0 then
    .error (.valueError "Negative zero coercion (z) not allowed in string format specifier")
  else if f.alternate then
    .error (.valueError "Alternate form (#) not allowed in string format specifier")
  else if f.align == 61 then
    .error (.valueError "'=' alignment not allowed in string format specifier")
  else if (f.width == -1 ∨ f.width ≤ value.length) ∧
      (f.precision == -1 ∨ f.precision ≥ value.length) then .ok value
  else
    let content := if f.precision ≥ 0 ∧ value.length ≥ f.precision
      then value.take f.precision.toNat else value
    let (l, r, _) := calcPadding content.length f.width f.align
    .ok (fillPadding content f.fillChar l r)

/-! ## The dispatchers -/

/-- `_PyUnicode_FormatAdvancedWriter`, formatter_unicode.c:1554-1587. `exact` is
`PyUnicode_CheckExact(obj)`; both branches for an empty spec write `str(obj)`. -/
def formatStrAdvanced (value spec : Str) : Py Str := do
  if spec.isEmpty then .ok value
  else
    let f ← parseFormatSpec "str" spec 115 60
    if f.type == 115 then formatStringInternal value f
    else .error (unknownPresentationType f.type "str")

/-- The check `format_float_internal` makes first, formatter_unicode.c:1167-1171. -/
def formatFloatChecks (f : FormatSpec) : Py Unit :=
  if f.precision > 2 ^ 31 - 1 then .error (.valueError "precision too big") else .ok ()

/-- `_PyLong_FormatAdvancedWriter`, formatter_unicode.c:1590-1649. A float type
stops at the checks: the result is `none`, for "goes on to format a float". `name`
is `int` or `bool`. -/
def formatLongAdvanced (v : Int) (name : String) (spec : Str) (emptyStr : Str) :
    Py (Option Str) := do
  if spec.isEmpty then .ok (some emptyStr)
  else
    let f ← parseFormatSpec name spec 100 62
    let t := f.type
    if t == 98 || t == 99 || t == 100 || t == 111 || t == 120 || t == 88 || t == 110 then
      some <$> formatLongInternal v f (name == "int")
    else if t == 101 || t == 69 || t == 102 || t == 70 || t == 103 || t == 71 || t == 37 then do
      -- `PyNumber_Float(obj)`: the int rounds to infinity from 2**1024 - 2**970 up
      if v.natAbs ≥ 2 ^ 1024 - 2 ^ 970 then
        .error (.overflowError "int too large to convert to float")
      else
        formatFloatChecks f
        .ok none
    else .error (unknownPresentationType t name)

/-- `_PyFloat_FormatAdvancedWriter`, formatter_unicode.c:1652-1688, up to its call of
`format_float_internal`: `none` for the empty spec, else the parsed spec. -/
def formatFloatDispatch (spec : Str) : Py (Option FormatSpec) := do
  if spec.isEmpty then .ok none
  else
    let f ← parseFormatSpec "float" spec 0 62
    let t := f.type
    if t == 0 || t == 101 || t == 69 || t == 102 || t == 70 || t == 103 || t == 71 ||
        t == 110 || t == 37 then .ok (some f)
    else .error (unknownPresentationType t "float")

/-- `_PyComplex_FormatAdvancedWriter`, formatter_unicode.c:1691-1726, up to its call of
`format_complex_internal`. -/
def formatComplexDispatch (spec : Str) : Py (Option FormatSpec) := do
  if spec.isEmpty then .ok none
  else
    let f ← parseFormatSpec "complex" spec 0 62
    let t := f.type
    if t == 0 || t == 101 || t == 69 || t == 102 || t == 70 || t == 103 || t == 71 ||
        t == 110 then .ok (some f)
    else .error (unknownPresentationType t "complex")

end PyLean.UnicodeObj
