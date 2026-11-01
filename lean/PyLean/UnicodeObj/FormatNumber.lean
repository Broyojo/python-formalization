import PyLean.UnicodeObj.FormatSpec
import PyLean.Binary64.Complex

/-!
`format()` of a `float` or `complex`: `format_float_internal` and
`format_complex_internal`, Python/formatter_unicode.c:1137-1540, over the exact binary64
model of `lean/PyLean/Binary64/`.

`calc_number_widths` and `fill_number` are mirrored here with the decimal point, the
fraction and the remainder that an `int` never has. `calcNumberWidthsFull` is what
`calcNumberWidths` specialises (`calcNumberWidths_eq_full` in `FormatFloat.lean`).

Abstraction: `'n'` reads the C locale, as `localeInfo` does.
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

/-! ## `parse_number` -/

/-- `Py_ISDIGIT`. -/
def pyDigit (c : Nat) : Bool := decide (48 ≤ c) && decide (c ≤ 57)

/-- What `parse_number` does after the integer digits: `has_decimal`, `n_frac`,
`n_remainder`. -/
def parseRest (rest : List Nat) : Bool × Nat × Nat :=
  let hasDecimal := rest.head? == some 46
  let r := if hasDecimal then rest.tail else rest
  (hasDecimal, (r.takeWhile pyDigit).length, (r.dropWhile pyDigit).length)

/-- `parse_number`, formatter_unicode.c:489-516: the digits before the point,
`has_decimal`, `n_frac`, `n_remainder`. -/
def parseNumber (s : Str) : Nat × Bool × Nat × Nat :=
  ((s.takeWhile pyDigit).length, parseRest (s.dropWhile pyDigit))

/-- The text `parse_number` measures, cut at the positions it finds: digits,
`has_decimal`, fraction, remainder. -/
def splitNumber (s : Str) : Str × Bool × Str × Str :=
  let (nd, hasDec, nFrac, _) := parseNumber s
  let afterDigits := s.drop nd
  let r := if hasDec then afterDigits.tail else afterDigits
  (s.take nd, hasDec, r.take nFrac, r.drop nFrac)

/-! ## `LocaleInfo` -/

/-- `LocaleInfo`, with the fields `localeInfo` leaves out. -/
structure LocaleFull where
  decimal : Str := [46]
  sep : Str
  fracSep : Str
  grouping : List Nat
  deriving Repr, DecidableEq

/-- `get_locale_info`, formatter_unicode.c:786-846, in the C locale. A fraction
separator turns grouping on when the integer part has none: `no_grouping` is the
`LT_NO_LOCALE` case. -/
def localeInfoFull (type fracType : Nat) : LocaleFull :=
  let (sep, grouping) := localeInfo type
  if fracType != LT_NO_LOCALE then
    { sep, fracSep := [if fracType == LT_DEFAULT_LOCALE then 44 else 95]
      grouping := if type == LT_NO_LOCALE then [3] else grouping }
  else { sep, fracSep := [], grouping }

/-! ## Forward grouping -/

/-- One call of `InsertThousandsGrouping_fill` with `forward` set, localeutil.h:45-97:
separator, digits, zeros, after what is already there. -/
def groupPieceFwd (sep : Str) (useSep : Bool) (nChars nZeros : Nat) (digits out : Str) :
    Str × Str :=
  (digits.drop nChars,
   out ++ (if useSep then sep else []) ++ digits.take nChars ++ List.replicate nZeros 48)

/-- The `while` loop of `_PyUnicode_InsertThousandsGrouping` with `forward` set,
unicodeobject.c:9849-9890. -/
def groupLoopFwd (grouping : List Nat) (sep : Str) :
    Nat → Nat → Nat → Bool → Int → Int → Str → Nat → Str → Py (Nat × Str)
  | 0, _, _, _, _, _, _, _, _ => .error .modelFuel
  | fuel + 1, i, prev, useSep, remaining, minWidth, digits, count, out =>
    let (len0, i, prev) := groupNext grouping i prev
    if len0 > 0 then
      let len : Int := min (len0 : Int) (max (max remaining minWidth) 1)
      let nZeros := max 0 (len - remaining)
      let nChars := max 0 (min remaining len)
      let count := count + (if useSep then sep.length else 0) + nZeros.toNat + nChars.toNat
      let (digits, out) := groupPieceFwd sep useSep nChars.toNat nZeros.toNat digits out
      let remaining := remaining - nChars
      let minWidth := minWidth - len
      if remaining ≤ 0 ∧ minWidth ≤ 0 then .ok (count, out)
      else
        groupLoopFwd grouping sep fuel i prev true remaining (minWidth - sep.length) digits
          count out
    else
      let len : Int := max (max remaining minWidth) 1
      let nZeros := max 0 (len - remaining)
      let nChars := max 0 (min remaining len)
      let count := count + (if useSep then sep.length else 0) + nZeros.toNat + nChars.toNat
      let (_, out) := groupPieceFwd sep useSep nChars.toNat nZeros.toNat digits out
      .ok (count, out)

/-- `_PyUnicode_InsertThousandsGrouping` with `forward` set: the count, the text. -/
def insertGroupingFwd (digits : Str) (minWidth : Int) (grouping : List Nat) (sep : Str) :
    Py (Nat × Str) :=
  groupLoopFwd grouping sep (digits.length + (max 0 minWidth).toNat + 2) 0 0 false digits.length
    (max 0 minWidth) digits 0 []

/-! ## The widths -/

/-- `NumberFieldWidths` with the text of each field. -/
structure NumFields where
  lpad : Nat
  sign : Option Nat
  spad : Nat
  grouped : Str
  decimal : Str
  fracGrouped : Str
  remainder : Str
  rpad : Nat
  deriving Repr, DecidableEq

/-- The `switch (format->sign)` of `calc_number_widths`, formatter_unicode.c:565-580. -/
def signField (sign signChar : Nat) : Option Nat :=
  if sign == 43 then some (if signChar == 45 then 45 else 43)
  else if sign == 32 then some (if signChar == 45 then 45 else 32)
  else if signChar == 45 then some 45
  else none

/-- The `switch (format->align)` of `calc_number_widths`, formatter_unicode.c:636-655:
`n_lpadding`, `n_spadding`, `n_rpadding` from `n_padding`. -/
def padFields (nPadding : Int) (align : Nat) : Nat × Nat × Nat :=
  if nPadding > 0 then
    let p := nPadding.toNat
    if align == 60 then (0, 0, p)
    else if align == 94 then (p / 2, 0, p - p / 2)
    else if align == 61 then (0, p, 0)
    else (p, 0, 0)
  else (0, 0, 0)

/-- `calc_number_widths`, formatter_unicode.c:524-668, for `n_prefix == 0`, which is
every float and complex call. -/
def calcNumberWidthsFull (signChar : Nat) (digits : Str) (hasDecimal : Bool) (frac remainder : Str)
    (loc : LocaleFull) (f : FormatSpec) : Py NumFields := do
  let nDecimal := if hasDecimal then loc.decimal.length else 0
  let sign := signField f.sign signChar
  let nSign := sign.toList.length
  let (nFracGrouped, fracGrouped) ←
    if frac.length = 0 then pure (0, [])
    else insertGroupingFwd frac frac.length loc.grouping loc.fracSep
  let nonDigit : Int := nSign + nDecimal + frac.length + remainder.length
  let minWidth : Int :=
    if f.fillChar == 48 && f.align == 61 then f.width - nonDigit + frac.length - nFracGrouped
    else 0
  let (nGrouped, grouped, _) ←
    if digits.length = 0 then pure (0, [], 0)
    else insertThousandsGrouping digits minWidth loc.grouping loc.sep
  let (l, s, r) := padFields (f.width - (nonDigit + nGrouped + nFracGrouped - frac.length)) f.align
  .ok { lpad := l, sign, spad := s, grouped
        decimal := if hasDecimal then loc.decimal else [], fracGrouped, remainder, rpad := r }

/-- `fill_number`, formatter_unicode.c:672-777, for `n_prefix == 0`, `toupper == 0`. -/
def fillNumberFull (n : NumFields) (fill : Nat) : Str :=
  List.replicate n.lpad fill ++ n.sign.toList ++ List.replicate n.spad fill ++ n.grouped ++
    n.decimal ++ n.fracGrouped ++ n.remainder ++ List.replicate n.rpad fill

/-! ## `format_float_internal` -/

/-- `PyOS_double_to_string` as text. `none` from the model is its fuel running out. -/
def doubleToString (x : F64) (code : Nat) (prec : Int) (fl : DtsFlags) : Py Str :=
  match PyOS_double_to_string x code prec fl with
  | none => .error .modelFuel
  | some r => .ok (render r.1)

/-- The sign of a buffer and what follows it, formatter_unicode.c:1240-1244. -/
def splitSign (buf : Str) : Nat × Str :=
  if buf.headD 0 == 45 then (45, buf.tail) else (0, buf)

/-- A buffer from `PyOS_double_to_string` laid out by the spec: the part of
`format_float_internal` after the fast path, formatter_unicode.c:1232-1279. -/
def formatFloatSlow (buf : Str) (f : FormatSpec) : Py Str := do
  let (signChar, body) := splitSign buf
  let (digits, hasDecimal, frac, remainder) := splitNumber body
  let loc := localeInfoFull (if f.type == 110 then LT_CURRENT_LOCALE else f.thousands)
    f.fracThousands
  let n ← calcNumberWidthsFull signChar digits hasDecimal frac remainder loc f
  .ok (fillNumberFull n f.fillChar)

/-- The test of the fast path, formatter_unicode.c:1222-1225. -/
def floatFastPath (f : FormatSpec) : Bool :=
  f.sign != 43 && f.sign != 32 && f.width == -1 && f.type != 110 &&
    f.thousands == LT_NO_LOCALE && f.fracThousands == LT_NO_LOCALE

/-- `format_float_internal`, formatter_unicode.c:1138-1285. -/
def formatFloatInternal (val0 : F64) (f : FormatSpec) : Py Str := do
  if f.precision > 2 ^ 31 - 1 then .error (.valueError "precision too big")
  else
    let flags0 : DtsFlags := { alt := f.alternate, no_neg_0 := f.noNeg0 }
    let (type0, flags, defaultPrecision) : Nat × DtsFlags × Int :=
      if f.type == 0 then (114, { flags0 with add_dot_0 := true }, 0) else (f.type, flags0, 6)
    let type1 := if type0 == 110 then 103 else type0
    let (type2, val, addPct) : Nat × F64 × Bool :=
      if type1 == 37 then (102, F64.mul val0 (F64.ofInt 100), true) else (type1, val0, false)
    let (precision, type3) : Int × Nat :=
      if f.precision < 0 then (defaultPrecision, type2)
      else (f.precision, if type2 == 114 then 103 else type2)
    let buf0 ← doubleToString val type3 precision flags
    let buf := if addPct then buf0 ++ [37] else buf0
    if floatFastPath f then .ok buf else formatFloatSlow buf f

/-- The `float` branch of `_PyLong_FormatAdvancedWriter` after `PyNumber_Float`,
formatter_unicode.c:1630-1640: `formatLongAdvanced` stops with `none` here. -/
def formatLongAsFloat (v : Int) (spec : Str) (name : String) : Py Str := do
  let f ← parseFormatSpec name spec 100 62
  formatFloatInternal (F64.ofInt v) f

/-- `_PyFloat_FormatAdvancedWriter`, formatter_unicode.c:1652-1688. The empty spec is
`str(obj)`. -/
def formatFloatAdvanced (val : F64) (spec : Str) : Py Str := do
  match ← formatFloatDispatch spec with
  | none =>
    match float_repr val with
    | none => .error .modelFuel
    | some s => .ok s
  | some f => formatFloatInternal val f

/-! ## `format_complex_internal` -/

/-- `format_complex_internal`, formatter_unicode.c:1291-1534. -/
def formatComplexInternal (re im : F64) (f : FormatSpec) : Py Str := do
  if f.precision > 2 ^ 31 - 1 then .error (.valueError "precision too big")
  else if f.fillChar == 48 then
    .error (.valueError "Zero padding is not allowed in complex format specifier")
  else if f.align == 61 then
    .error (.valueError "'=' alignment flag is not allowed in complex format specifier")
  else
    let flags : DtsFlags := { alt := f.alternate, no_neg_0 := f.noNeg0 }
    let (type0, defaultPrecision, skipRe, addParens) : Nat × Int × Bool × Bool :=
      if f.type == 0 then
        if F64.eq re d0 && !re.sign then (114, 0, true, false) else (114, 0, false, true)
      else (f.type, 6, false, false)
    let type1 := if type0 == 110 then 103 else type0
    let (precision, type2) : Int × Nat :=
      if f.precision < 0 then (defaultPrecision, type1)
      else (f.precision, if type1 == 114 then 103 else type1)
    let reBuf ← doubleToString re type2 precision flags
    let imBuf ← doubleToString im type2 precision flags
    let (reSign, reBody) := splitSign reBuf
    let (imSign, imBody) := splitSign imBuf
    let (reDigits, reDec, reFrac, reRem) := splitNumber reBody
    let (imDigits, imDec, imFrac, imRem) := splitNumber imBody
    let loc := localeInfoFull (if f.type == 110 then LT_CURRENT_LOCALE else f.thousands)
      f.fracThousands
    let tmp := { f with fillChar := 0, align := 60, width := -1 }
    let reN ← calcNumberWidthsFull reSign reDigits reDec reFrac reRem loc tmp
    let tmp2 := if skipRe then tmp else { tmp with sign := 43 }
    let imN ← calcNumberWidthsFull imSign imDigits imDec imFrac imRem loc tmp2
    let reText := if skipRe then [] else fillNumberFull reN 0
    let imText := fillNumberFull imN 0
    let content := (if addParens then [40] else []) ++ reText ++ imText ++ [106] ++
      (if addParens then [41] else [])
    let (l, r, _) := calcPadding content.length f.width f.align
    .ok (fillPadding content f.fillChar l r)

/-- `_PyComplex_FormatAdvancedWriter`, formatter_unicode.c:1691-1726. The empty spec is
`str(obj)`. -/
def formatComplexAdvanced (re im : F64) (spec : Str) : Py Str := do
  match ← formatComplexDispatch spec with
  | none =>
    match complex_repr ⟨re, im⟩ with
    | none => .error .modelFuel
    | some s => .ok s
  | some f => formatComplexInternal re im f

end PyLean.UnicodeObj
