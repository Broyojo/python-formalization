import PyLean.UnicodeObj.FormatSpec
import PyLean.Binary64.Complex

/-!
`format()` of a `float` or `complex`: `format_float_internal` and
`format_complex_internal`, Objects/unicode_formatter.c:1375-1778, over the exact binary64
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

/-- `parse_number`, unicode_formatter.c:724-751: the digits before the point,
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

/-- `get_locale_info`, unicode_formatter.c:1021-1081, in the C locale. A fraction
separator turns grouping on when the integer part has none: `no_grouping` is the
`LT_NO_LOCALE` case. -/
def localeInfoFull (type fracType : Nat) : LocaleFull :=
  let (sep, grouping) := localeInfo type
  if fracType != LT_NO_LOCALE then
    { sep, fracSep := [if fracType == LT_DEFAULT_LOCALE then 44 else 95]
      grouping := if type == LT_NO_LOCALE then [3] else grouping }
  else { sep, fracSep := [], grouping }

/-! ## Forward grouping -/

/-- One call of `InsertThousandsGrouping_fill` with `forward` set, unicode_formatter.c:56-108:
separator, digits, zeros, after what is already there. -/
def groupPieceFwd (sep : Str) (useSep : Bool) (nChars nZeros : Nat) (digits out : Str) :
    Str × Str :=
  (digits.drop nChars,
   out ++ (if useSep then sep else []) ++ digits.take nChars ++ List.replicate nZeros 48)

/-- The `while` loop of `_PyUnicode_InsertThousandsGrouping` with `forward` set,
unicode_formatter.c:193-234. -/
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

/-- The `switch (format->sign)` of `calc_number_widths`, unicode_formatter.c:800-815. -/
def signField (sign signChar : Nat) : Option Nat :=
  if sign == 43 then some (if signChar == 45 then 45 else 43)
  else if sign == 32 then some (if signChar == 45 then 45 else 32)
  else if signChar == 45 then some 45
  else none

/-- The `switch (format->align)` of `calc_number_widths`, unicode_formatter.c:871-890:
`n_lpadding`, `n_spadding`, `n_rpadding` from `n_padding`. -/
def padFields (nPadding : Int) (align : Nat) : Nat × Nat × Nat :=
  if nPadding > 0 then
    let p := nPadding.toNat
    if align == 60 then (0, 0, p)
    else if align == 94 then (p / 2, 0, p - p / 2)
    else if align == 61 then (0, p, 0)
    else (p, 0, 0)
  else (0, 0, 0)

/-- The fraction digits, unicode_formatter.c:819-830. -/
def groupedFrac (frac : Str) (loc : LocaleFull) : Py (Nat × Str) :=
  if frac.length = 0 then pure (0, [])
  else insertGroupingFwd frac frac.length loc.grouping loc.fracSep

/-- The integer digits, unicode_formatter.c:842-856. No digit at all happens for `inf` and
`nan`, whose text is the remainder. -/
def groupedDigits (digits : Str) (minWidth : Int) (loc : LocaleFull) : Py (Nat × Str × Nat) :=
  if digits.length = 0 then pure (0, [], 0)
  else insertThousandsGrouping digits minWidth loc.grouping loc.sep

/-- `n_non_digit_non_padding`, unicode_formatter.c:832-834. -/
def nonDigitOf (sign : Option Nat) (decimal frac remainder : Str) : Int :=
  sign.toList.length + decimal.length + frac.length + remainder.length

/-- `n_min_width`, unicode_formatter.c:836-841. It is what is left for the integer digits
when a `0=` fill turns the padding into digits. -/
def minWidthOf (f : FormatSpec) (nonDigit : Int) (nFrac nFracGrouped : Nat) : Int :=
  if f.fillChar == 48 && f.align == 61 then f.width - nonDigit + nFrac - nFracGrouped else 0

/-- `calc_number_widths`, unicode_formatter.c:759-903, for `n_prefix == 0`, which is
every float and complex call. -/
def calcNumberWidthsFull (signChar : Nat) (digits : Str) (hasDecimal : Bool) (frac remainder : Str)
    (loc : LocaleFull) (f : FormatSpec) : Py NumFields := do
  let sign := signField f.sign signChar
  let decimal := if hasDecimal then loc.decimal else []
  let nonDigit := nonDigitOf sign decimal frac remainder
  let (nFracGrouped, fracGrouped) ← groupedFrac frac loc
  let minWidth := minWidthOf f nonDigit frac.length nFracGrouped
  let (nGrouped, grouped, _) ← groupedDigits digits minWidth loc
  let (l, s, r) := padFields (f.width - (nonDigit + nGrouped + nFracGrouped - frac.length)) f.align
  .ok { lpad := l, sign, spad := s, grouped, decimal, fracGrouped, remainder, rpad := r }

/-- `fill_number`, unicode_formatter.c:907-1012, for `n_prefix == 0`, `toupper == 0`. -/
def fillNumberFull (n : NumFields) (fill : Nat) : Str :=
  List.replicate n.lpad fill ++ n.sign.toList ++ List.replicate n.spad fill ++ n.grouped ++
    n.decimal ++ n.fracGrouped ++ n.remainder ++ List.replicate n.rpad fill

/-! ## `format_float_internal` -/

/-- `PyOS_double_to_string` as text. `none` from the model is its fuel running out. -/
def doubleToString (x : F64) (code : Nat) (prec : Int) (fl : DtsFlags) : Py Str :=
  match PyOS_double_to_string x code prec fl with
  | none => .error .modelFuel
  | some r => .ok (render r.1)

/-- The sign of a buffer and what follows it, unicode_formatter.c:1478-1482. -/
def splitSign (buf : Str) : Nat × Str :=
  if buf.headD 0 == 45 then (45, buf.tail) else (0, buf)

/-- A buffer from `PyOS_double_to_string` laid out by the spec: the part of
`format_float_internal` after the fast path, unicode_formatter.c:1470-1517. -/
def formatFloatSlow (buf : Str) (f : FormatSpec) : Py Str := do
  let (signChar, body) := splitSign buf
  let (digits, hasDecimal, frac, remainder) := splitNumber body
  let loc := localeInfoFull (if f.type == 110 then LT_CURRENT_LOCALE else f.thousands)
    f.fracThousands
  let n ← calcNumberWidthsFull signChar digits hasDecimal frac remainder loc f
  .ok (fillNumberFull n f.fillChar)

/-- The test of the fast path, unicode_formatter.c:1460-1463. -/
def floatFastPath (f : FormatSpec) : Bool :=
  f.sign != 43 && f.sign != 32 && f.width == -1 && f.type != 110 &&
    f.thousands == LT_NO_LOCALE && f.fracThousands == LT_NO_LOCALE

/-- `format_float_internal` up to the fast path test, unicode_formatter.c:1411-1458: the
buffer from `PyOS_double_to_string`, with the `%` of the `'%'` type. -/
def floatBuf (val0 : F64) (f : FormatSpec) : Py Str := do
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
  .ok (if addPct then buf0 ++ [37] else buf0)

/-- `format_float_internal`, unicode_formatter.c:1376-1523. -/
def formatFloatInternal (val0 : F64) (f : FormatSpec) : Py Str := do
  if f.precision > 2 ^ 31 - 1 then .error (.valueError "precision too big")
  else
    let buf ← floatBuf val0 f
    if floatFastPath f then .ok buf else formatFloatSlow buf f

/-- The `float` branch of `_PyLong_FormatAdvancedWriter` after `PyNumber_Float`,
unicode_formatter.c:1868-1878: `formatLongAdvanced` stops with `none` here. -/
def formatLongAsFloat (v : Int) (spec : Str) (name : String) : Py Str := do
  let f ← parseFormatSpec name spec 100 62
  formatFloatInternal (F64.ofInt v) f

/-- `PyNumber_Float` of an exact `int`: `long_float`, which raises once the int rounds to
infinity, from `2**1024 - 2**970` up. -/
def pyNumberFloatLong (v : Int) : Py F64 :=
  if v.natAbs ≥ 2 ^ 1024 - 2 ^ 970 then .error (.overflowError "int too large to convert to float")
  else .ok (F64.ofInt v)

/-- `_PyLong_FormatAdvancedWriter`, unicode_formatter.c:1828-1887, for an `int` (or subclass)
instance of value `v`. `tpName` is `Py_TYPE(obj)->tp_name`, `exact` is `PyLong_CheckExact(obj)`,
`strObj` is `PyObject_Str(obj)` (what `format_obj` writes) and `toFloat` is `PyNumber_Float(obj)`,
which for a subclass can run its `__float__` and raise. For an exact int, the empty spec is
`_PyLong_FormatWriter(writer, obj, 10, 0)`. -/
def formatLongAdvancedObj (tpName : String) (exact : Bool) (strObj : Py Str) (toFloat : Py F64)
    (v : Int) (spec : Str) : Py Str := do
  if spec.isEmpty then
    if exact then longFormat v 10 false else formatObj strObj
  else
    let f ← parseFormatSpec tpName spec 100 62
    let t := f.type
    if t == 98 || t == 99 || t == 100 || t == 111 || t == 120 || t == 88 || t == 110 then
      formatLongInternal v f exact
    else if t == 101 || t == 69 || t == 102 || t == 70 || t == 103 || t == 71 || t == 37 then do
      let x ← toFloat
      formatFloatInternal x f
    else .error (unknownPresentationType t tpName)

/-- `_PyFloat_FormatAdvancedWriter`, unicode_formatter.c:1890-1926, for a `float` (or subclass)
instance of value `val`: an empty spec is `format_obj`, whatever the type. -/
def formatFloatAdvancedObj (tpName : String) (strObj : Py Str) (val : F64) (spec : Str) :
    Py Str := do
  match ← formatFloatDispatch spec tpName with
  | none => formatObj strObj
  | some f => formatFloatInternal val f

/-- `str()` of an exact float: `float_repr`. `none` from the model is its fuel running out. -/
def floatStr (val : F64) : Py Str :=
  match float_repr val with
  | none => .error .modelFuel
  | some s => .ok s

/-- `format(x, spec)` for an exact `float`. -/
def formatFloatAdvanced (val : F64) (spec : Str) : Py Str :=
  formatFloatAdvancedObj "float" (floatStr val) val spec

/-! ## `format_complex_internal` -/

/-- What `format_complex_internal` does with its two buffers, unicode_formatter.c:1658-1762.
`formatFloatSlow` is the `parse_number`, `calc_number_widths` and `fill_number` it runs on each
part, with padding off (`tmp_format`), in that order; `fill_number` cannot fail on the sizes
`calc_number_widths` returned, so writing the parts after both are measured changes nothing. -/
def complexRest (reBuf imBuf : Str) (f : FormatSpec) (skipRe addParens : Bool) : Py Str := do
  let tmp := { f with fillChar := 0, align := 60, width := -1 }
  let reText ← formatFloatSlow reBuf tmp
  let imText ← formatFloatSlow imBuf (if skipRe then tmp else { tmp with sign := 43 })
  let content := (if addParens then [40] else []) ++ (if skipRe then [] else reText) ++ imText ++
    [106] ++ (if addParens then [41] else [])
  let (l, r, _) := calcPadding content.length f.width f.align
  .ok (fillPadding content f.fillChar l r)

/-- `format_complex_internal`, unicode_formatter.c:1529-1772. -/
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
    let precision : Int := if f.precision < 0 then defaultPrecision else f.precision
    let type2 := if f.precision < 0 then type1 else if type1 == 114 then 103 else type1
    let reBuf ← doubleToString re type2 precision flags
    let imBuf ← doubleToString im type2 precision flags
    complexRest reBuf imBuf f skipRe addParens

/-- `_PyComplex_FormatAdvancedWriter`, unicode_formatter.c:1929-1964, for a `complex` (or
subclass) instance: an empty spec is `format_obj`, whatever the type. -/
def formatComplexAdvancedObj (tpName : String) (strObj : Py Str) (re im : F64) (spec : Str) :
    Py Str := do
  match ← formatComplexDispatch spec tpName with
  | none => formatObj strObj
  | some f => formatComplexInternal re im f

/-- `str()` of an exact complex: `complex_repr`. -/
def complexStr (re im : F64) : Py Str :=
  match complex_repr ⟨re, im⟩ with
  | none => .error .modelFuel
  | some s => .ok s

/-- `format(z, spec)` for an exact `complex`. -/
def formatComplexAdvanced (re im : F64) (spec : Str) : Py Str :=
  formatComplexAdvancedObj "complex" (complexStr re im) re im spec

end PyLean.UnicodeObj
