import PyLean.UnicodeObj.FormatNumber
import PyLean.UnicodeObj.StrFormatDoc

/-!
The error paths of float and complex formatting, Objects/unicode_formatter.c:
`format_float_internal` (:1376-1523), `format_complex_internal` (:1529-1772),
`_PyFloat_FormatAdvancedWriter` (:1890-1926) and `_PyComplex_FormatAdvancedWriter` (:1929-1964).
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

/-- A one-character spec that is no mini-language field other than a type. -/
def PlainChar (t : Nat) : Prop :=
  isAlignmentToken t = false ∧ isSignElement t = false ∧ t ≠ 122 ∧ t ≠ 35 ∧ toDecimalDigit t < 0 ∧
  t ≠ 44 ∧ t ≠ 95 ∧ t ≠ 46

/-- The types `_PyFloat_FormatAdvancedWriter` accepts: e E f F g G n %. -/
def floatTypes : List Nat := [101, 69, 102, 70, 103, 71, 110, 37]
/-- The types `_PyComplex_FormatAdvancedWriter` accepts: the float ones but `%`. -/
def complexTypes : List Nat := [101, 69, 102, 70, 103, 71, 110]

/-- The refusals of float and complex formatting, in the order the source makes them: a precision
above `INT_MAX`; for complex, then zero padding, then `=` alignment; and for both an unknown
presentation type, for every value. The type character NUL is the one exception: see
`NulTypeRejected`. -/
def FloatComplexErrors : Prop :=
  (∀ (x : F64) (f : FormatSpec), f.precision > 2 ^ 31 - 1 →
    formatFloatInternal x f = .error (.valueError "precision too big")) ∧
  (∀ (re im : F64) (f : FormatSpec), f.precision > 2 ^ 31 - 1 →
    formatComplexInternal re im f = .error (.valueError "precision too big")) ∧
  (∀ (re im : F64) (f : FormatSpec), f.precision ≤ 2 ^ 31 - 1 → f.fillChar = 48 →
    formatComplexInternal re im f = .error (.valueError "Zero padding is not allowed in complex format specifier")) ∧
  (∀ (re im : F64) (f : FormatSpec), f.precision ≤ 2 ^ 31 - 1 → f.fillChar ≠ 48 → f.align = 61 →
    formatComplexInternal re im f =
      .error (.valueError "'=' alignment flag is not allowed in complex format specifier")) ∧
  (∀ (x : F64) (t : Nat), PlainChar t → t ≠ 0 → t ∉ floatTypes →
    formatFloatAdvanced x [t] = .error (unknownPresentationType t "float")) ∧
  (∀ (re im : F64) (t : Nat), PlainChar t → t ≠ 0 → t ∉ complexTypes →
    formatComplexAdvanced re im [t] = .error (unknownPresentationType t "complex"))

theorem plainChar_parse (name : String) (t dt : Nat) (ht : PlainChar t) :
    parseFormatSpec name [t] dt 62 = .ok { align := 62, type := t } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ht
  have g : getInteger [t] 0 0 = .ok (0, 0, [t]) := by simp [getInteger, h5]
  have h48 : t ≠ 48 := by intro h; subst h; revert h5; decide
  have hn : (t == 110 && (0 : Nat) != LT_NO_LOCALE) = false := by simp [LT_NO_LOCALE]
  simp [parseFormatSpec, parseHead, parseAlign, h1, parseFlags, h2, headIs, h3, h4, h48, parseTail,
    parseWidth, g, h6, h7, h8, parseType, validateSpec, LT_NO_LOCALE, bind, Except.bind, pure, Except.pure]

theorem floatComplexErrors_proven : FloatComplexErrors := by
  refine ⟨fun x f h => ?_, fun re im f h => ?_, fun re im f h0 h => ?_, fun re im f h0 h1 h => ?_,
    fun x t ht h0 hn => ?_, fun re im t ht h0 hn => ?_⟩
  · simp [formatFloatInternal, show f.precision > 2147483647 by omega]
  · simp [formatComplexInternal, show f.precision > 2147483647 by omega]
  · simp [formatComplexInternal, show ¬ f.precision > 2147483647 by omega, h]
  · simp [formatComplexInternal, show ¬ f.precision > 2147483647 by omega, h1, h]
  · have hp := plainChar_parse "float" t 0 ht
    simp only [floatTypes, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := hn
    simp [formatFloatAdvanced, formatFloatDispatch, hp, bind, Except.bind, n1, n2, n3, n4, n5, n6, n7, n8, h0]
  · have hp := plainChar_parse "complex" t 0 ht
    simp only [complexTypes, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hn
    simp [formatComplexAdvanced, formatComplexDispatch, hp, bind, Except.bind, n1, n2, n3, n4, n5, n6, n7, h0]

/-- The documented presentation types of float and complex are e E f F g G n % and none (an empty
type field). `format(1, '\x00')` and `format('a', '\x00')` raise "Unknown format code '\x0'", as
`_pydecimal` and `Fraction` raise for it, but `_PyFloat_FormatAdvancedWriter` and
`_PyComplex_FormatAdvancedWriter` (unicode_formatter.c:1909-1918, 1948-1956) take a literal NUL type
character for the `'\0'` that `parse_internal_render_format_spec` stores when the type field is
absent, and format the value: `format(1.5, '\x00') == '1.5'`. Refuted at `t = 0`. -/
def NulTypeRejected : Prop :=
  (∀ t : Nat, PlainChar t → t ∉ floatTypes →
    formatFloatDispatch [t] = .error (unknownPresentationType t "float")) ∧
  (∀ t : Nat, PlainChar t → t ∉ complexTypes →
    formatComplexDispatch [t] = .error (unknownPresentationType t "complex"))

theorem plainChar_zero : PlainChar 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem nulTypeRejected_refuted : ¬ NulTypeRejected := by
  intro ⟨h, _⟩
  have := h 0 plainChar_zero (by decide)
  simp [formatFloatDispatch, plainChar_parse "float" 0 0 plainChar_zero, bind, Except.bind] at this

/-- The int side of the comparison: a NUL type character is an unknown type for `int`. -/
theorem int_nul_rejected (v : Int) (e : Str) :
    formatLongAdvanced v "int" [0] e = .error (unknownPresentationType 0 "int") := by
  have hp := plainChar_parse "int" 0 100 plainChar_zero
  simp [formatLongAdvanced, hp, bind, Except.bind]

end PyLean.UnicodeObj
