import PyLean.UnicodeObj.StrFormatDoc
import PyLean.UnicodeObj.FormatProps

/-!
`format(n, fill + align + width + 'd')` against `format(str(n), fill + align + width + 's')`: with
`<`, `>` or `^` an int is laid out like its decimal string. On the model of `FormatSpec.lean`:
`_PyLong_FormatAdvancedWriter` (`formatLongAdvanced`), `format_long_internal`, the slow path's
`calc_number_widths` and `fill_number`, Objects/unicode_formatter.c.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `str(n)` for an int within the int/str digit limit: a `-`, then the decimal digits. -/
def decimalStr (v : Int) : Str := (if v < 0 then [45] else []) ++ digitsOf 10 v.natAbs

/-- The head parse with any defaults, fill and alignment given. -/
theorem parseHead_spec' (fill align : Nat) (d : Nat) (rest : List Nat) (dt da : Nat)
    (hal : isAlignmentToken align = true) (hd : d < 10) :
    parseHead (fill :: align :: (d + 48) :: rest) dt da =
      ({ align := align, type := dt, fillChar := fill }, (d + 48) :: rest) := by
  have h1 : isSignElement (d + 48) = false := by revert d; decide
  have h2 : (d + 48 == 122) = false := by revert d; decide
  have h3 : (d + 48 == 35) = false := by revert d; decide
  simp [parseHead, parseAlign, hal, parseFlags, h1, headIs, h2, h3]

theorem d_nondigit : toDecimalDigit 100 < 0 := by decide

/-- For every int `n` within the 4300-digit limit, every fill character, alignment `<`, `>` or
`^` and width in ASCII digits (at most `sys.maxsize`), `format(n, fill + align + width + 'd')` is
the documented padding of `str(n)`, and so equals `format(str(n), fill + align + width + 's')`. -/
def IntFormatAsStr : Prop :=
  ∀ (v : Int) (fill align : Nat) (wd : List Nat) (emptyStr : Str),
    (align = 60 ∨ align = 62 ∨ align = 94) →
    wd ≠ [] → (∀ d ∈ wd, d < 10) → accum 0 wd ≤ ssizeMax → (digitsOf 10 v.natAbs).length ≤ 4300 →
    formatLongAdvanced v "int" ([fill, align] ++ asciiDigits wd ++ [100]) emptyStr
      = .ok (some (docFormat (decimalStr v) fill align (accum 0 wd) none)) ∧
    formatStrAdvanced (decimalStr v) ([fill, align] ++ asciiDigits wd ++ [115])
      = .ok (docFormat (decimalStr v) fill align (accum 0 wd) none)

theorem intFormatAsStr_proven : IntFormatAsStr := by
  intro v fill align wd emptyStr halign hwne hwd hwbig hlim
  refine ⟨?_, by
    have := strFormatDoc_proven (decimalStr v) fill align wd none halign hwne hwd hwbig (by simp)
    simpa using this⟩
  have hal : isAlignmentToken align = true := by rcases halign with h | h | h <;> subst h <;> decide
  have h61 : align ≠ 61 := by omega
  obtain ⟨d, ds, rfl⟩ : ∃ d ds, wd = d :: ds := by
    cases wd with | nil => exact absurd rfl hwne | cons d ds => exact ⟨d, ds, rfl⟩
  have hd := hwd d (by simp)
  have hhead := parseHead_spec' fill align d (asciiDigits ds ++ [100]) 100 62 hal hd
  have hw := getInteger_digits (d :: ds) [100] 0 0 (Int.le_refl _) hwd (by simp [d_nondigit]) hwbig
  have hw0 : 0 ≤ accum 0 (d :: ds) := accum_mono _ 0 (Int.le_refl _)
  unfold formatLongAdvanced parseFormatSpec
  simp only [asciiDigits, List.map_cons, List.cons_append, List.nil_append, List.append_assoc] at hhead hw ⊢
  rw [hhead]
  simp [List.isEmpty, parseTail, parseWidth, hw, headIs, bind, Except.bind, pure, Except.pure, parseType,
    validateSpec, LT_NO_LOCALE]
  -- format_long_internal: no precision, no z, type 'd', a width, so the slow path
  have hwne1 : accum 0 (d :: ds) ≠ -1 := by omega
  obtain ⟨hdne, hdm⟩ := digitsOf_spec 10 v.natAbs
  simp only [formatLongInternal, formatLongSlow, longFormat, hwne1, Functor.map, Except.map]
  simp [hlim, bind, Except.bind, pure, Except.pure, localeInfo, LT_CURRENT_LOCALE, LT_DEFAULT_LOCALE,
    LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]
  rw [if_neg hwne1, if_neg (by omega)]
  generalize hds : digitsOf 10 v.natAbs = D at hdne hdm
  generalize hW : accum 0 (d :: ds) = W at hw0 hwne1
  have hD0 : (D.head? == some 45) = false := by
    cases D with
    | nil => exact absurd rfl hdne
    | cons x xs => simpa using hdm x (by simp)
  have hng := noGroup D hdne 0 (Int.le_refl 0)
  have hfill : ((fill == 48 && align == 61) = true) ↔ False := by simp [h61]
  by_cases hv : v < 0
  · simp only [hv, if_true, List.cons_append, List.nil_append, List.head?_cons, List.tail_cons]
    simp [calcNumberWidths, hfill, hng, bind, Except.bind, pure, Except.pure, fillNumber, docFormat, decimalStr,
      hv, hds, keptText, hdne]
    have e1 : (W - (1 + (D.length : Int))).toNat = W.toNat - (D.length + 1) := by omega
    by_cases hp : 1 + (D.length : Int) < W
    · rcases halign with h | h | h <;> subst h <;> simp [hp, e1]
    · have e0 : W.toNat - (D.length + 1) = 0 := by omega
      rcases halign with h | h | h <;> subst h <;> simp [hp, e0]
  · have hD0' : D.head? ≠ some 45 := by simpa using hD0
    simp only [hv, if_false, List.nil_append, hD0]
    simp [hD0', calcNumberWidths, hfill, hng, bind, Except.bind, pure, Except.pure, fillNumber, docFormat, decimalStr,
      hv, hds, keptText, hdne]
    have e1 : (W - (D.length : Int)).toNat = W.toNat - D.length := by omega
    by_cases hp : (D.length : Int) < W
    · rcases halign with h | h | h <;> subst h <;> simp [hp, e1]
    · have e0 : W.toNat - D.length = 0 := by omega
      rcases halign with h | h | h <;> subst h <;> simp [hp, e0]

end PyLean.UnicodeObj
