import PyLean.UnicodeObj.FormatSpec

/-!
`format(s, spec)` for a `str` against the format-specification mini-language
(Doc/library/string.rst): the spec `fill align width [. precision] s` truncates to the precision
and pads to the width, on the model of `FormatSpec.lean` (`formatStrAdvanced`,
`parse_internal_render_format_spec`, `get_integer`, `calc_padding`, `fill_padding`,
`format_string_internal`, Objects/unicode_formatter.c).
-/

namespace PyLean.UnicodeObj

open PyLean

/-- The text kept: the first `precision` characters, or all of them. -/
def keptText (s : Str) : Option Int → Str
  | some p => s.take p.toNat
  | none => s

/-- The documented result: truncate to the precision, then pad with `fill` to the width, on the
right for `<`, on the left for `>`, around for `^` (the extra fill on the right). -/
def docFormat (s : Str) (fill align : Nat) (width : Int) (prec : Option Int) : Str :=
  let t := keptText s prec
  let pad := width.toNat - t.length
  if align == 60 then t ++ List.replicate pad fill
  else if align == 62 then List.replicate pad fill ++ t
  else List.replicate (pad / 2) fill ++ t ++ List.replicate (pad - pad / 2) fill

/-- The value of ASCII decimal digits. -/
def accum (acc : Int) (ds : List Nat) : Int := ds.foldl (fun (a : Int) (d : Nat) => a * 10 + (d : Int)) acc

def asciiDigits (ds : List Nat) : Str := ds.map (· + 48)

/-- For every string, fill character, alignment `<`, `>` or `^`, width in ASCII digits and optional
precision in ASCII digits (each at most `sys.maxsize`),
`format(s, fill + align + width [+ '.' + precision] + 's')` is the documented truncation and
padding. -/
def StrFormatDoc : Prop :=
  ∀ (s : Str) (fill align : Nat) (wd : List Nat) (pd : Option (List Nat)),
    (align = 60 ∨ align = 62 ∨ align = 94) →
    wd ≠ [] → (∀ d ∈ wd, d < 10) → accum 0 wd ≤ ssizeMax →
    (∀ p, pd = some p → p ≠ [] ∧ (∀ d ∈ p, d < 10) ∧ accum 0 p ≤ ssizeMax) →
    formatStrAdvanced s ([fill, align] ++ asciiDigits wd ++
        (match pd with | some p => 46 :: asciiDigits p | none => []) ++ [115])
      = .ok (docFormat s fill align (accum 0 wd) (pd.map (accum 0)))

theorem toDec_digit (d : Nat) (h : d < 10) : toDecimalDigit (d + 48) = d := by
  revert d; decide

theorem accum_mono (ds : List Nat) (acc : Int) (h : 0 ≤ acc) : acc ≤ accum acc ds := by
  induction ds generalizing acc with
  | nil => simp [accum]
  | cons x xs ih =>
    simp only [accum, List.foldl_cons]
    exact Int.le_trans (by omega) (ih _ (by omega))

/-- `get_integer` reads ASCII digits exactly, stopping at a non-digit. -/
theorem getInteger_digits (ds : List Nat) (rest : List Nat) (acc : Int) (n : Nat) (h0 : 0 ≤ acc)
    (hds : ∀ d ∈ ds, d < 10) (hstop : ∀ x ∈ rest.head?, toDecimalDigit x < 0)
    (hbig : accum acc ds ≤ ssizeMax) :
    getInteger (asciiDigits ds ++ rest) acc n = .ok (accum acc ds, n + ds.length, rest) := by
  induction ds generalizing n acc with
  | nil =>
    cases rest with
    | nil => rfl
    | cons x r =>
      have := hstop x (by simp)
      simp [asciiDigits, getInteger, this, accum]
  | cons d ds ih =>
    have hd := hds d (by simp)
    have hle := accum_mono ds (acc * 10 + d) (by omega)
    simp only [accum, List.foldl_cons] at hbig hle
    simp only [asciiDigits, List.map_cons, List.cons_append, getInteger, toDec_digit d hd]
    rw [if_neg (by omega), if_neg (by omega)]
    have := ih (acc * 10 + d) (n + 1) (by omega) (fun x hx => hds x (by simp [hx])) hbig
    simp only [asciiDigits] at this
    rw [this]
    simp only [accum, List.foldl_cons, List.length_cons, show n + 1 + ds.length = n + (ds.length + 1) by omega]

theorem dot_nondigit : toDecimalDigit 46 < 0 := by decide
theorem s_nondigit : toDecimalDigit 115 < 0 := by decide

/-- The head parse: fill and alignment given, so no sign, `z`, `#` or zero-padding is taken from the
digits that follow. -/
theorem parseHead_spec (fill align : Nat) (d : Nat) (rest : List Nat) (hal : isAlignmentToken align = true)
    (hd : d < 10) :
    parseHead (fill :: align :: (d + 48) :: rest) 115 60 =
      ({ align := align, type := 115, fillChar := fill }, (d + 48) :: rest) := by
  have h1 : isSignElement (d + 48) = false := by revert d; decide
  have h2 : (d + 48 == 122) = false := by revert d; decide
  have h3 : (d + 48 == 35) = false := by revert d; decide
  simp [parseHead, parseAlign, hal, parseFlags, h1, headIs, h2, h3]

/-- The spec `fill align width [. precision] s` parses to. -/
def docSpec (fill align : Nat) (w p : Int) : FormatSpec :=
  { fillChar := fill, align := align, width := w, thousands := 0, precision := p, fracThousands := 0, type := 115 }

/-- `format_string_internal` with no sign, `z`, `#` or `=`, a width and an optional precision, both
non-negative: the documented truncation and padding. -/
theorem fsi_doc (s : Str) (fill align : Nat) (w : Int) (po : Option Int) (hw : 0 ≤ w)
    (hp : ∀ p, po = some p → 0 ≤ p) (halign : align = 60 ∨ align = 62 ∨ align = 94) :
    formatStringInternal s (docSpec fill align w (po.getD (-1))) = .ok (docFormat s fill align w po) := by
  have h61 : align ≠ 61 := by omega
  have hcontent : (if po.getD (-1) ≥ 0 ∧ (s.length : Int) ≥ po.getD (-1) then s.take (po.getD (-1)).toNat else s)
      = keptText s po := by
    cases po with
    | none => simp [keptText]
    | some p =>
      have := hp p rfl
      simp only [Option.getD_some, keptText]
      split
      · rfl
      · rw [List.take_of_length_le (by omega)]
  unfold formatStringInternal docSpec docFormat
  simp only [show ((0 : Nat) != 0) = false from rfl, Bool.false_eq_true, if_false,
    show ((align == 61) = true) ↔ False by simp [h61]]
  split
  · rename_i hfast
    simp only [beq_iff_eq] at hfast
    have ht : keptText s po = s := by
      cases po with
      | none => rfl
      | some p =>
        have := hp p rfl
        simp only [Option.getD_some] at hfast
        show s.take p.toNat = s
        exact List.take_of_length_le (by omega)
    have hpad : w.toNat - s.length = 0 := by omega
    simp only [ht, hpad]
    rcases halign with h | h | h <;> subst h <;> (try simp)
  · rw [hcontent]
    generalize keptText s po = t
    unfold calcPadding fillPadding
    have htot : (if ((t.length : Int) > w) then t.length else w.toNat) - t.length = w.toNat - t.length := by
      split <;> omega
    simp only [show w ≥ 0 from hw, if_true, htot]
    rcases halign with h | h | h <;> subst h <;> simp [htot]

theorem strFormatDoc_proven : StrFormatDoc := by
  intro s fill align wd pd halign hwne hwd hwbig hpd
  have hal : isAlignmentToken align = true := by rcases halign with h | h | h <;> subst h <;> decide
  obtain ⟨d, ds, rfl⟩ : ∃ d ds, wd = d :: ds := by cases wd with | nil => exact absurd rfl hwne | cons d ds => exact ⟨d, ds, rfl⟩
  have hd := hwd d (by simp)
  have hhead := parseHead_spec fill align d (asciiDigits ds ++ ((match pd with | some p => 46 :: asciiDigits p | none => []) ++ [115])) hal hd
  unfold formatStrAdvanced parseFormatSpec
  simp only [asciiDigits, List.map_cons, List.cons_append, List.nil_append, List.singleton_append, List.append_assoc] at hhead ⊢
  rw [hhead]
  have hstop : ∀ x ∈ ((match pd with | some p => 46 :: asciiDigits p | none => []) ++ [115]).head?,
      toDecimalDigit x < 0 := by
    cases pd <;> simp [dot_nondigit, s_nondigit]
  have hw := getInteger_digits (d :: ds) _ 0 0 (Int.le_refl _) hwd hstop hwbig
  simp only [asciiDigits, List.map_cons, List.cons_append] at hw
  cases pd with
  | none =>
    simp only [List.append_nil, List.nil_append, Nat.zero_add] at hw ⊢
    simp [List.isEmpty, parseTail, parseWidth, hw, headIs, bind, Except.bind, pure, Except.pure, parseType,
      validateSpec, LT_NO_LOCALE]
    exact fsi_doc s fill align _ none (accum_mono _ 0 (Int.le_refl _)) (by simp) halign
  | some pp =>
    obtain ⟨hpne, hpd', hpbig⟩ := hpd pp rfl
    simp only [List.nil_append, Nat.zero_add, List.cons_append] at hw ⊢
    have hp := getInteger_digits pp [115] 0 0 (Int.le_refl _) hpd' (by simp [s_nondigit]) hpbig
    simp only [asciiDigits, Nat.zero_add] at hp
    simp [List.isEmpty, parseTail, parseWidth, hw, headIs, bind, Except.bind, pure, Except.pure, parseType,
      validateSpec, LT_NO_LOCALE, parsePrecision, hp, hpne]
    exact fsi_doc s fill align _ (some _) (accum_mono _ 0 (Int.le_refl _))
      (by intro q hq; cases hq; exact accum_mono _ 0 (Int.le_refl _)) halign


/-! ## Errors -/

/-- A one-character spec that is none of the mini-language's other fields. -/
def PlainType (t : Nat) : Prop :=
  isAlignmentToken t = false ∧ isSignElement t = false ∧ t ≠ 122 ∧ t ≠ 35 ∧ toDecimalDigit t < 0 ∧
  t ≠ 44 ∧ t ≠ 95 ∧ t ≠ 46 ∧ t ≠ 115

/-- `format(s, t)` with an unknown presentation type `t` raises "Unknown format code ..." (with
`\x..` for a character outside 33..127), for every string; and the grouping options that strings
refuse raise their messages: both `,` and `_`, or either alone (the default type is `s`). -/
def StrFormatErrors : Prop :=
  (∀ (s : Str) (t : Nat), PlainType t → formatStrAdvanced s [t] = .error (unknownPresentationType t "str")) ∧
  (∀ s : Str, formatStrAdvanced s [44, 95] = .error invalidCommaAndUnderscore ∧
    formatStrAdvanced s [95, 44] = .error invalidCommaAndUnderscore ∧
    formatStrAdvanced s [44] = .error (invalidThousandsSeparatorType 44 115) ∧
    formatStrAdvanced s [95] = .error (invalidThousandsSeparatorType 95 115) ∧
    formatStrAdvanced s [44, 115] = .error (invalidThousandsSeparatorType 44 115) ∧
    formatStrAdvanced s [95, 115] = .error (invalidThousandsSeparatorType 95 115))

theorem strFormatErrors_proven : StrFormatErrors := by
  refine ⟨fun s t ht => ?_, fun s => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ht
    have g : getInteger [t] 0 0 = .ok (0, 0, [t]) := by simp [getInteger, h5]
    have h48 : t ≠ 48 := by intro h; subst h; revert h5; decide
    simp [formatStrAdvanced, parseFormatSpec, parseHead, parseAlign, h1, parseFlags, h2, headIs, h3, h4, h48,
      parseTail, parseWidth, g, h6, h7, h8, parseType, validateSpec, LT_NO_LOCALE, h9, bind, Except.bind,
      pure, Except.pure]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end PyLean.UnicodeObj
