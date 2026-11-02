import PyLean.UnicodeObj.FormatSpec
import PyLean.UnicodeObj.FormatParseDoc

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
  unfold formatStrAdvanced formatStrAdvancedObj parseFormatSpec
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


/-! ## Every spec -/

/-- `format(s, spec)` for a parsed spec as the docs describe it: a sign, `z`, `#` or `=` is refused
with its message (in the order unicode_formatter.c:1109-1144 tests them), and otherwise the text is
cut to the precision and padded to the width with the fill, on the right for `<`, the left for `>`,
around for `^` (the odd one on the right). No width means no padding. -/
def docStr (value : Str) (f : FormatSpec) : Py Str :=
  if f.sign ≠ 0 then
    .error (.valueError (if f.sign = 32 then "Space not allowed in string format specifier"
      else "Sign not allowed in string format specifier"))
  else if f.noNeg0 then
    .error (.valueError "Negative zero coercion (z) not allowed in string format specifier")
  else if f.alternate then
    .error (.valueError "Alternate form (#) not allowed in string format specifier")
  else if f.align = 61 then .error (.valueError "'=' alignment not allowed in string format specifier")
  else .ok (docFormat value f.fillChar f.align f.width (if 0 ≤ f.precision then some f.precision else none))

/-- `format_string_internal` with `calc_padding` and `fill_padding` against the docs, for every
string and every spec the parser can return (`SpecInv`). -/
def StrInternalDoc : Prop :=
  ∀ (value : Str) (f : FormatSpec), SpecInv f → formatStringInternal value f = docStr value f

theorem strInternalDoc_proven : StrInternalDoc := by
  intro value f hf
  have hal := hf.align
  have hw := hf.width
  have hp := hf.precision
  unfold formatStringInternal docStr
  by_cases hs : f.sign = 0
  · simp only [hs, bne_self_eq_false, Bool.false_eq_true, if_false, ne_eq, not_true_eq_false]
    by_cases hz : f.noNeg0 = true
    · simp [hz]
    · simp only [hz, Bool.false_eq_true, if_false]
      by_cases ha : f.alternate = true
      · simp [ha]
      · simp only [ha, Bool.false_eq_true, if_false]
        by_cases h61 : f.align = 61
        · simp [h61]
        · have h61' : (f.align == 61) = false := by simpa using h61
          simp only [h61', Bool.false_eq_true, if_false, h61]
          unfold docFormat keptText
          split
          · rename_i hfast
            simp only [beq_iff_eq] at hfast
            have hkeep : (match (if 0 ≤ f.precision then some f.precision else none) with
                | some p => value.take p.toNat | none => value) = value := by
              split
              · rename_i p hpp
                split at hpp
                · cases hpp; exact List.take_of_length_le (by omega)
                · cases hpp
              · rfl
            rw [hkeep]
            have hpad : f.width.toNat - value.length = 0 := by omega
            simp only [hpad]
            rcases hal with h | h | h | h <;> simp [h] <;> omega
          · rename_i hslow
            have hkeep : (if f.precision ≥ 0 ∧ (value.length : Int) ≥ f.precision
                then value.take f.precision.toNat else value) =
                (match (if 0 ≤ f.precision then some f.precision else none) with
                  | some p => value.take p.toNat | none => value) := by
              by_cases h0 : 0 ≤ f.precision
              · have hm : (match (if 0 ≤ f.precision then some f.precision else none) with
                    | some p => value.take p.toNat | none => value) = value.take f.precision.toNat := by
                  simp [h0]
                rw [hm]
                by_cases h1 : (value.length : Int) ≥ f.precision
                · rw [if_pos ⟨h0, h1⟩]
                · rw [if_neg (by omega), List.take_of_length_le (by omega)]
              · have hm : (match (if 0 ≤ f.precision then some f.precision else none) with
                    | some p => value.take p.toNat | none => value) = value := by
                  simp [h0]
                rw [hm, if_neg (by omega)]
            rw [hkeep]
            generalize (match (if 0 ≤ f.precision then some f.precision else none) with
                  | some p => value.take p.toNat | none => value) = t
            unfold calcPadding fillPadding
            have htot : (if f.width ≥ 0 then (if (t.length : Int) > f.width then t.length else f.width.toNat)
                else t.length) - t.length = f.width.toNat - t.length := by
              split
              · split <;> omega
              · omega
            rcases hal with h | h | h | h
            · simp [h, htot]
            · simp [h, htot]
            · omega
            · simp [h, htot]
  · have hs' : (f.sign != 0) = true := by simpa using hs
    simp only [hs', if_true, hs, ne_eq, not_false_eq_true]
    by_cases h32 : f.sign = 32 <;> simp [h32]

/-- The message of `unknown_presentation_type` as written at unicode_formatter.c:254-265, with the
type name shown as `'%.200s'` shows `tp_name`. -/
def unknownTypeMessage (t : Nat) (tpName : String) : PyExc :=
  if 32 < t ∧ t < 128 then
    .valueError ("Unknown format code '" ++ String.singleton (Char.ofNat t) ++
      "' for object of type '" ++ tpNameShown tpName ++ "'")
  else
    .valueError ("Unknown format code '\\x" ++ String.ofList (Nat.toDigits 16 t) ++
      "' for object of type '" ++ tpNameShown tpName ++ "'")

theorem unknownTypeMessage_eq (t : Nat) (tn : String) :
    unknownPresentationType t tn = unknownTypeMessage t tn := by
  unfold unknownPresentationType unknownTypeMessage hexPlain
  split <;> rfl

/-- `format(s, spec)` for every `str` or subclass instance and every spec the grammar describes:
an empty spec gives the string itself for an exact `str` and `str(obj)` (its `__str__`, which can
raise) for a subclass; otherwise the documented reading of the spec, then the documented layout
for the `s` type, and "Unknown format code" with the object's type name for any other type. -/
def StrFormatSpecDoc : Prop :=
  ∀ (tpName : String) (exact : Bool) (strObj : Py Str) (value : Str) (d : SpecFields), d.WF →
    formatStrAdvancedObj tpName exact strObj value (renderSpec d) =
      if renderSpec d = [] then (if exact then .ok value else strObj)
      else docParse tpName d 115 60 >>= fun f =>
        if f.type = 115 then docStr value f else .error (unknownTypeMessage f.type tpName)

theorem strFormatSpecDoc_proven : StrFormatSpecDoc := by
  intro tn exact strObj value d hd
  unfold formatStrAdvancedObj formatObj
  by_cases he : renderSpec d = []
  · simp [he]
  · have hne : (renderSpec d).isEmpty = false := by
      cases h : renderSpec d with
      | nil => exact absurd h he
      | cons _ _ => rfl
    simp only [hne, Bool.false_eq_true, if_false, he]
    have hp := parseDoc_proven tn d 115 60 hd
    rw [hp]
    cases hq : docParse tn d 115 60 with
    | error e => rfl
    | ok f =>
      have hi : SpecInv f := parse_inv (t := tn) (spec := renderSpec d) (dt := 115) (da := 60) (by rfl) (by rw [hp, hq])
      simp only [bind, Except.bind]
      by_cases ht : f.type = 115
      · simp [ht, strInternalDoc_proven value f hi]
      · have ht' : (f.type == 115) = false := by simpa using ht
        simp [ht, ht', unknownTypeMessage_eq]

/-! ## Errors -/

/-- A one-character spec that is none of the mini-language's other fields. -/
def PlainType (t : Nat) : Prop :=
  isAlignmentToken t = false ∧ isSignElement t = false ∧ t ≠ 122 ∧ t ≠ 35 ∧ toDecimalDigit t < 0 ∧
  t ≠ 44 ∧ t ≠ 95 ∧ t ≠ 46 ∧ t ≠ 115

/-- The refusals of `format(s, spec)` with the messages written out: an unknown presentation type
`t` (as itself between 33 and 127, else in hex), for every string and type name; both `,` and `_`,
in either order, after the width or after the precision; and `,` or `_` with the `s` type. -/
def StrFormatErrors : Prop :=
  (∀ (tn : String) (exact : Bool) (strObj : Py Str) (s : Str) (t : Nat), PlainType t →
    formatStrAdvancedObj tn exact strObj s [t] =
      .error (if 32 < t ∧ t < 128 then
        .valueError ("Unknown format code '" ++ String.singleton (Char.ofNat t) ++
          "' for object of type '" ++ tpNameShown tn ++ "'")
      else .valueError ("Unknown format code '\\x" ++ String.ofList (Nat.toDigits 16 t) ++
          "' for object of type '" ++ tpNameShown tn ++ "'"))) ∧
  (∀ s : Str, formatStrAdvanced s [44, 95] = .error (.valueError "Cannot specify both ',' and '_'.") ∧
    formatStrAdvanced s [95, 44] = .error (.valueError "Cannot specify both ',' and '_'.") ∧
    formatStrAdvanced s [46, 49, 44, 95] = .error (.valueError "Cannot specify both ',' and '_'.") ∧
    formatStrAdvanced s [46, 95, 44] = .error (.valueError "Cannot specify both ',' and '_'.") ∧
    formatStrAdvanced s [44] = .error (.valueError "Cannot specify ',' with 's'.") ∧
    formatStrAdvanced s [95, 115] = .error (.valueError "Cannot specify '_' with 's'.") ∧
    formatStrAdvanced s [44, 1] = .error (.valueError "Cannot specify ',' with '\\x1'."))

theorem strFormatErrors_proven : StrFormatErrors := by
  refine ⟨fun tn exact strObj s t ht => ?_, fun s => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ht
    have g : getInteger [t] 0 0 = .ok (0, 0, [t]) := by simp [getInteger, h5]
    have h48 : t ≠ 48 := by intro h; subst h; revert h5; decide
    rw [← unknownTypeMessage.eq_1, ← unknownTypeMessage_eq]
    simp [formatStrAdvancedObj, parseFormatSpec, parseHead, parseAlign, h1, parseFlags, h2, headIs, h3,
      h4, h48, parseTail, parseWidth, g, h6, h7, h8, parseType, validateSpec, LT_NO_LOCALE, h9, bind,
      Except.bind, pure, Except.pure]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## The separator after the precision -/

/-- The docs give `,` and `_` to `d` and the float types only ("For other presentation types,
this option is not supported"), and `parse_internal_render_format_spec` refuses a separator after
the width for `s` ("Cannot specify ',' with 's'."). The separator after the precision, for the
fractional part (new in 3.14), should be refused for `s` the same way. It is checked only against
`n` (unicode_formatter.c:596-602), so `format('abc', '.,') == 'abc'`: refuted at `'abc'`, `,`.
The same holds for the integer types: `format(255, '.,x') == 'ff'`. -/
def FracSeparatorChecked : Prop :=
  ∀ (tn : String) (exact : Bool) (strObj : Py Str) (s : Str) (c : Nat), (c = 44 ∨ c = 95) →
    ∃ e, formatStrAdvancedObj tn exact strObj s [46, c] = .error e

theorem fracSeparatorChecked_refuted : ¬ FracSeparatorChecked := by
  intro h
  obtain ⟨e, he⟩ := h "str" true (.ok [97, 98, 99]) [97, 98, 99] 44 (Or.inl rfl)
  have : formatStrAdvancedObj "str" true (.ok [97, 98, 99]) [97, 98, 99] [46, 44] = .ok [97, 98, 99] := by
    decide
  rw [this] at he
  cases he

end PyLean.UnicodeObj
