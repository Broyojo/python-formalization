import PyLean.UnicodeObj.FormatGroupDoc
import PyLean.UnicodeObj.FormatParseDoc

/-!
`format_float_internal`, Objects/unicode_formatter.c:1376-1522, against the docs
(Doc/library/string.rst, "presentation types for float"), on the binary64 model.

Two statements. `FloatBufDoc` pins what is asked of `PyOS_double_to_string`: the omitted type is
`repr` (`'r'`, with `Py_DTSF_ADD_DOT_0`) without a precision and `'g'` with at least one digit after
the point with one, `n` is `g` (C locale), `%` is `f` of the value times 100 with a `%` after it,
the precision defaults to 6, and `#` and `z` become `Py_DTSF_ALT` and `Py_DTSF_NO_NEG_0`.
`FloatFormatDoc` pins the layout of that text: the sign the spec asks for, the integer digits
grouped from the decimal point, the fraction grouped from it, and the padding, for every spec the
parser returns, separators and the fast path included.
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

/-- The call of `PyOS_double_to_string` the docs describe for each float type. -/
def docFloatBuf (x : F64) (f : FormatSpec) : Py Str :=
  let fl : DtsFlags := { alt := f.alternate, no_neg_0 := f.noNeg0 }
  if f.type = 0 then
    if f.precision < 0 then doubleToString x 114 0 { fl with add_dot_0 := true }
    else doubleToString x 103 f.precision { fl with add_dot_0 := true }
  else if f.type = 37 then
    (fun b => b ++ [37]) <$>
      doubleToString (F64.mul x (F64.ofInt 100)) 102 (if f.precision < 0 then 6 else f.precision) fl
  else doubleToString x (if f.type = 110 then 103 else f.type) (if f.precision < 0 then 6 else f.precision) fl

/-- What `format_float_internal` hands to `PyOS_double_to_string` (unicode_formatter.c:1409-1458)
is what the docs ask for, for every float and every spec with a float type (the ones
`_PyFloat_FormatAdvancedWriter` and `_PyLong_FormatAdvancedWriter` pass on). -/
def FloatBufDoc : Prop :=
  ∀ (x : F64) (f : FormatSpec), f.type ∈ [0, 101, 69, 102, 70, 103, 71, 110, 37] →
    floatBuf x f = docFloatBuf x f

theorem floatBufDoc_proven : FloatBufDoc := by
  intro x f ht
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
  unfold floatBuf docFloatBuf
  by_cases hp : f.precision < 0 <;>
  rcases ht with h | h | h | h | h | h | h | h | h <;>
  simp [h, hp, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] <;>
  split <;> simp_all

/-! ## The layout -/

/-- An ASCII digit. -/
def asciiDigit (c : Nat) : Bool := decide (48 ≤ c ∧ c ≤ 57)

/-- The integral part's grouping: by 3 with `,` or `_`, none for `n` (the C locale). -/
def docIntGrouping (f : FormatSpec) : Nat × Str :=
  if f.type ≠ 110 ∧ f.thousands = 44 then (3, [44])
  else if f.type ≠ 110 ∧ f.thousands = 95 then (3, [95]) else (0, [])

/-- The fraction, grouped by 3 from the decimal point with the separator written after the
precision. -/
def docFrac (f : FormatSpec) (frac : Str) : Str :=
  if f.fracThousands = 44 then groupFL 3 [44] frac
  else if f.fracThousands = 95 then groupFL 3 [95] frac else frac

/-- The text of `PyOS_double_to_string` laid out as the docs describe it: a leading `-` is the sign
(with the `+` or space option otherwise), the run of digits after it is the integral part, grouped
from the decimal point by 3 with `,` or `_` (never for `n` in the C locale), a `.` and the run of
digits after it are the point and the fraction, grouped from the point by 3 with the separator
written after the precision, and the rest (exponent, `%`, `inf`, `nan`) follows as it is. -/
def docFloatLayout (buf : Str) (f : FormatSpec) : Str :=
  let neg := buf.head? = some 45
  let body := if neg then buf.tail else buf
  let ip := body.takeWhile asciiDigit
  let rest := body.dropWhile asciiDigit
  let dot := rest.head? = some 46
  let r2 := if dot then rest.tail else rest
  let frac := r2.takeWhile asciiDigit
  let rem := r2.dropWhile asciiDigit
  docNumber (signStr f.sign neg) [] ip (docIntGrouping f).1 (docIntGrouping f).2
    ((if dot then [46] else []) ++ docFrac f frac ++ rem) f

theorem groupRev_nosep (g : Nat) : ∀ (n : Nat) (R : Str), R.length = n → groupRev g [] R = R.reverse := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro R hR
    by_cases hs : R.length ≤ g ∨ g = 0
    · rw [groupRev, if_pos hs]
    · rw [groupRev, if_neg hs, ih (R.length - g) (by omega) (R.drop g) (by simp)]
      rw [List.append_nil, ← List.reverse_append, List.take_append_drop]

theorem zeroGrouped_nosep (g : Nat) (ds : Str) (w : Int) : zeroGrouped g [] ds w = zeroGrouped 0 [] ds w := by
  have hk : zerosFor g [] ds w = zerosFor 0 [] ds w := by
    unfold zerosFor; congr 1; funext k; simp [groupFR_length]
  unfold zeroGrouped
  rw [hk]
  unfold groupFR
  rw [groupRev_nosep g _ _ rfl, groupRev_nosep 0 _ _ rfl]

theorem groupFL_nosep (g : Nat) : ∀ (n : Nat) (D : Str), D.length = n → groupFL g [] D = D := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro D hD
    by_cases hs : D.length ≤ g ∨ g = 0
    · rw [groupFL, if_pos hs]
    · rw [groupFL, if_neg hs, ih (D.length - g) (by omega) (D.drop g) (by simp)]
      simp

theorem groupFR_nil (g : Nat) (sep : Str) : groupFR g sep [] = [] := by
  unfold groupFR; rw [groupRev, if_pos (Or.inl (by simp))]; rfl

theorem signField_toList (s sc : Nat) (hs : s = 0 ∨ s = 32 ∨ s = 43 ∨ s = 45) (hsc : sc = 0 ∨ sc = 45) :
    (signField s sc).toList = signStr s (sc = 45) := by
  rcases hsc with rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl <;> decide

/-- `calc_number_widths` and `fill_number` for a float or complex part (no prefix, no `toupper`),
unicode_formatter.c:759-1012, against `docNumber`, for a locale of the shape `get_locale_info`
gives in the C locale. -/
theorem fullCore (sc : Nat) (digits : Str) (hd : Bool) (frac rem : Str) (f : FormatSpec)
    (gr : List Nat) (sepI fsep : Str) (gI gD : Nat) (sepD : Str) (fracD : Str → Str)
    (hsc : sc = 0 ∨ sc = 45) (hsg : f.sign = 0 ∨ f.sign = 32 ∨ f.sign = 43 ∨ f.sign = 45)
    (hal : f.align = 60 ∨ f.align = 62 ∨ f.align = 61 ∨ f.align = 94)
    (hgr : (0 < gI ∧ gI < 127 ∧ gr = [gI]) ∨ (gI = 0 ∧ (gr = [127] ∨ gr = [])))
    (hzg : ∀ ds w, zeroGrouped gI sepI ds w = zeroGrouped gD sepD ds w)
    (hfr : ∀ fr : Str, fr ≠ [] → ∃ n, insertGroupingFwd fr fr.length gr fsep = .ok (n, fracD fr)) :
    (calcNumberWidthsFull sc digits hd frac rem { sep := sepI, fracSep := fsep, grouping := gr } f >>=
        fun n => (.ok (fillNumberFull n f.fillChar) : Py Str)) =
      .ok (docNumber (signStr f.sign (sc = 45)) [] digits gD sepD
        ((if hd then [46] else []) ++ (if frac = [] then [] else fracD frac) ++ rem) f) := by
  generalize hloc : ({ sep := sepI, fracSep := fsep, grouping := gr } : LocaleFull) = loc
  have hdec : loc.decimal = [46] := by rw [← hloc]
  obtain ⟨nF, hF⟩ : ∃ nF, groupedFrac frac loc = .ok (nF, if frac = [] then [] else fracD frac) := by
    by_cases h : frac = []
    · subst h; exact ⟨0, rfl⟩
    · obtain ⟨n, hn⟩ := hfr frac h
      refine ⟨n, ?_⟩
      rw [groupedFrac, if_neg (by simpa using h), if_neg h, ← hloc]
      exact hn
  generalize hFD : (if frac = [] then [] else fracD frac) = fg at hF
  have hfl : fg.length = nF := groupedFrac_len hF
  have hso : (signField f.sign sc).toList = signStr f.sign (sc = 45) := signField_toList _ _ hsg hsc
  generalize hsgS : signStr f.sign (sc = 45) = sgS at hso
  generalize hdD : (if hd = true then ([46] : Str) else []) = dD
  have hdD' : (if hd = true then loc.decimal else []) = dD := by rw [hdec, hdD]
  have hnd : nonDigitOf (signField f.sign sc) (if hd = true then loc.decimal else []) frac rem =
      (sgS.length : Int) + dD.length + frac.length + rem.length := by
    rw [nonDigitOf, hdD', hso]
  generalize hmw : minWidthOf f (nonDigitOf (signField f.sign sc) (if hd = true then loc.decimal else [])
    frac rem) frac.length nF = mw
  have hmwv : mw = if f.fillChar = 48 ∧ f.align = 61 then
      f.width - ((sgS.length : Int) + dD.length + fg.length + rem.length) else 0 := by
    rw [← hmw, minWidthOf, hnd]
    by_cases hz : f.fillChar = 48 ∧ f.align = 61
    · rw [if_pos (by simp [hz.1, hz.2]), if_pos hz]; omega
    · rw [if_neg (by simp only [Bool.and_eq_true, beq_iff_eq]; exact hz), if_neg hz]
  obtain ⟨it, hG⟩ : ∃ it, groupedDigits digits mw loc =
      .ok ((if digits = [] then [] else zeroGrouped gD sepD digits mw).length,
        if digits = [] then [] else zeroGrouped gD sepD digits mw, it) := by
    by_cases h : digits = []
    · subst h; exact ⟨0, by simp [groupedDigits, pure, Except.pure]⟩
    · obtain ⟨it, hi⟩ := insert_doc digits h mw gr gI sepI hgr
      refine ⟨it, ?_⟩
      rw [groupedDigits, if_neg (by simpa using h), ← hloc, hi, hzg, if_neg h]
  rw [← hmw] at hG
  rw [calc_ok hF hG, hmw, hnd, hdD']
  simp only [bind, Except.bind, fillNumberFull, hso]
  generalize hGD : (if digits = [] then [] else zeroGrouped gD sepD digits mw) = G
  have hGl : G.length = (if digits = [] then [] else zeroGrouped gD sepD digits mw).length := by rw [hGD]
  unfold docNumber
  by_cases hz : f.fillChar = 48 ∧ f.align = 61 ∧ digits ≠ []
  · rw [if_pos hz]
    have hG' : G = zeroGrouped gD sepD digits mw := by rw [← hGD, if_neg hz.2.2]
    have hmw' : mw = f.width - (sgS.length : Int) - (([] : Str).length : Int) -
        ((dD ++ fg ++ rem).length : Int) := by
      rw [hmwv, if_pos ⟨hz.1, hz.2.1⟩]; simp only [List.length_append, List.length_nil]; push_cast; omega
    have hreach := zerosFor_reach gD sepD digits mw
    rw [padFields_nonpos _ _ (by rw [hG']; omega)]
    rw [← hmw', hG', ← hFD]
    simp [List.append_assoc]
  · rw [if_neg hz]
    have hG' : G = groupFR gD sepD digits := by
      rw [← hGD]
      by_cases h : digits = []
      · subst h; rw [if_pos rfl, groupFR_nil]
      · rw [if_neg h]
        have hm0 : mw = 0 := by
          rw [hmwv, if_neg (fun h2 => hz ⟨h2.1, h2.2, h⟩)]
        unfold zeroGrouped; rw [hm0, zerosFor_nonpos _ _ _ _ (Int.le_refl 0)]; simp
    rw [hG'] at hGl ⊢
    rw [← hFD] at hfl ⊢
    rw [← padLayout_eq f sgS [] (groupFR gD sepD digits) (dD ++ (if frac = [] then [] else fracD frac) ++ rem)
      (f.width - ((sgS.length : Int) + dD.length + frac.length + rem.length + (groupFR gD sepD digits).length +
        nF - frac.length))
      (by simp only [List.length_append, List.length_nil]; push_cast; omega) hal]
    simp [List.append_assoc]

/-- With no width to fill, a number is its sign, prefix, grouped digits and tail. -/
theorem docNumber_nopad (sg pfx ds : Str) (g : Nat) (sep tail : Str) (f : FormatSpec) (hw : f.width ≤ 0)
    (hal : f.align = 60 ∨ f.align = 62 ∨ f.align = 61 ∨ f.align = 94) :
    docNumber sg pfx ds g sep tail f = sg ++ pfx ++ groupFR g sep ds ++ tail := by
  unfold docNumber
  split
  · unfold zeroGrouped
    rw [zerosFor_nonpos _ _ _ _ (by omega)]
    simp
  · unfold padLayout
    have : (f.width - ((sg.length : Int) + pfx.length + (groupFR g sep ds).length + tail.length)).toNat = 0 := by
      omega
    simp only [this]
    rcases hal with h | h | h | h <;> simp [h]

theorem groupFL_nil (g : Nat) (sep : Str) : groupFL g sep [] = [] := by
  rw [groupFL, if_pos (Or.inl (by simp))]

theorem docFrac_nil (f : FormatSpec) : docFrac f [] = [] := by
  unfold docFrac; split <;> (try split) <;> simp [groupFL_nil]

theorem asciiDigit_eq : asciiDigit = pyDigit := by
  funext c; simp [asciiDigit, pyDigit]

/-- The locale `get_locale_info` gives (C locale), in the shape `fullCore` takes. -/
theorem loc_cases (f : FormatSpec) (hf : SpecInv f) (ht : f.type ∈ [0, 101, 69, 102, 70, 103, 71, 110, 37]) :
    ∃ gr sepI fsep gI,
      localeInfoFull (if f.type == 110 then LT_CURRENT_LOCALE else f.thousands) f.fracThousands =
        { sep := sepI, fracSep := fsep, grouping := gr } ∧
      ((0 < gI ∧ gI < 127 ∧ gr = [gI]) ∨ (gI = 0 ∧ (gr = [127] ∨ gr = []))) ∧
      (∀ ds w, zeroGrouped gI sepI ds w = zeroGrouped (docIntGrouping f).1 (docIntGrouping f).2 ds w) ∧
      (∀ fr : Str, fr ≠ [] → ∃ n, insertGroupingFwd fr fr.length gr fsep = .ok (n, docFrac f fr)) := by
  have hth := hf.thousands
  have hfr := hf.frac
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht hth
  have h96 : f.thousands ≠ 96 := by
    rintro h
    rcases hth with h' | ⟨h' | h', -⟩ | ⟨-, h'⟩ <;> omega
  have hfwd0 : ∀ (gr : List Nat), (gr = [127] ∨ gr = []) → ∀ fr : Str, fr ≠ [] →
      ∃ n, insertGroupingFwd fr fr.length gr [] = .ok (n, fr) :=
    fun gr hg fr hne => ⟨_, noGroupFwd fr hne gr hg⟩
  have hfwd3 : ∀ sep : Str, ∀ fr : Str, fr ≠ [] → ∃ n, insertGroupingFwd fr fr.length [3] sep = .ok (n, groupFL 3 sep fr) :=
    fun sep fr hne => groupingFraction_proven 3 sep fr (by omega) (by omega) hne
  by_cases hn : f.type = 110
  · have h0 : f.thousands = 0 := by
      rcases hth with h | ⟨-, h⟩ | ⟨-, h⟩
      · exact h
      · omega
      · omega
    have hf0 : f.fracThousands = 0 := by
      rcases hfr with h | ⟨-, h⟩
      · exact h
      · exact absurd hn h
    refine ⟨[], [], [], 0, ?_, Or.inr ⟨rfl, Or.inr rfl⟩, ?_, ?_⟩
    · simp [hn, hf0, localeInfoFull, localeInfo, LT_CURRENT_LOCALE, LT_NO_LOCALE]
    · intro ds w; simp [docIntGrouping, hn]
    · intro fr hne
      obtain ⟨n, h⟩ := hfwd0 [] (Or.inr rfl) fr hne
      exact ⟨n, by simp [docFrac, hf0, h]⟩
  · have hn' : (f.type == 110) = false := by simpa using hn
    have ht3 : f.thousands = 0 ∨ f.thousands = 44 ∨ f.thousands = 95 := by
      rcases hth with h | ⟨h | h, -⟩ | ⟨h, -⟩ <;> omega
    have hf3 : f.fracThousands = 0 ∨ f.fracThousands = 44 ∨ f.fracThousands = 95 := by
      rcases hfr with h | ⟨h | h, -⟩ <;> omega
    rcases ht3 with h1 | h1 | h1 <;> rcases hf3 with h2 | h2 | h2
    · refine ⟨[127], [], [], 0, ?_, Or.inr ⟨rfl, Or.inl rfl⟩, ?_, ?_⟩
      · simp [hn', h1, h2, localeInfoFull, localeInfo, LT_CURRENT_LOCALE, LT_NO_LOCALE, LT_DEFAULT_LOCALE,
          LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]
      · intro ds w; simp [docIntGrouping, h1]
      · intro fr hne
        obtain ⟨n, h⟩ := hfwd0 [127] (Or.inl rfl) fr hne
        exact ⟨n, by simp [docFrac, h2, h]⟩
    · refine ⟨[3], [], [44], 3, ?_, Or.inl ⟨by omega, by omega, rfl⟩, ?_, ?_⟩
      · simp [hn', h1, h2, localeInfoFull, localeInfo, LT_CURRENT_LOCALE, LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]
      · intro ds w; rw [zeroGrouped_nosep]; simp [docIntGrouping, h1]
      · intro fr hne
        obtain ⟨n, h⟩ := hfwd3 [44] fr hne
        exact ⟨n, by simp [docFrac, h2, h]⟩
    · refine ⟨[3], [], [95], 3, ?_, Or.inl ⟨by omega, by omega, rfl⟩, ?_, ?_⟩
      · simp [hn', h1, h2, localeInfoFull, localeInfo, LT_CURRENT_LOCALE, LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]
      · intro ds w; rw [zeroGrouped_nosep]; simp [docIntGrouping, h1]
      · intro fr hne
        obtain ⟨n, h⟩ := hfwd3 [95] fr hne
        exact ⟨n, by simp [docFrac, h2, h]⟩
    · refine ⟨[3], [44], [], 3, ?_, Or.inl ⟨by omega, by omega, rfl⟩, ?_, ?_⟩
      · simp [hn', h1, h2, localeInfoFull, localeInfo, LT_CURRENT_LOCALE, LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]
      · intro ds w; simp [docIntGrouping, h1, hn]
      · intro fr hne
        obtain ⟨n, h⟩ := hfwd3 [] fr hne
        exact ⟨n, by rw [groupFL_nosep 3 _ fr rfl] at h; simp [docFrac, h2, h]⟩
    · refine ⟨[3], [44], [44], 3, ?_, Or.inl ⟨by omega, by omega, rfl⟩, ?_, ?_⟩
      · simp [hn', h1, h2, localeInfoFull, localeInfo, LT_CURRENT_LOCALE, LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]
      · intro ds w; simp [docIntGrouping, h1, hn]
      · intro fr hne
        obtain ⟨n, h⟩ := hfwd3 [44] fr hne
        exact ⟨n, by simp [docFrac, h2, h]⟩
    · refine ⟨[3], [44], [95], 3, ?_, Or.inl ⟨by omega, by omega, rfl⟩, ?_, ?_⟩
      · simp [hn', h1, h2, localeInfoFull, localeInfo, LT_CURRENT_LOCALE, LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]
      · intro ds w; simp [docIntGrouping, h1, hn]
      · intro fr hne
        obtain ⟨n, h⟩ := hfwd3 [95] fr hne
        exact ⟨n, by simp [docFrac, h2, h]⟩
    · refine ⟨[3], [95], [], 3, ?_, Or.inl ⟨by omega, by omega, rfl⟩, ?_, ?_⟩
      · simp [hn', h1, h2, localeInfoFull, localeInfo, LT_CURRENT_LOCALE, LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]
      · intro ds w; simp [docIntGrouping, h1, hn]
      · intro fr hne
        obtain ⟨n, h⟩ := hfwd3 [] fr hne
        exact ⟨n, by rw [groupFL_nosep 3 _ fr rfl] at h; simp [docFrac, h2, h]⟩
    · refine ⟨[3], [95], [44], 3, ?_, Or.inl ⟨by omega, by omega, rfl⟩, ?_, ?_⟩
      · simp [hn', h1, h2, localeInfoFull, localeInfo, LT_CURRENT_LOCALE, LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]
      · intro ds w; simp [docIntGrouping, h1, hn]
      · intro fr hne
        obtain ⟨n, h⟩ := hfwd3 [44] fr hne
        exact ⟨n, by simp [docFrac, h2, h]⟩
    · refine ⟨[3], [95], [95], 3, ?_, Or.inl ⟨by omega, by omega, rfl⟩, ?_, ?_⟩
      · simp [hn', h1, h2, localeInfoFull, localeInfo, LT_CURRENT_LOCALE, LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]
      · intro ds w; simp [docIntGrouping, h1, hn]
      · intro fr hne
        obtain ⟨n, h⟩ := hfwd3 [95] fr hne
        exact ⟨n, by simp [docFrac, h2, h]⟩

/-- The general path of `format_float_internal` (`parse_number`, `get_locale_info`,
`calc_number_widths`, `fill_number`), unicode_formatter.c:1472-1516, against `docFloatLayout`. -/
theorem floatSlow_doc (buf : Str) (f : FormatSpec) (hf : SpecInv f)
    (ht : f.type ∈ [0, 101, 69, 102, 70, 103, 71, 110, 37]) :
    formatFloatSlow buf f = .ok (docFloatLayout buf f) := by
  obtain ⟨gr, sepI, fsep, gI, hloc, hgr, hzg, hfr⟩ := loc_cases f hf ht
  have hss : splitSign buf = (if buf.head? = some 45 then 45 else 0,
      if buf.head? = some 45 then buf.tail else buf) := by
    unfold splitSign
    cases buf with
    | nil => rfl
    | cons c t => by_cases h : c = 45 <;> simp [h]
  unfold formatFloatSlow docFloatLayout
  rw [hss]
  simp only [splitNumber_eq, restOf, asciiDigit_eq]
  rw [hloc]
  generalize hB : (if buf.head? = some 45 then buf.tail else buf) = B
  have hsc : (if buf.head? = some 45 then (45 : Nat) else 0) = 0 ∨ (if buf.head? = some 45 then (45 : Nat) else 0) = 45 := by
    split <;> simp
  have hc := fullCore (if buf.head? = some 45 then 45 else 0) (B.takeWhile pyDigit)
    ((B.dropWhile pyDigit).head? == some 46)
    ((if ((B.dropWhile pyDigit).head? == some 46) = true then (B.dropWhile pyDigit).tail else B.dropWhile pyDigit).takeWhile pyDigit)
    ((if ((B.dropWhile pyDigit).head? == some 46) = true then (B.dropWhile pyDigit).tail else B.dropWhile pyDigit).dropWhile pyDigit)
    f gr sepI fsep gI (docIntGrouping f).1 (docIntGrouping f).2 (docFrac f) hsc hf.sign hf.align hgr hzg hfr
  rw [hc]
  have hneg : ((if buf.head? = some 45 then (45 : Nat) else 0) = 45) = (buf.head? = some 45) := by
    split <;> simp_all
  have hfr2 : ∀ X : Str, (if X = [] then [] else docFrac f X) = docFrac f X := by
    intro X; by_cases h : X = [] <;> simp [h, docFrac_nil]
  simp only [hneg, hfr2, beq_iff_eq]

/-- `format_float_internal` against the docs, for every float and every spec the parser returns
with a float type: "precision too big" above `INT_MAX`, and otherwise the text
`PyOS_double_to_string` gives for the documented type, precision and flags (`docFloatBuf`), laid
out as the docs describe (`docFloatLayout`). Both the fast path and the general path are in it. -/
def FloatFormatDoc : Prop :=
  ∀ (x : F64) (f : FormatSpec), SpecInv f → f.type ∈ [0, 101, 69, 102, 70, 103, 71, 110, 37] →
    formatFloatInternal x f =
      if f.precision > 2 ^ 31 - 1 then .error (.valueError "precision too big")
      else docFloatBuf x f >>= fun buf => .ok (docFloatLayout buf f)

theorem floatFormatDoc_proven : FloatFormatDoc := by
  intro x f hf ht
  unfold formatFloatInternal
  by_cases hp : f.precision > 2 ^ 31 - 1
  · rw [if_pos hp, if_pos hp]
  rw [if_neg hp, if_neg hp, floatBufDoc_proven x f ht]
  cases docFloatBuf x f with
  | error e => rfl
  | ok buf =>
    simp only [bind, Except.bind]
    split
    · rename_i hfast
      -- the fast path writes the buffer; the general path with width 0 writes it back
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := floatFastPath_facts hfast
      have hg : SpecInv { f with width := 0 } :=
        ⟨hf.align, hf.sign, by simp, hf.precision, hf.thousands, hf.frac⟩
      have hs := floatSlow_doc buf { f with width := 0 } hg ht
      rw [slow_plain buf { f with width := 0 } h5 h6, layout_self buf { f with width := 0 } h1 h2 (by simp)] at hs
      have hw : docFloatLayout buf { f with width := 0 } = docFloatLayout buf f := by
        unfold docFloatLayout
        rw [docNumber_nopad _ _ _ _ _ _ { f with width := 0 } (by simp) hf.align,
          docNumber_nopad _ _ _ _ _ _ f (by omega) hf.align]
        rfl
      have hs2 : buf = docFloatLayout buf { f with width := 0 } := Except.ok.inj hs
      rw [← hw]
      exact congrArg Except.ok hs2
    · exact floatSlow_doc buf f hf ht

end PyLean.UnicodeObj
