import PyLean.UnicodeObj.FormatSpec

/-!
Properties of the format specification mini-language.
-/

namespace PyLean.UnicodeObj

open PyLean

/-! ## The NUL presentation type -/

/-- The documented presentation types have no NUL: a spec ending in NUL is rejected
by `float` and `complex`, as it is by `int` and `str`. A NUL at the end of a spec can
only be the type field, since a fill character is followed by an alignment. -/
def FormatNulRejected : Prop :=
  ∀ spec : Str, spec.getLast? = some 0 →
    (∃ e, formatFloatDispatch spec = .error e) ∧ (∃ e, formatComplexDispatch spec = .error e)

/-- `format(1.5, '\x00')` succeeds: the explicit NUL is taken for the `'\0'` that
stands for "no presentation type". -/
theorem formatNulRejected_refuted : ¬ FormatNulRejected := by
  intro h
  obtain ⟨⟨e, he⟩, -⟩ := h [0] rfl
  have : formatFloatDispatch [0] = .ok (some { fillChar := 32, align := 62, type := 0 }) := by
    decide
  rw [this] at he
  cases he

/-- `int` and `str` do reject it: whatever the rest of the spec, a parsed type of
NUL raises the "Unknown format code" error. -/
def FormatNulIntStr : Prop :=
  ∀ (spec : Str) (f : FormatSpec),
    (parseFormatSpec "int" spec 100 62 = .ok f → f.type = 0 → spec ≠ [] →
      ∀ v e, formatLongAdvanced v "int" spec e =
        .error (unknownPresentationType 0 "int")) ∧
    (parseFormatSpec "str" spec 115 60 = .ok f → f.type = 0 → spec ≠ [] →
      ∀ s, formatStrAdvanced s spec = .error (unknownPresentationType 0 "str"))

theorem formatNulIntStr_proven : FormatNulIntStr := by
  intro spec f
  have hne : ∀ l : Str, l ≠ [] → l.isEmpty = false := by
    intro l h; cases l with
    | nil => exact absurd rfl h
    | cons _ _ => rfl
  constructor
  · intro hp ht hs v e
    simp only [formatLongAdvanced, hne spec hs, Bool.false_eq_true, if_false, hp, bind,
      Except.bind, ht]
    rw [if_neg (by decide), if_neg (by decide)]
  · intro hp ht hs s
    simp only [formatStrAdvanced, hne spec hs, Bool.false_eq_true, if_false, hp, bind,
      Except.bind, ht]
    rw [if_neg (by decide)]

/-! ## The parser's asserts -/

theorem validateSpec_keeps {f g : FormatSpec} (h : validateSpec f = .ok g) :
    g.align = f.align ∧ g.sign = f.sign := by
  simp only [validateSpec, bind, Except.bind, pure, Except.pure] at h
  grind

theorem parsePrecision_keeps {f g : FormatSpec} {rest r : List Nat}
    (h : parsePrecision f rest = .ok (g, r)) : g.align = f.align ∧ g.sign = f.sign := by
  simp only [parsePrecision, bind, Except.bind, pure, Except.pure] at h
  grind

theorem parseWidth_keeps {f g : FormatSpec} {rest r : List Nat}
    (h : parseWidth f rest = .ok (g, r)) : g.align = f.align ∧ g.sign = f.sign := by
  simp only [parseWidth, bind, Except.bind, pure, Except.pure] at h
  grind

theorem parseType_keeps {t spec f g rest} (h : parseType t spec f rest = .ok g) :
    g.align = f.align ∧ g.sign = f.sign := by
  simp only [parseType] at h
  split at h
  · exact validateSpec_keeps h
  · have := validateSpec_keeps h
    exact this
  · cases h

theorem parseTail_keeps {t spec f g rest} (h : parseTail t spec f rest = .ok g) :
    g.align = f.align ∧ g.sign = f.sign := by
  simp only [parseTail, bind, Except.bind, pure, Except.pure] at h
  cases h1 : parseWidth f rest with
  | error e => simp [h1] at h
  | ok p =>
    obtain ⟨p1, p2⟩ := p
    have k1 := parseWidth_keeps h1
    simp only [h1] at h
    by_cases h2 : headIs p2 46 = true
    · simp only [h2, if_true] at h
      cases h3 : parsePrecision p1 p2.tail with
      | error e => simp [h3] at h
      | ok q =>
        obtain ⟨q1, q2⟩ := q
        have k2 := parsePrecision_keeps h3
        simp only [h3] at h
        have k3 := parseType_keeps h
        exact ⟨by rw [k3.1, k2.1, k1.1], by rw [k3.2, k2.2, k1.2]⟩
    · simp only [h2, if_false, Bool.false_eq_true] at h
      have k3 := parseType_keeps h
      exact ⟨by rw [k3.1, k1.1], by rw [k3.2, k1.2]⟩

/-- The asserts at formatter_unicode.c@3.14.7:369-370, in their sharp form: whatever the
spec, a parsed spec has one of the four alignments (given a default among them) and
a sign of NUL, space, `+` or `-`. -/
def ParseAsserts : Prop :=
  ∀ (t : String) (spec : Str) (dt da : Nat) (f : FormatSpec), isAlignmentToken da = true →
    parseFormatSpec t spec dt da = .ok f →
    (isAlignmentToken f.align = true) ∧ (f.sign = 0 ∨ isSignElement f.sign = true)

theorem parseAlign_ok (f : FormatSpec) (spec : Str) (h : isAlignmentToken f.align = true)
    (hs : f.sign = 0) :
    isAlignmentToken (parseAlign f spec).1.align = true ∧ (parseAlign f spec).1.sign = 0 := by
  simp only [parseAlign]
  grind

theorem parseFlags_ok (f : FormatSpec) (rest : List Nat) (h : isAlignmentToken f.align = true)
    (hs : f.sign = 0) :
    isAlignmentToken (parseFlags f rest).1.align = true ∧
      ((parseFlags f rest).1.sign = 0 ∨ isSignElement (parseFlags f rest).1.sign = true) := by
  simp only [parseFlags]
  grind

theorem parseHead_ok (spec : Str) (dt da : Nat) (h : isAlignmentToken da = true) :
    isAlignmentToken (parseHead spec dt da).1.align = true ∧
      ((parseHead spec dt da).1.sign = 0 ∨ isSignElement (parseHead spec dt da).1.sign = true) := by
  have a := parseAlign_ok { align := da, type := dt } spec h rfl
  have b := parseFlags_ok _ (parseAlign { align := da, type := dt } spec).2.2.2 a.1 a.2
  simp only [parseHead]
  split
  · refine ⟨?_, b.2⟩
    dsimp only
    split
    · decide
    · exact b.1
  · exact b

theorem parseAsserts_proven : ParseAsserts := by
  intro t spec dt da f h hp
  simp only [parseFormatSpec] at hp
  obtain ⟨a, b⟩ := parseTail_keeps hp
  obtain ⟨c, d⟩ := parseHead_ok spec dt da h
  rw [a, b]
  exact ⟨c, d⟩

/-! ## `str` -/

theorem calcPadding_spec (n : Nat) (w : Int) (a : Nat) :
    (calcPadding n w a).1 + n + (calcPadding n w a).2.1 = (calcPadding n w a).2.2 ∧
    ((calcPadding n w a).2.2 : Int) = max (n : Int) w ∧
    (a = 62 → (calcPadding n w a).2.1 = 0) ∧
    (a = 60 → (calcPadding n w a).1 = 0) ∧
    (a = 94 → (calcPadding n w a).1 ≤ (calcPadding n w a).2.1 ∧
      (calcPadding n w a).2.1 ≤ (calcPadding n w a).1 + 1) := by
  simp only [calcPadding]
  grind

/-- `format(s, spec)` for every string and every parsed spec that reaches the
output: the text is `s` cut to the precision, padded to the width with the fill,
left, right or centred as the alignment says, the extra fill going to the right. -/
def StrFormatShape : Prop :=
  ∀ (value : Str) (f : FormatSpec) (r : Str), f.align ≠ 61 → f.width ≥ -1 → f.precision ≥ -1 →
    (f.align = 60 ∨ f.align = 62 ∨ f.align = 94) →
    formatStringInternal value f = .ok r →
    ∃ l rr n, r = List.replicate l f.fillChar ++ value.take n ++ List.replicate rr f.fillChar ∧
      (n : Int) = (if f.precision ≥ 0 ∧ value.length ≥ f.precision then f.precision
                   else value.length) ∧
      (r.length : Int) = max (n : Int) f.width ∧
      (f.align = 60 → l = 0) ∧ (f.align = 62 → rr = 0) ∧
      (f.align = 94 → l ≤ rr ∧ rr ≤ l + 1)

theorem strFormatShape_proven : StrFormatShape := by
  intro value f r hne hw hp ha h
  unfold formatStringInternal at h
  split at h
  · split at h <;> cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · rename_i hc
    cases h
    simp only [beq_iff_eq] at hc
    refine ⟨0, 0, value.length, by simp, ?_, ?_, by simp, by simp, by simp⟩
    · split <;> omega
    · omega
  · have key : ∃ n : Nat,
        (if f.precision ≥ 0 ∧ (value.length : Int) ≥ f.precision
         then value.take f.precision.toNat else value) = value.take n ∧
        (n : Int) = (if f.precision ≥ 0 ∧ (value.length : Int) ≥ f.precision
                     then f.precision else value.length) := by
      split
      · rename_i hh
        exact ⟨f.precision.toNat, rfl, by omega⟩
      · exact ⟨value.length, by simp, rfl⟩
    obtain ⟨n, h1, h2⟩ := key
    have hlen : (value.take n).length = n := by
      rw [List.length_take]
      split at h2 <;> omega
    simp only [h1, hlen] at h
    have hcp := calcPadding_spec n f.width f.align
    cases hc2 : calcPadding n f.width f.align with
    | mk l q =>
      cases q with
      | mk rr tot =>
        simp only [hc2] at h hcp
        simp only [fillPadding, Except.ok.injEq] at h
        subst h
        refine ⟨l, rr, n, rfl, h2, ?_, hcp.2.2.2.1, hcp.2.2.1, hcp.2.2.2.2⟩
        simp only [List.length_append, List.length_replicate, hlen]
        omega

/-! ## Fast path vs. general path of `int` -/

theorem hexLower_ne (d : Nat) : hexLower d ≠ 45 := by
  simp only [hexLower]
  split <;> omega

theorem natDigits_spec (b fuel n : Nat) (acc : Str) (h : ∀ c ∈ acc, c ≠ 45) (hf : 0 < fuel) :
    natDigits b fuel n acc ≠ [] ∧ ∀ c ∈ natDigits b fuel n acc, c ≠ 45 := by
  induction fuel generalizing n acc with
  | zero => omega
  | succ fuel ih =>
    simp only [natDigits]
    have ha : ∀ c ∈ hexLower (n % b) :: acc, c ≠ 45 := by
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hexLower_ne _
      · exact h c hc
    split
    · exact ⟨by simp, ha⟩
    · cases fuel with
      | zero => simpa [natDigits] using ha
      | succ k => exact ih _ _ ha (by omega)

theorem digitsOf_spec (b n : Nat) : digitsOf b n ≠ [] ∧ ∀ c ∈ digitsOf b n, c ≠ 45 :=
  natDigits_spec b (n + 1) n [] (by simp) (by omega)

theorem noGroup (ds : Str) (hne : ds ≠ []) (w : Int) (hw : w ≤ 0) :
    insertThousandsGrouping ds w [127] [] = .ok (ds.length, ds, 0) := by
  have hn : 0 < ds.length := List.length_pos_iff.2 hne
  have hm : max 0 w = 0 := by omega
  simp only [insertThousandsGrouping, hm, Int.toNat_zero]
  have hf : ds.length + 0 + 2 = (ds.length + 1) + 1 := by omega
  rw [hf]
  simp only [groupLoop, groupNext]
  have h1 : max (max (ds.length : Int) 0) 1 = ds.length := by omega
  have h2 : max (ds.length : Int) 1 = ds.length := by omega
  have h3 : max (0 : Int) ds.length = ds.length := by omega
  have h4 : ds.reverse.take ds.length = ds.reverse := List.take_of_length_le (by simp)
  simp [h1, h2, h3, h4, groupPiece, List.reverse_reverse]

theorem calcNW (nPrefix sc : Nat) (ds : Str) (f : FormatSpec) (hd : ds ≠ [])
    (h1 : f.sign ≠ 43) (h2 : f.sign ≠ 32) (h3 : f.width = -1) :
    calcNumberWidths nPrefix sc ds 0 [] [127] f =
      .ok (0, (if sc == 45 then some 45 else none), 0, 0, ds) := by
  have hs1 : (f.sign == 43) = false := by simpa using h1
  have hs2 : (f.sign == 32) = false := by simpa using h2
  have hn : ¬ ds.length = 0 := by
    intro h; exact hd (List.eq_nil_of_length_eq_zero h)
  by_cases hc : sc = 45
  · simp only [calcNumberWidths, hs1, hs2, hc, Bool.false_eq_true, if_false, if_neg hn, bind,
      Except.bind, pure, Except.pure, beq_self_eq_true, if_true]
    rw [noGroup ds hd _ (by rw [h3]; split <;> omega)]
    simp only [h3]
    rw [if_neg (by omega)]
  · have hc' : (sc == 45) = false := by simpa using hc
    simp only [calcNumberWidths, hs1, hs2, hc', Bool.false_eq_true, if_false, if_neg hn, bind,
      Except.bind, pure, Except.pure]
    rw [noGroup ds hd _ (by rw [h3]; split <;> omega)]
    simp only [h3]
    rw [if_neg (by omega)]

/-- For every int and every spec that takes the fast path of `format_long_internal`
(no sign option, no width, no grouping, not `X` or `n`), `_PyLong_FormatWriter` gives
what the general path would give, in all four bases and with or without `#`. -/
def IntFastSlow : Prop :=
  ∀ (v : Int) (f : FormatSpec) (base skip : Nat),
    ((base = 2 ∧ skip = 2) ∨ (base = 8 ∧ skip = 2) ∨ (base = 16 ∧ skip = 2) ∨
      (base = 10 ∧ skip = 0)) →
    f.sign ≠ 43 → f.sign ≠ 32 → f.width = -1 → f.type ≠ 88 → f.type ≠ 110 → f.thousands = 0 →
    longFormatWriter v base f.alternate = formatLongSlow v f base skip

theorem intFastSlow_proven : IntFastSlow := by
  intro v f base skip hb h1 h2 h3 hx h4 h5
  obtain ⟨hd, hm⟩ := digitsOf_spec base v.natAbs
  have hloc : localeInfo (if f.type == 110 then LT_CURRENT_LOCALE else f.thousands) =
      ([], [127]) := by
    have : (f.type == 110) = false := by simpa using h4
    simp only [this, Bool.false_eq_true, if_false, h5]
    decide
  have hxf : (f.type == 88) = false := by simpa using hx
  simp only [longFormatWriter, formatLongSlow, longFormat, bind, Except.bind, hloc]
  generalize digitsOf base v.natAbs = ds at *
  by_cases hlim : (base == 10 && decide (ds.length > 4300)) = true
  · simp [hlim]
  simp only [hlim, Bool.false_eq_true, if_false]
  obtain ⟨d, t, rfl⟩ : ∃ d t, ds = d :: t := by
    cases ds with
    | nil => exact absurd rfl hd
    | cons d t => exact ⟨d, t, rfl⟩
  have hd45 : d ≠ 45 := hm d List.mem_cons_self
  have hd45' : (d == 45) = false := by simpa using hd45
  rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    by_cases hv : v < 0 <;> cases ha : f.alternate <;>
    simp [hv, ha, hd45', fun a b => calcNW a b (d :: t) f hd h1 h2 h3, fillNumber, hxf]

/-! ## Grouping -/

/-- The rounds of the grouping loop are bounded by the digits, not by the width. -/
def GroupLoopLinear : Prop :=
  ∀ (ds : Str) (w : Int) (n it : Nat) (o : List Nat),
    insertThousandsGrouping ds w [3] [44] = .ok (n, o, it) → it ≤ ds.length + 1

/-- One digit padded to width 40: thirteen rounds of `min_width` bookkeeping. -/
theorem groupLoopLinear_refuted : ¬ GroupLoopLinear := by
  intro h
  have e : ∃ n o it, insertThousandsGrouping [49] 40 [3] [44] = .ok (n, o, it) ∧ 2 < it :=
    ⟨_, _, _, rfl, by decide⟩
  obtain ⟨n, o, it, h1, h2⟩ := e
  have := h _ _ _ _ _ h1
  simp only [List.length_cons, List.length_nil] at this
  omega

/-- With no padding, the grouped text is the digits with separators between them:
dropping the separator gives the digits back, and the count is the text's length. -/
def GroupDigits : Prop :=
  ∀ (ds : Str) (sep g : Nat), 0 < g → sep ∉ ds → ds ≠ [] →
    ∃ n o it, insertThousandsGrouping ds 0 [g] [sep] = .ok (n, o, it) ∧ o.length = n ∧
      o.filter (· != sep) = ds

end PyLean.UnicodeObj
