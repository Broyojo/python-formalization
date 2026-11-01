import PyLean.UnicodeObj.FormatStr

/-!
Properties of `str.format`.
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

theorem ssizeMax_val : ssizeMax = 9223372036854775807 := rfl

/-! ## `get_integer` -/

/-- The value of a run of decimal digits, in unbounded arithmetic. -/
def decVal : List Nat → Int → Int
  | [], acc => acc
  | c :: cs, acc => decVal cs (acc * 10 + toDecimalDigit c)

/-- A field index is read without wrapping: for every run of decimal digits, in any script, the
result is its value if that fits `Py_ssize_t`, and otherwise `ValueError`. Only unbounded
arithmetic is used to state it. -/
def GetIntegerNoWrap : Prop :=
  ∀ s : Str, s ≠ [] → (∀ c ∈ s, 0 ≤ toDecimalDigit c) →
    fieldInteger s =
      if decVal s 0 ≤ ssizeMax then .ok (some (decVal s 0).toNat)
      else .error (.valueError "Too many decimal digits in format string")

theorem decVal_ge : ∀ (s : List Nat) (acc : Int), (∀ c ∈ s, 0 ≤ toDecimalDigit c) → 0 ≤ acc →
    acc ≤ decVal s acc := by
  intro s
  induction s with
  | nil => intro acc _ _; simp [decVal]
  | cons c t ih =>
    intro acc h ha
    have hc := h c List.mem_cons_self
    have := ih (acc * 10 + toDecimalDigit c) (fun x hx => h x (List.mem_cons_of_mem _ hx)) (by omega)
    simp only [decVal]
    omega

theorem fieldIntegerLoop_val : ∀ (s : List Nat) (acc : Int), (∀ c ∈ s, 0 ≤ toDecimalDigit c) →
    0 ≤ acc → acc ≤ ssizeMax →
    fieldIntegerLoop s acc =
      if decVal s acc ≤ ssizeMax then .ok (some (decVal s acc).toNat)
      else .error (.valueError "Too many decimal digits in format string") := by
  intro s
  induction s with
  | nil =>
    intro acc _ _ hm
    simp [fieldIntegerLoop, decVal, hm]
  | cons c t ih =>
    intro acc h h0 hm
    have hc := h c List.mem_cons_self
    have ht : ∀ x ∈ t, 0 ≤ toDecimalDigit x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hv : decVal (c :: t) acc = decVal t (acc * 10 + toDecimalDigit c) := rfl
    simp only [fieldIntegerLoop]
    rw [hv, if_neg (by omega)]
    by_cases hov : acc > (ssizeMax - toDecimalDigit c) / 10
    · rw [if_pos hov]
      have hge := decVal_ge t (acc * 10 + toDecimalDigit c) ht (by omega)
      have hgt : acc * 10 + toDecimalDigit c > ssizeMax := by
        rw [ssizeMax_val] at hov ⊢
        omega
      rw [if_neg (by omega)]
    · rw [if_neg hov]
      have hle : acc * 10 + toDecimalDigit c ≤ ssizeMax := by
        rw [ssizeMax_val] at hov ⊢
        omega
      exact ih _ ht (by omega) hle

theorem getIntegerNoWrap_proven : GetIntegerNoWrap := by
  intro s hne h
  cases s with
  | nil => exact absurd rfl hne
  | cons c t =>
    simp only [fieldInteger, List.isEmpty_cons, Bool.false_eq_true, if_false]
    exact fieldIntegerLoop_val _ 0 h (by omega) (by rw [ssizeMax_val]; omega)

/-! ## Auto-numbering -/

/-- The numbering rule of `field_name_split`, for every field name and every state. An empty name
takes the next number and is refused once fields have been numbered by hand; a numeric name is
refused once automatic numbering has begun, and does not move the counter; a name that is not a
number leaves the state alone. -/
def AutoNumberingRule : Prop :=
  ∀ (s : Str) (st : FSt) (first : Str) (idx : Option Nat) (rest : Str) (st' : FSt),
    fieldNameSplit s st = .ok (first, idx, rest, st') →
    (first = [] → idx = some st.n ∧ st'.n = st.n + 1 ∧ st.an ≠ .manual ∧ st'.an = .auto) ∧
    (first ≠ [] → st'.n = st.n ∧
      (idx.isSome → st.an ≠ .auto ∧ st'.an = .manual) ∧ (idx.isNone → st'.an = st.an))

theorem autoNumberingRule_proven : AutoNumberingRule := by
  intro s st first idx rest st' h
  simp only [fieldNameSplit, bind, Except.bind] at h
  generalize hf : s.takeWhile (fun c => !isFieldStop c) = f at h
  cases hi : fieldInteger f with
  | error e =>
    rw [hi] at h
    cases h
  | ok i =>
    rw [hi] at h
    simp only at h
    cases hempty : f with
    | nil =>
      subst hempty
      have hin : fieldInteger [] = .ok Option.none := rfl
      simp only [hin, Except.ok.injEq] at hi
      subst hi
      cases han : st.an <;>
        simp [han, autonumberStateError] at h <;>
        (obtain ⟨rfl, rfl, -, rfl⟩ := h; simp [han])
    | cons a t =>
      subst hempty
      cases i with
      | none =>
        simp only [List.isEmpty_cons, Option.isSome_none, Bool.or_self, Bool.false_eq_true, if_false,
          Bool.and_false, Bool.false_and, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -, rfl⟩ := h
        simp
      | some n =>
        cases han : st.an <;>
          simp [han, autonumberStateError] at h <;>
          (obtain ⟨rfl, rfl, -, rfl⟩ := h; simp [han])

/-! ## Conversions -/

/-- `{!c}` for a character that is none of `r`, `s`, `a` is refused: the grammar has exactly those
three conversions. -/
def ConversionChecked : Prop :=
  ∀ (c : Nat) (x : GObj), c ≠ 114 → c ≠ 115 → c ≠ 97 →
    ∃ e, doStringFormat [123, 33, c, 125] [x] Option.none = .error e

/-- `'{!\x00}'.format(1)` is `'1'`: a NUL after `!` is taken for the NUL that stands for "no
conversion". -/
theorem conversionChecked_refuted : ¬ ConversionChecked := by
  intro h
  obtain ⟨e, he⟩ := h 0 (.int 1) (by decide) (by decide) (by decide)
  have hok : (doStringFormat [123, 33, 0, 125] [.int 1] Option.none).toBool = true := by
    decide +kernel
  rw [he] at hok
  cases hok

/-- The narrow form: every character but NUL is checked. The error is the exact one, for every
object in the argument tuple. -/
def ConversionRejected : Prop :=
  ∀ (c : Nat) (x : GObj), c ≠ 0 → c ≠ 114 → c ≠ 115 → c ≠ 97 →
    doStringFormat [123, 33, c, 125] [x] Option.none = .error (unknownConversion c)

theorem conversionRejected_proven : ConversionRejected := by
  intro c x h0 h1 h2 h3
  have e1 : (c == 114) = false := beq_eq_false_iff_ne.2 h1
  have e2 : (c == 115) = false := beq_eq_false_iff_ne.2 h2
  have e3 : (c == 97) = false := beq_eq_false_iff_ne.2 h3
  have e0 : (c != 0) = true := by simpa using h0
  have hz : doConversion x c = .error (unknownConversion c) := by
    simp [doConversion, e1, e2, e3]
  simp [doStringFormat, buildString, doMarkup, markupNext, isBrace, parseField, fieldNameScan,
    outputMarkup, getFieldObject, fieldNameSplit, fieldInteger, isFieldStop, autonumberStateError,
    walkField, fieldNameNext, bind, Except.bind, e0, hz, pure, Except.pure]

/-! ## `render_field` against `PyObject_Format` -/

/-- `render_field` skips the lookup of `__format__` for the exact types. It gives what
`format(obj, spec)` gives, for every object and spec. -/
def RenderFieldIsFormat : Prop := ∀ (o : GObj) (spec : Str), renderField o spec = pyObjectFormat o spec

theorem renderFieldIsFormat_proven : RenderFieldIsFormat := by
  intro o spec
  cases o <;> cases spec <;> rfl

/-! ## The whole path -/

theorem specScan_plain : ∀ (spec r : List Nat) (acc : Str) (e : Bool),
    (∀ c ∈ spec, c ≠ 123 ∧ c ≠ 125) →
    specScan (spec ++ 125 :: r) 1 acc e = .ok (acc ++ spec, e, r) := by
  intro spec
  induction spec with
  | nil =>
    intro r acc e _
    simp [specScan]
  | cons x t ih =>
    intro r acc e h
    have hx := h x List.mem_cons_self
    have a1 : (x == 123) = false := beq_eq_false_iff_ne.2 hx.1
    have a2 : (x == 125) = false := beq_eq_false_iff_ne.2 hx.2
    simp only [List.cons_append, specScan, a1, a2, Bool.false_eq_true, if_false]
    rw [ih r _ e (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    simp

theorem markup_field (spec : Str) (h : ∀ c ∈ spec, c ≠ 123 ∧ c ≠ 125) :
    markupNext ([123, 48, 58] ++ spec ++ [125]) =
      .ok (some ([], some { name := [48], spec := some spec, conv := 0, expand := false }, [])) := by
  have hs := specScan_plain spec [] [] false h
  have hscan : specScan (spec ++ [125]) 1 [] false = .ok (spec, false, []) := by simpa using hs
  have hfield : parseField (48 :: 58 :: (spec ++ [125])) =
      .ok ({ name := [48], spec := some spec, conv := 0, expand := false }, []) := by
    simp [parseField, fieldNameScan, hscan, bind, Except.bind, pure, Except.pure]
  have e : ([123, 48, 58] ++ spec ++ [125] : List Nat) = 123 :: 48 :: 58 :: (spec ++ [125]) := rfl
  rw [e]
  simp [markupNext, isBrace, hfield, bind, Except.bind, pure, Except.pure]

/-- `'{0:spec}'.format(x)` is `format(x, spec)`, for every object, spec included, as the docs say a
replacement field does. The spec has no braces, or it would be a nested field. The path runs from
`MarkupIterator_next` through `parse_field`, `get_field_object` and `output_markup` to
`render_field`. -/
def FormatFieldIsBuiltin : Prop :=
  ∀ (x : GObj) (spec : Str), (∀ c ∈ spec, c ≠ 123 ∧ c ≠ 125) →
    doStringFormat ([123, 48, 58] ++ spec ++ [125]) [x] Option.none = pyObjectFormat x spec

theorem digit48 : toDecimalDigit 48 = 0 := by decide +kernel

/-- One field and nothing after it, with `expand` left opaque. -/
theorem doMarkup_one (expand : Str → FSt → Py (Str × FSt)) (args : Option (List GObj))
    (kw : Option KwMap) (s : List Nat) (f : MField) (st st' : FSt) (j : Nat) (r : Py Str)
    (hm : markupNext s = .ok (some ([], some f, [])))
    (ho : outputMarkup expand args kw f st = (r >>= fun t => .ok (t, st'))) :
    doMarkup expand args kw (j + 2) s st [] = (r >>= fun t => .ok (t, st')) := by
  have hnil : markupNext [] = .ok Option.none := rfl
  simp only [doMarkup, hm, bind, Except.bind]
  simp only [bind, Except.bind] at ho
  rw [ho]
  cases r with
  | error e => rfl
  | ok t => simp [doMarkup, hnil]

theorem formatFieldIsBuiltin_proven : FormatFieldIsBuiltin := by
  intro x spec h
  have hint : fieldInteger [48] = .ok (some 0) := by
    simp [fieldInteger, fieldIntegerLoop, digit48]
    unfold ssizeMax
    decide
  have hsplit : fieldNameSplit [48] {} = .ok ([48], some 0, [], { an := .manual }) := by
    simp [fieldNameSplit, hint, isFieldStop, bind, Except.bind, autonumberStateError, pure, Except.pure]
  have hget : getFieldObject [48] (some [x]) Option.none {} = .ok (x, { an := .manual }) := by
    simp [getFieldObject, hsplit, walkField, fieldNameNext, bind, Except.bind, pure, Except.pure]
  have hmark := markup_field spec h
  have hout : ∀ expand : Str → FSt → Py (Str × FSt),
      outputMarkup expand (some [x]) Option.none
        { name := [48], spec := some spec, conv := 0, expand := false } {} =
      (renderField x spec >>= fun t => .ok (t, { an := .manual })) := by
    intro expand
    simp [outputMarkup, hget, bind, Except.bind, pure, Except.pure]
  rw [← renderFieldIsFormat_proven x spec]
  obtain ⟨j, hj⟩ : ∃ j, ([123, 48, 58] ++ spec ++ [125] : List Nat).length + 1 = j + 2 :=
    ⟨spec.length + 3, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
  have hb : buildString (some [x]) Option.none 2 ([123, 48, 58] ++ spec ++ [125]) {} =
      doMarkup (buildString (some [x]) Option.none 1) (some [x]) Option.none (j + 2)
        ([123, 48, 58] ++ spec ++ [125]) {} [] := by
    rw [← hj]
    rfl
  rw [doStringFormat, hb, doMarkup_one _ _ _ _ _ _ _ j _ hmark (hout _)]
  cases renderField x spec <;> rfl

/-! ## Escaped braces -/

def escapeBraces (s : Str) : Str := s.flatMap fun c => if isBrace c then [c, c] else [c]

theorem tw_app (p : Nat → Bool) (pre : List Nat) (b : Nat) (r : List Nat) (hp : ∀ c ∈ pre, p c = true)
    (hb : p b = false) : (pre ++ b :: r).takeWhile p = pre ∧ (pre ++ b :: r).dropWhile p = b :: r := by
  induction pre with
  | nil => simp [hb]
  | cons a t ih =>
    have ha := hp a List.mem_cons_self
    obtain ⟨i1, i2⟩ := ih (fun c hc => hp c (List.mem_cons_of_mem _ hc))
    simp [ha, i1, i2]

theorem escape_plain (pre : List Nat) (hp : ∀ c ∈ pre, (!isBrace c) = true) : escapeBraces pre = pre := by
  induction pre with
  | nil => rfl
  | cons a t ih =>
    have ha := hp a List.mem_cons_self
    have hb : isBrace a = false := by simpa using ha
    have := ih (fun c hc => hp c (List.mem_cons_of_mem _ hc))
    simp only [escapeBraces, List.flatMap_cons, hb, Bool.false_eq_true, if_false] at this ⊢
    simp [this]

theorem split_brace (s : List Nat) :
    (∀ c ∈ s, (!isBrace c) = true) ∨
      ∃ pre b r, s = pre ++ b :: r ∧ (∀ c ∈ pre, (!isBrace c) = true) ∧ isBrace b = true := by
  induction s with
  | nil => exact Or.inl (by simp)
  | cons a t ih =>
    by_cases ha : isBrace a = true
    · exact Or.inr ⟨[], a, t, rfl, by simp, ha⟩
    · have ha' : (!isBrace a) = true := by simpa using ha
      rcases ih with h | ⟨pre, b, r, rfl, h1, h2⟩
      · refine Or.inl fun c hc => ?_
        rcases List.mem_cons.1 hc with rfl | hc
        · exact ha'
        · exact h c hc
      · refine Or.inr ⟨a :: pre, b, r, rfl, ?_, h2⟩
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact ha'
        · exact h1 c hc

theorem nil_of_empty {l : List Nat} (h : l.isEmpty = true) : l = [] := by
  cases l <;> simp_all

theorem tw_all (p : Nat → Bool) (s : List Nat) (h : ∀ c ∈ s, p c = true) : s.takeWhile p = s := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    have ha := h a List.mem_cons_self
    simp [ha, ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]

theorem dw_all (p : Nat → Bool) (s : List Nat) (h : ∀ c ∈ s, p c = true) : s.dropWhile p = [] := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    have ha := h a List.mem_cons_self
    simp [ha, ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]

theorem markup_plain (s : List Nat) (hne : s ≠ []) (hs : ∀ c ∈ s, (!isBrace c) = true) :
    markupNext s = .ok (some (s, Option.none, [])) := by
  have h1 := tw_all (fun c => !isBrace c) s hs
  have h2 := dw_all (fun c => !isBrace c) s hs
  have h3 : s.isEmpty = false := by cases s <;> simp_all
  simp [markupNext, h1, h2, h3, pure, Except.pure]

theorem markup_escape (pre : List Nat) (b : Nat) (r : List Nat) (hp : ∀ c ∈ pre, (!isBrace c) = true)
    (hb : isBrace b = true) :
    markupNext (pre ++ b :: b :: r) = .ok (some (pre ++ [b], Option.none, r)) := by
  have hb' : (fun c => !isBrace c) b = false := by simp [hb]
  obtain ⟨h1, h2⟩ := tw_app (fun c => !isBrace c) pre b (b :: r) hp hb'
  have h3 : (pre ++ b :: b :: r).isEmpty = false := by simp
  simp only [markupNext, h3, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure]
  simp only [h1, h2]
  have e : (b == 125 && b != b) = false := by simp
  simp [e]

theorem escape_app (pre : List Nat) (b : Nat) (r : List Nat) (hp : ∀ c ∈ pre, (!isBrace c) = true)
    (hb : isBrace b = true) : escapeBraces (pre ++ b :: r) = pre ++ b :: b :: escapeBraces r := by
  have h := escape_plain pre hp
  unfold escapeBraces at h ⊢
  simp [List.flatMap_append, h, hb]

/-- A doubled brace is a brace. -/
theorem doMarkup_escape (expand : Str → FSt → Py (Str × FSt)) (args : Option (List GObj))
    (kw : Option KwMap) :
    ∀ (fuel : Nat) (s : List Nat) (st : FSt) (out : Str), s.length < fuel →
      doMarkup expand args kw fuel (escapeBraces s) st out = .ok (out ++ s, st) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; omega
  | succ fuel ih =>
    intro s st out hf
    rcases split_brace s with hs | ⟨pre, b, r, rfl, hp, hb⟩
    · rw [escape_plain s hs]
      have hnil : markupNext [] = .ok Option.none := rfl
      by_cases hne : s = []
      · subst hne
        rw [doMarkup]
        simp only [bind, Except.bind, hnil]
        simp
      · have hL : 0 < s.length := List.length_pos_iff.2 hne
        obtain ⟨j, rfl⟩ : ∃ j, fuel = j + 1 := ⟨fuel - 1, by omega⟩
        simp [doMarkup, markup_plain s hne hs, bind, Except.bind, hnil]
    · rw [escape_app pre b r hp hb]
      simp only [doMarkup, markup_escape pre b (escapeBraces r) hp hb, bind, Except.bind]
      rw [ih r st _ (by simp at hf; omega)]
      simp

/-- `{{` and `}}` are the way to write a brace: doubling every brace of any string and formatting
gives the string back, whatever the arguments. A string with no brace is its own format, for the
same reason. -/
def BraceEscapeRoundTrip : Prop :=
  ∀ (s : Str) (args : List GObj) (kw : Option KwMap),
    doStringFormat (escapeBraces s) args kw = .ok s

theorem escape_len (s : List Nat) : s.length ≤ (escapeBraces s).length := by
  induction s with
  | nil => simp [escapeBraces]
  | cons a t ih =>
    have e : escapeBraces (a :: t) = (if isBrace a = true then [a, a] else [a]) ++ escapeBraces t := by
      simp [escapeBraces]
    rw [e]
    split <;> simp only [List.length_append, List.length_cons, List.length_nil] <;> omega

theorem braceEscapeRoundTrip_proven : BraceEscapeRoundTrip := by
  intro s args kw
  have h := doMarkup_escape (buildString (some args) kw 1) (some args) kw ((escapeBraces s).length + 1)
    s {} [] (by have := escape_len s; omega)
  have hb : buildString (some args) kw 2 (escapeBraces s) {} =
      doMarkup (buildString (some args) kw 1) (some args) kw ((escapeBraces s).length + 1)
        (escapeBraces s) {} [] := rfl
  rw [doStringFormat, hb, h]
  simp [bind, Except.bind]

/-! ## `format_map` -/

/-- `format_map` has no positional arguments: a field that names one is refused, for every field
name, mapping and state, before the mapping is touched. -/
def FormatMapNoPositional : Prop :=
  (∀ (input first rest : Str) (i : Nat) (m : KwMap) (st st' : FSt),
    fieldNameSplit input st = .ok (first, some i, rest, st') →
    getFieldObject input Option.none (some m) st =
      .error (.valueError "Format string contains positional fields")) ∧
  (∀ m : KwMap, doStringFormatMap [123, 125] m =
    .error (.valueError "Format string contains positional fields"))

theorem formatMapNoPositional_proven : FormatMapNoPositional := by
  constructor
  · intro input first rest i m st st' h
    simp [getFieldObject, h, bind, Except.bind]
  · intro m
    simp [doStringFormatMap, buildString, doMarkup, markupNext, isBrace, parseField, fieldNameScan,
      outputMarkup, getFieldObject, fieldNameSplit, fieldInteger, isFieldStop, autonumberStateError,
      bind, Except.bind, pure, Except.pure]

/-! ## `_string` -/

/-- `string.Formatter` parses with `_string.formatter_parser`, and `str.format` with the same
iterator: whatever `str.format` accepts, the parser accepts. -/
def FormatterParserAccepts : Prop :=
  ∀ (s : Str) (args : List GObj) (kw : Option KwMap) (r : Str),
    doStringFormat s args kw = .ok r → ∃ items, formatterParser (s.length + 1) s [] = .ok items

theorem parser_of_markup (expand : Str → FSt → Py (Str × FSt)) (args : Option (List GObj))
    (kw : Option KwMap) : ∀ (fuel : Nat) (s : List Nat) (st : FSt) (out : Str) (acc : List ParserItem)
      (r : Str) (st' : FSt),
      doMarkup expand args kw fuel s st out = .ok (r, st') → ∃ items, formatterParser fuel s acc = .ok items := by
  intro fuel
  induction fuel with
  | zero =>
    intro s st out acc r st' h
    simp [doMarkup] at h
  | succ fuel ih =>
    intro s st out acc r st' h
    simp only [doMarkup, bind, Except.bind] at h
    simp only [formatterParser, bind, Except.bind]
    cases hm : markupNext s with
    | error e =>
      rw [hm] at h
      cases h
    | ok v =>
      rw [hm] at h
      cases v with
      | none => exact ⟨_, rfl⟩
      | some p =>
        obtain ⟨literal, field, rest⟩ := p
        cases field with
        | none => exact ih _ _ _ _ _ _ h
        | some f =>
          simp only at h
          split at h
          · cases h
          · exact ih _ _ _ _ _ _ h

theorem formatterParserAccepts_proven : FormatterParserAccepts := by
  intro s args kw r h
  have hb : buildString (some args) kw 2 s {} =
      doMarkup (buildString (some args) kw 1) (some args) kw (s.length + 1) s {} [] := rfl
  rw [doStringFormat, hb] at h
  cases hv : doMarkup (buildString (some args) kw 1) (some args) kw (s.length + 1) s {} [] with
  | error e =>
    rw [hv] at h
    cases h
  | ok v =>
    obtain ⟨r', st'⟩ := v
    exact parser_of_markup _ _ _ _ _ _ _ _ _ _ hv

/-! ## Field names -/

/-- A field name's tail written out: `.name` for `true`, `[name]` for `false`. -/
def renderSteps : List (Bool × Str) → Str
  | [] => []
  | (true, n) :: t => 46 :: n ++ renderSteps t
  | (false, s) :: t => 91 :: s ++ 93 :: renderSteps t

/-- A step that reads back as itself: an attribute with no `.` or `[`, or an item with no `]` that
is no number, since a number comes back as an int. -/
def StepOk : Bool × Str → Prop
  | (true, n) => n ≠ [] ∧ ∀ c ∈ n, (!isFieldStop c) = true
  | (false, s) => s ≠ [] ∧ ∀ c ∈ s, (c != 93) = true ∧ toDecimalDigit c < 0

theorem nonNumeric_none (s : Str) (h : ∀ c ∈ s, toDecimalDigit c < 0) : fieldInteger s = .ok Option.none := by
  cases s with
  | nil => rfl
  | cons a t =>
    have ha := h a List.mem_cons_self
    simp [fieldInteger, fieldIntegerLoop, ha]

theorem render_head (t : List (Bool × Str)) :
    renderSteps t = [] ∨ ∃ b r, renderSteps t = b :: r ∧ isFieldStop b = true := by
  cases t with
  | nil => exact Or.inl rfl
  | cons x t =>
    obtain ⟨f, s⟩ := x
    cases f with
    | true => exact Or.inr ⟨46, _, rfl, by decide⟩
    | false => exact Or.inr ⟨91, _, rfl, by decide⟩

theorem split_field (n : Str) (t : List (Bool × Str)) (hn : ∀ c ∈ n, (!isFieldStop c) = true) :
    (n ++ renderSteps t).takeWhile (fun c => !isFieldStop c) = n ∧
      (n ++ renderSteps t).dropWhile (fun c => !isFieldStop c) = renderSteps t := by
  rcases render_head t with h | ⟨b, r, h, hb⟩
  · rw [h]
    simp only [List.append_nil]
    exact ⟨tw_all _ n hn, dw_all _ n hn⟩
  · rw [h]
    exact tw_app _ n b r hn (by simp [hb])

/-- `_string.formatter_field_name_split` reads back what a field name says, for every chain of
attributes and non-numeric items. It runs `FieldNameIterator_next` with both its helpers on every
step. -/
def FieldNameRoundTrip : Prop :=
  ∀ (first : Str) (steps : List (Bool × Str)), (∀ c ∈ first, (!isFieldStop c) = true ∧ toDecimalDigit c < 0) →
    (∀ x ∈ steps, StepOk x) →
    formatterFieldNameSplit (first ++ renderSteps steps) =
      .ok (.inr first, steps.map fun x => (x.1, .inr x.2))

theorem fieldNameItems_steps : ∀ (steps : List (Bool × Str)) (fuel : Nat) (acc : List (Bool × (Nat ⊕ Str))),
    (∀ x ∈ steps, StepOk x) → (renderSteps steps).length < fuel →
    fieldNameItems fuel (renderSteps steps) acc = .ok (acc ++ steps.map fun x => (x.1, .inr x.2)) := by
  intro steps
  induction steps with
  | nil =>
    intro fuel acc _ hf
    obtain ⟨j, rfl⟩ : ∃ j, fuel = j + 1 := ⟨fuel - 1, by simp [renderSteps] at hf; omega⟩
    simp [renderSteps, fieldNameItems, fieldNameNext, bind, Except.bind]
  | cons x t ih =>
    intro fuel acc h hf
    have hx := h x List.mem_cons_self
    have ht : ∀ y ∈ t, StepOk y := fun y hy => h y (List.mem_cons_of_mem _ hy)
    obtain ⟨f, s⟩ := x
    obtain ⟨j, rfl⟩ : ∃ j, fuel = j + 1 := ⟨fuel - 1, by omega⟩
    cases f with
    | true =>
      obtain ⟨hne, hs⟩ := hx
      obtain ⟨h1, h2⟩ := split_field s t hs
      have hlen : (renderSteps t).length < j := by
        simp only [renderSteps, List.length_cons, List.length_append] at hf
        have := List.length_pos_iff.2 hne
        omega
      have hstep : fieldNameNext (46 :: s ++ renderSteps t) = .ok (.attr s (renderSteps t)) := by
        have he : s.isEmpty = false := by cases s <;> simp_all
        simp [fieldNameNext, attrName, h1, h2, he]
      simp only [renderSteps, fieldNameItems, hstep, bind, Except.bind]
      rw [ih j _ ht hlen]
      simp
    | false =>
      obtain ⟨hne, hs⟩ := hx
      have hbad : (fun c => c != 93) 93 = false := by decide
      obtain ⟨h1, h2⟩ := tw_app (fun c => c != 93) s 93 (renderSteps t) (fun c hc => (hs c hc).1) hbad
      have hint := nonNumeric_none s (fun c hc => (hs c hc).2)
      have hlen : (renderSteps t).length < j := by
        simp only [renderSteps, List.length_cons, List.length_append] at hf
        have := List.length_pos_iff.2 hne
        omega
      have hstep : fieldNameNext (91 :: s ++ 93 :: renderSteps t) = .ok (.item (.name s) (renderSteps t)) := by
        have he : s.isEmpty = false := by cases s <;> simp_all
        simp [fieldNameNext, h1, h2, he, hint, bind, Except.bind]
      simp only [renderSteps, fieldNameItems, hstep, bind, Except.bind]
      rw [ih j _ ht hlen]
      simp

theorem fieldNameRoundTrip_proven : FieldNameRoundTrip := by
  intro first steps hf hs
  obtain ⟨h1, h2⟩ := split_field first steps (fun c hc => (hf c hc).1)
  have hint := nonNumeric_none first (fun c hc => (hf c hc).2)
  have hi := fieldNameItems_steps steps ((renderSteps steps).length + 1) [] hs (by omega)
  simp only [formatterFieldNameSplit, h1, h2, hint, hi, bind, Except.bind]
  simp

/-- What `formatter_parser` reports. A field with a spec gives its name and spec and no conversion;
text with no field gives `None` in all three places, which is what tells `string.Formatter` there
is nothing to format; and anything but a `str` is refused. -/
def FormatterParserReads : Prop :=
  (∀ spec : Str, (∀ c ∈ spec, c ≠ 123 ∧ c ≠ 125) →
    formatterParserObj (.str ([123, 48, 58] ++ spec ++ [125])) =
      .ok [([], some [48], some spec, Option.none)]) ∧
  (∀ s : Str, s ≠ [] → (∀ c ∈ s, (!isBrace c) = true) →
    formatterParserObj (.str s) = .ok [(s, Option.none, Option.none, Option.none)]) ∧
  (∀ v : Int, formatterParserObj (.int v) = .error (.typeError "expected str, got int"))

theorem formatterParserReads_proven : FormatterParserReads := by
  have hnil : markupNext [] = .ok Option.none := rfl
  refine ⟨?_, ?_, fun _ => rfl⟩
  · intro spec h
    obtain ⟨j, hj⟩ : ∃ j, ([123, 48, 58] ++ spec ++ [125] : List Nat).length + 1 = j + 2 :=
      ⟨spec.length + 3, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
    simp only [formatterParserObj, hj, formatterParser, markup_field spec h, bind, Except.bind, hnil]
    rfl
  · intro s hne hs
    have hL : 0 < s.length := List.length_pos_iff.2 hne
    obtain ⟨j, hj⟩ : ∃ j, s.length = j + 1 := ⟨s.length - 1, by omega⟩
    simp only [formatterParserObj, hj, formatterParser, markup_plain s hne hs, bind, Except.bind, hnil]
    rfl

/-! ## Nested fields -/

theorem digit49 : toDecimalDigit 49 = 1 := by decide +kernel

theorem fi48 : fieldInteger [48] = .ok (some 0) := by
  simp [fieldInteger, fieldIntegerLoop, digit48]
  unfold ssizeMax
  decide

theorem fi49 : fieldInteger [49] = .ok (some 1) := by
  simp [fieldInteger, fieldIntegerLoop, digit49]
  unfold ssizeMax
  decide

theorem sp48 : fieldNameSplit [48] {} = .ok ([48], some 0, [], { an := .manual }) := by
  simp [fieldNameSplit, fi48, isFieldStop, bind, Except.bind, autonumberStateError, pure, Except.pure]

theorem sp49 : fieldNameSplit [49] { an := .manual } = .ok ([49], some 1, [], { an := .manual }) := by
  simp [fieldNameSplit, fi49, isFieldStop, bind, Except.bind, autonumberStateError, pure, Except.pure]

/-- `output_markup` for a field with no conversion, once the object is found. -/
theorem output_plain (expand : Str → FSt → Py (Str × FSt)) (args : Option (List GObj)) (kw : Option KwMap)
    (f : MField) (st st' : FSt) (o : GObj) (hc : f.conv = 0)
    (hg : getFieldObject f.name args kw st = .ok (o, st')) :
    outputMarkup expand args kw f st =
      ((if f.expand = true then expand (f.spec.getD []) st' else .ok (f.spec.getD [], st')) >>= fun p =>
        renderField o p.1 >>= fun t => .ok (t, p.2)) := by
  have e : (f.conv != 0) = false := by simp [hc]
  simp only [outputMarkup, hg, e, bind, Except.bind, Bool.false_eq_true, if_false, pure, Except.pure]
  split
  · generalize expand _ _ = r
    cases r with
    | error x => rfl
    | ok p =>
      obtain ⟨a, b⟩ := p
      simp only
  · simp only

/-- The text a nested field expands to is used as the spec and is not parsed again, so it can hold
any character, braces included: `'{0:{1}}'.format(x, spec)` is `format(x, spec)`, for every object
and every string. -/
def NestedSpecExpands : Prop :=
  ∀ (x : GObj) (spec : Str),
    doStringFormat [123, 48, 58, 123, 49, 125, 125] [x, .str spec] Option.none = pyObjectFormat x spec

theorem nestedSpecExpands_proven : NestedSpecExpands := by
  intro x spec
  rw [← renderFieldIsFormat_proven x spec]
  let args : Option (List GObj) := some [x, .str spec]
  have hg0 : getFieldObject [48] args Option.none {} = .ok (x, { an := .manual }) := by
    simp [getFieldObject, sp48, walkField, fieldNameNext, bind, Except.bind, pure, Except.pure, args]
  have hg1 : getFieldObject [49] args Option.none { an := .manual } = .ok (.str spec, { an := .manual }) := by
    simp [getFieldObject, sp49, walkField, fieldNameNext, bind, Except.bind, pure, Except.pure, args]
  have hm0 : markupNext [123, 48, 58, 123, 49, 125, 125] =
      .ok (some ([], some { name := [48], spec := some [123, 49, 125], conv := 0, expand := true }, [])) := rfl
  have hm1 : markupNext [123, 49, 125] =
      .ok (some ([], some { name := [49], spec := Option.none, conv := 0, expand := false }, [])) := rfl
  have hin : buildString args Option.none 1 [123, 49, 125] { an := .manual } =
      .ok (spec, { an := .manual }) := by
    have hb : buildString args Option.none 1 [123, 49, 125] { an := .manual } =
        doMarkup (buildString args Option.none 0) args Option.none (2 + 2) [123, 49, 125]
          { an := .manual } [] := rfl
    rw [hb]
    have ho := output_plain (buildString args Option.none 0) args Option.none
      { name := [49], spec := Option.none, conv := 0, expand := false } { an := .manual } { an := .manual }
      (.str spec) rfl hg1
    have ho' : outputMarkup (buildString args Option.none 0) args Option.none
        { name := [49], spec := Option.none, conv := 0, expand := false } { an := .manual } =
        ((.ok spec : Py Str) >>= fun t => .ok (t, { an := .manual })) := by
      rw [ho]
      rfl
    rw [doMarkup_one _ _ _ _ _ _ _ 2 _ hm1 ho']
    rfl
  have ho : outputMarkup (buildString args Option.none 1) args Option.none
      { name := [48], spec := some [123, 49, 125], conv := 0, expand := true } {} =
      (renderField x spec >>= fun t => .ok (t, { an := .manual })) := by
    rw [output_plain _ _ _ _ _ _ x rfl hg0]
    simp only [if_true, Option.getD_some, hin, bind, Except.bind]
  have hb : buildString args Option.none 2 [123, 48, 58, 123, 49, 125, 125] {} =
      doMarkup (buildString args Option.none 1) args Option.none (6 + 2)
        [123, 48, 58, 123, 49, 125, 125] {} [] := rfl
  rw [doStringFormat, hb, doMarkup_one _ _ _ _ _ _ _ 6 _ hm0 ho]
  cases renderField x spec <;> rfl

/-- A nested field shares the outer field's numbering, and the outer field numbers first:
`'{:{}}'.format(x, spec)` is `format(x, spec)`. -/
def NestedAutoNumbering : Prop :=
  ∀ (x : GObj) (spec : Str),
    doStringFormat [123, 58, 123, 125, 125] [x, .str spec] Option.none = pyObjectFormat x spec

theorem nestedAutoNumbering_proven : NestedAutoNumbering := by
  intro x spec
  rw [← renderFieldIsFormat_proven x spec]
  let args : Option (List GObj) := some [x, .str spec]
  have hs0 : fieldNameSplit [] ({} : FSt) = .ok ([], some 0, [], { an := .auto, n := 1 }) := rfl
  have hs1 : fieldNameSplit [] ({ an := .auto, n := 1 } : FSt) = .ok ([], some 1, [], { an := .auto, n := 2 }) := rfl
  have hg0 : getFieldObject [] args Option.none {} = .ok (x, { an := .auto, n := 1 }) := by
    simp [getFieldObject, hs0, walkField, fieldNameNext, bind, Except.bind, pure, Except.pure, args]
  have hg1 : getFieldObject [] args Option.none { an := .auto, n := 1 } =
      .ok (.str spec, { an := .auto, n := 2 }) := by
    simp [getFieldObject, hs1, walkField, fieldNameNext, bind, Except.bind, pure, Except.pure, args]
  have hm0 : markupNext [123, 58, 123, 125, 125] =
      .ok (some ([], some { name := [], spec := some [123, 125], conv := 0, expand := true }, [])) := rfl
  have hm1 : markupNext [123, 125] =
      .ok (some ([], some { name := [], spec := Option.none, conv := 0, expand := false }, [])) := rfl
  have hin : buildString args Option.none 1 [123, 125] { an := .auto, n := 1 } =
      .ok (spec, { an := .auto, n := 2 }) := by
    have hb : buildString args Option.none 1 [123, 125] { an := .auto, n := 1 } =
        doMarkup (buildString args Option.none 0) args Option.none (1 + 2) [123, 125]
          { an := .auto, n := 1 } [] := rfl
    rw [hb]
    have ho' : outputMarkup (buildString args Option.none 0) args Option.none
        { name := [], spec := Option.none, conv := 0, expand := false } { an := .auto, n := 1 } =
        ((.ok spec : Py Str) >>= fun t => .ok (t, { an := .auto, n := 2 })) := by
      rw [output_plain _ _ _ _ _ _ (.str spec) rfl hg1]
      rfl
    rw [doMarkup_one _ _ _ _ _ _ _ 1 _ hm1 ho']
    rfl
  have ho : outputMarkup (buildString args Option.none 1) args Option.none
      { name := [], spec := some [123, 125], conv := 0, expand := true } {} =
      (renderField x spec >>= fun t => .ok (t, { an := .auto, n := 2 })) := by
    rw [output_plain _ _ _ _ _ _ x rfl hg0]
    simp only [if_true, Option.getD_some, hin, bind, Except.bind]
  have hb : buildString args Option.none 2 [123, 58, 123, 125, 125] {} =
      doMarkup (buildString args Option.none 1) args Option.none (4 + 2) [123, 58, 123, 125, 125] {} [] := rfl
  rw [doStringFormat, hb, doMarkup_one _ _ _ _ _ _ _ 4 _ hm0 ho]
  cases renderField x spec <;> rfl

/-- A field that fails ends the string. -/
theorem doMarkup_err (expand : Str → FSt → Py (Str × FSt)) (args : Option (List GObj)) (kw : Option KwMap)
    (s rest : List Nat) (f : MField) (st : FSt) (j : Nat) (e : PyExc)
    (hm : markupNext s = .ok (some ([], some f, rest)))
    (ho : outputMarkup expand args kw f st = .error e) :
    doMarkup expand args kw (j + 1) s st [] = .error e := by
  simp only [doMarkup, hm, bind, Except.bind]
  rw [ho]

/-- PEP 3101 allows one level of nesting. `'{0:{1:{2}}}'` is refused, for every object, before
anything is rendered: the recursion check of `build_string` is reached by the third level. -/
def RecursionLimit : Prop :=
  ∀ (x y : GObj) (rest : List GObj),
    doStringFormat [123, 48, 58, 123, 49, 58, 123, 50, 125, 125, 125] (x :: y :: rest) Option.none =
      .error (.valueError "Max string recursion exceeded")

theorem recursionLimit_proven : RecursionLimit := by
  intro x y rest
  let args : Option (List GObj) := some (x :: y :: rest)
  let spec1 : Str := [123, 49, 58, 123, 50, 125, 125]
  let spec2 : Str := [123, 50, 125]
  have hg0 : getFieldObject [48] args Option.none {} = .ok (x, { an := .manual }) := by
    simp [getFieldObject, sp48, walkField, fieldNameNext, bind, Except.bind, pure, Except.pure, args]
  have hg1 : getFieldObject [49] args Option.none { an := .manual } = .ok (y, { an := .manual }) := by
    simp [getFieldObject, sp49, walkField, fieldNameNext, bind, Except.bind, pure, Except.pure, args]
  have hm0 : markupNext [123, 48, 58, 123, 49, 58, 123, 50, 125, 125, 125] =
      .ok (some ([], some { name := [48], spec := some spec1, conv := 0, expand := true }, [])) := rfl
  have hm1 : markupNext spec1 =
      .ok (some ([], some { name := [49], spec := some spec2, conv := 0, expand := true }, [])) := rfl
  have hin : buildString args Option.none 1 spec1 { an := .manual } =
      .error (.valueError "Max string recursion exceeded") := by
    have hb : buildString args Option.none 1 spec1 { an := .manual } =
        doMarkup (buildString args Option.none 0) args Option.none (6 + 2) spec1 { an := .manual } [] := rfl
    rw [hb]
    refine doMarkup_err _ _ _ _ _ _ _ _ _ hm1 ?_
    rw [output_plain _ _ _ _ _ _ y rfl hg1]
    rfl
  have hb : buildString args Option.none 2 [123, 48, 58, 123, 49, 58, 123, 50, 125, 125, 125] {} =
      doMarkup (buildString args Option.none 1) args Option.none (10 + 2)
        [123, 48, 58, 123, 49, 58, 123, 50, 125, 125, 125] {} [] := rfl
  have ho : outputMarkup (buildString args Option.none 1) args Option.none
      { name := [48], spec := some spec1, conv := 0, expand := true } {} =
      .error (.valueError "Max string recursion exceeded") := by
    rw [output_plain _ _ _ _ _ _ x rfl hg0]
    simp only [if_true, Option.getD_some, hin, bind, Except.bind]
  rw [doStringFormat, hb, doMarkup_err _ _ _ _ _ _ _ _ _ hm0 ho]
  rfl

/-! ## Many fields -/

/-- `{}` repeated. -/
def fieldRun : Nat → Str
  | 0 => []
  | n + 1 => 123 :: 125 :: fieldRun n

/-- Every field of `'{}{}...'` is its object formatted with an empty spec, in order: the text is
the concatenation, and if a `__format__` or `__str__` fails, the first failure is the exception,
with no later object touched. For every list of objects. -/
def AutoFieldsConcat : Prop :=
  ∀ xs : List GObj,
    doStringFormat (fieldRun xs.length) xs Option.none =
      (xs.mapM (fun x => pyObjectFormat x [])).map List.flatten

theorem markup_auto (r : List Nat) :
    markupNext (123 :: 125 :: r) =
      .ok (some ([], some { name := [], spec := Option.none, conv := 0, expand := false }, r)) := rfl

theorem auto_loop (expand : Str → FSt → Py (Str × FSt)) (all : List GObj) :
    ∀ (rem : List GObj) (fuel k : Nat) (an : ANState) (out : Str), all.drop k = rem → an ≠ .manual →
      rem.length < fuel →
      (doMarkup expand (some all) Option.none fuel (fieldRun rem.length) { an, n := k } out).map (·.1) =
        (rem.mapM (fun x => pyObjectFormat x [])).map (fun ts => out ++ ts.flatten) := by
  intro rem
  induction rem with
  | nil =>
    intro fuel k an out _ _ hf
    obtain ⟨j, rfl⟩ : ∃ j, fuel = j + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hnil : markupNext [] = .ok Option.none := rfl
    simp [fieldRun, doMarkup, hnil, bind, Except.bind, Except.map, pure, Except.pure]
  | cons x t ih =>
    intro fuel k an out hd han hf
    obtain ⟨j, rfl⟩ : ∃ j, fuel = j + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hk : all[k]? = some x := by
      have : (all.drop k)[0]? = some x := by simp [hd]
      simpa [List.getElem?_drop] using this
    have hsplit : fieldNameSplit [] ({ an, n := k } : FSt) = .ok ([], some k, [], { an := .auto, n := k + 1 }) := by
      cases an
      · rfl
      · rfl
      · exact absurd rfl han
    have hg : getFieldObject [] (some all) Option.none { an, n := k } = .ok (x, { an := .auto, n := k + 1 }) := by
      simp [getFieldObject, hsplit, hk, walkField, fieldNameNext, bind, Except.bind, pure, Except.pure]
    have ho := output_plain expand (some all) Option.none
      { name := [], spec := Option.none, conv := 0, expand := false } { an, n := k }
      { an := .auto, n := k + 1 } x rfl hg
    simp only [List.length_cons, fieldRun, doMarkup, markup_auto, bind, Except.bind]
    rw [ho]
    have hdrop : all.drop (k + 1) = t := by
      have := congrArg List.tail hd
      simpa [List.tail_drop] using this
    have hrec := ih j (k + 1) .auto
    simp only [Bool.false_eq_true, if_false, Option.getD_none, List.mapM_cons, bind, Except.bind]
    rw [renderFieldIsFormat_proven]
    cases hp : pyObjectFormat x [] with
    | error e => rfl
    | ok a =>
      have h2 := hrec (out ++ [] ++ a) hdrop (by simp) (by simp at hf; omega)
      simp only
      rw [h2]
      cases hm : List.mapM (fun x => pyObjectFormat x []) t with
      | error e => rfl
      | ok ts => simp [Except.map, pure, Except.pure, List.append_assoc]

theorem fieldRun_len (n : Nat) : (fieldRun n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fieldRun, List.length_cons, ih]
    omega

theorem autoFieldsConcat_proven : AutoFieldsConcat := by
  intro xs
  have h := auto_loop (buildString (some xs) Option.none 1) xs xs ((fieldRun xs.length).length + 1) 0
    .init [] (by simp) (by simp) (by rw [fieldRun_len]; omega)
  have hb : buildString (some xs) Option.none 2 (fieldRun xs.length) {} =
      doMarkup (buildString (some xs) Option.none 1) (some xs) Option.none
        ((fieldRun xs.length).length + 1) (fieldRun xs.length) { an := .init, n := 0 } [] := rfl
  rw [doStringFormat, hb]
  cases hd : doMarkup (buildString (some xs) Option.none 1) (some xs) Option.none
      ((fieldRun xs.length).length + 1) (fieldRun xs.length) { an := .init, n := 0 } [] with
  | error e =>
    rw [hd] at h
    cases hm : List.mapM (fun x => pyObjectFormat x []) xs with
    | error e2 =>
      rw [hm] at h
      simp only [Except.map, Except.error.injEq] at h
      subst h
      rfl
    | ok ts =>
      rw [hm] at h
      simp [Except.map] at h
  | ok v =>
    obtain ⟨r, st⟩ := v
    rw [hd] at h
    cases hm : List.mapM (fun x => pyObjectFormat x []) xs with
    | error e2 =>
      rw [hm] at h
      simp [Except.map] at h
    | ok ts =>
      rw [hm] at h
      simp only [Except.map, Except.ok.injEq] at h
      simp only [bind, Except.bind, Except.map, h]
      simp

end PyLean.UnicodeObj
