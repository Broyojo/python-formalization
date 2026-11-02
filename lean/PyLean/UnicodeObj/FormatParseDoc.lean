import PyLean.UnicodeObj.FormatStrProps
import PyLean.UnicodeObj.FormatProps

/-!
`parse_internal_render_format_spec`, Objects/unicode_formatter.c:386-607, with `get_integer`
(:296-326), `is_alignment_token` (:333-342), `is_sign_element` (:345-354),
`invalid_thousands_separator_type` (:269-280) and `invalid_comma_and_underscore` (:283-286),
against the grammar of Doc/library/string.rst ("Format specification mini-language"):

    format_spec: [options][width_and_precision][type]
    options: [[fill]align][sign]["z"]["#"]["0"]
    width_and_precision: [width_with_grouping][precision_with_grouping]
    width_with_grouping: [width][grouping]
    precision_with_grouping: "." [precision][grouping] | "." grouping

A spec is given by its fields (`SpecFields`) and written out by `renderSpec`. The theorem is that the
parser reads back what was written: every field lands where the docs say, and the refusals come
with their messages. Two writes of a separator (`,_`, `_,`, `,,`, `__`) are included: the first two
are refused by the parser itself, the last two leave a `,` or `_` as the type, which the
validation refuses. Width and precision are runs of decimal digits in any script
(`Py_UNICODE_TODECIMAL`), of any value: above `PY_SSIZE_T_MAX` they are refused, never wrapped.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- The fields of a standard format specifier, as the grammar lists them. -/
structure SpecFields where
  fill : Option Nat
  align : Option Nat
  sign : Option Nat
  z : Bool
  alt : Bool
  zero : Bool
  width : List Nat
  grouping : List Nat
  precision : Option (List Nat × List Nat)
  /-- What follows: empty, the type character, or more (refused). Every
  character of it is one no other field starts with. -/
  tail : List Nat

/-- The spec as text. -/
def renderSpec (d : SpecFields) : Str :=
  (match d.align, d.fill with
   | none, _ => []
   | some a, none => [a]
   | some a, some c => [c, a]) ++
  d.sign.toList ++ (if d.z then [122] else []) ++ (if d.alt then [35] else []) ++
  (if d.zero then [48] else []) ++ d.width ++ d.grouping ++
  (match d.precision with
   | none => []
   | some (p, g) => 46 :: (p ++ g)) ++ d.tail

/-- A separator option as written: none, one, or one of the four doubled forms. -/
def GroupingWritten (g : List Nat) : Prop :=
  g = [] ∨ g = [44] ∨ g = [95] ∨ g = [44, 95] ∨ g = [95, 44] ∨ g = [44, 44] ∨ g = [95, 95]

/-- A character that can only be read as the type: none of the other fields' characters. -/
def TypeChar (t : Nat) : Prop :=
  toDecimalDigit t < 0 ∧ t ≠ 60 ∧ t ≠ 62 ∧ t ≠ 61 ∧ t ≠ 94 ∧ t ≠ 32 ∧ t ≠ 43 ∧ t ≠ 45 ∧
    t ≠ 122 ∧ t ≠ 35 ∧ t ≠ 44 ∧ t ≠ 95 ∧ t ≠ 46

/-- The grammar's constraints. A fill needs an alignment; an alignment is one of `<>=^` and a sign
one of `+- `; width and precision are decimal digits; the tail starts with a type character. The
`'0'` option is written as the `0` before the width, so a width that starts with an ASCII `0` and
has no fill in front is that option (the docs' "preceding the width field by a zero"). The doubled
separators `,,` and `__` stand for a separator followed by a type `,` or `_`, so they have no
precision after them. -/
structure SpecFields.WF (d : SpecFields) : Prop where
  fill : d.fill.isSome → d.align.isSome
  align : ∀ a, d.align = some a → a = 60 ∨ a = 62 ∨ a = 61 ∨ a = 94
  sign : ∀ s, d.sign = some s → s = 43 ∨ s = 45 ∨ s = 32
  width : ∀ c ∈ d.width, 0 ≤ toDecimalDigit c
  zero : d.fill = none → d.zero = false → d.width.head? ≠ some 48
  grouping : GroupingWritten d.grouping
  doubled : (d.grouping = [44, 44] ∨ d.grouping = [95, 95]) → d.precision = none ∧ d.tail = []
  precision : ∀ p g, d.precision = some (p, g) →
    (∀ c ∈ p, 0 ≤ toDecimalDigit c) ∧ (g = [] ∨ g = [44] ∨ g = [95] ∨ g = [44, 95] ∨ g = [95, 44])
  tail : ∀ t ∈ d.tail, TypeChar t

/-- A run of decimal digits as the docs read it: its value, refused above `PY_SSIZE_T_MAX`. -/
def specDigitsValue (ds : List Nat) : Py Int :=
  if decVal ds 0 ≤ ssizeMax then .ok (decVal ds 0)
  else .error (.valueError "Too many decimal digits in format string")

/-- The message for a separator the type does not take, as written at unicode_formatter.c:272-279:
the type as itself between 33 and 127, else in hex. -/
def sepTypeMessage (sep t : Nat) : PyExc :=
  if 32 < t ∧ t < 128 then
    .valueError ("Cannot specify '" ++ String.singleton (Char.ofNat sep) ++ "' with '" ++
      String.singleton (Char.ofNat t) ++ "'.")
  else
    .valueError ("Cannot specify '" ++ String.singleton (Char.ofNat sep) ++ "' with '\\x" ++
      String.ofList (Nat.toDigits 16 t) ++ "'.")

def bothSeparators : PyExc := .valueError "Cannot specify both ',' and '_'."

/-- What a single separator option means; two different ones are refused. -/
def groupingValue : List Nat → Py Nat
  | [] => .ok 0
  | [c] => .ok c
  | [44, 44] => .ok 44
  | [95, 95] => .ok 95
  | _ => .error bothSeparators

/-- An optional run of digits: none is `-1`. -/
def optDigits (ds : List Nat) : Py Int := if ds = [] then .ok (-1) else specDigitsValue ds

/-- The digits of the width: after a written fill, the `0` option is one of them. -/
def widthDigits (d : SpecFields) : List Nat :=
  (if d.zero ∧ d.fill.isSome then [48] else []) ++ d.width

/-- The precision and its separator: no digits and no separator after the `.` is refused. -/
def precisionValue : Option (List Nat × List Nat) → Py (Int × Nat)
  | none => .ok (-1, 0)
  | some (p, g) => do
    let pv ← optDigits p
    let fr ← groupingValue g
    if p = [] ∧ g = [] then .error (.valueError "Format specifier missing precision")
    else pure (pv, fr)

/-- What a doubled separator leaves for the type. -/
def dblOf (G : List Nat) : List Nat :=
  if G = [44, 44] then [44] else if G = [95, 95] then [95] else []

/-- The documented reading of the fields. `dt` and `da` are the type's default type and
alignment. The `'0'` option gives a fill of `'0'` unless a fill was written, and the `=` alignment
for numbers (whose default alignment is `>`) unless an alignment was written; after a written fill
it is a digit of the width. `,` and `_` are taken for the types that the docs give them (`d`, the
float types and no type; `_` every 4 digits for `b`, `o`, `x`, `X`); a separator for the fraction
is refused only by `n`. -/
def docParse (tpName : String) (d : SpecFields) (dt da : Nat) : Py FormatSpec := do
  let fill := match d.fill with | some c => c | none => if d.zero then 48 else 32
  let align := match d.align with
    | some a => a
    | none => if d.zero ∧ da = 62 then 61 else da
  let width ← optDigits (widthDigits d)
  let thousands ← groupingValue d.grouping
  let pf ← precisionValue d.precision
  let rest := dblOf d.grouping ++ d.tail
  if 1 < rest.length then
    .error (.valueError ("Invalid format specifier '" ++ toLeanString (renderSpec d) ++
      "' for object of type '" ++ tpNameShown tpName ++ "'"))
  else
  let type := rest.headD dt
  let thousands ←
    if thousands = 0 then pure 0
    else if type ∈ [100, 101, 102, 103, 69, 71, 37, 70, 0] then pure thousands
    else if type ∈ [98, 111, 120, 88] ∧ thousands = 95 then pure 96
    else .error (sepTypeMessage thousands type)
  if type = 110 ∧ pf.2 ≠ 0 then .error (sepTypeMessage pf.2 type)
  else pure { fillChar := fill, align, alternate := d.alt, noNeg0 := d.z, sign := d.sign.getD 0,
              width, thousands, precision := pf.1, fracThousands := pf.2, type }

/-! ## The proof -/

/-- A character no option field before the width can take. -/
def Later (c : Nat) : Prop :=
  c ≠ 60 ∧ c ≠ 62 ∧ c ≠ 61 ∧ c ≠ 94 ∧ c ≠ 32 ∧ c ≠ 43 ∧ c ≠ 45 ∧ c ≠ 122 ∧ c ≠ 35

instance (c : Nat) : Decidable (Later c) := by unfold Later; infer_instance

theorem digit_later {c : Nat} (h : 0 ≤ toDecimalDigit c) : Later c ∧ c ≠ 44 ∧ c ≠ 95 ∧ c ≠ 46 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> (rintro rfl; revert h; decide)

theorem typeChar_later {t : Nat} (h : TypeChar t) : Later t := by
  obtain ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem later_notAlign {c : Nat} (h : Later c) : isAlignmentToken c = false := by
  obtain ⟨h1, h2, h3, h4, _⟩ := h
  simp [isAlignmentToken, h1, h2, h3, h4]

theorem later_notSign {c : Nat} (h : Later c) : isSignElement c = false := by
  obtain ⟨_, _, _, _, h5, h6, h7, _⟩ := h
  simp [isSignElement, h5, h6, h7]

/-- The part of the spec after the options and the `0`. -/
def precPart (d : SpecFields) : List Nat :=
  match d.precision with
  | none => []
  | some (p, g) => 46 :: (p ++ g)

def specRest (d : SpecFields) : List Nat := d.width ++ d.grouping ++ precPart d ++ d.tail

def alignPart (al fl : Option Nat) : List Nat :=
  match al, fl with
  | none, _ => []
  | some a, none => [a]
  | some a, some c => [c, a]

theorem render_eq (d : SpecFields) :
    renderSpec d = alignPart d.align d.fill ++ (d.sign.toList ++ ((if d.z then [122] else []) ++
      ((if d.alt then [35] else []) ++ ((if d.zero then [48] else []) ++ specRest d)))) := by
  simp only [renderSpec, specRest, precPart, alignPart, List.append_assoc]

theorem grouping_mem {g : List Nat} (h : GroupingWritten g) : ∀ c ∈ g, c = 44 ∨ c = 95 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem restOf_later {d : SpecFields} (hd : d.WF) : ∀ c ∈ specRest d, Later c := by
  intro c hc
  simp only [specRest, List.mem_append] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · exact (digit_later (hd.width c hc)).1
  · rcases grouping_mem hd.grouping c hc with rfl | rfl <;> decide
  · unfold precPart at hc
    split at hc
    · simp at hc
    · rename_i p g hp
      obtain ⟨hpd, hg⟩ := hd.precision p g hp
      simp only [List.mem_cons, List.mem_append] at hc
      rcases hc with rfl | hc | hc
      · decide
      · exact (digit_later (hpd c hc)).1
      · have : c = 44 ∨ c = 95 := by
          rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp at hc <;> omega
        rcases this with rfl | rfl <;> decide
  · exact typeChar_later (hd.tail c hc)

theorem restOf_zero {d : SpecFields} (hd : d.WF) (hf : d.fill = none) (hz : d.zero = false) :
    (specRest d).head? ≠ some 48 := by
  have hw := hd.zero hf hz
  unfold specRest
  cases hW : d.width with
  | cons c t => simpa [hW] using hw
  | nil =>
    simp only [List.nil_append]
    cases hG : d.grouping with
    | cons c t =>
      have := grouping_mem hd.grouping c (by simp [hG])
      simp; omega
    | nil =>
      simp only [List.nil_append]
      unfold precPart
      split
      · cases hT : d.tail with
        | nil => simp
        | cons t r =>
          have := (hd.tail t (by simp [hT])).1
          intro h
          simp at h
          subst h
          revert this; decide
      · simp

theorem parseAlign_none (f : FormatSpec) (X : List Nat) (h : ∀ c ∈ X, isAlignmentToken c = false) :
    parseAlign f X = (f, false, false, X) := by
  match X, h with
  | [], _ => rfl
  | [c], h => simp [parseAlign, h c (by simp)]
  | c :: a :: t, h =>
    simp [parseAlign, h c (by simp), h a (by simp)]

theorem parseAlign_some (f : FormatSpec) (a : Nat) (X : List Nat) (ha : isAlignmentToken a = true)
    (h : ∀ c ∈ X, isAlignmentToken c = false) :
    parseAlign f (a :: X) = ({ f with align := a }, true, false, X) := by
  match X, h with
  | [], _ => simp [parseAlign, ha]
  | c :: t, h => simp [parseAlign, ha, h c (by simp)]

theorem parseAlign_fill (f : FormatSpec) (c a : Nat) (X : List Nat) (ha : isAlignmentToken a = true) :
    parseAlign f (c :: a :: X) = ({ f with align := a, fillChar := c }, true, true, X) := by
  simp [parseAlign, ha]

theorem parseFlags_eq (f : FormatSpec) (sg : Option Nat) (z a : Bool) (Y : List Nat)
    (hsg : ∀ s, sg = some s → s = 43 ∨ s = 45 ∨ s = 32) (hY : ∀ c ∈ Y.head?, Later c) :
    parseFlags f (sg.toList ++ ((if z then [122] else []) ++ ((if a then [35] else []) ++ Y))) =
      ({ f with sign := sg.getD f.sign, noNeg0 := z || f.noNeg0, alternate := a || f.alternate }, Y) := by
  have hY' : ∀ c, Y.head? = some c → Later c := fun c h => hY c (by simp [h])
  rcases sg with _ | s
  · cases z <;> cases a <;>
    (cases hYh : Y with
     | nil => simp [parseFlags, headIs, isSignElement]
     | cons c t =>
       have hc := hY' c (by simp [hYh])
       obtain ⟨_, _, _, _, h5, h6, h7, h8, h9⟩ := hc
       simp [parseFlags, headIs, isSignElement, h5, h6, h7, h8, h9])
  · have hs : isSignElement s = true := by
      rcases hsg s rfl with rfl | rfl | rfl <;> rfl
    cases z <;> cases a <;>
    (cases hYh : Y with
     | nil => simp [parseFlags, headIs, hs]
     | cons c t =>
       have hc := hY' c (by simp [hYh])
       obtain ⟨_, _, _, _, _, _, _, h8, h9⟩ := hc
       simp [parseFlags, headIs, hs, h8, h9])

/-- What `parse_internal_render_format_spec` holds after the options, unicode_formatter.c:404-457. -/
def headOf (d : SpecFields) (dt da : Nat) : FormatSpec :=
  { fillChar := match d.fill with | some c => c | none => if d.zero then 48 else 32
    align := match d.align with | some a => a | none => if d.zero ∧ da = 62 then 61 else da
    alternate := d.alt, noNeg0 := d.z, sign := d.sign.getD 0, type := dt }

theorem parseHead_render (d : SpecFields) (hd : d.WF) (dt da : Nat) :
    parseHead (renderSpec d) dt da =
      (headOf d dt da, (if d.zero ∧ d.fill.isSome then [48] else []) ++ specRest d) := by
  have hR := restOf_later hd
  have hZ := restOf_zero hd
  rw [render_eq]
  generalize hY : (if d.zero then [48] else []) ++ specRest d = Y
  have hYl : ∀ c ∈ Y.head?, Later c := by
    intro c hc
    rw [← hY] at hc
    cases hzr : d.zero
    · simp only [hzr] at hc
      exact hR c (List.mem_of_mem_head? hc)
    · simp only [hzr] at hc
      simp at hc; subst hc; decide
  have hX : ∀ c ∈ d.sign.toList ++ ((if d.z then [122] else []) ++ ((if d.alt then [35] else []) ++ Y)),
      isAlignmentToken c = false := by
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc | hc | hc
    · cases hs : d.sign with
      | none => simp [hs] at hc
      | some s =>
        have hs' := hd.sign s hs
        simp [hs] at hc; subst hc
        rcases hs' with h | h | h <;> simp [isAlignmentToken, h]
    · split at hc <;> simp at hc; subst hc; decide
    · split at hc <;> simp at hc; subst hc; decide
    · rw [← hY] at hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc
      · split at hc <;> simp at hc; subst hc; decide
      · exact later_notAlign (hR c hc)
  have hF := fun f => parseFlags_eq f d.sign d.z d.alt Y hd.sign hYl
  unfold parseHead headOf
  rcases hal : d.align with _ | a
  · have hfl : d.fill = none := by
      cases h : d.fill with
      | none => rfl
      | some _ => have := hd.fill (by simp [h]); simp [hal] at this
    have hA := parseAlign_none { align := da, type := dt } _ hX
    simp only [alignPart, hal, hfl, List.nil_append, hA, hF]
    cases hzr : d.zero
    · have hY0 : Y = specRest d := by rw [← hY, hzr]; simp
      subst hY0
      have hh : headIs (specRest d) 48 = false := by
        simp only [headIs]; have := hZ hfl hzr; simpa using this
      simp [hh]
    · have hY0 : Y = 48 :: specRest d := by rw [← hY, hzr]; simp
      subst hY0
      simp [headIs]
  · have ha : isAlignmentToken a = true := by
      rcases hd.align a hal with rfl | rfl | rfl | rfl <;> rfl
    rcases hfl : d.fill with _ | c
    · have hA := parseAlign_some { align := da, type := dt } _ _ ha hX
      simp only [alignPart, hal, hfl, List.singleton_append, hA, hF]
      cases hzr : d.zero
      · have hY0 : Y = specRest d := by rw [← hY, hzr]; simp
        subst hY0
        have hh : headIs (specRest d) 48 = false := by
          simp only [headIs]; have := hZ hfl hzr; simpa using this
        simp [hh]
      · have hY0 : Y = 48 :: specRest d := by rw [← hY, hzr]; simp
        subst hY0
        simp [headIs]
    · have hA := parseAlign_fill { align := da, type := dt } c a
        (d.sign.toList ++ ((if d.z then [122] else []) ++ ((if d.alt then [35] else []) ++ Y))) ha
      simp only [alignPart, hal, hfl, List.cons_append, List.nil_append, hA, hF]
      cases hzr : d.zero
      · have hY0 : Y = specRest d := by rw [← hY, hzr]; simp
        subst hY0
        simp
      · have hY0 : Y = 48 :: specRest d := by rw [← hY, hzr]; simp
        subst hY0
        simp

/-! ### Width, precision, type -/

theorem getInteger_val : ∀ (ds R : List Nat) (acc : Int) (n : Nat), (∀ c ∈ ds, 0 ≤ toDecimalDigit c) →
    (∀ c ∈ R.head?, toDecimalDigit c < 0) → 0 ≤ acc → acc ≤ ssizeMax →
    getInteger (ds ++ R) acc n =
      if decVal ds acc ≤ ssizeMax then .ok (decVal ds acc, n + ds.length, R)
      else .error (.valueError "Too many decimal digits in format string") := by
  intro ds
  induction ds with
  | nil =>
    intro R acc n _ hR _ hm
    cases R with
    | nil => simp [getInteger, decVal, hm]
    | cons c t =>
      have := hR c (by simp)
      simp [getInteger, decVal, hm, this]
  | cons c t ih =>
    intro R acc n h hR h0 hm
    have hc := h c List.mem_cons_self
    have ht : ∀ x ∈ t, 0 ≤ toDecimalDigit x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hv : decVal (c :: t) acc = decVal t (acc * 10 + toDecimalDigit c) := rfl
    simp only [List.cons_append, getInteger]
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
      rw [ih R _ (n + 1) ht hR (by omega) hle]
      simp only [List.length_cons, show n + 1 + t.length = n + (t.length + 1) by omega]

/-- The width and its separator, unicode_formatter.c:459-490. -/
theorem parseWidth_eq (f : FormatSpec) (hf : f.thousands = 0) (wds G Y : List Nat) (hw : ∀ c ∈ wds, 0 ≤ toDecimalDigit c)
    (hG : GroupingWritten G) (hY : ∀ c ∈ Y.head?, c ≠ 44 ∧ c ≠ 95 ∧ toDecimalDigit c < 0)
    (hdbl : (G = [44, 44] ∨ G = [95, 95]) → Y = []) :
    parseWidth f (wds ++ (G ++ Y)) =
      (do
        let w ← optDigits wds
        let th ← groupingValue G
        pure ({ f with width := w, thousands := th }, dblOf G ++ Y)) := by
  have hhead : ∀ c ∈ (G ++ Y).head?, toDecimalDigit c < 0 := by
    intro c hc
    rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hY c (by simpa using hc)).2.2
    all_goals (simp at hc; subst hc; decide)
  unfold parseWidth
  rw [getInteger_val wds (G ++ Y) 0 0 hw hhead (by omega) (by rw [ssizeMax_val]; omega)]
  have hY' : ∀ c, Y.head? = some c → c ≠ 44 ∧ c ≠ 95 :=
    fun c h => ⟨(hY c (by simp [h])).1, (hY c (by simp [h])).2.1⟩
  by_cases hov : decVal wds 0 ≤ ssizeMax
  · rw [if_pos hov]
    have hwv : optDigits wds =
        .ok (if wds.length = 0 then -1 else decVal wds 0) := by
      by_cases he : wds = []
      · subst he; rfl
      · rw [optDigits, if_neg he, specDigitsValue, if_pos hov]
        have : wds.length ≠ 0 := fun h => he (List.eq_nil_of_length_eq_zero h)
        simp [this]
    rw [hwv]
    rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hYh : Y with
      | nil => simp [headIs, groupingValue, dblOf, bind, Except.bind, pure, Except.pure, hf]
      | cons c t =>
        have := hY' c (by simp [hYh])
        simp [headIs, groupingValue, dblOf, bind, Except.bind, pure, Except.pure, this.1, this.2, hf]
    · cases hYh : Y with
      | nil => simp [headIs, groupingValue, dblOf, bind, Except.bind, pure, Except.pure, LT_NO_LOCALE,
          LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, hf]
      | cons c t =>
        have := hY' c (by simp [hYh])
        simp [headIs, groupingValue, dblOf, bind, Except.bind, pure, Except.pure, this.1, this.2,
          LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, hf]
    · cases hYh : Y with
      | nil => simp [headIs, groupingValue, dblOf, bind, Except.bind, pure, Except.pure, LT_NO_LOCALE,
          LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, hf]
      | cons c t =>
        have := hY' c (by simp [hYh])
        simp [headIs, groupingValue, dblOf, bind, Except.bind, pure, Except.pure, this.1, this.2,
          LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, hf]
    · simp [headIs, groupingValue, dblOf, bind, Except.bind, pure, Except.pure, LT_NO_LOCALE,
        LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, invalidCommaAndUnderscore, bothSeparators]
    · simp [headIs, groupingValue, dblOf, bind, Except.bind, pure, Except.pure, LT_NO_LOCALE,
        LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, invalidCommaAndUnderscore, bothSeparators]
    · have := hdbl (Or.inl rfl); subst this
      simp [headIs, groupingValue, dblOf, bind, Except.bind, pure, Except.pure, LT_NO_LOCALE,
        LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, hf]
    · have := hdbl (Or.inr rfl); subst this
      simp [headIs, groupingValue, dblOf, bind, Except.bind, pure, Except.pure, LT_NO_LOCALE,
        LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, hf]
  · rw [if_neg hov]
    have he : wds ≠ [] := by intro h; subst h; simp [decVal, ssizeMax_val] at hov
    simp [he, optDigits, specDigitsValue, hov, bind, Except.bind]

/-- The precision and its separator, unicode_formatter.c:493-536. -/
theorem parsePrecision_eq (f : FormatSpec) (hf : f.fracThousands = 0) (pd pg T : List Nat)
    (hpd : ∀ c ∈ pd, 0 ≤ toDecimalDigit c)
    (hpg : pg = [] ∨ pg = [44] ∨ pg = [95] ∨ pg = [44, 95] ∨ pg = [95, 44])
    (hT : ∀ c ∈ T.head?, c ≠ 44 ∧ c ≠ 95 ∧ toDecimalDigit c < 0) :
    parsePrecision f (pd ++ (pg ++ T)) =
      (do
        let pf ← precisionValue (some (pd, pg))
        pure ({ f with precision := pf.1, fracThousands := pf.2 }, T)) := by
  have hhead : ∀ c ∈ (pg ++ T).head?, toDecimalDigit c < 0 := by
    intro c hc
    rcases hpg with rfl | rfl | rfl | rfl | rfl
    · exact (hT c (by simpa using hc)).2.2
    all_goals (simp at hc; subst hc; decide)
  have hT' : ∀ c, T.head? = some c → c ≠ 44 ∧ c ≠ 95 :=
    fun c h => ⟨(hT c (by simp [h])).1, (hT c (by simp [h])).2.1⟩
  unfold parsePrecision
  rw [getInteger_val pd (pg ++ T) 0 0 hpd hhead (by omega) (by rw [ssizeMax_val]; omega)]
  by_cases hov : decVal pd 0 ≤ ssizeMax
  · rw [if_pos hov]
    by_cases he : pd = []
    · subst he
      rcases hpg with rfl | rfl | rfl | rfl | rfl <;>
      (cases hTh : T with
       | nil => simp [headIs, groupingValue, precisionValue, optDigits, bind, Except.bind, pure, Except.pure, hf, LT_NO_LOCALE,
            LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, invalidCommaAndUnderscore, bothSeparators]
       | cons c t =>
         have := hT' c (by simp [hTh])
         simp [headIs, groupingValue, precisionValue, optDigits, bind, Except.bind, pure, Except.pure, hf, this.1, this.2, LT_NO_LOCALE,
            LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, invalidCommaAndUnderscore, bothSeparators])
    · have hl : pd.length ≠ 0 := fun h => he (List.eq_nil_of_length_eq_zero h)
      rcases hpg with rfl | rfl | rfl | rfl | rfl <;>
      (cases hTh : T with
       | nil => simp [headIs, groupingValue, precisionValue, optDigits, bind, Except.bind, pure, Except.pure, hf, he, hl, specDigitsValue, hov,
            LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, invalidCommaAndUnderscore, bothSeparators]
       | cons c t =>
         have := hT' c (by simp [hTh])
         simp [headIs, groupingValue, precisionValue, optDigits, bind, Except.bind, pure, Except.pure, hf, he, hl, specDigitsValue, hov,
            this.1, this.2, LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, invalidCommaAndUnderscore,
            bothSeparators])
  · rw [if_neg hov]
    have he : pd ≠ [] := by intro h; subst h; simp [decVal, ssizeMax_val] at hov
    simp [he, precisionValue, optDigits, specDigitsValue, hov, bind, Except.bind]

theorem sepTypeMessage_eq (s t : Nat) : sepTypeMessage s t = invalidThousandsSeparatorType s t := by
  unfold sepTypeMessage invalidThousandsSeparatorType hexPlain
  split <;> rfl

/-- The validation at the end, unicode_formatter.c:566-602. -/
theorem validateSpec_eq (f : FormatSpec) :
    validateSpec f =
      (do
        let thousands ←
          if f.thousands = 0 then pure 0
          else if f.type ∈ [100, 101, 102, 103, 69, 71, 37, 70, 0] then pure f.thousands
          else if f.type ∈ [98, 111, 120, 88] ∧ f.thousands = 95 then pure 96
          else .error (sepTypeMessage f.thousands f.type)
        if f.type = 110 ∧ f.fracThousands ≠ 0 then .error (sepTypeMessage f.fracThousands f.type)
        else pure { f with thousands }) := by
  unfold validateSpec
  simp only [sepTypeMessage_eq, LT_NO_LOCALE, LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE, List.mem_cons,
    List.mem_nil_iff, or_false]
  cases f with
  | mk fill al alt nz sg w th pr fr ty =>
    simp only
    by_cases h0 : th = 0 <;>
    by_cases h1 : (ty = 100 ∨ ty = 101 ∨ ty = 102 ∨ ty = 103 ∨ ty = 69 ∨ ty = 71 ∨ ty = 37 ∨ ty = 70 ∨
      ty = 0) <;>
    by_cases h2 : ((ty = 98 ∨ ty = 111 ∨ ty = 120 ∨ ty = 88) ∧ th = 95) <;>
    by_cases h3 : (ty = 110 ∧ fr ≠ 0) <;>
    simp_all [bind, Except.bind, pure, Except.pure, or_assoc] <;>
    (try (intros; exfalso; omega))

/-- The type field and the validation, unicode_formatter.c:538-607, on what is left. -/
theorem parseType_eq (tn : String) (spec : Str) (f : FormatSpec) (rest : List Nat) :
    parseType tn spec f rest =
      if 1 < rest.length then
        .error (.valueError ("Invalid format specifier '" ++ toLeanString spec ++
          "' for object of type '" ++ tpNameShown tn ++ "'"))
      else validateSpec { f with type := rest.headD f.type } := by
  match rest with
  | [] => simp [parseType]
  | [t] => simp [parseType]
  | a :: b :: t => simp [parseType]; rfl

/-! ### The theorem -/

/-- `parse_internal_render_format_spec` reads back the fields of every spec the grammar describes:
the fill, alignment, sign, `z`, `#` and `0` options, a width and a precision in decimal digits of
any script and any size, the separators, and the type, with the documented refusals in the order
the parser meets them. -/
def ParseDoc : Prop :=
  ∀ (tpName : String) (d : SpecFields) (dt da : Nat), d.WF →
    parseFormatSpec tpName (renderSpec d) dt da = docParse tpName d dt da

theorem typeChar_facts {t : Nat} (h : TypeChar t) : t ≠ 44 ∧ t ≠ 95 ∧ toDecimalDigit t < 0 ∧ t ≠ 46 :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1, h.1, h.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem parseDoc_proven : ParseDoc := by
  intro tn d dt da hd
  have hT : ∀ c ∈ d.tail.head?, c ≠ 44 ∧ c ≠ 95 ∧ toDecimalDigit c < 0 := by
    intro c hc
    have := typeChar_facts (hd.tail c (List.mem_of_mem_head? hc))
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  have hPT : ∀ c ∈ (precPart d ++ d.tail).head?, c ≠ 44 ∧ c ≠ 95 ∧ toDecimalDigit c < 0 := by
    unfold precPart
    split
    · simpa using hT
    · intro c hc; simp at hc; subst hc; decide
  have hdbl : (d.grouping = [44, 44] ∨ d.grouping = [95, 95]) → precPart d ++ d.tail = [] := by
    intro h
    obtain ⟨h1, h2⟩ := hd.doubled h
    simp [precPart, h1, h2]
  have hwds : ∀ c ∈ widthDigits d, 0 ≤ toDecimalDigit c := by
    intro c hc
    simp only [widthDigits, List.mem_append] at hc
    rcases hc with hc | hc
    · split at hc <;> simp at hc; subst hc; decide
    · exact hd.width c hc
  have hrest : (if d.zero ∧ d.fill.isSome then [48] else []) ++ specRest d =
      widthDigits d ++ (d.grouping ++ (precPart d ++ d.tail)) := by
    simp [specRest, widthDigits, List.append_assoc]
  have hW := parseWidth_eq (headOf d dt da) rfl _ d.grouping (precPart d ++ d.tail) hwds hd.grouping hPT hdbl
  unfold parseFormatSpec
  rw [parseHead_render d hd dt da]
  simp only []
  unfold parseTail
  rw [hrest, hW]
  unfold docParse
  cases hWv : optDigits (widthDigits d) with
  | error e => simp [bind, Except.bind]
  | ok w =>
    cases hG : groupingValue d.grouping with
    | error e => simp [bind, Except.bind, hG]
    | ok th =>
      simp only [bind, Except.bind, hG, pure, Except.pure]
      rcases hp : d.precision with _ | ⟨pd, pg⟩
      · -- no precision
        have hpp : precPart d = [] := by simp [precPart, hp]
        have hh : headIs (dblOf d.grouping ++ d.tail) 46 = false := by
          unfold dblOf
          split
          · rfl
          · split
            · rfl
            · cases ht : d.tail with
              | nil => rfl
              | cons t r =>
                have := (typeChar_facts (hd.tail t (by simp [ht]))).2.2.2
                simp [headIs, this]
        simp only [hpp, List.nil_append, hh, Bool.false_eq_true, if_false, parseType_eq,
          validateSpec_eq, precisionValue]
        simp [headOf, bind, Except.bind, pure, Except.pure, LT_NO_LOCALE]
      · -- a precision
        obtain ⟨hpd, hpg⟩ := hd.precision pd pg hp
        have hnd : dblOf d.grouping = [] := by
          unfold dblOf
          have : ¬ (d.grouping = [44, 44] ∨ d.grouping = [95, 95]) := by
            intro h; have := (hd.doubled h).1; rw [hp] at this; cases this
          split
          · exact absurd (Or.inl ‹_›) this
          · split
            · exact absurd (Or.inr ‹_›) this
            · rfl
        have hpp : precPart d = 46 :: (pd ++ pg) := by simp [precPart, hp]
        have hP := parsePrecision_eq { headOf d dt da with width := w, thousands := th } rfl pd pg d.tail
          hpd hpg hT
        simp only [hnd, hpp, List.nil_append, List.cons_append, List.append_assoc, headIs, List.head?_cons,
          beq_self_eq_true, if_true, List.tail_cons, hP]
        cases hPv : precisionValue (some (pd, pg)) with
        | error e => simp [bind, Except.bind]
        | ok pf =>
          simp only [bind, Except.bind, pure, Except.pure, parseType_eq, validateSpec_eq, hnd]
          simp [headOf, bind, Except.bind, pure, Except.pure, hnd]

/-! ## What every parsed spec satisfies -/

/-- The invariants of a spec `parse_internal_render_format_spec` returns: the asserts at
unicode_formatter.c:604-605, width and precision `-1` or a value, and the separators the validation
lets through for each type. The formatters below take these as their preconditions. -/
structure SpecInv (f : FormatSpec) : Prop where
  align : f.align = 60 ∨ f.align = 62 ∨ f.align = 61 ∨ f.align = 94
  sign : f.sign = 0 ∨ f.sign = 32 ∨ f.sign = 43 ∨ f.sign = 45
  width : -1 ≤ f.width
  precision : -1 ≤ f.precision
  thousands : f.thousands = 0 ∨
    ((f.thousands = 44 ∨ f.thousands = 95) ∧ f.type ∈ [100, 101, 102, 103, 69, 71, 37, 70, 0]) ∨
    (f.thousands = 96 ∧ f.type ∈ [98, 111, 120, 88])
  frac : f.fracThousands = 0 ∨ ((f.fracThousands = 44 ∨ f.fracThousands = 95) ∧ f.type ≠ 110)

theorem getInteger_nonneg : ∀ (l : List Nat) (acc : Int) (n : Nat) (v : Int) (k : Nat) (r : List Nat),
    getInteger l acc n = .ok (v, k, r) → 0 ≤ acc → 0 ≤ v := by
  intro l
  induction l with
  | nil => intro acc n v k r h h0; simp [getInteger] at h; omega
  | cons c t ih =>
    intro acc n v k r h h0
    simp only [getInteger] at h
    split at h
    · simp at h; omega
    · split at h
      · cases h
      · exact ih _ _ _ _ _ h (by omega)

theorem parseWidth_inv {f g : FormatSpec} {rest r : List Nat} (h : parseWidth f rest = .ok (g, r))
    (h0 : f.thousands = 0) :
    -1 ≤ g.width ∧ (g.thousands = 0 ∨ g.thousands = 44 ∨ g.thousands = 95) ∧
      g.precision = f.precision ∧ g.fracThousands = f.fracThousands ∧ g.type = f.type ∧
      g.align = f.align ∧ g.sign = f.sign := by
  unfold parseWidth at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i x hx
    obtain ⟨w, k, rest'⟩ := x
    have hw := getInteger_nonneg _ _ _ _ _ _ hx (Int.le_refl 0)
    simp only [pure, Except.pure, LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE] at h
    grind

theorem parsePrecision_inv {f g : FormatSpec} {rest r : List Nat} (h : parsePrecision f rest = .ok (g, r))
    (h0 : f.fracThousands = 0) :
    -1 ≤ g.precision ∧ (g.fracThousands = 0 ∨ g.fracThousands = 44 ∨ g.fracThousands = 95) ∧
      g.width = f.width ∧ g.thousands = f.thousands ∧ g.type = f.type ∧
      g.align = f.align ∧ g.sign = f.sign := by
  unfold parsePrecision at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i x hx
    obtain ⟨p, k, rest'⟩ := x
    have hp := getInteger_nonneg _ _ _ _ _ _ hx (Int.le_refl 0)
    simp only [pure, Except.pure, LT_NO_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE] at h
    repeat' split at h
    all_goals first
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, -⟩ := h
         dsimp only
         refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩ <;> (try split) <;> simp_all <;> omega)
      | cases h

theorem validateSpec_inv {f g : FormatSpec} (h : validateSpec f = .ok g)
    (ht : f.thousands = 0 ∨ f.thousands = 44 ∨ f.thousands = 95)
    (hf : f.fracThousands = 0 ∨ f.fracThousands = 44 ∨ f.fracThousands = 95) :
    (g.thousands = 0 ∨
      ((g.thousands = 44 ∨ g.thousands = 95) ∧ g.type ∈ [100, 101, 102, 103, 69, 71, 37, 70, 0]) ∨
      (g.thousands = 96 ∧ g.type ∈ [98, 111, 120, 88])) ∧
    (g.fracThousands = 0 ∨ ((g.fracThousands = 44 ∨ g.fracThousands = 95) ∧ g.type ≠ 110)) ∧
    g.width = f.width ∧ g.precision = f.precision ∧ g.align = f.align ∧ g.sign = f.sign := by
  rw [validateSpec_eq] at h
  simp only [bind, Except.bind, pure, Except.pure, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢
  cases f with
  | mk fill al alt nz sg w th pr fr ty =>
    simp only at h ht hf
    by_cases h0 : th = 0 <;>
    by_cases h1 : (ty = 100 ∨ ty = 101 ∨ ty = 102 ∨ ty = 103 ∨ ty = 69 ∨ ty = 71 ∨ ty = 37 ∨ ty = 70 ∨
      ty = 0) <;>
    by_cases h2 : ((ty = 98 ∨ ty = 111 ∨ ty = 120 ∨ ty = 88) ∧ th = 95) <;>
    by_cases h3 : (ty = 110 ∧ fr ≠ 0) <;>
    simp_all [or_assoc] <;>
    (try subst h) <;> simp_all [or_assoc] <;> omega

theorem parseTail_inv {t spec f g rest} (h : parseTail t spec f rest = .ok g) (h0 : f.thousands = 0)
    (h1 : f.fracThousands = 0) (hw : f.width = -1) (hp : f.precision = -1) :
    SpecInv { g with align := 60, sign := 0 } ∧ g.align = f.align ∧ g.sign = f.sign := by
  simp only [parseTail, bind, Except.bind, pure, Except.pure] at h
  cases h1' : parseWidth f rest with
  | error e => simp [h1'] at h
  | ok p =>
    obtain ⟨p1, p2⟩ := p
    have k1 := parseWidth_inv h1' h0
    simp only [h1'] at h
    have hty : ∀ q1 q2 g, parseType t spec q1 q2 = .ok g →
        (q1.thousands = 0 ∨ q1.thousands = 44 ∨ q1.thousands = 95) →
        (q1.fracThousands = 0 ∨ q1.fracThousands = 44 ∨ q1.fracThousands = 95) →
        SpecInv { g with align := 60, sign := 0, width := 0, precision := 0 } ∧ g.width = q1.width ∧
          g.precision = q1.precision ∧ g.align = q1.align ∧ g.sign = q1.sign := by
      intro q1 q2 g hq ht hf
      simp only [parseType] at hq
      split at hq
      · have := validateSpec_inv hq ht hf
        exact ⟨⟨by simp, by simp, by simp, by simp, this.1, this.2.1⟩, this.2.2.1, this.2.2.2.1,
          this.2.2.2.2.1, this.2.2.2.2.2⟩
      · have := validateSpec_inv hq ht hf
        exact ⟨⟨by simp, by simp, by simp, by simp, this.1, this.2.1⟩, this.2.2.1, this.2.2.2.1,
          this.2.2.2.2.1, this.2.2.2.2.2⟩
      · cases hq
    by_cases h2 : headIs p2 46 = true
    · simp only [h2, if_true] at h
      cases h3 : parsePrecision p1 p2.tail with
      | error e => simp [h3] at h
      | ok q =>
        obtain ⟨q1, q2⟩ := q
        have k2 := parsePrecision_inv h3 (by rw [k1.2.2.2.1, h1])
        simp only [h3] at h
        obtain ⟨i, hw', hp', ha, hs⟩ := hty q1 q2 g h (by rw [k2.2.2.2.1]; exact k1.2.1) k2.2.1
        refine ⟨⟨by simp, by simp, by rw [hw', k2.2.2.1]; omega, by rw [hp']; omega, i.thousands, i.frac⟩,
          by rw [ha, k2.2.2.2.2.2.1, k1.2.2.2.2.2.1], by rw [hs, k2.2.2.2.2.2.2, k1.2.2.2.2.2.2]⟩
    · simp only [h2, Bool.false_eq_true, if_false] at h
      obtain ⟨i, hw', hp', ha, hs⟩ := hty p1 p2 g h k1.2.1 (by rw [k1.2.2.2.1, h1]; simp)
      refine ⟨⟨by simp, by simp, by rw [hw']; omega, by rw [hp', k1.2.2.1, hp]; exact Int.le_refl _, i.thousands, i.frac⟩,
        by rw [ha, k1.2.2.2.2.2.1], by rw [hs, k1.2.2.2.2.2.2]⟩

/-- Every spec the parser returns satisfies `SpecInv`, whatever the input, given a default
alignment among the four. -/
theorem parse_inv {t : String} {spec : Str} {dt da : Nat} {f : FormatSpec}
    (hda : isAlignmentToken da = true) (h : parseFormatSpec t spec dt da = .ok f) : SpecInv f := by
  have hA := parseAsserts_proven t spec dt da f hda h
  unfold parseFormatSpec at h
  have hh : (parseHead spec dt da).1.thousands = 0 ∧ (parseHead spec dt da).1.fracThousands = 0 ∧
      (parseHead spec dt da).1.width = -1 ∧ (parseHead spec dt da).1.precision = -1 := by
    have ka : ∀ f sp, (parseAlign f sp).1.thousands = f.thousands ∧
        (parseAlign f sp).1.fracThousands = f.fracThousands ∧ (parseAlign f sp).1.width = f.width ∧
        (parseAlign f sp).1.precision = f.precision := by
      intro f sp
      unfold parseAlign
      split
      · split
        · simp
        · split <;> simp
      · split <;> simp
      · simp
    have kf : ∀ f r, (parseFlags f r).1.thousands = f.thousands ∧
        (parseFlags f r).1.fracThousands = f.fracThousands ∧ (parseFlags f r).1.width = f.width ∧
        (parseFlags f r).1.precision = f.precision := by
      intro f r
      unfold parseFlags
      dsimp only
      split
      · rename_i c t
        split <;> (split <;> (split <;> simp_all)) <;> simp_all
      · split <;> (split <;> simp_all) <;> simp_all
    unfold parseHead
    dsimp only
    have a1 := ka { align := da, type := dt } spec
    have f1 := kf (parseAlign { align := da, type := dt } spec).1 (parseAlign { align := da, type := dt } spec).2.2.2
    split
    · simp only []
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [LT_NO_LOCALE]
    · simp_all [LT_NO_LOCALE]
  obtain ⟨i, -, -⟩ := parseTail_inv h hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hal : f.align = 60 ∨ f.align = 62 ∨ f.align = 61 ∨ f.align = 94 := by
    have := hA.1; simp [isAlignmentToken] at this; omega
  have hsg : f.sign = 0 ∨ f.sign = 32 ∨ f.sign = 43 ∨ f.sign = 45 := by
    rcases hA.2 with h | h
    · left; exact h
    · simp [isSignElement] at h; omega
  exact ⟨hal, hsg, i.width, i.precision, i.thousands, i.frac⟩

end PyLean.UnicodeObj
