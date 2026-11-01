import PyLean.TextLibs.CsvDictProps

/-! `reader(writer(rows)) == rows`, on the reader and writer themselves. -/

namespace PyLean.TextLibs.Csv

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-- A row of strings, as the iterator `writerow` draws from. -/
def rowObj (row : List (List Nat)) : Obj := iterObj (row.map fun f => .ret (.str f))

/-- Reading back what `writerow` passed to `write` gives the row, for every accepted dialect that does
not convert fields. Refuted: with `skipinitialspace=True`, the writer leaves a leading space unquoted
and the reader drops it. The counterexample takes the plain-character path of `join_append_data`. -/
def CsvRoundTrip : Prop :=
  ∀ (a : DArgs) (d : Dialect) (row : List (List Nat)) (fuel : Nat) (c : WCtx) (o : Obj) (t : List Nat),
    dialectBuild a = .ok d → (d.quoting = QUOTE_MINIMAL ∨ d.quoting = QUOTE_ALL) →
    writerowM d fuel {} (rowObj row) = (c, .ok o) → c.written = [t] →
    (readerNext d fuel { acts := [.ret (.str t)], limit := 131072 }).2 =
      .ok (some (row.map Field.str))

theorem csvRoundTrip_refuted : ¬CsvRoundTrip := by
  intro h
  have := h { skipinitialspace := some (.bool true) } ⟨true, true, false, 0, 44, 34, NOT_SET, [13, 10]⟩
    [[32, 97]] 16 { buf := [32, 97, 13, 10], numFields := 1, written := [[32, 97, 13, 10]] } .none
    [32, 97, 13, 10] (by decide +kernel) (.inl rfl) rfl rfl
  revert this
  decide +kernel

/-! ### The narrowed round trip -/

/-- What the proof needs from a dialect. -/
structure Good (d : Dialect) : Prop where
  quoting : d.quoting = QUOTE_MINIMAL ∨ d.quoting = QUOTE_ALL
  skip : d.skipinitialspace = false
  dnl : isNl d.delimiter = false
  qnl : isNl d.quotechar = false
  enl : isNl d.escapechar = false
  deol : d.delimiter ≠ EOL
  qeol : d.quotechar ≠ EOL
  eeol : d.escapechar ≠ EOL
  dq : d.delimiter ≠ d.quotechar
  de : d.delimiter ≠ d.escapechar
  qe : d.quotechar ≠ d.escapechar
  lt : d.lineterminator = [13, 10] ∨ d.lineterminator = [10] ∨ d.lineterminator = [13]

theorem good_notNone {d : Dialect} (g : Good d) : d.quoting ≠ QUOTE_NONE := by
  rcases g.quoting with h | h <;> rw [h] <;> decide

theorem reach_cons {d : Dialect} {lim : Int} {s s1 s2 : RSt} {c : Nat} {cs : List Nat}
    (h : parseProcessChar d lim s c = .ok s1) (h2 : parseChars d lim s1 cs = (s2, Option.none)) :
    parseChars d lim s (c :: cs) = (s2, Option.none) := by
  simp [parseChars, parseProcessCharP, h, h2]

theorem reach_append {d : Dialect} {lim : Int} : ∀ {a : List Nat} {s s1 : RSt} {b : List Nat}
    {r : RSt × Option PyExc}, parseChars d lim s a = (s1, Option.none) →
    parseChars d lim s1 b = r → parseChars d lim s (a ++ b) = r := by
  intro a
  induction a with
  | nil =>
    intro s s1 b r h h2
    simp only [parseChars, Prod.mk.injEq, and_true] at h
    subst h
    exact h2
  | cons c cs ih =>
    intro s s1 b r h h2
    simp only [parseChars] at h
    simp only [List.cons_append, parseChars]
    cases hp : parseProcessCharP d lim s c with
    | mk s' e =>
      cases e with
      | some x => simp [hp] at h
      | none =>
        simp only [hp] at h
        simp only
        exact ih h h2

section Steps

variable {d : Dialect} {lim : Int} {s : RSt} {c : Nat}

theorem addOk (h : (s.field.length : Int) < lim) (c : Nat) :
    parseAddChar lim s c = .ok { s with field := s.field ++ [c] } := by
  simp [parseAddChar, Int.not_le.mpr h]

theorem saveOk (g : Good d) (s : RSt) (hn : s.nullFields = false) :
    parseSaveField d s = .ok { s with field := [], fields := s.fields ++ [.str s.field] } :=
  (saveFieldLaw_proven d s hn).2.2.2 (by
    rcases g.quoting with h | h
    · exact .inl h
    · exact .inr (.inl h))

theorem step_start_plain (g : Good d) (hst : s.state = .START_RECORD ∨ s.state = .START_FIELD)
    (h1 : c ≠ EOL) (h2 : isNl c = false) (h3 : c ≠ d.quotechar) (h4 : c ≠ d.escapechar)
    (h5 : c ≠ d.delimiter) (hl : (s.field.length : Int) < lim) :
    parseProcessChar d lim s c =
      .ok { s with state := .IN_FIELD, field := s.field ++ [c], unquoted := true } := by
  have ha : ∀ t : RSt, t.field = s.field → parseAddChar lim t c = .ok { t with field := s.field ++ [c] } := by
    intro t ht
    have : (t.field.length : Int) < lim := by rw [ht]; exact hl
    rw [addOk this c, ht]
  rcases hst with h | h
  · simp [parseProcessChar, h, startFieldStep, h1, h2, h3, h4, h5, g.skip, ha, bind, Except.bind,
      pure, Except.pure]
  · simp [parseProcessChar, h, startFieldStep, h1, h2, h3, h4, h5, g.skip, ha, bind, Except.bind,
      pure, Except.pure]

theorem step_in_plain (hst : s.state = .IN_FIELD) (h1 : c ≠ EOL) (h2 : isNl c = false)
    (h4 : c ≠ d.escapechar) (h5 : c ≠ d.delimiter) (hl : (s.field.length : Int) < lim) :
    parseProcessChar d lim s c = .ok { s with field := s.field ++ [c] } := by
  simp [parseProcessChar, hst, inFieldStep, h1, h2, h4, h5, addOk hl, bind, Except.bind, pure, Except.pure]

theorem step_start_esc (g : Good d) (hst : s.state = .START_RECORD ∨ s.state = .START_FIELD) :
    parseProcessChar d lim s d.escapechar =
      .ok { s with state := .ESCAPED_CHAR, unquoted := true } := by
  have h1 := g.eeol
  have h2 := g.enl
  have h3 : d.escapechar ≠ d.quotechar := Ne.symm g.qe
  rcases hst with h | h
  · simp [parseProcessChar, h, startFieldStep, h1, h2, h3, bind, Except.bind, pure, Except.pure]
  · simp [parseProcessChar, h, startFieldStep, h1, h2, h3, bind, Except.bind, pure, Except.pure]

theorem step_in_esc (g : Good d) (hst : s.state = .IN_FIELD) :
    parseProcessChar d lim s d.escapechar = .ok { s with state := .ESCAPED_CHAR } := by
  have h1 := g.eeol
  have h2 := g.enl
  simp [parseProcessChar, hst, inFieldStep, h1, h2, bind, Except.bind, pure, Except.pure]

theorem step_escaped (hst : s.state = .ESCAPED_CHAR) (h1 : c ≠ EOL) (h2 : isNl c = false)
    (hl : (s.field.length : Int) < lim) :
    parseProcessChar d lim s c = .ok { s with field := s.field ++ [c], state := .IN_FIELD } := by
  simp [parseProcessChar, hst, h1, h2, addOk hl, bind, Except.bind, pure, Except.pure]

theorem step_open (g : Good d) (hst : s.state = .START_RECORD ∨ s.state = .START_FIELD) :
    parseProcessChar d lim s d.quotechar =
      .ok { s with state := .IN_QUOTED_FIELD, unquoted := false } := by
  have h1 := g.qeol
  have h2 := g.qnl
  have h3 := good_notNone g
  rcases hst with h | h
  · simp [parseProcessChar, h, startFieldStep, h1, h2, h3, bind, Except.bind, pure, Except.pure]
  · simp [parseProcessChar, h, startFieldStep, h1, h2, h3, bind, Except.bind, pure, Except.pure]

theorem step_q_plain (hst : s.state = .IN_QUOTED_FIELD) (h1 : c ≠ EOL) (h3 : c ≠ d.quotechar)
    (h4 : c ≠ d.escapechar) (hl : (s.field.length : Int) < lim) :
    parseProcessChar d lim s c = .ok { s with field := s.field ++ [c] } := by
  simp [parseProcessChar, hst, h1, h3, h4, addOk hl]

theorem step_q_esc (g : Good d) (hst : s.state = .IN_QUOTED_FIELD) :
    parseProcessChar d lim s d.escapechar = .ok { s with state := .ESCAPE_IN_QUOTED_FIELD } := by
  have h1 := g.eeol
  simp [parseProcessChar, hst, h1]

theorem step_esc_q (hst : s.state = .ESCAPE_IN_QUOTED_FIELD) (h1 : c ≠ EOL)
    (hl : (s.field.length : Int) < lim) :
    parseProcessChar d lim s c = .ok { s with field := s.field ++ [c], state := .IN_QUOTED_FIELD } := by
  simp [parseProcessChar, hst, h1, addOk hl, bind, Except.bind, pure, Except.pure]

theorem step_q_quote (g : Good d) (hst : s.state = .IN_QUOTED_FIELD) :
    parseProcessChar d lim s d.quotechar =
      .ok { s with state := if d.doublequote then .QUOTE_IN_QUOTED_FIELD else .IN_FIELD } := by
  have h1 := g.qeol
  have h2 := g.qe
  have h3 := good_notNone g
  cases hq : d.doublequote <;> simp [parseProcessChar, hst, h1, h2, h3, hq]

theorem step_qq (g : Good d) (hst : s.state = .QUOTE_IN_QUOTED_FIELD)
    (hl : (s.field.length : Int) < lim) :
    parseProcessChar d lim s d.quotechar =
      .ok { s with field := s.field ++ [d.quotechar], state := .IN_QUOTED_FIELD } := by
  have h3 := good_notNone g
  simp [parseProcessChar, hst, h3, addOk hl, bind, Except.bind, pure, Except.pure]

/-- States where a field can end. -/
def Closing (s : RSt) : Prop :=
  s.state = .START_RECORD ∨ s.state = .START_FIELD ∨ s.state = .IN_FIELD ∨
    s.state = .QUOTE_IN_QUOTED_FIELD

theorem close_delim (g : Good d) (hc : Closing s) (hn : s.nullFields = false) :
    ∃ s', parseProcessChar d lim s d.delimiter = .ok s' ∧ s'.state = .START_FIELD ∧ s'.field = [] ∧
      s'.nullFields = false ∧ s'.fields = s.fields ++ [.str s.field] := by
  have h1 := g.deol
  have h2 := g.dnl
  have h3 := g.dq
  have h4 := g.de
  have h5 := good_notNone g
  have hdq : ¬(d.delimiter = 32 ∧ d.skipinitialspace = true) := by simp [g.skip]
  have hs := fun (t : RSt) (ht : t.nullFields = false) => saveOk g t ht
  rcases hc with h | h | h | h
  · refine ⟨{ s with field := [], fields := s.fields ++ [.str s.field], state := .START_FIELD, unquoted := true }, ?_, rfl, rfl, hn, rfl⟩
    simp [parseProcessChar, h, startFieldStep, h1, h2, h3, h4, g.skip, hs, hn]
  · refine ⟨{ s with field := [], fields := s.fields ++ [.str s.field], state := .START_FIELD, unquoted := true }, ?_, rfl, rfl, hn, rfl⟩
    simp [parseProcessChar, h, startFieldStep, h1, h2, h3, h4, g.skip, hs, hn]
  · refine ⟨{ s with field := [], fields := s.fields ++ [.str s.field], state := .START_FIELD }, ?_, rfl, rfl, hn, rfl⟩
    simp [parseProcessChar, h, inFieldStep, h1, h2, h4, hs, hn, bind, Except.bind, pure, Except.pure]
  · refine ⟨{ s with field := [], fields := s.fields ++ [.str s.field], state := .START_FIELD }, ?_, rfl, rfl, hn, rfl⟩
    simp [parseProcessChar, h, h3, h5, hs, hn, bind, Except.bind, pure, Except.pure]

theorem close_nl (g : Good d) (hc : s.state = .START_FIELD ∨ s.state = .IN_FIELD ∨
    s.state = .QUOTE_IN_QUOTED_FIELD) (hn : s.nullFields = false) (h2 : isNl c = true)
    (hq : c ≠ d.quotechar) (hd : c ≠ d.delimiter) (h1 : c ≠ EOL) :
    ∃ s', parseProcessChar d lim s c = .ok s' ∧ s'.state = .EAT_CRNL ∧ s'.field = [] ∧
      s'.nullFields = false ∧ s'.fields = s.fields ++ [.str s.field] := by
  have h5 := good_notNone g
  have hs := fun (t : RSt) (ht : t.nullFields = false) => saveOk g t ht
  rcases hc with h | h | h
  · refine ⟨{ s with field := [], fields := s.fields ++ [.str s.field], state := .EAT_CRNL, unquoted := true }, ?_, rfl, rfl, hn, rfl⟩
    simp [parseProcessChar, h, startFieldStep, h1, h2, hs, hn, bind, Except.bind, pure, Except.pure]
  · refine ⟨{ s with field := [], fields := s.fields ++ [.str s.field], state := .EAT_CRNL }, ?_, rfl, rfl, hn, rfl⟩
    simp [parseProcessChar, h, inFieldStep, h1, h2, hs, hn, bind, Except.bind, pure, Except.pure]
  · refine ⟨{ s with field := [], fields := s.fields ++ [.str s.field], state := .EAT_CRNL }, ?_, rfl, rfl, hn, rfl⟩
    simp [parseProcessChar, h, h1, h2, hq, hd, h5, hs, hn, bind, Except.bind, pure, Except.pure]

end Steps

/-! #### The writer's text, field by field -/

/-- The four things `join_append_data` does with a character, under a `Good` dialect. -/
theorem joinChar_cases {d : Dialect} (g : Good d) {c : Nat} {pre : List Nat} {q1 : Bool}
    (h : joinChar d c = .ok (pre, q1)) :
    (pre = [] ∧ q1 = false ∧ c ≠ d.delimiter ∧ c ≠ d.escapechar ∧ c ≠ d.quotechar ∧ isNl c = false) ∨
    (pre = [d.quotechar] ∧ q1 = true ∧ c = d.quotechar ∧ d.doublequote = true) ∨
    (pre = [d.escapechar] ∧ q1 = false ∧ (c = d.quotechar ∨ c = d.escapechar)) ∨
    (pre = [] ∧ q1 = true ∧ c ≠ d.escapechar ∧ c ≠ d.quotechar) := by
  have hn := good_notNone g
  by_cases hs : c = d.delimiter ∨ c = d.escapechar ∨ c = d.quotechar ∨ c = 10 ∨ c = 13 ∨
      d.lineterminator.contains c = true
  · by_cases h1 : c = d.quotechar
    · by_cases h2 : d.doublequote = true
      · have hv : joinChar d c = .ok ([d.quotechar], true) := by
          unfold joinChar
          rw [if_pos hs, if_neg hn, if_pos h1, if_pos h2]
          rfl
        rw [hv] at h
        cases h
        exact .inr (.inl ⟨rfl, rfl, h1, h2⟩)
      · by_cases he : d.escapechar = NOT_SET
        · have hv : joinChar d c = .error (csvErr "need to escape, but no escapechar set") := by
            unfold joinChar
            rw [if_pos hs, if_neg hn, if_pos h1, if_neg h2]
            simp [he]
          rw [hv] at h
          cases h
        · have hv : joinChar d c = .ok ([d.escapechar], false) := by
            unfold joinChar
            rw [if_pos hs, if_neg hn, if_pos h1, if_neg h2]
            simp [he]
          rw [hv] at h
          cases h
          exact .inr (.inr (.inl ⟨rfl, rfl, .inl h1⟩))
    · by_cases h3 : c = d.escapechar
      · by_cases he : d.escapechar = NOT_SET
        · have hv : joinChar d c = .error (csvErr "need to escape, but no escapechar set") := by
            unfold joinChar
            rw [if_pos hs, if_neg hn, if_neg h1, if_pos h3]
            simp [he]
          rw [hv] at h
          cases h
        · have hv : joinChar d c = .ok ([d.escapechar], false) := by
            unfold joinChar
            rw [if_pos hs, if_neg hn, if_neg h1, if_pos h3]
            simp [he]
          rw [hv] at h
          cases h
          exact .inr (.inr (.inl ⟨rfl, rfl, .inr h3⟩))
      · have hv : joinChar d c = .ok ([], true) := by
          unfold joinChar
          rw [if_pos hs, if_neg hn, if_neg h1, if_neg h3]
          rfl
        rw [hv] at h
        cases h
        exact .inr (.inr (.inr ⟨rfl, rfl, h3, h1⟩))
  · have hv : joinChar d c = .ok ([], false) := by
      unfold joinChar
      rw [if_neg hs]
    rw [hv] at h
    cases h
    have ha : c ≠ d.delimiter := fun e => hs (.inl e)
    have hb : c ≠ d.escapechar := fun e => hs (.inr (.inl e))
    have hc : c ≠ d.quotechar := fun e => hs (.inr (.inr (.inl e)))
    have h10 : c ≠ 10 := fun e => hs (.inr (.inr (.inr (.inl e))))
    have h13 : c ≠ 13 := fun e => hs (.inr (.inr (.inr (.inr (.inl e)))))
    exact .inl ⟨rfl, rfl, ha, hb, hc, by simp [isNl, h10, h13]⟩

theorem joinField_cons {d : Dialect} {c : Nat} {cs body : List Nat} {q q2 : Bool}
    (h : joinField d (c :: cs) q = .ok (body, q2)) :
    ∃ pre q1 rest, joinChar d c = .ok (pre, q1) ∧ joinField d cs (q || q1) = .ok (rest, q2) ∧
      body = pre ++ [c] ++ rest := by
  simp only [joinField] at h
  obtain ⟨⟨pre, q1⟩, h1, h⟩ := bind_ok h
  obtain ⟨⟨rest, q3⟩, h2, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hb, hq⟩ := h
  subst hq
  exact ⟨pre, q1, rest, h1, h2, hb.symm⟩

theorem joinField_true {d : Dialect} : ∀ {f body : List Nat} {q : Bool},
    joinField d f true = .ok (body, q) → q = true := by
  intro f
  induction f with
  | nil =>
    intro body q h
    simp only [joinField, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | cons c cs ih =>
    intro body q h
    obtain ⟨_, _, _, _, h2, _⟩ := joinField_cons h
    exact ih (by simpa using h2)

/-- The text does not depend on whether the field started out quoted. -/
theorem joinField_body {d : Dialect} : ∀ {f body : List Nat} {q q2 : Bool},
    joinField d f q = .ok (body, q2) → joinField d f true = .ok (body, true) := by
  intro f
  induction f with
  | nil =>
    intro body q q2 h
    simp only [joinField, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl
  | cons c cs ih =>
    intro body q q2 h
    obtain ⟨pre, q1, rest, h1, h2, hb⟩ := joinField_cons h
    have h3 := ih h2
    simp only [joinField, h1, bind, Except.bind, Bool.true_or, h3, pure, Except.pure, hb]

theorem valid_tail {lim : Int} {n c : Nat} {l : List Nat}
    (h : (n : Int) + ((c :: l).length : Int) ≤ lim) :
    (n : Int) < lim ∧ ((n + 1 : Nat) : Int) + (l.length : Int) ≤ lim := by
  simp only [List.length_cons] at h
  constructor <;> omega

/-- What the reader knows after a stretch of text. -/
structure After (s0 s : RSt) (f : List Nat) : Prop where
  fields : s.fields = s0.fields
  nulls : s.nullFields = s0.nullFields
  field : s.field = s0.field ++ f

/-- A field that needs no quotes: the characters and their escapes put it in the buffer. -/
theorem body_unquoted {d : Dialect} {lim : Int} (g : Good d) : ∀ (f : List Nat) (s : RSt) (body : List Nat),
    (∀ c ∈ f, c ≠ EOL) → joinField d f false = .ok (body, false) →
    (s.state = .START_RECORD ∨ s.state = .START_FIELD ∨ s.state = .IN_FIELD) →
    (s.field.length : Int) + (f.length : Int) ≤ lim →
    ∃ s', parseChars d lim s body = (s', Option.none) ∧ After s s' f ∧
      (f = [] → s' = s ∧ body = []) ∧ (f ≠ [] → s'.state = .IN_FIELD) := by
  intro f
  induction f with
  | nil =>
    intro s body _ h _ _
    simp only [joinField, Except.ok.injEq, Prod.mk.injEq, and_true] at h
    subst h
    exact ⟨s, rfl, ⟨rfl, rfl, by simp⟩, fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h⟩
  | cons c cs ih =>
    intro s body hv h hst hl
    obtain ⟨pre, q1, rest, h1, h2, hb⟩ := joinField_cons h
    have hq1 : q1 = false := by
      cases q1 with
      | false => rfl
      | true =>
        have := joinField_true (by simpa using h2)
        cases this
    subst hq1
    have hc : c ≠ EOL := hv c (by simp)
    have hv2 : ∀ x ∈ cs, x ≠ EOL := fun x hx => hv x (by simp [hx])
    obtain ⟨hl1, hl2⟩ := valid_tail hl
    have h2' : joinField d cs false = .ok (rest, false) := by simpa using h2
    have fin : ∀ (s1 : RSt), parseChars d lim s (pre ++ [c]) = (s1, Option.none) →
        s1.state = .IN_FIELD → s1.fields = s.fields → s1.nullFields = s.nullFields →
        s1.field = s.field ++ [c] →
        ∃ s', parseChars d lim s body = (s', Option.none) ∧ After s s' (c :: cs) ∧
          (c :: cs = [] → s' = s ∧ body = []) ∧ (c :: cs ≠ [] → s'.state = .IN_FIELD) := by
      intro s1 a5 a1 a2 a3 a4
      obtain ⟨s', r1, r2, r3, r4⟩ := ih s1 rest hv2 h2' (.inr (.inr a1)) (by
        rw [a4]
        simp only [List.length_append, List.length_cons, List.length_nil]
        simp only [List.length_cons] at hl
        omega)
      refine ⟨s', ?_, ⟨r2.fields.trans a2, r2.nulls.trans a3, ?_⟩, fun e => (by cases e), fun _ => ?_⟩
      · rw [hb]
        exact reach_append a5 r1
      · rw [r2.field, a4]
        simp
      · by_cases he : cs = []
        · obtain ⟨e1, _⟩ := r3 he
          rw [e1]
          exact a1
        · exact r4 he
    rcases joinChar_cases g h1 with ⟨e1, _, a1, a2, a3, a4⟩ | ⟨_, e2, _, _⟩ | ⟨e1, _, a1⟩ | ⟨_, e2, _, _⟩
    · subst e1
      rcases hst with hs | hs | hs
      · exact fin _ (reach_cons (step_start_plain g (.inl hs) hc a4 a3 a2 a1 hl1) rfl) rfl rfl rfl rfl
      · exact fin _ (reach_cons (step_start_plain g (.inr hs) hc a4 a3 a2 a1 hl1) rfl) rfl rfl rfl rfl
      · exact fin _ (reach_cons (step_in_plain hs hc a4 a2 a1 hl1) rfl) hs rfl rfl rfl
    · cases e2
    · subst e1
      have hnl : isNl c = false := by
        rcases a1 with e | e <;> rw [e]
        · exact g.qnl
        · exact g.enl
      rcases hst with hs | hs | hs
      · exact fin _ (reach_cons (step_start_esc g (.inl hs))
          (reach_cons (step_escaped rfl hc hnl hl1) rfl)) rfl rfl rfl rfl
      · exact fin _ (reach_cons (step_start_esc g (.inr hs))
          (reach_cons (step_escaped rfl hc hnl hl1) rfl)) rfl rfl rfl rfl
      · exact fin _ (reach_cons (step_in_esc g hs)
          (reach_cons (step_escaped rfl hc hnl hl1) rfl)) rfl rfl rfl rfl
    · cases e2

/-- Inside quotes, every character arrives: `""` and escapes undo themselves. -/
theorem body_quoted {d : Dialect} {lim : Int} (g : Good d) : ∀ (f : List Nat) (s : RSt) (body : List Nat),
    (∀ c ∈ f, c ≠ EOL) → joinField d f true = .ok (body, true) → s.state = .IN_QUOTED_FIELD →
    (s.field.length : Int) + (f.length : Int) ≤ lim →
    ∃ s', parseChars d lim s body = (s', Option.none) ∧ After s s' f ∧ s'.state = .IN_QUOTED_FIELD := by
  intro f
  induction f with
  | nil =>
    intro s body _ h hst _
    simp only [joinField, Except.ok.injEq, Prod.mk.injEq, and_true] at h
    subst h
    exact ⟨s, rfl, ⟨rfl, rfl, by simp⟩, hst⟩
  | cons c cs ih =>
    intro s body hv h hst hl
    obtain ⟨pre, q1, rest, h1, h2, hb⟩ := joinField_cons h
    have hc : c ≠ EOL := hv c (by simp)
    have hv2 : ∀ x ∈ cs, x ≠ EOL := fun x hx => hv x (by simp [hx])
    obtain ⟨hl1, hl2⟩ := valid_tail hl
    have h2' : joinField d cs true = .ok (rest, true) := by simpa using h2
    have fin : ∀ (s1 : RSt), parseChars d lim s (pre ++ [c]) = (s1, Option.none) →
        s1.state = .IN_QUOTED_FIELD → s1.fields = s.fields → s1.nullFields = s.nullFields →
        s1.field = s.field ++ [c] →
        ∃ s', parseChars d lim s body = (s', Option.none) ∧ After s s' (c :: cs) ∧
          s'.state = .IN_QUOTED_FIELD := by
      intro s1 a5 a1 a2 a3 a4
      obtain ⟨s', r1, r2, r3⟩ := ih s1 rest hv2 h2' a1 (by
        rw [a4]
        simp only [List.length_append, List.length_cons, List.length_nil]
        simp only [List.length_cons] at hl
        omega)
      refine ⟨s', ?_, ⟨r2.fields.trans a2, r2.nulls.trans a3, ?_⟩, r3⟩
      · rw [hb]
        exact reach_append a5 r1
      · rw [r2.field, a4]
        simp
    rcases joinChar_cases g h1 with ⟨e1, _, _, a2, a3, _⟩ | ⟨e1, _, a1, a2⟩ | ⟨e1, _, a1⟩ | ⟨e1, _, a2, a3⟩
    · subst e1
      exact fin _ (reach_cons (step_q_plain hst hc a3 a2 hl1) rfl) hst rfl rfl rfl
    · subst e1
      subst a1
      have hs1 := step_q_quote (lim := lim) g hst
      simp only [a2, if_true] at hs1
      exact fin _ (reach_cons hs1 (reach_cons (step_qq g rfl hl1) rfl)) rfl rfl rfl rfl
    · subst e1
      exact fin _ (reach_cons (step_q_esc g hst) (reach_cons (step_esc_q rfl hc hl1) rfl)) rfl rfl rfl rfl
    · subst e1
      exact fin _ (reach_cons (step_q_plain hst hc a3 a2 hl1) rfl) hst rfl rfl rfl

/-- A whole field, with its quotes if any, from the start of a field. An empty, unquoted field reads
as nothing, and is saved by what comes next. -/
theorem read_field {d : Dialect} {lim : Int} (g : Good d) (f : List Nat) (s : RSt) (body : List Nat)
    (q1 q2 : Bool) (hv : ∀ c ∈ f, c ≠ EOL) (hj : joinField d f q1 = .ok (body, q2))
    (hst : s.state = .START_RECORD ∨ s.state = .START_FIELD) (he : s.field = [])
    (hl : (f.length : Int) ≤ lim) :
    ∃ s', parseChars d lim s ((if q2 then [d.quotechar] else []) ++ body ++ (if q2 then [d.quotechar] else [])) =
        (s', Option.none) ∧ After s s' f ∧ Closing s' ∧
      (s'.state = .START_RECORD → f = [] ∧ q2 = false) ∧
      (s.state = .START_FIELD → s'.state ≠ .START_RECORD) := by
  cases q2 with
  | false =>
    have hq1 : q1 = false := by
      cases q1 with
      | false => rfl
      | true =>
        have := joinField_true hj
        cases this
    subst hq1
    have hl' : (s.field.length : Int) + (f.length : Int) ≤ lim := by rw [he]; simpa using hl
    obtain ⟨s', r1, r2, r3, r4⟩ := body_unquoted g f s body hv hj
      (by rcases hst with h | h; exact .inl h; exact .inr (.inl h)) hl'
    simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
    by_cases hf : f = []
    · obtain ⟨e1, _⟩ := r3 hf
      rw [e1] at r1 r2
      refine ⟨s, r1, r2, ?_, fun _ => ⟨hf, trivial⟩, fun h h2 => ?_⟩
      · rcases hst with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · rw [h] at h2
        cases h2
    · have h5 := r4 hf
      refine ⟨s', r1, r2, .inr (.inr (.inl h5)), fun h => ?_, fun _ h2 => ?_⟩
      · rw [h5] at h
        cases h
      · rw [h5] at h2
        cases h2
  | true =>
    have hb := joinField_body hj
    have hopen := step_open (lim := lim) g hst
    have hl' : (0 : Int) + (f.length : Int) ≤ lim := by simpa using hl
    obtain ⟨s1, r1, r2, r3⟩ := body_quoted (lim := lim) g f
      { s with state := .IN_QUOTED_FIELD, unquoted := false } body hv hb rfl (by simpa [he] using hl)
    have hclose := step_q_quote (lim := lim) (s := s1) g r3
    simp only [if_true]
    refine ⟨{ s1 with state := if d.doublequote then .QUOTE_IN_QUOTED_FIELD else .IN_FIELD }, ?_,
      ⟨r2.fields, r2.nulls, ?_⟩, ?_, fun h => ?_, fun _ h2 => ?_⟩
    · have hrest := reach_append r1 (reach_cons hclose (rfl :
        parseChars d lim { s1 with state := if d.doublequote then .QUOTE_IN_QUOTED_FIELD else .IN_FIELD } [] = _))
      simp only [List.cons_append, List.nil_append, List.singleton_append]
      exact reach_cons hopen (by simpa [List.append_assoc] using hrest)
    · exact r2.field
    · cases hq : d.doublequote
      · exact .inr (.inr (.inl (by simp [hq])))
      · exact .inr (.inr (.inr (by simp [hq])))
    · cases hq : d.doublequote <;> simp [hq] at h
    · cases hq : d.doublequote <;> simp [hq] at h2

/-- How the record buffer grows, field by field. -/
inductive Chain (d : Dialect) : List (List Nat) → List Nat → Int → List Nat → Int → Prop
  | nil (b : List Nat) (n : Int) : Chain d [] b n b n
  | cons {f : List Nat} {fs : List (List Nat)} {b b1 b2 : List Nat} {n n1 n2 : Int} {q : Bool} :
      joinAppend d b n (some f) q = .ok (b1, n1) → Chain d fs b1 n1 b2 n2 →
      Chain d (f :: fs) b n b2 n2

theorem chain_count {d : Dialect} : ∀ {fs : List (List Nat)} {b b2 : List Nat} {n n2 : Int},
    Chain d fs b n b2 n2 → 0 ≤ n → n + fs.length ≤ 2 ^ 31 - 1 → n2 = n + fs.length := by
  intro fs b b2 n n2 h
  induction h with
  | nil b n => intro _ _; simp
  | @cons f fs b b1 b2 n n1 n2 q h1 _ ih =>
    intro h3 h4
    obtain ⟨_, _, _, _, hn, _⟩ := joinAppend_ok h1
    simp only [List.length_cons] at h4
    have hw : cIntWrap (n + 1) = n + 1 := by
      unfold cIntWrap
      omega
    have e : n1 = n + 1 := by rw [hn, hw]
    subst e
    have := ih (by omega) (by omega)
    simp only [List.length_cons]
    omega

/-- The fields after the first: a delimiter closes the one before, then the next one is read. -/
theorem read_rest {d : Dialect} {lim : Int} (g : Good d) : ∀ {fs : List (List Nat)} {b b2 : List Nat}
    {n n2 : Int}, Chain d fs b n b2 n2 → 1 ≤ n → n + fs.length ≤ 2 ^ 31 - 1 →
    (∀ f ∈ fs, (∀ c ∈ f, c ≠ EOL) ∧ (f.length : Int) ≤ lim) →
    ∀ s : RSt, Closing s → s.nullFields = false →
    ∃ X s', b2 = b ++ X ∧ parseChars d lim s X = (s', Option.none) ∧ Closing s' ∧
      s'.nullFields = false ∧
      s'.fields ++ [.str s'.field] = s.fields ++ [.str s.field] ++ fs.map Field.str ∧
      (fs ≠ [] → s'.state ≠ .START_RECORD) ∧ (fs = [] → s' = s ∧ X = []) := by
  intro fs b b2 n n2 h
  induction h with
  | nil b n =>
    intro _ _ _ s hc hn
    exact ⟨[], s, by simp, rfl, hc, hn, by simp, fun h => absurd rfl h, fun _ => ⟨rfl, rfl⟩⟩
  | @cons f fs b b1 b2 n n1 n2 q h1 _ ih =>
    intro h3 h4 hv s hc hn
    obtain ⟨body, q1, q2, hj, hw, hb⟩ := joinAppend_ok h1
    simp only [List.length_cons] at h4
    have hw' : cIntWrap (n + 1) = n + 1 := by
      unfold cIntWrap
      omega
    have e : n1 = n + 1 := by rw [hw, hw']
    subst e
    obtain ⟨hv1, hv2⟩ := hv f (by simp)
    obtain ⟨s1, a1, a2, a3, a4, a5⟩ := close_delim (lim := lim) g hc hn
    obtain ⟨s2, r1, r2, r3, _, r5⟩ := read_field (lim := lim) g f s1 body q1 q2 hv1
      (by simpa using hj) (.inr a2) a3 hv2
    obtain ⟨X, s', e1, e2, e3, e4, e5, e6, e7⟩ := ih (by omega) (by omega)
      (fun x hx => hv x (by simp [hx])) s2 r3 (by rw [r2.nulls]; exact a4)
    have hp : (n > 0) := by omega
    rw [if_pos hp] at hb
    refine ⟨d.delimiter :: ((if q2 then [d.quotechar] else []) ++ body ++ (if q2 then [d.quotechar] else [])) ++ X,
      s', ?_, reach_cons a1 (reach_append r1 e2), e3, e4, ?_, fun _ => ?_, fun h => by cases h⟩
    · rw [e1, hb]
      simp [List.append_assoc]
    · rw [e5, r2.fields, a5, r2.field, a3]
      simp [List.append_assoc]
    · by_cases hf : fs = []
      · obtain ⟨e8, _⟩ := e7 hf
        rw [e8]
        exact r5 a2
      · exact e6 hf

/-! #### The end of the line -/

theorem pP_ok {d : Dialect} {lim : Int} {s s' : RSt} {c : Nat}
    (h : parseProcessChar d lim s c = .ok s') : parseProcessCharP d lim s c = (s', Option.none) := by
  simp [parseProcessCharP, h]

theorem nl_ne {c x : Nat} (h : isNl x = false) (hc : isNl c = true) : c ≠ x := by
  intro e
  rw [e, h] at hc
  cases hc

/-- After the last field, a line terminator made of newlines saves it and ends the record. -/
theorem line_end {d : Dialect} {lim : Int} (g : Good d) (s : RSt)
    (hc : s.state = .START_FIELD ∨ s.state = .IN_FIELD ∨ s.state = .QUOTE_IN_QUOTED_FIELD)
    (hn : s.nullFields = false) :
    ∃ s1 s2, parseChars d lim s d.lineterminator = (s1, Option.none) ∧
      parseProcessCharP d lim s1 EOL = (s2, Option.none) ∧ s2.state = .START_RECORD ∧
      s2.fields = s.fields ++ [.str s.field] := by
  have n13 : isNl 13 = true := by decide
  have n10 : isNl 10 = true := by decide
  have e13 : (13 : Nat) ≠ EOL := by decide
  have e10 : (10 : Nat) ≠ EOL := by decide
  rcases g.lt with h | h | h
  · obtain ⟨t, a1, a2, _, _, a5⟩ := close_nl (lim := lim) g hc hn n13 (nl_ne g.qnl n13) (nl_ne g.dnl n13) e13
    have h3 := (eatCrnl_proven d lim t 10 a2).2.1 n10
    have h4 := (eatCrnl_proven d lim t 10 a2).2.2
    exact ⟨t, _, by rw [h]; exact reach_cons a1 (reach_cons h3 rfl), pP_ok h4, rfl, a5⟩
  · obtain ⟨t, a1, a2, _, _, a5⟩ := close_nl (lim := lim) g hc hn n10 (nl_ne g.qnl n10) (nl_ne g.dnl n10) e10
    have h4 := (eatCrnl_proven d lim t 10 a2).2.2
    exact ⟨t, _, by rw [h]; exact reach_cons a1 rfl, pP_ok h4, rfl, a5⟩
  · obtain ⟨t, a1, a2, _, _, a5⟩ := close_nl (lim := lim) g hc hn n13 (nl_ne g.qnl n13) (nl_ne g.dnl n13) e13
    have h4 := (eatCrnl_proven d lim t 10 a2).2.2
    exact ⟨t, _, by rw [h]; exact reach_cons a1 rfl, pP_ok h4, rfl, a5⟩

/-- A row of no fields is a bare terminator, which reads as an empty row. -/
theorem line_end_empty {d : Dialect} {lim : Int} (g : Good d) (s : RSt) (hst : s.state = .START_RECORD) :
    ∃ s1 s2, parseChars d lim s d.lineterminator = (s1, Option.none) ∧
      parseProcessCharP d lim s1 EOL = (s2, Option.none) ∧ s2.state = .START_RECORD ∧
      s2.fields = s.fields := by
  have n13 : isNl 13 = true := by decide
  have n10 : isNl 10 = true := by decide
  have e13 : (13 : Nat) ≠ EOL := by decide
  have e10 : (10 : Nat) ≠ EOL := by decide
  have st : ∀ c, isNl c = true → c ≠ EOL →
      parseProcessChar d lim s c = .ok { s with state := .EAT_CRNL } := by
    intro c h1 h2
    simp [parseProcessChar, hst, h1, h2]
  rcases g.lt with h | h | h
  · have h3 := (eatCrnl_proven d lim { s with state := .EAT_CRNL } 10 rfl).2.1 n10
    have h4 := (eatCrnl_proven d lim { s with state := .EAT_CRNL } 10 rfl).2.2
    exact ⟨_, _, by rw [h]; exact reach_cons (st 13 n13 e13) (reach_cons h3 rfl), pP_ok h4, rfl, rfl⟩
  · have h4 := (eatCrnl_proven d lim { s with state := .EAT_CRNL } 10 rfl).2.2
    exact ⟨_, _, by rw [h]; exact reach_cons (st 10 n10 e10) rfl, pP_ok h4, rfl, rfl⟩
  · have h4 := (eatCrnl_proven d lim { s with state := .EAT_CRNL } 10 rfl).2.2
    exact ⟨_, _, by rw [h]; exact reach_cons (st 13 n13 e13) rfl, pP_ok h4, rfl, rfl⟩

theorem parseLine_of {d : Dialect} {lim : Int} {s s1 s2 s3 : RSt} {X lt : List Nat}
    (h1 : parseChars d lim s X = (s1, Option.none)) (h2 : parseChars d lim s1 lt = (s2, Option.none))
    (h3 : parseProcessCharP d lim s2 EOL = (s3, Option.none)) :
    parseLine d lim s (X ++ lt) = (s3, Option.none) := by
  simp only [parseLine, reach_append h1 h2, h3]

/-! #### The writer's side -/

theorem fieldLoop_strs {d : Dialect} : ∀ (fields : List (List Nat)) (fuel : Nat) (c c' : WCtx) (nf nf' : Bool),
    fieldLoop d fuel c (fields.map fun f => .ret (.str f)) nf = (c', .ok nf') →
    Chain d fields c.buf c.numFields c'.buf c'.numFields ∧ c'.written = c.written ∧ c'.calls = c.calls ∧
      (fields ≠ [] → nf' = false) := by
  intro fields
  induction fields with
  | nil =>
    intro fuel c c' nf nf' h
    cases fuel with
    | zero => simp [fieldLoop] at h
    | succ k =>
      simp only [List.map_nil, fieldLoop, Prod.mk.injEq, Except.ok.injEq] at h
      rw [← h.1]
      exact ⟨.nil _ _, rfl, rfl, fun e => absurd rfl e⟩
  | cons f fs ih =>
    intro fuel c c' nf nf' h
    cases fuel with
    | zero => simp [fieldLoop] at h
    | succ k =>
      simp only [List.map_cons, fieldLoop, Obj.asStr] at h
      cases hj : joinAppend d c.buf c.numFields (some f) (initialQuoted d (.str f)) with
      | error e =>
        simp [hj] at h
      | ok v =>
        obtain ⟨b, n⟩ := v
        simp only [hj] at h
        obtain ⟨r1, r2, r3, r4⟩ := ih k _ _ _ _ h
        refine ⟨.cons hj r1, r2, r3, fun _ => ?_⟩
        by_cases he : fs = []
        · subst he
          cases k with
          | zero => simp [fieldLoop] at h
          | succ j =>
            simp only [List.map_nil, fieldLoop, Prod.mk.injEq, Except.ok.injEq] at h
            exact h.2.symm
        · exact r4 he

theorem callWrite_ok {d : Dialect} {k : Nat} {c c' : WCtx} {o : Obj}
    (h : callWrite d k c = (c', .ok o)) (hc : c.calls = []) : c'.written = c.written ++ [c.buf] := by
  cases k with
  | zero => simp [callWrite] at h
  | succ j =>
    simp only [callWrite, hc, Prod.mk.injEq, Except.ok.injEq] at h
    rw [← h.1]

theorem finish_plain {d : Dialect} {k : Nat} {c c' : WCtx} {nf : Bool} {o : Obj}
    (h : finishRow d k c nf = (c', .ok o)) (hc : c.calls = []) (hw : c.written = [])
    (hb : ¬(c.numFields > 0 ∧ c.buf.isEmpty = true)) : c'.written = [c.buf ++ d.lineterminator] := by
  cases k with
  | zero => simp [finishRow] at h
  | succ j =>
    simp only [finishRow] at h
    rw [if_neg hb] at h
    have := callWrite_ok h hc
    simpa [hw] using this

theorem finish_single {d : Dialect} (g : Good d) {k : Nat} {c c' : WCtx} {nf : Bool} {o : Obj}
    (h : finishRow d k c nf = (c', .ok o)) (hc : c.calls = []) (hw : c.written = [])
    (hb : c.buf = []) (hn : c.numFields = 1) (hf : nf = false) :
    c'.written = [[d.quotechar, d.quotechar] ++ d.lineterminator] := by
  cases k with
  | zero => simp [finishRow] at h
  | succ j =>
    simp only [finishRow] at h
    rw [if_pos ⟨by omega, by simp [hb]⟩] at h
    have hnn := good_notNone g
    rw [if_neg (by simp [hnn, hf])] at h
    have hj : joinAppend d c.buf (c.numFields - 1) Option.none true =
        .ok ([d.quotechar, d.quotechar], cIntWrap (c.numFields - 1 + 1)) := by
      simp [joinAppend, joinField, hb, hn, g.skip, bind, Except.bind, pure, Except.pure]
    simp only [hj] at h
    have := callWrite_ok h hc
    simpa [hw] using this

/-- The round trip, with every assumption either a type invariant or a documented limit. The line
terminator is `\r`, `\n` or `\r\n` because the docs say the reader recognises only those, whatever
`lineterminator` says. Fields fit `field_size_limit`, which the reader would otherwise reject. Fewer
than `2 ^ 31` fields, because beyond that `textlibs-csv-num-fields` shows the writer loses delimiters.
Dialect characters are code points, and `skipinitialspace` is off because `CsvRoundTrip` shows what
happens when it is on. -/
def CsvRoundTripNoSkip : Prop :=
  ∀ (a : DArgs) (d : Dialect) (row : List (List Nat)) (lim : Int) (fuel g : Nat) (c : WCtx) (o : Obj)
    (t : List Nat),
    dialectBuild a = .ok d → (d.quoting = QUOTE_MINIMAL ∨ d.quoting = QUOTE_ALL) →
    d.skipinitialspace = false →
    (d.lineterminator = [13, 10] ∨ d.lineterminator = [10] ∨ d.lineterminator = [13]) →
    d.delimiter < 0x110000 → d.quotechar < 0x110000 →
    (d.escapechar < 0x110000 ∨ d.escapechar = NOT_SET) →
    row.length < 2 ^ 31 → (∀ f ∈ row, (f.length : Int) ≤ lim ∧ ∀ x ∈ f, x < 0x110000) →
    writerowM d fuel {} (rowObj row) = (c, .ok o) → c.written = [t] →
    (readerNext d (g + 4) { acts := [.ret (.str t)], limit := lim }).2 = .ok (some (row.map Field.str))

theorem good_of {a : DArgs} {d : Dialect} (h : dialectBuild a = .ok d)
    (h1 : d.quoting = QUOTE_MINIMAL ∨ d.quoting = QUOTE_ALL) (h2 : d.skipinitialspace = false)
    (h3 : d.lineterminator = [13, 10] ∨ d.lineterminator = [10] ∨ d.lineterminator = [13])
    (h4 : d.delimiter < 0x110000) (h5 : d.quotechar < 0x110000)
    (h6 : d.escapechar < 0x110000 ∨ d.escapechar = NOT_SET) : Good d := by
  obtain ⟨_, _, ⟨d13, d10, _⟩, ⟨e13, e10, _⟩, ⟨q13, q10, _⟩, _, c1, c2, c3⟩ := dialectValid_proven a d h
  have hNS : ∀ x : Nat, x < 0x110000 → x ≠ NOT_SET := by
    intro x hx e
    rw [e] at hx
    revert hx
    decide
  have hEOL : ∀ x : Nat, x < 0x110000 → x ≠ EOL := by
    intro x hx e
    rw [e] at hx
    revert hx
    decide
  have hnl : ∀ x : Nat, x ≠ 13 → x ≠ 10 → isNl x = false := by
    intro x a b
    simp [isNl, a, b]
  refine ⟨h1, h2, hnl _ d13 d10, hnl _ q13 q10, hnl _ e13 e10, hEOL _ h4, hEOL _ h5, ?_, ?_, ?_, ?_, h3⟩
  · rcases h6 with h6 | h6
    · exact hEOL _ h6
    · rw [h6]
      decide
  · exact fun e => hNS _ h4 (c2 e)
  · exact fun e => hNS _ h4 (c1 e)
  · exact fun e => hNS _ h5 (by rw [e]; exact c3 e.symm)

theorem chain_nil_inv {d : Dialect} {b b2 : List Nat} {n n2 : Int} (h : Chain d [] b n b2 n2) :
    b2 = b ∧ n2 = n := by
  cases h
  exact ⟨rfl, rfl⟩

theorem chain_cons_inv {d : Dialect} {f : List Nat} {fs : List (List Nat)} {b b2 : List Nat} {n n2 : Int}
    (h : Chain d (f :: fs) b n b2 n2) :
    ∃ q b1 n1, joinAppend d b n (some f) q = .ok (b1, n1) ∧ Chain d fs b1 n1 b2 n2 := by
  cases h with
  | cons h1 h2 => exact ⟨_, _, _, h1, h2⟩

/-- The text the writer produced reads back as the row, up to the end of the line. -/
theorem read_written {d : Dialect} {lim : Int} (g : Good d) (row : List (List Nat)) (c1 : WCtx)
    (hchain : Chain d row [] 0 c1.buf c1.numFields) (hlen : row.length < 2 ^ 31)
    (hv : ∀ f ∈ row, (∀ x ∈ f, x ≠ EOL) ∧ (f.length : Int) ≤ lim) :
    (∃ s, parseLine d lim (parseReset {}) (c1.buf ++ d.lineterminator) = (s, Option.none) ∧
      s.state = .START_RECORD ∧ s.fields = row.map Field.str ∧ ¬(c1.numFields > 0 ∧ c1.buf.isEmpty = true)) ∨
    (row = [[]] ∧ c1.buf = [] ∧ c1.numFields = 1 ∧
      ∃ s, parseLine d lim (parseReset {}) ([d.quotechar, d.quotechar] ++ d.lineterminator) = (s, Option.none) ∧
        s.state = .START_RECORD ∧ s.fields = row.map Field.str) := by
  have hs0 : (parseReset ({} : RSt)).state = .START_RECORD := rfl
  cases row with
  | nil =>
    obtain ⟨hb, hn⟩ := chain_nil_inv hchain
    obtain ⟨s1, s2, a1, a2, a3, a4⟩ := line_end_empty (lim := lim) g (parseReset {}) hs0
    refine .inl ⟨s2, ?_, a3, a4, ?_⟩
    · rw [hb]
      exact parseLine_of (rfl : parseChars d lim (parseReset {}) [] = _) a1 a2
    · rw [hn]
      simp
  | cons f0 rest =>
    obtain ⟨q, b1, n1, hj, hrest⟩ := chain_cons_inv hchain
    obtain ⟨body, q1, q2, hjf, hn1, hb1⟩ := joinAppend_ok hj
    have hn1' : n1 = 1 := by rw [hn1]; decide
    subst hn1'
    obtain ⟨hv1, hv2⟩ := hv f0 (by simp)
    obtain ⟨s1, r1, r2, r3, r4, _⟩ := read_field (lim := lim) g f0 (parseReset {}) body q1 q2 hv1
      (by simpa using hjf) (.inl hs0) rfl hv2
    have hb1' : b1 = (if q2 then [d.quotechar] else []) ++ body ++ (if q2 then [d.quotechar] else []) := by
      simpa [List.append_assoc] using hb1
    simp only [List.length_cons] at hlen
    obtain ⟨X, s', e1, e2, e3, e4, e5, e6, e7⟩ := read_rest (lim := lim) g hrest (Int.le_refl 1)
      (by omega) (fun x hx => hv x (by simp [hx])) s1 r3 (by rw [r2.nulls]; rfl)
    have hall := reach_append r1 e2
    rw [← hb1'] at hall
    have hfields : s'.fields ++ [.str s'.field] = (f0 :: rest).map Field.str := by
      rw [e5, r2.fields, r2.field]
      simp [parseReset]
    by_cases hstart : s'.state = .START_RECORD
    · -- one empty field, which the writer quotes
      have hrnil : rest = [] := by
        by_cases hr : rest = []
        · exact hr
        · exact absurd hstart (e6 hr)
      subst hrnil
      obtain ⟨e8, e9⟩ := e7 rfl
      subst e8
      obtain ⟨hf0, hq2⟩ := r4 hstart
      subst hf0
      subst hq2
      subst e9
      have hbody : body = [] := by
        have := hjf
        simp only [Option.getD_some, joinField, Except.ok.injEq, Prod.mk.injEq] at this
        exact this.1.symm
      obtain ⟨hb2, hn2⟩ := chain_nil_inv hrest
      have hbuf : c1.buf = [] := by
        rw [hb2, hb1', hbody]
        simp
      refine .inr ⟨rfl, hbuf, hn2, ?_⟩
      have hopen := step_open (lim := lim) (s := parseReset {}) g (.inl hs0)
      have hclose := step_q_quote (lim := lim)
        (s := { parseReset ({} : RSt) with state := .IN_QUOTED_FIELD, unquoted := false }) g rfl
      have hst : ({ parseReset ({} : RSt) with state := if d.doublequote then .QUOTE_IN_QUOTED_FIELD else .IN_FIELD } : RSt).state = .START_FIELD ∨
          ({ parseReset ({} : RSt) with state := if d.doublequote then .QUOTE_IN_QUOTED_FIELD else .IN_FIELD } : RSt).state = .IN_FIELD ∨
          ({ parseReset ({} : RSt) with state := if d.doublequote then .QUOTE_IN_QUOTED_FIELD else .IN_FIELD } : RSt).state = .QUOTE_IN_QUOTED_FIELD := by
        cases hq : d.doublequote <;> simp [hq]
      obtain ⟨s3, s4, a1, a2, a3, a4⟩ := line_end (lim := lim) g
        { parseReset ({} : RSt) with state := if d.doublequote then .QUOTE_IN_QUOTED_FIELD else .IN_FIELD } hst rfl
      refine ⟨s4, ?_, a3, a4⟩
      · exact parseLine_of (s1 := { parseReset ({} : RSt) with state := if d.doublequote then .QUOTE_IN_QUOTED_FIELD else .IN_FIELD })
          (reach_cons hopen (reach_cons hclose rfl)) a1 a2
    · have hc3 : s'.state = .START_FIELD ∨ s'.state = .IN_FIELD ∨ s'.state = .QUOTE_IN_QUOTED_FIELD := by
        rcases e3 with h | h | h | h
        · exact absurd h hstart
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h)
      obtain ⟨s3, s4, a1, a2, a3, a4⟩ := line_end (lim := lim) g s' hc3 e4
      refine .inl ⟨s4, ?_, a3, by rw [a4]; exact hfields, ?_⟩
      · rw [e1]
        exact parseLine_of hall a1 a2
      · rintro ⟨_, hemp⟩
        have hnil : c1.buf = [] := List.isEmpty_iff.1 hemp
        rw [e1] at hnil
        rw [hnil] at hall
        simp only [parseChars, Prod.mk.injEq, and_true] at hall
        rw [← hall] at hstart
        exact hstart hs0

theorem csvRoundTripNoSkip_proven : CsvRoundTripNoSkip := by
  intro a d row lim fuel g' c o t hd h1 h2 h3 h4 h5 h6 hlen hv hw ht
  have g := good_of hd h1 h2 h3 h4 h5 h6
  have hEOL : ∀ x : Nat, x < 0x110000 → x ≠ EOL := by
    intro x hx e
    rw [e] at hx
    revert hx
    decide
  have hv' : ∀ f ∈ row, (∀ x ∈ f, x ≠ EOL) ∧ (f.length : Int) ≤ lim :=
    fun f hf => ⟨fun x hx => hEOL x ((hv f hf).2 x hx), (hv f hf).1⟩
  cases fuel with
  | zero => simp [writerowM] at hw
  | succ k =>
    have hi : (rowObj row).getIter = .ok (row.map fun f => .ret (.str f)) := rfl
    simp only [writerowM, hi] at hw
    cases hf : fieldLoop d k { ({} : WCtx) with buf := [], numFields := 0 }
        (row.map fun f => .ret (.str f)) false with
    | mk c1 r =>
      cases r with
      | error e => simp [hf] at hw
      | ok nf =>
        simp only [hf] at hw
        obtain ⟨hchain, hwr, hca, hnf⟩ := fieldLoop_strs row k _ c1 false nf hf
        have hwr0 : c1.written = [] := hwr
        have hca0 : c1.calls = [] := hca
        have hch : Chain d row [] 0 c1.buf c1.numFields := hchain
        have hfinal : ∃ s, parseLine d lim (parseReset {}) t = (s, Option.none) ∧
            s.state = .START_RECORD ∧ s.fields = row.map Field.str := by
          rcases read_written (lim := lim) g row c1 hch hlen hv' with
            ⟨s, a1, a2, a3, a4⟩ | ⟨e1, e2, e3, s, a1, a2, a3⟩
          · have := finish_plain hw hca0 hwr0 a4
            rw [ht] at this
            have ht' : t = c1.buf ++ d.lineterminator := by simpa using this
            exact ⟨s, by rw [ht']; exact a1, a2, a3⟩
          · have hn0 : nf = false := hnf (by rw [e1]; simp)
            have := finish_single g hw hca0 hwr0 e2 e3 hn0
            rw [ht] at this
            have ht' : t = [d.quotechar, d.quotechar] ++ d.lineterminator := by simpa using this
            exact ⟨s, by rw [ht']; exact a1, a2, a3⟩
        obtain ⟨s, hp, hst, hfs⟩ := hfinal
        have hl := loop_line d (g' + 1) { s := parseReset {}, acts := [.ret (.str t)], limit := lim }
          (.str t) t [] s rfl rfl rfl hp hst
        rw [show g' + 4 = (g' + 3) + 1 from rfl, readerNext_succ]
        have hk := congrArg Prod.snd hl
        rw [← hfs]
        exact hk

end PyLean.TextLibs.Csv
