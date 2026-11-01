import PyLean.LongObj.ComplexObj

/-!
Properties of the `complex()` string parser.

The float conversion is the abstract `sd : Strtod R`. `StrtodSpec` lists all that
is assumed of it. Those are facts about any `strtod`, not about the input: it
consumes only what is there, and it never reads past a character that cannot
occur in a number, so what follows such a character cannot change its result.
`Dbl.asciiStrtod` runs in the difftest, where 100% agreement with CPython supports
these two facts for it.
-/

namespace PyLean.LongObj.Cplx

open CDouble

/-- A character no number contains: NUL, `?` (which the transform writes for an
unconvertible character), whitespace, and the parentheses. -/
def isStop (c : Nat) : Bool :=
  c == 0 || c == 63 || isSpaceC c || c == chLParen || c == chRParen

/-- What is assumed of the float conversion. -/
structure StrtodSpec {R : Type} (sd : Strtod R) : Prop where
  /-- It consumes only what is there. -/
  le_length : ∀ p, (sd p).2 ≤ p.length
  /-- A stop character ends the text it reads. -/
  cut : ∀ p c q, isStop c = true → sd (p ++ c :: q) = sd p

section stop

variable {R : Type} [CDouble R] {sd : Strtod R}

/-- `p` is the part of `u ++ t :: v` that the parser has not consumed, and the
position is `i`: it has not gone past `t`. -/
def Reach (t : Nat) (v : List Nat) (U : Nat) (p : List Nat) (i : Nat) : Prop :=
  ∃ u', p = u' ++ t :: v ∧ i + u'.length = U

theorem reach_tail {t v U p i} (h : Reach t v U p i) (hc : cur p ≠ t) :
    Reach t v U p.tail (i + 1) := by
  obtain ⟨u', rfl, hl⟩ := h
  cases u' with
  | nil => simp [cur] at hc
  | cons c r =>
    refine ⟨r, by simp, ?_⟩
    simp at hl
    omega

theorem reach_drop (hs : StrtodSpec sd) {t v U p i} (ht : isStop t = true)
    (h : Reach t v U p i) : Reach t v U (p.drop (sd p).2) (i + (sd p).2) := by
  obtain ⟨u', rfl, hl⟩ := h
  have hcut := hs.cut u' t v ht
  rw [hcut]
  have hle := hs.le_length u'
  refine ⟨u'.drop (sd u').2, ?_, ?_⟩
  · rw [List.drop_append_of_le_length hle]
  · simp only [List.length_drop]
    omega

theorem reach_skip {t v U} (ht : isSpaceC t = false) :
    ∀ (u' : List Nat) (i : Nat), i + u'.length = U →
      Reach t v U (skipSpace (u' ++ t :: v) i).1 (skipSpace (u' ++ t :: v) i).2 := by
  intro u'
  induction u' with
  | nil =>
    intro i hl
    simp only [List.nil_append, skipSpace, ht, Bool.false_eq_true, ite_false]
    exact ⟨[], by simp, by simpa using hl⟩
  | cons c r ih =>
    intro i hl
    simp only [List.cons_append, skipSpace]
    split
    · exact ih (i + 1) (by simp at hl; omega)
    · exact ⟨c :: r, by simp, hl⟩

theorem reach_skip' {t v U p i} (ht : isSpaceC t = false) (h : Reach t v U p i) :
    Reach t v U (skipSpace p i).1 (skipSpace p i).2 := by
  obtain ⟨u', rfl, hl⟩ := h
  exact reach_skip ht u' i hl

/-- The characters the parser steps over one at a time. -/
def NotSyntax (t : Nat) : Prop := isSign t = false ∧ isJ t = false ∧ t ≠ chLParen ∧ t ≠ chRParen

theorem reach_body (hs : StrtodSpec sd) {t v U p i x y q j} (ht : isStop t = true)
    (hn : NotSyntax t) (h : Reach t v U p i)
    (hb : parseBody sd p i = some (x, y, q, j)) : Reach t v U q j := by
  obtain ⟨hsg, hj, _, _⟩ := hn
  have hcur_sign : ∀ {r : List Nat}, isSign (cur r) = true → cur r ≠ t := by
    intro r hr he; rw [he, hsg] at hr; exact Bool.noConfusion hr
  have hcur_j : ∀ {r : List Nat}, isJ (cur r) = true → cur r ≠ t := by
    intro r hr he; rw [he, hj] at hr; exact Bool.noConfusion hr
  simp only [parseBody] at hb
  generalize hsd : sd p = sp at hb
  obtain ⟨z, n⟩ := sp
  simp only at hb
  by_cases hn0 : n ≠ 0
  · simp only [hn0, ne_eq, not_false_eq_true, ite_true] at hb
    have hd : Reach t v U (p.drop n) (i + n) := by
      have := reach_drop hs ht h
      rwa [hsd] at this
    by_cases hsgn : isSign (cur (p.drop n)) = true
    · simp only [hsgn, ite_true] at hb
      generalize hsd2 : sd (p.drop n) = sp2 at hb
      obtain ⟨y₀, m⟩ := sp2
      simp only at hb
      by_cases hm : m ≠ 0
      · simp only [hm, ne_eq, not_false_eq_true, ite_true] at hb
        have hd2 : Reach t v U ((p.drop n).drop m) (i + n + m) := by
          have := reach_drop hs ht hd
          rwa [hsd2] at this
        by_cases hjj : isJ (cur ((p.drop n).drop m)) = true
        · simp only [hjj, Bool.not_true, Bool.false_eq_true, ite_false, Option.some.injEq,
            Prod.mk.injEq] at hb
          obtain ⟨_, _, rfl, rfl⟩ := hb
          exact reach_tail hd2 (hcur_j hjj)
        · have hjf := Bool.eq_false_iff.2 hjj
          simp only [hjf, Bool.not_false, ite_true] at hb
          cases hb
      · simp only [hm, ne_eq, not_false_eq_true, ite_false, not_true_eq_false] at hb
        have hd2 := reach_tail hd (hcur_sign hsgn)
        by_cases hjj : isJ (cur (p.drop n).tail) = true
        · simp only [hjj, Bool.not_true, Bool.false_eq_true, ite_false, Option.some.injEq,
            Prod.mk.injEq] at hb
          obtain ⟨_, _, rfl, rfl⟩ := hb
          exact reach_tail hd2 (hcur_j hjj)
        · have hjf := Bool.eq_false_iff.2 hjj
          simp only [hjf, Bool.not_false, ite_true] at hb
          cases hb
    · simp only [hsgn, Bool.false_eq_true, ite_false] at hb
      by_cases hjj : isJ (cur (p.drop n)) = true
      · simp only [hjj, ite_true, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨_, _, rfl, rfl⟩ := hb
        exact reach_tail hd (hcur_j hjj)
      · simp only [hjj, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨_, _, rfl, rfl⟩ := hb
        exact hd
  · simp only [hn0, ne_eq, not_false_eq_true, ite_false, not_true_eq_false] at hb
    by_cases hsgn : isSign (cur p) = true
    · simp only [hsgn, ite_true] at hb
      have hd2 := reach_tail h (hcur_sign hsgn)
      by_cases hjj : isJ (cur p.tail) = true
      · simp only [hjj, Bool.not_true, Bool.false_eq_true, ite_false, Option.some.injEq,
          Prod.mk.injEq] at hb
        obtain ⟨_, _, rfl, rfl⟩ := hb
        exact reach_tail hd2 (hcur_j hjj)
      · have hjf := Bool.eq_false_iff.2 hjj
        simp only [hjf, Bool.not_false, ite_true] at hb
        cases hb
    · simp only [hsgn, Bool.false_eq_true, ite_false] at hb
      by_cases hjj : isJ (cur p) = true
      · simp only [hjj, Bool.not_true, Bool.false_eq_true, ite_false, Option.some.injEq,
          Prod.mk.injEq] at hb
        obtain ⟨_, _, rfl, rfl⟩ := hb
        exact reach_tail h (hcur_j hjj)
      · have hjf := Bool.eq_false_iff.2 hjj
        simp only [hjf, Bool.not_false, ite_true] at hb
        cases hb

/-- A string with a stop character that is not whitespace in it is never accepted:
the parser cannot step over `t`, so it cannot reach `len`. -/
theorem inner_stop (hs : StrtodSpec sd) (u v : List Nat) (t : Nat) (ht : t = 0 ∨ t = 63) :
    complex_from_string_inner sd (u ++ t :: v) (u ++ t :: v).length = .error malformed := by
  have hstop : isStop t = true := by rcases ht with rfl | rfl <;> decide
  have hsp : isSpaceC t = false := by rcases ht with rfl | rfl <;> decide
  have hsyn : NotSyntax t := by
    rcases ht with rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide⟩
  have hparen : t ≠ chLParen := hsyn.2.2.1
  have hr0 : Reach t v u.length (u ++ t :: v) 0 := ⟨u, rfl, by simp⟩
  have hlen : ∀ {j : Nat}, ∀ {q}, Reach t v u.length q j → j ≠ (u ++ t :: v).length := by
    intro j q h
    obtain ⟨u', _, hl⟩ := h
    simp only [List.length_append, List.length_cons]
    omega
  have hr1 := reach_skip' hsp hr0
  simp only [complex_from_string_inner]
  generalize hsk : skipSpace (u ++ t :: v) 0 = sk at hr1 ⊢
  obtain ⟨p₁, i₁⟩ := sk
  simp only at hr1 ⊢
  have hopen : Reach t v u.length
      (if cur p₁ == chLParen then ((skipSpace p₁.tail (i₁ + 1)).1, (skipSpace p₁.tail (i₁ + 1)).2, true)
        else (p₁, i₁, false)).1
      (if cur p₁ == chLParen then ((skipSpace p₁.tail (i₁ + 1)).1, (skipSpace p₁.tail (i₁ + 1)).2, true)
        else (p₁, i₁, false)).2.1 := by
    by_cases hb : (cur p₁ == chLParen) = true
    · simp only [hb, ite_true]
      have hc : cur p₁ ≠ t := by
        have : cur p₁ = chLParen := by simpa using hb
        rw [this]; exact fun e => hparen e.symm
      exact reach_skip' hsp (reach_tail hr1 hc)
    · simp only [hb, Bool.false_eq_true, ite_false]
      exact hr1
  by_cases hb : (cur p₁ == chLParen) = true
  · simp only [hb, ite_true] at hopen ⊢
    generalize hsk2 : skipSpace p₁.tail (i₁ + 1) = sk2 at hopen ⊢
    obtain ⟨p₂, i₂⟩ := sk2
    simp only at hopen ⊢
    cases hpb : parseBody sd p₂ i₂ with
    | none => rfl
    | some r =>
      obtain ⟨x, y, q, j⟩ := r
      have hq := reach_body hs hstop hsyn hopen hpb
      have hq' := reach_skip' hsp hq
      simp only
      generalize hsk3 : skipSpace q j = sk3 at hq' ⊢
      obtain ⟨q₂, j₂⟩ := sk3
      simp only at hq' ⊢
      by_cases hc : (cur q₂ != chRParen) = true
      · simp only [hc, ite_true]
      · have hc' : cur q₂ = chRParen := by simpa using hc
        have hne : cur q₂ ≠ t := by rw [hc']; exact fun e => hsyn.2.2.2 e.symm
        have hq3 := reach_skip' hsp (reach_tail hq' hne)
        simp only [hc, Bool.false_eq_true, ite_false]
        generalize hsk4 : skipSpace q₂.tail (j₂ + 1) = sk4 at hq3 ⊢
        obtain ⟨q₃, j₃⟩ := sk4
        simp only at hq3 ⊢
        have : (j₃ != (u ++ t :: v).length) = true := by simpa using hlen hq3
        simp only [this, ite_true]
  · simp only [hb, Bool.false_eq_true, ite_false] at hopen ⊢
    cases hpb : parseBody sd p₁ i₁ with
    | none => rfl
    | some r =>
      obtain ⟨x, y, q, j⟩ := r
      have hq := reach_body hs hstop hsyn hopen hpb
      have hq' := reach_skip' hsp hq
      simp only
      generalize hsk3 : skipSpace q j = sk3 at hq' ⊢
      obtain ⟨q₂, j₂⟩ := sk3
      simp only at hq' ⊢
      have : (j₂ != (u ++ t :: v).length) = true := by simpa using hlen hq'
      simp only [this, ite_true]

/-- Split a list at a chosen element. -/
theorem exists_split {t : Nat} {T : List Nat} (h : t ∈ T) : ∃ u v, T = u ++ t :: v := by
  obtain ⟨u, v, e⟩ := List.append_of_mem h
  exact ⟨u, v, e⟩

/-- The scan keeps every character but `_` when it reaches the end. -/
theorem underscoreScan_full : ∀ (T : List Nat) (prev : Nat) (acc : List Nat) (n : Nat)
    (o : List Nat) (p m : Nat), underscoreScan T prev acc n = some (o, p, m) →
    m = n + T.length → 0 ∉ T ∧ o.reverse = acc.reverse ++ T.filter (· != chUnderscore) := by
  intro T
  induction T with
  | nil =>
    intro prev acc n o p m h _
    simp only [underscoreScan, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _, _⟩ := h
    simp
  | cons c t ih =>
    intro prev acc n o p m h hm
    simp only [underscoreScan] at h
    by_cases h0 : (c == 0) = true
    · simp only [h0, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      simp at hm
    · simp only [h0, Bool.false_eq_true, ite_false] at h
      have hc0 : c ≠ 0 := by simpa using h0
      by_cases hu : (c == chUnderscore) = true
      · simp only [hu, ite_true] at h
        split at h
        · exact absurd h (by simp)
        · have := ih _ _ _ _ _ _ h (by simp at hm; omega)
          have hcu : c = chUnderscore := by simpa using hu
          refine ⟨?_, ?_⟩
          · simp only [List.mem_cons, not_or]
            exact ⟨fun e => hc0 e.symm, this.1⟩
          · rw [this.2]
            simp [hcu]
      · simp only [hu, Bool.false_eq_true, ite_false] at h
        split at h
        · exact absurd h (by simp)
        · have := ih _ _ _ _ _ _ h (by simp at hm; omega)
          have hcu : c ≠ chUnderscore := by simpa using hu
          refine ⟨?_, ?_⟩
          · simp only [List.mem_cons, not_or]
            exact ⟨fun e => hc0 e.symm, this.1⟩
          · rw [this.2]
            simp [hcu]

/-- A buffer holding NUL or `?` is rejected, with a `ValueError`, on both the
plain path and the underscore path. -/
theorem withUnderscores_stop (hs : StrtodSpec sd) (T : List Nat) (what r : String)
    (ht : 0 ∈ T ∨ 63 ∈ T) :
    ∃ m, withUnderscores T T.length what r (complex_from_string_inner sd) =
      .error (.valueError m) := by
  have direct : ∀ L : List Nat, (0 ∈ L ∨ 63 ∈ L) →
      complex_from_string_inner sd L L.length = .error malformed := by
    intro L hL
    rcases hL with hL | hL
    · obtain ⟨u, v, rfl⟩ := exists_split hL
      exact inner_stop hs u v 0 (Or.inl rfl)
    · obtain ⟨u, v, rfl⟩ := exists_split hL
      exact inner_stop hs u v 63 (Or.inr rfl)
  simp only [withUnderscores]
  by_cases hu : hasUnderscore T = true
  · simp only [hu, Bool.not_true, Bool.false_eq_true, ite_false]
    cases hsc : underscoreScan T 0 [] 0 with
    | none => exact ⟨_, rfl⟩
    | some r' =>
      obtain ⟨o, p, n⟩ := r'
      simp only
      by_cases hp : (p == chUnderscore) = true
      · simp only [hp, ite_true]
        exact ⟨_, rfl⟩
      · simp only [hp, Bool.false_eq_true, ite_false]
        by_cases hn : (n != T.length) = true
        · simp only [hn, ite_true]
          exact ⟨_, rfl⟩
        · simp only [hn, Bool.false_eq_true, ite_false]
          have hn' : n = T.length := by simpa using hn
          have := underscoreScan_full T 0 [] 0 o p n hsc (by omega)
          have h63 : 63 ∈ T := by
            rcases ht with h | h
            · exact absurd h this.1
            · exact h
          have hmem : 63 ∈ o.reverse := by
            rw [this.2]
            simp only [List.reverse_nil, List.nil_append, List.mem_filter]
            exact ⟨h63, by decide⟩
          refine ⟨"complex() arg is a malformed string", ?_⟩
          have hlenr : o.length = o.reverse.length := by simp
          rw [hlenr]
          exact direct _ (Or.inr hmem)
  · have : hasUnderscore T = false := by simpa using hu
    simp only [this, Bool.not_false, ite_true]
    exact ⟨"complex() arg is a malformed string", direct T ht⟩

/-- The transform keeps a NUL, or else stops at a `?` before reaching it. -/
theorem transformLoop_nul (db : UniDB) : ∀ s : List Nat, 0 ∈ s →
    0 ∈ transformLoop db s ∨ 63 ∈ transformLoop db s := by
  intro s
  induction s with
  | nil => intro h; simp at h
  | cons c t ih =>
    intro h
    simp only [transformLoop]
    by_cases hc : c < 127
    · simp only [hc, ite_true, List.mem_cons]
      rcases List.mem_cons.1 h with h | h
      · left; left; exact h
      · rcases ih h with h' | h'
        · left; right; exact h'
        · right; right; exact h'
    · have hc0 : c ≠ 0 := by omega
      have ht : 0 ∈ t := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hc0
        · exact h
      simp only [hc, ite_false]
      by_cases hsp : db.isSpace c = true
      · simp only [hsp, ite_true, List.mem_cons]
        rcases ih ht with h' | h'
        · left; right; exact h'
        · right; right; exact h'
      · simp only [hsp, Bool.false_eq_true, ite_false]
        cases hd : db.toDecimal c with
        | none => right; simp
        | some d =>
          simp only [List.mem_cons]
          rcases ih ht with h' | h'
          · left; right; exact h'
          · right; right; exact h'

end stop

/-- Every string holding a NUL is rejected with a `ValueError`, on any `strtod`,
whether or not it has underscores or non-ASCII characters. The C code works on a
NUL-terminated buffer, so this is the check at line 1042 doing its job. -/
def ParseRejectsNul : Prop :=
  ∀ (R : Type) [CDouble R] (sd : Strtod R), StrtodSpec sd →
    ∀ (db : UniDB) (v : List Nat) (r : String), 0 ∈ v →
      ∃ m, complex_from_str db sd v r = .error (.valueError m)

theorem parseRejectsNul_proven : ParseRejectsNul := by
  intro R _ sd hs db v r hv
  have ht : 0 ∈ transformDecimalAndSpace db v ∨ 63 ∈ transformDecimalAndSpace db v := by
    unfold transformDecimalAndSpace
    split
    · exact Or.inl hv
    · exact transformLoop_nul db v hv
  exact withUnderscores_stop hs _ _ _ ht

/-- The only exception `complex(str)` raises is `ValueError`: no `OverflowError`
for `1e400`, no `MemoryError` modelled, nothing else leaks from the parser. -/
def ParseRaisesOnlyValueError : Prop :=
  ∀ (R : Type) [CDouble R] (sd : Strtod R) (db : UniDB) (v : List Nat) (r : String) (e : PyExc),
    complex_from_str db sd v r = .error e → e.className = "ValueError"

theorem inner_error {R : Type} [CDouble R] (sd : Strtod R) (s : List Nat) (n : Nat) (e : PyExc)
    (h : complex_from_string_inner sd s n = .error e) : e = malformed := by
  simp only [complex_from_string_inner] at h
  repeat' (split at h)
  all_goals first
    | (simp only [Except.error.injEq] at h; exact h.symm)
    | simp at h

theorem parseRaisesOnlyValueError_proven : ParseRaisesOnlyValueError := by
  intro R _ sd db v r e h
  simp only [complex_from_str, withUnderscores] at h
  split at h
  · rw [inner_error sd _ _ _ h]; rfl
  · split at h
    · simp only [Except.error.injEq] at h; rw [← h]; rfl
    · split at h
      · simp only [Except.error.injEq] at h; rw [← h]; rfl
      · split at h
        · simp only [Except.error.injEq] at h; rw [← h]; rfl
        · rw [inner_error sd _ _ _ h]; rfl

/-- The buffer the parser sees is ASCII, the assert on line 1065, when
`Py_UNICODE_TODECIMAL` gives a digit; ASCII input is untouched; a non-ASCII
whitespace becomes a space and a decimal digit its ASCII digit. -/
def TransformAscii : Prop :=
  ∀ (db : UniDB), (∀ c d, db.toDecimal c = some d → d < 10) →
    ∀ s : List Nat, (∀ c ∈ transformDecimalAndSpace db s, c < 128) ∧
      (s.all (· < 128) = true → transformDecimalAndSpace db s = s)

theorem transformLoop_ascii (db : UniDB) (h : ∀ c d, db.toDecimal c = some d → d < 10) :
    ∀ (s : List Nat), ∀ c ∈ transformLoop db s, c < 128 := by
  intro s
  induction s with
  | nil => simp [transformLoop]
  | cons x t ih =>
    intro c hc
    simp only [transformLoop] at hc
    split at hc
    · rcases List.mem_cons.1 hc with h1 | h1
      · omega
      · exact ih c h1
    · split at hc
      · rcases List.mem_cons.1 hc with h1 | h1
        · omega
        · exact ih c h1
      · cases hd : db.toDecimal x with
        | none =>
          simp only [hd] at hc
          simp at hc
          omega
        | some d =>
          simp only [hd] at hc
          have := h x d hd
          rcases List.mem_cons.1 hc with h1 | h1
          · omega
          · exact ih c h1

theorem transformAscii_proven : TransformAscii := by
  intro db h s
  constructor
  · intro c hc
    unfold transformDecimalAndSpace at hc
    split at hc
    · next hall =>
      have := List.all_eq_true.1 hall c hc
      simpa using this
    · exact transformLoop_ascii db h s c hc
  · intro hall
    simp [transformDecimalAndSpace, hall]

/-! ## Whitespace -/

theorem skipSpace_shift : ∀ (s : List Nat) (i k : Nat),
    skipSpace s (i + k) = ((skipSpace s i).1, (skipSpace s i).2 + k) := by
  intro s
  induction s with
  | nil => intro i k; rfl
  | cons c t ih =>
    intro i k
    simp only [skipSpace]
    split
    · have := ih (i + 1) k
      rw [show i + k + 1 = i + 1 + k by omega]
      exact this
    · rfl

theorem skipSpace_append_spaces (ws s : List Nat) (hw : ∀ c ∈ ws, isSpaceC c = true) (i : Nat) :
    skipSpace (ws ++ s) i = skipSpace s (i + ws.length) := by
  induction ws generalizing i with
  | nil => rfl
  | cons c t ih =>
    have hc := hw c (by simp)
    simp only [List.cons_append, skipSpace, hc, ite_true]
    rw [ih (fun x hx => hw x (by simp [hx]))]
    congr 1
    simp only [List.length_cons]
    omega

section shift

variable {R : Type} [CDouble R]

theorem parseBody_shift (sd : Strtod R) (p : List Nat) (i k : Nat) :
    parseBody sd p (i + k) =
      (parseBody sd p i).map (fun r => (r.1, r.2.1, r.2.2.1, r.2.2.2 + k)) := by
  simp only [parseBody]
  generalize sd p = sp
  obtain ⟨z, n⟩ := sp
  simp only
  by_cases hn : n ≠ 0
  · simp only [hn, ne_eq, not_false_eq_true, ite_true]
    by_cases hs : isSign (cur (p.drop n)) = true
    · simp only [hs, ite_true]
      generalize sd (p.drop n) = sp2
      obtain ⟨y, m⟩ := sp2
      simp only
      by_cases hm : m ≠ 0
      · simp only [hm, ne_eq, not_false_eq_true, ite_true]
        by_cases hj : isJ (cur ((p.drop n).drop m)) = true
        · simp only [hj, Bool.not_true, Bool.false_eq_true, ite_false, Option.map_some,
            Option.some.injEq, Prod.mk.injEq, true_and]
          omega
        · have e := Bool.eq_false_iff.2 hj
          simp only [e, Bool.not_false, ite_true, Option.map_none]
      · simp only [hm, ne_eq, not_false_eq_true, ite_false, not_true_eq_false]
        by_cases hj : isJ (cur (p.drop n).tail) = true
        · simp only [hj, Bool.not_true, Bool.false_eq_true, ite_false, Option.map_some,
            Option.some.injEq, Prod.mk.injEq, true_and]
          omega
        · have e := Bool.eq_false_iff.2 hj
          simp only [e, Bool.not_false, ite_true, Option.map_none]
    · simp only [hs, Bool.false_eq_true, ite_false]
      by_cases hj : isJ (cur (p.drop n)) = true
      · simp only [hj, ite_true, Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
        omega
      · have e := Bool.eq_false_iff.2 hj
        simp only [e, Bool.false_eq_true, ite_false, Option.map_some, Option.some.injEq,
          Prod.mk.injEq, true_and]
        omega
  · simp only [hn, ne_eq, not_false_eq_true, ite_false, not_true_eq_false]
    by_cases hs : isSign (cur p) = true
    · simp only [hs, ite_true]
      by_cases hj : isJ (cur p.tail) = true
      · simp only [hj, Bool.not_true, Bool.false_eq_true, ite_false, Option.map_some,
          Option.some.injEq, Prod.mk.injEq, true_and]
        omega
      · have e := Bool.eq_false_iff.2 hj
        simp only [e, Bool.not_false, ite_true, Option.map_none]
    · simp only [hs, Bool.false_eq_true, ite_false]
      by_cases hj : isJ (cur p) = true
      · simp only [hj, Bool.not_true, Bool.false_eq_true, ite_false, Option.map_some,
          Option.some.injEq, Prod.mk.injEq, true_and]
        omega
      · have e := Bool.eq_false_iff.2 hj
        simp only [e, Bool.not_false, ite_true, Option.map_none]

end shift

/-- `complex_from_string_inner`, started at offset `k`: a run of leading whitespace
is the same as starting further along. -/
def innerAt {R : Type} [CDouble R] (sd : Strtod R) (s : List Nat) (k len : Nat) : Py (Cx R) :=
  let (p, i) := skipSpace s k
  let (p, i, got_bracket) : List Nat × Nat × Bool :=
    if cur p == chLParen then
      let (p', i') := skipSpace p.tail (i + 1)
      (p', i', true)
    else (p, i, false)
  match parseBody sd p i with
  | none => .error malformed
  | some (x, y, p, i) =>
    let (p, i) := skipSpace p i
    let tail : Option (List Nat × Nat) :=
      if got_bracket then
        if cur p != chRParen then none
        else some (skipSpace p.tail (i + 1))
      else some (p, i)
    match tail with
    | none => .error malformed
    | some (_, i) =>
      if i != len then .error malformed
      else .ok ⟨x, y⟩

theorem innerAt_shift {R : Type} [CDouble R] (sd : Strtod R) (s : List Nat) (k len : Nat) :
    innerAt sd s k (len + k) = innerAt sd s 0 len := by
  simp only [innerAt]
  have h0 := skipSpace_shift s 0 k
  rw [Nat.zero_add] at h0
  rw [h0]
  generalize skipSpace s 0 = sk
  obtain ⟨p, i⟩ := sk
  simp only
  by_cases hb : (cur p == chLParen) = true
  · simp only [hb, ite_true]
    have h1 := skipSpace_shift p.tail (i + 1) k
    rw [show i + k + 1 = i + 1 + k by omega, h1]
    generalize skipSpace p.tail (i + 1) = sk2
    obtain ⟨p₂, i₂⟩ := sk2
    simp only
    rw [parseBody_shift]
    cases parseBody sd p₂ i₂ with
    | none => rfl
    | some r =>
      obtain ⟨x, y, q, j⟩ := r
      simp only [Option.map_some]
      rw [skipSpace_shift]
      generalize skipSpace q j = sk3
      obtain ⟨q₂, j₂⟩ := sk3
      simp only
      by_cases hc : (cur q₂ != chRParen) = true
      · simp [hc]
      · simp only [hc, Bool.false_eq_true, ite_false]
        rw [show j₂ + k + 1 = j₂ + 1 + k by omega, skipSpace_shift]
        simp
  · simp only [hb, Bool.false_eq_true, ite_false]
    rw [parseBody_shift]
    cases parseBody sd p i with
    | none => rfl
    | some r =>
      obtain ⟨x, y, q, j⟩ := r
      simp only [Option.map_some]
      rw [skipSpace_shift]
      generalize skipSpace q j = sk3
      obtain ⟨q₂, j₂⟩ := sk3
      simp

/-- Leading C whitespace changes nothing, for every string and every `strtod`. It
is the `Py_ISSPACE` set: `\x1c`-`\x1f`, which `str.isspace` accepts, are not in it,
and on that `complex` and `float` agree. -/
def LeadingWhitespace : Prop :=
  ∀ (R : Type) [CDouble R] (sd : Strtod R) (ws s : List Nat) (len : Nat),
    (∀ c ∈ ws, isSpaceC c = true) →
    complex_from_string_inner sd (ws ++ s) (len + ws.length) =
      complex_from_string_inner sd s len

theorem leadingWhitespace_proven : LeadingWhitespace := by
  intro R _ sd ws s len hw
  have h1 : complex_from_string_inner sd (ws ++ s) (len + ws.length) =
      innerAt sd (ws ++ s) 0 (len + ws.length) := rfl
  have h2 : complex_from_string_inner sd s len = innerAt sd s 0 len := rfl
  have h3 : innerAt sd (ws ++ s) 0 (len + ws.length) = innerAt sd s ws.length (len + ws.length) := by
    simp only [innerAt]
    rw [skipSpace_append_spaces ws s hw 0, Nat.zero_add]
  rw [h1, h2, h3, innerAt_shift]

/-! ## The documented forms -/

/-- The forms of the comment on lines 950-969, read off `parseBody`: `f` is a
`<float>`, `g` a `<signed-float>`, and `z`, `y` what `strtod` makes of them. With
`f` read up to the text that follows it, each form gives the parts the comment
names. Here `rest` is whatever follows the form. -/
def ParseForms : Prop :=
  ∀ (R : Type) [CDouble R] (sd : Strtod R) (i : Nat),
    -- <float> and <float>j, with `n` characters of float
    (∀ (p : List Nat) (z : R) (n : Nat), sd p = (z, n) → n ≠ 0 →
      isSign (cur (p.drop n)) = false →
      (isJ (cur (p.drop n)) = true →
        parseBody sd p i = some (CDouble.zero, z, (p.drop n).tail, i + n + 1)) ∧
      (isJ (cur (p.drop n)) = false →
        parseBody sd p i = some (z, CDouble.zero, p.drop n, i + n))) ∧
    -- <float><signed-float>j
    (∀ (p : List Nat) (z y : R) (n m : Nat), sd p = (z, n) → n ≠ 0 →
      isSign (cur (p.drop n)) = true → sd (p.drop n) = (y, m) → m ≠ 0 →
      isJ (cur ((p.drop n).drop m)) = true →
      parseBody sd p i = some (z, y, ((p.drop n).drop m).tail, i + n + m + 1)) ∧
    -- <float><sign>j
    (∀ (p : List Nat) (z y : R) (n : Nat), sd p = (z, n) → n ≠ 0 →
      isSign (cur (p.drop n)) = true → sd (p.drop n) = (y, 0) →
      isJ (cur (p.drop n).tail) = true →
      parseBody sd p i =
        some (z, signOne (cur (p.drop n)), (p.drop n).tail.tail, i + n + 1 + 1)) ∧
    -- <sign>j and j
    (∀ (p : List Nat) (z : R), sd p = (z, 0) → isSign (cur p) = true →
      isJ (cur p.tail) = true →
      parseBody sd p i = some (CDouble.zero, signOne (cur p), p.tail.tail, i + 1 + 1)) ∧
    (∀ (p : List Nat) (z : R), sd p = (z, 0) → isSign (cur p) = false → isJ (cur p) = true →
      parseBody sd p i = some (CDouble.zero, CDouble.one, p.tail, i + 1))

theorem parseForms_proven : ParseForms := by
  intro R _ sd i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p z n h1 h2 h3
    constructor
    · intro h4; simp [parseBody, h1, h2, h3, h4]
    · intro h4; simp [parseBody, h1, h2, h3, h4]
  · intro p z y n m h1 h2 h3 h4 h5 h6
    rw [List.drop_drop] at h6
    simp [parseBody, h1, h2, h3, h4, h5, h6]
  · intro p z y n h1 h2 h3 h4 h5
    rw [List.tail_drop] at h5
    simp [parseBody, h1, h2, h3, h4, h5]
  · intro p z h1 h2 h3
    simp [parseBody, h1, h2, h3]
  · intro p z h1 h2 h3
    simp [parseBody, h1, h2, h3]

end PyLean.LongObj.Cplx
