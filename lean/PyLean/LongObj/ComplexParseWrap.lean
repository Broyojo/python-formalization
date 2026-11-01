import PyLean.LongObj.ComplexParseTwin

/-!
What may surround a `complex` string: trailing whitespace, and parentheses. With
`LeadingWhitespace` this is the sentence in the docs, "The string can optionally be
surrounded by whitespaces and the round parentheses".

Each theorem starts from a string the parser accepts and that has no parenthesis of
its own, because `((1))` is rejected.
-/

namespace PyLean.LongObj.Cplx

open CDouble

theorem skipSpace_append : ∀ (s r : List Nat) (i : Nat),
    skipSpace (s ++ r) i = skipSpace ((skipSpace s i).1 ++ r) (skipSpace s i).2 := by
  intro s
  induction s with
  | nil => intro r i; rfl
  | cons c t ih =>
    intro r i
    simp only [List.cons_append, skipSpace]
    split
    · exact ih r (i + 1)
    · simp only [List.cons_append, skipSpace]
      next hc =>
      simp only [hc, Bool.false_eq_true, ite_false]

theorem skipSpace_len : ∀ (s : List Nat) (i : Nat),
    (skipSpace s i).2 + (skipSpace s i).1.length = i + s.length := by
  intro s
  induction s with
  | nil => intro i; rfl
  | cons c t ih =>
    intro i
    simp only [skipSpace, List.length_cons]
    split
    · have := ih (i + 1)
      omega
    · simp only [List.length_cons]

theorem cur_sign_append (P r : List Nat) (c : Nat) (h : isSign c = false) :
    isSign (cur (P ++ c :: r)) = isSign (cur P) := by
  cases P with
  | nil => simp only [List.nil_append, cur, List.headD_cons, h]; rfl
  | cons x t => rfl

theorem cur_j_append (P r : List Nat) (c : Nat) (h : isJ c = false) :
    isJ (cur (P ++ c :: r)) = isJ (cur P) := by
  cases P with
  | nil => simp only [List.nil_append, cur, List.headD_cons, h]; rfl
  | cons x t => rfl

theorem tail_append_of_sign (P r : List Nat) (h : isSign (cur P) = true) :
    (P ++ r).tail = P.tail ++ r := by
  cases P with
  | nil => exact absurd h (by decide)
  | cons x t => rfl

theorem tail_append_of_j (P r : List Nat) (h : isJ (cur P) = true) :
    (P ++ r).tail = P.tail ++ r := by
  cases P with
  | nil => exact absurd h (by decide)
  | cons x t => rfl

section

variable {R : Type} [CDouble R] {sd : Strtod R}

/-- Text after a stop character does not reach `parseBody`: it only stays on the end
of what is left over. -/
theorem parseBody_append (hs : StrtodSpec sd) (p r : List Nat) (c : Nat)
    (hstop : isStop c = true) (hsg : isSign c = false) (hj : isJ c = false) (i : Nat) :
    parseBody sd (p ++ c :: r) i =
      (parseBody sd p i).map (fun e => (e.1, e.2.1, e.2.2.1 ++ c :: r, e.2.2.2)) := by
  have hcut := hs.cut p c r hstop
  have hle := hs.le_length p
  simp only [parseBody]
  rw [hcut]
  generalize hsp : sd p = sp at hle
  obtain ⟨z, n⟩ := sp
  simp only at hle ⊢
  by_cases hn : n ≠ 0
  · simp only [hn, ne_eq, not_false_eq_true, ite_true]
    rw [List.drop_append_of_le_length hle]
    generalize hP : p.drop n = P
    rw [cur_sign_append P r c hsg, cur_j_append P r c hj]
    by_cases hS : isSign (cur P) = true
    · simp only [hS, ite_true]
      have hP' : (P ++ c :: r).length ≥ 0 := Nat.zero_le _
      rw [hs.cut P c r hstop]
      generalize hsp2 : sd P = sp2
      obtain ⟨y, m⟩ := sp2
      have hle2 := hs.le_length P
      rw [hsp2] at hle2
      simp only at hle2 ⊢
      by_cases hm : m ≠ 0
      · simp only [hm, ne_eq, not_false_eq_true, ite_true]
        rw [List.drop_append_of_le_length hle2, cur_j_append _ r c hj]
        by_cases hJ : isJ (cur (P.drop m)) = true
        · simp only [hJ, Bool.not_true, Bool.false_eq_true, ite_false, Option.map_some]
          rw [tail_append_of_j _ _ hJ]
        · have e := Bool.eq_false_iff.2 hJ
          simp only [e, Bool.not_false, ite_true, Option.map_none]
      · simp only [hm, ne_eq, not_false_eq_true, ite_false, not_true_eq_false]
        have ht := tail_append_of_sign P (c :: r) hS
        rw [ht]
        have hscur : signOne (R := R) (cur (P ++ c :: r)) = signOne (cur P) := by
          cases P with
          | nil => exact absurd hS (by decide)
          | cons x t => rfl
        rw [hscur]
        by_cases hPT : P.tail = []
        · rw [hPT]
          simp only [List.nil_append]
          have h1 : isJ (cur (c :: r)) = false := by simpa [cur] using hj
          have h2 : isJ (cur ([] : List Nat)) = false := by decide
          simp only [h1, h2, Bool.not_false, ite_true, Option.map_none]
        · rw [cur_j_append _ r c hj]
          by_cases hJ : isJ (cur P.tail) = true
          · simp only [hJ, Bool.not_true, Bool.false_eq_true, ite_false, Option.map_some]
            rw [tail_append_of_j _ _ hJ]
          · have e := Bool.eq_false_iff.2 hJ
            simp only [e, Bool.not_false, ite_true, Option.map_none]
    · have hSf := Bool.eq_false_iff.2 hS
      simp only [hSf, Bool.false_eq_true, ite_false]
      by_cases hJ : isJ (cur P) = true
      · simp only [hJ, ite_true, Option.map_some]
        rw [tail_append_of_j _ _ hJ]
      · have e := Bool.eq_false_iff.2 hJ
        simp only [e, Bool.false_eq_true, ite_false, Option.map_some]
  · simp only [hn, ne_eq, not_false_eq_true, ite_false, not_true_eq_false]
    rw [cur_sign_append p r c hsg]
    by_cases hS : isSign (cur p) = true
    · simp only [hS, ite_true]
      have ht := tail_append_of_sign p (c :: r) hS
      rw [ht]
      have hscur : signOne (R := R) (cur (p ++ c :: r)) = signOne (cur p) := by
        cases p with
        | nil => exact absurd hS (by decide)
        | cons x t => rfl
      rw [hscur, cur_j_append _ r c hj]
      by_cases hJ : isJ (cur p.tail) = true
      · simp only [hJ, Bool.not_true, Bool.false_eq_true, ite_false, Option.map_some]
        rw [tail_append_of_j _ _ hJ]
      · have e := Bool.eq_false_iff.2 hJ
        simp only [e, Bool.not_false, ite_true, Option.map_none]
    · have hSf := Bool.eq_false_iff.2 hS
      simp only [hSf, Bool.false_eq_true, ite_false]
      rw [cur_j_append p r c hj]
      by_cases hJ : isJ (cur p) = true
      · simp only [hJ, Bool.not_true, Bool.false_eq_true, ite_false, Option.map_some]
        rw [tail_append_of_j _ _ hJ]
      · have e := Bool.eq_false_iff.2 hJ
        simp only [e, Bool.not_false, ite_true, Option.map_none]

theorem len_tail_of_sign {P : List Nat} (h : isSign (cur P) = true) :
    P.tail.length + 1 = P.length := by
  cases P with
  | nil => exact absurd h (by decide)
  | cons x t => simp

theorem len_tail_of_j {P : List Nat} (h : isJ (cur P) = true) :
    P.tail.length + 1 = P.length := by
  cases P with
  | nil => exact absurd h (by decide)
  | cons x t => simp

/-- `parseBody` only moves characters from what is left to what is consumed. -/
theorem parseBody_len (hs : StrtodSpec sd) (p : List Nat) (i : Nat) {x y : R} {q : List Nat}
    {j : Nat} (h : parseBody sd p i = some (x, y, q, j)) : j + q.length = i + p.length := by
  have hle := hs.le_length p
  simp only [parseBody] at h
  generalize hsp : sd p = sp at h hle
  obtain ⟨z, n⟩ := sp
  simp only at h hle
  by_cases hn : n ≠ 0
  · simp only [hn, ne_eq, not_false_eq_true, ite_true] at h
    have hd : (p.drop n).length = p.length - n := by simp
    by_cases hS : isSign (cur (p.drop n)) = true
    · simp only [hS, ite_true] at h
      generalize hsp2 : sd (p.drop n) = sp2 at h
      obtain ⟨y₀, m⟩ := sp2
      have hle2 := hs.le_length (p.drop n)
      rw [hsp2] at hle2
      simp only at h hle2
      by_cases hm : m ≠ 0
      · simp only [hm, ne_eq, not_false_eq_true, ite_true] at h
        by_cases hJ : isJ (cur ((p.drop n).drop m)) = true
        · simp only [hJ, Bool.not_true, Bool.false_eq_true, ite_false, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨_, _, rfl, rfl⟩ := h
          have := len_tail_of_j hJ
          simp only [List.length_drop] at this hd hle2 ⊢
          omega
        · have e := Bool.eq_false_iff.2 hJ
          simp only [e, Bool.not_false, ite_true] at h
          cases h
      · simp only [hm, ne_eq, not_false_eq_true, ite_false, not_true_eq_false] at h
        by_cases hJ : isJ (cur (p.drop n).tail) = true
        · simp only [hJ, Bool.not_true, Bool.false_eq_true, ite_false, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨_, _, rfl, rfl⟩ := h
          have h1 := len_tail_of_j hJ
          have h2 := len_tail_of_sign hS
          simp only [List.length_drop] at h1 h2
          omega
        · have e := Bool.eq_false_iff.2 hJ
          simp only [e, Bool.not_false, ite_true] at h
          cases h
    · have hSf := Bool.eq_false_iff.2 hS
      simp only [hSf, Bool.false_eq_true, ite_false] at h
      by_cases hJ : isJ (cur (p.drop n)) = true
      · simp only [hJ, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl, rfl⟩ := h
        have := len_tail_of_j hJ
        simp only [List.length_drop] at this ⊢
        omega
      · have e := Bool.eq_false_iff.2 hJ
        simp only [e, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl, rfl⟩ := h
        simp only [List.length_drop]
        omega
  · simp only [hn, ne_eq, not_false_eq_true, ite_false, not_true_eq_false] at h
    by_cases hS : isSign (cur p) = true
    · simp only [hS, ite_true] at h
      by_cases hJ : isJ (cur p.tail) = true
      · simp only [hJ, Bool.not_true, Bool.false_eq_true, ite_false, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨_, _, rfl, rfl⟩ := h
        have h1 := len_tail_of_j hJ
        have h2 := len_tail_of_sign hS
        omega
      · have e := Bool.eq_false_iff.2 hJ
        simp only [e, Bool.not_false, ite_true] at h
        cases h
    · have hSf := Bool.eq_false_iff.2 hS
      simp only [hSf, Bool.false_eq_true, ite_false] at h
      by_cases hJ : isJ (cur p) = true
      · simp only [hJ, Bool.not_true, Bool.false_eq_true, ite_false, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨_, _, rfl, rfl⟩ := h
        have := len_tail_of_j hJ
        omega
      · have e := Bool.eq_false_iff.2 hJ
        simp only [e, Bool.not_false, ite_true] at h
        cases h

/-- What an accepted string with no parenthesis of its own looks like to the parser. -/
theorem accepted_shape (hs : StrtodSpec sd) (s : List Nat) (c : Cx R)
    (h : complex_from_string_inner sd s s.length = .ok c)
    (hp : (cur (skipSpace s 0).1 == chLParen) = false) :
    ∃ q j, parseBody sd (skipSpace s 0).1 (skipSpace s 0).2 = some (c.real, c.imag, q, j) ∧
      skipSpace q j = ([], s.length) := by
  simp only [complex_from_string_inner] at h
  generalize hsk : skipSpace s 0 = sk at h hp
  obtain ⟨p, i⟩ := sk
  simp only at h hp ⊢
  simp only [hp, Bool.false_eq_true, ite_false] at h
  cases hpb : parseBody sd p i with
  | none => simp [hpb] at h
  | some res =>
    obtain ⟨x, y, q, j⟩ := res
    simp only [hpb] at h
    generalize hsk2 : skipSpace q j = sk2 at h
    obtain ⟨q₂, j₂⟩ := sk2
    simp only at h
    by_cases he : (j₂ != s.length) = true
    · simp [he] at h
    · simp only [he, Bool.false_eq_true, ite_false, Except.ok.injEq] at h
      subst h
      refine ⟨q, j, rfl, ?_⟩
      have hj : j₂ = s.length := by simpa using he
      have l1 := skipSpace_len s 0
      rw [hsk] at l1
      simp only at l1
      have l2 := parseBody_len hs p i hpb
      have l3 := skipSpace_len q j
      rw [hsk2] at l3
      simp only at l3
      have hq : q₂ = [] := List.length_eq_zero_iff.1 (by omega)
      rw [hsk2, hq, hj]

end

/-- Trailing whitespace, and parentheses around the string with whitespace after them,
leave an accepted string's value alone. The string must not have a parenthesis of its
own: `((1))` is rejected. `ws` is `Py_ISSPACE` whitespace. -/
def ParseSurroundings : Prop :=
  ∀ (R : Type) [CDouble R] (sd : Strtod R), StrtodSpec sd →
    ∀ (s ws : List Nat) (c : Cx R), (∀ x ∈ ws, isSpaceC x = true) →
      complex_from_string_inner sd s s.length = .ok c →
      (cur (skipSpace s 0).1 == chLParen) = false →
      complex_from_string_inner sd (s ++ ws) (s ++ ws).length = .ok c ∧
      complex_from_string_inner sd (chLParen :: (s ++ chRParen :: ws))
        (chLParen :: (s ++ chRParen :: ws)).length = .ok c

theorem parseSurroundings_proven : ParseSurroundings := by
  intro R _ sd hs s ws c hw h hp
  obtain ⟨q, j, hb, hq⟩ := accepted_shape hs s c h hp
  generalize hsk : skipSpace s 0 = sk at hb hp
  obtain ⟨p, i⟩ := sk
  simp only at hb hp
  -- the accepted text starts with a character that is not whitespace
  have hhead : ∃ a t, p = a :: t ∧ isSpaceC a = false := by
    cases hP : p with
    | nil =>
      exfalso
      rw [hP] at hb
      have hz : (sd ([] : List Nat)).2 = 0 := by simpa using hs.le_length []
      simp only [parseBody] at hb
      generalize sd ([] : List Nat) = sp at hz hb
      obtain ⟨z, n⟩ := sp
      simp only at hz
      subst hz
      have h1 : isSign (cur ([] : List Nat)) = false := by decide
      have h2 : isJ (cur ([] : List Nat)) = false := by decide
      simp [h1, h2] at hb
    | cons a t =>
      refine ⟨a, t, rfl, ?_⟩
      have : (skipSpace s 0).1 = a :: t := by rw [hsk, hP]
      exact skipSpace_not_space s 0 a t this
  obtain ⟨a, t, hpe, ha⟩ := hhead
  have hskipP : ∀ r : List Nat, skipSpace (p ++ r) i = (p ++ r, i) := by
    intro r
    rw [hpe]
    simp [skipSpace, ha]
  have hsp : ∀ r : List Nat, skipSpace (s ++ r) 0 = (p ++ r, i) := by
    intro r
    rw [skipSpace_append, hsk]
    exact hskipP r
  have hcurP : ∀ r : List Nat, (cur (p ++ r) == chLParen) = false := by
    intro r
    rw [hpe] at hp ⊢
    simpa [cur] using hp
  constructor
  · -- trailing whitespace
    cases ws with
    | nil => simpa using h
    | cons w rest =>
      have hsw := hw w (by simp)
      have hsg : isSign w = false := (cur_of_spaces [w] (by simpa using hsw)).1
      have hjw : isJ w = false := (cur_of_spaces [w] (by simpa using hsw)).2
      have hstop : isStop w = true := by simp [isStop, hsw]
      have hbody := parseBody_append hs p rest w hstop hsg hjw i
      rw [hb] at hbody
      simp only [Option.map_some] at hbody
      have hskq : skipSpace (q ++ w :: rest) j = ([], s.length + (w :: rest).length) := by
        rw [skipSpace_append, hq]
        exact skipSpace_all _ hw _
      simp only [complex_from_string_inner, hsp, hcurP, Bool.false_eq_true, ite_false, hbody, hskq]
      simp
  · -- parentheses
    have hopen : isSpaceC chLParen = false := by decide
    have hclose : isStop chRParen = true := by decide
    have hbody := parseBody_append hs p ws chRParen hclose (by decide) (by decide) (i + 1)
    have hshift := parseBody_shift sd p i 1
    rw [hb] at hshift
    simp only [Option.map_some] at hshift
    rw [hshift] at hbody
    simp only [Option.map_some] at hbody
    have hsk₁ : skipSpace (chLParen :: (s ++ chRParen :: ws)) 0 =
        (chLParen :: (s ++ chRParen :: ws), 0) := by
      simp [skipSpace, hopen]
    have hsk₂ : skipSpace (s ++ chRParen :: ws) (0 + 1) = (p ++ chRParen :: ws, i + 1) := by
      have := skipSpace_shift (s ++ chRParen :: ws) 0 1
      rw [hsp] at this
      exact this
    have hc₁ : (cur (chLParen :: (s ++ chRParen :: ws)) == chLParen) = true := by
      simp [cur]
    have hsk₃ : skipSpace (q ++ chRParen :: ws) (j + 1) = (chRParen :: ws, s.length + 1) := by
      rw [skipSpace_append]
      have := skipSpace_shift q j 1
      rw [hq] at this
      rw [this]
      simp [skipSpace, show isSpaceC chRParen = false by decide]
    have hc₂ : (cur (chRParen :: ws) != chRParen) = false := by
      simp [cur]
    have hsk₄ : skipSpace ws (s.length + 1 + 1) = ([], s.length + 1 + 1 + ws.length) :=
      skipSpace_all ws hw _
    simp only [complex_from_string_inner, hsk₁, hc₁, ite_true, List.tail_cons, hsk₂, hbody, hsk₃,
      hc₂, Bool.false_eq_true, ite_false, hsk₄]
    have hlen : (chLParen :: (s ++ chRParen :: ws)).length = s.length + 1 + 1 + ws.length := by
      simp only [List.length_cons, List.length_append]
      omega
    simp [hlen]

end PyLean.LongObj.Cplx
