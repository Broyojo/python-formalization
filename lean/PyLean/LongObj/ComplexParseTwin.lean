import PyLean.LongObj.ComplexParseProps

/-!
Two properties that tie the parser to code outside it: `complex` and `float` read
the same strings, and `repr` of a complex reads back as itself.
-/

namespace PyLean.LongObj.Cplx

open CDouble

/-! ## `float` and `complex` -/

theorem skipSpace_ge : ∀ (s : List Nat) (i : Nat), i ≤ (skipSpace s i).2 := by
  intro s
  induction s with
  | nil => intro i; exact Nat.le_refl _
  | cons c t ih =>
    intro i
    simp only [skipSpace]
    split
    · exact Nat.le_trans (Nat.le_succ i) (ih (i + 1))
    · exact Nat.le_refl _

theorem skipSpace_drop : ∀ (s : List Nat) (i : Nat),
    (skipSpace s i).1 = s.drop ((skipSpace s i).2 - i) := by
  intro s
  induction s with
  | nil => intro i; simp [skipSpace]
  | cons c t ih =>
    intro i
    simp only [skipSpace]
    split
    · have h := ih (i + 1)
      have hge := skipSpace_ge t (i + 1)
      rw [h]
      have : (skipSpace t (i + 1)).2 - i = ((skipSpace t (i + 1)).2 - (i + 1)) + 1 := by omega
      rw [this, List.drop_succ_cons]
    · simp

theorem skipSpace_not_space : ∀ (s : List Nat) (i : Nat) (c : Nat) (t : List Nat),
    (skipSpace s i).1 = c :: t → isSpaceC c = false := by
  intro s
  induction s with
  | nil => intro i c t h; simp [skipSpace] at h
  | cons x r ih =>
    intro i c t h
    simp only [skipSpace] at h
    split at h
    · exact ih _ _ _ h
    · next hc =>
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact Bool.eq_false_iff.2 hc

/-- `floatLead` is `skipSpace` as long as it stays inside the string. -/
theorem floatLead_eq (n : Nat) : ∀ (s : List Nat) (i : Nat), i + s.length ≤ n →
    floatLead n s i = ((skipSpace s i).2, (skipSpace s i).1) := by
  intro s
  induction s with
  | nil => intro i _; rfl
  | cons c t ih =>
    intro i hi
    simp only [List.length_cons] at hi
    have hlt : i < n := by omega
    simp only [floatLead, skipSpace, hlt, decide_true, Bool.true_and]
    split
    · exact ih (i + 1) (by omega)
    · rfl

theorem floatTrail_spec (s : List Nat) (i : Nat) : ∀ (fuel last : Nat), i + 1 ≤ last →
    i + 1 ≤ floatTrail s i fuel last ∧ floatTrail s i fuel last ≤ last ∧
      ∀ k, floatTrail s i fuel last ≤ k → k < last → isSpaceC (s.getD k 0) = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro last h
    exact ⟨h, Nat.le_refl _, fun k h1 h2 => by simp only [floatTrail] at h1; omega⟩
  | succ fuel ih =>
    intro last h
    simp only [floatTrail]
    split
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hc1, hc2⟩ := hc
      obtain ⟨a, b, d⟩ := ih (last - 1) (by omega)
      refine ⟨a, by omega, ?_⟩
      intro k h1 h2
      by_cases hk : k = last - 1
      · rw [hk]; exact hc2
      · exact d k h1 (by omega)
    · exact ⟨h, Nat.le_refl _, fun k h1 h2 => by omega⟩

/-- A list of whitespace is consumed to the end. -/
theorem skipSpace_all (q : List Nat) (hq : ∀ c ∈ q, isSpaceC c = true) (j : Nat) :
    skipSpace q j = ([], j + q.length) := by
  have := skipSpace_append_spaces q [] hq j
  simpa [skipSpace] using this

theorem cur_of_spaces (q : List Nat) (hq : ∀ c ∈ q, isSpaceC c = true) :
    isSign (cur q) = false ∧ isJ (cur q) = false := by
  cases q with
  | nil => exact ⟨by decide, by decide⟩
  | cons c t =>
    have hc := hq c (by simp)
    simp only [cur, List.headD_cons]
    simp only [isSpaceC, Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with (((((hc | hc) | hc) | hc) | hc) | hc) <;> subst hc <;>
      exact ⟨by decide, by decide⟩

section twin

variable {R : Type} [CDouble R] {sd : Strtod R}

/-- The core of the twin: what `float_from_string_inner` accepts,
`complex_from_string_inner` accepts as the real part. -/
theorem float_inner_ok (hs : StrtodSpec sd) (t : List Nat) (n : Nat) (r : String) (x : R)
    (hn : n = t.length) (h : float_from_string_inner sd t n r = .ok x) :
    complex_from_string_inner sd t n = .ok ⟨x, CDouble.zero⟩ := by
  subst hn
  simp only [float_from_string_inner] at h
  rw [floatLead_eq t.length t 0 (by omega)] at h
  simp only at h
  generalize hsk : skipSpace t 0 = sk at h
  obtain ⟨p, i⟩ := sk
  simp only at h
  by_cases hi : (i == t.length) = true
  · simp [hi] at h
  have hi' : i ≠ t.length := by simpa using hi
  simp only [hi, Bool.false_eq_true, ite_false] at h
  have hdrop : p = t.drop i := by
    have := skipSpace_drop t 0
    rw [hsk] at this
    simpa using this
  have hile : i ≤ t.length := by
    by_cases hc : i ≤ t.length
    · exact hc
    · exfalso
      have hpe : p = [] := by rw [hdrop]; exact List.drop_of_length_le (by omega)
      have hmono : ∀ (s : List Nat) (a : Nat), (skipSpace s a).2 ≤ a + s.length := by
        intro s
        induction s with
        | nil => intro a; exact Nat.le_add_right _ _
        | cons c w ih =>
          intro a
          simp only [skipSpace, List.length_cons]
          split
          · have := ih (a + 1); omega
          · omega
      have := hmono t 0
      rw [hsk] at this
      simp at this
      omega
  have hilt : i < t.length := by omega
  obtain ⟨hl1, hl2, hl3⟩ := floatTrail_spec t i t.length t.length (by omega)
  generalize hlast : floatTrail t i t.length t.length = last at h hl1 hl2 hl3
  generalize hsp : sd p = sp at h
  obtain ⟨y, m⟩ := sp
  simp only at h
  by_cases hm : (i + m != last) = true
  · simp [hm] at h
  have hm' : i + m = last := by simpa using hm
  simp only [hm, Bool.false_eq_true, ite_false, Except.ok.injEq] at h
  subst h
  have hm0 : m ≠ 0 := by omega
  -- `p` does not start with a parenthesis
  have hparen : (cur p == chLParen) = false := by
    cases hb : (cur p == chLParen) with
    | false => rfl
    | true =>
      exfalso
      have he : cur p = chLParen := by simpa using hb
      cases hp : p with
      | nil => rw [hp] at he; simp [cur, chLParen] at he
      | cons c w =>
        rw [hp] at he
        simp only [cur, List.headD_cons] at he
        subst he
        have hc : sd (([] : List Nat) ++ chLParen :: w) = sd [] := hs.cut [] chLParen w (by decide)
        have hle := hs.le_length []
        have : (sd p).2 = (sd ([] : List Nat)).2 := by rw [hp]; exact congrArg Prod.snd hc
        rw [hsp] at this
        simp only at this
        simp at hle
        omega
  -- what follows the number is whitespace
  have hq : ∀ c ∈ t.drop last, isSpaceC c = true := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hc
    have hk' : last + k < t.length := by
      simp only [List.length_drop] at hk
      omega
    have := hl3 (last + k) (by omega) hk'
    simpa [List.getD_eq_getElem?_getD, hk'] using this
  have hdn : p.drop m = t.drop last := by
    rw [hdrop, List.drop_drop, hm']
  obtain ⟨hns, hnj⟩ := cur_of_spaces _ hq
  have hbody : parseBody sd p i = some (y, CDouble.zero, t.drop last, last) := by
    have := ((parseForms_proven R sd i).1 p y m hsp hm0 (by rw [hdn]; exact hns)).2
      (by rw [hdn]; exact hnj)
    rwa [hdn, hm'] at this
  simp only [complex_from_string_inner, hsk, hparen, Bool.false_eq_true, ite_false, hbody]
  rw [skipSpace_all _ hq]
  have hend : last + (t.drop last).length = t.length := by
    simp only [List.length_drop]
    omega
  simp [hend]
  omega

end twin

/-- Every string `float()` accepts, `complex()` accepts as the same real number, for
every `strtod`. So the extra forms of `complex` only add strings. -/
def FloatStringsAreComplexStrings : Prop :=
  ∀ (R : Type) [CDouble R] (sd : Strtod R), StrtodSpec sd →
    ∀ (db : UniDB) (v : List Nat) (r r' : String) (x : R),
      float_from_str db sd v r = .ok x → complex_from_str db sd v r' = .ok ⟨x, CDouble.zero⟩

theorem floatStringsAreComplexStrings_proven : FloatStringsAreComplexStrings := by
  intro R _ sd hs db v r r' x h
  simp only [float_from_str, complex_from_str, withUnderscores] at h ⊢
  generalize transformDecimalAndSpace db v = T at h ⊢
  by_cases hu : hasUnderscore T = true
  · simp only [hu, Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
    cases hsc : underscoreScan T 0 [] 0 with
    | none => simp [hsc] at h
    | some res =>
      obtain ⟨o, p, n⟩ := res
      simp only [hsc] at h ⊢
      by_cases hp : (p == chUnderscore) = true
      · simp [hp] at h
      · simp only [hp, Bool.false_eq_true, ite_false] at h ⊢
        by_cases hn : (n != T.length) = true
        · simp [hn] at h
        · simp only [hn, Bool.false_eq_true, ite_false] at h ⊢
          exact float_inner_ok hs _ _ _ _ (by simp) h
  · have hu' : hasUnderscore T = false := by simpa using hu
    simp only [hu', Bool.not_false, ite_true] at h ⊢
    exact float_inner_ok hs _ _ _ _ rfl h

/-! ## `repr` -/

section repr

variable {R : Type} [CDouble R]

/-- The code points of the text `ds` writes. -/
def dsText (ds : R → Bool → String) (x : R) (b : Bool) : List Nat :=
  (ds x b).toList.map Char.toNat

/-- What is assumed of `PyOS_double_to_string` and `strtod` together. The text is
ASCII, starts with neither whitespace nor `(`, holds no `_`, and with the sign flag
starts with a sign; `strtod` reads it back as `canon x`, stopping exactly at its end
when a sign, a `j`, or the end of the string follows. `canon` is the identity
except on NaN, whose sign `repr` drops. -/
structure ReprSpec (ds : R → Bool → String) (sd : Strtod R) (canon : R → R) : Prop where
  head : ∀ x b, ∃ c t, dsText ds x b = c :: t ∧ isSpaceC c = false ∧ c ≠ chLParen
  ascii : ∀ x b, ∀ c ∈ dsText ds x b, c < 128 ∧ c ≠ chUnderscore
  signed : ∀ x, isSign (cur (dsText ds x true)) = true
  read : ∀ x b r, (r = [] ∨ isSign (cur r) = true ∨ isJ (cur r) = true) →
    sd (dsText ds x b ++ r) = (canon x, (dsText ds x b).length)

end repr

/-- `complex(repr(z))` gives `z` back, up to `canon`: the sign of a NaN. A `+0` real
part is left out of the text and comes back as `+0`. The hypotheses are `ReprSpec`,
and that `0.0` is what `complex_from_string_inner` initialises `x` to. -/
def ReprRoundTrip : Prop :=
  ∀ (R : Type) [CDouble R] (ds : R → Bool → String) (sd : Strtod R) (canon : R → R)
    (db : UniDB) (v : Cx R) (r : String), ReprSpec ds sd canon →
    complex_from_str db sd ((complex_repr ds v).toList.map Char.toNat) r =
      .ok (if (v.real ==. CDouble.zero &&
              CDouble.copysign CDouble.one v.real ==. CDouble.one) = true
           then ⟨CDouble.zero, canon v.imag⟩ else ⟨canon v.real, canon v.imag⟩)

section reprProof

variable {R : Type} [CDouble R] {ds : R → Bool → String} {sd : Strtod R} {canon : R → R}

theorem dsText_ne_length (h : ReprSpec ds sd canon) (x : R) (b : Bool) :
    (dsText ds x b).length ≠ 0 := by
  obtain ⟨c, t, e, _⟩ := h.head x b
  rw [e]
  simp

theorem hasUnderscore_of (s : List Nat) (h : ∀ c ∈ s, c ≠ chUnderscore) :
    hasUnderscore s = false := by
  simp only [hasUnderscore]
  have : ¬ (chUnderscore ∈ s.takeWhile (· != 0)) := fun hm =>
    h _ ((List.takeWhile_sublist _).subset hm) rfl
  simpa using this

theorem repr_prefix (ds : R → Bool → String) (db : UniDB) (sd : Strtod R) (r : String)
    (s : List Nat) (ha : ∀ c ∈ s, c < 128 ∧ c ≠ chUnderscore) :
    complex_from_str db sd s r = complex_from_string_inner sd s s.length := by
  have hall : s.all (· < 128) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact fun c hc => (ha c hc).1
  have hT : transformDecimalAndSpace db s = s := by
    simp [transformDecimalAndSpace, hall]
  simp only [complex_from_str, hT, withUnderscores]
  rw [hasUnderscore_of s (fun c hc => (ha c hc).2)]
  simp

end reprProof

theorem reprRoundTrip_proven : ReprRoundTrip := by
  intro R _ ds sd canon db v r h
  by_cases hz : (v.real ==. CDouble.zero &&
      CDouble.copysign CDouble.one v.real ==. CDouble.one) = true
  · -- `<float>j`
    have hs : (complex_repr ds v).toList.map Char.toNat = dsText ds v.imag false ++ [chJ] := by
      simp only [complex_repr, hz, ite_true]
      simp [dsText, chJ]
    rw [hs, if_pos hz]
    obtain ⟨c, t, ht, hsp, hne⟩ := h.head v.imag false
    have hascii : ∀ x ∈ dsText ds v.imag false ++ [chJ], x < 128 ∧ x ≠ chUnderscore := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h.ascii _ _ _ hx
      · simp only [List.mem_singleton] at hx
        subst hx
        decide
    rw [repr_prefix ds db sd r _ hascii]
    have hL := dsText_ne_length h v.imag false
    have hread := h.read v.imag false [chJ] (Or.inr (Or.inr (by decide)))
    have hdrop : (dsText ds v.imag false ++ [chJ]).drop (dsText ds v.imag false).length = [chJ] := by
      simp
    have hbody : parseBody sd (dsText ds v.imag false ++ [chJ]) 0 =
        some (CDouble.zero, canon v.imag, [], (dsText ds v.imag false).length + 1) := by
      have h1 : isSign (cur [chJ]) = false := by decide
      have h2 : isJ (cur [chJ]) = true := by decide
      have := ((parseForms_proven R sd 0).1 _ _ _ hread hL (by rw [hdrop]; exact h1)).1
        (by rw [hdrop]; exact h2)
      rw [hdrop] at this
      simpa using this
    have hsk : skipSpace (dsText ds v.imag false ++ [chJ]) 0 = (dsText ds v.imag false ++ [chJ], 0) := by
      rw [ht]
      simp [skipSpace, hsp]
    have hcur : (cur (dsText ds v.imag false ++ [chJ]) == chLParen) = false := by
      rw [ht]
      simpa [cur] using hne
    simp only [complex_from_string_inner, hsk, hcur, Bool.false_eq_true, ite_false, hbody]
    simp [skipSpace]
  · -- `(<float><signed-float>j)`
    have hb : (v.real ==. CDouble.zero &&
        CDouble.copysign CDouble.one v.real ==. CDouble.one) = false := by simpa using hz
    have hs : (complex_repr ds v).toList.map Char.toNat =
        chLParen :: (dsText ds v.real false ++ (dsText ds v.imag true ++ [chJ, chRParen])) := by
      simp only [complex_repr, hb, Bool.false_eq_true, ite_false]
      simp [dsText, chJ, chRParen, chLParen]
    rw [hs, if_neg hz]
    obtain ⟨A, hA⟩ : ∃ A, dsText ds v.real false = A := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, dsText ds v.imag true = B := ⟨_, rfl⟩
    rw [hA, hB]
    have hasc₁ : ∀ x ∈ A, x < 128 ∧ x ≠ chUnderscore := by
      rw [← hA]; exact h.ascii _ _
    have hasc₂ : ∀ x ∈ B, x < 128 ∧ x ≠ chUnderscore := by
      rw [← hB]; exact h.ascii _ _
    have hascii : ∀ x ∈ chLParen :: (A ++ (B ++ [chJ, chRParen])),
        x < 128 ∧ x ≠ chUnderscore := by
      intro x hx
      rcases List.mem_cons.1 hx with hx | hx
      · subst hx; decide
      · rcases List.mem_append.1 hx with hx | hx
        · exact hasc₁ x hx
        · rcases List.mem_append.1 hx with hx | hx
          · exact hasc₂ x hx
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl <;> decide
    rw [repr_prefix ds db sd r _ hascii]
    obtain ⟨c, t, ht, hsp, hne⟩ := h.head v.real false
    obtain ⟨c', t', ht', _, _⟩ := h.head v.imag true
    rw [hA] at ht
    rw [hB] at ht'
    have hsgn : isSign (cur B) = true := by rw [← hB]; exact h.signed _
    have hcurB : isSign (cur (B ++ [chJ, chRParen])) = true := by
      rw [ht'] at hsgn ⊢
      simpa [cur] using hsgn
    have hread₁ := h.read v.real false (B ++ [chJ, chRParen]) (Or.inr (Or.inl hcurB))
    have hread₂ := h.read v.imag true [chJ, chRParen] (Or.inr (Or.inr (by decide)))
    rw [hA] at hread₁
    rw [hB] at hread₂
    have hLA : A.length ≠ 0 := by rw [← hA]; exact dsText_ne_length h _ _
    have hLB : B.length ≠ 0 := by rw [← hB]; exact dsText_ne_length h _ _
    have hdrop₁ : (A ++ (B ++ [chJ, chRParen])).drop A.length = B ++ [chJ, chRParen] := by simp
    have hdrop₂ : (B ++ [chJ, chRParen]).drop B.length = [chJ, chRParen] := by simp
    have hbody : parseBody sd (A ++ (B ++ [chJ, chRParen])) 1 =
        some (canon v.real, canon v.imag, [chRParen], 1 + A.length + B.length + 1) := by
      have h2 : isJ (cur [chJ, chRParen]) = true := by decide
      have := (parseForms_proven R sd 1).2.1 (A ++ (B ++ [chJ, chRParen])) (canon v.real)
        (canon v.imag) A.length B.length hread₁ hLA (by rw [hdrop₁]; exact hcurB)
        (by rw [hdrop₁]; exact hread₂) hLB (by rw [hdrop₁, hdrop₂]; exact h2)
      rw [hdrop₁, hdrop₂] at this
      simpa using this
    have hsk₁ : skipSpace (chLParen :: (A ++ (B ++ [chJ, chRParen]))) 0 =
        (chLParen :: (A ++ (B ++ [chJ, chRParen])), 0) := by
      have : isSpaceC chLParen = false := by decide
      simp [skipSpace, this]
    have hsk₂ : skipSpace (A ++ (B ++ [chJ, chRParen])) (0 + 1) =
        (A ++ (B ++ [chJ, chRParen]), 1) := by
      rw [ht]
      simp [skipSpace, hsp]
    have hsk₃ : skipSpace [chRParen] (1 + A.length + B.length + 1) =
        ([chRParen], 1 + A.length + B.length + 1) := by
      have : isSpaceC chRParen = false := by decide
      simp [skipSpace, this]
    simp only [complex_from_string_inner, hsk₁]
    have hc₁ : (cur (chLParen :: (A ++ (B ++ [chJ, chRParen]))) == chLParen) = true := by
      simp [cur]
    simp only [hc₁, ite_true, List.tail_cons, hsk₂, hbody, hsk₃]
    have hc₂ : (cur [chRParen] != chRParen) = false := by decide
    simp only [hc₂, Bool.false_eq_true, ite_false, List.tail_cons]
    have hlen : (chLParen :: (A ++ (B ++ [chJ, chRParen]))).length =
        1 + A.length + B.length + 1 + 1 := by
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega
    simp [skipSpace, hlen]

end PyLean.LongObj.Cplx
