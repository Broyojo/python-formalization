import PyLean.StrSearch.Model

/-!
Basic facts about the search primitives: `findL`/`rfindL` return the least
and greatest occurrence, occurrences in a window are occurrences in the
string, and `ADJUST_INDICES` lands in `[0, len]`.
-/

set_option linter.deprecated false

namespace PyLean.StrSearch

open PyLean

/-- `p` occurs in `s` at index `i`: `s[i:i+len(p)] == p` with the whole match inside `s`. -/
def Occ (s p : Seq) (i : Nat) : Prop := i + p.length ≤ s.length ∧ (s.drop i).take p.length = p

theorem isPrefixOf_eq_true_iff {p s : Seq} : p.isPrefixOf s = true ↔ p.length ≤ s.length ∧ s.take p.length = p := by
  rw [List.isPrefixOf_iff_prefix]
  constructor
  · intro h; exact ⟨h.length_le, (List.prefix_iff_eq_take.mp h).symm⟩
  · intro ⟨_, h⟩; exact List.prefix_iff_eq_take.mpr h.symm

theorem occ_zero {p s : Seq} : Occ s p 0 ↔ p.isPrefixOf s = true := by
  rw [isPrefixOf_eq_true_iff]; simp [Occ]

theorem occ_cons_succ {p : Seq} {c : Nat} {cs : Seq} {j : Nat} : Occ (c :: cs) p (j + 1) ↔ Occ cs p j := by
  simp only [Occ, List.length_cons, List.drop_succ_cons]; constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

theorem occ_nil {p : Seq} {j : Nat} : Occ [] p j ↔ j = 0 ∧ p = [] := by
  simp only [Occ, List.length_nil, List.drop_nil, List.take_nil]; constructor
  · intro ⟨h1, h2⟩; exact ⟨by omega, h2.symm⟩
  · intro ⟨h1, h2⟩; subst h1 h2; simp

theorem isPrefixOf_nil_iff {p : Seq} : p.isPrefixOf [] = true ↔ p = [] := by
  cases p <;> simp [List.isPrefixOf]

/-- `findL` returns the least occurrence. -/
theorem findL_correct (p s : Seq) :
    match findL p s with
    | some i => Occ s p i ∧ ∀ j < i, ¬ Occ s p j
    | none => ∀ j, ¬ Occ s p j := by
  induction s with
  | nil =>
    by_cases h : p.isPrefixOf [] = true
    · simp only [findL, h, ↓reduceIte]; exact ⟨occ_zero.mpr h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · simp only [findL, h, ↓reduceIte, Bool.false_eq_true]; intro j hj; rw [occ_nil] at hj; exact h (isPrefixOf_nil_iff.mpr hj.2)
  | cons c cs ih =>
    by_cases h : p.isPrefixOf (c :: cs) = true
    · simp only [findL, h, ↓reduceIte]; exact ⟨occ_zero.mpr h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · simp only [findL, h, ↓reduceIte, Bool.false_eq_true]
      cases hf : findL p cs with
      | none =>
        rw [hf] at ih
        intro j hj
        cases j with
        | zero => exact h (occ_zero.mp hj)
        | succ j => exact ih j (occ_cons_succ.mp hj)
      | some i =>
        rw [hf] at ih
        refine ⟨occ_cons_succ.mpr ih.1, fun j hj hocc => ?_⟩
        have hj' : j < i + 1 := hj
        cases j with
        | zero => exact h (occ_zero.mp hocc)
        | succ j => exact ih.2 j (by omega) (occ_cons_succ.mp hocc)

/-- `rfindL` returns the greatest occurrence. -/
theorem rfindL_correct (p s : Seq) :
    match rfindL p s with
    | some i => Occ s p i ∧ ∀ j, i < j → ¬ Occ s p j
    | none => ∀ j, ¬ Occ s p j := by
  induction s with
  | nil =>
    by_cases h : p.isPrefixOf [] = true
    · simp only [rfindL, h, ↓reduceIte]
      refine ⟨occ_zero.mpr h, fun j hj hocc => ?_⟩
      rw [occ_nil] at hocc; omega
    · simp only [rfindL, h, ↓reduceIte, Bool.false_eq_true]; intro j hj; rw [occ_nil] at hj; exact h (isPrefixOf_nil_iff.mpr hj.2)
  | cons c cs ih =>
    rw [rfindL]
    cases hf : rfindL p cs with
    | some i =>
      rw [hf] at ih
      refine ⟨occ_cons_succ.mpr ih.1, fun j hj hocc => ?_⟩
      cases j with
      | zero => omega
      | succ j => exact ih.2 j (by omega) (occ_cons_succ.mp hocc)
    | none =>
      rw [hf] at ih
      by_cases h : p.isPrefixOf (c :: cs) = true
      · simp only [h, ↓reduceIte]
        refine ⟨occ_zero.mpr h, fun j hj hocc => ?_⟩
        cases j with
        | zero => omega
        | succ j => exact ih j (occ_cons_succ.mp hocc)
      · simp only [h, ↓reduceIte, Bool.false_eq_true]
        intro j hocc
        cases j with
        | zero => exact h (occ_zero.mp hocc)
        | succ j => exact ih j (occ_cons_succ.mp hocc)

theorem findL_eq_none {p s : Seq} : findL p s = none ↔ ∀ j, ¬ Occ s p j := by
  have h := findL_correct p s
  cases hf : findL p s with
  | none => rw [hf] at h; simpa using h
  | some i =>
    rw [hf] at h
    exact ⟨(fun h' => nomatch h'), (fun h' => absurd h.1 (h' i))⟩

theorem findL_eq_some {p s : Seq} {i : Nat} :
    findL p s = some i ↔ Occ s p i ∧ ∀ j < i, ¬ Occ s p j := by
  have h := findL_correct p s
  cases hf : findL p s with
  | none => rw [hf] at h; simp only [reduceCtorEq, false_iff, not_and]; intro ho; exact absurd ho (h i)
  | some k =>
    rw [hf] at h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl; exact h
    · intro ⟨ho, hl⟩
      rcases Nat.lt_trichotomy k i with hki | hki | hki
      · exact absurd h.1 (hl k hki)
      · exact hki
      · exact absurd ho (h.2 i hki)

theorem rfindL_eq_none {p s : Seq} : rfindL p s = none ↔ ∀ j, ¬ Occ s p j := by
  have h := rfindL_correct p s
  cases hf : rfindL p s with
  | none => rw [hf] at h; simpa using h
  | some i =>
    rw [hf] at h
    exact ⟨(fun h' => nomatch h'), (fun h' => absurd h.1 (h' i))⟩

theorem rfindL_eq_some {p s : Seq} {i : Nat} :
    rfindL p s = some i ↔ Occ s p i ∧ ∀ j, i < j → ¬ Occ s p j := by
  have h := rfindL_correct p s
  cases hf : rfindL p s with
  | none => rw [hf] at h; simp only [reduceCtorEq, false_iff, not_and]; intro ho; exact absurd ho (h i)
  | some k =>
    rw [hf] at h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl; exact h
    · intro ⟨ho, hl⟩
      rcases Nat.lt_trichotomy k i with hki | hki | hki
      · exact absurd ho (h.2 i hki)
      · exact hki
      · exact absurd h.1 (hl k hki)

/-- `findL` is determined by the occurrence predicate. -/
theorem findL_congr {p s p' s' : Seq} (h : ∀ j, Occ s p j ↔ Occ s' p' j) : findL p s = findL p' s' := by
  cases hf : findL p' s' with
  | none => rw [findL_eq_none] at hf ⊢; intro j hj; exact hf j ((h j).mp hj)
  | some i =>
    rw [findL_eq_some] at hf ⊢
    exact ⟨(h i).mpr hf.1, fun j hj ho => hf.2 j hj ((h j).mp ho)⟩

theorem rfindL_congr {p s p' s' : Seq} (h : ∀ j, Occ s p j ↔ Occ s' p' j) : rfindL p s = rfindL p' s' := by
  cases hf : rfindL p' s' with
  | none => rw [rfindL_eq_none] at hf ⊢; intro j hj; exact hf j ((h j).mp hj)
  | some i =>
    rw [rfindL_eq_some] at hf ⊢
    exact ⟨(h i).mpr hf.1, fun j hj ho => hf.2 j hj ((h j).mp ho)⟩

/-- An occurrence in `window s a n` is an occurrence in `s` that ends by `a + n`. -/
theorem occ_window {s p : Seq} {a n i : Nat} (ha : a ≤ s.length) :
    Occ ((s.drop a).take n) p i ↔ Occ s p (a + i) ∧ i + p.length ≤ n := by
  simp only [Occ, List.length_take, List.length_drop, List.drop_take, List.drop_drop, List.take_take]
  constructor
  · intro ⟨h1, h2⟩
    have hm : min p.length (n - i) = p.length := by omega
    rw [hm] at h2
    exact ⟨⟨by omega, h2⟩, by omega⟩
  · intro ⟨⟨h1, h2⟩, h3⟩
    have hm : min p.length (n - i) = p.length := by omega
    rw [hm]
    exact ⟨by omega, h2⟩

/-- Elements of an occurrence are elements of the string. -/
theorem Occ.mem {s p : Seq} {i : Nat} (h : Occ s p i) {x : Nat} (hx : x ∈ p) : x ∈ s := by
  rw [← h.2] at hx
  exact List.mem_of_mem_drop (List.mem_of_mem_take hx)

theorem not_occ_of_long {s p : Seq} (h : s.length < p.length) (i : Nat) : ¬ Occ s p i := by
  intro ho; have := ho.1; omega

/-! ## ADJUST_INDICES -/

theorem adjust_fst_nonneg (st en len : Int) : 0 ≤ (adjustIndices st en len).1 := by
  unfold adjustIndices; simp only; split <;> (try split) <;> omega

theorem adjust_snd_nonneg (st en len : Int) (h : 0 ≤ len) : 0 ≤ (adjustIndices st en len).2 := by
  unfold adjustIndices; simp only; split <;> (try split) <;> (try split) <;> omega

theorem adjust_snd_le (st en len : Int) (h : 0 ≤ len) : (adjustIndices st en len).2 ≤ len := by
  unfold adjustIndices; simp only; split <;> (try split) <;> (try split) <;> omega

/-- `window s a n` for `0 ≤ a`, `0 ≤ n`. -/
theorem window_eq (s : Seq) (a n : Int) : window s a n = (s.drop a.toNat).take n.toNat := rfl

/-! ## kinds -/

theorem kindOf_one {s : Seq} (h : kindOf s = 1) : ∀ x ∈ s, x < 256 := by
  unfold kindOf at h
  split at h
  · next h1 => intro x hx; simpa using List.all_eq_true.mp h1 x hx
  · split at h <;> simp at h

theorem kindOf_le_two {s : Seq} (h : kindOf s ≤ 2) : ∀ x ∈ s, x < 65536 := by
  unfold kindOf at h
  split at h
  · next h1 => intro x hx; have := List.all_eq_true.mp h1 x hx; simp at this; omega
  · split at h
    · next h1 => intro x hx; simpa using List.all_eq_true.mp h1 x hx
    · simp at h

theorem kindOf_cases (s : Seq) : kindOf s = 1 ∨ kindOf s = 2 ∨ kindOf s = 4 := by
  unfold kindOf; split <;> (try split) <;> simp

theorem kindOf_of_all {s : Seq} (h : ∀ x ∈ s, x < 256) : kindOf s = 1 := by
  have h' : (s.all fun x => decide (x < 256)) = true := List.all_eq_true.mpr (by simpa using h)
  unfold kindOf; simp only [h', ↓reduceIte]

/-- A string with wider characters than `s` does not occur in `s`. -/
theorem not_occ_of_kind {s p : Seq} (h : kindOf s < kindOf p) (i : Nat) : ¬ Occ s p i := by
  intro ho
  rcases kindOf_cases s with hs | hs | hs
  · have hb := kindOf_one hs
    have : kindOf p = 1 := kindOf_of_all fun x hx => hb x (ho.mem hx)
    omega
  · have hb := kindOf_le_two (by omega : kindOf s ≤ 2)
    have : kindOf p ≤ 2 := by
      unfold kindOf; split
      · simp
      · have h' : (p.all fun x => decide (x < 65536)) = true :=
          List.all_eq_true.mpr (by simpa using fun x hx => hb x (ho.mem hx))
        simp only [h', ↓reduceIte]; omega
    omega
  · rcases kindOf_cases p with hp | hp | hp <;> omega

/-! ## splitN -/

theorem findL_some_le {p s : Seq} {i : Nat} (h : findL p s = some i) : i + p.length ≤ s.length :=
  findL_le h

theorem length_drop_match {p s : Seq} {i : Nat} (hp : p ≠ []) (h : findL p s = some i) :
    (s.drop (i + p.length)).length + p.length ≤ s.length ∧ (s.drop (i + p.length)).length < s.length := by
  have := findL_le h
  have : p.length ≥ 1 := List.length_pos_iff.mpr hp
  simp; omega

/-- `splitN` stops by itself after at most `len / len(p)` splits. -/
theorem splitN_sat' {p : Seq} (hp : p ≠ []) :
    ∀ k k' t, t.length / p.length + 1 ≤ k → t.length / p.length + 1 ≤ k' →
      splitN p k t = splitN p k' t := by
  have hpl : p.length ≥ 1 := List.length_pos_iff.mpr hp
  intro k
  induction k with
  | zero => intro k' t hk; generalize t.length / p.length = q at hk; omega
  | succ k ih =>
    intro k' t hk hk'
    obtain ⟨k', rfl⟩ : ∃ m, k' = m + 1 := ⟨k' - 1, by generalize t.length / p.length = q at hk'; omega⟩
    simp only [splitN]
    cases hf : findL p t with
    | none => rfl
    | some i =>
      simp only
      have hl := findL_le hf
      have hd : (t.drop (i + p.length)).length = t.length - i - p.length := by simp; omega
      congr 1
      have h1 : (t.length - i - p.length) / p.length ≤ (t.length - p.length) / p.length :=
        Nat.div_le_div_right (by omega)
      have h2 : t.length / p.length = (t.length - p.length) / p.length + 1 :=
        Nat.div_eq_sub_div (by omega) (by omega)
      apply ih
      · rw [hd]; generalize (t.length - i - p.length) / p.length = q1 at *
        generalize (t.length - p.length) / p.length = q2 at *; omega
      · rw [hd]; generalize (t.length - i - p.length) / p.length = q1 at *
        generalize (t.length - p.length) / p.length = q2 at *; omega

theorem splitN_sat {p : Seq} (hp : p ≠ []) (k : Nat) (t : Seq) (hk : t.length / p.length + 1 ≤ k) :
    splitN p k t = splitN p (t.length + 1) t :=
  splitN_sat' hp k _ t hk (by have := Nat.div_le_self t.length p.length; omega)

/-- All splits. -/
def splitAll (p s : Seq) : List Seq := splitN p (s.length + 1) s

theorem countAll_eq (p s : Seq) : countAll p s = (splitAll p s).length - 1 := rfl

theorem splitAll_none {p s : Seq} (h : findL p s = none) : splitAll p s = [s] := by
  simp [splitAll, splitN, h]

theorem splitAll_some {p s : Seq} {i : Nat} (hp : p ≠ []) (h : findL p s = some i) :
    splitAll p s = s.take i :: splitAll p (s.drop (i + p.length)) := by
  have hl := findL_le h
  have hpl : p.length ≥ 1 := List.length_pos_iff.mpr hp
  simp only [splitAll, splitN, h]
  congr 1
  apply splitN_sat hp
  have : (s.drop (i + p.length)).length / p.length ≤ (s.drop (i + p.length)).length := Nat.div_le_self _ _
  simp only [List.length_drop] at this ⊢
  generalize (s.length - (i + p.length)) / p.length = q at this; omega

theorem splitN_ne_nil (p : Seq) (k : Nat) (s : Seq) : splitN p k s ≠ [] := by
  cases k <;> simp only [splitN] <;> (try split) <;> simp

theorem countAll_none {p s : Seq} (h : findL p s = none) : countAll p s = 0 := by
  rw [countAll_eq, splitAll_none h]; rfl

theorem countAll_some {p s : Seq} {i : Nat} (hp : p ≠ []) (h : findL p s = some i) :
    countAll p s = 1 + countAll p (s.drop (i + p.length)) := by
  rw [countAll_eq, countAll_eq, splitAll_some hp h]
  have := splitN_ne_nil p ((s.drop (i + p.length)).length + 1) (s.drop (i + p.length))
  simp only [List.length_cons, splitAll]
  cases h' : splitN p ((s.drop (i + p.length)).length + 1) (s.drop (i + p.length)) with
  | nil => exact absurd h' this
  | cons _ _ => simp; omega

theorem countAll_le {p : Seq} (hp : p ≠ []) : ∀ s : Seq, countAll p s ≤ s.length := by
  intro s
  induction s using (measure List.length).wf.induction with
  | _ s ih =>
    cases hf : findL p s with
    | none => rw [countAll_none hf]; omega
    | some i =>
      rw [countAll_some hp hf]
      have := length_drop_match hp hf
      have := ih _ this.2
      omega

end PyLean.StrSearch
