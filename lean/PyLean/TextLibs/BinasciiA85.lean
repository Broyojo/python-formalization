import PyLean.TextLibs.BinasciiB85e

/-!
`binascii.a2b_ascii85` and `binascii.b2a_ascii85` over every option: `foldspaces`, `adobe`,
`ignorechars`, `canonical`, `pad` and `wrapcol`. No message of this decoder gives a position, so taking
the ignored characters out changes nothing at all.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

theorem a85_stop (fs k : Bool) (ig : List Nat) (g : Nat) (len : Int) (o : List Nat) (h : len ≤ 0) :
    a2bA85Loop fs k ig (g + 1) [] len { out := o } = .ok { out := o } := by
  have : (decide (len ≤ 0) && ((0 : Nat) == 0)) = true := by simp; omega
  simp only [a2bA85Loop]
  rw [if_pos (by simpa using this)]

theorem flushA85_pos (k : Bool) (len : Int) (st st2 : Dec85) (h : flushA85 k len st = .ok st2) : st2.pos = 0 := by
  simp only [flushA85] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> simp_all <;>
    (cases h; rfl)

theorem a85_padphase (fs k : Bool) (ig ig' : List Nat) :
    ∀ (n : Nat) (st : Dec85) (len : Int) (f f' : Nat), st.pos < 5 → (st.pos = 0 ∨ 4 - st.pos ≤ n) → len ≤ 0 →
      n + 2 ≤ f → n + 2 ≤ f' → a2bA85Loop fs k ig f [] len st = a2bA85Loop fs k ig' f' [] len st := by
  intro n
  induction n with
  | zero =>
    intro st len f f' hp hn hl hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    by_cases h0 : st.pos = 0
    · have : (decide (len ≤ 0) && st.pos == 0) = true := by simp [h0]; omega
      simp only [a2bA85Loop, this, if_true]
    · have h4 : st.pos = 4 := by omega
      have : (decide (len ≤ 0) && st.pos == 0) = false := by simp [h0]
      obtain ⟨g2, rfl⟩ : ∃ g2, g = g2 + 1 := ⟨g - 1, by omega⟩
      obtain ⟨g2', rfl⟩ : ∃ g2, g' = g2 + 1 := ⟨g' - 1, by omega⟩
      rw [a2bA85Loop, a2bA85Loop]
      simp only [this, Bool.false_eq_true, if_false, show (84 : Nat) < 85 by decide, if_true]
      split
      · rfl
      · simp only [h4, show (4 + 1 != 5) = false by decide, Bool.false_eq_true, if_false]
        cases hfl : flushA85 k len { st with left := st.left * 85 + 84, pos := 4 + 1 } with
        | error e => rfl
        | ok st2 =>
          simp only
          have hst2 : st2.pos = 0 := flushA85_pos _ _ _ _ hfl
          have : (decide (len - 1 ≤ 0) && st2.pos == 0) = true := by simp [hst2]; omega
          simp only [a2bA85Loop, this, if_true]
  | succ n ih =>
    intro st len f f' hp hn hl hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    by_cases h0 : st.pos = 0
    · have : (decide (len ≤ 0) && st.pos == 0) = true := by simp [h0]; omega
      simp only [a2bA85Loop, this, if_true]
    · have : (decide (len ≤ 0) && st.pos == 0) = false := by simp [h0]
      simp only [a2bA85Loop, this, Bool.false_eq_true, if_false, show (84 : Nat) < 85 by decide, if_true]
      split
      · rfl
      · by_cases h5 : st.pos + 1 = 5
        · simp only [h5, show (5 != 5) = false by decide, Bool.false_eq_true, if_false]
          cases hfl : flushA85 k len { st with left := st.left * 85 + 84, pos := 5 } with
          | error e => rfl
          | ok st2 =>
            simp only
            have hst2 : st2.pos = 0 := flushA85_pos _ _ _ _ hfl
            exact ih st2 (len - 1) g g' (by omega) (.inl hst2) (by omega) (by omega) (by omega)
        · have : (st.pos + 1 != 5) = true := by simpa using h5
          simp only [this, if_true]
          exact ih _ _ _ _ (by simp only; omega) (by simp only; omega) (by omega) (by omega) (by omega)

theorem flushA85_full (k : Bool) (len len' : Int) (st : Dec85) (h : 1 ≤ len) (h' : 1 ≤ len') :
    flushA85 k len st = flushA85 k len' st := by
  have c1 : ¬ len < 1 := by omega
  have c2 : ¬ len' < 1 := by omega
  simp only [flushA85, c1, c2, if_false]

/-- What the loop reads of the input: it passes over the non-digits that are not `z` (or `y` with
`foldspaces`) and that `ignorechars` names. -/
def keepA (fs : Bool) (ig : List Nat) (x : Nat) : Bool :=
  !(decide (revT a85Alpha none x ≥ 85) && !((x == 121 && fs) || x == 122) && ig.contains x)

theorem a85_filter (fs k : Bool) (ig : List Nat) :
    ∀ (s : List Nat) (st : Dec85) (f f' : Nat), st.pos < 5 → s.length + 6 ≤ f → (s.filter (keepA fs ig)).length + 6 ≤ f' →
      a2bA85Loop fs k ig f s s.length st = a2bA85Loop fs k [] f' (s.filter (keepA fs ig)) (s.filter (keepA fs ig)).length st := by
  intro s
  induction s with
  | nil =>
    intro st f f' hp hf hf'
    exact a85_padphase fs k ig [] 4 st 0 f f' hp (by omega) (by omega) (by simp at hf; omega) (by simp at hf'; omega)
  | cons x xs ih =>
    intro st f f' hp hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hg : xs.length + 6 ≤ g := by simp at hf; omega
    have hst1 : (decide (((x :: xs).length : Int) ≤ 0) && st.pos == 0) = false := by simp; omega
    have e1 : ((x :: xs).length : Int) - 1 = xs.length := by simp
    by_cases hi : (decide (revT a85Alpha none x ≥ 85) && !((x == 121 && fs) || x == 122) && ig.contains x) = true
    · have hk : keepA fs ig x = false := by simp only [keepA, hi, Bool.not_true]
      rw [List.filter_cons_of_neg (by simp [hk])] at hf' ⊢
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hi
      obtain ⟨⟨h1, h2⟩, h3⟩ := hi
      have hp5 : (st.pos != 5) = true := by simp; omega
      simp only [a2bA85Loop, hst1, Bool.false_eq_true, if_false, Option.getD_some, Nat.not_lt.mpr h1, h2, h3,
        Bool.not_true, hp5, if_true, e1]
      exact ih _ _ _ hp hg hf'
    · have hk : keepA fs ig x = true := by
        cases h : (decide (revT a85Alpha none x ≥ 85) && !((x == 121 && fs) || x == 122) && ig.contains x)
        · simp only [keepA, h, Bool.not_false]
        · exact absurd h hi
      rw [List.filter_cons_of_pos hk] at hf' ⊢
      obtain ⟨g', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by simp at hf'; omega⟩
      have hg' : (xs.filter (keepA fs ig)).length + 6 ≤ g' := by simp at hf'; omega
      have hst2 : (decide (((x :: xs.filter (keepA fs ig)).length : Int) ≤ 0) && st.pos == 0) = false := by simp; omega
      have e2 : ((x :: xs.filter (keepA fs ig)).length : Int) - 1 = (xs.filter (keepA fs ig)).length := by simp
      have hfl : ∀ st' : Dec85, flushA85 k ((x :: xs).length : Int) st' =
          flushA85 k ((x :: xs.filter (keepA fs ig)).length : Int) st' :=
        fun st' => flushA85_full k _ _ st' (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
      -- the step after a group is complete, the same on both sides
      have hnext : ∀ st1 : Dec85, st1.pos = 5 →
          (match flushA85 k ((x :: xs).length : Int) st1 with
            | .error e => (.error e : Py Dec85)
            | .ok st => a2bA85Loop fs k ig g xs (((x :: xs).length : Int) - 1) st) =
          (match flushA85 k ((x :: xs.filter (keepA fs ig)).length : Int) st1 with
            | .error e => (.error e : Py Dec85)
            | .ok st => a2bA85Loop fs k [] g' (xs.filter (keepA fs ig))
                (((x :: xs.filter (keepA fs ig)).length : Int) - 1) st) := by
        intro st1 _
        rw [hfl]
        cases hF : flushA85 k ((x :: xs.filter (keepA fs ig)).length : Int) st1 with
        | error e => rfl
        | ok st2 =>
          simp only [e1, e2]
          exact ih st2 g g' (by rw [flushA85_pos _ _ _ _ hF]; decide) hg hg'
      by_cases hd : revT a85Alpha none x < 85
      · simp only [a2bA85Loop, hst1, hst2, Bool.false_eq_true, if_false, Option.getD_some, hd, if_true]
        by_cases hov : (st.pos == 4 && decide (st.left * 85 + revT a85Alpha none x ≥ 2 ^ 32)) = true
        · rw [if_pos hov, if_pos hov]
        · rw [if_neg hov, if_neg hov]
          by_cases h5 : st.pos + 1 = 5
          · have : (st.pos + 1 != 5) = false := by simpa using h5
            simp only [this, Bool.false_eq_true, if_false]
            exact hnext _ (by simp only; omega)
          · have : (st.pos + 1 != 5) = true := by simpa using h5
            simp only [this, if_true, e1, e2]
            exact ih _ _ _ (by simp only; omega) hg hg'
      · by_cases hz : ((x == 121 && fs) || x == 122) = true
        · simp only [a2bA85Loop, hst1, hst2, Bool.false_eq_true, if_false, Option.getD_some, hd, hz, if_true]
          by_cases hp0 : (st.pos != 0) = true
          · rw [if_pos hp0, if_pos hp0]
          · rw [if_neg hp0, if_neg hp0]
            simp only [show (5 != 5) = false by decide, Bool.false_eq_true, if_false]
            exact hnext _ rfl
        · have hc : ig.contains x = false := by
            cases hc : ig.contains x
            · rfl
            · exfalso
              apply hi
              have hz' : ((x == 121 && fs) || x == 122) = false := by simpa using hz
              simp only [decide_eq_true (Nat.not_lt.mp hd), hz', hc, Bool.not_false, Bool.and_self]
          have hz' : ((x == 121 && fs) || x == 122) = false := by simpa using hz
          simp only [a2bA85Loop, hst1, hst2, Bool.false_eq_true, if_false, Option.getD_some, hd, hz', hc,
            Bool.not_false, if_true, show [].contains x = false from rfl]

end PyLean.TextLibs.Binascii
