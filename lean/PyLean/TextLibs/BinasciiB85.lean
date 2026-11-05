import PyLean.TextLibs.BinasciiCacheProps

/-!
`binascii.a2b_base85` and `binascii.b2a_base85` over every option: `alphabet`, `ignorechars`,
`canonical`, `pad` and `wrapcol`.

The decoder's messages give positions in the input, so taking ignored characters out changes the
message of a failure but not whether it fails or what it returns; the statements say that much
(`Except.toOption`).
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

theorem b85_stop (t : Nat → Nat) (ig : Option (List Nat)) (k : Bool) (N g : Nat) (len : Int) (o : List Nat)
    (h : len ≤ 0) : a2bB85Loop t ig k N (g + 1) [] len { out := o } = .ok { out := o } := by
  have : (decide (len ≤ 0) && ((0 : Nat) == 0)) = true := by simp; omega
  simp only [a2bB85Loop]
  rw [if_pos (by simpa using this)]

/-- The flush of a group, `Modules/binascii.c:1484-1520`, as one step. -/
theorem b85_flush_eq (t : Nat → Nat) (ig ig' : Option (List Nat)) (k : Bool) (N N' g g' : Nat) (len : Int)
    (st : St85) (s s' : List Nat) (hlen : len ≤ 1) (hs : s = []) (hs' : s' = []) :
    (if (if len < 1 then (3 + len).toNat else 4) = 0 then (Except.error (err "Incomplete Base85 group") : Py St85)
      else if (k && decide ((if len < 1 then (3 + len).toNat else 4) < 4) &&
          nonCanon st.left (if len < 1 then (3 + len).toNat else 4)) = true then .error (err "Non-zero padding bits")
      else a2bB85Loop t ig k N (g + 1) s (len - 1) { out := st.out ++ word4 st.left (if len < 1 then (3 + len).toNat else 4) }).toOption =
    (if (if len < 1 then (3 + len).toNat else 4) = 0 then (Except.error (err "Incomplete Base85 group") : Py St85)
      else if (k && decide ((if len < 1 then (3 + len).toNat else 4) < 4) &&
          nonCanon st.left (if len < 1 then (3 + len).toNat else 4)) = true then .error (err "Non-zero padding bits")
      else a2bB85Loop t ig' k N' (g' + 1) s' (len - 1) { out := st.out ++ word4 st.left (if len < 1 then (3 + len).toNat else 4) }).toOption := by
  subst hs hs'
  rw [b85_stop t ig k N g _ _ (by omega), b85_stop t ig' k N' g' _ _ (by omega)]

/-! ### The padding digits do not depend on the input that is gone -/

theorem b85_padphase (t : Nat → Nat) (ig ig' : Option (List Nat)) (k : Bool) (N N' : Nat) :
    ∀ (n : Nat) (st : St85) (len : Int) (f f' : Nat), st.pos < 5 → (st.pos = 0 ∨ 4 - st.pos ≤ n) → len ≤ 0 →
      n + 2 ≤ f → n + 2 ≤ f' →
      (a2bB85Loop t ig k N f [] len st).toOption = (a2bB85Loop t ig' k N' f' [] len st).toOption := by
  intro n
  induction n with
  | zero =>
    intro st len f f' hp hn hl hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    by_cases h0 : st.pos = 0
    · have : (decide (len ≤ 0) && st.pos == 0) = true := by simp [h0]; omega
      simp only [a2bB85Loop, this, if_true]
    · have h4 : st.pos = 4 := by omega
      have : (decide (len ≤ 0) && st.pos == 0) = false := by simp [h0]
      simp only [a2bB85Loop, this, Bool.false_eq_true, if_false]
      simp only [show (84 : Nat) < 85 by decide, if_true, h4, beq_self_eq_true, Bool.true_and]
      split
      · rfl
      · simp only [show (4 + 1 != 5) = false by decide, Bool.false_eq_true, if_false]
        obtain ⟨g2, rfl⟩ : ∃ g2, g = g2 + 1 := ⟨g - 1, by omega⟩
        obtain ⟨g2', rfl⟩ : ∃ g2, g' = g2 + 1 := ⟨g' - 1, by omega⟩
        rw [b85_stop t ig k N g2 _ _ (by omega), b85_stop t ig' k N' g2' _ _ (by omega)]
  | succ n ih =>
    intro st len f f' hp hn hl hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    by_cases h0 : st.pos = 0
    · have : (decide (len ≤ 0) && st.pos == 0) = true := by simp [h0]; omega
      simp only [a2bB85Loop, this, if_true]
    · have : (decide (len ≤ 0) && st.pos == 0) = false := by simp [h0]
      simp only [a2bB85Loop, this, Bool.false_eq_true, if_false]
      simp only [show (84 : Nat) < 85 by decide, if_true]
      split
      · rfl
      · by_cases h5 : st.pos + 1 = 5
        · simp only [h5, show (5 != 5) = false by decide, Bool.false_eq_true, if_false]
          obtain ⟨g2, rfl⟩ : ∃ g2, g = g2 + 1 := ⟨g - 1, by omega⟩
          obtain ⟨g2', rfl⟩ : ∃ g2, g' = g2 + 1 := ⟨g' - 1, by omega⟩
          rw [b85_stop t ig k N g2 _ _ (by omega), b85_stop t ig' k N' g2' _ _ (by omega)]
        · have : (st.pos + 1 != 5) = true := by simpa using h5
          simp only [this, if_true]
          exact ih _ _ _ _ (by simp only; omega) (by simp only; omega) (by omega) (by omega) (by omega)

/-! ### Ignored characters can be taken out -/

/-- What the loop reads of the input: it passes over the non-digits that `ignorechars` names. -/
def keep85 (t : Nat → Nat) (ig : Option (List Nat)) (x : Nat) : Bool := !(decide (t x ≥ 85) && ign ig x)

theorem b85_filter (t : Nat → Nat) (ig : Option (List Nat)) (k : Bool) (N N' : Nat) :
    ∀ (s : List Nat) (st : St85) (f f' : Nat), st.pos < 5 → s.length + 6 ≤ f → (s.filter (keep85 t ig)).length + 6 ≤ f' →
      (a2bB85Loop t ig k N f s s.length st).toOption =
        (a2bB85Loop t none k N' f' (s.filter (keep85 t ig)) (s.filter (keep85 t ig)).length st).toOption := by
  intro s
  induction s with
  | nil =>
    intro st f f' hp hf hf'
    exact b85_padphase t ig none k N N' 4 st 0 f f' hp (by omega) (by omega) (by simp at hf; omega) (by simp at hf'; omega)
  | cons x xs ih =>
    intro st f f' hp hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hg : xs.length + 6 ≤ g := by simp at hf; omega
    have hst1 : (decide (((x :: xs).length : Int) ≤ 0) && st.pos == 0) = false := by simp; omega
    have e1 : ((x :: xs).length : Int) - 1 = xs.length := by simp
    by_cases hd : t x < 85
    · have hk : keep85 t ig x = true := by simp [keep85, Nat.not_le.mpr hd]
      rw [List.filter_cons_of_pos hk] at hf' ⊢
      obtain ⟨g', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by simp at hf'; omega⟩
      have hg' : (xs.filter (keep85 t ig)).length + 6 ≤ g' := by simp at hf'; omega
      have hst2 : (decide (((x :: xs.filter (keep85 t ig)).length : Int) ≤ 0) && st.pos == 0) = false := by simp; omega
      have e2 : ((x :: xs.filter (keep85 t ig)).length : Int) - 1 = (xs.filter (keep85 t ig)).length := by simp
      simp only [a2bB85Loop, hst1, hst2, Bool.false_eq_true, if_false, hd, if_true]
      split
      · rfl
      · by_cases h5 : st.pos + 1 = 5
        · have c1 : ¬ ((x :: xs).length : Int) < 1 := by simp; omega
          have c2 : ¬ ((x :: xs.filter (keep85 t ig)).length : Int) < 1 := by simp; omega
          simp only [h5, show (5 != 5) = false by decide, Bool.false_eq_true, if_false, c1, c2,
            show ¬ (4 : Nat) = 0 by decide, show decide ((4 : Nat) < 4) = false by decide, Bool.and_false,
            Bool.false_and, e1, e2]
          exact ih _ _ _ (by simp) hg hg'
        · have : (st.pos + 1 != 5) = true := by simpa using h5
          simp only [this, if_true, e1, e2]
          exact ih _ _ _ (by simp only; omega) hg hg'
    · by_cases hi : ign ig x = true
      · have hk : keep85 t ig x = false := by simp [keep85, Nat.not_lt.mp hd, hi]
        rw [List.filter_cons_of_neg (by simp [hk])] at hf' ⊢
        simp only [a2bB85Loop, hst1, Bool.false_eq_true, if_false, hd, Option.getD_some, hi, Bool.not_true]
        have hp5 : (st.pos != 5) = true := by simp; omega
        simp only [hp5, if_true, e1]
        exact ih _ _ _ hp hg hf'
      · have hk : keep85 t ig x = true := by simp [keep85, hi]
        rw [List.filter_cons_of_pos hk] at hf' ⊢
        obtain ⟨g', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by simp at hf'; omega⟩
        have hst2 : (decide (((x :: xs.filter (keep85 t ig)).length : Int) ≤ 0) && st.pos == 0) = false := by simp; omega
        have hi' : ign ig x = false := by simpa using hi
        simp only [a2bB85Loop, hst1, hst2, Bool.false_eq_true, if_false, hd, Option.getD_some, hi', show ign none x = false from rfl,
          Bool.not_false, if_true]
        rfl

end PyLean.TextLibs.Binascii
