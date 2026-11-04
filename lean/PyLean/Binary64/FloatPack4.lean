import PyLean.Binary64.FloatSmall

/-!
`PyFloat_Pack4`, `Objects/floatobject.c:2003-2066` (CPython 3.15.2), on every double: the
conversion `(float)x` rounds to nearest even in binary32, `OverflowError` exactly from the
binary32 overflow threshold on, and NaN payloads. `roundPos32_none_iff` is
`roundPos_none_iff` of `Lemmas.lean` with the binary32 constants.
-/

namespace PyLean.Binary64

open PyLean F64

/-- Halfway between `FLT_MAX` and `2 ** 128`: from here on a value rounds to infinity in
binary32. -/
def limit32 : Rat := ((2 ^ 25 - 1 : Nat) : Rat) * pw 103

/-- `n / d` at or past the limit is exactly when `roundPos` overflows. -/
theorem roundPos32_none_iff {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    roundPos binary32 n d = none ↔ limit32 ≤ (n : Rat) / d := by
  obtain ⟨hlt, h2, h3⟩ := roundExp_spec binary32 (by decide) hn hd
  obtain ⟨hq1, hq2⟩ := quotient_bounds binary32 (by decide) hn hd
  obtain ⟨hD, hr, hQ⟩ := divPow2_spec (n := n) hd (roundExp binary32 n d)
  obtain ⟨hx0, hx1, hup, htie, hdown⟩ := frac_facts hD hr
  have hc := roundInt_cases (divPow2 n d (roundExp binary32 n d)).1
    (divPow2 n d (roundExp binary32 n d)).2.1 (divPow2 n d (roundExp binary32 n d)).2.2
  have hdef : roundPos binary32 n d = (if ((127 : Nat) : Int) <
      (if roundedInt binary32 n d = 2 ^ 24 then ((2 ^ 23, roundExp binary32 n d + 1) : Nat × Int)
        else (roundedInt binary32 n d, roundExp binary32 n d)).2 + ((23 : Nat) : Int) then none
      else some (if roundedInt binary32 n d = 2 ^ 24 then ((2 ^ 23, roundExp binary32 n d + 1) : Nat × Int)
        else (roundedInt binary32 n d, roundExp binary32 n d))) := rfl
  have hv : (n : Rat) / d = (n : Rat) / d / pw (roundExp binary32 n d) * pw (roundExp binary32 n d) :=
    (Rat.div_mul_cancel (pw_ne _)).symm
  rw [← hQ] at hv
  rw [hdef]
  unfold roundedInt
  have hlt' : (n : Rat) / d < pw (roundExp binary32 n d + 24) := hlt
  have h2' : roundExp binary32 n d = -149 ∨ pw (roundExp binary32 n d + 23) ≤ (n : Rat) / d := h2
  have hq1' : (divPow2 n d (roundExp binary32 n d)).1 < 2 ^ 24 := hq1
  clear hlt h2 h3 hq1 hq2 hdef hQ
  generalize (n : Rat) / d = v at *
  generalize roundExp binary32 n d = e0 at *
  generalize roundInt (divPow2 n d e0).1 (divPow2 n d e0).2.1 (divPow2 n d e0).2.2 = q' at *
  generalize (divPow2 n d e0).1 = q at *
  generalize (divPow2 n d e0).2.1 = r at *
  generalize (divPow2 n d e0).2.2 = D at *
  generalize (r : Rat) / (D : Nat) = x at *
  have hL := pw_pos 103
  have h971 : pw 104 = 2 * pw 103 := pw_succ 103
  have h53 : pw 24 = 16777216 := by
    have := pw_natCast 24
    simpa using this
  have h1023 : pw 127 = 16777216 * pw 103 := by
    rw [show (127 : Int) = 103 + 24 from rfl, pw_add, h53, Rat.mul_comm]
  have h1024 : pw 128 = 33554432 * pw 103 := by
    rw [show (128 : Int) = 127 + 1 from rfl, pw_succ, h1023]; grind
  have hlim : limit32 = 33554431 * pw 103 := by
    unfold limit32; congr 1
  rw [hlim]
  have hq'cast : (q : Rat) ≤ 16777215 := by
    have : q ≤ 16777215 := by omega
    exact_mod_cast Rat.natCast_le_natCast.2 this
  constructor
  · intro hnone
    by_cases hcq : q' = 2 ^ 24
    · have he : 104 ≤ e0 := by
        simp only [hcq, ↓reduceIte] at hnone
        by_cases h9 : ((127 : Nat) : Int) < ((2 ^ 23, e0 + 1) : Nat × Int).2 + ((23 : Nat) : Int)
        · simp only at h9; omega
        · simp only [h9, ↓reduceIte] at hnone; cases hnone
      have hqeq : q = 16777215 := by
        rcases hc with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> omega
      have hx12 : 1 / 2 ≤ x := by
        rcases hc with ⟨c, e⟩ | ⟨c, _, e⟩ | ⟨c, _, e⟩ | ⟨c, _, e⟩
        · exact Rat.le_of_lt (hup c)
        · have := htie c; grind
        · omega
        · omega
      have hqr : (q : Rat) = 16777215 := by rw [hqeq]; rfl
      have hp : pw 104 ≤ pw e0 := pw_le he
      rw [hv, hqr]
      have h5 : (16777215 + 1 / 2) * pw 104 ≤ ((16777215 : Rat) + x) * pw e0 := by
        have a1 : (16777215 + 1 / 2) * pw 104 ≤ (16777215 + 1 / 2) * pw e0 :=
          Rat.mul_le_mul_of_nonneg_left hp (by decide +kernel)
        have a2 : (16777215 + 1 / 2) * pw e0 ≤ ((16777215 : Rat) + x) * pw e0 :=
          Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt (pw_pos e0))
        exact Rat.le_trans a1 a2
      rw [h971] at h5
      grind
    · have he : 105 ≤ e0 := by
        simp only [hcq, ↓reduceIte] at hnone
        by_cases h9 : ((127 : Nat) : Int) < ((q', e0) : Nat × Int).2 + ((23 : Nat) : Int)
        · simp only at h9; omega
        · simp only [h9, ↓reduceIte] at hnone; cases hnone
      have hp : pw 128 ≤ pw (e0 + 23) := pw_le (by omega)
      rcases h2' with h | h
      · omega
      · grind
  · intro hge
    have he0 : 104 ≤ e0 := by
      apply Int.not_lt.1
      intro h
      have : pw (e0 + 24) ≤ pw 127 := pw_le (by omega)
      grind
    by_cases he9 : 105 ≤ e0
    · split
      · simp only []
        split
        · rfl
        · omega
      · simp only []
        split
        · rfl
        · omega
    · have he : e0 = 104 := by omega
      subst he
      have hQ1 : 16777215 + 1 / 2 ≤ (q : Rat) + x := by
        rw [hv] at hge
        rw [h971] at hge
        apply Rat.le_of_mul_le_mul_right _ (pw_pos 103)
        grind
      have hqeq : q = 16777215 := by
        have : (16777214 : Rat) < (q : Rat) := by grind
        have h2 : ((16777214 : Nat) : Rat) < (q : Rat) := by exact_mod_cast this
        have := Rat.natCast_lt_natCast.1 h2
        omega
      have hx12 : 1 / 2 ≤ x := by
        have hqr : (q : Rat) = 16777215 := by rw [hqeq]; rfl
        grind
      have hq'' : q' = 2 ^ 24 := by
        rcases hc with ⟨c, e⟩ | ⟨c, _, e⟩ | ⟨c, c2, e⟩ | ⟨c, c2, e⟩
        · omega
        · omega
        · omega
        · exfalso
          have := hdown c c2
          grind
      simp [hq'']


end PyLean.Binary64
