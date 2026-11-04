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


/-! ## The specification -/

/-- `PyFloat_Pack4` on every double, in both byte orders.

* A finite `x` with `|x|` at or past `2**128 - 2**103` raises `OverflowError` (:2009-2013).
* Any other finite `x` packs to a binary32 pattern `v` with the sign of `x` (signed zeros
  and underflow to zero included) whose value, read back by `PyFloat_Unpack4`, is a
  binary32 number at least as close to `x` as every binary32 number, with an even
  significand (`v % 2 = 0`) on a tie: round to nearest even, so `0.1` packs to `0x3dcccccd`.
* An infinity packs to the infinity of its sign.
* A NaN keeps its sign and the top 22 payload bits (bits 51-29 of the fraction, the lower
  29 are dropped), and is quiet unless it was signaling with a nonzero kept payload
  (:2015-2029). -/
def Pack4Spec : Prop :=
  ∀ (x : F64) (le : Bool),
    (x.isFinite = true → limit32 ≤ Rat.abs x.toRat →
      PyFloat_Pack4 x le = .error (.overflowError "float too large to pack with f format")) ∧
    (x.isFinite = true → Rat.abs x.toRat < limit32 → ∃ v, v < 2 ^ 32 ∧
      PyFloat_Pack4 x le = .ok (layout 4 v le) ∧
      (2 ^ 31 ≤ v ↔ x.sign = true) ∧
      (PyFloat_Unpack4 (layout 4 v le) le).isFinite = true ∧
      Rep binary32 (PyFloat_Unpack4 (layout 4 v le) le).toRat ∧
      (∀ z, Rep binary32 z →
        Rat.abs (x.toRat - (PyFloat_Unpack4 (layout 4 v le) le).toRat) ≤ Rat.abs (x.toRat - z)) ∧
      (∀ z, Rep binary32 z →
        Rat.abs (x.toRat - (PyFloat_Unpack4 (layout 4 v le) le).toRat) = Rat.abs (x.toRat - z) →
        z ≠ (PyFloat_Unpack4 (layout 4 v le) le).toRat → v % 2 = 0)) ∧
    (x.isInf = true →
      PyFloat_Pack4 x le = .ok (layout 4 (if x.sign then 0xff800000 else 0x7f800000) le)) ∧
    (x.isNaN = true →
      PyFloat_Pack4 x le = .ok (layout 4 ((if x.sign then 2 ^ 31 else 0) + 0x7f800000 +
        (if (x.frac / 2 ^ 51) % 2 = 1 ∨ (x.frac / 2 ^ 29) % 2 ^ 22 = 0 then 2 ^ 22 else 0) +
        (x.frac / 2 ^ 29) % 2 ^ 22) le))

theorem rep32_neg {y : Rat} (h : Rep binary32 y) : Rep binary32 (-y) := by
  obtain ⟨M, E, hM, hE, hy⟩ := h
  refine ⟨M, E, hM, hE, ?_⟩
  rcases hy with rfl | rfl
  · right; rfl
  · left; simp [Rat.neg_neg]

/-- A rounded binary32 result read back as its pattern's fields. -/
theorem view_encode32 (neg : Bool) {m : Nat} {e : Int} (hm : m < 2 ^ 24) (he : -149 ≤ e)
    (hc : 2 ^ 23 ≤ m ∨ e = -149) (hmax : e ≤ 104) :
    binary32.encode neg (some (m, e)) < 2 ^ 32 ∧
    binary32.view (binary32.encode neg (some (m, e))) = .finite neg m e ∧
    (2 ^ 31 ≤ binary32.encode neg (some (m, e)) ↔ neg = true) ∧
    binary32.encode neg (some (m, e)) % 2 = m % 2 ∧
    binary32.encode neg (some (m, e)) % 2 ^ 31 ≠ 0x7f800000 := by
  rw [encode32]
  generalize hk : (e + 150).toNat = k
  have hk1 : k ≤ 254 := by omega
  by_cases hsub : m < 2 ^ 23
  · have he' : e = -149 := by omega
    simp only [hsub, ↓reduceIte]
    have hv := view32 ((if neg then 2 ^ 31 else 0) + m) (by split <;> omega)
    refine ⟨by split <;> omega, ?_, by cases neg <;> simp <;> omega, by split <;> omega,
      by split <;> omega⟩
    rw [hv, he']
    have h1 : ¬ (((if neg = true then 2 ^ 31 else 0) + m) / 2 ^ 23) % 256 = 255 := by split <;> omega
    have h2 : (((if neg = true then 2 ^ 31 else 0) + m) / 2 ^ 23) % 256 = 0 := by split <;> omega
    have h3 : ((if neg = true then 2 ^ 31 else 0) + m) % 2 ^ 23 = m := by split <;> omega
    have h4 : decide (2 ^ 31 ≤ (if neg = true then 2 ^ 31 else 0) + m) = neg := by
      cases neg <;> simp <;> omega
    simp only [h2, h3, h4, ↓reduceIte]
    simp
  · have hk0 : 1 ≤ k := by omega
    simp only [hsub, ↓reduceIte]
    have hv := view32 ((if neg then 2 ^ 31 else 0) + (k * 2 ^ 23 + (m - 2 ^ 23))) (by split <;> omega)
    refine ⟨by split <;> omega, ?_, by cases neg <;> simp <;> omega, by split <;> omega,
      by split <;> omega⟩
    rw [hv]
    have h1 : ¬ (((if neg = true then 2 ^ 31 else 0) + (k * 2 ^ 23 + (m - 2 ^ 23))) / 2 ^ 23) % 256 = 255 := by
      split <;> omega
    have h2 : ¬ (((if neg = true then 2 ^ 31 else 0) + (k * 2 ^ 23 + (m - 2 ^ 23))) / 2 ^ 23) % 256 = 0 := by
      split <;> omega
    have h3 : ((if neg = true then 2 ^ 31 else 0) + (k * 2 ^ 23 + (m - 2 ^ 23))) % 2 ^ 23 = m - 2 ^ 23 := by
      split <;> omega
    have h3' : (((if neg = true then 2 ^ 31 else 0) + (k * 2 ^ 23 + (m - 2 ^ 23))) / 2 ^ 23) % 256 = k := by
      split <;> omega
    have h4 : decide (2 ^ 31 ≤ (if neg = true then 2 ^ 31 else 0) + (k * 2 ^ 23 + (m - 2 ^ 23))) = neg := by
      cases neg <;> simp <;> omega
    simp only [h1, h2, h3, h3', h4, ↓reduceIte]
    have hk255 : k ≠ 255 := by omega
    have hk00 : k ≠ 0 := by omega
    simp only [hk255, hk00, ↓reduceIte, View.finite.injEq, true_and]
    exact ⟨by omega, by omega⟩

end PyLean.Binary64
