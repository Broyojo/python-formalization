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
    (x.isNaN = true → ∃ v, PyFloat_Pack4 x le = .ok (layout 4 v le) ∧
      (2 ^ 31 ≤ v ↔ x.sign = true) ∧ v < 2 ^ 32 ∧ (v / 2 ^ 23) % 256 = 255 ∧
      v % 2 ^ 22 = (x.frac / 2 ^ 29) % 2 ^ 22 ∧
      ((v / 2 ^ 22) % 2 = 0 ↔ ((x.frac / 2 ^ 51) % 2 = 0 ∧ (x.frac / 2 ^ 29) % 2 ^ 22 ≠ 0)))

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

theorem limit32_pos : 0 < limit32 := by
  unfold limit32; exact Rat.mul_pos (natCast_pos' (by decide)) (pw_pos _)

theorem pack4Spec_proven : Pack4Spec := by
  intro x le
  refine ⟨fun hx hge => ?_, fun hx hlt => ?_, fun hi => ?_, fun hn => ?_⟩
  · -- overflow
    have hz : x.isZero = false := by
      cases hc : x.isZero
      · rfl
      · rw [toRat_of_isZero hc, abs_of_nonneg (a := 0) (by decide)] at hge
        exact absurd hge (Rat.not_le.2 limit32_pos)
    have hq0 : x.toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat hx).2 h] at hz; cases hz
    obtain ⟨hn, hd, hnd⟩ := natAbs_div_den hq0
    rw [← abs_eq_ite] at hnd
    have hnone : roundPos binary32 x.toRat.num.natAbs x.toRat.den = none :=
      (roundPos32_none_iff hn hd).2 (by rw [hnd]; exact hge)
    have hT : toFloat32Bits x = (if x.sign then 2 ^ 31 else 0) + 255 * 2 ^ 23 := by
      simp only [toFloat32Bits, isNaN_false_of_finite hx, isInf_false_of_finite hx, hz,
        Bool.false_eq_true, ↓reduceIte, hnone]
      rfl
    simp only [PyFloat_Pack4, hT, isInf_false_of_finite hx]
    have : (((if x.sign = true then 2 ^ 31 else 0) + 255 * 2 ^ 23) % 2 ^ 31 == 0x7f800000) = true := by
      split <;> decide
    simp [this]
  · -- in range
    by_cases hz : x.isZero = true
    · have hT : toFloat32Bits x = if x.sign then 2 ^ 31 else 0 := by
        simp [toFloat32Bits, isNaN_false_of_finite hx, isInf_false_of_finite hx, hz]
      have hv : (if x.sign then 2 ^ 31 else 0) < 2 ^ 32 := by split <;> decide
      refine ⟨_, hv, ?_, by split <;> simp_all, ?_⟩
      · simp only [PyFloat_Pack4, hT, isNaN_false_of_finite hx, isInf_false_of_finite hx]
        have : ((if x.sign = true then 2 ^ 31 else 0) % 2 ^ 31 == 0x7f800000) = false := by
          split <;> decide
        simp [this]
      · have hw := unpack4Widen_proven (if x.sign then 2 ^ 31 else 0) le hv
        have hview : binary32.view (if x.sign then 2 ^ 31 else 0) = .finite x.sign 0 (-149) := by
          cases x.sign <;> decide
        rw [hview] at hw
        simp only [] at hw
        obtain ⟨w1, _, w3⟩ := hw
        have hd0 : dyadic 0 (-149) = 0 := by decide
        rw [hd0, Rat.neg_zero, ite_self] at w3
        rw [w3, toRat_of_isZero hz]
        refine ⟨w1, ⟨0, -149, by decide, by decide, Or.inl (by simp)⟩, fun z _ => ?_, fun z _ h hne => ?_⟩
        · rw [Rat.sub_self, abs_of_nonneg (a := 0) (by decide)]; exact abs_nonneg _
        · exfalso
          rw [Rat.sub_self, abs_of_nonneg (a := 0) (by decide)] at h
          have := abs_le_zero (a := 0 - z) (by rw [← h]; exact Rat.le_refl)
          apply hne; grind
    · have hz' : x.isZero = false := by simpa using hz
      have hq0 : x.toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat hx).2 h] at hz'; cases hz'
      obtain ⟨hn, hd, hnd⟩ := natAbs_div_den hq0
      rw [← abs_eq_ite] at hnd
      generalize hN : x.toRat.num.natAbs = n at hn hnd
      generalize hD : x.toRat.den = d at hd hnd
      have hsome : roundPos binary32 n d ≠ none := by
        intro h; have := (roundPos32_none_iff hn hd).1 h; rw [hnd] at this
        exact absurd hlt (Rat.not_lt.2 this)
      obtain ⟨⟨m, e⟩, hr⟩ : ∃ r, roundPos binary32 n d = some r := by
        cases h : roundPos binary32 n d with
        | none => exact absurd h hsome
        | some r => exact ⟨r, rfl⟩
      obtain ⟨hm, he, hc, hmax, hval, heven⟩ := roundPos_some binary32 (by decide) hn hd hr
      have he' : -149 ≤ e := by simpa [Fmt.etiny, binary32] using he
      have hc' : 2 ^ 23 ≤ m ∨ e = -149 := by simpa [Fmt.etiny, binary32] using hc
      have hmax' : e ≤ 104 := by simp [binary32] at hmax; omega
      obtain ⟨v1, v2, v3, v4, v5⟩ := view_encode32 x.sign (show m < 2 ^ 24 from hm) he' hc' hmax'
      have hT : toFloat32Bits x = binary32.encode x.sign (some (m, e)) := by
        simp only [toFloat32Bits, isNaN_false_of_finite hx, isInf_false_of_finite hx, hz',
          Bool.false_eq_true, ↓reduceIte, hN, hD, hr]
      generalize hV : binary32.encode x.sign (some (m, e)) = V at v1 v2 v3 v4 v5 hT
      refine ⟨V, v1, ?_, v3, ?_⟩
      · simp only [PyFloat_Pack4, hT, isNaN_false_of_finite hx, isInf_false_of_finite hx]
        have : (V % 2 ^ 31 == 0x7f800000) = false := by simpa using v5
        simp [this]
      · have hw := unpack4Widen_proven V le v1
        rw [v2] at hw
        simp only [] at hw
        obtain ⟨w1, _, w3⟩ := hw
        rw [dyadic_eq] at w3
        rw [w3]
        have hR : (m : Rat) * pw e = (roundedInt binary32 n d : Rat) * pw (roundExp binary32 n d) := hval
        have hrep : Rep binary32 ((m : Rat) * pw e) := ⟨m, e, hm, he, Or.inl rfl⟩
        have ex := MathInt.sign_val hx
        rw [← hnd] at ex
        refine ⟨w1, ?_, fun z hzr => ?_, fun z hzr htie hne => ?_⟩
        · split
          · exact rep32_neg hrep
          · exact hrep
        · cases hs : x.sign
          · simp only [hs, Bool.false_eq_true, ↓reduceIte] at ex ⊢
            rw [ex, hR]
            exact rounded_nearest binary32 (by decide) hn hd hzr
          · simp only [hs, ↓reduceIte] at ex ⊢
            rw [ex, hR]
            have := rounded_nearest binary32 (by decide) hn hd (rep32_neg hzr)
            have e1 : -((n : Rat) / d) - -((roundedInt binary32 n d : Rat) * pw (roundExp binary32 n d)) =
                -((n : Rat) / d - (roundedInt binary32 n d : Rat) * pw (roundExp binary32 n d)) := by grind
            have e2 : -((n : Rat) / d) - z = -((n : Rat) / d - -z) := by grind
            rw [e1, e2, abs_neg, abs_neg]
            unfold roundedInt at this ⊢
            exact this
        · rw [v4]
          apply heven
          cases hs : x.sign
          · simp only [hs, Bool.false_eq_true, ↓reduceIte] at ex htie hne
            rw [ex, hR] at htie
            rw [hR] at hne
            unfold roundedInt at htie hne ⊢
            exact rounded_tie binary32 (by decide) hn hd hzr htie (fun h => hne h)
          · simp only [hs, ↓reduceIte] at ex htie hne
            rw [ex, hR] at htie
            rw [hR] at hne
            have e1 : -((n : Rat) / d) - -((roundedInt binary32 n d : Rat) * pw (roundExp binary32 n d)) =
                -((n : Rat) / d - (roundedInt binary32 n d : Rat) * pw (roundExp binary32 n d)) := by grind
            have e2 : -((n : Rat) / d) - z = -((n : Rat) / d - -z) := by grind
            rw [e1, e2, abs_neg, abs_neg] at htie
            unfold roundedInt at htie hne ⊢
            exact rounded_tie binary32 (by decide) hn hd (rep32_neg hzr) htie
              (fun h => hne (by rw [← Rat.neg_neg z, h]))
  · -- infinity
    have hT : toFloat32Bits x = if x.sign then 0xff800000 else 0x7f800000 := by
      simp [toFloat32Bits, not_nan_of_inf hi, hi]
    simp only [PyFloat_Pack4, hT, hi, not_nan_of_inf hi]
    simp
  · -- NaN
    have hb : (x.bits / 2 ^ 51) % 2 = (x.frac / 2 ^ 51) % 2 := by
      unfold F64.frac; omega
    have hT0 : toFloat32Bits x = (if x.sign then 2 ^ 31 else 0) + 0x7fc00000 + (x.frac / 2 ^ 29) % 2 ^ 22 := by
      simp [toFloat32Bits, hn]
    have hSb : ((if x.sign = true then 2 ^ 31 else 0 : Nat) = 0 ∧ x.sign = false) ∨
        ((if x.sign = true then 2 ^ 31 else 0 : Nat) = 2 ^ 31 ∧ x.sign = true) := by
      cases x.sign
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
    generalize hTdef : toFloat32Bits x = T at hT0
    generalize hSdef : (if x.sign = true then 2 ^ 31 else 0 : Nat) = S at hT0 hSb
    have hinf : (T % 2 ^ 31 == 0x7f800000) = false := by
      have : T % 2 ^ 31 ≠ 0x7f800000 := by omega
      simpa using this
    have hP : PyFloat_Pack4 x le = .ok (layout 4
        (if ((x.bits / 2 ^ 51) % 2 == 0 && T % 2 ^ 22 != 0) = true then T - 2 ^ 22 else T) le) := by
      unfold PyFloat_Pack4
      rw [hTdef]
      simp only [hinf, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hn, Bool.true_and]
    refine ⟨_, hP, ?_⟩
    have hp : x.frac / 2 ^ 29 % 2 ^ 22 < 4194304 := Nat.mod_lt _ (by decide)
    have hb1 : x.bits / 2 ^ 51 % 2 < 2 := Nat.mod_lt _ (by decide)
    generalize x.frac / 2 ^ 29 % 2 ^ 22 = p at hp hT0 ⊢
    generalize x.bits / 2 ^ 51 % 2 = b1 at hb hb1 ⊢
    generalize x.frac / 2 ^ 51 % 2 = b2 at hb ⊢
    split
    · rename_i h1
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1
      rcases hSb with ⟨h, hs⟩ | ⟨h, hs⟩ <;> rw [hs] <;> simp only [Bool.false_eq_true, iff_false,
        iff_true] <;> refine ⟨by omega, by omega, by omega, by omega, by constructor <;> intro <;> omega⟩
    · rename_i h1
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at h1
      rcases hSb with ⟨h, hs⟩ | ⟨h, hs⟩ <;> rw [hs] <;> simp only [Bool.false_eq_true, iff_false,
        iff_true] <;> refine ⟨by omega, by omega, by omega, by omega, by constructor <;> intro <;> omega⟩

end PyLean.Binary64
