import PyLean.Fractions.Ctor

/-!
`_add`, `_sub`, `_mul`, `_div` (Knuth's gcd-optimised algorithms,
fractions.py:726-860) and `__pow__` with an int exponent: results are in
lowest terms with a positive denominator and have the exact value.
-/

namespace PyLean.Fractions

open PyLean

theorem pyDiv_mul_left (G y : Int) (hG : G ≠ 0) : pyDiv (G * y) G = y := by
  rw [pyDiv_of_dvd ⟨y, rfl⟩]; exact Int.mul_ediv_cancel_left _ hG

theorem add_spec (a b : Frac) (ha : a.Normal) (hb : b.Normal) :
    (add a b).Normal ∧
      (add a b).num * (a.den * b.den) = (a.num * b.den + b.num * a.den) * (add a b).den := by
  obtain ⟨hda, hga⟩ := ha
  obtain ⟨hdb, hgb⟩ := hb
  obtain ⟨s, s', hs, hs', hss, hG⟩ := gcd_cofactors (n := a.den) (d := b.den) (by omega)
  generalize hGdef : (Int.gcd a.den b.den : Int) = G at hs hs' hG
  have hspos : 0 < s := pos_of_mul_pos_left hG (hs ▸ hda)
  have hs'pos : 0 < s' := pos_of_mul_pos_left hG (hs' ▸ hdb)
  have h_s_na : Int.gcd s a.num = 1 :=
    gcd_one_of_dvd (dvd_of_eq_mul_left hs) (Int.dvd_refl _) (gcd_one_comm hga)
  have h_s'_nb : Int.gcd s' b.num = 1 :=
    gcd_one_of_dvd (dvd_of_eq_mul_left hs') (Int.dvd_refl _) (gcd_one_comm hgb)
  by_cases hG1 : G = 1
  · subst hG1
    have e1 : a.den = s := by omega
    have e2 : b.den = s' := by omega
    have hr : add a b = ⟨a.num * b.den + a.den * b.num, a.den * b.den⟩ := by
      simp only [add, hGdef, ↓reduceIte]
    rw [hr]
    refine ⟨⟨Int.mul_pos hda hdb, ?_⟩, by simp only; grind⟩
    simp only
    apply gcd_mul_one
    · apply gcd_one_comm
      rw [Int.gcd_add_mul_left_right, Int.gcd_mul_right_right_of_gcd_eq_one (gcd_one_comm hga)]
      rw [e1, e2]; exact hss
    · apply gcd_one_comm
      rw [Int.gcd_mul_right_add_right, Int.gcd_mul_right_right_of_gcd_eq_one]
      · exact gcd_one_comm hgb
      · rw [e1, e2]; exact gcd_one_comm hss
  · have hGne : G ≠ 0 := by omega
    have hsdiv : pyDiv a.den G = s := by rw [hs]; exact pyDiv_mul_left G s hGne
    have hs'div : pyDiv b.den G = s' := by rw [hs']; exact pyDiv_mul_left G s' hGne
    generalize ht : a.num * s' + b.num * s = t
    obtain ⟨t', h, ht', hh, hth, hg2⟩ := gcd_cofactors (n := t) (d := G) hGne
    generalize hg2def : (Int.gcd t G : Int) = g2 at ht' hh hg2
    have hhpos : 0 < h := pos_of_mul_pos_left hg2 (hh ▸ hG)
    have hr : add a b = ⟨t', s * (h * s')⟩ := by
      simp only [add, hGdef, hG1, ↓reduceIte, hsdiv, hs'div, ht, hg2def]
      by_cases hg21 : g2 = 1
      · subst hg21
        simp only [↓reduceIte]
        have e3 : t' = t := by omega
        have e4 : h = G := by omega
        rw [e3, e4, ← hs']
      · simp only [hg21, ↓reduceIte]
        have hg2ne : g2 ≠ 0 := by omega
        rw [ht', hs', hh, Int.mul_assoc, pyDiv_mul_left _ _ hg2ne, pyDiv_mul_left _ _ hg2ne]
    rw [hr]
    have h_t_s : Int.gcd t s = 1 := by
      apply gcd_one_comm
      rw [← ht, Int.gcd_add_mul_right_right, Int.gcd_mul_right_right_of_gcd_eq_one h_s_na]
      exact hss
    have h_t_s' : Int.gcd t s' = 1 := by
      apply gcd_one_comm
      rw [← ht, Int.gcd_mul_right_add_right, Int.gcd_mul_right_right_of_gcd_eq_one h_s'_nb]
      exact gcd_one_comm hss
    have htt : t' ∣ t := dvd_of_eq_mul_left ht'
    refine ⟨⟨Int.mul_pos hspos (Int.mul_pos hhpos hs'pos), ?_⟩, ?_⟩
    · simp only
      exact gcd_mul_one (gcd_one_of_dvd htt (Int.dvd_refl _) h_t_s)
        (gcd_mul_one hth (gcd_one_of_dvd htt (Int.dvd_refl _) h_t_s'))
    · simp only
      rw [hs, hs', hh]
      have : a.num * s' + b.num * s = g2 * t' := by rw [ht, ht']
      grind

/-- `sub` is `add` with the second operand negated. -/
theorem sub_eq_add_neg (a b : Frac) : sub a b = add a ⟨-b.num, b.den⟩ := by
  simp only [sub, add, Int.sub_eq_add_neg, Int.mul_neg, Int.neg_mul]

theorem neg_normal {b : Frac} (hb : b.Normal) : (⟨-b.num, b.den⟩ : Frac).Normal :=
  ⟨hb.1, by simp only [Int.neg_gcd]; exact hb.2⟩

theorem sub_spec (a b : Frac) (ha : a.Normal) (hb : b.Normal) :
    (sub a b).Normal ∧
      (sub a b).num * (a.den * b.den) = (a.num * b.den - b.num * a.den) * (sub a b).den := by
  rw [sub_eq_add_neg]
  obtain ⟨h1, h2⟩ := add_spec a _ ha (neg_normal hb)
  refine ⟨h1, ?_⟩
  simp only at h2
  rw [h2]; grind

theorem mul_spec (a b : Frac) (ha : a.Normal) (hb : b.Normal) :
    (mul a b).Normal ∧ (mul a b).num * (a.den * b.den) = (a.num * b.num) * (mul a b).den := by
  obtain ⟨hda, hga⟩ := ha
  obtain ⟨hdb, hgb⟩ := hb
  obtain ⟨na', db', hna, hdb', h1, hg1⟩ := gcd_cofactors (n := a.num) (d := b.den) (by omega)
  obtain ⟨nb', da', hnb, hda', h2, hg2⟩ := gcd_cofactors (n := b.num) (d := a.den) (by omega)
  generalize hg1def : (Int.gcd a.num b.den : Int) = g1 at hna hdb' hg1
  generalize hg2def : (Int.gcd b.num a.den : Int) = g2 at hnb hda' hg2
  have hr : mul a b = ⟨na' * nb', db' * da'⟩ := by
    simp only [mul, hg1def, hg2def]
    have e1 : (if g1 > 1 then (pyDiv a.num g1, pyDiv b.den g1) else (a.num, b.den)) = (na', db') := by
      split
      · rw [hna, hdb', pyDiv_mul_left _ _ (by omega), pyDiv_mul_left _ _ (by omega)]
      · have : g1 = 1 := by omega
        subst this; simp only [Prod.mk.injEq]; omega
    have e2 : (if g2 > 1 then (pyDiv b.num g2, pyDiv a.den g2) else (b.num, a.den)) = (nb', da') := by
      split
      · rw [hnb, hda', pyDiv_mul_left _ _ (by omega), pyDiv_mul_left _ _ (by omega)]
      · have : g2 = 1 := by omega
        subst this; simp only [Prod.mk.injEq]; omega
    rw [e1, e2]
  rw [hr]
  have hdb'pos : 0 < db' := pos_of_mul_pos_left hg1 (hdb' ▸ hdb)
  have hda'pos : 0 < da' := pos_of_mul_pos_left hg2 (hda' ▸ hda)
  have c1 : Int.gcd na' da' = 1 :=
    gcd_one_of_dvd (dvd_of_eq_mul_left hna) (dvd_of_eq_mul_left hda') hga
  have c2 : Int.gcd nb' db' = 1 :=
    gcd_one_of_dvd (dvd_of_eq_mul_left hnb) (dvd_of_eq_mul_left hdb') hgb
  refine ⟨⟨Int.mul_pos hdb'pos hda'pos, ?_⟩, ?_⟩
  · simp only
    exact gcd_mul_one (gcd_one_comm (gcd_mul_one (gcd_one_comm h1) (gcd_one_comm c2)))
      (gcd_one_comm (gcd_mul_one (gcd_one_comm c1) (gcd_one_comm h2)))
  · simp only
    rw [hna, hdb', hnb, hda']
    grind

theorem div_spec (a b : Frac) (ha : a.Normal) (hb : b.Normal) (hnz : b.num ≠ 0) :
    ∃ r, div a b = .ok r ∧ r.Normal ∧ r.num * (a.den * b.num) = (a.num * b.den) * r.den := by
  obtain ⟨hda, hga⟩ := ha
  obtain ⟨hdb, hgb⟩ := hb
  obtain ⟨na', nb', hna, hnb, h1, hg1⟩ := gcd_cofactors (n := a.num) (d := b.num) hnz
  obtain ⟨db', da', hdb', hda', h2, hg2⟩ := gcd_cofactors (n := b.den) (d := a.den) (by omega)
  generalize hg1def : (Int.gcd a.num b.num : Int) = g1 at hna hnb hg1
  generalize hg2def : (Int.gcd b.den a.den : Int) = g2 at hdb' hda' hg2
  have hdb'pos : 0 < db' := pos_of_mul_pos_left hg2 (hdb' ▸ hdb)
  have hda'pos : 0 < da' := pos_of_mul_pos_left hg2 (hda' ▸ hda)
  have hnb'ne : nb' ≠ 0 := by intro h; rw [h] at hnb; simp at hnb; exact hnz hnb
  have c1 : Int.gcd na' da' = 1 :=
    gcd_one_of_dvd (dvd_of_eq_mul_left hna) (dvd_of_eq_mul_left hda') hga
  have c2 : Int.gcd db' nb' = 1 :=
    gcd_one_of_dvd (dvd_of_eq_mul_left hdb') (dvd_of_eq_mul_left hnb) (gcd_one_comm hgb)
  have hcop : Int.gcd (na' * db') (nb' * da') = 1 := by
    exact gcd_mul_one (gcd_one_comm (gcd_mul_one (gcd_one_comm h1) (gcd_one_comm c2)))
      (gcd_one_comm (gcd_mul_one (gcd_one_comm c1) (gcd_one_comm h2)))
  have hval : na' * db' * (a.den * b.num) = a.num * b.den * (nb' * da') := by
    rw [hna, hnb, hdb', hda']; grind
  have e1 : (if g1 > 1 then (pyDiv a.num g1, pyDiv b.num g1) else (a.num, b.num)) = (na', nb') := by
    split
    · rw [hna, hnb, pyDiv_mul_left _ _ (by omega), pyDiv_mul_left _ _ (by omega)]
    · have : g1 = 1 := by omega
      subst this; simp only [Prod.mk.injEq]; omega
  have e2 : (if g2 > 1 then (pyDiv a.den g2, pyDiv b.den g2) else (a.den, b.den)) = (da', db') := by
    split
    · rw [hda', hdb', pyDiv_mul_left _ _ (by omega), pyDiv_mul_left _ _ (by omega)]
    · have : g2 = 1 := by omega
      subst this; simp only [Prod.mk.injEq]; omega
  have hd0 : nb' * da' ≠ 0 := Int.mul_ne_zero hnb'ne (by omega)
  by_cases hneg : nb' * da' < 0
  · refine ⟨⟨-(na' * db'), -(nb' * da')⟩, ?_, ⟨by simp only; omega, ?_⟩, ?_⟩
    · simp only [div, hnz, ↓reduceIte, hg1def, hg2def]
      rw [e1, e2]; simp only [hneg, ↓reduceIte]; rfl
    · simp only [Int.neg_gcd, Int.gcd_neg]; exact hcop
    · simp only; grind
  · refine ⟨⟨na' * db', nb' * da'⟩, ?_, ⟨by simp only; omega, hcop⟩, by simp only; grind⟩
    simp only [div, hnz, ↓reduceIte, hg1def, hg2def]
    rw [e1, e2]; simp only [hneg, ↓reduceIte]; rfl

end PyLean.Fractions
