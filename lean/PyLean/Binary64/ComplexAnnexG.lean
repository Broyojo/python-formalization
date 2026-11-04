import PyLean.Binary64.ComplexExact

/-!
The infinity and zero recovery of `_Py_c_prod`, `_Py_c_quot` and `_Py_rc_quot`
(complexobject.c:90-304, CPython 3.15.2), stated as C11 Annex G.5.1-2 states the rules, for
every input, at binary64.
-/

namespace PyLean.Binary64

open F64

/-! ## Single operations -/

theorem qnan_isFinite : qnan.isFinite = false := by decide +kernel

theorem nonfin_cases {x : F64} (h : x.isFinite = false) : x.isInf = true ∨ x.isNaN = true := by
  rcases classify x with h' | h' | h'
  · rw [h] at h'; cases h'
  · exact Or.inl h'
  · exact Or.inr h'

theorem nan_not_finite {x : F64} (h : x.isNaN = true) : x.isFinite = false := by
  cases hf : x.isFinite
  · rfl
  · rw [isNaN_false_of_finite hf] at h; cases h

/-- Every finite double is an integer multiple of the smallest subnormal. -/
theorem grid_of_finite {x : F64} (hx : x.isFinite = true) :
    ∃ k : Int, x.toRat = (k : Rat) * pw (-1074) := by
  obtain ⟨M, E, _, hE, hy⟩ := toRat_rep hx
  have hE' : -1074 ≤ E := by simpa [Fmt.etiny, binary64] using hE
  have hp : pw E = ((2 ^ (E + 1074).toNat : Nat) : Rat) * pw (-1074) := by
    rw [← pw_natCast, Int.toNat_of_nonneg (by omega), ← pw_add]
    congr 1
    omega
  rcases hy with h | h
  · refine ⟨((M * 2 ^ (E + 1074).toNat : Nat) : Int), ?_⟩
    rw [h, hp]
    push_cast
    grind
  · refine ⟨-((M * 2 ^ (E + 1074).toNat : Nat) : Int), ?_⟩
    rw [h, hp]
    push_cast
    grind

theorem tiny_lt_limit : pw (-1074) < overflowLimit := by
  have a : pw (-1074) < pw 970 := pw_lt (by omega)
  have b : pw 970 ≤ overflowLimit := by
    unfold overflowLimit
    have : (1 : Rat) ≤ ((2 ^ 54 - 1 : Nat) : Rat) := by
      have : ((1 : Nat) : Rat) ≤ ((2 ^ 54 - 1 : Nat) : Rat) := Rat.natCast_le_natCast.2 (by decide)
      simpa using this
    have := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt (pw_pos 970))
    rwa [Rat.one_mul] at this
  grind

/-- The smallest subnormal, as a datum. -/
theorem tiny_facts : (ofRat (pw (-1074))).isFinite = true ∧ (ofRat (pw (-1074))).toRat = pw (-1074) := by
  have hrep : Rep binary64 (pw (-1074)) :=
    ⟨1, -1074, by decide, by simp [Fmt.etiny, binary64], Or.inl (by simp)⟩
  have hlt : Rat.abs (pw (-1074)) < overflowLimit := by
    rw [abs_of_nonneg (Rat.le_of_lt (pw_pos _))]; exact tiny_lt_limit
  exact ⟨(ofRat_isFinite _).2 hlt, ofRat_exact hrep hlt⟩

/-- A sum of two finite doubles rounds to zero only when it is exactly zero: there is no
underflow to zero between multiples of the smallest subnormal. -/
theorem add_isZero_exact {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hz : (F64.add x y).isZero = true) : x.toRat + y.toRat = 0 := by
  apply Classical.byContradiction
  intro hq
  rw [add_of_finite hx hy, if_neg hq] at hz
  have hf := isFinite_of_isZero hz
  have h0 := toRat_of_isZero hz
  obtain ⟨kx, ekx⟩ := grid_of_finite hx
  obtain ⟨ky, eky⟩ := grid_of_finite hy
  obtain ⟨tf, tv⟩ := tiny_facts
  have hpw := pw_pos (-1074)
  have hsum : x.toRat + y.toRat = ((kx + ky : Int) : Rat) * pw (-1074) := by
    rw [ekx, eky]; push_cast; grind
  generalize x.toRat + y.toRat = q at hq hz hf h0 hsum
  have hk : kx + ky ≠ 0 := by intro h; rw [h] at hsum; simp at hsum; exact hq hsum
  by_cases hpos : 0 < q
  · have hk1 : (1 : Rat) ≤ ((kx + ky : Int) : Rat) := by
      have : 0 < kx + ky := by
        apply Classical.byContradiction; intro hn
        have h3 : ((kx + ky : Int) : Rat) ≤ 0 := by exact_mod_cast (by omega : kx + ky ≤ 0)
        have := Rat.mul_le_mul_of_nonneg_right h3 (Rat.le_of_lt hpw)
        rw [Rat.zero_mul] at this
        grind
      exact_mod_cast (show (1 : Int) ≤ kx + ky by omega)
    have hge : pw (-1074) ≤ q := by
      rw [hsum]
      have := Rat.mul_le_mul_of_nonneg_right hk1 (Rat.le_of_lt hpw)
      rwa [Rat.one_mul] at this
    have hn := ofRat_nearest q hf tf
    rw [h0, tv, abs_eq_ite, abs_eq_ite] at hn
    split at hn <;> split at hn <;> grind
  · have hneg : q < 0 := by grind
    have hk1 : ((kx + ky : Int) : Rat) ≤ -1 := by
      have : kx + ky < 0 := by
        apply Classical.byContradiction; intro hn
        have : (0 : Rat) ≤ ((kx + ky : Int) : Rat) := by exact_mod_cast (by omega : 0 ≤ kx + ky)
        have := Rat.mul_nonneg this (Rat.le_of_lt hpw)
        grind
      have h4 : ((kx + ky + 1 : Int) : Rat) ≤ 0 := by exact_mod_cast (show kx + ky + 1 ≤ 0 by omega)
      push_cast at h4 ⊢
      grind
    have hge : q ≤ -pw (-1074) := by
      rw [hsum]
      have := Rat.mul_le_mul_of_nonneg_right hk1 (Rat.le_of_lt hpw)
      grind
    have tnf : (ofRat (pw (-1074))).neg.isFinite = true := by rw [neg_isFinite]; exact tf
    have hn := ofRat_nearest q hf tnf
    rw [h0, toRat_neg, tv, abs_eq_ite, abs_eq_ite] at hn
    split at hn <;> split at hn <;> grind

/-- A "unit": a finite datum worth `0`, `1` or `-1`, what the boxing of Annex G produces. -/
def Unit (p : F64) : Prop := p.isFinite = true ∧ (p.toRat = 1 ∨ p.toRat = -1 ∨ p.toRat = 0)

theorem d1_neg_toRat : d1.neg.toRat = -1 := by rw [toRat_neg, d1_toRat]

theorem copysign_unit (v x : F64) (hv : Unit v) : Unit (F64.copysign v x) := by
  unfold F64.copysign
  split
  · exact hv
  · obtain ⟨hf, hr⟩ := hv
    refine ⟨by rw [neg_isFinite]; exact hf, ?_⟩
    rw [toRat_neg]
    rcases hr with h | h | h <;> rw [h] <;> simp

theorem boxInf_unit (x : F64) : Unit (boxInf x) := by
  unfold boxInf
  apply copysign_unit
  split
  · exact ⟨d1_facts.2.2.1, Or.inl d1_toRat⟩
  · exact ⟨d0_isFinite, Or.inr (Or.inr d0_toRat)⟩

/-- The boxed value of an infinity is `±1`. -/
theorem boxInf_inf {x : F64} (h : x.isInf = true) : (boxInf x).toRat * (boxInf x).toRat = 1 := by
  unfold boxInf F64.copysign
  simp only [h, ite_true]
  split
  · rw [d1_toRat]; simp
  · rw [d1_neg_toRat]; grind

theorem boxInf_fin {x : F64} (h : x.isInf = false) : (boxInf x).toRat = 0 := by
  unfold boxInf F64.copysign
  simp only [h, Bool.false_eq_true, ite_false]
  split
  · exact d0_toRat
  · rw [toRat_neg, d0_toRat]; rfl

theorem nanToZero_of {x : F64} (h : x.isNaN = false) : nanToZero x = x := by
  simp [nanToZero, h]

theorem nanToZero_finite {x : F64} (h : x.isInf = false) : (nanToZero x).isFinite = true := by
  unfold nanToZero
  split
  · unfold F64.copysign
    split
    · exact d0_isFinite
    · rw [neg_isFinite]; exact d0_isFinite
  · rename_i hn
    rcases classify x with h' | h' | h'
    · exact h'
    · rw [h] at h'; cases h'
    · simp at hn; rw [hn] at h'; cases h'

/-- Multiplying by a unit is exact. -/
theorem mul_unit_l {p c : F64} (hp : Unit p) (hc : c.isFinite = true) :
    (F64.mul p c).isFinite = true ∧ (F64.mul p c).toRat = p.toRat * c.toRat := by
  obtain ⟨hpf, hr⟩ := hp
  rw [mul_of_finite hpf hc]
  split
  · rename_i h; rw [h]; exact ⟨zero_isFinite _, zero_toRat _⟩
  · rename_i h
    have hcz : c.toRat ≠ 0 := by intro h'; apply h; rw [h', Rat.mul_zero]
    have hcz' : c.isZero = false := by
      cases hh : c.isZero
      · rfl
      · exact absurd (toRat_of_isZero hh) hcz
    rcases hr with e | e | e
    · rw [e, Rat.one_mul, ofRat_toRat hc hcz']
      exact ⟨hc, rfl⟩
    · rw [e, show (-1 : Rat) * c.toRat = -c.toRat by grind, MathInt.ofRat_neg hcz,
        ofRat_toRat hc hcz', neg_isFinite, toRat_neg]
      exact ⟨hc, rfl⟩
    · rw [e, Rat.zero_mul] at h; exact absurd rfl h

theorem mul_unit_r {c p : F64} (hc : c.isFinite = true) (hp : Unit p) :
    (F64.mul c p).isFinite = true ∧ (F64.mul c p).toRat = c.toRat * p.toRat := by
  obtain ⟨hpf, hr⟩ := hp
  rw [mul_of_finite hc hpf]
  split
  · rename_i h; rw [h]; exact ⟨zero_isFinite _, zero_toRat _⟩
  · rename_i h
    have hcz : c.toRat ≠ 0 := by intro h'; apply h; rw [h', Rat.zero_mul]
    have hcz' : c.isZero = false := by
      cases hh : c.isZero
      · rfl
      · exact absurd (toRat_of_isZero hh) hcz
    rcases hr with e | e | e
    · rw [e, Rat.mul_one, ofRat_toRat hc hcz']
      exact ⟨hc, rfl⟩
    · rw [e, show c.toRat * (-1 : Rat) = -c.toRat by grind, MathInt.ofRat_neg hcz,
        ofRat_toRat hc hcz', neg_isFinite, toRat_neg]
      exact ⟨hc, rfl⟩
    · rw [e, Rat.mul_zero] at h; exact absurd rfl h

theorem add_fin_notNaN {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (F64.add x y).isNaN = false := by
  rw [add_of_finite hx hy]
  split
  · exact isNaN_false_of_finite (zero_isFinite _)
  · exact ofRat_isNaN _

/-- `INFINITY * e` is an infinity for every `e` that is not a NaN and not a zero. -/
theorem inf_mul_isInf {e : F64} (hn : e.isNaN = false) (hz : e.isZero = false) :
    (F64.mul (F64.inf false) e).isInf = true := by
  rw [(mul_spec (F64.inf false) e).inf (by simp [inf_isInf]) (inf_isNaN false) hn
    (by have := inf_isFinite false; cases h : (F64.inf false).isZero
        · rfl
        · rw [isFinite_of_isZero h] at this; cases this) hz]
  exact inf_isInf _

theorem add_nonfin_l {x y : F64} (hx : x.isFinite = false) : (F64.add x y).isFinite = false := by
  unfold F64.add
  by_cases h1 : (x.isNaN || y.isNaN) = true
  · rw [if_pos h1]; exact qnan_isFinite
  · rw [if_neg h1]
    rcases nonfin_cases hx with hi | hn
    · rw [if_pos hi]
      split
      · exact qnan_isFinite
      · exact hx
    · simp [hn] at h1

theorem add_nonfin_r {x y : F64} (hy : y.isFinite = false) : (F64.add x y).isFinite = false := by
  unfold F64.add
  by_cases h1 : (x.isNaN || y.isNaN) = true
  · rw [if_pos h1]; exact qnan_isFinite
  · rw [if_neg h1]
    by_cases hxi : x.isInf = true
    · rw [if_pos hxi]
      split
      · exact qnan_isFinite
      · exact not_finite_of_inf hxi
    · rw [if_neg hxi]
      rcases nonfin_cases hy with hi | hn
      · rw [if_pos hi]; exact hy
      · simp [hn] at h1

theorem mul_inf_l {x y : F64} (hx : x.isInf = true) : (F64.mul x y).isFinite = false := by
  unfold F64.mul
  split
  · exact qnan_isFinite
  · simp only [hx, ite_true]
    split
    · exact qnan_isFinite
    · exact inf_isFinite _

theorem mul_inf_r {x y : F64} (hy : y.isInf = true) : (F64.mul x y).isFinite = false := by
  unfold F64.mul
  split
  · exact qnan_isFinite
  · split
    · split
      · exact qnan_isFinite
      · exact inf_isFinite _
    · simp only [hy, ite_true]
      split
      · exact qnan_isFinite
      · exact inf_isFinite _

theorem sub_nonfin_l {x y : F64} (hx : x.isFinite = false) : (F64.sub x y).isFinite = false :=
  add_nonfin_l hx

theorem sub_nonfin_r {x y : F64} (hy : y.isFinite = false) : (F64.sub x y).isFinite = false :=
  add_nonfin_r (by rw [neg_isFinite]; exact hy)

theorem div_nonfin_l {x y : F64} (hx : x.isFinite = false) : (F64.div x y).isFinite = false := by
  rcases nonfin_cases hx with hi | hn
  · unfold F64.div
    split
    · exact qnan_isFinite
    · simp only [hi, ite_true]
      split
      · exact qnan_isFinite
      · exact inf_isFinite _
  · unfold F64.div; simp [hn, qnan_isFinite]

/-- The rational fact behind both recoveries: `a c - b d` and `a d + b c` vanish together only
when `a` and `b`, or `c` and `d`, are both zero. -/
theorem lin_zero {a b c d : Rat} (hab : a * a + b * b ≠ 0) (h1 : a * c - b * d = 0)
    (h2 : a * d + b * c = 0) : c = 0 ∧ d = 0 := by
  have e1 : (a * a + b * b) * c = 0 := by grind
  have e2 : (a * a + b * b) * d = 0 := by grind
  rcases Rat.mul_eq_zero.1 e1 with h | h
  · exact absurd h hab
  rcases Rat.mul_eq_zero.1 e2 with h' | h'
  · exact absurd h' hab
  exact ⟨h, h'⟩

theorem sq_ne_of {a b : Rat} (h : ¬ (a = 0 ∧ b = 0)) : a * a + b * b ≠ 0 := by
  intro hs
  apply h
  have ha : 0 ≤ a * a := by
    rcases Rat.le_total (a := (0 : Rat)) (b := a) with h | h
    · exact Rat.mul_nonneg h h
    · have := Rat.mul_nonneg (show 0 ≤ -a by grind) (show 0 ≤ -a by grind); grind
  have hb : 0 ≤ b * b := by
    rcases Rat.le_total (a := (0 : Rat)) (b := b) with h | h
    · exact Rat.mul_nonneg h h
    · have := Rat.mul_nonneg (show 0 ≤ -b by grind) (show 0 ≤ -b by grind); grind
  have haa : a * a = 0 := by grind
  have hbb : b * b = 0 := by grind
  exact ⟨by rcases Rat.mul_eq_zero.1 haa with h | h <;> exact h,
    by rcases Rat.mul_eq_zero.1 hbb with h | h <;> exact h⟩

theorem unit_sq {p : F64} (hp : Unit p) (h : p.toRat * p.toRat = 1) : p.toRat ≠ 0 := by
  intro h0; rw [h0, Rat.zero_mul] at h; exact absurd h (by decide)

theorem toRat_ne_of_nonzero {x : F64} (hf : x.isFinite = true) (hz : x.isZero = false) :
    x.toRat ≠ 0 := by
  intro h; rw [(isZero_iff_toRat hf).2 h] at hz; cases hz

/-- The recomputation of `_Py_c_prod` (:141-144): with finite factors, one pair of them units,
and neither factor zero, `INFINITY*(a*c - b*d)` or `INFINITY*(a*d + b*c)` is an infinity. -/
theorem prod_recov {a b c d : F64} (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hc : c.isFinite = true) (hd : d.isFinite = true) (hu : (Unit a ∧ Unit b) ∨ (Unit c ∧ Unit d))
    (hab : ¬ (a.toRat = 0 ∧ b.toRat = 0)) (hcd : ¬ (c.toRat = 0 ∧ d.toRat = 0)) :
    ((F64.mul (F64.inf false) (F64.sub (F64.mul a c) (F64.mul b d))).isInf ||
      (F64.mul (F64.inf false) (F64.add (F64.mul a d) (F64.mul b c))).isInf) = true := by
  have hp : ∀ {x y : F64}, x.isFinite = true → y.isFinite = true →
      (x = a ∨ x = b) → (y = c ∨ y = d) →
      (F64.mul x y).isFinite = true ∧ (F64.mul x y).toRat = x.toRat * y.toRat := by
    intro x y hx hy hxa hyc
    rcases hu with ⟨ua, ub⟩ | ⟨uc, ud⟩
    · rcases hxa with rfl | rfl
      · exact mul_unit_l ua hy
      · exact mul_unit_l ub hy
    · rcases hyc with rfl | rfl
      · exact mul_unit_r hx uc
      · exact mul_unit_r hx ud
  obtain ⟨f1, v1⟩ := hp ha hc (Or.inl rfl) (Or.inl rfl)
  obtain ⟨f2, v2⟩ := hp hb hd (Or.inr rfl) (Or.inr rfl)
  obtain ⟨f3, v3⟩ := hp ha hd (Or.inl rfl) (Or.inr rfl)
  obtain ⟨f4, v4⟩ := hp hb hc (Or.inr rfl) (Or.inl rfl)
  have f2n : (F64.mul b d).neg.isFinite = true := by rw [neg_isFinite]; exact f2
  have n1 : (F64.sub (F64.mul a c) (F64.mul b d)).isNaN = false := add_fin_notNaN f1 f2n
  have n2 : (F64.add (F64.mul a d) (F64.mul b c)).isNaN = false := add_fin_notNaN f3 f4
  apply Classical.byContradiction
  intro hno
  have hz1 : (F64.sub (F64.mul a c) (F64.mul b d)).isZero = true := by
    cases hz : (F64.sub (F64.mul a c) (F64.mul b d)).isZero
    · exact absurd (by simp [inf_mul_isInf n1 hz]) hno
    · rfl
  have hz2 : (F64.add (F64.mul a d) (F64.mul b c)).isZero = true := by
    cases hz : (F64.add (F64.mul a d) (F64.mul b c)).isZero
    · exact absurd (by simp [inf_mul_isInf n2 hz]) hno
    · rfl
  have e1 := add_isZero_exact f1 f2n hz1
  have e2 := add_isZero_exact f3 f4 hz2
  rw [toRat_neg, v1, v2] at e1
  rw [v3, v4] at e2
  have := lin_zero (sq_ne_of hab) (by grind) e2
  exact hcd this

/-- C11 Annex G.5.1, which complexobject.c:96-97 cites: if one operand of `*` is an infinity
(a part is infinite, whatever the other part) and the other is a nonzero number with no NaN
part, finite or infinite, the product is an infinity (a part is infinite). The plain product
`(ac - bd) + (ad + bc)j` already has an infinite part, or it is `nan+nanj` and the boxing of
:101-124 and the recomputation of :141-144 make one; for every such input, at binary64. A
version without the recovery fails at `complex(inf, inf) * complex(1, 1)`. The overflow
branch (:125-140) is not covered here. -/
def ProdAnnexG : Prop :=
  ∀ z w : C,
    ((z.re.isInf || z.im.isInf) = true → (w.re.isNaN || w.im.isNaN) = false →
      (w.re.isZero && w.im.isZero) = false →
      ((_Py_c_prod z w).re.isInf || (_Py_c_prod z w).im.isInf) = true) ∧
    ((w.re.isInf || w.im.isInf) = true → (z.re.isNaN || z.im.isNaN) = false →
      (z.re.isZero && z.im.isZero) = false →
      ((_Py_c_prod z w).re.isInf || (_Py_c_prod z w).im.isInf) = true)

theorem unit_of_finite_box {x : F64} : Unit (boxInf x) := boxInf_unit x

theorem box_pair_ne {x y : F64} (h : (x.isInf || y.isInf) = true) :
    ¬ ((boxInf x).toRat = 0 ∧ (boxInf y).toRat = 0) := by
  intro ⟨h1, h2⟩
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · have := boxInf_inf h; rw [h1, Rat.zero_mul] at this; exact absurd this (by decide)
  · have := boxInf_inf h; rw [h2, Rat.zero_mul] at this; exact absurd this (by decide)

theorem fin_pair_ne {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (h : (x.isZero && y.isZero) = false) : ¬ (x.toRat = 0 ∧ y.toRat = 0) := by
  intro ⟨h1, h2⟩
  rw [(isZero_iff_toRat hx).2 h1, (isZero_iff_toRat hy).2 h2] at h
  cases h

theorem fin_of_not {x : F64} (hn : x.isNaN = false) (hi : x.isInf = false) : x.isFinite = true := by
  rcases classify x with h | h | h
  · exact h
  · rw [hi] at h; cases h
  · rw [hn] at h; cases h

theorem box_notNaN (x : F64) : (boxInf x).isNaN = false := isNaN_false_of_finite (boxInf_unit x).1

theorem prod_nonfin_z {a b c d : F64} (h : (a.isInf || b.isInf) = true) :
    (fsub (fmul a c) (fmul b d)).isFinite = false ∧ (fadd (fmul a d) (fmul b c)).isFinite = false := by
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · exact ⟨sub_nonfin_l (mul_inf_l h), add_nonfin_l (mul_inf_l h)⟩
  · exact ⟨sub_nonfin_r (mul_inf_l h), add_nonfin_r (mul_inf_l h)⟩

theorem prod_nonfin_w {a b c d : F64} (h : (c.isInf || d.isInf) = true) :
    (fsub (fmul a c) (fmul b d)).isFinite = false ∧ (fadd (fmul a d) (fmul b c)).isFinite = false := by
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · exact ⟨sub_nonfin_l (mul_inf_r h), add_nonfin_r (mul_inf_r h)⟩
  · exact ⟨sub_nonfin_r (mul_inf_r h), add_nonfin_l (mul_inf_r h)⟩

/-- Two non-finite parts that are not both NaN include an infinity. -/
theorem inf_of_nonfin {x y : F64} (hx : x.isFinite = false) (hy : y.isFinite = false)
    (h : (x.isNaN && y.isNaN) = false) : (x.isInf || y.isInf) = true := by
  rcases nonfin_cases hx with h1 | h1
  · simp [h1]
  · rcases nonfin_cases hy with h2 | h2
    · simp [h2]
    · rw [h1, h2] at h; cases h

theorem prodAnnexG_proven : ProdAnnexG := by
  intro z w
  obtain ⟨a0, b0⟩ := z
  obtain ⟨c0, e0⟩ := w
  simp only
  constructor
  · intro hz hw hw0
    have hcn : c0.isNaN = false := by simp only [Bool.or_eq_false_iff] at hw; exact hw.1
    have hen : e0.isNaN = false := by simp only [Bool.or_eq_false_iff] at hw; exact hw.2
    obtain ⟨n1, n2⟩ := prod_nonfin_z (c := c0) (d := e0) hz
    unfold _Py_c_prod
    dsimp only
    by_cases hb : ((fsub (fmul a0 c0) (fmul b0 e0)).isNaN && (fadd (fmul a0 e0) (fmul b0 c0)).isNaN) = true
    · simp only [hb, ite_true, hz, nanToZero_of hcn, nanToZero_of hen, Bool.true_or, Bool.not_true,
        Bool.false_and, Bool.or_false]
      by_cases hwi : (c0.isInf || e0.isInf) = true
      · simp only [hwi, ite_true, nanToZero_of (box_notNaN a0), nanToZero_of (box_notNaN b0)]
        exact prod_recov (boxInf_unit _).1 (boxInf_unit _).1 (boxInf_unit _).1 (boxInf_unit _).1
          (Or.inl ⟨boxInf_unit _, boxInf_unit _⟩) (box_pair_ne hz) (box_pair_ne hwi)
      · have hwi' : (c0.isInf || e0.isInf) = false := by simpa using hwi
        simp only [hwi', Bool.false_eq_true, ite_false]
        have hci : c0.isInf = false := by simp only [Bool.or_eq_false_iff] at hwi'; exact hwi'.1
        have hei : e0.isInf = false := by simp only [Bool.or_eq_false_iff] at hwi'; exact hwi'.2
        exact prod_recov (boxInf_unit _).1 (boxInf_unit _).1 (fin_of_not hcn hci) (fin_of_not hen hei)
          (Or.inl ⟨boxInf_unit _, boxInf_unit _⟩) (box_pair_ne hz)
          (fin_pair_ne (fin_of_not hcn hci) (fin_of_not hen hei) hw0)
    · have hb' : ((fsub (fmul a0 c0) (fmul b0 e0)).isNaN && (fadd (fmul a0 e0) (fmul b0 c0)).isNaN) = false := by
        simpa using hb
      simp only [hb', Bool.false_eq_true, ite_false]
      exact inf_of_nonfin n1 n2 hb'
  · intro hwi hz hz0
    have han : a0.isNaN = false := by simp only [Bool.or_eq_false_iff] at hz; exact hz.1
    have hbn : b0.isNaN = false := by simp only [Bool.or_eq_false_iff] at hz; exact hz.2
    obtain ⟨n1, n2⟩ := prod_nonfin_w (a := a0) (b := b0) hwi
    unfold _Py_c_prod
    dsimp only
    by_cases hb : ((fsub (fmul a0 c0) (fmul b0 e0)).isNaN && (fadd (fmul a0 e0) (fmul b0 c0)).isNaN) = true
    · simp only [hb, ite_true]
      by_cases hzi : (a0.isInf || b0.isInf) = true
      · have hc1 : ((nanToZero c0).isInf || (nanToZero e0).isInf) = true := by
          rcases Bool.or_eq_true _ _ ▸ hwi with h | h
          · have : c0.isNaN = false := not_nan_of_inf h
            simp [nanToZero_of this, h]
          · have : e0.isNaN = false := not_nan_of_inf h
            simp [nanToZero_of this, h]
        simp only [hzi, ite_true, hc1, nanToZero_of (box_notNaN a0), nanToZero_of (box_notNaN b0),
          Bool.true_or, Bool.not_true, Bool.false_and, Bool.or_false]
        exact prod_recov (boxInf_unit _).1 (boxInf_unit _).1 (boxInf_unit _).1 (boxInf_unit _).1
          (Or.inl ⟨boxInf_unit _, boxInf_unit _⟩) (box_pair_ne hzi) (box_pair_ne hc1)
      · have hzi' : (a0.isInf || b0.isInf) = false := by simpa using hzi
        have hai : a0.isInf = false := by simp only [Bool.or_eq_false_iff] at hzi'; exact hzi'.1
        have hbi : b0.isInf = false := by simp only [Bool.or_eq_false_iff] at hzi'; exact hzi'.2
        simp only [hzi', Bool.false_eq_true, ite_false, hwi, ite_true, nanToZero_of han,
          nanToZero_of hbn, Bool.false_or, Bool.not_true, Bool.false_and, Bool.or_false]
        exact prod_recov (fin_of_not han hai) (fin_of_not hbn hbi) (boxInf_unit _).1 (boxInf_unit _).1
          (Or.inr ⟨boxInf_unit _, boxInf_unit _⟩)
          (fin_pair_ne (fin_of_not han hai) (fin_of_not hbn hbi) hz0) (box_pair_ne hwi)
    · have hb' : ((fsub (fmul a0 c0) (fmul b0 e0)).isNaN && (fadd (fmul a0 e0) (fmul b0 c0)).isNaN) = false := by
        simpa using hb
      simp only [hb', Bool.false_eq_true, ite_false]
      exact inf_of_nonfin n1 n2 hb'

end PyLean.Binary64
