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
version without the recovery fails at `complex(inf, nan) * complex(1, 0)`, whose plain product
is `nan+nanj` and whose result is `inf+nanj`. The overflow
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

/-! ## Division -/

theorem inf_notZero {x : F64} (h : x.isInf = true) : x.isZero = false := by
  cases hz : x.isZero
  · rfl
  · rw [isInf_false_of_finite (isFinite_of_isZero hz)] at h; cases h

theorem absLt_inf {x : F64} (h : x.isInf = true) : absLt x = F64.inf false := by
  unfold absLt
  have hl : F64.lt x d0 = x.sign := by
    have hn := not_nan_of_inf h
    have h0 : d0.isNaN = false := isNaN_false_of_finite d0_isFinite
    have h0i : d0.isInf = false := isInf_false_of_finite d0_isFinite
    simp [F64.lt, hn, h0, h, h0i]
  rw [hl]
  have hx := eq_inf_of_isInf h
  cases hs : x.sign
  · simp only [Bool.false_eq_true, ite_false]; rw [hx, hs]
  · simp only [ite_true]; rw [hx, hs, MathInt.neg_inf]; rfl

theorem absLt_nan {x : F64} (h : x.isNaN = true) : absLt x = x := by
  unfold absLt
  simp [F64.lt, h]

theorem absLt_fin {x : F64} (h : x.isFinite = true) :
    (absLt x).isFinite = true ∧ (absLt x).toRat = Rat.abs x.toRat := by
  unfold absLt
  rw [lt_of_finite h d0_isFinite, d0_toRat]
  by_cases hl : x.toRat < 0
  · simp only [hl, decide_true, ite_true]
    rw [neg_isFinite, toRat_neg, abs_of_nonpos (Rat.le_of_lt hl)]
    exact ⟨h, rfl⟩
  · simp only [hl, decide_false, Bool.false_eq_true, ite_false]
    exact ⟨h, (abs_of_nonneg (by grind)).symm⟩

theorem ge_fin {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    F64.ge x y = decide (y.toRat ≤ x.toRat) := by
  unfold F64.ge F64.le
  rw [lt_of_finite hy hx, eq_of_finite hy hx]
  by_cases h : y.toRat < x.toRat
  · simp [h, Rat.le_of_lt h]
  · by_cases h' : y.toRat = x.toRat
    · simp [h', Rat.le_refl]
    · simp only [h, h', decide_false, Bool.or_false]
      symm
      simp only [decide_eq_false_iff_not]
      intro hle
      rcases Rat.le_iff_lt_or_eq.1 hle with h2 | h2
      · exact h h2
      · exact h' h2

theorem ge_inf_fin {y : F64} (hy : y.isFinite = true) : F64.ge (F64.inf false) y = true := by
  have hn := isNaN_false_of_finite hy
  have hi := isInf_false_of_finite hy
  simp [F64.ge, F64.le, F64.lt, hn, hi, inf_isNaN, inf_isInf, (MathInt.inf_bits false).2]

theorem ge_fin_inf {y : F64} (hy : y.isFinite = true) : F64.ge y (F64.inf false) = false := by
  have hn := isNaN_false_of_finite hy
  have hi := isInf_false_of_finite hy
  simp [F64.ge, F64.le, F64.lt, F64.eq, hn, hi, inf_isNaN, inf_isInf, (MathInt.inf_bits false).2]

theorem ge_nan_l {x y : F64} (h : x.isNaN = true) : F64.ge x y = false := by
  simp [F64.ge, F64.le, F64.lt, F64.eq, h]

theorem ge_nan_r {x y : F64} (h : y.isNaN = true) : F64.ge x y = false := by
  simp [F64.ge, F64.le, F64.lt, F64.eq, h]

theorem ge_inf_inf : F64.ge (F64.inf false) (F64.inf false) = true := by decide +kernel

theorem eq_inf_d0 : F64.eq (F64.inf false) d0 = false := by decide +kernel

theorem div_fin_inf {x y : F64} (hx : x.isFinite = true) (hy : y.isInf = true) :
    F64.div x y = F64.zero (x.sign != y.sign) := (div_spec x y (inf_notZero hy)).infR hx hy

theorem add_inf_fin {x y : F64} (hx : x.isInf = true) (hy : y.isFinite = true) : F64.add x y = x :=
  (add_spec x y).infL hx (isNaN_false_of_finite hy) (fun h => by
    rw [isInf_false_of_finite hy] at h; cases h)

theorem add_fin_inf {x y : F64} (hx : x.isFinite = true) (hy : y.isInf = true) : F64.add x y = y :=
  (add_spec x y).infR hx hy

theorem add_zero_fin {x : F64} (hx : x.isFinite = true) (t : Bool) :
    (F64.add x (F64.zero t)).isFinite = true := by
  rw [add_of_finite hx (zero_isFinite t), zero_toRat, Rat.add_zero]
  split
  · exact zero_isFinite _
  · rename_i h
    have hz : x.isZero = false := by
      cases hh : x.isZero
      · rfl
      · exact absurd (toRat_of_isZero hh) h
    rw [ofRat_toRat hx hz]; exact hx

theorem zero_add_fin {x : F64} (hx : x.isFinite = true) (t : Bool) :
    (F64.add (F64.zero t) x).isFinite = true := by
  rw [add_of_finite (zero_isFinite t) hx, zero_toRat, Rat.zero_add]
  split
  · exact zero_isFinite _
  · rename_i h
    have hz : x.isZero = false := by
      cases hh : x.isZero
      · rfl
      · exact absurd (toRat_of_isZero hh) h
    rw [ofRat_toRat hx hz]; exact hx

theorem neg_zero' (t : Bool) : (F64.zero t).neg = F64.zero (!t) := by cases t <;> decide +kernel

theorem div_nan_l {x y : F64} (h : x.isNaN = true) : (F64.div x y).isNaN = true := by
  simp [F64.div, h, qnan_isNaN]

theorem div_nan_r {x y : F64} (h : y.isNaN = true) : (F64.div x y).isNaN = true := by
  simp [F64.div, h, qnan_isNaN]

theorem mul_nan_r {x y : F64} (h : y.isNaN = true) : (F64.mul x y).isNaN = true := by
  simp [F64.mul, h, qnan_isNaN]

theorem add_nan_r {x y : F64} (h : y.isNaN = true) : (F64.add x y).isNaN = true := by
  simp [F64.add, h, qnan_isNaN]

theorem add_nan_l {x y : F64} (h : x.isNaN = true) : (F64.add x y).isNaN = true := by
  simp [F64.add, h, qnan_isNaN]

theorem div_inf_inf {x y : F64} (hx : x.isInf = true) (hy : y.isInf = true) :
    (F64.div x y).isNaN = true := (div_spec x y (inf_notZero hy)).infInf hx hy

/-- `0.0 * e` is a zero for every finite `e`. -/
theorem d0_mul_zero {e : F64} (he : e.isFinite = true) : (F64.mul d0 e).isZero = true := by
  rw [mul_of_finite d0_isFinite he, d0_toRat, Rat.zero_mul, if_pos rfl]
  exact zero_isZero _

theorem lin_zero2 {x y c d : Rat} (hxy : x * x + y * y ≠ 0) (h1 : x * c + y * d = 0)
    (h2 : y * c - x * d = 0) : c = 0 ∧ d = 0 := by
  have e1 : (x * x + y * y) * c = 0 := by grind
  have e2 : (x * x + y * y) * d = 0 := by grind
  rcases Rat.mul_eq_zero.1 e1 with h | h
  · exact absurd h hxy
  rcases Rat.mul_eq_zero.1 e2 with h' | h'
  · exact absurd h' hxy
  exact ⟨h, h'⟩

/-- The recomputation of `_Py_c_quot` for an infinite dividend (:230-233). -/
theorem quot_recov {x y c d : F64} (ux : Unit x) (uy : Unit y) (hc : c.isFinite = true)
    (hd : d.isFinite = true) (hxy : ¬ (x.toRat = 0 ∧ y.toRat = 0)) (hcd : ¬ (c.toRat = 0 ∧ d.toRat = 0)) :
    ((F64.mul (F64.inf false) (F64.add (F64.mul x c) (F64.mul y d))).isInf ||
      (F64.mul (F64.inf false) (F64.sub (F64.mul y c) (F64.mul x d))).isInf) = true := by
  obtain ⟨f1, v1⟩ := mul_unit_l ux hc
  obtain ⟨f2, v2⟩ := mul_unit_l uy hd
  obtain ⟨f3, v3⟩ := mul_unit_l uy hc
  obtain ⟨f4, v4⟩ := mul_unit_l ux hd
  have f4n : (F64.mul x d).neg.isFinite = true := by rw [neg_isFinite]; exact f4
  have n1 : (F64.add (F64.mul x c) (F64.mul y d)).isNaN = false := add_fin_notNaN f1 f2
  have n2 : (F64.sub (F64.mul y c) (F64.mul x d)).isNaN = false := add_fin_notNaN f3 f4n
  apply Classical.byContradiction
  intro hno
  have hz1 : (F64.add (F64.mul x c) (F64.mul y d)).isZero = true := by
    cases hz : (F64.add (F64.mul x c) (F64.mul y d)).isZero
    · exact absurd (by simp [inf_mul_isInf n1 hz]) hno
    · rfl
  have hz2 : (F64.sub (F64.mul y c) (F64.mul x d)).isZero = true := by
    cases hz : (F64.sub (F64.mul y c) (F64.mul x d)).isZero
    · exact absurd (by simp [inf_mul_isInf n2 hz]) hno
    · rfl
  have e1 := add_isZero_exact f1 f2 hz1
  have e2 := add_isZero_exact f3 f4n hz2
  rw [v1, v2] at e1
  rw [toRat_neg, v3, v4] at e2
  exact hcd (lin_zero2 (sq_ne_of hxy) e1 (by grind))

theorem add_fin_small {u v : F64} (hu : u.isFinite = true) (hv : v.isFinite = true)
    (h : Rat.abs (u.toRat + v.toRat) < overflowLimit) : (F64.add u v).isFinite = true := by
  have hr := (add_spec u v).round hu hv
  rcases classify (F64.add u v) with h' | h' | h'
  · exact h'
  · exact absurd (hr.inf.1 h') (Rat.not_le.2 h)
  · rw [hr.notNaN] at h'; cases h'

theorem zero_notNaN (t : Bool) : (F64.zero t).isNaN = false := isNaN_false_of_finite (zero_isFinite t)

theorem zero_div_inf {y : F64} (hy : y.isInf = true) (t : Bool) :
    (F64.div (F64.zero t) y).isZero = true := by
  rw [div_fin_inf (zero_isFinite t) hy]; exact zero_isZero _

theorem fin_div_inf_zero {x y : F64} (hx : x.isFinite = true) (hy : y.isInf = true) :
    (F64.div x y).isZero = true := by
  rw [div_fin_inf hx hy]; exact zero_isZero _

theorem isZero_notNaN {x : F64} (h : x.isZero = true) : x.isNaN = false :=
  isNaN_false_of_finite (isFinite_of_isZero h)

theorem box_fin_toRat {x : F64} (h : x.isInf = false) : (boxInf x).toRat = 0 := boxInf_fin h

/-- C11 Annex G.5.2 for `_Py_rc_quot` (complexobject.c:265-304): a finite float over a complex
with an infinite part gives a zero in both parts, for every such divisor: through Smith's
branches when the other part is finite, through the recovery of :294-301 when it is infinite
or a NaN. `errno` is left alone. -/
def RcQuotZero : Prop :=
  ∀ (a : F64) (b : C), a.isFinite = true → (b.re.isInf || b.im.isInf) = true →
    (_Py_rc_quot a b).1.re.isZero = true ∧ (_Py_rc_quot a b).1.im.isZero = true ∧
      (_Py_rc_quot a b).2 = false

theorem rcQuotZero_proven : RcQuotZero := by
  intro a b ha hb
  obtain ⟨br, bi⟩ := b
  simp only at hb ⊢
  have han : a.neg.isFinite = true := by rw [neg_isFinite]; exact ha
  -- the recovery: both parts are `0.0 * (finite)`
  have hrec : ∀ x y : F64, Unit x → Unit y →
      (F64.mul d0 (F64.mul a x)).isZero = true ∧ (F64.mul d0 (F64.mul a.neg y)).isZero = true :=
    fun x y ux uy => ⟨d0_mul_zero (mul_unit_r ha ux).1, d0_mul_zero (mul_unit_r han uy).1⟩
  unfold _Py_rc_quot
  dsimp only
  simp only [fdiv, fmul, fadd, fsub]
  by_cases hri : br.isInf = true
  · rw [absLt_inf hri]
    rcases classify bi with hif | hii | hin
    · obtain ⟨fi, _⟩ := absLt_fin hif
      simp only [ge_inf_fin fi, ite_true, eq_inf_d0, Bool.false_eq_true, ite_false]
      rw [div_fin_inf hif hri, mul_zero_of_finite hif, add_inf_fin hri (zero_isFinite _),
        mul_zero_of_finite han]
      have z1 := fin_div_inf_zero ha hri
      have z2 := zero_div_inf hri (a.neg.sign != (bi.sign != br.sign))
      simp only [isZero_notNaN z1, Bool.false_and, Bool.false_eq_true, ite_false]
      exact ⟨z1, z2, by simp⟩
    · rw [absLt_inf hii]
      simp only [ge_inf_inf, ite_true, eq_inf_d0, Bool.false_eq_true, ite_false]
      have hr : (F64.div bi br).isNaN = true := div_inf_inf hii hri
      have hd : (F64.add br (F64.mul bi (F64.div bi br))).isNaN = true :=
        add_nan_r (mul_nan_r hr)
      simp only [div_nan_r hd, ha, inf_isInf, Bool.true_and, Bool.true_or, ite_true]
      exact ⟨(hrec (boxInf br) (boxInf bi) (boxInf_unit br) (boxInf_unit bi)).1,
        (hrec (boxInf br) (boxInf bi) (boxInf_unit br) (boxInf_unit bi)).2, by simp⟩
    · rw [absLt_nan hin]
      simp only [ge_nan_r hin, ge_nan_l hin, Bool.false_eq_true, ite_false, qnan_isNaN, ha,
        inf_isInf, Bool.true_and, Bool.true_or, ite_true]
      exact ⟨(hrec (boxInf br) (boxInf bi) (boxInf_unit br) (boxInf_unit bi)).1,
        (hrec (boxInf br) (boxInf bi) (boxInf_unit br) (boxInf_unit bi)).2, by simp⟩
  · have hri' : br.isInf = false := by simpa using hri
    have hii : bi.isInf = true := by simpa [hri'] using hb
    rw [absLt_inf hii]
    rcases classify br with hrf | hrr | hrn
    · obtain ⟨fr, _⟩ := absLt_fin hrf
      simp only [ge_fin_inf fr, Bool.false_eq_true, ite_false, ge_inf_fin fr, ite_true]
      rw [div_fin_inf hrf hii, mul_zero_of_finite hrf, add_fin_inf (zero_isFinite _) hii,
        mul_zero_of_finite ha]
      have z1 := zero_div_inf hii (a.sign != (br.sign != bi.sign))
      have z2 := fin_div_inf_zero han hii
      simp only [isZero_notNaN z1, Bool.false_and, Bool.false_eq_true, ite_false]
      exact ⟨z1, z2, by simp⟩
    · rw [hri'] at hrr; cases hrr
    · rw [absLt_nan hrn]
      simp only [ge_nan_l hrn, ge_nan_r hrn, Bool.false_eq_true, ite_false, qnan_isNaN, ha,
        inf_isInf, Bool.true_and, Bool.or_true, ite_true]
      exact ⟨(hrec (boxInf br) (boxInf bi) (boxInf_unit br) (boxInf_unit bi)).1,
        (hrec (boxInf br) (boxInf bi) (boxInf_unit br) (boxInf_unit bi)).2, by simp⟩

theorem not_nan_of_inf' {x : F64} (h : x.isNaN = true) : x.isInf = false := by
  cases hi : x.isInf
  · rfl
  · rw [not_nan_of_inf hi] at h; cases h

theorem lt_of_le_lt' {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by grind

theorem abs_mul_unit (q : Rat) {u : F64} (hu : Unit u) : Rat.abs (q * u.toRat) ≤ Rat.abs q := by
  rcases hu.2 with h | h | h <;> rw [h]
  · rw [Rat.mul_one]; exact Rat.le_refl
  · rw [show q * -1 = -q by grind, abs_neg]; exact Rat.le_refl
  · rw [Rat.mul_zero, abs_of_nonneg (a := 0) (by decide)]; exact abs_nonneg _

/-- The second recovery of `_Py_c_quot` (:235-241) when one boxed factor is a zero. -/
theorem rec2_zero {ar ai x y : F64} (har : ar.isFinite = true) (hai : ai.isFinite = true)
    (ux : Unit x) (uy : Unit y) (h0 : x.toRat = 0 ∨ y.toRat = 0) :
    (F64.mul d0 (F64.add (F64.mul ar x) (F64.mul ai y))).isZero = true ∧
      (F64.mul d0 (F64.sub (F64.mul ai x) (F64.mul ar y))).isZero = true := by
  obtain ⟨f1, v1⟩ := mul_unit_r har ux
  obtain ⟨f2, v2⟩ := mul_unit_r hai uy
  obtain ⟨f3, v3⟩ := mul_unit_r hai ux
  obtain ⟨f4, v4⟩ := mul_unit_r har uy
  have f4n : (F64.mul ar y).neg.isFinite = true := by rw [neg_isFinite]; exact f4
  have lr := abs_toRat_lt har
  have li := abs_toRat_lt hai
  have m1 := abs_mul_unit ar.toRat ux
  have m2 := abs_mul_unit ai.toRat uy
  have m3 := abs_mul_unit ai.toRat ux
  have m4 := abs_mul_unit ar.toRat uy
  refine ⟨d0_mul_zero (add_fin_small f1 f2 ?_), d0_mul_zero (add_fin_small f3 f4n ?_)⟩
  · rw [v1, v2]
    rcases h0 with h | h
    · rw [h, Rat.mul_zero, Rat.zero_add]; exact (lt_of_le_lt' m2 li)
    · rw [h, Rat.mul_zero, Rat.add_zero]; exact (lt_of_le_lt' m1 lr)
  · rw [toRat_neg, v3, v4]
    rcases h0 with h | h
    · rw [h, Rat.mul_zero, Rat.zero_add, abs_neg]
      exact (lt_of_le_lt' m4 lr)
    · rw [h, Rat.mul_zero, Rat.neg_zero, Rat.add_zero]; exact (lt_of_le_lt' m3 li)

theorem ge_total_fin {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (h : F64.ge x y = false) : F64.ge y x = true := by
  rw [ge_fin hx hy] at h
  rw [ge_fin hy hx]
  simp only [decide_eq_false_iff_not] at h
  simp only [decide_eq_true_eq]
  exact Rat.le_of_lt (Rat.not_le.1 h)

/-- C11 Annex G.5.2, which complexobject.c:224-225 cites, for `_Py_c_quot`, at binary64, for
every input of each kind:

* an infinite dividend (a part is infinite, whatever the other part) over a nonzero finite
  divisor gives an infinity (a part is infinite), and no `EDOM`: Smith's quotient (:195-222)
  already has an infinite part or it is `nan+nanj` and the recovery of :226-234 makes one;
* a finite dividend over a divisor with one infinite part gives a zero in both parts, through
  Smith's branches when the other part is finite and through the recovery of :235-241 when it
  is a NaN.

When both parts of the divisor are infinite, the recovery computes `0.0 * (a.real*x +
a.imag*y)` with `x` and `y` both `±1`, and the sum can overflow: `complex(1e308, 1e308) /
complex(inf, inf)` is `nan+0j`, as in the C11 reference `_Cdivd`. That case is left out. -/
def QuotAnnexG : Prop :=
  ∀ a b : C,
    ((a.re.isInf || a.im.isInf) = true → b.re.isFinite = true → b.im.isFinite = true →
      (b.re.isZero && b.im.isZero) = false →
      ((_Py_c_quot a b).1.re.isInf || (_Py_c_quot a b).1.im.isInf) = true ∧
        (_Py_c_quot a b).2 = false) ∧
    (a.re.isFinite = true → a.im.isFinite = true → (b.re.isInf || b.im.isInf) = true →
      (b.re.isInf && b.im.isInf) = false →
      (_Py_c_quot a b).1.re.isZero = true ∧ (_Py_c_quot a b).1.im.isZero = true ∧
        (_Py_c_quot a b).2 = false)

theorem quotAnnexG_proven : QuotAnnexG := by
  intro a b
  obtain ⟨ar, ai⟩ := a
  obtain ⟨br, bi⟩ := b
  simp only
  constructor
  · intro hz hbr hbi hb0
    obtain ⟨fr, vr⟩ := absLt_fin hbr
    obtain ⟨fi, vi⟩ := absLt_fin hbi
    have hbz := fin_pair_ne hbr hbi hb0
    unfold _Py_c_quot
    dsimp only
    simp only [fdiv, fmul, fadd, fsub]
    by_cases h1 : F64.ge (absLt br) (absLt bi) = true
    · have h2 : F64.eq (absLt br) d0 = false := by
        have h1' := h1
        rw [ge_fin fr fi, vr, vi] at h1'
        rw [eq_of_finite fr d0_isFinite, vr, d0_toRat]
        simp only [decide_eq_true_eq] at h1'
        simp only [decide_eq_false_iff_not]
        intro h0
        apply hbz
        rw [h0] at h1'
        exact ⟨abs_le_zero (by rw [h0]; exact Rat.le_refl), abs_le_zero h1'⟩
      simp only [h1, ite_true, h2, Bool.false_eq_true, ite_false]
      have n1 : (F64.div (F64.add ar (F64.mul ai (F64.div bi br)))
          (F64.add br (F64.mul bi (F64.div bi br)))).isFinite = false := by
        apply div_nonfin_l
        rcases Bool.or_eq_true _ _ ▸ hz with h | h
        · exact add_nonfin_l (not_finite_of_inf h)
        · exact add_nonfin_r (mul_inf_l h)
      have n2 : (F64.div (F64.sub ai (F64.mul ar (F64.div bi br)))
          (F64.add br (F64.mul bi (F64.div bi br)))).isFinite = false := by
        apply div_nonfin_l
        rcases Bool.or_eq_true _ _ ▸ hz with h | h
        · exact sub_nonfin_r (mul_inf_l h)
        · exact sub_nonfin_l (not_finite_of_inf h)
      by_cases hb : ((F64.div (F64.add ar (F64.mul ai (F64.div bi br)))
          (F64.add br (F64.mul bi (F64.div bi br)))).isNaN &&
          (F64.div (F64.sub ai (F64.mul ar (F64.div bi br)))
          (F64.add br (F64.mul bi (F64.div bi br)))).isNaN) = true
      · simp only [hb, ite_true, hz, hbr, hbi, Bool.and_self, Bool.true_and]
        exact ⟨quot_recov (boxInf_unit ar) (boxInf_unit ai) hbr hbi (box_pair_ne hz) hbz, by simp⟩
      · have hb' : ((F64.div (F64.add ar (F64.mul ai (F64.div bi br)))
            (F64.add br (F64.mul bi (F64.div bi br)))).isNaN &&
            (F64.div (F64.sub ai (F64.mul ar (F64.div bi br)))
            (F64.add br (F64.mul bi (F64.div bi br)))).isNaN) = false := by simpa using hb
        simp only [hb', Bool.false_eq_true, ite_false]
        exact ⟨inf_of_nonfin n1 n2 hb', by simp⟩
    · have h1' : F64.ge (absLt br) (absLt bi) = false := by simpa using h1
      have h2 := ge_total_fin fr fi h1'
      simp only [h1', Bool.false_eq_true, ite_false, h2, ite_true]
      have n1 : (F64.div (F64.add (F64.mul ar (F64.div br bi)) ai)
          (F64.add (F64.mul br (F64.div br bi)) bi)).isFinite = false := by
        apply div_nonfin_l
        rcases Bool.or_eq_true _ _ ▸ hz with h | h
        · exact add_nonfin_l (mul_inf_l h)
        · exact add_nonfin_r (not_finite_of_inf h)
      have n2 : (F64.div (F64.sub (F64.mul ai (F64.div br bi)) ar)
          (F64.add (F64.mul br (F64.div br bi)) bi)).isFinite = false := by
        apply div_nonfin_l
        rcases Bool.or_eq_true _ _ ▸ hz with h | h
        · exact sub_nonfin_r (not_finite_of_inf h)
        · exact sub_nonfin_l (mul_inf_l h)
      by_cases hb : ((F64.div (F64.add (F64.mul ar (F64.div br bi)) ai)
          (F64.add (F64.mul br (F64.div br bi)) bi)).isNaN &&
          (F64.div (F64.sub (F64.mul ai (F64.div br bi)) ar)
          (F64.add (F64.mul br (F64.div br bi)) bi)).isNaN) = true
      · simp only [hb, ite_true, hz, hbr, hbi, Bool.and_self, Bool.true_and]
        exact ⟨quot_recov (boxInf_unit ar) (boxInf_unit ai) hbr hbi (box_pair_ne hz) hbz, by simp⟩
      · have hb' : ((F64.div (F64.add (F64.mul ar (F64.div br bi)) ai)
            (F64.add (F64.mul br (F64.div br bi)) bi)).isNaN &&
            (F64.div (F64.sub (F64.mul ai (F64.div br bi)) ar)
            (F64.add (F64.mul br (F64.div br bi)) bi)).isNaN) = false := by simpa using hb
        simp only [hb', Bool.false_eq_true, ite_false]
        exact ⟨inf_of_nonfin n1 n2 hb', by simp⟩
  · intro har hai hb hnb
    have hri0 : ar.isInf = false := isInf_false_of_finite har
    have hai0 : ai.isInf = false := isInf_false_of_finite hai
    unfold _Py_c_quot
    dsimp only
    simp only [fdiv, fmul, fadd, fsub]
    by_cases hri : br.isInf = true
    · have hii : bi.isInf = false := by simpa [hri] using hnb
      rw [absLt_inf hri]
      rcases classify bi with hif | hii' | hin
      · obtain ⟨fi, _⟩ := absLt_fin hif
        simp only [ge_inf_fin fi, ite_true, eq_inf_d0, Bool.false_eq_true, ite_false]
        rw [div_fin_inf hif hri, mul_zero_of_finite hif, add_inf_fin hri (zero_isFinite _),
          mul_zero_of_finite hai, mul_zero_of_finite har]
        have z1 := fin_div_inf_zero (add_zero_fin har (ai.sign != (bi.sign != br.sign))) hri
        have z2 : (F64.div (F64.sub ai (F64.zero (ar.sign != (bi.sign != br.sign)))) br).isZero = true := by
          apply fin_div_inf_zero _ hri
          show (F64.add ai (F64.zero _).neg).isFinite = true
          rw [neg_zero']; exact add_zero_fin hai _
        simp only [isZero_notNaN z1, Bool.false_and, Bool.false_eq_true, ite_false]
        exact ⟨z1, z2, by simp⟩
      · rw [hii] at hii'; cases hii'
      · rw [absLt_nan hin]
        simp only [ge_nan_r hin, ge_nan_l hin, Bool.false_eq_true, ite_false, qnan_isNaN, hri0, hai0,
          Bool.or_false, Bool.false_and, inf_isInf, Bool.true_or, har, hai, Bool.true_and, ite_true]
        obtain ⟨z1, z2⟩ := rec2_zero har hai (boxInf_unit br) (boxInf_unit bi)
          (Or.inr (boxInf_fin (not_nan_of_inf' hin)))
        exact ⟨z1, z2, by simp⟩
    · have hri' : br.isInf = false := by simpa using hri
      have hii : bi.isInf = true := by simpa [hri'] using hb
      rw [absLt_inf hii]
      rcases classify br with hrf | hrr | hrn
      · obtain ⟨fr, _⟩ := absLt_fin hrf
        simp only [ge_fin_inf fr, Bool.false_eq_true, ite_false, ge_inf_fin fr, ite_true]
        rw [div_fin_inf hrf hii, mul_zero_of_finite hrf, add_fin_inf (zero_isFinite _) hii,
          mul_zero_of_finite har, mul_zero_of_finite hai]
        have z1 := fin_div_inf_zero (zero_add_fin hai (ar.sign != (br.sign != bi.sign))) hii
        have z2 : (F64.div (F64.sub (F64.zero (ai.sign != (br.sign != bi.sign))) ar) bi).isZero = true := by
          apply fin_div_inf_zero _ hii
          show (F64.add (F64.zero _) ar.neg).isFinite = true
          exact zero_add_fin (by rw [neg_isFinite]; exact har) _
        simp only [isZero_notNaN z1, Bool.false_and, Bool.false_eq_true, ite_false]
        exact ⟨z1, z2, by simp⟩
      · rw [hri'] at hrr; cases hrr
      · rw [absLt_nan hrn]
        simp only [ge_nan_l hrn, ge_nan_r hrn, Bool.false_eq_true, ite_false, qnan_isNaN, hri0, hai0,
          Bool.or_false, Bool.false_and, inf_isInf, Bool.or_true, har, hai, Bool.true_and, ite_true]
        obtain ⟨z1, z2⟩ := rec2_zero har hai (boxInf_unit br) (boxInf_unit bi)
          (Or.inl (boxInf_fin (not_nan_of_inf' hrn)))
        exact ⟨z1, z2, by simp⟩

end PyLean.Binary64
