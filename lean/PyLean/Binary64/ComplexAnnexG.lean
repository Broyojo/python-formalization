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

end PyLean.Binary64
