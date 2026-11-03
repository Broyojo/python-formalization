import PyLean.MathInt.FltGammaVal
import PyLean.MathInt.FltRemainder

/-!
# `m_sinpi` and the sign of `gamma`

`m_sinpi(x)` (Modules/mathmodule.c:222-254) reduces `|x|` modulo 2 (`fmod`, exact), picks one of
five arguments of `sin` or `cos` in `[-pi/4, pi/4]` by `n = round(2y)`, and puts the sign of `x`
back. For a non-integer `x` the result is nonzero with the sign of `sin(pi*x)`, for every C `sin`
and `cos` that have the sign of the mathematical functions on `[-1, 1]`; the reductions `y - 0.5`,
`1.0 - y`, `y - 1.5` and `y - 2.0` stay in `[-1/4, 1/4]` (the second and last are exact by
Sterbenz's lemma, as the comment at :241-242 needs for `y == 1.0`).

`m_tgamma` (:445-449) returns `0.0/m_sinpi(x)` for `x < -200`: a zero carrying the sign of
`Gamma(x)`, which is negative exactly when `floor(-x)` is even.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- A C `sin` and `cos` with the sign of the mathematical functions on `[-1, 1]`, finite there and
leaving `errno` alone (`sin t > 0` for `0 < t <= 1`, `sin t < 0` for `-1 <= t < 0`, `cos t > 0`
for `|t| <= 1`; any implementation within a few ulps has this). -/
def TrigSign (L : GammaLibm) : Prop :=
  (∀ t : F64, t.isFinite = true → 0 < t.toRat → t.toRat ≤ 1 →
      (L.sin t).1.isFinite = true ∧ 0 < (L.sin t).1.toRat ∧ (L.sin t).2 = .zero) ∧
  (∀ t : F64, t.isFinite = true → -1 ≤ t.toRat → t.toRat < 0 →
      (L.sin t).1.isFinite = true ∧ (L.sin t).1.toRat < 0 ∧ (L.sin t).2 = .zero) ∧
  (∀ t : F64, t.isFinite = true → -1 ≤ t.toRat → t.toRat ≤ 1 →
      (L.cos t).1.isFinite = true ∧ 0 < (L.cos t).1.toRat ∧ (L.cos t).2 = .zero)

/-- `math.gamma(x)` for every non-integer `x < -200` is a zero with the sign of `Gamma(x)`: `-0.0`
when `floor(-x)` is even, `0.0` when it is odd (C99 Annex F leaves the underflow to the
implementation; CPython's comment at :438-440 says it "underflows to +-0.0"). -/
def GammaUnderflowSign : Prop :=
  ∀ L : GammaLibm, TrigSign L → ∀ x : F64, x.isFinite = true → x.toRat < -200 →
    (∀ n : Int, x.toRat ≠ n) →
    math_gamma L (.float x) = .ok (F64.zero (decide ((-x.toRat).floor % 2 = 0)))

/-- `m_sinpi` for a non-integer: nonzero, with the sign of `sin(pi*x)`, and `errno` untouched. -/
def SinpiSign : Prop :=
  ∀ L : GammaLibm, TrigSign L → ∀ x : F64, x.isFinite = true → (∀ n : Int, x.toRat ≠ n) →
    ∀ e : Errno,
      (m_sinpi L x e).2 = e ∧ (m_sinpi L x e).1.isFinite = true ∧ (m_sinpi L x e).1.toRat ≠ 0 ∧
      ((m_sinpi L x e).1.toRat < 0 ↔ (x.sign = true ↔ (Rat.abs x.toRat).floor % 2 = 0))

/-! ## Bounds -/

theorem rnd_between {q lo hi : Rat} (rl : Rep binary64 lo) (rh : Rep binary64 hi)
    (ll : Rat.abs lo < overflowLimit) (lh : Rat.abs hi < overflowLimit) (h1 : lo ≤ q)
    (h2 : q ≤ hi) : (ofRat q).isFinite = true ∧ lo ≤ rnd q ∧ rnd q ≤ hi := by
  have fq : (ofRat q).isFinite = true := by
    apply (ofRat_isFinite _).2
    rw [abs_eq_ite q]; rw [abs_eq_ite lo] at ll; rw [abs_eq_ite hi] at lh
    split <;> split at ll <;> split at lh <;> grind
  have flo := (ofRat_isFinite lo).2 ll
  have fhi := (ofRat_isFinite hi).2 lh
  refine ⟨fq, ?_, ?_⟩
  · have := ofRat_mono h1 flo fq; rwa [ofRat_exact rl ll] at this
  · have := ofRat_mono h2 fq fhi; rwa [ofRat_exact rh lh] at this

theorem pi_mul_mid {p u : Rat} (hp0 : 0 ≤ p) (hp : p ≤ 4) (hu1 : -1 / 4 ≤ u) (hu2 : u ≤ 1 / 4) :
    -1 ≤ p * u ∧ p * u ≤ 1 := by
  by_cases h : 0 ≤ u
  · have := Rat.mul_le_mul_of_nonneg_right hp h
    have := Rat.mul_nonneg hp0 h
    constructor <;> grind
  · have h' : 0 ≤ -u := by grind
    have := Rat.mul_le_mul_of_nonneg_right hp h'
    have := Rat.mul_nonneg hp0 h'
    constructor <;> grind

theorem pi_mul_pos {p u : Rat} (hp1 : 1 ≤ p) (hp : p ≤ 4) (hu0 : 0 < u) (hu : u ≤ 1 / 4) :
    u ≤ p * u ∧ p * u ≤ 1 := by
  have := Rat.mul_le_mul_of_nonneg_right hp1 (Rat.le_of_lt hu0)
  have := Rat.mul_le_mul_of_nonneg_right hp (Rat.le_of_lt hu0)
  constructor <;> grind

theorem pi_mul_neg {p u : Rat} (hp1 : 1 ≤ p) (hp : p ≤ 4) (hu0 : u < 0) (hu : -1 / 4 ≤ u) :
    -1 ≤ p * u ∧ p * u ≤ u := by
  have h' : 0 ≤ -u := by grind
  have := Rat.mul_le_mul_of_nonneg_right hp1 h'
  have := Rat.mul_le_mul_of_nonneg_right hp h'
  constructor <;> grind

theorem consts_sinpi : piG.isFinite = true ∧ 3 < piG.toRat ∧ piG.toRat < 4 ∧
    c1.isFinite = true ∧ c1.toRat = 1 ∧ c1.sign = false ∧
    cHalf.isFinite = true ∧ cHalf.toRat = 1 / 2 ∧
    c1p5.isFinite = true ∧ c1p5.toRat = 3 / 2 ∧
    c2.isFinite = true ∧ c2.toRat = 2 ∧ c2.sign = false ∧ c2.isZero = false ∧
    c0p25.isFinite = true ∧ c0p25.toRat = 1 / 4 := by
  decide +kernel

theorem rep_of_float {f : F64} (ff : f.isFinite = true) :
    Rep binary64 f.toRat ∧ Rat.abs f.toRat < overflowLimit := ⟨toRat_rep ff, abs_toRat_lt ff⟩

theorem rep_of_neg_float {f : F64} (ff : f.isFinite = true) :
    Rep binary64 (-f.toRat) ∧ Rat.abs (-f.toRat) < overflowLimit :=
  ⟨rep_neg (toRat_rep ff), by rw [abs_neg]; exact abs_toRat_lt ff⟩

theorem rep_double {q : Rat} (h : Rep binary64 q) : Rep binary64 (2 * q) := by
  obtain ⟨M, E, hM, hE, hq⟩ := h
  refine ⟨M, E + 1, hM, by simp [Fmt.etiny, binary64] at hE ⊢; omega, ?_⟩
  rw [pw_succ]
  rcases hq with hq | hq
  · left; rw [hq]; grind
  · right; rw [hq]; grind

theorem roundToInt_pos {v : F64} (fv : v.isFinite = true) (h0 : 0 < v.toRat) (h4 : v.toRat < 4) :
    roundToInt v = (v.toRat + 1 / 2).floor := by
  have hz : v.isZero = false := by
    cases h : v.isZero
    · rfl
    · rw [toRat_of_isZero h] at h0; simp at h0
  have hs : v.sign = false := by
    have := toRat_neg_iff_sign fv hz
    cases hv : v.sign
    · rfl
    · rw [hv] at this; simp at this; grind
  have hn : v.isNaN = false := isNaN_false_of_finite fv
  have hmk : mkRat 1 2 = 1 / 2 := by decide +kernel
  unfold roundToInt F64.roundAway
  simp only [hn, fv, hz, hs, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hmk]
  generalize hn0 : (v.toRat + 1 / 2).floor = n0
  have b0 : 0 ≤ n0 := by rw [← hn0]; exact Rat.le_floor_iff.2 (by push_cast; grind)
  have b4 : n0 ≤ 4 := by
    have := Rat.floor_le (v.toRat + 1 / 2)
    rw [hn0] at this
    have : (n0 : Rat) < 5 := by grind
    have : n0 < 5 := by exact_mod_cast this
    omega
  unfold F64.ofIntS
  split
  · rename_i h; subst h; decide +kernel
  · obtain ⟨_, v1⟩ := ofInt_small (n := n0) (by omega)
    exact truncInt_of_int v1

/-! ## `m_sinpi` -/

theorem sinpiSign_proven : SinpiSign := by
  intro L hL x fx hni e
  obtain ⟨hs1, hs2, hc⟩ := hL
  obtain ⟨pf, p3, p4, f1, v1, s1, fh, vh, f15, v15, f2, v2, s2, z2, fq, vq⟩ := consts_sinpi
  have fa : (F64.abs x).isFinite = true := by rw [abs_isFinite]; exact fx
  have va : (F64.abs x).toRat = Rat.abs x.toRat := abs_toRat x
  generalize hA : Rat.abs x.toRat = A at va
  have hA0 : 0 ≤ A := by rw [← hA]; exact abs_nonneg _
  have hAni : ∀ n : Int, A ≠ n := by
    intro n hn
    have sx := sign_val fx
    rw [hA, hn] at sx
    cases hsx : x.sign
    · rw [hsx] at sx; simp at sx; exact hni n sx
    · rw [hsx] at sx; simp at sx; exact hni (-n) (by rw [sx]; push_cast; rfl)
  obtain ⟨fy, vy, hy0, hy2, hq0, _⟩ := fmod_val fa f2 z2 (by rw [va]; exact hA0)
  rw [va, v2, abs_of_nonneg (by decide +kernel : (0 : Rat) ≤ 2)] at vy hy0 hy2 hq0
  generalize hy : F64.fmod (F64.abs x) c2 = y at fy vy
  generalize hq : (A / 2).floor = q at vy hy0 hy2 hq0
  have hAq : A = 2 * q + y.toRat := by grind
  have hy_ne0 : y.toRat ≠ 0 := by
    intro h; apply hAni (2 * q); rw [hAq, h]; push_cast; grind
  have hy_ne1 : y.toRat ≠ 1 := by
    intro h; apply hAni (2 * q + 1); rw [hAq, h]; push_cast; grind
  have hypos : 0 < y.toRat := by grind
  have hyz : y.isZero = false := by
    cases h : y.isZero
    · rfl
    · exact absurd (toRat_of_isZero h) hy_ne0
  have ys : y.sign = false := by
    have := toRat_neg_iff_sign fy hyz
    cases hv : y.sign
    · rfl
    · rw [hv] at this; simp at this; grind
  -- parity of floor |x|
  have hpar : (A.floor % 2 = 0) ↔ y.toRat < 1 := by
    by_cases h : y.toRat < 1
    · have : A.floor = 2 * q := floor_eq_of (by push_cast; grind) (by push_cast; grind)
      rw [this]; simp only [h, iff_true]; omega
    · have : A.floor = 2 * q + 1 := floor_eq_of (by push_cast; grind) (by push_cast; grind)
      rw [this]; simp only [h, iff_false]; omega
  -- `n = round(2y)`
  have r2y := rep_double (toRat_rep fy)
  obtain ⟨fv, vv⟩ := mul_exact f2 fy (by rw [v2]; exact r2y)
    (by rw [v2, abs_of_nonneg (by grind)]; have := pw_natAbs_le_limit; grind)
  rw [v2] at vv
  have hround := roundToInt_pos fv (by rw [vv]; grind) (by rw [vv]; grind)
  rw [vv] at hround
  generalize hn0 : (2 * y.toRat + 1 / 2).floor = n0 at hround
  have nb1 := Rat.floor_le (2 * y.toRat + 1 / 2)
  have nb2 := Rat.lt_floor_add_one (2 * y.toRat + 1 / 2)
  rw [hn0] at nb1 nb2
  have n0lo : 0 ≤ n0 := by
    have : (0 : Rat) < ((n0 + 1 : Int) : Rat) := by push_cast; grind
    have : (0 : Int) < n0 + 1 := by exact_mod_cast this
    omega
  have n0hi : n0 ≤ 4 := by
    have : (n0 : Rat) < 5 := by grind
    have : n0 < 5 := by exact_mod_cast this
    omega
  -- the value before the sign of `x`
  have core : ∃ r : F64, m_sinpi L x e = (F64.mul (F64.copysign c1 x) r, e) ∧ r.isFinite = true ∧
      r.toRat ≠ 0 ∧ (0 < r.toRat ↔ y.toRat < 1) := by
    have yRep := rep_of_float fy
    rcases (by omega : n0 = 0 ∨ n0 = 1 ∨ n0 = 2 ∨ n0 = 3 ∨ n0 = 4) with h | h | h | h | h <;>
      subst h <;> push_cast at nb1 nb2
    · -- `sin(pi*y)`, `0 < y < 1/4`
      obtain ⟨ht1, ht2, _⟩ := mul_facts pf fy
      obtain ⟨b1, b2⟩ := pi_mul_pos (p := piG.toRat) (u := y.toRat) (by grind) (by grind) hypos (by grind)
      obtain ⟨tf, tl, th⟩ := rnd_between yRep.1 (by rw [← v1]; exact (rep_of_float f1).1)
        yRep.2 (by rw [← v1]; exact (rep_of_float f1).2) b1 b2
      rw [← ht1] at tl th; rw [← ht2] at tf
      obtain ⟨sf, sp, se⟩ := hs1 _ tf (by grind) th
      refine ⟨(L.sin (F64.mul piG y)).1, ?_, sf, by grind, by grind⟩
      unfold m_sinpi
      simp only [hy, hround, call1, se, Errno.after, beq_self_eq_true, ↓reduceIte]
    · -- `cos(pi*(y - 0.5))`
      obtain ⟨u1, u2, _⟩ := sub_facts fy fh
      rw [vh] at u1 u2
      obtain ⟨uf, ul, uh⟩ := rnd_between (by rw [← vq]; exact (rep_of_neg_float fq).1)
        (by rw [← vq]; exact (rep_of_float fq).1) (by rw [← vq]; exact (rep_of_neg_float fq).2)
        (by rw [← vq]; exact (rep_of_float fq).2)
        (show -(1 / 4 : Rat) ≤ y.toRat - 1 / 2 by grind) (show y.toRat - 1 / 2 ≤ 1 / 4 by grind)
      rw [← u1] at ul uh; rw [← u2] at uf
      obtain ⟨t1, t2, _⟩ := mul_facts pf uf
      obtain ⟨b1, b2⟩ := pi_mul_mid (p := piG.toRat) (u := (F64.sub y cHalf).toRat) (by grind)
        (by grind) (by grind) uh
      obtain ⟨tf, tl, th⟩ := rnd_between (by rw [← v1]; exact (rep_of_neg_float f1).1)
        (by rw [← v1]; exact (rep_of_float f1).1) (by rw [← v1]; exact (rep_of_neg_float f1).2)
        (by rw [← v1]; exact (rep_of_float f1).2) b1 b2
      rw [← t1] at tl th; rw [← t2] at tf
      obtain ⟨cf, cp, ce⟩ := hc _ tf tl th
      refine ⟨(L.cos (F64.mul piG (F64.sub y cHalf))).1, ?_, cf, by grind, by grind⟩
      unfold m_sinpi
      simp only [hy, hround, call1, ce, Errno.after, beq_self_eq_true, ↓reduceIte]
    · -- `sin(pi*(1 - y))`, `1 - y` exact
      have hrep : Rep binary64 (c1.toRat - y.toRat) := by
        by_cases hlt : y.toRat < 1
        · exact sterbenz f1 fy s1 ys (by grind) (by grind)
        · have := sterbenz fy f1 ys s1 (by grind) (by grind)
          have e' : c1.toRat - y.toRat = -(y.toRat - c1.toRat) := by grind
          rw [e']; exact rep_neg this
      obtain ⟨uf, uv⟩ := sub_exact f1 fy hrep
        (by apply lim_of_le f1; rw [v1, abs_eq_ite, abs_eq_ite]; split <;> split <;> grind)
      rw [v1] at uv
      obtain ⟨t1, t2, _⟩ := mul_facts pf uf
      by_cases hlt : y.toRat < 1
      · obtain ⟨b1, b2⟩ := pi_mul_pos (p := piG.toRat) (u := (F64.sub c1 y).toRat) (by grind)
          (by grind) (by rw [uv]; grind) (by rw [uv]; grind)
        obtain ⟨tf, tl, th⟩ := rnd_between (rep_of_float uf).1 (by rw [← v1]; exact (rep_of_float f1).1)
          (rep_of_float uf).2 (by rw [← v1]; exact (rep_of_float f1).2) b1 b2
        rw [← t1] at tl th; rw [← t2] at tf
        obtain ⟨sf, sp, se⟩ := hs1 _ tf (by rw [uv] at tl; grind) th
        refine ⟨(L.sin (F64.mul piG (F64.sub c1 y))).1, ?_, sf, by grind, by grind⟩
        unfold m_sinpi
        simp only [hy, hround, call1, se, Errno.after, beq_self_eq_true, ↓reduceIte]
      · obtain ⟨b1, b2⟩ := pi_mul_neg (p := piG.toRat) (u := (F64.sub c1 y).toRat) (by grind)
          (by grind) (by rw [uv]; grind) (by rw [uv]; grind)
        obtain ⟨tf, tl, th⟩ := rnd_between (by rw [← v1]; exact (rep_of_neg_float f1).1)
          (rep_of_float uf).1 (by rw [← v1]; exact (rep_of_neg_float f1).2) (rep_of_float uf).2 b1 b2
        rw [← t1] at tl th; rw [← t2] at tf
        obtain ⟨sf, sp, se⟩ := hs2 _ tf tl (by rw [uv] at th; grind)
        refine ⟨(L.sin (F64.mul piG (F64.sub c1 y))).1, ?_, sf, by grind, by grind⟩
        unfold m_sinpi
        simp only [hy, hround, call1, se, Errno.after, beq_self_eq_true, ↓reduceIte]
    · -- `-cos(pi*(y - 1.5))`
      obtain ⟨u1, u2, _⟩ := sub_facts fy f15
      rw [v15] at u1 u2
      obtain ⟨uf, ul, uh⟩ := rnd_between (by rw [← vq]; exact (rep_of_neg_float fq).1)
        (by rw [← vq]; exact (rep_of_float fq).1) (by rw [← vq]; exact (rep_of_neg_float fq).2)
        (by rw [← vq]; exact (rep_of_float fq).2)
        (show -(1 / 4 : Rat) ≤ y.toRat - 3 / 2 by grind) (show y.toRat - 3 / 2 ≤ 1 / 4 by grind)
      rw [← u1] at ul uh; rw [← u2] at uf
      obtain ⟨t1, t2, _⟩ := mul_facts pf uf
      obtain ⟨b1, b2⟩ := pi_mul_mid (p := piG.toRat) (u := (F64.sub y c1p5).toRat) (by grind)
        (by grind) (by grind) uh
      obtain ⟨tf, tl, th⟩ := rnd_between (by rw [← v1]; exact (rep_of_neg_float f1).1)
        (by rw [← v1]; exact (rep_of_float f1).1) (by rw [← v1]; exact (rep_of_neg_float f1).2)
        (by rw [← v1]; exact (rep_of_float f1).2) b1 b2
      rw [← t1] at tl th; rw [← t2] at tf
      obtain ⟨cf, cp, ce⟩ := hc _ tf tl th
      refine ⟨F64.neg (L.cos (F64.mul piG (F64.sub y c1p5))).1, ?_, by rw [neg_isFinite]; exact cf,
        by rw [toRat_neg]; grind, by rw [toRat_neg]; grind⟩
      unfold m_sinpi
      simp only [hy, hround, call1, ce, Errno.after, beq_self_eq_true, ↓reduceIte]
    · -- `sin(pi*(y - 2))`, `y - 2` exact
      have hrep : Rep binary64 (y.toRat - c2.toRat) := by
        have := sterbenz f2 fy s2 ys (by grind) (by grind)
        have e' : y.toRat - c2.toRat = -(c2.toRat - y.toRat) := by grind
        rw [e']; exact rep_neg this
      obtain ⟨uf, uv⟩ := sub_exact fy f2 hrep
        (by apply lim_of_le f2; rw [v2, abs_eq_ite, abs_eq_ite]; split <;> split <;> grind)
      rw [v2] at uv
      obtain ⟨t1, t2, _⟩ := mul_facts pf uf
      obtain ⟨b1, b2⟩ := pi_mul_neg (p := piG.toRat) (u := (F64.sub y c2).toRat) (by grind)
        (by grind) (by rw [uv]; grind) (by rw [uv]; grind)
      obtain ⟨tf, tl, th⟩ := rnd_between (by rw [← v1]; exact (rep_of_neg_float f1).1)
        (rep_of_float uf).1 (by rw [← v1]; exact (rep_of_neg_float f1).2) (rep_of_float uf).2 b1 b2
      rw [← t1] at tl th; rw [← t2] at tf
      obtain ⟨sf, sp, se⟩ := hs2 _ tf tl (by rw [uv] at th; grind)
      refine ⟨(L.sin (F64.mul piG (F64.sub y c2))).1, ?_, sf, by grind, by grind⟩
      unfold m_sinpi
      simp only [hy, hround, call1, se, Errno.after, beq_self_eq_true, ↓reduceIte]
  obtain ⟨r, hr, rf, rnz, rsg⟩ := core
  rw [hr]
  obtain ⟨cf, cv, cs⟩ := copysign_c1_val x
  have hrep : Rep binary64 ((F64.copysign c1 x).toRat * r.toRat) := by
    rw [cv]; split
    · rw [show (-1 : Rat) * r.toRat = -r.toRat by grind]; exact (rep_of_neg_float rf).1
    · rw [Rat.one_mul]; exact (rep_of_float rf).1
  have hlim : Rat.abs ((F64.copysign c1 x).toRat * r.toRat) < overflowLimit := by
    rw [cv]; split
    · rw [show (-1 : Rat) * r.toRat = -r.toRat by grind]; exact (rep_of_neg_float rf).2
    · rw [Rat.one_mul]; exact (rep_of_float rf).2
  obtain ⟨mf, mv⟩ := mul_exact cf rf hrep hlim
  refine ⟨rfl, mf, ?_, ?_⟩
  · rw [mv, cv]; split <;> grind
  · rw [mv, cv, hpar]
    cases hxs : x.sign
    · simp only [Bool.false_eq_true, ↓reduceIte, Rat.one_mul, false_iff]; grind
    · simp only [↓reduceIte, true_iff]; constructor <;> intro h <;> grind

/-! ## `gamma` below `-200` -/

theorem gammaUnderflowSign_proven : GammaUnderflowSign := by
  intro L hL x fx hlt hni
  have h200 : c200.isFinite = true ∧ c200.toRat = 200 := by decide +kernel
  have hneg : x.toRat < 0 := by grind
  have hz : x.isZero = false := by
    cases h : x.isZero
    · rfl
    · rw [toRat_of_isZero h] at hneg; simp at hneg
  have hsx : x.sign = true := by
    have := toRat_neg_iff_sign fx hz; rw [this] at hneg; exact hneg
  have hfl : F64.eq x (F64.floor x) = false := by
    cases h : F64.eq x (F64.floor x)
    · rfl
    · obtain ⟨n, hn⟩ := (eq_floor_iff fx).1 h; exact absurd hn (hni n)
  have habs : (F64.abs x).toRat = -x.toRat := by
    rw [abs_toRat, abs_of_nonpos (Rat.le_of_lt hneg)]
  have fa : (F64.abs x).isFinite = true := by rw [abs_isFinite]; exact fx
  have h20 : c1em20.isFinite = true ∧ c1em20.toRat < 1 := by decide +kernel
  have hsmall : F64.lt (F64.abs x) c1em20 = false := by
    rw [lt_of_finite fa h20.1, habs]; simp; grind
  have hbig : F64.lt c200 (F64.abs x) = true := by
    rw [lt_of_finite h200.1 fa, habs, h200.2]; simp; grind
  have hlt0 : F64.lt x c0 = true := by
    rw [lt_of_finite fx c0_facts.1, c0_facts.2.2.1]; simp; exact hneg
  obtain ⟨se, sf, snz, ssg⟩ := sinpiSign_proven L hL x fx hni .zero
  generalize hs : m_sinpi L x .zero = s at se sf snz ssg
  obtain ⟨s, es⟩ := s
  simp only at se sf snz ssg
  subst se
  have hm : m_tgamma L x = (F64.div c0 s, .zero) := by
    simp only [m_tgamma, fx, Bool.not_true, Bool.false_eq_true, ↓reduceIte, isZeroC_eq, hz, hfl,
      Bool.false_and, hsmall, hbig, hlt0, hs]
  have hszero : s.isZero = false := by
    cases h : s.isZero
    · rfl
    · exact absurd (toRat_of_isZero h) snz
  have hdiv : F64.div c0 s = F64.zero s.sign := by
    rw [div_of_finite c0_facts.1 sf hszero]
    have : c0.toRat / s.toRat = 0 := by rw [c0_facts.2.2.1, Rat.div_def, Rat.zero_mul]
    simp only [this, ↓reduceIte]
    have : c0.sign = false := by decide +kernel
    rw [this]; cases s.sign <;> rfl
  have hsgn : s.sign = decide ((-x.toRat).floor % 2 = 0) := by
    have e1 := toRat_neg_iff_sign sf hszero
    rw [abs_of_nonpos (Rat.le_of_lt hneg), hsx] at ssg
    simp only [true_iff] at ssg
    rw [e1] at ssg
    cases h : s.sign
    · simp only [h, Bool.false_eq_true, false_iff] at ssg
      simp [ssg]
    · simp only [h, true_iff] at ssg
      simp [ssg]
  obtain ⟨hz0, _, _, _⟩ := (math1aRules_proven (m_tgamma L) (some gmsg) (.float x)).2 _ rfl
  unfold math_gamma
  rw [hm] at hz0
  rw [hz0 rfl, hdiv, hsgn]

end PyLean.MathInt
