import PyLean.MathInt.FltOpen
import PyLean.MathInt.FltFmod
import PyLean.MathInt.FltIsclose
import PyLean.MathInt.FltNext

/-!
# Proof: `math.remainder` is the exact IEEE remainder

`m_remainder` (Modules/mathmodule.c:530-618) computes `m = fmod(|x|, |y|)` and compares it with
`c = |y| - m` instead of `|y| / 2`. The comment at :545-563 argues that the comparison is right
even though `c` is rounded: when `m > |y|/2`, `c` is exact by Sterbenz's lemma; when `m < |y|/2`,
either `|y|/2` is a float (and `c >= |y|/2 > m`) or `|y|` is so small that `c` is exact. In the
tie `m == |y|/2`, `|x| - m` and `0.5 * (|x| - m)` are exact (:586-600), so the parity of the
quotient picks the even multiple. This file proves all of it for every finite `x` and finite
nonzero `y`.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-! ## Rationals -/

theorem floor_eq_of {q : Rat} {z : Int} (h1 : (z : Rat) ≤ q) (h2 : q < (z : Rat) + 1) :
    q.floor = z := by
  apply Int.le_antisymm
  · have : q.floor < z + 1 := by
      rw [Rat.floor_lt_iff]; push_cast; exact h2
    omega
  · exact Rat.le_floor_iff.2 h1

theorem rhe_int_add (k : Int) {t : Rat} (h0 : 0 ≤ t) (h1 : t < 1) :
    roundHalfEven ((k : Rat) + t) =
      if t < 1 / 2 then k else if 1 / 2 < t then k + 1 else if k % 2 = 0 then k else k + 1 := by
  have hf : ((k : Rat) + t).floor = k := floor_eq_of (by grind) (by grind)
  unfold roundHalfEven
  simp only [hf]
  have : (k : Rat) + t - (k : Rat) = t := by grind
  rw [this]

theorem rhe_neg (q : Rat) : roundHalfEven (-q) = -roundHalfEven q := by
  have hk1 := Rat.floor_le q
  have hk2 := Rat.lt_floor_add_one q
  obtain ⟨k, t, ht0, ht1, hq⟩ : ∃ (k : Int) (t : Rat), 0 ≤ t ∧ t < 1 ∧ q = (k : Rat) + t :=
    ⟨q.floor, q - q.floor, by grind, by grind, by grind⟩
  subst hq
  by_cases hz : t = 0
  · subst hz
    have e2 : -((k : Rat) + 0) = ((-k : Int) : Rat) + 0 := by push_cast; grind
    rw [e2, rhe_int_add _ (Rat.le_refl) (by decide), rhe_int_add _ (Rat.le_refl) (by decide)]
    simp only [show (0 : Rat) < 1 / 2 by decide +kernel, ↓reduceIte]
  · have e2 : -((k : Rat) + t) = ((-k - 1 : Int) : Rat) + (1 - t) := by push_cast; grind
    rw [e2, rhe_int_add _ (by grind) (by grind), rhe_int_add _ ht0 ht1]
    by_cases a : t < 1 / 2
    · have b : ¬ (1 - t < 1 / 2) := by grind
      have c : 1 / 2 < 1 - t := by grind
      simp only [a, b, c, ↓reduceIte]; omega
    · by_cases a2 : 1 / 2 < t
      · have b : 1 - t < 1 / 2 := by grind
        simp only [a, a2, b, ↓reduceIte]; omega
      · have b : ¬ (1 - t < 1 / 2) := by grind
        have c : ¬ (1 / 2 < 1 - t) := by grind
        simp only [a, a2, b, c, ↓reduceIte]
        split <;> split <;> omega

/-! ## Grids -/

theorem rep_of_grid {N : Nat} {e : Int} (hN : N < 2 ^ 53) (he : -1074 ≤ e) :
    Rep binary64 ((N : Rat) * pw e) :=
  ⟨N, e, hN, by show binary64.etiny ≤ e; simp [Fmt.etiny, binary64]; omega, Or.inl rfl⟩

theorem nat_le_of_scaled {P Q : Nat} {e : Int} (h : (P : Rat) * pw e ≤ (Q : Rat) * pw e) : P ≤ Q :=
  Rat.natCast_le_natCast.1 (Rat.le_of_mul_le_mul_right h (pw_pos e))

theorem nat_eq_of_scaled {P Q : Nat} {e : Int} (h : (P : Rat) * pw e = (Q : Rat) * pw e) : P = Q := by
  have h1 := nat_le_of_scaled (P := P) (Q := Q) (e := e) (by rw [h]; exact Rat.le_refl)
  have h2 := nat_le_of_scaled (P := Q) (Q := P) (e := e) (by rw [h]; exact Rat.le_refl)
  omega

/-- `N * 2 ^ e` on the finer grid `2 ^ e'`. -/
theorem regrid (N : Nat) {e e' : Int} (h : e' ≤ e) :
    (N : Rat) * pw e = ((N * 2 ^ (e - e').toNat : Nat) : Rat) * pw e' := by
  rw [Rat.natCast_mul, ← pw_natCast, Rat.mul_assoc, ← pw_add]
  congr 2; omega

theorem sign_false_toRat {a : F64} (fa : a.isFinite = true) (sa : a.sign = false) :
    a.toRat = (a.mant : Rat) * pw a.lsbExp := by
  rw [toRat_of_finite fa, sa]; rfl

theorem sign_false_nonneg {a : F64} (fa : a.isFinite = true) (sa : a.sign = false) : 0 ≤ a.toRat := by
  rw [sign_false_toRat fa sa]
  exact Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))

/-- Sterbenz's lemma: `a - b` is exact when `b <= a <= 2b`. -/
theorem sterbenz {a b : F64} (fa : a.isFinite = true) (fb : b.isFinite = true)
    (sa : a.sign = false) (sb : b.sign = false) (h1 : b.toRat ≤ a.toRat)
    (h2 : a.toRat ≤ 2 * b.toRat) : Rep binary64 (a.toRat - b.toRat) := by
  have ha := sign_false_toRat fa sa
  have hb := sign_false_toRat fb sb
  have hA := mant_lt a
  have hB := mant_lt b
  have ga := lsbExp_ge a
  have gb := lsbExp_ge b
  rcases Int.le_total a.lsbExp b.lsbExp with h | h
  · -- the grid of `a`
    have hb' := regrid b.mant h
    generalize b.mant * 2 ^ (b.lsbExp - a.lsbExp).toNat = P at hb'
    rw [hb'] at hb
    have hPA : P ≤ a.mant := nat_le_of_scaled (by rw [← ha, ← hb]; exact h1)
    obtain ⟨N, hN⟩ := Nat.exists_eq_add_of_le hPA
    have : a.toRat - b.toRat = (N : Rat) * pw a.lsbExp := by
      rw [ha, hb, hN, Rat.natCast_add]; grind
    rw [this]; exact rep_of_grid (by omega) ga
  · have ha' := regrid a.mant h
    generalize a.mant * 2 ^ (a.lsbExp - b.lsbExp).toNat = Q at ha'
    rw [ha'] at ha
    have hBQ : b.mant ≤ Q := nat_le_of_scaled (by rw [← ha, ← hb]; exact h1)
    have hQ2 : Q ≤ 2 * b.mant := nat_le_of_scaled (e := b.lsbExp)
      (by rw [Rat.natCast_mul, ← ha, Rat.mul_assoc, ← hb]; push_cast; exact h2)
    obtain ⟨N, hN⟩ := Nat.exists_eq_add_of_le hBQ
    have : a.toRat - b.toRat = (N : Rat) * pw b.lsbExp := by
      rw [ha, hb, hN, Rat.natCast_add]; grind
    rw [this]; exact rep_of_grid (by omega) gb

/-- Either `b / 2` is a float, or `b` is on the bottom grid and then so is `b - R`. -/
theorem half_or_sub {b m : F64} (fb : b.isFinite = true) (sb : b.sign = false)
    (fm : m.isFinite = true) (h0 : 0 ≤ m.toRat) (hlt : m.toRat < b.toRat) :
    Rep binary64 (b.toRat / 2) ∨ Rep binary64 (b.toRat - m.toRat) := by
  have hb := sign_false_toRat fb sb
  have hB := mant_lt b
  have gb := lsbExp_ge b
  by_cases he : -1074 < b.lsbExp
  · left
    have : b.toRat / 2 = (b.mant : Rat) * pw (b.lsbExp - 1) := by
      rw [hb]
      have := pw_succ (b.lsbExp - 1)
      rw [show b.lsbExp - 1 + 1 = b.lsbExp by omega] at this
      rw [this]; grind
    rw [this]; exact rep_of_grid hB (by omega)
  · right
    have he' : b.lsbExp = -1074 := by omega
    obtain ⟨Z, hZ⟩ := toRat_grid m fm
    rw [he'] at hb
    have hZ0 : 0 ≤ Z := by
      have : (0 : Rat) ≤ (Z : Rat) := by
        have hp := pw_pos (-1074)
        rw [hZ] at h0
        apply Rat.le_of_mul_le_mul_right (c := pw (-1074)) _ hp
        rw [Rat.zero_mul]; exact h0
      exact Rat.intCast_nonneg.1 this
    have hZb : Z < b.mant := by
      have : (Z : Rat) * pw (-1074) < (b.mant : Rat) * pw (-1074) := by rw [← hZ, ← hb]; exact hlt
      have h3 := (Rat.mul_lt_mul_right (pw_pos _)).1 this
      have h4 : ((Z.toNat : Nat) : Rat) < (b.mant : Rat) := by
        rw [show ((Z.toNat : Nat) : Rat) = (Z : Rat) by
          rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hZ0]]; exact h3
      have := Rat.natCast_lt_natCast.1 h4; omega
    have : b.toRat - m.toRat = (((b.mant - Z.toNat : Nat)) : Rat) * pw (-1074) := by
      rw [hb, hZ]
      have hle : Z.toNat ≤ b.mant := by omega
      obtain ⟨N, hN⟩ := Nat.exists_eq_add_of_le hle
      rw [hN, show Z.toNat + N - Z.toNat = N by omega, Rat.natCast_add,
        show ((Z.toNat : Nat) : Rat) = (Z : Rat) by rw [← Rat.intCast_natCast, Int.toNat_of_nonneg hZ0]]
      grind
    rw [this]; exact rep_of_grid (by omega) (by omega)

theorem odd_decomp : ∀ n : Nat, 0 < n → ∃ o t : Nat, n = o * 2 ^ t ∧ o % 2 = 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h : n % 2 = 1
    · exact ⟨n, 0, by simp, h⟩
    · obtain ⟨o, t, h1, h2⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨o, t + 1, ?_, h2⟩
      rw [Nat.pow_succ, ← Nat.mul_assoc, ← h1]; omega

/-- In the tie `|x| = (2k+1) m`, `m` sits on a grid where `(2k+1) m` still has fewer than 54
bits: so `2k m` and `k m` are floats. -/
theorem tie_grid {a m : F64} (fa : a.isFinite = true) (sa : a.sign = false)
    (fm : m.isFinite = true) (sm : m.sign = false) (hm0 : 0 < m.toRat) (k : Nat)
    (hk : a.toRat = (2 * k + 1 : Nat) * m.toRat) :
    ∃ (R : Nat) (e : Int), m.toRat = (R : Rat) * pw e ∧ -1074 ≤ e ∧ (2 * k + 1) * R < 2 ^ 53 := by
  have ha := sign_false_toRat fa sa
  have hmv := sign_false_toRat fm sm
  have hA := mant_lt a
  have ga := lsbExp_ge a
  have gm := lsbExp_ge m
  have hmpos : 0 < m.mant := by
    rcases Nat.eq_zero_or_pos m.mant with h | h
    · rw [hmv, h] at hm0; simp at hm0
    · exact h
  obtain ⟨o, t, ho, hodd⟩ := odd_decomp m.mant hmpos
  have hmv' : m.toRat = (o : Rat) * pw (m.lsbExp + t) := by
    rw [hmv, ho, Rat.natCast_mul, ← pw_natCast, Rat.mul_assoc, ← pw_add, Int.add_comm]
  refine ⟨o, m.lsbExp + t, hmv', by omega, ?_⟩
  rw [hmv'] at hk
  have hk' : a.toRat = (((2 * k + 1) * o : Nat) : Rat) * pw (m.lsbExp + t) := by
    rw [hk, Rat.natCast_mul, Rat.mul_assoc]
  by_cases h : a.lsbExp ≤ m.lsbExp + t
  · have := regrid ((2 * k + 1) * o) h
    rw [this] at hk'
    have heq := nat_eq_of_scaled (hk'.symm.trans ha)
    have : (2 * k + 1) * o ≤ (2 * k + 1) * o * 2 ^ (m.lsbExp + t - a.lsbExp).toNat :=
      Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    omega
  · exfalso
    have h' : m.lsbExp + t ≤ a.lsbExp := by omega
    have := regrid a.mant h'
    rw [this] at ha
    have heq := nat_eq_of_scaled (hk'.symm.trans ha)
    have hd : 1 ≤ (a.lsbExp - (m.lsbExp + t)).toNat := by omega
    have hpow : 2 ^ (a.lsbExp - (m.lsbExp + t)).toNat =
        2 * 2 ^ ((a.lsbExp - (m.lsbExp + t)).toNat - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    rw [hpow] at heq
    have hpar : ((2 * k + 1) * o) % 2 = 1 := by
      rw [Nat.mul_mod, hodd]; omega
    have : a.mant * (2 * 2 ^ ((a.lsbExp - (m.lsbExp + t)).toNat - 1)) =
        2 * (a.mant * 2 ^ ((a.lsbExp - (m.lsbExp + t)).toNat - 1)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm a.mant 2, Nat.mul_assoc]
    omega

/-! ## Exact operations -/

theorem lim_of_le {q : Rat} {f : F64} (ff : f.isFinite = true) (h : Rat.abs q ≤ Rat.abs f.toRat) :
    Rat.abs q < overflowLimit := by
  have := abs_toRat_lt ff; grind

theorem sub_exact {a b : F64} (fa : a.isFinite = true) (fb : b.isFinite = true)
    (hr : Rep binary64 (a.toRat - b.toRat)) (hl : Rat.abs (a.toRat - b.toRat) < overflowLimit) :
    (F64.sub a b).isFinite = true ∧ (F64.sub a b).toRat = a.toRat - b.toRat := by
  obtain ⟨h1, h2, _⟩ := sub_facts fa fb
  exact ⟨by rw [h2]; exact (ofRat_isFinite _).2 hl, by rw [h1]; exact ofRat_exact hr hl⟩

theorem mul_exact {a b : F64} (fa : a.isFinite = true) (fb : b.isFinite = true)
    (hr : Rep binary64 (a.toRat * b.toRat)) (hl : Rat.abs (a.toRat * b.toRat) < overflowLimit) :
    (F64.mul a b).isFinite = true ∧ (F64.mul a b).toRat = a.toRat * b.toRat := by
  obtain ⟨h1, h2, _⟩ := mul_facts fa fb
  exact ⟨by rw [h2]; exact (ofRat_isFinite _).2 hl, by rw [h1]; exact ofRat_exact hr hl⟩

/-- `fmod` of a nonnegative float by a float: the exact remainder. -/
theorem fmod_val {a b : F64} (fa : a.isFinite = true) (fb : b.isFinite = true)
    (hb : b.isZero = false) (ha0 : 0 ≤ a.toRat) :
    (F64.fmod a b).isFinite = true ∧
    (F64.fmod a b).toRat = a.toRat - Rat.abs b.toRat * (Rat.floor (a.toRat / Rat.abs b.toRat) : Rat) ∧
    0 ≤ a.toRat - Rat.abs b.toRat * (Rat.floor (a.toRat / Rat.abs b.toRat) : Rat) ∧
    a.toRat - Rat.abs b.toRat * (Rat.floor (a.toRat / Rat.abs b.toRat) : Rat) < Rat.abs b.toRat ∧
    0 ≤ Rat.floor (a.toRat / Rat.abs b.toRat) ∧
    (a.sign = false → F64.fmod a b =
      ofRat (a.toRat - Rat.abs b.toRat * (Rat.floor (a.toRat / Rat.abs b.toRat) : Rat))) := by
  have hA : Rat.abs a.toRat = a.toRat := abs_of_nonneg ha0
  obtain ⟨hrep, hr0, hrlt, hk0⟩ := fmod_rem fa fb hb
  simp only [hA] at hrep hr0 hrlt hk0
  generalize hR : a.toRat - Rat.abs b.toRat * ((Rat.floor (a.toRat / Rat.abs b.toRat) : Int) : Rat)
    = R at hrep hr0 hrlt
  have hyi : b.isInf = false := isInf_false_of_finite fb
  have hfm : F64.fmod a b = if R = 0 then F64.zero a.sign else ofRat (if a.sign then -R else R) := by
    unfold F64.fmod
    simp only [isNaN_false_of_finite fa, isNaN_false_of_finite fb, isInf_false_of_finite fa, hb,
      hyi, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    rw [← abs_eq_ite, ← abs_eq_ite, hA, hR]
  have hlim : Rat.abs R < overflowLimit := by
    rw [abs_of_nonneg hr0]; have := abs_toRat_lt fb; grind
  have hfR : (ofRat R).isFinite = true := (ofRat_isFinite _).2 hlim
  have hvR : (ofRat R).toRat = R := ofRat_exact hrep hlim
  refine ⟨?_, ?_, hr0, hrlt, hk0, fun hs => ?_⟩
  · rw [hfm]; split
    · exact zero_isFinite _
    · split
      · exact (ofRat_isFinite _).2 (by rw [abs_neg]; exact hlim)
      · exact hfR
  · rw [hfm]; split
    · rename_i h0; rw [zero_toRat, h0]
    · rename_i h0
      split
      · -- a negative sign with a nonnegative value is `-0.0`, whose remainder is `0`
        rename_i hs
        exfalso; apply h0
        have hz : a.toRat = 0 := by
          rw [toRat_of_finite fa, hs] at ha0 ⊢
          simp only [↓reduceIte] at ha0 ⊢
          have := Rat.mul_nonneg (Rat.natCast_nonneg (a := a.mant)) (Rat.le_of_lt (pw_pos a.lsbExp))
          grind
        have hb0 := abs_nonneg b.toRat
        have hk' : (0 : Rat) ≤ ((Rat.floor (a.toRat / Rat.abs b.toRat) : Int) : Rat) :=
          Rat.intCast_nonneg.2 hk0
        have := Rat.mul_nonneg hb0 hk'
        grind
      · exact hvR
  · rw [hfm, hs]; simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i h0; rw [h0, ofRat_zero]
    · rfl

theorem cHalf_val : cHalf.isFinite = true ∧ cHalf.toRat = 1 / 2 := by decide +kernel
theorem c2_val : c2.isFinite = true ∧ c2.toRat = 2 := by decide +kernel

theorem copysign_c1_val (x : F64) :
    (F64.copysign c1 x).isFinite = true ∧ (F64.copysign c1 x).toRat = (if x.sign then -1 else 1) ∧
    (F64.copysign c1 x).sign = x.sign := by
  have h1 : c1.isFinite = true ∧ c1.toRat = 1 ∧ c1.sign = false := by decide +kernel
  refine ⟨?_, ?_, copysign_sign c1 x⟩
  · unfold F64.copysign; split
    · exact h1.1
    · rw [neg_isFinite]; exact h1.1
  · unfold F64.copysign
    cases hx : x.sign
    · simp [h1.2.2, h1.2.1]
    · simp [h1.2.2, toRat_neg, h1.2.1]

/-! ## `m_remainder` -/

/-- The value of `m_remainder(x, y)` for finite `x` and finite nonzero `y`, with
`|x| = k |y| + R`, `0 <= R < |y|`: `sign(x) * R` below the half, `sign(x) * (R - |y|)` above,
and at the half the one of the two whose quotient is even. A zero result has the sign of `x`. -/
theorem m_remainder_val {x y : F64} (fx : x.isFinite = true) (fy : y.isFinite = true)
    (hy : y.isZero = false) (X Y R : Rat) (k : Int) (hX : X = Rat.abs x.toRat)
    (hY : Y = Rat.abs y.toRat) (hk : k = Rat.floor (X / Y)) (hR : R = X - Y * k) :
    (m_remainder x y).isFinite = true ∧
    (m_remainder x y).toRat = (if x.sign then -1 else 1) *
      (if 2 * R < Y then R else if Y < 2 * R then R - Y else if k % 2 = 0 then R else R - Y) ∧
    ((m_remainder x y).isZero = true → (m_remainder x y).sign = x.sign) ∧
    0 ≤ R ∧ R < Y ∧ 0 ≤ k := by
  have fax : (F64.abs x).isFinite = true := by rw [abs_isFinite]; exact fx
  have fay : (F64.abs y).isFinite = true := by rw [abs_isFinite]; exact fy
  have sax := (abs_fields x).1
  have say := (abs_fields y).1
  have vax : (F64.abs x).toRat = X := by rw [abs_toRat, hX]
  have vay : (F64.abs y).toRat = Y := by rw [abs_toRat, hY]
  have zay : (F64.abs y).isZero = false := by rw [abs_isZero]; exact hy
  have hY0 : 0 < Y := by
    have h1 := sign_false_nonneg fay say
    have h2 : (F64.abs y).toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat fay).2 h] at zay; cases zay
    rw [vay] at h1 h2; grind
  have hX0 : 0 ≤ X := by rw [← vax]; exact sign_false_nonneg fax sax
  obtain ⟨fm, vm, hR0, hRY, hk0, hmeq⟩ := fmod_val fax fay zay (by rw [vax]; exact hX0)
  simp only [vax, vay, abs_of_nonneg (Rat.le_of_lt hY0)] at vm hR0 hRY hk0 hmeq
  simp only [← hk] at vm hR0 hRY hk0 hmeq
  simp only [← hR] at vm hR0 hRY hmeq
  generalize hm : F64.fmod (F64.abs x) (F64.abs y) = m at fm vm hmeq
  have sm : m.sign = false := by
    rw [hmeq sax]
    by_cases h0 : R = 0
    · rw [h0, ofRat_zero]; exact zero_sign _
    · rw [ofRat_sign h0]; simp; grind
  -- `c = |y| - m`
  have repY : Rep binary64 Y := by rw [← vay]; exact toRat_rep fay
  have repR : Rep binary64 R := by rw [← vm]; exact toRat_rep fm
  have limY : Rat.abs Y < overflowLimit := by rw [← vay]; exact abs_toRat_lt fay
  have limR : Rat.abs R < overflowLimit := by rw [← vm]; exact abs_toRat_lt fm
  obtain ⟨hc1, hc2, _⟩ := sub_facts fay fm
  generalize hc : F64.sub (F64.abs y) m = c at hc1 hc2
  rw [vay, vm] at hc1 hc2
  have limYR : Rat.abs (Y - R) < overflowLimit := by
    have : Rat.abs (Y - R) ≤ Rat.abs Y := by
      rw [abs_of_nonneg (by grind), abs_of_nonneg (Rat.le_of_lt hY0)]; grind
    grind
  have fc : c.isFinite = true := by rw [hc2]; exact (ofRat_isFinite _).2 limYR
  have ltmc : F64.lt m c = decide (R < rnd (Y - R)) := by rw [lt_of_finite fm fc, vm, hc1]
  have ltcm : F64.lt c m = decide (rnd (Y - R) < R) := by rw [lt_of_finite fc fm, vm, hc1]
  -- the body
  have hbody : m_remainder x y = F64.mul (F64.copysign c1 x)
      (if F64.lt m c then m else if F64.lt c m then F64.neg c
       else F64.sub m (F64.mul c2 (F64.fmod (F64.mul cHalf (F64.sub (F64.abs x) m)) (F64.abs y)))) := by
    simp only [m_remainder, fx, fy, Bool.and_self, ↓reduceIte, isZeroC_eq, hy, Bool.false_eq_true,
      hm, hc]
  -- the value before the sign
  have hr0 : ∃ r0 : F64, (if F64.lt m c then m else if F64.lt c m then F64.neg c
       else F64.sub m (F64.mul c2 (F64.fmod (F64.mul cHalf (F64.sub (F64.abs x) m)) (F64.abs y))))
        = r0 ∧ r0.isFinite = true ∧
      r0.toRat = (if 2 * R < Y then R else if Y < 2 * R then R - Y else if k % 2 = 0 then R else R - Y) ∧
      (r0.toRat = 0 → r0.sign = false) := by
    by_cases c1' : 2 * R < Y
    · have hlt : R < rnd (Y - R) := by
        rcases half_or_sub fay say fm (by rw [vm]; exact hR0) (by rw [vm, vay]; exact hRY) with h | h
        · rw [vay] at h
          have lim2 : Rat.abs (Y / 2) < overflowLimit := by
            have : Rat.abs (Y / 2) ≤ Rat.abs Y := by
              rw [abs_of_nonneg (by grind), abs_of_nonneg (Rat.le_of_lt hY0)]; grind
            grind
          have e2 : rnd (Y / 2) = Y / 2 := ofRat_exact h lim2
          have mono := ofRat_mono (show Y / 2 ≤ Y - R by grind) ((ofRat_isFinite _).2 lim2)
            ((ofRat_isFinite _).2 limYR)
          have : rnd (Y / 2) ≤ rnd (Y - R) := mono
          grind
        · rw [vay, vm] at h
          have : rnd (Y - R) = Y - R := ofRat_exact h limYR
          grind
      refine ⟨m, by rw [ltmc]; simp [hlt], fm, by rw [vm]; simp [c1'], fun _ => sm⟩
    · by_cases c2' : Y < 2 * R
      · have hrep := sterbenz fay fm say sm (by rw [vay, vm]; grind) (by rw [vay, vm]; grind)
        rw [vay, vm] at hrep
        have ex : rnd (Y - R) = Y - R := ofRat_exact hrep limYR
        have n1 : ¬ R < rnd (Y - R) := by rw [ex]; grind
        have n2 : rnd (Y - R) < R := by rw [ex]; grind
        refine ⟨F64.neg c, by rw [ltmc, ltcm]; simp [n1, n2], by rw [neg_isFinite]; exact fc,
          by rw [toRat_neg, hc1, ex]; simp [c1', c2']; grind, fun h => ?_⟩
        rw [toRat_neg, hc1, ex] at h; grind
      · -- the tie: `2R = |y|`
        have htie : 2 * R = Y := by grind
        have hRpos : 0 < R := by grind
        have ex : rnd (Y - R) = R := by
          rw [show Y - R = R by grind]; exact ofRat_exact repR limR
        have n1 : ¬ R < rnd (Y - R) := by rw [ex]; grind
        have n2 : ¬ rnd (Y - R) < R := by rw [ex]; grind
        obtain ⟨kn, hkn⟩ : ∃ kn : Nat, k = kn := ⟨k.toNat, by omega⟩
        have hXk : X = (2 * kn + 1 : Nat) * R := by
          have : X = Y * k + R := by grind
          rw [this, hkn, ← htie]; push_cast; grind
        obtain ⟨Rn, e, hRn, he, hbnd⟩ := tie_grid fax sax fm sm (by rw [vm]; exact hRpos) kn
          (by rw [vax, vm]; exact hXk)
        rw [vm] at hRn
        -- `|x| - m = 2k R`, exact
        have v1 : X - R = ((2 * kn * Rn : Nat) : Rat) * pw e := by
          rw [hXk, hRn]; push_cast; grind
        have b1 : 2 * kn * Rn ≤ (2 * kn + 1) * Rn := Nat.mul_le_mul_right _ (by omega)
        have b1' : 2 * kn * Rn < 2 ^ 53 := by omega
        have r1 : Rep binary64 (X - R) := by rw [v1]; exact rep_of_grid b1' he
        have hRX : R ≤ X := by
          have h1 : (1 : Rat) ≤ ((2 * kn + 1 : Nat) : Rat) := by
            have : 1 ≤ 2 * kn + 1 := by omega
            exact_mod_cast this
          have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hRpos)
          rw [hXk]; grind
        have l1 : Rat.abs (X - R) < overflowLimit := by
          apply lim_of_le fax
          rw [vax, abs_of_nonneg (by grind), abs_of_nonneg hX0]; grind
        obtain ⟨f1, e1⟩ := sub_exact fax fm (by rw [vax, vm]; exact r1) (by rw [vax, vm]; exact l1)
        generalize ht1 : F64.sub (F64.abs x) m = t1 at f1 e1
        rw [vax, vm] at e1
        -- `0.5 * (|x| - m) = k R`, exact
        have v2 : cHalf.toRat * t1.toRat = ((kn * Rn : Nat) : Rat) * pw e := by
          rw [cHalf_val.2, e1, v1]; push_cast; grind
        have b2 : kn * Rn ≤ (2 * kn + 1) * Rn := Nat.mul_le_mul_right _ (by omega)
        have b2' : kn * Rn < 2 ^ 53 := by omega
        have r2 : Rep binary64 (cHalf.toRat * t1.toRat) := by
          rw [v2]; exact rep_of_grid b2' he
        have l2 : Rat.abs (cHalf.toRat * t1.toRat) < overflowLimit := by
          apply lim_of_le fax
          rw [vax, v2, abs_of_nonneg (Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))),
            abs_of_nonneg hX0]
          have h3 : ((kn * Rn : Nat) : Rat) * pw e ≤ ((2 * kn * Rn : Nat) : Rat) * pw e := by
            apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt (pw_pos _))
            exact Rat.natCast_le_natCast.2 (by rw [Nat.mul_assoc]; omega)
          rw [← v1] at h3
          grind
        obtain ⟨f2, e2⟩ := mul_exact cHalf_val.1 f1 r2 l2
        generalize ht2 : F64.mul cHalf t1 = t2 at f2 e2
        have kR : t2.toRat = (kn : Rat) * R := by
          rw [e2, v2, hRn]; push_cast; grind
        -- `fmod(k R, 2R) = (k mod 2) R`
        have t20 : 0 ≤ t2.toRat := by
          rw [kR]; exact Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt hRpos)
        obtain ⟨f3, e3, _, _, _, _⟩ := fmod_val f2 fay zay t20
        generalize ht3 : F64.fmod t2 (F64.abs y) = t3 at f3 e3
        rw [vay, abs_of_nonneg (Rat.le_of_lt hY0), kR, ← htie] at e3
        have hRne : R ≠ 0 := by grind
        have hq : (kn : Rat) * R / (2 * R) = (kn : Rat) / ((2 : Nat) : Rat) := by
          rw [Rat.div_def, Rat.div_def, inv_mul' (by decide +kernel) hRne]
          have := Rat.mul_inv_cancel R hRne
          push_cast
          grind
        rw [hq, floor_natDiv kn 2 (by decide)] at e3
        have hdm := nat_divmod_rat kn 2
        have v3 : t3.toRat = ((kn % 2 : Nat) : Rat) * R := by
          rw [e3]; rw [Rat.intCast_natCast]; push_cast at hdm ⊢; grind
        -- `2.0 * t3` and `m - 2.0 * t3`, exact
        have hpar : kn % 2 = 0 ∨ kn % 2 = 1 := by omega
        have v4 : c2.toRat * t3.toRat = if kn % 2 = 0 then 0 else Y := by
          rw [c2_val.2, v3, ← htie]
          rcases hpar with h | h <;> simp [h]
        have r4 : Rep binary64 (c2.toRat * t3.toRat) := by
          rw [v4]; split
          · exact rep_zero
          · exact repY
        have l4 : Rat.abs (c2.toRat * t3.toRat) < overflowLimit := by
          rw [v4]; split
          · rw [abs_of_nonneg Rat.le_refl]; exact overflowLimit_pos
          · exact limY
        obtain ⟨f4, e4⟩ := mul_exact c2_val.1 f3 r4 l4
        generalize ht4 : F64.mul c2 t3 = t4 at f4 e4
        have v5 : m.toRat - t4.toRat = if kn % 2 = 0 then R else -R := by
          rw [vm, e4, v4, ← htie]; split <;> grind
        have r5 : Rep binary64 (m.toRat - t4.toRat) := by
          rw [v5]; split
          · exact repR
          · exact rep_neg repR
        have l5 : Rat.abs (m.toRat - t4.toRat) < overflowLimit := by
          rw [v5]; split
          · exact limR
          · rw [abs_neg]; exact limR
        obtain ⟨f5, e5⟩ := sub_exact fm f4 r5 l5
        refine ⟨F64.sub m t4, ?_, f5, ?_, fun h => ?_⟩
        · rw [ltmc, ltcm]
          simp only [n1, n2, decide_false, Bool.false_eq_true, ↓reduceIte, ht1, ht2, ht3, ht4]
        · rw [e5, v5]
          simp only [c1', c2', ↓reduceIte, hkn]
          have : ((kn : Int) % 2 = 0) ↔ kn % 2 = 0 := by omega
          by_cases hk2 : kn % 2 = 0
          · simp [hk2, this.2 hk2]
          · have : ¬ ((kn : Int) % 2 = 0) := fun h' => hk2 (this.1 h')
            simp [hk2, this]; grind
        · rw [e5, v5] at h; split at h <;> grind
  obtain ⟨r0, hr0e, fr0, vr0, zr0⟩ := hr0
  rw [hbody, hr0e]
  obtain ⟨fs, vs, ss⟩ := copysign_c1_val x
  rw [mul_of_finite fs fr0]
  have hs0 : (F64.copysign c1 x).toRat ≠ 0 := by rw [vs]; split <;> decide
  refine ⟨?_, ?_, ?_, hR0, hRY, hk0⟩
  · split
    · exact zero_isFinite _
    · apply (ofRat_isFinite _).2
      apply lim_of_le fr0
      rw [vs]; split
      · rw [show (-1 : Rat) * r0.toRat = -r0.toRat by grind, abs_neg]; exact Rat.le_refl
      · rw [Rat.one_mul]; exact Rat.le_refl
  · split
    · rename_i h0; rw [zero_toRat, ← vr0, ← vs, h0]
    · rename_i h0
      rw [← vr0, ← vs]
      apply ofRat_exact
      · rw [vs]; split
        · rw [show (-1 : Rat) * r0.toRat = -r0.toRat by grind]; exact rep_neg (toRat_rep fr0)
        · rw [Rat.one_mul]; exact toRat_rep fr0
      · apply lim_of_le fr0
        rw [vs]; split
        · rw [show (-1 : Rat) * r0.toRat = -r0.toRat by grind, abs_neg]; exact Rat.le_refl
        · rw [Rat.one_mul]; exact Rat.le_refl
  · intro hz
    split at hz
    · rename_i h0
      have : r0.toRat = 0 := by
        rcases Rat.mul_eq_zero.1 h0 with h | h
        · exact absurd h hs0
        · exact h
      split
      · rw [zero_sign, ss, zr0 this]; cases x.sign <;> rfl
      · rename_i h1; exact absurd h0 h1
    · exfalso
      rename_i h0
      have hne : (ofRat ((F64.copysign c1 x).toRat * r0.toRat)).toRat ≠ 0 := by
        rw [ofRat_exact]
        · exact h0
        · rw [vs]; split
          · rw [show (-1 : Rat) * r0.toRat = -r0.toRat by grind]; exact rep_neg (toRat_rep fr0)
          · rw [Rat.one_mul]; exact toRat_rep fr0
        · apply lim_of_le fr0
          rw [vs]; split
          · rw [show (-1 : Rat) * r0.toRat = -r0.toRat by grind, abs_neg]; exact Rat.le_refl
          · rw [Rat.one_mul]; exact Rat.le_refl
      exact hne (toRat_of_isZero hz)

theorem remainderExact_proven : RemainderExact := by
  intro x y fx fy hy
  obtain ⟨fr, vr, zr, hR0, hRY, hk0⟩ := m_remainder_val fx fy hy (Rat.abs x.toRat) (Rat.abs y.toRat)
    _ _ rfl rfl rfl rfl
  generalize hX : Rat.abs x.toRat = X at fr vr zr hR0 hRY hk0
  generalize hY : Rat.abs y.toRat = Y at fr vr zr hR0 hRY hk0
  generalize hk : Rat.floor (X / Y) = k at fr vr zr hR0 hRY hk0
  generalize hR : X - Y * (k : Rat) = R at fr vr zr hR0 hRY hk0
  refine ⟨m_remainder x y, ?_, fr, ?_, zr⟩
  · -- through `math_2`: a finite result with `errno` 0 is returned
    have := ((math2Rules_proven (fun x y => (m_remainder x y, .zero)) "remainder"
      [.float x, .float y]).2 (.float x) (.float y) rfl).2.2 x y rfl rfl
    exact this.2.2.2.2.2.2.2.1 fr rfl
  · rw [vr]
    have sx := sign_val fx
    have sy := sign_val fy
    rw [hX] at sx; rw [hY] at sy
    have hY0 : 0 < Y := by
      have : y.toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat fy).2 h] at hy; cases hy
      have := abs_nonneg y.toRat
      rw [hY] at this
      cases hys : y.sign <;> rw [hys] at sy <;> simp at sy <;> grind
    -- `x / y = s (k + R / Y)` with `s` the product of the signs
    have hXk : X = Y * k + R := by grind
    have ht0 : 0 ≤ R / Y := by
      rw [Rat.div_def]; exact Rat.mul_nonneg hR0 (Rat.le_of_lt (Rat.inv_pos.2 hY0))
    have ht1 : R / Y < 1 := by rw [Rat.div_lt_iff hY0]; grind
    have hYne : Y ≠ 0 := by grind
    have hYi := Rat.mul_inv_cancel Y hYne
    have hq : X / Y = (k : Rat) + R / Y := by
      rw [hXk, Rat.div_def, Rat.div_def]; grind
    have hrhe := rhe_int_add k ht0 ht1
    rw [← hq] at hrhe
    have half : (R / Y < 1 / 2 ↔ 2 * R < Y) ∧ (1 / 2 < R / Y ↔ Y < 2 * R) := by
      constructor
      · rw [Rat.div_lt_iff hY0]; constructor <;> intro h <;> grind
      · rw [Rat.lt_div_iff hY0]; constructor <;> intro h <;> grind
    have hrhe' : roundHalfEven (X / Y) =
        if 2 * R < Y then k else if Y < 2 * R then k + 1 else if k % 2 = 0 then k else k + 1 := by
      rw [hrhe]
      by_cases a : 2 * R < Y
      · simp [a, half.1.2 a]
      · have a' : ¬ R / Y < 1 / 2 := fun h => a (half.1.1 h)
        by_cases b : Y < 2 * R
        · simp [a, a', b, half.2.2 b]
        · have b' : ¬ 1 / 2 < R / Y := fun h => b (half.2.1 h)
          simp [a, a', b, b']
    have hdiv : x.toRat / y.toRat = (if x.sign == y.sign then 1 else -1) * (X / Y) := by
      have hYne' : Y ≠ 0 := by grind
      have hinv : (-Y)⁻¹ = -Y⁻¹ :=
        Rat.inv_eq_of_mul_eq_one (by have := Rat.mul_inv_cancel Y hYne'; grind)
      rw [sx, sy]
      cases x.sign <;> cases y.sign <;>
        simp only [Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
          show (true == false) = false from rfl, show (false == true) = false from rfl,
          Rat.div_def, hinv] <;> grind
    rw [hdiv]
    have hrhe2 : roundHalfEven ((if x.sign == y.sign then 1 else -1) * (X / Y)) =
        (if x.sign == y.sign then 1 else -1) * roundHalfEven (X / Y) := by
      split
      · simp
      · rw [show (-1 : Rat) * (X / Y) = -(X / Y) by grind, rhe_neg]; grind
    rw [hrhe2, hrhe', sx, sy]
    cases hxs : x.sign <;> cases hys : y.sign <;>
      simp only [hxs, hys, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
        show (true == false) = false from rfl, show (false == true) = false from rfl] <;>
      (by_cases a : 2 * R < Y <;> by_cases b : Y < 2 * R <;> by_cases c : k % 2 = 0 <;>
        simp only [a, b, c, ↓reduceIte] <;> push_cast <;> grind)

end PyLean.MathInt
