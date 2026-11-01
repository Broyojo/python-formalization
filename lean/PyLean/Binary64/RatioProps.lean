import PyLean.Binary64.Props4

/-!
`float.as_integer_ratio`, through its doubling loop.
-/

namespace PyLean.Binary64

open F64

theorem exists_odd_part : ∀ M : Nat, 0 < M → ∃ o s, o % 2 = 1 ∧ M = o * 2 ^ s := by
  intro M
  induction M using Nat.strongRecOn with
  | ind M ih =>
    intro hM
    by_cases h : M % 2 = 1
    · exact ⟨M, 0, h, by simp⟩
    · obtain ⟨o, s, h1, h2⟩ := ih (M / 2) (by omega) (by omega)
      refine ⟨o, s + 1, h1, ?_⟩
      rw [Nat.pow_succ, ← Nat.mul_assoc, ← h2]
      omega

/-- `±o / 2 ^ j` is representable. -/
theorem odd_rep (sg : Int) (hs : sg = 1 ∨ sg = -1) {o j : Nat} (ho : o < 2 ^ 53) (hj : j ≤ 1074) :
    Rep binary64 ((sg : Rat) * ((o : Rat) * pw (-(j : Int)))) ∧
      Rat.abs ((sg : Rat) * ((o : Rat) * pw (-(j : Int)))) < overflowLimit := by
  have hv : 0 ≤ (o : Rat) * pw (-(j : Int)) :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))
  have hb : (o : Rat) * pw (-(j : Int)) < overflowLimit := by
    have h1 : (o : Rat) < ((2 ^ 53 : Nat) : Rat) := Rat.natCast_lt_natCast.2 ho
    have h2 : pw (-(j : Int)) ≤ pw 0 := pw_le (by omega)
    rw [pw_zero] at h2
    have h3 : (o : Rat) * pw (-(j : Int)) ≤ (o : Rat) * 1 :=
      Rat.mul_le_mul_of_nonneg_left h2 Rat.natCast_nonneg
    rw [Rat.mul_one] at h3
    have := pw_natAbs_le_limit
    grind
  rcases hs with rfl | rfl
  · have e : ((1 : Int) : Rat) = 1 := rfl
    rw [e, Rat.one_mul]
    exact ⟨⟨o, -(j : Int), ho, by simp [Fmt.etiny, binary64]; omega, Or.inl rfl⟩, by
      rw [abs_of_nonneg hv]; exact hb⟩
  · have e : ((-1 : Int) : Rat) = -1 := rfl
    have e2 : (-1 : Rat) * ((o : Rat) * pw (-(j : Int))) = -((o : Rat) * pw (-(j : Int))) := by grind
    rw [e, e2]
    exact ⟨⟨o, -(j : Int), ho, by simp [Fmt.etiny, binary64]; omega, Or.inr rfl⟩, by
      rw [abs_neg, abs_of_nonneg hv]; exact hb⟩

/-- `ratioLoop` doubles a value `±o / 2 ^ j` until it is an integer. -/
theorem ratioLoop_spec (sg : Int) (hs : sg = 1 ∨ sg = -1) {o : Nat} (hodd : o % 2 = 1) (ho : o < 2 ^ 53) :
    ∀ (j fuel : Nat) (f : F64) (e : Int), j ≤ fuel → j ≤ 1074 → f.isFinite = true →
      f.toRat = (sg : Rat) * ((o : Rat) * pw (-(j : Int))) →
      ∃ f', ratioLoop fuel f e = (f', e - j) ∧ f'.isFinite = true ∧ f'.toRat = ((sg * o : Int) : Rat) := by
  have hint : ((sg * o : Int) : Rat) = (sg : Rat) * (o : Rat) := by
    rw [Rat.intCast_mul, Rat.intCast_natCast]
  intro j
  induction j with
  | zero =>
    intro fuel f e _ _ hf hv
    have hv' : f.toRat = ((sg * o : Int) : Rat) := by
      rw [hv, hint]
      simp [pw_zero, Rat.mul_one]
    obtain ⟨h1, h2⟩ := floor_value hf
    have hne : F64.ne f (F64.floor f) = false := by
      unfold F64.ne
      rw [eq_of_finite hf h1, h2, floor_of_int hv', hv']
      simp
    refine ⟨f, ?_, hf, hv'⟩
    cases fuel with
    | zero => simp [ratioLoop]
    | succ n => simp [ratioLoop, hne]
  | succ j ih =>
    intro fuel f e hfu hj hf hv
    cases fuel with
    | zero => omega
    | succ n =>
      obtain ⟨h1, h2⟩ := floor_value hf
      have hnon : f.toRat ≠ (f.floorInt : Rat) := by
        intro hc
        rw [hv] at hc
        generalize f.floorInt = t at hc
        have hp : pw (-(((j + 1 : Nat) : Int))) * ((2 ^ (j + 1) : Nat) : Rat) = 1 := by
          rw [← pw_natCast, ← pw_add]
          have : -(((j + 1 : Nat) : Int)) + ((j + 1 : Nat) : Int) = 0 := by omega
          rw [this, pw_zero]
        have h3 : (sg : Rat) * (o : Rat) = (t : Rat) * ((2 ^ (j + 1) : Nat) : Rat) := by
          generalize pw (-(((j + 1 : Nat) : Int))) = q at *
          generalize ((2 ^ (j + 1) : Nat) : Rat) = w at *
          have e1 : (sg : Rat) * ((o : Rat) * q) * w = (t : Rat) * w := by rw [hc]
          calc (sg : Rat) * (o : Rat) = (sg : Rat) * (o : Rat) * (q * w) := by rw [hp, Rat.mul_one]
            _ = (sg : Rat) * ((o : Rat) * q) * w := by grind
            _ = (t : Rat) * w := e1
        have h4 : sg * (o : Int) = t * ((2 ^ (j + 1) : Nat) : Int) := by
          have : ((sg * (o : Int) : Int) : Rat) = ((t * ((2 ^ (j + 1) : Nat) : Int) : Int) : Rat) := by
            rw [Rat.intCast_mul, Rat.intCast_mul, Rat.intCast_natCast, Rat.intCast_natCast]; exact h3
          exact Rat.intCast_inj.1 this
        have h5 : ((2 ^ (j + 1) : Nat) : Int) = 2 * ((2 ^ j : Nat) : Int) := by
          rw [Nat.pow_succ]; omega
        rw [h5] at h4
        have h6 : (2 : Int) ∣ sg * (o : Int) := ⟨t * ((2 ^ j : Nat) : Int), by rw [h4]; grind⟩
        rcases hs with rfl | rfl <;> omega
      have hne : F64.ne f (F64.floor f) = true := by
        unfold F64.ne
        rw [eq_of_finite hf h1, h2]
        simp [hnon]
      have hd2 : d2.isFinite = true ∧ d2.toRat = 2 := by decide +kernel
      obtain ⟨hrep, hlt⟩ := odd_rep sg hs (j := j) ho (by omega)
      have hq : f.toRat * d2.toRat = (sg : Rat) * ((o : Rat) * pw (-(j : Int))) := by
        rw [hv, hd2.2]
        have : pw (-(((j + 1 : Nat) : Int))) * 2 = pw (-(j : Int)) := by
          have e : -(j : Int) = -(((j + 1 : Nat) : Int)) + 1 := by omega
          rw [e, pw_succ]; grind
        rw [← this]; grind
      have hoz : (sg : Rat) * ((o : Rat) * pw (-(j : Int))) ≠ 0 := by
        have h7 : (0 : Rat) < (o : Rat) * pw (-(j : Int)) :=
          Rat.mul_pos (natCast_pos' (by omega)) (pw_pos _)
        rcases hs with rfl | rfl
        · have e : ((1 : Int) : Rat) = 1 := rfl
          rw [e]; grind
        · have e : ((-1 : Int) : Rat) = -1 := rfl
          rw [e]; grind
      have hm : (F64.mul f d2) = ofRat ((sg : Rat) * ((o : Rat) * pw (-(j : Int)))) := by
        rw [mul_of_finite hf hd2.1, hq]; simp [hoz]
      have hf2 : (F64.mul f d2).isFinite = true := by
        rw [hm]; exact (ofRat_isFinite _).2 hlt
      have hv2 : (F64.mul f d2).toRat = (sg : Rat) * ((o : Rat) * pw (-(j : Int))) := by
        rw [hm]; exact ofRat_exact hrep hlt
      obtain ⟨f', e1, e2, e3⟩ := ih n (F64.mul f d2) (e - 1) (by omega) (by omega) hf2 hv2
      refine ⟨f', ?_, e2, e3⟩
      simp only [ratioLoop, hne, ↓reduceIte, e1]
      congr 1
      omega

theorem coprime_two_pow {o : Nat} (hodd : o % 2 = 1) (k : Nat) : Nat.gcd o (2 ^ k) = 1 := by
  have h2 : Nat.gcd o 2 = 1 := by
    have hd : Nat.gcd o 2 ∣ 2 := Nat.gcd_dvd_right o 2
    have hle : Nat.gcd o 2 ≤ 2 := Nat.le_of_dvd (by omega) hd
    have hd2 : Nat.gcd o 2 ∣ o := Nat.gcd_dvd_left o 2
    have hpos : 0 < Nat.gcd o 2 := Nat.gcd_pos_of_pos_right _ (by omega)
    by_cases h : Nat.gcd o 2 = 2
    · rw [h] at hd2; omega
    · omega
  exact Nat.Coprime.pow_right k h2

/-- `x.as_integer_ratio()` is exact, in lowest terms, with a positive denominator, and
raises for infinities and NaNs. -/
def AsIntegerRatioExact : Prop :=
  ∀ x : F64,
    (x.isFinite = true → ∃ n d : Int, float_as_integer_ratio x = .ok (n, d) ∧ 0 < d ∧
      (n : Rat) / d = x.toRat ∧ Nat.gcd n.natAbs d.natAbs = 1) ∧
    (x.isInf = true → float_as_integer_ratio x =
      .error (.overflowError "cannot convert Infinity to integer ratio")) ∧
    (x.isNaN = true → float_as_integer_ratio x =
      .error (.valueError "cannot convert NaN to integer ratio"))

theorem asIntegerRatioExact_proven : AsIntegerRatioExact := by
  intro x
  refine ⟨fun hx => ?_, fun hi => ?_, fun hn => ?_⟩
  · have hdef : float_as_integer_ratio x =
        (let t := F64.frexp x
         let u := ratioLoop 300 t.1 t.2
         match PyLong_FromDouble u.1 with
         | .error e => .error e
         | .ok numerator =>
           if 0 < u.2 then .ok (numerator * 2 ^ u.2.toNat, 1)
           else .ok (numerator, 2 ^ (-u.2).toNat)) := by
      simp [float_as_integer_ratio, isInf_false_of_finite hx, isNaN_false_of_finite hx]
      rfl
    rw [hdef]
    cases hz : x.isZero
    · have hM := mant_pos_of_not_zero hz
      obtain ⟨o, s, hodd, hMs⟩ := exists_odd_part x.mant hM
      have hMlt := mant_lt x
      have hb1 : x.mant < 2 ^ (Nat.log2 x.mant + 1) := Nat.lt_log2_self
      have hb53 : Nat.log2 x.mant + 1 ≤ 53 := by
        have := (Nat.log2_lt (by omega)).2 hMlt
        omega
      have hfr : F64.frexp x = (ofRat (if x.sign then -mkRat x.mant (2 ^ (Nat.log2 x.mant + 1))
          else mkRat x.mant (2 ^ (Nat.log2 x.mant + 1))),
          x.lsbExp + ((Nat.log2 x.mant + 1 : Nat) : Int)) := by
        simp [F64.frexp, hx, hz]
      generalize Nat.log2 x.mant + 1 = b at *
      have hop : 0 < o := by omega
      have hsle : 2 ^ s ≤ x.mant := by rw [hMs]; exact Nat.le_mul_of_pos_left _ hop
      have hole : o ≤ x.mant := by rw [hMs]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos s)
      have hsb : s < b := (Nat.pow_lt_pow_iff_right (a := 2) (by omega)).1 (by omega)
      have hoLT : o < 2 ^ 53 := by omega
      have hvv : mkRat x.mant (2 ^ b) = (o : Rat) * pw (-((b - s : Nat) : Int)) := by
        rw [Rat.mkRat_eq_div, Rat.intCast_natCast, hMs, Rat.natCast_mul, ← pw_natCast, ← pw_natCast,
          Rat.div_def, ← pw_neg, Rat.mul_assoc, ← pw_add]
        have e : ((s : Nat) : Int) + -((b : Nat) : Int) = -((b - s : Nat) : Int) := by omega
        rw [e]
      generalize hsg : (if x.sign then (-1 : Int) else 1) = sg
      have hs1 : sg = 1 ∨ sg = -1 := by
        rw [← hsg]; split
        · right; rfl
        · left; rfl
      have hval : (if x.sign then -mkRat x.mant (2 ^ b) else mkRat x.mant (2 ^ b)) =
          (sg : Rat) * ((o : Rat) * pw (-((b - s : Nat) : Int))) := by
        rw [hvv, ← hsg]
        cases x.sign
        · simp only [Bool.false_eq_true, ↓reduceIte]
          show _ = ((1 : Int) : Rat) * _
          have e : ((1 : Int) : Rat) = 1 := rfl
          rw [e, Rat.one_mul]
        · simp only [↓reduceIte]
          show _ = ((-1 : Int) : Rat) * _
          have e : ((-1 : Int) : Rat) = -1 := rfl
          rw [e]; grind
      obtain ⟨hrep, hlt⟩ := odd_rep sg hs1 (j := b - s) hoLT (by omega)
      rw [hval] at hfr
      have hf0 := (ofRat_isFinite _).2 hlt
      have hv0 := ofRat_exact hrep hlt
      obtain ⟨f', e1, e2, e3⟩ := ratioLoop_spec sg hs1 hodd hoLT (b - s) 300 _
        (x.lsbExp + (b : Int)) (by omega) (by omega) hf0 hv0
      simp only [hfr, e1]
      rw [fromDouble_finite e2, truncInt_of_int e3]
      have hexp : x.lsbExp + (b : Int) - ((b - s : Nat) : Int) = x.lsbExp + s := by omega
      rw [hexp]
      have hxv : x.toRat = (sg : Rat) * ((o : Rat) * pw (x.lsbExp + s)) := by
        have e4 : (x.mant : Rat) * pw x.lsbExp = (o : Rat) * pw (x.lsbExp + s) := by
          rw [hMs, Rat.natCast_mul, ← pw_natCast, Rat.mul_assoc, ← pw_add]
          have e : ((s : Nat) : Int) + x.lsbExp = x.lsbExp + s := by omega
          rw [e]
        rw [toRat_of_finite hx, e4, ← hsg]
        cases x.sign
        · simp only [Bool.false_eq_true, ↓reduceIte]
          show _ = ((1 : Int) : Rat) * _
          have e : ((1 : Int) : Rat) = 1 := rfl
          rw [e, Rat.one_mul]
        · simp only [↓reduceIte]
          show _ = ((-1 : Int) : Rat) * _
          have e : ((-1 : Int) : Rat) = -1 := rfl
          rw [e]; grind
      have hnat : (sg * (o : Int)).natAbs = o := by rcases hs1 with rfl | rfl <;> omega
      generalize hE : x.lsbExp + (s : Int) = E at *
      by_cases hpos : 0 < E
      · simp only [hpos, ↓reduceIte]
        refine ⟨sg * o * 2 ^ E.toNat, 1, rfl, by decide, ?_, by simp⟩
        have e5 : pw E = ((2 ^ E.toNat : Nat) : Rat) := by
          rw [← pw_natCast]
          have : ((E.toNat : Nat) : Int) = E := by omega
          rw [this]
        have e6 : ((2 : Int) ^ E.toNat) = ((2 ^ E.toNat : Nat) : Int) := by push_cast; rfl
        rw [hxv, e5, e6, Rat.intCast_mul, Rat.intCast_mul, Rat.intCast_natCast, Rat.intCast_natCast]
        have e7 : ((1 : Int) : Rat) = 1 := rfl
        rw [e7]
        simp only [Rat.div_def]
        have e8 : (1 : Rat)⁻¹ = 1 := Rat.inv_eq_of_mul_eq_one (by simp)
        rw [e8]; grind
      · simp only [hpos, ↓reduceIte]
        have hk : (((-E).toNat : Nat) : Int) = -E := by omega
        have e6 : ((2 : Int) ^ (-E).toNat) = ((2 ^ (-E).toNat : Nat) : Int) := by push_cast; rfl
        refine ⟨sg * o, 2 ^ (-E).toNat, rfl, ?_, ?_, ?_⟩
        · rw [e6]; have := Nat.two_pow_pos (-E).toNat; omega
        · have e5 : pw E = (((2 ^ (-E).toNat : Nat) : Rat))⁻¹ := by
            rw [← pw_natCast, hk, pw_neg, Rat.inv_inv]
          rw [hxv, e5, e6, Rat.intCast_mul, Rat.intCast_natCast, Rat.intCast_natCast, Rat.div_def]
          grind
        · rw [hnat, e6, Int.natAbs_natCast]
          exact coprime_two_pow hodd _
    · have hfr : F64.frexp x = (x, 0) := by simp [F64.frexp, hx, hz]
      have ht := toRat_of_isZero hz
      obtain ⟨h1, h2⟩ := floor_value hx
      have hne : F64.ne x (F64.floor x) = false := by
        unfold F64.ne
        rw [eq_of_finite hx h1, h2, zero_floorInt hz, ht]
        rfl
      have hl : ratioLoop 300 x 0 = (x, 0) := by
        show (if F64.ne x (F64.floor x) then _ else (x, 0)) = _
        simp [hne]
      simp only [hfr, hl]
      rw [fromDouble_finite hx, truncInt_of_int (t := 0) (by rw [ht]; rfl)]
      refine ⟨0, 1, rfl, by decide, ?_, by simp⟩
      rw [ht]; simp [Rat.div_def]
  · simp [float_as_integer_ratio, hi]
  · simp [float_as_integer_ratio, not_inf_of_nan hn, hn]

end PyLean.Binary64
