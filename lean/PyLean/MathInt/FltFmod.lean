import PyLean.MathInt.FltIsclose
import PyLean.MathInt.FltFrexp

/-!
# Properties: `fmod` and `modf`

`math_fmod_impl` and `math_modf_impl` (Modules/mathmodule.c:1555-1570, 1762-1791) against
Doc/library/math.rst: `fmod(x, y)` is "exactly (mathematically; to infinite precision) equal to
`x - n*y` for some integer `n` such that the result has the same sign as `x` and magnitude less
than `abs(y)`", with `fmod(x, inf) == x` and `ValueError` for `fmod(inf, y)` and `fmod(x, 0)`;
`modf(x)` gives "the fractional and integer parts of x. Both results carry the sign of x".
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-! ## Integer division inside the rationals -/

theorem nat_divmod_rat (A B : Nat) :
    (A : Rat) = ((A / B : Nat) : Rat) * (B : Rat) + ((A % B : Nat) : Rat) := by
  have := Nat.div_add_mod A B
  have h2 : ((B * (A / B) + A % B : Nat) : Rat) = (A : Rat) := by rw [this]
  rw [Rat.natCast_add, Rat.natCast_mul] at h2
  grind

theorem floor_natDiv (A B : Nat) (hB : 0 < B) :
    Rat.floor ((A : Rat) / (B : Rat)) = ((A / B : Nat) : Int) := by
  have hBq : (0 : Rat) < (B : Rat) := natCast_pos' hB
  have hdm := nat_divmod_rat A B
  have hm : ((A % B : Nat) : Rat) < (B : Rat) := Rat.natCast_lt_natCast.2 (Nat.mod_lt _ hB)
  have hm0 : (0 : Rat) ≤ ((A % B : Nat) : Rat) := Rat.natCast_nonneg
  have e1 : ((((A / B : Nat) : Int) + 1 : Int) : Rat) = ((A / B : Nat) : Rat) + 1 := by
    rw [Rat.intCast_add, Rat.intCast_natCast]; rfl
  have e0 : (((A / B : Nat) : Int) : Rat) = ((A / B : Nat) : Rat) := Rat.intCast_natCast _
  apply Int.le_antisymm
  · have : Rat.floor ((A : Rat) / (B : Rat)) < ((A / B : Nat) : Int) + 1 := by
      rw [Rat.floor_lt_iff, e1, Rat.div_lt_iff hBq]
      grind
    omega
  · rw [Rat.le_floor_iff, e0]
    apply Rat.not_lt.1
    rw [Rat.div_lt_iff hBq]
    grind

theorem inv_mul' {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  apply Rat.inv_eq_of_mul_eq_one
  have h1 := Rat.mul_inv_cancel a ha
  have h2 := Rat.mul_inv_cancel b hb
  rw [show a * b * (a⁻¹ * b⁻¹) = (a * a⁻¹) * (b * b⁻¹) by grind, h1, h2, Rat.mul_one]

/-- The value of a finite float: its sign times `mant * 2 ^ lsbExp`. -/
theorem toRat_abs_val {x : F64} (hf : x.isFinite = true) :
    Rat.abs x.toRat = (x.mant : Rat) * pw x.lsbExp := by
  have h0 : 0 ≤ (x.mant : Rat) * pw x.lsbExp :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))
  rw [toRat_of_finite hf]
  split
  · rw [abs_neg, abs_of_nonneg h0]
  · rw [abs_of_nonneg h0]

theorem sign_val {x : F64} (hf : x.isFinite = true) :
    x.toRat = (if x.sign then -Rat.abs x.toRat else Rat.abs x.toRat) := by
  rw [toRat_abs_val hf, toRat_of_finite hf]

/-! ## `fmod` -/

/-- The remainder `C fmod` computes on magnitudes is a multiple of the finer of the two grids,
below both magnitudes: representable. -/
theorem fmod_rem {x y : F64} (fx : x.isFinite = true) (fy : y.isFinite = true)
    (hy : y.isZero = false) :
    let ax := Rat.abs x.toRat
    let ay := Rat.abs y.toRat
    let k := Rat.floor (ax / ay)
    let r := ax - ay * (k : Rat)
    Rep binary64 r ∧ 0 ≤ r ∧ r < ay ∧ 0 ≤ k := by
  have hmy := mant_pos_of_not_zero hy
  generalize he : min x.lsbExp y.lsbExp = e
  have hex : e ≤ x.lsbExp := by omega
  have hey : e ≤ y.lsbExp := by omega
  have hA : Rat.abs x.toRat = ((x.mant * 2 ^ (x.lsbExp - e).toNat : Nat) : Rat) * pw e := by
    rw [toRat_abs_val fx, Rat.natCast_mul, ← pw_natCast, Rat.mul_assoc, ← pw_add]
    congr 2; omega
  have hB : Rat.abs y.toRat = ((y.mant * 2 ^ (y.lsbExp - e).toNat : Nat) : Rat) * pw e := by
    rw [toRat_abs_val fy, Rat.natCast_mul, ← pw_natCast, Rat.mul_assoc, ← pw_add]
    congr 2; omega
  generalize hAd : x.mant * 2 ^ (x.lsbExp - e).toNat = A at hA
  generalize hBd : y.mant * 2 ^ (y.lsbExp - e).toNat = B at hB
  have hB0 : 0 < B := by rw [← hBd]; exact Nat.mul_pos hmy (Nat.two_pow_pos _)
  have hpe := pw_pos e
  have hq : Rat.abs x.toRat / Rat.abs y.toRat = (A : Rat) / (B : Rat) := by
    have hBne : (B : Rat) ≠ 0 := by have := natCast_pos' hB0; grind
    rw [hA, hB, Rat.div_def, Rat.div_def, inv_mul' hBne (pw_ne e)]
    rw [show (A : Rat) * pw e * ((B : Rat)⁻¹ * (pw e)⁻¹) = (A : Rat) * (B : Rat)⁻¹ * (pw e * (pw e)⁻¹)
      by grind, pw_mul_inv, Rat.mul_one]
  simp only []
  rw [hq, floor_natDiv A B hB0]
  have hr : Rat.abs x.toRat - Rat.abs y.toRat * (((A / B : Nat) : Int) : Rat) =
      ((A % B : Nat) : Rat) * pw e := by
    rw [hA, hB, Rat.intCast_natCast]
    have := nat_divmod_rat A B
    grind
  rw [hr]
  have hmodlt : A % B < B := Nat.mod_lt _ hB0
  refine ⟨⟨A % B, e, ?_, ?_, Or.inl rfl⟩, Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt hpe), ?_, by first | exact Int.natCast_nonneg _ | exact Int.ediv_nonneg (by omega) (by omega)⟩
  · -- the multiplier fits in 53 bits
    rcases Int.le_total x.lsbExp y.lsbExp with h | h
    · have : e = x.lsbExp := by omega
      have hA' : A = x.mant := by rw [← hAd, this]; simp
      have := Nat.mod_le A B
      have := mant_lt x
      show A % B < 2 ^ 53; omega
    · have : e = y.lsbExp := by omega
      have hB' : B = y.mant := by rw [← hBd, this]; simp
      have := mant_lt y
      show A % B < 2 ^ 53; omega
  · have := lsbExp_ge x; have := lsbExp_ge y
    show binary64.etiny ≤ e; simp [Fmt.etiny, binary64]; omega
  · rw [hB]; exact (Rat.mul_lt_mul_right hpe).2 (Rat.natCast_lt_natCast.2 hmodlt)

/-- `fmod` for every argument object. -/
def FmodDoc : Prop :=
  (∀ ox oy e, convDouble ox = .error e → math_fmod ox oy = .error e) ∧
  (∀ ox oy x e, convDouble ox = .ok x → convDouble oy = .error e → math_fmod ox oy = .error e) ∧
  ∀ x y : F64,
    let r := math_fmod (.float x) (.float y)
    (x.isFinite = true → y.isInf = true → r = .ok x) ∧
    ((x.isNaN || y.isNaN) = true → ∃ v, r = .ok v ∧ v.isNaN = true) ∧
    ((x.isNaN || y.isNaN) = false → (x.isInf || y.isZero) = true →
      r = .error (.valueError "math domain error")) ∧
    (x.isFinite = true → y.isFinite = true → y.isZero = false →
      ∃ v, r = .ok v ∧ v.isFinite = true ∧ (∃ n : Int, v.toRat = x.toRat - n * y.toRat) ∧
        Rat.abs v.toRat < Rat.abs y.toRat ∧ v.sign = x.sign)

theorem fmodDoc_proven : FmodDoc := by
  refine ⟨fun ox oy e he => ?_, fun ox oy x e hx he => ?_, fun x y => ⟨fun fx hi => ?_, fun hn => ?_,
    fun hn hiz => ?_, fun fx fy hy => ?_⟩⟩
  · simp [math_fmod, he, bind, Except.bind]
  · simp [math_fmod, hx, he, bind, Except.bind]
  · simp [math_fmod, convDouble, hi, fx, bind, Except.bind, pure, Except.pure]
  · have hf : (F64.fmod x y).isNaN = true := by
      unfold F64.fmod; simp [hn, qnan_facts.2]
    have hnn : (!x.isNaN && !y.isNaN) = false := by
      cases h1 : x.isNaN <;> cases h2 : y.isNaN <;> simp_all
    refine ⟨F64.fmod x y, ?_, hf⟩
    simp only [math_fmod, convDouble, bind, Except.bind]
    split
    · rename_i h
      have : x.isNaN = false := by
        cases hx : x.isFinite
        · simp [hx] at h
        · exact isNaN_false_of_finite hx
      have : y.isNaN = false := by
        simp at h; exact not_nan_of_inf h.1
      simp_all
    · simp [hf, hnn, finishErrno_zero]
  · have hx : x.isNaN = false := by cases h : x.isNaN <;> simp_all
    have hyn : y.isNaN = false := by cases h : y.isNaN <;> simp_all
    have hf : F64.fmod x y = qnan := by
      unfold F64.fmod; simp [hiz, hx, hyn]
    have hskip : (y.isInf && x.isFinite) = false := by
      cases hxi : x.isInf
      · have hyz : y.isZero = true := by simpa [hxi] using hiz
        have : y.isInf = false := isInf_false_of_finite (isFinite_of_isZero hyz)
        simp [this]
      · simp [not_finite_of_inf hxi]
    simp only [math_fmod, convDouble, bind, Except.bind, hskip, Bool.false_eq_true, ↓reduceIte, hf,
      qnan_facts.2, hx, hyn]
    decide +kernel
  · obtain ⟨hrep, hr0, hrlt, hk0⟩ := fmod_rem fx fy hy
    generalize hR : Rat.abs x.toRat - Rat.abs y.toRat * ((Rat.floor (Rat.abs x.toRat / Rat.abs y.toRat)
      : Int) : Rat) = R at hrep hr0 hrlt
    have hyi : y.isInf = false := isInf_false_of_finite fy
    have hfm : F64.fmod x y = if R = 0 then F64.zero x.sign else ofRat (if x.sign then -R else R) := by
      unfold F64.fmod
      simp only [isNaN_false_of_finite fx, isNaN_false_of_finite fy, isInf_false_of_finite fx, hy,
        hyi, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      rw [← abs_eq_ite, ← abs_eq_ite, hR]
    have hlim : Rat.abs R < overflowLimit := by
      rw [abs_of_nonneg hr0]
      have := abs_toRat_lt fy; grind
    -- the value of the result
    have hv : ∃ v, F64.fmod x y = v ∧ v.isFinite = true ∧ v.toRat = (if x.sign then -R else R) ∧
        v.sign = x.sign := by
      rw [hfm]
      by_cases h0 : R = 0
      · refine ⟨_, if_pos h0, zero_isFinite _, ?_, zero_sign _⟩
        rw [zero_toRat, h0]; simp
      · have hrep' : Rep binary64 (if x.sign then -R else R) := by
          split
          · exact rep_neg hrep
          · exact hrep
        have hlim' : Rat.abs (if x.sign then -R else R) < overflowLimit := by
          split
          · rw [abs_neg]; exact hlim
          · exact hlim
        refine ⟨_, if_neg h0, (ofRat_isFinite _).2 hlim', ofRat_exact hrep' hlim', ?_⟩
        have hne : (if x.sign then -R else R) ≠ 0 := by split <;> grind
        rw [ofRat_sign hne]
        have hpos : 0 < R := by grind
        cases x.sign <;> simp <;> grind
    obtain ⟨v, hvdef, vf, vv, vs⟩ := hv
    refine ⟨v, ?_, vf, ?_, ?_, vs⟩
    · simp only [math_fmod, convDouble, bind, Except.bind, hyi, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte]
      rw [hvdef, isNaN_false_of_finite vf]
      simp [finishErrno_zero]
    · -- `x - v = n * y`
      generalize hk : Rat.floor (Rat.abs x.toRat / Rat.abs y.toRat) = k at hR
      refine ⟨if x.sign == y.sign then k else -k, ?_⟩
      have sx := sign_val fx
      have sy := sign_val fy
      rw [vv, ← hR]
      cases hxs : x.sign <;> cases hys : y.sign <;> simp only [hxs, hys] at sx sy ⊢ <;>
        simp only [Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Rat.intCast_neg] <;>
        (try simp only [show (true == false) = false from rfl, show (false == true) = false from rfl,
          Bool.false_eq_true, ↓reduceIte, Rat.intCast_neg]) <;> rw [sx, sy] <;> grind
    · rw [vv]; split
      · rw [abs_neg, abs_of_nonneg hr0]; exact hrlt
      · rw [abs_of_nonneg hr0]; exact hrlt

/-! ## `modf` -/

/-- The fractional part of a finite float is representable. -/
theorem frac_rep {x : F64} (hf : x.isFinite = true) :
    Rep binary64 (x.toRat - (x.truncInt : Rat)) := by
  by_cases hl : 0 ≤ x.lsbExp
  · have hk : (x.lsbExp.toNat : Int) = x.lsbExp := by omega
    have hint : x.toRat = ((if x.sign then -((x.mant * 2 ^ x.lsbExp.toNat : Nat) : Int) else
        ((x.mant * 2 ^ x.lsbExp.toNat : Nat) : Int) : Int) : Rat) := by
      rw [toRat_of_finite hf]
      have : (x.mant : Rat) * pw x.lsbExp = ((x.mant * 2 ^ x.lsbExp.toNat : Nat) : Rat) := by
        rw [Rat.natCast_mul, ← pw_natCast, hk]
      rw [this]
      split <;> simp [Rat.intCast_natCast]
    rw [truncInt_of_int hint, hint, show ∀ q : Rat, q - q = 0 from fun q => by grind]
    exact rep_zero
  · generalize hk : (-x.lsbExp).toNat = k
    have hk' : x.lsbExp = -(k : Int) := by omega
    have hP : 0 < 2 ^ k := Nat.two_pow_pos k
    have hPq : ((2 ^ k : Nat) : Rat) ≠ 0 := by have := natCast_pos' hP; grind
    have hpw : pw x.lsbExp = (((2 ^ k : Nat) : Rat))⁻¹ := by rw [hk', pw_neg, pw_natCast]
    have hdm := nat_divmod_rat x.mant (2 ^ k)
    have hinv := Rat.mul_inv_cancel _ hPq
    have hval : (x.mant : Rat) * pw x.lsbExp - ((x.mant / 2 ^ k : Nat) : Rat) =
        ((x.mant % 2 ^ k : Nat) : Rat) * pw x.lsbExp := by
      rw [hpw]
      generalize ((x.mant / 2 ^ k : Nat) : Rat) = q at hdm
      generalize ((x.mant % 2 ^ k : Nat) : Rat) = r at hdm
      generalize ((2 ^ k : Nat) : Rat) = P at hdm hinv hPq
      rw [hdm]
      grind
    have hfl : Rat.floor ((x.mant : Rat) * pw x.lsbExp) = ((x.mant / 2 ^ k : Nat) : Int) := by
      rw [hpw, ← Rat.div_def]; exact floor_natDiv _ _ hP
    have hrep : Rep binary64 (((x.mant % 2 ^ k : Nat) : Rat) * pw x.lsbExp) := by
      refine ⟨x.mant % 2 ^ k, x.lsbExp, ?_, ?_, Or.inl rfl⟩
      · have := Nat.mod_le x.mant (2 ^ k); have := mant_lt x; show x.mant % 2 ^ k < 2 ^ 53; omega
      · have := lsbExp_ge x; show binary64.etiny ≤ x.lsbExp; simp [Fmt.etiny, binary64]; omega
    have e0 : (((x.mant / 2 ^ k : Nat) : Int) : Rat) = ((x.mant / 2 ^ k : Nat) : Rat) :=
      Rat.intCast_natCast _
    cases hs : x.sign
    · have ht : x.truncInt = ((x.mant / 2 ^ k : Nat) : Int) := by
        unfold F64.truncInt F64.floorInt
        rw [toRat_of_finite hf, hs]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact hfl
      rw [ht, e0, toRat_of_finite hf, hs]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hval]; exact hrep
    · have ht : x.truncInt = -((x.mant / 2 ^ k : Nat) : Int) := by
        unfold F64.truncInt F64.ceilInt
        rw [toRat_of_finite hf, hs]
        simp only [↓reduceIte]
        rw [Rat.ceil_eq_neg_floor_neg, Rat.neg_neg, hfl]
      rw [ht, Rat.intCast_neg, e0, toRat_of_finite hf, hs]
      simp only [↓reduceIte]
      rw [show -((x.mant : Rat) * pw x.lsbExp) - -((x.mant / 2 ^ k : Nat) : Rat) =
        -((x.mant : Rat) * pw x.lsbExp - ((x.mant / 2 ^ k : Nat) : Rat)) by grind, hval]
      exact rep_neg hrep

theorem copysign_sign (y x : F64) : (F64.copysign y x).sign = x.sign := by
  unfold F64.copysign
  split
  · rename_i h; simpa using h
  · rename_i h; rw [(neg_fields y).1]; cases hy : y.sign <;> cases hx : x.sign <;> simp_all

theorem copysign_toRat {y x : F64} (h : y.toRat = 0 ∨ (y.sign = x.sign)) :
    (F64.copysign y x).toRat = y.toRat := by
  unfold F64.copysign
  split
  · rfl
  · rename_i hne
    rcases h with h | h
    · rw [toRat_neg, h]; simp
    · simp [h] at hne

theorem truncInt_sign {x : F64} (hf : x.isFinite = true) (hz : x.isZero = false) :
    (x.sign = false → 0 ≤ x.truncInt) ∧ (x.sign = true → x.truncInt ≤ 0) := by
  obtain ⟨tb1, tb2⟩ := trunc_bounds hf
  have e2 := toRat_neg_iff_sign hf hz
  have hne : x.toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat hf).2 h] at hz; cases hz
  constructor
  · intro hs
    rw [hs] at e2
    have hp : 0 < x.toRat := by simp at e2; grind
    have := (tb1 hp).2
    have : ((-1 : Int) : Rat) < (x.truncInt : Rat) := by
      rw [show ((-1 : Int) : Rat) = -1 from rfl]; grind
    have : (-1 : Int) < x.truncInt := by exact_mod_cast this
    omega
  · intro hs
    rw [hs] at e2
    have hn : x.toRat < 0 := by simpa using e2
    have := (tb2 hn).2
    have : (x.truncInt : Rat) < ((1 : Int) : Rat) := by
      rw [show ((1 : Int) : Rat) = 1 from rfl]; grind
    have : x.truncInt < 1 := by exact_mod_cast this
    omega

/-- `modf` for every argument object. -/
def ModfDoc : Prop :=
  (∀ o e, convDouble o = .error e → math_modf o = .error e) ∧
  ∀ x : F64,
    (x.isNaN = true → math_modf (.float x) = .ok (x, x)) ∧
    (x.isInf = true → math_modf (.float x) = .ok (F64.zero x.sign, x)) ∧
    (x.isFinite = true → ∃ f i, math_modf (.float x) = .ok (f, i) ∧ f.isFinite = true ∧
      i.isFinite = true ∧ i.toRat = x.truncInt ∧ f.toRat + i.toRat = x.toRat ∧
      Rat.abs f.toRat < 1 ∧ f.sign = x.sign ∧ i.sign = x.sign)

theorem modfDoc_proven : ModfDoc := by
  refine ⟨fun o e he => by simp [math_modf, he, bind, Except.bind], fun x => ⟨fun hn => ?_,
    fun hi => ?_, fun hf => ?_⟩⟩
  · simp [math_modf, convDouble, hn, not_inf_of_nan hn, bind, Except.bind, pure, Except.pure]
  · simp [math_modf, convDouble, hi, bind, Except.bind, pure, Except.pure, copysign_c0]
  · have hi := isInf_false_of_finite hf
    have hn := isNaN_false_of_finite hf
    have hm : math_modf (.float x) = .ok (cModf x) := by
      simp [math_modf, convDouble, hi, hn, bind, Except.bind, pure, Except.pure]
    rw [hm]
    unfold cModf
    by_cases hz : x.isZero = true
    · have ht : F64.trunc x = x := by simp [F64.trunc, hn, hz]
      rw [ht]
      have hsub : (F64.sub x x).toRat = 0 ∧ (F64.sub x x).isFinite = true := by
        obtain ⟨v, f, _⟩ := sub_facts hf hf
        rw [v, f, show x.toRat - x.toRat = 0 by grind, rnd_zero]
        exact ⟨rfl, ofRat_zero_finite⟩
      have htr : x.truncInt = 0 := by
        unfold F64.truncInt F64.floorInt F64.ceilInt; rw [toRat_of_isZero hz]; split <;> rfl
      refine ⟨_, _, rfl, ?_, hf, ?_, ?_, ?_, copysign_sign _ _, rfl⟩
      · unfold F64.copysign; split
        · exact hsub.2
        · rw [neg_isFinite]; exact hsub.2
      · rw [toRat_of_isZero hz, htr]; rfl
      · rw [copysign_toRat (Or.inl hsub.1), hsub.1, toRat_of_isZero hz]; exact Rat.add_zero 0
      · rw [copysign_toRat (Or.inl hsub.1), hsub.1]; decide
    · have hz' : x.isZero = false := by simpa using hz
      obtain ⟨i1, i2⟩ := trunc_value hf hz'
      obtain ⟨dv, df, _⟩ := sub_facts hf i1
      rw [i2] at dv df
      have hrep := frac_rep hf
      obtain ⟨tb1, tb2⟩ := trunc_bounds hf
      have hne : x.toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat hf).2 h] at hz'; cases hz'
      have hd1 : Rat.abs (x.toRat - (x.truncInt : Rat)) < 1 := by
        rw [abs_eq_ite]
        by_cases hp : 0 < x.toRat
        · have := tb1 hp; split <;> grind
        · have hneg : x.toRat < 0 := by grind
          have := tb2 hneg; split <;> grind
      have hone : (1 : Rat) ≤ overflowLimit := by
        unfold overflowLimit
        have a : (1 : Rat) ≤ pw 970 := by
          have := pw_le (show (0 : Int) ≤ 970 by omega); rwa [pw_zero] at this
        have b : (1 : Rat) ≤ ((2 ^ 54 - 1 : Nat) : Rat) := by
          have : ((1 : Nat) : Rat) ≤ ((2 ^ 54 - 1 : Nat) : Rat) := Rat.natCast_le_natCast.2 (by decide)
          simpa using this
        have := Rat.mul_le_mul_of_nonneg_left a (Rat.le_trans (by decide) b)
        rw [Rat.mul_one] at this; exact Rat.le_trans b this
      have hlim : Rat.abs (x.toRat - (x.truncInt : Rat)) < overflowLimit := by grind
      have hval : (F64.sub x (F64.trunc x)).toRat = x.toRat - (x.truncInt : Rat) := by
        rw [dv]; exact ofRat_exact hrep hlim
      have hfin : (F64.sub x (F64.trunc x)).isFinite = true := by
        rw [df]; exact (ofRat_isFinite _).2 hlim
      have hsg : (F64.sub x (F64.trunc x)).toRat = 0 ∨ (F64.sub x (F64.trunc x)).sign = x.sign := by
        by_cases h0 : (F64.sub x (F64.trunc x)).toRat = 0
        · left; exact h0
        · right
          have hz2 : (F64.sub x (F64.trunc x)).isZero = false := by
            cases h : (F64.sub x (F64.trunc x)).isZero
            · rfl
            · exact absurd (toRat_of_isZero h) h0
          have e1 := toRat_neg_iff_sign hfin hz2
          have e2 := toRat_neg_iff_sign hf hz'
          rw [hval] at e1 h0
          have hsame : (x.toRat - (x.truncInt : Rat) < 0) = (x.toRat < 0) := by
            apply propext
            by_cases hp : 0 < x.toRat
            · have := tb1 hp; constructor <;> intro h <;> grind
            · have hneg : x.toRat < 0 := by grind
              have := tb2 hneg; constructor <;> intro h <;> grind
          rw [hsame, e2] at e1
          revert e1
          cases (F64.sub x (F64.trunc x)).sign <;> cases x.sign <;> simp
      have htsign : (F64.trunc x).sign = x.sign := by
        have e : F64.trunc x = ofIntS x.sign x.truncInt := by simp [F64.trunc, hn, hf, hz']
        rw [e]; unfold ofIntS
        split
        · exact zero_sign _
        · rename_i ht0
          rw [show F64.ofInt x.truncInt = ofRat (x.truncInt : Rat) from rfl]
          have hne' : ((x.truncInt : Int) : Rat) ≠ 0 := by
            intro h; apply ht0; exact_mod_cast h
          rw [ofRat_sign hne']
          obtain ⟨s1, s2⟩ := truncInt_sign hf hz'
          cases hs : x.sign
          · have := s1 hs
            have : ¬ ((x.truncInt : Int) : Rat) < 0 := by
              have : ¬ x.truncInt < 0 := by omega
              intro h; apply this; exact_mod_cast h
            simp [this]
          · have := s2 hs
            have : ((x.truncInt : Int) : Rat) < 0 := by
              have : x.truncInt < 0 := by omega
              exact_mod_cast this
            simp [this]
      refine ⟨_, _, rfl, ?_, i1, i2, ?_, ?_, copysign_sign _ _, htsign⟩
      · unfold F64.copysign; split
        · exact hfin
        · rw [neg_isFinite]; exact hfin
      · rw [copysign_toRat hsg, hval, i2]; grind
      · rw [copysign_toRat hsg, hval]; exact hd1

end PyLean.MathInt
