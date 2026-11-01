import PyLean.Binary64.Props

/-!
Integer conversions of floats, `divmod`, the special values of `pow`, and the simple
methods of `Objects/floatobject.c`.
-/

namespace PyLean.Binary64

open F64

/-! ## Integer-valued floats -/

theorem pw_natAbs_le_limit : ((2 ^ 53 : Nat) : Rat) < overflowLimit := by
  have hL : pw 0 ≤ pw 970 := pw_le (by decide)
  rw [pw_zero] at hL
  have hlim : overflowLimit = 18014398509481983 * pw 970 := by
    unfold overflowLimit; congr 1
  rw [hlim]
  have h1 : ((2 ^ 53 : Nat) : Rat) = 9007199254740992 := by simp
  rw [h1]; grind

theorem abs_intCast (n : Int) : Rat.abs (n : Rat) = (n.natAbs : Rat) := by
  by_cases h : 0 ≤ n
  · rw [abs_of_nonneg (Rat.intCast_nonneg.2 h)]
    have : ((n.natAbs : Nat) : Int) = n := by omega
    rw [← Rat.intCast_natCast, this]
  · rw [abs_of_nonpos (by
      have : n ≤ 0 := by omega
      exact Rat.intCast_nonpos.2 this)]
    have : ((n.natAbs : Nat) : Int) = -n := by omega
    rw [← Rat.intCast_natCast, this]; simp

theorem int_rep {n : Int} (h : n.natAbs < 2 ^ 53) : Rep binary64 (n : Rat) := by
  refine ⟨n.natAbs, 0, h, by decide, ?_⟩
  rw [pw_zero, Rat.mul_one]
  by_cases h0 : 0 ≤ n
  · left
    have : ((n.natAbs : Nat) : Int) = n := by omega
    rw [← Rat.intCast_natCast, this]
  · right
    have : ((n.natAbs : Nat) : Int) = -n := by omega
    rw [← Rat.intCast_natCast, this]; simp

theorem ofInt_small {n : Int} (h : n.natAbs < 2 ^ 53) :
    (ofInt n).isFinite = true ∧ (ofInt n).toRat = n := by
  have hlt : Rat.abs (n : Rat) < overflowLimit := by
    rw [abs_intCast]
    have h2 : (n.natAbs : Rat) < ((2 ^ 53 : Nat) : Rat) := Rat.natCast_lt_natCast.2 h
    have := pw_natAbs_le_limit
    grind
  exact ⟨(ofRat_isFinite _).2 hlt, ofRat_exact (int_rep h) hlt⟩

theorem truncInt_of_int {y : F64} {t : Int} (h : y.toRat = t) : y.truncInt = t := by
  unfold truncInt floorInt ceilInt
  rw [h, Rat.floor_intCast, Rat.ceil_intCast]
  split <;> rfl

/-- A finite float is an integer, or smaller than `2 ^ 52`. -/
theorem int_or_small {x : F64} (hx : x.isFinite = true) :
    (∃ t : Int, x.toRat = t) ∨ Rat.abs x.toRat < ((2 ^ 52 : Nat) : Rat) := by
  by_cases he : 0 ≤ x.lsbExp
  · left
    have hk : (x.lsbExp.toNat : Int) = x.lsbExp := by omega
    have h1 : (x.mant : Rat) * pw x.lsbExp = ((x.mant * 2 ^ x.lsbExp.toNat : Nat) : Rat) := by
      rw [Rat.natCast_mul, ← pw_natCast, hk]
    rw [toRat_of_finite hx, h1]
    split
    · exact ⟨-((x.mant * 2 ^ x.lsbExp.toNat : Nat) : Int), by rw [Rat.intCast_neg, Rat.intCast_natCast]⟩
    · exact ⟨((x.mant * 2 ^ x.lsbExp.toNat : Nat) : Int), by rw [Rat.intCast_natCast]⟩
  · right
    have h1 : (x.mant : Rat) < ((2 ^ 53 : Nat) : Rat) := Rat.natCast_lt_natCast.2 (mant_lt x)
    have h2 : pw x.lsbExp ≤ pw (-1) := pw_le (by omega)
    have a1 : (x.mant : Rat) * pw x.lsbExp < ((2 ^ 53 : Nat) : Rat) * pw x.lsbExp :=
      (Rat.mul_lt_mul_right (pw_pos _)).2 h1
    have a2 := Rat.mul_le_mul_of_nonneg_left h2 (Rat.le_of_lt (natCast_pos' (Nat.two_pow_pos 53)))
    have h4 : ((2 ^ 53 : Nat) : Rat) * pw (-1) = ((2 ^ 52 : Nat) : Rat) := by
      rw [← pw_natCast, ← pw_natCast, ← pw_add]; rfl
    have h0 : 0 ≤ (x.mant : Rat) * pw x.lsbExp :=
      Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))
    rw [h4] at a2
    rw [toRat_of_finite hx]
    split
    · rw [abs_neg, abs_of_nonneg h0]; grind
    · rw [abs_of_nonneg h0]; grind

theorem ofIntS_value {x : F64} {n : Int} (s : Bool) (hx : x.isFinite = true)
    (hz : x.isZero = false) (h : x.toRat = n ∨ n.natAbs < 2 ^ 53) :
    (ofIntS s n).isFinite = true ∧ (ofIntS s n).toRat = n := by
  unfold ofIntS
  split
  · rename_i h0
    subst h0
    exact ⟨zero_isFinite s, zero_toRat s⟩
  · rcases h with h | h
    · have e : ofInt n = x := by
        unfold ofInt; rw [← h]; exact ofRat_toRat hx hz
      rw [e]; exact ⟨hx, h⟩
    · exact ofInt_small h

theorem natAbs_of_bound {n : Int} {a : Rat} (h1 : (n : Rat) ≤ a + 1) (h2 : a - 1 ≤ (n : Rat))
    (h3 : Rat.abs a < ((2 ^ 52 : Nat) : Rat)) : n.natAbs < 2 ^ 53 := by
  have b : ((2 ^ 52 : Nat) : Rat) = 4503599627370496 := by simp
  rw [b] at h3
  have h4 : a < 4503599627370496 ∧ -4503599627370496 < a := by
    unfold Rat.abs at h3; split at h3 <;> grind
  have c1 : ((4503599627370497 : Int) : Rat) = 4503599627370497 := by simp
  have c2 : ((-4503599627370497 : Int) : Rat) = -4503599627370497 := by simp
  have h5 : (n : Rat) < ((4503599627370497 : Int) : Rat) := by rw [c1]; grind
  have h6 : ((-4503599627370497 : Int) : Rat) < (n : Rat) := by rw [c2]; grind
  have h7 := Rat.intCast_lt_intCast.1 h5
  have h8 := Rat.intCast_lt_intCast.1 h6
  omega

theorem floorInt_bound {x : F64} (h : Rat.abs x.toRat < ((2 ^ 52 : Nat) : Rat)) :
    x.floorInt.natAbs < 2 ^ 53 := by
  have h1 := Rat.floor_le x.toRat
  have h2 := Rat.lt_floor_add_one x.toRat
  rw [Rat.intCast_add] at h2
  have e1 : ((1 : Int) : Rat) = 1 := rfl
  rw [e1] at h2
  apply natAbs_of_bound (a := x.toRat) _ _ h
  · show (x.toRat.floor : Rat) ≤ _; grind
  · show _ ≤ (x.toRat.floor : Rat); grind

theorem ceilInt_bound {x : F64} (h : Rat.abs x.toRat < ((2 ^ 52 : Nat) : Rat)) :
    x.ceilInt.natAbs < 2 ^ 53 := by
  have h1 := Rat.floor_le (-x.toRat)
  have h2 := Rat.lt_floor_add_one (-x.toRat)
  rw [Rat.intCast_add] at h2
  have e1 : ((1 : Int) : Rat) = 1 := rfl
  rw [e1] at h2
  have e : x.ceilInt = -((-x.toRat).floor) := Rat.ceil_eq_neg_floor_neg _
  have hc : (x.ceilInt : Rat) = -(((-x.toRat).floor : Int) : Rat) := by rw [e]; rfl
  apply natAbs_of_bound (a := x.toRat) _ _ h
  · rw [hc]; grind
  · rw [hc]; grind

theorem ceil_of_int {x : F64} {t : Int} (h : x.toRat = t) : x.ceilInt = t := by
  unfold ceilInt; rw [h, Rat.ceil_intCast]

theorem floor_of_int {x : F64} {t : Int} (h : x.toRat = t) : x.floorInt = t := by
  unfold floorInt; rw [h, Rat.floor_intCast]

theorem zero_floorInt {x : F64} (h : x.isZero = true) : x.floorInt = 0 :=
  floor_of_int (t := 0) (by rw [toRat_of_isZero h]; rfl)

theorem zero_ceilInt {x : F64} (h : x.isZero = true) : x.ceilInt = 0 :=
  ceil_of_int (t := 0) (by rw [toRat_of_isZero h]; rfl)

/-- `floor` on a finite float gives the exact floor. -/
theorem floor_value {x : F64} (hx : x.isFinite = true) :
    (F64.floor x).isFinite = true ∧ (F64.floor x).toRat = x.floorInt := by
  have hn := isNaN_false_of_finite hx
  by_cases hz : x.isZero = true
  · have e : F64.floor x = x := by simp [F64.floor, hn, hx, hz]
    rw [e, zero_floorInt hz, toRat_of_isZero hz]
    exact ⟨hx, rfl⟩
  · have hz' : x.isZero = false := by simpa using hz
    have e : F64.floor x = ofIntS x.sign x.floorInt := by simp [F64.floor, hn, hx, hz']
    rw [e]
    apply ofIntS_value _ hx hz'
    rcases int_or_small hx with ⟨t, ht⟩ | h
    · left; rw [floor_of_int ht]; exact ht
    · right; exact floorInt_bound h

/-- `ceil` on a finite float gives the exact ceiling. -/
theorem ceil_value {x : F64} (hx : x.isFinite = true) :
    (F64.ceil x).isFinite = true ∧ (F64.ceil x).toRat = x.ceilInt := by
  have hn := isNaN_false_of_finite hx
  by_cases hz : x.isZero = true
  · have e : F64.ceil x = x := by simp [F64.ceil, hn, hx, hz]
    rw [e, zero_ceilInt hz, toRat_of_isZero hz]
    exact ⟨hx, rfl⟩
  · have hz' : x.isZero = false := by simpa using hz
    have e : F64.ceil x = ofIntS x.sign x.ceilInt := by simp [F64.ceil, hn, hx, hz']
    rw [e]
    apply ofIntS_value _ hx hz'
    rcases int_or_small hx with ⟨t, ht⟩ | h
    · left; rw [ceil_of_int ht]; exact ht
    · right; exact ceilInt_bound h

theorem fromDouble_finite {y : F64} (hy : y.isFinite = true) :
    PyLong_FromDouble y = .ok y.truncInt := by
  simp [PyLong_FromDouble, isInf_false_of_finite hy, isNaN_false_of_finite hy]

/-- `math.floor` and `math.ceil` on a float are the exact floor and ceiling; a NaN
raises `ValueError` and an infinity `OverflowError`. `int(x)` truncates toward zero. -/
def FloatIntConversions : Prop :=
  ∀ x : F64,
    (x.isFinite = true → float_floor x = .ok x.toRat.floor ∧ float_ceil x = .ok x.toRat.ceil ∧
      float_trunc x = .ok (if x.toRat < 0 then x.toRat.ceil else x.toRat.floor)) ∧
    (x.isNaN = true → float_trunc x = .error (.valueError "cannot convert float NaN to integer") ∧
      float_floor x = .error (.valueError "cannot convert float NaN to integer") ∧
      float_ceil x = .error (.valueError "cannot convert float NaN to integer")) ∧
    (x.isInf = true →
      float_trunc x = .error (.overflowError "cannot convert float infinity to integer") ∧
      float_floor x = .error (.overflowError "cannot convert float infinity to integer") ∧
      float_ceil x = .error (.overflowError "cannot convert float infinity to integer"))

theorem qnan_facts : qnan.isInf = false ∧ qnan.isNaN = true := by decide +kernel

theorem not_nan_of_inf {x : F64} (hi : x.isInf = true) : x.isNaN = false := by
  cases h : x.isNaN
  · rfl
  · rw [isInf_eq] at hi; rw [isNaN_eq] at h; omega

theorem not_finite_of_inf {x : F64} (hi : x.isInf = true) : x.isFinite = false := by
  cases h : x.isFinite
  · rfl
  · rw [isInf_false_of_finite h] at hi; cases hi

theorem not_inf_of_nan {x : F64} (hn : x.isNaN = true) : x.isInf = false := by
  cases h : x.isInf
  · rfl
  · rw [isInf_eq] at h; rw [isNaN_eq] at hn; omega

theorem mantVal_nonneg (x : F64) : 0 ≤ (x.mant : Rat) * pw x.lsbExp :=
  Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))

theorem floatIntConversions_proven : FloatIntConversions := by
  intro x
  refine ⟨fun hx => ⟨?_, ?_, ?_⟩, fun hn => ⟨?_, ?_, ?_⟩, fun hi => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨h1, h2⟩ := floor_value hx
    unfold float_floor
    rw [fromDouble_finite h1, truncInt_of_int h2]; rfl
  · obtain ⟨h1, h2⟩ := ceil_value hx
    unfold float_ceil
    rw [fromDouble_finite h1, truncInt_of_int h2]; rfl
  · unfold float_trunc
    rw [fromDouble_finite hx]
    unfold truncInt
    have hv := mantVal_nonneg x
    by_cases hneg : x.toRat < 0
    · have hs : x.sign = true := by
        rw [toRat_of_finite hx] at hneg
        cases hc : x.sign
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hneg
          grind
        · rfl
      simp only [hs, hneg, ↓reduceIte]; rfl
    · simp only [hneg, ↓reduceIte]
      cases hc : x.sign
      · rfl
      · simp only [↓reduceIte]
        have hz : x.toRat = 0 := by
          rw [toRat_of_finite hx] at hneg ⊢
          simp only [hc, ↓reduceIte] at hneg ⊢
          grind
        have h1 := ceil_of_int (x := x) (t := 0) (by rw [hz]; rfl)
        have h2 := floor_of_int (x := x) (t := 0) (by rw [hz]; rfl)
        rw [h1]
        unfold floorInt at h2
        rw [h2]
  · simp [float_trunc, PyLong_FromDouble, not_inf_of_nan hn, hn]
  · have : F64.floor x = qnan := by simp [F64.floor, hn]
    simp [float_floor, this, PyLong_FromDouble, qnan_facts.1, qnan_facts.2]
  · have : F64.ceil x = qnan := by simp [F64.ceil, hn]
    simp [float_ceil, this, PyLong_FromDouble, qnan_facts.1, qnan_facts.2]
  · simp [float_trunc, PyLong_FromDouble, hi]
  · have : F64.floor x = x := by simp [F64.floor, not_nan_of_inf hi, not_finite_of_inf hi]
    simp [float_floor, this, PyLong_FromDouble, hi]
  · have : F64.ceil x = x := by simp [F64.ceil, not_nan_of_inf hi, not_finite_of_inf hi]
    simp [float_ceil, this, PyLong_FromDouble, hi]

/-- `x.is_integer()` is true exactly for finite floats with an integer value. -/
def FloatIsInteger : Prop :=
  ∀ x : F64, float_is_integer x = true ↔ x.isFinite = true ∧ ∃ n : Int, x.toRat = n

theorem floatIsInteger_proven : FloatIsInteger := by
  intro x
  unfold float_is_integer
  cases hf : x.isFinite
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, true_and]
    obtain ⟨h1, h2⟩ := floor_value hf
    rw [eq_of_finite h1 hf, h2]
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact ⟨_, h.symm⟩
    · rintro ⟨n, hn⟩
      rw [floor_of_int hn, hn]

/-! ## `divmod`, `//` and `%` -/

/-- `%` and `//` agree with `divmod`, on every pair of floats. -/
def DivmodTwins : Prop :=
  ∀ x y : F64, F64.eq y d0 = false →
    float_divmod (.float x) (.float y) = .ok (some (float_div_mod x y)) ∧
    float_floor_div (.float x) (.float y) = .ok (some (float_div_mod x y).1) ∧
    float_rem (.float x) (.float y) = .ok (some (float_div_mod x y).2)

theorem divmodTwins_proven : DivmodTwins := by
  intro x y h
  refine ⟨?_, ?_, ?_⟩
  · simp [float_divmod, withDoubles, convertToDouble, h, bind, Except.bind, pure, Except.pure]
  · simp [float_floor_div, withDoubles, convertToDouble, h, bind, Except.bind, pure, Except.pure]
  · simp only [float_rem, withDoubles, convertToDouble, floatRemCore, h, float_div_mod]
    by_cases h1 : (F64.fmod x y).isZero = true
    · simp [h, h1, bind, Except.bind, pure, Except.pure]
    · have h1' : (F64.fmod x y).isZero = false := by simpa using h1
      by_cases h2 : F64.lt y d0 = F64.lt (F64.fmod x y) d0
      · simp [h, h1', h2, bind, Except.bind, pure, Except.pure]
      · simp [h, h1', h2, bind, Except.bind, pure, Except.pure]

/-- `%`, `//` and `divmod` raise `ZeroDivisionError` for a zero divisor, whatever the
dividend. -/
def DivmodZero : Prop :=
  ∀ x y : F64, y.isZero = true →
    float_rem (.float x) (.float y) = .error (.zeroDivisionError "division by zero") ∧
    float_divmod (.float x) (.float y) = .error (.zeroDivisionError "division by zero") ∧
    float_floor_div (.float x) (.float y) = .error (.zeroDivisionError "division by zero")

theorem divmodZero_proven : DivmodZero := by
  intro x y hz
  have hy := isFinite_of_isZero hz
  have h : F64.eq y d0 = true := by
    rw [eq_of_finite hy d0_isFinite, d0_toRat, toRat_of_isZero hz]; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp [float_rem, withDoubles, convertToDouble, floatRemCore, h, bind, Except.bind, zeroDiv]
  · simp [float_divmod, withDoubles, convertToDouble, h, bind, Except.bind, zeroDiv]
  · simp [float_floor_div, withDoubles, convertToDouble, h, bind, Except.bind, zeroDiv]

/-! ## Refutations by concrete counterexample -/

/-- `x // y` is the exact floor of the quotient whenever that floor fits in the 53-bit
integers, where the float result could be exact. -/
def FloorDivExactFloor : Prop :=
  ∀ x y : F64, x.isFinite = true → y.isFinite = true → y.isZero = false →
    (x.toRat / y.toRat).floor.natAbs < 2 ^ 53 →
    (float_div_mod x y).1.toRat = ((x.toRat / y.toRat).floor : Rat)

/-- `574432016605032.2 // 0.24012708848409187`: the exact floor is 2392199981398965. -/
theorem floorDivExactFloor_refuted : ¬ FloorDivExactFloor := by
  intro h
  have := h (ofBits 0x4300538b0260fb42) (ofBits 0x3fcebc7c03f620b2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this
  decide +kernel

/-- For finite floats, `divmod(a, b)[0]` is `math.floor(a / b)` or one less, as the
documentation of `divmod` says. -/
def DivmodQuotientDoc : Prop :=
  ∀ x y : F64, x.isFinite = true → y.isFinite = true → y.isZero = false →
    (F64.div x y).isFinite = true →
    let q := (float_div_mod x y).1.toRat
    let f := ((F64.div x y).toRat.floor : Rat)
    q = f ∨ q = f - 1

/-- `-0x1.765b303d50491p+51 // 0x1.b92103f617877p-2` is one *more* than the floor. -/
theorem divmodQuotientDoc_refuted : ¬ DivmodQuotientDoc := by
  intro h
  have := h (ofBits 0xc32765b303d50491) (ofBits 0x3fdb92103f617877)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this
  decide +kernel

end PyLean.Binary64
