import PyLean.Binary64.FloatArith

/-!
`float_rem`, `float_divmod` and `float_floor_div` of `Objects/floatobject.c` (CPython 3.15.2)
on every operand: the dispatch of `CONVERT_TO_DOUBLE`, the remainder itself, and the
wrappers around `_float_div_mod`.
-/

namespace PyLean.Binary64

open PyLean F64

/-! ## Rational helpers -/

theorem floor_eq_of {q : Rat} {n : Int} (h1 : (n : Rat) ≤ q) (h2 : q < (n : Rat) + 1) :
    q.floor = n := by
  apply Int.le_antisymm
  · have : q.floor < n + 1 := by
      rw [Rat.floor_lt_iff]; push_cast; exact h2
    omega
  · exact Rat.le_floor_iff.2 h1

theorem neg_div' (a b : Rat) : (-a) / b = -(a / b) := by
  rw [Rat.div_def, Rat.div_def, Rat.neg_mul]

theorem div_neg' (a : Rat) {b : Rat} (hb : b ≠ 0) : a / (-b) = -(a / b) := by
  have : (-b)⁻¹ = -b⁻¹ := by
    apply Rat.inv_eq_of_mul_eq_one
    rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.mul_inv_cancel _ hb]
  rw [Rat.div_def, Rat.div_def, this, Rat.mul_neg]

/-- The magnitude of a nonzero finite float is positive. -/
theorem abs_pos_of {x : F64} (hx : x.isFinite = true) (hz : x.isZero = false) :
    0 < Rat.abs x.toRat := by
  rw [MathInt.toRat_abs_val hx]
  exact Rat.mul_pos (natCast_pos' (mant_pos_of_not_zero hz)) (pw_pos _)

theorem lt_d0_sign {x : F64} (hx : x.isFinite = true) (hz : x.isZero = false) :
    F64.lt x d0 = x.sign := by
  cases hs : x.sign
  · exact not_lt_d0_of_pos hx hs
  · exact lt_d0_of_neg hx hs hz

/-- `fmod` of two finite floats with a nonzero divisor: the remainder of the magnitudes,
with the sign of `x`. -/
theorem fmod_finite {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hzy : y.isZero = false) :
    F64.fmod x y =
      (if Rat.abs x.toRat - Rat.abs y.toRat * ((Rat.abs x.toRat / Rat.abs y.toRat).floor : Rat) = 0
       then zero x.sign
       else ofRat (if x.sign
         then -(Rat.abs x.toRat - Rat.abs y.toRat * ((Rat.abs x.toRat / Rat.abs y.toRat).floor : Rat))
         else Rat.abs x.toRat - Rat.abs y.toRat * ((Rat.abs x.toRat / Rat.abs y.toRat).floor : Rat))) := by
  simp only [F64.fmod, isNaN_false_of_finite hx, isNaN_false_of_finite hy, isInf_false_of_finite hx,
    isInf_false_of_finite hy, hzy, ← abs_eq_ite, Bool.or_false, Bool.false_eq_true, ↓reduceIte]

theorem zero_copysign (y : F64) : F64.copysign d0 y = F64.zero y.sign := by
  cases hs : y.sign <;> simp [F64.copysign, hs] <;> decide +kernel

/-- The exact remainder `x - y * floor(x / y)`, from the remainder of the magnitudes. -/
theorem rem_target {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hzy : y.isZero = false) (r : Rat)
    (hr : r = Rat.abs x.toRat - Rat.abs y.toRat * ((Rat.abs x.toRat / Rat.abs y.toRat).floor : Rat)) :
    x.toRat - y.toRat * ((x.toRat / y.toRat).floor : Rat) =
      if r = 0 then 0
      else if x.sign = y.sign then (if x.sign then -r else r)
      else (if x.sign then -r else r) + y.toRat := by
  have hB : 0 < Rat.abs y.toRat := abs_pos_of hy hzy
  have hBne : Rat.abs y.toRat ≠ 0 := Rat.ne_of_gt hB
  have ex := MathInt.sign_val hx
  have ey := MathInt.sign_val hy
  generalize Rat.abs x.toRat = A at hr ex
  generalize Rat.abs y.toRat = B at hr ey hB hBne
  generalize hq : A / B = q at hr
  have hqB : q * B = A := by rw [← hq]; exact Rat.div_mul_cancel hBne
  have hk1 := Rat.floor_le q
  have hk2 := Rat.lt_floor_add_one q
  generalize hk : q.floor = k at hk1 hk2 hr
  have hk2' : q < (k : Rat) + 1 := by push_cast at hk2; exact hk2
  by_cases hr0 : r = 0
  · rw [if_pos hr0]
    have hqk : q = k := by
      have : B * (q - k) = 0 := by grind
      rcases Rat.mul_eq_zero.1 this with h | h
      · exact absurd h hBne
      · grind
    have hdiv : x.toRat / y.toRat = if x.sign = y.sign then (k : Rat) else -(k : Rat) := by
      rw [ex, ey]
      cases x.sign <;> cases y.sign <;>
        simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, neg_div', div_neg' _ hBne, Rat.neg_neg, hq, hqk]
    have hfl : (x.toRat / y.toRat).floor = if x.sign = y.sign then k else -k := by
      rw [hdiv]; split
      · exact Rat.floor_intCast k
      · rw [show -(k : Rat) = ((-k : Int) : Rat) by push_cast; rfl]; exact Rat.floor_intCast _
    rw [hfl, ex, ey]
    cases x.sign <;> cases y.sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      push_cast <;> grind
  · rw [if_neg hr0]
    have hqk : (k : Rat) < q := by
      rcases Rat.le_iff_lt_or_eq.1 hk1 with h | h
      · exact h
      · exfalso; apply hr0; rw [hr, ← hqB, ← h]; grind
    have hdiv : x.toRat / y.toRat = if x.sign = y.sign then q else -q := by
      rw [ex, ey]
      cases x.sign <;> cases y.sign <;>
        simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, neg_div', div_neg' _ hBne, Rat.neg_neg, hq]
    have hfl : (x.toRat / y.toRat).floor = if x.sign = y.sign then k else -k - 1 := by
      rw [hdiv]; split
      · exact hk
      · apply floor_eq_of <;> push_cast <;> grind
    rw [hfl, ex, ey]
    cases x.sign <;> cases y.sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      push_cast <;> grind

/-! ## `float_rem` -/

/-- `float_rem` on two floats, floatobject.c:592-611: `ZeroDivisionError` for a zero
divisor whatever the dividend; a NaN for a NaN operand or an infinite dividend; for an
infinite divisor the dividend itself when it has the divisor's sign, the divisor when it
does not, and a zero with the divisor's sign for a zero dividend; and for finite operands
the exact `x - y * floor(x / y)` rounded to nearest even, with the sign of `y` always,
zero included. -/
def RemIEEE : Prop :=
  ∀ x y : F64,
    (y.isZero = true → float_rem (.float x) (.float y) = .error (.zeroDivisionError "division by zero")) ∧
    (y.isZero = false → (x.isNaN || y.isNaN || x.isInf) = true → NaNRes (float_rem (.float x) (.float y))) ∧
    (x.isFinite = true → y.isInf = true →
      float_rem (.float x) (.float y) =
        .ok (some (if x.isZero then F64.zero y.sign else if x.sign = y.sign then x else y))) ∧
    (x.isFinite = true → y.isFinite = true → y.isZero = false →
      ∃ z, float_rem (.float x) (.float y) = .ok (some z) ∧
        IsRounding (x.toRat - y.toRat * ((x.toRat / y.toRat).floor : Rat)) z ∧ z.sign = y.sign)

/-- `float_rem`, floatobject.c:586-612, on every pair of operands. -/
def FloatRemSpec : Prop := BinDispatch float_rem ∧ RemIEEE

theorem float_rem_floats (x y : F64) :
    float_rem (.float x) (.float y) = (floatRemCore x y).map some := by
  show withDoubles (.float x) (.float y) floatRemCore = _
  simp only [withDoubles, convertToDouble, bind, Except.bind]
  rcases floatRemCore x y with e | r <;> rfl

theorem remIEEE_proven : RemIEEE := by
  intro x y
  refine ⟨fun hz => ?_, fun hz h => ?_, fun hx hy => ?_, fun hx hy hzy => ?_⟩
  · rw [float_rem_floats]
    simp [floatRemCore, eq_d0_of_zero hz, zeroDiv, Except.map]
  · rw [float_rem_floats]
    have hm : F64.fmod x y = qnan := by
      simp only [F64.fmod]
      rw [if_pos (by simpa [hz] using h)]
    have hq : qnan.isZero = false := by decide +kernel
    have hlt : F64.lt qnan d0 = false := by decide +kernel
    simp only [floatRemCore, eq_d0_of_nonzero_any hz, hm, hq, hlt, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false]
    split
    · exact ⟨_, rfl, by simp [F64.add, qnan_isNaN]⟩
    · exact ⟨_, rfl, qnan_isNaN⟩
  · rw [float_rem_floats]
    have hm : F64.fmod x y = x := by
      simp [F64.fmod, isNaN_false_of_finite hx, not_nan_of_inf hy, isInf_false_of_finite hx, hy,
        inf_not_zero hy]
    simp only [floatRemCore, eq_d0_inf hy, hm, Bool.false_eq_true, ↓reduceIte]
    cases hzx : x.isZero
    · have h1 := lt_d0_sign hx hzx
      have h2 : F64.lt y d0 = y.sign := by
        cases hs : y.sign
        · rw [eq_inf_of_isInf hy, hs]; decide +kernel
        · rw [eq_inf_of_isInf hy, hs]; decide +kernel
      rw [h1, h2]
      simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
      by_cases hs : x.sign = y.sign
      · simp [hs]; rfl
      · have : (y.sign != x.sign) = true := by simp; exact fun h => hs h.symm
        simp only [this, ↓reduceIte, hs]
        rw [(addIEEE x y).2.2.2.1 hx hy]; rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, zero_copysign]; rfl
  · rw [float_rem_floats]
    obtain ⟨hrep, hr0, hrB, _⟩ := MathInt.fmod_rem hx hy hzy
    have hT := rem_target hx hy hzy _ rfl
    have hfm := fmod_finite hx hy hzy
    generalize Rat.abs x.toRat - Rat.abs y.toRat * ((Rat.abs x.toRat / Rat.abs y.toRat).floor : Rat) = r
      at hT hrep hr0 hrB hfm
    have hylt : Rat.abs y.toRat < overflowLimit := abs_toRat_lt hy
    by_cases hz : r = 0
    · rw [if_pos hz] at hT hfm
      have hzz : (zero x.sign).isZero = true := zero_isZero _
      simp only [floatRemCore, hfm, eq_d0_of_not_zero hy hzy, hzz, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, zero_copysign]
      refine ⟨_, rfl, ?_, zero_sign _⟩
      rw [hT]; exact zero_isRounding _
    · rw [if_neg hz] at hT hfm
      have hpos : 0 < r := by grind
      generalize hsr : (if x.sign then -r else r) = sr at hT hfm
      have hsrrep : Rep binary64 sr := by
        rw [← hsr]; split
        · exact rep_neg hrep
        · exact hrep
      have hsrabs : Rat.abs sr = r := by
        rw [← hsr]; split
        · rw [abs_neg, abs_of_nonneg hr0]
        · rw [abs_of_nonneg hr0]
      have hsrlt : Rat.abs sr < overflowLimit := by rw [hsrabs]; grind
      have hmv : (ofRat sr).toRat = sr := ofRat_exact hsrrep hsrlt
      have hmf : (ofRat sr).isFinite = true := (ofRat_isFinite _).2 hsrlt
      have hsr0 : sr ≠ 0 := fun h => by rw [h] at hsrabs; exact hz (by rw [← hsrabs]; decide)
      have hmz : (ofRat sr).isZero = false := by
        cases hc : (ofRat sr).isZero
        · rfl
        · rw [toRat_of_isZero hc] at hmv; exact absurd hmv.symm hsr0
      have hsign : decide (sr < 0) = x.sign := by
        rw [← hsr]; cases x.sign
        · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not]; grind
        · simp only [↓reduceIte, decide_eq_true_eq]; grind
      have hml : F64.lt (ofRat sr) d0 = x.sign := by
        rw [lt_d0_sign hmf hmz, MathInt.ofRat_sign hsr0, hsign]
      simp only [floatRemCore, hfm, eq_d0_of_not_zero hy hzy, hmz, Bool.not_false, ↓reduceIte, hml,
        lt_d0_sign hy hzy, Bool.false_eq_true]
      by_cases hs : x.sign = y.sign
      · rw [if_pos hs] at hT
        simp only [hs, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        refine ⟨_, rfl, by rw [hT]; exact ofRat_isRounding _, ?_⟩
        rw [MathInt.ofRat_sign hsr0, hsign, hs]
      · rw [if_neg hs] at hT
        have hb : (y.sign != x.sign) = true := by simp; exact fun h => hs h.symm
        simp only [hb, ↓reduceIte]
        have hT0 : sr + y.toRat ≠ 0 := by
          intro h0
          have : Rat.abs sr = Rat.abs y.toRat := by
            rw [show sr = -y.toRat by grind, abs_neg]
          rw [hsrabs] at this; rw [this] at hrB; exact Rat.lt_irrefl hrB
        rw [add_of_finite hmf hy, hmv, if_neg hT0]
        refine ⟨_, rfl, by rw [hT]; exact ofRat_isRounding _, ?_⟩
        rw [MathInt.ofRat_sign hT0]
        have ey := MathInt.sign_val hy
        have hyB : 0 < Rat.abs y.toRat := abs_pos_of hy hzy
        rw [← hsr]
        cases hsx : x.sign <;> cases hsy : y.sign <;> rw [hsx, hsy] at hs <;> simp at hs <;>
          rw [hsy] at ey <;> simp only [Bool.false_eq_true, ↓reduceIte] at ey ⊢ <;>
          rw [ey] <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] <;> grind

theorem floatRemSpec_proven : FloatRemSpec := ⟨withDoubles_dispatch _, remIEEE_proven⟩

/-! ## `float_divmod` and `float_floor_div` -/

/-- `float_divmod` (floatobject.c:652-665) and `float_floor_div` (:667-680) on every pair of
operands: the `CONVERT_TO_DOUBLE` dispatch (an int converts, `1e308 // 10**400` raises
`OverflowError`, a non-number is `NotImplemented`), `ZeroDivisionError` for a zero divisor
of either sign whatever the dividend, and otherwise `divmod(x, y)` is the pair
`(x // y, x % y)`, the remainder being the one `RemIEEE` states. The quotient itself is
pinned by the two refutations `FloorDivExactFloor` and `DivmodQuotientDoc`, which run these
wrappers. -/
def FloatDivmodSpec : Prop :=
  BinDispatch float_divmod ∧ BinDispatch float_floor_div ∧
  (∀ x y : F64, y.isZero = true →
    float_divmod (.float x) (.float y) = .error (.zeroDivisionError "division by zero") ∧
    float_floor_div (.float x) (.float y) = .error (.zeroDivisionError "division by zero")) ∧
  (∀ x y : F64, y.isZero = false → ∃ q r,
    float_divmod (.float x) (.float y) = .ok (some (q, r)) ∧
    float_floor_div (.float x) (.float y) = .ok (some q) ∧
    float_rem (.float x) (.float y) = .ok (some r)) ∧
  float_floor_div (.float (ofBits 0x7fe1ccf385ebc8a0)) (.int (10 ^ 400)) =
    .error (.overflowError "int too large to convert to float")

theorem floatDivmodSpec_proven : FloatDivmodSpec := by
  refine ⟨withDoubles_dispatch _, withDoubles_dispatch _, fun x y hz => ?_, fun x y hz => ?_, ?_⟩
  · exact ⟨(divmodZero_proven x y hz).2.1, (divmodZero_proven x y hz).2.2⟩
  · obtain ⟨h1, h2, h3⟩ := divmodTwins_proven x y (eq_d0_of_nonzero_any hz)
    exact ⟨_, _, h1, h2, h3⟩
  · decide +kernel

end PyLean.Binary64
