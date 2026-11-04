import PyLean.Binary64.Pack4Props
import PyLean.Binary64.Props4
import PyLean.MathInt.FltFmod

/-!
The binary operators of `Objects/floatobject.c` (CPython 3.15.2) stated on every operand.

`CONVERT_TO_DOUBLE` (floatobject.c:311-315) and `_Py_convert_int_to_double` (:319-336) are
stated against `operandSpec`, which names the overflow threshold of `PyLong_AsDouble`
directly instead of going through `F64.ofInt` and `isInf`. Each operator then gets two
statements: `BinDispatch` fixes the order in which the operands are converted, the
`NotImplemented` exits and the propagation of the `OverflowError`; and an IEEE 754
statement fixes the result for every pair of floats, NaNs and infinities included.
-/

namespace PyLean.Binary64

open PyLean F64

/-! ## Operand conversion -/

/-- What one `CONVERT_TO_DOUBLE` line yields, floatobject.c:311-315 and :319-336: a float
(`PyFloat_Check`, so a subclass too) gives its value, an int (`PyLong_Check`) its value
rounded to nearest even, or `OverflowError` from the threshold `DBL_MAX + 2**970` on, and
anything else `NotImplemented` (`none`). -/
def operandSpec : Obj → Py (Option F64)
  | .float x | .floatSub _ x => .ok (some x)
  | .int n =>
    if overflowLimit ≤ Rat.abs (n : Rat) then .error (.overflowError "int too large to convert to float")
    else .ok (some (ofRat n))
  | .other .. => .ok none

/-- `_Py_convert_int_to_double` with the `PyFloat_Check` line of `CONVERT_TO_DOUBLE`: the
conversion is `operandSpec`, and an int below the threshold rounds to a finite float that
is its round-to-nearest-even value. `10**400` raises, `NotImplemented` is not an error. -/
def ConvertToDoubleSpec : Prop :=
  (∀ v : Obj, convertToDouble v = operandSpec v) ∧
  (∀ n : Int, Rat.abs (n : Rat) < overflowLimit →
    (ofRat (n : Rat)).isFinite = true ∧ IsRounding n (ofRat n)) ∧
  convertToDouble (.int (10 ^ 400)) = .error (.overflowError "int too large to convert to float") ∧
  convertToDouble (.int (-(10 ^ 400))) = .error (.overflowError "int too large to convert to float")

theorem convert_eq_spec (v : Obj) : convertToDouble v = operandSpec v := by
  cases v with
  | float x => rfl
  | floatSub t x => rfl
  | other t f i q => rfl
  | int n =>
    simp only [convertToDouble, operandSpec, PyLong_AsDouble, F64.ofInt]
    by_cases h : overflowLimit ≤ Rat.abs (n : Rat)
    · have hi := (ofRat_isInf (n : Rat)).2 h
      simp [hi, h, bind, Except.bind]
    · have hi : (ofRat (n : Rat)).isInf = false := by
        cases hc : (ofRat (n : Rat)).isInf
        · rfl
        · exact absurd ((ofRat_isInf _).1 hc) h
      simp [hi, h, bind, Except.bind, pure, Except.pure]

theorem convertToDoubleSpec_proven : ConvertToDoubleSpec := by
  refine ⟨convert_eq_spec, fun n h => ⟨(ofRat_isFinite _).2 h, ofRat_isRounding _⟩, ?_, ?_⟩
  · rw [convert_eq_spec]; decide +kernel
  · rw [convert_eq_spec]; decide +kernel

/-! ## Dispatch -/

/-- The two `CONVERT_TO_DOUBLE` lines in order: the left operand first, so its
`NotImplemented` or `OverflowError` wins; then the right one; and only two converted
operands reach the arithmetic, exactly as two floats would. -/
def BinDispatch {α : Type} (op : Obj → Obj → Py (Option α)) : Prop :=
  ∀ v w : Obj, op v w =
    match operandSpec v, operandSpec w with
    | .error e, _ => .error e
    | .ok none, _ => .ok none
    | .ok (some _), .error e => .error e
    | .ok (some _), .ok none => .ok none
    | .ok (some a), .ok (some b) => op (.float a) (.float b)

theorem withDoubles_dispatch {α : Type} (k : F64 → F64 → Py α) :
    BinDispatch (fun v w => withDoubles v w k) := by
  intro v w
  rw [← convert_eq_spec v, ← convert_eq_spec w]
  rcases hv : convertToDouble v with e | _ | a <;>
    rcases hw : convertToDouble w with e' | _ | b <;>
    (show withDoubles v w k = _; unfold withDoubles; rw [hv, hw]; rfl)

/-- A result that is a float NaN. -/
def NaNRes (r : Py (Option F64)) : Prop := ∃ z, r = .ok (some z) ∧ z.isNaN = true

theorem qnan_isNaN : qnan.isNaN = true := by decide +kernel

theorem nan_res_qnan : NaNRes (.ok (some qnan)) := ⟨qnan, rfl, qnan_isNaN⟩

/-! ## Addition and subtraction -/

theorem float_add_floats (x y : F64) : float_add (.float x) (.float y) = .ok (some (F64.add x y)) := rfl
theorem float_sub_floats (x y : F64) : float_sub (.float x) (.float y) = .ok (some (F64.sub x y)) := rfl
theorem float_mul_floats (x y : F64) : float_mul (.float x) (.float y) = .ok (some (F64.mul x y)) := rfl

/-- `float_add` on two floats, floatobject.c:546, as IEEE 754 addition: a NaN operand or
infinities of opposite signs give a NaN, an infinity otherwise wins, and finite operands
give the exact sum rounded to nearest even, an exact zero being `-0.0` only for two
negative operands. -/
def AddIEEE : Prop :=
  ∀ x y : F64,
    ((x.isNaN || y.isNaN) = true → NaNRes (float_add (.float x) (.float y))) ∧
    (x.isInf = true → y.isInf = true → x.sign ≠ y.sign → NaNRes (float_add (.float x) (.float y))) ∧
    (x.isInf = true → y.isNaN = false → (y.isInf = true → x.sign = y.sign) →
      float_add (.float x) (.float y) = .ok (some x)) ∧
    (x.isFinite = true → y.isInf = true → float_add (.float x) (.float y) = .ok (some y)) ∧
    (x.isFinite = true → y.isFinite = true → ∃ z, float_add (.float x) (.float y) = .ok (some z) ∧
      IsRounding (x.toRat + y.toRat) z ∧
      (x.toRat + y.toRat = 0 → z.isZero = true ∧ z.sign = (x.sign && y.sign)))

/-- `float_add`, floatobject.c:541-549, on every pair of operands. -/
def FloatAddSpec : Prop := BinDispatch float_add ∧ AddIEEE

theorem addIEEE (x y : F64) :
    ((x.isNaN || y.isNaN) = true → (F64.add x y).isNaN = true) ∧
    (x.isInf = true → y.isInf = true → x.sign ≠ y.sign → (F64.add x y).isNaN = true) ∧
    (x.isInf = true → y.isNaN = false → (y.isInf = true → x.sign = y.sign) → F64.add x y = x) ∧
    (x.isFinite = true → y.isInf = true → F64.add x y = y) ∧
    (x.isFinite = true → y.isFinite = true →
      IsRounding (x.toRat + y.toRat) (F64.add x y) ∧
      (x.toRat + y.toRat = 0 → (F64.add x y).isZero = true ∧ (F64.add x y).sign = (x.sign && y.sign))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [F64.add, h, qnan_isNaN]
  · intro hx hy hs
    have h1 := not_nan_of_inf hx
    have h2 := not_nan_of_inf hy
    have : (x.sign != y.sign) = true := by simpa using hs
    simp [F64.add, h1, h2, hx, hy, this, qnan_isNaN]
  · intro hx hy hs
    have h1 := not_nan_of_inf hx
    by_cases hyi : y.isInf = true
    · have : (x.sign != y.sign) = false := by simp [hs hyi]
      simp [F64.add, h1, hy, hx, hyi, this]
    · simp [F64.add, h1, hy, hx, hyi]
  · intro hx hy
    simp [F64.add, isNaN_false_of_finite hx, not_nan_of_inf hy, isInf_false_of_finite hx, hy]
  · intro hx hy
    rw [add_of_finite hx hy]
    refine ⟨?_, ?_⟩
    · split
      · rename_i h; rw [h]; exact zero_isRounding _
      · exact ofRat_isRounding _
    · intro h; rw [if_pos h]; exact ⟨zero_isZero _, zero_sign _⟩

theorem floatAddSpec_proven : FloatAddSpec := by
  refine ⟨withDoubles_dispatch _, ?_⟩
  intro x y
  obtain ⟨a1, a2, a3, a4, a5⟩ := addIEEE x y
  simp only [float_add_floats]
  refine ⟨fun h => ⟨_, rfl, a1 h⟩, fun h1 h2 h3 => ⟨_, rfl, a2 h1 h2 h3⟩,
    fun h1 h2 h3 => by rw [a3 h1 h2 h3], fun h1 h2 => by rw [a4 h1 h2], fun h1 h2 => ?_⟩
  exact ⟨_, rfl, (a5 h1 h2).1, (a5 h1 h2).2⟩

/-- `float_sub` on two floats, floatobject.c:556: NaN for a NaN operand or for infinities
of the same sign, the left infinity otherwise, the negated right infinity for a finite
left operand, and for finite operands the exact difference rounded, an exact zero being
`-0.0` only for `-0.0 - 0.0`. -/
def SubIEEE : Prop :=
  ∀ x y : F64,
    ((x.isNaN || y.isNaN) = true → NaNRes (float_sub (.float x) (.float y))) ∧
    (x.isInf = true → y.isInf = true → x.sign = y.sign → NaNRes (float_sub (.float x) (.float y))) ∧
    (x.isInf = true → y.isNaN = false → (y.isInf = true → x.sign ≠ y.sign) →
      float_sub (.float x) (.float y) = .ok (some x)) ∧
    (x.isFinite = true → y.isInf = true →
      float_sub (.float x) (.float y) = .ok (some (F64.inf (!y.sign)))) ∧
    (x.isFinite = true → y.isFinite = true → ∃ z, float_sub (.float x) (.float y) = .ok (some z) ∧
      IsRounding (x.toRat - y.toRat) z ∧
      (x.toRat - y.toRat = 0 → z.isZero = true ∧ z.sign = (x.sign && !y.sign)))

/-- `float_sub`, floatobject.c:551-559, on every pair of operands. -/
def FloatSubSpec : Prop := BinDispatch float_sub ∧ SubIEEE

theorem floatSubSpec_proven : FloatSubSpec := by
  refine ⟨withDoubles_dispatch _, ?_⟩
  intro x y
  obtain ⟨n1, n2, n3⟩ := neg_fields y
  obtain ⟨a1, a2, a3, a4, a5⟩ := addIEEE x y.neg
  have hsub : F64.sub x y = F64.add x y.neg := rfl
  simp only [float_sub_floats, hsub]
  rw [neg_isNaN, neg_isInf, n1, neg_isFinite] at *
  refine ⟨fun h => ⟨_, rfl, a1 h⟩, fun h1 h2 h3 => ⟨_, rfl, a2 h1 h2 (by cases hx : x.sign <;> cases hy : y.sign <;> simp_all)⟩,
    fun h1 h2 h3 => by rw [a3 h1 h2 (fun h => by have := h3 h; cases hx : x.sign <;> cases hy : y.sign <;> simp_all)],
    fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [a4 h1 h2, eq_inf_of_isInf (show y.neg.isInf = true by rw [neg_isInf]; exact h2), (neg_fields y).1]
  · obtain ⟨r1, r2⟩ := a5 h1 h2
    rw [toRat_neg] at r1 r2
    refine ⟨_, rfl, ?_, ?_⟩
    · have e : x.toRat + -y.toRat = x.toRat - y.toRat := by grind
      rw [e] at r1; exact r1
    · intro h
      have e : x.toRat + -y.toRat = 0 := by grind
      exact r2 e

/-! ## Multiplication -/

theorem neg_val_iff {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hzx : x.isZero = false) (hzy : y.isZero = false) :
    decide (x.toRat * y.toRat < 0) = (x.sign != y.sign) := by
  have ex := MathInt.toRat_neg_iff_sign hx hzx
  have ey := MathInt.toRat_neg_iff_sign hy hzy
  have nx : x.toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat hx).2 h] at hzx; cases hzx
  have ny : y.toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat hy).2 h] at hzy; cases hzy
  cases hsx : x.sign <;> cases hsy : y.sign <;> rw [hsx] at ex <;> rw [hsy] at ey <;>
    simp only [Bool.false_eq_true, eq_iff_iff, iff_false, iff_true] at ex ey <;>
    simp only [bne_self_eq_false, Bool.bne_true, Bool.bne_false, Bool.not_false, Bool.not_true,
      decide_eq_true_eq, decide_eq_false_iff_not]
  · have h1 : 0 < x.toRat := by grind
    have h2 : 0 < y.toRat := by grind
    exact Rat.not_lt.2 (Rat.le_of_lt (Rat.mul_pos h1 h2))
  · have h1 : 0 < x.toRat := by grind
    have : 0 < x.toRat * -y.toRat := Rat.mul_pos h1 (by grind)
    grind
  · have h2 : 0 < y.toRat := by grind
    have : 0 < -x.toRat * y.toRat := Rat.mul_pos (by grind) h2
    grind
  · have : 0 < -x.toRat * -y.toRat := Rat.mul_pos (by grind) (by grind)
    have e : -x.toRat * -y.toRat = x.toRat * y.toRat := by grind
    rw [e] at this
    exact Rat.not_lt.2 (Rat.le_of_lt this)

/-- `float_mul` on two floats, floatobject.c:566: NaN for a NaN operand and for an
infinity times a zero, otherwise an infinity times anything is the infinity of the
exclusive or of the signs, and finite operands give the exact product rounded, with
that sign whether or not it is zero. -/
def MulIEEE : Prop :=
  ∀ x y : F64,
    ((x.isNaN || y.isNaN) = true → NaNRes (float_mul (.float x) (.float y))) ∧
    ((x.isInf && y.isZero || x.isZero && y.isInf) = true → NaNRes (float_mul (.float x) (.float y))) ∧
    ((x.isInf || y.isInf) = true → x.isNaN = false → y.isNaN = false → x.isZero = false →
      y.isZero = false → float_mul (.float x) (.float y) = .ok (some (F64.inf (x.sign != y.sign)))) ∧
    (x.isFinite = true → y.isFinite = true → ∃ z, float_mul (.float x) (.float y) = .ok (some z) ∧
      IsRounding (x.toRat * y.toRat) z ∧ z.sign = (x.sign != y.sign))

/-- `float_mul`, floatobject.c:561-569, on every pair of operands. -/
def FloatMulSpec : Prop := BinDispatch float_mul ∧ MulIEEE

theorem inf_not_zero {x : F64} (h : x.isInf = true) : x.isZero = false := by
  cases hz : x.isZero
  · rfl
  · rw [isInf_false_of_finite (isFinite_of_isZero hz)] at h; cases h

theorem floatMulSpec_proven : FloatMulSpec := by
  refine ⟨withDoubles_dispatch _, ?_⟩
  intro x y
  simp only [float_mul_floats]
  refine ⟨fun h => ⟨_, rfl, by simp [F64.mul, h, qnan_isNaN]⟩, fun h => ⟨_, rfl, ?_⟩, fun h hnx hny hzx hzy => ?_,
    fun hx hy => ?_⟩
  · rcases Bool.or_eq_true _ _ ▸ h with h | h
    · simp only [Bool.and_eq_true] at h
      have := not_nan_of_inf h.1
      have hny := isNaN_false_of_finite (isFinite_of_isZero h.2)
      simp [F64.mul, this, hny, h.1, h.2, qnan_isNaN]
    · simp only [Bool.and_eq_true] at h
      have := not_nan_of_inf h.2
      have hnx := isNaN_false_of_finite (isFinite_of_isZero h.1)
      have hix := isInf_false_of_finite (isFinite_of_isZero h.1)
      simp [F64.mul, this, hnx, hix, h.1, h.2, qnan_isNaN]
  · by_cases hix : x.isInf = true
    · simp [F64.mul, hnx, hny, hix, hzy]
    · have hiy : y.isInf = true := by simpa [hix] using h
      simp [F64.mul, hnx, hny, hix, hiy, hzx]
  · refine ⟨_, rfl, ?_, ?_⟩
    · rw [mul_of_finite hx hy]
      split
      · rename_i h; rw [h]; exact zero_isRounding _
      · exact ofRat_isRounding _
    · rw [mul_of_finite hx hy]
      split
      · exact zero_sign _
      · rename_i h
        rw [MathInt.ofRat_sign h]
        have hzx : x.isZero = false := by
          cases hc : x.isZero
          · rfl
          · rw [toRat_of_isZero hc, Rat.zero_mul] at h; exact absurd rfl h
        have hzy : y.isZero = false := by
          cases hc : y.isZero
          · rfl
          · rw [toRat_of_isZero hc, Rat.mul_zero] at h; exact absurd rfl h
        exact neg_val_iff hx hy hzx hzy

/-! ## Division -/

theorem div_neg_val_iff {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hzx : x.isZero = false) (hzy : y.isZero = false) :
    decide (x.toRat / y.toRat < 0) = (x.sign != y.sign) := by
  have ny : y.toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat hy).2 h] at hzy; cases hzy
  have hyy : 0 < y.toRat * y.toRat := by
    rcases Rat.le_total (a := y.toRat) (b := 0) with h | h
    · have h1 : 0 < -y.toRat := by grind
      have := Rat.mul_pos h1 h1
      rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] at this; exact this
    · have h1 : 0 < y.toRat := by grind
      exact Rat.mul_pos h1 h1
  have e : x.toRat * (y.toRat)⁻¹ * (y.toRat * y.toRat) = x.toRat * y.toRat := by
    rw [show x.toRat * (y.toRat)⁻¹ * (y.toRat * y.toRat) = x.toRat * y.toRat * ((y.toRat)⁻¹ * y.toRat)
      by grind, Rat.inv_mul_cancel _ ny, Rat.mul_one]
  rw [← neg_val_iff hx hy hzx hzy, Rat.div_def]
  simp only [decide_eq_decide]
  rw [← Rat.mul_neg_iff_of_pos_right hyy, e]

/-- `float_div` on two floats, floatobject.c:577-583: a zero divisor of either sign raises
`ZeroDivisionError` whatever the dividend, NaN included; otherwise a NaN operand or two
infinities give a NaN, an infinite dividend an infinity, an infinite divisor a zero, and
finite operands the exact quotient rounded; every non-NaN result has the exclusive or of
the signs. -/
def DivIEEE : Prop :=
  ∀ x y : F64,
    (y.isZero = true → float_div (.float x) (.float y) = .error (.zeroDivisionError "division by zero")) ∧
    (y.isZero = false → (x.isNaN || y.isNaN) = true → NaNRes (float_div (.float x) (.float y))) ∧
    (x.isInf = true → y.isInf = true → NaNRes (float_div (.float x) (.float y))) ∧
    (x.isInf = true → y.isFinite = true → y.isZero = false →
      float_div (.float x) (.float y) = .ok (some (F64.inf (x.sign != y.sign)))) ∧
    (x.isFinite = true → y.isInf = true →
      float_div (.float x) (.float y) = .ok (some (F64.zero (x.sign != y.sign)))) ∧
    (x.isFinite = true → y.isFinite = true → y.isZero = false →
      ∃ z, float_div (.float x) (.float y) = .ok (some z) ∧
        IsRounding (x.toRat / y.toRat) z ∧ z.sign = (x.sign != y.sign))

/-- `float_div`, floatobject.c:571-584, on every pair of operands. -/
def FloatDivSpec : Prop := BinDispatch float_div ∧ DivIEEE

theorem float_div_floats (x y : F64) :
    float_div (.float x) (.float y) = if F64.eq y d0 then zeroDiv else .ok (some (F64.div x y)) := by
  simp only [float_div, withDoubles, convertToDouble]
  split <;> simp [*, bind, Except.bind, pure, Except.pure, zeroDiv]

theorem floatDivSpec_proven : FloatDivSpec := by
  refine ⟨withDoubles_dispatch _, ?_⟩
  intro x y
  refine ⟨fun hz => ?_, fun hz h => ?_, fun hx hy => ?_, fun hx hy hz => ?_, fun hx hy => ?_,
    fun hx hy hz => ?_⟩
  · rw [float_div_floats, if_pos (eq_d0_of_zero hz)]; rfl
  · rw [float_div_floats, if_neg (by rw [eq_d0_of_nonzero_any hz]; decide)]
    exact ⟨_, rfl, by simp [F64.div, h, qnan_isNaN]⟩
  · rw [float_div_floats, if_neg (by rw [eq_d0_inf hy]; decide)]
    exact ⟨_, rfl, by simp [F64.div, not_nan_of_inf hx, not_nan_of_inf hy, hx, hy, qnan_isNaN]⟩
  · rw [float_div_floats, if_neg (by rw [eq_d0_of_not_zero hy hz]; decide)]
    simp [F64.div, not_nan_of_inf hx, isNaN_false_of_finite hy, hx, isInf_false_of_finite hy]
  · rw [float_div_floats, if_neg (by rw [eq_d0_inf hy]; decide)]
    simp [F64.div, isNaN_false_of_finite hx, not_nan_of_inf hy, isInf_false_of_finite hx, hy]
  · rw [float_div_floats, if_neg (by rw [eq_d0_of_not_zero hy hz]; decide)]
    refine ⟨_, rfl, ?_, ?_⟩
    · rw [div_of_finite hx hy hz]
      split
      · rename_i h; rw [h]; exact zero_isRounding _
      · exact ofRat_isRounding _
    · rw [div_of_finite hx hy hz]
      split
      · exact zero_sign _
      · rename_i h
        rw [MathInt.ofRat_sign h]
        have hzx : x.isZero = false := by
          cases hc : x.isZero
          · rfl
          · rw [toRat_of_isZero hc, Rat.div_def, Rat.zero_mul] at h; exact absurd rfl h
        exact div_neg_val_iff hx hy hzx hz

end PyLean.Binary64
