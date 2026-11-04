import PyLean.Binary64.FloatRem

/-!
Small pieces of `Objects/floatobject.c` (CPython 3.15.2) stated exactly: the float-vs-float
branch of `float_richcompare`, the two hexadecimal digit tables, the bytes `PyFloat_Pack8`
writes, and the double `PyFloat_Unpack4` widens a binary32 pattern to.
-/

namespace PyLean.Binary64

open PyLean F64

/-! ## `float_richcompare` between floats -/

/-- `x < y` in the extended reals, for non-NaN floats: `-inf` is below everything but
itself, `+inf` above everything but itself, finite floats compare by value. -/
def extLt (x y : F64) : Bool :=
  !x.isNaN && !y.isNaN &&
    ((x.isInf && x.sign && !(y.isInf && y.sign)) || (y.isInf && !y.sign && !(x.isInf && !x.sign)) ||
      (x.isFinite && y.isFinite && decide (x.toRat < y.toRat)))

/-- `x == y` in the extended reals, for non-NaN floats: so `0.0 == -0.0`. -/
def extEq (x y : F64) : Bool :=
  !x.isNaN && !y.isNaN &&
    ((x.isInf && y.isInf && x.sign == y.sign) || (x.isFinite && y.isFinite && decide (x.toRat = y.toRat)))

/-- The six IEEE 754 relations: every one is false on a NaN except `!=`. -/
def ieeeRel : CmpOp → F64 → F64 → Bool
  | .lt, x, y => extLt x y
  | .le, x, y => extLt x y || extEq x y
  | .eq, x, y => extEq x y
  | .ne, x, y => !extEq x y
  | .gt, x, y => extLt y x
  | .ge, x, y => extLt y x || extEq x y

/-- `float_richcompare` when `w` is a float (`PyFloat_Check`, floatobject.c:383-384, so a
subclass too): the `Compare:` block (:507-528) gives the IEEE relation of the two values
for each of the six operators, NaNs, infinities and signed zeros included. When `w` is
neither a float nor an int the result is `NotImplemented` (:394 for a NaN or infinite `v`,
:504-505 otherwise). -/
def FloatCompareFloats : Prop :=
  (∀ (x y : F64) (op : CmpOp), float_richcompare x (.float y) op = some (ieeeRel op x y)) ∧
  (∀ (x y : F64) (t : String) (op : CmpOp), float_richcompare x (.floatSub t y) op = some (ieeeRel op x y)) ∧
  (∀ (x : F64) (t : String) (f : Option Obj) (i : Option Int) (q : String) (op : CmpOp),
    float_richcompare x (.other t f i q) op = none)

theorem lt_ext (x y : F64) : F64.lt x y = extLt x y := by
  rcases classify x with hx | hx | hx <;> rcases classify y with hy | hy | hy
  · simp [F64.lt, extLt, isNaN_false_of_finite hx, isNaN_false_of_finite hy, isInf_false_of_finite hx,
      isInf_false_of_finite hy, hx, hy]
  · cases hs : y.sign <;>
      simp [F64.lt, extLt, isNaN_false_of_finite hx, not_nan_of_inf hy, isInf_false_of_finite hx,
        hy, hx, not_finite_of_inf hy, hs]
  · simp [F64.lt, extLt, hy]
  · cases hs : x.sign <;>
      simp [F64.lt, extLt, not_nan_of_inf hx, isNaN_false_of_finite hy, isInf_false_of_finite hy,
        hx, hy, not_finite_of_inf hx, hs]
  · cases hs : x.sign <;> cases ht : y.sign <;>
      simp [F64.lt, extLt, not_nan_of_inf hx, not_nan_of_inf hy, hx, hy, not_finite_of_inf hx,
        not_finite_of_inf hy, hs, ht]
  · simp [F64.lt, extLt, hy]
  · simp [F64.lt, extLt, hx]
  · simp [F64.lt, extLt, hx]
  · simp [F64.lt, extLt, hx]

theorem eq_ext (x y : F64) : F64.eq x y = extEq x y := by
  rcases classify x with hx | hx | hx <;> rcases classify y with hy | hy | hy
  · simp [F64.eq, extEq, isNaN_false_of_finite hx, isNaN_false_of_finite hy, isInf_false_of_finite hx,
      isInf_false_of_finite hy, hx, hy]
  · simp [F64.eq, extEq, isNaN_false_of_finite hx, not_nan_of_inf hy, isInf_false_of_finite hx,
      hy, not_finite_of_inf hy]
  · simp [F64.eq, extEq, hy]
  · simp [F64.eq, extEq, not_nan_of_inf hx, isNaN_false_of_finite hy, isInf_false_of_finite hy,
      hx, not_finite_of_inf hx]
  · simp [F64.eq, extEq, not_nan_of_inf hx, not_nan_of_inf hy, hx, hy, not_finite_of_inf hx,
      not_finite_of_inf hy]
  · simp [F64.eq, extEq, hy]
  · simp [F64.eq, extEq, hx]
  · simp [F64.eq, extEq, hx]
  · simp [F64.eq, extEq, hx]

theorem extEq_comm (x y : F64) : extEq x y = extEq y x := by
  unfold extEq
  have e1 : (x.sign == y.sign) = (y.sign == x.sign) := by cases x.sign <;> cases y.sign <;> rfl
  have e2 : decide (x.toRat = y.toRat) = decide (y.toRat = x.toRat) := by simp [eq_comm]
  rw [e1, e2]
  cases x.isNaN <;> cases y.isNaN <;> cases x.isInf <;> cases y.isInf <;> cases x.isFinite <;>
    cases y.isFinite <;> simp

theorem compare_ext (op : CmpOp) (x y : F64) : compareDoubles op x y = ieeeRel op x y := by
  cases op <;> simp only [compareDoubles, ieeeRel, F64.le, F64.ne, F64.gt, F64.ge, lt_ext, eq_ext]
  rw [extEq_comm y x]

theorem floatCompareFloats_proven : FloatCompareFloats :=
  ⟨fun x y op => by simp [float_richcompare, compare_ext],
   fun x y t op => by simp [float_richcompare, compare_ext],
   fun _ _ _ _ _ _ => rfl⟩

/-! ## The hexadecimal digit tables -/

/-- `char_from_hex` (floatobject.c:1094-1099, `Py_hexdigits`) and `hex_from_char`
(:1107-1134, `_CHAR_TO_HEX`) are inverse tables: the sixteen digits are `0-9a-f` in order,
`hex_from_char` reads each of them and the capitals `A-F` back to its value, and every other
byte maps to `-1` (`none`). -/
def HexDigitTables : Prop :=
  (List.range 16).map (fun d => (char_from_hex d).toNat) =
    [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 97, 98, 99, 100, 101, 102] ∧
  (∀ d, d < 16 → hex_from_char (char_from_hex d).toNat = some d) ∧
  (∀ d, 10 ≤ d → d < 16 → hex_from_char ((char_from_hex d).toNat - 32) = some d) ∧
  (∀ c, c < 256 → (hex_from_char c).isSome = true →
    ∃ d, d < 16 ∧ (c = (char_from_hex d).toNat ∨ (10 ≤ d ∧ c = (char_from_hex d).toNat - 32)))

theorem hexDigitTables_proven : HexDigitTables := by
  refine ⟨by decide +kernel, ?_, ?_, ?_⟩
  · intro d hd
    rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d
    all_goals first | decide +kernel | omega
  · intro d h1 hd
    rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d
    all_goals first | omega | decide +kernel
  · intro c hc hs
    have : ∀ c, c < 256 → (hex_from_char c).isSome = true →
        ∃ d, d < 16 ∧ (c = (char_from_hex d).toNat ∨ (10 ≤ d ∧ c = (char_from_hex d).toNat - 32)) := by
      intro c hc hs
      simp only [hex_from_char] at hs
      by_cases h1 : 48 ≤ c ∧ c ≤ 57
      · refine ⟨c - 48, by omega, Or.inl ?_⟩
        have : c - 48 < 10 := by omega
        generalize hk : c - 48 = k at this
        have hc' : c = k + 48 := by omega
        subst hc'
        rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
        all_goals first | decide +kernel | omega
      · by_cases h2 : 97 ≤ c ∧ c ≤ 102
        · refine ⟨c - 87, by omega, Or.inl ?_⟩
          generalize hk : c - 97 = k
          have hc' : c = k + 97 := by omega
          have hk6 : k < 6 := by omega
          subst hc'
          rcases k with _ | _ | _ | _ | _ | _ | k
          all_goals first | decide +kernel | omega
        · by_cases h3 : 65 ≤ c ∧ c ≤ 70
          · refine ⟨c - 55, by omega, Or.inr ⟨by omega, ?_⟩⟩
            generalize hk : c - 65 = k
            have hc' : c = k + 65 := by omega
            have hk6 : k < 6 := by omega
            subst hc'
            rcases k with _ | _ | _ | _ | _ | _ | k
            all_goals first | decide +kernel | omega
          · exfalso
            simp [h1, h2, h3] at hs
    exact this c hc hs

/-! ## `PyFloat_Pack8` -/

/-- `PyFloat_Pack8`, floatobject.c:2069-2087: exactly eight bytes, byte `i` holding bits
`8i .. 8i+7` of the double for `le` and byte `7 - i` holding them otherwise. -/
def Pack8Bytes : Prop :=
  ∀ (x : F64) (le : Bool), ∃ b, PyFloat_Pack8 x le = .ok b ∧ b.length = 8 ∧
    ∀ i, i < 8 → b.getD i 0 = (x.bits / 2 ^ (8 * (if le then i else 7 - i))) % 256

theorem pack8Bytes_proven : Pack8Bytes := by
  intro x le
  refine ⟨layout 8 x.bits le, rfl, ?_, ?_⟩
  · cases le <;> simp [layout]
  · intro i hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
    all_goals first | omega | (cases le <;> simp [layout, List.range, List.range.loop])

/-! ## `PyFloat_Unpack4` -/

/-- `PyFloat_Unpack4`, floatobject.c:2146-2201, widens exactly, in both byte orders: a finite
binary32 `±m * 2**e` becomes the double of that value and sign (signed zeros included), an
infinity the infinity of its sign, and a NaN keeps its sign and all 23 fraction bits, quiet
bit included, shifted up by 29, so a signaling NaN stays signaling (:2165-2172). -/
def Unpack4Widen : Prop :=
  ∀ (v : Nat) (le : Bool), v < 2 ^ 32 →
    match binary32.view v with
    | .finite neg m e =>
      (PyFloat_Unpack4 (layout 4 v le) le).isFinite = true ∧
      (PyFloat_Unpack4 (layout 4 v le) le).sign = neg ∧
      (PyFloat_Unpack4 (layout 4 v le) le).toRat = (if neg then -dyadic m e else dyadic m e)
    | .inf neg => PyFloat_Unpack4 (layout 4 v le) le = F64.inf neg
    | .nan neg _ =>
      (PyFloat_Unpack4 (layout 4 v le) le).bits =
        (if neg then 2 ^ 63 else 0) + 0x7ff0000000000000 + (v % 2 ^ 23) * 2 ^ 29

theorem unpack4Widen_proven : Unpack4Widen := by
  intro b le hb
  have hv := view32 b hb
  by_cases he1 : (b / 2 ^ 23) % 256 = 255
  · by_cases hf0 : b % 2 ^ 23 = 0
    · simp only [he1, hf0, ↓reduceIte] at hv
      rw [hv]
      simp only [PyFloat_Unpack4, byte_layout4 b hb le, hv, ofFloat32Bits]
    · simp only [he1, hf0, ↓reduceIte] at hv
      rw [hv]
      simp only []
      generalize hS : (if 2 ^ 31 ≤ b then 2 ^ 63 else 0 : Nat) = S
      generalize hp : (b % 2 ^ 23) % 2 ^ 22 = p
      generalize hq : (b / 2 ^ 22) % 2 = q
      have hq1 : q ≤ 1 := by omega
      have hfr : b % 2 ^ 23 = q * 2 ^ 22 + p := by omega
      have hS' : S = 2 ^ 63 ∨ S = 0 := by
        rw [← hS]; split
        · left; rfl
        · right; rfl
      have hy0 : (ofFloat32Bits b).bits = S + 0x7ff8000000000000 + p * 2 ^ 29 := by
        have e0 : ofFloat32Bits b = F64.ofBits (((if decide (2 ^ 31 ≤ b) = true then 2 ^ 63 else 0) +
            0x7ff8000000000000) + ((b % 2 ^ 23) % 2 ^ 22) * 2 ^ 29) := by
          simp only [ofFloat32Bits, hv]
        rw [e0, hp]
        have e1 : (if decide (2 ^ 31 ≤ b) = true then 2 ^ 63 else 0) = S := by
          rw [← hS]; simp
        rw [e1]
        apply bits_ofBits_of_lt
        rcases hS' with h | h <;> omega
      have e2 : PyFloat_Unpack4 (layout 4 b le) le = if q == 0 then
          F64.ofBits ((ofFloat32Bits b).bits - 2 ^ 51) else ofFloat32Bits b := by
        simp only [PyFloat_Unpack4, byte_layout4 b hb le, hv, hq]
      have e3 : (if decide (2 ^ 31 ≤ b) = true then 2 ^ 63 else 0) = S := by
        rw [← hS]; simp
      rw [e2, e3, hfr]
      by_cases hq0 : q = 0
      · simp only [hq0, beq_self_eq_true, ↓reduceIte]
        rw [bits_ofBits_of_lt (by rw [hy0]; rcases hS' with h | h <;> omega), hy0]
        omega
      · have hq0' : (q == 0) = false := by simpa using hq0
        have hq11 : q = 1 := by omega
        simp only [hq0', Bool.false_eq_true, ↓reduceIte]
        rw [hy0, hq11]
        omega
  · have hfin : ∀ (neg : Bool) (m : Nat) (e : Int), binary32.view b = .finite neg m e →
        m < 2 ^ 24 → -149 ≤ e → e ≤ 104 →
        (PyFloat_Unpack4 (layout 4 b le) le).isFinite = true ∧
        (PyFloat_Unpack4 (layout 4 b le) le).sign = neg ∧
        (PyFloat_Unpack4 (layout 4 b le) le).toRat = (if neg then -dyadic m e else dyadic m e) := by
      intro neg m e hview hm he hmax
      have hU : PyFloat_Unpack4 (layout 4 b le) le =
          if m == 0 then zero neg else ofRat (if neg then -dyadic m e else dyadic m e) := by
        simp only [PyFloat_Unpack4, byte_layout4 b hb le, hview, ofFloat32Bits]
      rw [hU]
      by_cases hm0 : m = 0
      · subst hm0
        have hd : dyadic 0 e = 0 := by cases e <;> simp [dyadic]
        simp only [beq_self_eq_true, ↓reduceIte, hd]
        refine ⟨zero_isFinite _, zero_sign _, ?_⟩
        rw [zero_toRat]; cases neg <;> simp
      · have hmb : (m == 0) = false := by simpa using hm0
        simp only [hmb, Bool.false_eq_true, ↓reduceIte, dyadic_eq]
        have hv0 : 0 < (m : Rat) * pw e := Rat.mul_pos (natCast_pos' (by omega)) (pw_pos _)
        have hrep0 : Rep binary64 ((m : Rat) * pw e) :=
          ⟨m, e, by show m < 2 ^ 53; omega, by show (-1074 : Int) ≤ e; omega, Or.inl rfl⟩
        have hlt : Rat.abs (if neg then -((m : Rat) * pw e) else (m : Rat) * pw e) < overflowLimit := by
          have := value_bound hm hmax
          cases neg
          · simp only [Bool.false_eq_true, ↓reduceIte]; rw [abs_of_nonneg (Rat.le_of_lt hv0)]; exact this
          · simp only [↓reduceIte]; rw [abs_neg, abs_of_nonneg (Rat.le_of_lt hv0)]; exact this
        have hrep : Rep binary64 (if neg then -((m : Rat) * pw e) else (m : Rat) * pw e) := by
          cases neg
          · simpa using hrep0
          · simpa using rep_neg hrep0
        have hne : (if neg then -((m : Rat) * pw e) else (m : Rat) * pw e) ≠ 0 := by
          cases neg <;> simp <;> grind
        refine ⟨(ofRat_isFinite _).2 hlt, ?_, ofRat_exact hrep hlt⟩
        rw [MathInt.ofRat_sign hne]
        cases neg
        · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not]; grind
        · simp only [↓reduceIte, decide_eq_true_eq]; grind
    by_cases he0 : (b / 2 ^ 23) % 256 = 0
    · simp only [he1, he0, ↓reduceIte] at hv
      rw [hv]
      exact hfin _ _ _ hv (by omega) (by decide) (by decide)
    · simp only [he1, he0, ↓reduceIte] at hv
      rw [hv]
      exact hfin _ _ _ hv (by omega) (by omega) (by omega)

end PyLean.Binary64
