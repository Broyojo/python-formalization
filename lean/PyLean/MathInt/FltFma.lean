import PyLean.MathInt.FltLemmas

/-!
# Property: `fma`

`math_fma_impl` (Modules/mathmodule.c:1721-1747) against Doc/library/math.rst: one rounding
of the exact `x * y + z`, IEEE 754 special cases, `ValueError` for an invalid operation,
`OverflowError` for an overflow, and a NaN without an exception whenever an argument is a
NaN (`fma(0, inf, nan)` and `fma(inf, 0, nan)` included).
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- The invalid operations of fusedMultiplyAdd on non-NaN arguments (IEEE 754 §7.2):
`0 * inf`, and `inf - inf` between the product and `z`. -/
def fmaInvalid (x y z : F64) : Bool :=
  ((x.isInf && y.isZero) || (x.isZero && y.isInf)) ||
    (z.isInf && (x.isInf || y.isInf) && z.sign != (x.sign != y.sign))

/-- `math.fma(x, y, z)` for every argument object.

* Conversion errors come first, in argument order.
* Finite arguments: the exact `x * y + z` rounded once ("computed as though with infinite
  precision and range followed by a single round"); an exact zero is `+0.0` unless both the
  product and `z` are negative zeros, as IEEE 754 §6.3 requires; a result that rounds to an
  infinity raises `OverflowError("overflow in fma")`.
* A NaN argument gives a NaN and never raises ("In these cases, math.fma returns a NaN, and does
  not raise any exception").
* Otherwise, with an infinite argument: an invalid operation raises
  `ValueError("invalid operation in fma")`, anything else is the infinity of the right sign. -/
def FmaDoc : Prop :=
  (∀ ox oy oz e, convDouble ox = .error e → math_fma ox oy oz = .error e) ∧
  (∀ ox oy oz x e, convDouble ox = .ok x → convDouble oy = .error e → math_fma ox oy oz = .error e) ∧
  (∀ ox oy oz x y e, convDouble ox = .ok x → convDouble oy = .ok y → convDouble oz = .error e →
    math_fma ox oy oz = .error e) ∧
  (∀ ox oy oz x y z, convDouble ox = .ok x → convDouble oy = .ok y → convDouble oz = .ok z →
    let r := math_fma ox oy oz
    (x.isFinite = true → y.isFinite = true → z.isFinite = true →
      let q := x.toRat * y.toRat + z.toRat
      r = if q = 0 then .ok (F64.zero ((x.sign != y.sign) && z.sign))
          else if (ofRat q).isInf then .error (.overflowError "overflow in fma")
          else .ok (ofRat q)) ∧
    ((x.isNaN || y.isNaN || z.isNaN) = true → ∃ v, r = .ok v ∧ v.isNaN = true) ∧
    ((x.isNaN || y.isNaN || z.isNaN) = false → (x.isInf || y.isInf || z.isInf) = true →
      (fmaInvalid x y z = true → r = .error (.valueError "invalid operation in fma")) ∧
      (fmaInvalid x y z = false →
        r = .ok (F64.inf (if x.isInf || y.isInf then x.sign != y.sign else z.sign)))))

theorem fmaDoc_proven : FmaDoc := by
  refine ⟨fun ox oy oz e he => ?_, fun ox oy oz x e hx he => ?_, fun ox oy oz x y e hx hy he => ?_,
    fun ox oy oz x y z hx hy hz => ?_⟩
  · simp [math_fma, he, bind, Except.bind]
  · simp [math_fma, hx, he, bind, Except.bind]
  · simp [math_fma, hx, hy, he, bind, Except.bind]
  · have base : math_fma ox oy oz =
        (let r := F64.fma x y z
         if r.isFinite then .ok r
         else if r.isNaN then
           (if !x.isNaN && !y.isNaN && !z.isNaN then .error (.valueError "invalid operation in fma")
            else .ok r)
         else if x.isFinite && y.isFinite && z.isFinite then .error (.overflowError "overflow in fma")
         else .ok r) := by
      simp only [math_fma, hx, hy, hz, bind, Except.bind]
    rw [base]
    refine ⟨fun fx fy fz => ?_, fun hn => ?_, fun hn hi => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · have hfma : F64.fma x y z = if x.toRat * y.toRat + z.toRat = 0
          then F64.zero ((x.sign != y.sign) && z.sign) else ofRat (x.toRat * y.toRat + z.toRat) := by
        unfold F64.fma
        simp [isNaN_false_of_finite fx, isNaN_false_of_finite fy, isNaN_false_of_finite fz,
          isInf_false_of_finite fx, isInf_false_of_finite fy, isInf_false_of_finite fz]
      simp only []
      rw [hfma]
      by_cases hq : x.toRat * y.toRat + z.toRat = 0
      · simp [hq, zero_isFinite]
      · simp only [hq, ↓reduceIte]
        rcases classify (ofRat (x.toRat * y.toRat + z.toRat)) with h | h | h
        · simp [h, isInf_false_of_finite h]
        · simp [h, not_finite_of_inf h, not_nan_of_inf h, fx, fy, fz]
        · rw [ofRat_isNaN] at h; cases h
    · have hr : (F64.fma x y z).isNaN = true := by
        unfold F64.fma; simp [hn, qnan_facts.2]
      have hrf : (F64.fma x y z).isFinite = false := by
        cases h : (F64.fma x y z).isFinite
        · rfl
        · rw [isNaN_false_of_finite h] at hr; cases hr
      have hnn : (!x.isNaN && !y.isNaN && !z.isNaN) = false := by
        cases h1 : x.isNaN <;> cases h2 : y.isNaN <;> cases h3 : z.isNaN <;> simp_all
      simp only [hrf, hr, hnn, Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, rfl, hr⟩
    · have hx' : x.isNaN = false := by cases h : x.isNaN <;> simp_all
      have hy' : y.isNaN = false := by cases h : y.isNaN <;> simp_all
      have hz' : z.isNaN = false := by cases h : z.isNaN <;> simp_all
      have hr : F64.fma x y z = qnan := by
        unfold F64.fma fmaInvalid at *
        simp only [hx', hy', hz', Bool.or_false, Bool.false_eq_true, ↓reduceIte]
        cases hxi : x.isInf <;> cases hyi : y.isInf <;> cases hxz : x.isZero <;>
          cases hyz : y.isZero <;> cases hzi : z.isInf <;> simp_all
      simp only [hr, qnan_facts.2, hx', hy', hz']
      have : qnan.isFinite = false := by decide +kernel
      simp [this]
    · have hx' : x.isNaN = false := by cases h : x.isNaN <;> simp_all
      have hy' : y.isNaN = false := by cases h : y.isNaN <;> simp_all
      have hz' : z.isNaN = false := by cases h : z.isNaN <;> simp_all
      have hr : F64.fma x y z = F64.inf (if x.isInf || y.isInf then x.sign != y.sign else z.sign) := by
        unfold fmaInvalid at hv
        unfold F64.fma
        simp only [hx', hy', hz', Bool.or_false, Bool.false_eq_true, ↓reduceIte]
        by_cases hxy : (x.isInf || y.isInf) = true
        · have key : ∀ w : F64, w.isInf = true → w.isZero = false := fun w hw => by
            cases hz : w.isZero
            · rfl
            · have := isFinite_of_isZero hz; rw [not_finite_of_inf hw] at this; cases this
          have hz0 : (x.isZero || y.isZero) = false := by
            cases hxi : x.isInf <;> cases hyi : y.isInf
            · simp_all
            · have := key y hyi; simp_all
            · have := key x hxi; simp_all
            · have := key x hxi; have := key y hyi; simp_all
          have hzz : (z.isInf && z.sign != (x.sign != y.sign)) = false := by
            cases hzi : z.isInf
            · rfl
            · simp_all
          simp only [hxy, hz0, hzz, Bool.false_eq_true, ↓reduceIte]
        · have hxy' : (x.isInf || y.isInf) = false := by simpa using hxy
          have hzi : z.isInf = true := by
            cases h : z.isInf
            · rw [hxy', h] at hi; cases hi
            · rfl
          simp only [hxy', hzi, Bool.false_eq_true, ↓reduceIte]
          exact eq_inf_of_isInf hzi
      rw [hr]
      generalize (if (x.isInf || y.isInf) = true then x.sign != y.sign else z.sign) = sg
      obtain ⟨h1, _⟩ := inf_bits sg
      have hfin : (x.isFinite && y.isFinite && z.isFinite) = false := by
        cases h1 : x.isInf <;> cases h2 : y.isInf <;> cases h3 : z.isInf <;>
          simp_all [not_finite_of_inf]
      simp [not_finite_of_inf h1, not_nan_of_inf h1, hfin]

end PyLean.MathInt
