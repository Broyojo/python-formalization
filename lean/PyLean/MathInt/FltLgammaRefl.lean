import PyLean.MathInt.FltSinpi

/-!
# `lgamma` of a negative number is reflected from `lgamma` of its magnitude

`m_lgamma` (Modules/mathmodule.c:515-521) computes the Lanczos value `r` for `|x|` and, for
`x < 0`, returns `logpi - log(fabs(m_sinpi(absx))) - log(absx) - r`: the reflection formula
`lgamma(x) = log(pi) - log|sin(pi x)| - log|x| - lgamma(-x)`. Since `lgamma(|x|)` is that same
`r`, the two results are related exactly, in float arithmetic, for every C library.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- For every C library and every negative non-integer `x` with `|x| >= 1e-20`: whenever
`math.lgamma(x)` and `math.lgamma(-x)` both return, `lgamma(x)` is
`log(pi) - log(|sinpi(-x)|) - log(-x) - lgamma(-x)` evaluated left to right in float arithmetic,
with CPython's `logpi` and `m_sinpi` (whose sign `SinpiSign` pins) and the C `log`. -/
def LgammaReflection : Prop :=
  ∀ L : GammaLibm, ∀ x : F64, x.isFinite = true → x.toRat < 0 → (∀ n : Int, x.toRat ≠ n) →
    F64.lt (F64.abs x) c1em20 = false →
    ∀ v w, math_lgamma L (.float x) = .ok w → math_lgamma L (.float (F64.abs x)) = .ok v →
      w = F64.sub (F64.sub (F64.sub logpi (L.log (F64.abs (m_sinpi L (F64.abs x) .zero).1)).1)
        (L.log (F64.abs x)).1) v

theorem math_1a_ok_val {f : CFun1} {msg : Option String} {x w : F64}
    (h : math_1a (.float x) f msg = .ok w) : w = (f x).1 := by
  unfold math_1a at h
  simp only [asDouble, bind, Except.bind] at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
    · split at h <;> cases h
  · cases h; rfl

theorem m_sinpi_fst (L : GammaLibm) (x : F64) (e e' : Errno) :
    (m_sinpi L x e).1 = (m_sinpi L x e').1 := by
  unfold m_sinpi
  simp only [call1]
  generalize roundToInt (F64.mul c2 (F64.fmod (F64.abs x) c2)) = n
  split <;> rfl

theorem lgammaReflection_proven : LgammaReflection := by
  intro L x fx hneg hni hsmall v w hw hv
  have hz : x.isZero = false := by
    cases h : x.isZero
    · rfl
    · rw [toRat_of_isZero h] at hneg; simp at hneg
  have hfl : F64.eq x (F64.floor x) = false := by
    cases h : F64.eq x (F64.floor x)
    · rfl
    · obtain ⟨n, hn⟩ := (eq_floor_iff fx).1 h; exact absurd hn (hni n)
  have fa : (F64.abs x).isFinite = true := by rw [abs_isFinite]; exact fx
  have sa : (F64.abs x).sign = false := (abs_fields x).1
  have aa : F64.abs (F64.abs x) = F64.abs x := abs_eq_self sa
  have hfla : F64.eq (F64.abs x) (F64.floor (F64.abs x)) = false := by
    cases h : F64.eq (F64.abs x) (F64.floor (F64.abs x))
    · rfl
    · obtain ⟨n, hn⟩ := (eq_floor_iff fa).1 h
      rw [abs_toRat, abs_of_nonpos (Rat.le_of_lt hneg)] at hn
      exact absurd (by rw [show x.toRat = -(n : Rat) by grind]; push_cast; rfl) (hni (-n))
  have hlt0 : F64.lt x c0 = true := by
    rw [lt_of_finite fx c0_facts.1, c0_facts.2.2.1]; simp; exact hneg
  have hlta : F64.lt (F64.abs x) c0 = false := by
    rw [lt_of_finite fa c0_facts.1, c0_facts.2.2.1]; simp; exact Rat.not_lt.2 (sign_false_nonneg fa sa)
  have ex : m_lgamma L x = lgammaLanczos L x (F64.abs x) := by
    simp [m_lgamma, fx, hfl, hsmall]
  have ea : m_lgamma L (F64.abs x) = lgammaLanczos L (F64.abs x) (F64.abs x) := by
    simp [m_lgamma, fa, hfla, aa, hsmall]
  have hw' := math_1a_ok_val (by unfold math_lgamma at hw; exact hw)
  have hv' := math_1a_ok_val (by unfold math_lgamma at hv; exact hv)
  rw [hw', ex]; rw [hv', ea]
  unfold lgammaLanczos
  simp only [call1, hlt0, hlta, ↓reduceIte, Bool.false_eq_true]
  rw [m_sinpi_fst L (F64.abs x) _ .zero]

end PyLean.MathInt
