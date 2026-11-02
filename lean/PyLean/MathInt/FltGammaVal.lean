import PyLean.MathInt.FltGammaProps
import PyLean.MathInt.FltIsclose
import PyLean.MathInt.FltNext

/-!
# Properties: the values of `gamma` and `lgamma` near zero

`m_tgamma` (Modules/mathmodule.c:428-434) returns `1.0/x` for `0 < |x| < 1e-20` ("tgamma(x) ~
1/x for x near 0"), setting `ERANGE` when that overflows; `m_lgamma` (:508-510) returns
`-log(fabs(x))` there ("lgamma(x) ~ -log(fabs(x)) for small x"). Neither needs the C library for
`gamma`, and `lgamma` only its `log`.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- `math.gamma(x)` is `1.0/x` for every nonzero `x` with `|x| < 1e-20`, or
`OverflowError('math range error')` when `1.0/x` overflows (`x` subnormal below `2**-1024`), for
every C library; `math.lgamma(x)` is `-log(|x|)` there, for every C `log` that returns a finite
value without `errno` on positive finite arguments. -/
def GammaTiny : Prop :=
  ∀ L : GammaLibm, ∀ x : F64, x.isFinite = true → x.isZero = false →
    F64.lt (F64.abs x) c1em20 = true →
    math_gamma L (.float x) =
      (if (F64.div c1 x).isInf then .error (.overflowError "math range error")
       else .ok (F64.div c1 x)) ∧
    (SaneLog L.log → math_lgamma L (.float x) = .ok (F64.neg (L.log (F64.abs x)).1))

theorem tiny_facts {x : F64} (fx : x.isFinite = true) (hz : x.isZero = false)
    (ht : F64.lt (F64.abs x) c1em20 = true) :
    isZeroC x = false ∧ F64.eq x (F64.floor x) = false ∧ (F64.abs x).isFinite = true ∧
      F64.lt c0 (F64.abs x) = true := by
  have fa : (F64.abs x).isFinite = true := by rw [abs_isFinite]; exact fx
  have h20 : c1em20.isFinite = true ∧ c1em20.toRat < 1 := by decide +kernel
  rw [lt_of_finite fa h20.1, abs_toRat] at ht
  simp only [decide_eq_true_eq] at ht
  have hlt : Rat.abs x.toRat < 1 := by have := h20.2; grind
  have hne : x.toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat fx).2 h] at hz; cases hz
  refine ⟨by rw [isZeroC_eq]; exact hz, ?_, fa, ?_⟩
  · cases h : F64.eq x (F64.floor x)
    · rfl
    · exfalso
      obtain ⟨n, hn⟩ := (eq_floor_iff fx).1 h
      rw [hn] at hlt hne
      have h1 : Rat.abs (n : Rat) = (n.natAbs : Rat) := abs_intCast n
      rw [h1] at hlt
      have : n.natAbs < 1 := by
        have : ((n.natAbs : Nat) : Rat) < ((1 : Nat) : Rat) := by simpa using hlt
        exact Rat.natCast_lt_natCast.1 this
      have : n = 0 := by omega
      subst this; exact hne rfl
  · rw [lt_of_finite c0_facts.1 fa, c0_facts.2.2.1, abs_toRat]
    simp only [decide_eq_true_eq]
    have := abs_nonneg x.toRat
    have : Rat.abs x.toRat ≠ 0 := fun h => hne (abs_le_zero (by rw [h]; exact Rat.le_refl))
    grind

theorem erange_inf (s : Bool) : erangeOutcome (F64.inf s) = .error (.overflowError "math range error") := by
  cases s <;> decide +kernel

theorem gammaTiny_proven : GammaTiny := by
  intro L x fx hz ht
  obtain ⟨hzc, hfl, fa, hpos⟩ := tiny_facts fx hz ht
  have hfl' : (F64.eq x (F64.floor x) && F64.lt x c0) = false := by simp [hfl]
  have hfl'' : (F64.eq x (F64.floor x) && F64.le x NGAMMA_INTEGRAL) = false := by simp [hfl]
  refine ⟨?_, fun hs => ?_⟩
  · have hm : m_tgamma L x = (F64.div c1 x, if (F64.div c1 x).isInf then .erange else .zero) := by
      simp only [m_tgamma, fx, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hzc, hfl', hfl'', ht]
    obtain ⟨hz0, _, hr, _⟩ := (math1aRules_proven (m_tgamma L) (some gmsg) (.float x)).2 _ rfl
    unfold math_gamma
    rw [hm] at hz0 hr
    by_cases hi : (F64.div c1 x).isInf = true
    · simp only [hi, ↓reduceIte] at hr ⊢
      rw [hr trivial, eq_inf_of_isInf hi, erange_inf]
    · simp only [hi, Bool.false_eq_true, ↓reduceIte] at hz0 ⊢
      exact hz0 trivial
  · obtain ⟨hlf, hle⟩ := hs (F64.abs x) fa hpos
    have hfl2 : (F64.eq x (F64.floor x) && F64.le x c2) = false := by simp [hfl]
    have hm : m_lgamma L x = (F64.neg (L.log (F64.abs x)).1, .zero) := by
      simp only [m_lgamma, fx, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hfl2, ht, call1,
        Errno.after, hle]
      rfl
    obtain ⟨hz0, _, _, _⟩ := (math1aRules_proven (m_lgamma L) (some gmsg) (.float x)).2 _ rfl
    unfold math_lgamma
    rw [hm] at hz0
    exact hz0 rfl

end PyLean.MathInt
