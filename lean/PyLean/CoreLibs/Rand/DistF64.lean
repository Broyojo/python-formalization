import PyLean.CoreLibs.Rand.DistProps
import PyLean.CoreLibs.Rand.F64Inst
import PyLean.MathInt.FltLemmas

/-!
The distributions of `Lib/random.py:500-890` over IEEE 754 binary64 (`F64`), with the
C library a parameter (`RandLibm`).

Two kinds of statement:

* Formula theorems pin what each method computes from the `random()` values it
  draws: the binary64 expression, the order of the draws, the state after them, and
  every exception the expression can raise. A rejection loop is pinned one round at a
  time: which draws a round makes, the candidate it computes, the test that accepts it,
  and that a rejected round is followed by the next one on the state after its draws.
  These hold for every C library and every core generator (`Random`, `SystemRandom`, a
  user subclass), because the method only touches randomness through `random()`.
* The NaN refutations. They need one fact of C99 Annex F about the library:
  `exp(NaN)` is NaN (`ExpNaN`). Everything else about NaN is the `F64` arithmetic.
-/

namespace PyLean.CoreLibs.Rand

open PyLean PyLean.Binary64 RM Flt

/-! ### NaN in binary64 -/

/-- C99 Annex F.10.3.1: `exp(NaN)` returns a NaN. -/
def ExpNaN [RandLibm] : Prop := ∀ x : F64, x.isNaN = true → (RandLibm.exp x).isNaN = true

theorem qnan_isNaN : F64.qnan.isNaN = true := by decide +kernel

theorem f64_isInf_of_isNaN {x : F64} (h : x.isNaN = true) : x.isInf = false := by
  unfold F64.isNaN at h
  unfold F64.isInf
  cases hb : (x.bexp == 2047) <;> cases hf : (x.frac == 0) <;> simp_all

/-- `F64` satisfies `IeeeNaN`, given `ExpNaN`: every other field is a theorem about the
binary64 operations. -/
theorem f64_ieeeNaN [RandLibm] (hexp : ExpNaN) : IeeeNaN F64 where
  add_l a b h := by
    have h' : a.isNaN = true := h
    show (F64.add a b).isNaN = true
    simp [F64.add, h', qnan_isNaN]
  add_r a b h := by
    have h' : b.isNaN = true := h
    show (F64.add a b).isNaN = true
    simp [F64.add, h', qnan_isNaN]
  sub_l a b h := by
    have h' : a.isNaN = true := h
    show (F64.add a b.neg).isNaN = true
    simp [F64.add, h', qnan_isNaN]
  sub_r a b h := by
    have h' : b.neg.isNaN = true := by rw [F64.neg_isNaN]; exact h
    show (F64.add a b.neg).isNaN = true
    simp [F64.add, h', qnan_isNaN]
  mul_l a b h := by
    have h' : a.isNaN = true := h
    show (F64.mul a b).isNaN = true
    simp [F64.mul, h', qnan_isNaN]
  mul_r a b h := by
    have h' : b.isNaN = true := h
    show (F64.mul a b).isNaN = true
    simp [F64.mul, h', qnan_isNaN]
  div_l a b h := by
    have h' : a.isNaN = true := h
    show (F64.div a b).isNaN = true
    simp [F64.div, h', qnan_isNaN]
  div_r a b h := by
    have h' : b.isNaN = true := h
    show (F64.div a b).isNaN = true
    simp [F64.div, h', qnan_isNaN]
  neg a h := by
    show (F64.neg a).isNaN = true
    rw [F64.neg_isNaN]; exact h
  exp a h := hexp a h
  sqrt a h := by
    have h' : a.isNaN = true := h
    show (F64.sqrt a).isNaN = true
    simp [F64.sqrt, h', qnan_isNaN]
  lt_l a b h := by
    have h' : a.isNaN = true := h
    show F64.lt a b = false
    simp [F64.lt, h']
  lt_r a b h := by
    have h' : b.isNaN = true := h
    show F64.lt a b = false
    simp [F64.lt, h']
  le_l a b h := by
    have h' : a.isNaN = true := h
    show F64.le a b = false
    simp [F64.le, F64.lt, F64.eq, h']
  le_r a b h := by
    have h' : b.isNaN = true := h
    show F64.le a b = false
    simp [F64.le, F64.lt, F64.eq, h']
  beq_l a b h := by
    have h' : a.isNaN = true := h
    show F64.eq a b = false
    simp [F64.eq, h']
  not_inf a h := f64_isInf_of_isNaN h

theorem le_one_zero [RandLibm] : Flt.le (1.0 : F64) 0.0 = false := by
  show F64.le (F64R.ofDecimal 10 true 1) (F64R.ofDecimal 0 true 1) = false
  decide +kernel

theorem annexWitness_expNaN : @ExpNaN annexWitness := fun _ h => h

/-! ### The NaN hangs, over binary64 -/

/-- `gammavariate(nan, beta)` with `beta > 0` never returns, for every C library with
`exp(NaN) = NaN`, every generator and every state: each round of the `alpha < 1.0`
loop is rejected (`gammaGS_nan`). -/
theorem gammavariate_nan_f64 [RandLibm] (hexp : ExpNaN) {σ : Type} (g : Gen σ F64)
    (alpha beta : F64) (ha : alpha.isNaN = true) (hb : F64.le beta 0.0 = false) (fuel : Nat) (s : σ) :
    (gammavariate g fuel alpha beta s).1 = .error .modelFuel :=
  gammavariate_nan (f64_ieeeNaN hexp) g alpha beta ha hb fuel s

/-- Every `gammavariate(alpha, beta)` call either raises or leaves its rejection loop
for some sequence of `random()` values, over binary64 with any C library that has
`exp(NaN) = NaN`. False: `alpha = nan` passes `alpha <= 0.0 or beta <= 0.0`
(Lib/random.py:687), fails `alpha > 1.0` and `alpha == 1.0` (:690, :713), and in the
`alpha < 1.0` loop (:720-733) `p` is NaN, so `p > 1.0` and `u1 <= _exp(-x)` are both
false for every draw (`gammavariate_nan_f64`). -/
def GammaExitsForSomeDraws : Prop :=
  ∀ [RandLibm], ExpNaN → ∀ alpha beta : F64,
    ∃ (σ : Type) (g : Gen σ F64) (s : σ) (fuel : Nat),
      (gammavariate g fuel alpha beta s).1 ≠ .error .modelFuel

theorem gammaExitsForSomeDraws_refuted : ¬ GammaExitsForSomeDraws := by
  intro h
  letI := annexWitness
  obtain ⟨σ, g, s, fuel, hne⟩ := h annexWitness_expNaN F64.qnan 1.0
  exact hne (gammavariate_nan_f64 annexWitness_expNaN g _ _ qnan_isNaN le_one_zero fuel s)

/-- `betavariate(nan, beta)` hangs in its first `gammavariate(alpha, 1.0)` call
(Lib/random.py:762), and `betavariate(alpha, nan)` with `alpha > 0` hangs in the
second one (:764) whenever the first returns a nonzero value. -/
theorem betavariate_nan_f64 [RandLibm] (hexp : ExpNaN) {σ : Type} (g : Gen σ F64)
    (alpha beta : F64) (ha : alpha.isNaN = true) (fuel : Nat) (s : σ) :
    (betavariate g fuel alpha beta s).1 = .error .modelFuel := by
  have hl := gammavariate_nan_f64 hexp g alpha 1.0 ha le_one_zero fuel s
  simp only [betavariate, RM.bind_apply]
  cases hc : gammavariate g fuel alpha 1.0 s with
  | mk r t =>
    rw [hc] at hl
    simp only at hl
    subst hl
    rfl

/-- The second half: once the first `gammavariate(alpha, 1.0)` returned a truthy `y`,
`gammavariate(nan, 1.0)` never returns. -/
theorem betavariate_nan_beta_f64 [RandLibm] (hexp : ExpNaN) {σ : Type} (g : Gen σ F64)
    (alpha beta y : F64) (hb : beta.isNaN = true) (fuel : Nat) (s s1 : σ)
    (hy : gammavariate g fuel alpha 1.0 s = (.ok y, s1)) (ht : truthy y = true) :
    (betavariate g fuel alpha beta s).1 = .error .modelFuel := by
  have hl := gammavariate_nan_f64 hexp g beta 1.0 hb le_one_zero fuel s1
  simp only [betavariate, RM.bind_apply, hy, ht, if_true]
  cases hc : gammavariate g fuel beta 1.0 s1 with
  | mk r t =>
    rw [hc] at hl
    simp only at hl
    subst hl
    rfl

/-- Every `betavariate(alpha, beta)` call raises or returns for some draws. False for
`alpha = nan` (`betavariate_nan_f64`), and for `beta = nan` too once the first gamma
variate is nonzero (`betavariate_nan_beta_f64`). -/
def BetaExitsForSomeDraws : Prop :=
  ∀ [RandLibm], ExpNaN → ∀ alpha beta : F64,
    ∃ (σ : Type) (g : Gen σ F64) (s : σ) (fuel : Nat),
      (betavariate g fuel alpha beta s).1 ≠ .error .modelFuel

theorem betaExitsForSomeDraws_refuted : ¬ BetaExitsForSomeDraws := by
  intro h
  letI := annexWitness
  obtain ⟨σ, g, s, fuel, hne⟩ := h annexWitness_expNaN F64.qnan 1.0
  exact hne (betavariate_nan_f64 annexWitness_expNaN g _ _ qnan_isNaN fuel s)

/-- `vonmisesvariate(mu, nan)` never returns, for every C library with `exp(NaN) = NaN`
and every generator whose `cos(pi * random())` is defined. -/
theorem vonmisesvariate_nan_f64 [RandLibm] (hexp : ExpNaN) {σ : Type} (g : Gen σ F64)
    (mu kappa : F64) (hk : kappa.isNaN = true)
    (hcos : ∀ s, ∃ z, mathCos (PI * (g.random s).1) = .ok z) (fuel : Nat) (s : σ) :
    (vonmisesvariate g fuel mu kappa s).1 = .error .modelFuel :=
  vonmisesvariate_nan (f64_ieeeNaN hexp) g mu kappa hk hcos fuel s

/-- Every `vonmisesvariate(mu, kappa)` call raises or returns for some draws, over
binary64. False: `kappa = nan` passes `kappa <= 1e-6` (Lib/random.py:642), so
`s = 0.5 / kappa` and `r` are NaN, `d = z / (r + z)` is NaN in every round, and both
`u2 < 1.0 - d * d` and `u2 <= (1.0 - d) * _exp(d)` (:654) are false. -/
def VonmisesExitsForSomeDraws : Prop :=
  ∀ [RandLibm], ExpNaN → ∀ mu kappa : F64,
    ∃ (σ : Type) (g : Gen σ F64) (s : σ) (fuel : Nat),
      (vonmisesvariate g fuel mu kappa s).1 ≠ .error .modelFuel

theorem vonmisesExitsForSomeDraws_refuted : ¬ VonmisesExitsForSomeDraws := by
  intro h
  letI := annexWitness
  obtain ⟨σ, g, s, fuel, hne⟩ := h annexWitness_expNaN 0.0 F64.qnan
  have hcos : ∀ x : F64, ∃ z, mathCos x = .ok z := by
    intro x
    refine ⟨x, ?_⟩
    show math1Dom id x = .ok x
    unfold math1Dom
    cases hn : x.isNaN <;> cases hi : x.isInf <;>
      simp_all [Flt.isFinite, Flt.isNan, Flt.isInf, instFltF64]
  exact hne (vonmisesvariate_nan_f64 annexWitness_expNaN g _ _ qnan_isNaN
    (fun t => hcos _) fuel s)

/-- A `p` outside `0.0 <= p <= 1.0` raises the documented `ValueError`
(Lib/random.py:819), over binary64 with any C library. False for NaN: the check is
`p <= 0.0 or p >= 1.0`, which a NaN passes, and for `n >= 2` the `assert` at :850
raises `AssertionError` (with `python -O`, `_floor(nan)` raises instead), while `n == 1`
returns `0`. -/
def BinomialRejectsNaN : Prop :=
  ∀ [RandLibm] (p : F64), p.isNaN = true →
    ∀ (σ : Type) (g : Gen σ F64) (fuel depth : Nat) (n : Int) (s : σ), 0 ≤ n →
      ∃ e, (binomialvariate g fuel (depth + 1) n p s).1 = .error e ∧ e.className = "ValueError"

/-- What a NaN `p` does for `n >= 2`, over binary64, with any C library and any
generator: `AssertionError` before any draw. (`x` is `float(n)`.) -/
theorem binomial_nan_f64 [RandLibm] {σ : Type} (g : Gen σ F64) (fuel depth : Nat) (n : Int)
    (p x : F64) (s : σ) (hp : p.isNaN = true) (h0 : 0 ≤ n) (h1 : n ≠ 1) (hx : Flt.ofInt n = some x) :
    binomialvariate g fuel (depth + 1) n p s = (.error (.assertionError ""), s) := by
  have hxp : (F64.mul x p).isNaN = true := by simp [F64.mul, hp, qnan_isNaN]
  have a1 : Flt.le p 0.0 = false := by show F64.le p _ = false; simp [F64.le, F64.lt, F64.eq, hp]
  have a2 : Flt.le 1.0 p = false := by show F64.le _ p = false; simp [F64.le, F64.lt, F64.eq, hp]
  have a3 : Flt.lt 0.5 p = false := by show F64.lt _ p = false; simp [F64.lt, hp]
  have a4 : Flt.lt (x * p) 10.0 = false := by
    show F64.lt (F64.mul x p) _ = false; simp [F64.lt, hxp]
  have a5 : Flt.le 10.0 (x * p) = false := by
    show F64.le _ (F64.mul x p) = false; simp [F64.le, F64.lt, F64.eq, hxp]
  have hf : (pyFloat n : Py F64) = .ok x := by simp [pyFloat, hx]
  simp only [binomialvariate]
  rw [if_neg (by omega)]
  simp only [a1, a2, Bool.or_self, Bool.false_eq_true, if_false]
  rw [if_neg h1]
  simp only [a3, Bool.false_eq_true, if_false, RM.bind_apply, RM.lift_apply, hf, a4, a5,
    Bool.false_and, Bool.not_false, if_true]
  rfl

theorem binomialRejectsNaN_refuted : ¬ BinomialRejectsNaN := by
  intro h
  letI := annexWitness
  obtain ⟨e, he, hc⟩ := h F64.qnan qnan_isNaN Unit ⟨fun s => (0.5, s), fun _ s => (.ok 0, s)⟩
    0 0 2 () (by decide)
  have h2 : (Flt.ofInt (2 : Int) : Option F64) = some (F64.ofInt 2) := by
    show F64R.ofIntOpt 2 = some (F64.ofInt 2)
    decide +kernel
  rw [binomial_nan_f64 _ 0 0 2 F64.qnan (F64.ofInt 2) () qnan_isNaN (by decide) (by decide)
    h2] at he
  cases he
  simp [PyExc.className] at hc

end PyLean.CoreLibs.Rand
