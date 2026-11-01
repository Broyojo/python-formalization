import PyLean.LongObj.ComplexDbl
import PyLean.LongObj.ComplexObj

/-!
Statements about `Objects/complexobject.c` at exact binary64, `Dbl`. The false
ones are refuted by the kernel evaluating the mirrored source, and each comes
with a CPython reproducer in `bugs/`. Each refutation sits next to the narrower
statement that does hold, where one could be settled without a rounding proof.
-/

namespace PyLean.LongObj.Cplx

open CDouble

namespace Dbl

def d1 : Dbl := ⟨0x3ff0000000000000⟩
def dNeg2 : Dbl := ⟨0xc000000000000000⟩
def d1e308 : Dbl := ⟨0x7fe1ccf385ebc8a0⟩
def d1em200 : Dbl := ⟨0x16687e92154ef7ac⟩
def d42 : Dbl := ⟨0x4045000000000000⟩
/-- `atan2(1.0, 1.0)`. -/
def dPiOver4 : Dbl := ⟨0x3fe921fb54442d18⟩

end Dbl

open Dbl

/-- A libm about which nothing is claimed. Used where the path under test makes
no libm call, so the result does not depend on it. -/
def noLibm : Libm Dbl where
  hypot _ _ := (⟨0⟩, none)
  pow _ _ := (⟨0⟩, none)
  atan2 _ _ := (⟨0⟩, none)
  exp _ := (⟨0⟩, none)
  log _ := (⟨0⟩, none)
  cos _ := (⟨0⟩, none)
  sin _ := (⟨0⟩, none)

/-! ## `abs()` and a stale `errno` -/

/-- `abs(z)` depends only on `z`, not on what the previous C call left in
`errno`. The comment on line 370 promises `errno` is set either way. -/
def ComplexAbsIgnoresStaleErrno : Prop :=
  ∀ (L : Libm Dbl) (z : Cx Dbl) (e : Errno), complex_abs L z e = complex_abs L z Errno.ok

theorem complexAbsIgnoresStaleErrno_refuted : ¬ ComplexAbsIgnoresStaleErrno := by
  intro h
  have := h noLibm ⟨qnan, ⟨0⟩⟩ Errno.erange
  revert this
  decide +kernel

/-- A NaN path is the only one where the incoming `errno` survives: the narrowed
statement. With `errno` clear on entry, as `complex_abs` should ensure, the
result does not raise on a value with a NaN and no infinity. -/
def ComplexAbsCleanErrno : Prop :=
  ∀ (L : Libm Dbl) (z : Cx Dbl) (e : Errno), e ≠ Errno.erange →
    (isnan z.real = true ∨ isnan z.imag = true) →
    isinf z.real = false → isinf z.imag = false →
    complex_abs L z e = .ok qnan

theorem complexAbsCleanErrno_proven : ComplexAbsCleanErrno := by
  intro L z e he hn hr hi
  have hnf : (!isfinite z.real || !isfinite z.imag) = true := by
    rcases hn with hn | hn <;> simp [isfinite, hn]
  simp only [complex_abs, c_abs, hnf, ite_true, hr, hi, Bool.false_eq_true, ite_false]
  simp [he]
  rfl

/-- C99 Annex G, the comment on lines 374-376: an infinite part gives an infinite
absolute value, even if the other part is a NaN, whatever `errno` was. -/
def CAbsInfinity : Prop :=
  ∀ (R : Type) (_ : CDouble R) (L : Libm R) (z : Cx R) (e : Errno),
    (isinf z.real = true → c_abs L z e = (fabs z.real, Errno.ok)) ∧
    (isinf z.real = false → isinf z.imag = true → c_abs L z e = (fabs z.imag, Errno.ok))

theorem cAbsInfinity_proven : CAbsInfinity := by
  intro R _ L z e
  constructor
  · intro h
    simp [c_abs, isfinite, h]
  · intro h1 h2
    simp [c_abs, isfinite, h1, h2]

/-! ## `**` -/

/-- `ZeroDivisionError: zero to a negative or complex power` is raised only for a
zero base. -/
def PowZeroDivisionNeedsZeroBase : Prop :=
  ∀ (L : Libm Dbl) (a b : Cx Dbl),
    complex_pow_core L a b =
        .error (.zeroDivisionError "zero to a negative or complex power") →
      (a.real ==. CDouble.zero && a.imag ==. CDouble.zero) = true

/-- `complex(1e-200) ** -2`: `c_powu` underflows to `0`, so `c_powi` divides by
zero, and the `EDOM` reports a zero base. The integer-exponent path makes no libm
call, so this holds for every libm. -/
theorem powZeroDivisionNeedsZeroBase_refuted : ¬ PowZeroDivisionNeedsZeroBase := by
  intro h
  have := h noLibm ⟨d1em200, ⟨0⟩⟩ ⟨dNeg2, ⟨0⟩⟩ (by decide +kernel)
  revert this
  decide +kernel

/-- What glibc does at the points the slow path needs. `cos` and `sin` of an
infinity set `EDOM`, and `atan2(1, 1)` is the double nearest `π/4`. -/
structure GlibcTrig (L : Libm Dbl) : Prop where
  cos_inf : ∀ x : Dbl, x.isInf = true → (L.cos x).2 = some Errno.edom
  sin_inf : ∀ x : Dbl, x.isInf = true → (L.sin x).2 = some Errno.edom
  atan2_one : (L.atan2 d1 d1).1 = dPiOver4

/-- `_Py_c_pow` sets `EDOM` only for a zero base. -/
def CPowEdomNeedsZeroBase : Prop :=
  ∀ (L : Libm Dbl), GlibcTrig L → ∀ a b : Cx Dbl,
    (c_pow L a b Errno.ok).2 = Errno.edom →
      (a.real ==. CDouble.zero && a.imag ==. CDouble.zero) = true

/-- A libm agreeing with glibc on what `GlibcTrig` names. -/
def glibcLike : Libm Dbl where
  hypot _ _ := (d1, none)
  pow _ _ := (pinf, none)
  atan2 _ _ := (dPiOver4, none)
  exp _ := (d1, none)
  log _ := (⟨0⟩, none)
  cos x := (qnan, if x.isInf then some Errno.edom else none)
  sin x := (qnan, if x.isInf then some Errno.edom else none)

theorem glibcLike_trig : GlibcTrig glibcLike where
  cos_inf x h := by simp [glibcLike, h]
  sin_inf x h := by simp [glibcLike, h]
  atan2_one := rfl

/-- `(1+1j) ** inf`: the phase is infinite, `cos` sets `EDOM`, and `complex_pow`
reports a zero base. glibc only: macOS libm does not set `errno`. -/
theorem cPowEdomNeedsZeroBase_refuted : ¬ CPowEdomNeedsZeroBase := by
  intro h
  have := h glibcLike glibcLike_trig ⟨d1, d1⟩ ⟨pinf, ⟨0⟩⟩ (by decide +kernel)
  revert this
  decide +kernel

/-- `x ** 1` does not raise. -/
def PowOneNeverRaises : Prop :=
  ∀ (L : Libm Dbl) (x : Cx Dbl), (complex_pow_core L x ⟨d1, ⟨0⟩⟩).toBool = true

/-- `complex('inf') ** 1`: the base is already infinite, and `_Py_ADJUST_ERANGE2`
takes any infinite result for an overflow. -/
theorem powOneNeverRaises_refuted : ¬ PowOneNeverRaises := by
  intro h
  have := h noLibm ⟨pinf, ⟨0⟩⟩
  revert this
  decide +kernel

/-! ## Mixed-mode division -/

/-- Equal as C `==` sees it, or both NaN: signed zeros are not distinguished. -/
def sameValue (x y : Dbl) : Bool := (isnan x && isnan y) || x ==. y

/-- `_Py_rc_quot` is "an equivalent of `_Py_c_quot()` function, when 1st argument
is real" (line 263), up to the signs of zeros. -/
def RcQuotMatchesCQuot : Prop :=
  ∀ (a : Dbl) (b : Cx Dbl),
    let r := rc_quot a b Errno.ok
    let c := c_quot ⟨a, CDouble.zero⟩ b Errno.ok
    (sameValue r.1.real c.1.real && sameValue r.1.imag c.1.imag && r.2 == c.2) = true

/-- `float('inf') / (1e308+1e308j)`: the denominator overflows, both parts are
NaN, and `_Py_rc_quot` lacks the first recovery branch of `_Py_c_quot`
(lines 227-234), so it stays `nan+nanj` where `_Py_c_quot` gives `inf-infj`. -/
theorem rcQuotMatchesCQuot_refuted : ¬ RcQuotMatchesCQuot := by
  intro h
  have := h pinf ⟨d1e308, d1e308⟩
  revert this
  decide +kernel

/-! ## `complex(x)` and `complex(x, 0)` -/

/-- A `float` subclass that overrides `__float__`. -/
def floatSubOverriding (ret : Dbl) : Obj Dbl :=
  .mk ⟨"F", "m.F", true⟩ false (.flt d1) .absent (.returns (mkFloat ret)) .absent

/-- The real part `m` computes, if it computes. -/
def realPart (m : M (Made Dbl)) : Option Dbl :=
  match m.run [] with
  | .ok r _ => some r.cval.real
  | .error _ _ => none

/-- An environment no path here consults. -/
def plainEnv : Env Dbl :=
  { warnErr := false, db := ⟨fun _ => false, fun _ => none⟩, sd := Dbl.asciiStrtod }

/-- `complex(x)` and `complex(x, 0)` take the same real part from a `float`
instance. The first goes through `PyFloat_AsDouble` (line 1141), the second
through `PyNumber_Float` (line 1256). -/
def OneArgMatchesTwoArgOnFloats : Prop :=
  ∀ (x : Obj Dbl), (∃ v, x.val = .flt v) →
    realPart (actual_complex_new plainEnv .complex [x] []) =
      realPart (actual_complex_new plainEnv .complex [x, mkFloat CDouble.zero] [])

/-- `class F(float): __float__ = lambda s: 42.0`: `complex(F(1))` is `1+0j`,
`complex(F(1), 0)` is `42+0j`. -/
theorem oneArgMatchesTwoArgOnFloats_refuted : ¬ OneArgMatchesTwoArgOnFloats := by
  intro h
  have := h (floatSubOverriding d42) ⟨d1, rfl⟩
  revert this
  decide +kernel

/-! ## Stated, waiting on `Binary64`

These need facts about rounding that `Dbl` has no proofs for. `Dbl.Valid` is the type
invariant of a 64-bit pattern. -/

def Dbl.Valid (x : Dbl) : Prop := x.bits < 2 ^ 64

/-- C11 Annex G.5.1: an infinite operand and a nonzero finite one multiply to a value
with an infinite part. -/
def CProdAnnexG : Prop :=
  ∀ z w : Cx Dbl, z.real.Valid → z.imag.Valid → w.real.Valid → w.imag.Valid →
    (isinf z.real || isinf z.imag) = true → isfinite w.real = true → isfinite w.imag = true →
    ((w.real ==. CDouble.zero) && (w.imag ==. CDouble.zero)) = false →
    (isinf (c_prod z w).real || isinf (c_prod z w).imag) = true

/-- C11 Annex G.5.2: an infinite dividend over a finite nonzero divisor has an infinite
part, and a finite dividend over an infinite divisor has zero parts. -/
def CQuotAnnexG : Prop :=
  ∀ a b : Cx Dbl, a.real.Valid → a.imag.Valid → b.real.Valid → b.imag.Valid →
    ((isinf a.real || isinf a.imag) = true → isfinite b.real = true → isfinite b.imag = true →
      ((b.real ==. CDouble.zero) && (b.imag ==. CDouble.zero)) = false →
      (isinf (c_quot a b Errno.ok).1.real || isinf (c_quot a b Errno.ok).1.imag) = true) ∧
    (isfinite a.real = true → isfinite a.imag = true → (isinf b.real || isinf b.imag) = true →
      ((c_quot a b Errno.ok).1.real ==. CDouble.zero) = true ∧
      ((c_quot a b Errno.ok).1.imag ==. CDouble.zero) = true)

/-- The narrowing of `RcQuotMatchesCQuot`: the disagreement needs an infinite dividend
(or a NaN one). -/
def RcQuotMatchesCQuotFinite : Prop :=
  ∀ (a : Dbl) (b : Cx Dbl), a.Valid → b.real.Valid → b.imag.Valid → isfinite a = true →
    let r := rc_quot a b Errno.ok
    let c := c_quot ⟨a, CDouble.zero⟩ b Errno.ok
    (sameValue r.1.real c.1.real && sameValue r.1.imag c.1.imag && r.2 == c.2) = true

end PyLean.LongObj.Cplx
