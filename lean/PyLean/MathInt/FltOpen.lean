import PyLean.MathInt.FltSum

/-!
# Open properties of `Modules/mathmodule.c`

Stated, smoke-tested against CPython 3.15.2 and checked by the difftest. `FsumCorrectlyRounded` is
still open; `RemainderExact` is proven in `FltRemainder`.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64

/-- `q` rounded to the nearest integer, ties to the even one. -/
def roundHalfEven (q : Rat) : Int :=
  let f := q.floor
  let d := q - f
  if d < 1 / 2 then f else if 1 / 2 < d then f + 1 else if f % 2 = 0 then f else f + 1

/-- `math.fsum` of finite floats is the exact sum rounded once ("an accurate floating-point
sum"; the msum algorithm's claim that the result is correctly rounded), a zero for an exact zero
sum, or `OverflowError("intermediate overflow in fsum")` when a partial sum overflows. -/
def FsumCorrectlyRounded : Prop :=
  ∀ xs : List F64, xs.all (·.isFinite) = true →
    match math_fsum ⟨xs.map .float, none⟩ with
    | .ok r =>
      (((xs.map (·.toRat)).sum ≠ 0) → r = F64.ofRat (xs.map (·.toRat)).sum) ∧
      (((xs.map (·.toRat)).sum = 0) → r.isZero = true)
    | .error e => e = .overflowError "intermediate overflow in fsum"

/-- `math.remainder(x, y)` for finite `x` and finite nonzero `y` is exactly `x - n*y` with `n`
the integer nearest `x / y`, ties to even, and a zero result has the sign of `x`
(Doc/library/math.rst, "remainder": "the result of this operation is always exactly
representable"). Proven in `FltRemainder` by the argument of the comment at
mathmodule.c:545-563. -/
def RemainderExact : Prop :=
  ∀ x y : F64, x.isFinite = true → y.isFinite = true → y.isZero = false →
    ∃ r, math_remainder [.float x, .float y] = .ok r ∧ r.isFinite = true ∧
      r.toRat = x.toRat - (roundHalfEven (x.toRat / y.toRat) : Rat) * y.toRat ∧
      (r.isZero = true → r.sign = x.sign)

end PyLean.MathInt
