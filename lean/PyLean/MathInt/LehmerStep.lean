import PyLean.MathInt.IsqrtAlg

/-!
One iteration of the inner loop of Lehmer's algorithm in `_PyLong_GCD`
(longobject.c:5816-5827), on integers.

The loop works on `x, y`, the top bits of `a, b` (`a = M*x0 + α`,
`b = M*y0 + β`, `0 <= α, β < M`), with cofactors `A, B, C, D`. Writing
`(xp, yp, ap, bp)` for `(x0, y0, a, b)` after an even number of steps and
`(y0, x0, b, a)` after an odd number, the loop keeps

* `x = A*xp - B*yp`, `y = D*yp - C*xp`, `A*D - B*C = 1`,
* `A, D >= 1`, `B, C >= 0`, `C <= y <= x`,

and the "true" pair `X = A*ap - B*bp`, `Y = D*bp - C*ap` is a pair of
consecutive remainders of Euclid's algorithm on `(a, b)`. The acceptance test
`B + q*D <= x - q*y` (with `q = (x + A - 1) // (y - C)`) is exactly what makes
`q` the true quotient `X // Y`, so the next true pair is `(Y, X - q*Y)`.
-/

namespace PyLean.MathInt

/-- Bounds from `a = M*xp + u`, `b = M*yp + v`: the approximation
`M*x` of `X` is off by less than `M*A` above and at most `M*B` below. -/
theorem lehmer_true_bounds (M xp yp ap bp x y A B C D : Int)
    (hM : 1 ≤ M) (hx : x = A * xp - B * yp) (hy : y = D * yp - C * xp)
    (hA : 1 ≤ A) (hD : 1 ≤ D) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha1 : M * xp ≤ ap) (ha2 : ap < M * (xp + 1)) (hb1 : M * yp ≤ bp) (hb2 : bp < M * (yp + 1)) :
    M * (x - B) ≤ A * ap - B * bp ∧ A * ap - B * bp < M * (x + A) ∧
    M * (y - C) ≤ D * bp - C * ap ∧ D * bp - C * ap < M * (y + D) := by
  have hu0 : 0 ≤ ap - M * xp := by omega
  have hu1 : ap - M * xp ≤ M - 1 := by have : M * (xp + 1) = M * xp + M := by grind
                                       omega
  have hv0 : 0 ≤ bp - M * yp := by omega
  have hv1 : bp - M * yp ≤ M - 1 := by have : M * (yp + 1) = M * yp + M := by grind
                                       omega
  generalize hu : ap - M * xp = u at *
  generalize hv : bp - M * yp = v at *
  have eX : A * ap - B * bp = M * x + A * u - B * v := by
    rw [show ap = M * xp + u by omega, show bp = M * yp + v by omega, hx]; grind
  have eY : D * bp - C * ap = M * y + D * v - C * u := by
    rw [show ap = M * xp + u by omega, show bp = M * yp + v by omega, hy]; grind
  have p1 : 0 ≤ A * u := Int.mul_nonneg (by omega) hu0
  have p2 : A * u ≤ A * (M - 1) := Int.mul_le_mul_of_nonneg_left hu1 (by omega)
  have p3 : 0 ≤ B * v := Int.mul_nonneg hB hv0
  have p4 : B * v ≤ B * (M - 1) := Int.mul_le_mul_of_nonneg_left hv1 hB
  have p5 : 0 ≤ D * v := Int.mul_nonneg (by omega) hv0
  have p6 : D * v ≤ D * (M - 1) := Int.mul_le_mul_of_nonneg_left hv1 (by omega)
  have p7 : 0 ≤ C * u := Int.mul_nonneg hC hu0
  have p8 : C * u ≤ C * (M - 1) := Int.mul_le_mul_of_nonneg_left hu1 hC
  rw [eX, eY]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- The acceptance test makes `q` the true quotient: `0 <= X - q*Y < Y`. -/
theorem lehmer_true_quotient (M x y A B C D X Y q : Int) (hM : 1 ≤ M)
    (hA : 1 ≤ A) (hq0 : 0 ≤ q) (hyc : 1 ≤ y - C)
    (hq2 : x + A - 1 < (q + 1) * (y - C)) (hacc : B + q * D ≤ x - q * y)
    (hX1 : M * (x - B) ≤ X) (hX2 : X < M * (x + A))
    (hY1 : M * (y - C) ≤ Y) (hY2 : Y < M * (y + D)) :
    0 ≤ X - q * Y ∧ X - q * Y < Y := by
  constructor
  · have h1 : q * Y ≤ q * (M * (y + D)) := Int.mul_le_mul_of_nonneg_left (by omega) hq0
    have h2 : 0 ≤ M * ((x - q * y) - (B + q * D)) := Int.mul_nonneg (by omega) (by omega)
    grind
  · have h1 : (q + 1) * (M * (y - C)) ≤ (q + 1) * Y := Int.mul_le_mul_of_nonneg_left hY1 (by omega)
    have h2 : M * (x + A) ≤ M * ((q + 1) * (y - C)) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    grind

/-- No `int64_t` overflow: every intermediate of one iteration stays below
`2^62` in absolute value (the cofactors are bounded through
`xp = D*x + B*y`, `yp = C*x + A*y`). -/
theorem lehmer_no_overflow (xp yp x y A B C D q : Int)
    (hx : x = A * xp - B * yp) (hy : y = D * yp - C * xp) (hdet : A * D - B * C = 1)
    (hA : 1 ≤ A) (hD : 1 ≤ D) (hB : 0 ≤ B) (hC : 0 ≤ C) (hCy : C ≤ y) (hyx : y ≤ x)
    (hxp : xp < 2 ^ 60) (hyp : yp < 2 ^ 60) (hyc : 1 ≤ y - C)
    (hq0 : 0 ≤ q) (hq1 : q * (y - C) ≤ x + A - 1) :
    0 ≤ x + (A - 1) ∧ x + (A - 1) < 2 ^ 61 ∧ 0 ≤ q * D ∧ q * D ≤ 2 ^ 61 + 1 ∧
    0 ≤ q * C ∧ q * C ≤ 2 ^ 61 ∧ 0 ≤ q * y ∧ q * y ≤ 2 ^ 62 ∧ B ≤ 2 ^ 60 ∧ A ≤ 2 ^ 60 := by
  have exp : D * x + B * y = xp := by
    have : (A * D - B * C) * xp = xp := by rw [hdet, Int.one_mul]
    rw [hx, hy]; grind
  have eyp : C * x + A * y = yp := by
    have : (A * D - B * C) * yp = yp := by rw [hdet, Int.one_mul]
    rw [hx, hy]; grind
  have hy1 : 1 ≤ y := by omega
  have f1 : 0 ≤ D * x := Int.mul_nonneg (by omega) (by omega)
  have f2 : 0 ≤ B * y := Int.mul_nonneg hB (by omega)
  have f3 : 0 ≤ C * x := Int.mul_nonneg hC (by omega)
  have f4 : 0 ≤ A * y := Int.mul_nonneg (by omega) (by omega)
  have f5 : A ≤ A * y := by have := Int.mul_nonneg (show 0 ≤ A by omega) (show 0 ≤ y - 1 by omega); grind
  have f6 : B ≤ B * y := by have := Int.mul_nonneg hB (show 0 ≤ y - 1 by omega); grind
  have f7 : B * C ≤ B * y := Int.mul_le_mul_of_nonneg_left hCy hB
  have f8 : A * C ≤ A * y := Int.mul_le_mul_of_nonneg_left hCy (by omega)
  have hq : q ≤ x + A - 1 := by
    have := Int.mul_nonneg hq0 (show 0 ≤ y - C - 1 by omega); grind
  have g1 : q * D ≤ (x + A - 1) * D := Int.mul_le_mul_of_nonneg_right hq (by omega)
  have g2 : q * C ≤ (x + A - 1) * C := Int.mul_le_mul_of_nonneg_right hq hC
  have g3 : 0 ≤ q * D := Int.mul_nonneg hq0 (by omega)
  have g4 : 0 ≤ q * C := Int.mul_nonneg hq0 hC
  have g5 : 0 ≤ q * y := Int.mul_nonneg hq0 (by omega)
  have f9 : x ≤ D * x := by have := Int.mul_nonneg (show 0 ≤ D - 1 by omega) (show 0 ≤ x by omega); grind
  have e1 : (x + A - 1) * D = D * x + A * D - D := by grind
  have e2 : (x + A - 1) * C = C * x + A * C - C := by grind
  have e3 : q * y = q * (y - C) + q * C := by grind
  refine ⟨by omega, by omega, g3, by omega, g4, by omega, g5, by omega, by omega, by omega⟩

end PyLean.MathInt
