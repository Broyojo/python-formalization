import PyLean.CoreLibs.Rand.F64Inst
import PyLean.CoreLibs.Rand.Dist

/-!
Statements about float values that are still open, over the exact binary64 model
`F64` with any C library `RandLibm` (none of them calls libm).
-/

namespace PyLean.CoreLibs.Rand

open PyLean Flt PyLean.Binary64

/-- For `n >= 2**53`, `floor(random() * n)` is below `n`
(`_randbelow_without_getrandbits`, Lib/random.py:266). -/
def RandbelowWithoutHuge : Prop :=
  ∀ (n : Nat) [RandLibm] (r x : F64) (v : Int), 2 ^ 53 ≤ n → Flt.le 0.0 r = true → Flt.lt r 1.0 = true →
    Flt.ofInt (n : Int) = some x → mathFloor (r * x) = .ok v → 0 ≤ v ∧ v < n

/-- For `n > 0`, `population[floor(random() * n)]` is in range (`choices`,
Lib/random.py:473), so `choices` on a non-empty population raises no `IndexError`. -/
def ChoicesIndexInRange : Prop :=
  ∀ (n : Nat) [RandLibm] (r x : F64) (v : Int), 0 < n → Flt.le 0.0 r = true → Flt.lt r 1.0 = true →
    Flt.ofInt (n : Int) = some x → mathFloor (r * (x + 0.0)) = .ok v → 0 ≤ v ∧ v < n

/-- `a + (b - a) * random()` lies in `[a, b]` when `b - a` does not overflow
(`uniform`, Lib/random.py:501). -/
def UniformInRange : Prop :=
  ∀ [RandLibm] (a b r : F64), Flt.le a b = true → isFinite (b - a) = true →
    Flt.le 0.0 r = true → Flt.lt r 1.0 = true →
    Flt.le a (a + (b - a) * r) = true ∧ Flt.le (a + (b - a) * r) b = true

/-- `binomialvariate(n, p)` lies in `[0, n]` for a generator with `random()` in
`[0, 1)` (docstring, Lib/random.py:797-799). -/
def BinomialInRange : Prop :=
  ∀ [RandLibm] (σ : Type) (g : Gen σ F64) (fuel depth : Nat) (n : Int) (p : F64) (s s' : σ) (r : Int),
    (∀ t, Flt.le 0.0 (g.random t).1 = true ∧ Flt.lt (g.random t).1 1.0 = true) →
    binomialvariate g fuel depth n p s = (.ok r, s') → 0 ≤ r ∧ r ≤ n

end PyLean.CoreLibs.Rand
