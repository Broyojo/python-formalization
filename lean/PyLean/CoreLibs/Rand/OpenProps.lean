import PyLean.CoreLibs.Rand.FloatInst
import PyLean.CoreLibs.Rand.Dist

/-!
Statements about float values, open until the Binary64 model is merged. They are
about Lean's `Float`, which proofs cannot reduce; the difftest checks these paths bit
for bit against CPython.
-/

namespace PyLean.CoreLibs.Rand

open PyLean Flt PyLean.CoreLibs.Rand.FloatInst

/-- For `n >= 2**53`, `floor(random() * n)` is below `n`
(`_randbelow_without_getrandbits`, Lib/random.py:266). -/
def RandbelowWithoutHuge : Prop :=
  ∀ (n : Nat) (r x : Float) (v : Int), 2 ^ 53 ≤ n → Flt.le 0.0 r = true → Flt.lt r 1.0 = true →
    Flt.ofInt (n : Int) = some x → mathFloor (r * x) = .ok v → 0 ≤ v ∧ v < n

/-- For `n > 0`, `population[floor(random() * n)]` is in range (`choices`,
Lib/random.py:473), so `choices` on a non-empty population raises no `IndexError`. -/
def ChoicesIndexInRange : Prop :=
  ∀ (n : Nat) (r x : Float) (v : Int), 0 < n → Flt.le 0.0 r = true → Flt.lt r 1.0 = true →
    Flt.ofInt (n : Int) = some x → mathFloor (r * (x + 0.0)) = .ok v → 0 ≤ v ∧ v < n

/-- `a + (b - a) * random()` lies in `[a, b]` when `b - a` does not overflow
(`uniform`, Lib/random.py:501). -/
def UniformInRange : Prop :=
  ∀ (a b r : Float), Flt.le a b = true → isFinite (b - a) = true →
    Flt.le 0.0 r = true → Flt.lt r 1.0 = true →
    Flt.le a (a + (b - a) * r) = true ∧ Flt.le (a + (b - a) * r) b = true

/-- `binomialvariate(n, p)` lies in `[0, n]` for a generator with `random()` in
`[0, 1)` (docstring, Lib/random.py:797-799). -/
def BinomialInRange : Prop :=
  ∀ (σ : Type) (g : Gen σ Float) (fuel depth : Nat) (n : Int) (p : Float) (s s' : σ) (r : Int),
    (∀ t, Flt.le 0.0 (g.random t).1 = true ∧ Flt.lt (g.random t).1 1.0 = true) →
    binomialvariate g fuel depth n p s = (.ok r, s') → 0 ≤ r ∧ r ≤ n

end PyLean.CoreLibs.Rand
