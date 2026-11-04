import PyLean.CoreLibs.Rand.DistF64
import PyLean.CoreLibs.Rand.F64Order

/-!
What each distribution of `Lib/random.py:500-890` computes from its draws, over binary64.

Every statement is for every C library (`RandLibm`), every core generator `g` and every
state `s`. `g.random s = (u, s1)` names the value of a `random()` call and the state
after it. The arithmetic is binary64's (`instFltF64`: `+` is `F64.add`, and so on), so
each statement pins the exact double the method returns, the exception it raises, and
the generator state either way. A method that used a different expression, a different
order of draws, or a different argument to `log` or `**`, fails them.

Rejection loops are pinned one round at a time: a round draws the values it draws,
computes a candidate, and either returns it or starts the next round on the state after
its draws. `Py (Option F64)` in a statement is the round's own computation: `some x`
accepts `x`, `none` rejects.
-/

namespace PyLean.CoreLibs.Rand

open PyLean PyLean.Binary64 RM Flt

/-! ### Unfolding the monad -/

theorem lift_bind_apply {σ α β : Type} (x : Py α) (f : α → RM σ β) (s : σ) :
    (RM.lift x >>= f) s = match x with
      | .ok a => f a s
      | .error e => (.error e, s) := by cases x <;> rfl

theorem rnd_bind_apply {σ F β : Type} {g : Gen σ F} {s s1 : σ} {u : F} (h : g.random s = (u, s1))
    (f : F → RM σ β) : (rnd g >>= f) s = f u s1 := by
  simp [RM.bind_apply, rnd, h]

/-! ### `uniform`, Lib/random.py:500-509 -/

theorem zero_f64 [RandLibm] : (0.0 : F64) = F64.zero false := by
  show F64R.ofDecimal 0 true 1 = _
  decide +kernel

/-- `uniform(a, b)` is `a + (b - a) * self.random()` (:509) in binary64, after exactly
one draw; and for finite `a <= b` whose difference does not overflow, with `random()` in
`[0, 1)`, it is never below `a` (the docstring's `[a, b)` or `[a, b]`; the upper end is
the open entry `rand-uniform-range`). -/
def UniformF64 : Prop :=
  ∀ [RandLibm] (σ : Type) (g : Gen σ F64) (a b u : F64) (s s1 : σ), g.random s = (u, s1) →
    uniform g a b s = (.ok (a + (b - a) * u), s1) ∧
    (a.isFinite = true → b.isFinite = true → a.toRat ≤ b.toRat → (b - a).isFinite = true →
      u.isFinite = true → 0 ≤ u.toRat → u.toRat < 1 → F64.le a (a + (b - a) * u) = true)

theorem uniformF64_proven : UniformF64 := by
  intro _ σ g a b u s s1 h
  refine ⟨?_, ?_⟩
  · simp only [uniform, RM.bind_apply, rnd, h]; rfl
  · intro ha hb hab hd hu hu0 hu1
    have hd0 := F64Order.sub_nonneg ha hb hab hd
    obtain ⟨hm, hm0, _⟩ := F64Order.mul_unit hd hu hd0 hu0 (Rat.le_of_lt hu1)
    exact F64Order.le_add ha hm hm0

/-! ### `triangular`, Lib/random.py:511-534 -/

/-- Lib/random.py:530-534 once `u` and `c` are known: swap the ends when `u > c`, then
`low + (high - low) * sqrt(u * c)`. -/
def triangularTail [RandLibm] (u c low high : F64) : Py F64 :=
  if Flt.lt c u then do
    let r ← mathSqrt ((1.0 - u) * (1.0 - c))
    pure (high + (low - high) * r)
  else do
    let r ← mathSqrt (u * c)
    pure (low + (high - low) * r)

/-- `triangular(low, high, mode)` after its one draw `u`: `c = 0.5` without a mode;
with one, `c = (mode - low) / (high - low)`, except that `high - low == 0` makes the
`ZeroDivisionError` handler (:526-529) return `low`; then `triangularTail`. -/
def TriangularF64 : Prop :=
  ∀ [RandLibm] (σ : Type) (g : Gen σ F64) (low high m u : F64) (s s1 : σ), g.random s = (u, s1) →
    triangular g low high none s = (triangularTail u 0.5 low high, s1) ∧
    (F64.eq (high - low) 0.0 = true → triangular g low high (some m) s = (.ok low, s1)) ∧
    (F64.eq (high - low) 0.0 = false →
      triangular g low high (some m) s = (triangularTail u ((m - low) / (high - low)) low high, s1))

theorem triangularF64_proven : TriangularF64 := by
  intro _ σ g low high m u s s1 h
  have tail : ∀ c : F64, (match (if Flt.lt c u then (1.0 - u, 1.0 - c, high, low) else (u, c, low, high)) with
      | (u, c, low, high) => (RM.lift (mathSqrt (u * c)) >>= fun s => Pure.pure (low + (high - low) * s)) s1)
      = (triangularTail u c low high, s1) := by
    intro c
    unfold triangularTail
    by_cases hc : Flt.lt c u = true
    · simp only [hc, if_true, lift_bind_apply, RM.pure_apply]
      cases mathSqrt ((1.0 - u) * (1.0 - c)) <;> rfl
    · simp only [hc, Bool.false_eq_true, if_false, lift_bind_apply, RM.pure_apply]
      cases mathSqrt (u * c) <;> rfl
  refine ⟨?_, fun hz => ?_, fun hz => ?_⟩
  · simp only [triangular, rnd_bind_apply h]
    exact tail 0.5
  · have : pyDiv (m - low) (high - low) = .error (.zeroDivisionError "division by zero") := by
      simp [pyDiv]; exact hz
    simp only [triangular, rnd_bind_apply h, this]; rfl
  · have : pyDiv (m - low) (high - low) = .ok ((m - low) / (high - low)) := by
      simp [pyDiv]; exact hz
    simp only [triangular, rnd_bind_apply h, this]
    exact tail _

/-! ### `normalvariate`, `lognormvariate`, Lib/random.py:536-603 -/

/-- One round of the Kinderman-Monahan loop (:548-554): draws `u1` and `r2`, sets
`u2 = 1.0 - r2`, `z = NV_MAGICCONST * (u1 - 0.5) / u2`, and accepts when
`z * z / 4.0 <= -log(u2)`; `normalvariate` returns `mu + z * sigma` (:555); and
`lognormvariate` is `exp` of `normalvariate` on the same draws (:603). -/
def NormalvariateF64 : Prop :=
  ∀ [RandLibm] (σ : Type) (g : Gen σ F64),
    (∀ (fuel : Nat) (u1 r2 : F64) (s s1 s2 : σ), g.random s = (u1, s1) → g.random s1 = (r2, s2) →
      normalLoop g (fuel + 1) s =
        match (do
            let z ← pyDiv (NV_MAGICCONST * (u1 - 0.5)) (1.0 - r2)
            let l ← mathLog (1.0 - r2)
            pure (if Flt.le (z * z / 4.0) (-l) then some z else none) : Py (Option F64)) with
        | .ok (some z) => (.ok z, s2)
        | .ok none => normalLoop g fuel s2
        | .error e => (.error e, s2)) ∧
    (∀ (fuel : Nat) (mu sigma : F64) (s : σ),
      normalvariate g fuel mu sigma s =
        match normalLoop g fuel s with
        | (.ok z, t) => (.ok (mu + z * sigma), t)
        | (.error e, t) => (.error e, t)) ∧
    (∀ (fuel : Nat) (mu sigma : F64) (s : σ),
      lognormvariate g fuel mu sigma s =
        match normalvariate g fuel mu sigma s with
        | (.ok x, t) => (mathExp x, t)
        | (.error e, t) => (.error e, t))

theorem normalvariateF64_proven : NormalvariateF64 := by
  intro _ σ g
  refine ⟨fun fuel u1 r2 s s1 s2 h1 h2 => ?_, fun fuel mu sigma s => ?_, fun fuel mu sigma s => ?_⟩
  · simp only [normalLoop, rnd_bind_apply h1, rnd_bind_apply h2, lift_bind_apply]
    cases pyDiv (NV_MAGICCONST * (u1 - 0.5)) (1.0 - r2) with
    | error e => rfl
    | ok z =>
      cases mathLog (1.0 - r2) with
      | error e => rfl
      | ok l =>
        by_cases hc : Flt.le (z * z / 4.0) (-l) = true
        · simp [hc, bind, Except.bind, pure, Except.pure]; rfl
        · simp [hc, bind, Except.bind, pure, Except.pure]
  · simp only [normalvariate, RM.bind_apply]
    cases normalLoop g fuel s with
    | mk r t => cases r <;> rfl
  · simp only [lognormvariate, RM.bind_apply]
    cases normalvariate g fuel mu sigma s with
    | mk r t => cases r <;> rfl

/-! ### `gauss`, Lib/random.py:557-593 -/

/-- Box-Muller with a cache. With `gauss_next` empty, `gauss` draws `u1` then `u2`,
computes `g2rad = sqrt(-2.0 * log(1.0 - u2))`, returns `mu + cos(u1 * TWOPI) * g2rad * sigma`
and stores `sin(u1 * TWOPI) * g2rad`; with a stored `z` it draws nothing, returns
`mu + z * sigma` and empties the cache. Together: two calls from an empty cache return
the two normals of one Box-Muller pair, from two draws. -/
def GaussF64 : Prop :=
  ∀ [RandLibm] (σ : Type) (g : Gen σ F64),
    (∀ (mu sigma u1 u2 : F64) (s s1 s2 : σ), g.random s = (u1, s1) → g.random s1 = (u2, s2) →
      gauss g mu sigma none s =
        match (do
            let l ← mathLog (1.0 - u2)
            let g2 ← mathSqrt (-2.0 * l)
            let c ← mathCos (u1 * TWOPI)
            let sn ← mathSin (u1 * TWOPI)
            pure (c * g2, sn * g2) : Py (F64 × F64)) with
        | .ok (z0, z1) => (.ok (mu + z0 * sigma, some z1), s2)
        | .error e => (.error e, s2)) ∧
    (∀ (mu sigma z : F64) (s : σ), gauss g mu sigma (some z) s = (.ok (mu + z * sigma, none), s))

theorem gaussF64_proven : GaussF64 := by
  intro _ σ g
  refine ⟨fun mu sigma u1 u2 s s1 s2 h1 h2 => ?_, fun _ _ _ _ => rfl⟩
  simp only [gauss, rnd_bind_apply h1, rnd_bind_apply h2, lift_bind_apply]
  cases mathLog (1.0 - u2) with
  | error e => rfl
  | ok l =>
    dsimp only [bind, Except.bind]
    cases mathSqrt (-2.0 * l) with
    | error e => rfl
    | ok g2 =>
      dsimp only [bind, Except.bind]
      cases mathCos (u1 * TWOPI) with
      | error e => rfl
      | ok c =>
        dsimp only [bind, Except.bind]
        cases mathSin (u1 * TWOPI) with
        | error e => rfl
        | ok sn => rfl

/-! ### `expovariate`, Lib/random.py:605-623 -/

/-- `expovariate(lambd)` is `-log(1.0 - u) / lambd` after one draw, with
`ZeroDivisionError` for a zero `lambd`. -/
def ExpovariateF64 : Prop :=
  ∀ [RandLibm] (σ : Type) (g : Gen σ F64) (lambd u : F64) (s s1 : σ), g.random s = (u, s1) →
    expovariate g lambd s =
      ((do let l ← mathLog (1.0 - u); pyDiv (-l) lambd : Py F64), s1)

theorem expovariateF64_proven : ExpovariateF64 := by
  intro _ σ g lambd u s s1 h
  simp only [expovariate, rnd_bind_apply h, lift_bind_apply]
  cases mathLog (1.0 - u) with
  | error e => rfl
  | ok l => cases pyDiv (-l) lambd <;> rfl

end PyLean.CoreLibs.Rand
