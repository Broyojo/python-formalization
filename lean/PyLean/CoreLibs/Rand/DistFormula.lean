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

theorem ex_ok_bind {α β : Type} (a : α) (f : α → Py β) : ((Except.ok a : Py α) >>= f) = f a := rfl
theorem ex_err_bind {α β : Type} (e : PyExc) (f : α → Py β) : ((Except.error e : Py α) >>= f) = .error e := rfl
theorem ex_pure {α : Type} (a : α) : (Pure.pure a : Py α) = .ok a := rfl

/-- Reduce what a `cases` on a `Py` value exposed. -/
macro "pysimp" : tactic => `(tactic| (try simp only [ex_ok_bind, ex_err_bind, ex_pure, lift_bind_apply, RM.pure_apply]))

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

/-! ### `vonmisesvariate`, Lib/random.py:625-665 -/

/-- `vonmisesvariate(mu, kappa)`: for `kappa <= 1e-6`, `TWOPI * random()` (:642-643);
otherwise `s = 0.5 / kappa`, `r = s + sqrt(1.0 + s * s)`, rounds that draw `u1`, take
`z = cos(pi * u1)`, `d = z / (r + z)`, draw `u2` and accept when
`u2 < 1.0 - d * d or u2 <= (1.0 - d) * exp(d)` (:648-655, with the short circuit), then
`q = 1.0 / r`, `f = (q + z) / (1.0 + q * z)`, a third draw `u3`, and
`(mu +- acos(f)) % TWOPI` by `u3 > 0.5` (:657-665). -/
def VonmisesF64 : Prop :=
  ∀ [RandLibm] (σ : Type) (g : Gen σ F64),
    (∀ (fuel : Nat) (mu kappa u : F64) (s s1 : σ), Flt.le kappa 1e-6 = true → g.random s = (u, s1) →
      vonmisesvariate g fuel mu kappa s = (.ok (TWOPI * u), s1)) ∧
    (∀ (r : F64) (fuel : Nat) (u1 u2 : F64) (s s1 s2 : σ), g.random s = (u1, s1) → g.random s1 = (u2, s2) →
      vonmisesLoop g r (fuel + 1) s =
        match (do let z ← mathCos (PI * u1); let d ← pyDiv z (r + z); pure (z, d) : Py (F64 × F64)) with
        | .error e => (.error e, s1)
        | .ok (z, d) =>
          match (if Flt.lt u2 (1.0 - d * d) then .ok true
                 else do let e ← mathExp d; pure (Flt.le u2 ((1.0 - d) * e)) : Py Bool) with
          | .error e => (.error e, s2)
          | .ok true => (.ok z, s2)
          | .ok false => vonmisesLoop g r fuel s2) ∧
    (∀ (fuel : Nat) (mu kappa sv root z u3 : F64) (s t t1 : σ), Flt.le kappa 1e-6 = false →
      pyDiv 0.5 kappa = .ok sv → mathSqrt (1.0 + sv * sv) = .ok root →
      vonmisesLoop g (sv + root) fuel s = (.ok z, t) → g.random t = (u3, t1) →
      vonmisesvariate g fuel mu kappa s =
        match (do let q ← pyDiv 1.0 (sv + root); pyDiv (q + z) (1.0 + q * z) : Py F64) with
        | .error e => (.error e, t)
        | .ok f => ((mathAcos f >>= fun a =>
                       if Flt.lt 0.5 u3 then pyMod (mu + a) TWOPI else pyMod (mu - a) TWOPI : Py F64), t1)) ∧
    (∀ (fuel : Nat) (mu kappa sv root : F64) (e : PyExc) (s t : σ), Flt.le kappa 1e-6 = false →
      pyDiv 0.5 kappa = .ok sv → mathSqrt (1.0 + sv * sv) = .ok root →
      vonmisesLoop g (sv + root) fuel s = (.error e, t) →
      vonmisesvariate g fuel mu kappa s = (.error e, t))

theorem vonmisesF64_proven : VonmisesF64 := by
  intro _ σ g
  refine ⟨fun fuel mu kappa u s s1 hk h => ?_, fun r fuel u1 u2 s s1 s2 h1 h2 => ?_,
    fun fuel mu kappa sv root z u3 s t t1 hk h1 h2 h3 h4 => ?_,
    fun fuel mu kappa sv root e s t hk h1 h2 h3 => ?_⟩
  · simp only [vonmisesvariate, hk, if_true, rnd_bind_apply h]; rfl
  · simp only [vonmisesLoop, rnd_bind_apply h1, lift_bind_apply]
    cases mathCos (PI * u1) with
    | error e => rfl
    | ok z =>
      pysimp
      cases pyDiv z (r + z) with
      | error e => rfl
      | ok d =>
        pysimp
        rw [rnd_bind_apply h2]
        simp only [lift_bind_apply]
        unfold vonmisesAccept
        by_cases hc : Flt.lt u2 (1.0 - d * d) = true
        · simp only [hc, if_true]; rfl
        · simp only [hc, Bool.false_eq_true, if_false]
          cases mathExp d with
          | error e => rfl
          | ok ex =>
            pysimp
            cases Flt.le u2 ((1.0 - d) * ex) <;> rfl
  · simp only [vonmisesvariate, hk, Bool.false_eq_true, if_false, lift_bind_apply, h1, h2]
    rw [RM.bind_apply, h3]
    dsimp only
    simp only [lift_bind_apply]
    cases pyDiv 1.0 (sv + root) with
    | error e => rfl
    | ok q =>
      pysimp
      cases pyDiv (q + z) (1.0 + q * z) with
      | error e => rfl
      | ok f =>
        dsimp only
        rw [rnd_bind_apply h4]
        simp only [lift_bind_apply]
        cases mathAcos f with
        | error e => rfl
        | ok a =>
          pysimp
          by_cases hc : Flt.lt 0.5 u3 = true
          · simp only [hc, if_true, RM.lift_apply]
          · simp only [hc, Bool.false_eq_true, if_false, RM.lift_apply]
  · simp only [vonmisesvariate, hk, Bool.false_eq_true, if_false, lift_bind_apply, h1, h2]
    rw [RM.bind_apply, h3]

/-! ### `gammavariate`, Lib/random.py:667-734 -/

/-- `gammavariate(alpha, beta)`: the `ValueError` before any draw when `alpha <= 0.0` or
`beta <= 0.0` (:687-688); for `alpha == 1.0`, `-log(1.0 - random()) * beta` (:713-716); for
`alpha > 1.0`, `beta` times the result of Cheng's loop with `ainv = sqrt(2.0 * alpha - 1.0)`,
`bbb = alpha - LOG4`, `ccc = alpha + ainv` (:690-711); otherwise `beta` times the result of
the GS loop (:718-734). The rounds of both loops are pinned in `GammaLoopsF64`. -/
def GammaF64 : Prop :=
  ∀ [RandLibm] (σ : Type) (g : Gen σ F64),
    (∀ (fuel : Nat) (alpha beta : F64) (s : σ), (Flt.le alpha 0.0 || Flt.le beta 0.0) = true →
      gammavariate g fuel alpha beta s = (.error (.valueError "gammavariate: alpha and beta must be > 0.0"), s)) ∧
    (∀ (fuel : Nat) (beta u : F64) (s s1 : σ), Flt.le beta 0.0 = false → g.random s = (u, s1) →
      gammavariate g fuel 1.0 beta s = ((do let l ← mathLog (1.0 - u); pure (-l * beta) : Py F64), s1)) ∧
    (∀ (fuel : Nat) (alpha beta ainv : F64) (s : σ), (Flt.le alpha 0.0 || Flt.le beta 0.0) = false →
      Flt.lt 1.0 alpha = true → mathSqrt (2.0 * alpha - 1.0) = .ok ainv →
      gammavariate g fuel alpha beta s =
        match gammaCheng g alpha ainv (alpha - LOG4) (alpha + ainv) fuel s with
        | (.ok x, t) => (.ok (x * beta), t)
        | (.error e, t) => (.error e, t)) ∧
    (∀ (fuel : Nat) (alpha beta : F64) (s : σ), (Flt.le alpha 0.0 || Flt.le beta 0.0) = false →
      Flt.lt 1.0 alpha = false → Flt.beq alpha 1.0 = false →
      gammavariate g fuel alpha beta s =
        match gammaGS g alpha fuel s with
        | (.ok x, t) => (.ok (x * beta), t)
        | (.error e, t) => (.error e, t))

theorem one_facts [RandLibm] : Flt.le (1.0 : F64) 0.0 = false ∧ Flt.lt (1.0 : F64) 1.0 = false ∧
    Flt.beq (1.0 : F64) 1.0 = true := by
  show F64.le (F64R.ofDecimal 10 true 1) (F64R.ofDecimal 0 true 1) = false ∧
    F64.lt (F64R.ofDecimal 10 true 1) (F64R.ofDecimal 10 true 1) = false ∧
    F64.eq (F64R.ofDecimal 10 true 1) (F64R.ofDecimal 10 true 1) = true
  decide +kernel

theorem gammaF64_proven : GammaF64 := by
  intro _ σ g
  obtain ⟨o1, o2, o3⟩ := one_facts
  refine ⟨fun fuel alpha beta s h => ?_, fun fuel beta u s s1 hb h => ?_,
    fun fuel alpha beta ainv s h0 h1 h2 => ?_, fun fuel alpha beta s h0 h1 h2 => ?_⟩
  · simp only [gammavariate, h, if_true]; rfl
  · simp only [gammavariate, o1, hb, Bool.or_self, Bool.false_eq_true, if_false, o2, o3, if_true,
      rnd_bind_apply h, lift_bind_apply]
    cases mathLog (1.0 - u) <;> rfl
  · simp only [gammavariate, h0, h1, Bool.false_eq_true, if_false, if_true, lift_bind_apply, h2]
    rw [RM.bind_apply]
    cases gammaCheng g alpha ainv (alpha - LOG4) (alpha + ainv) fuel s with
    | mk r t => cases r <;> rfl
  · simp only [gammavariate, h0, h1, h2, Bool.false_eq_true, if_false]
    rw [RM.bind_apply]
    cases gammaGS g alpha fuel s with
    | mk r t => cases r <;> rfl

/-- One round of each `gammavariate` loop. Cheng's (:701-711): draw `u1`; outside
`1e-7 < u1 < .9999999` start again after that one draw; else draw `r2`, `u2 = 1.0 - r2`,
`v = log(u1 / (1.0 - u1)) / ainv`, `x = alpha * exp(v)`, `z = u1 * u1 * u2`,
`r = bbb + ccc * v - x`, and accept `x` when `r + SG_MAGICCONST - 4.5 * z >= 0.0` or
`r >= log(z)`. GS (:720-733): draw `u`, `b = (_e + alpha) / _e`, `p = b * u`,
`x = p ** (1.0 / alpha)` for `p <= 1.0` and `-log((b - p) / alpha)` otherwise, draw `u1`,
and accept when `u1 <= x ** (alpha - 1.0)` (for `p > 1.0`) or `u1 <= exp(-x)`. -/
def GammaLoopsF64 : Prop :=
  ∀ [RandLibm] (σ : Type) (g : Gen σ F64),
    (∀ (alpha ainv bbb ccc : F64) (fuel : Nat) (u1 r2 : F64) (s s1 s2 : σ),
      g.random s = (u1, s1) → g.random s1 = (r2, s2) →
      gammaCheng g alpha ainv bbb ccc (fuel + 1) s =
        if !(Flt.lt 1e-7 u1 && Flt.lt u1 0.9999999) then gammaCheng g alpha ainv bbb ccc fuel s1
        else match (do
            let q ← pyDiv u1 (1.0 - u1)
            let l ← mathLog q
            let v ← pyDiv l ainv
            let ev ← mathExp v
            let x := alpha * ev
            let z := u1 * u1 * (1.0 - r2)
            let r := bbb + ccc * v - x
            if Flt.le 0.0 (r + SG_MAGICCONST - 4.5 * z) then pure (some x)
            else do
              let lz ← mathLog z
              pure (if Flt.le lz r then some x else none) : Py (Option F64)) with
          | .ok (some x) => (.ok x, s2)
          | .ok none => gammaCheng g alpha ainv bbb ccc fuel s2
          | .error e => (.error e, s2)) ∧
    (∀ (alpha : F64) (fuel : Nat) (u u1 : F64) (s s1 s2 : σ),
      g.random s = (u, s1) → g.random s1 = (u1, s2) →
      gammaGS g alpha (fuel + 1) s =
        match gammaGSx alpha ((E + alpha) / E) ((E + alpha) / E * u) with
        | .error e => (.error e, s1)
        | .ok x =>
          match (if Flt.lt 1.0 ((E + alpha) / E * u) then pyPow x (alpha - 1.0) else mathExp (-x)) with
          | .error e => (.error e, s2)
          | .ok w => if Flt.le u1 w then (.ok x, s2) else gammaGS g alpha fuel s2) ∧
    (∀ (alpha b p : F64), gammaGSx alpha b p =
      if Flt.le p 1.0 then (do let e ← pyDiv 1.0 alpha; pyPow p e)
      else (do let q ← pyDiv (b - p) alpha; let l ← mathLog q; pure (-l)))

theorem gammaLoopsF64_proven : GammaLoopsF64 := by
  intro _ σ g
  refine ⟨fun alpha ainv bbb ccc fuel u1 r2 s s1 s2 h1 h2 => ?_,
    fun alpha fuel u u1 s s1 s2 h1 h2 => ?_, fun _ _ _ => rfl⟩
  · simp only [gammaCheng, rnd_bind_apply h1]
    by_cases hc : (!(Flt.lt 1e-7 u1 && Flt.lt u1 0.9999999)) = true
    · simp only [hc, if_true]
    · simp only [hc, Bool.false_eq_true, if_false, rnd_bind_apply h2, lift_bind_apply]
      cases pyDiv u1 (1.0 - u1) with
      | error e => rfl
      | ok q =>
        pysimp
        cases mathLog q with
        | error e => rfl
        | ok l =>
          pysimp
          cases pyDiv l ainv with
          | error e => rfl
          | ok v =>
            pysimp
            cases mathExp v with
            | error e => rfl
            | ok ev =>
              pysimp
              by_cases ha : Flt.le 0.0 (bbb + ccc * v - alpha * ev + SG_MAGICCONST -
                  4.5 * (u1 * u1 * (1.0 - r2))) = true
              · simp only [ha, if_true]; rfl
              · simp only [ha, Bool.false_eq_true, if_false, lift_bind_apply]
                cases mathLog (u1 * u1 * (1.0 - r2)) with
                | error e => rfl
                | ok lz =>
                  pysimp
                  by_cases hb : Flt.le lz (bbb + ccc * v - alpha * ev) = true
                  · simp only [hb, if_true]; rfl
                  · simp only [hb, Bool.false_eq_true, if_false]
  · simp only [gammaGS, rnd_bind_apply h1, lift_bind_apply]
    cases gammaGSx alpha ((E + alpha) / E) ((E + alpha) / E * u) with
    | error e => rfl
    | ok x =>
      dsimp only
      rw [rnd_bind_apply h2]
      by_cases hp : Flt.lt 1.0 ((E + alpha) / E * u) = true
      · simp only [hp, if_true, lift_bind_apply]
        cases pyPow x (alpha - 1.0) with
        | error e => rfl
        | ok w => by_cases hw : Flt.le u1 w = true <;> simp [hw] <;> rfl
      · simp only [hp, Bool.false_eq_true, if_false, lift_bind_apply]
        cases mathExp (-x) with
        | error e => rfl
        | ok w => by_cases hw : Flt.le u1 w = true <;> simp [hw] <;> rfl

/-! ### `betavariate`, `paretovariate`, `weibullvariate`, Lib/random.py:736-784 -/

/-- `betavariate(alpha, beta)` is `y / (y + gammavariate(beta, 1.0))` with
`y = gammavariate(alpha, 1.0)` drawn first, and `0.0` without the second call when `y`
is zero (:762-766); `paretovariate(alpha)` is `(1.0 - random()) ** (-1.0 / alpha)`
(:771-773); `weibullvariate(alpha, beta)` is
`alpha * (-log(1.0 - random())) ** (1.0 / beta)` (:782-784). -/
def BetaParetoWeibullF64 : Prop :=
  ∀ [RandLibm] (σ : Type) (g : Gen σ F64),
    (∀ (fuel : Nat) (alpha beta : F64) (s : σ),
      betavariate g fuel alpha beta s =
        match gammavariate g fuel alpha 1.0 s with
        | (.error e, t) => (.error e, t)
        | (.ok y, t) =>
          if truthy y then
            match gammavariate g fuel beta 1.0 t with
            | (.ok w, t') => (pyDiv y (y + w), t')
            | (.error e, t') => (.error e, t')
          else (.ok 0.0, t)) ∧
    (∀ (alpha u : F64) (s s1 : σ), g.random s = (u, s1) →
      paretovariate g alpha s = ((do let e ← pyDiv (-1.0) alpha; pyPow (1.0 - u) e : Py F64), s1)) ∧
    (∀ (alpha beta u : F64) (s s1 : σ), g.random s = (u, s1) →
      weibullvariate g alpha beta s =
        ((do let l ← mathLog (1.0 - u); let e ← pyDiv 1.0 beta; let w ← pyPow (-l) e
             pure (alpha * w) : Py F64), s1))

theorem betaParetoWeibullF64_proven : BetaParetoWeibullF64 := by
  intro _ σ g
  refine ⟨fun fuel alpha beta s => ?_, fun alpha u s s1 h => ?_, fun alpha beta u s s1 h => ?_⟩
  · simp only [betavariate, RM.bind_apply]
    cases gammavariate g fuel alpha 1.0 s with
    | mk r t =>
      cases r with
      | error e => rfl
      | ok y =>
        dsimp only
        by_cases hy : truthy y = true
        · simp only [hy, if_true, RM.bind_apply]
          cases gammavariate g fuel beta 1.0 t with
          | mk r' t' => cases r' <;> rfl
        · simp only [hy, Bool.false_eq_true, if_false]; rfl
  · simp only [paretovariate, rnd_bind_apply h, lift_bind_apply]
    cases pyDiv (-1.0) alpha with
    | error e => rfl
    | ok e => cases pyPow (1.0 - u) e <;> rfl
  · simp only [weibullvariate, rnd_bind_apply h, lift_bind_apply]
    cases mathLog (1.0 - u) with
    | error e => rfl
    | ok l =>
      pysimp
      cases pyDiv 1.0 beta with
      | error e => rfl
      | ok e =>
        pysimp
        cases pyPow (-l) e <;> rfl

end PyLean.CoreLibs.Rand
