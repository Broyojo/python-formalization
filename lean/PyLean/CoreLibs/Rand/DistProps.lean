import PyLean.CoreLibs.Rand.ExactProps
import PyLean.CoreLibs.Rand.Dist

/-!
Properties of the distributions, `Lib/random.py:500-890`.

These methods "only access randomness through the methods: random(), getrandbits(),
or _randbelow()" (Lib/random.py:280-282), and the real-valued ones only through
`random()`. `Draws g x P` says: whenever `x` returns, the generator has moved by a
whole number `d` of `random()` calls with `P d`. That is the exact part of each
distribution, stated for every core generator and every float type.

Values are not stated here: Lean cannot compute with `Float`. They are compared with
CPython bit for bit by the difftest, and stay `.open` until the Binary64 model is
available.
-/

namespace PyLean.CoreLibs.Rand

open PyLean RM Flt

variable {σ F α β : Type}

/-- The state after `d` calls of `random()`. -/
def iterDraw (g : Gen σ F) : Nat → σ → σ
  | 0, s => s
  | n + 1, s => iterDraw g n (g.random s).2

theorem iterDraw_add (g : Gen σ F) : ∀ (a b : Nat) (s : σ),
    iterDraw g (a + b) s = iterDraw g b (iterDraw g a s)
  | 0, b, s => by simp [iterDraw]
  | a + 1, b, s => by
    have : a + 1 + b = (a + b) + 1 := by omega
    rw [this]
    simp only [iterDraw]
    exact iterDraw_add g a b _

/-- If `x` returns, the generator moved by `d` calls of `random()` with `P d`. -/
def Draws (g : Gen σ F) (x : RM σ α) (P : Nat → Prop) : Prop :=
  ∀ s a s', x s = (.ok a, s') → ∃ d, P d ∧ s' = iterDraw g d s

theorem Draws.pure (g : Gen σ F) {a : α} {P : Nat → Prop} (h : P 0) :
    Draws g (Pure.pure a : RM σ α) P := by
  intro s b s' e
  simp only [RM.pure_apply, Prod.mk.injEq] at e
  exact ⟨0, h, e.2.symm⟩

theorem Draws.lift (g : Gen σ F) (x : Py α) {P : Nat → Prop} (h : P 0) :
    Draws g (RM.lift x : RM σ α) P := by
  intro s b s' e
  simp only [RM.lift_apply, Prod.mk.injEq] at e
  exact ⟨0, h, e.2.symm⟩

theorem Draws.raise (g : Gen σ F) (e : PyExc) {P : Nat → Prop} : Draws g (RM.raise e : RM σ α) P := by
  intro s b s' h
  simp at h

theorem Draws.rnd (g : Gen σ F) {P : Nat → Prop} (h : P 1) : Draws g (Rand.rnd g) P := by
  intro s b s' e
  simp only [Rand.rnd, Prod.mk.injEq] at e
  exact ⟨1, h, e.2.symm⟩

theorem Draws.bind {g : Gen σ F} {x : RM σ α} {f : α → RM σ β} {Q R P : Nat → Prop}
    (hx : Draws g x Q) (hf : ∀ a, Draws g (f a) R) (h : ∀ a b, Q a → R b → P (a + b)) :
    Draws g (x >>= f) P := by
  intro s b s' e
  simp only [RM.bind_apply] at e
  cases hxs : x s with
  | mk r t =>
    rw [hxs] at e
    cases r with
    | error err => cases e
    | ok a =>
      obtain ⟨d1, h1, h2⟩ := hx s a t hxs
      obtain ⟨d2, h3, h4⟩ := hf a t b s' e
      exact ⟨d1 + d2, h d1 d2 h1 h3, by rw [iterDraw_add, ← h2, h4]⟩

theorem Draws.mono {g : Gen σ F} {x : RM σ α} {P Q : Nat → Prop} (hx : Draws g x P)
    (h : ∀ d, P d → Q d) : Draws g x Q := by
  intro s a s' e
  obtain ⟨d, h1, h2⟩ := hx s a s' e
  exact ⟨d, h _ h1, h2⟩

/-- Arithmetic side goal of `Draws.bind`. -/
macro "dr" : tactic =>
  `(tactic| (intro a b h1 h2; (try dsimp only at h1 h2 ⊢); omega))

/-- Sequencing with exact counts. -/
theorem Draws.seq {g : Gen σ F} {x : RM σ α} {f : α → RM σ β} {a b : Nat}
    (hx : Draws g x (· = a)) (hf : ∀ v, Draws g (f v) (· = b)) :
    Draws g (x >>= f) (· = a + b) :=
  Draws.bind hx hf (by intro p q h1 h2; (try dsimp only at h1 h2 ⊢); omega)

/-! ### Exactly one draw -/

variable [Flt F]

theorem uniform_draws (g : Gen σ F) (a b : F) : Draws g (uniform g a b) (· = 1) :=
  Draws.seq (Draws.rnd g rfl) (fun _ => Draws.pure g rfl)

theorem triangular_draws (g : Gen σ F) (low high : F) (mode : Option F) :
    Draws g (triangular g low high mode) (· = 1) := by
  unfold triangular
  refine Draws.seq (a := 1) (b := 0) (Draws.rnd g rfl) (fun u => ?_)
  dsimp only
  split
  · exact Draws.pure g rfl
  · split <;>
    exact Draws.seq (a := 0) (b := 0) (Draws.lift g _ rfl) (fun _ => Draws.pure g rfl)

theorem expovariate_draws (g : Gen σ F) (lambd : F) : Draws g (expovariate g lambd) (· = 1) :=
  Draws.seq (a := 1) (b := 0) (Draws.rnd g rfl) (fun _ =>
    Draws.seq (a := 0) (b := 0) (Draws.lift g _ rfl) (fun _ => Draws.lift g _ rfl))

theorem paretovariate_draws (g : Gen σ F) (alpha : F) : Draws g (paretovariate g alpha) (· = 1) :=
  Draws.seq (a := 1) (b := 0) (Draws.rnd g rfl) (fun _ =>
    Draws.seq (a := 0) (b := 0) (Draws.lift g _ rfl) (fun _ => Draws.lift g _ rfl))

theorem weibullvariate_draws (g : Gen σ F) (alpha beta : F) :
    Draws g (weibullvariate g alpha beta) (· = 1) :=
  Draws.seq (a := 1) (b := 0) (Draws.rnd g rfl) (fun _ =>
    Draws.seq (a := 0) (b := 0) (Draws.lift g _ rfl) (fun _ =>
      Draws.seq (a := 0) (b := 0) (Draws.lift g _ rfl) (fun _ =>
        Draws.seq (a := 0) (b := 0) (Draws.lift g _ rfl) (fun _ => Draws.pure g rfl))))

/-- `uniform`, `triangular`, `expovariate`, `paretovariate` and `weibullvariate` use
exactly one `random()`, on every path that returns, including the
`ZeroDivisionError` path of `triangular`. -/
def OneDraw : Prop :=
  ∀ (σ F : Type) [Flt F] (g : Gen σ F) (a b : F) (m : Option F),
    Draws g (uniform g a b) (· = 1) ∧ Draws g (triangular g a b m) (· = 1) ∧
    Draws g (expovariate g a) (· = 1) ∧ Draws g (paretovariate g a) (· = 1) ∧
    Draws g (weibullvariate g a b) (· = 1)

theorem oneDraw_proven : OneDraw := fun _ _ _ g a b m =>
  ⟨uniform_draws g a b, triangular_draws g a b m, expovariate_draws g a, paretovariate_draws g a,
   weibullvariate_draws g a b⟩

/-- `gauss` makes two `random()` calls every other time: with `gauss_next` empty it
draws twice and stores the second normal, and with it full it draws nothing, returns
the stored value and empties it. -/
def GaussDraws : Prop :=
  ∀ (σ F : Type) [Flt F] (g : Gen σ F) (mu sigma z : F),
    Draws g (gauss g mu sigma none) (· = 2) ∧
    Draws g (gauss g mu sigma (some z)) (· = 0) ∧
    Post (gauss g mu sigma none) (fun r => r.2.isSome) ∧
    Post (gauss g mu sigma (some z)) (fun r => r.2 = none)

theorem gaussDraws_proven : GaussDraws := by
  intro σ F _ g mu sigma z
  refine ⟨?_, Draws.pure g rfl, ?_, Post.pure rfl⟩
  · unfold gauss
    refine Draws.seq (a := 1) (b := 1) (Draws.rnd g rfl) (fun r1 => ?_)
    refine Draws.seq (a := 1) (b := 0) (Draws.rnd g rfl) (fun r2 => ?_)
    refine Draws.seq (a := 0) (b := 0) (Draws.lift g _ rfl) (fun _ => ?_)
    refine Draws.seq (a := 0) (b := 0) (Draws.lift g _ rfl) (fun _ => ?_)
    refine Draws.seq (a := 0) (b := 0) (Draws.lift g _ rfl) (fun _ => ?_)
    refine Draws.seq (a := 0) (b := 0) (Draws.lift g _ rfl) (fun _ => ?_)
    exact Draws.pure g rfl
  · unfold gauss
    refine Post.bind (Post.any _) (fun _ _ => ?_)
    refine Post.bind (Post.any _) (fun _ _ => ?_)
    refine Post.bind (Post.any _) (fun _ _ => ?_)
    refine Post.bind (Post.any _) (fun _ _ => ?_)
    refine Post.bind (Post.any _) (fun _ _ => ?_)
    refine Post.bind (Post.any _) (fun _ _ => ?_)
    exact Post.pure rfl

/-! ### Rejection loops -/

theorem normalLoop_draws (g : Gen σ F) : ∀ fuel,
    Draws g (normalLoop g fuel) (fun d => d % 2 = 0 ∧ 2 ≤ d)
  | 0 => Draws.raise g _
  | fuel + 1 => by
    simp only [normalLoop]
    refine Draws.bind (Q := (· = 1)) (R := fun d => d % 2 = 1 ∧ 1 ≤ d) (Draws.rnd g rfl)
      (fun u1 => ?_) (by dr)
    refine Draws.bind (Q := (· = 1)) (R := fun d => d % 2 = 0) (Draws.rnd g rfl)
      (fun r2 => ?_) (by dr)
    refine Draws.bind (Q := (· = 0)) (R := fun d => d % 2 = 0) (Draws.lift g _ rfl)
      (fun _ => ?_) (by dr)
    refine Draws.bind (Q := (· = 0)) (R := fun d => d % 2 = 0) (Draws.lift g _ rfl)
      (fun _ => ?_) (by dr)
    split
    · exact Draws.pure g rfl
    · exact Draws.mono (normalLoop_draws g fuel) (by intro d h; exact h.1)

theorem normalvariate_draws (g : Gen σ F) (fuel : Nat) (mu sigma : F) :
    Draws g (normalvariate g fuel mu sigma) (fun d => d % 2 = 0 ∧ 2 ≤ d) :=
  Draws.bind (Q := fun d => d % 2 = 0 ∧ 2 ≤ d) (R := (· = 0)) (normalLoop_draws g fuel)
    (fun _ => Draws.pure g rfl) (by dr)

theorem lognormvariate_draws (g : Gen σ F) (fuel : Nat) (mu sigma : F) :
    Draws g (lognormvariate g fuel mu sigma) (fun d => d % 2 = 0 ∧ 2 ≤ d) :=
  Draws.bind (Q := fun d => d % 2 = 0 ∧ 2 ≤ d) (R := (· = 0)) (normalvariate_draws g fuel mu sigma)
    (fun _ => Draws.lift g _ rfl) (by dr)

theorem vonmisesLoop_draws (g : Gen σ F) (r : F) : ∀ fuel,
    Draws g (vonmisesLoop g r fuel) (fun d => d % 2 = 0 ∧ 2 ≤ d)
  | 0 => Draws.raise g _
  | fuel + 1 => by
    simp only [vonmisesLoop]
    refine Draws.bind (Q := (· = 1)) (R := fun d => d % 2 = 1 ∧ 1 ≤ d) (Draws.rnd g rfl)
      (fun u1 => ?_) (by dr)
    refine Draws.bind (Q := (· = 0)) (R := fun d => d % 2 = 1 ∧ 1 ≤ d) (Draws.lift g _ rfl)
      (fun _ => ?_) (by dr)
    refine Draws.bind (Q := (· = 0)) (R := fun d => d % 2 = 1 ∧ 1 ≤ d) (Draws.lift g _ rfl)
      (fun _ => ?_) (by dr)
    refine Draws.bind (Q := (· = 1)) (R := fun d => d % 2 = 0) (Draws.rnd g rfl)
      (fun u2 => ?_) (by dr)
    refine Draws.bind (Q := (· = 0)) (R := fun d => d % 2 = 0) (Draws.lift g _ rfl)
      (fun accept => ?_) (by dr)
    split
    · exact Draws.pure g rfl
    · exact Draws.mono (vonmisesLoop_draws g r fuel) (by intro d h; exact h.1)

theorem vonmisesvariate_draws (g : Gen σ F) (fuel : Nat) (mu kappa : F) :
    Draws g (vonmisesvariate g fuel mu kappa)
      (fun d => if Flt.le kappa 1e-6 then d = 1 else d % 2 = 1 ∧ 3 ≤ d) := by
  unfold vonmisesvariate
  split
  · rename_i h
    refine Draws.mono (P := (· = 1)) ?_ (fun d hd => by
      try dsimp only
      try rw [if_pos h]
      exact hd)
    exact Draws.seq (a := 1) (b := 0) (Draws.rnd g rfl) (fun _ => Draws.pure g rfl)
  · rename_i h
    refine Draws.mono (P := fun d => d % 2 = 1 ∧ 3 ≤ d) ?_ (fun d hd => by
      try dsimp only
      try rw [if_neg h]
      exact hd)
    refine Draws.bind (Q := (· = 0)) (R := fun d => d % 2 = 1 ∧ 3 ≤ d) (Draws.lift g _ rfl)
      (fun _ => ?_) (by dr)
    refine Draws.bind (Q := (· = 0)) (R := fun d => d % 2 = 1 ∧ 3 ≤ d) (Draws.lift g _ rfl)
      (fun _ => ?_) (by dr)
    refine Draws.bind (Q := fun d => d % 2 = 0 ∧ 2 ≤ d) (R := (· = 1)) (vonmisesLoop_draws g _ fuel)
      (fun _ => ?_) (by dr)
    refine Draws.seq (a := 0) (b := 1) (Draws.lift g _ rfl) (fun _ => ?_)
    refine Draws.seq (a := 0) (b := 1) (Draws.lift g _ rfl) (fun _ => ?_)
    refine Draws.seq (a := 1) (b := 0) (Draws.rnd g rfl) (fun _ => ?_)
    refine Draws.seq (a := 0) (b := 0) (Draws.lift g _ rfl) (fun _ => ?_)
    split <;> exact Draws.lift g _ rfl

theorem gammaCheng_draws (g : Gen σ F) (alpha ainv bbb ccc : F) : ∀ fuel,
    Draws g (gammaCheng g alpha ainv bbb ccc fuel) (fun d => 2 ≤ d)
  | 0 => Draws.raise g _
  | fuel + 1 => by
    simp only [gammaCheng]
    refine Draws.bind (Q := (· = 1)) (R := fun d => 1 ≤ d) (Draws.rnd g rfl)
      (fun u1 => ?_) (by dr)
    split
    · exact Draws.mono (gammaCheng_draws g alpha ainv bbb ccc fuel) (by intro d h; omega)
    · refine Draws.bind (Q := (· = 1)) (R := fun _ => True) (Draws.rnd g rfl)
        (fun r2 => ?_) (by dr)
      refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
        (fun _ => ?_) (by intro a b h1 h2; trivial)
      refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
        (fun _ => ?_) (by intro a b h1 h2; trivial)
      refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
        (fun _ => ?_) (by intro a b h1 h2; trivial)
      refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
        (fun _ => ?_) (by intro a b h1 h2; trivial)
      split
      · exact Draws.pure g trivial
      · refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
          (fun _ => ?_) (by intro a b h1 h2; trivial)
        split
        · exact Draws.pure g trivial
        · exact Draws.mono (gammaCheng_draws g alpha ainv bbb ccc fuel) (by intro _ _; trivial)

theorem gammaGS_draws (g : Gen σ F) (alpha : F) : ∀ fuel,
    Draws g (gammaGS g alpha fuel) (fun d => d % 2 = 0 ∧ 2 ≤ d)
  | 0 => Draws.raise g _
  | fuel + 1 => by
    simp only [gammaGS]
    refine Draws.bind (Q := (· = 1)) (R := fun d => d % 2 = 1 ∧ 1 ≤ d) (Draws.rnd g rfl)
      (fun u => ?_) (by dr)
    refine Draws.bind (Q := (· = 0)) (R := fun d => d % 2 = 1 ∧ 1 ≤ d) (Draws.lift g _ rfl)
      (fun x => ?_) (by dr)
    refine Draws.bind (Q := (· = 1)) (R := fun d => d % 2 = 0) (Draws.rnd g rfl)
      (fun u1 => ?_) (by dr)
    split
    · refine Draws.bind (Q := (· = 0)) (R := fun d => d % 2 = 0) (Draws.lift g _ rfl)
        (fun _ => ?_) (by dr)
      split
      · exact Draws.pure g rfl
      · exact Draws.mono (gammaGS_draws g alpha fuel) (by intro d h; exact h.1)
    · refine Draws.bind (Q := (· = 0)) (R := fun d => d % 2 = 0) (Draws.lift g _ rfl)
        (fun _ => ?_) (by dr)
      split
      · exact Draws.pure g rfl
      · exact Draws.mono (gammaGS_draws g alpha fuel) (by intro d h; exact h.1)

/-- The draw count of `gammavariate` for each branch of `alpha`. -/
def gammaDrawCount (alpha : F) (d : Nat) : Prop :=
  if Flt.lt 1.0 alpha then 2 ≤ d
  else if Flt.beq alpha 1.0 then d = 1
  else d % 2 = 0 ∧ 2 ≤ d

theorem gammavariate_draws (g : Gen σ F) (fuel : Nat) (alpha beta : F) :
    Draws g (gammavariate g fuel alpha beta) (gammaDrawCount alpha) := by
  unfold gammavariate
  split
  · exact Draws.raise g _
  · split
    · rename_i h1
      refine Draws.mono (P := fun d => 2 ≤ d) ?_ (fun d hd => by
        unfold gammaDrawCount
        rw [if_pos h1]
        exact hd)
      refine Draws.bind (Q := (· = 0)) (R := fun d => 2 ≤ d) (Draws.lift g _ rfl)
        (fun _ => ?_) (by dr)
      exact Draws.bind (Q := fun d => 2 ≤ d) (R := (· = 0)) (gammaCheng_draws g _ _ _ _ fuel)
        (fun _ => Draws.pure g rfl) (by dr)
    · rename_i h1
      split
      · rename_i h2
        refine Draws.mono (P := (· = 1)) ?_ (fun d hd => by
          unfold gammaDrawCount
          rw [if_neg h1, if_pos h2]
          exact hd)
        exact Draws.seq (a := 1) (b := 0) (Draws.rnd g rfl) (fun _ =>
          Draws.seq (a := 0) (b := 0) (Draws.lift g _ rfl) (fun _ => Draws.pure g rfl))
      · rename_i h2
        refine Draws.mono (P := fun d => d % 2 = 0 ∧ 2 ≤ d) ?_ (fun d hd => by
          unfold gammaDrawCount
          rw [if_neg h1, if_neg h2]
          exact hd)
        exact Draws.bind (Q := fun d => d % 2 = 0 ∧ 2 ≤ d) (R := (· = 0)) (gammaGS_draws g _ fuel)
          (fun _ => Draws.pure g rfl) (by dr)

/-- `betavariate` is one `gammavariate(alpha, 1.0)` and, unless that returned `0.0`,
one `gammavariate(beta, 1.0)`. -/
theorem betavariate_draws (g : Gen σ F) (fuel : Nat) (alpha beta : F) :
    Draws g (betavariate g fuel alpha beta) (fun d => 1 ≤ d) := by
  have hg : ∀ a b : F, Draws g (gammavariate g fuel a b) (fun d => 1 ≤ d) := by
    intro a b
    refine Draws.mono (gammavariate_draws g fuel a b) ?_
    intro d h
    unfold gammaDrawCount at h
    split at h
    · omega
    · split at h <;> omega
  unfold betavariate
  refine Draws.bind (Q := fun d => 1 ≤ d) (R := fun _ => True) (hg _ _) (fun y => ?_)
    (by dr)
  split
  · exact Draws.bind (Q := fun _ => True) (R := (· = 0))
      (Draws.mono (hg _ _) (by intro _ _; trivial)) (fun _ => Draws.lift g _ rfl)
      (by intro a b h1 h2; trivial)
  · exact Draws.pure g trivial

/-- The rejection samplers use a whole number of `random()` calls with the shape the
source fixes: `normalvariate` and `lognormvariate` draw in pairs; `vonmisesvariate`
draws once for `kappa <= 1e-6`, else pairs and a final one; `gammavariate` draws once
for `alpha == 1.0`, pairs for `alpha < 1.0`, and at least two for `alpha > 1.0`;
`betavariate` at least once. -/
def RejectionDraws : Prop :=
  ∀ (σ F : Type) [Flt F] (g : Gen σ F) (fuel : Nat) (a b : F),
    Draws g (normalvariate g fuel a b) (fun d => d % 2 = 0 ∧ 2 ≤ d) ∧
    Draws g (lognormvariate g fuel a b) (fun d => d % 2 = 0 ∧ 2 ≤ d) ∧
    Draws g (vonmisesvariate g fuel a b)
      (fun d => if Flt.le b 1e-6 then d = 1 else d % 2 = 1 ∧ 3 ≤ d) ∧
    Draws g (gammavariate g fuel a b) (gammaDrawCount a) ∧
    Draws g (betavariate g fuel a b) (fun d => 1 ≤ d)

theorem rejectionDraws_proven : RejectionDraws := fun _ _ _ g fuel a b =>
  ⟨normalvariate_draws g fuel a b, lognormvariate_draws g fuel a b,
   vonmisesvariate_draws g fuel a b, gammavariate_draws g fuel a b, betavariate_draws g fuel a b⟩

/-- `gammavariate` checks its parameters first: `alpha <= 0` or `beta <= 0` raises
`ValueError` before any draw, and so does `betavariate` when `alpha <= 0`. -/
def GammaChecksFirst : Prop :=
  ∀ (σ F : Type) [Flt F] (g : Gen σ F) (fuel : Nat) (alpha beta : F) (s : σ),
    (Flt.le alpha 0.0 = true ∨ Flt.le beta 0.0 = true) →
      gammavariate g fuel alpha beta s =
        (.error (.valueError "gammavariate: alpha and beta must be > 0.0"), s)

theorem gammaChecksFirst_proven : GammaChecksFirst := by
  intro σ F _ g fuel alpha beta s h
  unfold gammavariate
  have : (Flt.le alpha 0.0 || Flt.le beta 0.0) = true := by
    rcases h with h | h <;> simp [h]
  simp only [this, if_true]
  rfl

theorem binomBG_draws (g : Gen σ F) (n : Int) (c : F) : ∀ (fuel : Nat) (x y : Int),
    Draws g (binomBG g n c fuel x y) (fun d => 1 ≤ d)
  | 0, _, _ => Draws.raise g _
  | fuel + 1, x, y => by
    simp only [binomBG]
    refine Draws.bind (Q := (· = 1)) (R := fun _ => True) (Draws.rnd g rfl)
      (fun r => ?_) (by dr)
    split
    · exact Draws.mono (binomBG_draws g n c fuel x y) (by intro _ _; trivial)
    · exact Draws.raise g _
    · split
      · exact Draws.pure g trivial
      · exact Draws.mono (binomBG_draws g n c fuel _ _) (by intro _ _; trivial)

theorem btrsLoop_draws (g : Gen σ F) (n : Int) (p spq a b c vr : F) : ∀ (fuel : Nat)
    (setup : Option (BtrsSetup F)),
    Draws g (btrsLoop g n p spq a b c vr fuel setup) (fun d => 1 ≤ d)
  | 0, _ => Draws.raise g _
  | fuel + 1, setup => by
    simp only [btrsLoop]
    refine Draws.bind (Q := (· = 1)) (R := fun _ => True) (Draws.rnd g rfl)
      (fun u0 => ?_) (by dr)
    split
    · exact Draws.mono (btrsLoop_draws g n p spq a b c vr fuel setup) (by intro _ _; trivial)
    · exact Draws.raise g _
    · split
      · exact Draws.mono (btrsLoop_draws g n p spq a b c vr fuel setup) (by intro _ _; trivial)
      · refine Draws.bind (Q := (· = 1)) (R := fun _ => True) (Draws.rnd g rfl)
          (fun v => ?_) (by intro a b h1 h2; trivial)
        split
        · exact Draws.pure g trivial
        · refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
            (fun st => ?_) (by intro _ _ _ _; trivial)
          refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
            (fun _ => ?_) (by intro _ _ _ _; trivial)
          refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
            (fun _ => ?_) (by intro _ _ _ _; trivial)
          refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
            (fun _ => ?_) (by intro _ _ _ _; trivial)
          refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
            (fun _ => ?_) (by intro _ _ _ _; trivial)
          refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
            (fun _ => ?_) (by intro _ _ _ _; trivial)
          refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
            (fun _ => ?_) (by intro _ _ _ _; trivial)
          refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
            (fun _ => ?_) (by intro _ _ _ _; trivial)
          refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
            (fun _ => ?_) (by intro _ _ _ _; trivial)
          split
          · exact Draws.pure g trivial
          · exact Draws.mono (btrsLoop_draws g n p spq a b c vr fuel _) (by intro _ _; trivial)

theorem binomial_draws (g : Gen σ F) (fuel : Nat) : ∀ (depth : Nat) (n : Int) (p : F),
    Draws g (binomialvariate g fuel depth n p) (fun _ => True)
  | 0, _, _ => Draws.raise g _
  | depth + 1, n, p => by
    simp only [binomialvariate]
    split
    · exact Draws.raise g _
    · split
      · split
        · exact Draws.pure g trivial
        · split
          · exact Draws.pure g trivial
          · exact Draws.raise g _
      · split
        · exact Draws.seq (a := 1) (b := 0) (Draws.rnd g rfl) (fun _ => Draws.pure g rfl)
            |>.mono (by intro _ _; trivial)
        · split
          · exact Draws.bind (Q := fun _ => True) (R := (· = 0)) (binomial_draws g fuel depth n _)
              (fun _ => Draws.pure g rfl) (by intro _ _ _ _; trivial)
          · refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
              (fun nf => ?_) (by intro _ _ _ _; trivial)
            split
            · refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
                (fun c => ?_) (by intro _ _ _ _; trivial)
              split
              · exact Draws.pure g trivial
              · exact Draws.mono (binomBG_draws g n c fuel 0 0) (by intro _ _; trivial)
            · split
              · exact Draws.raise g _
              · refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
                  (fun _ => ?_) (by intro _ _ _ _; trivial)
                refine Draws.bind (Q := (· = 0)) (R := fun _ => True) (Draws.lift g _ rfl)
                  (fun _ => ?_) (by intro _ _ _ _; trivial)
                exact Draws.mono (btrsLoop_draws g n p _ _ _ _ _ fuel none) (by intro _ _; trivial)

/-- `binomialvariate`: `p == 0.0` and `p == 1.0` return `0` and `n` without a draw,
`n == 1` with `0 < p < 1` draws once, and the argument checks come first. Every other
path uses a whole number of `random()` calls. -/
def BinomialEdges : Prop :=
  ∀ (σ F : Type) [Flt F] (g : Gen σ F) (fuel depth : Nat) (n : Int) (p : F) (s : σ),
    Draws g (binomialvariate g fuel (depth + 1) n p) (fun _ => True) ∧
    (n < 0 → binomialvariate g fuel (depth + 1) n p s =
      (.error (.valueError "n must be non-negative"), s)) ∧
    (0 ≤ n → Flt.le p 0.0 = true → Flt.beq p 0.0 = true →
      binomialvariate g fuel (depth + 1) n p s = (.ok 0, s)) ∧
    (0 ≤ n → Flt.le 1.0 p = true → Flt.beq p 0.0 = false → Flt.beq p 1.0 = true →
      binomialvariate g fuel (depth + 1) n p s = (.ok n, s)) ∧
    (Flt.le p 0.0 = false → Flt.le 1.0 p = false →
      Draws g (binomialvariate g fuel (depth + 1) 1 p) (· = 1))

theorem binomialEdges_proven : BinomialEdges := by
  intro σ F _ g fuel depth n p s
  refine ⟨binomial_draws g fuel _ n p, fun h => ?_, fun h0 h1 h2 => ?_, fun h0 h1 h2 h3 => ?_,
    fun h1 h2 => ?_⟩
  · simp only [binomialvariate]
    rw [if_pos h]
    rfl
  · simp only [binomialvariate]
    rw [if_neg (by omega)]
    simp only [h1, h2, Bool.true_or, if_true]
    rfl
  · simp only [binomialvariate]
    rw [if_neg (by omega)]
    simp only [h1, h2, h3, Bool.or_true, if_true, Bool.false_eq_true, if_false]
    rfl
  · simp only [binomialvariate]
    rw [if_neg (by omega)]
    simp only [h1, h2, Bool.or_false, Bool.false_eq_true, if_false, if_true]
    exact Draws.seq (a := 1) (b := 0) (Draws.rnd g rfl) (fun _ => Draws.pure g rfl)

/-! ### NaN parameters -/

/-- What IEEE 754 says about NaN, for a float type: an arithmetic operation or a libm
function with a NaN operand gives NaN, every comparison with NaN is false, and NaN is
not an infinity. -/
structure IeeeNaN (F : Type) [Flt F] : Prop where
  add_l : ∀ a b : F, isNan a → isNan (a + b)
  add_r : ∀ a b : F, isNan b → isNan (a + b)
  sub_l : ∀ a b : F, isNan a → isNan (a - b)
  sub_r : ∀ a b : F, isNan b → isNan (a - b)
  mul_l : ∀ a b : F, isNan a → isNan (a * b)
  mul_r : ∀ a b : F, isNan b → isNan (a * b)
  div_l : ∀ a b : F, isNan a → isNan (a / b)
  div_r : ∀ a b : F, isNan b → isNan (a / b)
  neg : ∀ a : F, isNan a → isNan (-a)
  exp : ∀ a : F, isNan a → isNan (Flt.exp a)
  sqrt : ∀ a : F, isNan a → isNan (Flt.sqrt a)
  lt_l : ∀ a b : F, isNan a → Flt.lt a b = false
  lt_r : ∀ a b : F, isNan b → Flt.lt a b = false
  le_l : ∀ a b : F, isNan a → Flt.le a b = false
  le_r : ∀ a b : F, isNan b → Flt.le a b = false
  beq_l : ∀ a b : F, isNan a → Flt.beq a b = false
  not_inf : ∀ a : F, isNan a → isInf a = false

/-! ### `choices` -/

theorem choicesPlain_spec (g : Gen σ F) (pop : SeqObj α) (n : F) : ∀ k : Nat,
    Draws g (choicesPlain g pop n k) (· = k) ∧
    Post (choicesPlain g pop n k) (fun l => l.length = k ∧ ∀ x ∈ l, ∃ j, pop.getItem j = .ok x)
  | 0 => ⟨Draws.pure g rfl, Post.pure ⟨rfl, by simp⟩⟩
  | k + 1 => by
    have ih := choicesPlain_spec g pop n k
    constructor
    · simp only [choicesPlain]
      refine Draws.bind (Q := (· = 1)) (R := (· = k)) (Draws.rnd g rfl) (fun r => ?_)
        (by dr)
      refine Draws.bind (Q := (· = 0)) (R := (· = k)) (Draws.lift g _ rfl) (fun j => ?_)
        (by dr)
      refine Draws.bind (Q := (· = 0)) (R := (· = k)) (Draws.lift g _ rfl) (fun x => ?_)
        (by dr)
      exact Draws.bind (Q := (· = k)) (R := (· = 0)) ih.1 (fun _ => Draws.pure g rfl)
        (by dr)
    · simp only [choicesPlain]
      refine Post.bind (Post.any _) (fun r _ => ?_)
      refine Post.bind (Post.any _) (fun j _ => ?_)
      refine Post.bind (Post.lift _) (fun x hx => ?_)
      refine Post.bind ih.2 (fun l hl => Post.pure ⟨by simp [hl.1], ?_⟩)
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨_, hx⟩
      · exact hl.2 y hy

theorem choicesWeighted_spec (g : Gen σ F) (pop : SeqObj α) (cum : List (Num F)) (total : F) (hi : Nat) :
    ∀ k : Nat,
    Draws g (choicesWeighted g pop cum total hi k) (· = k) ∧
    Post (choicesWeighted g pop cum total hi k)
      (fun l => l.length = k ∧ ∀ x ∈ l, ∃ j, pop.getItem j = .ok x)
  | 0 => ⟨Draws.pure g rfl, Post.pure ⟨rfl, by simp⟩⟩
  | k + 1 => by
    have ih := choicesWeighted_spec g pop cum total hi k
    constructor
    · simp only [choicesWeighted]
      refine Draws.bind (Q := (· = 1)) (R := (· = k)) (Draws.rnd g rfl) (fun r => ?_)
        (by dr)
      refine Draws.bind (Q := (· = 0)) (R := (· = k)) (Draws.lift g _ rfl) (fun x => ?_)
        (by dr)
      exact Draws.bind (Q := (· = k)) (R := (· = 0)) ih.1 (fun _ => Draws.pure g rfl)
        (by dr)
    · simp only [choicesWeighted]
      refine Post.bind (Post.any _) (fun r _ => ?_)
      refine Post.bind (Post.lift _) (fun x hx => ?_)
      refine Post.bind ih.2 (fun l hl => Post.pure ⟨by simp [hl.1], ?_⟩)
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨_, hx⟩
      · exact hl.2 y hy

/-- `choices(population, ...)` returns `k` items (none for `k <= 0`), each
`population[j]` for some `j`, with exactly `k` calls of `random()`, weighted or not.
Giving both `weights` and `cum_weights`, or a wrong number of cumulative weights,
raises before any draw. -/
def ChoicesSpec : Prop :=
  ∀ (σ F α : Type) [Flt F] (g : Gen σ F) (pop : SeqObj α) (n : Nat) (k : Int) (s : σ),
    pop.len = .ok n →
    (Draws g (choices g pop none none k) (· = k.toNat) ∧
     Post (choices g pop none none k)
      (fun l => l.length = k.toNat ∧ ∀ x ∈ l, ∃ j, pop.getItem j = .ok x)) ∧
    (∀ cum, Draws g (choices g pop none (some cum) k) (· = k.toNat) ∧
     Post (choices g pop none (some cum) k)
      (fun l => l.length = k.toNat ∧ ∀ x ∈ l, ∃ j, pop.getItem j = .ok x)) ∧
    (∀ w cum, choices g pop (some w) (some cum) k s =
      (.error (.typeError "Cannot specify both weights and cumulative weights"), s)) ∧
    (∀ cum : List (Num F), cum.length ≠ n → choices g pop none (some cum) k s =
      (.error (.valueError "The number of weights does not match the population"), s))

theorem choicesCum_spec (g : Gen σ F) (pop : SeqObj α) (n : Nat) (cum : List (Num F)) (k : Int) :
    Draws g (choicesCum g pop n cum k) (· = k.toNat) ∧
    Post (choicesCum g pop n cum k)
      (fun l => l.length = k.toNat ∧ ∀ x ∈ l, ∃ j, pop.getItem j = .ok x) := by
  unfold choicesCum
  split
  · exact ⟨Draws.raise g _, Post.raise⟩
  · split
    · exact ⟨Draws.raise g _, Post.raise⟩
    · constructor
      · refine Draws.bind (Q := (· = 0)) (R := (· = k.toNat)) (Draws.lift g _ rfl) (fun total => ?_)
          (by dr)
        split
        · exact Draws.raise g _
        · split
          · exact Draws.raise g _
          · exact (choicesWeighted_spec g pop cum total (n - 1) k.toNat).1
      · refine Post.bind (Post.any _) (fun total _ => ?_)
        split
        · exact Post.raise
        · split
          · exact Post.raise
          · exact (choicesWeighted_spec g pop cum total (n - 1) k.toNat).2

theorem choicesSpec_proven : ChoicesSpec := by
  intro σ F α _ g pop n k s hn
  have hcum : ∀ cum : List (Num F), choices g pop none (some cum) k =
      (RM.lift pop.len >>= fun n => choicesCum g pop n cum k) := fun _ => rfl
  have hplain : choices g pop none none k =
      (RM.lift pop.len >>= fun n =>
        (RM.lift (pyFloat (n : Int)) >>= fun nf => choicesPlain g pop (nf + 0.0) k.toNat)) := rfl
  refine ⟨⟨?_, ?_⟩, fun cum => ⟨?_, ?_⟩, fun w cum => ?_, fun cum h => ?_⟩
  · rw [hplain]
    refine Draws.bind (Q := (· = 0)) (R := (· = k.toNat)) (Draws.lift g _ rfl) (fun m => ?_)
      (by dr)
    exact Draws.bind (Q := (· = 0)) (R := (· = k.toNat)) (Draws.lift g _ rfl)
      (fun nf => (choicesPlain_spec g pop _ k.toNat).1) (by dr)
  · rw [hplain]
    refine Post.bind (Post.any _) (fun m _ => ?_)
    exact Post.bind (Post.any _) (fun nf _ => (choicesPlain_spec g pop _ k.toNat).2)
  · rw [hcum]
    exact Draws.bind (Q := (· = 0)) (R := (· = k.toNat)) (Draws.lift g _ rfl)
      (fun m => (choicesCum_spec g pop m cum k).1) (by dr)
  · rw [hcum]
    exact Post.bind (Post.any _) (fun m _ => (choicesCum_spec g pop m cum k).2)
  · simp only [choices, RM.bind_apply, RM.lift_apply, hn]
    rfl
  · rw [hcum]
    simp only [RM.bind_apply, RM.lift_apply, hn, choicesCum]
    rw [if_pos h]
    rfl

theorem mathLog_nan (x : F) (hx : isNan x) : mathLog x = .ok x := by
  simp [mathLog, hx]

theorem mathExp_nan (L : IeeeNaN F) (x : F) (hx : isNan x) : mathExp x = .ok (Flt.exp x) := by
  simp [mathExp, math1Over, hx, L.not_inf _ (L.exp x hx)]

theorem mathSqrt_nan (L : IeeeNaN F) (x : F) (hx : isNan x) : mathSqrt x = .ok (Flt.sqrt x) := by
  simp [mathSqrt, math1Dom, hx, L.not_inf _ (L.sqrt x hx)]

theorem pyDiv_nan (a b : F) (h : Flt.beq b 0.0 = false) : pyDiv a b = .ok (a / b) := by
  simp [pyDiv, h]

/-- With a NaN `alpha`, `gammaGS` rejects every pair of draws: whatever the generator
produces, the loop never ends. -/
theorem gammaGS_nan (L : IeeeNaN F) (g : Gen σ F) (alpha : F) (ha : isNan alpha) :
    ∀ (fuel : Nat) (s : σ), (gammaGS g alpha fuel s).1 = .error .modelFuel := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
    intro s
    rcases hs : g.random s with ⟨u, s1⟩
    rcases hs2 : g.random s1 with ⟨u1, s2⟩
    have hb : isNan ((E + alpha) / E) := L.div_l _ _ (L.add_r _ _ ha)
    have hp : isNan ((E + alpha) / E * u) := L.mul_l _ _ hb
    have hle : Flt.le ((E + alpha) / E * u) 1.0 = false := L.le_l _ _ hp
    have hlt : Flt.lt 1.0 ((E + alpha) / E * u) = false := L.lt_r _ _ hp
    have hq : isNan (((E + alpha) / E - (E + alpha) / E * u) / alpha) :=
      L.div_l _ _ (L.sub_l _ _ hb)
    have hdiv : pyDiv ((E + alpha) / E - (E + alpha) / E * u) alpha =
        .ok (((E + alpha) / E - (E + alpha) / E * u) / alpha) :=
      pyDiv_nan _ _ (L.beq_l _ _ ha)
    have hgx : gammaGSx alpha ((E + alpha) / E) ((E + alpha) / E * u) =
        .ok (-(((E + alpha) / E - (E + alpha) / E * u) / alpha)) := by
      simp only [gammaGSx, hle, Bool.false_eq_true, if_false, hdiv, mathLog_nan _ hq, bind,
        Except.bind, pure, Except.pure]
    have hx : isNan (-(-(((E + alpha) / E - (E + alpha) / E * u) / alpha))) := L.neg _ (L.neg _ hq)
    have hw : Flt.le u1 (Flt.exp (-(-(((E + alpha) / E - (E + alpha) / E * u) / alpha)))) = false :=
      L.le_r _ _ (L.exp _ hx)
    simp only [gammaGS, RM.bind_apply, rnd, hs, hs2, hlt, hgx, RM.lift_apply,
      mathExp_nan L _ hx, hw, Bool.false_eq_true, if_false]
    exact ih s2

/-- `gammaGS_nan` for the public method. -/
theorem gammavariate_nan (L : IeeeNaN F) (g : Gen σ F) (alpha beta : F) (ha : isNan alpha)
    (hb : Flt.le beta 0.0 = false) (fuel : Nat) (s : σ) :
    (gammavariate g fuel alpha beta s).1 = .error .modelFuel := by
  have h1 : Flt.le alpha 0.0 = false := L.le_l _ _ ha
  have h2 : Flt.lt 1.0 alpha = false := L.lt_r _ _ ha
  have h3 : Flt.beq alpha 1.0 = false := L.beq_l _ _ ha
  simp only [gammavariate, h1, hb, h2, h3, Bool.or_self, Bool.false_eq_true, if_false,
    RM.bind_apply]
  have hl := gammaGS_nan L g alpha ha fuel s
  cases hc : gammaGS g alpha fuel s with
  | mk r t =>
    rw [hc] at hl
    simp only at hl
    subst hl
    rfl

/-- With a NaN `r`, the `vonmisesvariate` loop rejects every pair of draws (given that
`cos(pi * u1)` is defined, as it is for `0 <= u1 < 1`). -/
theorem vonmisesLoop_nan (L : IeeeNaN F) (g : Gen σ F) (r : F) (hr : isNan r)
    (hcos : ∀ s, ∃ z, mathCos (PI * (g.random s).1) = .ok z) :
    ∀ (fuel : Nat) (s : σ), (vonmisesLoop g r fuel s).1 = .error .modelFuel := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
    intro s
    obtain ⟨z, hz⟩ := hcos s
    rcases hs : g.random s with ⟨u1, s1⟩
    rcases hs2 : g.random s1 with ⟨u2, s2⟩
    rw [hs] at hz
    have hsum : isNan (r + z) := L.add_l _ _ hr
    have hd : isNan (z / (r + z)) := L.div_r _ _ hsum
    have hdiv : pyDiv z (r + z) = .ok (z / (r + z)) := pyDiv_nan _ _ (L.beq_l _ _ hsum)
    have h1 : Flt.lt u2 (1.0 - z / (r + z) * (z / (r + z))) = false :=
      L.lt_r _ _ (L.sub_r _ _ (L.mul_l _ _ hd))
    have h2 : Flt.le u2 ((1.0 - z / (r + z)) * Flt.exp (z / (r + z))) = false :=
      L.le_r _ _ (L.mul_l _ _ (L.sub_r _ _ hd))
    have hacc : vonmisesAccept u2 (z / (r + z)) = .ok false := by
      simp only [vonmisesAccept, h1, Bool.false_eq_true, if_false, mathExp_nan L _ hd, h2, bind,
        Except.bind, pure, Except.pure]
    simp only [vonmisesLoop, RM.bind_apply, rnd, hs, hs2, RM.lift_apply, hz, hdiv, hacc,
      Bool.false_eq_true, if_false]
    exact ih s2

/-- `vonmisesLoop_nan` for the public method: a NaN `kappa` passes `kappa <= 1e-6` and
makes `r` NaN. -/
theorem vonmisesvariate_nan (L : IeeeNaN F) (g : Gen σ F) (mu kappa : F) (hk : isNan kappa)
    (hcos : ∀ s, ∃ z, mathCos (PI * (g.random s).1) = .ok z) (fuel : Nat) (s : σ) :
    (vonmisesvariate g fuel mu kappa s).1 = .error .modelFuel := by
  have a1 : Flt.le kappa 1e-6 = false := L.le_l _ _ hk
  have a2 : pyDiv 0.5 kappa = .ok (0.5 / kappa) := pyDiv_nan _ _ (L.beq_l _ _ hk)
  have hs0 : isNan ((0.5 : F) / kappa) := L.div_r _ _ hk
  have hx : isNan (1.0 + (0.5 : F) / kappa * ((0.5 : F) / kappa)) := L.add_r _ _ (L.mul_l _ _ hs0)
  have hr : isNan ((0.5 : F) / kappa + Flt.sqrt (1.0 + (0.5 : F) / kappa * ((0.5 : F) / kappa))) :=
    L.add_l _ _ hs0
  simp only [vonmisesvariate, a1, Bool.false_eq_true, if_false, RM.bind_apply, RM.lift_apply, a2,
    mathSqrt_nan L _ hx]
  have hl := vonmisesLoop_nan L g _ hr hcos fuel s
  cases hc : vonmisesLoop g ((0.5 : F) / kappa + Flt.sqrt (1.0 + (0.5 : F) / kappa * ((0.5 : F) / kappa))) fuel s with
  | mk r t =>
    rw [hc] at hl
    simp only at hl
    subst hl
    rfl

/-- What a NaN `p` does for `n != 1`. -/
theorem binomial_nan (L : IeeeNaN F) (g : Gen σ F) (fuel depth : Nat) (n : Int) (p x : F) (s : σ)
    (hp : isNan p) (h0 : 0 ≤ n) (h1 : n ≠ 1) (hx : Flt.ofInt n = some x) :
    binomialvariate g fuel (depth + 1) n p s = (.error (.assertionError ""), s) := by
  have a1 : Flt.le p 0.0 = false := L.le_l _ _ hp
  have a2 : Flt.le 1.0 p = false := L.le_r _ _ hp
  have a3 : Flt.lt 0.5 p = false := L.lt_r _ _ hp
  have a4 : Flt.lt (x * p) 10.0 = false := L.lt_l _ _ (L.mul_r _ _ hp)
  have a5 : Flt.le 10.0 (x * p) = false := L.le_r _ _ (L.mul_r _ _ hp)
  have hf : (pyFloat n : Py F) = .ok x := by simp [pyFloat, hx]
  simp only [binomialvariate]
  rw [if_neg (by omega)]
  simp only [a1, a2, Bool.or_self, Bool.false_eq_true, if_false]
  rw [if_neg h1]
  simp only [a3, Bool.false_eq_true, if_false, RM.bind_apply, RM.lift_apply, hf, a4, a5,
    Bool.false_and, Bool.not_false, if_true]
  rfl

end PyLean.CoreLibs.Rand
