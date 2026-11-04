import PyLean.Decimal.DelegateExact

/-!
More delegates of the `Context` wrappers, stated outright: `to_integral_exact` and `normalize`.
-/

namespace PyLean.Decimal

open PyLean

/-! ## `to_integral_exact` -/

/-- `to_integral_exact` (_pydecimal.py:2733-2760) on every operand, for every context and rounding
argument: a finite value with exponent ≥ 0 is returned unchanged; a zero with a negative exponent
becomes the zero of its sign at exponent 0; a non-zero value with a negative exponent becomes the
integer `roundSpec` prescribes at exponent 0, signalling Inexact when non-zero digits were dropped
and then Rounded (the first trapped one raising), with the int/str-limit `ValueError` exactly when
the rounded integer is the truncated one plus one with more than 4300 digits; an infinity is
returned unchanged and a NaN goes through `_check_nans`. -/
def ToIntegralExactExact : Prop :=
  ∀ (c : Ctx) (r : Option Rounding) (fl : List Signal),
    (∀ (neg : Bool) (co : Nat) (e : Int), 0 ≤ e →
      (toIntegralExact c (.fin neg co e) r).run fl = .ok (.fin neg co e, fl)) ∧
    (∀ (neg : Bool) (e : Int), e < 0 →
      (toIntegralExact c (.fin neg 0 e) r).run fl = .ok (.fin neg 0 0, fl)) ∧
    (∀ (neg : Bool) (co : Nat) (e : Int), e < 0 → co ≠ 0 →
      let k := e.natAbs
      let q := co / 10 ^ k
      let v := roundSpec (r.getD c.rounding) neg q (co % 10 ^ k) (10 ^ k)
      ((v = q ∨ numDigits v ≤ maxStrDigits) →
        (toIntegralExact c (.fin neg co e) r).run fl =
          sigRun c ((if co % 10 ^ k ≠ 0 then [.inexact] else []) ++ [.rounded]) fl (.fin neg v 0)) ∧
      (v ≠ q → maxStrDigits < numDigits v →
        ∃ m, (toIntegralExact c (.fin neg co e) r).run fl = .error (.valueError m))) ∧
    (∀ neg : Bool, (toIntegralExact c (.inf neg) r).run fl = .ok (.inf neg, fl)) ∧
    (∀ (neg : Bool) (p : Nat),
      (toIntegralExact c (.nan neg false p) r).run fl = .ok (.nan neg false (p % 10 ^ nanDigits c), fl) ∧
      (toIntegralExact c (.nan neg true p) r).run fl =
        afterSig c .invalidOperation fl (.nan neg false (p % 10 ^ nanDigits c)))

theorem toIntegralExactExact_proven : ToIntegralExactExact := by
  intro c r fl
  refine ⟨fun neg co e he => ?_, fun neg e he => ?_, fun neg co e he hc => ?_, fun neg => ?_,
    fun neg p => ⟨?_, ?_⟩⟩
  · simp [toIntegralExact, he]; rfl
  · simp [toIntegralExact, show ¬ e ≥ 0 by omega]; rfl
  · intro k q v
    have hk : (0 - e).toNat = k := by simp only [k]; omega
    have hre := rescale_exact (r.getD c.rounding) neg co e 0 hc he
    simp only [hk] at hre
    have hq : quantSpec (r.getD c.rounding) neg co e 0 = v := by
      simp only [quantSpec, show ¬ e ≥ 0 by omega, ↓reduceIte, hk, v, q]
    have heq := cmpVal_quantized (r.getD c.rounding) neg co e 0 hc he
    rw [hq, hk] at heq
    refine ⟨fun hv => ?_, fun h1 h2 => ?_⟩
    · have hr := hre.1 hv
      simp only [toIntegralExact, show ¬ e ≥ 0 by omega, hc, ↓reduceIte]
      rw [liftPy_run, hr]
      simp only []
      simp only [v, q] at heq ⊢
      generalize roundSpec (r.getD c.rounding) neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k) = V at heq ⊢
      by_cases h0 : co % 10 ^ k = 0
      · rw [if_neg (by simp [heq, h0])]
        simp only [h0, ne_eq, not_true_eq_false, ↓reduceIte, List.nil_append, sigRun_cons, sigRun]
        rw [raiseSig_bind, pure_run]
      · rw [if_pos (by simp [heq, h0])]
        simp only [h0, ne_eq, not_false_eq_true, ↓reduceIte, List.cons_append, List.nil_append,
          sigRun_cons, sigRun]
        rw [raiseSig_bind]
        split
        · rfl
        · rw [raiseSig_bind, pure_run]
    · obtain ⟨m, hm⟩ := hre.2 h1 h2
      refine ⟨m, ?_⟩
      simp only [toIntegralExact, show ¬ e ≥ 0 by omega, hc, ↓reduceIte]
      rw [liftPy_run, hm]
  · simp [toIntegralExact, checkNans]; rfl
  · simp [toIntegralExact, checkNans, fixNan_spec]; rfl
  · rw [← sNaN_run]; simp [toIntegralExact, checkNans]

/-! ## `normalize` -/

/-- The trailing-zero loop of `normalize` (_pydecimal.py:2593-2597) strips `k` zeros: the most
that divide the coefficient, but stopping at the exponent `M` (`Emax`, or `Etop` under clamp). -/
theorem strip_spec (M : Int) : ∀ (f co : Nat) (e : Int), co ≠ 0 → ¬ 10 ^ f ∣ co →
    ∃ k : Nat, normalize.strip M co e f = (co / 10 ^ k, e + k) ∧ 10 ^ k ∣ co ∧
      (M ≤ e + k ∨ ¬ 10 ^ (k + 1) ∣ co) ∧ (k = 0 ∨ e + k ≤ M) := by
  intro f
  induction f with
  | zero => intro co e hc h; exact absurd (Nat.one_dvd co) (by simpa using h)
  | succ f ih =>
    intro co e hc h
    simp only [normalize.strip]
    by_cases hs : co % 10 = 0 ∧ e < M
    · rw [if_pos hs]
      obtain ⟨c', rfl⟩ : ∃ c', co = 10 * c' := ⟨co / 10, by omega⟩
      have hc' : c' ≠ 0 := by omega
      have h' : ¬ 10 ^ f ∣ c' := by
        intro hd; apply h; rw [Nat.pow_succ, Nat.mul_comm]; exact Nat.mul_dvd_mul_left 10 hd
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih c' (e + 1) hc' h'
      refine ⟨k + 1, ?_, ?_, ?_, ?_⟩
      · rw [Nat.mul_div_cancel_left _ (by decide : 0 < 10), hk1, Nat.pow_succ, Nat.mul_comm (10 ^ k) 10,
          ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ (by decide : 0 < 10)]
        simp only [Prod.mk.injEq, true_and]; push_cast; omega
      · rw [Nat.pow_succ, Nat.mul_comm (10 ^ k) 10]; exact Nat.mul_dvd_mul_left 10 hk2
      · rcases hk3 with h3 | h3
        · left; push_cast; omega
        · right; intro hd; apply h3
          rw [Nat.pow_succ, Nat.mul_comm (10 ^ (k + 1)) 10] at hd
          exact Nat.dvd_of_mul_dvd_mul_left (by decide) hd
      · right; rcases hk4 with h4 | h4
        · subst h4; push_cast; omega
        · push_cast; omega
    · rw [if_neg hs]
      refine ⟨0, by simp, Nat.one_dvd _, ?_, Or.inl rfl⟩
      by_cases he : e < M
      · right; intro hd; apply hs; refine ⟨?_, he⟩; simpa using Nat.mod_eq_zero_of_dvd hd
      · left; push_cast; omega

/-- `normalize` (_pydecimal.py:2575-2598) for every context and every operand that is not a NaN:
the operand is first rounded by `_fix` (decimal-fix-exact), whose exception, if any, is raised;
a zero result becomes the zero of its sign at exponent 0; a non-zero `±co·10^e` loses its trailing
zeros, as many as divide `co`, but no more than bring the exponent to `Emax` (`Etop` under
`clamp=1`); an infinity is returned. A NaN goes through `_check_nans`. -/
def NormalizeExact : Prop :=
  ∀ (c : Ctx) (a : Dec) (fl : List Signal), nanKind a = 0 →
    let M := if c.clamp then c.etop else c.emax
    match (fix c a).run fl with
    | .error e => (normalize c a).run fl = .error e
    | .ok (.fin neg co e, fl') =>
      (co = 0 → (normalize c a).run fl = .ok (.fin neg 0 0, fl')) ∧
      (co ≠ 0 → ∃ k : Nat, (normalize c a).run fl = .ok (.fin neg (co / 10 ^ k) (e + k), fl') ∧
        10 ^ k ∣ co ∧ (M ≤ e + k ∨ ¬ 10 ^ (k + 1) ∣ co) ∧ (k = 0 ∨ e + k ≤ M))
    | .ok (d, fl') => (normalize c a).run fl = .ok (d, fl')

theorem normalizeExact_proven : NormalizeExact := by
  intro c a fl ha M
  have hrun : (normalize c a).run fl = (fix c a >>= fun dup => (match dup with
      | .fin neg co e =>
        if co = 0 then pure (.fin neg 0 0)
        else
          let p := normalize.strip M co e (numDigits co)
          pure (.fin neg p.1 p.2)
      | d => pure d : DM Dec)).run fl := by
    rcases a with ⟨n, co, e⟩ | n | ⟨n, s, p⟩
    · rfl
    · simp only [normalize, checkNans]; rfl
    · cases s <;> simp [nanKind] at ha
  rw [hrun, bind_run]
  cases hf : (fix c a).run fl with
  | error e => rfl
  | ok p =>
    obtain ⟨d, fl'⟩ := p
    rcases d with ⟨neg, co, e⟩ | n | ⟨n, s, pl⟩
    · refine ⟨fun h0 => by simp [h0]; rfl, fun h0 => ?_⟩
      have hnd : ¬ 10 ^ numDigits co ∣ co := by
        intro hd
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
        have := lt_pow_numDigits co
        omega
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := strip_spec M (numDigits co) co e h0 hnd
      exact ⟨k, by simp only [h0, ↓reduceIte, hk1]; rfl, hk2, hk3, hk4⟩
    · rfl
    · rfl

end PyLean.Decimal
