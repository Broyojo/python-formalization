import PyLean.Decimal.Lemmas

/-!
The rounding modes. `roundSpec` is the specification (General Decimal
Arithmetic, "Rounding"; decimal docs, "Rounding modes") of rounding the
magnitude `c / b` of a value with sign `neg` to an integer, where
`c = q * b + r`, `0 ≤ r < b`:

* ROUND_DOWN truncates; ROUND_UP rounds away from zero when inexact;
* ROUND_CEILING / ROUND_FLOOR round toward +∞ / −∞ (away from zero for a
  positive / negative value);
* ROUND_HALF_UP / HALF_DOWN / HALF_EVEN round to nearest, ties away from
  zero / toward zero / to an even result;
* ROUND_05UP truncates, then rounds away from zero if inexact and the
  truncated result ends in 0 or 5.
-/

namespace PyLean.Decimal

open PyLean

def roundSpec (m : Rounding) (neg : Bool) (q r b : Nat) : Nat :=
  match m with
  | .down => q
  | .up => if r = 0 then q else q + 1
  | .ceiling => if neg ∨ r = 0 then q else q + 1
  | .floor => if !neg ∨ r = 0 then q else q + 1
  | .halfUp => if 2 * r ≥ b then q + 1 else q
  | .halfDown => if 2 * r > b then q + 1 else q
  | .halfEven => if 2 * r > b ∨ (2 * r = b ∧ q % 2 = 1) then q + 1 else q
  | .r05up => if r ≠ 0 ∧ q % 5 = 0 then q + 1 else q

/-- `_pydecimal`'s `_round_*` functions implement `roundSpec` (with `b = 2h`,
the `_exact_half` value), and report a change exactly when the dropped digits
are not all zero. -/
theorem roundDir_spec (m : Rounding) (neg : Bool) (q r h : Nat) (hr : r < 2 * h) :
    (if roundDir m neg q r h = 1 then q + 1 else q) = roundSpec m neg q r (2 * h) ∧
    (roundDir m neg q r h = 0 ↔ r = 0) := by
  cases m <;> cases neg <;> simp only [roundDir, roundSpec, Bool.not_true, Bool.not_false] <;>
    refine ⟨?_, ?_⟩ <;> (try constructor) <;> (try intro) <;> (repeat' split) <;> simp_all <;> omega

/-- The digits-below-zero substitution of `_rescale`/`_fix`
(`self = _dec_from_triple(self._sign, '1', exp-1)`, _pydecimal.py:2700-2702)
rounds like dropping all digits of `c` directly. -/
theorem roundDir_small (m : Rounding) (neg : Bool) (c h : Nat) (hc0 : c ≠ 0) (_h5 : 5 ≤ h) (hck : c < h) :
    roundDir m neg 0 1 5 = roundDir m neg 0 c h := by
  cases m <;> cases neg <;> simp only [roundDir, Bool.not_true, Bool.not_false] <;> (repeat' split) <;> simp_all <;> omega

theorem incr_cases (q d : Nat) : incr q d = .ok (q + 1) ∨ ∃ msg, incr q d = .error (.valueError msg) := by
  unfold incr intLimit strLimit
  by_cases h1 : max d 1 > maxStrDigits
  · right; exact ⟨limitToIntMsg (max d 1), by simp [h1, bind, Except.bind]⟩
  · by_cases h2 : numDigits (q + 1) > maxStrDigits
    · right; exact ⟨limitToStrMsg, by simp [h1, h2, bind, Except.bind]⟩
    · left; simp [h1, h2, bind, Except.bind, pure, Except.pure]

/-- `rescale` on a finite non-zero value with a larger target exponent
returns the coefficient `roundSpec` prescribes for the dropped digits, or
raises the int/str-limit `ValueError`. -/
theorem rescale_round (m : Rounding) (neg : Bool) (c : Nat) (e x : Int) (hc : c ≠ 0) (hx : e < x) :
    (rescale (.fin neg c e) x m = .ok (.fin neg
        (roundSpec m neg (c / 10 ^ (x - e).toNat) (c % 10 ^ (x - e).toNat) (10 ^ (x - e).toNat)) x)) ∨
    (∃ msg, rescale (.fin neg c e) x m = .error (.valueError msg)) := by
  have hk : 1 ≤ (x - e).toNat := by omega
  have hb := pow_ten_eq_two_half hk
  have hr : c % 10 ^ (x - e).toNat < 10 ^ (x - e).toNat := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have key : ∀ q r h D, roundDir m neg q r h = roundDir m neg (c / 10 ^ (x - e).toNat) (c % 10 ^ (x - e).toNat) (5 * 10 ^ ((x - e).toNat - 1)) →
      q = c / 10 ^ (x - e).toNat →
      ((if roundDir m neg q r h = 1 then (do let v ← incr q D; pure (Dec.fin neg v x)) else (pure (Dec.fin neg q x) : Py Dec)) = .ok (.fin neg
        (roundSpec m neg (c / 10 ^ (x - e).toNat) (c % 10 ^ (x - e).toNat) (10 ^ (x - e).toNat)) x) ∨
      (∃ msg, (if roundDir m neg q r h = 1 then (do let v ← incr q D; pure (Dec.fin neg v x)) else (pure (Dec.fin neg q x) : Py Dec)) = .error (.valueError msg))) := by
    intro q r h D hdir hq
    subst hq
    have hs := (roundDir_spec m neg (c / 10 ^ (x - e).toNat) (c % 10 ^ (x - e).toNat) (5 * 10 ^ ((x - e).toNat - 1)) (by omega)).1
    rw [← hb] at hs
    rw [hdir]
    split
    · rename_i h1
      simp only [h1, ↓reduceIte] at hs
      rcases incr_cases (c / 10 ^ (x - e).toNat) D with h2 | ⟨msg, h2⟩
      · left; simp [h2, bind, Except.bind, pure, Except.pure, ← hs]
      · right; exact ⟨msg, by simp [h2, bind, Except.bind]⟩
    · rename_i h1
      simp only [h1, ↓reduceIte] at hs
      left; simp [pure, Except.pure, ← hs]
  unfold rescale
  simp only [hc, ↓reduceIte, show ¬(e ≥ x) by omega]
  by_cases hd : (numDigits c : Int) + e - x < 0
  · have hlt : numDigits c < (x - e).toNat := by omega
    have hcl : c < 10 ^ (numDigits c) := lt_pow_numDigits c
    have hc2 : c < 5 * 10 ^ ((x - e).toNat - 1) := by
      have : 10 ^ (numDigits c) ≤ 10 ^ ((x - e).toNat - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hq : c / 10 ^ (x - e).toNat = 0 := Nat.div_eq_of_lt (by omega)
    have hrr : c % 10 ^ (x - e).toNat = c := Nat.mod_eq_of_lt (by omega)
    simp only [hd, ↓reduceIte, roundKeep]
    apply key
    · rw [hq, hrr]
      exact roundDir_small m neg c _ hc (by have : 1 ≤ 10 ^ ((x - e).toNat - 1) := Nat.one_le_pow _ _ (by decide); omega) hc2
    · rw [hq]; rfl
  · have hdg : numDigits c - ((numDigits c : Int) + e - x).toNat = (x - e).toNat := by omega
    simp only [hd, ↓reduceIte, roundKeep, hdg]
    exact key _ _ _ _ rfl rfl

end PyLean.Decimal
