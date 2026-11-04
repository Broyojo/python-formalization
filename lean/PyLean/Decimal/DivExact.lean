import PyLean.Decimal.AddExact
import PyLean.Decimal.DivisionProps

/-!
`__truediv__` over every operand pair: for non-zero finite operands whose quotient is not exact
at the working exponent, `_fix` of the truncated quotient with its inexact bit, which is `_fix` of
every decimal strictly between the truncation bounds of the exact quotient, so the exact rational
quotient rounded into the context; an exact quotient at the exponent closest to the ideal one; and
`_pydecimal`'s int/str-limit `ValueError`s where they are raised.
-/

namespace PyLean.Decimal

open PyLean

/-! ## Arithmetic -/

theorem dm10 (x P : Nat) : x % (10 * P) = x % 10 + 10 * (x / 10 % P) ∧ x / (10 * P) = x / 10 / P :=
  ⟨Nat.mod_mul, (Nat.div_div_eq_div_mul x 10 P).symm⟩

theorem pow_ten_cases (k : Nat) : 10 ^ k = 1 ∨ ∃ P', 10 ^ k = 10 * P' := by
  cases k with
  | zero => exact Or.inl rfl
  | succ n => exact Or.inr ⟨10 ^ n, by rw [Nat.pow_succ, Nat.mul_comm]⟩

/-- The `coeff % 5 == 0` bump of `__truediv__` (_pydecimal.py:1414-1416). -/
def bump (T : Nat) : Nat := if T % 5 = 0 then T + 1 else T

theorem bump_div10 (T : Nat) : bump T / 10 = T / 10 := by
  unfold bump; split <;> omega

theorem bump_mod10 (T : Nat) :
    (T % 10 % 5 = 0 → bump T % 10 = T % 10 + 1) ∧ (T % 10 % 5 ≠ 0 → bump T % 10 = T % 10) := by
  have h5 : T % 5 = T % 10 % 5 := by omega
  unfold bump
  constructor <;> intro h
  · rw [if_pos (by omega)]; omega
  · rw [if_neg (by omega)]

/-- The bumped quotient at `E0` and the truncated quotient with an inexact digit `1` at `E0 - 1`
drop the same digits as far as `_fix` can tell. -/
theorem sticky_bump (T : Nat) : StickyAt (bump T) (10 * T + 1) 1 := by
  intro k hk
  obtain ⟨P, hP⟩ : ∃ P, 10 ^ k = 10 * P := ⟨10 ^ (k - 1), by
    rw [show k = (k - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]; simp⟩
  have hP1 : 10 ^ (k + 1) = 10 * (10 * P) := by rw [Nat.pow_succ, hP, Nat.mul_comm]
  have hPpos : 0 < P := by have := Nat.pow_pos (n := k) (show 0 < 10 by decide); omega
  rw [hP, hP1]
  obtain ⟨wm, wd⟩ := dm10 (bump T) P
  obtain ⟨xm, xd⟩ := dm10 (10 * T + 1) (10 * P)
  obtain ⟨tm, td⟩ := dm10 T P
  have x10 : (10 * T + 1) / 10 = T := by omega
  have x10' : (10 * T + 1) % 10 = 1 := by omega
  rw [x10] at xm xd
  rw [x10'] at xm
  rw [tm] at xm
  rw [td] at xd
  rw [bump_div10] at wm wd
  have hA := Nat.mod_lt (T / 10) hPpos
  have hb := bump_mod10 T
  have ht := Nat.mod_lt T (show 0 < 10 by decide)
  rw [wm, xm, wd, xd]
  -- P is 1 or a multiple of 10
  have hPc : P = 1 ∨ ∃ P', P = 10 * P' := by
    rcases pow_ten_cases (k - 1) with h | ⟨P', h⟩
    · left
      have : 10 ^ k = 10 * 10 ^ (k - 1) := by
        rw [show k = (k - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]; simp
      omega
    · right; refine ⟨P', ?_⟩
      have : 10 ^ k = 10 * 10 ^ (k - 1) := by
        rw [show k = (k - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]; simp
      omega
  generalize T / 10 % P = A at hA ⊢
  generalize T % 10 = t at ht hb ⊢
  generalize bump T % 10 = c' at hb ⊢
  refine ⟨rfl, ?_, by omega, ?_, ?_, ?_⟩
  · by_cases h5 : t % 5 = 0
    · have := hb.1 h5; omega
    · have := hb.2 h5; omega
  all_goals
    rcases hPc with rfl | ⟨P', rfl⟩
    · have : A = 0 := by omega
      subst this
      by_cases h5 : t % 5 = 0
      · have := hb.1 h5; omega
      · have := hb.2 h5; omega
    · by_cases h5 : t % 5 = 0
      · have := hb.1 h5; omega
      · have := hb.2 h5; omega

/-- `fixSpec_sticky` when `_fix` drops at least two digits of `W`, so the facts are needed only
from `k = 2` on. -/
def StickyAt2 (W X d : Nat) : Prop :=
  ∀ k, 2 ≤ k → X / 10 ^ (k + d) = W / 10 ^ k ∧ W % 10 ^ k ≠ 0 ∧ X % 10 ^ (k + d) ≠ 0 ∧
    (2 * (W % 10 ^ k) ≥ 10 ^ k ↔ 2 * (X % 10 ^ (k + d)) ≥ 10 ^ (k + d)) ∧
    (2 * (W % 10 ^ k) > 10 ^ k ↔ 2 * (X % 10 ^ (k + d)) > 10 ^ (k + d)) ∧
    (2 * (W % 10 ^ k) = 10 ^ k ↔ 2 * (X % 10 ^ (k + d)) = 10 ^ (k + d))

theorem fixSpec_sticky2 (c : Ctx) (neg : Bool) (W X d : Nat) (E : Int) (fl : List Signal)
    (hW : c.prec + 1 < numDigits W) (hnd : numDigits X = numDigits W + d) (hs : StickyAt2 W X d) :
    fixSpec c neg X (E - d) fl = fixSpec c neg W E fl := by
  rw [fixSpec_round c neg X (E - d) fl (by omega), fixSpec_round c neg W E fl (by omega)]
  have hae : ((numDigits X : Nat) : Int) + (E - d) = (numDigits W : Int) + E := by rw [hnd]; push_cast; omega
  have hm := Int.le_max_left ((numDigits W : Int) + E - c.prec) (c.emin - c.prec + 1)
  have hk1 : 2 ≤ fixK c W E := by unfold fixK; omega
  have hk : fixK c X (E - d) = fixK c W E + d := by
    unfold fixK; rw [hae]; omega
  rw [hae, hk]
  obtain ⟨hq, hr, hr', h1, h2, h3⟩ := hs (fixK c W E) hk1
  rw [hq, roundSpec_congr c.rounding neg (W / 10 ^ fixK c W E) _ _ _ _ hr' hr h1.symm h2.symm h3.symm]
  simp only [hr, hr', ne_eq, not_false_eq_true, decide_true]

/-- `5Q ≤ u` decides how `R·u + v` compares with `5·Q·R` when `0 < v < R`. -/
theorem half_scale (u Q R v : Nat) (hv0 : 0 < v) (hvR : v < R) :
    (5 * Q ≤ u → 5 * Q * R < R * u + v) ∧ (u < 5 * Q → R * u + v < 5 * Q * R) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := Nat.mul_le_mul_left R h
    rw [Nat.mul_comm R (5 * Q)] at this
    omega
  · have := Nat.mul_le_mul_left R (show u + 1 ≤ 5 * Q by omega)
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm R (5 * Q)] at this
    omega

/-- Every decimal strictly between `T·10^(d+1)` and `(T+1)·10^(d+1)` drops, from two digits of
`10T + 1` on, what `10T + 1` drops as far as `_fix` can tell. -/
theorem sticky_between (T X d : Nat) (h1 : 10 ^ (d + 1) * T < X) (h2 : X < 10 ^ (d + 1) * (T + 1)) :
    StickyAt2 (10 * T + 1) X d := by
  intro k hk
  generalize hR : 10 ^ (d + 1) = R at h1 h2
  have hRpos : 0 < R := by rw [← hR]; exact Nat.pow_pos (by decide)
  obtain ⟨Q, hQ⟩ : ∃ Q, 10 ^ (k - 2) = Q := ⟨_, rfl⟩
  have hk1 : 10 ^ k = 10 * (10 * Q) := by
    rw [← hQ, show k = (k - 2) + 1 + 1 by omega, Nat.pow_succ, Nat.pow_succ]; simp; omega
  have hkd : 10 ^ (k + d) = R * (10 * Q) := by
    rw [← hR, ← hQ, show k + d = (d + 1) + ((k - 2) + 1) by omega, Nat.pow_add, Nat.pow_succ 10 (k - 2),
      Nat.mul_comm (10 ^ (k - 2)) 10]
  have hQpos : 0 < Q := by rw [← hQ]; exact Nat.pow_pos (by decide)
  rw [hk1, hkd]
  have hXT : X / R = T := Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega) (by rw [Nat.mul_comm]; omega)
  have hdm := Nat.div_add_mod X R
  rw [hXT] at hdm
  have hv0 : 0 < X % R := by
    have : R * T < X := h1
    omega
  have hvR := Nat.mod_lt X hRpos
  have xm : X % (R * (10 * Q)) = X % R + R * (T % (10 * Q)) := by rw [Nat.mod_mul, hXT]
  have xd : X / (R * (10 * Q)) = T / (10 * Q) := by rw [← Nat.div_div_eq_div_mul, hXT]
  obtain ⟨wm, wd⟩ := dm10 (10 * T + 1) (10 * Q)
  have x10 : (10 * T + 1) / 10 = T := by omega
  have x10' : (10 * T + 1) % 10 = 1 := by omega
  rw [x10] at wm wd
  rw [x10'] at wm
  rw [xm, xd, wm, wd]
  have hu := Nat.mod_lt T (show 0 < 10 * Q by omega)
  have hs := half_scale (T % (10 * Q)) Q R (X % R) hv0 hvR
  have e1 : R * (10 * Q) = 10 * (Q * R) := by
    rw [Nat.mul_comm R (10 * Q), Nat.mul_assoc]
  have e2 : 5 * Q * R = 5 * (Q * R) := Nat.mul_assoc ..
  rw [e1]
  rw [e2] at hs
  generalize T % (10 * Q) = u at hu hs ⊢
  generalize X % R = v at hv0 hvR hs ⊢
  generalize R * u = RU at hs ⊢
  generalize Q * R = QR at hs ⊢
  refine ⟨rfl, by omega, by omega, ?_, ?_, ?_⟩ <;>
    by_cases hc : 5 * Q ≤ u
  all_goals first
    | (have := hs.1 hc; omega)
    | (have := hs.2 (by omega); omega)

/-! ## `__truediv__`'s working values -/

/-- `shift = len(other._int) - len(self._int) + context.prec + 1` (_pydecimal.py:1405). -/
def tdShift (prec ca cb : Nat) : Int := (numDigits cb : Int) - numDigits ca + prec + 1

/-- The dividend and divisor `divmod` divides (_pydecimal.py:1409-1412), so that the exact quotient
`(ca/cb)·10^(ea-eb)` is `(tdNum/tdDen)·10^(ea - eb - shift)`. -/
def tdNum (prec ca cb : Nat) : Nat :=
  if tdShift prec ca cb ≥ 0 then ca * 10 ^ (tdShift prec ca cb).toNat else ca

def tdDen (prec ca cb : Nat) : Nat :=
  if tdShift prec ca cb ≥ 0 then cb else cb * 10 ^ (-tdShift prec ca cb).toNat

/-- An exact quotient `T·10^E0` written `m·10^k` with the exponent closest to the ideal `ea - eb`
(_pydecimal.py:1418-1423): below the ideal exponent, trailing zeros are removed until it is
reached; at or above it, nothing is removed. -/
def TdRep (T : Nat) (E0 ideal : Int) (m : Nat) (k : Int) : Prop :=
  E0 ≤ k ∧ m * 10 ^ (k - E0).toNat = T ∧
    (if E0 < ideal then k ≤ ideal ∧ (k = ideal ∨ m % 10 ≠ 0) else k = E0)

theorem truedivFin_eval (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (ha : ca ≠ 0) (h1 : numDigits ca ≤ maxStrDigits) (h2 : numDigits cb ≤ maxStrDigits) :
    truedivFin c sa ca ea sb cb eb =
      .ok (if tdNum c.prec ca cb % tdDen c.prec ca cb ≠ 0 then
          (bump (tdNum c.prec ca cb / tdDen c.prec ca cb), ea - eb - tdShift c.prec ca cb)
        else stripIdeal (tdNum c.prec ca cb / tdDen c.prec ca cb) (ea - eb - tdShift c.prec ca cb)
          (ea - eb) (ea - eb - (ea - eb - tdShift c.prec ca cb)).toNat) := by
  have g1 : ¬ numDigits ca > maxStrDigits := by omega
  have g2 : ¬ numDigits cb > maxStrDigits := by omega
  simp only [truedivFin, ha, ↓reduceIte, workRep, intLimit, g1, g2, bind, Except.bind, pure, Except.pure]
  unfold tdNum tdDen tdShift bump
  split <;> split <;> simp_all

theorem truedivFin_err_a (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (ha : ca ≠ 0) (h1 : maxStrDigits < numDigits ca) :
    truedivFin c sa ca ea sb cb eb = .error (.valueError (limitToIntMsg (numDigits ca))) := by
  have g1 : numDigits ca > maxStrDigits := h1
  simp only [truedivFin, ha, ↓reduceIte, workRep, intLimit, g1, bind, Except.bind]

theorem truedivFin_err_b (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (ha : ca ≠ 0) (h1 : numDigits ca ≤ maxStrDigits) (h2 : maxStrDigits < numDigits cb) :
    truedivFin c sa ca ea sb cb eb = .error (.valueError (limitToIntMsg (numDigits cb))) := by
  have g1 : ¬ numDigits ca > maxStrDigits := by omega
  have g2 : numDigits cb > maxStrDigits := h2
  simp only [truedivFin, ha, ↓reduceIte, workRep, intLimit, g1, g2, bind, Except.bind, pure, Except.pure]

/-- `__truediv__` of non-zero finite operands is its integer division, `str(coeff)` and `_fix`
(_pydecimal.py:1401-1426). -/
theorem truediv_fin_run (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (fl : List Signal) (hb : cb ≠ 0) :
    (truediv c (.fin sa ca ea) (.fin sb cb eb)).run fl =
      match truedivFin c sa ca ea sb cb eb with
      | .error e => .error e
      | .ok r => if maxStrDigits < numDigits r.1 then .error (.valueError limitToStrMsg)
          else (fix c (.fin (sa != sb) r.1 r.2)).run fl := by
  have hz2 : isZero (.fin sb cb eb) = false := isZero_fin sb cb eb hb
  have hd : decBool (.fin sb cb eb) = true := by simp [decBool, hz2]
  simp only [truediv, isSpecial, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hd,
    Bool.not_true, Dec.neg]
  rw [liftPy_run]
  cases truedivFin c sa ca ea sb cb eb with
  | error e => rfl
  | ok r => exact strLimit_fix_run c r.1 (sa != sb) r.2 fl

theorem truediv_zero_run (c : Ctx) (sa : Bool) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (fl : List Signal) (hb : cb ≠ 0) :
    (truediv c (.fin sa 0 ea) (.fin sb cb eb)).run fl = (fix c (.fin (sa != sb) 0 (ea - eb))).run fl := by
  rw [truediv_fin_run c sa 0 ea sb cb eb fl hb]
  simp only [truedivFin, ↓reduceIte, pure, Except.pure]
  simp [numDigits_zero, maxStrDigits]

theorem truediv_nan_run (c : Ctx) (fl : List Signal) (a b : Dec) (h : nanKind a ≠ 0 ∨ nanKind b ≠ 0) :
    (truediv c a b).run fl = nanSpec2 c a b fl := by
  rcases a with ⟨sa, ca, ea⟩ | na | ⟨na, ssa, pa⟩ <;> rcases b with ⟨sb, cb, eb⟩ | nb | ⟨nb, ssb, pb⟩ <;>
    first
    | (simp [nanKind] at h; done)
    | (simp only [truediv, isSpecial, Bool.or_true, Bool.true_or, ↓reduceIte]
       exact checkNans_return c _ _ fl _ (fun d => rfl) h)

theorem numDigits_ten_mul_add (T r : Nat) (hT : T ≠ 0) (hr : r < 10) :
    numDigits (10 * T + r) = numDigits T + 1 := by
  obtain ⟨l, u⟩ := numDigits_bounds hT
  have hpos := numDigits_pos T
  apply numDigits_eq
  · rw [show numDigits T + 1 - 1 = (numDigits T - 1) + 1 by omega, Nat.pow_succ]; omega
  · rw [Nat.pow_succ]; omega
  · omega

theorem numDigits_between (T X d : Nat) (hT : T ≠ 0) (h1 : 10 ^ (d + 1) * T < X)
    (h2 : X < 10 ^ (d + 1) * (T + 1)) : numDigits X = numDigits T + 1 + d := by
  obtain ⟨l, u⟩ := numDigits_bounds hT
  have hpos := numDigits_pos T
  apply numDigits_eq
  · rw [show numDigits T + 1 + d - 1 = (d + 1) + (numDigits T - 1) by omega, Nat.pow_add]
    have := Nat.mul_le_mul_left (10 ^ (d + 1)) l
    omega
  · rw [show numDigits T + 1 + d = (d + 1) + numDigits T by omega, Nat.pow_add]
    have := Nat.mul_le_mul_left (10 ^ (d + 1)) (show T + 1 ≤ 10 ^ numDigits T by omega)
    omega
  · omega

theorem numDigits_bump (T : Nat) (hT : 10 ≤ T) : numDigits (bump T) = numDigits T := by
  unfold bump
  split
  · rename_i h5
    obtain ⟨l, u⟩ := numDigits_bounds (show T ≠ 0 by omega)
    have h2 := ten_le_numDigits hT
    have hm := pow_mod_ten (show 1 ≤ numDigits T by omega)
    apply numDigits_eq
    · omega
    · have : T + 1 ≠ 10 ^ numDigits T := fun h => by rw [← h] at hm; omega
      omega
    · omega
  · rfl


/-! ## The exact quotient's representation -/

theorem tdRep_strip (T : Nat) (E0 ideal : Int) :
    TdRep T E0 ideal (stripIdeal T E0 ideal (ideal - E0).toNat).1 (stripIdeal T E0 ideal (ideal - E0).toNat).2 := by
  obtain ⟨p1, p2, p3⟩ := stripIdeal_spec ideal (ideal - E0).toNat T E0 rfl
  refine ⟨p2, p1, ?_⟩
  split
  · exact p3 (by omega)
  · rename_i h
    have hf : (ideal - E0).toNat = 0 := by omega
    rw [hf]; rfl

theorem pow_cancel {m m0 a b : Nat} (h : m * 10 ^ a = m0 * 10 ^ b) (hab : a ≤ b) :
    m = m0 * 10 ^ (b - a) := by
  have hb : 10 ^ b = 10 ^ (b - a) * 10 ^ a := by rw [← Nat.pow_add]; congr 1; omega
  rw [hb, ← Nat.mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by decide)) h

/-- The representation `TdRep` describes is unique. -/
theorem tdRep_unique {T : Nat} {E0 ideal : Int} {m k m0 k0}
    (h : TdRep T E0 ideal m k) (h0 : TdRep T E0 ideal m0 k0) : m = m0 ∧ k = k0 := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨b1, b2, b3⟩ := h0
  have hmm := a2.trans b2.symm
  have hk : k = k0 := by
    by_cases hE : E0 < ideal
    · simp only [if_pos hE] at a3 b3
      obtain ⟨a4, a5⟩ := a3
      obtain ⟨b4, b5⟩ := b3
      refine Classical.byContradiction fun hne => ?_
      rcases Nat.lt_or_gt_of_ne (show (k - E0).toNat ≠ (k0 - E0).toNat by omega) with hl | hl
      · have := pow_cancel hmm (Nat.le_of_lt hl)
        have hm : m % 10 = 0 := by
          rw [this, Nat.mul_mod, pow_mod_ten (show 1 ≤ (k0 - E0).toNat - (k - E0).toNat by omega)]
          simp
        rcases a5 with a5 | a5
        · omega
        · exact a5 hm
      · have := pow_cancel hmm.symm (Nat.le_of_lt hl)
        have hm : m0 % 10 = 0 := by
          rw [this, Nat.mul_mod, pow_mod_ten (show 1 ≤ (k - E0).toNat - (k0 - E0).toNat by omega)]
          simp
        rcases b5 with b5 | b5
        · omega
        · exact b5 hm
    · simp only [if_neg hE] at a3 b3
      omega
  subst hk
  exact ⟨Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by decide)) hmm, rfl⟩

/-! ## `__truediv__`, exactly -/

/-- `__truediv__` (_pydecimal.py:1369-1426) on every pair of finite operands with a non-zero
divisor, for every context with `prec ≥ 1`. With `s` the exclusive or of the signs, `shift`
(`tdShift`), the working exponent `E0 = ea - eb - shift`, and `N`, `D` (`tdNum`, `tdDen`) the
integers with `a / b = ±(N/D)·10^E0`, `T = N // D`:

* `_WorkRep`'s int/str-limit `ValueError` (`value has N digits`) for a coefficient of more than
  4300 digits, the dividend's first;
* `T` has more than `prec` digits;
* when `D` does not divide `N`, the exact quotient lies strictly between `T·10^E0` and
  `(T+1)·10^E0`; `str(coeff)` raises the int/str-limit `ValueError` when `T` has more than 4300
  digits; otherwise the result is `fixSpec` of every decimal `X·10^(E0-1-d)` strictly between those
  bounds, the truncated quotient with an inexact digit `10T + 1` (d = 0) among them: since `_fix`
  drops at least two of its digits, every such decimal rounds alike, and so does the exact quotient,
  which is the exact rational quotient rounded into the context (overflow and the subnormal range
  included);
* when `D` divides `N`, the exact quotient `m·10^k` at the exponent closest to the ideal `ea - eb`
  (`TdRep`, which has one solution), through `str()` and `_fix`;
* a zero dividend: the zero `_fix` makes of `±0·10^(ea-eb)`;
* a NaN operand: `_check_nans` (`nanSpec2`).

`TruedivSpecials` states the remaining operand pairs: `x/0`, `0/0`, infinities. -/
def TruedivExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal), 1 ≤ c.prec →
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int), ca ≠ 0 → cb ≠ 0 →
      let s := sa != sb
      let E0 := ea - eb - tdShift c.prec ca cb
      let N := tdNum c.prec ca cb
      let D := tdDen c.prec ca cb
      let T := N / D
      (maxStrDigits < numDigits ca →
        (truediv c (.fin sa ca ea) (.fin sb cb eb)).run fl = .error (.valueError (limitToIntMsg (numDigits ca)))) ∧
      (numDigits ca ≤ maxStrDigits → maxStrDigits < numDigits cb →
        (truediv c (.fin sa ca ea) (.fin sb cb eb)).run fl = .error (.valueError (limitToIntMsg (numDigits cb)))) ∧
      (numDigits ca ≤ maxStrDigits → numDigits cb ≤ maxStrDigits →
        10 ^ c.prec ≤ T ∧
        (N % D ≠ 0 → T * D < N ∧ N < (T + 1) * D ∧
          (maxStrDigits < numDigits T →
            (truediv c (.fin sa ca ea) (.fin sb cb eb)).run fl = .error (.valueError limitToStrMsg)) ∧
          (numDigits T ≤ maxStrDigits → ∀ (d X : Nat), 10 ^ (d + 1) * T < X → X < 10 ^ (d + 1) * (T + 1) →
            (truediv c (.fin sa ca ea) (.fin sb cb eb)).run fl = fixSpec c s X (E0 - 1 - d) fl)) ∧
        (N % D = 0 → (∃ m k, TdRep T E0 (ea - eb) m k) ∧ ∀ m k, TdRep T E0 (ea - eb) m k →
          (truediv c (.fin sa ca ea) (.fin sb cb eb)).run fl =
            if maxStrDigits < numDigits m then .error (.valueError limitToStrMsg) else fixSpec c s m k fl))) ∧
    (∀ (sa : Bool) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int), cb ≠ 0 →
      (truediv c (.fin sa 0 ea) (.fin sb cb eb)).run fl = (fix c (.fin (sa != sb) 0 (ea - eb))).run fl) ∧
    (∀ a b : Dec, nanKind a ≠ 0 ∨ nanKind b ≠ 0 → (truediv c a b).run fl = nanSpec2 c a b fl)

theorem truedivExact_proven : TruedivExact := by
  intro c fl hp
  refine ⟨fun sa ca ea sb cb eb ha hb => ?_, fun sa ea sb cb eb hb => truediv_zero_run c sa ea sb cb eb fl hb,
    fun a b h => truediv_nan_run c fl a b h⟩
  dsimp only
  rw [truediv_fin_run c sa ca ea sb cb eb fl hb]
  refine ⟨fun h1 => by rw [truedivFin_err_a c sa ca ea sb cb eb ha h1],
    fun h1 h2 => by rw [truedivFin_err_b c sa ca ea sb cb eb ha h1 h2], fun h1 h2 => ?_⟩
  rw [truedivFin_eval c sa ca ea sb cb eb ha h1 h2]
  have hdig := truediv_digits c.prec ca cb ha hb (tdShift c.prec ca cb) rfl
  have hD0 : 0 < tdDen c.prec ca cb := by
    unfold tdDen; split
    · exact Nat.pos_of_ne_zero hb
    · exact Nat.mul_pos (Nat.pos_of_ne_zero hb) (Nat.pow_pos (by decide))
  have hT : 10 ^ c.prec ≤ tdNum c.prec ca cb / tdDen c.prec ca cb := (Nat.le_div_iff_mul_le hD0).mpr (by
    unfold tdNum tdDen; exact hdig)
  generalize ea - eb - tdShift c.prec ca cb = E0
  generalize tdNum c.prec ca cb = N at hT ⊢
  generalize tdDen c.prec ca cb = D at hT hD0 ⊢
  generalize hTd : N / D = T at hT ⊢
  have hp10 : 10 ≤ 10 ^ c.prec := by
    have := Nat.pow_le_pow_right (show 0 < 10 by decide) hp
    simpa using this
  have hT10 : 10 ≤ T := by omega
  have hT0 : T ≠ 0 := by omega
  have hndT : c.prec < numDigits T := by
    rcases Nat.lt_or_ge c.prec (numDigits T) with h | h
    · exact h
    · have := (numDigits_le_iff (n := T) (show 0 < c.prec by omega)).mp h
      omega
  refine ⟨hT, fun hr => ?_, fun hr => ?_⟩
  · have hdm := Nat.div_add_mod N D
    have hml := Nat.mod_lt N hD0
    rw [hTd] at hdm
    have hTD : T * D = D * T := Nat.mul_comm ..
    have hsucc : (T + 1) * D = T * D + D := Nat.succ_mul ..
    refine ⟨by omega, by omega, fun hl => ?_, fun hl d X hx1 hx2 => ?_⟩
    · simp only [hr, ne_eq, not_false_eq_true, ↓reduceIte, numDigits_bump T hT10]
      exact if_pos hl
    · simp only [hr, ne_eq, not_false_eq_true, ↓reduceIte, numDigits_bump T hT10,
        show ¬ maxStrDigits < numDigits T by omega]
      have hb0 : bump T ≠ 0 := by unfold bump; split <;> omega
      rw [fixExact_fin c (sa != sb) (bump T) E0 fl hp hb0]
      have e1 := fixSpec_sticky c (sa != sb) (bump T) (10 * T + 1) 1 E0 fl
        (by rw [numDigits_bump T hT10]; exact hndT)
        (by rw [numDigits_bump T hT10]; exact numDigits_ten_mul_add T 1 hT0 (by decide)) (sticky_bump T)
      have e2 := fixSpec_sticky2 c (sa != sb) (10 * T + 1) X d (E0 - 1) fl
        (by rw [numDigits_ten_mul_add T 1 hT0 (by decide)]; omega)
        (by rw [numDigits_ten_mul_add T 1 hT0 (by decide)]; exact numDigits_between T X d hT0 hx1 hx2)
        (sticky_between T X d hx1 hx2)
      rw [e2, ← e1]
      rfl
  · have hstrip := tdRep_strip T E0 (ea - eb)
    refine ⟨⟨_, _, hstrip⟩, fun m k hmk => ?_⟩
    obtain ⟨rfl, rfl⟩ := tdRep_unique hmk hstrip
    simp only [hr, ne_eq, not_true_eq_false, ↓reduceIte]
    split
    · rfl
    · have hm0 : (stripIdeal T E0 (ea - eb) (ea - eb - E0).toNat).1 ≠ 0 := by
        intro h0
        have := hstrip.2.1
        rw [h0, Nat.zero_mul] at this
        omega
      exact fixExact_fin c (sa != sb) _ _ fl hp hm0

/-! ## `_divide`, exactly -/

/-- `_divide` (_pydecimal.py:1428-1464) for a finite dividend and a non-zero finite divisor, for
every context, on every outcome. With `s` the exclusive or of the signs, `ie = min(ea, eb)`, the
operands as integers `X`, `Y` at exponent `ie` (`scaled`) and the adjusted-exponent gap `gap`:
a zero dividend, or `gap <= -2`, gives the zero quotient and the dividend itself at `ie`; a gap
above `prec` gives `DivisionImpossible` (InvalidOperation, a NaN pair); otherwise `_WorkRep`'s
int/str-limit `ValueError` for a coefficient of more than 4300 digits, and then whatever
`_is_less_than_pow10a_use_str(X // Y, prec)` (:1454) decides: its exception (the OverflowError of a
`prec` too large for a double), `DivisionImpossible` when it says the quotient is too large, and the
quotient `X // Y` at exponent 0 with the remainder `X % Y` at `ie` when it says it fits, through
`str()` of each (the int/str-limit `ValueError`). The helper is the code's own decision:
`Pow10BandExact` pins it in the band it computes `str(q)`, and decimal-pow10-correct refutes it at
prec 355861594 (decimal-pydecimal-pow10-float-misfire), where `//`, `%` and `divmod` therefore
raise DivisionImpossible for a quotient that fits. -/
def DivideExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int),
    cb ≠ 0 →
    let s := sa != sb
    let ie := min ea eb
    let X := (scaled ca ea cb eb).1
    let Y := (scaled ca ea cb eb).2
    let gap := adjustedD ca ea - adjustedD cb eb
    ((ca = 0 ∨ gap ≤ -2) → (divideD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
      .ok ((.fin s 0 0, .fin sa (ca * 10 ^ (ea - ie).toNat) ie), fl)) ∧
    (ca ≠ 0 → -2 < gap → (c.prec : Int) < gap →
      (divideD c (.fin sa ca ea) (.fin sb cb eb)).run fl = afterSig c .invalidOperation fl (nanD, nanD)) ∧
    (ca ≠ 0 → -2 < gap → gap ≤ c.prec →
      (maxStrDigits < numDigits ca → (divideD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
        .error (.valueError (limitToIntMsg (numDigits ca)))) ∧
      (numDigits ca ≤ maxStrDigits → maxStrDigits < numDigits cb →
        (divideD c (.fin sa ca ea) (.fin sb cb eb)).run fl = .error (.valueError (limitToIntMsg (numDigits cb)))) ∧
      (numDigits ca ≤ maxStrDigits → numDigits cb ≤ maxStrDigits →
        (∀ e, isLessThanPow10aUseStr (X / Y) c.prec = .error e →
          (divideD c (.fin sa ca ea) (.fin sb cb eb)).run fl = .error e) ∧
        (∀ st, isLessThanPow10aUseStr (X / Y) c.prec = .ok (false, st) →
          (divideD c (.fin sa ca ea) (.fin sb cb eb)).run fl = afterSig c .invalidOperation fl (nanD, nanD)) ∧
        (∀ st, isLessThanPow10aUseStr (X / Y) c.prec = .ok (true, st) →
          (divideD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
            if st = false ∧ maxStrDigits < numDigits (X / Y) then .error (.valueError limitToStrMsg)
            else if maxStrDigits < numDigits (X % Y) then .error (.valueError limitToStrMsg)
            else .ok ((.fin s (X / Y) 0, .fin sa (X % Y) ie), fl))))

theorem strLimit_then {β : Type} (n : Nat) (k : DM β) (fl : List Signal) :
    (liftPy (strLimit n) >>= fun _ => k).run fl =
      if maxStrDigits < numDigits n then .error (.valueError limitToStrMsg) else k.run fl := by
  rw [liftPy_run]
  unfold strLimit
  by_cases h : numDigits n > maxStrDigits
  · simp [h]
  · simp [h, show ¬ maxStrDigits < numDigits n by omega]

theorem invalid_pair_run (c : Ctx) (fl : List Signal) :
    (do let ans ← invalid c; pure (ans, ans) : DM (Dec × Dec)).run fl =
      afterSig c .invalidOperation fl (nanD, nanD) := by
  simp only [invalid, bind_assoc, pure_bind]
  exact raiseSig_then c .invalidOperation fl _

theorem divideExact_proven : DivideExact := by
  intro c fl sa ca ea sb cb eb hb
  dsimp only
  have hz2 : isZero (.fin sb cb eb) = false := isZero_fin sb cb eb hb
  refine ⟨fun h => ?_, fun ha hg hp => ?_, fun ha hg hp => ?_⟩
  · rcases h with rfl | h
    · simp [divideD, decBool, isZero, rescale, Dec.neg, isinfinity, expOf, pure, StateT.pure, Except.pure,
        liftPy, StateT.run, bind, StateT.bind, Except.bind, Functor.map, Except.map]
    · by_cases ha : ca = 0
      · subst ha
        simp [divideD, decBool, isZero, rescale, Dec.neg, isinfinity, expOf, pure, StateT.pure, Except.pure,
          liftPy, StateT.run, bind, StateT.bind, Except.bind, Functor.map, Except.map]
      · have hza : isZero (.fin sa ca ea) = false := isZero_fin sa ca ea ha
        have hh : adjustedD ca ea - adjustedD cb eb ≤ -2 := h
        simp [divideD, decBool, hza, isinfinity, expOf, Dec.adjusted, hh, Dec.neg,
          rescale_pad sa ca ea _ _ ha (Int.min_le_left ea eb), pure, StateT.pure, Except.pure, liftPy,
          StateT.run, bind, StateT.bind, Except.bind, Functor.map, Except.map]
  · have hza : isZero (.fin sa ca ea) = false := isZero_fin sa ca ea ha
    have g1 : ¬ adjustedD ca ea - adjustedD cb eb ≤ -2 := by omega
    have g2 : ¬ adjustedD ca ea - adjustedD cb eb ≤ (c.prec : Int) := by omega
    have := invalid_pair_run c fl
    simp only [divideD, decBool, hza, isinfinity, expOf, Dec.adjusted, Bool.not_false, Bool.not_true,
      ne_eq, not_true_eq_false, decide_false, Bool.false_or, g1, g2, ↓reduceIte, decide_eq_true_eq,
      Bool.false_eq_true, Dec.neg]
    exact this
  · have hza : isZero (.fin sa ca ea) = false := isZero_fin sa ca ea ha
    have g1 : ¬ adjustedD ca ea - adjustedD cb eb ≤ -2 := by omega
    have g2 : adjustedD ca ea - adjustedD cb eb ≤ (c.prec : Int) := hp
    simp only [divideD, decBool, hza, isinfinity, expOf, Dec.adjusted, Bool.not_false, Bool.not_true,
      ne_eq, not_true_eq_false, decide_false, Bool.false_or, g1, g2, ↓reduceIte, decide_eq_true_eq,
      Bool.false_eq_true, Dec.neg]
    refine ⟨fun h1 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
    · have : workRep (.fin sa ca ea) = .error (.valueError (limitToIntMsg (numDigits ca))) := by
        simp [workRep, intLimit, show numDigits ca > maxStrDigits from h1, bind, Except.bind]
      rw [liftPy_err_run _ fl this]
    · have e1 : workRep (.fin sa ca ea) = .ok (sa, ca, ea) := by
        simp [workRep, intLimit, show ¬ numDigits ca > maxStrDigits by omega, bind, Except.bind, pure,
          Except.pure]
      have e2 : workRep (.fin sb cb eb) = .error (.valueError (limitToIntMsg (numDigits cb))) := by
        simp [workRep, intLimit, show numDigits cb > maxStrDigits from h2, bind, Except.bind]
      rw [liftPy_ok_run _ fl e1, liftPy_err_run _ fl e2]
    · have e1 : workRep (.fin sa ca ea) = .ok (sa, ca, ea) := by
        simp [workRep, intLimit, show ¬ numDigits ca > maxStrDigits by omega, bind, Except.bind, pure,
          Except.pure]
      have e2 : workRep (.fin sb cb eb) = .ok (sb, cb, eb) := by
        simp [workRep, intLimit, show ¬ numDigits cb > maxStrDigits by omega, bind, Except.bind, pure,
          Except.pure]
      rw [liftPy_ok_run _ fl e1, liftPy_ok_run _ fl e2]
      refine ⟨fun e he => ?_, fun st he => ?_, fun st he => ?_⟩
      · rw [liftPy_err_run _ fl he]
      · rw [liftPy_ok_run _ fl he]
        simpa using invalid_pair_run c fl
      · rw [liftPy_ok_run _ fl he]
        cases st with
        | true =>
          simp only [↓reduceIte, Bool.true_eq_false, false_and]
          rw [show (liftPy (Except.ok () : Py Unit) : DM Unit) = pure () from rfl, pure_bind, strLimit_then]
          rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, true_and]
          rw [strLimit_then]
          by_cases hq : maxStrDigits < numDigits ((scaled ca ea cb eb).1 / (scaled ca ea cb eb).2)
          · simp only [hq, ↓reduceIte]
          · simp only [hq, ↓reduceIte]
            rw [strLimit_then]
            rfl

/-! ## `%` and `divmod`, exactly -/

theorem modD_fin (c : Ctx) (fl : List Signal) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat)
    (eb : Int) (hb : cb ≠ 0) :
    (modD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
      match (divideD c (.fin sa ca ea) (.fin sb cb eb)).run fl with
      | .ok (qr, fl') => (fix c qr.2).run fl'
      | .error e => .error e := by
  have hz2 : isZero (.fin sb cb eb) = false := isZero_fin sb cb eb hb
  have hd : decBool (.fin sb cb eb) = true := by simp [decBool, hz2]
  simp only [modD, checkNans, isinfinity, hd, pure_bind, ne_eq, not_true_eq_false, ↓reduceIte,
    Bool.not_true, Bool.false_eq_true]
  simp only [StateT.run, bind, StateT.bind, Except.bind]
  cases divideD c (.fin sa ca ea) (.fin sb cb eb) fl <;> rfl

theorem divmodD_fin (c : Ctx) (fl : List Signal) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat)
    (eb : Int) (hb : cb ≠ 0) :
    (divmodD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
      match (divideD c (.fin sa ca ea) (.fin sb cb eb)).run fl with
      | .ok (qr, fl') => ((fix c qr.2).run fl').map (fun p => ((qr.1, p.1), p.2))
      | .error e => .error e := by
  have hz2 : isZero (.fin sb cb eb) = false := isZero_fin sb cb eb hb
  have hd : decBool (.fin sb cb eb) = true := by simp [decBool, hz2]
  simp only [divmodD, checkNans, isinfinity, hd, pure_bind, ne_eq, not_true_eq_false, ↓reduceIte,
    Bool.not_true, Bool.false_eq_true]
  simp only [StateT.run, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure]
  cases divideD c (.fin sa ca ea) (.fin sb cb eb) fl with
  | error e => rfl
  | ok v =>
    simp only
    cases fix c v.1.2 v.2 <;> rfl

theorem fix_nanD (c : Ctx) (fl : List Signal) : (fix c nanD).run fl = .ok (nanD, fl) := by
  simp [fix, nanD, fixNan_spec]; rfl

/-- `%` (_pydecimal.py:1516-1541) on every operand pair, for every context: a NaN operand gives
`_check_nans`; `INF % x`, `x % 0` and `0 % 0` are InvalidOperation (`DivisionUndefined` is
InvalidOperation too) with a NaN; `x % INF` is `x` through `_fix`; and for a finite non-zero divisor
the remainder `_divide` makes (`DivideExact`, the helper's verdict included) through `_fix`, with
`_divide`'s exceptions. -/
def ModExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal),
    (∀ a b : Dec, nanKind a ≠ 0 ∨ nanKind b ≠ 0 → (modD c a b).run fl = nanSpec2 c a b fl) ∧
    (∀ (s : Bool) (b : Dec), nanKind b = 0 → (modD c (.inf s) b).run fl = afterSig c .invalidOperation fl nanD) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (eb : Int),
      (modD c (.fin sa ca ea) (.fin sb 0 eb)).run fl = afterSig c .invalidOperation fl nanD) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool),
      (modD c (.fin sa ca ea) (.inf sb)).run fl = (fix c (.fin sa ca ea)).run fl) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int), cb ≠ 0 →
      let ie := min ea eb
      let X := (scaled ca ea cb eb).1
      let Y := (scaled ca ea cb eb).2
      let gap := adjustedD ca ea - adjustedD cb eb
      ((ca = 0 ∨ gap ≤ -2) → (modD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
        (fix c (.fin sa (ca * 10 ^ (ea - ie).toNat) ie)).run fl) ∧
      (ca ≠ 0 → -2 < gap → (c.prec : Int) < gap →
        (modD c (.fin sa ca ea) (.fin sb cb eb)).run fl = afterSig c .invalidOperation fl nanD) ∧
      (ca ≠ 0 → -2 < gap → gap ≤ c.prec →
        (maxStrDigits < numDigits ca → (modD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
          .error (.valueError (limitToIntMsg (numDigits ca)))) ∧
        (numDigits ca ≤ maxStrDigits → maxStrDigits < numDigits cb →
          (modD c (.fin sa ca ea) (.fin sb cb eb)).run fl = .error (.valueError (limitToIntMsg (numDigits cb)))) ∧
        (numDigits ca ≤ maxStrDigits → numDigits cb ≤ maxStrDigits →
          (∀ e, isLessThanPow10aUseStr (X / Y) c.prec = .error e →
            (modD c (.fin sa ca ea) (.fin sb cb eb)).run fl = .error e) ∧
          (∀ st, isLessThanPow10aUseStr (X / Y) c.prec = .ok (false, st) →
            (modD c (.fin sa ca ea) (.fin sb cb eb)).run fl = afterSig c .invalidOperation fl nanD) ∧
          (∀ st, isLessThanPow10aUseStr (X / Y) c.prec = .ok (true, st) →
            (modD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
              if st = false ∧ maxStrDigits < numDigits (X / Y) then .error (.valueError limitToStrMsg)
              else if maxStrDigits < numDigits (X % Y) then .error (.valueError limitToStrMsg)
              else (fix c (.fin sa (X % Y) ie)).run fl))))

theorem afterSig_fix (c : Ctx) (fl : List Signal) :
    (match afterSig c .invalidOperation fl (nanD, nanD) with
      | .ok (qr, fl') => (fix c qr.2).run fl'
      | .error e => .error e) = afterSig c .invalidOperation fl nanD := by
  by_cases h : Signal.invalidOperation ∈ c.traps
  · simp [afterSig, h]
  · simp only [afterSig, h, ↓reduceIte]
    exact fix_nanD c _

theorem modExact_proven : ModExact := by
  intro c fl
  refine ⟨fun a b h => ?_, fun s b hb => ?_, fun sa ca ea sb eb => ?_, fun sa ca ea sb => ?_,
    fun sa ca ea sb cb eb hb => ?_⟩
  · rcases a with ⟨sa, ca, ea⟩ | na | ⟨na, ssa, pa⟩ <;> rcases b with ⟨sb, cb, eb⟩ | nb | ⟨nb, ssb, pb⟩ <;>
      first
      | (simp [nanKind] at h; done)
      | (simp only [modD]; exact checkNans_return c _ _ fl _ (fun d => rfl) h)
  · rcases b with ⟨sb, cb, eb⟩ | nb | ⟨nb, ssb, pb⟩
    · cases s <;> simpa [modD, checkNans, isinfinity, nanD] using invalid_run c fl
    · cases s <;> simpa [modD, checkNans, isinfinity, nanD] using invalid_run c fl
    · cases ssb <;> simp [nanKind] at hb
  · simpa [modD, checkNans, isinfinity, decBool, isZero, nanD] using invalid_run c fl
  · cases sb <;> cases ca <;>
      simp [modD, checkNans, isinfinity, decBool, isZero, divideD, expOf, rescale, liftPy, StateT.run, bind,
        StateT.bind, Except.bind, pure, StateT.pure, Except.pure, Functor.map, Except.map]
  · have DE := divideExact_proven c fl sa ca ea sb cb eb hb
    dsimp only at DE ⊢
    rw [modD_fin c fl sa ca ea sb cb eb hb]
    obtain ⟨d1, d2, d3⟩ := DE
    refine ⟨fun h => by rw [d1 h], fun ha hg hp => by rw [d2 ha hg hp]; exact afterSig_fix c fl,
      fun ha hg hp => ?_⟩
    obtain ⟨d4, d5, d6⟩ := d3 ha hg hp
    refine ⟨fun h1 => by rw [d4 h1], fun h1 h2 => by rw [d5 h1 h2], fun h1 h2 => ?_⟩
    obtain ⟨d7, d8, d9⟩ := d6 h1 h2
    refine ⟨fun e he => by rw [d7 e he], fun st he => by rw [d8 st he]; exact afterSig_fix c fl,
      fun st he => ?_⟩
    rw [d9 st he]
    by_cases g1 : st = false ∧ maxStrDigits < numDigits ((scaled ca ea cb eb).1 / (scaled ca ea cb eb).2)
    · simp only [if_pos g1]
    · simp only [if_neg g1]
      by_cases g2 : maxStrDigits < numDigits ((scaled ca ea cb eb).1 % (scaled ca ea cb eb).2)
      · simp only [if_pos g2]
      · simp only [if_neg g2]

/-- `checkNans` then returning the NaN twice, as `__divmod__` does (_pydecimal.py:1484-1486). -/
theorem checkNans_return2 (c : Ctx) (a b : Dec) (fl : List Signal) (k : Option Dec → DM (Dec × Dec))
    (hk : ∀ d, k (some d) = pure (d, d)) (h : nanKind a ≠ 0 ∨ nanKind b ≠ 0) :
    (checkNans c a (some b) >>= k).run fl = (nanSpec2 c a b fl).map (fun p => ((p.1, p.1), p.2)) := by
  have sig : ∀ x, ((do raiseSig c .invalidOperation; (pure (some x) : DM (Option Dec))) >>= k).run fl =
      afterSig c .invalidOperation fl (x, x) := by
    intro x; rw [bind_assoc]; simp only [pure_bind, hk]; exact raiseSig_then c _ fl (x, x)
  have ok : ∀ x, ((pure (some x) : DM (Option Dec)) >>= k).run fl = .ok ((x, x), fl) := by
    intro x; rw [pure_bind, hk]; rfl
  rcases a with ⟨na, ca, ea⟩ | na | ⟨na, sa, pa⟩ <;> rcases b with ⟨nb, cb, eb⟩ | nb | ⟨nb, sb, pb⟩ <;>
    (try cases sa) <;> (try cases sb) <;>
    first
    | (simp [nanKind] at h; done)
    | (simp only [checkNans]
       first
       | (rw [sig]
          by_cases ht : Signal.invalidOperation ∈ c.traps <;>
            simp [afterSig, ht, nanSpec2, nanKind, quietNaN, fixNan_spec, Except.map])
       | (rw [ok]; simp [nanSpec2, nanKind, quietNaN, fixNan_spec, Except.map]))

/-- `divmod` (_pydecimal.py:1473-1507) on every operand pair, for every context: a NaN operand gives
`_check_nans`'s NaN twice; `divmod(INF, INF)` and `divmod(0, 0)` InvalidOperation twice; `divmod(INF, x)`
the signed infinity and InvalidOperation; `divmod(x, 0)` DivisionByZero's signed infinity, then
InvalidOperation (the first trapped one raising); `divmod(x, INF)` a signed zero and `x` through
`_fix`; and for a finite non-zero divisor `_divide`'s quotient (`DivideExact`, the helper's verdict
included) with its remainder through `_fix`. -/
def DivmodExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal),
    (∀ a b : Dec, nanKind a ≠ 0 ∨ nanKind b ≠ 0 →
      (divmodD c a b).run fl = (nanSpec2 c a b fl).map (fun p => ((p.1, p.1), p.2))) ∧
    (∀ s t : Bool, (divmodD c (.inf s) (.inf t)).run fl = afterSig c .invalidOperation fl (nanD, nanD)) ∧
    (∀ (s sb : Bool) (cb : Nat) (eb : Int),
      (divmodD c (.inf s) (.fin sb cb eb)).run fl = afterSig c .invalidOperation fl (.inf (s != sb), nanD)) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (eb : Int), ca ≠ 0 →
      (divmodD c (.fin sa ca ea) (.fin sb 0 eb)).run fl =
        if Signal.divisionByZero ∈ c.traps then .error (.named "DivisionByZero" "~")
        else afterSig c .invalidOperation (addFlag .divisionByZero fl) (.inf (sa != sb), nanD)) ∧
    (∀ (sa : Bool) (ea : Int) (sb : Bool) (eb : Int),
      (divmodD c (.fin sa 0 ea) (.fin sb 0 eb)).run fl = afterSig c .invalidOperation fl (nanD, nanD)) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool),
      (divmodD c (.fin sa ca ea) (.inf sb)).run fl =
        ((fix c (.fin sa ca ea)).run fl).map (fun p => ((.fin (sa != sb) 0 0, p.1), p.2))) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int), cb ≠ 0 →
      let s := sa != sb
      let ie := min ea eb
      let X := (scaled ca ea cb eb).1
      let Y := (scaled ca ea cb eb).2
      let gap := adjustedD ca ea - adjustedD cb eb
      ((ca = 0 ∨ gap ≤ -2) → (divmodD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
        ((fix c (.fin sa (ca * 10 ^ (ea - ie).toNat) ie)).run fl).map (fun p => ((.fin s 0 0, p.1), p.2))) ∧
      (ca ≠ 0 → -2 < gap → (c.prec : Int) < gap →
        (divmodD c (.fin sa ca ea) (.fin sb cb eb)).run fl = afterSig c .invalidOperation fl (nanD, nanD)) ∧
      (ca ≠ 0 → -2 < gap → gap ≤ c.prec →
        (maxStrDigits < numDigits ca → (divmodD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
          .error (.valueError (limitToIntMsg (numDigits ca)))) ∧
        (numDigits ca ≤ maxStrDigits → maxStrDigits < numDigits cb →
          (divmodD c (.fin sa ca ea) (.fin sb cb eb)).run fl = .error (.valueError (limitToIntMsg (numDigits cb)))) ∧
        (numDigits ca ≤ maxStrDigits → numDigits cb ≤ maxStrDigits →
          (∀ e, isLessThanPow10aUseStr (X / Y) c.prec = .error e →
            (divmodD c (.fin sa ca ea) (.fin sb cb eb)).run fl = .error e) ∧
          (∀ st, isLessThanPow10aUseStr (X / Y) c.prec = .ok (false, st) →
            (divmodD c (.fin sa ca ea) (.fin sb cb eb)).run fl = afterSig c .invalidOperation fl (nanD, nanD)) ∧
          (∀ st, isLessThanPow10aUseStr (X / Y) c.prec = .ok (true, st) →
            (divmodD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
              if st = false ∧ maxStrDigits < numDigits (X / Y) then .error (.valueError limitToStrMsg)
              else if maxStrDigits < numDigits (X % Y) then .error (.valueError limitToStrMsg)
              else ((fix c (.fin sa (X % Y) ie)).run fl).map (fun p => ((.fin s (X / Y) 0, p.1), p.2))))))

theorem afterSig_fix2 (c : Ctx) (fl : List Signal) :
    (match afterSig c .invalidOperation fl (nanD, nanD) with
      | .ok (qr, fl') => ((fix c qr.2).run fl').map (fun p => ((qr.1, p.1), p.2))
      | .error e => .error e) = afterSig c .invalidOperation fl (nanD, nanD) := by
  by_cases h : Signal.invalidOperation ∈ c.traps
  · simp [afterSig, h]
  · simp only [afterSig, h, ↓reduceIte, fix_nanD]
    rfl

theorem invalid_pair_run' (c : Ctx) (fl : List Signal) :
    (invalid c >>= fun ans => (pure (ans, ans) : DM (Dec × Dec))).run fl =
      afterSig c .invalidOperation fl (nanD, nanD) := invalid_pair_run c fl

theorem divmodExact_proven : DivmodExact := by
  intro c fl
  refine ⟨fun a b h => ?_, fun s t => ?_, fun s sb cb eb => ?_, fun sa ca ea sb eb ha => ?_,
    fun sa ea sb eb => ?_, fun sa ca ea sb => ?_, fun sa ca ea sb cb eb hb => ?_⟩
  · rcases a with ⟨sa, ca, ea⟩ | na | ⟨na, ssa, pa⟩ <;> rcases b with ⟨sb, cb, eb⟩ | nb | ⟨nb, ssb, pb⟩ <;>
      first
      | (simp [nanKind] at h; done)
      | (simp only [divmodD]; exact checkNans_return2 c _ _ fl _ (fun d => rfl) h)
  · cases s <;> cases t <;>
      simpa [divmodD, checkNans, isinfinity, nanD] using invalid_pair_run' c fl
  · have hv : (do let r ← invalid c; (pure (Dec.inf (s != sb), r) : DM (Dec × Dec))).run fl =
        afterSig c .invalidOperation fl (.inf (s != sb), nanD) := by
      simp only [invalid, bind_assoc, pure_bind]
      exact raiseSig_then c .invalidOperation fl _
    cases s <;> simpa [divmodD, checkNans, isinfinity, Dec.neg] using hv
  · have hza : isZero (.fin sa ca ea) = false := isZero_fin sa ca ea ha
    have hd : decBool (.fin sa ca ea) = true := by simp [decBool, hza]
    have hd0 : decBool (.fin sb 0 eb) = false := rfl
    simp only [divmodD, checkNans, isinfinity, hd, hd0, pure_bind, ne_eq, not_true_eq_false, ↓reduceIte,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Dec.neg, divByZero_eq, invalid, bind_assoc]
    rw [raiseSig_bind]
    by_cases h : Signal.divisionByZero ∈ c.traps
    · simp only [h, ↓reduceIte]
      rfl
    · simp only [h, ↓reduceIte, pure_bind]
      exact raiseSig_then c .invalidOperation _ _
  · simpa [divmodD, checkNans, isinfinity, decBool, isZero, nanD] using invalid_pair_run' c fl
  · cases sb <;> cases ca <;>
      simp [divmodD, checkNans, isinfinity, decBool, isZero, divideD, expOf, rescale, liftPy, StateT.run, bind,
        StateT.bind, Except.bind, pure, StateT.pure, Except.pure, Functor.map, Except.map, Dec.neg] <;>
      (cases fix c _ fl <;> rfl)
  · have DE := divideExact_proven c fl sa ca ea sb cb eb hb
    dsimp only at DE ⊢
    rw [divmodD_fin c fl sa ca ea sb cb eb hb]
    obtain ⟨d1, d2, d3⟩ := DE
    refine ⟨fun h => by rw [d1 h], fun ha hg hp => by rw [d2 ha hg hp]; exact afterSig_fix2 c fl,
      fun ha hg hp => ?_⟩
    obtain ⟨d4, d5, d6⟩ := d3 ha hg hp
    refine ⟨fun h1 => by rw [d4 h1], fun h1 h2 => by rw [d5 h1 h2], fun h1 h2 => ?_⟩
    obtain ⟨d7, d8, d9⟩ := d6 h1 h2
    refine ⟨fun e he => by rw [d7 e he], fun st he => by rw [d8 st he]; exact afterSig_fix2 c fl,
      fun st he => ?_⟩
    rw [d9 st he]
    by_cases g1 : st = false ∧ maxStrDigits < numDigits ((scaled ca ea cb eb).1 / (scaled ca ea cb eb).2)
    · simp only [if_pos g1]
    · simp only [if_neg g1]
      by_cases g2 : maxStrDigits < numDigits ((scaled ca ea cb eb).1 % (scaled ca ea cb eb).2)
      · simp only [if_pos g2]
      · simp only [if_neg g2]

end PyLean.Decimal
