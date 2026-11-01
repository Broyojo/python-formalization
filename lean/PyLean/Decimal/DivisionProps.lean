import PyLean.Decimal.ContextProps

/-!
The division family: `_divide`'s integer identity, the special values, `__truediv__`'s
integer core, and the agreement of `//` and `divmod` between the twins.
-/

namespace PyLean.Decimal

open PyLean

/-! ## Digit bounds on the scaled operands -/

theorem pow10_pos (k : Nat) : 0 < 10 ^ k := Nat.pow_pos (by decide)

/-- `self` below `other` by adjusted exponent: the scaled integer is smaller. -/
theorem scaled_lt (ca cb : Nat) (ea eb : Int) (hb : cb ≠ 0)
    (h : adjustedD ca ea < adjustedD cb eb) : (scaled ca ea cb eb).1 < (scaled ca ea cb eb).2 := by
  have h1 := lt_pow_numDigits ca
  have h2 := pow_numDigits_le hb
  have hna := numDigits_pos ca
  have hnb := numDigits_pos cb
  simp only [adjustedD] at h
  by_cases he : ea ≥ eb
  · simp only [scaled, if_pos he]
    obtain ⟨k, hk⟩ : ∃ k : Nat, ea - eb = k := ⟨(ea - eb).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hk' : (ea - eb).toNat = k := by omega
    rw [hk']
    calc ca * 10 ^ k < 10 ^ numDigits ca * 10 ^ k := Nat.mul_lt_mul_of_pos_right h1 (pow10_pos k)
      _ = 10 ^ (numDigits ca + k) := (Nat.pow_add ..).symm
      _ ≤ 10 ^ (numDigits cb - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ cb := h2
  · simp only [scaled, if_neg he]
    obtain ⟨k, hk⟩ : ∃ k : Nat, eb - ea = k := ⟨(eb - ea).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hk' : (eb - ea).toNat = k := by omega
    rw [hk']
    calc ca < 10 ^ numDigits ca := h1
      _ ≤ 10 ^ (numDigits cb - 1 + k) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 10 ^ (numDigits cb - 1) * 10 ^ k := Nat.pow_add ..
      _ ≤ cb * 10 ^ k := Nat.mul_le_mul_right _ h2

/-- `self` above `other` by more than `prec` adjusted exponents: the quotient has
more than `prec` digits. -/
theorem scaled_big (ca cb : Nat) (ea eb : Int) (prec : Nat) (ha : ca ≠ 0) (hb : cb ≠ 0)
    (h : adjustedD ca ea - adjustedD cb eb > prec) :
    10 ^ prec ≤ (scaled ca ea cb eb).1 / (scaled ca ea cb eb).2 := by
  have h1 := pow_numDigits_le ha
  have h2 := lt_pow_numDigits cb
  have hna := numDigits_pos ca
  have hnb := numDigits_pos cb
  have hcb : 0 < cb := Nat.pos_of_ne_zero hb
  simp only [adjustedD] at h
  by_cases he : ea ≥ eb
  · simp only [scaled, if_pos he]
    obtain ⟨k, hk⟩ : ∃ k : Nat, ea - eb = k := ⟨(ea - eb).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hk' : (ea - eb).toNat = k := by omega
    rw [hk', Nat.le_div_iff_mul_le hcb]
    calc 10 ^ prec * cb ≤ 10 ^ prec * 10 ^ numDigits cb := Nat.mul_le_mul_left _ (Nat.le_of_lt h2)
      _ = 10 ^ (prec + numDigits cb) := (Nat.pow_add ..).symm
      _ ≤ 10 ^ (numDigits ca - 1 + k) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 10 ^ (numDigits ca - 1) * 10 ^ k := Nat.pow_add ..
      _ ≤ ca * 10 ^ k := Nat.mul_le_mul_right _ h1
  · simp only [scaled, if_neg he]
    obtain ⟨k, hk⟩ : ∃ k : Nat, eb - ea = k := ⟨(eb - ea).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hk' : (eb - ea).toNat = k := by omega
    rw [hk', Nat.le_div_iff_mul_le (Nat.mul_pos hcb (pow10_pos k))]
    calc 10 ^ prec * (cb * 10 ^ k) ≤ 10 ^ prec * (10 ^ numDigits cb * 10 ^ k) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_of_lt h2))
      _ = 10 ^ (prec + (numDigits cb + k)) := by rw [Nat.pow_add, Nat.pow_add]
      _ ≤ 10 ^ (numDigits ca - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ ca := h1

/-- The second operand of `scaled` is positive. -/
theorem scaled_pos (ca cb : Nat) (ea eb : Int) (hb : cb ≠ 0) : 0 < (scaled ca ea cb eb).2 := by
  have hcb : 0 < cb := Nat.pos_of_ne_zero hb
  by_cases he : ea ≥ eb
  · simp only [scaled, if_pos he]; exact hcb
  · simp only [scaled, if_neg he]; exact Nat.mul_pos hcb (pow10_pos _)

/-! ## `_fix` of an integer in range -/

/-- A value at exponent 0 with at most `prec` digits is left alone by `_fix`, when the
context has room for it: `Emin ≤ 0` and `Emax ≥ prec - 1`. -/
theorem fix_int (c : Ctx) (s : Bool) (q : Nat) (fl : List Signal) (hq : numDigits q ≤ c.prec)
    (he : c.emin ≤ 0) (hx : (c.prec : Int) - 1 ≤ c.emax) :
    (fix c (.fin s q 0)).run fl = .ok (.fin s q 0, fl) := by
  have hn := numDigits_pos q
  have h1 : c.etiny ≤ 0 := by simp only [Ctx.etiny]; omega
  have h2 : 0 ≤ c.etop := by simp only [Ctx.etop]; omega
  simp only [fix]
  by_cases hc : q = 0
  · subst hc
    simp only [↓reduceIte]
    have h : min (max (0 : Int) c.etiny) (if c.clamp = true then c.etop else c.emax) = 0 := by
      cases hcl : c.clamp <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    simp only [h]
    rfl
  · simp only [hc, ↓reduceIte]
    have g1 : ¬((numDigits q : Int) + 0 - c.prec > c.etop) := by omega
    have g2 : ¬((numDigits q : Int) + 0 - c.prec < c.etiny) := by simp only [Ctx.etiny]; omega
    have g3 : ¬((0 : Int) < (numDigits q : Int) + 0 - c.prec) := by omega
    have g4 : ¬(c.clamp = true ∧ (0 : Int) > c.etop) := by omega
    simp only [if_neg g1, g2, decide_false, Bool.false_eq_true, ↓reduceIte, g3, if_neg g4]
    rfl

/-! ## `_divide` -/

/-- For finite non-zero operands, `_divide` returns the integer quotient and remainder of
the operands scaled to their lower exponent: `X = q·Y + r`, `0 ≤ r < Y`, the quotient at
exponent 0 with the sign of the product, the remainder at `min(ea, eb)` with the sign of
the dividend. If the quotient needs more than `prec` digits, both results are NaN and
InvalidOperation is set. This is the identity `x == (x // y) * y + x % y` of
Doc/library/decimal.rst:441. -/
def DivideCorrect : Prop :=
  ∀ (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (fl fl' : List Signal) (q r : Dec),
    ca ≠ 0 → cb ≠ 0 →
    (divideD c (.fin sa ca ea) (.fin sb cb eb)).run fl = .ok ((q, r), fl') →
    let X := (scaled ca ea cb eb).1
    let Y := (scaled ca ea cb eb).2
    (X / Y < 10 ^ c.prec ∧ q = .fin (sa != sb) (X / Y) 0 ∧ r = .fin sa (X % Y) (min ea eb) ∧ fl' = fl) ∨
    (10 ^ c.prec ≤ X / Y ∧ q = .nan false false 0 ∧ r = .nan false false 0 ∧
      Signal.invalidOperation ∈ fl')

theorem isZero_fin (s : Bool) (co : Nat) (e : Int) (h : co ≠ 0) : isZero (.fin s co e) = false := by
  cases co with
  | zero => exact absurd rfl h
  | succ n => rfl

theorem rescale_pad (s : Bool) (co : Nat) (e x : Int) (m : Rounding) (hc : co ≠ 0) (h : e ≥ x) :
    rescale (.fin s co e) x m = .ok (.fin s (co * 10 ^ (e - x).toNat) x) := by
  simp only [rescale, hc, ↓reduceIte, if_pos h]

theorem scaled_at_min (ca cb : Nat) (ea eb : Int) :
    ca * 10 ^ (ea - min ea eb).toNat = (scaled ca ea cb eb).1 := by
  by_cases he : ea ≥ eb
  · simp only [scaled, if_pos he]
    rw [Int.min_eq_right he]
  · have : min ea eb = ea := Int.min_eq_left (by omega)
    simp [scaled, if_neg he, this]

theorem invalid_run_ok {c : Ctx} {fl fl' : List Signal} {g : Dec → DM (Dec × Dec)}
    {r : Dec × Dec}
    (h : (invalid c >>= g).run fl = .ok (r, fl'))
    (hg : ∀ x, g x = pure (x, x)) :
    r = (.nan false false 0, .nan false false 0) ∧ Signal.invalidOperation ∈ fl' := by
  obtain ⟨x, fl1, h1, h2⟩ := bind_ok h
  obtain ⟨rfl, hm, _⟩ := invalid_ok h1
  rw [hg] at h2
  have := pure_ok h2
  cases this
  exact ⟨rfl, hm⟩

theorem divideCorrect_proven : DivideCorrect := by
  intro c sa ca ea sb cb eb fl fl' q r ha hb h X Y
  simp only [divideD, decBool, isZero_fin sa ca ea ha, isinfinity, expOf, Dec.adjusted, Dec.neg,
    Bool.not_false, Bool.not_true, ne_eq, not_true_eq_false, decide_false, Bool.false_or,
    ↓reduceIte, decide_eq_true_eq] at h
  have hY := scaled_pos ca cb ea eb hb
  split at h
  · rename_i h2'
    have h2 : adjustedD ca ea - adjustedD cb eb ≤ -2 := of_decide_eq_true h2'
    obtain ⟨d, fl1, h3, h4⟩ := bind_ok h
    obtain ⟨hr, rfl⟩ := liftPy_ok h3
    have h5 := pure_ok h4
    cases h5
    rw [rescale_pad sa ca ea _ _ ha (Int.min_le_left ea eb)] at hr
    cases hr
    have hlt : X < Y := scaled_lt ca cb ea eb hb (by omega)
    have h0 : X / Y = 0 := Nat.div_eq_of_lt hlt
    have hm : X % Y = X := Nat.mod_eq_of_lt hlt
    left
    refine ⟨by rw [h0]; exact pow10_pos _, by rw [h0], ?_, rfl⟩
    rw [hm, scaled_at_min ca cb ea eb]
  · rename_i h2'
    have h2 : ¬(adjustedD ca ea - adjustedD cb eb ≤ -2) := fun hc => h2' (decide_eq_true hc)
    by_cases h3 : adjustedD ca ea - adjustedD cb eb ≤ c.prec
    · rw [if_pos h3] at h
      obtain ⟨_, fl1, h4, h5⟩ := bind_ok h
      obtain ⟨_, rfl⟩ := liftPy_ok h4
      obtain ⟨_, fl2, h6, h7⟩ := bind_ok h5
      obtain ⟨_, rfl⟩ := liftPy_ok h6
      by_cases h8 : (scaled ca ea cb eb).1 / (scaled ca ea cb eb).2 < 10 ^ c.prec
      · rw [if_pos h8] at h7
        obtain ⟨_, fl3, h9, h10⟩ := bind_ok h7
        obtain ⟨_, rfl⟩ := liftPy_ok h9
        obtain ⟨_, fl4, h11, h12⟩ := bind_ok h10
        obtain ⟨_, rfl⟩ := liftPy_ok h11
        have h13 := pure_ok h12
        cases h13
        exact Or.inl ⟨h8, rfl, rfl, rfl⟩
      · rw [if_neg h8] at h7
        obtain ⟨hr, hm⟩ := invalid_run_ok h7 (fun _ => rfl)
        cases hr
        exact Or.inr ⟨Nat.le_of_not_gt h8, rfl, rfl, hm⟩
    · rw [if_neg h3] at h
      obtain ⟨hr, hm⟩ := invalid_run_ok h (fun _ => rfl)
      cases hr
      exact Or.inr ⟨scaled_big ca cb ea eb c.prec ha hb (by omega), rfl, rfl, hm⟩

/-- The special values of `/`, General Decimal Arithmetic, "divide": `x/0` is an infinity
with DivisionByZero, `0/0` and `inf/inf` are NaN with InvalidOperation, `inf/x` is an
infinity with no flag, and `x/inf` is a zero at `Etiny` with Clamped. -/
def TruedivSpecials : Prop :=
  ∀ (c : Ctx) (s t : Bool) (co : Nat) (e e2 : Int) (fl : List Signal),
    (co ≠ 0 → (truediv c (.fin s co e) (.fin t 0 e2)).run fl =
      (do raiseSig c .divisionByZero; pure (.inf (s != t)) : DM Dec).run fl) ∧
    (truediv c (.fin s 0 e) (.fin t 0 e2)).run fl = (invalid c).run fl ∧
    (truediv c (.inf s) (.inf t)).run fl = (invalid c).run fl ∧
    (truediv c (.inf s) (.fin t co e)).run fl = .ok (.inf (s != t), fl) ∧
    (truediv c (.fin s co e) (.inf t)).run fl =
      (do raiseSig c .clamped; pure (.fin (s != t) 0 c.etiny) : DM Dec).run fl

theorem truedivSpecials_proven : TruedivSpecials := by
  intro c s t co e e2 fl
  refine ⟨?_, rfl, by cases s <;> cases t <;> rfl, by cases s <;> rfl, by cases t <;> rfl⟩
  intro hc
  have hz : isZero (.fin s co e) = false := isZero_fin s co e hc
  have hz2 : isZero (.fin t 0 e2) = true := rfl
  simp only [truediv, isSpecial, Bool.or_false, Bool.false_eq_true, ↓reduceIte, decBool, hz, hz2,
    Bool.not_true, Bool.not_false, Dec.neg, divByZero]

/-! ## `__truediv__`'s integer core -/

theorem stripIdeal_spec (ideal : Int) : ∀ (f : Nat) (coeff : Nat) (exp : Int), (ideal - exp).toNat = f →
    (stripIdeal coeff exp ideal f).1 * 10 ^ ((stripIdeal coeff exp ideal f).2 - exp).toNat = coeff ∧
    exp ≤ (stripIdeal coeff exp ideal f).2 ∧
    (exp ≤ ideal → (stripIdeal coeff exp ideal f).2 ≤ ideal ∧
      ((stripIdeal coeff exp ideal f).2 = ideal ∨ (stripIdeal coeff exp ideal f).1 % 10 ≠ 0)) := by
  intro f
  induction f with
  | zero =>
    intro coeff exp hf
    simp only [stripIdeal]
    refine ⟨by simp, by omega, fun h => ⟨by omega, Or.inl (by omega)⟩⟩
  | succ n ih =>
    intro coeff exp hf
    simp only [stripIdeal]
    by_cases h : exp < ideal ∧ coeff % 10 = 0
    · rw [if_pos h]
      obtain ⟨h1, h2, h3⟩ := ih (coeff / 10) (exp + 1) (by omega)
      generalize stripIdeal (coeff / 10) (exp + 1) ideal n = p at h1 h2 h3
      refine ⟨?_, by omega, fun _ => h3 (by omega)⟩
      have hk : (p.2 - exp).toNat = (p.2 - (exp + 1)).toNat + 1 := by omega
      rw [hk, Nat.pow_succ, ← Nat.mul_assoc, h1]
      omega
    · rw [if_neg h]
      simp only
      refine ⟨by simp, by omega, fun h3 => ⟨h3, ?_⟩⟩
      by_cases hx : exp < ideal
      · right
        intro hc
        exact h ⟨hx, hc⟩
      · left; omega

/-- `__truediv__`'s integer division, before `_fix`. With `num`, `den` the operands
scaled so that `a/b = (num/den)·10^e`: if the division was exact, `q·den = num`, with the
exponent as close to the ideal `ea - eb` as trailing zeros allow. If not, `q` has more than
`prec` digits, the exact quotient lies strictly between `q₀` and `q₀ + 1` for `q₀` either
`q` or `q - 1`, and the last digit of `q` is not 0 or 5, so `_fix` sees an inexact tail
whatever it rounds. -/
def TruedivCoreCorrect : Prop :=
  ∀ (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int) (q : Nat) (e : Int),
    ca ≠ 0 → cb ≠ 0 →
    truedivFin c sa ca ea sb cb eb = .ok (q, e) →
    let ideal := ea - eb
    let num := ca * 10 ^ (ideal - e).toNat
    let den := cb * 10 ^ (e - ideal).toNat
    (q * den = num ∧ (e ≤ ideal → e = ideal ∨ q % 10 ≠ 0)) ∨
    (10 ^ c.prec ≤ q ∧ q % 5 ≠ 0 ∧ ∃ q₀, (q₀ = q ∨ q₀ + 1 = q) ∧ q₀ * den < num ∧ num < (q₀ + 1) * den)

/-- The integer division keeps more than `prec` digits, whichever way it is scaled. -/
theorem truediv_digits (prec ca cb : Nat) (ha : ca ≠ 0) (hb : cb ≠ 0) (shift : Int)
    (hs : shift = (numDigits cb : Int) - numDigits ca + prec + 1) :
    10 ^ prec * (if shift ≥ 0 then cb else cb * 10 ^ (-shift).toNat) ≤
      (if shift ≥ 0 then ca * 10 ^ shift.toNat else ca) := by
  have h1 := pow_numDigits_le ha
  have h2 := lt_pow_numDigits cb
  have hna := numDigits_pos ca
  by_cases h : shift ≥ 0
  · simp only [if_pos h]
    calc 10 ^ prec * cb ≤ 10 ^ prec * 10 ^ numDigits cb := Nat.mul_le_mul_left _ (Nat.le_of_lt h2)
      _ = 10 ^ (prec + numDigits cb) := (Nat.pow_add ..).symm
      _ = 10 ^ (numDigits ca - 1 + shift.toNat) := by congr 1; omega
      _ = 10 ^ (numDigits ca - 1) * 10 ^ shift.toNat := Nat.pow_add ..
      _ ≤ ca * 10 ^ shift.toNat := Nat.mul_le_mul_right _ h1
  · simp only [if_neg h]
    calc 10 ^ prec * (cb * 10 ^ (-shift).toNat)
        ≤ 10 ^ prec * (10 ^ numDigits cb * 10 ^ (-shift).toNat) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_of_lt h2))
      _ = 10 ^ (prec + (numDigits cb + (-shift).toNat)) := by rw [Nat.pow_add, Nat.pow_add]
      _ = 10 ^ (numDigits ca - 1) := by congr 1; omega
      _ ≤ ca := h1

theorem workRep_fin {s : Bool} {co : Nat} {e : Int} {p : Bool × Nat × Int}
    (h : workRep (.fin s co e) = .ok p) : p = (s, co, e) := by
  simp only [workRep] at h
  obtain ⟨_, _, h⟩ := ebind_ok h
  simpa [pure, Except.pure, eq_comm] using h

theorem truedivCoreCorrect_proven : TruedivCoreCorrect := by
  intro c sa ca ea sb cb eb q e ha hb h ideal num den
  simp only [truedivFin, ha, ↓reduceIte] at h
  obtain ⟨op1, h1, h⟩ := ebind_ok h
  obtain ⟨op2, h2, h⟩ := ebind_ok h
  cases workRep_fin h1
  cases workRep_fin h2
  have hcb : 0 < cb := Nat.pos_of_ne_zero hb
  simp only at h
  generalize hsh : (numDigits cb : Int) - numDigits ca + c.prec + 1 = shift at h
  have hdig := truediv_digits c.prec ca cb ha hb shift hsh.symm
  have hexp : ea - eb - shift = ideal - shift := rfl
  have hden0 : 0 < (if shift ≥ 0 then cb else cb * 10 ^ (-shift).toNat) := by
    split
    · exact hcb
    · exact Nat.mul_pos hcb (pow10_pos _)
  generalize hnum0 : (if shift ≥ 0 then ca * 10 ^ shift.toNat else ca) = n0 at h hdig
  generalize hdn0 : (if shift ≥ 0 then cb else cb * 10 ^ (-shift).toNat) = d0 at h hdig hden0
  have hbase : 10 ^ c.prec ≤ n0 / d0 := (Nat.le_div_iff_mul_le hden0).mpr hdig
  have hdm := Nat.div_add_mod n0 d0
  have hmd := Nat.mod_lt n0 hden0
  by_cases hr : n0 % d0 = 0
  · rw [if_neg (by simpa using hr)] at h
    have hx : (n0 / d0) * d0 = n0 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hr)
    simp only [pure, Except.pure, Except.ok.injEq] at h
    have hsp := stripIdeal_spec (ea - eb) _ (n0 / d0) (ea - eb - shift) rfl
    rw [h] at hsp
    obtain ⟨p1, p2, p3⟩ := hsp
    simp only at p1 p2 p3
    left
    by_cases hs : shift ≥ 0
    · simp only [if_pos hs] at hnum0 hdn0
      have hle : e ≤ ideal := (p3 (by omega)).1
      have hi : (ideal - (ea - eb - shift)).toNat = (ideal - e).toNat + (e - (ea - eb - shift)).toNat := by omega
      have hsn : shift.toNat = (ideal - e).toNat + (e - (ea - eb - shift)).toNat := by omega
      have h0 : (e - ideal).toNat = 0 := by omega
      refine ⟨?_, fun _ => (p3 (by omega)).2⟩
      simp only [num, den, h0, Nat.pow_zero, Nat.mul_one]
      apply Nat.eq_of_mul_eq_mul_right (pow10_pos (e - (ea - eb - shift)).toNat)
      calc q * cb * 10 ^ (e - (ea - eb - shift)).toNat
          = (q * 10 ^ (e - (ea - eb - shift)).toNat) * cb := Nat.mul_right_comm ..
        _ = (n0 / d0) * d0 := by rw [p1, hdn0]
        _ = n0 := hx
        _ = ca * 10 ^ shift.toNat := hnum0.symm
        _ = ca * 10 ^ (ideal - e).toNat * 10 ^ (e - (ea - eb - shift)).toNat := by
            rw [hsn, Nat.pow_add, Nat.mul_assoc]
    · simp only [if_neg hs] at hnum0 hdn0
      have hf : (ea - eb - (ea - eb - shift)).toNat = 0 := by omega
      rw [hf] at h
      simp only [stripIdeal, Prod.mk.injEq] at h
      obtain ⟨hq, he⟩ := h
      subst hq he
      have g1 : (ideal - (ea - eb - shift)).toNat = 0 := by omega
      have g2 : (ea - eb - shift - ideal).toNat = (-shift).toNat := by omega
      refine ⟨?_, fun hc => by omega⟩
      simp only [num, den, g1, g2, Nat.pow_zero, Nat.mul_one]
      rw [hdn0, hx, hnum0]
  · rw [if_pos (by simpa using hr)] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hq, he⟩ := h
    subst he
    right
    have hN : ca * 10 ^ (ideal - (ea - eb - shift)).toNat * 1 = n0 ∧
        cb * 10 ^ (ea - eb - shift - ideal).toNat = d0 := by
      by_cases hs : shift ≥ 0
      · simp only [if_pos hs] at hnum0 hdn0
        have g1 : (ideal - (ea - eb - shift)).toNat = shift.toNat := by omega
        have g2 : (ea - eb - shift - ideal).toNat = 0 := by omega
        rw [g1, g2, Nat.mul_one, Nat.pow_zero, Nat.mul_one]
        exact ⟨hnum0, hdn0⟩
      · simp only [if_neg hs] at hnum0 hdn0
        have g1 : (ideal - (ea - eb - shift)).toNat = 0 := by omega
        have g2 : (ea - eb - shift - ideal).toNat = (-shift).toNat := by omega
        rw [g1, g2, Nat.pow_zero, Nat.mul_one, Nat.mul_one]
        exact ⟨hnum0, hdn0⟩
    have hn : num = n0 := by simpa [num] using hN.1
    have hd : den = d0 := hN.2
    rw [hn, hd]
    have hmul : d0 * (n0 / d0) = (n0 / d0) * d0 := Nat.mul_comm ..
    have hsucc : (n0 / d0 + 1) * d0 = (n0 / d0) * d0 + d0 := Nat.succ_mul ..
    refine ⟨?_, ?_, n0 / d0, ?_, by omega, by omega⟩
    · split at hq <;> omega
    · split at hq <;> omega
    · split at hq
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)

/-! ## `//`, `%`, `divmod` -/

/-- `//`, `%` and `divmod` run the same `_divide`, so for finite operands with a
non-zero divisor `divmod(x, y)` is `(x // y, x % y)`, as Doc/reference/datamodel.rst:3418 asks of `__divmod__`,
with the remainder alone going through `_fix`. -/
def DivmodConsistent : Prop :=
  ∀ (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int) (fl : List Signal),
    cb ≠ 0 →
    (floordivD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
      (do let qr ← divideD c (.fin sa ca ea) (.fin sb cb eb); pure qr.1 : DM Dec).run fl ∧
    (modD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
      (do let qr ← divideD c (.fin sa ca ea) (.fin sb cb eb); fix c qr.2 : DM Dec).run fl ∧
    (divmodD c (.fin sa ca ea) (.fin sb cb eb)).run fl =
      (do let qr ← divideD c (.fin sa ca ea) (.fin sb cb eb)
          let r ← fix c qr.2
          pure (qr.1, r) : DM (Dec × Dec)).run fl

theorem divmodConsistent_proven : DivmodConsistent := by
  intro c sa ca ea sb cb eb fl hb
  cases cb with
  | zero => exact absurd rfl hb
  | succ n => exact ⟨rfl, rfl, rfl⟩

/-- `//` gives the same result in both twins, for every context and operands. -/
def FloordivTwinsAgree : Prop :=
  ∀ (c : Ctx) (a b : Dec) (fl : List Signal),
    (floordivD c a b).run fl = (floordivC c a b).run fl

/-- `Context(prec=28, Emax=10, Emin=-10, traps=[]).divide_int(Decimal(10)**20, 1)`:
`_pydecimal` returns the quotient as `_divide` built it, with adjusted exponent 20, while
`mpd_qdivint` finalizes it to Infinity with Overflow. -/
theorem floordivTwinsAgree_refuted : ¬FloordivTwinsAgree := by
  intro h
  let c : Ctx := { prec := 28, emax := 10, emin := -10, traps := [] }
  have hv := h c (.fin false (10 ^ 20) 0) (.fin false 1 0) []
  have h1 : (floordivD c (.fin false (10 ^ 20) 0) (.fin false 1 0)).run [] =
      .ok (.fin false (10 ^ 20) 0, []) := by decide
  have h2 : (floordivC c (.fin false (10 ^ 20) 0) (.fin false 1 0)).run [] =
      .ok (.inf false, [.overflow, .inexact, .rounded]) := by decide
  rw [h1, h2] at hv
  cases hv

/-- In a context with room for every quotient, `Emin ≤ 0` and `Emax ≥ prec - 1`, a
returning `//` gives the same value and flags in both twins. The excluded contexts are
decimal-pydecimal-floordiv-no-finalize. -/
def FloordivTwinsAgreeInRange : Prop :=
  ∀ (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int)
    (fl fl' : List Signal) (q : Dec),
    1 ≤ c.prec → c.emin ≤ 0 → (c.prec : Int) - 1 ≤ c.emax → cb ≠ 0 →
    (floordivD c (.fin sa ca ea) (.fin sb cb eb)).run fl = .ok (q, fl') →
    (floordivC c (.fin sa ca ea) (.fin sb cb eb)).run fl = .ok (q, fl')

end PyLean.Decimal
