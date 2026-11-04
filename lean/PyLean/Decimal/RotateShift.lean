import PyLean.Decimal.AddExact

/-!
`rotate` and `shift` (_pydecimal.py:3713-3744, :3771-3807) on every operand pair, the result's
coefficient stated digit by digit: the source works on the digit string (`rotdig[torot:] +
rotdig[:torot]`, `rotdig[:torot]`, `(rotdig + '0'*torot)[-prec:]`), the model on the integer, and
the statements say which digit of the operand lands at each position.
-/

namespace PyLean.Decimal

open PyLean

/-- Digit `i` of `x`, counted from the least significant (`0`). -/
def digitAt (x i : Nat) : Nat := x / 10 ^ i % 10

theorem digitAt_div (x m i : Nat) : digitAt (x / 10 ^ m) i = digitAt x (i + m) := by
  unfold digitAt
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm m i]

theorem digitAt_mod (x m i : Nat) (h : i < m) : digitAt (x % 10 ^ m) i = digitAt x i := by
  unfold digitAt
  have hm : 10 ^ m = 10 ^ i * 10 ^ (m - i) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hm, Nat.mod_mul_right_div_self]
  obtain ⟨b1, hb, _⟩ := pow_ten_eq_ten_mul (show 1 ≤ m - i by omega)
  exact Nat.mod_mod_of_dvd _ ⟨b1, hb⟩

theorem digitAt_low (A B k i : Nat) (hB : B < 10 ^ k) (hi : i < k) :
    digitAt (A * 10 ^ k + B) i = digitAt B i := by
  unfold digitAt
  have hk : 10 ^ k = 10 ^ i * (10 * 10 ^ (k - i - 1)) := by
    rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
  have hpos : 0 < 10 ^ i := Nat.pow_pos (by decide)
  rw [hk, show A * (10 ^ i * (10 * 10 ^ (k - i - 1))) + B = B + 10 ^ i * (10 * (A * 10 ^ (k - i - 1))) by
    rw [Nat.add_comm]; congr 1
    rw [Nat.mul_comm A, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (10 ^ (k - i - 1)) A],
    Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]

theorem digitAt_high (A B k i : Nat) (hB : B < 10 ^ k) (hi : k ≤ i) :
    digitAt (A * 10 ^ k + B) i = digitAt A (i - k) := by
  unfold digitAt
  have hpos : 0 < 10 ^ k := Nat.pow_pos (by decide)
  have hi' : 10 ^ i = 10 ^ k * 10 ^ (i - k) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hi', ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.mul_comm A, Nat.add_mul_div_left _ _ hpos,
    Nat.div_eq_of_lt hB, Nat.zero_add]

theorem digitAt_zero (i : Nat) : digitAt 0 i = 0 := by simp [digitAt]

/-- `rotate(a, n)` for a finite `a`, as the model computes it. -/
theorem rotate_fin_run (c : Ctx) (fl : List Signal) (s : Bool) (co : Nat) (e : Int) (bn : Bool) (bc : Nat)
    (hl : numDigits bc ≤ maxStrDigits)
    (hr : -(c.prec : Int) ≤ (if bn then -(bc : Int) else bc) ∧ (if bn then -(bc : Int) else bc) ≤ c.prec) :
    (rotate c (.fin s co e) (.fin bn bc 0)).run fl =
      let n : Int := if bn then -(bc : Int) else bc
      let cut := co % 10 ^ c.prec
      let k : Nat := if n ≥ 0 then n.toNat else c.prec - n.natAbs
      .ok (.fin s ((cut % 10 ^ (c.prec - k)) * 10 ^ k + cut / 10 ^ (c.prec - k)) e, fl) := by
  have hrun : (rotate c (.fin s co e) (.fin bn bc 0)).run fl =
      (intArg c (.fin s co e) (.fin bn bc 0) (-(c.prec : Int)) c.prec >>= fun x => match x with
        | .inl r => pure r
        | .inr torot => match Dec.fin s co e with
          | .fin neg co e =>
            let cut := co % 10 ^ c.prec
            let k : Nat := if torot ≥ 0 then torot.toNat else c.prec - torot.natAbs
            pure (.fin neg ((cut % 10 ^ (c.prec - k)) * 10 ^ k + cut / 10 ^ (c.prec - k)) e)
          | d => pure d).run fl := rfl
  rw [hrun, intArg_run c _ bn bc _ _ _ fl rfl hl]
  simp only [hr, and_self, not_true_eq_false, ↓reduceIte, isinfinity, ne_eq]
  rfl

theorem shift_fin_run (c : Ctx) (fl : List Signal) (s : Bool) (co : Nat) (e : Int) (bn : Bool) (bc : Nat)
    (hl : numDigits bc ≤ maxStrDigits)
    (hr : -(c.prec : Int) ≤ (if bn then -(bc : Int) else bc) ∧ (if bn then -(bc : Int) else bc) ≤ c.prec) :
    (shift c (.fin s co e) (.fin bn bc 0)).run fl =
      let n : Int := if bn then -(bc : Int) else bc
      let cut := co % 10 ^ c.prec
      .ok (.fin s (if n < 0 then cut / 10 ^ n.natAbs else (cut * 10 ^ n.toNat) % 10 ^ c.prec) e, fl) := by
  have hrun : (shift c (.fin s co e) (.fin bn bc 0)).run fl =
      (intArg c (.fin s co e) (.fin bn bc 0) (-(c.prec : Int)) c.prec >>= fun x => match x with
        | .inl r => pure r
        | .inr torot => match Dec.fin s co e with
          | .fin neg co e =>
            let cut := co % 10 ^ c.prec
            pure (.fin neg (if torot < 0 then cut / 10 ^ torot.natAbs
              else (cut * 10 ^ torot.toNat) % 10 ^ c.prec) e)
          | d => pure d).run fl := rfl
  rw [hrun, intArg_run c _ bn bc _ _ _ fl rfl hl]
  simp only [hr, and_self, not_true_eq_false, ↓reduceIte, isinfinity, ne_eq]
  rfl

/-- `rotate(a, n)` (_pydecimal.py:3713-3744) on every operand pair, for every context with
`prec ≥ 1`: a NaN operand goes through `_check_nans` (:3720-3722); a second operand that is not
integral (a non-zero exponent, an infinity) is InvalidOperation (:3724-3725); `int(other)` raises
the int/str-limit `ValueError` for a digit string of more than 4300 digits (:3726); `n` outside
`[-prec, prec]` is InvalidOperation (:3726-3727); an infinite `a` is returned (:3729-3730); and a
finite `±co·10^e` keeps its sign and exponent, its coefficient being the last `prec` digits of `co`
(padded with zeros, :3733-3738) rotated left by `n` (right by `-n` when negative): digit `i` of the
result is digit `i - n` of `co mod 10^prec`, wrapping around modulo `prec` (:3741). -/
def RotateExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal), 1 ≤ c.prec →
    (∀ a b : Dec, nanKind a ≠ 0 ∨ nanKind b ≠ 0 → (rotate c a b).run fl = nanSpec2 c a b fl) ∧
    (∀ (a : Dec) (bn : Bool) (bc : Nat) (be : Int), nanKind a = 0 → be ≠ 0 →
      (rotate c a (.fin bn bc be)).run fl = afterSig c .invalidOperation fl (.nan false false 0)) ∧
    (∀ (a : Dec) (bn : Bool), nanKind a = 0 →
      (rotate c a (.inf bn)).run fl = afterSig c .invalidOperation fl (.nan false false 0)) ∧
    (∀ (a : Dec) (bn : Bool) (bc : Nat), nanKind a = 0 → maxStrDigits < numDigits bc →
      (rotate c a (.fin bn bc 0)).run fl = .error (.valueError (limitToIntMsg (numDigits bc)))) ∧
    (∀ (a : Dec) (bn : Bool) (bc : Nat), nanKind a = 0 → numDigits bc ≤ maxStrDigits →
      let n : Int := if bn then -(bc : Int) else bc
      (¬(-(c.prec : Int) ≤ n ∧ n ≤ c.prec) →
        (rotate c a (.fin bn bc 0)).run fl = afterSig c .invalidOperation fl (.nan false false 0)) ∧
      ((-(c.prec : Int) ≤ n ∧ n ≤ c.prec) →
        (∀ s, a = .inf s → (rotate c a (.fin bn bc 0)).run fl = .ok (.inf s, fl)) ∧
        (∀ s co e, a = .fin s co e → ∃ r, (rotate c a (.fin bn bc 0)).run fl = .ok (.fin s r e, fl) ∧
          r < 10 ^ c.prec ∧ ∀ i < c.prec, digitAt r i =
            if 0 ≤ n then
              (if i < n.toNat then digitAt (co % 10 ^ c.prec) (i + c.prec - n.toNat)
               else digitAt (co % 10 ^ c.prec) (i - n.toNat))
            else
              (if i + n.natAbs < c.prec then digitAt (co % 10 ^ c.prec) (i + n.natAbs)
               else digitAt (co % 10 ^ c.prec) (i + n.natAbs - c.prec)))))

/-- `shift(a, n)` (_pydecimal.py:3771-3807) on every operand pair, for every context with
`prec ≥ 1`: the same operand checks as `rotate` (:3778-3788); a finite `±co·10^e` keeps its sign and
exponent, its coefficient being the last `prec` digits of `co` shifted left by `n` (zeros coming in,
digits past `prec` dropped, :3800-3802) or right by `-n` (the last `-n` digits dropped, :3798):
digit `i` of the result is digit `i - n` of `co mod 10^prec` when that is a digit position, and 0
otherwise. -/
def ShiftExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal), 1 ≤ c.prec →
    (∀ a b : Dec, nanKind a ≠ 0 ∨ nanKind b ≠ 0 → (shift c a b).run fl = nanSpec2 c a b fl) ∧
    (∀ (a : Dec) (bn : Bool) (bc : Nat) (be : Int), nanKind a = 0 → be ≠ 0 →
      (shift c a (.fin bn bc be)).run fl = afterSig c .invalidOperation fl (.nan false false 0)) ∧
    (∀ (a : Dec) (bn : Bool), nanKind a = 0 →
      (shift c a (.inf bn)).run fl = afterSig c .invalidOperation fl (.nan false false 0)) ∧
    (∀ (a : Dec) (bn : Bool) (bc : Nat), nanKind a = 0 → maxStrDigits < numDigits bc →
      (shift c a (.fin bn bc 0)).run fl = .error (.valueError (limitToIntMsg (numDigits bc)))) ∧
    (∀ (a : Dec) (bn : Bool) (bc : Nat), nanKind a = 0 → numDigits bc ≤ maxStrDigits →
      let n : Int := if bn then -(bc : Int) else bc
      (¬(-(c.prec : Int) ≤ n ∧ n ≤ c.prec) →
        (shift c a (.fin bn bc 0)).run fl = afterSig c .invalidOperation fl (.nan false false 0)) ∧
      ((-(c.prec : Int) ≤ n ∧ n ≤ c.prec) →
        (∀ s, a = .inf s → (shift c a (.fin bn bc 0)).run fl = .ok (.inf s, fl)) ∧
        (∀ s co e, a = .fin s co e → ∃ r, (shift c a (.fin bn bc 0)).run fl = .ok (.fin s r e, fl) ∧
          r < 10 ^ c.prec ∧ ∀ i < c.prec, digitAt r i =
            if 0 ≤ n then
              (if i < n.toNat then 0 else digitAt (co % 10 ^ c.prec) (i - n.toNat))
            else
              (if i + n.natAbs < c.prec then digitAt (co % 10 ^ c.prec) (i + n.natAbs) else 0))))

theorem digitAt_ge (x p i : Nat) (hx : x < 10 ^ p) (hi : p ≤ i) : digitAt x i = 0 := by
  unfold digitAt
  have : x < 10 ^ i := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi)
  rw [Nat.div_eq_of_lt this]

/-- The digit facts of the rotation the model computes. -/
theorem rotate_digits (p k cut : Nat) (hk : k ≤ p) (hc : cut < 10 ^ p) :
    let r := (cut % 10 ^ (p - k)) * 10 ^ k + cut / 10 ^ (p - k)
    r < 10 ^ p ∧ ∀ i < p, digitAt r i =
      if i < k then digitAt cut (i + (p - k)) else digitAt cut (i - k) := by
  intro r
  have hpk : 10 ^ p = 10 ^ (p - k) * 10 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  have hB : cut / 10 ^ (p - k) < 10 ^ k := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), Nat.mul_comm, ← hpk]; exact hc
  have hA : cut % 10 ^ (p - k) < 10 ^ (p - k) := Nat.mod_lt _ (Nat.pow_pos (by decide))
  refine ⟨?_, fun i hi => ?_⟩
  · have := Nat.mul_le_mul_right (10 ^ k) (show cut % 10 ^ (p - k) + 1 ≤ 10 ^ (p - k) by omega)
    rw [Nat.add_mul, Nat.one_mul, ← hpk] at this
    show cut % 10 ^ (p - k) * 10 ^ k + cut / 10 ^ (p - k) < 10 ^ p
    omega
  · by_cases h : i < k
    · rw [if_pos h]
      show digitAt (cut % 10 ^ (p - k) * 10 ^ k + cut / 10 ^ (p - k)) i = _
      rw [digitAt_low _ _ _ _ hB h, digitAt_div]
    · rw [if_neg h]
      show digitAt (cut % 10 ^ (p - k) * 10 ^ k + cut / 10 ^ (p - k)) i = _
      rw [digitAt_high _ _ _ _ hB (by omega), digitAt_mod _ _ _ (by omega)]

theorem rotate_specials (c : Ctx) (fl : List Signal) :
    (∀ a b : Dec, nanKind a ≠ 0 ∨ nanKind b ≠ 0 → (rotate c a b).run fl = nanSpec2 c a b fl) ∧
    (∀ a b : Dec, nanKind a ≠ 0 ∨ nanKind b ≠ 0 → (shift c a b).run fl = nanSpec2 c a b fl) := by
  refine ⟨fun a b h => ?_, fun a b h => ?_⟩
  · simp only [rotate, intArg, bind_assoc]
    exact checkNans_return c a b fl _ (fun d => by simp [pure_bind]) h
  · simp only [shift, intArg, bind_assoc]
    exact checkNans_return c a b fl _ (fun d => by simp [pure_bind]) h

theorem rotateExact_proven : RotateExact := by
  intro c fl hp
  have hrun : ∀ a b, rotate c a b = (intArg c a b (-(c.prec : Int)) c.prec >>= fun x => match x with
      | .inl r => pure r
      | .inr torot => match a with
        | .fin neg co e =>
          let cut := co % 10 ^ c.prec
          let k : Nat := if torot ≥ 0 then torot.toNat else c.prec - torot.natAbs
          pure (.fin neg ((cut % 10 ^ (c.prec - k)) * 10 ^ k + cut / 10 ^ (c.prec - k)) e)
        | d => pure d) := fun _ _ => rfl
  refine ⟨(rotate_specials c fl).1, fun a bn bc be ha hb => ?_, fun a bn ha => ?_,
    fun a bn bc ha hl => ?_, fun a bn bc ha hl => ⟨fun hr => ?_, fun hr => ⟨fun s hs => ?_, fun s co e hs => ?_⟩⟩⟩
  · rw [hrun, intArg_bad c a _ _ _ _ fl ha rfl (fun bn' bc' h => by cases h; exact hb rfl)]
    rw [bind_pure]; exact invalid_run c fl
  · rw [hrun, intArg_bad c a _ _ _ _ fl ha rfl (by intro bn' bc' h; cases h)]
    rw [bind_pure]; exact invalid_run c fl
  · rw [hrun]
    simp only [intArg, bind_assoc]
    rw [checkNans_none_bind c a _ ha rfl]
    simp only [intLimit, show numDigits bc > maxStrDigits from hl, ↓reduceIte]
    rfl
  · rw [hrun, intArg_run c _ bn bc _ _ _ fl ha hl]
    simp only [hr, not_false_eq_true, ↓reduceIte]
    rw [bind_pure]; exact invalid_run c fl
  · subst hs
    rw [hrun, intArg_run c _ bn bc _ _ _ fl rfl hl]
    simp only [hr, and_self, not_true_eq_false, ↓reduceIte, isinfinity]
    cases s <;> rfl
  · subst hs
    rw [rotate_fin_run c fl s co e bn bc hl hr]
    dsimp only
    have hc : co % 10 ^ c.prec < 10 ^ c.prec := Nat.mod_lt _ (Nat.pow_pos (by decide))
    obtain ⟨hn1, hn2⟩ := hr
    by_cases hn : (0 : Int) ≤ (if bn then -(bc : Int) else bc)
    · have hk : (if bn then -(bc : Int) else bc).toNat ≤ c.prec := by omega
      obtain ⟨hlt, hd⟩ := rotate_digits c.prec _ (co % 10 ^ c.prec) hk hc
      refine ⟨_, ?_, hlt, fun i hi => ?_⟩
      · simp only [hn, ↓reduceIte, ge_iff_le]
      · rw [if_pos hn, hd i hi]
        by_cases h : i < (if bn then -(bc : Int) else bc).toNat
        · rw [if_pos h, if_pos h, Nat.add_sub_assoc hk]
        · rw [if_neg h, if_neg h]
    · have hk : c.prec - (if bn then -(bc : Int) else bc).natAbs ≤ c.prec := by omega
      obtain ⟨hlt, hd⟩ := rotate_digits c.prec _ (co % 10 ^ c.prec) hk hc
      have hn' : ¬ (if bn then -(bc : Int) else bc) ≥ 0 := by omega
      refine ⟨_, ?_, hlt, fun i hi => ?_⟩
      · simp only [hn', ↓reduceIte]
      · rw [if_neg hn, hd i hi]
        have hm : (if bn then -(bc : Int) else bc).natAbs ≤ c.prec := by omega
        by_cases h : i + (if bn then -(bc : Int) else bc).natAbs < c.prec
        · rw [if_pos (by omega), if_pos h]; congr 1; omega
        · rw [if_neg (by omega), if_neg h]; congr 1; omega

theorem shiftExact_proven : ShiftExact := by
  intro c fl hp
  have hrun : ∀ a b, shift c a b = (intArg c a b (-(c.prec : Int)) c.prec >>= fun x => match x with
      | .inl r => pure r
      | .inr torot => match a with
        | .fin neg co e =>
          let cut := co % 10 ^ c.prec
          pure (.fin neg (if torot < 0 then cut / 10 ^ torot.natAbs
            else (cut * 10 ^ torot.toNat) % 10 ^ c.prec) e)
        | d => pure d) := fun _ _ => rfl
  refine ⟨(rotate_specials c fl).2, fun a bn bc be ha hb => ?_, fun a bn ha => ?_,
    fun a bn bc ha hl => ?_, fun a bn bc ha hl => ⟨fun hr => ?_, fun hr => ⟨fun s hs => ?_, fun s co e hs => ?_⟩⟩⟩
  · rw [hrun, intArg_bad c a _ _ _ _ fl ha rfl (fun bn' bc' h => by cases h; exact hb rfl)]
    rw [bind_pure]; exact invalid_run c fl
  · rw [hrun, intArg_bad c a _ _ _ _ fl ha rfl (by intro bn' bc' h; cases h)]
    rw [bind_pure]; exact invalid_run c fl
  · rw [hrun]
    simp only [intArg, bind_assoc]
    rw [checkNans_none_bind c a _ ha rfl]
    simp only [intLimit, show numDigits bc > maxStrDigits from hl, ↓reduceIte]
    rfl
  · rw [hrun, intArg_run c _ bn bc _ _ _ fl ha hl]
    simp only [hr, not_false_eq_true, ↓reduceIte]
    rw [bind_pure]; exact invalid_run c fl
  · subst hs
    rw [hrun, intArg_run c _ bn bc _ _ _ fl rfl hl]
    simp only [hr, and_self, not_true_eq_false, ↓reduceIte, isinfinity]
    cases s <;> rfl
  · subst hs
    rw [shift_fin_run c fl s co e bn bc hl hr]
    dsimp only
    have hc : co % 10 ^ c.prec < 10 ^ c.prec := Nat.mod_lt _ (Nat.pow_pos (by decide))
    obtain ⟨hn1, hn2⟩ := hr
    by_cases hn : (0 : Int) ≤ (if bn then -(bc : Int) else bc)
    · have hn' : ¬ (if bn then -(bc : Int) else bc) < 0 := by omega
      refine ⟨_, ?_, Nat.mod_lt (co % 10 ^ c.prec * 10 ^ (if bn then -(bc : Int) else bc).toNat)
        (Nat.pow_pos (by decide)), fun i hi => ?_⟩
      · simp only [hn', ↓reduceIte]
      · rw [if_pos hn, digitAt_mod _ _ _ hi, show co % 10 ^ c.prec * 10 ^ (if bn then -(bc : Int) else bc).toNat =
          co % 10 ^ c.prec * 10 ^ (if bn then -(bc : Int) else bc).toNat + 0 by rfl]
        by_cases h : i < (if bn then -(bc : Int) else bc).toNat
        · rw [if_pos h, digitAt_low _ _ _ _ (Nat.pow_pos (by decide)) h, digitAt_zero]
        · rw [if_neg h, digitAt_high _ _ _ _ (Nat.pow_pos (by decide)) (by omega)]
    · have hn' : (if bn then -(bc : Int) else bc) < 0 := by omega
      refine ⟨_, ?_, Nat.lt_of_le_of_lt (Nat.div_le_self (co % 10 ^ c.prec)
        (10 ^ (if bn then -(bc : Int) else bc).natAbs)) hc, fun i hi => ?_⟩
      · simp only [hn', ↓reduceIte]
      · rw [if_neg hn, digitAt_div]
        by_cases h : i + (if bn then -(bc : Int) else bc).natAbs < c.prec
        · rw [if_pos h]
        · rw [if_neg h]; exact digitAt_ge _ _ _ hc (by omega)

end PyLean.Decimal
