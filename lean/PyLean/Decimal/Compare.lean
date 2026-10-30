import PyLean.Decimal.Round

/-! `_cmp` compares values, and `compare_total` is a total order on representations. -/

namespace PyLean.Decimal

open PyLean

/-- Two scaled coefficients with different digit-count-plus-scale differ. -/
theorem scaled_ne {c1 c2 A B : Nat} (_h1 : c1 ≠ 0) (h2 : c2 ≠ 0)
    (hlt : numDigits c1 + A < numDigits c2 + B) : c1 * 10 ^ A < c2 * 10 ^ B := by
  have u1 := lt_pow_numDigits c1
  have l2 := pow_numDigits_le h2
  have hp1 : c1 * 10 ^ A < 10 ^ (numDigits c1 + A) := by
    rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right u1 (Nat.pow_pos (by decide))
  have hp2 : 10 ^ (numDigits c2 - 1 + B) ≤ c2 * 10 ^ B := by
    rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ l2
  have hp3 : 10 ^ (numDigits c1 + A) ≤ 10 ^ (numDigits c2 - 1 + B) :=
    Nat.pow_le_pow_right (by decide) (by have := numDigits_pos c2; omega)
  omega

/-- `_cmp` on finite operands says "equal" exactly when the values are equal. -/
theorem cmpVal_fin_eq (n1 n2 : Bool) (c1 c2 : Nat) (e1 e2 : Int) :
    cmpVal (.fin n1 c1 e1) (.fin n2 c2 e2) = .eq ↔
      (c1 = 0 ∧ c2 = 0) ∨
      (c1 ≠ 0 ∧ n1 = n2 ∧ c1 * 10 ^ (e1 - min e1 e2).toNat = c2 * 10 ^ (e2 - min e1 e2).toNat) := by
  have hA : (e1 - min e1 e2).toNat = (e1 - e2).toNat := by omega
  have hB : (e2 - min e1 e2).toNat = (e2 - e1).toNat := by omega
  rw [hA, hB]
  simp only [cmpVal]
  by_cases h1 : c1 = 0
  · subst h1
    by_cases h2 : c2 = 0
    · simp [h2]
    · cases n2 <;> simp [h2, signOrd, Ordering.swap]
  by_cases h2 : c2 = 0
  · subst h2
    have : c1 * 10 ^ (e1 - e2).toNat ≠ 0 := Nat.mul_ne_zero h1 (Nat.ne_of_gt (Nat.pow_pos (show 0 < 10 by decide)))
    cases n1 <;> simp [h1, signOrd, this]
  simp only [h1, h2, ↓reduceIte, false_and, false_or, ne_eq, not_false_eq_true, true_and]
  cases n1 <;> cases n2 <;> simp only [Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true,
    Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and, true_and, signOrd, Ordering.swap] <;>
  · by_cases ha : e1 + (numDigits c1 : Int) - 1 = e2 + numDigits c2 - 1
    · simp only [ha, ↓reduceIte]
      repeat' split
      all_goals simp_all
    · simp only [ha, ↓reduceIte]
      have hne : c1 * 10 ^ (e1 - e2).toNat ≠ c2 * 10 ^ (e2 - e1).toNat := by
        rcases Int.lt_or_gt_of_ne ha with h | h
        · exact Nat.ne_of_lt (scaled_ne h1 h2 (by omega))
        · exact Nat.ne_of_gt (scaled_ne h2 h1 (by omega))
      split <;> simp [hne]

theorem cmpVal_swap_fin (n1 n2 : Bool) (c1 c2 : Nat) (e1 e2 : Int) :
    cmpVal (.fin n2 c2 e2) (.fin n1 c1 e1) = (cmpVal (.fin n1 c1 e1) (.fin n2 c2 e2)).swap := by
  simp only [cmpVal]
  cases n1 <;> cases n2 <;> simp only [signOrd, Bool.not_true, Bool.not_false, Bool.and_false,
    Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;>
    (repeat' split) <;> simp_all [Ordering.swap] <;> omega

theorem cmpVal_swap (a b : Dec) (ha : ∀ n s p, a ≠ .nan n s p) (hb : ∀ n s p, b ≠ .nan n s p) :
    cmpVal b a = (cmpVal a b).swap := by
  cases a with
  | nan n s p => exact absurd rfl (ha n s p)
  | inf n1 =>
    cases b with
    | nan n s p => exact absurd rfl (hb n s p)
    | inf n2 => cases n1 <;> cases n2 <;> rfl
    | fin n2 c2 e2 => cases n1 <;> rfl
  | fin n1 c1 e1 =>
    cases b with
    | nan n s p => exact absurd rfl (hb n s p)
    | inf n2 => cases n2 <;> rfl
    | fin n2 c2 e2 => exact cmpVal_swap_fin n1 n2 c1 c2 e1 e2

theorem nanKind_zero {a : Dec} (h : nanKind a = 0) : ∀ n s p, a ≠ .nan n s p := by
  intro n s p he; subst he; cases s <;> simp [nanKind] at h

theorem nanKind_le (a : Dec) : nanKind a ≤ 2 := by
  cases a with
  | nan n s p => cases s <;> simp [nanKind]
  | _ => simp [nanKind]

theorem compareTotalSame_antisymm (sg : Bool) (a b : Dec) :
    compareTotalSame sg b a = -compareTotalSame sg a b := by
  have := nanKind_le a
  have := nanKind_le b
  unfold compareTotalSame
  by_cases hn : nanKind a ≠ 0 ∨ nanKind b ≠ 0
  · have hn' : nanKind b ≠ 0 ∨ nanKind a ≠ 0 := hn.symm
    simp only [hn, hn', ↓reduceIte]
    cases sg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> (repeat' split) <;> omega
  · have ha : nanKind a = 0 := by omega
    have hb : nanKind b = 0 := by omega
    simp only [ha, hb, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
    rw [cmpVal_swap a b (nanKind_zero ha) (nanKind_zero hb)]
    generalize cmpVal a b = o
    cases o <;> cases sg <;> simp only [Ordering.swap, Bool.false_eq_true, ↓reduceIte] <;>
      (repeat' split) <;> omega

theorem compareTotal_antisymm (a b : Dec) : compareTotal b a = -compareTotal a b := by
  unfold compareTotal
  cases ha : a.neg <;> cases hb : b.neg <;> simp only [Int.reduceNeg, Int.neg_neg] <;>
    exact compareTotalSame_antisymm _ _ _

theorem flip_ne_zero (sg : Bool) (x : Int) (hx : x ≠ 0) : (if sg then -x else x) ≠ 0 := by
  cases sg <;> simp <;> omega

theorem compareTotalSame_zero (sg : Bool) (a b : Dec) (ha : a.neg = sg) (hb : b.neg = sg)
    (h : compareTotalSame sg a b = 0) : a = b := by
  unfold compareTotalSame at h
  cases a with
  | fin n1 c1 e1 =>
    cases b with
    | fin n2 c2 e2 =>
      simp only [Dec.neg] at ha hb
      subst ha hb
      simp only [nanKind, ne_eq, not_true_eq_false, or_self, ↓reduceIte, expOf] at h
      split at h
      · omega
      · omega
      · rename_i heq
        rcases (cmpVal_fin_eq _ _ c1 c2 e1 e2).mp heq with ⟨h1, h2⟩ | ⟨_, _, h3⟩
        · subst h1 h2
          by_cases hlt : e1 < e2
          · simp only [hlt, ↓reduceIte] at h; exact absurd h (flip_ne_zero _ _ (by decide))
          by_cases hgt : e1 > e2
          · simp only [hlt, hgt, ↓reduceIte] at h; exact absurd h (flip_ne_zero _ _ (by decide))
          have : e1 = e2 := by omega
          subst this; rfl
        · by_cases hlt : e1 < e2
          · simp only [hlt, ↓reduceIte] at h; exact absurd h (flip_ne_zero _ _ (by decide))
          by_cases hgt : e1 > e2
          · simp only [hlt, hgt, ↓reduceIte] at h; exact absurd h (flip_ne_zero _ _ (by decide))
          have : e1 = e2 := by omega
          subst this
          simp only [Int.min_self, Int.sub_self, Int.toNat_zero, Nat.pow_zero, Nat.mul_one] at h3
          subst h3; rfl
    | inf n2 =>
      simp only [nanKind, ne_eq, not_true_eq_false, or_self, ↓reduceIte] at h
      simp only [Dec.neg] at ha hb; subst ha hb
      cases n2 <;> simp [cmpVal] at h
    | nan n2 s2 p2 =>
      cases s2 <;> simp [nanKind] at h <;> exact absurd h (flip_ne_zero _ _ (by decide))
  | inf n1 =>
    cases b with
    | fin n2 c2 e2 =>
      simp only [nanKind, ne_eq, not_true_eq_false, or_self, ↓reduceIte] at h
      simp only [Dec.neg] at ha hb; subst ha hb
      cases n2 <;> simp [cmpVal] at h
    | inf n2 => simp only [Dec.neg] at ha hb; subst ha hb; rfl
    | nan n2 s2 p2 =>
      cases s2 <;> simp [nanKind] at h <;> exact absurd h (flip_ne_zero _ _ (by decide))
  | nan n1 s1 p1 =>
    cases b with
    | nan n2 s2 p2 =>
      simp only [Dec.neg] at ha hb; subst ha hb
      cases s1 <;> cases s2 <;> simp only [nanKind, payloadOf] at h <;>
        simp at h <;>
        (repeat' split at h) <;> (try exact absurd h (flip_ne_zero _ _ (by decide))) <;>
        (try (have : p1 = p2 := by omega); subst this; rfl) <;> omega
    | _ => cases s1 <;> simp [nanKind] at h <;> exact absurd h (flip_ne_zero _ _ (by decide))

/-- `compare_total` returns 0 exactly on identical representations. -/
theorem compareTotal_eq_zero (a b : Dec) : compareTotal a b = 0 ↔ a = b := by
  constructor
  · intro h
    unfold compareTotal at h
    cases ha : a.neg <;> cases hb : b.neg <;> simp only [ha, hb] at h <;> try omega
    · exact compareTotalSame_zero false a b ha hb h
    · exact compareTotalSame_zero true a b ha hb h
  · intro h; subst h
    have := compareTotal_antisymm a a
    omega

end PyLean.Decimal
