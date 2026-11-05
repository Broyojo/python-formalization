import PyLean.TextLibs.BinasciiB85c

/-!
What `canonical` and the rejections of `binascii.a2b_base85` do, and the encoder's options.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-! ### What the decoder rejects -/

theorem b85_bad (t : Nat → Nat) (ig : Option (List Nat)) (k : Bool) (N : Nat) (x : Nat) (hx : 85 ≤ t x)
    (hi : ign ig x = false) : ∀ (s : List Nat) (st : St85) (f : Nat), x ∈ s → st.pos < 5 →
      ∀ r, a2bB85Loop t ig k N f s s.length st ≠ .ok r := by
  intro s
  induction s with
  | nil => intro _ _ h; cases h
  | cons y ys ih =>
    intro st f hm hp r h
    cases f with
    | zero => simp [a2bB85Loop] at h
    | succ g =>
      have hst1 : (decide (((y :: ys).length : Int) ≤ 0) && st.pos == 0) = false := by simp; omega
      have e1 : ((y :: ys).length : Int) - 1 = ys.length := by simp
      simp only [a2bB85Loop, hst1, Bool.false_eq_true, if_false, Option.getD_some] at h
      by_cases hd : t y < 85
      · have hxy : x ∈ ys := by
          rcases List.mem_cons.mp hm with e | e
          · subst e; omega
          · exact e
        simp only [hd, if_true] at h
        split at h
        · cases h
        · by_cases h5 : st.pos + 1 = 5
          · have c1 : ¬ ((y :: ys).length : Int) < 1 := by simp; omega
            simp only [h5, show (5 != 5) = false by decide, Bool.false_eq_true, if_false, c1,
              show ¬ (4 : Nat) = 0 by decide, show decide ((4 : Nat) < 4) = false by decide, Bool.and_false,
              Bool.false_and, e1] at h
            exact ih _ _ hxy (by simp) r h
          · have : (st.pos + 1 != 5) = true := by simpa using h5
            simp only [this, if_true, e1] at h
            exact ih _ _ hxy (by simp only; omega) r h
      · simp only [hd, if_false] at h
        by_cases hy : ign ig y = true
        · have hxy : x ∈ ys := by
            rcases List.mem_cons.mp hm with e | e
            · subst e; rw [hi] at hy; cases hy
            · exact e
          have hp5 : (st.pos != 5) = true := by simp; omega
          simp only [hy, Bool.not_true, Bool.false_eq_true, if_false, hp5, if_true, e1] at h
          exact ih _ _ hxy hp r h
        · have hy' : ign ig y = false := by simpa using hy
          simp only [hy', Bool.not_false, if_true] at h
          cases h

/-- What `a2b_base85` refuses, for every option: a byte that is not in the alphabet and that
`ignorechars` does not name. A decoder that skips unknown bytes does not satisfy this, and one that
ignores `ignorechars` fails `B85RoundTripAll`. -/
def B85StrictLaw : Prop :=
  ∀ (s : List Nat) (alpha : AlphaArg) (g : List Nat) (k : Bool),
    (∃ x ∈ s, x ∉ alphaChars85 alpha ∧ x ∉ g) → ∀ r, a2bB85 (.bytes s) alpha (.bytes g) k ≠ .ok r

theorem b85StrictLaw_proven : B85StrictLaw := by
  intro s alpha g k ⟨x, hx, h1, h2⟩ r hr
  by_cases hA : (alphaChars85 alpha).length = 85
  · rw [a2bB85_eq alpha hA] at hr
    have h85 : 85 ≤ revT (alphaChars85 alpha) none x := by
      rw [revT_large _ none x (by simp) (fun y hy e => h1 (e ▸ hy))]; decide
    cases hl : a2bB85Loop (revT (alphaChars85 alpha) none) (if g.isEmpty then none else some g) k s.length
        (s.length + 6) s s.length {} with
    | error e => rw [hl] at hr; cases hr
    | ok st =>
      exact b85_bad _ _ k _ x h85 (ign_g g x h2) s {} _ hx (by decide) st hl
  · cases alpha with
    | absent => exact hA (by decide)
    | bytes a =>
      simp only [alphaChars85] at hA
      simp [a2bB85, asciiBuffer, alphaDec, bufData, decTable, hA, bind, Except.bind] at hr
    | other t => simp [a2bB85, asciiBuffer, alphaDec, bind, Except.bind] at hr

/-! ### `canonical` -/

/-- The value of base-85 digits, most significant first. -/
def val85 (ds : List Nat) : Nat := ds.foldl (fun l v => l * 85 + v) 0

/-- The last group is short (two to four digits) and its digits are not those the encoder writes for the
bytes it decodes to: the decoder pads it with the largest digit, and compares the quotients by
`85 ** (5 - m)` of that value and of the value with the cut bytes zeroed. -/
def canonBad85 (vs : List Nat) : Bool :=
  let m := vs.length % 5
  decide (2 ≤ m) && nonCanon (val85 (vs.drop (vs.length - m)) * 85 ^ (5 - m) + (85 ^ (5 - m) - 1)) (m - 1)

theorem pad_val (l P : Nat) (hP : 1 ≤ P) : (l * 85 + 84) * P + (P - 1) = l * (P * 85) + (P * 85 - 1) := by
  rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 85 P]
  generalize l * (P * 85) = Q
  omega

theorem b85_padcanon (t : Nat → Nat) (ig : Option (List Nat)) (N N' : Nat) :
    ∀ (n : Nat) (st : St85) (len : Int) (g g' : Nat), st.pos + n = 4 → 1 ≤ st.pos → len ≤ 0 → n + 2 ≤ g →
      n + 2 ≤ g' →
      (a2bB85Loop t ig true N g [] len st).toOption = (a2bB85Loop t ig false N' g' [] len st).toOption.bind
        (fun r => if (decide ((3 + (len - n)).toNat ≠ 0) &&
            nonCanon (st.left * 85 ^ (n + 1) + (85 ^ (n + 1) - 1)) (3 + (len - n)).toNat) then none else some r) := by
  intro n
  induction n with
  | zero =>
    intro st len g g' hn hp hl hg hg'
    obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ k, g' = k + 1 := ⟨g' - 1, by omega⟩
    have h4 : st.pos = 4 := by omega
    have h0 : (decide (len ≤ 0) && st.pos == 0) = false := by simp [h4]
    obtain ⟨g2, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
    obtain ⟨g2', rfl⟩ : ∃ k, g' = k + 1 := ⟨g' - 1, by omega⟩
    simp only [a2bB85Loop, h0, Bool.false_eq_true, if_false]
    simp only [show (84 : Nat) < 85 by decide, if_true, h4, beq_self_eq_true, Bool.true_and,
      show (4 + 1 != 5) = false by decide, Bool.false_eq_true, if_false]
    have hl1 : (decide (len - 1 ≤ 0) && ((0 : Nat) == 0)) = true := by simp; omega
    try simp only [hl1, if_true]
    have hc : len < 1 := by omega
    have hpw : st.left * 85 ^ (0 + 1) + (85 ^ (0 + 1) - 1) = st.left * 85 + 84 := by simp
    have hlen0 : len - ((0 : Nat) : Int) = len := by simp
    rw [hpw, hlen0]
    by_cases hov : decide (st.left * 85 + 84 ≥ 2 ^ 32) = true
    · rw [if_pos hov, if_pos hov]
      rfl
    · rw [if_neg hov, if_neg hov]
      simp only [hc, if_true]
      by_cases hz : (3 + len).toNat = 0
      · simp [hz]
      · have hlt : (3 + len).toNat < 4 := by omega
        rw [if_neg hz, if_neg hz]
        simp only [Bool.false_and, Bool.false_eq_true, if_false, Bool.true_and, decide_eq_true hlt]

        by_cases hnc : nonCanon (st.left * 85 + 84) (3 + len).toNat = true
        · rw [if_pos hnc]
          simp [hnc, hz] <;> rfl
        · rw [if_neg hnc]
          simp [hnc, show len - 1 ≤ 0 by omega]
  | succ n ih =>
    intro st len g g' hn hp hl hg hg'
    obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ k, g' = k + 1 := ⟨g' - 1, by omega⟩
    have h0 : (decide (len ≤ 0) && st.pos == 0) = false := by simp; omega
    have h4 : (st.pos == 4) = false := by simp; omega
    have h5 : (st.pos + 1 != 5) = true := by simp; omega
    simp only [a2bB85Loop, h0, Bool.false_eq_true, if_false, show (84 : Nat) < 85 by decide, if_true, h4,
      Bool.false_and, h5]
    rw [ih { st with left := st.left * 85 + 84, pos := st.pos + 1 } (len - 1) g g' (by simp only; omega)
      (by simp only; omega) (by omega) (by omega) (by omega)]
    have e1 : len - 1 - n = len - (n + 1) := by omega
    have hP : 1 ≤ 85 ^ (n + 1) := Nat.one_le_pow _ _ (by decide)
    have e2 : (st.left * 85 + 84) * 85 ^ (n + 1) + (85 ^ (n + 1) - 1) = st.left * 85 ^ (n + 1 + 1) + (85 ^ (n + 1 + 1) - 1) := by
      rw [pad_val st.left _ hP, ← Nat.pow_succ]
    have e3 : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
    simp only [e1, e2, e3]

end PyLean.TextLibs.Binascii
