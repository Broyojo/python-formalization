import PyLean.Decimal.Basic

/-! ASCII digit strings: reading them (`digitsValue`) and spelling numbers (`Nat.toDigits`). -/

namespace PyLean.Decimal

open PyLean

theorem digitVal_ascii_aux : ∀ n, n < 10 → digitVal (Char.ofNat (48 + n)) = some n := by decide

theorem isDigit_iff' {c : Char} : c.isDigit = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  have := @Char.isDigit_iff_toNat c
  simpa using this

theorem char_eq_ofNat (c : Char) : c = Char.ofNat c.toNat := (Char.ofNat_toNat c).symm

theorem digitVal_of_isDigit {c : Char} (h : c.isDigit = true) : digitVal c = some (c.toNat - 48) := by
  have h' := isDigit_iff'.mp h
  have := digitVal_ascii_aux (c.toNat - 48) (by omega)
  rw [show 48 + (c.toNat - 48) = c.toNat by omega, ← char_eq_ofNat] at this
  exact this

theorem isDigit_of_digitVal {c : Char} (h : c.isDigit = true) : isDigit c = true := by
  simp [isDigit, digitVal_of_isDigit h]

theorem foldl_digits (D : List Char) (h : ∀ c ∈ D, c.isDigit = true) (acc : Nat) :
    D.foldl (fun acc c => acc * 10 + (digitVal c).getD 0) acc = Nat.ofDigitChars 10 D acc := by
  induction D generalizing acc with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, digitVal_of_isDigit (h c (by simp)), Option.getD_some]
    rw [ih (fun x hx => h x (by simp [hx])), Nat.ofDigitChars_cons]
    congr 1
    simp only [show '0'.toNat = 48 from rfl]
    omega

theorem digitsValue_eq (D : List Char) (h : ∀ c ∈ D, c.isDigit = true) :
    digitsValue D = Nat.ofDigitChars 10 D 0 := foldl_digits D h 0

theorem mem_toDigits_isDigit {n : Nat} {c : Char} (h : c ∈ Nat.toDigits 10 n) : c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

theorem digitsValue_toDigits (n : Nat) : digitsValue (Nat.toDigits 10 n) = n := by
  rw [digitsValue_eq _ (fun c hc => mem_toDigits_isDigit hc)]
  exact Nat.ofDigitChars_ten_toDigits

theorem digitChar_aux : ∀ k, k < 10 → Nat.digitChar k = Char.ofNat (48 + k) := by decide

theorem digitChar_of_isDigit {c : Char} (h : c.isDigit = true) : Nat.digitChar (c.toNat - 48) = c := by
  have h' := isDigit_iff'.mp h
  rw [digitChar_aux _ (by omega), show 48 + (c.toNat - 48) = c.toNat by omega, ← char_eq_ofNat]

theorem ofDigitChars_pos (c : Char) (cs : List Char) (hc : c.isDigit = true) (h0 : c ≠ '0') :
    0 < Nat.ofDigitChars 10 (c :: cs) 0 := by
  rw [Nat.ofDigitChars_cons, Nat.ofDigitChars_eq_ofDigitChars_zero]
  have h' := isDigit_iff'.mp hc
  have : c.toNat ≠ 48 := fun e => h0 (by rw [char_eq_ofNat c, e])
  have : 0 < 10 ^ cs.length := Nat.pow_pos (by decide)
  simp only [show '0'.toNat = 48 from rfl]
  have : 0 < 10 ^ cs.length * (10 * 0 + (c.toNat - 48)) := Nat.mul_pos (by omega) (by omega)
  omega

/-- A digit string without a leading zero is the spelling of its value. -/
theorem toDigits_ofDigitChars : ∀ (n : Nat) (D : List Char), D.length = n → (∀ c ∈ D, c.isDigit = true) →
    D ≠ [] → D.head? ≠ some '0' → Nat.toDigits 10 (Nat.ofDigitChars 10 D 0) = D := by
  intro n
  induction n with
  | zero => intro D hl _ hne; exact absurd (List.eq_nil_of_length_eq_zero hl) hne
  | succ n ih =>
    intro D hl h hne h0
    rcases List.eq_nil_or_concat D with hD | ⟨D', c, rfl⟩
    · exact absurd hD hne
    simp only [List.concat_eq_append] at *
    have hc : c.isDigit = true := h c (by simp)
    have hcl : c.toNat - 48 < 10 := by have := isDigit_iff'.mp hc; omega
    rw [Nat.ofDigitChars_append, Nat.ofDigitChars_cons, Nat.ofDigitChars_nil]
    simp only [show '0'.toNat = 48 from rfl]
    by_cases hD' : D' = []
    · subst hD'
      simp only [Nat.ofDigitChars_nil, Nat.mul_zero, Nat.zero_add, List.nil_append]
      rw [Nat.toDigits_of_lt_base hcl, digitChar_of_isDigit hc]
    · obtain ⟨d, ds, rfl⟩ : ∃ d ds, D' = d :: ds := List.exists_cons_of_ne_nil hD'
      have hd : d.isDigit = true := h d (by simp)
      have hd0 : d ≠ '0' := by intro e; subst e; simp at h0
      have hpos := ofDigitChars_pos d ds hd hd0
      rw [← Nat.toDigits_append_toDigits (by decide) hpos hcl,
        ih (d :: ds) (by simp at hl ⊢; omega) (fun x hx => h x (by simp at hx ⊢; rcases hx with hx | hx <;> simp [hx]))
          (by simp) (by simpa using hd0),
        Nat.toDigits_of_lt_base hcl, digitChar_of_isDigit hc]

end PyLean.Decimal
