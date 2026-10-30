import PyLean.Fractions.StrProps

/-!
`__format__` properties: the empty spec gives `str`, and float-style
formatting does not raise for a valid spec.
-/

namespace PyLean.Fractions

open PyLean

theorem strInt_eq_sign (i : Int) :
    strInt i = (strInt (i.natAbs : Int)).map (fun t => (if i < 0 then ['-'] else []) ++ t) := by
  simp only [strInt, Int.natAbs_natCast]
  split
  · rfl
  · simp [Except.map]

theorem rep_nonpos (c : Char) (k : Int) (h : k ≤ 0) : rep c k = [] := by
  simp [rep]; omega

/-- Python convention for `__format__` (and the 3.13 docs for Fraction
formatting without a presentation type): `format(x, '') == str(x)`, including
which exception is raised. For every Fraction. -/
def FormatEmptyIsStr : Prop := ∀ x : Frac, x.Normal → format x [] = str x

theorem formatEmptyIsStr_proven : FormatEmptyIsStr := by
  intro x ⟨hd, _⟩
  have hm : matchGeneral [] = some ⟨none, none, [], false, none, none⟩ := rfl
  have hdabs : ((x.den.natAbs : Nat) : Int) = x.den := by omega
  simp only [format, hm, formatGeneral, specInt, fmtIntSep, str]
  rw [strInt_eq_sign x.num]
  cases hn : strInt (x.num.natAbs : Int) with
  | error e => simp [bind, Except.bind, Except.map]
  | ok t =>
    simp only [bind, Except.bind, Except.map, pure, Except.pure]
    by_cases h1 : x.den = 1
    · have : ¬ (x.den > 1 ∨ false = true) := by simp; omega
      simp only [this, h1, ↓reduceIte]
      congr 1
      simp only [alignPad, Option.getD, ↓reduceIte]
      rw [rep_nonpos _ _ (by omega)]
      simp
    · have : (x.den > 1 ∨ false = true) := by left; omega
      simp only [this, h1, ↓reduceIte]
      cases hdn : strInt x.den with
      | error e => rfl
      | ok td =>
        simp only
        congr 1
        simp only [alignPad, Option.getD, ↓reduceIte]
        rw [rep_nonpos _ _ (by omega)]
        simp

/-- Docs (`Fraction.__format__`): with a presentation type `'e'`, formatting
"follows the rules outlined for the float type", which never raise for a
valid spec. For every Fraction `x` and precision `p`, `format(x, f'.{p}e')`
returns a string. -/
def FormatETotal : Prop :=
  ∀ x : Frac, x.Normal → ∀ p : Nat, ∃ s, format x ('.' :: (D p ++ ['e'])) = .ok s

theorem numDigits_big : numDigits (10 ^ 4300 + 1) > maxStrDigits := by
  unfold numDigits maxStrDigits
  apply Nat.lt_of_not_le
  intro h
  have := (Nat.length_toDigits_le_iff (b := 10) (n := 10 ^ 4300 + 1) (k := 4300) (by decide)
    (by decide)).mp h
  omega

/-- `format(Fraction(10**4300 + 1, 10**4300), '.2e')` raises `ValueError`
(int string-conversion limit, from `str(abs(n))` in `_round_to_figures`); the
exact answer is `'1.00e+00'`. -/
theorem formatETotal_refuted : ¬FormatETotal := by
  intro h
  have hx : (⟨10 ^ 4300 + 1, 10 ^ 4300⟩ : Frac).Normal := by
    refine ⟨Int.pow_pos (by decide), ?_⟩
    simp only
    rw [Int.add_comm, Int.gcd_add_self_left]
    exact Int.gcd_one_left _
  obtain ⟨s, hs⟩ := h _ hx 2
  have hspec : ('.' :: (D 2 ++ ['e'])) = ['.', '2', 'e'] := rfl
  have hg : matchGeneral ['.', '2', 'e'] = none := rfl
  have hf : matchFloat ['.', '2', 'e'] =
      some ⟨none, none, [], false, false, false, none, none, some ['2'], none, 'e'⟩ := rfl
  have hp : pyIntOfDigits ['2'] = .ok 2 := rfl
  have hbig : numDigits (Int.natAbs (10 ^ 4300 + 1 : Int)) > maxStrDigits := by
    have : Int.natAbs (10 ^ 4300 + 1 : Int) = 10 ^ 4300 + 1 := by omega
    rw [this]; exact numDigits_big
  have hrf : roundToFigures (10 ^ 4300 + 1) (10 ^ 4300) 3 = .error (.valueError limitToStrMsg) := by
    have hne : (10 ^ 4300 + 1 : Int) ≠ 0 := by omega
    simp only [roundToFigures, hne, ↓reduceIte, strInt, Int.natAbs_natCast]
    simp only [show ¬ ((((10 ^ 4300 + 1 : Int).natAbs : Nat) : Int) < 0) by omega, hbig, ↓reduceIte]
    rfl
  rw [hspec] at hs
  simp only [format, hg, hf, Option.isNone_none, Bool.true_or, ↓reduceIte, formatFloat, specInt,
    hp] at hs
  simp [bind, Except.bind, hrf] at hs

end PyLean.Fractions
