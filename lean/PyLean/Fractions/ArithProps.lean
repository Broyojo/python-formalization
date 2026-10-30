import PyLean.Fractions.Arith

/-!
Registered properties of the arithmetic operators, `**` and comparisons.
Operands are `Fraction` objects, so they satisfy the class invariant
`Frac.Normal`; an int operand `n` is `⟨n, 1⟩`, which is normal too.
-/

namespace PyLean.Fractions

open PyLean

/-- Invariant (class invariant plus exactness): `a + b`, `a - b`, `a * b` and
`a / b` return a Fraction in lowest terms with a positive denominator whose
value is the exact rational result; `a / 0` raises `ZeroDivisionError`. For
all Fraction (or int) operands. -/
def ArithExact : Prop :=
  ∀ a b : Frac, a.Normal → b.Normal →
    ((add a b).Normal ∧
      (add a b).num * (a.den * b.den) = (a.num * b.den + b.num * a.den) * (add a b).den) ∧
    ((sub a b).Normal ∧
      (sub a b).num * (a.den * b.den) = (a.num * b.den - b.num * a.den) * (sub a b).den) ∧
    ((mul a b).Normal ∧ (mul a b).num * (a.den * b.den) = (a.num * b.num) * (mul a b).den) ∧
    (b.num ≠ 0 → ∃ r, div a b = .ok r ∧ r.Normal ∧
      r.num * (a.den * b.num) = (a.num * b.den) * r.den) ∧
    (b.num = 0 → (div a b).raises "ZeroDivisionError")

theorem normal_zero_den {b : Frac} (hb : b.Normal) (h0 : b.num = 0) : b.den = 1 := by
  have := hb.2
  rw [h0, Int.zero_gcd] at this
  have := hb.1
  omega

theorem arithExact_proven : ArithExact := by
  intro a b ha hb
  refine ⟨add_spec a b ha hb, sub_spec a b ha hb, mul_spec a b ha hb,
    fun h => div_spec a b ha hb h, fun h => ?_⟩
  have h1 := normal_zero_den hb h
  refine ⟨.zeroDivisionError "Fraction(1, 0)", ?_, rfl⟩
  simp only [div, h, h1, zeroDivMsg, strInt]
  rfl

/-- `__pow__` docstring, fractions.py:886-891: "If b is an integer, the
result will be rational." For every Fraction `a` and int `e`: the result is in
lowest terms with positive denominator and equals `a ** e` exactly, and
`0 ** e` raises `ZeroDivisionError` for `e < 0`. -/
def PowExact : Prop :=
  ∀ a : Frac, a.Normal → ∀ e : Int,
    (0 ≤ e → ∃ r, pow a e = .ok r ∧ r.Normal ∧
      r.num = a.num ^ e.toNat ∧ r.den = a.den ^ e.toNat) ∧
    (e < 0 → a.num ≠ 0 → ∃ r, pow a e = .ok r ∧ r.Normal ∧
      r.num * a.num ^ (-e).toNat = a.den ^ (-e).toNat * r.den) ∧
    (e < 0 → a.num = 0 → (pow a e).raises "ZeroDivisionError")

theorem powExact_proven : PowExact := by
  intro a ha e
  obtain ⟨hd, hg⟩ := ha
  refine ⟨fun he => ?_, fun he hn => ?_, fun he hn => ?_⟩
  · refine ⟨_, by simp only [pow, he, ↓reduceIte]; rfl, ⟨Int.pow_pos hd, ?_⟩, rfl, rfl⟩
    exact Int.pow_gcd_pow_of_gcd_eq_one hg
  · have hne : ¬ 0 ≤ e := by omega
    by_cases hpos : a.num > 0
    · refine ⟨_, by simp only [pow, hne, hpos, ↓reduceIte]; rfl, ⟨Int.pow_pos hpos, ?_⟩, ?_⟩
      · exact Int.pow_gcd_pow_of_gcd_eq_one (gcd_one_comm hg)
      · grind
    · have hneg : a.num < 0 := by omega
      have hn0 : ¬ a.num = 0 := hn
      refine ⟨_, by simp only [pow, hne, hpos, hn0, ↓reduceIte]; rfl,
        ⟨Int.pow_pos (show 0 < -a.num by omega), ?_⟩, ?_⟩
      · simp only
        apply Int.pow_gcd_pow_of_gcd_eq_one
        simp only [Int.neg_gcd, Int.gcd_neg]; exact gcd_one_comm hg
      · simp only
        rw [← Int.mul_pow, ← Int.mul_pow]
        congr 1; grind
  · have hne : ¬ 0 ≤ e := by omega
    have h1 := normal_zero_den ⟨hd, hg⟩ hn
    refine ⟨.zeroDivisionError "Fraction(1, 0)", ?_, rfl⟩
    simp only [pow, hne, hn, h1, ↓reduceIte, Int.one_pow, zeroDivMsg, strInt]
    rfl

/-- Invariant: `==` (which compares numerator and denominator,
fractions.py:1000-1019) agrees with `<`, `<=`, `>`, `>=` (which
cross-multiply, fractions.py:1021-1058) and with the rational order, for
Fraction and int operands. -/
def CompareConsistent : Prop :=
  ∀ a b : Frac, a.Normal → b.Normal →
    (eq a b = true ↔ a.num * b.den = b.num * a.den) ∧
    (lt a b = true ↔ a.num * b.den < b.num * a.den) ∧
    (le a b = true ↔ a.num * b.den ≤ b.num * a.den) ∧
    (gt a b = true ↔ a.num * b.den > b.num * a.den) ∧
    (ge a b = true ↔ a.num * b.den ≥ b.num * a.den)

theorem normal_eq_of_cross {a b : Frac} (ha : a.Normal) (hb : b.Normal)
    (h : a.num * b.den = b.num * a.den) : a = b := by
  obtain ⟨hda, hga⟩ := ha
  obtain ⟨hdb, hgb⟩ := hb
  have d1 : a.den ∣ b.den := by
    apply dvd_of_dvd_mul_coprime (gcd_one_comm hga)
    exact ⟨b.num, by rw [h, Int.mul_comm]⟩
  have d2 : b.den ∣ a.den := by
    apply dvd_of_dvd_mul_coprime (gcd_one_comm hgb)
    exact ⟨a.num, by rw [← h, Int.mul_comm]⟩
  have hden : a.den = b.den := Int.dvd_antisymm (by omega) (by omega) d1 d2
  have hnum : a.num = b.num := by
    rw [hden] at h
    exact Int.eq_of_mul_eq_mul_right (by omega) h
  cases a; cases b; simp_all

theorem compareConsistent_proven : CompareConsistent := by
  intro a b ha hb
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [eq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2]
  · have := normal_eq_of_cross ha hb h
    subst this; simp [eq]
  · simp only [lt, decide_eq_true_eq]; rw [Int.mul_comm a.den]
  · simp only [le, decide_eq_true_eq]; rw [Int.mul_comm a.den]
  · simp only [gt, decide_eq_true_eq]; rw [Int.mul_comm a.den]
  · simp only [ge, decide_eq_true_eq]; rw [Int.mul_comm a.den]

/-- Invariant (Python `divmod` semantics, Reference "Binary arithmetic
operations"): for `b ≠ 0`, `divmod(a, b) == (a // b, a % b)`,
`a == (a // b) * b + a % b` exactly, the remainder is a normalized Fraction
with the sign of `b` and smaller magnitude; `b == 0` raises
`ZeroDivisionError` for all three. -/
def DivmodConsistent : Prop :=
  ∀ a b : Frac, a.Normal → b.Normal →
    (b.num ≠ 0 → ∃ q m, floordiv a b = .ok q ∧ mod a b = .ok m ∧ divmod a b = .ok (q, m) ∧
      m.Normal ∧
      m.num * (a.den * b.den) = (a.num * b.den - q * b.num * a.den) * m.den ∧
      (0 < b.num → 0 ≤ m.num ∧ m.num * b.den < b.num * m.den) ∧
      (b.num < 0 → m.num ≤ 0 ∧ b.num * m.den < m.num * b.den)) ∧
    (b.num = 0 → (floordiv a b).raises "ZeroDivisionError" ∧ (mod a b).raises "ZeroDivisionError" ∧
      (divmod a b).raises "ZeroDivisionError")

theorem divmodConsistent_proven : DivmodConsistent := by
  intro a b ha hb
  obtain ⟨hda, hga⟩ := ha
  obtain ⟨hdb, hgb⟩ := hb
  refine ⟨fun hnz => ?_, fun hz => ?_⟩
  · have hq : a.den * b.num ≠ 0 := Int.mul_ne_zero (by omega) hnz
    have hq' : b.num * a.den ≠ 0 := by rw [Int.mul_comm]; exact hq
    have hD : a.den * b.den ≠ 0 := Int.mul_ne_zero (by omega) (by omega)
    obtain ⟨m, hm, hmn, hmv⟩ := normalize_ok (n := pyMod (a.num * b.den) (a.den * b.num)) hD
    refine ⟨pyDiv (a.num * b.den) (a.den * b.num), m, ?_, ?_, ?_, hmn, ?_, ?_, ?_⟩
    · simp only [floordiv, hq, ↓reduceIte]
    · simp only [mod, hq', ↓reduceIte, ofInts]; rw [Int.mul_comm b.num]; exact hm
    · simp only [divmod, hq, ↓reduceIte, ofInts, hm]; rfl
    · simp only [Frac.Rep] at hmv
      have hdef := Int.fmod_add_fdiv_mul (a.num * b.den) (a.den * b.num)
      simp only [pyMod, pyDiv] at hmv ⊢
      grind
    · intro hbpos
      simp only [Frac.Rep] at hmv
      have hpos : 0 < a.den * b.num := Int.mul_pos hda hbpos
      have h0 := Int.fmod_nonneg_of_pos (a.num * b.den) hpos
      have h1 := Int.fmod_lt_of_pos (a.num * b.den) hpos
      simp only [pyMod] at hmv
      generalize (a.num * b.den).fmod (a.den * b.num) = r at hmv h0 h1
      have hmd := hmn.1
      constructor
      · -- m.num * D = r * m.den with D > 0, r ≥ 0
        apply Int.le_of_mul_le_mul_right (a := a.den * b.den) _ (Int.mul_pos hda hdb)
        rw [hmv, Int.zero_mul]; exact Int.mul_nonneg h0 (by omega)
      · apply lt_of_mul_lt_mul_r (z := a.den)  _ hda
        have : m.num * b.den * a.den = r * m.den := by rw [← hmv]; grind
        rw [this]
        have := mul_lt_mul_r h1 hmd
        grind
    · intro hbneg
      simp only [Frac.Rep] at hmv
      have hpos : 0 < -(a.den * b.num) := by
        have := Int.mul_neg_of_pos_of_neg hda hbneg; omega
      have e := Int.neg_fmod_neg (a.num * b.den) (a.den * b.num)
      have h0 := Int.fmod_nonneg_of_pos (-(a.num * b.den)) hpos
      have h1 := Int.fmod_lt_of_pos (-(a.num * b.den)) hpos
      rw [e] at h0 h1
      simp only [pyMod] at hmv
      generalize (a.num * b.den).fmod (a.den * b.num) = r at hmv h0 h1 e
      have hmd := hmn.1
      constructor
      · apply Int.le_of_mul_le_mul_right (a := a.den * b.den) _ (Int.mul_pos hda hdb)
        rw [hmv, Int.zero_mul]
        have := Int.mul_nonneg (show 0 ≤ -r by omega) (Int.le_of_lt hmd)
        grind
      · apply lt_of_mul_lt_mul_r (z := a.den)  _ hda
        have : m.num * b.den * a.den = r * m.den := by rw [← hmv]; grind
        rw [this]
        have := mul_lt_mul_r (show -r < -(a.den * b.num) by omega) hmd
        grind
  · have hq : a.den * b.num = 0 := by rw [hz, Int.mul_zero]
    have hq' : b.num * a.den = 0 := by rw [hz, Int.zero_mul]
    refine ⟨⟨.zeroDivisionError intDivZeroMsg, ?_, rfl⟩, ⟨.zeroDivisionError intDivZeroMsg, ?_, rfl⟩,
      ⟨.zeroDivisionError intDivZeroMsg, ?_, rfl⟩⟩
    · simp only [floordiv, hq, ↓reduceIte]
    · simp only [mod, hq', ↓reduceIte]; rfl
    · simp only [divmod, hq, ↓reduceIte]; rfl

end PyLean.Fractions
