import PyLean.LongObj.Pylong

/-!
`_div2n1n`, `_div3n2n`, `_int2digits`, `_digits2int` and `_divmod_pos` of
`Lib/_pylong.py` are exact: the Burnikel-Ziegler recursion under the docstring's
preconditions, including that `while r < 0` adds `b` at most twice.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

theorem div3Loop_spec {b q r A : Int} (hb : 0 < b) (hA : A = q * b + r) (h1 : -(2 * b) < r)
    (h2 : r < b) : ∃ q' r', div3Loop b 4 q r = .ok (q', r') ∧ A = q' * b + r' ∧ 0 ≤ r' ∧ r' < b := by
  by_cases h3 : r < 0
  · by_cases h4 : r + b < 0
    · refine ⟨q - 1 - 1, r + b + b, ?_, ?_, by omega, by omega⟩
      · rw [div3Loop, if_pos h3, div3Loop, if_pos h4, div3Loop, if_neg (by omega)]
      · rw [hA, Int.sub_mul, Int.sub_mul, Int.one_mul]
        omega
    · refine ⟨q - 1, r + b, ?_, ?_, by omega, by omega⟩
      · rw [div3Loop, if_pos h3, div3Loop, if_neg h4]
      · rw [hA, Int.sub_mul, Int.one_mul]
        omega
  · exact ⟨q, r, by rw [div3Loop, if_neg h3], hA, by omega, h2⟩

/-- The arithmetic of `_div3n2n` after its first branch: the estimate `q` is at most two
too large. -/
theorem div3_arith {a12 a3 b b1 b2 P q r : Nat} (hP : 0 < P) (hb : b = b1 * P + b2) (hb2 : b2 < P)
    (ha3 : a3 < P) (hb1 : P ≤ 2 * b1) (hq : q < P) (hdec : a12 = q * b1 + r)
    (hR : r * P + a3 < b + q * b2) :
    ∃ q' r' : Int, div3Loop b 4 q (((r * P + a3 : Nat) : Int) - (q : Int) * (b2 : Int)) =
        .ok (q', r') ∧ q'.toNat = (a12 * P + a3) / b ∧ r'.toNat = (a12 * P + a3) % b := by
  have hbpos : 0 < b := by
    have : 0 < b1 * P := Nat.mul_pos (by omega) hP
    omega
  have hprod : q * b2 < 2 * b := by
    have h1 : q * b2 < P * P := Nat.mul_lt_mul'' hq hb2
    have h2 : P * P ≤ (2 * b1) * P := Nat.mul_le_mul_right _ hb1
    have h3 : (2 * b1) * P = 2 * (b1 * P) := Nat.mul_assoc ..
    omega
  obtain ⟨X, hX⟩ : ∃ X, (a12 * P + a3 : Nat) = X := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, (r * P + a3 : Nat) = Y := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, q * b2 = Z := ⟨_, rfl⟩
  have hnat : X + Z = q * b + Y := by
    rw [← hX, ← hY, ← hZ, hdec, hb, Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
    omega
  have hA : (X : Int) = (q : Int) * (b : Int) + ((Y : Int) - (Z : Int)) := by
    have : ((X + Z : Nat) : Int) = ((q * b + Y : Nat) : Int) := by rw [hnat]
    push_cast at this
    omega
  rw [hZ] at hprod
  rw [hY, hX]
  have hZc : (q : Int) * (b2 : Int) = (Z : Int) := by rw [← hZ]; push_cast; rfl
  rw [hZc]
  have hr : Y < b + Z := by rw [← hY, ← hZ]; exact hR
  obtain ⟨q', r', e, h1, h2, h3⟩ := div3Loop_spec (b := (b : Int)) (by omega) hA (by omega) (by omega)
  have hq0 : 0 ≤ q' := by
    apply Int.not_lt.1
    intro hc
    have : q' * (b : Int) ≤ (-1) * (b : Int) :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega
  obtain ⟨qn, rfl⟩ := Int.eq_ofNat_of_zero_le hq0
  obtain ⟨rn, rfl⟩ := Int.eq_ofNat_of_zero_le h2
  have hu : rn + b * qn = X := by
    have : ((rn + b * qn : Nat) : Int) = (X : Int) := by
      push_cast
      rw [h1, Int.mul_comm (b : Int), Int.add_comm]
    exact_mod_cast this
  have ⟨u1, u2⟩ := (Nat.div_mod_unique hbpos).2 ⟨hu, by omega⟩
  exact ⟨qn, rn, e, by simpa using u1.symm, by simpa using u2.symm⟩

/-- Preconditions of `_div2n1n`: `b` has exactly `n` bits, `a < 2**n * b`. -/
def Pre2 (a b n : Nat) : Prop := 1 ≤ n ∧ 2 ^ (n - 1) ≤ b ∧ b < 2 ^ n ∧ a < 2 ^ n * b

/-- What `_div2n1n` needs of `_div3n2n`: `b = b1*2**n + b2` with `b1` of exactly `n` bits,
`a3 < 2**n` and `a12 < b`. -/
def Pre3 (a12 a3 b b1 b2 n : Nat) : Prop :=
  1 ≤ n ∧ 2 ^ (n - 1) ≤ b1 ∧ b1 < 2 ^ n ∧ b2 < 2 ^ n ∧ a3 < 2 ^ n ∧ b = b1 * 2 ^ n + b2 ∧ a12 < b

theorem pow_half {n : Nat} (h : 1 ≤ n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.pow_succ']

theorem shr1 (x : Nat) : x >>> 1 = x / 2 := by simp [Nat.shiftRight_eq_div_pow]

/-- One level of the recursion on an even width `2 * h`, given `_div3n2n` at `h`. -/
theorem div2_even {D3 : Nat → Nat → Nat → Nat → Nat → Nat → Py (Nat × Nat)} {a b h : Nat}
    (hD : ∀ a12 a3 b b1 b2, Pre3 a12 a3 b b1 b2 h →
      D3 a12 a3 b b1 b2 h = .ok ((a12 * 2 ^ h + a3) / b, (a12 * 2 ^ h + a3) % b))
    (hp : Pre2 a b (2 * h)) (hh : 1 ≤ h) :
    ∃ q1 r1 q2 r2,
      D3 (a >>> (2 * h)) ((a >>> h) &&& ((1 <<< h) - 1)) b (b >>> h)
        (b &&& ((1 <<< h) - 1)) h = .ok (q1, r1) ∧
      D3 r1 (a &&& ((1 <<< h) - 1)) b (b >>> h) (b &&& ((1 <<< h) - 1)) h = .ok (q2, r2) ∧
      (q1 <<< h) ||| q2 = a / b ∧ r2 = a % b := by
  obtain ⟨_, hlo, hhi, ha⟩ := hp
  obtain ⟨P, hPd⟩ : ∃ P, 2 ^ h = P := ⟨_, rfl⟩
  have hPpos : 0 < P := by rw [← hPd]; exact Nat.pow_pos (by decide)
  have hPP : 2 ^ (2 * h) = P * P := by rw [← hPd, ← Nat.pow_add]; congr 1; omega
  have hmask : (1 <<< h) - 1 = 2 ^ h - 1 := by rw [Nat.one_shiftLeft]
  have hm : ∀ x, x &&& ((1 <<< h) - 1) = x % P := by
    intro x; rw [hmask, Nat.and_two_pow_sub_one_eq_mod, hPd]
  have hs : ∀ x, x >>> h = x / P := by intro x; rw [Nat.shiftRight_eq_div_pow, hPd]
  have hs2 : ∀ x, x >>> (2 * h) = x / (P * P) := by intro x; rw [Nat.shiftRight_eq_div_pow, hPP]
  simp only [hm, hs, hs2]
  rw [hPP] at ha hhi
  have hb0 : 0 < b := by
    have : 0 < 2 ^ (2 * h - 1) := Nat.pow_pos (by decide)
    omega
  obtain ⟨b1, hb1⟩ : ∃ b1, b / P = b1 := ⟨_, rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ b2, b % P = b2 := ⟨_, rfl⟩
  rw [hb1, hb2]
  have hbd : b = b1 * P + b2 := by
    rw [← hb1, ← hb2, Nat.mul_comm]; exact (Nat.div_add_mod b P).symm
  have hb2lt : b2 < P := by rw [← hb2]; exact Nat.mod_lt _ hPpos
  have hb1hi : b1 < P := by
    rw [← hb1]; exact Nat.div_lt_of_lt_mul hhi
  have hb1lo : 2 ^ (h - 1) ≤ b1 := by
    rw [← hb1]
    apply (Nat.le_div_iff_mul_le hPpos).2
    have e : 2 ^ (2 * h - 1) = 2 ^ (h - 1) * P := by
      rw [← hPd, ← Nat.pow_add]; congr 1; omega
    omega
  obtain ⟨a1, ha1⟩ : ∃ a1, a / (P * P) = a1 := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, a / P = X := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a2, X % P = a2 := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ a3, a % P = a3 := ⟨_, rfl⟩
  have hX1 : X / P = a1 := by
    rw [← hX, ← ha1, Nat.div_div_eq_div_mul]
  have hXd : X = a1 * P + a2 := by
    rw [← hX1, ← ha2, Nat.mul_comm]; exact (Nat.div_add_mod X P).symm
  have had : a = X * P + a3 := by
    rw [← hX, ← ha3, Nat.mul_comm]; exact (Nat.div_add_mod a P).symm
  have ha2lt : a2 < P := by rw [← ha2]; exact Nat.mod_lt _ hPpos
  have ha3lt : a3 < P := by rw [← ha3]; exact Nat.mod_lt _ hPpos
  have ha1lt : a1 < b := by
    rw [← ha1]; exact Nat.div_lt_of_lt_mul ha
  rw [hX, ha2, ha3, ha1]
  have h1 := hD a1 a2 b b1 b2 ⟨hh, hb1lo, hPd ▸ hb1hi, hPd ▸ hb2lt, hPd ▸ ha2lt, hPd ▸ hbd, ha1lt⟩
  rw [hPd, ← hXd] at h1
  have hr1 : X % b < b := Nat.mod_lt _ hb0
  have h2 := hD (X % b) a3 b b1 b2 ⟨hh, hb1lo, hPd ▸ hb1hi, hPd ▸ hb2lt, hPd ▸ ha3lt, hPd ▸ hbd, hr1⟩
  rw [hPd] at h2
  obtain ⟨Y, hY⟩ : ∃ Y, X % b * P + a3 = Y := ⟨_, rfl⟩
  rw [hY] at h2
  have hYlt : Y < b * P := by
    have : (X % b + 1) * P ≤ b * P := Nat.mul_le_mul_right _ hr1
    rw [Nat.add_mul] at this
    omega
  have hq2 : Y / b < P := Nat.div_lt_of_lt_mul hYlt
  have hor : (X / b) <<< h ||| (Y / b) = X / b * P + Y / b := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (hPd ▸ hq2), Nat.shiftLeft_eq, hPd]
  have hu : Y % b + b * (X / b * P + Y / b) = a := by
    have e1 := Nat.mod_add_div X b
    have e2 := Nat.mod_add_div Y b
    have e3 : b * (X / b * P + Y / b) = b * (X / b) * P + b * (Y / b) := by
      rw [Nat.mul_add, Nat.mul_assoc]
    have e4 : X * P = X % b * P + b * (X / b) * P := by
      conv => lhs; rw [← e1]
      rw [Nat.add_mul]
    rw [e3, had, e4]
    omega
  have hmod : Y % b < b := Nat.mod_lt _ hb0
  obtain ⟨u1, u2⟩ := (Nat.div_mod_unique hb0).2 ⟨hu, hmod⟩
  exact ⟨X / b, X % b, Y / b, Y % b, h1, h2, by rw [hor, u1], u2.symm⟩

theorem div_spec : ∀ f,
    (∀ a b n, Pre2 a b n → 2 * n + 2 ≤ f → div2n1n f a b n = .ok (a / b, a % b)) ∧
    (∀ a12 a3 b b1 b2 n, Pre3 a12 a3 b b1 b2 n → 2 * n + 3 ≤ f →
      div3n2n f a12 a3 b b1 b2 n = .ok ((a12 * 2 ^ n + a3) / b, (a12 * 2 ^ n + a3) % b))
  | 0 => ⟨fun _ _ n _ h => by omega, fun _ _ _ _ _ n _ h => by omega⟩
  | f + 1 => by
    obtain ⟨ih2, ih3⟩ := div_spec f
    constructor
    · intro a b n hp hf
      rw [div2n1n]
      by_cases hbase : (bitLength a : Int) - n ≤ 4000
      · rw [if_pos hbase]
      · rw [if_neg hbase]
        obtain ⟨hn1, hlo, hhi, ha⟩ := hp
        have hbl : bitLength a ≤ 2 * n := by
          apply bitLength_le_of_lt'
          rw [show 2 * n = n + n by omega, Nat.pow_add]
          exact Nat.lt_of_lt_of_le ha (Nat.mul_le_mul_left _ (Nat.le_of_lt hhi))
        have hn4 : 4000 < n := by omega
        have hpar : n &&& 1 = n % 2 := Nat.and_one_is_mod n
        have hb0 : 0 < b := by
          have : 0 < 2 ^ (n - 1) := Nat.pow_pos (by decide)
          omega
        by_cases hodd : n % 2 = 0
        · obtain ⟨h, rfl⟩ : ∃ h, n = 2 * h := ⟨n / 2, by omega⟩
          have hhalf : (2 * h) >>> 1 = h := by rw [shr1]; omega
          obtain ⟨q1, r1, q2, r2, e1, e2, e3, e4⟩ := div2_even (D3 := div3n2n f)
            (fun a12 a3 b b1 b2 hp => ih3 a12 a3 b b1 b2 h hp (by omega))
            ⟨hn1, hlo, hhi, ha⟩ (by omega)
          simp only [hpar, hodd, ne_eq, not_true_eq_false, ↓reduceIte, hhalf]
          simp only [e1, bindOk, e2, pureOk, e3, e4]
        · obtain ⟨h, hh⟩ : ∃ h, n + 1 = 2 * h := ⟨(n + 1) / 2, by omega⟩
          have hhalf : (n + 1) >>> 1 = h := by rw [shr1]; omega
          have hp2 : Pre2 (a <<< 1) (b <<< 1) (2 * h) := by
            rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, ← hh]
            have e0 : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ ..
            refine ⟨by omega, ?_, ?_, ?_⟩
            · rw [Nat.add_sub_cancel]
              have := pow_half hn1
              simp only [Nat.pow_one]
              omega
            · simp only [Nat.pow_one]
              omega
            · simp only [Nat.pow_one]
              rw [e0, Nat.mul_assoc]
              have : a < 2 ^ n * (2 * (b * 2)) := by
                have : 2 ^ n * b ≤ 2 ^ n * (2 * (b * 2)) := Nat.mul_le_mul_left _ (by omega)
                omega
              have h2 : 2 ^ n * (2 * (b * 2)) = 2 * (2 ^ n * (b * 2)) := by
                rw [Nat.mul_left_comm]
              have h3 : 0 < 2 ^ n * b := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
              have h4 : a * 2 < 2 ^ n * b * 2 := by omega
              have h5 : 2 ^ n * b * 2 ≤ 2 * (2 ^ n * (b * 2)) := by
                rw [Nat.mul_assoc]
                omega
              omega
          obtain ⟨q1, r1, q2, r2, e1, e2, e3, e4⟩ := div2_even (D3 := div3n2n f)
            (fun a12 a3 b b1 b2 hp => ih3 a12 a3 b b1 b2 h hp (by omega)) hp2 (by omega)
          have hdv : (a <<< 1) / (b <<< 1) = a / b := by
            rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
            simp only [Nat.pow_one]
            rw [Nat.mul_comm a, Nat.mul_comm b, Nat.mul_div_mul_left _ _ (by decide)]
          have hmd : (a <<< 1) % (b <<< 1) = 2 * (a % b) := by
            rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
            simp only [Nat.pow_one]
            rw [Nat.mul_comm a, Nat.mul_comm b, Nat.mul_mod_mul_left]
          have hodd1 : n % 2 ≠ 0 := hodd
          simp only [hpar, ne_eq, hodd, not_false_eq_true, ↓reduceIte, hhalf]
          have hn2 : n + 1 = 2 * h := hh
          rw [hn2]
          simp only [e1, bindOk, e2, pureOk, e3, hdv, e4, hmd]
          congr 2
          rw [shr1]
          omega
    · intro a12 a3 b b1 b2 n hp hf
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hp
      rw [div3n2n]
      obtain ⟨P, hPd⟩ : ∃ P, 2 ^ n = P := ⟨_, rfl⟩
      rw [hPd] at h3 h4 h5 h6 ⊢
      have hPpos : 0 < P := by rw [← hPd]; exact Nat.pow_pos (by decide)
      have hhalf : P ≤ 2 * b1 := by
        have := pow_half h1
        omega
      have hshr : a12 >>> n = a12 / P := by rw [Nat.shiftRight_eq_div_pow, hPd]
      have hor : ∀ r, (r <<< n) ||| a3 = r * P + a3 := by
        intro r
        rw [← Nat.shiftLeft_add_eq_or_of_lt (hPd ▸ h5), Nat.shiftLeft_eq, hPd]
      by_cases hc : a12 >>> n = b1
      · rw [if_pos hc]
        rw [hshr] at hc
        have hone : (1 <<< n) - 1 = P - 1 := by rw [Nat.one_shiftLeft, hPd]
        have hshl : b1 <<< n = b1 * P := by rw [Nat.shiftLeft_eq, hPd]
        rw [hone, hshl]
        have hdm := Nat.div_add_mod a12 P
        rw [hc] at hdm
        obtain ⟨e, he⟩ : ∃ e, a12 % P = e := ⟨_, rfl⟩
        rw [he, Nat.mul_comm] at hdm
        have he2 : e < b2 := by
          rw [h6] at h7
          omega
        obtain ⟨q, hq⟩ : ∃ q, P - 1 = q := ⟨_, rfl⟩
        rw [hq]
        have hP1 : P = q + 1 := by omega
        have hr : a12 - b1 * P + b1 = e + b1 := by omega
        have hdec : a12 = q * b1 + (e + b1) := by
          rw [← hdm, hP1, Nat.mul_add, Nat.mul_one, Nat.mul_comm b1 q]
          omega
        have hR : (e + b1) * P + a3 < b + q * b2 := by
          rw [Nat.add_mul, h6]
          have h8 : (e + 1) * P ≤ b2 * P := Nat.mul_le_mul_right _ he2
          rw [Nat.add_mul, Nat.one_mul] at h8
          have h9 : b2 * P = q * b2 + b2 := by
            rw [hP1, Nat.mul_add, Nat.mul_one, Nat.mul_comm]
          omega
        obtain ⟨q', r', e1, e2, e3⟩ := div3_arith hPpos h6 h4 h5 hhalf (by omega) hdec hR
        rw [hr]
        simp only [pureOk, bindOk, hor]
        rw [e1]
        simp only [bindOk, pureOk, e2, e3]
      · rw [if_neg hc]
        rw [hshr] at hc
        have hlt : a12 / P < b1 := by
          have h8 : a12 / P ≤ b1 := by
            have h9 : a12 < (b1 + 1) * P := by
              rw [Nat.add_mul, Nat.one_mul]
              omega
            have := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h9 : a12 < P * (b1 + 1))
            omega
          omega
        have ha12 : a12 < P * b1 := by
          have h9 := Nat.div_add_mod a12 P
          have h10 : a12 % P < P := Nat.mod_lt _ hPpos
          have h11 : P * (a12 / P + 1) ≤ P * b1 := Nat.mul_le_mul_left _ hlt
          rw [Nat.mul_add] at h11
          omega
        have hb1pos : 0 < b1 := by omega
        have hp2 : Pre2 a12 b1 n := ⟨h1, h2, hPd ▸ h3, hPd ▸ ha12⟩
        have ed := ih2 a12 b1 n hp2 (by omega)
        have hq : a12 / b1 < P := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact ha12)
        have hdec : a12 = a12 / b1 * b1 + a12 % b1 := by
          rw [Nat.mul_comm]; exact (Nat.div_add_mod a12 b1).symm
        have hR : a12 % b1 * P + a3 < b + a12 / b1 * b2 := by
          have h8 : a12 % b1 < b1 := Nat.mod_lt _ hb1pos
          have h9 : (a12 % b1 + 1) * P ≤ b1 * P := Nat.mul_le_mul_right _ h8
          rw [Nat.add_mul, Nat.one_mul] at h9
          omega
        obtain ⟨q', r', e1, e2, e3⟩ := div3_arith hPpos h6 h4 h5 hhalf hq hdec hR
        simp only [ed, bindOk, hor]
        rw [e1]
        simp only [bindOk, pureOk, e2, e3]

/-- `_div2n1n` meets its docstring. -/
theorem div2n1n_spec {a b n : Nat} (hp : Pre2 a b n) :
    div2n1n (2 * n + 2) a b n = .ok (a / b, a % b) :=
  (div_spec _).1 a b n hp (Nat.le_refl _)

/-- `_div3n2n` is the exact division of `a12*2**n + a3` by `b = b1*2**n + b2`. -/
theorem div3n2n_spec {a12 a3 b b1 b2 n : Nat} (hp : Pre3 a12 a3 b b1 b2 n) :
    div3n2n (2 * n + 3) a12 a3 b b1 b2 n =
      .ok ((a12 * 2 ^ n + a3) / b, (a12 * 2 ^ n + a3) % b) :=
  (div_spec _).2 a12 a3 b b1 b2 n hp (Nat.le_refl _)

/-! ## `_int2digits` and `_digits2int` -/

theorem xor_shift (x s : Nat) : x ^^^ ((x >>> s) <<< s) = x % 2 ^ s := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h : j < s
  · simp [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow, h,
      Nat.not_le_of_gt h]
  · have h2 : s ≤ j := by omega
    simp [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      Nat.testBit_mod_two_pow, h, h2]

theorem i2d_spec {n : Nat} (hn : 1 ≤ n) : ∀ (f x L R : Nat), L < R → R - L < f →
    x < 2 ^ ((R - L) * n) → ∃ l, i2dInner n f x L R = .ok l ∧ l.length = R - L ∧
      (∀ d ∈ l, d < 2 ^ n) ∧ limbVal (2 ^ n) l = x
  | 0, _, _, _, _, h, _ => by omega
  | f + 1, x, L, R, h1, h2, h3 => by
    rw [i2dInner]
    by_cases he : L + 1 = R
    · rw [if_pos he]
      have hR : R - L = 1 := by omega
      rw [hR, Nat.one_mul] at h3
      refine ⟨[x], rfl, by simp [hR], ?_, by simp [limbVal_cons, limbVal_nil]⟩
      intro d hd
      simp only [List.mem_singleton] at hd
      subst hd
      exact h3
    · rw [if_neg he]
      obtain ⟨mid, hmid⟩ : ∃ mid, (L + R) >>> 1 = mid := ⟨_, rfl⟩
      have hm : mid = (L + R) / 2 := by rw [← hmid, shr1]
      have hm1 : L < mid := by omega
      have hm2 : mid < R := by omega
      obtain ⟨s, hs⟩ : ∃ s, (mid - L) * n = s := ⟨_, rfl⟩
      have hup : x >>> s = x / 2 ^ s := Nat.shiftRight_eq_div_pow ..
      have hlow : x ^^^ ((x >>> s) <<< s) = x % 2 ^ s := xor_shift x s
      have hlowlt : x % 2 ^ s < 2 ^ ((mid - L) * n) := by
        rw [hs]; exact Nat.mod_lt _ (Nat.pow_pos (by decide))
      have huplt : x / 2 ^ s < 2 ^ ((R - mid) * n) := by
        apply Nat.div_lt_of_lt_mul
        rw [← Nat.pow_add, ← hs, ← Nat.add_mul, show mid - L + (R - mid) = R - L by omega]
        exact h3
      obtain ⟨a, e1, a1, a2, a3⟩ := i2d_spec hn f _ L mid hm1 (by omega) hlowlt
      obtain ⟨b, e2, b1, b2, b3⟩ := i2d_spec hn f _ mid R hm2 (by omega) huplt
      refine ⟨a ++ b, ?_, by simp [a1, b1]; omega, ?_, ?_⟩
      · simp only [hmid, hs, hup, hlow]
        rw [← hup, hlow, e1] at *
        simp only [bindOk, e2, pureOk] at *
      · intro d hd
        rcases List.mem_append.1 hd with h | h
        · exact a2 d h
        · exact b2 d h
      · rw [limbVal_append, a1, a3, b3, ← Nat.pow_mul, Nat.mul_comm n, hs, Nat.mod_add_div]

theorem limbVal_lt {B : Nat} (hB : 0 < B) : ∀ {l : List Nat}, (∀ d ∈ l, d < B) →
    limbVal B l < B ^ l.length
  | [], _ => by simp [limbVal_nil]
  | x :: l, h => by
    have h1 := limbVal_lt hB (l := l) (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have h2 := h x (by simp)
    rw [limbVal_cons, List.length_cons, Nat.pow_succ']
    have : B * (limbVal B l + 1) ≤ B * B ^ l.length := Nat.mul_le_mul_left _ h1
    rw [Nat.mul_add] at this
    omega

/-- `_int2digits` meets its docstring: little-endian digits of `a` in base `2**n`, the
top one non-zero. -/
theorem int2digits_spec {a n : Nat} (hn : 1 ≤ n) : ∃ l, int2digits a n = .ok l ∧
    l.length = (bitLength a + n - 1) / n ∧ (∀ d ∈ l, d < 2 ^ n) ∧ limbVal (2 ^ n) l = a ∧
    (∀ h : l ≠ [], l.getLast h ≠ 0) := by
  unfold int2digits
  by_cases h0 : a = 0
  · subst h0
    have hl : (bitLength 0 + n - 1) / n = 0 := by
      have : bitLength 0 = 0 := rfl
      rw [this, Nat.zero_add]
      exact Nat.div_eq_of_lt (by omega)
    rw [if_neg (by simp), hl]
    exact ⟨[], rfl, rfl, by simp, by simp [limbVal_nil], fun h => absurd rfl h⟩
  · rw [if_pos h0]
    obtain ⟨len, hlen⟩ : ∃ len, (bitLength a + n - 1) / n = len := ⟨_, rfl⟩
    simp only [hlen]
    have hbl : 1 ≤ bitLength a := (bitLength_facts a).2.1 (by omega) |>.2
    have hdm := Nat.div_add_mod (bitLength a + n - 1) n
    have hml := Nat.mod_lt (bitLength a + n - 1) (show 0 < n by omega)
    rw [hlen] at hdm
    have hlenpos : 0 < len := by
      rw [← hlen]
      exact Nat.div_pos (by omega) (by omega)
    have hbn : bitLength a ≤ n * len := by omega
    have hlt : a < 2 ^ ((len - 0) * n) := by
      rw [Nat.sub_zero, Nat.mul_comm]
      exact Nat.lt_of_lt_of_le (bitLength_facts a).1 (Nat.pow_le_pow_right (by decide) hbn)
    obtain ⟨l, e, h1, h2, h3⟩ := i2d_spec hn (len + 1) a 0 len hlenpos (by omega) hlt
    refine ⟨l, e, by omega, h2, h3, ?_⟩
    intro hne htop
    obtain ⟨l', t, hl⟩ : ∃ l' t, l = l' ++ [t] :=
      ⟨l.dropLast, l.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    subst hl
    have ht0 : t = 0 := by simpa using htop
    subst ht0
    have hv : limbVal (2 ^ n) l' = a := by
      rw [limbVal_append] at h3
      simpa [limbVal_cons, limbVal_nil] using h3
    have hlt2 : a < (2 ^ n) ^ l'.length := by
      rw [← hv]
      exact limbVal_lt (Nat.pow_pos (by decide))
        (fun d hd => h2 d (List.mem_append_left _ hd))
    rw [← Nat.pow_mul] at hlt2
    have hbl2 := bitLength_le_of_lt' hlt2
    have hll : l'.length + 1 = len := by simpa using h1
    have : (l'.length + 1) * n = n * l'.length + n := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    have hdm2 : n * len + (bitLength a + n - 1) % n = bitLength a + n - 1 := hdm
    rw [← hll, Nat.mul_comm n (l'.length + 1), this] at hdm2
    omega

theorem d2i_spec {n : Nat} (digits : List Nat) : ∀ (f L R : Nat), L < R → R ≤ digits.length →
    R - L < f → d2iInner digits n f L R = .ok (limbVal (2 ^ n) ((digits.drop L).take (R - L)))
  | 0, _, _, _, _, h => by omega
  | f + 1, L, R, h1, h2, h3 => by
    rw [d2iInner]
    by_cases he : L + 1 = R
    · rw [if_pos he]
      have hR : R - L = 1 := by omega
      have hL : L < digits.length := by omega
      rw [hR, List.getElem?_eq_getElem hL]
      have : (digits.drop L).take 1 = [digits[L]] := by
        have h := List.drop_eq_getElem_cons hL
        rw [h]
        rfl
      rw [this]
      simp [limbVal_cons, limbVal_nil]
    · rw [if_neg he]
      obtain ⟨mid, hmid⟩ : ∃ mid, (L + R) >>> 1 = mid := ⟨_, rfl⟩
      have hm : mid = (L + R) / 2 := by rw [← hmid, shr1]
      have hm1 : L < mid := by omega
      have hm2 : mid < R := by omega
      have e1 := d2i_spec (n := n) digits f mid R hm2 h2 (by omega)
      have e2 := d2i_spec (n := n) digits f L mid hm1 (by omega) (by omega)
      simp only [hmid, e1, e2, bindOk, pureOk]
      have hsplit : (digits.drop L).take (R - L) = (digits.drop L).take (mid - L) ++
          (digits.drop mid).take (R - mid) := by
        rw [show R - L = (mid - L) + (R - mid) by omega, List.take_add, List.drop_drop,
          show L + (mid - L) = mid by omega]
      rw [hsplit, limbVal_append]
      have hlen : ((digits.drop L).take (mid - L)).length = mid - L := by
        simp; omega
      rw [hlen, ← Nat.pow_mul, Nat.shiftLeft_eq, Nat.mul_comm n]
      congr 1
      rw [Nat.add_comm, Nat.mul_comm]

/-- `_digits2int` evaluates base-`2**n` digits, little-endian. -/
theorem digits2int_spec (digits : List Nat) (n : Nat) :
    digits2int digits n = .ok (limbVal (2 ^ n) digits) := by
  unfold digits2int
  by_cases h : digits = []
  · subst h; rfl
  · rw [if_pos h]
    have hl : 0 < digits.length := List.length_pos_iff.2 h
    rw [d2i_spec digits _ 0 _ hl (Nat.le_refl _) (by omega)]
    simp

/-! ## `_divmod_pos` -/

/-- Horner in base `B` over top-first digits. -/
def be (B acc : Nat) (l : List Nat) : Nat := l.foldl (fun a d => a * B + d) acc

theorem be_nil (B acc : Nat) : be B acc [] = acc := rfl
theorem be_cons (B acc d : Nat) (l : List Nat) : be B acc (d :: l) = be B (acc * B + d) l := rfl

theorem be_add (B : Nat) : ∀ (l : List Nat) (X y : Nat),
    be B (X + y) l = X * B ^ l.length + be B y l
  | [], _, _ => by simp [be_nil]
  | d :: l, X, y => by
    rw [be_cons, be_cons, Nat.add_mul, Nat.add_assoc, be_add B l (X * B) (y * B + d),
      List.length_cons, Nat.pow_succ', Nat.mul_assoc, Nat.mul_comm B]

theorem be_reverse (B : Nat) : ∀ (l : List Nat) (acc : Nat),
    be B acc l.reverse = acc * B ^ l.length + limbVal B l
  | [], acc => by simp [be_nil, limbVal_nil]
  | d :: l, acc => by
    have h1 : be B acc (d :: l).reverse = be B acc l.reverse * B + d := by
      simp [be, List.foldl_append]
    rw [h1, be_reverse B l acc, limbVal_cons, List.length_cons, Nat.add_mul, Nat.pow_succ,
      Nat.mul_assoc, Nat.mul_comm (limbVal B l) B]
    omega

theorem dmLoop_spec {b n fuel : Nat} (hn : 1 ≤ n) (hlo : 2 ^ (n - 1) ≤ b) (hhi : b < 2 ^ n)
    (hf : fuel = 2 * n + 2) : ∀ (l : List Nat) (r : Nat) (qs : List Nat), (∀ d ∈ l, d < 2 ^ n) →
    r < b → ∃ new r', dmLoop b n fuel l r qs = .ok (qs ++ new, r') ∧ r' < b ∧
      new.length = l.length ∧ be (2 ^ n) 0 new * b + r' = be (2 ^ n) r l
  | [], r, qs, _, hr => ⟨[], r, by simp [dmLoop], hr, rfl, by simp [be_nil]⟩
  | d :: l, r, qs, hd, hr => by
    have hd0 : d < 2 ^ n := hd d (by simp)
    obtain ⟨X, hX⟩ : ∃ X, (r <<< n) + d = X := ⟨_, rfl⟩
    have hXv : X = r * 2 ^ n + d := by rw [← hX, Nat.shiftLeft_eq]
    have hlt : X < 2 ^ n * b := by
      have : (r + 1) * 2 ^ n ≤ b * 2 ^ n := Nat.mul_le_mul_right _ hr
      rw [Nat.add_mul, Nat.one_mul] at this
      rw [Nat.mul_comm (2 ^ n) b]
      omega
    have hb0 : 0 < b := by omega
    have e := div2n1n_spec (a := X) (b := b) (n := n) ⟨hn, hlo, hhi, hlt⟩
    rw [← hf] at e
    obtain ⟨new, r', e2, h1, h2, h3⟩ := dmLoop_spec hn hlo hhi hf l (X % b) (qs ++ [X / b])
      (fun x hx => hd x (List.mem_cons_of_mem _ hx)) (Nat.mod_lt _ hb0)
    refine ⟨X / b :: new, r', ?_, h1, by simp [h2], ?_⟩
    · simp only [dmLoop, hX, e, bindOk, e2, List.append_assoc, List.singleton_append]
    · have h4 : be (2 ^ n) 0 (X / b :: new) = X / b * (2 ^ n) ^ new.length + be (2 ^ n) 0 new := by
        rw [be_cons, Nat.zero_mul, Nat.zero_add]
        have := be_add (2 ^ n) new (X / b) 0
        simpa using this
      have h5 : be (2 ^ n) r (d :: l) = (X / b) * b * (2 ^ n) ^ l.length + be (2 ^ n) (X % b) l := by
        rw [be_cons, ← hXv]
        have hd2 := Nat.div_add_mod X b
        have := be_add (2 ^ n) l (X / b * b) (X % b)
        rw [Nat.mul_comm (X / b), hd2] at this
        rw [this, Nat.mul_comm b]
      rw [h4, h5, h2, ← h3, Nat.add_mul, Nat.mul_right_comm (X / b)]
      omega

/-- `_divmod_pos` is exact: `a = b*q + r`, `0 <= r < b`. -/
theorem divmodPos_spec (a b : Nat) (hb : 0 < b) : divmodPos a b = .ok (a / b, a % b) := by
  have hb1 : 1 ≤ b := hb
  obtain ⟨b1, b2⟩ := bitLength_bounds b hb1
  have hn : 1 ≤ bitLength b := (bitLength_facts b).2.1 hb1 |>.2
  obtain ⟨n, hnd⟩ : ∃ n, bitLength b = n := ⟨_, rfl⟩
  rw [hnd] at b1 b2 hn
  obtain ⟨l, e1, h1, h2, h3, _⟩ := int2digits_spec (a := a) hn
  obtain ⟨new, r', e2, h4, h5, h6⟩ := dmLoop_spec hn b1 b2 rfl l.reverse 0 []
    (fun d hd => h2 d (List.mem_reverse.1 hd)) hb
  have hval : be (2 ^ n) 0 l.reverse = a := by
    rw [be_reverse, ← h3]
    simp
  have hq : limbVal (2 ^ n) new.reverse = be (2 ^ n) 0 new := by
    have := be_reverse (2 ^ n) new.reverse 0
    simpa using this.symm
  have h7 : be (2 ^ n) 0 new * b + r' = a := by rw [h6, hval]
  have hu : r' + b * be (2 ^ n) 0 new = a := by
    rw [← h7, Nat.mul_comm b, Nat.add_comm]
  obtain ⟨u1, u2⟩ := (Nat.div_mod_unique hb).2 ⟨hu, h4⟩
  unfold divmodPos
  simp only [hnd, e1, bindOk, e2, List.nil_append, digits2int_spec, pureOk, hq, u1, u2]

end PyLean.LongObj

