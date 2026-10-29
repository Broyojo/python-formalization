import PyLean.MathInt.IntOps

/-!
Three-argument `pow` with a negative exponent: `long_invmod` and the
modulus handling of `long_pow`.
-/

namespace PyLean.MathInt

open PyLean

theorem mod_mul_mod_eq (x y c : Nat) : (x % c) * y % c = x * y % c := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem mul_mod_mod_eq (x y c : Nat) : x * (y % c) % c = x * y % c := by
  rw [Nat.mul_comm, mod_mul_mod_eq, Nat.mul_comm]

theorem modPowAux_mod (c : Nat) :
    ∀ fuel base e acc, e < fuel → modPowAux c fuel base e acc % c = acc * base ^ e % c := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; omega
  | succ f ih =>
    intro base e acc he
    unfold modPowAux
    by_cases h0 : e = 0
    · simp [h0]
    · simp only [h0, ite_false]
      rw [ih _ _ _ (by omega)]
      have hsplit : base ^ e = base ^ (e % 2) * (base * base) ^ (e / 2) := by
        rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_add]
        congr 1; omega
      rw [hsplit, ← mul_mod_mod_eq, ← Nat.pow_mod, mul_mod_mod_eq]
      split
      · rename_i h1
        rw [mod_mul_mod_eq, h1, Nat.pow_one, Nat.mul_assoc]
      · rename_i h1
        rw [show e % 2 = 0 by omega, Nat.pow_zero, Nat.one_mul]

theorem modPowAux_lt (c : Nat) (hc : 0 < c) :
    ∀ fuel base e acc, acc < c → modPowAux c fuel base e acc < c := by
  intro fuel
  induction fuel with
  | zero => intro _ _ acc h; simpa [modPowAux] using h
  | succ f ih =>
    intro base e acc h
    unfold modPowAux
    split
    · exact h
    · apply ih
      split
      · exact Nat.mod_lt _ hc
      · exact h

/-- `modPow a e c = a^e % c`. -/
theorem modPow_eq (a e c : Nat) (hc : 0 < c) : modPow a e c = a ^ e % c := by
  have h1 := modPowAux_mod c (e + 1) (a % c) e (1 % c) (by omega)
  have h2 := modPowAux_lt c hc (e + 1) (a % c) e (1 % c) (Nat.mod_lt _ hc)
  unfold modPow
  rw [Nat.mod_eq_of_lt h2] at h1
  rw [h1, mod_mul_mod_eq, Nat.one_mul, ← Nat.pow_mod]

/-- The extended-Euclid loop of `long_invmod` keeps `a ≡ b*a0`, `n ≡ c*a0`
(mod `M`) and `gcd(a, n) = gcd(a0, M)`, and ends with `a = gcd(a0, M)`. -/
theorem invmodLoop_spec (a0 M : Int) :
    ∀ fuel a b c n, 0 ≤ n → (n = 0 → 0 ≤ a) → n.toNat < fuel →
      M ∣ a - b * a0 → M ∣ n - c * a0 → Int.gcd a n = Int.gcd a0 M →
      ∃ g b', invmodLoop fuel a b c n = .ok (g, b') ∧ 0 ≤ g ∧
        g.natAbs = Int.gcd a0 M ∧ M ∣ g - b' * a0 := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ n _ _ h; omega
  | succ f ih =>
    intro a b c n hn ha hf h1 h2 hg
    unfold invmodLoop
    by_cases h0 : n = 0
    · subst h0
      simp only [ite_true]
      refine ⟨a, b, rfl, ha rfl, ?_, h1⟩
      rw [← hg, Int.gcd_zero_right]
    · simp only [h0, ite_false]
      have hn' : 0 < n := by omega
      have e := Int.fmod_add_fdiv_mul a n
      have r0 : 0 ≤ Int.fmod a n := by
        rw [Int.fmod_eq_emod_of_nonneg _ (by omega)]; exact Int.emod_nonneg _ (by omega)
      have r1 : Int.fmod a n < n := Int.fmod_lt_of_pos _ hn'
      unfold floorDiv floorMod
      apply ih
      · exact r0
      · intro _; omega
      · omega
      · exact h2
      · have : Int.fmod a n - (b - Int.fdiv a n * c) * a0 =
            (a - b * a0) - Int.fdiv a n * (n - c * a0) := by grind
        rw [this]
        exact Int.dvd_sub h1 (Int.dvd_mul_of_dvd_right h2)
      · rw [← hg, show Int.fmod a n = a - Int.fdiv a n * n by omega,
          Int.gcd_sub_mul_right_right, Int.gcd_comm]

theorem dvd_pow_sub_pow {c x y : Int} (h : c ∣ x - y) : ∀ k : Nat, c ∣ x ^ k - y ^ k
  | 0 => by simp
  | k + 1 => by
    have ih := dvd_pow_sub_pow h k
    have : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + y ^ k * (x - y) := by
      rw [Int.pow_succ, Int.pow_succ]; grind
    rw [this]
    exact Int.dvd_add (Int.dvd_mul_of_dvd_right ih) (Int.dvd_mul_of_dvd_right h)

/-- `invmod a c` for `c > 1`: an inverse when `gcd(a, c) == 1`, else `ValueError`. -/
theorem invmod_spec (a c : Int) (hc : 1 < c) :
    (Int.gcd a c = 1 → ∃ b, invmod a c = .ok b ∧ c ∣ 1 - b * a) ∧
    (Int.gcd a c ≠ 1 → (invmod a c).raises "ValueError") := by
  obtain ⟨g, b', hl, hg0, hg, hd⟩ :=
    invmodLoop_spec a c (c.toNat + 2) a 1 0 c (by omega) (by omega) (by omega)
      (by simp) (by simp) rfl
  unfold invmod
  rw [hl]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : g = 1 := by omega
    subst this
    exact ⟨b', rfl, hd⟩
  · have : g ≠ 1 := by intro e; subst e; simp at hg; omega
    refine ⟨.valueError "base is not invertible for the given modulus", ?_, rfl⟩
    simp only [bind, Except.bind, ne_eq, this, not_false_eq_true, ite_true]; rfl

/-- The steps of `long_pow` for a negative exponent and `abs(x) > 1`. -/
def powModNegSteps (v w x : Int) : Py Int := do
  let c : Int := x.natAbs
  let a ← invmod v c
  let a := if a < 0 ∨ digitCount a.natAbs > digitCount c.natAbs then floorMod a c else a
  let z : Int := modPow a.toNat (-w).toNat c.toNat
  if x < 0 ∧ z ≠ 0 then return z - c
  return z

theorem powMod_neg_eq (v w x : Int) (hw : w < 0) (hx : 1 < x.natAbs) :
    powMod v w x = powModNegSteps v w x := by
  have hx0 : x ≠ 0 := by omega
  have hx1 : ((x.natAbs : Int) = 1) = False := by simp; omega
  unfold powMod powModNegSteps
  simp [hx0, hx1, hw]
  congr 1; funext a
  split <;> simp_all

/-- Built-in `pow()` docs: "If mod is present and exp is negative, base must be
relatively prime to mod. In that case, pow(inv_base, -exp, mod) is returned,
where inv_base is an inverse to base modulo mod"; the result of a three-argument
`pow` lies in `range(mod)` (or `range(0, mod, -1)` shifted for negative mod) as
`%` does; `mod == 0` raises `ValueError`. For `abs(mod) == 1` every base is
invertible and the result is 0. -/
def PowNegExpInverse : Prop :=
  ∀ (a m : Int) (k : Nat), 0 < k →
    (m = 0 → (powMod a (-(k : Int)) m).raises "ValueError") ∧
    (m.natAbs = 1 → powMod a (-(k : Int)) m = .ok 0) ∧
    (1 < m.natAbs → Int.gcd a m = 1 → ∃ r, powMod a (-(k : Int)) m = .ok r ∧
      m ∣ r * a ^ k - 1 ∧ (0 < m → 0 ≤ r ∧ r < m) ∧ (m < 0 → m < r ∧ r ≤ 0)) ∧
    (1 < m.natAbs → Int.gcd a m ≠ 1 → (powMod a (-(k : Int)) m).raises "ValueError")

theorem powNegExpInverse_proven : PowNegExpInverse := by
  intro a m k hk
  have hneg : -(k : Int) < 0 := by omega
  refine ⟨fun h => ?_, fun h => ?_, fun h hg => ?_, fun h hg => ?_⟩
  · subst h; exact ⟨_, by simp [powMod]; rfl, rfl⟩
  · have hm : m ≠ 0 := by omega
    simp [powMod, hm, h]; rfl
  · have hm : m ≠ 0 := by omega
    have hc : (1 : Int) < (m.natAbs : Int) := by omega
    have hgc : Int.gcd a (m.natAbs : Int) = 1 := by simpa [Int.gcd] using hg
    obtain ⟨b, hb, hdb⟩ := (invmod_spec a m.natAbs hc).1 hgc
    rw [powMod_neg_eq a _ m hneg h]
    simp only [powModNegSteps, hb, bind, Except.bind, Int.neg_neg]
    have hk' : (k : Int).toNat = k := by omega
    rw [hk']
    generalize hC : (m.natAbs : Int) = C at *
    have hC0 : 0 < C := by omega
    -- the base after the optional reduction `a = a % c`
    have hred : ∀ (p : Prop) [Decidable p], (b < 0 → p) →
        0 ≤ (if p then floorMod b C else b) ∧ C ∣ (if p then floorMod b C else b) - b := by
      intro p _ hp
      split
      · refine ⟨?_, ?_⟩
        · unfold floorMod; rw [Int.fmod_eq_emod_of_nonneg _ (by omega)]
          exact Int.emod_nonneg _ (by omega)
        · unfold floorMod; rw [Int.fmod_eq_emod_of_nonneg _ (by omega)]
          have := @Int.dvd_self_sub_emod b C
          have e : b % C - b = -(b - b % C) := by omega
          rw [e]; exact Int.dvd_neg.mpr this
      · rename_i hnp
        refine ⟨Classical.byContradiction fun hn => hnp (hp (by omega)), by simp⟩
    obtain ⟨h0, hd2⟩ := hred (b < 0 ∨ digitCount b.natAbs > digitCount C.natAbs)
      (fun hb0 => Or.inl hb0)
    generalize (if b < 0 ∨ digitCount b.natAbs > digitCount C.natAbs then floorMod b C else b) = a2
      at h0 hd2 ⊢
    have hz : (modPow a2.toNat k C.toNat : Int) = a2 ^ k % C := by
      rw [modPow_eq _ _ _ (by omega), Int.natCast_emod, Int.natCast_pow, Int.toNat_of_nonneg h0,
        Int.toNat_of_nonneg (by omega)]
    rw [hz]
    have zl : 0 ≤ a2 ^ k % C := Int.emod_nonneg _ (by omega)
    have zu : a2 ^ k % C < C := Int.emod_lt_of_pos _ hC0
    -- `C ∣ z * a^k - 1`
    have key : C ∣ a2 ^ k % C * a ^ k - 1 := by
      have d1 : C ∣ a2 ^ k % C - a2 ^ k := by
        have := @Int.dvd_self_sub_emod (a2 ^ k) C
        have e : a2 ^ k % C - a2 ^ k = -(a2 ^ k - a2 ^ k % C) := by omega
        rw [e]; exact Int.dvd_neg.mpr this
      have d2 : C ∣ a2 ^ k - b ^ k := dvd_pow_sub_pow hd2 k
      have d3 : C ∣ (b * a) ^ k - 1 ^ k := by
        have : C ∣ b * a - 1 := by
          have e : b * a - 1 = -(1 - b * a) := by omega
          rw [e]; exact Int.dvd_neg.mpr hdb
        exact dvd_pow_sub_pow this k
      have e : a2 ^ k % C * a ^ k - 1 =
          (a2 ^ k % C - a2 ^ k) * a ^ k + (a2 ^ k - b ^ k) * a ^ k + ((b * a) ^ k - 1 ^ k) := by
        rw [Int.mul_pow, Int.one_pow]; grind
      rw [e]
      exact Int.dvd_add (Int.dvd_add (Int.dvd_mul_of_dvd_left d1) (Int.dvd_mul_of_dvd_left d2)) d3
    have hmC : m ∣ C := by rw [← hC]; exact Int.dvd_natAbs.mpr (Int.dvd_refl m)
    have hCm : C ∣ m := by rw [← hC]; exact Int.natAbs_dvd.mpr (Int.dvd_refl m)
    by_cases hm0 : m < 0
    · have hCe : C = -m := by omega
      by_cases hz0 : a2 ^ k % C = 0
      · rw [hz0] at key; simp at key
        have : C ∣ (1 : Int) := by have := Int.dvd_neg.mpr key; simpa using this
        have := Int.le_of_dvd (by decide) this; omega
      · simp only [hm0, ne_eq, hz0, not_false_eq_true, and_self, ite_true]
        refine ⟨_, rfl, ?_, fun h => by omega, fun _ => by omega⟩
        have e : (a2 ^ k % C - C) * a ^ k - 1 = (a2 ^ k % C * a ^ k - 1) - C * a ^ k := by grind
        rw [e]
        exact Int.dvd_sub (Int.dvd_trans hmC key) (Int.dvd_mul_of_dvd_left hmC)
    · simp only [hm0, false_and, ite_false]
      have hCe : C = m := by omega
      refine ⟨_, rfl, Int.dvd_trans hmC key, fun _ => ⟨zl, by omega⟩, fun h => (by first | exact h.elim | omega)⟩
  · have hm : m ≠ 0 := by omega
    have hc : (1 : Int) < (m.natAbs : Int) := by omega
    have hgc : Int.gcd a (m.natAbs : Int) ≠ 1 := by simpa [Int.gcd] using hg
    obtain ⟨e, he, hcls⟩ := (invmod_spec a m.natAbs hc).2 hgc
    rw [powMod_neg_eq a _ m hneg h]
    simp only [powModNegSteps, he]
    exact ⟨e, rfl, hcls⟩
end PyLean.MathInt
