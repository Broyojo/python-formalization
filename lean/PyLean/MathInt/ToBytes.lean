import PyLean.MathInt.ToBytesLoop
import PyLean.MathInt.Isqrt
import PyLean.MathInt.Factorial

/-!
`int.to_bytes` (`_PyLong_AsByteArray`, longobject.c:1031-1170) writes `v mod
256**n` and raises `OverflowError` exactly when `v` does not fit in `n` bytes.
-/

namespace PyLean.MathInt

open PyLean

/-! ### Digits of a Python int -/

theorem digitsOf_go (k : Nat) : ∀ n, (digitsOf.go k n).length = k ∧
    (∀ d ∈ digitsOf.go k n, d < 2 ^ 30) ∧ digitsValue (digitsOf.go k n) = n % 2 ^ (30 * k) := by
  induction k with
  | zero => intro n; simp [digitsOf.go, digitsValue, Nat.mod_one]
  | succ k ih =>
    intro n
    obtain ⟨h1, h2, h3⟩ := ih (n / 2 ^ 30)
    refine ⟨by simp [digitsOf.go, h1], ?_, ?_⟩
    · intro d hd
      simp only [digitsOf.go, List.mem_cons] at hd
      rcases hd with h | h
      · subst h; exact Nat.mod_lt _ (by decide)
      · exact h2 d h
    · simp only [digitsOf.go, digitsValue, h3]
      rw [show 30 * (k + 1) = 30 + 30 * k by omega, Nat.pow_add, Nat.mod_mul, Nat.add_comm]

theorem digitCount_spec (V : Nat) : V < 2 ^ (30 * digitCount V) ∧
    (1 ≤ V → 1 ≤ digitCount V ∧ 2 ^ (30 * (digitCount V - 1)) ≤ V) := by
  unfold digitCount
  constructor
  · exact Nat.lt_of_lt_of_le (lt_two_pow_bitLength' V)
      (Nat.pow_le_pow_right (by decide) (by omega))
  · intro hV
    obtain ⟨b1, _⟩ := bitLength_bounds V hV
    have : 1 ≤ bitLength V := by unfold bitLength; simp [show V ≠ 0 by omega]
    exact ⟨by omega, Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) b1⟩

theorem digitsOf_spec (V : Nat) : (digitsOf V).length = digitCount V ∧
    (∀ d ∈ digitsOf V, d < 2 ^ 30) ∧ digitsValue (digitsOf V) = V := by
  obtain ⟨h1, h2, h3⟩ := digitsOf_go (digitCount V) V
  exact ⟨h1, h2, by unfold digitsOf; rw [h3, Nat.mod_eq_of_lt (digitCount_spec V).1]⟩

/-! ### Effective digits -/

theorem effVal_unsigned : ∀ ds c, effVal false ds c = digitsValue ds
  | [], _ => rfl
  | d :: ds, c => by simp [effVal, effStep, digitsValue, effVal_unsigned ds c]

theorem effVal_lt (twos : Bool) : ∀ ds c, (∀ d ∈ ds, d < 2 ^ 30) → c ≤ 1 →
    effVal twos ds c < 2 ^ (30 * ds.length)
  | [], _, _, _ => by simp [effVal]
  | d :: ds, c, h, hc => by
    have hd := h d (by simp)
    obtain ⟨he, hc'⟩ := effStep_lt twos d c hd hc
    have ih := effVal_lt twos ds (effStep twos d c).2 (fun x hx => h x (by simp [hx])) hc'
    simp only [effVal, List.length_cons]
    rw [show 30 * (ds.length + 1) = 30 + 30 * ds.length by omega, Nat.pow_add]
    have : 2 ^ 30 * effVal twos ds (effStep twos d c).2 + 2 ^ 30 ≤ 2 ^ 30 * 2 ^ (30 * ds.length) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    omega

theorem effStep_true (d c : Nat) (hd : d < 2 ^ 30) :
    (effStep true d c).1 + 2 ^ 30 * (effStep true d c).2 = (2 ^ 30 - 1 - d) + c := by
  unfold effStep digitMask
  simp only [ite_true]
  rw [and_mask_eq_mod, Nat.shiftRight_eq_div_pow, Nat.xor_comm, xor_mask 30 d hd]
  have := Nat.mod_add_div (2 ^ 30 - 1 - d + c) (2 ^ 30); omega

theorem effVal_twos : ∀ ds c, (∀ d ∈ ds, d < 2 ^ 30) → c ≤ 1 →
    effVal true ds c + 2 ^ (30 * ds.length) * effCarry true ds c + digitsValue ds =
      2 ^ (30 * ds.length) - 1 + c
  | [], c, _, _ => by simp [effVal, effCarry, digitsValue]
  | d :: ds, c, h, hc => by
    have hd := h d (by simp)
    obtain ⟨_, hc'⟩ := effStep_lt true d c hd hc
    have ih := effVal_twos ds (effStep true d c).2 (fun x hx => h x (by simp [hx])) hc'
    have hs := effStep_true d c hd
    simp only [effVal, effCarry, digitsValue, List.length_cons]
    rw [show 30 * (ds.length + 1) = 30 + 30 * ds.length by omega, Nat.pow_add]
    generalize (effStep true d c).1 = e at *
    generalize (effStep true d c).2 = c' at *
    generalize effVal true ds c' = W at *
    generalize effCarry true ds c' = cf at *
    generalize digitsValue ds = D at *
    have hP := Nat.one_le_two_pow (n := 30 * ds.length)
    generalize 2 ^ (30 * ds.length) = P at *
    have : 2 ^ 30 * W + 2 ^ 30 * P * cf + 2 ^ 30 * D = 2 ^ 30 * (P - 1 + c') := by
      rw [← ih]; simp only [Nat.mul_add, Nat.mul_assoc]
    have : 2 ^ 30 * (P - 1 + c') = 2 ^ 30 * P - 2 ^ 30 + 2 ^ 30 * c' := by
      rw [Nat.mul_add, Nat.mul_sub, Nat.mul_one]
    have : 2 ^ 30 ≤ 2 ^ 30 * P := Nat.le_mul_of_pos_right _ hP
    omega

theorem bitLength_add_shift (x C s : Nat) (hx : x < 2 ^ s) (hC : 1 ≤ C) :
    bitLength (x + 2 ^ s * C) = s + bitLength C := by
  obtain ⟨c1, c2⟩ := bitLength_bounds C hC
  have hpos : 1 ≤ x + 2 ^ s * C := by have := Nat.mul_le_mul_left (2 ^ s) hC; have := Nat.one_le_two_pow (n := s); omega
  apply Nat.le_antisymm
  · apply bitLength_le_of_lt'
    rw [Nat.pow_add]
    have : 2 ^ s * C + 2 ^ s ≤ 2 ^ s * 2 ^ bitLength C := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ c2
    omega
  · have := (two_pow_le_iff_lt_bitLength (x + 2 ^ s * C) (s + (bitLength C - 1)) hpos).mp (by
      rw [Nat.pow_add]; have := Nat.mul_le_mul_left (2 ^ s) c1; omega)
    have : 1 ≤ bitLength C := by unfold bitLength; simp [show C ≠ 0 by omega]
    omega


/-- Complement value of the effective digits. -/
theorem effBits_twos : ∀ ds c, ds ≠ [] → (∀ d ∈ ds, d < 2 ^ 30) → c ≤ 1 →
    effBits true ds c = max (30 * (ds.length - 1))
      (bitLength (2 ^ (30 * ds.length) - 1 - effVal true ds c))
  | [], _, h, _, _ => absurd rfl h
  | [d], c, _, h, hc => by
    have hd := h d (by simp)
    obtain ⟨he, _⟩ := effStep_lt true d c hd hc
    simp only [effBits, ite_true, effVal, List.length_singleton, Nat.mul_zero, Nat.add_zero,
      Nat.sub_self, Nat.mul_one]
    unfold digitMask
    rw [Nat.xor_comm, xor_mask 30 _ he]
    omega
  | d :: d2 :: ds, c, _, h, hc => by
    have hd := h d (by simp)
    obtain ⟨he, hc'⟩ := effStep_lt true d c hd hc
    have hrest : ∀ x ∈ d2 :: ds, x < 2 ^ 30 := fun x hx => h x (by simp [hx])
    have ih := effBits_twos (d2 :: ds) (effStep true d c).2 (by simp) hrest hc'
    have hlt := effVal_lt true (d2 :: ds) (effStep true d c).2 hrest hc'
    simp only [effBits]
    rw [show effVal true (d :: d2 :: ds) c =
      (effStep true d c).1 + 2 ^ 30 * effVal true (d2 :: ds) (effStep true d c).2 from rfl]
    rw [ih]
    generalize (effStep true d c).1 = e at *
    generalize effVal true (d2 :: ds) (effStep true d c).2 = W at *
    simp only [List.length_cons] at *
    rw [show ds.length + 1 + 1 - 1 = ds.length + 1 by omega,
      show ds.length + 1 - 1 = ds.length by omega] at *
    generalize hm : ds.length + 1 = m at *
    have hm1 : 1 ≤ m := by omega
    rw [show ds.length = m - 1 by omega]
    -- complement value: (MASK - e) + 2^30 * (2^(30m) - 1 - W)
    have hcv : 2 ^ (30 * (m + 1)) - 1 - (e + 2 ^ 30 * W) =
        (2 ^ 30 - 1 - e) + 2 ^ 30 * (2 ^ (30 * m) - 1 - W) := by
      rw [show 30 * (m + 1) = 30 + 30 * m by omega, Nat.pow_add, Nat.mul_sub, Nat.mul_sub,
        Nat.mul_one]
      have : 2 ^ 30 * W + 2 ^ 30 ≤ 2 ^ 30 * 2 ^ (30 * m) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega
    rw [hcv]
    generalize 2 ^ (30 * m) - 1 - W = C
    by_cases hC : C = 0
    · subst hC
      simp only [Nat.mul_zero, Nat.add_zero]
      have : bitLength (2 ^ 30 - 1 - e) ≤ 30 :=
        bitLength_le_of_lt' (by omega)
      have : bitLength 0 = 0 := rfl
      omega
    · have hb := bitLength_add_shift (2 ^ 30 - 1 - e) C 30 (by omega) (by omega)
      rw [hb]
      omega

theorem effBits_unsigned : ∀ ds c, ds ≠ [] → (∀ d ∈ ds, d < 2 ^ 30) →
    2 ^ (30 * (ds.length - 1)) ≤ digitsValue ds → effBits false ds c = bitLength (digitsValue ds)
  | [], _, h, _, _ => absurd rfl h
  | [d], c, _, _, _ => by simp [effBits, effStep, digitsValue]
  | d :: d2 :: ds, c, _, h, htop => by
    have hd := h d (by simp)
    have hrest : ∀ x ∈ d2 :: ds, x < 2 ^ 30 := fun x hx => h x (by simp [hx])
    simp only [effBits, effStep, Bool.false_eq_true, ite_false, digitsValue] at htop ⊢
    simp only [List.length_cons] at htop
    have hW : 2 ^ (30 * ds.length) ≤ digitsValue (d2 :: ds) := by
      simp only [digitsValue]
      refine Classical.byContradiction fun hc => ?_
      rw [show ds.length + 1 + 1 - 1 = 1 + ds.length by omega, show 30 * (1 + ds.length) = 30 + 30 * ds.length by omega,
        Nat.pow_add] at htop
      have : 2 ^ 30 * (d2 + 2 ^ 30 * digitsValue ds) + 2 ^ 30 ≤ 2 ^ 30 * 2 ^ (30 * ds.length) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    have ih := effBits_unsigned (d2 :: ds) c (by simp) hrest (by simpa using hW)
    simp only [digitsValue] at ih hW
    rw [ih, bitLength_add_shift d _ 30 hd (by
      have := Nat.one_le_two_pow (n := 30 * ds.length); omega)]

/-! ### The whole of `_PyLong_AsByteArray` -/

/-- `v` is representable in `n` bytes: `0 <= v < 256**n` unsigned, or
`-256**n/2 <= v < 256**n/2` signed. -/
def FitsBytes (v : Int) (n : Nat) (signed : Bool) : Prop :=
  if signed then -(2 ^ (8 * n) : Int) ≤ 2 * v ∧ 2 * v < 2 ^ (8 * n) else 0 ≤ v ∧ v < 2 ^ (8 * n)

/-- Either the right bytes and `v` fits, or `OverflowError` and it does not. -/
def BytesOutcome (v : Int) (n : Nat) (signed : Bool) (r : Py (List Nat)) : Prop :=
  ((∃ bs, r = .ok bs ∧ bs.length = n ∧ AllBytes bs ∧ (bytesVal bs : Int) = v % 2 ^ (8 * n)) ∧
    FitsBytes v n signed) ∨ (r.raises "OverflowError" ∧ ¬ FitsBytes v n signed)

theorem getLastD_lowBytes (x k d : Nat) : (lowBytes x (k + 1)).getLastD d = (x / 256 ^ k) % 256 := by
  induction k generalizing x d with
  | zero => simp [lowBytes]
  | succ k ih =>
    rw [show lowBytes x (k + 1 + 1) = x % 256 :: lowBytes (x / 256) (k + 1) from rfl,
      List.getLastD_cons, ih, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256]

theorem allBytes_append {xs ys : List Nat} (h1 : AllBytes xs) (h2 : AllBytes ys) :
    AllBytes (xs ++ ys) := by
  intro b hb; rcases List.mem_append.mp hb with h | h; exact h1 b h; exact h2 b h

theorem allBytes_replicate (k b : Nat) (hb : b < 256) : AllBytes (List.replicate k b) := by
  intro x hx; rw [List.eq_of_mem_replicate hx]; exact hb

theorem pow256 (k : Nat) : (256 : Nat) ^ k = 2 ^ (8 * k) := by
  rw [Nat.pow_mul]

theorem straggler (x ab : Nat) (hab : ab < 8) :
    (x ||| (255 <<< ab)) % 256 = x % 2 ^ ab + (256 - 2 ^ ab) := by
  have h1 : (x ||| (255 <<< ab)) % 256 = ((x % 256) ||| ((255 <<< ab) % 256)) % 256 := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.or_mod_two_pow]
    exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)))).symm
  have h2 : x % 2 ^ ab = (x % 256) % 2 ^ ab := by
    rw [Nat.mod_mod_of_dvd]; exact Nat.pow_dvd_pow 2 (show ab ≤ 8 by omega) |> fun h => by
      simpa using h
  rw [h1, h2]
  have hx := Nat.mod_lt x (show 0 < 256 by decide)
  generalize x % 256 = y at hx ⊢
  have key : (List.range 256).all (fun y => (List.range 8).all fun ab =>
      ((y ||| ((255 <<< ab) % 256)) % 256 == y % 2 ^ ab + (256 - 2 ^ ab))) = true := by
    decide +kernel
  have := (List.all_eq_true.mp ((List.all_eq_true.mp key) y (List.mem_range.mpr hx))) ab
    (List.mem_range.mpr hab)
  simpa using this

theorem bitLength_facts (V : Nat) :
    V < 2 ^ bitLength V ∧ (1 ≤ V → 2 ^ (bitLength V - 1) ≤ V ∧ 1 ≤ bitLength V) ∧
      (V = 0 → bitLength V = 0) := by
  refine ⟨lt_two_pow_bitLength' V, fun h => ⟨(bitLength_bounds V h).1, ?_⟩, fun h => by subst h; rfl⟩
  unfold bitLength; simp [show V ≠ 0 by omega]

theorem effBits_digitsOf_unsigned (V : Nat) : effBits false (digitsOf V) 0 = bitLength V := by
  obtain ⟨hlen, hdig, hval⟩ := digitsOf_spec V
  by_cases hV : V = 0
  · subst hV
    have : digitsOf 0 = [] := by rw [← List.length_eq_zero_iff, hlen]; rfl
    rw [this]; rfl
  · obtain ⟨hk, htop⟩ := (digitCount_spec V).2 (by omega)
    have hne : digitsOf V ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
    rw [effBits_unsigned _ 0 hne hdig (by rw [hlen, hval]; exact htop), hval]

/-- `_PyLong_AsByteArray` for `v >= 0`. -/
theorem asByteArray_nonneg (V n : Nat) (signed : Bool) :
    BytesOutcome V n signed (asByteArray V n signed) := by
  obtain ⟨_, hdig, hval⟩ := digitsOf_spec V
  have loop := asByteArrayLoop_spec n false (digitsOf V) ⟨[], 0, 0, 0⟩ hdig (by decide)
    (by decide) (by decide) (by simp)
  simp only [List.length_nil, Nat.zero_add, Nat.pow_zero, Nat.one_mul, List.nil_append] at loop
  rw [effVal_unsigned, hval, effBits_digitsOf_unsigned] at loop
  obtain ⟨hVL, hVL2, hV0⟩ := bitLength_facts V
  generalize bitLength V = L at *
  unfold asByteArray
  have hd : decide ((V : Int) < 0) = false := by simp
  simp only [show ¬ ((V : Int) < 0 ∧ ¬signed = true) by omega, ite_false, hd, Int.natAbs_natCast,
    Bool.false_eq_true, ite_false]
  rw [loop]
  have hq : L = 8 * (L / 8) + L % 8 := by omega
  have h256 := pow256 (L / 8)
  unfold BytesOutcome FitsBytes
  by_cases hov : L / 8 > n
  · simp only [hov, ite_true]
    right
    refine ⟨⟨_, rfl, rfl⟩, ?_⟩
    have hV1 : 1 ≤ V := Classical.byContradiction fun h => by have := hV0 (by omega); omega
    have := (hVL2 hV1).1
    have : 2 ^ (8 * n + 7) ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have e : (2 : Int) ^ (8 * n + 7) = 2 ^ (8 * n) * 2 ^ 7 := by rw [Int.pow_add]
    have : ((2 ^ (8 * n + 7) : Nat) : Int) ≤ (V : Int) := by exact_mod_cast (by omega)
    push_cast at this
    cases signed <;> simp <;> omega
  · simp only [hov, ite_false]
    have hqn : L / 8 ≤ n := by omega
    generalize hq8 : L / 8 = q at *
    generalize hr8 : L % 8 = r at *
    have hr7 : r < 8 := by omega
    -- facts about V
    have hVq1 : V < 256 ^ (q + 1) := by
      rw [pow256]; exact Nat.lt_of_lt_of_le hVL (Nat.pow_le_pow_right (by decide) (by omega))
    have hmodq1 : V % 256 ^ q + 256 ^ q * (V / 256 ^ q % 256) = V := by
      rw [← Nat.mod_mul, ← Nat.pow_succ, Nat.mod_eq_of_lt hVq1]
    have hemod : ∀ m : Nat, V < 2 ^ m → ((V : Int) % 2 ^ m) = V := fun m hm =>
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast hm)
    by_cases hr0 : r > 0
    · simp only [hr0, ite_true, lowBytes_length]
      by_cases hfull : q ≥ n
      · simp only [hfull, ite_true]
        right; refine ⟨⟨_, rfl, rfl⟩, ?_⟩
        have hV1 : 1 ≤ V := Classical.byContradiction fun h => by have := hV0 (by omega); omega
        have := (hVL2 hV1).1
        have : 2 ^ (8 * n) ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide) (by omega)
        have : ((2 ^ (8 * n) : Nat) : Int) ≤ (V : Int) := by exact_mod_cast (by omega)
        push_cast at this
        cases signed <;> simp <;> omega
      · simp only [hfull, ite_false]
        left
        have hfit : V < 2 ^ (8 * n) ∧ 2 * V < 2 ^ (8 * n) := by
          have : 2 ^ (L + 1) ≤ 2 ^ (8 * n) := Nat.pow_le_pow_right (by decide) (by omega)
          rw [Nat.pow_succ] at this; omega
        refine ⟨⟨_, rfl, ?_, ?_, ?_⟩, ?_⟩
        · simp [lowBytes_length]; omega
        · exact allBytes_append (allBytes_append (lowBytes_all _ _)
            (fun b hb => by simp at hb; rw [hb]; exact Nat.mod_lt _ (by decide)))
            (allBytes_replicate _ _ (by decide))
        · rw [bytesVal_append, bytesVal_append, bytesVal_replicate_zero, bytesVal_lowBytes]
          simp only [bytesVal, lowBytes_length, Nat.mul_zero, Nat.add_zero]
          rw [hmodq1, hemod _ hfit.1]
        · have : ((V : Nat) : Int) < 2 ^ (8 * n) := by exact_mod_cast hfit.1
          have : 2 * ((V : Nat) : Int) < 2 ^ (8 * n) := by exact_mod_cast hfit.2
          cases signed <;> simp <;> omega
    · have hr00 : r = 0 := by omega
      subst hr00
      simp only [Nat.lt_irrefl, ite_false, lowBytes_length]
      have hVq : V < 256 ^ q := by rw [pow256]; rw [show 8 * q = L by omega]; exact hVL
      by_cases hs : q = n ∧ signed = true
      · obtain ⟨rfl, rfl⟩ := hs
        simp only [and_self, ite_true]
        by_cases hV : V = 0
        · subst hV
          have hq0 : q = 0 := by have := hV0 rfl; omega
          subst hq0
          simp only [Nat.lt_irrefl, false_and, decide_false, ite_true]
          left
          refine ⟨⟨_, rfl, rfl, lowBytes_all _ _, by simp [lowBytes, bytesVal]⟩, by simp⟩
        · have hV1 : 1 ≤ V := by omega
          obtain ⟨h1, h2⟩ := hVL2 hV1
          have hq1 : 1 ≤ q := by omega
          obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
          have hlast : (lowBytes V (k + 1)).getLastD 0 ≥ 128 := by
            rw [getLastD_lowBytes]
            have hk : 2 ^ (L - 1) = 256 ^ k * 128 := by
              rw [pow256, show L - 1 = 8 * k + 7 by omega, Nat.pow_add]
            have : 128 ≤ V / 256 ^ k := (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).mpr
              (by rw [Nat.mul_comm]; omega)
            have : V / 256 ^ k < 256 := (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr
              (by have := Nat.pow_succ 256 k; omega)
            have := Nat.mod_eq_of_lt this; omega
          simp only [show k + 1 > 0 by omega, hlast, and_self, decide_true, Bool.true_eq_false,
            ite_false]
          right; refine ⟨⟨_, rfl, rfl⟩, ?_⟩
          have : 2 ^ (8 * (k + 1)) ≤ 2 * V := by
            rw [show 8 * (k + 1) = (L - 1) + 1 by omega, Nat.pow_succ]; omega
          have : ((2 ^ (8 * (k + 1)) : Nat) : Int) ≤ 2 * (V : Int) := by exact_mod_cast this
          push_cast at this
          simp; omega
      · simp only [hs, ite_false]
        left
        have hfit : V < 2 ^ (8 * n) ∧ (signed = true → 2 * V < 2 ^ (8 * n)) := by
          rw [pow256] at hVq
          constructor
          · exact Nat.lt_of_lt_of_le hVq (Nat.pow_le_pow_right (by decide) (by omega))
          · intro hsg
            have : q < n := Classical.byContradiction fun h => hs ⟨by omega, hsg⟩
            have : 2 ^ (8 * q + 1) ≤ 2 ^ (8 * n) := Nat.pow_le_pow_right (by decide) (by omega)
            rw [Nat.pow_succ] at this; omega
        refine ⟨⟨_, rfl, ?_, ?_, ?_⟩, ?_⟩
        · simp [lowBytes_length]; omega
        · exact allBytes_append (lowBytes_all _ _) (allBytes_replicate _ _ (by decide))
        · rw [bytesVal_append, bytesVal_replicate_zero, bytesVal_lowBytes, Nat.mul_zero, Nat.add_zero,
            Nat.mod_eq_of_lt hVq, hemod _ hfit.1]
        · have : ((V : Nat) : Int) < 2 ^ (8 * n) := by exact_mod_cast hfit.1
          cases signed with
          | false => simp; omega
          | true =>
            have : 2 * ((V : Nat) : Int) < 2 ^ (8 * n) := by exact_mod_cast hfit.2 rfl
            simp; omega

theorem twos_facts (V : Nat) (hV : 1 ≤ V) :
    effVal true (digitsOf V) 1 + V = 2 ^ (30 * digitCount V) ∧
    effBits true (digitsOf V) 1 = bitLength (V - 1) ∧ bitLength (V - 1) ≤ 30 * digitCount V := by
  obtain ⟨hlen, hdig, hval⟩ := digitsOf_spec V
  obtain ⟨hlt, hK⟩ := digitCount_spec V
  obtain ⟨hK1, htop⟩ := hK hV
  have h1 := effVal_twos (digitsOf V) 1 hdig (by decide)
  have h2 := effVal_lt true (digitsOf V) 1 hdig (by decide)
  rw [hlen, hval] at h1; rw [hlen] at h2
  have hE : effVal true (digitsOf V) 1 + V = 2 ^ (30 * digitCount V) := by
    rcases Nat.eq_zero_or_pos (effCarry true (digitsOf V) 1) with hc | hc
    · rw [hc] at h1; omega
    · have := Nat.mul_le_mul_left (2 ^ (30 * digitCount V)) hc; omega
  refine ⟨hE, ?_, ?_⟩
  · have hne : digitsOf V ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
    rw [effBits_twos _ 1 hne hdig (by decide), hlen,
      show 2 ^ (30 * digitCount V) - 1 - effVal true (digitsOf V) 1 = V - 1 by omega]
    have : 30 * (digitCount V - 1) ≤ bitLength (V - 1) := by
      by_cases hk : digitCount V - 1 = 0
      · rw [hk]; omega
      · have := (two_pow_le_iff_lt_bitLength (V - 1) (30 * (digitCount V - 1) - 1) (by
          have := Nat.one_le_two_pow (n := 30 * (digitCount V - 1)); have : 2 ≤ 2 ^ (30 * (digitCount V - 1)) := by
            calc 2 = 2 ^ 1 := rfl
              _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
          omega)).mp (by
          have : 2 ^ (30 * (digitCount V - 1) - 1) * 2 = 2 ^ (30 * (digitCount V - 1)) := by
            rw [← Nat.pow_succ]; congr 1; omega
          omega)
        omega
    omega
  · exact bitLength_le_of_lt' (by omega)

/-- `_PyLong_AsByteArray` for `v < 0` with `is_signed`. -/
theorem asByteArray_neg (V n : Nat) (hV : 1 ≤ V) :
    BytesOutcome (-(V : Int)) n true (asByteArray (-(V : Int)) n true) := by
  obtain ⟨_, hdig, _⟩ := digitsOf_spec V
  obtain ⟨hE, hLb, hL30⟩ := twos_facts V hV
  have loop := asByteArrayLoop_spec n true (digitsOf V) ⟨[], 0, 0, 1⟩ hdig (by decide)
    (by decide) (by decide) (by simp)
  simp only [List.length_nil, Nat.zero_add, Nat.pow_zero, Nat.one_mul, List.nil_append] at loop
  rw [hLb] at loop
  generalize effVal true (digitsOf V) 1 = E at *
  generalize hK : 30 * digitCount V = K at *
  generalize hLdef : bitLength (V - 1) = L at *
  obtain ⟨hVL, hVL2, hV0⟩ := bitLength_facts (V - 1)
  rw [hLdef] at hVL hVL2 hV0
  -- E mod 2^L = 2^L - V
  have hEmod : E % 2 ^ L = 2 ^ L - V := by
    have hsplit : 2 ^ K = 2 ^ L * 2 ^ (K - L) := by rw [← Nat.pow_add]; congr 1; omega
    have h1 : 1 ≤ 2 ^ (K - L) := Nat.one_le_two_pow
    have : E = (2 ^ L - V) + 2 ^ L * (2 ^ (K - L) - 1) := by
      rw [Nat.mul_sub, Nat.mul_one, ← hsplit]
      have : 2 ^ L ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  unfold asByteArray
  have hd : decide (-(V : Int) < 0) = true := by simp; omega
  simp only [not_true_eq_false, and_false, ite_false, hd, Int.natAbs_neg,
    Int.natAbs_natCast, ite_true]
  rw [loop]
  have hq : L = 8 * (L / 8) + L % 8 := by omega
  -- the target value
  have htarget : ∀ m : Nat, 2 * V ≤ 2 ^ m → (-(V : Int)) % 2 ^ m = ((2 ^ m - V : Nat) : Int) := by
    intro m hm
    have hVm : V ≤ 2 ^ m := by omega
    have hc : ((V : Nat) : Int) ≤ ((2 ^ m : Nat) : Int) := by exact_mod_cast hVm
    push_cast at hc
    have e : -(V : Int) = ((2 : Int) ^ m - V) + (-1) * (2 : Int) ^ m := by omega
    rw [e, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega),
      Int.ofNat_sub hVm]
    push_cast; rfl
  unfold BytesOutcome FitsBytes
  simp only [ite_true]
  by_cases hov : L / 8 > n
  · simp only [hov, ite_true]
    right; refine ⟨⟨_, rfl, rfl⟩, ?_⟩
    have hV1 : 1 ≤ V - 1 := Classical.byContradiction fun h => by have := hV0 (by omega); omega
    have := (hVL2 hV1).1
    have : 2 ^ (8 * n) ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have : ((2 ^ (8 * n) : Nat) : Int) < 2 * (V : Int) := by exact_mod_cast (by omega)
    push_cast at this; omega
  · simp only [hov, ite_false]
    have hqn : L / 8 ≤ n := by omega
    generalize hq8 : L / 8 = q at *
    generalize hr8 : L % 8 = r at *
    have hr7 : r < 8 := by omega
    have h2L : 256 ^ q * 2 ^ r = 2 ^ L := by rw [pow256, ← Nat.pow_add]; congr 1; omega
    have hlow : E % 256 ^ q + 256 ^ q * ((E / 256 ^ q) % 2 ^ r) = 2 ^ L - V := by
      rw [← Nat.mod_mul, h2L, hEmod]
    have hVle : V ≤ 2 ^ L := by omega
    have hq1 : 256 ^ (q + 1) = 256 ^ q * 256 := Nat.pow_succ 256 q
    have hpr : 2 ^ r ≤ 256 := by
      calc 2 ^ r ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 256 := rfl
    have hneg : ∀ m, (0 : Int) ≤ ((2 ^ m - V : Nat) : Int) := fun m => by omega
    by_cases hr0 : r > 0
    · simp only [hr0, ite_true, lowBytes_length]
      by_cases hfull : q ≥ n
      · simp only [hfull, ite_true]
        right; refine ⟨⟨_, rfl, rfl⟩, ?_⟩
        have hV1 : 1 ≤ V - 1 := Classical.byContradiction fun h => by have := hV0 (by omega); omega
        have := (hVL2 hV1).1
        have : 2 ^ (8 * n) ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide) (by omega)
        have : ((2 ^ (8 * n) : Nat) : Int) < 2 * (V : Int) := by exact_mod_cast (by omega)
        push_cast at this; omega
      · simp only [hfull, ite_false]
        left
        have hfit : 2 * V ≤ 2 ^ (8 * n) := by
          have : 2 ^ (L + 1) ≤ 2 ^ (8 * n) := Nat.pow_le_pow_right (by decide) (by omega)
          rw [Nat.pow_succ] at this; omega
        have hLq : 2 ^ L ≤ 256 ^ (q + 1) := by
          rw [pow256]; exact Nat.pow_le_pow_right (by decide) (by omega)
        have hqn2 : 256 ^ (q + 1) ≤ 2 ^ (8 * n) := by
          rw [pow256]; exact Nat.pow_le_pow_right (by decide) (by omega)
        refine ⟨⟨_, rfl, ?_, ?_, ?_⟩, ?_⟩
        · simp [lowBytes_length]; omega
        · exact allBytes_append (allBytes_append (lowBytes_all _ _)
            (fun b hb => by simp at hb; rw [hb]; exact Nat.mod_lt _ (by decide)))
            (allBytes_replicate _ _ (by decide))
        · rw [htarget _ hfit, bytesVal_append, bytesVal_append, bytesVal_lowBytes]
          simp only [bytesVal, lowBytes_length, Nat.mul_zero, Nat.add_zero, List.length_append,
            List.length_singleton]
          rw [straggler _ r hr7]
          have hrep := bytesVal_replicate_255 (n - (q + 1))
          have e1 : 256 ^ q * ((E / 256 ^ q) % 2 ^ r + (256 - 2 ^ r)) =
              256 ^ q * ((E / 256 ^ q) % 2 ^ r) + (256 ^ (q + 1) - 2 ^ L) := by
            rw [Nat.mul_add, Nat.mul_sub, ← h2L, hq1]
          have e2 : 256 ^ (q + 1) * bytesVal (List.replicate (n - (q + 1)) 255) =
              2 ^ (8 * n) - 256 ^ (q + 1) := by
            rw [show bytesVal (List.replicate (n - (q + 1)) 255) = 256 ^ (n - (q + 1)) - 1 by omega,
              Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, show q + 1 + (n - (q + 1)) = n by omega,
              pow256]
          rw [e1, e2]
          have : ((E % 256 ^ q + (256 ^ q * (E / 256 ^ q % 2 ^ r) + (256 ^ (q + 1) - 2 ^ L)) +
              (2 ^ (8 * n) - 256 ^ (q + 1)) : Nat) : Int) = ((2 ^ (8 * n) - V : Nat) : Int) := by
            congr 1; omega
          exact this
        · have : 2 * (V : Int) ≤ 2 ^ (8 * n) := by exact_mod_cast hfit
          omega
    · have hr00 : r = 0 := by omega
      subst hr00
      simp only [Nat.lt_irrefl, ite_false, lowBytes_length, and_true]
      have hLq : 2 ^ L = 256 ^ q := by rw [pow256]; congr 1 <;> omega
      have hEq : E % 256 ^ q = 2 ^ L - V := by rw [← hLq, hEmod]
      by_cases hqn' : q = n
      · subst hqn'
        simp only [ite_true]
        by_cases hq0 : q = 0
        · subst hq0
          simp only [Nat.lt_irrefl, false_and, decide_false, Bool.false_eq_true, ite_false]
          right; refine ⟨⟨_, rfl, rfl⟩, ?_⟩
          have : L = 0 := by omega
          subst this
          have : V = 1 := by simp at hVL; omega
          subst this; simp
        · obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
          have hlast : (lowBytes E (k + 1)).getLastD 0 = (2 ^ L - V) / 256 ^ k := by
            rw [getLastD_lowBytes, ← Nat.mod_mul_right_div_self, ← Nat.pow_succ, hEq]
          have hk : 2 ^ (L - 1) = 256 ^ k * 128 := by
            rw [pow256, show L - 1 = 8 * k + 7 by omega, Nat.pow_add]
          have hkL : 2 ^ L = 256 ^ k * 256 := by rw [hLq, Nat.pow_succ]
          by_cases hfit : 2 * V ≤ 2 ^ (8 * (k + 1))
          · have hge : (2 ^ L - V) / 256 ^ k ≥ 128 :=
              (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).mpr (by
                rw [Nat.mul_comm]; rw [pow256] at hLq; omega)
            simp only [show k + 1 > 0 by omega, hlast, hge, and_self, decide_true, ite_true]
            left
            refine ⟨⟨_, rfl, lowBytes_length _ _, lowBytes_all _ _, ?_⟩, ?_⟩
            · rw [htarget _ hfit, bytesVal_lowBytes, hEq, hLq, pow256]
            · have : 2 * (V : Int) ≤ 2 ^ (8 * (k + 1)) := by exact_mod_cast hfit
              omega
          · have hlt : (2 ^ L - V) / 256 ^ k < 128 :=
              (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr (by
                rw [Nat.mul_comm]; rw [pow256] at hLq; omega)
            simp only [show k + 1 > 0 by omega, hlast, show ¬ ((2 ^ L - V) / 256 ^ k ≥ 128) by omega,
              and_false, decide_false, Bool.false_eq_true, ite_false]
            right; refine ⟨⟨_, rfl, rfl⟩, ?_⟩
            have : 2 ^ (8 * (k + 1)) < 2 * (V : Int) := by exact_mod_cast (by omega)
            omega
      · simp only [hqn', ite_false]
        left
        have hfit : 2 * V ≤ 2 ^ (8 * n) := by
          have : 2 ^ (L + 1) ≤ 2 ^ (8 * n) := Nat.pow_le_pow_right (by decide) (by omega)
          rw [Nat.pow_succ] at this; omega
        have hqn2 : 256 ^ q ≤ 2 ^ (8 * n) := by
          rw [pow256]; exact Nat.pow_le_pow_right (by decide) (by omega)
        refine ⟨⟨_, rfl, ?_, ?_, ?_⟩, ?_⟩
        · simp [lowBytes_length]; omega
        · exact allBytes_append (lowBytes_all _ _) (allBytes_replicate _ _ (by decide))
        · rw [htarget _ hfit, bytesVal_append, bytesVal_lowBytes, lowBytes_length, hEq]
          have hrep := bytesVal_replicate_255 (n - q)
          have e2 : 256 ^ q * bytesVal (List.replicate (n - q) 255) = 2 ^ (8 * n) - 256 ^ q := by
            rw [show bytesVal (List.replicate (n - q) 255) = 256 ^ (n - q) - 1 by omega,
              Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, show q + (n - q) = n by omega, pow256]
          rw [e2]
          have : (((2 ^ L - V) + (2 ^ (8 * n) - 256 ^ q) : Nat) : Int) = ((2 ^ (8 * n) - V : Nat) : Int) := by
            congr 1; omega
          exact this
        · have : 2 * (V : Int) ≤ 2 ^ (8 * n) := by exact_mod_cast hfit
          omega

end PyLean.MathInt
