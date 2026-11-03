import PyLean.Ipaddress.Parse6

/-! `'%032x' % ip_int` and its four-character slices (`_BaseV6._string_from_ip_int`,
Lib/ipaddress.py:1855-1856), for every int the method lets through.

For `0 <= ip_int < 2**128` the slices are the eight 16-bit groups of `ip_int`, so
`stringFromIpInt6Int` is `stringFromIpInt6` (`stringFromIpInt6Int_nat`). For a negative `ip_int`
the text is `-` and the hex digits of `abs(ip_int)`, padded to 31 digits; the slices read only the
first 32 characters, so the first slice is `-` and three digits and the other seven are groups of
the leading 31 digits (`hextetsOfInt_neg` in `Compress6`). -/

namespace PyLean.Ipaddress

open PyLean

/-! ## Digits -/

theorem pow16_pos (j : Nat) : 0 < 16 ^ j := by
  induction j with
  | zero => decide
  | succ j ih => rw [Nat.pow_succ]; omega

theorem digitsW_zero (m : Nat) : digitsW 0 m = [] := rfl

theorem digitsW_length (w m : Nat) : (digitsW w m).length = w := by simp [digitsW]

theorem hd_pow_congr (m a b : Nat) (h : a = b) : hd (m / 16 ^ a % 16) = hd (m / 16 ^ b % 16) := by
  subst h; rfl

theorem digitsW_succ (w m : Nat) : digitsW (w + 1) m = hd (m / 16 ^ w % 16) :: digitsW w m := by
  apply List.ext_getElem
  · simp [digitsW_length]
  · intro j h1 h2
    cases j with
    | zero =>
      simp only [digitsW, List.getElem_map, List.getElem_range, List.getElem_cons_zero] <;>
        exact hd_pow_congr _ _ _ (by omega)
    | succ j =>
      simp only [digitsW, List.getElem_map, List.getElem_range, List.getElem_cons_succ] <;>
        exact hd_pow_congr _ _ _ (by omega)

/-- The `k + d` digits of `m` are the `k` digits of `m / 16**d` and then the `d` digits of `m`. -/
theorem digitsW_add (k d m : Nat) : digitsW (k + d) m = digitsW k (m / 16 ^ d) ++ digitsW d m := by
  induction k with
  | zero => simp [digitsW_zero]
  | succ k ih =>
    rw [show k + 1 + d = (k + d) + 1 by omega, digitsW_succ, ih, digitsW_succ, List.cons_append,
      Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm d k]

/-! ## The number of hex digits -/

theorem lt_16pow_succ (m : Nat) : m < 16 ^ (m + 1) := by
  induction m with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

theorem hexLenAux_spec : ∀ f m, m < 16 ^ (f + 1) →
    1 ≤ hexLenAux f m ∧ m < 16 ^ hexLenAux f m ∧
      (hexLenAux f m = 1 ∨ 16 ^ (hexLenAux f m - 1) ≤ m) := by
  intro f
  induction f with
  | zero =>
    intro m hm
    show 1 ≤ 1 ∧ m < 16 ^ 1 ∧ (1 = 1 ∨ 16 ^ (1 - 1) ≤ m)
    exact ⟨Nat.le_refl 1, by simpa using hm, Or.inl rfl⟩
  | succ f ih =>
    intro m hm
    by_cases h16 : m < 16
    · have e : hexLenAux (f + 1) m = 1 := by simp [hexLenAux, h16]
      rw [e]
      exact ⟨Nat.le_refl 1, by simpa using h16, Or.inl rfl⟩
    · have e : hexLenAux (f + 1) m = hexLenAux f (m / 16) + 1 := by simp [hexLenAux, h16]
      have hm' : m / 16 < 16 ^ (f + 1) := by
        rw [Nat.pow_succ] at hm; omega
      obtain ⟨h1, h2, h3⟩ := ih (m / 16) hm'
      rw [e]
      generalize hexLenAux f (m / 16) = L at h1 h2 h3 ⊢
      refine ⟨by omega, ?_, Or.inr ?_⟩
      · rw [Nat.pow_succ]; omega
      · rw [Nat.add_sub_cancel]
        rcases h3 with h3 | h3
        · subst h3
          rw [Nat.pow_one]; omega
        · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
          rw [Nat.add_sub_cancel] at h3
          rw [Nat.pow_succ]; omega

theorem hexLen_spec (m : Nat) :
    1 ≤ hexLen m ∧ m < 16 ^ hexLen m ∧ (hexLen m = 1 ∨ 16 ^ (hexLen m - 1) ≤ m) :=
  hexLenAux_spec m m (lt_16pow_succ m)

theorem hexLen_le (m w : Nat) (hw : 1 ≤ w) (h : m < 16 ^ w) : hexLen m ≤ w := by
  obtain ⟨h1, h2, h3⟩ := hexLen_spec m
  rcases Nat.lt_or_ge w (hexLen m) with hc | hc
  · rcases h3 with h3 | h3
    · omega
    · have : 16 ^ w ≤ 16 ^ (hexLen m - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  · exact hc

theorem hexLen_eq (m k : Nat) (hk : 2 ≤ k) (h1 : 16 ^ (k - 1) ≤ m) (h2 : m < 16 ^ k) :
    hexLen m = k := by
  obtain ⟨g1, g2, -⟩ := hexLen_spec m
  have hle := hexLen_le m k (by omega) h2
  rcases Nat.lt_or_ge (hexLen m) k with hlt | hge
  · have : 16 ^ hexLen m ≤ 16 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · omega

/-! ## `'%032x'` -/

/-- For `0 <= n < 2**128`, `'%032x' % n` is the 32 digits of `n`. -/
theorem fmt032x_nat (n : Nat) (h : n < 2 ^ 128) :
    fmt032x n = (hd (n / 16 ^ 31 % 16) :: digitsW 31 n) ++ [] := by
  have h' : n < 16 ^ 32 := by rw [show (16 : Nat) ^ 32 = 2 ^ 128 from rfl]; exact h
  have hl := hexLen_le n 32 (by decide) h'
  have ha : (n : Int).natAbs = n := by simp
  have hneg : ¬ ((n : Int) < 0) := by omega
  unfold fmt032x
  rw [if_neg hneg, ha, show max 32 (hexLen n) = 31 + 1 by omega, digitsW_succ, List.append_nil]

/-- For `m > 0` with `k` hex digits (or at most 31), `'%032x' % -m` is `-`, the leading 31 hex
digits of `m`, and possibly more digits. -/
theorem fmt032x_neg (m k : Nat) (hm : 0 < m) (hk : m < 16 ^ k) (hk' : k ≤ 31 ∨ 16 ^ (k - 1) ≤ m) :
    ∃ B, fmt032x (-(m : Int)) = ('-' :: digitsW 31 (m / 16 ^ (k - 31))) ++ B := by
  unfold fmt032x
  have hneg : -(m : Int) < 0 := by omega
  have ha : (-(m : Int)).natAbs = m := by simp
  rw [if_pos hneg, ha]
  by_cases hk31 : k ≤ 31
  · have hl := hexLen_le m 31 (by decide)
      (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) hk31))
    refine ⟨[], ?_⟩
    rw [show max 31 (hexLen m) = 31 by omega, show k - 31 = 0 by omega, Nat.pow_zero, Nat.div_one,
      List.append_nil]
  · have hk2 : 16 ^ (k - 1) ≤ m := by
      rcases hk' with h | h
      · omega
      · exact h
    have hL := hexLen_eq m k (by omega) hk2 hk
    refine ⟨digitsW (k - 31) m, ?_⟩
    rw [show max 31 (hexLen m) = 31 + (k - 31) by omega, digitsW_add, List.cons_append]

/-! ## The slices -/

theorem drop_cons_four (c : Char) (L : List Char) (i : Nat) (h : 1 ≤ i) :
    (c :: L).drop (4 * i) = L.drop (4 * i - 1) := by
  obtain ⟨j, hj⟩ : ∃ j, 4 * i = j + 1 := ⟨4 * i - 1, by omega⟩
  rw [hj, List.drop_succ_cons, Nat.add_sub_cancel]

/-- `hex_str[4i:4i+4]` for `1 <= i < 8`: four digits of the 31 after the first character. -/
theorem slice_hi (c : Char) (v : Nat) (B : List Char) (i : Nat) (h1 : 1 ≤ i) (h8 : i < 8) :
    ((((c :: digitsW 31 v) ++ B).drop (4 * i)).take 4) = digitsW 4 (v / 16 ^ (28 - 4 * i)) := by
  have e1 := digitsW_add (4 * i - 1) (32 - 4 * i) v
  rw [show 4 * i - 1 + (32 - 4 * i) = 31 by omega] at e1
  have e2 := digitsW_add 4 (28 - 4 * i) v
  rw [show 4 + (28 - 4 * i) = 32 - 4 * i by omega] at e2
  rw [List.cons_append, drop_cons_four c _ i h1, e1, e2, List.append_assoc,
    List.drop_left' (digitsW_length _ _), List.append_assoc, List.take_left' (digitsW_length _ _)]

/-- `hex_str[0:4]`: the first character and three digits. -/
theorem slice_zero (c : Char) (v : Nat) (B : List Char) :
    ((((c :: digitsW 31 v) ++ B).drop (4 * 0)).take 4) = c :: digitsW 3 (v / 16 ^ 28) := by
  have e := digitsW_add 3 28 v
  rw [show 3 + 28 = 31 from rfl] at e
  rw [e]
  show c :: ((digitsW 3 (v / 16 ^ 28) ++ digitsW 28 v) ++ B).take 3 = _
  rw [List.append_assoc, List.take_left' (digitsW_length _ _)]

/-! ## `int(..., 16)` and `'%x'` of a slice -/

theorem hd_facts : ∀ k, k < 16 → hexValC (hd k) = k ∧ hd k ≠ '-' := by decide

theorem hexValC_hd_mod (x : Nat) : hexValC (hd (x % 16)) = x % 16 :=
  (hd_facts _ (Nat.mod_lt _ (by decide))).1

theorem hd_mod_ne (x : Nat) : hd (x % 16) ≠ '-' := (hd_facts _ (Nat.mod_lt _ (by decide))).2

theorem hexVal_digits4 (v : Nat) : hexVal (digitsW 4 v) = v % 65536 := by
  have e : digitsW 4 v =
      [hd (v / 16 ^ 3 % 16), hd (v / 16 ^ 2 % 16), hd (v / 16 ^ 1 % 16), hd (v / 16 ^ 0 % 16)] := rfl
  rw [e]
  simp only [hexVal, List.foldl_cons, List.foldl_nil, hexValC_hd_mod, Nat.reducePow]
  omega

theorem hexVal_digits3 (v : Nat) : hexVal (digitsW 3 v) = v % 4096 := by
  have e : digitsW 3 v = [hd (v / 16 ^ 2 % 16), hd (v / 16 ^ 1 % 16), hd (v / 16 ^ 0 % 16)] := rfl
  rw [e]
  simp only [hexVal, List.foldl_cons, List.foldl_nil, hexValC_hd_mod, Nat.reducePow]
  omega

theorem intHex_digits4 (v : Nat) : intHex (digitsW 4 v) = ((v % 65536 : Nat) : Int) := by
  have e : digitsW 4 v =
      [hd (v / 16 ^ 3 % 16), hd (v / 16 ^ 2 % 16), hd (v / 16 ^ 1 % 16), hd (v / 16 ^ 0 % 16)] := rfl
  have hne : ¬ ((digitsW 4 v).head? = some '-') := by
    rw [e]; simp [hd_mod_ne]
  unfold intHex
  rw [if_neg hne, hexVal_digits4]

theorem intHex_neg3 (u : Nat) : intHex ('-' :: digitsW 3 u) = -((u % 4096 : Nat) : Int) := by
  unfold intHex
  rw [if_pos (show ('-' :: digitsW 3 u).head? = some '-' from rfl)]
  simp only [List.tail_cons, hexVal_digits3]

theorem fmtX_nat (v : Nat) : fmtX (v : Int) = hexStr v := by
  unfold fmtX
  rw [if_neg (show ¬ ((v : Int) < 0) by omega)]
  simp

theorem fmtX_neg (u : Nat) : fmtX (-(u : Int)) = if u = 0 then hexStr 0 else '-' :: hexStr u := by
  unfold fmtX
  by_cases h : u = 0
  · subst h; simp
  · rw [if_pos (show -(u : Int) < 0 by omega), if_neg h]
    simp

/-! ## Non-negative ints -/

theorem hextetsOfInt_nat (n : Nat) (h : n < 2 ^ 128) : hextetsOfInt n = hextetsOf n := by
  unfold hextetsOfInt hextetsOf
  rw [fmt032x_nat n h]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have e4 : digitsW 4 (n / 16 ^ 28) = hd (n / 16 ^ 31 % 16) :: digitsW 3 (n / 16 ^ 28) := by
      rw [show (4 : Nat) = 3 + 1 from rfl, digitsW_succ, Nat.div_div_eq_div_mul, ← Nat.pow_add]
      all_goals rfl
    rw [slice_zero, ← e4, intHex_digits4, fmtX_nat]
    all_goals rfl
  · rw [slice_hi _ _ _ i hpos hi, intHex_digits4, fmtX_nat, show 28 - 4 * i = 4 * (7 - i) by omega,
      Nat.pow_mul]
    all_goals rfl

/-- For `0 <= n < 2**128` the mirror of `_string_from_ip_int` is `stringFromIpInt6`. -/
theorem stringFromIpInt6Int_nat (n : Nat) (h : n < 2 ^ 128) :
    stringFromIpInt6Int n = stringFromIpInt6 n := by
  unfold stringFromIpInt6Int stringFromIpInt6
  rw [hextetsOfInt_nat n h]

theorem stringFromIpInt6Py_nat (cls : V6Cls) (n : Nat) (h : n < 2 ^ 128) :
    stringFromIpInt6Py cls (some (n : Int)) = .ok (stringFromIpInt6 n) := by
  have hle : ¬ ((n : Int) > ((allOnes 128 : Nat) : Int)) := by unfold allOnes; omega
  unfold stringFromIpInt6Py
  dsimp only
  rw [if_neg hle, stringFromIpInt6Int_nat n h]

end PyLean.Ipaddress
