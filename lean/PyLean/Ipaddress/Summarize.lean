import PyLean.Ipaddress.Spec

/-!
`summarize_address_range`.
-/

namespace PyLean.Ipaddress

open PyLean

/-- `summarize_address_range` docstring, ipaddress.py:201-232: for
`first <= last` it returns networks that cover exactly the range
`first..last`, in ascending order, each a valid network of the same version. -/
def SummarizeExactCover : Prop :=
  ∀ bits first last : Nat, IsVersion bits → first ≤ last → last < 2 ^ bits →
    ∃ nets, summarizeAddressRange bits first last = .ok nets ∧
      (∀ n ∈ nets, n.bits = bits ∧ n.Valid) ∧ Tiles nets first last

theorem lt_two_pow_bitLength (b : Nat) : b < 2 ^ bitLength b := by
  unfold bitLength
  split
  · omega
  · exact Nat.lt_log2_self

theorem bitLength_le_of_lt {x k : Nat} (h : x < 2 ^ k) : bitLength x ≤ k := by
  unfold bitLength
  split
  · omega
  · have := (Nat.log2_lt (n := x) (k := k) (by omega)).mpr h
    omega

theorem two_pow_bitLength_pred_le {m : Nat} (h : m ≠ 0) : 2 ^ (bitLength m - 1) ≤ m := by
  unfold bitLength
  simp only [h, ite_false, Nat.add_sub_cancel]
  exact Nat.log2_self_le h

theorem testBit_notAnd (a b i : Nat) :
    (notAnd a b).testBit i = (!a.testBit i && b.testBit i) := by
  unfold notAnd
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  by_cases h : i < bitLength b
  · simp [h]
  · have hb : b.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt_two_pow_bitLength b)
        (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hb]

theorem exists_two_pow_mul_odd : ∀ n : Nat, n ≠ 0 → ∃ k q, n = 2 ^ k * (2 * q + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · obtain ⟨k, q, hkq⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨k + 1, q, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, ← hkq]
      omega
    · exact ⟨0, n / 2, by simp; omega⟩

theorem testBit_false_of_dvd {x n i : Nat} (h : 2 ^ n ∣ x) (hi : i < n) :
    x.testBit i = false := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.testBit_two_pow_mul]
  simp; omega

theorem two_pow_bitLength_notAnd_dvd {n : Nat} (hn : n ≠ 0) :
    2 ^ bitLength (notAnd n (n - 1)) ∣ n := by
  obtain ⟨k, q, hkq⟩ := exists_two_pow_mul_odd n hn
  have hP : 0 < 2 ^ k := Nat.two_pow_pos k
  have e1 : n = 2 ^ (k + 1) * q + 2 ^ k := by
    rw [hkq, Nat.pow_succ, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  have e2 : n - 1 = 2 ^ (k + 1) * q + (2 ^ k - 1) := by omega
  have hlt : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hx : notAnd n (n - 1) < 2 ^ k := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [testBit_notAnd, e2, e1, Nat.testBit_two_pow_mul_add _ hlt,
      Nat.testBit_two_pow_mul_add _ (by omega)]
    by_cases hik : i < k + 1
    · have : i = k := by omega
      subst this
      simp [hik]
    · simp [hik]
  have hb := bitLength_le_of_lt hx
  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hb) ⟨_, hkq⟩

theorem crzb_spec (first bits : Nat) :
    countRighthandZeroBits first bits ≤ bits ∧ 2 ^ countRighthandZeroBits first bits ∣ first := by
  unfold countRighthandZeroBits
  split
  · subst_vars; exact ⟨Nat.le_refl _, Nat.dvd_zero _⟩
  · rename_i h
    refine ⟨Nat.min_le_left _ _, ?_⟩
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.min_le_right _ _))
      (two_pow_bitLength_notAnd_dvd h)

theorem and_ipIntFromPrefix {x n bits : Nat} (hd : 2 ^ n ∣ x) (hx : x < 2 ^ bits)
    (hn : n ≤ bits) : x &&& ipIntFromPrefix bits (bits - n) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [ipIntFromPrefix, allOnes, Nat.testBit_and, Nat.testBit_xor,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < n
  · simp [testBit_false_of_dvd hd h1]
  · by_cases h2 : i < bits
    · have : ¬ (bits - n + i < bits) := by omega
      simp [h2, this]
    · have : x.testBit i = false := Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [this]

theorem mkNet_ok {a n bits : Nat} (hd : 2 ^ n ∣ a) (ha : a < 2 ^ bits) (hn : n ≤ bits) :
    mkNet bits (a : Int) ((bits - n : Nat) : Int) = .ok ⟨bits, a, bits - n⟩ := by
  have hm := and_ipIntFromPrefix hd ha hn
  have h1 : ¬ ((a : Int) > ((allOnes bits : Nat) : Int)) := by
    unfold allOnes; omega
  have h0 : ¬ ((a : Int) < 0) := by omega
  simp [mkNet, checkIntAddress, h1, h0, bind, Except.bind, hm, pure, Except.pure]

theorem summarizeLoop_spec (bits last : Nat) (hlast : last < 2 ^ bits) :
    ∀ fuel first, first ≤ last + 1 → last + 2 - first ≤ fuel →
      ∃ nets, summarizeLoop bits last fuel first = .ok nets ∧
        (∀ n ∈ nets, n.bits = bits ∧ n.Valid) ∧ Tiles nets first last := by
  intro fuel
  induction fuel with
  | zero => intro first h1 h2; omega
  | succ fuel ih =>
    intro first h1 h2
    by_cases hfl : first ≤ last
    · obtain ⟨hr, hdvd⟩ := crzb_spec first bits
      have hm := two_pow_bitLength_pred_le (m := last - first + 1) (by omega)
      rw [summarizeLoop]; simp only [hfl, ↓reduceIte]
      generalize hn : min (countRighthandZeroBits first bits) (bitLength (last - first + 1) - 1) = nbits
      have hnb : nbits ≤ bits := by omega
      have hdvd' : 2 ^ nbits ∣ first := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hdvd
      have hle : 2 ^ nbits ≤ 2 ^ (bitLength (last - first + 1) - 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hpos : 1 ≤ 2 ^ nbits := Nat.one_le_two_pow
      have hfit : first + 2 ^ nbits ≤ last + 1 := by omega
      have hfb : first < 2 ^ bits := by omega
      have hvalid : (⟨bits, first, bits - nbits⟩ : Net).Valid := by
        refine ⟨Nat.sub_le _ _, hfb, ?_⟩
        show first % 2 ^ (bits - (bits - nbits)) = 0
        rw [Nat.sub_sub_self hnb]
        exact Nat.dvd_iff_mod_eq_zero.mp hdvd'
      have hsize : (⟨bits, first, bits - nbits⟩ : Net).size = 2 ^ nbits := by
        show 2 ^ (bits - (bits - nbits)) = _
        rw [Nat.sub_sub_self hnb]
      simp only [mkNet_ok hdvd' hfb hnb, Nat.shiftLeft_eq, Nat.one_mul]
      by_cases hend : first + 2 ^ nbits - 1 = allOnes bits
      · refine ⟨[⟨bits, first, bits - nbits⟩], ?_, ?_, ?_⟩
        · simp [hend, bind, Except.bind, pure, Except.pure]
        · intro n hn
          simp only [List.mem_singleton] at hn
          subst hn
          exact ⟨rfl, hvalid⟩
        · refine ⟨rfl, ?_⟩
          show first + _ = last + 1
          rw [hsize]
          unfold allOnes at hend
          omega
      · obtain ⟨rest, hrest, hv, ht⟩ := ih (first + 2 ^ nbits) (by omega) (by omega)
        refine ⟨⟨bits, first, bits - nbits⟩ :: rest, ?_, ?_, ?_⟩
        · simp [hend, hrest, bind, Except.bind, pure, Except.pure]
        · intro n hn
          rcases List.mem_cons.mp hn with rfl | hn
          · exact ⟨rfl, hvalid⟩
          · exact hv n hn
        · refine ⟨rfl, ?_⟩
          rw [hsize]
          exact ht
    · refine ⟨[], ?_, ?_, ?_⟩
      · rw [summarizeLoop]; simp only [hfl, ↓reduceIte]
      · simp
      · show first = last + 1
        omega

theorem summarizeExactCover_proven : SummarizeExactCover := by
  intro bits first last _ hfl hlast
  have hng : ¬ first > last := by omega
  rw [summarizeAddressRange]; simp only [hng, ↓reduceIte]
  exact summarizeLoop_spec bits last hlast _ first (by omega) (by omega)


/-- The docstring's error contract: `first > last` raises `ValueError`. -/
def SummarizeRejectsReversed : Prop :=
  ∀ bits first last : Nat, first > last →
    summarizeAddressRange bits first last =
      .error (.valueError "last IP address must be greater than first")

theorem summarizeRejectsReversed_proven : SummarizeRejectsReversed := by
  intro bits first last h
  simp [summarizeAddressRange, h]

end PyLean.Ipaddress
