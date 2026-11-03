import PyLean.Ipaddress.Spec

/-!
`summarize_address_range`.
-/

namespace PyLean.Ipaddress

open PyLean

/-- The blocks of the docstring's summary of `lo..last` (ipaddress.py:198-205, "Summarize a network
range given the first and last IP addresses", with the doctest's `192.0.2.0/25, 192.0.2.128/31,
192.0.2.130/32`): each block starts where the previous one ended, is aligned to its size, ends at
or below `last`, and is the largest such block: doubling it would make the prefix negative, break
the alignment, or pass `last`. At each start exactly one size passes, so `Greedy` fixes the list. -/
def Greedy (bits last : Nat) : List Net → Nat → Prop
  | [], lo => lo = last + 1
  | n :: ns, lo =>
    n.bits = bits ∧ n.addr = lo ∧ n.prefixlen ≤ bits ∧ lo % n.size = 0 ∧ lo + n.size ≤ last + 1 ∧
      (n.prefixlen = 0 ∨ lo % (2 * n.size) ≠ 0 ∨ last + 1 < lo + 2 * n.size) ∧
      Greedy bits last ns (lo + n.size)

/-- `summarize_address_range` docstring, ipaddress.py:198-229: for addresses `first <= last` of one
version (`last < 2**bits`, the type invariant of `_ip`), the result is the summary of
`first..last`: valid networks, each the largest aligned block that starts where the previous one
ended and does not pass `last`. -/
def SummarizeExactCover : Prop :=
  ∀ bits first last : Nat, IsVersion bits → first ≤ last → last < 2 ^ bits →
    ∃ nets, summarizeOp (.addr bits first) (.addr bits last) = .ok nets ∧
      (∀ n ∈ nets, n.Valid) ∧ Greedy bits last nets first

/-- `_count_righthand_zero_bits(number, bits)`, ipaddress.py:181-194, "the number of zero bits on
the right hand side of the number", capped at `bits`: for `0` it is `bits`; otherwise `2**c`
divides `number`, and `2**(c+1)` does not unless the cap was reached. For the non-negative ints
its callers pass (`_ip` and netmask ints). -/
def CrzbExact : Prop :=
  ∀ number bits : Nat,
    (number = 0 → countRighthandZeroBits number bits = bits) ∧
    (number ≠ 0 → countRighthandZeroBits number bits ≤ bits ∧
      2 ^ countRighthandZeroBits number bits ∣ number ∧
      (countRighthandZeroBits number bits < bits → ¬ 2 ^ (countRighthandZeroBits number bits + 1) ∣ number))

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

theorem bitLength_two_pow_sub_one (k : Nat) : bitLength (2 ^ k - 1) = k := by
  have h1 := bitLength_le_of_lt (x := 2 ^ k - 1) (k := k) (by have := Nat.two_pow_pos k; omega)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · decide
  · have hm : 2 ^ k - 1 ≠ 0 := by
      have : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
      omega
    have h2 := lt_two_pow_bitLength (2 ^ k - 1)
    apply Nat.le_antisymm h1
    apply Nat.le_of_not_lt
    intro hlt
    have : 2 ^ bitLength (2 ^ k - 1) ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have e : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    omega

theorem notAnd_odd (k q : Nat) :
    notAnd (2 ^ k * (2 * q + 1)) (2 ^ k * (2 * q + 1) - 1) = 2 ^ k - 1 := by
  have hP : 0 < 2 ^ k := Nat.two_pow_pos k
  have e1 : 2 ^ k * (2 * q + 1) = 2 ^ (k + 1) * q + 2 ^ k := by
    rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  have e2 : 2 ^ k * (2 * q + 1) - 1 = 2 ^ (k + 1) * q + (2 ^ k - 1) := by omega
  have hlt : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_notAnd, e2, e1, Nat.testBit_two_pow_mul_add _ hlt,
    Nat.testBit_two_pow_mul_add _ (by omega), Nat.testBit_two_pow_sub_one]
  by_cases hik : i < k + 1
  · by_cases hk : i = k
    · subst hk; simp
    · have : i < k := by omega
      simp [hik, Nat.testBit_two_pow, this, hk]
      omega
  · simp [hik]; omega

theorem crzb_odd (k q bits : Nat) :
    countRighthandZeroBits (2 ^ k * (2 * q + 1)) bits = min bits k := by
  have hn : 2 ^ k * (2 * q + 1) ≠ 0 := Nat.mul_ne_zero (by have := Nat.two_pow_pos k; omega) (by omega)
  simp only [countRighthandZeroBits, hn, ↓reduceIte, notAnd_odd, bitLength_two_pow_sub_one]

theorem not_two_pow_succ_dvd (k q : Nat) : ¬ 2 ^ (k + 1) ∣ 2 ^ k * (2 * q + 1) := by
  intro h
  rw [Nat.pow_succ, Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos k)] at h
  omega

/-- The count stops at the lowest set bit, unless the cap `bits` stops it first. -/
theorem crzb_max (number bits : Nat) :
    countRighthandZeroBits number bits = bits ∨
      ¬ 2 ^ (countRighthandZeroBits number bits + 1) ∣ number := by
  by_cases h0 : number = 0
  · left; simp [countRighthandZeroBits, h0]
  · obtain ⟨k, q, rfl⟩ := exists_two_pow_mul_odd number h0
    rw [crzb_odd]
    by_cases hk : bits ≤ k
    · left; omega
    · right; rw [show min bits k = k by omega]; exact not_two_pow_succ_dvd k q

theorem crzbExact_proven : CrzbExact := by
  intro number bits
  refine ⟨fun h => by simp [countRighthandZeroBits, h], fun h => ?_⟩
  obtain ⟨h1, h2⟩ := crzb_spec number bits
  refine ⟨h1, h2, fun hlt => ?_⟩
  rcases crzb_max number bits with e | e
  · omega
  · exact e

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

theorem bitLength_pos {m : Nat} (h : m ≠ 0) : 1 ≤ bitLength m := by
  unfold bitLength; simp [h]

theorem summarizeLoop_spec (bits last : Nat) (hlast : last < 2 ^ bits) :
    ∀ fuel first, first ≤ last + 1 → last + 2 - first ≤ fuel →
      ∃ nets, summarizeLoop bits last fuel first = .ok nets ∧
        (∀ n ∈ nets, n.Valid) ∧ Greedy bits last nets first := by
  intro fuel
  induction fuel with
  | zero => intro first h1 h2; omega
  | succ fuel ih =>
    intro first h1 h2
    by_cases hfl : first ≤ last
    · obtain ⟨hr, hdvd⟩ := crzb_spec first bits
      have hmax := crzb_max first bits
      have hm := two_pow_bitLength_pred_le (m := last - first + 1) (by omega)
      have hbl := lt_two_pow_bitLength (last - first + 1)
      have hbp := bitLength_pos (m := last - first + 1) (by omega)
      rw [summarizeLoop]; simp only [hfl, ↓reduceIte]
      generalize hn : min (countRighthandZeroBits first bits) (bitLength (last - first + 1) - 1) = nbits
      generalize hc : countRighthandZeroBits first bits = c at hr hdvd hmax hn
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
      have hmaxi : bits - nbits = 0 ∨ first % (2 * 2 ^ nbits) ≠ 0 ∨
          last + 1 < first + 2 * 2 ^ nbits := by
        by_cases hcn : nbits = c
        · subst hcn
          rcases hmax with e | e
          · left; omega
          · right; left
            intro h0
            exact e (by rw [Nat.pow_succ, Nat.mul_comm]; exact Nat.dvd_of_mod_eq_zero h0)
        · right; right
          have e : nbits = bitLength (last - first + 1) - 1 := by omega
          have : 2 * 2 ^ nbits = 2 ^ bitLength (last - first + 1) := by
            rw [show bitLength (last - first + 1) = nbits + 1 by omega, Nat.pow_succ]; omega
          omega
      have hhead : (⟨bits, first, bits - nbits⟩ : Net).bits = bits ∧
          (⟨bits, first, bits - nbits⟩ : Net).addr = first ∧
          (⟨bits, first, bits - nbits⟩ : Net).prefixlen ≤ bits ∧
          first % (⟨bits, first, bits - nbits⟩ : Net).size = 0 ∧
          first + (⟨bits, first, bits - nbits⟩ : Net).size ≤ last + 1 ∧
          ((⟨bits, first, bits - nbits⟩ : Net).prefixlen = 0 ∨
            first % (2 * (⟨bits, first, bits - nbits⟩ : Net).size) ≠ 0 ∨
            last + 1 < first + 2 * (⟨bits, first, bits - nbits⟩ : Net).size) := by
        rw [hsize]
        exact ⟨rfl, rfl, Nat.sub_le _ _, Nat.dvd_iff_mod_eq_zero.mp hdvd', hfit, hmaxi⟩
      simp only [mkNet_ok hdvd' hfb hnb, Nat.shiftLeft_eq, Nat.one_mul]
      by_cases hend : first + 2 ^ nbits - 1 = allOnes bits
      · refine ⟨[⟨bits, first, bits - nbits⟩], ?_, ?_, ?_⟩
        · simp [hend, bind, Except.bind, pure, Except.pure]
        · intro n hn
          simp only [List.mem_singleton] at hn
          subst hn
          exact hvalid
        · refine ⟨hhead.1, hhead.2.1, hhead.2.2.1, hhead.2.2.2.1, hhead.2.2.2.2.1, hhead.2.2.2.2.2, ?_⟩
          show first + _ = last + 1
          rw [hsize]
          unfold allOnes at hend
          omega
      · obtain ⟨rest, hrest, hv, ht⟩ := ih (first + 2 ^ nbits) (by omega) (by omega)
        refine ⟨⟨bits, first, bits - nbits⟩ :: rest, ?_, ?_, ?_⟩
        · simp [hend, hrest, bind, Except.bind, pure, Except.pure]
        · intro n hn
          rcases List.mem_cons.mp hn with rfl | hn
          · exact hvalid
          · exact hv n hn
        · refine ⟨hhead.1, hhead.2.1, hhead.2.2.1, hhead.2.2.2.1, hhead.2.2.2.2.1, hhead.2.2.2.2.2, ?_⟩
          rw [hsize]
          exact ht
    · refine ⟨[], ?_, ?_, ?_⟩
      · rw [summarizeLoop]; simp only [hfl, ↓reduceIte]
      · simp
      · show first = last + 1
        omega

theorem summarizeExactCover_proven : SummarizeExactCover := by
  intro bits first last hb hfl hlast
  have hng : ¬ first > last := by omega
  have hv : ¬ (versionOf bits ≠ 4 ∧ versionOf bits ≠ 6) := by
    rcases hb with rfl | rfl <;> decide
  simp only [summarizeOp, Ne, not_true_eq_false, ↓reduceIte]
  rw [summarizeAddressRange]; simp only [hng, hv, ↓reduceIte]
  exact summarizeLoop_spec bits last hlast _ first (by omega) (by omega)

/-- `Greedy` admits one list: at each start the block size is fixed. So `SummarizeExactCover`
pins the result, not just a tiling. -/
theorem greedy_unique (bits last : Nat) :
    ∀ (ns ms : List Net) (lo : Nat), Greedy bits last ns lo → Greedy bits last ms lo → ns = ms := by
  intro ns
  induction ns with
  | nil =>
    intro ms lo h1 h2
    cases ms with
    | nil => rfl
    | cons m ms =>
      obtain ⟨-, -, -, -, hf, -⟩ := h2
      have : 0 < m.size := Nat.two_pow_pos _
      simp only [Greedy] at h1; omega
  | cons n ns ih =>
    intro ms lo h1 h2
    cases ms with
    | nil =>
      obtain ⟨-, -, -, -, hf, -⟩ := h1
      have : 0 < n.size := Nat.two_pow_pos _
      simp only [Greedy] at h2; omega
    | cons m ms =>
      obtain ⟨nb, na, np, nal, nf, nmx, nrest⟩ := h1
      obtain ⟨mb, ma, mp, mal, mf, mmx, mrest⟩ := h2
      have hsz : n.prefixlen = m.prefixlen := by
        -- sizes are powers of two; the larger one would violate the other's maximality
        unfold Net.size at *
        rw [nb] at nal nf nmx; rw [mb] at mal mf mmx
        rcases Nat.lt_trichotomy n.prefixlen m.prefixlen with hlt | heq | hlt
        · -- n's block is larger: m's doubled block fits inside n's
          have hd : 2 * 2 ^ (bits - m.prefixlen) ∣ 2 ^ (bits - n.prefixlen) := by
            rw [← Nat.pow_succ']; exact Nat.pow_dvd_pow 2 (by omega)
          have hle : 2 * 2 ^ (bits - m.prefixlen) ≤ 2 ^ (bits - n.prefixlen) :=
            Nat.le_of_dvd (Nat.two_pow_pos _) hd
          rcases mmx with h | h | h
          · omega
          · exact absurd (Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hd (Nat.dvd_of_mod_eq_zero nal))) h
          · omega
        · exact heq
        · have hd : 2 * 2 ^ (bits - n.prefixlen) ∣ 2 ^ (bits - m.prefixlen) := by
            rw [← Nat.pow_succ']; exact Nat.pow_dvd_pow 2 (by omega)
          have hle : 2 * 2 ^ (bits - n.prefixlen) ≤ 2 ^ (bits - m.prefixlen) :=
            Nat.le_of_dvd (Nat.two_pow_pos _) hd
          rcases nmx with h | h | h
          · omega
          · exact absurd (Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hd (Nat.dvd_of_mod_eq_zero mal))) h
          · omega
      have hnm : n = m := by
        obtain ⟨nb', na', np'⟩ := n
        obtain ⟨mb', ma', mp'⟩ := m
        simp only at nb na hsz mb ma
        simp only [Net.mk.injEq]
        exact ⟨by omega, by omega, by omega⟩
      subst hnm
      rw [ih ms (lo + n.size) nrest mrest]

/-- The docstring's "Raise:" list, ipaddress.py:214-221, in the order the code checks it
(:223-237): an argument that is not an address raises `TypeError('first and last must be IP
addresses, not networks')`; addresses of two versions raise `TypeError`; `first > last` raises
`ValueError('last IP address must be greater than first')`; a version other than 4 and 6 raises
`ValueError('unknown IP version')`. -/
def SummarizeRejects : Prop :=
  (∀ f l : Operand, (∀ b x, f ≠ .addr b x) ∨ (∀ b y, l ≠ .addr b y) →
    summarizeOp f l = .error (.typeError "first and last must be IP addresses, not networks")) ∧
  (∀ b1 b2 x y : Nat, versionOf b1 ≠ versionOf b2 →
    summarizeOp (.addr b1 x) (.addr b2 y) = .error (.typeError "~are not of the same version")) ∧
  (∀ b1 b2 x y : Nat, versionOf b1 = versionOf b2 → x > y →
    summarizeOp (.addr b1 x) (.addr b2 y) =
      .error (.valueError "last IP address must be greater than first")) ∧
  (∀ b1 b2 x y : Nat, versionOf b1 = versionOf b2 → ¬ IsVersion b1 → x ≤ y →
    summarizeOp (.addr b1 x) (.addr b2 y) = .error (.valueError "unknown IP version"))

theorem summarizeRejects_proven : SummarizeRejects := by
  refine ⟨fun f l h => ?_, fun b1 b2 x y h => ?_, fun b1 b2 x y h hxy => ?_,
    fun b1 b2 x y h hb hxy => ?_⟩
  · cases f <;> cases l <;> first
      | rfl
      | (rcases h with h | h <;> exact absurd rfl (h _ _))
  · simp [summarizeOp, h]
  · simp [summarizeOp, h, summarizeAddressRange, hxy]
  · have hv : versionOf b1 = 0 := by
      unfold versionOf; simp only [IsVersion, not_or] at hb; simp [hb.1, hb.2]
    have hv2 : versionOf b2 = 0 := by rw [← h, hv]
    have hn : ¬ x > y := by omega
    simp [summarizeOp, h, summarizeAddressRange, hn, hv2]

end PyLean.Ipaddress
