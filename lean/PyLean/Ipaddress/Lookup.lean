import PyLean.Ipaddress.Spec

/-!
Indexing and membership: `__getitem__`, `__contains__`, `overlaps`,
`subnet_of`.
-/

namespace PyLean.Ipaddress

open PyLean

/-- `allOnes bits >>> p = 2^(bits - p) - 1`. -/
private theorem allOnes_shiftRight (bits p : Nat) :
    allOnes bits >>> p = 2 ^ (bits - p) - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [allOnes, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  apply decide_eq_decide.mpr
  omega

/-- The hostmask is `2^(bits - prefixlen) - 1`. -/
private theorem Net.hostmask_eq (n : Net) : n.hostmask = 2 ^ (n.bits - n.prefixlen) - 1 := by
  unfold Net.hostmask Net.netmask ipIntFromPrefix
  rw [Nat.xor_comm, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, allOnes_shiftRight]

/-- `a ||| (2^k - 1) = a + (2^k - 1)` when `2^k ∣ a`. -/
private theorem or_two_pow_sub_one_of_mod (a k : Nat) (h : a % 2 ^ k = 0) :
    a ||| (2 ^ k - 1) = a + (2 ^ k - 1) := by
  have ha : a = (a / 2 ^ k) <<< k := by
    rw [Nat.shiftLeft_eq]
    have := Nat.mod_add_div a (2 ^ k)
    rw [Nat.mul_comm]; omega
  have hlt : 2 ^ k - 1 < 2 ^ k := Nat.sub_lt (Nat.two_pow_pos k) Nat.one_pos
  rw [ha, ← Nat.shiftLeft_add_eq_or_of_lt hlt]

/-- The broadcast address of a valid net is `addr + size - 1`. -/
private theorem Net.broadcast_eq (n : Net) (h : n.Valid) : n.broadcast = n.addr + (n.size - 1) := by
  unfold Net.broadcast
  rw [Net.hostmask_eq, or_two_pow_sub_one_of_mod _ _ h.2.2]
  rfl

private theorem Net.size_pos (n : Net) : 0 < n.size := Nat.two_pow_pos _

/-- A valid net lies within the address space. -/
private theorem Net.addr_add_size_le (n : Net) (h : n.Valid) : n.addr + n.size ≤ 2 ^ n.bits := by
  obtain ⟨hp, hlt, hmod⟩ := h
  unfold Net.size
  have hb : 2 ^ n.bits = 2 ^ (n.bits - n.prefixlen) * 2 ^ n.prefixlen := by
    rw [← Nat.pow_add]; congr 1; omega
  have hd := Nat.mod_add_div n.addr (2 ^ (n.bits - n.prefixlen))
  rw [hmod, Nat.zero_add] at hd
  generalize 2 ^ (n.bits - n.prefixlen) = K at *
  generalize n.addr / K = q at *
  rw [hb] at hlt ⊢
  rw [← hd] at hlt ⊢
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0; simp at hlt
    · exact h0
  have : q < 2 ^ n.prefixlen := Nat.lt_of_mul_lt_mul_left hlt
  have := Nat.mul_le_mul_left K (Nat.succ_le_of_lt this)
  rw [Nat.mul_succ] at this
  exact this

/-- `x &&& netmask` clears the host bits of an in-range address. -/
private theorem and_netmask (n : Net) (x : Nat) (hx : x < 2 ^ n.bits) :
    x &&& n.netmask = x / 2 ^ (n.bits - n.prefixlen) * 2 ^ (n.bits - n.prefixlen) := by
  rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  unfold Net.netmask ipIntFromPrefix
  rw [allOnes_shiftRight]
  simp only [allOnes, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < n.bits
  · by_cases hk : i ≥ n.bits - n.prefixlen
    · have e : n.bits - n.prefixlen + (i - (n.bits - n.prefixlen)) = i := by omega
      rw [e]
      have h1 : decide (i < n.bits - n.prefixlen) = false := by simp; omega
      simp [hi, hk, h1]
    · have h1 : decide (i < n.bits - n.prefixlen) = true := by simp; omega
      simp [hi, hk, h1]
  · have h0 : x.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    have h0' : x.testBit (n.bits - n.prefixlen + (i - (n.bits - n.prefixlen))) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h0, h0']

private theorem contains_eq_mem (n : Net) (x : Nat) (hn : n.Valid) (hx : x < 2 ^ n.bits) :
    contains n x = n.mem x := by
  unfold contains Net.mem
  rw [and_netmask n x hx]
  have hmod := hn.2.2
  have hK := Net.size_pos n
  unfold Net.size at *
  generalize 2 ^ (n.bits - n.prefixlen) = K at *
  have hd := Nat.mod_add_div n.addr K
  have hx1 := Nat.mod_add_div x K
  have hx2 := Nat.mod_lt x hK
  generalize n.addr = a at *
  rw [hmod, Nat.zero_add] at hd
  generalize a / K = q at *
  subst hd
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    rw [Nat.mul_comm] at h
    omega
  · intro ⟨h1, h2⟩
    have e1 : q ≤ x / K := (Nat.le_div_iff_mul_le hK).mpr (by rw [Nat.mul_comm]; exact h1)
    have e2 : x / K < q + 1 := (Nat.div_lt_iff_lt_mul hK).mpr (by rw [Nat.add_mul, Nat.mul_comm]; omega)
    have : x / K = q := by omega
    rw [this, Nat.mul_comm]

/-- `net[i]` behaves like indexing a Python sequence of the block's addresses:
for `-size <= i < size` it returns `addr + i mod size`, otherwise it raises
`IndexError`. Library docs: "network objects ... can be indexed". -/
def GetitemSequence : Prop :=
  ∀ (n : Net) (i : Int), n.Valid →
    getitem n i =
      if -(n.size : Int) ≤ i ∧ i < n.size then .ok (n.addr + (i % n.size).toNat)
      else .error (.indexError "address out of range")

theorem getitemSequence_proven : GetitemSequence := by
  intro n i hn
  unfold getitem
  rw [Net.broadcast_eq n hn]
  have hK := Net.size_pos n
  generalize n.size = K at *
  generalize n.addr = a
  by_cases hi : 0 ≤ i
  · by_cases h : i < K
    · have hm : i % (K : Int) = i := Int.emod_eq_of_lt hi h
      rw [ite_eq_left hi, ite_eq_right (by omega), ite_eq_left ⟨by omega, h⟩, hm]
      congr 1; omega
    · rw [ite_eq_left hi, ite_eq_left (by omega), ite_eq_right (by omega)]
  · by_cases h : -(K : Int) ≤ i
    · have hm : i % (K : Int) = i + K := by
        rw [← Int.add_emod_right]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [ite_eq_right hi, ite_eq_right (by omega), ite_eq_left ⟨h, by omega⟩, hm]
      congr 1; omega
    · rw [ite_eq_right hi, ite_eq_left (by omega), ite_eq_right (by omega)]

/-- `address in net` holds exactly for the addresses of the block. -/
def ContainsMem : Prop :=
  ∀ (n : Net) (x : Nat), n.Valid → x < 2 ^ n.bits → contains n x = n.mem x

theorem containsMem_proven : ContainsMem :=
  fun n x hn hx => contains_eq_mem n x hn hx

/-- `overlaps` docstring, ipaddress.py:747: "Tell if self is partly contained
in other", i.e. the two blocks share an address. -/
def OverlapsShareAddress : Prop :=
  ∀ a b : Net, a.Valid → b.Valid → a.bits = b.bits →
    (overlaps a b = true ↔ ∃ x, a.mem x = true ∧ b.mem x = true)

theorem overlapsShareAddress_proven : OverlapsShareAddress := by
  intro a b ha hb hbits
  have hal := Net.addr_add_size_le a ha
  have hbl := Net.addr_add_size_le b hb
  have hal' : a.addr + a.size ≤ 2 ^ b.bits := hbits ▸ hal
  have hbl' : b.addr + b.size ≤ 2 ^ a.bits := hbits ▸ hbl
  have haK := Net.size_pos a
  have hbK := Net.size_pos b
  have habc := Net.broadcast_eq a ha
  have hbbc := Net.broadcast_eq b hb
  unfold overlaps
  rw [contains_eq_mem b a.addr hb (by omega), contains_eq_mem b a.broadcast hb (by omega),
    contains_eq_mem a b.addr ha (by omega), contains_eq_mem a b.broadcast ha (by omega),
    habc, hbbc]
  unfold Net.mem
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (((h | h) | h) | h)
    · exact ⟨a.addr, ⟨by omega, by omega⟩, h⟩
    · exact ⟨a.addr + (a.size - 1), ⟨by omega, by omega⟩, h⟩
    · exact ⟨b.addr, h, ⟨by omega, by omega⟩⟩
    · exact ⟨b.addr + (b.size - 1), h, ⟨by omega, by omega⟩⟩
  · rintro ⟨x, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
    by_cases h : b.addr ≤ a.addr
    · exact Or.inl (Or.inl (Or.inl ⟨h, by omega⟩))
    · exact Or.inl (Or.inr ⟨by omega, by omega⟩)

/-- `subnet_of`: every address of `a` is an address of `b`. -/
def SubnetOfMem : Prop :=
  ∀ a b : Net, a.Valid → b.Valid → a.bits = b.bits →
    (subnetOf a b = true ↔ ∀ x, a.mem x = true → b.mem x = true)

theorem subnetOfMem_proven : SubnetOfMem := by
  intro a b ha hb _
  have haK := Net.size_pos a
  have hbK := Net.size_pos b
  unfold subnetOf Net.mem
  rw [Net.broadcast_eq a ha, Net.broadcast_eq b hb]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩ x ⟨h3, h4⟩
    exact ⟨by omega, by omega⟩
  · intro h
    have e1 := h a.addr ⟨Nat.le_refl _, by omega⟩
    have e2 := h (a.addr + (a.size - 1)) ⟨by omega, by omega⟩
    exact ⟨by omega, by omega⟩

end PyLean.Ipaddress
