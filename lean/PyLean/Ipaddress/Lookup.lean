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
theorem Net.broadcast_eq (n : Net) (h : n.Valid) : n.broadcast = n.addr + (n.size - 1) := by
  unfold Net.broadcast
  rw [Net.hostmask_eq, or_two_pow_sub_one_of_mod _ _ h.2.2]
  rfl

theorem Net.size_pos (n : Net) : 0 < n.size := Nat.two_pow_pos _

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

/-- `other in net`, ipaddress.py:731-741, for every kind of `other`: an address of the network's
version is in it exactly when it is one of the block's addresses, whatever either scope id (:741
reads only `_ip`); an address of the other version and any network are not (the comment at :732,
"always false if one is v4 and the other is v6"); an object without `version` raises
`AttributeError`. -/
def ContainsMem : Prop :=
  ∀ n : Net, IsVersion n.bits → n.Valid →
    (∀ x sc, x < 2 ^ n.bits → containsOp n (.addr n.bits x sc) = .ok (n.mem x)) ∧
    (∀ b x sc, versionOf b ≠ versionOf n.bits → containsOp n (.addr b x sc) = .ok false) ∧
    (∀ m : Net, containsOp n (.net m) = .ok false) ∧
    (∀ ty, containsOp n (.other ty) =
      .error (.named "AttributeError" s!"'{ty}' object has no attribute 'version'"))

theorem containsMem_proven : ContainsMem := by
  intro n _ hn
  refine ⟨fun x sc hx => ?_, fun b x sc hb => ?_, fun m => ?_, fun ty => rfl⟩
  · simp [containsOp, contains_eq_mem n x hn hx]
  · simp [containsOp, Ne.symm hb]
  · simp only [containsOp]; split <;> rfl

theorem overlapsOp_net (a b : Net) (h : versionOf a.bits = versionOf b.bits) :
    overlapsOp a (.net b) = .ok (contains b a.addr || contains b a.broadcast ||
      contains a b.addr || contains a b.broadcast) := by
  simp only [overlapsOp, inOp, containsOp, h, ne_eq, not_true_eq_false, ↓reduceIte]
  cases contains b a.addr <;> cases contains b a.broadcast <;> cases contains a b.addr <;>
    cases contains a b.broadcast <;> rfl

/-- `a.overlaps(b)`, ipaddress.py:743-748, docstring "Tell if self is partly contained in other":
for a network `b` of the same version, true exactly when the blocks share an address; a network
of the other version never overlaps (its `__contains__` refuses the addresses); an address or an
object without `__contains__` makes the first `in` raise `TypeError`. -/
def OverlapsShareAddress : Prop :=
  ∀ a : Net, IsVersion a.bits → a.Valid →
    (∀ b : Net, b.Valid → b.bits = a.bits →
      ∃ r, overlapsOp a (.net b) = .ok r ∧ (r = true ↔ ∃ x, a.mem x = true ∧ b.mem x = true)) ∧
    (∀ b : Net, versionOf b.bits ≠ versionOf a.bits → overlapsOp a (.net b) = .ok false) ∧
    (∀ bb x sc, overlapsOp a (.addr bb x sc) =
      .error (.typeError s!"argument of type 'IPv{versionOf bb}Address' is not a container or iterable")) ∧
    (∀ ty, overlapsOp a (.other ty) =
      .error (.typeError s!"argument of type '{ty}' is not a container or iterable"))

theorem overlapsShareAddress_proven : OverlapsShareAddress := by
  intro a _ ha
  refine ⟨fun b hb hbits => ?_, fun b hv => ?_, fun bb x sc => rfl, fun ty => rfl⟩
  · refine ⟨_, overlapsOp_net a b (by rw [hbits]), ?_⟩
    have hal := Net.addr_add_size_le a ha
    have hbl := Net.addr_add_size_le b hb
    have hal' : a.addr + a.size ≤ 2 ^ b.bits := hbits ▸ hal
    have hbl' : b.addr + b.size ≤ 2 ^ a.bits := hbits.symm ▸ hbl
    have haK := Net.size_pos a
    have hbK := Net.size_pos b
    have habc := Net.broadcast_eq a ha
    have hbbc := Net.broadcast_eq b hb
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
  · simp [overlapsOp, inOp, containsOp, hv, Ne.symm hv, bind, Except.bind]

/-- `a.subnet_of(b)`, ipaddress.py:1039-1041 through `_is_subnet_of` (:1028-1037): for a network `b`
of the same version the result is `True` exactly when every address of `a` is in `b` and, for
IPv6 networks with the same network address, their scope ids are equal. `b.network_address <=
a.network_address` (:1033) is `total_ordering`'s `b < a or b == a`, and only `==` reads the scope
id (`IPv6Address.__eq__`, :2009-2015). A different version raises `TypeError` (:1031-1032); an
address of the same version or an object without `version` raises `TypeError` through the caught
`AttributeError` (:1035-1037). The docstring's "Return True if this network is a subnet of other"
without the scope condition is `SubnetOfScopeBlind`, refuted. -/
def SubnetOfMem : Prop :=
  ∀ a : Net, IsVersion a.bits → a.Valid →
    (∀ b : Net, b.Valid → b.bits = a.bits →
      ∃ r, subnetOfOp a (.net b) = .ok r ∧
        (r = true ↔ (∀ x, a.mem x = true → b.mem x = true) ∧
          (b.addr = a.addr → a.bits = 128 → b.scope = a.scope))) ∧
    (∀ b : Net, versionOf b.bits ≠ versionOf a.bits →
      subnetOfOp a (.net b) = .error (.typeError "~are not of the same version")) ∧
    (∀ bb x sc, versionOf bb ≠ versionOf a.bits →
      subnetOfOp a (.addr bb x sc) = .error (.typeError "~are not of the same version")) ∧
    (∀ x sc, subnetOfOp a (.addr a.bits x sc) =
      .error (.typeError "~Unable to test subnet containment between")) ∧
    (∀ ty, subnetOfOp a (.other ty) = .error (.typeError "~Unable to test subnet containment between"))

theorem subnetOfMem_proven : SubnetOfMem := by
  intro a _ ha
  refine ⟨fun b hb hbits => ?_, fun b hv => ?_, fun bb x sc hv => ?_, fun x sc => ?_, fun ty => rfl⟩
  · refine ⟨subnetOf a b, by simp [subnetOfOp, isSubnetOf, hbits], ?_⟩
    have haK := Net.size_pos a
    have hbK := Net.size_pos b
    rw [subnetOf_iff, Net.broadcast_eq a ha, Net.broadcast_eq b hb]
    have hmem : (∀ x, a.mem x = true → b.mem x = true) ↔
        b.addr ≤ a.addr ∧ a.addr + (a.size - 1) ≤ b.addr + (b.size - 1) := by
      unfold Net.mem
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · intro h
        have e1 := h a.addr ⟨Nat.le_refl _, by omega⟩
        have e2 := h (a.addr + (a.size - 1)) ⟨by omega, by omega⟩
        exact ⟨by omega, by omega⟩
      · rintro ⟨h1, h2⟩ x ⟨h3, h4⟩
        exact ⟨by omega, by omega⟩
    rw [hmem]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨by rcases h1 with h | ⟨h, -⟩ <;> omega, h2⟩, fun he h128 => ?_⟩
      rcases h1 with h | ⟨-, h⟩
      · omega
      · have h6 : versionOf b.bits = 6 := by simp [hbits, h128, versionOf]
        exact h h6
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨?_, h2⟩
      rcases Nat.lt_or_eq_of_le h1 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, fun hv => h3 h (by rw [← hbits]; exact versionOf_six hv)⟩
  · simp [subnetOfOp, isSubnetOf, Ne.symm hv]
  · simp [subnetOfOp, isSubnetOf, Ne.symm hv]
  · simp [subnetOfOp, isSubnetOf]

/-- `subnet_of` docstring, ipaddress.py:1040, "Return True if this network is a subnet of other",
read on addresses: a network all of whose addresses are in `b` is a subnet of `b`. Refuted:
`IPv6Network('fe80::%1/64').subnet_of(IPv6Network('fe80::/10'))` is `False`, because
`IPv6Address('fe80::') <= IPv6Address('fe80::%1')` is `False` (`__lt__` ignores the scope id,
`__eq__` does not), while `IPv6Network('fe80:0:0:1::%1/64')` is a subnet of the same network.
Upstream: gh-151769 (open), the scope-blind ordering. -/
def SubnetOfScopeBlind : Prop :=
  ∀ a b : Net, IsVersion a.bits → a.Valid → b.Valid → b.bits = a.bits →
    (∀ x, a.mem x = true → b.mem x = true) → subnetOfOp a (.net b) = .ok true

theorem subnetOfScopeBlind_refuted : ¬ SubnetOfScopeBlind := by
  intro h
  have hc := h ⟨128, 338288524927261089654018896841347694592, 64, some "1"⟩
    ⟨128, 338288524927261089654018896841347694592, 10, none⟩ (Or.inr rfl) (by decide) (by decide) rfl
    (by
      intro x hx
      have hx' : 338288524927261089654018896841347694592 ≤ x ∧
          x < 338288524927261089654018896841347694592 + 2 ^ (128 - 64) := by
        simp only [Net.mem, Net.size, Bool.and_eq_true] at hx
        exact ⟨of_decide_eq_true hx.1, of_decide_eq_true hx.2⟩
      show (decide (338288524927261089654018896841347694592 ≤ x) &&
        decide (x < 338288524927261089654018896841347694592 + 2 ^ (128 - 10))) = true
      have hp : (2 : Nat) ^ (128 - 10) = 332306998946228968225951765070086144 := by decide
      have hq : (2 : Nat) ^ (128 - 64) = 18446744073709551616 := by decide
      rw [hp]
      rw [hq] at hx'
      rw [Bool.and_eq_true]
      exact ⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩)
  exact absurd hc (by decide)

end PyLean.Ipaddress
