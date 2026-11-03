import PyLean.Ipaddress.Model

/-!
Arithmetic vocabulary for stating `ipaddress` properties without bitwise
operations: a valid network is an aligned block of `2^(bits - prefixlen)`
addresses.
-/

namespace PyLean.Ipaddress

/-- The address families CPython implements. -/
def IsVersion (bits : Nat) : Prop := bits = 32 ∨ bits = 128

instance : DecidablePred IsVersion := fun b => inferInstanceAs (Decidable (b = 32 ∨ b = 128))

/-- What `IPvXNetwork(...)` with `strict=True` can produce. -/
def Net.Valid (n : Net) : Prop :=
  n.prefixlen ≤ n.bits ∧ n.addr < 2 ^ n.bits ∧ n.addr % 2 ^ (n.bits - n.prefixlen) = 0

instance (n : Net) : Decidable n.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Number of addresses in the block. -/
def Net.size (n : Net) : Nat := 2 ^ (n.bits - n.prefixlen)

/-- Address `x` lies in the block. -/
def Net.mem (n : Net) (x : Nat) : Bool := n.addr ≤ x && x < n.addr + n.size

/-! ## The comparisons, as propositions -/

theorem versionOf_six {b : Nat} (h : versionOf b = 6) : b = 128 := by
  unfold versionOf at h
  by_cases h1 : b = 32
  · simp [h1] at h
  · by_cases h2 : b = 128
    · exact h2
    · simp [h1, h2] at h

theorem testBit_ipIntFromPrefix_s (b p i : Nat) :
    (ipIntFromPrefix b p).testBit i = decide (i < b ∧ b ≤ p + i) := by
  simp only [ipIntFromPrefix, allOnes, Nat.testBit_xor, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < b <;> by_cases h2 : p + i < b <;> simp [h1, h2] <;> omega

/-- Distinct prefix lengths have distinct netmasks, so `int(netmask) == int(other.netmask)` compares
prefix lengths. -/
theorem ipIntFromPrefix_inj {b p q : Nat} (hp : p ≤ b) (hq : q ≤ b)
    (h : ipIntFromPrefix b p = ipIntFromPrefix b q) : p = q := by
  have key : ∀ p q, q ≤ b → p < q → ipIntFromPrefix b p ≠ ipIntFromPrefix b q := by
    intro p q hq hlt e
    have h1 := testBit_ipIntFromPrefix_s b q (b - q)
    have h2 := testBit_ipIntFromPrefix_s b p (b - q)
    rw [e, h1] at h2
    have t1 : (b - q < b ∧ b ≤ q + (b - q)) := ⟨by omega, by omega⟩
    have t2 : ¬ (b - q < b ∧ b ≤ p + (b - q)) := by omega
    rw [decide_eq_true t1, decide_eq_false t2] at h2
    cases h2
  rcases Nat.lt_trichotomy p q with hlt | heq | hlt
  · exact absurd h (key p q hq hlt)
  · exact heq
  · exact absurd h.symm (key q p hp hlt)

theorem addrLt_iff (x y : Nat) : addrLt x y = true ↔ x < y := by
  unfold addrLt
  by_cases h : x = y
  · subst h; simp
  · simp [h]

theorem addrEq_iff (bits x : Nat) (sx : Option String) (y : Nat) (sy : Option String) :
    addrEq bits x sx y sy = true ↔ x = y ∧ (versionOf bits = 6 → sx = sy) := by
  unfold addrEq
  by_cases h : x = y
  · subst h
    by_cases hv : versionOf bits = 6 <;> simp [hv]
  · simp [h]

theorem addrLe_iff (bits x : Nat) (sx : Option String) (y : Nat) (sy : Option String) :
    addrLe bits x sx y sy = true ↔ x < y ∨ (x = y ∧ (versionOf bits = 6 → sx = sy)) := by
  unfold addrLe
  rw [Bool.or_eq_true, addrLt_iff, addrEq_iff]

theorem addrGe_iff (x y : Nat) : addrGe x y = true ↔ y ≤ x := by
  unfold addrGe
  have l1 := addrLt_iff x y
  cases e : addrLt x y
  · have : ¬ x < y := fun h => by have := l1.mpr h; rw [e] at this; cases this
    constructor
    · intro _; omega
    · intro _; rfl
  · have := l1.mp e
    constructor
    · intro h; simp at h
    · intro h; omega

theorem addrGt_iff (bits x : Nat) (sx : Option String) (y : Nat) (sy : Option String) :
    addrGt bits x sx y sy = true ↔ y < x ∨ (x = y ∧ versionOf bits = 6 ∧ sx ≠ sy) := by
  unfold addrGt
  rw [Bool.and_eq_true]
  have l1 := addrLt_iff x y
  have l2 := addrEq_iff bits x sx y sy
  constructor
  · rintro ⟨h1, h2⟩
    have n1 : ¬ x < y := fun hl => by rw [l1.mpr hl] at h1; simp at h1
    have n2 : ¬ (x = y ∧ (versionOf bits = 6 → sx = sy)) := fun he => by
      rw [l2.mpr he] at h2; simp at h2
    by_cases h : x = y
    · subst h
      by_cases hv : versionOf bits = 6
      · exact Or.inr ⟨rfl, hv, fun hs => n2 ⟨rfl, fun _ => hs⟩⟩
      · exact (n2 ⟨rfl, fun hv' => absurd hv' hv⟩).elim
    · exact Or.inl (by omega)
  · intro h
    have n1 : addrLt x y = false := by
      cases e : addrLt x y
      · rfl
      · have := l1.mp e
        rcases h with h | ⟨h, -⟩ <;> omega
    have n2 : addrEq bits x sx y sy = false := by
      cases e : addrEq bits x sx y sy
      · rfl
      · obtain ⟨hxy, hs⟩ := l2.mp e
        rcases h with h | ⟨-, hv, hne⟩
        · omega
        · exact absurd (hs hv) hne
    rw [n1, n2]
    exact ⟨rfl, rfl⟩

/-- `a.subnet_of(b)`'s two comparisons (ipaddress.py:1033-1034) as propositions. -/
theorem subnetOf_iff (a b : Net) : subnetOf a b = true ↔
    (b.addr < a.addr ∨ (b.addr = a.addr ∧ (versionOf b.bits = 6 → b.scope = a.scope))) ∧
      a.broadcast ≤ b.broadcast := by
  unfold subnetOf
  rw [Bool.and_eq_true, addrLe_iff, addrGe_iff]

/-- `subnetOf` of two networks without scope ids compares the integers. -/
theorem subnetOf_none_iff (a b : Net) (ha : a.scope = none) (hb : b.scope = none) :
    subnetOf a b = true ↔ b.addr ≤ a.addr ∧ a.broadcast ≤ b.broadcast := by
  rw [subnetOf_iff, ha, hb]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases h1 with h | ⟨h, -⟩ <;> omega
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases Nat.lt_or_eq_of_le h1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, fun _ => rfl⟩

/-- Network `==` (ipaddress.py:720-726) for two networks of one family with valid prefix lengths:
equal network addresses and prefix lengths, and for IPv6 equal scope ids. -/
theorem netEq_iff (a b : Net) (hab : a.bits = b.bits) (ha : a.prefixlen ≤ a.bits)
    (hb : b.prefixlen ≤ b.bits) :
    netEq a b = true ↔
      a.addr = b.addr ∧ a.prefixlen = b.prefixlen ∧ (versionOf a.bits = 6 → a.scope = b.scope) := by
  unfold netEq Net.netmask
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, addrEq_iff, hab]
  constructor
  · rintro ⟨⟨_, h1, h2⟩, h3⟩
    exact ⟨h1, ipIntFromPrefix_inj (by omega) hb h3, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨rfl, h1, h3⟩, by rw [h2]⟩

/-- `ns` lists blocks in ascending order that together cover exactly the
addresses `lo, lo+1, ..., hi` once each (empty when `lo = hi + 1`). -/
def Tiles : List Net → Nat → Nat → Prop
  | [], lo, hi => lo = hi + 1
  | n :: ns, lo, hi => n.addr = lo ∧ Tiles ns (lo + n.size) hi

end PyLean.Ipaddress
