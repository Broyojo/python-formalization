import PyLean.Ipaddress.Mask4

/-! `summarize_address_range` with interfaces. `IPv4Interface` and `IPv6Interface` subclass the
address classes (Lib/ipaddress.py:1413, :2207), so they pass the `isinstance(_, _BaseAddress)` check
at :223, and `first > last` (:229) then runs through their own `__lt__` and `__eq__`
(:1431-1453, :2225-2247), which order by network first; the loop afterwards reads only `_ip`. -/

namespace PyLean.Ipaddress

open PyLean

/-! ## Netmasks are ordered like prefix lengths -/

theorem mask_eq_sub (bits p : Nat) (hp : p ≤ bits) :
    ipIntFromPrefix bits p = 2 ^ bits - 2 ^ (bits - p) := by
  rw [ipIntFromPrefix_eq bits p hp, Nat.shiftLeft_eq, Nat.sub_mul, ← Nat.pow_add,
    Nat.add_sub_cancel' hp, Nat.one_mul]

theorem mask_lt (bits p q : Nat) (hp : p ≤ bits) (hq : q ≤ bits) (h : p < q) :
    ipIntFromPrefix bits p < ipIntFromPrefix bits q := by
  rw [mask_eq_sub bits p hp, mask_eq_sub bits q hq]
  have h1 : 2 ^ (bits - q) < 2 ^ (bits - p) := Nat.pow_lt_pow_right (by decide) (by omega)
  have h2 : 2 ^ (bits - p) ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem mask_lt_iff (bits p q : Nat) (hp : p ≤ bits) (hq : q ≤ bits) :
    ipIntFromPrefix bits p < ipIntFromPrefix bits q ↔ p < q := by
  constructor
  · intro h
    rcases Nat.lt_or_ge p q with h' | h'
    · exact h'
    · rcases Nat.eq_or_lt_of_le h' with e | e
      · subst e; omega
      · have := mask_lt bits q p hq hp e; omega
  · exact mask_lt bits p q hp hq

theorem mask_eq_iff (bits p q : Nat) (hp : p ≤ bits) (hq : q ≤ bits) :
    ipIntFromPrefix bits p = ipIntFromPrefix bits q ↔ p = q := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy p q with e | e | e
    · have := mask_lt bits p q hp hq e; omega
    · exact e
    · have := mask_lt bits q p hq hp e; omega
  · intro h; rw [h]

/-! ## The interface order -/

/-- `_BaseNetwork.__lt__` (:708-718) for two networks of one family as a proposition: the network
addresses (`!=` reads the scope ids, `<` does not), then the prefix lengths. -/
theorem netLt_iff (bits a1 p1 a2 p2 : Nat) (s1 s2 : Option String) (h1 : p1 ≤ bits)
    (h2 : p2 ≤ bits) :
    netLt ⟨bits, a1, p1, s1⟩ ⟨bits, a2, p2, s2⟩ = true ↔
      a1 < a2 ∨ ((a1 = a2 ∧ (versionOf bits = 6 → s1 = s2)) ∧ p1 < p2) := by
  unfold netLt
  simp only [Net.netmask]
  split
  · rename_i hne
    rw [addrLt_iff]
    have hE : ¬ (a1 = a2 ∧ (versionOf bits = 6 → s1 = s2)) := by
      intro h
      rw [(addrEq_iff _ _ _ _ _).mpr h] at hne
      simp at hne
    constructor
    · exact Or.inl
    · rintro (h | ⟨h, -⟩)
      · exact h
      · exact absurd h hE
  · rename_i hne
    have hE : a1 = a2 ∧ (versionOf bits = 6 → s1 = s2) := by
      apply (addrEq_iff _ _ _ _ _).mp
      simpa using hne
    by_cases hm : ipIntFromPrefix bits p1 = ipIntFromPrefix bits p2
    · have hp : p1 = p2 := (mask_eq_iff bits p1 p2 h1 h2).mp hm
      simp only [hm, ne_eq, eq_self_iff_true, not_true_eq_false, ↓reduceIte, Bool.false_eq_true,
        false_iff]
      rintro (h | ⟨-, h⟩) <;> omega
    · simp only [hm, ne_eq, not_false_eq_true, ↓reduceIte]
      constructor
      · intro h
        have h' : ipIntFromPrefix bits p1 < ipIntFromPrefix bits p2 := of_decide_eq_true h
        exact Or.inr ⟨hE, (mask_lt_iff bits p1 p2 h1 h2).mp h'⟩
      · rintro (h | ⟨-, h⟩)
        · omega
        · exact decide_eq_true ((mask_lt_iff bits p1 p2 h1 h2).mpr h)

/-- `first < last or first == last` for two interfaces of one family whose networks have network
addresses `a1`, `a2`, prefix lengths `p1`, `p2` and scope ids `s1`, `s2`, and whose addresses are
`x`, `y` with scope ids `sx`, `sy`: lexicographic on the network address, then (network addresses
equal, scope ids included) the prefix length, then the address. -/
theorem order_core (bits a1 a2 p1 p2 x y : Nat) (s1 s2 sx sy : Option String) (h1 : p1 ≤ bits)
    (h2 : p2 ≤ bits) :
    (netLt ⟨bits, a1, p1, s1⟩ ⟨bits, a2, p2, s2⟩ ||
        (netEq ⟨bits, a1, p1, s1⟩ ⟨bits, a2, p2, s2⟩ && addrLt x y) ||
        (addrEq bits x sx y sy && netEq ⟨bits, a1, p1, s1⟩ ⟨bits, a2, p2, s2⟩)) = true ↔
      a1 < a2 ∨ ((a1 = a2 ∧ (versionOf bits = 6 → s1 = s2)) ∧
        (p1 < p2 ∨ (p1 = p2 ∧ (x < y ∨ (x = y ∧ (versionOf bits = 6 → sx = sy)))))) := by
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    netLt_iff bits a1 p1 a2 p2 s1 s2 h1 h2,
    netEq_iff ⟨bits, a1, p1, s1⟩ ⟨bits, a2, p2, s2⟩ rfl h1 h2, addrLt_iff, addrEq_iff]
  constructor
  · rintro (((h | ⟨hE, hp⟩) | ⟨⟨ha, hp, hs⟩, hxy⟩) | ⟨⟨hxy, hsx⟩, ⟨ha, hp, hs⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hE, Or.inl hp⟩
    · exact Or.inr ⟨⟨ha, hs⟩, Or.inr ⟨hp, Or.inl hxy⟩⟩
    · exact Or.inr ⟨⟨ha, hs⟩, Or.inr ⟨hp, Or.inr ⟨hxy, hsx⟩⟩⟩
  · rintro (h | ⟨hE, hp | ⟨hp, hxy | ⟨hxy, hsx⟩⟩⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨hE, hp⟩))
    · exact Or.inl (Or.inr ⟨⟨hE.1, hp, hE.2⟩, hxy⟩)
    · exact Or.inr ⟨⟨hxy, hsx⟩, ⟨hE.1, hp, hE.2⟩⟩

/-! ## `summarize_address_range` on interfaces -/

theorem summarizeOp_addr_none (bits x y : Nat) (h : x ≤ y) :
    summarizeOp (.addr bits x none) (.addr bits y none) = summarizeInts bits x y := by
  have hg : addrGt bits x none y none = false := by
    rw [Bool.eq_false_iff]
    intro e
    rcases (addrGt_iff bits x none y none).mp e with e | ⟨-, -, e⟩
    · omega
    · exact e rfl
  simp [summarizeOp, summarizeAddressRange, hg, summarizeInts]

theorem summarizeInts_gt (bits x y : Nat) (hb : IsVersion bits) (h : y < x) :
    summarizeInts bits x y = .ok [] := by
  have hv : ¬ (versionOf bits ≠ 4 ∧ versionOf bits ≠ 6) := by rcases hb with rfl | rfl <;> decide
  unfold summarizeInts
  rw [if_neg hv, show y - x + 2 = 1 + 1 by omega]
  simp [summarizeLoop, show ¬ x ≤ y by omega]

/-- `summarize_address_range` with interfaces, ipaddress.py:197-249, for every interface (prefix
length within `max_prefixlen`, the type invariant) and address of one version:

* an interface `first` and an address `last` raise `ValueError('last IP address must be greater
  than first')` whatever the two ints: `first > last` is `not first < last and first != last`
  (`total_ordering`, Lib/functools.py:89-94), the interface's `__lt__` gives `False` and `__eq__`
  gives `False` from the `AttributeError` on `last.network` (:1436-1441, :1447-1453; the comment
  at :1451-1452 says an address sorts before every interface);
* an address `first` and an interface `last`: Python tries the interface's reflected `__lt__` first
  (a proper subclass, Objects/object.c:1055-1061), which gives `False`, so `first > last` is
  `False` and the loop runs on the two ints: the summary of `int(first)..int(last)` (the result
  for two unscoped addresses, which `SummarizeExactCover` gives), and `[]` when `int(first) >
  int(last)`;
* two interfaces: `ValueError` unless `first < last or first == last` in the interfaces' order,
  which compares `first.network` and `last.network` (network address, the scope ids through
  `IPv6Address.__eq__`, then prefix length) and then the addresses (`_ip`, and for `==` the scope
  ids); otherwise the same int summary, `[]` when `int(first) > int(last)`. So
  `summarize_address_range(IPv4Interface('10.0.0.1/24'), IPv4Interface('10.0.0.5/8'))` raises and
  `(IPv4Interface('10.0.0.5/8'), IPv4Interface('10.0.0.1/24'))` returns `[]`. -/
def SummarizeInterfaces : Prop :=
  (∀ (b1 b2 x y p : Nat) (sx sy : Option String), versionOf b1 = versionOf b2 →
    summarizeOp (.iface b1 x sx p) (.addr b2 y sy) =
      .error (.valueError "last IP address must be greater than first")) ∧
  (∀ (bits x y p : Nat) (sx sy : Option String), IsVersion bits →
    summarizeOp (.addr bits x sx) (.iface bits y sy p) =
      if x ≤ y then summarizeOp (.addr bits x none) (.addr bits y none) else .ok []) ∧
  (∀ (bits x y px py : Nat) (sx sy : Option String), IsVersion bits → px ≤ bits → py ≤ bits →
    summarizeOp (.iface bits x sx px) (.iface bits y sy py) =
      if (ifaceNet bits x sx px).addr < (ifaceNet bits y sy py).addr ∨
          (((ifaceNet bits x sx px).addr = (ifaceNet bits y sy py).addr ∧
            (bits = 128 → (ifaceNet bits x sx px).scope = (ifaceNet bits y sy py).scope)) ∧
          (px < py ∨ (px = py ∧ (x < y ∨ (x = y ∧ (bits = 128 → sx = sy)))))) then
        (if x ≤ y then summarizeOp (.addr bits x none) (.addr bits y none) else .ok [])
      else .error (.valueError "last IP address must be greater than first"))

theorem summarizeInterfaces_proven : SummarizeInterfaces := by
  refine ⟨fun b1 b2 x y p sx sy h => ?_, fun bits x y p sx sy hb => ?_,
    fun bits x y px py sx sy hb hpx hpy => ?_⟩
  · simp [summarizeOp, summarizeGt, ifaceLtOp, ifaceEqOp, h]
  · have hl : summarizeOp (.addr bits x sx) (.iface bits y sy p) = summarizeInts bits x y := by
      simp [summarizeOp, summarizeGt, ifaceLtOp]
    rw [hl]
    split
    · rename_i hxy; rw [summarizeOp_addr_none bits x y hxy]
    · rename_i hxy; exact summarizeInts_gt bits x y hb (by omega)
  · have h6 : versionOf bits = 6 ↔ bits = 128 := by rcases hb with rfl | rfl <;> decide
    have hl : summarizeOp (.iface bits x sx px) (.iface bits y sy py) =
        if summarizeGt (.iface bits x sx px) (.iface bits y sy py) then
          .error (.valueError "last IP address must be greater than first")
        else summarizeInts bits x y := by
      simp only [summarizeOp, ne_eq, eq_self_iff_true, not_true_eq_false, ↓reduceIte]
    have hg : summarizeGt (.iface bits x sx px) (.iface bits y sy py) =
        !(ifaceLt bits x sx px y sy py || ifaceEq bits x sx px y sy py) := by
      simp only [summarizeGt, ifaceLtOp, ifaceEqOp, Bool.not_or]
    have hc := order_core bits (ifaceNet bits x sx px).addr (ifaceNet bits y sy py).addr px py x y
      (ifaceNet bits x sx px).scope (ifaceNet bits y sy py).scope sx sy hpx hpy
    rw [h6] at hc
    have hc' : (ifaceLt bits x sx px y sy py || ifaceEq bits x sx px y sy py) = true ↔ _ := hc
    rw [hl, hg]
    cases hb' : (ifaceLt bits x sx px y sy py || ifaceEq bits x sx px y sy py)
    · rw [if_neg (mt hc'.mpr (by simp [hb']))]
      rfl
    · rw [if_pos (hc'.mp (by simp [hb']))]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i hxy; rw [summarizeOp_addr_none bits x y hxy]
      · rename_i hxy; exact summarizeInts_gt bits x y hb (by omega)

end PyLean.Ipaddress
