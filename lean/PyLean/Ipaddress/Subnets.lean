import PyLean.Ipaddress.Spec

/-!
`subnets`, `supernet` and `address_exclude` on valid arguments.
-/

namespace PyLean.Ipaddress

open PyLean

/-- The network of prefix `k` next to the one holding address `a`: `a`'s block of prefix `k`
with the bit of weight `2**(bits - k)` flipped. -/
def sibling (bits a k : Nat) : Net :=
  let h := 2 ^ (bits - k)
  let q := a / h
  ⟨bits, (if q % 2 = 0 then q + 1 else q - 1) * h, k⟩

/-- The siblings of `a`'s blocks of prefix `p + 1, ..., p + n`, in that order. -/
def excludeTail (bits a p n : Nat) : List Net :=
  (List.range n).map fun j => sibling bits a (p + 1 + j)

namespace SubnetsAux

theorem testBit_allOnes (b i : Nat) : (allOnes b).testBit i = decide (i < b) := by
  simp [allOnes, Nat.testBit_two_pow_sub_one]

theorem testBit_ipIntFromPrefix (b p i : Nat) :
    (ipIntFromPrefix b p).testBit i = decide (i < b ∧ b ≤ p + i) := by
  simp only [ipIntFromPrefix, Nat.testBit_xor, Nat.testBit_shiftRight, testBit_allOnes]
  by_cases h1 : i < b <;> by_cases h2 : p + i < b <;> simp [h1, h2] <;> omega

theorem hostmask_eq (n : Net) : n.hostmask = 2 ^ (n.bits - n.prefixlen) - 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Net.hostmask, Net.netmask, Nat.testBit_xor, testBit_ipIntFromPrefix,
    testBit_allOnes, Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < n.bits <;> by_cases h2 : n.bits ≤ n.prefixlen + i <;> simp [h1, h2] <;> omega

theorem testBit_false_of_lt {a b i : Nat} (ha : a < 2 ^ b) (hi : b ≤ i) : a.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hi))

theorem shift_align (a k : Nat) : a >>> k <<< k = a / 2 ^ k * 2 ^ k := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

theorem and_ipIntFromPrefix {a b p : Nat} (ha : a < 2 ^ b) (hp : p ≤ b) :
    a &&& ipIntFromPrefix b p = a / 2 ^ (b - p) * 2 ^ (b - p) := by
  rw [← shift_align]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, testBit_ipIntFromPrefix, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases h1 : i < b
  · by_cases h2 : b ≤ p + i
    · have : b - p + (i - (b - p)) = i := by omega
      simp [h1, h2, this]; omega
    · simp [h1, h2]; omega
  · have : b - p + (i - (b - p)) = i ∨ ¬ (i ≥ b - p) := by omega
    rcases this with h | h
    · simp [h1, h, testBit_false_of_lt ha (by omega : b ≤ i)]
    · simp [h1, h]

theorem align_of_mod {a k : Nat} (h : a % 2 ^ k = 0) : a / 2 ^ k * 2 ^ k = a :=
  Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)

theorem broadcast_eq {n : Net} (h : n.Valid) : n.broadcast = n.addr + n.size - 1 := by
  obtain ⟨hp, ha, hm⟩ := h
  rw [Net.broadcast, hostmask_eq, Net.size]
  generalize hk : n.bits - n.prefixlen = k at hm
  have e : n.addr = (n.addr / 2 ^ k) <<< k := by
    rw [Nat.shiftLeft_eq]; exact (align_of_mod hm).symm
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [e, ← Nat.shiftLeft_add_eq_or_of_lt (i := k) (b := 2 ^ k - 1) (by omega)]
  omega


theorem add_le_of_mod {x y m : Nat} (hx : x % m = 0) (hy : y % m = 0) (h : x < y) :
    x + m ≤ y := by
  have ex := Nat.mod_add_div x m
  have ey := Nat.mod_add_div y m
  rw [hx, Nat.zero_add] at ex
  rw [hy, Nat.zero_add] at ey
  have hlt : x / m < y / m := by
    apply Nat.lt_of_not_le; intro hle
    have := Nat.mul_le_mul_left m hle
    omega
  have := Nat.mul_le_mul_left m (Nat.succ_le_of_lt hlt)
  rw [Nat.mul_succ] at this
  omega

theorem mkNet_ok {b a p : Nat} (ha : a < 2 ^ b) (hp : p ≤ b) (hm : a % 2 ^ (b - p) = 0) :
    mkNet b a p = .ok ⟨b, a, p⟩ := by
  have hpos : 0 < 2 ^ b := Nat.two_pow_pos b
  have h1 : ¬ ((a : Int) > ((allOnes b : Nat) : Int)) := by
    simp only [allOnes]; omega
  have h3 : ((p : Int) ≤ (b : Int)) := by omega
  have h0 : ¬ ((a : Int) < 0) := by omega
  have h4 : a &&& ipIntFromPrefix b p = a := by rw [and_ipIntFromPrefix ha hp, align_of_mod hm]
  simp [h0, mkNet, checkIntAddress, h1, h3, h4, bind, Except.bind, pure, Except.pure]


theorem and_ipIntFromPrefix_shift {a b p d : Nat} (ha : a < 2 ^ b) (hp : p ≤ b) :
    a &&& (ipIntFromPrefix b p <<< d) = a / 2 ^ (b - p + d) * 2 ^ (b - p + d) := by
  rw [← shift_align]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, testBit_ipIntFromPrefix, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases h1 : i < b
  · by_cases h2 : b - p + d ≤ i
    · have : b - p + d + (i - (b - p + d)) = i := by omega
      have h3 : i - d < b ∧ b ≤ p + (i - d) := by omega
      simp [h2, this, h3]; omega
    · have h3 : (decide (i ≥ d) && decide (i - d < b ∧ b ≤ p + (i - d))) = false := by
        by_cases h4 : i ≥ d <;> simp [h4] <;> omega
      have h5 : decide (i ≥ b - p + d) = false := by simp; omega
      rw [h3, h5]; simp
  · rw [testBit_false_of_lt ha (by omega : b ≤ i)]
    by_cases h2 : b - p + d ≤ i
    · have : b - p + d + (i - (b - p + d)) = i := by omega
      simp [this, testBit_false_of_lt ha (by omega : b ≤ i)]
    · simp [h2]

theorem supernet_spec (n : Net) (d : Nat) (hv : n.Valid) (h0 : 0 < n.prefixlen)
    (hd : d ≤ n.prefixlen) :
    ∃ s, supernet n d none = .ok s ∧ s.bits = n.bits ∧ s.Valid ∧
      s.prefixlen = n.prefixlen - d ∧ subnetOf n s = true := by
  obtain ⟨hp, ha, hm⟩ := hv
  have e := and_ipIntFromPrefix_shift (d := d) ha hp
  generalize hr : n.addr / 2 ^ (n.bits - n.prefixlen + d) * 2 ^ (n.bits - n.prefixlen + d) = r at e
  have hK : n.bits - (n.prefixlen - d) = n.bits - n.prefixlen + d := by omega
  have hrle : r ≤ n.addr := hr ▸ Nat.div_mul_le_self _ _
  have hrm : r % 2 ^ (n.bits - (n.prefixlen - d)) = 0 := by rw [hK, ← hr]; exact Nat.mul_mod_left _ _
  have hmk := mkNet_ok (b := n.bits) (a := r) (p := n.prefixlen - d) (by omega) (by omega) hrm
  have hpz : n.prefixlen ≠ 0 := by omega
  have hc : ((n.prefixlen : Int) - (d : Int)) = ((n.prefixlen - d : Nat) : Int) := by omega
  refine ⟨⟨n.bits, r, n.prefixlen - d⟩, ?_, rfl, ⟨by simp; omega, by simp; omega, hrm⟩, rfl, ?_⟩
  · have h6 : ¬ ((↑(n.prefixlen - d) : Int) < 0) := by omega
    have h7 : ¬ ((d : Int) < 0) := by omega
    simp [supernet, hpz, Net.netmask, e, hc, hmk, h6, h7]
  · have hv1 : n.Valid := ⟨hp, ha, hm⟩
    have hv2 : (⟨n.bits, r, n.prefixlen - d⟩ : Net).Valid := ⟨by simp; omega, by simp; omega, hrm⟩
    simp only [subnetOf, broadcast_eq hv1, broadcast_eq hv2, Net.size, hK]
    have hmod : n.addr % 2 ^ (n.bits - n.prefixlen + d) + r = n.addr := by
      rw [← hr]; have := Nat.mod_add_div n.addr (2 ^ (n.bits - n.prefixlen + d))
      rw [Nat.mul_comm] at this; omega
    have hdvd : 2 ^ (n.bits - n.prefixlen) ∣ 2 ^ (n.bits - n.prefixlen + d) :=
      Nat.pow_dvd_pow 2 (by omega)
    have h1 : n.addr % 2 ^ (n.bits - n.prefixlen + d) % 2 ^ (n.bits - n.prefixlen) = 0 := by
      rw [Nat.mod_mod_of_dvd _ hdvd]; exact hm
    have h2 : 2 ^ (n.bits - n.prefixlen + d) % 2 ^ (n.bits - n.prefixlen) = 0 :=
      Nat.mod_eq_zero_of_dvd hdvd
    have h3 := add_le_of_mod h1 h2 (Nat.mod_lt _ (Nat.two_pow_pos _))
    have := Nat.two_pow_pos (n.bits - n.prefixlen)
    simp; omega


theorem go_mapM (b q stop : Nat) (hq : q ≤ b) (hstop : stop ≤ 2 ^ b) (hs : 0 < stop) :
    ∀ (j fuel x : Nat), x % 2 ^ (b - q) = 0 → x + j * 2 ^ (b - q) = stop → j ≤ fuel →
    ∃ ns, (pyRange.go stop (2 ^ (b - q)) fuel x).mapM (fun a : Nat => mkNet b a (q : Int)) = .ok ns ∧
      ns.length = j ∧ (∀ m ∈ ns, m.bits = b ∧ m.Valid ∧ m.prefixlen = q) ∧
      Tiles ns x (stop - 1) := by
  have hpos := Nat.two_pow_pos (b - q)
  intro j
  induction j with
  | zero =>
    intro fuel x _ hx _
    refine ⟨[], ?_, rfl, by simp, ?_⟩
    · have hxs : ¬ x < stop := by omega
      cases fuel <;> simp [pyRange.go, hxs] <;> rfl
    · simp [Tiles]; omega
  | succ j ih =>
    intro fuel x hxm hx hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hlt : x < stop := by
      have : 0 < (j + 1) * 2 ^ (b - q) := Nat.mul_pos (by omega) hpos
      omega
    obtain ⟨ns, h1, h2, h3, h4⟩ := ih f (x + 2 ^ (b - q)) (by simp [Nat.add_mod_right, hxm])
      (by rw [Nat.add_mul] at hx; omega) (by omega)
    refine ⟨⟨b, x, q⟩ :: ns, ?_, by simp [h2], ?_, ?_⟩
    · simp only [pyRange.go, hlt, ↓reduceIte]
      rw [List.mapM_cons, mkNet_ok (by omega) hq hxm, h1]
      rfl
    · intro m hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ⟨rfl, ⟨hq, by simp; omega, hxm⟩, rfl⟩
      · exact h3 m hm
    · exact ⟨rfl, h4⟩

theorem subnets_spec (n : Net) (d : Nat) (hv : n.Valid) (hlt : n.prefixlen < n.bits)
    (hd : n.prefixlen + d ≤ n.bits) :
    ∃ ns, subnets n d none = .ok ns ∧ ns.length = 2 ^ d ∧
      (∀ m ∈ ns, m.bits = n.bits ∧ m.Valid ∧ m.prefixlen = n.prefixlen + d) ∧
      Tiles ns n.addr (n.addr + n.size - 1) := by
  have hv' := hv
  obtain ⟨hp, ha, hm⟩ := hv'
  have hk : n.bits - (n.prefixlen + d) + d = n.bits - n.prefixlen := by omega
  have hstep : (n.hostmask + 1) >>> d = 2 ^ (n.bits - (n.prefixlen + d)) := by
    rw [hostmask_eq, Nat.sub_add_cancel (Nat.two_pow_pos _), Nat.shiftRight_eq_div_pow, ← hk,
      Nat.pow_add, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  have hbc : n.broadcast + 1 = n.addr + 2 ^ (n.bits - n.prefixlen) := by
    rw [broadcast_eq hv, Net.size]; have := Nat.two_pow_pos (n.bits - n.prefixlen); omega
  have hstop : n.addr + 2 ^ (n.bits - n.prefixlen) ≤ 2 ^ n.bits :=
    add_le_of_mod hm (Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))) ha
  have hxm : n.addr % 2 ^ (n.bits - (n.prefixlen + d)) = 0 := by
    rw [← Nat.mod_mod_of_dvd n.addr (Nat.pow_dvd_pow 2 (by omega : n.bits - (n.prefixlen + d) ≤ n.bits - n.prefixlen)), hm]
    rfl
  obtain ⟨ns, h1, h2, h3, h4⟩ := go_mapM n.bits (n.prefixlen + d) (n.addr + 2 ^ (n.bits - n.prefixlen))
    hd hstop (by have := Nat.two_pow_pos (n.bits - n.prefixlen); omega) (2 ^ d) (2 ^ (n.bits - n.prefixlen)) n.addr
    hxm (by rw [← Nat.pow_add, Nat.add_comm d, hk]) (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨ns, ?_, h2, h3, ?_⟩
  · have hne : n.prefixlen ≠ n.bits := by omega
    have c1 : ¬ ((d : Int) < 0) := by omega
    have c2 : ¬ (((n.prefixlen + d : Nat) : Int) > (n.bits : Int)) := by omega
    have c3 : ((n.prefixlen : Int) + (d : Int)) = ((n.prefixlen + d : Nat) : Int) := by omega
    simp only [subnets, hne, c1, c2, c3, ite_false, Int.toNat_natCast, hstep, hbc, pyRange,
      Nat.add_sub_cancel_left]
    exact h1
  · have : n.addr + n.size - 1 = n.addr + 2 ^ (n.bits - n.prefixlen) - 1 := rfl
    rw [this]; exact h4


theorem halves_spec (n : Net) (hv : n.Valid) (hlt : n.prefixlen < n.bits) :
    halves n = .ok (⟨n.bits, n.addr, n.prefixlen + 1⟩,
      ⟨n.bits, n.addr + 2 ^ (n.bits - (n.prefixlen + 1)), n.prefixlen + 1⟩) ∧
    (⟨n.bits, n.addr, n.prefixlen + 1⟩ : Net).Valid ∧
    (⟨n.bits, n.addr + 2 ^ (n.bits - (n.prefixlen + 1)), n.prefixlen + 1⟩ : Net).Valid := by
  obtain ⟨ns, h1, h2, h3, h4⟩ := subnets_spec n 1 hv hlt (by omega)
  have h1' : subnets n 1 none = .ok ns := by simpa using h1
  match ns, h2 with
  | [m1, m2], _ =>
    obtain ⟨b1, v1, p1⟩ := h3 m1 (by simp)
    obtain ⟨b2, v2, p2⟩ := h3 m2 (by simp)
    obtain ⟨a1, a2, _⟩ := h4
    have e1 : m1 = ⟨n.bits, n.addr, n.prefixlen + 1⟩ := by
      cases m1; simp_all
    have e2 : m2 = ⟨n.bits, n.addr + 2 ^ (n.bits - (n.prefixlen + 1)), n.prefixlen + 1⟩ := by
      subst e1; cases m2; simp_all [Net.size]
    subst e1 e2
    refine ⟨?_, v1, v2⟩
    simp [halves, h1', bind, Except.bind, pure, Except.pure]

theorem excludeLoop_spec (o : Net) (ho : o.Valid) :
    ∀ (fuel : Nat) (B : Net), B.Valid → B.bits = o.bits → B.prefixlen < o.prefixlen →
      B.addr ≤ o.addr → o.addr + o.size ≤ B.addr + B.size →
      o.prefixlen - B.prefixlen ≤ fuel →
      ∃ out, excludeLoop o fuel ⟨B.bits, B.addr, B.prefixlen + 1⟩
          ⟨B.bits, B.addr + 2 ^ (B.bits - (B.prefixlen + 1)), B.prefixlen + 1⟩ = .ok out ∧
        (∀ m ∈ out, m.bits = B.bits ∧ m.Valid) ∧
        ∀ x, out.countP (fun m => m.mem x) = if B.mem x && !o.mem x then 1 else 0 := by
  intro fuel
  induction fuel with
  | zero => intro B _ _ hp _ _ hf; omega
  | succ fuel ih =>
    intro B hB hbits hp hlo hhi hf
    have hov := ho
    obtain ⟨hop, hoa, hom⟩ := ho
    obtain ⟨hBp, hBa, hBm⟩ := hB
    have hBlt : B.prefixlen < B.bits := by omega
    obtain ⟨_, v1, v2⟩ := halves_spec B ⟨hBp, hBa, hBm⟩ hBlt
    have hsz : ∀ x, B.mem x = (decide (B.addr ≤ x) && decide (x < B.addr + 2 ^ (B.bits - B.prefixlen))) := fun _ => rfl
    have osz : ∀ x, o.mem x = (decide (o.addr ≤ x) && decide (x < o.addr + 2 ^ (o.bits - o.prefixlen))) := fun _ => rfl
    -- sizes
    have hK : 2 ^ (B.bits - B.prefixlen) = 2 * 2 ^ (B.bits - (B.prefixlen + 1)) := by
      rw [show B.bits - B.prefixlen = (B.bits - (B.prefixlen + 1)) + 1 by omega, Nat.pow_succ]
      omega
    have hdk : 2 ^ (o.bits - o.prefixlen) ∣ 2 ^ (B.bits - (B.prefixlen + 1)) :=
      Nat.pow_dvd_pow 2 (by omega)
    have hdK : 2 ^ (B.bits - (B.prefixlen + 1)) ∣ 2 ^ (B.bits - B.prefixlen) :=
      Nat.pow_dvd_pow 2 (by omega)
    simp only [Net.size] at hhi
    rw [hK] at hhi hsz
    have hBo : B.addr % 2 ^ (o.bits - o.prefixlen) = 0 := by
      have := Nat.mod_mod_of_dvd B.addr (Nat.dvd_trans hdk hdK); rw [hBm] at this
      rw [← this]; exact Nat.zero_mod _
    generalize hh : 2 ^ (B.bits - (B.prefixlen + 1)) = h at hdk hdK hK v2 hhi hsz ⊢
    generalize hso : 2 ^ (o.bits - o.prefixlen) = so at hdk hom hhi osz hBo
    have hhpos : 0 < h := hh ▸ Nat.two_pow_pos _
    have hsopos : 0 < so := hso ▸ Nat.two_pow_pos _
    have hhso : h % so = 0 := Nat.mod_eq_zero_of_dvd hdk
    by_cases hc : o.addr < B.addr + h
    · have hin : o.addr + so ≤ B.addr + h :=
        add_le_of_mod hom (by rw [Nat.add_mod, hBo, hhso]; simp) hc
      by_cases heq : o.prefixlen = B.prefixlen + 1
      · have hso_h : so = h := by rw [← hso, ← hh, hbits, heq]
        have hs1 : (⟨B.bits, B.addr, B.prefixlen + 1⟩ : Net) = o := by
          cases o; simp only [Net.mk.injEq] at *; omega
        refine ⟨[⟨B.bits, B.addr + h, B.prefixlen + 1⟩], ?_, ?_, ?_⟩
        · simp [excludeLoop, hs1]
        · intro m hm; simp at hm; subst hm; exact ⟨rfl, v2⟩
        · intro x
          simp only [List.countP_cons, List.countP_nil, Net.mem, Net.size, hh, hK, hso,
            Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
            decide_eq_false_iff_not]
          repeat' split
          all_goals omega
      · have hs1 : ¬ ((⟨B.bits, B.addr, B.prefixlen + 1⟩ : Net) = o) := by
          intro e; rw [← e] at heq; exact heq rfl
        have hs2 : ¬ ((⟨B.bits, B.addr + h, B.prefixlen + 1⟩ : Net) = o) := by
          intro e; rw [← e] at heq; exact heq rfl
        have hsub : subnetOf o ⟨B.bits, B.addr, B.prefixlen + 1⟩ = true := by
          simp only [subnetOf, broadcast_eq hov, broadcast_eq v1, Net.size, hh, hso]
          simp; omega
        obtain ⟨hhv, -, -⟩ := halves_spec _ v1 (by simp; omega)
        obtain ⟨out, h1, h2, h3⟩ := ih ⟨B.bits, B.addr, B.prefixlen + 1⟩ v1 hbits
          (by simp; omega) hlo (by simp only [Net.size, hh, hso]; omega) (by simp; omega)
        refine ⟨⟨B.bits, B.addr + h, B.prefixlen + 1⟩ :: out, ?_, ?_, ?_⟩
        · simp only [excludeLoop, hs1, hs2, hsub, hhv]
          simp only at h1
          simp [h1, hs1, hs2, bind, Except.bind, pure, Except.pure]
        · intro m hm
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact ⟨rfl, v2⟩
          · exact h2 m hm
        · intro x
          rw [List.countP_cons, h3 x]
          simp only [Net.mem, Net.size, hh, hK, hso,
            Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
            decide_eq_false_iff_not]
          repeat' split
          all_goals omega
    · by_cases heq : o.prefixlen = B.prefixlen + 1
      · have hso_h : so = h := by rw [← hso, ← hh, hbits, heq]
        have hs2 : (⟨B.bits, B.addr + h, B.prefixlen + 1⟩ : Net) = o := by
          cases o; simp only [Net.mk.injEq] at *; omega
        have hs1 : ¬ ((⟨B.bits, B.addr, B.prefixlen + 1⟩ : Net) = o) := by
          intro e; rw [← hs2] at e; simp at e; omega
        refine ⟨[⟨B.bits, B.addr, B.prefixlen + 1⟩], ?_, ?_, ?_⟩
        · simp [excludeLoop, hs1, hs2]
        · intro m hm; simp at hm; subst hm; exact ⟨rfl, v1⟩
        · intro x
          simp only [List.countP_cons, List.countP_nil, Net.mem, Net.size, hh, hK, hso,
            Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
            decide_eq_false_iff_not]
          repeat' split
          all_goals omega
      · have hs1 : ¬ ((⟨B.bits, B.addr, B.prefixlen + 1⟩ : Net) = o) := by
          intro e; rw [← e] at heq; exact heq rfl
        have hs2 : ¬ ((⟨B.bits, B.addr + h, B.prefixlen + 1⟩ : Net) = o) := by
          intro e; rw [← e] at heq; exact heq rfl
        have hnsub : subnetOf o ⟨B.bits, B.addr, B.prefixlen + 1⟩ = false := by
          simp only [subnetOf, broadcast_eq hov, broadcast_eq v1, Net.size, hh, hso]
          simp; omega
        have hsub : subnetOf o ⟨B.bits, B.addr + h, B.prefixlen + 1⟩ = true := by
          simp only [subnetOf, broadcast_eq hov, broadcast_eq v2, Net.size, hh, hso]
          simp; omega
        obtain ⟨hhv, -, -⟩ := halves_spec _ v2 (by simp; omega)
        obtain ⟨out, h1, h2, h3⟩ := ih ⟨B.bits, B.addr + h, B.prefixlen + 1⟩ v2 hbits
          (by simp; omega) (by simp; omega) (by simp only [Net.size, hh, hso]; omega)
          (by simp; omega)
        refine ⟨⟨B.bits, B.addr, B.prefixlen + 1⟩ :: out, ?_, ?_, ?_⟩
        · simp only [excludeLoop, hs1, hs2, hsub, hnsub, hhv]
          simp only at h1
          simp [h1, hs1, hs2, bind, Except.bind, pure, Except.pure]
        · intro m hm
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact ⟨rfl, v1⟩
          · exact h2 m hm
        · intro x
          rw [List.countP_cons, h3 x]
          simp only [Net.mem, Net.size, hh, hK, hso,
            Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
            decide_eq_false_iff_not]
          repeat' split
          all_goals omega


theorem sibling_lo {bits bits' x A h k : Nat} (hb : bits = bits') (hh : 2 ^ (bits - k) = h)
    (hpos : 0 < h) (hA : A % (2 * h) = 0) (h1 : A ≤ x) (h2 : x < A + h) :
    sibling bits x k = ⟨bits', A + h, k⟩ := by
  subst hb
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hA
  have ec : A = 2 * (c * h) := by rw [hc, Nat.mul_assoc, Nat.mul_comm h c]
  have hq : x / h = 2 * c := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_assoc]; omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]; omega
  have hev : 2 * c % 2 = 0 := Nat.mul_mod_right 2 c
  show (⟨bits, (if x / 2 ^ (bits - k) % 2 = 0 then x / 2 ^ (bits - k) + 1
    else x / 2 ^ (bits - k) - 1) * 2 ^ (bits - k), k⟩ : Net) = _
  rw [hh, hq]
  simp only [hev, ↓reduceIte, Net.mk.injEq, and_true, true_and]
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]; omega

theorem sibling_hi {bits bits' x A h k : Nat} (hb : bits = bits') (hh : 2 ^ (bits - k) = h)
    (hpos : 0 < h) (hA : A % (2 * h) = 0) (h1 : A + h ≤ x) (h2 : x < A + 2 * h) :
    sibling bits x k = ⟨bits', A, k⟩ := by
  subst hb
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hA
  have ec : A = 2 * (c * h) := by rw [hc, Nat.mul_assoc, Nat.mul_comm h c]
  have hq : x / h = 2 * c + 1 := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]; omega
    · rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]; omega
  have hodd : (2 * c + 1) % 2 = 1 := by omega
  have hne : ¬ ((2 * c + 1) % 2 = 0) := by omega
  show (⟨bits, (if x / 2 ^ (bits - k) % 2 = 0 then x / 2 ^ (bits - k) + 1
    else x / 2 ^ (bits - k) - 1) * 2 ^ (bits - k), k⟩ : Net) = _
  rw [hh, hq]
  simp only [hne, ↓reduceIte, Nat.add_sub_cancel, Net.mk.injEq, and_true, true_and]
  rw [Nat.mul_assoc]; omega

theorem excludeTail_succ (bits a p n : Nat) :
    excludeTail bits a p (n + 1) = sibling bits a (p + 1) :: excludeTail bits a (p + 1) n := by
  unfold excludeTail
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  congr 1
  omega

theorem excludeLoop_exact (o : Net) (ho : o.Valid) :
    ∀ (fuel : Nat) (B : Net), B.Valid → B.bits = o.bits → B.prefixlen < o.prefixlen →
      B.addr ≤ o.addr → o.addr + o.size ≤ B.addr + B.size →
      o.prefixlen - B.prefixlen ≤ fuel →
      excludeLoop o fuel ⟨B.bits, B.addr, B.prefixlen + 1⟩
          ⟨B.bits, B.addr + 2 ^ (B.bits - (B.prefixlen + 1)), B.prefixlen + 1⟩ =
        .ok (excludeTail o.bits o.addr B.prefixlen (o.prefixlen - B.prefixlen)) := by
  intro fuel
  induction fuel with
  | zero => intro B _ _ hp _ _ hf; omega
  | succ fuel ih =>
    intro B hB hbits hp hlo hhi hf
    have hov := ho
    obtain ⟨hop, hoa, hom⟩ := ho
    obtain ⟨hBp, hBa, hBm⟩ := hB
    have hBlt : B.prefixlen < B.bits := by omega
    obtain ⟨_, v1, v2⟩ := halves_spec B ⟨hBp, hBa, hBm⟩ hBlt
    have hK : 2 ^ (B.bits - B.prefixlen) = 2 * 2 ^ (B.bits - (B.prefixlen + 1)) := by
      rw [show B.bits - B.prefixlen = (B.bits - (B.prefixlen + 1)) + 1 by omega, Nat.pow_succ]
      omega
    have hdk : 2 ^ (o.bits - o.prefixlen) ∣ 2 ^ (B.bits - (B.prefixlen + 1)) :=
      Nat.pow_dvd_pow 2 (by omega)
    have hdK : 2 ^ (B.bits - (B.prefixlen + 1)) ∣ 2 ^ (B.bits - B.prefixlen) :=
      Nat.pow_dvd_pow 2 (by omega)
    simp only [Net.size] at hhi
    rw [hK] at hhi
    have hBo : B.addr % 2 ^ (o.bits - o.prefixlen) = 0 := by
      have := Nat.mod_mod_of_dvd B.addr (Nat.dvd_trans hdk hdK); rw [hBm] at this
      rw [← this]; exact Nat.zero_mod _
    rw [hK] at hBm
    have hh' : 2 ^ (o.bits - (B.prefixlen + 1)) = 2 ^ (B.bits - (B.prefixlen + 1)) := by rw [hbits]
    generalize hh : 2 ^ (B.bits - (B.prefixlen + 1)) = h at hdk hdK hK v2 hhi hBm hh' ⊢
    generalize hso : 2 ^ (o.bits - o.prefixlen) = so at hdk hom hhi hBo
    have hhpos : 0 < h := hh ▸ Nat.two_pow_pos _
    have hsopos : 0 < so := hso ▸ Nat.two_pow_pos _
    have hhso : h % so = 0 := Nat.mod_eq_zero_of_dvd hdk
    rw [show o.prefixlen - B.prefixlen = (o.prefixlen - (B.prefixlen + 1)) + 1 by omega,
      excludeTail_succ]
    by_cases hc : o.addr < B.addr + h
    · have hin : o.addr + so ≤ B.addr + h :=
        add_le_of_mod hom (by rw [Nat.add_mod, hBo, hhso]; simp) hc
      rw [sibling_lo hbits.symm hh' hhpos hBm hlo hc]
      by_cases heq : o.prefixlen = B.prefixlen + 1
      · have hso_h : so = h := by rw [← hso, ← hh, hbits, heq]
        have hs1 : (⟨B.bits, B.addr, B.prefixlen + 1⟩ : Net) = o := by
          cases o; simp only [Net.mk.injEq] at *; omega
        have hz : o.prefixlen - (B.prefixlen + 1) = 0 := by omega
        rw [hz]
        simp [excludeLoop, hs1, excludeTail]
      · have hs1 : ¬ ((⟨B.bits, B.addr, B.prefixlen + 1⟩ : Net) = o) := by
          intro e; rw [← e] at heq; exact heq rfl
        have hs2 : ¬ ((⟨B.bits, B.addr + h, B.prefixlen + 1⟩ : Net) = o) := by
          intro e; rw [← e] at heq; exact heq rfl
        have hsub : subnetOf o ⟨B.bits, B.addr, B.prefixlen + 1⟩ = true := by
          simp only [subnetOf, broadcast_eq hov, broadcast_eq v1, Net.size, hh, hso]
          simp; omega
        obtain ⟨hhv, -, -⟩ := halves_spec _ v1 (by simp; omega)
        have h1 := ih ⟨B.bits, B.addr, B.prefixlen + 1⟩ v1 hbits
          (by simp; omega) hlo (by simp only [Net.size, hh, hso]; omega) (by simp; omega)
        simp only [excludeLoop, hs1, hs2, hsub, hhv]
        simp only at h1
        simp [h1, hs1, hs2, bind, Except.bind, pure, Except.pure]
    · rw [sibling_hi hbits.symm hh' hhpos hBm (by omega) (by omega)]
      by_cases heq : o.prefixlen = B.prefixlen + 1
      · have hso_h : so = h := by rw [← hso, ← hh, hbits, heq]
        have hs2 : (⟨B.bits, B.addr + h, B.prefixlen + 1⟩ : Net) = o := by
          cases o; simp only [Net.mk.injEq] at *; omega
        have hs1 : ¬ ((⟨B.bits, B.addr, B.prefixlen + 1⟩ : Net) = o) := by
          intro e; rw [← hs2] at e; simp at e; omega
        have hz : o.prefixlen - (B.prefixlen + 1) = 0 := by omega
        rw [hz]
        simp [excludeLoop, hs1, hs2, excludeTail]
      · have hs1 : ¬ ((⟨B.bits, B.addr, B.prefixlen + 1⟩ : Net) = o) := by
          intro e; rw [← e] at heq; exact heq rfl
        have hs2 : ¬ ((⟨B.bits, B.addr + h, B.prefixlen + 1⟩ : Net) = o) := by
          intro e; rw [← e] at heq; exact heq rfl
        have hnsub : subnetOf o ⟨B.bits, B.addr, B.prefixlen + 1⟩ = false := by
          simp only [subnetOf, broadcast_eq hov, broadcast_eq v1, Net.size, hh, hso]
          simp; omega
        have hsub : subnetOf o ⟨B.bits, B.addr + h, B.prefixlen + 1⟩ = true := by
          simp only [subnetOf, broadcast_eq hov, broadcast_eq v2, Net.size, hh, hso]
          simp; omega
        obtain ⟨hhv, -, -⟩ := halves_spec _ v2 (by simp; omega)
        have h1 := ih ⟨B.bits, B.addr + h, B.prefixlen + 1⟩ v2 hbits
          (by simp; omega) (by simp; omega) (by simp only [Net.size, hh, hso]; omega)
          (by simp; omega)
        simp only [excludeLoop, hs1, hs2, hsub, hnsub, hhv]
        simp only at h1
        simp [h1, hs1, hs2, bind, Except.bind, pure, Except.pure]

theorem addressExclude_spec (s o : Net) (hs : s.Valid) (ho : o.Valid) (hb : o.bits = s.bits)
    (hsub : subnetOf o s = true) :
    ∃ out, addressExclude s o = .ok out ∧
      (∀ m ∈ out, m.bits = s.bits ∧ m.Valid) ∧
      ∀ x, out.countP (fun m => m.mem x) = if s.mem x && !o.mem x then 1 else 0 := by
  by_cases he : o = s
  · subst he
    refine ⟨[], ?_, by simp, ?_⟩
    · simp [addressExclude, hsub]; rfl
    · intro x; simp
  · have hsub' := hsub
    simp only [subnetOf, broadcast_eq hs, broadcast_eq ho, Bool.and_eq_true, decide_eq_true_eq] at hsub'
    obtain ⟨hlo, hhi⟩ := hsub'
    have p1 := Nat.two_pow_pos (o.bits - o.prefixlen)
    have p2 := Nat.two_pow_pos (s.bits - s.prefixlen)
    have hhi' : o.addr + o.size ≤ s.addr + s.size := by
      simp only [Net.size] at hhi ⊢; omega
    have hp : s.prefixlen < o.prefixlen := by
      apply Nat.lt_of_not_le; intro hle
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · have := Nat.pow_lt_pow_right (a := 2) (by decide)
          (by obtain ⟨_, _, _⟩ := ho; obtain ⟨_, _, _⟩ := hs; omega :
            s.bits - s.prefixlen < o.bits - o.prefixlen)
        simp only [Net.size] at hhi'; omega
      · apply he
        have : o.size = s.size := by simp only [Net.size, hb, heq]
        cases o; cases s; simp only [Net.mk.injEq] at *; simp only [Net.size] at *
        refine ⟨hb, ?_, heq⟩; omega
    have hslt : s.prefixlen < s.bits := by obtain ⟨_, _, _⟩ := ho; omega
    obtain ⟨hhv, -, -⟩ := halves_spec s hs hslt
    obtain ⟨out, h1, h2, h3⟩ := excludeLoop_spec o ho (s.bits + 1) s hs hb.symm hp hlo hhi'
      (by obtain ⟨_, _, _⟩ := ho; omega)
    refine ⟨out, ?_, h2, h3⟩
    simp [addressExclude, hsub, he, hhv, h1, bind, Except.bind]

end SubnetsAux

/-- `subnets` docstring, ipaddress.py:922-948: with a valid `prefixlen_diff`
the result is the `2^prefixlen_diff` subnets of the new prefix length that
"join to make the current subnet", in ascending order. -/
def SubnetsPartition : Prop :=
  ∀ (n : Net) (d : Nat), IsVersion n.bits → n.Valid → n.prefixlen < n.bits →
    n.prefixlen + d ≤ n.bits →
    ∃ ns, subnets n d none = .ok ns ∧ ns.length = 2 ^ d ∧
      (∀ m ∈ ns, m.bits = n.bits ∧ m.Valid ∧ m.prefixlen = n.prefixlen + d) ∧
      Tiles ns n.addr (n.addr + n.size - 1)

theorem subnetsPartition_proven : SubnetsPartition :=
  fun n d _ hv hlt hd => SubnetsAux.subnets_spec n d hv hlt hd

/-- `supernet` docstring, ipaddress.py:975-995: for `0 <= d <= prefixlen` the
result is the unique valid network of prefix length `prefixlen - d` that
contains `self`. -/
def SupernetContains : Prop :=
  ∀ (n : Net) (d : Nat), IsVersion n.bits → n.Valid → 0 < n.prefixlen → d ≤ n.prefixlen →
    ∃ s, supernet n d none = .ok s ∧ s.bits = n.bits ∧ s.Valid ∧
      s.prefixlen = n.prefixlen - d ∧ subnetOf n s = true

theorem supernetContains_proven : SupernetContains :=
  fun n d _ hv h0 hd => SubnetsAux.supernet_spec n d hv h0 hd

/-- `address_exclude` docstring, ipaddress.py:789-822, and its doctest in
`Doc/library/ipaddress.rst` (`192.0.2.0/28` minus `192.0.2.1/32` is `192.0.2.8/29, 192.0.2.4/30,
192.0.2.2/31, 192.0.2.0/32`): for a network `o` of the same version inside `s`, the result is,
for each prefix length from `s.prefixlen + 1` to `o.prefixlen` in that order, the block of that
length next to the one holding `o`; these blocks and `o` cover `s` once. An `o` outside `s` raises
`ValueError` (:831-832); a network or address of the other version raises `TypeError` (:824-826),
an address of the same version raises `TypeError` (:828-829), and an object without `version`
raises `AttributeError` at `other.version`. -/
def AddressExcludePartition : Prop :=
  ∀ s : Net, IsVersion s.bits → s.Valid →
    (∀ o : Net, o.Valid → o.bits = s.bits → subnetOf o s = true →
      addressExcludeOp s (.net o) = .ok (excludeTail s.bits o.addr s.prefixlen (o.prefixlen - s.prefixlen)) ∧
      ∀ x, (excludeTail s.bits o.addr s.prefixlen (o.prefixlen - s.prefixlen)).countP (fun m => m.mem x) =
        if s.mem x && !o.mem x then 1 else 0) ∧
    (∀ o : Net, o.bits = s.bits → subnetOf o s = false →
      addressExcludeOp s (.net o) = .error (.valueError "~not contained in")) ∧
    (∀ o : Net, versionOf o.bits ≠ versionOf s.bits →
      addressExcludeOp s (.net o) = .error (.typeError "~are not of the same version")) ∧
    (∀ b x, versionOf b ≠ versionOf s.bits →
      addressExcludeOp s (.addr b x) = .error (.typeError "~are not of the same version")) ∧
    (∀ x, addressExcludeOp s (.addr s.bits x) = .error (.typeError "~is not a network object")) ∧
    (∀ ty, addressExcludeOp s (.other ty) =
      .error (.named "AttributeError" s!"'{ty}' object has no attribute 'version'"))

theorem addressExclude_exact (s o : Net) (hs : s.Valid) (ho : o.Valid) (hb : o.bits = s.bits)
    (hsub : subnetOf o s = true) :
    addressExclude s o = .ok (excludeTail s.bits o.addr s.prefixlen (o.prefixlen - s.prefixlen)) := by
  by_cases he : o = s
  · subst he
    simp [addressExclude, hsub, excludeTail]; rfl
  · have hsub' := hsub
    simp only [subnetOf, SubnetsAux.broadcast_eq hs, SubnetsAux.broadcast_eq ho, Bool.and_eq_true,
      decide_eq_true_eq] at hsub'
    obtain ⟨hlo, hhi⟩ := hsub'
    have p1 := Nat.two_pow_pos (o.bits - o.prefixlen)
    have p2 := Nat.two_pow_pos (s.bits - s.prefixlen)
    have hhi' : o.addr + o.size ≤ s.addr + s.size := by
      simp only [Net.size] at hhi ⊢; omega
    have hp : s.prefixlen < o.prefixlen := by
      apply Nat.lt_of_not_le; intro hle
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · have := Nat.pow_lt_pow_right (a := 2) (by decide)
          (by obtain ⟨_, _, _⟩ := ho; obtain ⟨_, _, _⟩ := hs; omega :
            s.bits - s.prefixlen < o.bits - o.prefixlen)
        simp only [Net.size] at hhi'; omega
      · apply he
        cases o; cases s; simp only [Net.mk.injEq] at *; simp only [Net.size] at *
        refine ⟨hb, ?_, heq⟩
        rw [hb, heq] at hhi'; omega
    have hslt : s.prefixlen < s.bits := by obtain ⟨_, _, _⟩ := ho; omega
    obtain ⟨hhv, -, -⟩ := SubnetsAux.halves_spec s hs hslt
    have h1 := SubnetsAux.excludeLoop_exact o ho (s.bits + 1) s hs hb.symm hp hlo hhi'
      (by obtain ⟨_, _, _⟩ := ho; omega)
    rw [hb] at h1
    simp [addressExclude, hsub, he, hhv, h1, bind, Except.bind]

theorem addressExcludePartition_proven : AddressExcludePartition := by
  intro s _ hs
  refine ⟨fun o ho hb hsub => ?_, fun o hb hsub => ?_, fun o hv => ?_, fun b x hv => ?_,
    fun x => ?_, fun ty => rfl⟩
  · have hv : versionOf s.bits = versionOf o.bits := by rw [hb]
    have hx := addressExclude_exact s o hs ho hb hsub
    obtain ⟨out, h1, -, h3⟩ := SubnetsAux.addressExclude_spec s o hs ho hb hsub
    rw [hx] at h1
    cases h1
    refine ⟨?_, h3⟩
    simp [addressExcludeOp, hv, hx]
  · have hv : versionOf s.bits = versionOf o.bits := by rw [hb]
    simp [addressExcludeOp, hv, addressExclude, hsub, bind, Except.bind] <;> rfl
  · simp [addressExcludeOp, Ne.symm hv]
  · simp [addressExcludeOp, Ne.symm hv]
  · simp [addressExcludeOp]

/-- The argument checks of `subnets`, ipaddress.py:921-972, as the docstring lists them (:940-946):
a network of one address yields itself whatever the arguments (:949-951, the documented
"yield an iterator with just ourself"); otherwise `new_prefix` shorter than the prefix,
`new_prefix` with a `prefixlen_diff` other than 1, a negative `prefixlen_diff` and a new prefix
past `max_prefixlen` each raise `ValueError` with the source's message, and `new_prefix=k` is
`prefixlen_diff=k - prefixlen` (:957), whose result `SubnetsPartition` gives. -/
def SubnetsArgs : Prop :=
  ∀ n : Net, IsVersion n.bits → n.Valid →
    (n.prefixlen = n.bits → ∀ d np, subnets n d np = .ok [n]) ∧
    (n.prefixlen < n.bits →
      (∀ k d : Int, k < n.prefixlen → subnets n d (some k) = .error (.valueError "new prefix must be longer")) ∧
      (∀ k d : Int, n.prefixlen ≤ k → d ≠ 1 →
        subnets n d (some k) = .error (.valueError "cannot set prefixlen_diff and new_prefix")) ∧
      (∀ k : Int, n.prefixlen ≤ k → subnets n 1 (some k) = subnets n (k - n.prefixlen) none) ∧
      (∀ d : Int, d < 0 → subnets n d none = .error (.valueError "prefix length diff must be > 0")) ∧
      (∀ d : Int, 0 ≤ d → (n.bits : Int) < n.prefixlen + d →
        subnets n d none = .error (.valueError "~prefix length diff is invalid for netblock")))

theorem subnetsArgs_proven : SubnetsArgs := by
  intro n _ _
  refine ⟨fun h d np => by simp [subnets, h]; rfl, fun hlt => ?_⟩
  have hne : n.prefixlen ≠ n.bits := by omega
  refine ⟨fun k d hk => ?_, fun k d hk hd => ?_, fun k hk => ?_, fun d hd => ?_, fun d hd hb => ?_⟩
  · simp [subnets, hne, hk] <;> rfl
  · have : ¬ k < n.prefixlen := by omega
    simp [subnets, hne, this, hd] <;> rfl
  · have : ¬ k < n.prefixlen := by omega
    simp [subnets, hne, this] <;> rfl
  · simp [subnets, hne, hd] <;> rfl
  · have : ¬ d < 0 := by omega
    simp [subnets, hne, this, hb] <;> rfl

/-- The argument checks of `supernet`, ipaddress.py:974-1013, as the docstring lists them
(:987-994): a `/0` network returns itself whatever the arguments (:996-997); otherwise
`new_prefix` longer than the prefix and `new_prefix` with a `prefixlen_diff` other than 1 raise
`ValueError`, `new_prefix=k` is `prefixlen_diff=prefixlen - k` (:1004), a `prefixlen_diff` past the
prefix length raises `ValueError` naming both (:1006-1010), and a negative one raises `ValueError`
from the shift `int(self.netmask) << prefixlen_diff` (:1011-1012). With `SupernetContains`
(`0 <= prefixlen_diff <= prefixlen`) every argument is covered. -/
def SupernetArgs : Prop :=
  ∀ n : Net, IsVersion n.bits → n.Valid →
    (n.prefixlen = 0 → ∀ d np, supernet n d np = .ok n) ∧
    (0 < n.prefixlen →
      (∀ k d : Int, n.prefixlen < k → supernet n d (some k) = .error (.valueError "new prefix must be shorter")) ∧
      (∀ k d : Int, k ≤ n.prefixlen → d ≠ 1 →
        supernet n d (some k) = .error (.valueError "cannot set prefixlen_diff and new_prefix")) ∧
      (∀ k : Int, k ≤ n.prefixlen → supernet n 1 (some k) = supernet n (n.prefixlen - k) none) ∧
      (∀ d : Int, n.prefixlen < d → supernet n d none =
        .error (.valueError s!"current prefixlen is {n.prefixlen}, cannot have a prefixlen_diff of {d}")) ∧
      (∀ d : Int, d < 0 → supernet n d none = .error (.valueError "negative shift count")))

theorem supernetArgs_proven : SupernetArgs := by
  intro n _ _
  refine ⟨fun h d np => by simp [supernet, h]; rfl, fun hlt => ?_⟩
  have hne : n.prefixlen ≠ 0 := by omega
  refine ⟨fun k d hk => ?_, fun k d hk hd => ?_, fun k hk => ?_, fun d hd => ?_, fun d hd => ?_⟩
  · simp [supernet, hne, hk] <;> rfl
  · have : ¬ n.prefixlen < k := by omega
    simp [supernet, hne, this, hd] <;> rfl
  · have : ¬ n.prefixlen < k := by omega
    simp [supernet, hne, this] <;> rfl
  · have : (n.prefixlen : Int) - d < 0 := by omega
    simp [supernet, hne, this] <;> rfl
  · have : ¬ ((n.prefixlen : Int) - d < 0) := by omega
    simp [supernet, hne, this, hd] <;> rfl

end PyLean.Ipaddress
