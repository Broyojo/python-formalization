import PyLean.Ipaddress.Spec

/-!
`subnets`, `supernet` and `address_exclude` on valid arguments.
-/

namespace PyLean.Ipaddress

open PyLean

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

/-- `subnets` docstring, ipaddress.py:925-951: with a valid `prefixlen_diff`
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

/-- `supernet` docstring, ipaddress.py:978-998: for `0 <= d <= prefixlen` the
result is the unique valid network of prefix length `prefixlen - d` that
contains `self`. -/
def SupernetContains : Prop :=
  ∀ (n : Net) (d : Nat), IsVersion n.bits → n.Valid → 0 < n.prefixlen → d ≤ n.prefixlen →
    ∃ s, supernet n d none = .ok s ∧ s.bits = n.bits ∧ s.Valid ∧
      s.prefixlen = n.prefixlen - d ∧ subnetOf n s = true

theorem supernetContains_proven : SupernetContains :=
  fun n d _ hv h0 hd => SubnetsAux.supernet_spec n d hv h0 hd

/-- `address_exclude` docstring, ipaddress.py:792-825: for `other` a subnet of
`self`, the result is "self minus other": valid networks of the same version
that, together with `other`, cover every address of `self` exactly once. -/
def AddressExcludePartition : Prop :=
  ∀ s o : Net, IsVersion s.bits → s.Valid → o.Valid → o.bits = s.bits →
    subnetOf o s = true →
    ∃ out, addressExclude s o = .ok out ∧
      (∀ m ∈ out, m.bits = s.bits ∧ m.Valid) ∧
      ∀ x, out.countP (fun m => m.mem x) = if s.mem x && !o.mem x then 1 else 0

theorem addressExcludePartition_proven : AddressExcludePartition :=
  fun s o _ hs ho hb hsub => SubnetsAux.addressExclude_spec s o hs ho hb hsub

end PyLean.Ipaddress
