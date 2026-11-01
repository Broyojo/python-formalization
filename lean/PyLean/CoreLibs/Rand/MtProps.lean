import PyLean.CoreLibs.Rand.Mt

/-!
Properties of the Mersenne Twister core, `Modules/_randommodule.c`.
-/

namespace PyLean.CoreLibs.Rand

open PyLean

/-! ### Array reads and writes -/

@[simp] theorem size_wr (mt : Array UInt32) (i : Nat) (v : UInt32) : (wr mt i v).size = mt.size := by
  simp [wr]

theorem rd_wr_ne (mt : Array UInt32) {i j : Nat} (v : UInt32) (h : i ≠ j) :
    rd (wr mt i v) j = rd mt j := by
  simp only [rd, wr, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h]

theorem rd_wr_self (mt : Array UInt32) {i : Nat} (v : UInt32) (h : i < mt.size) :
    rd (wr mt i v) i = v := by
  simp [rd, wr, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self, h]

theorem size_twist (mt : Array UInt32) (a b c : Nat) : (twist mt a b c).size = mt.size := by
  simp [twist]

theorem size_twistLow : ∀ (n kk : Nat) (mt : Array UInt32), (twistLow n kk mt).size = mt.size
  | 0, _, _ => rfl
  | n + 1, kk, mt => by simp [twistLow, size_twistLow n, size_twist]

theorem size_twistHigh : ∀ (n kk : Nat) (mt : Array UInt32), (twistHigh n kk mt).size = mt.size
  | 0, _, _ => rfl
  | n + 1, kk, mt => by simp [twistHigh, size_twistHigh n, size_twist]

theorem size_regenerate (mt : Array UInt32) : (regenerate mt).size = mt.size := by
  simp [regenerate, size_twistLow, size_twistHigh, size_twist]

/-! ### The invariant of `genrand_uint32` -/

/-- `genrand_uint32` keeps the type invariant, and the slot it reads is in bounds:
after the refill test `index < N`. -/
def GenrandInBounds : Prop :=
  ∀ s : State, s.WF →
    (let t := if s.index ≥ N then { mt := regenerate s.mt, index := 0 } else s
     t.mt.size = N ∧ t.index < N) ∧
    (genrand s).2.WF ∧ 1 ≤ (genrand s).2.index

theorem genrandInBounds_proven : GenrandInBounds := by
  rintro ⟨mt, idx⟩ ⟨h1, h2⟩
  simp only at h1 h2
  by_cases h : idx ≥ N
  · have : idx = N := by omega
    subst this
    simp [genrand, State.WF, size_regenerate, h1]
    decide
  · simp only [genrand, if_neg h, State.WF]
    refine ⟨⟨h1, by omega⟩, ⟨h1, by omega⟩, by omega⟩

theorem genrand_wf {s : State} (h : s.WF) : (genrand s).2.WF := (genrandInBounds_proven s h).2.1

theorem advance_wf : ∀ (n : Nat) {s : State}, s.WF → (advance n s).WF
  | 0, _, h => h
  | n + 1, _, h => advance_wf n (genrand_wf h)

theorem advance_add : ∀ (a b : Nat) (s : State), advance (a + b) s = advance b (advance a s)
  | 0, b, s => by simp [advance]
  | a + 1, b, s => by
    have : a + 1 + b = (a + b) + 1 := by omega
    rw [this]
    simp only [advance]
    exact advance_add a b _

/-! ### The twist recurrence -/

/-- `(mt[k]&UPPER_MASK)|(mt[k1]&LOWER_MASK)` mapped through `A`:
`(y >> 1) ^ mag01[y & 1]`, the matrix of the recurrence. -/
def twistMix (a b : UInt32) : UInt32 :=
  let y := (a &&& UPPER_MASK) ||| (b &&& LOWER_MASK)
  (y >>> 1) ^^^ mag01 y

theorem twist_eq (mt : Array UInt32) (a b c : Nat) :
    twist mt a b c = wr mt a (rd mt c ^^^ twistMix (rd mt a) (rd mt b)) := by
  simp [twist, twistMix, UInt32.xor_assoc]

theorem rd_twistLow : ∀ (n kk : Nat) (mt : Array UInt32), mt.size = N → kk + n ≤ N - MM →
    ∀ i, rd (twistLow n kk mt) i =
      if kk ≤ i ∧ i < kk + n then rd mt (i + MM) ^^^ twistMix (rd mt i) (rd mt (i + 1))
      else rd mt i
  | 0, kk, mt, _, _, i => by simp [twistLow]; intro h1 h2; omega
  | n + 1, kk, mt, hs, hb, i => by
    have hkk : kk < mt.size := by simp only [N, MM] at hs hb ⊢; omega
    have hs' : (twist mt kk (kk + 1) (kk + MM)).size = N := by rw [size_twist]; exact hs
    simp only [twistLow]
    rw [rd_twistLow n (kk + 1) _ hs' (by omega) i, twist_eq]
    by_cases h1 : kk + 1 ≤ i ∧ i < kk + 1 + n
    · rw [if_pos h1, if_pos (by omega)]
      have e1 : kk ≠ i + MM := by simp only [MM]; omega
      have e2 : kk ≠ i := by omega
      have e3 : kk ≠ i + 1 := by omega
      rw [rd_wr_ne _ _ e1, rd_wr_ne _ _ e2, rd_wr_ne _ _ e3]
    · rw [if_neg h1]
      by_cases h2 : i = kk
      · subst h2
        rw [rd_wr_self _ _ hkk, if_pos (by omega)]
      · rw [rd_wr_ne _ _ (Ne.symm h2), if_neg (by omega)]

theorem rd_twistHigh : ∀ (n kk : Nat) (mt : Array UInt32), mt.size = N → N - MM ≤ kk → kk + n ≤ N - 1 →
    ∀ i, rd (twistHigh n kk mt) i =
      if kk ≤ i ∧ i < kk + n then
        rd (twistHigh n kk mt) (i + MM - N) ^^^ twistMix (rd mt i) (rd mt (i + 1))
      else rd mt i
  | 0, kk, mt, _, _, _, i => by simp [twistHigh]; intro h1 h2; omega
  | n + 1, kk, mt, hs, hl, hb, i => by
    have hkk : kk < mt.size := by simp only [N, MM] at hs hb hl ⊢; omega
    have hs' : (twist mt kk (kk + 1) (kk + MM - N)).size = N := by rw [size_twist]; exact hs
    have ih := rd_twistHigh n (kk + 1) _ hs' (by omega) (by omega)
    simp only [twistHigh]
    rw [ih i, twist_eq]
    by_cases h1 : kk + 1 ≤ i ∧ i < kk + 1 + n
    · rw [if_pos h1, if_pos (by omega), ← twist_eq]
      rw [twist_eq]
      have e2 : kk ≠ i := by omega
      have e3 : kk ≠ i + 1 := by omega
      rw [rd_wr_ne _ _ e2, rd_wr_ne _ _ e3]
    · rw [if_neg h1]
      by_cases h2 : i = kk
      · subst h2
        rw [rd_wr_self _ _ hkk, if_pos (by omega)]
        have hlow := ih (i + MM - N)
        rw [twist_eq] at hlow
        rw [hlow, ← twist_eq, if_neg (by simp only [N, MM] at hl hb ⊢; omega), twist_eq,
          rd_wr_ne _ _ (by simp only [N, MM] at hl hb ⊢; omega)]
      · rw [rd_wr_ne _ _ (Ne.symm h2), if_neg (by omega)]

/-- The in-place loops of `genrand_uint32` compute the MT19937 recurrence on the
`N` words: with `x` the old array and `x'` the new one,
`x'[k] = x[k+M] ^ A(x[k], x[k+1])` for `k < N-M`,
`x'[k] = x'[k+M-N] ^ A(x[k], x[k+1])` for `N-M ≤ k < N-1`, and
`x'[N-1] = x'[M-1] ^ A(x[N-1], x'[0])`. -/
def TwistRecurrence : Prop :=
  ∀ mt : Array UInt32, mt.size = N →
    let x' := regenerate mt
    x'.size = N ∧
    (∀ k, k < N - MM → rd x' k = rd mt (k + MM) ^^^ twistMix (rd mt k) (rd mt (k + 1))) ∧
    (∀ k, N - MM ≤ k → k < N - 1 →
      rd x' k = rd x' (k + MM - N) ^^^ twistMix (rd mt k) (rd mt (k + 1))) ∧
    rd x' (N - 1) = rd x' (MM - 1) ^^^ twistMix (rd mt (N - 1)) (rd x' 0)

theorem twistRecurrence_proven : TwistRecurrence := by
  intro mt hs
  have hsize : (regenerate mt).size = N := by rw [size_regenerate, hs]
  set_option maxRecDepth 2000 in
  have hN1 : N - 1 - (N - MM) = 396 := by decide
  let low := twistLow (N - MM) 0 mt
  have hlowS : low.size = N := by simp only [low]; rw [size_twistLow]; exact hs
  let high := twistHigh (N - 1 - (N - MM)) (N - MM) low
  have hhighS : high.size = N := by simp only [high]; rw [size_twistHigh]; exact hlowS
  have hfin : regenerate mt = twist high (N - 1) 0 (MM - 1) := rfl
  have hlast : (N - 1) < high.size := by rw [hhighS]; decide
  have hne : ∀ {k : Nat}, k < N - 1 → (N - 1) ≠ k := by intro k hk; omega
  have hLow := rd_twistLow (N - MM) 0 mt hs (by omega)
  have hHigh := rd_twistHigh (N - 1 - (N - MM)) (N - MM) low hlowS (Nat.le_refl _) (by decide)
  have rdFin : ∀ k, k < N - 1 → rd (regenerate mt) k = rd high k := by
    intro k hk
    rw [hfin, twist_eq, rd_wr_ne _ _ (hne hk)]
  refine ⟨hsize, ?_, ?_, ?_⟩
  · intro k hk
    rw [rdFin k (by simp only [N, MM] at hk ⊢; omega)]
    show rd high k = _
    simp only [high]
    rw [hHigh k, if_neg (by omega), hLow k, if_pos (by omega)]
  · intro k hk1 hk2
    rw [rdFin k hk2, rdFin (k + MM - N) (by simp only [N, MM] at hk1 hk2 ⊢; omega)]
    simp only [high]
    rw [hHigh k, if_pos (by omega)]
    have e1 : ¬ (N - MM ≤ k + 1 ∧ False) := by simp
    have e2 := hLow k
    have e3 := hLow (k + 1)
    rw [if_neg (by omega)] at e2 e3
    rw [e2, e3]
  · rw [hfin, twist_eq, rd_wr_self _ _ hlast]
    have hm : (MM - 1) ≠ (N - 1) := by decide
    have h0 : (0 : Nat) ≠ (N - 1) := by decide
    rw [rd_wr_ne _ _ (Ne.symm hm), rd_wr_ne _ _ (Ne.symm h0)]
    have hhl : rd high (N - 1) = rd mt (N - 1) := by
      simp only [high]
      rw [hHigh (N - 1), if_neg (by decide), hLow (N - 1), if_neg (by decide)]
    rw [hhl]

/-! ### `random()` -/

theorem shr_toNat (w : UInt32) (s : Nat) (h : s < 32) : (w >>> s.toUInt32).toNat = w.toNat / 2 ^ s := by
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  simp
  have h2 : s % 32 = s := Nat.mod_eq_of_lt h
  simp [h2]

theorem shr5 (w : UInt32) : (w >>> 5).toNat = w.toNat / 32 := by
  simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem shr6 (w : UInt32) : (w >>> 6).toNat = w.toNat / 64 := by
  simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-- `random()` is the exact rational `(a*67108864+b)/2**53`, drawn from two
consecutive words: its numerator is below `2**53`, so the C double holds it exactly
and the result lies in `[0, 1)`. -/
def RandomIsExactRational : Prop :=
  ∀ s : State,
    let w1 := genrand s
    let w2 := genrand w1.2
    let a := w1.1.toNat / 32
    let b := w2.1.toNat / 64
    (randomNum s).1 = a * 67108864 + b ∧
    (randomNum s).1 < 2 ^ 53 ∧
    (randomNum s).2 = advance 2 s ∧
    (randomRat s).2 = advance 2 s ∧
    (randomRat s).1 = ((randomNum s).1 : Rat) / (9007199254740992 : Rat) ∧
    0 ≤ (randomRat s).1 ∧ (randomRat s).1 < 1

theorem randomNum_eq (s : State) :
    randomNum s = ((genrand s).1.toNat / 32 * 67108864 + (genrand (genrand s).2).1.toNat / 64,
      advance 2 s) := by
  simp [randomNum, randomParts, shr5, shr6, advance, Nat.shiftRight_eq_div_pow]

theorem randomNum_lt (s : State) : (randomNum s).1 < 2 ^ 53 := by
  rw [randomNum_eq]
  have h1 := (genrand s).1.toNat_lt
  have h2 := (genrand (genrand s).2).1.toNat_lt
  simp only
  omega

theorem randomIsExactRational_proven : RandomIsExactRational := by
  intro s
  have hlt := randomNum_lt s
  have hpos : (0 : Rat) < 9007199254740992 := by decide
  have hm : ((randomNum s).1 : Rat) < 9007199254740992 := by
    have : (randomNum s).1 < 9007199254740992 := hlt
    exact_mod_cast this
  have hdef : (randomRat s).1 = ((randomNum s).1 : Rat) / (9007199254740992 : Rat) := rfl
  refine ⟨by rw [randomNum_eq], hlt, by rw [randomNum_eq], rfl, hdef, ?_, ?_⟩
  · rw [hdef]
    have : (0 : Rat) ≤ ((randomNum s).1 : Rat) := Rat.natCast_nonneg
    grind
  · rw [hdef, Rat.div_lt_iff hpos]
    grind

/-! ### Seeding -/

theorem state_ext {a b : State} (h1 : a.mt = b.mt) (h2 : a.index = b.index) : a = b := by
  cases a
  cases b
  simp_all

/-- Two `N`-word arrays that read the same are equal. -/
theorem arr_ext {a b : Array UInt32} (ha : a.size = N) (hb : b.size = N)
    (h : ∀ i, i < N → rd a i = rd b i) : a = b := by
  apply Array.ext (by omega)
  intro i h1 h2
  have := h i (by omega)
  simpa [rd, Array.getD_eq_getD_getElem?, h1, h2] using this

theorem size_initLoop : ∀ (n mti : Nat) (mt : Array UInt32), (initLoop n mti mt).size = mt.size
  | 0, _, _ => rfl
  | n + 1, mti, mt => by simp [initLoop, size_initLoop n]

/-- One assignment of `init_genrand`. -/
def initMix (p : UInt32) (i : Nat) : UInt32 := (1812433253 : UInt32) * (p ^^^ (p >>> 30)) + i.toUInt32

theorem rd_initLoop : ∀ (n mti : Nat) (mt : Array UInt32), mt.size = N → 1 ≤ mti → mti + n ≤ N →
    ∀ i, rd (initLoop n mti mt) i =
      if mti ≤ i ∧ i < mti + n then initMix (rd (initLoop n mti mt) (i - 1)) i else rd mt i
  | 0, mti, mt, _, _, _, i => by simp [initLoop]; intro h1 h2; omega
  | n + 1, mti, mt, hs, h1, hb, i => by
    have hkk : mti < mt.size := by omega
    have hs' : (wr mt mti (initMix (rd mt (mti - 1)) mti)).size = N := by simp [hs]
    have ih := rd_initLoop n (mti + 1) _ hs' (by omega) (by omega)
    have hdef : initLoop (n + 1) mti mt
        = initLoop n (mti + 1) (wr mt mti (initMix (rd mt (mti - 1)) mti)) := rfl
    rw [hdef, ih i]
    by_cases hc : mti + 1 ≤ i ∧ i < mti + 1 + n
    · rw [if_pos hc, if_pos (by omega)]
    · rw [if_neg hc]
      by_cases h2 : i = mti
      · subst h2
        rw [rd_wr_self _ _ hkk, if_pos (by omega), ih (i - 1), if_neg (by omega),
          rd_wr_ne _ _ (by omega)]
      · rw [rd_wr_ne _ _ (Ne.symm h2), if_neg (by omega)]

/-- `init_genrand` writes every slot: `mt[0] = s` and
`mt[i] = 1812433253 * (mt[i-1] ^ (mt[i-1] >> 30)) + i`, and leaves `index = N`. The
old contents and the old `index` play no part. -/
def InitGenrandRecurrence : Prop :=
  ∀ (self : State) (s : UInt32), self.mt.size = N →
    let t := initGenrand self s
    t.WF ∧ t.index = N ∧ rd t.mt 0 = s ∧
    (∀ i, 1 ≤ i → i < N →
      rd t.mt i = (1812433253 : UInt32) * (rd t.mt (i - 1) ^^^ (rd t.mt (i - 1) >>> 30)) + i.toUInt32)

theorem initGenrand_mt (self : State) (s : UInt32) :
    (initGenrand self s).mt = initLoop (N - 1) 1 (wr self.mt 0 s) := by
  simp only [initGenrand]

theorem initGenrand_index (self : State) (s : UInt32) : (initGenrand self s).index = N := by
  simp only [initGenrand]

theorem initGenrand_size (self : State) (s : UInt32) :
    (initGenrand self s).mt.size = self.mt.size := by
  rw [initGenrand_mt, size_initLoop, size_wr]

theorem initGenrandRecurrence_proven : InitGenrandRecurrence := by
  intro self s hs
  have hs0 : (wr self.mt 0 s).size = N := by simp [hs]
  have hrd := rd_initLoop (N - 1) 1 _ hs0 (Nat.le_refl _) (by decide)
  have hidx := initGenrand_index self s
  refine ⟨⟨by rw [initGenrand_size, hs], Nat.le_of_eq hidx⟩, hidx, ?_, ?_⟩
  · rw [initGenrand_mt, hrd 0, if_neg (by omega), rd_wr_self _ _ (by rw [hs]; decide)]
  · intro i h1 h2
    rw [initGenrand_mt, hrd i, if_pos (by omega)]
    rfl

theorem initGenrand_indep {a b : State} (s : UInt32) (ha : a.mt.size = N) (hb : b.mt.size = N) :
    initGenrand a s = initGenrand b s := by
  have hA := initGenrandRecurrence_proven a s ha
  have hB := initGenrandRecurrence_proven b s hb
  simp only at hA hB
  obtain ⟨⟨sa, _⟩, ia, r0a, ra⟩ := hA
  obtain ⟨⟨sb, _⟩, ib, r0b, rb⟩ := hB
  have key : ∀ i, i < N → rd (initGenrand a s).mt i = rd (initGenrand b s).mt i := by
    intro i
    induction i with
    | zero => intro _; rw [r0a, r0b]
    | succ i ih =>
      intro h
      have := ih (by omega)
      rw [ra (i + 1) (by omega) h, rb (i + 1) (by omega) h]
      simp only [Nat.add_sub_cancel]
      rw [this]
  exact state_ext (arr_ext sa sb key) (by rw [ia, ib])

theorem size_byArrayKey (key : Array UInt32) : ∀ (k i j : Nat) (mt : Array UInt32),
    (byArrayKey key k i j mt).2.size = mt.size
  | 0, _, _, _ => rfl
  | k + 1, i, j, mt => by
    simp only [byArrayKey]
    split <;> simp [size_byArrayKey key k]

theorem size_byArrayMix : ∀ (k i : Nat) (mt : Array UInt32), (byArrayMix k i mt).size = mt.size
  | 0, _, _ => rfl
  | k + 1, i, mt => by
    simp only [byArrayMix]
    split <;> simp [size_byArrayMix k]

/-- `init_by_array`: the result depends on the key alone, is a valid state with
`index = N`, and has `mt[0] = 0x80000000` ("MSB is 1; assuring non-zero initial
array", _randommodule.c:243), so the all-zero fixed point of the recurrence cannot
be reached by seeding. -/
def InitByArrayComplete : Prop :=
  ∀ (key : Array UInt32) (a b : State), a.mt.size = N → b.mt.size = N →
    initByArray a key = initByArray b key ∧
    (initByArray a key).WF ∧ (initByArray a key).index = N ∧
    rd (initByArray a key).mt 0 = 0x80000000

theorem initByArray_mt (self : State) (key : Array UInt32) :
    (initByArray self key).mt = wr (byArrayMix (N - 1)
      (byArrayKey key (if N > key.size then N else key.size) 1 0 (initGenrand self 19650218).mt).1
      (byArrayKey key (if N > key.size then N else key.size) 1 0 (initGenrand self 19650218).mt).2)
      0 0x80000000 := by
  simp only [initByArray]

theorem initByArray_index (self : State) (key : Array UInt32) :
    (initByArray self key).index = N := by
  simp only [initByArray, initGenrand_index]

theorem initByArray_size (self : State) (key : Array UInt32) :
    (initByArray self key).mt.size = self.mt.size := by
  rw [initByArray_mt, size_wr, size_byArrayMix, size_byArrayKey, initGenrand_size]

theorem initByArray_facts (key : Array UInt32) (a : State) (ha : a.mt.size = N) :
    (initByArray a key).WF ∧ (initByArray a key).index = N ∧
    rd (initByArray a key).mt 0 = 0x80000000 := by
  have hsz := initByArray_size a key
  have hidx := initByArray_index a key
  refine ⟨⟨by rw [hsz, ha], Nat.le_of_eq hidx⟩, hidx, ?_⟩
  rw [initByArray_mt]
  apply rd_wr_self
  rw [size_byArrayMix, size_byArrayKey, initGenrand_size, ha]
  decide

theorem initByArrayComplete_proven : InitByArrayComplete := by
  intro key a b ha hb
  refine ⟨?_, initByArray_facts key a ha⟩
  apply state_ext
  · rw [initByArray_mt, initByArray_mt, initGenrand_indep _ ha hb]
  · rw [initByArray_index, initByArray_index]

/-! ### Splitting a seed into words -/

theorem toNat_toUInt32 (n : Nat) : n.toUInt32.toNat = n % 2 ^ 32 := by simp

theorem wordsToNat_keyWords : ∀ (m n : Nat),
    wordsToNat ((List.range m).map fun i => (n >>> (32 * i)).toUInt32) = n % 2 ^ (32 * m)
  | 0, n => by simp [wordsToNat, Nat.mod_one]
  | m + 1, n => by
    have hmap : ((List.range (m + 1)).map fun i => (n >>> (32 * i)).toUInt32)
        = n.toUInt32 :: (List.range m).map (fun i => ((n >>> 32) >>> (32 * i)).toUInt32) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.mul_zero, Nat.shiftRight_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp, Nat.succ_eq_add_one, Nat.shiftRight_add, Nat.mul_add, Nat.mul_one]
      rw [← Nat.shiftRight_add, ← Nat.shiftRight_add, Nat.add_comm]
    rw [hmap]
    simp only [wordsToNat]
    rw [wordsToNat_keyWords m (n >>> 32), toNat_toUInt32]
    have h : 32 * (m + 1) = 32 + 32 * m := by omega
    rw [h, Nat.pow_add, Nat.mod_mul, Nat.shiftRight_eq_div_pow]

theorem lt_pow_bitLength (n : Nat) : n < 2 ^ bitLength n := by
  unfold bitLength
  split
  · simp_all
  · exact Nat.lt_log2_self

theorem bitLength_le_keyUsed (n : Nat) : bitLength n ≤ 32 * keyUsed (bitLength n) := by
  unfold keyUsed
  split <;> omega

/-- The key of a non-negative int, read back as an integer. -/
theorem keyWords_reassemble (n : Nat) :
    wordsToNat (keyWords n (keyUsed (bitLength n))).toList = n := by
  have : (keyWords n (keyUsed (bitLength n))).toList
      = (List.range (keyUsed (bitLength n))).map fun i => (n >>> (32 * i)).toUInt32 := by
    simp [keyWords]
  rw [this, wordsToNat_keyWords]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le (lt_pow_bitLength n)
    (Nat.pow_le_pow_right (by decide) (bitLength_le_keyUsed n))

/-- "If *a* is an int, all bits are used" (Lib/random.py:137): splitting into 32-bit
chunks (_randommodule.c:337-371) loses nothing, so different non-negative seeds give
different keys, and `keyused` is at least 1. -/
def SeedKeyWords : Prop :=
  (∀ n : Nat, 1 ≤ (keyWords n (keyUsed (bitLength n))).size ∧
    wordsToNat (keyWords n (keyUsed (bitLength n))).toList = n) ∧
  (∀ n m : Nat, keyWords n (keyUsed (bitLength n)) = keyWords m (keyUsed (bitLength m)) → n = m)

theorem seedKeyWords_proven : SeedKeyWords := by
  refine ⟨fun n => ⟨?_, keyWords_reassemble n⟩, fun n m h => ?_⟩
  · simp only [keyWords, Array.size_map, Array.size_range, keyUsed]
    split <;> omega
  · rw [← keyWords_reassemble n, ← keyWords_reassemble m, h]

/-- How `random_seed` treats its argument, _randommodule.c:316-333: an `int` by its
absolute value (and a subclass the same way, without calling its `__abs__`), any
other object by `(size_t)hash(x)`, and an unhashable object is an error. -/
def SeedArgKinds : Prop :=
  ∀ (self : State) (ent : Entropy) (n h : Int) (ty : String),
    randomSeed self (.exactInt (-n)) ent = randomSeed self (.exactInt n) ent ∧
    randomSeed self (.intSubclass n) ent = randomSeed self (.exactInt n) ent ∧
    randomSeed self (.hashable h) ent = randomSeed self (.exactInt (h % (2 ^ 64))) ent ∧
    randomSeed self (.unhashable ty) ent = .error (.typeError s!"unhashable type: '{ty}'")

theorem seedArgKinds_proven : SeedArgKinds := by
  intro self ent n h ty
  refine ⟨?_, rfl, ?_, rfl⟩
  · simp [randomSeed, seedValue, Int.natAbs_neg]
  · have h1 : 0 ≤ h % (2 ^ 64 : Int) := Int.emod_nonneg _ (by decide)
    have h2 : ((h % (2 ^ 64 : Int)).natAbs : Int) = h % (2 ^ 64) := Int.natAbs_of_nonneg h1
    simp only [randomSeed, seedValue]
    have h3 : (h % (2 ^ 64 : Int)).natAbs = (h % (2 ^ 64 : Int)).toNat := by omega
    rw [h3]

/-- The fallback seed keeps all 64 bits of a `PyTime_t`: the two words of
_randommodule.c:272-273, read back as an unsigned integer, equal `now` modulo `2**64`. -/
def TimeWordsExact : Prop :=
  ∀ now : Int,
    (((timeWords now).1.toNat : Int) + 2 ^ 32 * ((timeWords now).2.toNat : Int)) % (2 ^ 64) = now % (2 ^ 64)

theorem timeWordsExact_proven : TimeWordsExact := by
  intro now
  have hr0 : 0 ≤ now % (2 ^ 32 : Int) := Int.emod_nonneg _ (by decide)
  have hr1 : now % (2 ^ 32 : Int) < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  have hq0 : 0 ≤ (now / (2 ^ 32 : Int)) % (2 ^ 32 : Int) := Int.emod_nonneg _ (by decide)
  have hq1 : (now / (2 ^ 32 : Int)) % (2 ^ 32 : Int) < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  have e1 : (((now % (2 ^ 32 : Int)).toNat.toUInt32.toNat : Nat) : Int) = now % (2 ^ 32 : Int) := by
    rw [toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    omega
  have e2 : (((now / (2 ^ 32 : Int) % (2 ^ 32 : Int)).toNat.toUInt32.toNat : Nat) : Int)
      = (now / (2 ^ 32 : Int)) % (2 ^ 32 : Int) := by
    rw [toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [timeWords]
  rw [e1, e2]
  omega

/-- `seed(None)`: the operating-system key when there is one
(`random_seed_urandom`), else the time-and-pid key (`random_seed_time_pid`), and in
either case a valid state. Only a failing clock raises. -/
def SeedNone : Prop :=
  ∀ (self : State) (ent : Entropy), self.mt.size = N →
    (∀ key, ent.urandom = some key → randomSeed self .none ent = .ok (initByArray self key)) ∧
    (ent.urandom = none → randomSeed self .none ent = randomSeedTimePid self ent) ∧
    (∀ s, randomSeed self .none ent = .ok s →
      s.WF ∧ s.index = N ∧ rd s.mt 0 = 0x80000000) ∧
    randomSeed self .null ent = randomSeed self .none ent

theorem seedNone_proven : SeedNone := by
  intro self ent hs
  have hkey : ∀ key, ent.urandom = some key →
      randomSeed self .none ent = .ok (initByArray self key) := by
    intro key h
    simp [randomSeed, randomSeedUrandom, h]
  have hnone : ent.urandom = none → randomSeed self .none ent = randomSeedTimePid self ent := by
    intro h
    simp [randomSeed, randomSeedUrandom, h]
  refine ⟨hkey, hnone, ?_, rfl⟩
  intro s h
  cases hu : ent.urandom with
  | some key =>
    rw [hkey key hu] at h
    have := Except.ok.inj h
    subst this
    exact initByArray_facts key self hs
  | none =>
    rw [hnone hu] at h
    simp only [randomSeedTimePid, bind, Except.bind] at h
    cases hn : ent.now with
    | error e => rw [hn] at h; cases h
    | ok now =>
      rw [hn] at h
      cases hm : ent.monotonic with
      | error e => simp [hm] at h
      | ok mono =>
        rw [hm] at h
        have := Except.ok.inj h
        subst this
        exact initByArray_facts _ self hs

/-- `_random.Random(x)`, `r.seed(x)` for any `r`: seeding does not depend on the
previous state. `random_init_impl` and `_random_Random_seed_impl` are both
`random_seed`, so `Random(x)` and `seed(x)` start the same stream (bpo-42008). -/
def SeedIndependentOfState : Prop :=
  ∀ (a b : State) (arg : CArg) (ent : Entropy), a.mt.size = N → b.mt.size = N →
    (cSeedMethod a arg ent = cSeedMethod b arg ent) ∧ cInit arg ent = cSeedMethod a arg ent

theorem randomSeed_indep {a b : State} (arg : CArg) (ent : Entropy) (ha : a.mt.size = N) (hb : b.mt.size = N) :
    randomSeed a arg ent = randomSeed b arg ent := by
  have hA := fun k => (initByArrayComplete_proven k a b ha hb).1
  unfold randomSeed
  cases arg with
  | null | none =>
    simp only [randomSeedUrandom]
    cases hu : ent.urandom with
    | some key => simp [hA]
    | none =>
      simp only [Option.map, randomSeedTimePid]
      simp [hA]
  | exactInt n | intSubclass n | hashable n | unhashable n =>
    simp only [bind, Except.bind, hA]

theorem genericNew_size : genericNew.mt.size = N := by simp [genericNew]

theorem seedIndependentOfState_proven : SeedIndependentOfState := by
  intro a b arg ent ha hb
  exact ⟨randomSeed_indep arg ent ha hb, randomSeed_indep arg ent genericNew_size ha⟩

/-! ### `getstate`, `setstate` -/

theorem convertWords_map (ws : List UInt32) :
    convertWords (ws.map fun w => Elem.int (w.toNat : Int)) = .ok ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hw := w.toNat_lt
    have h1 : asUnsignedLong (.int (w.toNat : Int)) = .ok w.toNat := by
      simp only [asUnsignedLong]
      rw [if_neg (by omega), if_neg (by omega)]
      simp
    simp only [List.map_cons, convertWords, h1, ih]
    simp [bind, Except.bind, pure, Except.pure]

theorem rd_toArray_range (mt : Array UInt32) (hs : mt.size = N) :
    ((List.range N).map (fun i => rd mt i)).toArray = mt := by
  apply Array.ext
  · simp [hs]
  · intro i h1 h2
    simp [rd, Array.getD_eq_getD_getElem?, h2]

/-- A state read by `getstate` is a 625-tuple of a word list and the index, and
`setstate` restores it exactly from anywhere in the stream. -/
def CStateRoundTrip : Prop :=
  ∀ s : State, s.WF →
    (cGetstate s).length = N + 1 ∧
    (∀ x ∈ cGetstate s, 0 ≤ x ∧ x < 2 ^ 32) ∧
    (∀ n, cSetstate (.tuple ((cGetstate (advance n s)).map .int)) = .ok (advance n s))

theorem cSetstate_getstate {s : State} (h : s.WF) :
    cSetstate (.tuple ((cGetstate s).map .int)) = .ok s := by
  obtain ⟨hs, hi⟩ := h
  have hlen : ((cGetstate s).map Elem.int).length = N + 1 := by simp [cGetstate]
  have hwords : (cGetstate s).map Elem.int
      = ((List.range N).map (fun i => rd s.mt i)).map (fun w => Elem.int (w.toNat : Int))
        ++ [Elem.int (s.index : Int)] := by
    simp [cGetstate, Function.comp_def]
  have htake : ((cGetstate s).map Elem.int).take N
      = ((List.range N).map (fun i => rd s.mt i)).map (fun w => Elem.int (w.toNat : Int)) := by
    rw [hwords, List.take_left' (by simp)]
  have hget : ((cGetstate s).map Elem.int).getD N (.int 0) = Elem.int (s.index : Int) := by
    rw [hwords]
    simp [List.getD]
  have hidx : asLong (.int (s.index : Int)) = .ok (s.index : Int) := by
    simp only [asLong]
    rw [if_neg (by simp only [N] at hi; omega)]
  simp only [cSetstate]
  rw [if_neg (by rw [hlen]; simp), htake, convertWords_map, hget, hidx]
  simp only [bind, Except.bind]
  rw [if_neg (by simp only [N] at hi ⊢; omega)]
  cases s
  simp only at hs ⊢
  simp only [pure, Except.pure, rd_toArray_range _ hs]
  simp

theorem cStateRoundTrip_proven : CStateRoundTrip := by
  intro s h
  refine ⟨by simp [cGetstate], ?_, fun n => cSetstate_getstate (advance_wf n h)⟩
  intro x hx
  simp only [cGetstate, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hx
  rcases hx with ⟨i, _, rfl⟩ | rfl
  · have := (rd s.mt i).toNat_lt
    simp
    omega
  · have := h.2
    simp only [N] at this
    omega

theorem convertWords_spec : ∀ (l : List Elem) (ws : List UInt32), convertWords l = .ok ws →
    ws.length = l.length ∧ ∀ (i : Nat) (hi : i < l.length),
      ∃ w : Int, l[i] = .int w ∧ 0 ≤ w ∧ w < 2 ^ 64 ∧ ws.getD i 0 = w.toNat.toUInt32
  | [], ws, h => by
    cases h
    simp
  | e :: es, ws, h => by
    simp only [convertWords, bind, Except.bind] at h
    cases he : asUnsignedLong e with
    | error x => rw [he] at h; cases h
    | ok w =>
      rw [he] at h
      simp only at h
      cases hr : convertWords es with
      | error x => rw [hr] at h; cases h
      | ok rest =>
        rw [hr] at h
        simp only [pure, Except.pure] at h
        cases h
        have ih := convertWords_spec es rest hr
        refine ⟨by simp [ih.1], ?_⟩
        intro i hi
        cases i with
        | zero =>
          cases e with
          | other ty => simp [asUnsignedLong] at he
          | int n =>
            simp only [asUnsignedLong] at he
            split at he
            · cases he
            · split at he
              · cases he
              · cases he
                refine ⟨n, rfl, by omega, by omega, rfl⟩
        | succ i =>
          obtain ⟨w', h1, h2, h3, h4⟩ := ih.2 i (by simpa using hi)
          exact ⟨w', by simpa using h1, h2, h3, by simpa [List.getD] using h4⟩

/-- `setstate` validates before it writes: whatever it accepts is a valid state with
`0 ≤ index ≤ N` (so `genrand_uint32` cannot read past the array), each word being
its element truncated to `uint32_t` (elements up to `2**64 - 1` are accepted
silently). A non-tuple, a wrong size or a bad index never succeed. -/
def CSetstateValidates : Prop :=
  (∀ (xs : List Elem) (s : State), cSetstate (.tuple xs) = .ok s →
    xs.length = N + 1 ∧ s.WF ∧
    ∀ (i : Nat) (hi : i < N), ∃ (w : Int) (h : i < xs.length),
      xs[i] = .int w ∧ 0 ≤ w ∧ w < 2 ^ 64 ∧ rd s.mt i = w.toNat.toUInt32) ∧
  cSetstate .notTuple = .error (.typeError "state vector must be a tuple") ∧
  (∀ xs : List Elem, xs.length ≠ N + 1 →
    cSetstate (.tuple xs) = .error (.valueError "state vector is the wrong size"))

theorem cSetstateValidates_proven : CSetstateValidates := by
  refine ⟨?_, rfl, ?_⟩
  · intro xs s h
    simp only [cSetstate] at h
    split at h
    · cases h
    rename_i hlen
    have hlen' : xs.length = N + 1 := Decidable.not_not.mp hlen
    simp only [bind, Except.bind] at h
    cases hw : convertWords (xs.take N) with
    | error e => rw [hw] at h; cases h
    | ok ws =>
      rw [hw] at h
      simp only at h
      cases hi : asLong (xs.getD N (.int 0)) with
      | error e => rw [hi] at h; cases h
      | ok index =>
        rw [hi] at h
        simp only at h
        split at h
        · cases h
        rename_i hbad
        simp only [pure, Except.pure] at h
        cases h
        have spec := convertWords_spec _ _ hw
        have hlenws : ws.length = N := by
          rw [spec.1, List.length_take]
          omega
        refine ⟨hlen', ⟨by simp [hlenws], ?_⟩, ?_⟩
        · simp only
          omega
        · intro i hiN
          obtain ⟨w, h1, h2, h3, h4⟩ := spec.2 i (by rw [List.length_take]; omega)
          refine ⟨w, by omega, by simpa using h1, h2, h3, ?_⟩
          simpa [rd, Array.getD_eq_getD_getElem?, List.getD] using h4
  · intro xs h
    simp [cSetstate, h]

/-! ### `getrandbits` -/

theorem fillWords_state : ∀ (w k : Nat) (s : State), (fillWords w k s).2 = advance w s
  | 0, _, _ => rfl
  | w + 1, k, s => by
    simp only [fillWords, advance]
    exact fillWords_state w (k - 32) _

theorem fillWords_full : ∀ (w k : Nat) (s : State), 32 * w ≤ k →
    (fillWords w k s).1 = stream w s
  | 0, _, _, _ => rfl
  | w + 1, k, s, h => by
    simp only [fillWords, stream]
    rw [if_neg (by omega)]
    rw [fillWords_full w (k - 32) _ (by omega)]

/-- The last, possibly partial, word. -/
theorem shifted_lt (r : UInt32) (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 32) :
    (r >>> (32 - k).toUInt32).toNat < 2 ^ k := by
  rw [shr_toNat _ _ (by omega)]
  have hr := r.toNat_lt
  apply Nat.div_lt_of_lt_mul
  have : 2 ^ (32 - k) * 2 ^ k = 2 ^ 32 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [this]
  exact hr

theorem fillWords_lt : ∀ (w k : Nat) (s : State), 1 ≤ k → k ≤ 32 * w → 32 * w < k + 32 →
    wordsToNat (fillWords w k s).1 < 2 ^ k
  | 0, k, _, _, h, _ => by omega
  | w + 1, k, s, h1, h2, h3 => by
    simp only [fillWords]
    by_cases hk : k ≤ 32
    · cases w with
      | zero =>
        simp only [fillWords, wordsToNat]
        by_cases hk' : k < 32
        · rw [if_pos hk']
          have := shifted_lt (genrand s).1 k h1 hk
          omega
        · rw [if_neg hk']
          have hk32 : k = 32 := by omega
          subst hk32
          have := (genrand s).1.toNat_lt
          simpa using this
      | succ w => omega
    · rw [if_neg (by omega)]
      simp only [wordsToNat]
      have ih := fillWords_lt w (k - 32) (genrand s).2 (by omega) (by omega) (by omega)
      have hw := (genrand s).1.toNat_lt
      have hp : (2 : Nat) ^ k = 2 ^ 32 * 2 ^ (k - 32) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      rw [hp]
      have : 2 ^ 32 * (wordsToNat (fillWords w (k - 32) (genrand s).2).1 + 1)
          ≤ 2 ^ 32 * 2 ^ (k - 32) := Nat.mul_le_mul_left _ ih
      rw [Nat.mul_add] at this
      omega

/-- `getrandbits(k)` is below `2**k`, on all three paths: `k = 0`, `k ≤ 32`, `k > 32`. -/
def GetrandbitsBound : Prop :=
  ∀ (mallocOk : Nat → Bool) (k : Nat) (s s' : State) (r : Nat),
    getrandbitsImpl mallocOk k s = (.ok r, s') → r < 2 ^ k

theorem getrandbitsBound_proven : GetrandbitsBound := by
  intro m k s s' r h
  unfold getrandbitsImpl at h
  split at h
  · rename_i h0
    subst h0
    cases h
    decide
  split at h
  · rename_i h0 h1
    cases h
    exact shifted_lt _ k (by omega) h1
  split at h
  · cases h
  simp only at h
  split at h
  · cases h
  rename_i h0 h1 _ _
  simp only [Prod.mk.injEq, Except.ok.injEq] at h
  rw [← h.1]
  apply fillWords_lt _ _ _ (by omega)
  · have := Nat.div_add_mod (k - 1) 32
    omega
  · have := Nat.div_add_mod (k - 1) 32
    have := Nat.mod_lt (k - 1) (show 32 > 0 by decide)
    omega

/-- The fast path agrees with the word loop: `k ≤ 32` gives what the loop of
_randommodule.c:535-544 would give for one word. -/
theorem fast_eq_fill (m : Nat → Bool) (k : Nat) (s : State) (h1 : 0 < k) (h2 : k ≤ 32) :
    getrandbitsImpl m k s = (.ok (wordsToNat (fillWords 1 k s).1), (fillWords 1 k s).2) := by
  have hg : getrandbitsImpl m k s =
      (.ok ((genrand s).1 >>> (32 - k).toUInt32).toNat, (genrand s).2) := by
    unfold getrandbitsImpl
    rw [if_neg (by omega), if_pos h2]
  rw [hg]
  simp only [fillWords, wordsToNat]
  by_cases h3 : k < 32
  · rw [if_pos h3]
    simp
  · have : k = 32 := by omega
    subst this
    simp

/-- The structure of `getrandbits(k)`. Writing `words = (k - 1) // 32 + 1`: the check
at _randommodule.c:521 cannot fire for a `uint64_t` `k`; `k ≤ 32` (the fast path)
computes what the word loop would; a failed allocation raises `MemoryError` before
any draw; otherwise exactly `words` words are drawn. -/
def GetrandbitsWords : Prop :=
  ∀ (m : Nat → Bool) (k : Nat) (s : State), 0 < k → k < 2 ^ 64 →
    let words := (k - 1) / 32 + 1
    words ≤ maxWords ∧
    (k ≤ 32 → getrandbitsImpl m k s =
      (.ok (wordsToNat (fillWords words k s).1), advance words s)) ∧
    (32 < k → m (words * 4) = true → getrandbitsImpl m k s =
      (.ok (wordsToNat (fillWords words k s).1), advance words s)) ∧
    (32 < k → m (words * 4) = false →
      getrandbitsImpl m k s = (.error (.named "MemoryError" ""), s))

theorem getrandbits_words (m : Nat → Bool) (k : Nat) (s : State) (h0 : 0 < k) (hk : k < 2 ^ 64)
    (hm : 32 < k → m (((k - 1) / 32 + 1) * 4) = true) :
    getrandbitsImpl m k s =
      (.ok (wordsToNat (fillWords ((k - 1) / 32 + 1) k s).1), advance ((k - 1) / 32 + 1) s) := by
  by_cases h32 : k ≤ 32
  · have hw : (k - 1) / 32 + 1 = 1 := by omega
    rw [hw, fast_eq_fill m k s h0 h32, fillWords_state]
  · unfold getrandbitsImpl
    have hmax : ¬ (k - 1) / 32 + 1 > maxWords := by
      simp only [maxWords]
      omega
    rw [if_neg (by omega), if_neg h32, if_neg hmax]
    simp only [hm (by omega), Bool.not_true, Bool.false_eq_true, if_false]
    rw [fillWords_state]

theorem getrandbitsWords_proven : GetrandbitsWords := by
  intro m k s h0 hk
  refine ⟨by simp only [maxWords]; omega, fun h => ?_, fun h hm => ?_, fun h hm => ?_⟩
  · exact getrandbits_words m k s h0 hk (fun h' => by omega)
  · exact getrandbits_words m k s h0 hk (fun _ => hm)
  · unfold getrandbitsImpl
    have hmax : ¬ (k - 1) / 32 + 1 > maxWords := by
      simp only [maxWords]
      omega
    rw [if_neg (by omega), if_neg (by omega), if_neg hmax]
    simp [hm]

/-- `getrandbits(k)` against repeated 32-bit draws, with an allocator that succeeds.
For `k > 32` the low 32 bits are one `getrandbits(32)` and the rest is
`getrandbits(k - 32)` on the following state. So `getrandbits(32 * w)` is the next `w`
words of the stream, least significant first, and uses exactly those. -/
def GetrandbitsRecursive : Prop :=
  ∀ (m : Nat → Bool) (s : State), (∀ n, m n = true) →
    getrandbitsImpl m 32 s = (.ok (genrand s).1.toNat, (genrand s).2) ∧
    (∀ k, 32 < k → k < 2 ^ 64 →
      getrandbitsImpl m k s =
        match getrandbitsImpl m (k - 32) (genrand s).2 with
        | (.ok r, s2) => (.ok ((genrand s).1.toNat + 2 ^ 32 * r), s2)
        | (.error e, s2) => (.error e, s2)) ∧
    (∀ w, 0 < w → 32 * w < 2 ^ 64 →
      getrandbitsImpl m (32 * w) s = (.ok (wordsToNat (stream w s)), advance w s))

theorem getrandbitsRecursive_proven : GetrandbitsRecursive := by
  intro m s hm
  refine ⟨?_, fun k h1 h2 => ?_, fun w h1 h2 => ?_⟩
  · rw [fast_eq_fill m 32 s (by decide) (by decide)]
    simp [fillWords, wordsToNat]
  · rw [getrandbits_words m k s (by omega) h2 (fun _ => hm _)]
    rw [getrandbits_words m (k - 32) _ (by omega) (by omega) (fun _ => hm _)]
    have hw : (k - 1) / 32 + 1 = ((k - 32 - 1) / 32 + 1) + 1 := by omega
    rw [hw]
    simp only [fillWords, advance, wordsToNat]
    rw [if_neg (by omega)]
  · have hw : (32 * w - 1) / 32 + 1 = w := by omega
    rw [getrandbits_words m (32 * w) s (by omega) h2 (fun _ => hm _), hw,
      fillWords_full w (32 * w) s (Nat.le_refl _)]

/-! ### An instance that was never seeded -/

theorem rd_wr_zero {mt : Array UInt32} (k : Nat) (hz : ∀ i, rd mt i = 0) : ∀ i, rd (wr mt k 0) i = 0 := by
  intro i
  by_cases h : k = i
  · subst h
    by_cases hk : k < mt.size
    · exact rd_wr_self _ _ hk
    · have : wr mt k 0 = mt := by
        simp [wr, Array.setIfInBounds, hk]
      rw [this]
      exact hz k
  · rw [rd_wr_ne _ _ h]
    exact hz i

theorem twist_zero {mt : Array UInt32} (a b c : Nat) (hz : ∀ i, rd mt i = 0) :
    ∀ i, rd (twist mt a b c) i = 0 := by
  have : twist mt a b c = wr mt a 0 := by
    simp [twist, hz]
    rfl
  rw [this]
  exact rd_wr_zero a hz

theorem twistLow_zero : ∀ (n kk : Nat) {mt : Array UInt32}, (∀ i, rd mt i = 0) →
    ∀ i, rd (twistLow n kk mt) i = 0
  | 0, _, _, hz => hz
  | n + 1, kk, _, hz => twistLow_zero n (kk + 1) (twist_zero _ _ _ hz)

theorem twistHigh_zero : ∀ (n kk : Nat) {mt : Array UInt32}, (∀ i, rd mt i = 0) →
    ∀ i, rd (twistHigh n kk mt) i = 0
  | 0, _, _, hz => hz
  | n + 1, kk, _, hz => twistHigh_zero n (kk + 1) (twist_zero _ _ _ hz)

theorem regenerate_zero {mt : Array UInt32} (hz : ∀ i, rd mt i = 0) :
    ∀ i, rd (regenerate mt) i = 0 :=
  twist_zero _ _ _ (twistHigh_zero _ _ (twistLow_zero _ _ hz))

theorem temper_zero : temper 0 = 0 := by decide

theorem genrand_zero {s : State} (hz : ∀ i, rd s.mt i = 0) :
    (genrand s).1 = 0 ∧ ∀ i, rd (genrand s).2.mt i = 0 := by
  unfold genrand
  by_cases h : s.index ≥ N
  · simp only [if_pos h]
    exact ⟨by rw [regenerate_zero hz, temper_zero], regenerate_zero hz⟩
  · simp only [if_neg h]
    exact ⟨by rw [hz, temper_zero], hz⟩

theorem stream_zero : ∀ (n : Nat) {s : State}, (∀ i, rd s.mt i = 0) → ∀ w ∈ stream n s, w = 0
  | 0, _, _, _, h => by simp [stream] at h
  | n + 1, s, hz, w, h => by
    simp only [stream, List.mem_cons] at h
    rcases h with rfl | h
    · exact (genrand_zero hz).1
    · exact stream_zero n (genrand_zero hz).2 w h

theorem genericNew_zero : ∀ i, rd genericNew.mt i = 0 := by
  intro i
  simp only [genericNew, rd, Array.getD_eq_getD_getElem?]
  by_cases h : i < N
  · simp [h]
  · simp [h]

/-- An instance of `_random.Random` or a subclass produces some non-zero word,
however it was created. `tp_new` does not seed (:584), so an instance whose `__init__`
did not run `random_seed` (a subclass that does not call `super().__init__()`) stays
on the all-zero state, the fixed point of the recurrence. Before Python 3.11 `tp_new`
seeded. -/
def NewInstanceProducesRandomness : Prop :=
  ∃ n, ∃ w ∈ stream n genericNew, w ≠ 0

theorem newInstanceProducesRandomness_refuted : ¬ NewInstanceProducesRandomness := by
  rintro ⟨n, w, hw, hne⟩
  exact hne (stream_zero n genericNew_zero w hw)

end PyLean.CoreLibs.Rand
