import PyLean.RangeSlice.Length

/-!
Indexing, membership, `index`/`count`, equality and hashing of ranges,
against the mathematical sequence `start + k*step, 0 <= k < L`, for all
Python ints.
-/

namespace PyLean.RangeSlice

open PyLean

theorem computeItem_eq (r : Range) (i : Int) : computeItem r i = r.elem i := by
  unfold computeItem Range.elem
  split
  · rename_i h; rw [h, Int.mul_one]
  · rfl

/-- `r[i]` for an int `i`: element `i` (or `i + L` for negative `i`) when
`-L <= i < L`, `IndexError` otherwise, for every Python int `i` and every
range (`r.WF` is the type invariant; `L` is the mathematical length). -/
def GetItemSeq : Prop :=
  ∀ (r : Range) (L i : Int), r.WF → r.Len L →
    computeRangeItem r i =
      if 0 ≤ i ∧ i < L then .ok (r.elem i)
      else if -L ≤ i ∧ i < 0 then .ok (r.elem (i + L))
      else .error (.indexError "range object index out of range")

theorem getItemSeq_proven : GetItemSeq := by
  intro r L i hw hL
  have hlen := hw.length_eq hL
  unfold computeRangeItem
  rw [hlen]
  by_cases h1 : 0 ≤ i ∧ i < L
  · rw [ite_t h1, ite_f (show ¬ i < 0 by omega), ite_f (show ¬ (i < 0 ∨ i ≥ L) by omega),
      computeItem_eq]
  · rw [ite_f h1]
    by_cases h2 : -L ≤ i ∧ i < 0
    · rw [ite_t h2, ite_t h2.2, ite_f (show ¬ (L + i < 0 ∨ L + i ≥ L) by omega),
        computeItem_eq, Int.add_comm L i]
    · rw [ite_f h2]
      by_cases h3 : i < 0
      · rw [ite_t h3, ite_t (show L + i < 0 ∨ L + i ≥ L by omega)]
      · rw [ite_f h3, ite_t (show i < 0 ∨ i ≥ L by omega)]

/-- Core membership lemma: for `step ≠ 0`, `x = start + k*step` for some
`k >= 0` exactly when `x` is on the `start` side in the step direction and
`step` divides `x - start`. -/
theorem mem_iff_dvd (start step x : Int) (hs : step ≠ 0) :
    (∃ k, 0 ≤ k ∧ x = start + k * step) ↔
      ((if step > 0 then start ≤ x else x ≤ start) ∧ (x - start) % step = 0) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨?_, ?_⟩
    · by_cases hp : step > 0
      · rw [ite_t hp]; have := Int.mul_nonneg hk (Int.le_of_lt hp); omega
      · rw [ite_f hp]
        have := Int.mul_nonpos_of_nonneg_of_nonpos hk (show step ≤ 0 by omega); omega
    · rw [show start + k * step - start = k * step by omega]
      exact Int.mul_emod_left k step
  · rintro ⟨hside, hmod⟩
    have hd : step ∣ x - start := Int.dvd_of_emod_eq_zero hmod
    have hc := Int.ediv_mul_cancel hd
    refine ⟨(x - start) / step, ?_, by omega⟩
    by_cases hp : step > 0
    · rw [ite_t hp] at hside
      exact Int.ediv_nonneg (by omega) (Int.le_of_lt hp)
    · rw [ite_f hp] at hside
      apply Int.not_lt.mp
      intro hneg
      have := Int.mul_pos_of_neg_of_neg hneg (show step < 0 by omega)
      omega

/-- `x in r` for an int `x` (the `range_contains_long` fast path) holds
exactly when `x` is one of the `L` elements, for all Python ints. -/
def ContainsMem : Prop :=
  ∀ (r : Range) (L x : Int), r.WF → r.Len L → (rangeContainsLong r x = true ↔ r.MemL L x)

theorem rangeContainsLong_iff (r : Range) (x : Int) :
    rangeContainsLong r x = true ↔
      ((if r.step > 0 then r.start ≤ x ∧ x < r.stop else x ≤ r.start ∧ r.stop < x) ∧
        (x - r.start) % r.step = 0) := by
  unfold rangeContainsLong
  by_cases hp : r.step > 0
  · simp only [hp, ite_true]
    by_cases h1 : r.start ≤ x <;> by_cases h2 : x < r.stop <;> simp [h1, h2]
  · simp only [hp, ite_false]
    by_cases h1 : x ≤ r.start <;> by_cases h2 : r.stop < x <;> simp [h1, h2]

theorem containsMem_proven : ContainsMem := by
  intro r L x hw hL
  have hs := hw.1
  obtain ⟨hL0, hLk⟩ := hL
  rw [rangeContainsLong_iff]
  unfold Range.MemL Range.elem
  have key := mem_iff_dvd r.start r.step x hs
  by_cases hp : r.step > 0
  · rw [ite_t hp] at key ⊢
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      obtain ⟨k, hk, hx⟩ := key.2 ⟨h1, h3⟩
      refine ⟨k, hk, ?_, hx⟩
      apply (hLk k hk).2
      unfold InSeq; rw [ite_t (show (0 : Int) < r.step from hp)]; omega
    · rintro ⟨k, hk, hkL, hx⟩
      have hin := (hLk k hk).1 hkL
      unfold InSeq at hin; rw [ite_t (show (0 : Int) < r.step from hp)] at hin
      have hm := key.1 ⟨k, hk, hx⟩
      exact ⟨⟨hm.1, by omega⟩, hm.2⟩
  · rw [ite_f hp] at key ⊢
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      obtain ⟨k, hk, hx⟩ := key.2 ⟨h1, h3⟩
      refine ⟨k, hk, ?_, hx⟩
      apply (hLk k hk).2
      unfold InSeq; rw [ite_f (show ¬ (0 : Int) < r.step by omega)]; omega
    · rintro ⟨k, hk, hkL, hx⟩
      have hin := (hLk k hk).1 hkL
      unfold InSeq at hin; rw [ite_f (show ¬ (0 : Int) < r.step by omega)] at hin
      have hm := key.1 ⟨k, hk, hx⟩
      exact ⟨⟨hm.1, by omega⟩, hm.2⟩

theorem elem_inj {r : Range} (hs : r.step ≠ 0) {j k : Int} (h : r.elem j = r.elem k) : j = k := by
  unfold Range.elem at h
  have : (j - k) * r.step = 0 := by rw [Int.sub_mul]; omega
  rcases Int.mul_eq_zero.mp this with h | h
  · omega
  · exact absurd h hs

/-- `r.index(x)` and `r.count(x)` for an int `x` agree with membership:
`index` returns the unique position `k` with `r[k] == x` and raises
`ValueError` exactly for non-members; `count` is 1 for members and 0
otherwise. For all Python ints, `r.WF` being the type invariant. -/
def IndexCount : Prop :=
  ∀ (r : Range) (L x : Int), r.WF → r.Len L →
    (∀ k, rangeIndex r x = .ok k ↔ (0 ≤ k ∧ k < L ∧ r.elem k = x)) ∧
    (rangeIndex r x = .error (.valueError "range.index(x): x not in range") ↔ ¬ r.MemL L x) ∧
    (r.MemL L x → rangeCount r x = 1) ∧ (¬ r.MemL L x → rangeCount r x = 0)

theorem indexCount_proven : IndexCount := by
  intro r L x hw hL
  have hc := containsMem_proven r L x hw hL
  have hs := hw.1
  -- The value `index` returns for a member.
  have hidx : ∀ k, x = r.elem k →
      (if r.step = 1 then (Except.ok (x - r.start) : Py Int) else .ok ((x - r.start) / r.step)) = .ok k := by
    intro k hk
    unfold Range.elem at hk
    split
    · rename_i h1; rw [hk, h1]; congr 1; omega
    · congr 1; rw [hk, show r.start + k * r.step - r.start = k * r.step by omega]
      exact Int.mul_ediv_cancel k hs
  refine ⟨fun k => ?_, ?_, fun hm => ?_, fun hm => ?_⟩
  · unfold rangeIndex
    constructor
    · intro h
      split at h
      · rename_i hin
        obtain ⟨j, hj0, hjL, hj⟩ := hc.1 hin
        rw [hidx j hj] at h
        cases h
        exact ⟨hj0, hjL, hj.symm⟩
      · cases h
    · rintro ⟨hk0, hkL, hk⟩
      have hin : rangeContainsLong r x = true := hc.2 ⟨k, hk0, hkL, hk.symm⟩
      rw [ite_t hin]
      exact hidx k hk.symm
  · unfold rangeIndex
    constructor
    · intro h hm
      rw [ite_t (hc.2 hm)] at h
      split at h <;> cases h
    · intro hm
      have : ¬ rangeContainsLong r x = true := fun h => hm (hc.1 h)
      rw [ite_f this]
  · unfold rangeCount; rw [ite_t (hc.2 hm)]
  · unfold rangeCount
    have : ¬ rangeContainsLong r x = true := fun h => hm (hc.1 h)
    rw [ite_f this]

/-- Range equality compares the sequences: `r0 == r1` exactly when both have
the same length and the same elements, for all Python ints. -/
def EqSameSeq : Prop :=
  ∀ (r0 r1 : Range) (L0 L1 : Int), r0.WF → r1.WF → r0.Len L0 → r1.Len L1 →
    (rangeEquals r0 r1 = true ↔ (L0 = L1 ∧ ∀ k, 0 ≤ k → k < L0 → r0.elem k = r1.elem k))

theorem eqSameSeq_proven : EqSameSeq := by
  intro r0 r1 L0 L1 hw0 hw1 hL0 hL1
  have e0 := hw0.length_eq hL0
  have e1 := hw1.length_eq hL1
  have hnn := hL0.1
  unfold rangeEquals Range.elem
  rw [e0, e1]
  by_cases h01 : L0 = L1
  · subst h01
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, true_and]
    by_cases hz : L0 = 0
    · simp only [hz, beq_self_eq_true, ite_true, true_iff]; intro k hk hk'; omega
    · simp only [beq_iff_eq, hz, ite_false]
      by_cases hst : r0.start = r1.start
      · simp only [hst, bne_self_eq_false, Bool.false_eq_true, ite_false]
        by_cases h1 : L0 = 1
        · simp only [h1, ite_true, true_iff]
          intro k hk hk'
          rw [show k = 0 by omega]; simp
        · simp only [h1, ite_false, beq_iff_eq]
          constructor
          · intro h k _ _; rw [h]
          · intro h
            have := h 1 (by decide) (by omega)
            simp only [Int.one_mul] at this
            omega
      · have : (r0.start != r1.start) = true := by simp [hst]
        simp only [this, ite_true, Bool.false_eq_true, false_iff]
        intro h
        have := h 0 (by decide) (by omega)
        simp at this
        exact hst this
  · have : (L0 != L1) = true := by simp [h01]
    simp only [this, ite_true, Bool.false_eq_true, false_iff, not_and]
    intro h; exact absurd h h01

/-- Equal ranges hash alike: `range_hash` hashes `(len, start, step)` with
`None` for the parts `range_equals` ignores, so `r0 == r1` implies the hashed
tuples are equal (and hence `hash(r0) == hash(r1)`). -/
def EqHashConsistent : Prop :=
  ∀ (r0 r1 : Range), r0.WF → r1.WF → rangeEquals r0 r1 = true → rangeHashKey r0 = rangeHashKey r1

theorem eqHashConsistent_proven : EqHashConsistent := by
  intro r0 r1 _ _ h
  unfold rangeEquals at h
  unfold rangeHashKey
  by_cases hl : r0.length = r1.length
  · rw [hl] at h ⊢
    by_cases hz : r1.length = 0
    · simp [hz]
    · by_cases hs : r0.start = r1.start
      · by_cases h1 : r1.length = 1
        · simp [h1, hs]
        · simp [hz, h1, hs] at h ⊢; exact h
      · simp [hz, hs] at h
  · simp [hl] at h

end PyLean.RangeSlice
