import PyLean.Sequences.Insert

/-!
`array.array` range checks: storing an int raises `OverflowError` exactly
when it does not fit the typecode.
-/

namespace PyLean.Sequences

open PyLean

theorem tcSetitem_range (tc : TC) (v : Int) :
    (tc.lo ≤ v ∧ v ≤ tc.hi → tcSetitem tc true v = .ok v) ∧
    (¬ (tc.lo ≤ v ∧ v ≤ tc.hi) → (tcSetitem tc true v).raises "OverflowError") := by
  refine ⟨fun h => tcSetitem_ok tc v h.1 h.2, fun h => ?_⟩
  by_cases hl : -9223372036854775808 ≤ v ∧ v ≤ 9223372036854775807
  · have hal : asLong v = .ok v := by unfold asLong; rw [iteT hl]
    cases tc <;> simp only [TC.lo, TC.hi] at h <;>
      simp only [tcSetitem, hal, bind, Except.bind, pure, Except.pure, Bool.not_true, Bool.false_eq_true,
        ite_false]
    · by_cases h1 : v < -32768
      · rw [iteT h1]; exact ⟨_, rfl, rfl⟩
      rw [iteF h1]
      by_cases h2 : v > 32767
      · rw [iteT h2]; exact ⟨_, rfl, rfl⟩
      rw [iteF h2]
      by_cases h3 : v < -128
      · rw [iteT h3]; exact ⟨_, rfl, rfl⟩
      rw [iteF h3, iteT (show v > 127 by omega)]; exact ⟨_, rfl, rfl⟩
    · by_cases h1 : v < 0
      · rw [iteT h1]; exact ⟨_, rfl, rfl⟩
      rw [iteF h1, iteT (show v > 255 by omega)]; exact ⟨_, rfl, rfl⟩
    · by_cases h1 : v < -32768
      · rw [iteT h1]; exact ⟨_, rfl, rfl⟩
      rw [iteF h1, iteT (show v > 32767 by omega)]; exact ⟨_, rfl, rfl⟩
    · by_cases h1 : v > 2147483647
      · rw [iteT h1]; exact ⟨_, rfl, rfl⟩
      rw [iteF h1, iteT (show v < -2147483648 by omega)]; exact ⟨_, rfl, rfl⟩
    · exact absurd hl h
  · have hal : asLong v = .error longOverflow := by unfold asLong; rw [iteF hl]
    cases tc <;> simp only [tcSetitem, hal, bind, Except.bind]
    all_goals (try exact ⟨_, rfl, rfl⟩)
    rw [iteT hl]; exact ⟨_, rfl, rfl⟩

/-- For every array (type invariant `Arr.WF`: items fit the typecode), every
int `v` and index `i`: `a.append(v)`, `a.insert(i, v)` (`i` inside
`Py_ssize_t`), `a[j] = v` (valid index `j`; `len(a) <= sys.maxsize` is a type invariant) and `array(tc, xs)` succeed and
store exactly `v` when `v` fits the typecode's C range
(`'b'`: [-128, 127], `'B'`: [0, 255], `'h'`: 16-bit, `'i'`: 32-bit, `'q'`:
64-bit signed), and raise `OverflowError` (leaving the array unchanged)
otherwise; the result again satisfies the invariant. -/
def ArrayRangeCheck : Prop :=
  ∀ (a : Arr) (v i : Int), a.WF → (a.items.length : Int) ≤ ssizeMax →
    let fits := a.tc.lo ≤ v ∧ v ≤ a.tc.hi
    (fits → arrAppend a v = .ok ⟨a.tc, a.items ++ [v]⟩ ∧ (⟨a.tc, a.items ++ [v]⟩ : Arr).WF) ∧
    (¬ fits → (arrAppend a v).raises "OverflowError") ∧
    (ssizeMin ≤ i → i ≤ ssizeMax →
      (fits → ∃ a', arrInsert a i v = .ok a' ∧ a'.WF ∧ v ∈ a'.items) ∧
      (¬ fits → (arrInsert a i v).raises "OverflowError")) ∧
    (0 ≤ i → i < a.items.length →
      (fits → arrAssSubscr a (.inl i) (some [v]) = .ok ⟨a.tc, a.items.set i.toNat v⟩) ∧
      (¬ fits → (arrAssSubscr a (.inl i) (some [v])).raises "OverflowError")) ∧
    (∀ xs : List Int, (∀ x ∈ xs, a.tc.lo ≤ x ∧ x ≤ a.tc.hi) → arrNew a.tc xs = .ok ⟨a.tc, xs⟩) ∧
    (∀ xs : List Int, (∃ x ∈ xs, ¬ (a.tc.lo ≤ x ∧ x ≤ a.tc.hi)) → (arrNew a.tc xs).raises "OverflowError")

theorem mapM_tcSetitem_ok (tc : TC) (xs : List Int) (h : ∀ x ∈ xs, tc.lo ≤ x ∧ x ≤ tc.hi) :
    xs.mapM (tcSetitem tc true) = .ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, (tcSetitem_range tc x).1 (h x (by simp))]
    simp only [bind, Except.bind]
    rw [ih (fun y hy => h y (by simp [hy]))]
    rfl

theorem mapM_tcSetitem_err (tc : TC) (xs : List Int) (h : ∃ x ∈ xs, ¬ (tc.lo ≤ x ∧ x ≤ tc.hi)) :
    (xs.mapM (tcSetitem tc true)).raises "OverflowError" := by
  induction xs with
  | nil => obtain ⟨x, hx, _⟩ := h; simp at hx
  | cons x xs ih =>
    rw [List.mapM_cons]
    by_cases hx : tc.lo ≤ x ∧ x ≤ tc.hi
    · rw [(tcSetitem_range tc x).1 hx]
      simp only [bind, Except.bind]
      have h' : ∃ y ∈ xs, ¬ (tc.lo ≤ y ∧ y ≤ tc.hi) := by
        obtain ⟨y, hy, hny⟩ := h
        rcases List.mem_cons.mp hy with e | e
        · subst e; exact absurd hx hny
        · exact ⟨y, e, hny⟩
      obtain ⟨e, he, hc⟩ := ih h'
      rw [he]; exact ⟨e, rfl, hc⟩
    · obtain ⟨e, he, hc⟩ := (tcSetitem_range tc x).2 hx
      rw [he]; exact ⟨e, rfl, hc⟩

theorem arrayRangeCheck_proven : ArrayRangeCheck := by
  intro a v i hwf hlen
  dsimp only
  have hok := (tcSetitem_range a.tc v).1
  have herr := (tcSetitem_range a.tc v).2
  have hwf' : ∀ fits : a.tc.lo ≤ v ∧ v ≤ a.tc.hi, ∀ p : Nat, (⟨a.tc, insAt a.items p v⟩ : Arr).WF := by
    intro fits p x hx
    unfold insAt at hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | hx | hx
    · exact hwf x (List.mem_of_mem_take hx)
    · subst hx; exact fits
    · exact hwf x (List.mem_of_mem_drop hx)
  refine ⟨fun fits => ⟨?_, ?_⟩, fun nf => ?_, fun hi0 hi1 => ⟨fun fits => ?_, fun nf => ?_⟩,
    fun hi0 hi1 => ⟨fun fits => ?_, fun nf => ?_⟩, fun xs hxs => ?_, fun xs hxs => ?_⟩
  · simp only [arrAppend, arrIns1, hok fits, bind, Except.bind, pure, Except.pure]
    unfold ins1Pos insAt
    simp only [show ¬ ((a.items.length : Int) < 0) by omega, ite_false, gt_iff_lt, Int.lt_irrefl,
      show ((a.items.length : Int)).toNat = a.items.length by omega, List.take_length, List.drop_length]
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact hwf x hx
    · subst hx; exact fits
  · obtain ⟨e, he, hc⟩ := herr nf
    simp only [arrAppend, arrIns1, he, bind, Except.bind]
    exact ⟨e, rfl, hc⟩
  · simp only [arrInsert, asSsize, bind, Except.bind]
    rw [iteT ⟨hi0, hi1⟩]
    simp only [arrIns1, hok fits, pure, Except.pure]
    refine ⟨_, rfl, hwf' fits _, ?_⟩
    simp [insAt]
  · simp only [arrInsert, asSsize, bind, Except.bind]
    rw [iteT ⟨hi0, hi1⟩]
    obtain ⟨e, he, hc⟩ := herr nf
    simp only [arrIns1, he]
    exact ⟨e, rfl, hc⟩
  · simp only [arrAssSubscr, subIndex, asSsizeExc, bind, Except.bind]
    rw [iteT ⟨by unfold ssizeMin; omega, by omega⟩]
    simp only [pure, Except.pure]
    rw [iteF (show ¬ i < 0 by omega), iteF (show ¬ (i < 0 ∨ i ≥ (a.items.length : Int)) by omega)]
    simp only [hok fits]
    rfl
  · simp only [arrAssSubscr, subIndex, asSsizeExc, bind, Except.bind]
    rw [iteT ⟨by unfold ssizeMin; omega, by omega⟩]
    simp only [pure, Except.pure]
    rw [iteF (show ¬ i < 0 by omega), iteF (show ¬ (i < 0 ∨ i ≥ (a.items.length : Int)) by omega)]
    obtain ⟨e, he, hc⟩ := herr nf
    simp only [he]
    exact ⟨e, rfl, hc⟩
  · simp only [arrNew, mapM_tcSetitem_ok a.tc xs hxs, bind, Except.bind, pure, Except.pure]
  · obtain ⟨e, he, hc⟩ := mapM_tcSetitem_err a.tc xs hxs
    simp only [arrNew, he, bind, Except.bind]
    exact ⟨e, rfl, hc⟩

end PyLean.Sequences
