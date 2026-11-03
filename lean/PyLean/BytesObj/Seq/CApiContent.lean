import PyLean.BytesObj.Seq.CApiProps
import PyLean.BytesObj.Seq.ContentProps

/-!
The C API entry points, by what they do to the contents rather than by the function they call.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α ρ : Type}

/-- `list_ass_slice` on a range in bounds: the items before it, the new items, the items after. -/
theorem listAssSlice_content (o o' : LObj α) (i j : Int) (vs : List α) (hw : o.WF) (h0 : 0 ≤ i) (h1 : i ≤ j)
    (h2 : j ≤ o.items.length) (h : listAssSlice o i j (some vs) = .ok o') :
    o'.items = o.items.take i.toNat ++ vs ++ o.items.drop j.toNat := by
  unfold listAssSlice at h
  have c1 : ¬ i < 0 := by omega
  have c2 : ¬ i > (o.items.length : Int) := by omega
  have c3 : ¬ j < i := by omega
  have c4 : ¬ j > (o.items.length : Int) := by omega
  simp only [Option.getD_some, c1, c2, c3, c4, if_false] at h
  by_cases hz : (o.items.length : Int) + ((vs.length : Int) - (j - i)) = 0
  · rw [if_pos hz] at h
    simp only [Except.ok.injEq] at h
    have hv : vs = [] := List.length_eq_zero_iff.mp (by omega)
    have hi : i.toNat = 0 := by omega
    have hd : o.items.drop j.toNat = [] := List.drop_eq_nil_of_le (by omega)
    rw [← h, listClear_items o hw, hv, hi, hd]
    simp
  · rw [if_neg hz] at h
    by_cases hd : (vs.length : Int) - (j - i) = 0
    · rw [if_pos hd] at h
      simp only [Except.ok.injEq] at h
      rw [← h]
    · rw [if_neg hd] at h
      exact (resizeTo_wf hw h).2

/-- The C API of `list` and `tuple`, for every argument, by what each entry point does. Each one
refuses an object of another type with its own error (`NULL`, modelled as `none`). `PyList_GetItem`
and `PyTuple_GetItem` take no negative index, unlike `l[i]`, and `PyList_SetItem` likewise. `PyList_Insert`
clips like `l.insert`; `PyList_SetSlice` replaces the range; `PyList_Clear`, `PyList_Reverse`,
`PyList_AsTuple` and `PyList_Extend` act on the contents. Hypotheses: a list satisfying its layout
invariant (`LObj.WF`, proven of every method by `ListOpsWF`), `len <= sys.maxsize`, and indices a
`Py_ssize_t` holds. A successful result is what is described; `MemoryError` is the other outcome. -/
def CApiAgree : Prop :=
  ∀ (α : Type) (l : List α) (o o' : LObj α) (t : List (Option α)) (i j k : Int) (v : α) (w : List α)
    (mt : α → Bool),
    o.WF → (l.length : Int) ≤ ssizeMax → (o.items.length : Int) ≤ ssizeMax → ssizeMin ≤ i → i ≤ ssizeMax →
    (pyTupleSize (some l) = .ok l.length ∧ pyTupleSize (none : Option (List α)) = .error systemError) ∧
    (pyListSize (some l) = .ok l.length ∧ pyListSize (none : Option (List α)) = .error systemError) ∧
    (0 ≤ i → i < l.length → ∃ x, slot l i = some x ∧ pyTupleGetItem (some l) i = .ok x ∧
      pyListGetItem (some l) i = .ok x ∧ pyListGetItemRef (some l) i = .ok x) ∧
    ((i < 0 ∨ i ≥ l.length) →
      pyTupleGetItem (some l) i = .error (.indexError "tuple index out of range") ∧
      pyListGetItem (some l) i = .error (.indexError "list index out of range") ∧
      pyListGetItemRef (some l) i = .error (.indexError "list index out of range")) ∧
    (pyTupleGetItem (none : Option (List α)) i = .error systemError ∧
      pyListGetItem (none : Option (List α)) i = .error systemError ∧
      pyListGetItemRef (none : Option (List α)) i = .error (.typeError "expected a list")) ∧
    (0 ≤ i → i < o.items.length → ∃ x, pyListSetItem (some o) i v = .ok x ∧ x.items = o.items.set i.toNat v ∧
      x.allocated = o.allocated) ∧
    ((i < 0 ∨ i ≥ o.items.length) →
      pyListSetItem (some o) i v = .error (.indexError "list assignment index out of range")) ∧
    (pyListInsert (some o) i (some v) = .ok o' →
      o'.items = o.items.take (ins1Where o.items.length i).toNat ++ v :: o.items.drop (ins1Where o.items.length i).toNat) ∧
    pyListInsert (some o) i none = .error systemError ∧
    (pyListAppend (some o) (some v) = .ok o' → o'.items = o.items ++ [v]) ∧
    pyListAppend (some o) none = .error systemError ∧
    (0 ≤ j → j ≤ k → k ≤ o.items.length →
      (pyListSetSlice (some o) j k (.seq w) = .ok o' →
        o'.items = o.items.take j.toNat ++ w ++ o.items.drop k.toNat) ∧
      (pyListSetSlice (some o) j k .selfCopy = .ok o' →
        o'.items = o.items.take j.toNat ++ o.items ++ o.items.drop k.toNat)) ∧
    (pyListClear (some o) = .ok o' → o'.items = []) ∧
    (pyListReverse (some o) = .ok o' → o'.items = o.items.reverse) ∧
    (l ≠ [] → (l.length : Int) ≤ tupleLimit →
      pyListAsTuple mt (some l) = .ok (.fresh { items := l, tracked := l.any mt })) ∧
    pyListAsTuple mt (none : Option (List α)) = .error systemError ∧
    (∀ r, pyListExtend (some o) (.fast l) = ((o', none), r) → o'.items = o.items ++ l) ∧
    pyTupleSetItem (some l) false i v = .error systemError ∧
    (∀ (n : Int), 0 < n → t ≠ [] → n ≤ tupleLimit →
      tupleResize (some t) true true n = .ok (t.take n.toNat ++ List.replicate (n - t.length).toNat none)) ∧
    (∀ (n : Int), n > tupleLimit → t ≠ [] → (t.length : Int) ≠ n →
      tupleResize (some t) true true n = .error memoryError) ∧
    (∀ (n : Int), n < 0 → tupleResize (some t) true true n = .error systemError)

theorem cApiAgree_proven : CApiAgree := by
  intro α l o o' t i j k v w mt hw hl hol hi0 hi1
  have hmax : ssizeMax = 9223372036854775807 := by decide
  have hmin : ssizeMin = -9223372036854775808 := by decide
  have hC := listContents_proven α o o' [] [] [] v i "" hw
  obtain ⟨c1, c2, -, -, c5, -⟩ := hC
  have hE : ∀ o2, listExtendFast o l = .ok o2 → o2.items = o.items ++ l := fun o2 h => by
    have hC2 := listContents_proven α o o2 [] [] l v i "" hw
    exact hC2.2.2.2.2.2.1 h
  have hv : ∀ n : Int, 0 ≤ n → n ≤ ssizeMax → validIndex i n = decide (0 ≤ i ∧ i < n) := by
    intro n h0 h1
    exact validIndex_eq i n (by have : (2 : Int) ^ 63 = 9223372036854775808 := by decide
                                omega)
      (by have : (2 : Int) ^ 63 = 9223372036854775808 := by decide
          omega) h0 h1
  have hl0 : (0 : Int) ≤ l.length := by omega
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, fun h0 h1 => ?_, fun h => ?_, ⟨rfl, rfl, rfl⟩, fun h0 h1 => ?_, fun h => ?_,
    fun h => c2 h, rfl, fun h => c1 h, rfl, fun h0 h1 h2 => ⟨fun h => ?_, fun h => ?_⟩, fun h => ?_, fun h => ?_,
    fun h0 h1 => ?_, rfl, fun r h => ?_, rfl, fun n h0 hnil hlim => ?_, fun n h1 hnil hne => ?_,
    fun n h => ?_⟩
  · have hlt : i.toNat < l.length := by omega
    have hs : slot l i = some l[i.toNat] := by simp [slot, h0, hlt]
    have hb : validIndex i l.length = true := by
      rw [hv _ hl0 hl]
      simp only [decide_eq_true_eq]
      omega
    refine ⟨l[i.toNat], hs, ?_, ?_, ?_⟩
    · simp only [pyTupleGetItem]
      rw [if_neg (by omega), hs]
    · simp only [pyListGetItem, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hs]
    · simp only [pyListGetItemRef, listGetItemRef, hb, ↓reduceIte, hs]
  · have hb : validIndex i l.length = false := by
      rw [hv _ hl0 hl]
      simp only [decide_eq_false_iff_not]
      omega
    refine ⟨?_, ?_, ?_⟩
    · simp only [pyTupleGetItem]
      rw [if_pos h]
    · simp only [pyListGetItem, hb, Bool.not_false, ↓reduceIte]
    · simp only [pyListGetItemRef, listGetItemRef, hb, Bool.false_eq_true, ↓reduceIte]
  · have hb : validIndex i o.items.length = true := by
      rw [hv _ (by omega) hol]
      simp only [decide_eq_true_eq]
      omega
    refine ⟨{ o with items := o.items.set i.toNat v }, ?_, rfl, rfl⟩
    simp only [pyListSetItem, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · have hb : validIndex i o.items.length = false := by
      rw [hv _ (by omega) hol]
      simp only [decide_eq_false_iff_not]
      omega
    simp only [pyListSetItem, hb, Bool.not_false, ↓reduceIte]
  · exact listAssSlice_content o o' j k w hw h0 h1 h2 h
  · exact listAssSlice_content o o' j k o.items hw h0 h1 h2 h
  · simp only [pyListClear, Except.ok.injEq] at h
    rw [← h]
    exact listClear_items o hw
  · simp only [pyListReverse, Except.ok.injEq] at h
    rw [← h]
    exact c5
  · have h0' : l.length ≠ 0 := fun hz => h0 (List.length_eq_zero_iff.mp hz)
    simp only [pyListAsTuple, tupleFromArray, h0', ↓reduceIte, tupleAlloc_ok (l.length : Int) (by omega) h1]
  · simp only [pyListExtend, Prod.mk.injEq] at h
    obtain ⟨h1, -⟩ := h
    simp only [listExtend, liftRes] at h1
    cases hr : listExtendFast o l with
    | error e => simp [hr] at h1
    | ok o2 =>
      simp only [hr, Prod.mk.injEq] at h1
      rw [← h1.1]
      exact hE o2 hr
  · have hlen : t.length ≠ 0 := fun h => hnil (List.length_eq_zero_iff.mp h)
    have hn0 : ¬ n = 0 := by omega
    have ho0 : ¬ (t.length : Int) = 0 := by omega
    have hneg : ¬ n < 0 := by omega
    unfold tupleResize
    simp only [Bool.not_true, Bool.false_eq_true, Bool.false_or, Bool.and_false, Bool.or_false,
      hneg, decide_false, if_false]
    by_cases heq : (t.length : Int) = n
    · rw [if_pos heq]
      have h1 : n.toNat = t.length := by omega
      have h2 : (n - (t.length : Int)).toNat = 0 := by omega
      simp [h1, h2]
    · rw [if_neg heq, if_neg hn0, if_neg ho0, if_neg (by unfold tupleLimit at hlim; omega)]
  · have hlen : t.length ≠ 0 := fun h => hnil (List.length_eq_zero_iff.mp h)
    have hpos : 0 < tupleLimit := by decide
    have hn0 : ¬ n = 0 := by omega
    have ho0 : ¬ (t.length : Int) = 0 := by omega
    have hneg : ¬ n < 0 := by omega
    unfold tupleResize
    simp only [Bool.not_true, Bool.false_eq_true, Bool.false_or, Bool.and_false, Bool.or_false,
      hneg, decide_false, if_false]
    rw [if_neg hne, if_neg hn0, if_neg ho0, if_pos (by unfold tupleLimit at h1; omega)]
  · simp [tupleResize, h]

end PyLean.BytesObj.Seq
