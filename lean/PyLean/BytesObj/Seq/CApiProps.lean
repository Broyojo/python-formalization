import PyLean.BytesObj.Seq.MiscProps
import PyLean.BytesObj.Seq.SliceProps

/-!
Integer indexing and `len`, and the construction entry points of the C API, stated
in full rather than at their edge cases.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α ρ : Type}

/-- `t[i]` and `l[i]` for every int `i`, of any size: both take a negative index from
the end, both return the item at that position, and outside `[-len, len)` both raise
`IndexError`. Inside, the position is in the object, so there is no out-of-bounds
read. `len(t)` and `len(l)` are the `n` of that range. `len <= sys.maxsize` is the
type invariant. -/
def ItemAccess : Prop :=
  ∀ (α : Type) (l : List α) (i : Int), (l.length : Int) ≤ ssizeMax →
    let n : Int := tupleLength l
    let p := if i < 0 then i + n else i
    listLength l = n ∧ n = l.length ∧
    (-n ≤ i ∧ i < n → ∃ v, slot l p = some v ∧ tupleGetItem l i = .ok v ∧ listGetItem l i = .ok v) ∧
    (¬ (-n ≤ i ∧ i < n) → Py.raises (tupleGetItem l i) "IndexError" ∧ Py.raises (listGetItem l i) "IndexError")

theorem subIndex_ok (i : Int) (h : ssizeMin ≤ i ∧ i ≤ ssizeMax) :
    PyLean.Sequences.subIndex i = .ok i := by
  unfold PyLean.Sequences.subIndex PyLean.Sequences.asSsizeExc
  rw [if_pos h]

theorem subIndex_big (i : Int) (h : ¬ (ssizeMin ≤ i ∧ i ≤ ssizeMax)) :
    PyLean.Sequences.subIndex i = .error (.indexError "cannot fit 'int' into an index-sized integer") := by
  unfold PyLean.Sequences.subIndex PyLean.Sequences.asSsizeExc
  rw [if_neg h]

theorem itemAccess_proven : ItemAccess := by
  intro α l i hl n p
  have hn : n = (l.length : Int) := rfl
  have hmax : ssizeMax = 9223372036854775807 := by decide
  have hmin : ssizeMin = -9223372036854775808 := by decide
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro hin
    have hs : ssizeMin ≤ i ∧ i ≤ ssizeMax := by omega
    have hp0 : 0 ≤ p ∧ p < n := by
      simp only [p]
      split <;> omega
    have hlt : p.toNat < l.length := by omega
    have hget : slot l p = some l[p.toNat] := by
      simp [slot, hp0.1, hlt]
    have hv := validIndex_eq p l.length (by omega) (by omega) (by omega) hl
    have hvt : validIndex p l.length = true := by
      rw [hv]
      simp only [decide_eq_true_eq]
      omega
    refine ⟨l[p.toNat], hget, ?_, ?_⟩
    · have hstep : tupleItem l p = .ok l[p.toNat] := by
        unfold tupleItem
        rw [if_neg (by omega), hget]
      simp only [tupleGetItem, subIndex_ok i hs, bind, Except.bind]
      exact hstep
    · have hstep : listItem l p = .ok l[p.toNat] := by
        unfold listItem
        rw [if_neg (by simp [hvt]), hget]
      simp only [listGetItem, subIndex_ok i hs, bind, Except.bind]
      exact hstep
  · intro hout
    by_cases hs : ssizeMin ≤ i ∧ i ≤ ssizeMax
    · have hp : p < 0 ∨ p ≥ n := by
        simp only [p]
        split <;> omega
      have hbad : validIndex p l.length = false := by
        have hv := validIndex_eq p l.length (by simp only [p]; split <;> omega)
          (by simp only [p]; split <;> omega) (by omega) hl
        rw [hv]
        simp only [decide_eq_false_iff_not]
        omega
      constructor
      · refine ⟨.indexError "tuple index out of range", ?_, rfl⟩
        have hstep : tupleItem l p = .error (.indexError "tuple index out of range") := by
          unfold tupleItem
          rw [if_pos (by omega)]
        simp only [tupleGetItem, subIndex_ok i hs, bind, Except.bind]
        exact hstep
      · refine ⟨.indexError "list index out of range", ?_, rfl⟩
        have hstep : listItem l p = .error (.indexError "list index out of range") := by
          unfold listItem
          rw [if_pos (by simp [hbad])]
        simp only [listGetItem, subIndex_ok i hs, bind, Except.bind]
        exact hstep
    · constructor
      · exact ⟨.indexError "cannot fit 'int' into an index-sized integer",
          by simp only [tupleGetItem, subIndex_big i hs, bind, Except.bind], rfl⟩
      · exact ⟨.indexError "cannot fit 'int' into an index-sized integer",
          by simp only [listGetItem, subIndex_big i hs, bind, Except.bind], rfl⟩

/-- The constructors and slice getters of the C API, in full: `PyList_New` and
`PyTuple_New` for every size (`SystemError` when negative, `NULL` slots otherwise);
`_PyList_FromStackRefStealOnSuccess`; `_PyList_AsTupleAndClear`, which moves the items
into a tracked tuple and leaves an empty list with its array; `PyTuple_SetItem` on a uniquely referenced
tuple; `PyList_GetSlice` and `PyTuple_GetSlice`; and the argument checks of
`list_vectorcall`, keywords first. -/
def CApiConstruct : Prop :=
  ∀ (α : Type) (l : List α) (o : LObj α) (n i j : Int) (v : α) (mt : α → Bool) (a b : ExtArg α) (m : Nat),
    (n < 0 → pyListNew n = (.error systemError : Py (LObj (Option α)))) ∧
    (0 < n → n ≤ ssizeMax / 8 →
      pyListNew n = (.ok { items := List.replicate n.toNat none, allocated := n, hasItems := true } :
        Py (LObj (Option α)))) ∧
    (n < 0 → pyTupleNew n = (.error systemError : Py (TRes (Option α)))) ∧
    (0 < n → n ≤ tupleLimit →
      pyTupleNew n = (.ok (.fresh { items := List.replicate n.toNat none, tracked := true }) :
        Py (TRes (Option α)))) ∧
    ((listFromStack l).items = l ∧ (l ≠ [] → (listFromStack l).allocated = l.length)) ∧
    (o.hasItems = false → listAsTupleAndClear o = .ok (.empty, o)) ∧
    (o.hasItems = true → o.items ≠ [] → (o.items.length : Int) ≤ tupleLimit →
      listAsTupleAndClear o =
        .ok (.fresh { items := o.items, tracked := true }, { o with items := [] })) ∧
    (0 ≤ i → i < l.length → pyTupleSetItem (some l) true i v = .ok (l.set i.toNat v)) ∧
    ((i < 0 ∨ i ≥ l.length) →
      pyTupleSetItem (some l) true i v = .error (.indexError "tuple assignment index out of range")) ∧
    (pyListGetSlice (none : Option (List α)) i j = .error systemError) ∧
    (pyTupleGetSlice mt (none : Option (Tup α)) i j = .error systemError) ∧
    (∀ t : Tup α, pyTupleGetSlice mt (some t) i j = tupleSlice mt t i j) ∧
    (0 ≤ i → i ≤ j → j ≤ l.length →
      (pyListGetSlice (some l) i j).map LObj.items = .ok ((l.drop i.toNat).take (j - i).toNat)) ∧
    (listVectorcall ([] : List (ExtArg α)) 0 = .ok LObj.empty) ∧
    (listVectorcall [a] (m + 1) = .error (.typeError "list() takes no keyword arguments")) ∧
    (listVectorcall [a, b] 0 = .error (.typeError "list expected at most 1 argument, got 2"))

theorem cApiConstruct_proven : CApiConstruct := by
  intro α l o n i j v mt a b m
  refine ⟨?_, ?_, ?_, ?_, ⟨by simp [listFromStack], ?_⟩, ?_, ?_, ?_, ?_, rfl, rfl, fun _ => rfl, ?_,
    rfl, ?_, ?_⟩
  · intro h
    unfold pyListNew
    rw [if_pos h]
  · intro h0 h1
    unfold pyListNew
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · intro h
    unfold pyTupleNew
    rw [if_neg (by omega), tupleAlloc_neg n h]
  · intro h0 h1
    unfold pyTupleNew
    rw [if_neg (by omega), tupleAlloc_ok n (by omega) h1]
  · intro h
    have h0 : l.length ≠ 0 := fun hz => h (List.length_eq_zero_iff.mp hz)
    simp [listFromStack, LObj.prealloc, h0]
  · intro h
    simp [listAsTupleAndClear, h]
  · intro h1 h2 h3
    have h0 : o.items.length ≠ 0 := fun hz => h2 (List.length_eq_zero_iff.mp hz)
    have hal := tupleAlloc_ok (o.items.length : Int) (by omega) h3
    unfold listAsTupleAndClear
    simp only [h1, Bool.not_true, Bool.false_eq_true, if_false]
    have hs : tupleFromArraySteal o.items = .ok (.fresh { items := o.items, tracked := true }) := by
      unfold tupleFromArraySteal
      rw [if_neg h0, hal]
    rw [hs]
  · intro h0 h1
    simp only [pyTupleSetItem, Bool.not_true, Bool.false_eq_true, if_false]
    rw [if_neg (by omega)]
  · intro h
    simp only [pyTupleSetItem, Bool.not_true, Bool.false_eq_true, if_false]
    rw [if_pos h]
  · intro h0 h1 h2
    simp only [pyListGetSlice]
    have c1 : ¬ i < 0 := by omega
    have c2 : ¬ i > (l.length : Int) := by omega
    have c3 : ¬ j < i := by omega
    have c4 : ¬ j > (l.length : Int) := by omega
    simp only [c1, c2, c3, c4, if_false]
    show Except.ok (listSliceLH l i j).items = _
    unfold listSliceLH
    simp only
    by_cases h3 : j - i ≤ 0
    · rw [if_pos h3]
      have hz : (j - i).toNat = 0 := by omega
      simp [hz, LObj.empty]
    · rw [if_neg h3, prealloc_items]
  · simp [listVectorcall]
  · simp [listVectorcall]
    rfl

end PyLean.BytesObj.Seq
