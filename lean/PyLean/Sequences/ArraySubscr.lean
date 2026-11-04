import PyLean.Sequences.ArrayLimits
import PyLean.Sequences.SliceAssign

/-!
`array.array`: `a[s]` for a slice (the `memcpy` path for step 1 and the `size_t` cursor
loop), the key dispatch of `array_subscr`, `tolist` against `a[i]`, and the checks of
`a[s] = value` before anything is changed.
-/

namespace PyLean.Sequences

open PyLean
open PyLean.RangeSlice

set_option linter.unusedSectionVars false

/-- `a[s]` for every array (`len(a)` fits) and every slice: a zero step raises `ValueError`
(from `PySlice_Unpack`); otherwise the result is a new `array.array` of the same typecode
holding the items at `start + k*step` for the `start`, `step` and length `slice.indices` gives,
both through the step-1 `memcpy` (arraymodule.c:2753-2758) and through the `size_t` cursor
loop (:2760-2781). The other keys: an `__index__` key is `a[i]`, anything else but a slice is
`TypeError("array indices must be integers")` (:2787-2790). -/
def ArrayGetSlice : Prop :=
  ∀ (a : Arr), a.Fits a.items.length →
    (∀ s : Slice, s.step ≠ some 0 →
      ∃ start stop step L, sliceIndices s a.items.length = .ok (start, stop, step) ∧ IsLen start stop step L ∧
        ∃ r, arrGetSlice a s = .ok r ∧
          r.items = (List.range L.toNat).map (fun (k : Nat) => ix a.items (start + (k : Int) * step)) ∧
          r.tc = a.tc ∧ r.tname = "array" ∧ r.exports = 0) ∧
    (∀ s : Slice, s.step = some 0 → (arrGetSlice a s).raises "ValueError") ∧
    (∀ i, arrSubscr a (.int i) = Sum.inl <$> arrGetItem a i) ∧
    arrSubscr a .other = .error (.typeError "array indices must be integers")

theorem len_le_n (a b c n L : Int) (hL : IsLen a b c L) (hb : Bnds a b c n) (hc : c ≠ 0) : L ≤ n := by
  have h0 := hL.1
  by_cases hz : L = 0
  · have : 0 ≤ n := by
      rcases Int.lt_or_gt_of_ne hc with h | h
      · have := hb.2 h; omega
      · have := hb.1 h; omega
    omega
  · have hfirst := indices_in_bounds a b c n L hL hb 0 (by omega) (by omega)
    have hlast := indices_in_bounds a b c n L hL hb (L - 1) (by omega) (by omega)
    rcases Int.lt_or_gt_of_ne hc with h | h
    · have : (L - 1) * c ≤ (L - 1) * (-1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have := hb.2 h
      omega
    · have : (L - 1) * 1 ≤ (L - 1) * c := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega

theorem arrayGetSlice_proven : ArrayGetSlice := by
  intro a hf
  have hn' : (a.items.length : Int) ≤ ssizeMax := fits_ssize a _ hf
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun i => rfl, rfl⟩
  · obtain ⟨st0, sp0, c, L, st, sp, c', hsi, hlen, hb, _, hun, hadj, h1, _, hc0, _, hpos⟩ :=
      adjust_spec s a.items.length (by omega) hn' hs
    refine ⟨st0, sp0, c, L, hsi, hlen, ?_⟩
    have hLn := len_le_n st0 sp0 c a.items.length L hlen hb hc0
    have hL0 := hlen.1
    unfold arrGetSlice
    simp only [hun, bind, Except.bind, pure, Except.pure]
    rw [hadj]
    simp only
    by_cases hz : L ≤ 0
    · rw [iteT hz, newArr_ok _ _ _ (by unfold Arr.Fits at hf; omega)]
      refine ⟨_, rfl, ?_, rfl, rfl, rfl⟩
      rw [show L.toNat = 0 by omega]
      simp
    · rw [iteF hz, newArr_ok _ _ L (by unfold Arr.Fits at hf; omega)]
      simp only
      by_cases hs1 : c' = 1
      · rw [iteT hs1]
        have hc1 : c = 1 := h1.mp hs1
        refine ⟨_, rfl, ?_, rfl, rfl, rfl⟩
        have hend := indices_in_bounds st0 sp0 c a.items.length L hlen hb (L - 1) (by omega) (by omega)
        have hst := indices_in_bounds st0 sp0 c a.items.length L hlen hb 0 (by omega) (by omega)
        rw [hc1] at hend hst
        apply List.ext_getElem
        · simp only [List.length_take, List.length_drop, List.length_map, List.length_range]
          omega
        · intro k hk1 hk2
          simp only [List.length_map, List.length_range] at hk2
          simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range, hc1,
            Int.mul_one]
          rw [show st0 + (k : Int) = ((st0.toNat + k : Nat) : Int) by omega,
            ix_getElem _ _ (by omega)]
      · rw [iteF hs1]
        refine ⟨_, rfl, ?_, rfl, rfl, rfl⟩
        apply List.map_congr_left
        intro k hk
        rw [List.mem_range] at hk
        rw [hpos k (by omega) (by omega)]
  · obtain ⟨e, he, hc⟩ : (sliceUnpack s).raises "ValueError" := by
      unfold sliceUnpack
      simp only [hs, bind, Except.bind]
      exact ⟨_, rfl, rfl⟩
    unfold arrGetSlice
    simp only [he, bind, Except.bind]
    exact ⟨e, rfl, hc⟩

/-- `a.tolist()` is `[a[0], ..., a[len(a)-1]]` for every array and typecode (floats and
complex numbers through their getitem's C conversion, characters through
`PyUnicode_FromOrdinal`), reading in order: the first item that does not read (a `u`/`w`
value outside `[0, 0x10FFFF]`, arraymodule.c:1902-1903) raises its `ValueError`. -/
def ArrayToList : Prop :=
  ∀ a : Arr, arrToList a = (List.range a.items.length).mapM (fun (i : Nat) => arrItem a i)

theorem mapM_range_item (a : Arr) :
    ∀ (pre l : List Int), a.items = pre ++ l →
      l.mapM (tcGetitem a.tc) = (List.range' pre.length l.length).mapM (fun (i : Nat) => arrItem a i) := by
  intro pre l
  induction l generalizing pre with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    rw [List.length_cons, List.range'_succ, List.mapM_cons, List.mapM_cons]
    have hi : arrItem a pre.length = tcGetitem a.tc x := by
      rw [arrItem_eq, iteT ⟨by omega, by rw [h]; simp <;> omega⟩]
      unfold Arr.get
      rw [h, show ((pre.length : Nat) : Int) = ((pre.length : Nat) : Int) from rfl,
        ix_getElem _ _ (by simp)]
      simp
    rw [hi, ih (pre ++ [x]) (by rw [h]; simp)]
    simp

theorem arrayToList_proven : ArrayToList := by
  intro a
  unfold arrToList
  rw [mapM_range_item a [] a.items (by simp), List.range_eq_range']
  rfl

/-- What `a[s] = value` checks, in order, for every array and slice: the slice is unpacked
first (a zero step is `ValueError` whatever the value); then a value that is not an array is
`TypeError("can only assign array (not \"T\") to array slice")`; `a[s] = a` is the assignment of a
copy of `a` (arraymodule.c:2843-2851); an array of another typecode is `TypeError` from
`PyErr_BadArgument` (:2853-2856); and while a buffer is exported, an assignment that would
change the size (or delete) raises `BufferError` before the array is touched (:2872-2878). -/
def ArrayAssSliceChecks : Prop :=
  ∀ (a : Arr) (s : Slice), a.Fits a.items.length →
    (s.step = some 0 → ∀ v, (arrAssSlice a s v).raises "ValueError") ∧
    (s.step ≠ some 0 →
      (∀ t, arrAssSlice a s (.other t) =
        .error (.typeError s!"can only assign array (not \"{t}\") to array slice")) ∧
      (∀ c, arrCopy a = .ok c → arrAssSlice a s (.arr a true) = arrAssSlice a s (.arr c false)) ∧
      (∀ o : Arr, o.tc ≠ a.tc → arrAssSlice a s (.arr o false) =
        .error (.typeError "bad argument type for built-in operation")) ∧
      (a.exports > 0 → ∀ st sp c', sliceUnpack s = .ok (st, sp, c') →
        arrAssSlice a s .delete = .error bufferErr ∧
        ∀ o : Arr, o.tc = a.tc →
          ((o.items.length : Int) = 0 ∨ (adjustIndices a.items.length st sp c').2.2 ≠ o.items.length) →
          arrAssSlice a s (.arr o false) = .error bufferErr))

theorem arrayAssSliceChecks_proven : ArrayAssSliceChecks := by
  intro a s hf
  refine ⟨fun hs v => ?_, fun hs => ⟨fun t => ?_, fun c hc => ?_, fun o ho => ?_, fun hx => ?_⟩⟩
  · obtain ⟨e, he, hcls⟩ : (sliceUnpack s).raises "ValueError" := by
      unfold sliceUnpack
      simp only [hs, bind, Except.bind]
      exact ⟨_, rfl, rfl⟩
    unfold arrAssSlice
    simp only [he, bind, Except.bind]
    exact ⟨e, rfl, hcls⟩
  · obtain ⟨st, sp, c', hun⟩ : ∃ st sp c', sliceUnpack s = .ok (st, sp, c') := by
      obtain ⟨_, _, _, _, st, sp, c', _, _, _, _, hun, _⟩ := adjust_spec s 0 (by omega) (by decide) hs
      exact ⟨st, sp, c', hun⟩
    unfold arrAssSlice
    simp only [hun, bind, Except.bind]
    rfl
  · obtain ⟨st, sp, c', hun⟩ : ∃ st sp c', sliceUnpack s = .ok (st, sp, c') := by
      obtain ⟨_, _, _, _, st, sp, c', _, _, _, _, hun, _⟩ := adjust_spec s 0 (by omega) (by decide) hs
      exact ⟨st, sp, c', hun⟩
    have hci : c.items = a.items ∧ c.tc = a.tc := by
      obtain ⟨c2, h1, h2, h3, _⟩ := (arrayClearCopy_proven a hf).2.2.1
      rw [h1] at hc
      injection hc with hc
      subst hc
      exact ⟨h2, h3⟩
    unfold arrAssSlice
    simp only [hun, bind, Except.bind, hci.1, hci.2, ne_eq, not_true_eq_false, and_false, ite_false,
      Bool.not_true, Bool.false_eq_true, false_and, decide_true, not_false_eq_true, true_and, and_true]
    all_goals rfl
  · obtain ⟨st, sp, c', hun⟩ : ∃ st sp c', sliceUnpack s = .ok (st, sp, c') := by
      obtain ⟨_, _, _, _, st, sp, c', _, _, _, _, hun, _⟩ := adjust_spec s 0 (by omega) (by decide) hs
      exact ⟨st, sp, c', hun⟩
    unfold arrAssSlice
    simp only [hun, bind, Except.bind]
    rw [iteT ⟨by decide, ho⟩]
    rfl
  · intro st sp c' hun
    refine ⟨?_, fun o ho hsz => ?_⟩
    · unfold arrAssSlice
      simp only [hun, bind, Except.bind]
      unfold arrAssCore
      simp only [bind, Except.bind, pure, Except.pure, throwE, Option.getD_none]
      rw [iteT ⟨by simp, hx⟩]
    · unfold arrAssSlice
      simp only [hun, bind, Except.bind]
      rw [iteF (by simp [ho])]
      unfold arrAssCore
      simp only [bind, Except.bind, pure, Except.pure, throwE, Option.getD_some]
      rw [iteT ⟨by omega, hx⟩]

/-- `typecode_to_mformat_code` (arraymodule.c:2138-2233) on a little-endian machine agrees with
the descriptor table it is derived from: for every typecode but `u` and `w`, the machine format's
row of `mformat_descriptors` (:2096-2129) has the typecode's item size, is signed exactly for the
signed integer typecodes, and is little-endian; every code (`u` and `w` included) is inside
`MACHINE_FORMAT_CODE_MIN..MAX` and names a little-endian row. (For `u` and `w` the code is `UTF32_LE`, whose row
says 8 bytes: bugs/sequences-array-mformat-utf-sizes.yaml.) -/
def ArrayMformatTable : Prop :=
  ∀ tc : TC, 0 ≤ mformatOf tc ∧ mformatOf tc ≤ 27 ∧ (mformatDescr (mformatOf tc)).2.2 = false ∧
    (tc ≠ .u → tc ≠ .w →
      mformatDescr (mformatOf tc) = (tc.itemsize.toNat, tc.isSigned, false))

theorem arrayMformatTable_proven : ArrayMformatTable := by
  intro tc
  cases tc <;> decide

end PyLean.Sequences
