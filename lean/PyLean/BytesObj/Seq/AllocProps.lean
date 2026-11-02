import PyLean.BytesObj.Seq.ListModel

/-!
The allocation behaviour of `list`: `list_resize` and the invariant that every
mutating operation keeps.

`list.__sizeof__` exposes `allocated`, so these are statements about something a
Python program can see, and the difftest checks them after every operation.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α ρ : Type}

/-- The invariant of a `PyListObject` outside `list.sort`: `allocated` is a
non-negative count that covers the items, there is an array when there is
anything to hold, and the array's size in bytes fits `Py_ssize_t`. -/
structure LObj.WF (o : LObj α) : Prop where
  nonneg : 0 ≤ o.allocated
  covers : (o.items.length : Int) ≤ o.allocated
  array : 0 < o.allocated → o.hasItems = true
  bytes : o.allocated ≤ ssizeMax / 8

theorem overalloc_ge (n : Int) (h : 0 ≤ n) : n + 3 ≤ overalloc n := by
  unfold overalloc
  omega

theorem newAllocated_ge (size n : Int) (h : 0 ≤ n) : n ≤ newAllocated size n := by
  unfold newAllocated
  have := overalloc_ge n h
  simp only
  by_cases h0 : n = 0
  · simp [h0]
  · simp only [h0, if_false]
    split <;> omega

/-- What `list_resize` promises its callers. -/
theorem listResize_spec (allocated : Int) (hasItems : Bool) (size newsize a : Int) (h : Bool)
    (hn : 0 ≤ newsize) (ha : 0 ≤ allocated) (hb : allocated ≤ ssizeMax / 8)
    (harr : 0 < allocated → hasItems = true)
    (hr : listResize allocated hasItems size newsize = .ok (a, h)) :
    newsize ≤ a ∧ 0 ≤ a ∧ a ≤ ssizeMax / 8 ∧ (0 < a → h = true) := by
  unfold listResize at hr
  split at hr
  · rename_i hfast
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hfast.1, ha, hb, harr⟩
  · simp only at hr
    split at hr
    · rename_i hsize
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have := newAllocated_ge size newsize hn
      exact ⟨this, by omega, hsize, fun _ => rfl⟩
    · split at hr
      · rename_i hless
        simp only [Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨by omega, ha, hb, harr⟩
      · simp at hr

/-- `list_resize`, for every state and size: a successful resize leaves room for
`newsize`; the fast path of line 121 changes nothing, and it is taken when `newsize <= allocated`
and either `allocated >> 1 <= newsize` or the list is small. The over-allocation is a
multiple of 4 for a non-zero size. The note at lines 130-131 of listobject.c holds:
`new_allocated` is below `2^64` for all `newsize <= PY_SSIZE_T_MAX`, so it cannot
overflow `size_t`, and it is at most `newsize * 9/8 + 6`. -/
def ListResizeSpec : Prop :=
  (∀ (allocated : Int) (h : Bool) (size newsize : Int),
    allocated ≥ newsize → (newsize ≥ allocated / 2 ∨ allocated ≤ 32) →
      listResize allocated h size newsize = .ok (allocated, h)) ∧
  (∀ (n : Int), 0 ≤ n → n ≤ ssizeMax →
    overalloc n % 4 = 0 ∧ n ≤ overalloc n ∧ overalloc n ≤ n + n / 8 + 6 ∧ overalloc n < 2 ^ 64) ∧
  (∀ (size n : Int), 0 ≤ n → (n ≠ 0 → newAllocated size n % 4 = 0) ∧ n ≤ newAllocated size n)

theorem listResizeSpec_proven : ListResizeSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro allocated h size newsize h1 h2
    unfold listResize
    rw [if_pos ⟨h1, h2⟩]
  · intro n h0 h1
    unfold overalloc ssizeMax at *
    have h2 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
    have h3 : (2 : Int) ^ 63 = 9223372036854775808 := by decide
    rw [h2]
    rw [h3] at h1
    refine ⟨by omega, by omega, by omega, by omega⟩
  · intro size n h0
    refine ⟨?_, newAllocated_ge size n h0⟩
    intro hn
    unfold newAllocated overalloc
    simp only [hn, if_false]
    split <;> omega

/-- `allocated` after `n` appends to `[]`, as `_PyList_AppendTakeRef` would do it. -/
def appendAllocs : Nat → LObj Unit → List Int
  | 0, _ => []
  | n + 1, o =>
    match listAppend o () with
    | .ok o' => o'.allocated :: appendAllocs n o'
    | .error _ => []

/-- The growth pattern in the comment at listobject.c:144: "0, 4, 8, 16, 24, 32, 40,
52, 64, 76". The capacity after each of the first 65 appends, dropping repeats, is
that sequence (the 65th append is the one that reaches 76). -/
def ListGrowthPattern : Prop :=
  (((appendAllocs 65 LObj.empty).foldl
      (fun (acc : List Int) x => if acc.getLast? = some x then acc else acc ++ [x]) [0])) =
    [0, 4, 8, 16, 24, 32, 40, 52, 64, 76]

theorem listGrowthPattern_proven : ListGrowthPattern := by
  unfold ListGrowthPattern
  decide +kernel

/-! ## The invariant is preserved -/

theorem resizeTo_wf {o o' : LObj α} {items : List α} (hw : o.WF)
    (hr : resizeTo o items = .ok o') : o'.WF ∧ o'.items = items := by
  unfold resizeTo at hr
  cases hl : listResize o.allocated o.hasItems o.items.length items.length with
  | error e => rw [hl] at hr; simp at hr
  | ok p =>
    obtain ⟨a, h⟩ := p
    rw [hl] at hr
    simp only [Except.ok.injEq] at hr
    subst hr
    obtain ⟨h1, h2, h3, h4⟩ :=
      listResize_spec _ _ _ _ a h (by omega) hw.nonneg hw.bytes hw.array hl
    exact ⟨⟨h2, h1, h4, h3⟩, rfl⟩

theorem empty_wf : (LObj.empty : LObj α).WF :=
  ⟨by simp [LObj.empty], by simp [LObj.empty], by simp [LObj.empty], by simp [LObj.empty, ssizeMax]⟩

theorem clear_wf (o : LObj α) (hw : o.WF) : (listClear o).WF := by
  unfold listClear
  split
  · exact hw
  · exact empty_wf

theorem prealloc_wf (items : List α) (h : (items.length : Int) ≤ ssizeMax / 8) :
    (LObj.prealloc items).WF := by
  unfold LObj.prealloc
  split
  · exact empty_wf
  · exact ⟨by simp, by simp, fun _ => rfl, h⟩

@[simp] theorem prealloc_items (items : List α) : (LObj.prealloc items).items = items := by
  unfold LObj.prealloc
  split
  · rename_i h
    exact (List.length_eq_zero_iff.mp h).symm
  · rfl

theorem listSliceLH_all (a : List α) : (listSliceLH a 0 a.length).items = a := by
  unfold listSliceLH
  simp only
  by_cases h : (a.length : Int) - 0 ≤ 0
  · have h1 : a = [] := List.length_eq_zero_iff.mp (by omega)
    simp [h1, LObj.empty]
  · rw [if_neg h, prealloc_items]
    have e1 : (0 : Int).toNat = 0 := rfl
    have e2 : ((a.length : Int) - 0).toNat = a.length := by omega
    rw [e1, e2]
    simp

/-- Every mutating `list` method keeps the invariant, for every list and every
argument: `append`, `insert`, `pop`, `clear`, `reverse`, `l[i] = x`, `del l[i]`,
slice assignment and deletion through `list_ass_slice`, `*=`, and `extend` from a
sequence or a sized container. The contents are in `Sequences` and in the entries
below; this is the bookkeeping. -/
def ListOpsWF : Prop :=
  ∀ (α : Type) (o o' : LObj α), o.WF →
    (∀ v, listAppend o v = .ok o' → o'.WF) ∧
    (∀ w v, ins1 o w (some v) = .ok o' → o'.WF) ∧
    (∀ v i, listPopK o i = .ok (v, o') → o'.WF) ∧
    (listClear o = o' → o'.WF) ∧
    (listReverse o = o' → o'.WF) ∧
    (∀ i v, listAssItem o i v = .ok o' → o'.WF) ∧
    (∀ lo hi v, listAssSlice o lo hi v = .ok o' → o'.WF) ∧
    (∀ n, listInplaceRepeat o n = .ok o' → o'.WF) ∧
    (∀ s, listExtendFast o s = .ok o' → o'.WF) ∧
    (∀ s, listExtendSized o s = .ok o' → o'.WF)

theorem reverseLoop_length (f : Nat) (front mid back : List α) :
    (reverseLoop f front mid back).length = front.length + mid.length + back.length := by
  induction f generalizing front mid back with
  | zero => simp [reverseLoop]; omega
  | succ f ih =>
    unfold reverseLoop
    split
    · rename_i a b rest
      rw [ih]
      simp
      omega
    · simp; omega

/-- `list.pop` either clears the list or goes through `list_resize`. -/
theorem listPopK_cases {o o' : LObj α} {i : Int} {v : α} (h : listPopK o i = .ok (v, o')) :
    o' = listClear o ∨ ∃ items, resizeTo o items = .ok o' := by
  unfold listPopK at h
  simp only at h
  generalize (if i < 0 then i + (o.items.length : Int) else i) = idx at h
  by_cases h0 : (o.items.length : Int) = 0
  · rw [if_pos h0] at h
    simp at h
  · rw [if_neg h0] at h
    by_cases h1 : (!validIndex idx (o.items.length : Int)) = true
    · rw [if_pos h1] at h
      simp at h
    · rw [if_neg h1] at h
      cases hs : slot o.items idx with
      | none => rw [hs] at h; simp at h
      | some x =>
        rw [hs] at h
        simp only at h
        by_cases h2 : (o.items.length : Int) - 1 = 0
        · rw [if_pos h2] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          exact Or.inl h.2.symm
        · rw [if_neg h2] at h
          cases hr : resizeTo o (o.items.eraseIdx idx.toNat) with
          | error e => rw [hr] at h; simp at h
          | ok o2 =>
            rw [hr] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            exact Or.inr ⟨_, by rw [hr, h.2]⟩

/-- `len(l * n)`: the replicated copies concatenate to `n * len(l)` items. -/
theorem length_repeat (l : List α) (n : Nat) :
    (List.replicate n l).flatten.length = n * l.length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.add_mul, Nat.add_comm]
    simp

theorem listOpsWF_proven : ListOpsWF := by
  intro α o o' hw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v h
    unfold listAppend at h
    split at h
    · rename_i hroom
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨hw.nonneg, ?_, hw.array, hw.bytes⟩
      simp
      omega
    · exact (resizeTo_wf hw h).1
  · intro w v h
    exact (resizeTo_wf hw h).1
  · intro v i h
    rcases listPopK_cases h with h1 | ⟨items, h1⟩
    · rw [h1]; exact clear_wf o hw
    · exact (resizeTo_wf hw h1).1
  · intro h
    subst h
    exact clear_wf o hw
  · intro h
    subst h
    unfold listReverse
    split
    · refine ⟨hw.nonneg, ?_, hw.array, hw.bytes⟩
      simp only [reverseLoop_length]
      have := hw.covers
      simp
      omega
    · exact hw
  · intro i v h
    unfold listAssItem at h
    split at h
    · simp at h
    · cases v with
      | none => exact (resizeTo_wf hw h).1
      | some v =>
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨hw.nonneg, ?_, hw.array, hw.bytes⟩
        have := hw.covers
        simpa using this
  · intro lo hi v h
    unfold listAssSlice at h
    simp only at h
    generalize hl' : (if lo < 0 then (0 : Int) else
      if lo > (o.items.length : Int) then (o.items.length : Int) else lo) = ilow at h
    generalize hh' : (if hi < ilow then ilow else
      if hi > (o.items.length : Int) then (o.items.length : Int) else hi) = ihigh at h
    have hb1 : 0 ≤ ilow ∧ ilow ≤ o.items.length := by
      rw [← hl']; split <;> (try split) <;> omega
    have hb2 : ilow ≤ ihigh ∧ ihigh ≤ o.items.length := by
      rw [← hh']; split <;> (try split) <;> omega
    by_cases hz : (o.items.length : Int) + (((v.getD []).length : Int) - (ihigh - ilow)) = 0
    · rw [if_pos hz] at h
      simp only [Except.ok.injEq] at h
      subst h
      exact clear_wf o hw
    · rw [if_neg hz] at h
      by_cases hd : ((v.getD []).length : Int) - (ihigh - ilow) = 0
      · rw [if_pos hd] at h
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨hw.nonneg, ?_, hw.array, hw.bytes⟩
        have := hw.covers
        show ((o.items.take ilow.toNat ++ v.getD [] ++ o.items.drop ihigh.toNat).length : Int) ≤ o.allocated
        simp only [List.length_append, List.length_take, List.length_drop]
        omega
      · rw [if_neg hd] at h
        exact (resizeTo_wf hw h).1
  · intro n h
    unfold listInplaceRepeat at h
    simp only at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact hw
    · split at h
      · simp only [Except.ok.injEq] at h
        subst h
        exact clear_wf o hw
      · split at h
        · simp at h
        · rename_i h1 h2 h3
          cases hl : listResize o.allocated o.hasItems o.items.length (o.items.length * n) with
          | error e => rw [hl] at h; simp at h
          | ok p =>
            obtain ⟨a, b⟩ := p
            rw [hl] at h
            simp only [Except.ok.injEq] at h
            subst h
            have hn : 0 ≤ n := by omega
            obtain ⟨g1, g2, g3, g4⟩ :=
              listResize_spec _ _ _ _ a b (Int.mul_nonneg (by omega) hn) hw.nonneg hw.bytes hw.array hl
            refine ⟨g2, ?_, g4, g3⟩
            have hcast : ((n.toNat * o.items.length : Nat) : Int) = (o.items.length : Int) * n := by
              rw [Int.natCast_mul, Int.toNat_of_nonneg hn, Int.mul_comm]
            simp only [length_repeat]
            omega
  · intro s h
    unfold listExtendFast at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact hw
    · split at h
      · rename_i h1 h2
        cases hp : listPreallocateExact (s.length : Int) with
        | error e => rw [hp] at h; simp at h
        | ok a =>
          rw [hp] at h
          simp only [Except.ok.injEq] at h
          subst h
          unfold listPreallocateExact at hp
          simp only at hp
          split at hp
          · rename_i hle
            simp only [Except.ok.injEq] at hp
            subst hp
            have hempty : o.items.length = 0 := by
              have harr := hw.array
              have hcov := hw.covers
              by_cases hne : o.items.length = 0
              · exact hne
              · have hpos : 0 < o.allocated := by omega
                have := harr hpos
                simp [this] at h2
            have hs : s.length ≠ 0 := h1
            have hlen : ((o.items ++ s).length : Int) ≤ (((s.length : Int) + 1) / 2) * 2 := by
              simp only [List.length_append, hempty]
              omega
            have hnn : (0 : Int) ≤ (((s.length : Int) + 1) / 2) * 2 := by omega
            exact ⟨hnn, hlen, fun _ => rfl, hle⟩
          · simp at hp
      · exact (resizeTo_wf hw h).1
  · intro s h
    unfold listExtendSized at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact hw
    · exact (resizeTo_wf hw h).1

end PyLean.BytesObj.Seq
