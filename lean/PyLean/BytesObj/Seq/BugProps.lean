import PyLean.BytesObj.Seq.AllocProps

/-!
Three things that are not so, each with the version that is. The Python reproducers
are in `bugs/`. `ListDelLikePop` is the behaviour of gh-158592, on record here because
the model mirrors 3.14.7, which still has it; it is fixed on main.
-/

namespace PyLean.BytesObj.Seq

open PyLean

/-- `list.__sizeof__()` never reports less than an empty list's 40 bytes, in any
state a list can be in, including while `list.sort` runs. It does not hold: `sort`
sets `allocated` to `-1` (listobject.c:2929), and `list___sizeof___impl` casts that
to `size_t` and multiplies, wrapping to `32`. -/
def ListSizeofBase : Prop :=
  ∀ (α : Type) (o : LObj α), (o.WF ∨ o = listDuringSort) → 40 ≤ listSizeof o

theorem listSizeofBase_refuted : ¬ ListSizeofBase := by
  intro h
  have := h Unit listDuringSort (Or.inr rfl)
  revert this
  decide

/-- Outside `list.sort`, `list.__sizeof__()` is exactly `40 + 8 * allocated`, with no
wraparound, for every list satisfying the invariant. -/
def ListSizeofExact : Prop :=
  ∀ (α : Type) (o : LObj α), o.WF → listSizeof o = 40 + 8 * o.allocated

theorem listSizeofExact_proven : ListSizeofExact := by
  intro α o hw
  have h1 := hw.nonneg
  have h2 := hw.bytes
  unfold listSizeof PyLean.RangeSlice.toU
  have h3 : ssizeMax / 8 = 1152921504606846975 := by decide
  rw [h3] at h2
  have h4 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  unfold PyLean.RangeSlice.two64
  rw [Int.emod_eq_of_lt h1 (by omega), h4]
  have e : 40 + o.allocated * 8 = 40 + 8 * o.allocated := by omega
  rw [e]
  apply Int.emod_eq_of_lt <;> omega

/-- `__length_hint__` is an estimate ("may be greater or less than the actual length",
Doc/reference/datamodel.rst), so any value it may legally return, `0` to
`sys.maxsize`, should leave `list.extend` succeeding on a small iterable. It does not:
`list_extend_iter_lock_held` passes the hint to `list_preallocate_exact` or
`list_resize`, whose failure is an error even when the iterable is empty. -/
def ListHintInert : Prop :=
  ∀ (α : Type) (o : LObj α) (src : IterSrc α) (n : Int), o.WF → src.hint = .ok n →
    0 ≤ n → n ≤ ssizeMax → src.err = none → src.items = [] →
    (listExtendIter o src).2 = none

theorem listHintInert_refuted : ¬ ListHintInert := by
  intro h
  have := h Unit LObj.empty { hint := .ok ssizeMax, items := [] } ssizeMax empty_wf rfl
    (by decide) (Int.le_refl _) rfl rfl
  revert this
  decide

/-- The same hint is ignored for a one-item list, because `m > PY_SSIZE_T_MAX - n`
skips the allocation (listobject.c:1241): the outcome depends on whether the list is
empty, not only on the hint. -/
def ListHintIgnoredWhenOverflowing : Prop :=
  ∀ (α : Type) (x : α) (src : IterSrc α), src.hint = .ok ssizeMax → src.err = none → src.items = [] →
    (listExtendIter { items := [x], allocated := 1, hasItems := true } src).2 = none

theorem listHintIgnoredWhenOverflowing_proven : ListHintIgnoredWhenOverflowing := by
  intro α x src h1 h2 h3
  unfold listExtendIter
  simp only [h1]
  have hroom : extendRoom ({ items := [x], allocated := 1, hasItems := true } : LObj α) ssizeMax =
      .ok { items := [x], allocated := 1, hasItems := true } := by
    unfold extendRoom
    simp only [List.length_cons, List.length_nil]
    rw [if_pos (by decide)]
  rw [hroom]
  simp [h2, h3, extendDrain]

/-- `del l[i]` and `l.pop(i)` remove the same item, so they should leave the list with
the same allocation. On 3.14.7 they do not: `list_ass_item_lock_held` deletes without
calling `list_resize`, so the array never shrinks however many items go. gh-158592,
closed; `list_ass_item_impl` on main calls `list_resize`. -/
def ListDelLikePop : Prop :=
  ∀ (α : Type) (o o1 o2 : LObj α) (v : α), o.WF →
    listSetItem o (-1) none = .ok o1 → listPop o none = .ok (v, o2) →
      o1.allocated = o2.allocated

theorem listDelLikePop_refuted : ¬ ListDelLikePop := by
  intro h
  let o : LObj Unit := { items := List.replicate 5 (), allocated := 16, hasItems := true }
  have hw : o.WF := ⟨by decide, by decide, fun _ => rfl, by decide⟩
  have := h Unit o { o with items := List.replicate 4 () }
    { items := List.replicate 4 (), allocated := 8, hasItems := true } () hw (by decide) (by decide)
  revert this
  decide

/-- What 3.14.7 does: `del l[i]` and `l[i] = x` leave `allocated` and `ob_item` alone. -/
def ListAssItemKeepsAllocation : Prop :=
  ∀ (α : Type) (o o' : LObj α) (i : Int) (v : Option α), listAssItem o i v = .ok o' →
    o'.allocated = o.allocated ∧ o'.hasItems = o.hasItems

theorem listAssItemKeepsAllocation_proven : ListAssItemKeepsAllocation := by
  intro α o o' i v h
  unfold listAssItem at h
  split at h
  · simp at h
  · cases v with
    | none =>
      simp only [Except.ok.injEq] at h
      rw [← h]
      exact ⟨rfl, rfl⟩
    | some x =>
      simp only [Except.ok.injEq] at h
      rw [← h]
      exact ⟨rfl, rfl⟩

end PyLean.BytesObj.Seq
