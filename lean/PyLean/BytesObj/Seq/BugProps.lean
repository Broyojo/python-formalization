import PyLean.BytesObj.Seq.AllocProps

/-!
Things that are not so, each with the version that is, and the allocation of `del`. The Python
reproducers are in `bugs/`.
-/

namespace PyLean.BytesObj.Seq

open PyLean

/-- `list.__sizeof__()` never reports less than an empty list's 40 bytes, in any
state a list can be in, including while `list.sort` runs. It does not hold: `sort`
sets `allocated` to `-1` (listobject.c:2994), and `list___sizeof___impl` casts that
to `size_t` and multiplies, wrapping to `32`. -/
def ListSizeofBase : Prop :=
  ∀ (α : Type) (o : LObj α), (o.WF ∨ o = listDuringSort) → 40 ≤ listSizeof o

theorem listSizeofBase_refuted : ¬ ListSizeofBase := by
  intro h
  have := h Unit listDuringSort (Or.inr rfl)
  revert this
  decide

/-- Outside `list.sort`, `list.__sizeof__()` is exactly `tp_basicsize + 8 * allocated`, with no
wraparound, for every list satisfying the invariant and every list type: `tp_basicsize` is a
`Py_ssize_t` that is not negative (type invariant), 40 for `list` itself and `40 + 8 * k` for a
subclass with `k` `__slots__`, so `class L(list): __slots__ = ('a', 'b')` gives `L().__sizeof__()
== 56`. -/
def ListSizeofExact : Prop :=
  ∀ (α : Type) (o : LObj α) (basicsize : Int), o.WF → 0 ≤ basicsize → basicsize ≤ ssizeMax →
    listSizeof o basicsize = basicsize + 8 * o.allocated ∧ listSizeof o = 40 + 8 * o.allocated

theorem listSizeof_eq {α : Type} (o : LObj α) (basicsize : Int) (hw : o.WF) (h0 : 0 ≤ basicsize)
    (h1 : basicsize ≤ ssizeMax) : listSizeof o basicsize = basicsize + 8 * o.allocated := by
  have h2 := hw.nonneg
  have h3 := hw.bytes
  unfold listSizeof PyLean.RangeSlice.toU
  have h8 : ssizeMax / 8 = 1152921504606846975 := by decide
  have hM : ssizeMax = 9223372036854775807 := by decide
  rw [h8] at h3
  have h4 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  unfold PyLean.RangeSlice.two64
  rw [h4, Int.emod_eq_of_lt h2 (by omega), Int.emod_eq_of_lt h0 (by omega)]
  have e : basicsize + o.allocated * 8 = basicsize + 8 * o.allocated := by omega
  rw [e]
  apply Int.emod_eq_of_lt <;> omega

theorem listSizeofExact_proven : ListSizeofExact := by
  intro α o b hw h0 h1
  exact ⟨listSizeof_eq o b hw h0 h1, listSizeof_eq o 40 hw (by decide) (by decide)⟩

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
skips the allocation (listobject.c:1317): the outcome depends on whether the list is
empty, not only on the hint. -/
def ListHintIgnoredWhenOverflowing : Prop :=
  ∀ (α : Type) (x : α) (src : IterSrc α), src.hint = .ok ssizeMax → src.err = none → src.items = [] →
    (listExtendIter { items := [x], allocated := 1, hasItems := true } src).2 = none

theorem listHintIgnoredWhenOverflowing_proven : ListHintIgnoredWhenOverflowing := by
  intro α x src h1 h2 h3
  have hroom : extendRoom ({ items := [x], allocated := 1, hasItems := true } : LObj α) ssizeMax =
      .ok { items := [x], allocated := 1, hasItems := true } := by
    unfold extendRoom
    simp only [List.length_cons, List.length_nil]
    rw [if_pos (by decide)]
  unfold listExtendIter listExtendIterFx
  simp only [IterSrc.fx, h1]
  rw [hroom]
  simp [drainFx, IterSrc.fx, h2, h3, extendCutBack]

/-- `del l[-1]` and `l.pop()` remove the same item and leave the same list, allocation included,
because both call `list_resize`. A list of one item is the exception `list_pop_impl` makes itself
(listobject.c:1626-1630): `pop` clears it and gives the array back, and `del` keeps a small array.
Hypothesis: a valid list object. -/
def ListDelLikePop : Prop :=
  ∀ (α : Type) (o o1 o2 : LObj α) (v : α), o.WF →
    listSetItem o (-1) none = .ok o1 → listPop o none = .ok (v, o2) →
      (2 ≤ o.items.length → o1 = o2) ∧ (o.items.length = 1 → o1.items = [] ∧ o2.allocated = 0)

theorem listDelLikePop_proven : ListDelLikePop := by
  intro α o o1 o2 v hw h1 h2
  have hs : PyLean.Sequences.subIndex (-1) = .ok (-1) := by decide
  have h1' : listAssItem o (-1 + (o.items.length : Int)) none = .ok o1 := by
    simpa [listSetItem, hs, bind, Except.bind] using h1
  by_cases h0 : o.items.length = 0
  · simp [listPop, listPopK, h0] at h2
  have hne : ¬ (o.items.length : Int) = 0 := by omega
  have hlt : (o.items.length : Int) < 2 ^ 63 := by
    have h3 := hw.covers
    have h4 := hw.bytes
    unfold ssizeMax at h4
    have h8 : (2 : Int) ^ 63 = 9223372036854775808 := by decide
    rw [h8]
    omega
  have hv : validIndex (-1 + (o.items.length : Int)) (o.items.length : Int) = true := by
    have h2 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
    have h8 : (2 : Int) ^ 63 = 9223372036854775808 := by decide
    rw [h8] at hlt
    unfold validIndex
    rw [h2, Int.emod_eq_of_lt (a := -1 + (o.items.length : Int)) (by omega) (by omega),
      Int.emod_eq_of_lt (a := (o.items.length : Int)) (by omega) (by omega)]
    exact decide_eq_true (by omega)
  have hneg : (-1 : Int) < 0 := by decide
  simp only [listAssItem, hv, Bool.not_true, Bool.false_eq_true, if_false] at h1'
  simp only [listPop, listPopK, hne, if_false, hneg, if_true, hv, Bool.not_true, Bool.false_eq_true] at h2
  constructor
  · intro h2le
    have hn1 : ¬ ((o.items.length : Int) - 1 = 0) := by omega
    split at h2
    · simp at h2
    · simp only [hn1, if_false] at h2
      rw [h1'] at h2
      simp only [Except.ok.injEq, Prod.mk.injEq] at h2
      exact h2.2
  · intro h1e
    have hn1 : ((o.items.length : Int) - 1 = 0) := by omega
    constructor
    · have hr := (resizeTo_wf hw h1').2
      rw [hr]
      apply List.length_eq_zero_iff.mp
      rw [List.length_eraseIdx]
      split <;> omega
    · split at h2
      · simp at h2
      · simp only [hn1, if_true, Except.ok.injEq, Prod.mk.injEq] at h2
        rw [← h2.2]
        have hhas : o.hasItems = true := hw.array (by have := hw.covers; omega)
        simp [listClear, hhas]

/-- `l[i] = x` leaves the array alone, and `del l[i]` is `list_resize` to one item less. -/
def ListAssItemAllocation : Prop :=
  ∀ (α : Type) (o o' : LObj α) (i : Int) (v : Option α), listAssItem o i v = .ok o' →
    (v.isSome → o'.allocated = o.allocated ∧ o'.hasItems = o.hasItems) ∧
    (v = none → ∃ (a : Int) (h : Bool),
      listResize o.allocated o.hasItems o.items.length o'.items.length = .ok (a, h) ∧
      o'.allocated = a ∧ o'.hasItems = h)

theorem listAssItemAllocation_proven : ListAssItemAllocation := by
  intro α o o' i v h
  unfold listAssItem at h
  split at h
  · simp at h
  · cases v with
    | none =>
      simp only [resizeTo] at h
      split at h
      · rename_i a b hr
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨by simp, fun _ => ⟨a, b, hr, rfl, rfl⟩⟩
      · simp at h
    | some x =>
      simp only [Except.ok.injEq] at h
      rw [← h]
      exact ⟨fun _ => ⟨rfl, rfl⟩, by simp⟩

end PyLean.BytesObj.Seq
