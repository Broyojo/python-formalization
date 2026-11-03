import PyLean.BytesObj.Seq.ListRows5

/-!
The re-read after user code, as step equations over every callback, for `repr(l)`
(`list_repr_impl`) and the list invariant after `list_extend_iter_lock_held` under callbacks
that change the list in any invariant-preserving way (Objects/listobject.c, CPython 3.15.2).
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α : Type}

/-- `list_repr_impl`'s loop (listobject.c:621-640), for every item `__repr__`, including one that
replaces, inserts or removes items or makes the array move: each pass compares the index with the
size of the list as the previous `__repr__` left it (:623), takes the item from that list's current
array (`v->ob_item[i]`, :625, not a pointer saved before the loop), and goes on with the list the
`__repr__` leaves; past the current end it closes the bracket; a raising `__repr__` ends it with that
list. -/
def ReprStep : Prop :=
  ∀ (α : Type) (elem : LObj α → α → Py String × LObj α),
    (∀ (f i : Nat) (acc : String) (p p' : LObj α) (h : i < p.items.length) (s : String),
      elem p p.items[i] = (.ok s, p') →
      listReprLoop elem (f + 1) i acc p =
        listReprLoop elem f (i + 1) ((if i > 0 then acc ++ ", " else acc) ++ s) p') ∧
    (∀ (f i : Nat) (acc : String) (p p' : LObj α) (h : i < p.items.length) (e : PyExc),
      elem p p.items[i] = (.error e, p') → listReprLoop elem (f + 1) i acc p = (.error e, p')) ∧
    (∀ (f i : Nat) (acc : String) (p : LObj α), ¬ i < p.items.length →
      listReprLoop elem (f + 1) i acc p = (.ok (acc ++ "]"), p))

theorem reprStep_proven : ReprStep := by
  intro α elem
  refine ⟨fun f i acc p p' h s he => ?_, fun f i acc p p' h e he => ?_, fun f i acc p h => ?_⟩
  · rw [listReprLoop, dif_pos h]
    simp only
    rw [he]
  · rw [listReprLoop, dif_pos h]
    simp only
    rw [he]
  · rw [listReprLoop, dif_neg h]

theorem extendCutBack_wf (o : LObj α) (hw : o.WF) : (extendCutBack o).1.WF := by
  unfold extendCutBack
  split
  · cases hr : listResize o.allocated o.hasItems o.items.length o.items.length with
    | error e => exact hw
    | ok r =>
      obtain ⟨a, b⟩ := r
      obtain ⟨g1, g2, g3, g4⟩ := listResize_spec _ _ _ _ a b (by omega) hw.nonneg hw.bytes hw.array hr
      exact ⟨g2, g1, g4, g3⟩
  · exact hw

theorem extendRoom_wf (o o' : LObj α) (n : Int) (hw : o.WF) (hn : 0 ≤ n) (h : extendRoom o n = .ok o') :
    o'.WF ∧ o'.items = o.items := by
  unfold extendRoom at h
  simp only at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; exact ⟨hw, rfl⟩
  · split at h
    · rename_i _ hh
      have hh' : o.hasItems = false := by simpa using hh
      obtain ⟨hi, -⟩ := wf_noitems hw hh'
      split at h
      · cases hp : listPreallocateExact n with
        | error e => rw [hp] at h; simp at h
        | ok a =>
          rw [hp] at h
          simp only [Except.ok.injEq] at h
          subst h
          unfold listPreallocateExact at hp
          simp only at hp
          split at hp
          · simp only [Except.ok.injEq] at hp
            subst hp
            refine ⟨⟨?_, ?_, fun _ => rfl, ?_⟩, rfl⟩
            · show 0 ≤ (n + 1) / 2 * 2; omega
            · show ((o.items.length : Nat) : Int) ≤ (n + 1) / 2 * 2; rw [hi]; simp; omega
            · show (n + 1) / 2 * 2 ≤ ssizeMax / 8; omega
          · simp at hp
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨hw, rfl⟩
    · cases hr : listResize o.allocated o.hasItems o.items.length (o.items.length + n) with
      | error e => rw [hr] at h; simp at h
      | ok r =>
        obtain ⟨a, b⟩ := r
        rw [hr] at h
        simp only [Except.ok.injEq] at h
        subst h
        obtain ⟨g1, g2, g3, g4⟩ := listResize_spec _ _ _ _ a b (by omega) hw.nonneg hw.bytes hw.array hr
        exact ⟨⟨g2, by show ((o.items.length : Nat) : Int) ≤ a; omega, g4, g3⟩, rfl⟩

/-- `list_extend_iter_lock_held` keeps the list's invariant (`LObj.WF`: `allocated` covers the items,
an array exists when anything is allocated, the array fits) for every iterator whose callbacks keep
it, whatever they do to the list: clear it, shrink it, append to it, or replace its array. Because
`Py_SIZE(self)` and `allocated` are reread after each `tp_iternext` (listobject.c:1350), an iterator
that clears the list (freeing the array, `allocated == 0`) sends the next item to
`_PyList_AppendTakeRef`, not into the freed array; a drain that kept the allocation it saw before
the call would leave a list claiming slots with no array. The length hint is non-negative, as
`PyObject_LengthHint` guarantees (Objects/abstract.c; a negative value is an error). -/
def ListExtendIterWF : Prop :=
  ∀ (α : Type) (src : IterFx α) (fuel : Nat) (o : LObj α),
    (∀ (k : Nat) (p : LObj α), p.WF → ((src.next k p).2).WF) →
    o.WF → (drainFx src fuel 0 o).1.WF ∧
    ((∀ p, p.WF → ((src.getIter p).2).WF) → (∀ p, p.WF → ((src.hint p).2).WF) →
      (∀ p n, (src.hint p).1 = .ok n → 0 ≤ n) → (listExtendIterFx o src fuel).1.WF)

theorem drainFx_wf (src : IterFx α) (hs : ∀ (k : Nat) (p : LObj α), p.WF → ((src.next k p).2).WF) :
    ∀ (f k : Nat) (o : LObj α), o.WF → (drainFx src f k o).1.WF := by
  intro f
  induction f with
  | zero => intro k o hw; exact hw
  | succ f ih =>
    intro k o hw
    have hq := hs k o hw
    unfold drainFx
    generalize src.next k o = r at hq
    obtain ⟨r1, q⟩ := r
    simp only at hq
    match r1 with
    | none => exact extendCutBack_wf q hq
    | some (.error e) => exact hq
    | some (.ok x) =>
      simp only
      split
      · rename_i hroom
        apply ih
        refine ⟨hq.nonneg, ?_, hq.array, hq.bytes⟩
        show (((q.items ++ [x]).length : Nat) : Int) ≤ q.allocated
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · cases ha : listAppend q x with
        | ok o' =>
          simp only
          exact ih _ _ ((listOpsWF_proven α q o' hq).1 x ha)
        | error e => exact hq

theorem listExtendIterWF_proven : ListExtendIterWF := by
  intro α src fuel o hs hw
  refine ⟨drainFx_wf src hs fuel 0 o hw, fun hg hh hn => ?_⟩
  unfold listExtendIterFx
  have hg' := hg o hw
  generalize hgr : src.getIter o = g at hg'
  obtain ⟨g1, o0⟩ := g
  simp only at hg'
  match g1 with
  | .error e => exact hg'
  | .ok () =>
    simp only
    have hh' := hh o0 hg'
    have hn' := hn o0
    generalize hhr : src.hint o0 = r at hh' hn'
    obtain ⟨r1, o1⟩ := r
    simp only at hh' hn'
    match r1 with
    | .error e => exact hh'
    | .ok n =>
      simp only
      cases hr : extendRoom o1 n with
      | error e => exact hh'
      | ok o2 =>
        simp only
        exact drainFx_wf src hs fuel 0 o2 (extendRoom_wf o1 o2 n hh' (hn' n rfl) hr).1

end PyLean.BytesObj.Seq
