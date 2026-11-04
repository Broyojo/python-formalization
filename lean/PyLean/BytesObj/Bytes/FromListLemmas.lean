import PyLean.BytesObj.Bytes.BasicProps3

/-!
`_PyBytes_FromList` on a list whose items do not touch it: the 3.15 loop, which rereads the list at
every step, gives what the item-by-item conversion `bytesFromItems` gives, for every list that can
exist.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

set_option linter.unusedSimpArgs false

theorem bytesFromItems_len (items : List Obj) (t : Seq) (h : bytesFromItems items = .ok t) :
    t.length = items.length := by
  induction items generalizing t with
  | nil => simp [bytesFromItems] at h; subst h; rfl
  | cons x xs ih =>
    simp only [bytesFromItems, bind, Except.bind] at h
    cases hx : byteItem x with
    | error e => simp [hx] at h
    | ok v =>
      simp only [hx] at h
      cases hr : bytesFromItems xs with
      | error e => simp [hr] at h
      | ok r =>
        simp [hr, pure, Except.pure] at h
        subst h
        simp [ih r hr]

/-- With no `__index__` touching the list, the size never passes the allocation, so the writer
does not grow, and every step converts the next item as `byteItem` does. -/
theorem fromList_plain (items : List Obj) (w : Writer) (size : Int) (hL : (items.length : Int) ≤ size) :
    ∀ (fuel i : Nat) (out : Seq), items.length - i < fuel → i ≤ items.length →
      fromListLoop fuel (items.map .plain) i w size out =
        (bytesFromItems (items.drop i)).map (fun t => (out ++ t, w)) := by
  intro fuel
  induction fuel with
  | zero => intro i out h; omega
  | succ f ih =>
    intro i out hf hi
    rw [fromListLoop]
    by_cases hlt : i < items.length
    · have hlt' : i < (items.map LItem.plain).length := by simpa using hlt
      rw [if_pos hlt']
      have hget : (items.map LItem.plain).getD i default = .plain (items[i]) := by
        simp [List.getD, hlt]
      rw [hget, List.drop_eq_getElem_cons hlt]
      simp only [lItemIndex, bytesFromItems, byteItem, bind, Except.bind]
      cases ha : asSsizeClamp items[i] with
      | error e => simp [Except.map]
      | ok v =>
        simp only
        by_cases hv : v < 0 ∨ v ≥ 256
        · simp [hv, Except.map, throw, throwThe, MonadExcept.throw]
          rfl
        · have hge : ¬ ((i : Int) ≥ size) := by omega
          simp only [hv, if_false, hge, pure, Except.pure]
          rw [ih (i + 1) (out ++ [v.toNat]) (by omega) (by omega)]
          cases bytesFromItems (items.drop (i + 1)) <;> simp [Except.map]
    · have hge : ¬ (i < (items.map LItem.plain).length) := by simpa using hlt
      rw [if_neg hge]
      have : items.drop i = [] := List.drop_of_length_le (by omega)
      simp [this, bytesFromItems, Except.map]

theorem writerCreate_facts (n : Nat) (w : Writer) (h : writerCreate n false = .ok w) :
    w.size = n ∧ (n : Int) ≤ writerAllocated w ∧ writerAllocated w ≤ max 256 (n : Int) ∧ w.useBytearray = false := by
  have hinv := writerInvariant_proven.1 n false w h
  unfold writerCreate at h
  have h0 : ¬ ((n : Int) < 0) := by omega
  simp only [if_neg h0] at h
  split at h
  · split at h
    · rename_i w1 hr
      simp only [Except.ok.injEq] at h
      subst h
      unfold writerResizeRaw at hr
      split at hr
      · simp only [Except.ok.injEq] at hr
        subst hr
        refine ⟨hinv.1, hinv.2, ?_, rfl⟩
        simp only [writerAllocated, smallBufferSize]; omega
      · simp only at hr
        split at hr
        · rename_i obj hobj
          simp only [Except.ok.injEq] at hr
          subst hr
          have := writerObjResize_size _ _ _ hobj
          refine ⟨hinv.1, hinv.2, ?_, rfl⟩
          simp only [writerAllocated]
          rcases obj with ⟨a, b⟩
          simp at this ⊢
          omega
        · cases hr
    · cases h
  · simp only [Except.ok.injEq] at h
    subst h
    refine ⟨hinv.1, hinv.2, ?_, rfl⟩
    simp only [writerAllocated, smallBufferSize]; omega

theorem wfinish_ok (w : Writer) (out : Seq) (hb : w.useBytearray = false)
    (h1 : (out.length : Int) ≤ w.size) (h2 : w.size < 2 ^ 46) : writerFinish w out = .ok out := by
  have hc : ∀ m : Int, 0 ≤ m → m < 2 ^ 46 → bytesSizeCheck m = .ok () :=
    fun m a b => bytesSizeCheck_ok m a (by omega)
  have hk : ¬ ((out.length : Int) < 0) := by omega
  have hg : ¬ ((out.length : Int) > w.size) := by omega
  have hcs := hc (out.length : Int) (by omega) (by omega)
  unfold writerFinish writerFinishSize
  rw [if_neg hk, if_neg hg]
  by_cases hz : (out.length : Int) = 0
  · simp [hz, hb]
  · have hz' : out ≠ [] := by intro e; simp [e] at hz
    rw [if_neg (by simp [hz'])]
    rcases hobj : w.obj with _ | ⟨n, a⟩
    · simp [hcs]
    · simp only [hb, Bool.false_eq_true, ite_false]
      by_cases hn : (out.length : Int) = n
      · simp [hn]
      · rw [if_pos hn]
        unfold bytesResizeCheck
        rw [if_neg hk]
        simp only [hcs, ite_self]

/-- `bytes(list)` for a list whose items leave it alone is the item-by-item conversion, for every list
that can exist (fewer than `2^46` items: its own pointer array is 8 bytes an item). -/
theorem bytesFromList_plain (items : List Obj) (h : (items.length : Int) + 33 < 2 ^ 46) :
    bytesFromList (items.map .plain) = bytesFromItems items := by
  obtain ⟨w, hw, _⟩ := writerCreate_ok items.length (by omega)
  obtain ⟨hs, ha1, ha2, hb⟩ := writerCreate_facts items.length w hw
  unfold bytesFromList
  simp only [List.length_map, hw, bind, Except.bind]
  have hL : (items.length : Int) ≤ (writerResizeToAllocated w).size := by
    simp [writerResizeToAllocated]; omega
  rw [fromList_plain items _ _ hL (2 * items.length + 1) 0 [] (by omega) (by omega)]
  cases hr : bytesFromItems items with
  | error e => simp [hr, Except.map]
  | ok t =>
    have ht := bytesFromItems_len items t hr
    simp only [List.drop_zero, hr, Except.map, List.nil_append]
    apply wfinish_ok
    · simp [writerResizeToAllocated, hb]
    · simp [writerResizeToAllocated, ht]; omega
    · simp [writerResizeToAllocated]; omega

end PyLean.BytesObj.Bytes
