import PyLean.Sequences.ArrayLimits

/-!
`a.fromlist(list)` with items whose conversion runs Python code that changes the array
(`arrFromListRe`, `ArrayReModel`): the store index `Py_SIZE(self) - n + i` is computed from the
live size before each conversion (arraymodule.c:1869-1870), and the restore
`array_resize(self, old_size)` (:1871, :1877) resizes whatever array the code left.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

/-- The store index of `fromlist` is read from the live size. For every array without exported
buffers, every two-item list whose second item's conversion changes nothing and whose first
item's conversion leaves any array `b` with a buffer and more than `len(a)` items (code that
grows, shrinks or replaces the array) and leaves the list alone: item 0 is stored at
`Py_SIZE - n + 0 = len(a)`, computed before its conversion ran, and item 1 at
`Py_SIZE(b) - 2 + 1 = len(b) - 1`, so when the code grew the array the cells
`array_resize(self, len(a) + 2)` added between them are never written (uninitialised memory in
CPython, 0 in the model; python/cpython#152166), and when it shrank it to `len(a) + 1` items the
second store overwrites the first. A conversion that the store refuses raises its exception
first (sequences-array-fromlist-guard). -/
def ArrayFromListLive : Prop :=
  ∀ {X : Type} (conv : X → Arr × List X → (Arr × List X) × PyVal) (a a1 b : Arr) (p q : X)
    (x y : PyVal) (cx cy : Int),
    a.exports = 0 → arrResize a (a.items.length + 2) = .ok a1 →
    conv p (a1, [p, q]) = ((b, [p, q]), x) →
    (∀ c, conv q (c, [p, q]) = ((c, [p, q]), y)) →
    b.hasBuf = true → (a.items.length : Int) < b.items.length →
    tcSetitem b.tc true x = .ok cx → tcSetitem b.tc true y = .ok cy →
    arrFromListRe conv a (.inl [p, q]) =
      (.ok (), { b with items := (b.items.set a.items.length cx).set (b.items.length - 1) cy })

theorem arrayFromListLive_proven : ArrayFromListLive := by
  intro X conv a a1 b p q x y cx cy hx hr hp hq hb hlt hsx hsy
  obtain ⟨_, _, hl1, _, _⟩ := arrResize_pos a a1 _ hr (by omega)
  unfold arrFromListRe
  simp only [List.length_cons, List.length_nil]
  rw [iteT (by omega)]
  rw [show ((0 + 1 + 1 : Nat) : Int) = 2 from rfl, show (a.items.length : Int) + 2 = a.items.length + 2 from rfl, hr]
  simp only
  rw [fromListReLoop, iteT (by omega)]
  simp only [Int.toNat_zero, List.getElem?_cons_zero]
  rw [show (a1.items.length : Int) - 2 + 0 = a.items.length by omega, hp]
  simp only
  have hs1 : storeAfter b a.items.length x = ({ b with items := b.items.set a.items.length cx }, .ok ()) := by
    unfold storeAfter
    rw [iteF (by omega)]
    have : (b.hasBuf && decide ((a.items.length : Int) < b.items.length)) = true := by
      rw [hb]; simp only [Bool.true_and, decide_eq_true_eq]; exact hlt
    rw [this, hsx]
    simp
  rw [hs1]
  simp only [List.length_cons, List.length_nil, show ((0 + 1 + 1 : Nat) : Int) = 2 from rfl, ne_eq,
    eq_self_iff_true, not_true_eq_false, ite_false]
  rw [fromListReLoop, iteT (by omega)]
  simp only [show ((0 : Int) + 1).toNat = 1 from rfl, List.getElem?_cons_succ, List.getElem?_cons_zero]
  rw [hq]
  simp only [List.length_set]
  rw [show (b.items.length : Int) - 2 + (0 + 1) = b.items.length - 1 by omega]
  have hs2 : storeAfter { b with items := b.items.set a.items.length cx } ((b.items.length : Int) - 1) y =
      ({ b with items := (b.items.set a.items.length cx).set ((b.items.length : Int) - 1).toNat cy }, .ok ()) := by
    unfold storeAfter
    rw [iteF (by omega)]
    have : (b.hasBuf && decide ((b.items.length : Int) - 1 < ((b.items.set a.items.length cx).length : Int))) = true := by
      rw [hb]; simp only [Bool.true_and, decide_eq_true_eq, List.length_set]; omega
    simp only
    rw [this, hsy]
  rw [hs2]
  simp only [List.length_cons, List.length_nil, show ((0 + 1 + 1 : Nat) : Int) = 2 from rfl, ne_eq,
    eq_self_iff_true, not_true_eq_false, ite_false]
  rw [fromListReLoop]
  rw [show ((b.items.length : Int) - 1).toNat = b.items.length - 1 by omega]

/-- The restore of `fromlist` after a conversion that cleared the array. For every integer
typecode, every array of `old` items without exported buffers and every list of `n` items with
`old + n >= 16` (and the new size fits) whose first item's conversion clears the array
(`a.clear()`, which frees the buffer of 16 or more items, arraymodule.c:163-169) and returns
any int `x`: the store's `CHECK_ARRAY_BOUNDS` refuses (`IndexError`, or the conversion's own
`OverflowError` first), and `array_resize(self, old_size)` (:1871) reallocates the NULL buffer
to `old` items (:183-198) that nobody writes: fromlist raises and leaves `old` items, none of
them written (uninitialised memory in CPython, 0 in the model), though the code left none. -/
def ArrayFromListClear : Prop :=
  ∀ {X : Type} (conv : X → Arr × List X → (Arr × List X) × PyVal) (a : Arr) (p : X)
    (rest : List X) (x : Int),
    a.tc.isInteger = true → a.exports = 0 → 16 ≤ a.items.length + rest.length + 1 →
    a.Fits (a.items.length + rest.length + 1) →
    (∀ c l, conv p (c, l) = (((arrClear c).toOption.getD c, l), .int x)) →
    arrFromListRe conv a (.inl (p :: rest)) =
      (.error ((intPreCheck a.tc x).getD boundsErr),
        ⟨a.tc, List.replicate a.items.length 0,
          if a.items.length = 0 then 0 else (a.items.length : Int) / 16 + 3 + a.items.length,
          decide (0 < a.items.length), 0, a.tname⟩)

theorem arrayFromListClear_proven : ArrayFromListClear := by
  intro X conv a p rest x hi hx h16 hf hp
  obtain ⟨a1, hr, hitems, ht, he, hn⟩ := arrResize_ok a ((a.items.length : Int) + ((rest.length + 1 : Nat) : Int)) hx
    (by omega) (by unfold Arr.Fits at *; omega)
  obtain ⟨hb1, _, hl1, _, _⟩ := arrResize_pos a a1 _ hr (by omega)
  have hcl : arrClear a1 = .ok { a1 with items := [], hasBuf := false, allocated := 0 } := by
    unfold arrClear arrResize
    dsimp only
    rw [iteF (by omega), iteF (by omega), iteT rfl]
  unfold arrFromListRe
  simp only [List.length_cons]
  rw [iteT (by omega), hr]
  simp only
  rw [fromListReLoop, iteT (by omega)]
  simp only [Int.toNat_zero, List.getElem?_cons_zero]
  rw [hp, hcl]
  simp only [Except.toOption, Option.getD_some]
  rw [show (a1.items.length : Int) - ((rest.length + 1 : Nat) : Int) + 0 = a.items.length by omega]
  have hst : storeAfter { a1 with items := [], hasBuf := false, allocated := 0 } a.items.length (.int x) =
      ({ a1 with items := [], hasBuf := false, allocated := 0 }, .error ((intPreCheck a.tc x).getD boundsErr)) := by
    unfold storeAfter
    rw [iteF (by omega)]
    simp only [Bool.false_and]
    rw [← ht, tcSetitem_false_int _ (by rw [ht]; exact hi) x]
  rw [hst]
  simp only [fromListRestore]
  unfold arrResize
  simp only [List.length_nil, he]
  rw [iteF (by omega), iteF (by simp)]
  by_cases h0 : a.items.length = 0
  · rw [iteT (by omega)]
    simp only [h0, ite_true, List.replicate_zero, Nat.lt_irrefl, decide_false]
    rw [← ht, ← hn]
  · rw [iteF (by omega)]
    have hfit : (a.items.length : Int) / 16 + (if ((0 : Nat) : Int) < 8 then 3 else 7) + a.items.length ≤
        18446744073709551615 / a.tc.itemsize := by
      unfold Arr.Fits ssizeMax at hf
      rcases itemsize_cases a.tc with h | h | h | h | h <;> rw [h] at hf ⊢ <;> simp <;> omega
    rw [iteT (by first | (rw [ht]; exact hfit) | (simp only [ht]; exact hfit) | simpa [ht] using hfit)]
    simp only [resized, List.length_nil, h0, ite_false]
    rw [iteF (by omega)]
    simp only [List.nil_append, Int.sub_zero, Int.toNat_natCast, ← ht, ← hn]
    congr 1
    simp only [Arr.mk.injEq, true_and]
    refine ⟨by simp, by simp, ?_, trivial⟩
    simp only [eq_comm (a := true), decide_eq_true_eq]
    omega

/-- A failed `fromlist` does not create items: for every array without exported buffers and
every list whose first item's conversion may run code that changes the array, if the store of
that item fails, fromlist leaves the array with no more items than the code left it with (the
restore `array_resize(self, old_size)` only undoes fromlist's own growth). Refuted on 3.15.2:
the restore resizes to the old size whatever the code did, so a 16-item array whose
`__index__` clears it comes back with 16 items nobody wrote (uninitialised memory in CPython). -/
def ArrayFromListRestore : Prop :=
  ∀ {X : Type} (conv : X → Arr × List X → (Arr × List X) × PyVal) (a a1 : Arr) (p : X)
    (rest : List X) (e : PyExc),
    a.exports = 0 → arrResize a ((a.items.length : Int) + ((rest.length + 1 : Nat) : Int)) = .ok a1 →
    (storeAfter (conv p (a1, p :: rest)).1.1 a.items.length (conv p (a1, p :: rest)).2).2 = .error e →
    (arrFromListRe conv a (.inl (p :: rest))).2.items.length ≤ (conv p (a1, p :: rest)).1.1.items.length

theorem arrayFromListRestore_refuted : ¬ ArrayFromListRestore := by
  intro h
  let conv : Unit → Arr × List Unit → (Arr × List Unit) × PyVal :=
    fun _ s => (((arrClear s.1).toOption.getD s.1, s.2), .int 7)
  have hq : q16.items.length = 16 := rfl
  have hc := arrayFromListClear_proven conv q16 () [] 7 rfl rfl (by decide) (by unfold Arr.Fits; decide)
    (fun _ _ => rfl)
  obtain ⟨a1, hr, _⟩ := arrResize_ok q16 ((q16.items.length : Int) + ((([] : List Unit).length + 1 : Nat) : Int)) rfl
    (by decide) (by unfold Arr.Fits; decide)
  obtain ⟨hb1, htc, hl1, hx1, _⟩ := arrResize_pos q16 a1 _ hr (by decide)
  have hcl : arrClear a1 = .ok { a1 with items := [], hasBuf := false, allocated := 0 } := by
    unfold arrClear arrResize
    dsimp only
    rw [iteF (by rw [hx1]; simp [q16]), iteF (by rw [hq] at hl1; simp at hl1; omega), iteT rfl]
  have h1 := h conv q16 a1 () [] (.indexError "array assignment index out of range") rfl hr (by
    simp only [conv, hcl, Except.toOption, Option.getD_some]
    unfold storeAfter
    rw [iteF (by decide)]
    simp only [htc]
    rfl)
  rw [hc] at h1
  simp [conv, hcl, Except.toOption, hq] at h1

end PyLean.Sequences
