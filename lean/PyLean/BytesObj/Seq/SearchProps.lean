import PyLean.BytesObj.Seq.ListModel

/-!
`tuple` and `list` search and compare the same way. The C loops differ: a list
rereads its size and slot on every pass and goes through `list_get_item_ref`, and
`list.count` and the list comparison test identity before they compare. When
comparisons leave the list alone, each loop agrees with its tuple twin, for every
element type and every comparison, including one that raises.

`len(l) <= sys.maxsize` is the type invariant used throughout: it is what makes
the unsigned compare in `valid_index` the same as `0 <= i < len`.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α ρ : Type}

theorem validIndex_eq (i n : Int) (hi : -(2 ^ 63 : Int) ≤ i) (hi' : i < 2 ^ 63)
    (hn : 0 ≤ n) (hn' : n ≤ ssizeMax) : validIndex i n = decide (0 ≤ i ∧ i < n) := by
  unfold validIndex ssizeMax at *
  have h2 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  have h3 : (2 : Int) ^ 63 = 9223372036854775808 := by decide
  rw [h2]
  rw [h3] at hi hi' hn'
  by_cases h : 0 ≤ i
  · have e1 : i % 18446744073709551616 = i := Int.emod_eq_of_lt h (by omega)
    have e2 : n % 18446744073709551616 = n := Int.emod_eq_of_lt hn (by omega)
    rw [e1, e2]
    simp [h]
  · have e1 : i % 18446744073709551616 = i + 18446744073709551616 := by omega
    have e2 : n % 18446744073709551616 = n := Int.emod_eq_of_lt hn (by omega)
    rw [e1, e2]
    simp only [h, false_and, decide_false, decide_eq_false_iff_not]
    omega

theorem slot_nat (l : List α) (i : Nat) : slot l (i : Int) = l[i]? := by
  simp [slot]

/-- `list_get_item_ref` at a non-negative index is plain indexing. -/
theorem listGetItemRef_nat (l : List α) (i : Nat) (hl : (l.length : Int) ≤ ssizeMax)
    (hi : (i : Int) ≤ ssizeMax) : listGetItemRef l (i : Int) = l[i]? := by
  unfold listGetItemRef
  have hv := validIndex_eq (i : Int) l.length (by unfold ssizeMax at *; omega)
    (by unfold ssizeMax at *; omega) (by omega) hl
  rw [hv, slot_nat]
  by_cases h : i < l.length
  · simp [h]
  · have : l[i]? = none := List.getElem?_eq_none (by omega)
    rw [this]
    simp

theorem drop_cons_of_lt (l : List α) (i : Nat) (h : i < l.length) :
    l.drop i = l[i] :: l.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons h]

/-- `list_contains` with a comparison that leaves the list alone is `tuple_contains`
on the rest of the list. -/
theorem containsLoop_pure (E : ElemOps α ρ) (o : LObj α) (el : α)
    (hl : (o.items.length : Int) ≤ ssizeMax) (f i : Nat) (hi : i ≤ o.items.length)
    (hf : o.items.length < i + f) :
    containsLoop (pureCmp E) el f (i : Int) o = (tupleContains E el (o.items.drop i), o) := by
  induction f generalizing i with
  | zero => omega
  | succ f ih =>
    have hg := listGetItemRef_nat o.items i hl (by omega)
    by_cases hi' : i < o.items.length
    · have hget : o.items[i]? = some o.items[i] := List.getElem?_eq_getElem hi'
      rw [containsLoop, hg, hget, drop_cons_of_lt _ _ hi']
      simp only [tupleContains, pureCmp]
      cases hc : richBool E .eq o.items[i] el with
      | error e => rfl
      | ok b =>
        cases b with
        | true => rfl
        | false =>
          have h := ih (i + 1) (by omega) (by omega)
          have hnext : ((i + 1 : Nat) : Int) = (i : Int) + 1 := by omega
          rw [hnext] at h
          exact h
    · have hd : o.items.drop i = [] := List.drop_eq_nil_of_le (by omega)
      have : o.items[i]? = none := List.getElem?_eq_none (by omega)
      rw [containsLoop, hg, this, hd]
      rfl

/-- `x in l` and `x in tuple(l)` agree, for every element type and every comparison
(which may raise), when the comparison does not change the list.
`len(l) <= sys.maxsize` is the type invariant. The operands are `item == x`, item
on the left, in both (gh-81829 made that deliberate). -/
def ContainsAgree : Prop :=
  ∀ (α ρ : Type) (E : ElemOps α ρ) (o : LObj α) (el : α) (fuel : Nat),
    (o.items.length : Int) ≤ ssizeMax → o.items.length < fuel →
      listContains (pureCmp E) fuel o el = (tupleContains E el o.items, o)

theorem containsAgree_proven : ContainsAgree := by
  intro α ρ E o el fuel hl hf
  have := containsLoop_pure E o el hl fuel 0 (by omega) (by omega)
  simpa [listContains] using this

/-- `tupleContains` is "some item compares true before anything raises". -/
theorem tupleContains_true (E : ElemOps α ρ) (el : α) (l : List α)
    (h : tupleContains E el l = .ok true) : ∃ x ∈ l, richBool E .eq x el = .ok true := by
  induction l with
  | nil => simp [tupleContains] at h
  | cons x xs ih =>
    simp only [tupleContains] at h
    cases hc : richBool E .eq x el with
    | error e => rw [hc] at h; simp at h
    | ok b =>
      cases b with
      | true => exact ⟨x, by simp, hc⟩
      | false =>
        rw [hc] at h
        obtain ⟨y, hy, hr⟩ := ih h
        exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

/-- The identity shortcut of `PyObject_RichCompareBool` under `Py_EQ`: an object is in a tuple
that holds that very object at any position, even a NaN-like one, unless an earlier comparison
raises or finds it first. Hypothesis: the comparisons before that position succeed, which is the
case; `tupleContains_exists` is the other direction. -/
def ContainsIdentity : Prop :=
  ∀ (α ρ : Type) (E : ElemOps α ρ) (x y : α) (pre post : List α), E.same y x = true →
    (∀ z ∈ pre, ∃ b, richBool E .eq z x = .ok b) →
    tupleContains E x (pre ++ y :: post) = .ok true

theorem containsIdentity_proven : ContainsIdentity := by
  intro α ρ E x y pre post h hp
  induction pre with
  | nil => simp [tupleContains, richBool, h]
  | cons z zs ih =>
    obtain ⟨b, hb⟩ := hp z (by simp)
    have hr := ih (fun w hw => hp w (by simp [hw]))
    cases b with
    | true => simp [tupleContains, hb]
    | false => simp only [List.cons_append, tupleContains, hb, hr]

/-! ## A comparison that changes the list -/

/-- What a comparison can do is Python code: it can raise, and it can replace the list, but it
cannot produce the model's marker for a C-level fault. -/
def NoFault (cmp : Cmp α) : Prop := ∀ o a b msg, (cmp o a b).1 ≠ .error (cUB msg)

theorem containsLoop_safe (cmp : Cmp α) (hc : NoFault cmp) (el : α) (fuel : Nat) (i : Int) (o : LObj α)
    (msg : String) : (containsLoop cmp el fuel i o).1 ≠ .error (cUB msg) := by
  induction fuel generalizing i o with
  | zero =>
    simp only [containsLoop]
    intro h
    injection h with h
    simp [cUB] at h
    cases h
  | succ fuel ih =>
    simp only [containsLoop]
    cases hg : listGetItemRef o.items i with
    | none => simp
    | some item =>
      simp only
      have hx := hc o item el msg
      rcases hr : cmp o item el with ⟨r, s⟩
      rw [hr] at hx
      simp only at hx
      cases r with
      | ok b =>
        cases b with
        | true => simp
        | false => exact ih _ _
      | error e => exact hx

theorem indexLoop_safe (cmp : Cmp α) (hc : NoFault cmp) (v : α) (stop : Int) (fuel : Nat) (i : Int)
    (o : LObj α) (msg : String) : (indexLoop cmp v stop fuel i o).1 ≠ .error (cUB msg) := by
  induction fuel generalizing i o with
  | zero =>
    simp only [indexLoop]
    intro h
    injection h with h
    simp [cUB] at h
    cases h
  | succ fuel ih =>
    simp only [indexLoop]
    split
    · cases hg : listGetItemRef o.items i with
      | none => simp
      | some item =>
        simp only
        have hx := hc o item v msg
        rcases hr : cmp o item v with ⟨r, s⟩
        rw [hr] at hx
        simp only at hx
        cases r with
        | ok b =>
          cases b with
          | true => simp
          | false => exact ih _ _
        | error e => simpa using hx
    · simp

theorem countLoop_safe (same : α → α → Bool) (cmp : Cmp α) (hc : NoFault cmp) (v : α) (fuel : Nat)
    (i n : Int) (o : LObj α) (msg : String) : (countLoop same cmp v fuel i n o).1 ≠ .error (cUB msg) := by
  induction fuel generalizing i n o with
  | zero =>
    simp only [countLoop]
    intro h
    injection h with h
    simp [cUB] at h
    cases h
  | succ fuel ih =>
    simp only [countLoop]
    cases hg : listGetItemRef o.items i with
    | none => simp
    | some item =>
      simp only
      split
      · exact ih _ _ _
      · have hx := hc o item v msg
        rcases hr : cmp o item v with ⟨r, s⟩
        rw [hr] at hx
        simp only at hx
        cases r with
        | ok b =>
          cases b with
          | true => exact ih _ _ _
          | false => exact ih _ _ _
        | error e => simpa using hx

theorem resizeTo_err (o : LObj α) (items : List α) (e : PyExc) (h : resizeTo o items = .error e) :
    e = memoryError := by
  unfold resizeTo at h
  cases hl : listResize o.allocated o.hasItems o.items.length items.length with
  | ok p =>
    rw [hl] at h
    simp at h
  | error x =>
    rw [hl] at h
    simp only [Except.error.injEq] at h
    subst h
    unfold listResize at hl
    split at hl
    · simp at hl
    · dsimp only at hl
      split at hl
      · simp at hl
      · simpa using hl.symm

theorem listAssSlice_err (o : LObj α) (i j : Int) (v : Option (List α)) (e : PyExc)
    (h : listAssSlice o i j v = .error e) : e = memoryError := by
  unfold listAssSlice at h
  dsimp only at h
  repeat' (split at h)
  all_goals first
    | (simp at h; done)
    | exact resizeTo_err _ _ _ h

theorem memoryError_ne (msg : String) : memoryError ≠ cUB msg := by
  intro h
  injection h with h1
  exact absurd h1 (by decide)

theorem removeLoop_safe (cmp : Cmp α) (hc : NoFault cmp) (v : α) (fuel : Nat) (i : Int) (h0 : 0 ≤ i)
    (o : LObj α) (msg : String) : (removeLoop cmp v fuel i o).1 ≠ .error (cUB msg) := by
  induction fuel generalizing i o with
  | zero =>
    simp only [removeLoop]
    intro h
    injection h with h
    simp [cUB] at h
    cases h
  | succ fuel ih =>
    simp only [removeLoop]
    split
    · rename_i hlt
      have hlt' : i.toNat < o.items.length := by omega
      have hs : slot o.items i = some o.items[i.toNat] := by simp [slot, h0, hlt']
      rw [hs]
      simp only
      have hx := hc o o.items[i.toNat] v msg
      rcases hr : cmp o o.items[i.toNat] v with ⟨r, s⟩
      rw [hr] at hx
      simp only at hx
      cases r with
      | ok b =>
        cases b with
        | true =>
          simp only
          cases ha : listAssSlice s i (i + 1) none with
          | ok x => simp
          | error e =>
            have := listAssSlice_err _ _ _ _ _ ha
            subst this
            simpa using memoryError_ne msg
        | false => exact ih _ (by omega) _
      | error e => simpa using hx
    · simp [PyLean.Sequences.cUB, cUB]

/-- `cmp_loop` rereads sizes and slots on every pass, so a comparison that changes either list
cannot make it read outside them. -/
theorem cmpLoop_safe (same : α → α → Bool) (cmp : Cmp2 α) (hc : ∀ st a b msg, (cmp st a b).1 ≠ .error (cUB msg))
    (fuel : Nat) (i : Int) (h0 : 0 ≤ i) (st : List α × List α) (msg : String) :
    (cmpLoop same cmp fuel i st).1 ≠ .error (cUB msg) := by
  induction fuel generalizing i st with
  | zero =>
    simp only [cmpLoop]
    intro h
    injection h with h
    simp [cUB] at h
    cases h
  | succ fuel ih =>
    simp only [cmpLoop]
    split
    · rename_i hlt
      have h1 : i.toNat < st.1.length := by omega
      have h2 : i.toNat < st.2.length := by omega
      have hs1 : slot st.1 i = some st.1[i.toNat] := by simp [slot, h0, h1]
      have hs2 : slot st.2 i = some st.2[i.toNat] := by simp [slot, h0, h2]
      rw [hs1, hs2]
      simp only
      split
      · exact ih _ (by omega) _
      · have hx := hc st st.1[i.toNat] st.2[i.toNat] msg
        rcases hr : cmp st st.1[i.toNat] st.2[i.toNat] with ⟨r, s⟩
        rw [hr] at hx
        simp only at hx
        cases r with
        | ok b =>
          cases b with
          | true => exact ih _ (by omega) _
          | false => simp
        | error e => simpa using hx
    · simp

/-- `x in l`, `l.index`, `l.count`, `l.remove` and the search of `l == r` on a comparison that can do
anything Python can: raise, and change the list, however often. No path reads outside the items, in
the C sense. The list is reread on each pass (`list_get_item_ref`, the size tests of :3361-3382
and :3416-3432), which is what these functions are written for; `l.remove` then deletes with the old
index on the current list, and `list_ass_slice` clips it. Hypothesis: `NoFault`. -/
def ListSearchSafe : Prop :=
  ∀ (α : Type) (cmp : Cmp α) (cmp2 : Cmp2 α) (same : α → α → Bool) (o : LObj α) (x : α) (fuel : Nat)
    (stop : Int) (v w : List α) (msg : String), NoFault cmp →
    (∀ st a b m, (cmp2 st a b).1 ≠ .error (cUB m)) →
    (listContains cmp fuel o x).1 ≠ .error (cUB msg) ∧
    (indexLoop cmp x stop fuel 0 o).1 ≠ .error (cUB msg) ∧
    (listCount same cmp fuel o x).1 ≠ .error (cUB msg) ∧
    (listRemove cmp fuel o x).1 ≠ .error (cUB msg) ∧
    (cmpLoop same cmp2 fuel 0 (v, w)).1 ≠ .error (cUB msg)

theorem listSearchSafe_proven : ListSearchSafe := by
  intro α cmp cmp2 same o x fuel stop v w msg hc hc2
  exact ⟨containsLoop_safe cmp hc x fuel 0 o msg, indexLoop_safe cmp hc x stop fuel 0 o msg,
    countLoop_safe same cmp hc x fuel 0 0 o msg, removeLoop_safe cmp hc x fuel 0 (by omega) o msg,
    cmpLoop_safe same cmp2 hc2 fuel 0 (by omega) (v, w) msg⟩

/-! ## index -/

/-- `indexLoop` with a comparison that leaves the list alone, on the rest of the list. -/
theorem indexLoop_pure (E : ElemOps α ρ) (o : LObj α) (v : α) (stop : Int)
    (hl : (o.items.length : Int) ≤ ssizeMax) (f i : Nat) (hi : i ≤ o.items.length)
    (hf : o.items.length < i + f) :
    indexLoop (pureCmp E) v stop f (i : Int) o =
      (tupleIndexLoop E v stop (o.items.drop i) (i : Int), o) := by
  induction f generalizing i with
  | zero => omega
  | succ f ih =>
    have hg := listGetItemRef_nat o.items i hl (by omega)
    by_cases hi' : i < o.items.length
    · have hget : o.items[i]? = some o.items[i] := List.getElem?_eq_getElem hi'
      rw [indexLoop, drop_cons_of_lt _ _ hi']
      simp only [tupleIndexLoop]
      by_cases hs : (i : Int) < stop
      · simp only [hs, if_true, hg, hget, pureCmp]
        cases hc : richBool E .eq o.items[i] v with
        | error e => rfl
        | ok b =>
          cases b with
          | true => rfl
          | false =>
            have h := ih (i + 1) (by omega) (by omega)
            have hnext : ((i + 1 : Nat) : Int) = (i : Int) + 1 := by omega
            rw [hnext] at h
            exact h
      · simp [hs]
    · have hd : o.items.drop i = [] := List.drop_eq_nil_of_le (by omega)
      have : o.items[i]? = none := List.getElem?_eq_none (by omega)
      rw [indexLoop, hd]
      simp only [tupleIndexLoop]
      by_cases hs : (i : Int) < stop
      · simp [hs, hg, this]
      · simp [hs]

/-- A `start` at or past the end finds nothing, without a comparison. -/
theorem indexLoop_past (E : ElemOps α ρ) (o : LObj α) (v : α) (stop : Int)
    (hl : (o.items.length : Int) ≤ ssizeMax) (f i : Nat) (hi : o.items.length ≤ i)
    (hi' : (i : Int) ≤ ssizeMax) (hf : 0 < f) :
    indexLoop (pureCmp E) v stop f (i : Int) o = (.ok none, o) := by
  cases f with
  | zero => omega
  | succ f =>
    have hg := listGetItemRef_nat o.items i hl hi'
    have : o.items[i]? = none := List.getElem?_eq_none (by omega)
    rw [indexLoop]
    by_cases hs : (i : Int) < stop
    · simp [hs, hg, this]
    · simp [hs]

/-- Where the two sets of bounds can differ, the loop cannot tell. -/
theorem tupleIndexLoop_stop (E : ElemOps α ρ) (v : α) (xs : List α) (i n stop stop' : Int)
    (hi : 0 ≤ i) (hlen : i + xs.length = n)
    (h : (stop' ≤ 0 ∧ stop ≤ 0) ∨ stop' = stop ∨ (stop = n ∧ n ≤ stop')) :
    tupleIndexLoop E v stop xs i = tupleIndexLoop E v stop' xs i := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons] at hlen
    simp only [tupleIndexLoop]
    have hsame : i < stop ↔ i < stop' := by
      rcases h with ⟨h1, h2⟩ | h1 | ⟨h1, h2⟩ <;> omega
    by_cases hs : i < stop
    · have hs' := hsame.mp hs
      simp only [hs, hs', if_true]
      cases hc : richBool E .eq x v with
      | error e => rfl
      | ok b =>
        cases b with
        | true => rfl
        | false => exact ih (i + 1) (by omega) (by omega)
    · have hs' : ¬ i < stop' := fun h' => hs (hsame.mpr h')
      simp [hs, hs']

/-- The start is the same in both, and in range for the loop; the stops differ only
for a negative `stop`, which `list.index` clips at 0 and `tuple.index` does not, and
past the end, which `tuple.index` clips and `list.index` does not. -/
theorem index_bounds (n : Int) (start stop : Option Int) (hn : 0 ≤ n) (hn' : n ≤ ssizeMax) :
    (listIndexBounds n start stop).1 = (tupleIndexBounds n start stop).1 ∧
    0 ≤ (tupleIndexBounds n start stop).1 ∧
    (tupleIndexBounds n start stop).1 ≤ ssizeMax ∧
    (((listIndexBounds n start stop).2 ≤ 0 ∧ (tupleIndexBounds n start stop).2 ≤ 0) ∨
      (listIndexBounds n start stop).2 = (tupleIndexBounds n start stop).2 ∨
      ((tupleIndexBounds n start stop).2 = n ∧ n ≤ (listIndexBounds n start stop).2)) := by
  simp only [listIndexBounds, tupleIndexBounds]
  have ha : PyLean.Sequences.sliceIndex (start.getD 0) ≤ ssizeMax := by
    unfold PyLean.Sequences.sliceIndex PyLean.RangeSlice.clampSsize ssizeMax ssizeMin
    split <;> (try split) <;> omega
  generalize PyLean.Sequences.sliceIndex (start.getD 0) = a at ha ⊢
  generalize PyLean.Sequences.sliceIndex (stop.getD ssizeMax) = b
  refine ⟨trivial, ?_, ?_, ?_⟩
  · split
    · split <;> omega
    · omega
  · split
    · split <;> omega
    · omega
  · by_cases h3 : b < 0
    · simp only [h3, if_true]
      by_cases h4 : b + n < 0
      · rw [if_pos h4]
        exact Or.inl ⟨by omega, by omega⟩
      · rw [if_neg h4]
        exact Or.inr (Or.inl rfl)
    · simp only [h3, if_false]
      by_cases h5 : b > n
      · rw [if_pos h5]
        exact Or.inr (Or.inr ⟨rfl, by omega⟩)
      · rw [if_neg h5]
        exact Or.inr (Or.inl rfl)

/-- `list.index` and `tuple.index` find the same position or fail the same way, for
every element type, every comparison (which may raise) and every int `start` and
`stop`, when the comparison does not change the list. The `ValueError` text is the
one thing they do not share, so the statement compares the search itself: `none`
is what raises it, and a raising `__eq__` cannot be mistaken for it, whatever its
message says. `len(l) <= sys.maxsize` is the type invariant. -/
def IndexAgree : Prop :=
  ∀ (α ρ : Type) (E : ElemOps α ρ) (o : LObj α) (v : α) (start stop : Option Int) (fuel : Nat),
    (o.items.length : Int) ≤ ssizeMax → o.items.length < fuel →
    (indexLoop (pureCmp E) v (listIndexBounds o.items.length start stop).2 fuel
        (listIndexBounds o.items.length start stop).1 o).1 =
      tupleIndexLoop E v (tupleIndexBounds o.items.length start stop).2
        (o.items.drop (tupleIndexBounds o.items.length start stop).1.toNat)
        (tupleIndexBounds o.items.length start stop).1

theorem indexAgree_proven : IndexAgree := by
  intro α ρ E o v start stop fuel hl hf
  obtain ⟨h1, h2, h3, h4⟩ := index_bounds o.items.length start stop (by omega) hl
  rw [h1]
  generalize (tupleIndexBounds o.items.length start stop).1 = a at h2 h3 ⊢
  generalize (tupleIndexBounds o.items.length start stop).2 = b at h4 ⊢
  generalize (listIndexBounds o.items.length start stop).2 = b' at h4 ⊢
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h2
  simp only [Int.toNat_natCast]
  by_cases hover : o.items.length ≤ k
  · rw [indexLoop_past E o v b' hl fuel k hover h3 (by omega),
      List.drop_eq_nil_of_le hover]
    rfl
  · rw [indexLoop_pure E o v b' hl fuel k (by omega) (by omega)]
    simp only
    exact (tupleIndexLoop_stop E v _ _ o.items.length b b' (by omega)
      (by simp only [List.length_drop]; omega) h4).symm

/-! ## count -/

theorem countLoop_pure (E : ElemOps α ρ) (o : LObj α) (v : α)
    (hl : (o.items.length : Int) ≤ ssizeMax) (f i : Nat) (count : Int) (hi : i ≤ o.items.length)
    (hf : o.items.length < i + f) :
    countLoop E.same (pureCmp E) v f (i : Int) count o =
      (tupleCount E v (o.items.drop i) count, o) := by
  induction f generalizing i count with
  | zero => omega
  | succ f ih =>
    have hg := listGetItemRef_nat o.items i hl (by omega)
    have hnext : ((i + 1 : Nat) : Int) = (i : Int) + 1 := by omega
    by_cases hi' : i < o.items.length
    · have hget : o.items[i]? = some o.items[i] := List.getElem?_eq_getElem hi'
      rw [countLoop, hg, hget, drop_cons_of_lt _ _ hi']
      simp only [tupleCount]
      by_cases hs : E.same o.items[i] v = true
      · have hr : richBool E .eq o.items[i] v = .ok true := by simp [richBool, hs]
        simp only [hs, if_true, hr]
        have h := ih (i + 1) (count + 1) (by omega) (by omega)
        rw [hnext] at h
        exact h
      · simp only [hs, if_false, pureCmp]
        cases hc : richBool E .eq o.items[i] v with
        | error e => rfl
        | ok b =>
          cases b with
          | true =>
            have h := ih (i + 1) (count + 1) (by omega) (by omega)
            rw [hnext] at h
            exact h
          | false =>
            have h := ih (i + 1) count (by omega) (by omega)
            rw [hnext] at h
            exact h
    · have hd : o.items.drop i = [] := List.drop_eq_nil_of_le (by omega)
      have : o.items[i]? = none := List.getElem?_eq_none (by omega)
      rw [countLoop, hg, this, hd]
      rfl

/-- `list.count` and `tuple.count` agree, for every element type and comparison
(which may raise), when the comparison does not change the list. The explicit
`obj == value` test of `list_count_impl` (listobject.c:3334) is the same as the
shortcut inside `PyObject_RichCompareBool`, which `tuple_count_impl` relies on. -/
def CountAgree : Prop :=
  ∀ (α ρ : Type) (E : ElemOps α ρ) (o : LObj α) (v : α) (fuel : Nat),
    (o.items.length : Int) ≤ ssizeMax → o.items.length < fuel →
      listCount E.same (pureCmp E) fuel o v = (tupleCount E v o.items 0, o)

theorem countAgree_proven : CountAgree := by
  intro α ρ E o v fuel hl hf
  have := countLoop_pure E o v hl fuel 0 0 (by omega) (by omega)
  simpa [listCount] using this

end PyLean.BytesObj.Seq
