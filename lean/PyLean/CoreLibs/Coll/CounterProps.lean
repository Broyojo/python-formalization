import PyLean.CoreLibs.Coll.CounterLemmas

/-!
Properties of `Counter`, part 1: counting, `update`, `subtract`, `total`, copies,
`__delitem__`, and the rich comparisons. Hypotheses of the form `D.WF` are the dict type
invariant: a key occurs once.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PyLean.CoreLibs.Coll

open PyLean D

variable {κ : Type} [DecidableEq κ]

/-! ### `_count_elements`: Python twin, C fast path, C slow path -/

theorem cFast_eq_py (m : Ctr κ) (xs : List κ) : countElementsCFast m xs = countElementsPy m xs := by
  unfold countElementsCFast countElementsPy
  congr 1
  funext m e
  cases h : D.get? m e <;> simp [cGet0, h]

theorem cSlow_eq_py (m : Ctr κ) (xs : List κ) : countElementsCSlow m xs = countElementsPy m xs := by
  unfold countElementsCSlow countElementsPy
  congr 1
  funext m e
  simp only
  congr 1
  split <;> omega

/-- The three implementations of `_count_elements` write the same dict, keys in
the same order: the C fast path (Modules/_collectionsmodule.c:2572-2617), the C slow path
(:2618-2644) and the Python original (Lib/collections/__init__.py:540-544). -/
def CountElementsTwins : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (m : Ctr κ) (xs : List κ),
    countElementsCFast m xs = countElementsPy m xs ∧ countElementsCSlow m xs = countElementsPy m xs

theorem countElementsTwins_proven : CountElementsTwins :=
  fun _ _ m xs => ⟨cFast_eq_py m xs, cSlow_eq_py m xs⟩

theorem cGet_countPy (m : Ctr κ) (xs : List κ) (x : κ) :
    cGet (countElementsPy m xs) x = cGet m x + xs.count x := by
  induction xs generalizing m with
  | nil => simp [countElementsPy]
  | cons e t ih =>
    have : countElementsPy m (e :: t) = countElementsPy (D.set m e (cGet m e + 1)) t := rfl
    rw [this, ih, cGet_set, List.count_cons]
    by_cases h : e = x
    · subst h; simp; omega
    · simp [h]

theorem cGet_count (m : Ctr κ) (xs : List κ) (x : κ) :
    cGet (countElements m xs) x = cGet m x + xs.count x := by
  rw [countElements, cFast_eq_py, cGet_countPy]

/-! ### `update` and `subtract` -/

@[simp] theorem cGet_nil (x : κ) : cGet ([] : Ctr κ) x = 0 := rfl

/-- The `Mapping` loop of `update` on a non-empty counter. -/
def slowLoop (items : List (κ × Int)) (c : Ctr κ) : Ctr κ :=
  items.foldl (fun c p => D.set c p.1 (p.2 + cGet0 c p.1)) c

theorem slowLoop_fresh {items : List (κ × Int)} {c : Ctr κ} (h : WF items)
    (hf : ∀ x ∈ keys items, x ∉ keys c) : slowLoop items c = c ++ items := by
  induction items generalizing c with
  | nil => simp [slowLoop]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hn := notMem_of_cons h
    have hfa : a ∉ keys c := hf a (by simp)
    have h0 : cGet0 c a = 0 := cGet_eq_zero hfa
    have : slowLoop ((a, b) :: t) c = slowLoop t (c ++ [(a, b)]) := by
      show slowLoop t (D.set c a (b + cGet0 c a)) = _
      rw [h0, Int.add_zero, D.set_of_notMem _ hfa]
    rw [this, ih (WF_of_cons h)]
    · simp
    · intro x hx
      simp only [keys_append, keys_cons, keys_nil, List.mem_append, List.mem_singleton, not_or]
      refine ⟨hf x (by simp [hx]), ?_⟩
      intro e
      rw [e] at hx
      exact hn hx

/-- `Counter.update` on a mapping takes a fast path when the counter is empty
(`super().update(iterable)`, :705) instead of adding count by count (:700-702).
The two paths build the same dict, keys in the same order, for every dict of
int counts. -/
def UpdateFastEqSlow : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (items : List (κ × Int)), WF items →
    D.update [] items = slowLoop items []

theorem updateFastEqSlow_proven : UpdateFastEqSlow := by
  intro κ _ items h
  rw [slowLoop_fresh h (by simp), D.update_fresh h (by simp)]

theorem update_nil {items : List (κ × Int)} (h : WF items) : D.update [] items = items := by
  rw [D.update_fresh h (by simp)]; rfl

theorem cGet_slow (items : List (κ × Int)) (h : WF items) (c : Ctr κ) (x : κ) :
    cGet (slowLoop items c) x = cGet c x + cGet items x := by
  induction items generalizing c with
  | nil => simp [slowLoop, cGet]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hn := notMem_of_cons h
    have : slowLoop ((a, b) :: t) c = slowLoop t (D.set c a (b + cGet0 c a)) := rfl
    rw [this, ih (WF_of_cons h), cGet_set]
    by_cases hax : a = x
    · subst hax
      have h0 : cGet t a = 0 := cGet_eq_zero hn
      have h1 : cGet ((a, b) :: t) a = b := by simp [cGet, get?_cons]
      have hc0 : cGet0 c a = cGet c a := rfl
      simp only [ite_true, h0, h1, hc0]
      omega
    · have h1 : cGet ((a, b) :: t) x = cGet t x := by simp [cGet, get?_cons, hax]
      simp [hax, h1]

theorem updateMapping_eq (c : Ctr κ) (items : List (κ × Int)) (h : WF items) :
    updateMapping c items = slowLoop items c := by
  unfold updateMapping
  by_cases hc : c = []
  · subst hc
    simp only [ne_eq, not_true_eq_false, if_false]
    rw [update_nil h, slowLoop_fresh h (by simp)]; rfl
  · simp [hc, slowLoop]

/-- The value a source contributes to the count of `x`. -/
def srcVal (s : Src κ) (x : κ) : Int :=
  match s with
  | .none => 0
  | .mapping items => cGet items x
  | .iter xs => xs.count x

/-- A `Mapping` source has unique keys; an iterable may repeat elements. -/
def SrcWF : Src κ → Prop
  | .mapping items => WF items
  | _ => True

theorem cGet_updateSrc (c : Ctr κ) (s : Src κ) (hs : SrcWF s) (x : κ) :
    cGet (updateSrc c s) x = cGet c x + srcVal s x := by
  cases s with
  | none => simp [updateSrc, srcVal]
  | mapping items => simp only [updateSrc, srcVal, updateMapping_eq c items hs, cGet_slow items hs]
  | iter xs => simp [updateSrc, srcVal, cGet_count]

theorem cGet_update (c : Ctr κ) (s : Src κ) (k : List (κ × Int)) (hs : SrcWF s) (hk : WF k) (x : κ) :
    cGet (update c s k) x = cGet c x + srcVal s x + cGet k x := by
  unfold update
  simp only
  by_cases hk0 : k = []
  · subst hk0
    simp [cGet_updateSrc c s hs x]
  · simp only [ne_eq, hk0, not_false_eq_true, if_true]
    rw [updateMapping_eq _ _ hk, cGet_slow _ hk, cGet_updateSrc c s hs x]

/-- `Counter.update` adds counts: for every counter (zero and negative counts
included), every source and every keyword dict, the count of `x` afterwards is its count
before plus what the sources bring. `Counter(src, **kw)` is the case of an
empty counter, `self[x]` for a missing `x` being 0. Docstrings at :605-615, :678. -/
def UpdateAddsCounts : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (c : Ctr κ) (s : Src κ) (k : List (κ × Int)) (x : κ),
    SrcWF s → WF k →
      cGet (update c s k) x = cGet c x + srcVal s x + cGet k x ∧
      cGet (counterNew s k) x = srcVal s x + cGet k x

theorem updateAddsCounts_proven : UpdateAddsCounts := by
  intro κ _ c s k x hs hk
  refine ⟨cGet_update c s k hs hk x, ?_⟩
  have := cGet_update [] s k hs hk x
  simpa [counterNew, cGet] using this

theorem keys_step {β : Type} (m : D κ Int) (d : D κ β) (e : κ) (v : Int) (w : β) (h : keys m = keys d) :
    keys (D.set m e v) = keys (D.set d e w) := by
  rw [D.keys_set, D.keys_set, h]

/-- `Counter(iterable)` lists its elements in first-seen order, the order of
`dict.fromkeys(iterable)`. Doc/library/collections.rst: "Elements are counted from
an iterable or added-in from another mapping (or counter)", and "Changed in
version 3.7: As a dict subclass, Counter inherited the capability to remember
insertion order". -/
def CounterFirstSeenOrder : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (xs : List κ),
    keys (counterNew (.iter xs) []) = keys (D.fromkeys xs ())

theorem counterFirstSeenOrder_proven : CounterFirstSeenOrder := by
  intro κ _ xs
  have gen : ∀ (m : Ctr κ) (d : D κ Unit), keys m = keys d →
      keys (countElementsPy m xs) = keys (xs.foldl (fun d x => D.set d x ()) d) := by
    induction xs with
    | nil => intro m d h; exact h
    | cons e t ih =>
      intro m d h
      exact ih _ _ (keys_step m d e _ () h)
  simp only [counterNew, update, updateSrc, countElements, cFast_eq_py]
  simpa [D.fromkeys] using gen [] [] rfl

theorem cGet_subMap (items : List (κ × Int)) (hs : WF items) (c : Ctr κ) (x : κ) :
    cGet (items.foldl (fun c p => D.set c p.1 (cGet0 c p.1 - p.2)) c) x = cGet c x - cGet items x := by
  induction items generalizing c with
  | nil => simp
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hn := notMem_of_cons hs
    simp only [List.foldl_cons]
    rw [ih (WF_of_cons hs), cGet_set]
    by_cases hax : a = x
    · subst hax
      have h0 : cGet t a = 0 := cGet_eq_zero hn
      have h1 : cGet ((a, b) :: t) a = b := by simp [cGet, get?_cons]
      have hc0 : cGet0 c a = cGet c a := rfl
      simp only [ite_true, h0, h1, hc0]
      omega
    · have h1 : cGet ((a, b) :: t) x = cGet t x := by simp [cGet, get?_cons, hax]
      simp [hax, h1]

theorem cGet_subIter (xs : List κ) (c : Ctr κ) (x : κ) :
    cGet (xs.foldl (fun c e => D.set c e (cGet0 c e - 1)) c) x = cGet c x - xs.count x := by
  induction xs generalizing c with
  | nil => simp
  | cons e t ih =>
    simp only [List.foldl_cons]
    rw [ih, cGet_set, List.count_cons]
    by_cases h : e = x
    · subst h
      have hc0 : cGet0 c e = cGet c e := rfl
      simp [hc0]; omega
    · simp [h]

theorem cGet_subtractSrc (c : Ctr κ) (s : Src κ) (hs : SrcWF s) (x : κ) :
    cGet (subtractSrc c s) x = cGet c x - srcVal s x := by
  cases s with
  | none => simp [subtractSrc, srcVal]
  | mapping items => exact cGet_subMap items hs c x
  | iter xs => exact cGet_subIter xs c x

theorem cGet_subtract (c : Ctr κ) (s : Src κ) (k : List (κ × Int)) (hs : SrcWF s) (hk : WF k) (x : κ) :
    cGet (subtract c s k) x = cGet c x - srcVal s x - cGet k x := by
  unfold subtract
  simp only
  by_cases hk0 : k = []
  · subst hk0
    simp [cGet_subtractSrc c s hs x]
  · simp only [ne_eq, hk0, not_false_eq_true, if_true]
    rw [cGet_subtractSrc _ (.mapping k) hk, cGet_subtractSrc c s hs x]
    rfl

/-- `subtract` undoes `update`: "Like dict.update() but subtracts counts instead
of replacing them", :721. The result can hold zero counts for new keys, and is `==`
to the original, since `Counter.__eq__` treats missing as zero. -/
def SubtractUndoesUpdate : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (c : Ctr κ) (s : Src κ) (k : List (κ × Int)) (x : κ),
    SrcWF s → WF k →
      cGet (subtract c s k) x = cGet c x - srcVal s x - cGet k x ∧
      cGet (subtract (update c s k) s k) x = cGet c x

theorem subtractUndoesUpdate_proven : SubtractUndoesUpdate := by
  intro κ _ c s k x hs hk
  refine ⟨cGet_subtract c s k hs hk x, ?_⟩
  rw [cGet_subtract _ s k hs hk, cGet_update c s k hs hk]
  omega

/-! ### `total` -/

theorem total_eq_sum (c : Ctr κ) : total c = (values c).sum := by
  unfold total
  have : ∀ (l : List Int) (acc : Int), l.foldl (· + ·) acc = acc + l.sum := by
    intro l
    induction l with
    | nil => simp
    | cons h t ih => intro acc; simp [ih]; omega
  rw [this]; simp

theorem sum_set_add (d : Ctr κ) (e : κ) (v : Int) :
    (values (D.set d e (cGet d e + v))).sum = (values d).sum + v := by
  induction d with
  | nil => simp [D.set, values, cGet]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : a = e
    · subst h
      simp [D.set, values, cGet, get?_cons]; omega
    · have hg : cGet ((a, b) :: t) e = cGet t e := by simp [cGet, get?_cons, h]
      rw [hg]
      simp only [D.set, h, if_false]
      simp only [values, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]; omega

theorem total_set_add (d : Ctr κ) (e : κ) (v : Int) :
    total (D.set d e (cGet d e + v)) = total d + v := by
  rw [total_eq_sum, total_eq_sum, sum_set_add]

/-- `total()` tracks `update`: counting `n` elements raises the total by `n`, and
merging a mapping raises it by that mapping's total, on every counter. -/
def TotalTracksUpdate : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (c : Ctr κ),
    (∀ xs : List κ, total (update c (.iter xs) []) = total c + xs.length) ∧
    (∀ items : List (κ × Int), WF items → total (update c (.mapping items) []) = total c + total items)

theorem totalTracksUpdate_proven : TotalTracksUpdate := by
  intro κ _ c
  constructor
  · intro xs
    simp only [update, updateSrc, ne_eq, not_true_eq_false, if_false, countElements, cFast_eq_py]
    induction xs generalizing c with
    | nil => simp [countElementsPy]
    | cons e t ih =>
      have : countElementsPy c (e :: t) = countElementsPy (D.set c e (cGet c e + 1)) t := rfl
      rw [this, ih, total_set_add]
      simp; omega
  · intro items h
    simp only [update, updateSrc, ne_eq, not_true_eq_false, if_false]
    rw [updateMapping_eq _ _ h]
    induction items generalizing c with
    | nil => simp [slowLoop, total, values]
    | cons p t ih =>
      obtain ⟨a, b⟩ := p
      have hs : slowLoop ((a, b) :: t) c = slowLoop t (D.set c a (b + cGet0 c a)) := rfl
      have e1 : b + cGet0 c a = cGet c a + b := by simp only [cGet0, cGet]; omega
      rw [hs, ih _ (WF_of_cons h), e1, total_set_add, total_eq_sum t, total_eq_sum ((a, b) :: t)]
      simp [values]; omega

/-! ### Copies -/

/-- `copy()` and the `__reduce__` payload preserve items and their order: on
every counter, `c.copy()` and `Counter(c.__reduce__()[1][0])` have the same items
as `c`, zero and negative counts included. -/
def CopyReduceFaithful : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (c : Ctr κ), WF c →
    counterCopy c = c ∧ counterReduce c = c ∧ counterNew (.mapping (counterReduce c)) [] = c

theorem copyReduceFaithful_proven : CopyReduceFaithful := by
  intro κ _ c h
  have h1 : counterCopy c = c := by
    simp [counterCopy, counterNew, update, updateSrc, updateMapping, update_nil h]
  have h2 : counterReduce c = c := update_nil h
  refine ⟨h1, h2, ?_⟩
  rw [h2]; exact h1

/-! ### `__delitem__` -/

/-- `del c[e]` is total, unlike on a plain dict, and removes exactly `e`
(docstring :755). -/
def DelitemTotal : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (c : Ctr κ) (e : κ), WF c →
    WF (delitem c e) ∧ e ∉ keys (delitem c e) ∧
    (∀ x, x ≠ e → cGet (delitem c e) x = cGet c x) ∧
    (e ∉ keys c → delitem c e = c)

theorem delitemTotal_proven : DelitemTotal := by
  intro κ _ c e h
  have hg : ∀ x, cGet (delitem c e) x = if e = x then 0 else cGet c x := by
    intro x
    unfold delitem
    cases hm : D.mem c e with
    | true =>
      simp only [ite_true, cGet, get?_del h]
      split <;> simp
    | false =>
      have hx := D.mem_false_iff.mp hm
      simp only [Bool.false_eq_true, if_false]
      split
      · next he => subst he; exact cGet_eq_zero hx
      · rfl
  have hwf : WF (delitem c e) := by
    unfold delitem
    split
    · exact D.WF_del h e
    · exact h
  refine ⟨hwf, ?_, ?_, ?_⟩
  · unfold delitem
    split
    · next hm =>
      intro hm2
      have := D.get?_del h e e
      simp only [ite_true] at this
      exact (D.get?_eq_none_iff.mp this) hm2
    · next hm => exact D.mem_false_iff.mp (by simpa using hm)
  · intro x hx
    rw [hg x]
    have : ¬ e = x := fun h => hx h.symm
    simp [this]
  · intro hx
    unfold delitem
    have : D.mem c e = false := D.mem_false_iff.mpr hx
    simp [this]

/-! ### Rich comparison -/

theorem cmpAll_iff (r : Int → Int → Bool) (h0 : r 0 0 = true) (a b : Ctr κ) :
    cmpAll r a b = true ↔ ∀ x, r (cGet a x) (cGet b x) = true := by
  simp only [cmpAll, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩ x
    by_cases ha : x ∈ keys a
    · obtain ⟨p, hp, e⟩ := List.mem_map.mp ha
      have := h1 p hp
      rwa [e] at this
    · by_cases hb : x ∈ keys b
      · obtain ⟨p, hp, e⟩ := List.mem_map.mp hb
        have := h2 p hp
        rwa [e] at this
      · rw [cGet_eq_zero ha, cGet_eq_zero hb]; exact h0
  · intro h
    exact ⟨fun p _ => h p.1, fun p _ => h p.1⟩

theorem eqC_iff (a b : Ctr κ) : eqC a b = true ↔ ∀ x, cGet a x = cGet b x := by
  have := cmpAll_iff (fun x y => decide (x = y)) (by simp) a b
  simpa [eqC] using this

theorem leC_iff (a b : Ctr κ) : leC a b = true ↔ ∀ x, cGet a x ≤ cGet b x := by
  have := cmpAll_iff (fun x y => decide (x ≤ y)) (by simp) a b
  simpa [leC] using this

theorem geC_iff (a b : Ctr κ) : geC a b = true ↔ ∀ x, cGet b x ≤ cGet a x := by
  have := cmpAll_iff (fun x y => decide (x ≥ y)) (by simp) a b
  simpa [geC] using this

theorem neC_iff (a b : Ctr κ) : neC a b = true ↔ ∃ x, cGet a x ≠ cGet b x := by
  simp only [neC, Bool.not_eq_true']
  rw [← Bool.not_eq_true, eqC_iff]
  simp

/-- The six comparisons are the pointwise orders of the count functions, with
missing as zero. Docstrings at :805-835: "True if all counts agree", "a subset",
"a proper subset", "a superset", "a proper superset". They hold for every pair of
counters, whatever their keys and order, negative counts included. -/
def ComparisonsPointwise : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (a b : Ctr κ),
    (eqC a b = true ↔ ∀ x, cGet a x = cGet b x) ∧
    (neC a b = true ↔ ∃ x, cGet a x ≠ cGet b x) ∧
    (leC a b = true ↔ ∀ x, cGet a x ≤ cGet b x) ∧
    (geC a b = true ↔ ∀ x, cGet b x ≤ cGet a x) ∧
    (ltC a b = true ↔ (∀ x, cGet a x ≤ cGet b x) ∧ ∃ x, cGet a x < cGet b x) ∧
    (gtC a b = true ↔ (∀ x, cGet b x ≤ cGet a x) ∧ ∃ x, cGet b x < cGet a x)

theorem comparisonsPointwise_proven : ComparisonsPointwise := by
  intro κ _ a b
  refine ⟨eqC_iff a b, neC_iff a b, leC_iff a b, geC_iff a b, ?_, ?_⟩
  · simp only [ltC, Bool.and_eq_true, leC_iff, neC_iff]
    constructor
    · rintro ⟨h1, x, hx⟩
      exact ⟨h1, x, by have := h1 x; omega⟩
    · rintro ⟨h1, x, hx⟩
      exact ⟨h1, x, by omega⟩
  · simp only [gtC, Bool.and_eq_true, geC_iff, neC_iff]
    constructor
    · rintro ⟨h1, x, hx⟩
      exact ⟨h1, x, by have := h1 x; omega⟩
    · rintro ⟨h1, x, hx⟩
      exact ⟨h1, x, by omega⟩

/-- The order is a partial order compatible with `==`: `a <= b` and `b <= a`
exactly when `a == b`, `<` and `>` are converses and so are `<=` and `>=`. -/
def ComparisonsAreOrder : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (a b : Ctr κ),
    ((leC a b && leC b a) = eqC a b) ∧ ltC a b = gtC b a ∧ leC a b = geC b a

theorem comparisonsAreOrder_proven : ComparisonsAreOrder := by
  intro κ _ a b
  have hle : leC a b = geC b a := by
    apply Bool.eq_iff_iff.mpr
    rw [leC_iff, geC_iff]
  have hne : neC a b = neC b a := by
    apply Bool.eq_iff_iff.mpr
    rw [neC_iff, neC_iff]
    exact ⟨fun ⟨x, h⟩ => ⟨x, fun e => h e.symm⟩, fun ⟨x, h⟩ => ⟨x, fun e => h e.symm⟩⟩
  refine ⟨?_, ?_, hle⟩
  · apply Bool.eq_iff_iff.mpr
    rw [Bool.and_eq_true, leC_iff, leC_iff, eqC_iff]
    constructor
    · rintro ⟨h1, h2⟩ x
      have := h1 x
      have := h2 x
      omega
    · intro h
      exact ⟨fun x => Int.le_of_eq (h x), fun x => Int.le_of_eq (h x).symm⟩
  · simp only [ltC, gtC, hle, hne]

/-- `Counter.fromkeys` is not a constructor: it raises for every input. Doc: "This
class method is not implemented for Counter objects." -/
def FromkeysUndefined : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (it : List κ) (v : Option Int),
    (counterFromkeys it v : Py (Ctr κ)) = .error (.named "NotImplementedError"
      "Counter.fromkeys() is undefined.  Use Counter(iterable) instead.")

theorem fromkeysUndefined_proven : FromkeysUndefined := fun _ _ _ _ => rfl

end PyLean.CoreLibs.Coll
