import PyLean.CoreLibs.Operator.Copy

/-!
Properties of `copy`.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

/-- The first `n` cells of `h'` are those of `h`. -/
def Keeps (n : Nat) (h h' : Heap) : Prop :=
  n ≤ h'.cells.length ∧ ∀ i, i < n → h'.cells[i]? = h.cells[i]?

theorem Keeps.refl (n : Nat) (h : Heap) (hn : n ≤ h.cells.length) : Keeps n h h := ⟨hn, fun _ _ => rfl⟩

theorem Keeps.trans {n : Nat} {a b c : Heap} (h1 : Keeps n a b) (h2 : Keeps n b c) : Keeps n a c :=
  ⟨h2.1, fun i hi => by rw [h2.2 i hi, h1.2 i hi]⟩

theorem keeps_alloc (n : Nat) (h : Heap) (c : Cell) (hn : n ≤ h.cells.length) : Keeps n h (h.alloc c).1 := by
  refine ⟨by simp [Heap.alloc]; omega, fun i hi => ?_⟩
  simp only [Heap.alloc]
  rw [List.getElem?_append_left (by omega)]

theorem keeps_remember (n : Nat) (h : Heap) (x y : Nat) (hn : n ≤ h.cells.length) :
    Keeps n h (h.remember x y) := ⟨hn, fun _ _ => rfl⟩

theorem keeps_set (n : Nat) (h : Heap) (y : Nat) (c : Cell) (hn : n ≤ h.cells.length) (hy : n ≤ y) :
    Keeps n h (h.set y c) := by
  refine ⟨by simpa [Heap.set] using hn, fun i hi => ?_⟩
  simp only [Heap.set]
  rw [List.getElem?_set_ne (by omega)]

theorem keeps_alloc_rem (n : Nat) (h : Heap) (c : Cell) (x : Nat) (hn : n ≤ h.cells.length) :
    Keeps n h ((h.alloc c).1.remember x (h.alloc c).2) ∧ n ≤ (h.alloc c).2 :=
  ⟨(keeps_alloc n h c hn).trans (keeps_remember n _ x _ (keeps_alloc n h c hn).1), hn⟩

theorem appendTo_keeps (n : Nat) (h h' : Heap) (y i : Nat) (hn : n ≤ h.cells.length) (hy : n ≤ y)
    (e : appendTo h y i = .ok h') : Keeps n h h' := by
  simp only [appendTo] at e
  split at e
  · cases e
    exact keeps_set n h y _ hn hy
  · cases e

theorem setItemOf_keeps (n : Nat) (h h' : Heap) (y k v : Nat) (hn : n ≤ h.cells.length) (hy : n ≤ y)
    (e : setItemOf h y k v = .ok h') : Keeps n h h' := by
  unfold setItemOf at e
  repeat' split at e
  all_goals first
    | (cases e; done)
    | (cases e; exact keeps_set n h y _ hn hy)

theorem setAttrOf_keeps (n : Nat) (h h' : Heap) (y : Nat) (k : AttrKey) (v : Nat) (hn : n ≤ h.cells.length)
    (hy : n ≤ y) (e : setAttrOf h y k v = .ok h') : Keeps n h h' := by
  simp only [setAttrOf] at e
  split at e
  · split at e
    · cases e
    · cases e
      exact keeps_set n h y _ hn hy
  · cases e

theorem updateFrom_keeps (n y : Nat) (hy : n ≤ y) : ∀ (l : List (Nat × Nat)) (h h' : Heap),
    n ≤ h.cells.length → updateFrom y h l = .ok h' → Keeps n h h'
  | [], h, h', hn, e => by
    simp only [updateFrom, Except.ok.injEq] at e
    subst e
    exact Keeps.refl n h hn
  | (k, v) :: rest, h, h', hn, e => by
    simp only [updateFrom] at e
    split at e
    · cases e
    · next h1 h2 =>
      have k1 := setAttrOf_keeps n h h1 y _ _ hn hy h2
      exact k1.trans (updateFrom_keeps n y hy rest h1 h' k1.1 e)

theorem pairOf_keeps (n : Nat) (h h1 : Heap) (i e k v : Nat) (hn : n ≤ h.cells.length)
    (p : pairOf h i e = .ok (h1, k, v)) : Keeps n h h1 := by
  unfold pairOf at p
  split at p
  all_goals (try split at p)
  all_goals (try simp only [reduceCtorEq] at p)
  all_goals (try (simp only [Except.ok.injEq, Prod.mk.injEq] at p; obtain ⟨rfl, -, -⟩ := p))
  all_goals first
    | exact Keeps.refl n _ hn
    | exact (keeps_alloc n h _ hn).trans (keeps_alloc n _ _ (keeps_alloc n h _ hn).1)

theorem updateSeq_keeps (n y : Nat) (hy : n ≤ y) : ∀ (l : List Nat) (i : Nat) (h h' : Heap),
    n ≤ h.cells.length → updateSeq y i h l = .ok h' → Keeps n h h'
  | [], _, h, h', hn, e => by
    simp only [updateSeq, Except.ok.injEq] at e
    subst e
    exact Keeps.refl n h hn
  | x :: rest, i, h, h', hn, e => by
    simp only [updateSeq] at e
    split at e
    · cases e
    · next h1 k v e1 =>
      have k1 := pairOf_keeps n h h1 i x k v hn e1
      split at e
      · cases e
      · split at e
        · cases e
        · next h2 e2 =>
          have k2 := setAttrOf_keeps n h1 h2 y _ _ k1.1 hy e2
          exact (k1.trans k2).trans (updateSeq_keeps n y hy rest _ h2 h' k2.1 e)

theorem dictUpdate_keeps (n y s : Nat) (h h' : Heap) (hn : n ≤ h.cells.length) (hy : n ≤ y)
    (e : dictUpdate h y s = .ok h') : Keeps n h h' := by
  unfold dictUpdate at e
  split at e
  · exact updateFrom_keeps n y hy _ h h' hn e
  · exact updateFrom_keeps n y hy _ h h' hn e
  · exact updateSeq_keeps n y hy _ _ h h' hn e
  · exact updateSeq_keeps n y hy _ _ h h' hn e
  · split at e
    · cases e
      exact Keeps.refl n _ hn
    · cases e
  · cases e

theorem slotSet_keeps (n y : Nat) (hy : n ≤ y) : ∀ (l : List (Nat × Nat)) (h h' : Heap),
    n ≤ h.cells.length → slotSet y h l = .ok h' → Keeps n h h'
  | [], h, h', hn, e => by
    simp only [slotSet, Except.ok.injEq] at e
    subst e
    exact Keeps.refl n h hn
  | (k, v) :: rest, h, h', hn, e => by
    simp only [slotSet] at e
    split at e
    · split at e
      · split at e
        · cases e
        · next h1 e1 =>
          have k1 := setAttrOf_keeps n h h1 y _ _ hn hy e1
          exact k1.trans (slotSet_keeps n y hy rest h1 h' k1.1 e)
      · cases e
    · cases e

theorem stateStep_keeps (n y st : Nat) (h h' : Heap) (hn : n ≤ h.cells.length) (hy : n ≤ y)
    (e : stateStep h y st = .ok h') : Keeps n h h' := by
  unfold stateStep at e
  generalize stateSplit h st = p at e
  obtain ⟨s, slot⟩ := p
  try simp only at e
  split at e
  · cases e
  · next h2 e2 =>
    have k1 : Keeps n h h2 := by
      split at e2
      · cases e2
        exact Keeps.refl n _ hn
      · split at e2
        · exact dictUpdate_keeps n y s h h2 hn hy e2
        · cases e2
    split at e
    · cases e
      exact k1
    · split at e
      · cases e
        exact k1
      · split at e
        · exact k1.trans (slotSet_keeps n y hy _ h2 h' k1.1 e)
        · exact k1.trans (slotSet_keeps n y hy _ h2 h' k1.1 e)
        · cases e

theorem stateApply_keeps (n y st : Nat) (h h' : Heap) (ss : Option (Option PyExc)) (hn : n ≤ h.cells.length)
    (hy : n ≤ y) (e : stateApply h y st ss = .ok h') : Keeps n h h' := by
  unfold stateApply at e
  split at e
  · simp only [setstateOf] at e
    split at e
    · cases e
    · exact setAttrOf_keeps n h h' y _ _ hn hy e
  · exact stateStep_keeps n y st h h' hn hy e

theorem foldl_keeps' {β : Type} (n : Nat) (step : Heap → β → Py Heap)
    (hs : ∀ h h' b, n ≤ h.cells.length → step h b = .ok h' → Keeps n h h') :
    ∀ (l : List β) (a : Py Heap) (h' : Heap),
      (l.foldl (fun (acc : Py Heap) b =>
        match acc with
        | .error e => .error e
        | .ok h => step h b) a) = .ok h' →
      ∃ h0, a = .ok h0 ∧ (n ≤ h0.cells.length → Keeps n h0 h')
  | [], a, h', e => by
    simp only [List.foldl_nil] at e
    exact ⟨h', e, fun hn => Keeps.refl n h' hn⟩
  | b :: bs, a, h', e => by
    simp only [List.foldl_cons] at e
    obtain ⟨h1, e1, k⟩ := foldl_keeps' n step hs bs _ h' e
    cases a with
    | error x => cases e1
    | ok h0 =>
      refine ⟨h0, rfl, fun hn => ?_⟩
      simp only at e1
      have k1 := hs _ _ _ hn e1
      exact k1.trans (k k1.1)

theorem appendAll_keeps (n y : Nat) (hy : n ≤ y) : ∀ (l : List Nat) (h h' : Heap),
    n ≤ h.cells.length → appendAll h y l = .ok h' → Keeps n h h'
  | [], h, h', hn, e => by
    simp only [appendAll, Except.ok.injEq] at e
    subst e
    exact Keeps.refl n h hn
  | i :: rest, h, h', hn, e => by
    simp only [appendAll] at e
    split at e
    · cases e
    · next h1 e1 =>
      have k1 := appendTo_keeps n h h1 y i hn hy e1
      exact k1.trans (appendAll_keeps n y hy rest h1 h' k1.1 e)

theorem setAll_keeps (n y : Nat) (hy : n ≤ y) : ∀ (l : List (Nat × Nat)) (h h' : Heap),
    n ≤ h.cells.length → setAll h y l = .ok h' → Keeps n h h'
  | [], h, h', hn, e => by
    simp only [setAll, Except.ok.injEq] at e
    subst e
    exact Keeps.refl n h hn
  | (k, v) :: rest, h, h', hn, e => by
    simp only [setAll] at e
    split at e
    · cases e
    · next h1 e1 =>
      have k1 := setItemOf_keeps n h h1 y k v hn hy e1
      exact k1.trans (setAll_keeps n y hy rest h1 h' k1.1 e)

theorem reconRest_keeps (n y : Nat) (hy : n ≤ y) (h h' : Heap) (hn : n ≤ h.cells.length) (st : Option Nat)
    (li : Option (ItemsIter Nat)) (di : Option (ItemsIter (Nat × Nat))) (ss : Option (Option PyExc))
    (e : reconRest h y st li di ss = .ok h') : Keeps n h h' := by
  simp only [reconRest] at e
  split at e
  · cases e
  · next h2 h2e =>
    have k1 : Keeps n h h2 := by
      split at h2e
      · cases h2e
        exact Keeps.refl n _ hn
      · split at h2e
        · cases h2e
          exact Keeps.refl n _ hn
        · exact stateApply_keeps n y _ h h2 ss hn hy h2e
    split at e
    · cases e
    · next h4 h4e =>
      have k2 : Keeps n h2 h4 := by
        split at h4e
        · cases h4e
          exact Keeps.refl n _ k1.1
        · split at h4e
          · cases h4e
          · next h5 h5e =>
            have k := appendAll_keeps n y hy _ h2 h5 k1.1 h5e
            split at h4e
            · cases h4e
            · cases h4e
              exact k
      split at e
      · cases e
        exact k1.trans k2
      · split at e
        · cases e
        · next h6 h6e =>
          have k := setAll_keeps n y hy _ h4 h6 k2.1 h6e
          split at e
          · cases e
          · cases e
            exact (k1.trans k2).trans k

theorem keeps_all (n : Nat) : ∀ fuel : Nat,
    (∀ h x h' y, n ≤ h.cells.length → deepcopy fuel h x = .ok (h', y) → Keeps n h h') ∧
    (∀ h l h' ys, n ≤ h.cells.length → deepList fuel h l = .ok (h', ys) → Keeps n h h') ∧
    (∀ h acc l h' ys, n ≤ h.cells.length → deepPairs fuel h acc l = .ok (h', ys) → Keeps n h h') ∧
    (∀ h y l h', n ≤ h.cells.length → n ≤ y → deepAttrs fuel h y l = .ok h' → Keeps n h h') ∧
    (∀ h y l ss h', n ≤ h.cells.length → n ≤ y → deepState fuel h y l ss = .ok h' → Keeps n h h') ∧
    (∀ h y l h', n ≤ h.cells.length → n ≤ y → deepAppend fuel h y l = .ok h' → Keeps n h h') ∧
    (∀ h y l h', n ≤ h.cells.length → n ≤ y → deepSetItems fuel h y l = .ok h' → Keeps n h h') ∧
    (∀ h k h' k', n ≤ h.cells.length → deepKey fuel h k = .ok (h', k') → Keeps n h h')
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h x h' y _ e; simp [deepcopy] at e
    · intro h l h' ys _ e; simp [deepList] at e
    · intro h acc l h' ys _ e; simp [deepPairs] at e
    · intro h y l h' _ _ e; simp [deepAttrs] at e
    · intro h y l ss h' hn _ e
      cases l with
      | none =>
        simp only [deepState, Except.ok.injEq] at e
        subst e
        exact Keeps.refl n _ hn
      | some s =>
        simp only [deepState] at e
        split at e
        · cases e
          exact Keeps.refl n _ hn
        · cases e
    · intro h y l h' _ _ e; simp [deepAppend] at e
    · intro h y l h' _ _ e; simp [deepSetItems] at e
    · intro h k h' k' hn e
      cases k with
      | name s =>
        simp only [deepKey, Except.ok.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, -⟩ := e
        exact Keeps.refl n _ hn
      | obj c => simp [deepKey] at e
  | fuel + 1 => by
    obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7, ih8⟩ := keeps_all n fuel
    have hfresh : ∀ (h : Heap) (c : Cell), n ≤ h.cells.length →
        Keeps n h ((h.alloc c).1) ∧ n ≤ (h.alloc c).2 ∧ n ≤ (h.alloc c).1.cells.length := by
      intro h c hn
      have k := keeps_alloc n h c hn
      exact ⟨k, hn, k.1⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h x h' y hn e
      simp only [deepcopy] at e
      split at e
      · cases e
        exact Keeps.refl n _ hn
      · cases e
        exact Keeps.refl n _ hn
      · cases e
        exact Keeps.refl n _ hn
      · split at e
        · cases e
          exact Keeps.refl n _ hn
        · split at e
          · -- list
            have hk := keeps_alloc_rem n h (.list []) x hn
            split at e
            · cases e
            · next h3 ys e3 =>
              have k2 := ih2 _ _ _ _ hk.1.1 e3
              cases e
              exact (hk.1.trans k2).trans (keeps_set n _ _ _ k2.1 hk.2)
          · -- tuple
            split at e
            · cases e
            · next h1 ys e1 =>
              have k1 := ih2 _ _ _ _ hn e1
              split at e
              · cases e
                exact k1
              · split at e
                · cases e
                  exact k1
                · have hk := keeps_alloc_rem n h1 (.tuple ys) x k1.1
                  cases e
                  exact k1.trans hk.1
          · -- dict
            have hk := keeps_alloc_rem n h (.dict []) x hn
            split at e
            · cases e
            · next h3 ys e3 =>
              have k2 := ih3 _ _ _ _ _ hk.1.1 e3
              cases e
              exact (hk.1.trans k2).trans (keeps_set n _ _ _ k2.1 hk.2)
          · -- frozendict
            split at e
            · cases e
            · next h1 ys e1 =>
              have k1 := ih3 _ _ _ _ _ hn e1
              split at e
              · cases e
                exact k1
              · cases e
                exact k1.trans (keeps_alloc_rem n h1 _ x k1.1).1
          · -- method
            split at e
            · cases e
            · next h1 s' e1 =>
              have k1 := ih1 _ _ _ _ hn e1
              cases e
              exact k1.trans (keeps_alloc_rem n h1 _ x k1.1).1
          · -- class
            cases e
            exact Keeps.refl n _ hn
          · -- class with a metaclass
            cases e
            exact Keeps.refl n _ hn
          · -- plain instance
            have hk := keeps_alloc_rem n h (.inst []) x hn
            split at e
            · cases e
            · next h3 e3 =>
              cases e
              exact hk.1.trans (ih4 _ _ _ _ hk.1.1 hk.2 e3)
          · -- hooked
            split at e
            · cases e
            · have hk := keeps_alloc_rem n h (.atom 1) x hn
              cases e
              exact hk.1
            · split at e
              · cases e
              · cases e
                exact Keeps.refl n _ hn
              · cases e
              · next size fail kind args st li di ss _ =>
                split at e
                · cases e
                · split at e
                  · cases e
                  · next h1 args' e1 =>
                    have k1 := ih2 _ _ _ _ hn e1
                    split at e
                    · cases e
                    · have hk := keeps_alloc_rem n h1 (freshOf kind args') x k1.1
                      split at e
                      · cases e
                      · next h5 e5 =>
                        have k3 := ih5 _ _ _ _ _ hk.1.1 hk.2 e5
                        split at e
                        · cases e
                        · next h6 e6 =>
                          have k5 := ih6 _ _ _ _ k3.1 hk.2 e6
                          split at e
                          · cases e
                          · split at e
                            · cases e
                            · next h7 e7 =>
                              have k6 := ih7 _ _ _ _ k5.1 hk.2 e7
                              split at e
                              · cases e
                              · cases e
                                exact (((k1.trans hk.1).trans k3).trans k5).trans k6
          · cases e
            exact Keeps.refl n _ hn
          · cases e
            exact Keeps.refl n _ hn
    · intro h l h' ys hn e
      cases l with
      | nil =>
        simp only [deepList, Except.ok.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, -⟩ := e
        exact Keeps.refl n _ hn
      | cons a as =>
        simp only [deepList] at e
        split at e
        · cases e
        · next h1 y e1 =>
          have k1 := ih1 _ _ _ _ hn e1
          split at e
          · cases e
          · next h2 ys2 e2 =>
            have k2 := ih2 _ _ _ _ k1.1 e2
            cases e
            exact k1.trans k2
    · intro h acc l h' ys hn e
      cases l with
      | nil =>
        simp only [deepPairs, Except.ok.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, -⟩ := e
        exact Keeps.refl n _ hn
      | cons p rest =>
        obtain ⟨k, v⟩ := p
        simp only [deepPairs] at e
        split at e
        · cases e
        · next h1 v' e1 =>
          have k1 := ih1 _ _ _ _ hn e1
          split at e
          · cases e
          · next h2 k' e2 =>
            have k2 := ih1 _ _ _ _ k1.1 e2
            split at e
            · cases e
            · exact (k1.trans k2).trans (ih3 _ _ _ _ _ k2.1 e)
    · intro h y l h' hn hy e
      cases l with
      | nil =>
        simp only [deepAttrs, Except.ok.injEq] at e
        subst e
        exact Keeps.refl n _ hn
      | cons p rest =>
        obtain ⟨k, v⟩ := p
        simp only [deepAttrs] at e
        split at e
        · cases e
        · next h1 v' e1 =>
          have k1 := ih1 _ _ _ _ hn e1
          split at e
          · cases e
          · next h2 k' e2 =>
            have k2 := ih8 _ _ _ _ k1.1 e2
            split at e
            · cases e
            · next h3 e3 =>
              have k3 := setAttrOf_keeps n _ _ _ _ _ k2.1 hy e3
              exact ((k1.trans k2).trans k3).trans (ih4 _ _ _ _ k3.1 hy e)
    · intro h y l ss h' hn hy e
      cases l with
      | none =>
        simp only [deepState, Except.ok.injEq] at e
        subst e
        exact Keeps.refl n _ hn
      | some s =>
        simp only [deepState] at e
        split at e
        · cases e
          exact Keeps.refl n _ hn
        · split at e
          · cases e
          · next h1 s' e1 =>
            have k1 := ih1 _ _ _ _ hn e1
            exact k1.trans (stateApply_keeps n y s' h1 h' ss k1.1 hy e)
    · intro h y l h' hn hy e
      cases l with
      | nil =>
        simp only [deepAppend, Except.ok.injEq] at e
        subst e
        exact Keeps.refl n _ hn
      | cons i rest =>
        simp only [deepAppend] at e
        split at e
        · cases e
        · next h1 i' e1 =>
          have k1 := ih1 _ _ _ _ hn e1
          split at e
          · cases e
          · next h2 e2 =>
            have k2 := appendTo_keeps n _ _ _ _ k1.1 hy e2
            exact (k1.trans k2).trans (ih6 _ _ _ _ k2.1 hy e)
    · intro h y l h' hn hy e
      cases l with
      | nil =>
        simp only [deepSetItems, Except.ok.injEq] at e
        subst e
        exact Keeps.refl n _ hn
      | cons p rest =>
        obtain ⟨k, v⟩ := p
        simp only [deepSetItems] at e
        split at e
        · cases e
        · next h1 k' e1 =>
          have k1 := ih1 _ _ _ _ hn e1
          split at e
          · cases e
          · next h2 v' e2 =>
            have k2 := ih1 _ _ _ _ k1.1 e2
            split at e
            · cases e
            · next h3 e3 =>
              have k3 := setItemOf_keeps n _ _ _ _ _ k2.1 hy e3
              exact ((k1.trans k2).trans k3).trans (ih7 _ _ _ _ k3.1 hy e)
    · intro h k h' k' hn e
      cases k with
      | name s =>
        simp only [deepKey, Except.ok.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, -⟩ := e
        exact Keeps.refl n _ hn
      | obj c =>
        simp only [deepKey] at e
        split at e
        · cases e
        · next h1 c' e1 =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at e
          obtain ⟨rfl, -⟩ := e
          exact ih1 _ _ _ _ hn e1

/-- `deepcopy` leaves the source alone: every cell that existed before the call is the same after it, for any
object graph, cycles included, with `__deepcopy__`, `__reduce_ex__`, constructors and `__setstate__` of all shapes:
everything it writes is on the objects it created. The point of a deep copy. -/
def DeepcopyKeepsSource : Prop :=
  ∀ (fuel : Nat) (h h' : Heap) (x y i : Nat), deepcopy fuel h x = .ok (h', y) → i < h.cells.length →
    h'.cells[i]? = h.cells[i]?

theorem deepcopyKeepsSource_proven : DeepcopyKeepsSource := by
  intro fuel h h' x y i e hi
  exact ((keeps_all h.cells.length fuel).1 h x h' y (Nat.le_refl _) e).2 i hi

theorem get_alloc (h : Heap) (c : Cell) (x : Nat) (hx : x < h.cells.length) : (h.alloc c).1.get x = h.get x := by
  simp [Heap.alloc, Heap.get, List.getD, List.getElem?_append_left hx]

theorem get_of_list (h : Heap) (x : Nat) (l : List Nat) (e : h.get x = .list l) : x < h.cells.length := by
  by_cases hn : x < h.cells.length
  · exact hn
  · have : h.cells[x]? = none := by
      rw [List.getElem?_eq_none_iff]
      omega
    simp [Heap.get, List.getD, this] at e

/-- A list holding itself copies to a new list holding that new list: the memo entry is made before the items are
copied, so the recursion ends and the cycle is rebuilt. An object already in the memo is answered from there with
no other effect, and an atom is itself. `copy` docs: "keeping a memo dictionary". -/
def DeepcopyMemo : Prop :=
  ∀ (fuel : Nat) (h : Heap) (x y : Nat) (n : Int),
    (h.get x = .atom n → deepcopy (fuel + 1) h x = .ok (h, x)) ∧
    (h.memo.lookup x = some y → (∀ m, h.get x ≠ .atom m) → (∀ t, h.get x ≠ .str t) → (∀ m, h.get x ≠ .cls m) →
      deepcopy (fuel + 1) h x = .ok (h, y)) ∧
    (h.get x = .list [x] → h.memo.lookup x = none → ∃ h', deepcopy (fuel + 4) h x = .ok (h', h.cells.length) ∧
      h'.get h.cells.length = .list [h.cells.length])

theorem deepcopyMemo_proven : DeepcopyMemo := by
  intro fuel h x y n
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    simp [deepcopy, hc]
  · intro hl hn hs hc
    rw [deepcopy]
    split
    · next m hm => exact absurd hm (hn m)
    · next m hm => exact absurd hm (hs m)
    · next m hm => exact absurd hm (hc m)
    · simp [hl]
  · intro hc hm
    have hx := get_of_list h x _ hc
    let h1 := (h.alloc (.list [])).1
    let h2 := h1.remember x h.cells.length
    have hg2 : h2.get x = .list [x] := by
      have := get_alloc h (.list []) x hx
      rw [hc] at this
      exact this
    have hl2 : h2.memo.lookup x = some h.cells.length := by simp [h2, Heap.remember, List.lookup]
    have hc2 : deepcopy (fuel + 2) h2 x = .ok (h2, h.cells.length) := by
      rw [deepcopy]
      simp [hg2, hl2]
    have hd : deepList (fuel + 3) h2 [x] = .ok (h2, [h.cells.length]) := by
      simp [deepList, hc2]
    refine ⟨h2.set h.cells.length (.list [h.cells.length]), ?_, ?_⟩
    · rw [deepcopy]
      have halloc : h.alloc (.list []) = (h1, h.cells.length) := rfl
      simp [hc, hm, halloc, h2, hd]
    · simp [Heap.get, Heap.set, h2, h1, Heap.remember, Heap.alloc, List.getD]

/-- A tuple of atoms is its own deep copy, so the identity is kept, the `else: y = x` of `_deepcopy_tuple`; a
tuple that changed is a new tuple. -/
def DeepcopyTupleIdentity : Prop :=
  ∀ (fuel : Nat) (h : Heap) (x : Nat) (items : List Nat), h.get x = .tuple items →
    h.memo.lookup x = none → (∀ i ∈ items, ∃ n, h.get i = .atom n) → items.length ≤ fuel →
    deepcopy (fuel + 2) h x = .ok (h, x)

theorem deepList_atoms (h : Heap) : ∀ (fuel : Nat) (items : List Nat), (∀ i ∈ items, ∃ n, h.get i = .atom n) →
    items.length ≤ fuel → deepList (fuel + 1) h items = .ok (h, items)
  | _, [], _, _ => by simp [deepList]
  | 0, _ :: _, _, hl => by simp at hl
  | fuel + 1, i :: is, ha, hl => by
    obtain ⟨n, hn⟩ := ha i (by simp)
    have h1 : deepcopy (fuel + 1) h i = .ok (h, i) := by simp [deepcopy, hn]
    have h2 := deepList_atoms h fuel is (fun j hj => ha j (List.mem_cons_of_mem _ hj)) (by simpa using hl)
    simp [deepList, h1, h2]

theorem deepcopyTupleIdentity_proven : DeepcopyTupleIdentity := by
  intro fuel h x items hc hm ha hl
  rw [deepcopy]
  simp [hc, hm, deepList_atoms h fuel items ha hl]

/-- `copy` by kind. A list, a dict and an instance become a new object with the same contents, so the items are shared
(`cls.copy(x)`, Lib/copy.py:72-73, and the reduce path of a plain instance); an atom, a `str`, a tuple and a
`frozendict` are themselves (:70-71). A bound method goes through `method.__reduce__`, so the copy is
`getattr(self, name)`: an instance attribute of that name if there is one, which can be any object, else the class's
function bound anew, and `AttributeError` when the class has no such function or `__self__` is not an instance. `__copy__` goes first (:80-82): its exception propagates and its result is the copy. With no
`__copy__`, the reduce value goes to `_reconstruct` (:98-100), a string meaning `x`, a raising reductor propagating, and
with no reductor at all `copy.Error`. -/
def CopyShallow : Prop :=
  ∀ (h : Heap) (x f s v : Nat) (l : List Nat) (d : List (Nat × Nat)) (a : List (AttrKey × Nat)) (e : PyExc)
    (dc : Option (Option PyExc)) (r : Option RvSpec) (rv : RvSpec) (n : Int) (t : String),
    (h.get x = .list l → copyShallow h x = .ok ((h.alloc (.list l)).1, h.cells.length)) ∧
    (h.get x = .dict d → copyShallow h x = .ok ((h.alloc (.dict d)).1, h.cells.length)) ∧
    (h.get x = .inst a → copyShallow h x = .ok ((h.alloc (.inst a)).1, h.cells.length)) ∧
    (h.get x = .tuple l → copyShallow h x = .ok (h, x)) ∧
    (h.get x = .fdict d → copyShallow h x = .ok (h, x)) ∧
    (h.get x = .atom n → copyShallow h x = .ok (h, x)) ∧
    (h.get x = .str t → copyShallow h x = .ok (h, x)) ∧
    (h.get x = .method f s → h.get s = .inst a → a.lookup (.name (methName f)) = some v →
      copyShallow h x = .ok (h, v)) ∧
    (h.get x = .method 0 s → h.get s = .inst a → a.lookup (.name (methName 0)) = none →
      copyShallow h x = .ok ((h.alloc (.method 0 s)).1, h.cells.length)) ∧
    (h.get x = .method f s → h.get s = .inst a → a.lookup (.name (methName f)) = none → f ≠ 0 →
      (copyShallow h x).raises "AttributeError") ∧
    (h.get x = .method f s → (∀ q, h.get s ≠ .inst q) → (copyShallow h x).raises "AttributeError") ∧
    (h.get x = .hooked (some (some e)) dc r → copyShallow h x = .error e) ∧
    (h.get x = .hooked (some none) dc r → copyShallow h x = .ok ((h.alloc (.atom 1)).1, h.cells.length)) ∧
    (h.get x = .hooked none dc none → (copyShallow h x).raises "Error") ∧
    (h.get x = .hooked none dc (some rv) → copyShallow h x = reconShallow h rv x) ∧
    reconShallow h .str x = .ok (h, x) ∧ reconShallow h (.raises e) x = .error e

theorem copyShallow_proven : CopyShallow := by
  intro h x f s v l d a e dc r rv n t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · intro hc; simp [copyShallow, hc, Heap.alloc]
  · intro hc; simp [copyShallow, hc, Heap.alloc]
  · intro hc; simp [copyShallow, hc, Heap.alloc]
  · intro hc; simp [copyShallow, hc]
  · intro hc; simp [copyShallow, hc]
  · intro hc; simp [copyShallow, hc]
  · intro hc; simp [copyShallow, hc]
  · intro hc hs hl; simp [copyShallow, getMethodAttr, hc, hs, hl]
  · intro hc hs hl; simp [copyShallow, getMethodAttr, hc, hs, hl, Heap.alloc]
  · intro hc hs hl hf
    refine ⟨.named "AttributeError" "~object has no attribute", ?_, rfl⟩
    simp [copyShallow, getMethodAttr, hc, hs, hl, hf]
  · intro hc hs
    refine ⟨.named "AttributeError" "~object has no attribute", ?_, rfl⟩
    cases hg : h.get s with
    | inst q => exact absurd hg (hs q)
    | _ => simp [copyShallow, getMethodAttr, hc, hg]
  · intro hc; simp [copyShallow, hc]
  · intro hc; simp [copyShallow, hc, Heap.alloc]
  · intro hc; exact ⟨_, by simp [copyShallow, hc]; rfl, rfl⟩
  · intro hc; simp [copyShallow, hc]

theorem storeItem_miss {α : Type} (eq : α → α → Py Bool) (k : α) (v : Nat) : ∀ (acc : List (α × Nat)),
    (∀ p ∈ acc, eq p.1 k = .ok false) → storeItem eq acc k v = .ok (acc ++ [(k, v)])
  | [], _ => by simp [storeItem]
  | (k0, v0) :: rest, hp => by
    have h0 : eq k0 k = .ok false := hp (k0, v0) (by simp)
    have h1 := storeItem_miss eq k v rest (fun p q => hp p (by simp [q]))
    simp [storeItem, h0, h1]

theorem storeItem_hit {α : Type} (eq : α → α → Py Bool) (k : α) (v : Nat) (k0 : α) (v0 : Nat)
    (post : List (α × Nat)) :
    ∀ (pre : List (α × Nat)), (∀ p ∈ pre, eq p.1 k = .ok false) → eq k0 k = .ok true →
    storeItem eq (pre ++ (k0, v0) :: post) k v = .ok (pre ++ (k0, v) :: post)
  | [], _, he => by simp [storeItem, he]
  | (a, b) :: rest, hp, he => by
    have h0 : eq a k = .ok false := hp (a, b) (by simp)
    have h1 := storeItem_hit eq k v k0 v0 post rest (fun p q => hp p (by simp [q])) he
    simp [storeItem, h0, h1]

theorem akEq_name_ne (h : Heap) (q : AttrKey) (t : String) (hq : q ≠ .name t) : akEq h q (.name t) = .ok false := by
  cases q with
  | name s =>
    have : s ≠ t := fun e => hq (by rw [e])
    simp [akEq, this]
  | obj c => simp [akEq]

/-- `copy` takes whatever `__reduce__` tuple `pickle` takes. False: `pickle` takes a sixth item, the state
setter, and `_reconstruct(x, None, *rv)` has parameters for five. -/
def CopyAcceptsPickleReduce : Prop :=
  ∀ (size : Nat) (h : Heap) (x : Nat), pickleReduceOk size = true →
    ¬(reconShallow h (.tuple size none .inst [] none none none none) x).raises "TypeError"

theorem copyAcceptsPickleReduce_refuted : ¬CopyAcceptsPickleReduce := by
  intro h
  exact h 6 ⟨[], []⟩ 0 rfl ⟨_, rfl, rfl⟩

/-- `_reconstruct`. Fewer than two or more than five reduce items is a `TypeError`, and a constructor that raises
stops it. A state that is `None` does nothing at all, Lib/copy.py:252: neither `__setstate__` nor the default step
runs. Otherwise `__setstate__` wins, and its exception propagates. The default step reads `y.__dict__` before it looks
at the state, so even an empty dict state on an object without `__dict__` is an `AttributeError`; a dict state is
merged item by item; a pair sequence stores its pairs, a new name at the end and a name already there in its place
with the new value, as a dict store does, and an element of another length is the `ValueError` of `dict.update`. A two-item tuple is `(state, slotstate)`: `None` in either place is skipped, the slot state goes
through `setattr`, which wants `str` names. `listiter` needs `append`, which an object without it turns into
`AttributeError`. -/
def ReconstructSteps : Prop :=
  ∀ (h : Heap) (x y st a b p k v : Nat) (e : PyExc) (n : Nat) (bk : BuildKind) (args : List Nat) (s : Option Nat)
    (li : Option (ItemsIter Nat)) (di : Option (ItemsIter (Nat × Nat))) (ss : Option (Option PyExc))
    (d : List (Nat × Nat)) (attrs pre post : List (AttrKey × Nat)) (t : String) (w : Nat),
    (n < 2 ∨ n > 5 → (reconShallow h (.tuple n none bk args s li di ss) x).raises "TypeError") ∧
    (2 ≤ n → n ≤ 5 → reconShallow h (.tuple n (some e) bk args s li di ss) x = .error e) ∧
    (noneCell h st = true → reconRest h y (some st) none none ss = .ok h) ∧
    (noneCell h st = false → reconRest h y (some st) none none (some (some e)) = .error e) ∧
    (h.get st = .dict d → (∀ q, h.get y ≠ .inst q) → (reconRest h y (some st) none none none).raises "AttributeError") ∧
    (h.get st = .dict d → h.get y = .inst attrs → reconRest h y (some st) none none none = updateFrom y h d) ∧
    (h.get st = .list [p] → h.get p = .tuple [k, v] → h.get k = .str t → h.get y = .inst attrs →
      (∀ q ∈ attrs, q.1 ≠ .name t) →
      reconRest h y (some st) none none none = .ok (h.set y (.inst (attrs ++ [(.name t, v)])))) ∧
    (h.get st = .list [p] → h.get p = .tuple [k, v] → h.get k = .str t → h.get y = .inst (pre ++ (.name t, w) :: post) →
      (∀ q ∈ pre, q.1 ≠ .name t) →
      reconRest h y (some st) none none none = .ok (h.set y (.inst (pre ++ (.name t, v) :: post)))) ∧
    (h.get st = .list [p] → h.get p = .tuple [k] → h.get y = .inst attrs →
      reconRest h y (some st) none none none =
        .error (.valueError "dictionary update sequence element #0 has length 1; 2 is required")) ∧
    (h.get st = .tuple [a, b] → noneCell h a = true → noneCell h b = true →
      reconRest h y (some st) none none none = .ok h) ∧
    (h.get st = .tuple [a, b] → noneCell h a = true → h.get b = .dict d →
      reconRest h y (some st) none none none = slotSet y h d) ∧
    (h.get st = .tuple [a, b] → noneCell h a = true → h.get b = .dict ((k, v) :: d) → (∀ u, h.get k ≠ .str u) →
      (reconRest h y (some st) none none none).raises "TypeError") ∧
    ((∀ l, h.get y ≠ .list l) → (reconRest h y none (some ⟨[a], none⟩) none none).raises "AttributeError")

theorem noneCell_of_ne (h : Heap) (s : Nat) (hs : ∀ m, h.get s ≠ .atom m) : noneCell h s = false := by
  unfold noneCell
  split
  · next he => exact absurd he (hs 0)
  · rfl

theorem reconstructSteps_proven : ReconstructSteps := by
  intro h x y st a b p k v e n bk args s li di ss d attrs pre post t w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hn
    rcases hn with hn | hn
    · exact ⟨_, by simp [reconShallow, reconArity, hn]; rfl, rfl⟩
    · have h2 : ¬ n < 2 := by omega
      exact ⟨_, by simp [reconShallow, reconArity, h2, hn]; rfl, rfl⟩
  · intro h1 h2
    have h3 : ¬ n < 2 := by omega
    have h4 : ¬ n > 5 := by omega
    simp [reconShallow, reconArity, h3, h4]
  · intro hs
    simp [reconRest, hs]
  · intro hs
    simp [reconRest, hs, stateApply, setstateOf]
  · intro hs hy
    have hn : noneCell h st = false := noneCell_of_ne h st (by intro m hm; rw [hs] at hm; cases hm)
    refine ⟨.named "AttributeError" "~object has no attribute '__dict__'", ?_, rfl⟩
    cases hg : h.get y with
    | inst q => exact absurd hg (hy q)
    | _ => simp [reconRest, hn, stateApply, stateStep, stateSplit, hs, hg]
  · intro hs hy
    have hn : noneCell h st = false := noneCell_of_ne h st (by intro m hm; rw [hs] at hm; cases hm)
    simp only [reconRest, hn, stateApply, stateStep, stateSplit, hs, hy, dictUpdate, Bool.false_eq_true, ite_false]
    cases updateFrom y h d <;> rfl
  · intro hs hp hk hy hq
    have hn : noneCell h st = false := noneCell_of_ne h st (by intro m hm; rw [hs] at hm; cases hm)
    have hst : storeItem (akEq h) attrs (.name t) v = .ok (attrs ++ [(.name t, v)]) :=
      storeItem_miss _ _ _ attrs (fun q hq' => akEq_name_ne h q.1 t (hq q hq'))
    simp [reconRest, hn, stateApply, stateStep, stateSplit, hs, hy, dictUpdate, updateSeq, pairOf, hp, storeKey,
      keyHashErr, hk, attrKey, setAttrOf, hst]
  · intro hs hp hk hy hq
    have hn : noneCell h st = false := noneCell_of_ne h st (by intro m hm; rw [hs] at hm; cases hm)
    have hst : storeItem (akEq h) (pre ++ (.name t, w) :: post) (.name t) v = .ok (pre ++ (.name t, v) :: post) :=
      storeItem_hit _ _ _ _ _ post pre (fun q hq' => akEq_name_ne h q.1 t (hq q hq')) (by simp [akEq])
    simp [reconRest, hn, stateApply, stateStep, stateSplit, hs, hy, dictUpdate, updateSeq, pairOf, hp, storeKey,
      keyHashErr, hk, attrKey, setAttrOf, hst]
  · intro hs hp hy
    have hn : noneCell h st = false := noneCell_of_ne h st (by intro m hm; rw [hs] at hm; cases hm)
    simp [reconRest, hn, stateApply, stateStep, stateSplit, hs, hy, dictUpdate, updateSeq, pairOf, hp] <;>
      first | rfl | decide
  · intro hs ha hb
    have hn : noneCell h st = false := noneCell_of_ne h st (by intro m hm; rw [hs] at hm; cases hm)
    simp [reconRest, hn, stateApply, stateStep, stateSplit, hs, ha, hb]
  · intro hs ha hb
    have hn : noneCell h st = false := noneCell_of_ne h st (by intro m hm; rw [hs] at hm; cases hm)
    have hbn : noneCell h b = false := noneCell_of_ne h b (by intro m hm; rw [hb] at hm; cases hm)
    simp only [reconRest, hn, stateApply, stateStep, stateSplit, hs, ha, hbn, hb, Bool.false_eq_true, ite_false, ite_true]
    try (cases slotSet y h d <;> rfl)
  · intro hs ha hb hk
    have hn : noneCell h st = false := noneCell_of_ne h st (by intro m hm; rw [hs] at hm; cases hm)
    have hbn : noneCell h b = false := noneCell_of_ne h b (by intro m hm; rw [hb] at hm; cases hm)
    have hk' : slotSet y h ((k, v) :: d) = .error (.typeError "~attribute name must be string") := by
      cases hg : h.get k <;> simp [slotSet, hg] <;> exact absurd hg (hk _)
    refine ⟨.typeError "~attribute name must be string", ?_, rfl⟩
    simp [reconRest, hn, stateApply, stateStep, stateSplit, hs, ha, hbn, hb, hk']
  · intro hl
    have : appendTo h y a = .error (.named "AttributeError" "~object has no attribute 'append'") := by
      cases hg : h.get y with
      | list l => exact absurd hg (hl l)
      | _ => simp [appendTo, hg]
    refine ⟨.named "AttributeError" "~object has no attribute 'append'", ?_, rfl⟩
    simp [reconRest, appendAll, this]

/-- `deepcopy` of a bound method shares the function and copies `__self__`: `_deepcopy_method`. A failing
`__deepcopy__` propagates; with no way to reduce, `copy.Error`. -/
def DeepcopyMethod : Prop :=
  ∀ (fuel : Nat) (h h1 : Heap) (x f s s' : Nat) (e : PyExc) (c : Option (Option PyExc)) (r : Option RvSpec),
    (h.get x = .method f s → h.memo.lookup x = none → deepcopy (fuel + 1) h s = .ok (h1, s') →
      deepcopy (fuel + 2) h x = .ok (((h1.alloc (.method f s')).1).remember x h1.cells.length, h1.cells.length)) ∧
    (h.get x = .hooked c (some (some e)) r → h.memo.lookup x = none → deepcopy (fuel + 1) h x = .error e) ∧
    (h.get x = .hooked c none none → h.memo.lookup x = none → (deepcopy (fuel + 1) h x).raises "Error")

theorem deepcopyMethod_proven : DeepcopyMethod := by
  intro fuel h h1 x f s s' e c r
  refine ⟨?_, ?_, ?_⟩
  · intro h2 h3 h4
    rw [deepcopy]
    simp [h2, h3, h4, Heap.alloc]
  · intro h2 h3
    rw [deepcopy]
    simp [h2, h3]
  · intro h2 h3
    refine ⟨uncopyable true, ?_, rfl⟩
    rw [deepcopy]
    simp [h2, h3]

/-- `replace(obj, **changes)`: the class is `obj.__class__`; a `__replace__` that is missing or set to `None` is the
`TypeError` naming the class, Lib/copy.py:296-299; otherwise the result is the call `__replace__(obj, **changes)`, with
that object and those changes, whatever it returns or raises, :300. -/
def ReplaceCall : Prop :=
  ∀ {β α : Type} (clsOf : β → ReplaceCls β α) (obj : β) (changes : List (String × α))
    (f : β → List (String × α) → Py β),
    ((clsOf obj).replace = some (some f) → replaceOp clsOf obj changes = f obj changes) ∧
    ((clsOf obj).replace = none ∨ (clsOf obj).replace = some none →
      replaceOp clsOf obj changes = .error (.typeError s!"replace() does not support {(clsOf obj).name} objects"))

theorem replaceCall_proven : ReplaceCall := by
  intro β α clsOf obj changes f
  refine ⟨?_, ?_⟩
  · intro hr
    simp [replaceOp, hr]
  · intro hr
    rcases hr with hr | hr <;> simp [replaceOp, hr]

end PyLean.CoreLibs.Operator
