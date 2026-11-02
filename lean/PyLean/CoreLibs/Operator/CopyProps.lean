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
  simp only [setItemOf] at e
  split at e
  · cases e
    exact keeps_set n h y _ hn hy
  · cases e

theorem setAttrOf_keeps (n : Nat) (h h' : Heap) (y : Nat) (k : String) (v : Nat) (hn : n ≤ h.cells.length)
    (hy : n ≤ y) (e : setAttrOf h y k v = .ok h') : Keeps n h h' := by
  simp only [setAttrOf] at e
  split at e
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

theorem stateStep_keeps (n y st : Nat) (h h' : Heap) (hn : n ≤ h.cells.length) (hy : n ≤ y)
    (e : stateStep h y st = .ok h') : Keeps n h h' := by
  simp only [stateStep] at e
  have hu : ∀ (h h' : Heap) (s : Nat), n ≤ h.cells.length →
      (match h.get s with
       | .dict items => updateFrom y h items
       | _ => (.error (.typeError "~object is not iterable") : Py Heap)) = .ok h' → Keeps n h h' := by
    intro h h' s h1 h2
    split at h2
    · exact updateFrom_keeps n y hy _ h h' h1 h2
    · cases h2
  split at e
  · next a b hs =>
    split at e
    · cases e
    · next h2 h3 =>
      have k1 : Keeps n h h2 := by
        split at h3
        · cases h3
          exact Keeps.refl n _ hn
        · exact hu h h2 a hn h3
      split at e
      · cases e
        exact k1
      · split at e
        · exact k1.trans (updateFrom_keeps n y hy _ h2 h' k1.1 e)
        · cases e
  · split at e
    · cases e
      exact Keeps.refl n _ hn
    · exact hu h h' st hn e

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

theorem reconRest_keeps (n y : Nat) (hy : n ≤ y) (h h' : Heap) (hn : n ≤ h.cells.length) (st : Option Nat)
    (li : Option (List Nat)) (di : Option (List (Nat × Nat))) (ss : Option (Option PyExc))
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
        · next f =>
          simp only [setstateOf] at h2e
          split at h2e
          · cases h2e
          · exact setAttrOf_keeps n h h2 y _ _ hn hy h2e
        · exact stateStep_keeps n y _ h h2 hn hy h2e
    split at e
    · cases e
    · next h4 h4e =>
      have k2 : Keeps n h2 h4 := by
        split at h4e
        · cases h4e
          exact Keeps.refl n _ k1.1
        · obtain ⟨h0, e0, k⟩ := foldl_keeps' n (fun h i => appendTo h y i)
            (fun a b c h3 h4 => appendTo_keeps n a b y c h3 hy h4) _ _ _ h4e
          cases e0
          exact k k1.1
      split at e
      · cases e
        exact k1.trans k2
      · obtain ⟨h0, e0, k⟩ := foldl_keeps' n (fun h (p : Nat × Nat) => setItemOf h y p.1 p.2)
          (fun a b c h3 h4 => setItemOf_keeps n a b y _ _ h3 hy h4) _ _ _ e
        cases e0
        exact (k1.trans k2).trans (k k2.1)

theorem keeps_all (n : Nat) : ∀ fuel : Nat,
    (∀ h x h' y, n ≤ h.cells.length → deepcopy fuel h x = .ok (h', y) → Keeps n h h') ∧
    (∀ h l h' ys, n ≤ h.cells.length → deepList fuel h l = .ok (h', ys) → Keeps n h h') ∧
    (∀ h l h' ys, n ≤ h.cells.length → deepPairs fuel h l = .ok (h', ys) → Keeps n h h') ∧
    (∀ h y l h', n ≤ h.cells.length → n ≤ y → deepAttrs fuel h y l = .ok h' → Keeps n h h') ∧
    (∀ h l h' ys, n ≤ h.cells.length → deepOpt fuel h l = .ok (h', ys) → Keeps n h h') ∧
    (∀ h y l h', n ≤ h.cells.length → n ≤ y → deepAppend fuel h y l = .ok h' → Keeps n h h') ∧
    (∀ h y l h', n ≤ h.cells.length → n ≤ y → deepSetItems fuel h y l = .ok h' → Keeps n h h')
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h x h' y _ e; simp [deepcopy] at e
    · intro h l h' ys _ e; simp [deepList] at e
    · intro h l h' ys _ e; simp [deepPairs] at e
    · intro h y l h' _ _ e; simp [deepAttrs] at e
    · intro h l h' ys hn e
      cases l with
      | none =>
        simp only [deepOpt, Except.ok.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, -⟩ := e
        exact Keeps.refl n _ hn
      | some _ => simp [deepOpt] at e
    · intro h y l h' _ _ e; simp [deepAppend] at e
    · intro h y l h' _ _ e; simp [deepSetItems] at e
  | fuel + 1 => by
    obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7⟩ := keeps_all n fuel
    have hfresh : ∀ (h : Heap) (c : Cell), n ≤ h.cells.length →
        Keeps n h ((h.alloc c).1) ∧ n ≤ (h.alloc c).2 ∧ n ≤ (h.alloc c).1.cells.length := by
      intro h c hn
      have k := keeps_alloc n h c hn
      exact ⟨k, hn, k.1⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h x h' y hn e
      simp only [deepcopy] at e
      split at e
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
              have k2 := ih3 _ _ _ _ hk.1.1 e3
              cases e
              exact (hk.1.trans k2).trans (keeps_set n _ _ _ k2.1 hk.2)
          · -- frozendict
            split at e
            · cases e
            · next h1 ys e1 =>
              have k1 := ih3 _ _ _ _ hn e1
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
                      · next h4 st' e4 =>
                        have k3 := ih5 _ _ _ _ hk.1.1 e4
                        split at e
                        · cases e
                        · next h5 e5 =>
                          have k4 := reconRest_keeps n _ hk.2 _ _ k3.1 _ _ _ _ e5
                          split at e
                          · cases e
                          · next h6 e6 =>
                            have k5 := ih6 _ _ _ _ k4.1 hk.2 e6
                            split at e
                            · cases e
                            · next h7 e7 =>
                              have k6 := ih7 _ _ _ _ k5.1 hk.2 e7
                              cases e
                              exact ((((k1.trans hk.1).trans k3).trans k4).trans k5).trans k6
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
    · intro h l h' ys hn e
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
        · next h1 k' e1 =>
          have k1 := ih1 _ _ _ _ hn e1
          split at e
          · cases e
          · next h2 v' e2 =>
            have k2 := ih1 _ _ _ _ k1.1 e2
            split at e
            · cases e
            · split at e
              · cases e
              · next h3 ys3 e3 =>
                have k3 := ih3 _ _ _ _ k2.1 e3
                cases e
                exact (k1.trans k2).trans k3
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
          · next h2 e2 =>
            have k2 := setAttrOf_keeps n _ _ _ _ _ k1.1 hy e2
            exact (k1.trans k2).trans (ih4 _ _ _ _ k2.1 hy e)
    · intro h l h' ys hn e
      cases l with
      | none =>
        simp only [deepOpt, Except.ok.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, -⟩ := e
        exact Keeps.refl n _ hn
      | some s =>
        simp only [deepOpt] at e
        split at e
        · cases e
        · next h1 s' e1 =>
          cases e
          exact ih1 _ _ _ _ hn e1
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
    (h.memo.lookup x = some y → (∀ m, h.get x ≠ .atom m) → (∀ m, h.get x ≠ .cls m) →
      deepcopy (fuel + 1) h x = .ok (h, y)) ∧
    (h.get x = .list [x] → h.memo.lookup x = none → ∃ h', deepcopy (fuel + 4) h x = .ok (h', h.cells.length) ∧
      h'.get h.cells.length = .list [h.cells.length])

theorem deepcopyMemo_proven : DeepcopyMemo := by
  intro fuel h x y n
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    simp [deepcopy, hc]
  · intro hl hn hc
    rw [deepcopy]
    split
    · next m hm => exact absurd hm (hn m)
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

/-- `copy` by kind: a list, a dict, an instance and a method become a new object with the same contents, so the
items are shared; a tuple, an atom and a class are themselves. `__copy__` goes before the reduce protocol, and
its exception propagates; with neither `__copy__` nor a reductor, `copy.Error`. A reduce string means `x`. -/
def CopyShallow : Prop :=
  ∀ (h : Heap) (x : Nat) (l : List Nat) (e : PyExc) (d : Option (Option PyExc)) (r : Option RvSpec),
    (h.get x = .list l → copyShallow h x = .ok ((h.alloc (.list l)).1, h.cells.length)) ∧
    (h.get x = .tuple l → copyShallow h x = .ok (h, x)) ∧
    (h.get x = .hooked (some (some e)) d r → copyShallow h x = .error e) ∧
    (h.get x = .hooked none d none → (copyShallow h x).raises "Error") ∧
    (h.get x = .hooked none d (some .str) → copyShallow h x = .ok (h, x)) ∧
    (h.get x = .hooked none d (some (.raises e)) → copyShallow h x = .error e)

theorem copyShallow_proven : CopyShallow := by
  intro h x l e d r
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc; simp [copyShallow, hc, Heap.alloc]
  · intro hc; simp [copyShallow, hc]
  · intro hc; simp [copyShallow, hc]
  · intro hc; exact ⟨_, by simp [copyShallow, hc]; rfl, rfl⟩
  · intro hc; simp [copyShallow, hc, reconShallow]
  · intro hc; simp [copyShallow, hc, reconShallow]

/-- `copy` takes whatever `__reduce__` tuple `pickle` takes. False: `pickle` takes a sixth item, the state
setter, and `_reconstruct(x, None, *rv)` has parameters for five. -/
def CopyAcceptsPickleReduce : Prop :=
  ∀ (size : Nat) (h : Heap) (x : Nat), pickleReduceOk size = true →
    ¬(reconShallow h (.tuple size none .inst [] none none none none) x).raises "TypeError"

theorem copyAcceptsPickleReduce_refuted : ¬CopyAcceptsPickleReduce := by
  intro h
  exact h 6 ⟨[], []⟩ 0 rfl ⟨_, rfl, rfl⟩

/-- `_reconstruct`: fewer than two or more than five reduce items is a `TypeError`, and a constructor that raises
stops it. Otherwise `y` is a new object. `__setstate__` wins over the default state step, and its exception
propagates. Without it, a two-item state is `(dict state, slot state)`, a `None` in either place is skipped, the
first goes through `__dict__`, the second through `setattr`. `listiter` needs `append`, which an object without it
turns into `AttributeError`. -/
def ReconstructSteps : Prop :=
  ∀ (h : Heap) (x y st a b : Nat) (e : PyExc) (n : Nat) (k : BuildKind) (args : List Nat) (s : Option Nat)
    (li : Option (List Nat)) (di : Option (List (Nat × Nat))) (ss : Option (Option PyExc))
    (d : List (Nat × Nat)),
    (n < 2 ∨ n > 5 → (reconShallow h (.tuple n none k args s li di ss) x).raises "TypeError") ∧
    (2 ≤ n → n ≤ 5 → reconShallow h (.tuple n (some e) k args s li di ss) x = .error e) ∧
    (reconRest h y (some st) none none (some (some e)) = .error e) ∧
    (noneCell h st = true → (∀ p q, h.get st ≠ .tuple [p, q]) → reconRest h y (some st) none none none = .ok h) ∧
    (h.get st = .tuple [a, b] → noneCell h a = true → noneCell h b = true →
      reconRest h y (some st) none none none = .ok h) ∧
    (h.get st = .tuple [a, b] → noneCell h a = true → noneCell h b = false → h.get b = .dict d →
      reconRest h y (some st) none none none = updateFrom y h d) ∧
    ((∀ l, h.get y ≠ .list l) → (reconRest h y none (some [a]) none none).raises "AttributeError")

theorem reconstructSteps_proven : ReconstructSteps := by
  intro h x y st a b e n k args s li di ss d
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hn
    rcases hn with hn | hn
    · exact ⟨_, by simp [reconShallow, reconArity, hn]; rfl, rfl⟩
    · have h2 : ¬ n < 2 := by omega
      exact ⟨_, by simp [reconShallow, reconArity, h2, hn]; rfl, rfl⟩
  · intro h1 h2
    have h3 : ¬ n < 2 := by omega
    have h4 : ¬ n > 5 := by omega
    simp [reconShallow, reconArity, h3, h4]
  · simp [reconRest, setstateOf]
  · intro h1 h2
    have : stateStep h y st = .ok h := by
      simp only [stateStep]
      split
      · simp_all
      · simp [h1]
    simp [reconRest, this]
  · intro h1 h2 h3
    simp [reconRest, stateStep, h1, h2, h3]
  · intro h1 h2 h3 h4
    have : stateStep h y st = updateFrom y h d := by
      simp only [stateStep, h1, h2, ite_true, h3, Bool.false_eq_true, ite_false, h4]
    simp only [reconRest, this]
    first
      | done
      | (cases updateFrom y h d <;> rfl)
  · intro hl
    have : appendTo h y a = .error (.named "AttributeError" "~object has no attribute 'append'") := by
      cases hg : h.get y with
      | list l => exact absurd hg (hl l)
      | _ => simp [appendTo, hg]
    exact ⟨_, by simp [reconRest, this]; rfl, rfl⟩

/-- `deepcopy` of a bound method shares the function and copies `__self__`: `_deepcopy_method`. A failing
`__deepcopy__` propagates; with no way to reduce, `copy.Error`. `replace` runs the class's `__replace__`, whose
outcome comes through, or raises `TypeError`. -/
def DeepcopyMethod : Prop :=
  ∀ (fuel : Nat) (h h1 : Heap) (x f s s' : Nat) (e : PyExc) (c : Option (Option PyExc)) (r : Option RvSpec)
    (b : Py Nat) (cls : String),
    (h.get x = .method f s → h.memo.lookup x = none → deepcopy (fuel + 1) h s = .ok (h1, s') →
      deepcopy (fuel + 2) h x = .ok (((h1.alloc (.method f s')).1).remember x h1.cells.length, h1.cells.length)) ∧
    (h.get x = .hooked c (some (some e)) r → h.memo.lookup x = none → deepcopy (fuel + 1) h x = .error e) ∧
    (h.get x = .hooked c none none → h.memo.lookup x = none → (deepcopy (fuel + 1) h x).raises "Error") ∧
    replaceOp (some b) cls = b ∧ (replaceOp (none : Option (Py Nat)) cls).raises "TypeError"

theorem deepcopyMethod_proven : DeepcopyMethod := by
  intro fuel h h1 x f s s' e c r b cls
  refine ⟨?_, ?_, ?_, rfl, ⟨_, rfl, rfl⟩⟩
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

end PyLean.CoreLibs.Operator
