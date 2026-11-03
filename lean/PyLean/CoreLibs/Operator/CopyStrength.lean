import PyLean.CoreLibs.Operator.CopyProps

/-!
What `deepcopy` and `_reconstruct` build, on graphs, with the order of the copies and the failure paths. `Keeps` in
`CopyProps` says the source is untouched, which the identity function and an always-raising function also do; these
statements say what the copy is.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

/-- A new cell, recorded in `memo` as the copy of `x`: the first lines of `_deepcopy_list` and `_deepcopy_dict`. -/
def Heap.fresh (h : Heap) (c : Cell) (x : Nat) : Heap := (h.alloc c).1.remember x h.cells.length

theorem fresh_len (h : Heap) (c : Cell) (x : Nat) : (h.fresh c x).cells.length = h.cells.length + 1 := by
  simp [Heap.fresh, Heap.remember, Heap.alloc]

theorem fresh_get_new (h : Heap) (c : Cell) (x : Nat) : (h.fresh c x).get h.cells.length = c := by
  simp [Heap.fresh, Heap.remember, Heap.get, Heap.alloc, List.getD]

theorem fresh_get_old (h : Heap) (c : Cell) (x i : Nat) (hi : i < h.cells.length) :
    (h.fresh c x).get i = h.get i := get_alloc h c i hi

theorem fresh_lookup_self (h : Heap) (c : Cell) (x : Nat) :
    (h.fresh c x).memo.lookup x = some h.cells.length := by
  simp [Heap.fresh, Heap.remember, Heap.alloc, List.lookup]

theorem fresh_lookup_other (h : Heap) (c : Cell) (x a : Nat) (hne : a ≠ x) :
    (h.fresh c x).memo.lookup a = h.memo.lookup a := by
  have : (a == x) = false := by simpa using hne
  simp [Heap.fresh, Heap.remember, Heap.alloc, List.lookup, this]

theorem get_set_same (h : Heap) (y : Nat) (c : Cell) (hy : y < h.cells.length) : (h.set y c).get y = c := by
  simp [Heap.get, Heap.set, List.getD, hy]

theorem get_set_other (h : Heap) (y z : Nat) (c : Cell) (hz : z ≠ y) : (h.set y c).get z = h.get z := by
  simp [Heap.get, Heap.set, List.getD, List.getElem?_set_ne hz.symm]

theorem set_memo (h : Heap) (y : Nat) (c : Cell) : (h.set y c).memo = h.memo := rfl

theorem set_len (h : Heap) (y : Nat) (c : Cell) : (h.set y c).cells.length = h.cells.length := by
  simp [Heap.set]

theorem deepcopy_list (fuel : Nat) (h : Heap) (x : Nat) (items : List Nat) (hc : h.get x = .list items)
    (hm : h.memo.lookup x = none) (h3 : Heap) (ys : List Nat)
    (hd : deepList fuel (h.fresh (.list []) x) items = .ok (h3, ys)) :
    deepcopy (fuel + 1) h x = .ok (h3.set h.cells.length (.list ys), h.cells.length) := by
  rw [deepcopy]
  simp only [hc, hm]
  simp only [Heap.fresh] at hd
  simp [Heap.alloc] at hd ⊢
  simp [hd]

theorem deepcopy_dict (fuel : Nat) (h : Heap) (x : Nat) (items : List (Nat × Nat)) (hc : h.get x = .dict items)
    (hm : h.memo.lookup x = none) (h3 : Heap) (ys : List (Nat × Nat))
    (hd : deepPairs fuel (h.fresh (.dict []) x) [] items = .ok (h3, ys)) :
    deepcopy (fuel + 1) h x = .ok (h3.set h.cells.length (.dict ys), h.cells.length) := by
  rw [deepcopy]
  simp only [hc, hm]
  simp only [Heap.fresh] at hd
  simp [Heap.alloc] at hd ⊢
  simp [hd]

theorem deepcopy_tuple_new (fuel : Nat) (h h1 : Heap) (x : Nat) (items ys : List Nat)
    (hc : h.get x = .tuple items) (hm : h.memo.lookup x = none)
    (hd : deepList fuel h items = .ok (h1, ys)) (hm1 : h1.memo.lookup x = none) (hne : (ys == items) = false) :
    deepcopy (fuel + 1) h x = .ok (h1.fresh (.tuple ys) x, h1.cells.length) := by
  rw [deepcopy]
  simp only [hc, hm, hd, hm1, hne]
  rfl

theorem deepcopy_tuple_memo (fuel : Nat) (h h1 : Heap) (x y : Nat) (items ys : List Nat)
    (hc : h.get x = .tuple items) (hm : h.memo.lookup x = none)
    (hd : deepList fuel h items = .ok (h1, ys)) (hm1 : h1.memo.lookup x = some y) :
    deepcopy (fuel + 1) h x = .ok (h1, y) := by
  rw [deepcopy]
  simp only [hc, hm, hd, hm1]

/-- `_deepcopy_frozendict`, with `deepcopy` around it. The keys and values are copied in order into a new `dict`
(`deepPairs` from no items, so equal key copies merge as in `_deepcopy_dict`) with nothing in `memo` for `x`; a copy that
a recursive structure put there wins, and otherwise the result is a new `frozendict` of those items, even if every copy is
the object itself, which is where it differs from `_deepcopy_tuple`; the first failure stops it. Unlike a `dict`, the
object is not in `memo` while its items are copied. -/
def DeepcopyFrozendict : Prop :=
  ∀ (fuel : Nat) (h h1 : Heap) (x y : Nat) (items ys : List (Nat × Nat)) (e : PyExc),
    h.get x = .fdict items → h.memo.lookup x = none →
    (deepPairs fuel h [] items = .ok (h1, ys) → h1.memo.lookup x = none →
      deepcopy (fuel + 1) h x = .ok (h1.fresh (.fdict ys) x, h1.cells.length)) ∧
    (deepPairs fuel h [] items = .ok (h1, ys) → h1.memo.lookup x = some y → deepcopy (fuel + 1) h x = .ok (h1, y)) ∧
    (deepPairs fuel h [] items = .error e → deepcopy (fuel + 1) h x = .error e)

theorem deepcopyFrozendict_proven : DeepcopyFrozendict := by
  intro fuel h h1 x y items ys e hc hm
  refine ⟨?_, ?_, ?_⟩
  · intro hd hm1
    rw [deepcopy]
    simp only [hc, hm, hd, hm1]
    rfl
  · intro hd hm1
    rw [deepcopy]
    simp only [hc, hm, hd, hm1]
  · intro hd
    rw [deepcopy]
    simp only [hc, hm, hd]

theorem deepcopy_atom (fuel : Nat) (h : Heap) (x : Nat) (n : Int) (hc : h.get x = .atom n) :
    deepcopy (fuel + 1) h x = .ok (h, x) := by
  simp [deepcopy, hc]

theorem deepcopy_memo (fuel : Nat) (h : Heap) (x y : Nat) (hl : h.memo.lookup x = some y)
    (ha : ∀ m, h.get x ≠ .atom m) (hs : ∀ t, h.get x ≠ .str t) (hc : ∀ m, h.get x ≠ .cls m) :
    deepcopy (fuel + 1) h x = .ok (h, y) :=
  (deepcopyMemo_proven fuel h x y 0).2.1 hl ha hs hc

theorem deepList_nil (fuel : Nat) (h : Heap) : deepList (fuel + 1) h [] = .ok (h, []) := by simp [deepList]

theorem deepList_cons (fuel : Nat) (h h1 h2 : Heap) (a y : Nat) (as ys : List Nat)
    (e1 : deepcopy fuel h a = .ok (h1, y)) (e2 : deepList fuel h1 as = .ok (h2, ys)) :
    deepList (fuel + 1) h (a :: as) = .ok (h2, y :: ys) := by
  simp [deepList, e1, e2]

theorem pyEq_atoms (f : Nat) (h : Heap) (a b : Nat) (m n : Int) (ha : h.get a = .atom m) (hb : h.get b = .atom n) :
    pyEq (f + 1) h a b = .ok (if a = b then true else m == n) := by
  by_cases e : a = b
  · simp [pyEq, e]
  · simp [pyEq, e, ha, hb]

theorem storeKey_atom (h : Heap) (k : Nat) (n : Int) (hn : h.get k = .atom n) : storeKey h k = none := by
  simp [storeKey, keyHashErr, hn]

/-- A store of an atom key that no stored key equals goes at the end. -/
theorem dictSet_atom_fresh (h : Heap) (acc : List (Nat × Nat)) (k v : Nat) (n : Int) (hn : h.get k = .atom n)
    (ha : ∀ p ∈ acc, (∃ m, h.get p.1 = .atom m) ∧ h.get p.1 ≠ .atom n) :
    dictSet h acc k v = .ok (acc ++ [(k, v)]) := by
  simp only [dictSet, storeKey_atom h k n hn]
  apply storeItem_miss
  intro p hp
  obtain ⟨⟨m, hm⟩, hne⟩ := ha p hp
  have hpk : p.1 ≠ k := by
    intro e
    rw [e, hn] at hne
    exact hne rfl
  have hmn : m ≠ n := by
    intro e
    rw [e] at hm
    exact hne hm
  rw [show eqFuel h = (2 * h.cells.length + 1) + 1 from rfl, pyEq_atoms _ h _ _ m n hm hn]
  simp [hpk, hmn]

theorem deepPairs_atoms (h : Heap) : ∀ (fuel : Nat) (acc l : List (Nat × Nat)),
    (∀ p ∈ acc ++ l, ∃ n, h.get p.1 = .atom n) → (∀ p ∈ l, ∃ n, h.get p.2 = .atom n) →
    List.Pairwise (fun p q => h.get p.1 ≠ h.get q.1) (acc ++ l) → l.length ≤ fuel →
    deepPairs (fuel + 1) h acc l = .ok (h, acc ++ l)
  | _, acc, [], _, _, _, _ => by simp [deepPairs]
  | 0, _, _ :: _, _, _, _, hl => by simp at hl
  | fuel + 1, acc, (k, v) :: r, hk, hv, hp, hl => by
    obtain ⟨n, hn⟩ := hk (k, v) (by simp)
    obtain ⟨m, hm⟩ := hv (k, v) (by simp)
    have h1 : deepcopy (fuel + 1) h v = .ok (h, v) := deepcopy_atom _ _ _ _ hm
    have h2 : deepcopy (fuel + 1) h k = .ok (h, k) := deepcopy_atom _ _ _ _ hn
    have hs : dictSet h acc k v = .ok (acc ++ [(k, v)]) := by
      apply dictSet_atom_fresh h acc k v n hn
      intro p hp'
      refine ⟨hk p (by simp [hp']), ?_⟩
      rw [← hn]
      exact (List.pairwise_append.1 hp).2.2 p hp' (k, v) (by simp)
    have e : acc ++ [(k, v)] ++ r = acc ++ (k, v) :: r := by simp
    have h3 := deepPairs_atoms h fuel (acc ++ [(k, v)]) r (by rw [e]; exact hk)
      (fun p q => hv p (by simp [q])) (by rw [e]; exact hp) (by simpa using hl)
    rw [e] at h3
    simp only [deepPairs, h1, h2, hs]
    exact h3

/-- `_deepcopy_list` on a list of atoms: a new list, recorded in `memo`, with the same items. Every reference is a
cell of the heap, which is the invariant of a real object graph. -/
def DeepcopyListExact : Prop :=
  ∀ (fuel : Nat) (h : Heap) (x : Nat) (items : List Nat), h.get x = .list items → h.memo.lookup x = none →
    (∀ i ∈ items, (∃ n, h.get i = .atom n) ∧ i < h.cells.length) → items.length ≤ fuel →
    ∃ h', deepcopy (fuel + 2) h x = .ok (h', h.cells.length) ∧ h'.get h.cells.length = .list items ∧
      h'.memo.lookup x = some h.cells.length ∧ h.cells.length ≠ x

theorem deepcopyListExact_proven : DeepcopyListExact := by
  intro fuel h x items hc hm ha hl
  have hx := get_of_list h x _ hc
  have ha2 : ∀ i ∈ items, ∃ n, (h.fresh (.list []) x).get i = .atom n := by
    intro i hi
    obtain ⟨⟨n, hn⟩, hlt⟩ := ha i hi
    exact ⟨n, by rw [fresh_get_old _ _ _ _ hlt]; exact hn⟩
  have hd := deepList_atoms _ fuel items ha2 hl
  refine ⟨_, deepcopy_list (fuel + 1) h x items hc hm _ _ hd, ?_, ?_, by omega⟩
  · apply get_set_same
    rw [fresh_len]; omega
  · rw [set_memo, fresh_lookup_self]

/-- `_deepcopy_dict` on a dict of atoms: a new dict, recorded in `memo`, with the same items. The keys are pairwise
unequal, the invariant of a `dict` (on atoms, distinct values); a heap list with two equal keys is no Python dict. -/
def DeepcopyDictExact : Prop :=
  ∀ (fuel : Nat) (h : Heap) (x : Nat) (items : List (Nat × Nat)), h.get x = .dict items → h.memo.lookup x = none →
    (∀ p ∈ items, ((∃ n, h.get p.1 = .atom n) ∧ p.1 < h.cells.length) ∧
      ((∃ n, h.get p.2 = .atom n) ∧ p.2 < h.cells.length)) →
    List.Pairwise (fun p q => h.get p.1 ≠ h.get q.1) items → items.length ≤ fuel →
    ∃ h', deepcopy (fuel + 2) h x = .ok (h', h.cells.length) ∧ h'.get h.cells.length = .dict items ∧
      h'.memo.lookup x = some h.cells.length

theorem deepcopyDictExact_proven : DeepcopyDictExact := by
  intro fuel h x items hc hm ha hp hl
  have hk : ∀ p ∈ items, (h.fresh (.dict []) x).get p.1 = h.get p.1 := fun p hi =>
    fresh_get_old _ _ _ _ (ha p hi).1.2
  have hk2 : ∀ p ∈ ([] : List (Nat × Nat)) ++ items, ∃ n, (h.fresh (.dict []) x).get p.1 = .atom n := by
    intro p hi
    simp only [List.nil_append] at hi
    rw [hk p hi]
    exact (ha p hi).1.1
  have hv2 : ∀ p ∈ items, ∃ n, (h.fresh (.dict []) x).get p.2 = .atom n := by
    intro p hi
    obtain ⟨-, ⟨⟨m, hm⟩, h3⟩⟩ := ha p hi
    exact ⟨m, by rw [fresh_get_old _ _ _ _ h3]; exact hm⟩
  have hp2 : List.Pairwise (fun p q => (h.fresh (.dict []) x).get p.1 ≠ (h.fresh (.dict []) x).get q.1)
      ([] ++ items) := by
    simp only [List.nil_append]
    exact hp.imp_of_mem (fun ha' hb' r => by rw [hk _ ha', hk _ hb']; exact r)
  have hd := deepPairs_atoms _ fuel [] items hk2 hv2 hp2 hl
  simp only [List.nil_append] at hd
  refine ⟨_, deepcopy_dict (fuel + 1) h x items hc hm _ _ hd, ?_, ?_⟩
  · apply get_set_same
    rw [fresh_len]; omega
  · rw [set_memo, fresh_lookup_self]

/-- `_deepcopy_dict` stores with `y[k] = v`, Lib/copy.py:201, so it does not keep the length: two source keys whose
copies are equal make one item. Here `memo` sends the first key to an atom equal to the second key (:125-126 answer the
first from `memo`, :118-119 return the second as itself): the copy has one item, the first key's copy in the first
place, holding the second value. A dict is unhashable, so `x` is not its own key. -/
def DeepcopyDictMerge : Prop :=
  ∀ (fuel : Nat) (h : Heap) (x k1 v1 k2 v2 a : Nat) (n m1 m2 : Int),
    h.get x = .dict [(k1, v1), (k2, v2)] → h.memo.lookup x = none → k1 ≠ x →
    (∀ m, h.get k1 ≠ .atom m) → (∀ t, h.get k1 ≠ .str t) → (∀ m, h.get k1 ≠ .cls m) → k1 < h.cells.length →
    h.memo.lookup k1 = some a →
    h.get a = .atom n → a < h.cells.length → h.get k2 = .atom n → k2 < h.cells.length →
    h.get v1 = .atom m1 → v1 < h.cells.length → h.get v2 = .atom m2 → v2 < h.cells.length →
    ∃ h', deepcopy (fuel + 4) h x = .ok (h', h.cells.length) ∧ h'.get h.cells.length = .dict [(a, v2)]

theorem deepcopyDictMerge_proven : DeepcopyDictMerge := by
  intro fuel h x k1 v1 k2 v2 a n m1 m2 hc hm hkx hk1a hk1s hk1c hk1l hmk1 ha hal hk2 hk2l hv1 hv1l hv2 hv2l
  have g : ∀ i, i < h.cells.length → (h.fresh (.dict []) x).get i = h.get i := fun i hi =>
    fresh_get_old _ _ _ _ hi
  have e1 : deepcopy (fuel + 2) (h.fresh (.dict []) x) v1 = .ok (h.fresh (.dict []) x, v1) :=
    deepcopy_atom _ _ _ m1 (by rw [g _ hv1l]; exact hv1)
  have e2 : deepcopy (fuel + 2) (h.fresh (.dict []) x) k1 = .ok (h.fresh (.dict []) x, a) := by
    apply deepcopy_memo
    · rw [fresh_lookup_other _ _ _ _ hkx]; exact hmk1
    · intro m; rw [g _ hk1l]; exact hk1a m
    · intro m; rw [g _ hk1l]; exact hk1s m
    · intro m; rw [g _ hk1l]; exact hk1c m
  have ha0 : (h.fresh (.dict []) x).get a = .atom n := by rw [g _ hal]; exact ha
  have hk20 : (h.fresh (.dict []) x).get k2 = .atom n := by rw [g _ hk2l]; exact hk2
  have s1 : dictSet (h.fresh (.dict []) x) [] a v1 = .ok [(a, v1)] :=
    dictSet_atom_fresh _ [] a v1 n ha0 (by simp)
  have e3 : deepcopy (fuel + 1) (h.fresh (.dict []) x) v2 = .ok (h.fresh (.dict []) x, v2) :=
    deepcopy_atom _ _ _ m2 (by rw [g _ hv2l]; exact hv2)
  have e4 : deepcopy (fuel + 1) (h.fresh (.dict []) x) k2 = .ok (h.fresh (.dict []) x, k2) :=
    deepcopy_atom _ _ _ n hk20
  have s2 : dictSet (h.fresh (.dict []) x) [(a, v1)] k2 v2 = .ok [(a, v2)] := by
    simp only [dictSet, storeKey_atom _ k2 n hk20]
    have hq : pyEq (eqFuel (h.fresh (.dict []) x)) (h.fresh (.dict []) x) a k2 = .ok true := by
      rw [show eqFuel (h.fresh (.dict []) x) = (2 * (h.fresh (.dict []) x).cells.length + 1) + 1 from rfl,
        pyEq_atoms _ _ _ _ n n ha0 hk20]
      simp
    have := storeItem_hit (pyEq (eqFuel (h.fresh (.dict []) x)) (h.fresh (.dict []) x)) k2 v2 a v1 [] []
      (by simp) hq
    simpa using this
  have hd : deepPairs (fuel + 3) (h.fresh (.dict []) x) [] [(k1, v1), (k2, v2)] =
      .ok (h.fresh (.dict []) x, [(a, v2)]) := by
    simp only [deepPairs, e1, e2, s1, e3, e4, s2]
  refine ⟨_, deepcopy_dict (fuel + 3) h x _ hc hm _ _ hd, ?_⟩
  apply get_set_same
  rw [fresh_len]; omega

/-- The order inside the copy of a dict, and the reverse order in `_reconstruct`. `y[deepcopy(key, memo)] =
deepcopy(value, memo)` evaluates its right side first, so at Lib/copy.py:201 a failing value hides a failing key. The
explicit lines of `_reconstruct`, :279-281, copy the key first. Inside `deepList`, a failing item stops the list. -/
def DeepCopyOrder : Prop :=
  ∀ (fuel : Nat) (h h1 : Heap) (k v y a v' : Nat) (acc r : List (Nat × Nat)) (as : List Nat) (e : PyExc),
    (deepcopy fuel h v = .error e → deepPairs (fuel + 1) h acc ((k, v) :: r) = .error e) ∧
    (deepcopy fuel h v = .ok (h1, v') → deepcopy fuel h1 k = .error e →
      deepPairs (fuel + 1) h acc ((k, v) :: r) = .error e) ∧
    (deepcopy fuel h k = .error e → deepSetItems (fuel + 1) h y ((k, v) :: r) = .error e) ∧
    (deepcopy fuel h a = .error e → deepList (fuel + 1) h (a :: as) = .error e) ∧
    (deepcopy fuel h a = .error e → deepAppend (fuel + 1) h y (a :: as) = .error e)

theorem deepCopyOrder_proven : DeepCopyOrder := by
  intro fuel h h1 k v y a v' acc r as e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h2; simp [deepPairs, h2]
  · intro h2 h3; simp [deepPairs, h2, h3]
  · intro h2; simp [deepSetItems, h2]
  · intro h2; simp [deepList, h2]
  · intro h2; simp [deepAppend, h2]

/-- `memo` keeps aliasing: in `[a, a]`, the two items of the copy are one new object, and not the old one and not two
new ones. -/
def DeepcopyAliasing : Prop :=
  ∀ (fuel : Nat) (h : Heap) (x a : Nat), h.get x = .list [a, a] → h.get a = .list [] → h.memo.lookup x = none →
    h.memo.lookup a = none →
    ∃ h', deepcopy (fuel + 5) h x = .ok (h', h.cells.length) ∧
      h'.get h.cells.length = .list [h.cells.length + 1, h.cells.length + 1] ∧
      h'.get (h.cells.length + 1) = .list [] ∧ a < h.cells.length

theorem deepcopyAliasing_proven : DeepcopyAliasing := by
  intro fuel h x a hc ha hm hma
  have hax := get_of_list h a _ ha
  have hxx := get_of_list h x _ hc
  have hne : a ≠ x := by
    intro he; rw [he, hc] at ha; simp at ha
  generalize hh2 : h.fresh (.list []) x = h2
  have hlen : h2.cells.length = h.cells.length + 1 := by rw [← hh2, fresh_len]
  have hg : h2.get a = .list [] := by rw [← hh2, fresh_get_old _ _ _ _ hax]; exact ha
  have hl : h2.memo.lookup a = none := by rw [← hh2, fresh_lookup_other _ _ _ _ hne]; exact hma
  generalize hh3 : (h2.fresh (.list []) a).set h2.cells.length (.list []) = h3
  have c1 : deepcopy (fuel + 3) h2 a = .ok (h3, h2.cells.length) := by
    rw [← hh3]
    exact deepcopy_list _ h2 a [] hg hl _ _ (deepList_nil _ _)
  have hl3 : h3.memo.lookup a = some h2.cells.length := by rw [← hh3, set_memo, fresh_lookup_self]
  have hg3 : h3.get a = .list [] := by
    rw [← hh3, get_set_other _ _ _ _ (by omega), fresh_get_old _ _ _ _ (by omega)]
    exact hg
  have c2 : deepcopy (fuel + 2) h3 a = .ok (h3, h2.cells.length) :=
    deepcopy_memo _ _ _ _ hl3 (by intro m hm; rw [hg3] at hm; cases hm) (by intro m hm; rw [hg3] at hm; cases hm) (by intro m hm; rw [hg3] at hm; cases hm)
  have d1 : deepList (fuel + 3) h3 [a] = .ok (h3, [h2.cells.length]) :=
    deepList_cons _ _ _ _ _ _ _ _ c2 (deepList_nil _ _)
  have d2 : deepList (fuel + 4) h2 [a, a] = .ok (h3, [h2.cells.length, h2.cells.length]) :=
    deepList_cons _ _ _ _ _ _ _ _ c1 d1
  rw [← hh2] at d2
  have hlen3 : h3.cells.length = h.cells.length + 2 := by rw [← hh3, set_len, fresh_len]; omega
  refine ⟨_, deepcopy_list _ h x _ hc hm _ _ d2, ?_, ?_, hax⟩
  · rw [hh2, hlen]
    apply get_set_same
    omega
  · rw [get_set_other _ _ _ _ (by omega), ← hh3]
    rw [hlen, get_set_same]
    rw [fresh_len]; omega

/-- `_deepcopy_tuple`, the two paths past the atoms of `DeepcopyTupleIdentity`. A tuple holding something mutable
becomes a new tuple of the copies, recorded in `memo`. A tuple reached again through its own items is the point of
the second `memo` read at Lib/copy.py:185: for `t = ([t],)`, the inner call builds the one copy, the outer call finds
it, and the copied list and tuple refer to each other. Without that read there would be two tuples. -/
def DeepcopyTupleExact : Prop :=
  ∀ (fuel : Nat) (h : Heap) (x a : Nat), h.memo.lookup x = none → h.memo.lookup a = none →
    (h.get x = .tuple [a] → h.get a = .list [] →
      ∃ h', deepcopy (fuel + 4) h x = .ok (h', h.cells.length + 1) ∧
        h'.get (h.cells.length + 1) = .tuple [h.cells.length] ∧ h'.get h.cells.length = .list [] ∧
        h'.memo.lookup x = some (h.cells.length + 1)) ∧
    (x < h.cells.length → h.get x = .tuple [a] → h.get a = .list [x] →
      ∃ h', deepcopy (fuel + 7) h x = .ok (h', h.cells.length + 1) ∧
        h'.get (h.cells.length + 1) = .tuple [h.cells.length] ∧
        h'.get h.cells.length = .list [h.cells.length + 1])

theorem deepcopyTupleExact_proven : DeepcopyTupleExact := by
  intro fuel h x a hmx hma
  refine ⟨?_, ?_⟩
  · intro hc ha
    have hax := get_of_list h a _ ha
    have hn : x ≠ a := by
      intro he; rw [← he, hc] at ha; cases ha
    have c1 : deepcopy (fuel + 2) h a = .ok ((h.fresh (.list []) a).set h.cells.length (.list []), h.cells.length) :=
      deepcopy_list _ h a [] ha hma _ _ (deepList_nil _ _)
    have d1 := deepList_cons _ _ _ _ _ _ _ _ c1 (deepList_nil (fuel + 1) _)
    generalize hh : (h.fresh (.list []) a).set h.cells.length (.list []) = h1 at d1
    have hm1 : h1.memo.lookup x = none := by
      rw [← hh, set_memo, fresh_lookup_other _ _ _ _ hn]
      exact hmx
    have hl1 : h1.cells.length = h.cells.length + 1 := by rw [← hh, set_len, fresh_len]
    have hne : ([h.cells.length] == [a]) = false := by
      have : h.cells.length ≠ a := by omega
      simp [this]
    have ct := deepcopy_tuple_new (fuel + 3) h h1 x [a] [h.cells.length] hc hmx d1 hm1 hne
    rw [hl1] at ct
    refine ⟨_, ct, ?_, ?_, ?_⟩
    · have := fresh_get_new h1 (.tuple [h.cells.length]) x
      rwa [hl1] at this
    · rw [fresh_get_old _ _ _ _ (by omega), ← hh]
      apply get_set_same
      rw [fresh_len]; omega
    · have := fresh_lookup_self h1 (.tuple [h.cells.length]) x
      rwa [hl1] at this
  · intro hx hc ha
    have hax := get_of_list h a _ ha
    have hn : x ≠ a := by
      intro he; rw [← he, hc] at ha; cases ha
    generalize hh2 : h.fresh (.list []) a = h2
    have hlen : h2.cells.length = h.cells.length + 1 := by rw [← hh2, fresh_len]
    have hg2x : h2.get x = .tuple [a] := by rw [← hh2, fresh_get_old _ _ _ _ hx]; exact hc
    have hg2a : h2.get a = .list [x] := by rw [← hh2, fresh_get_old _ _ _ _ hax]; exact ha
    have hl2a : h2.memo.lookup a = some h.cells.length := by rw [← hh2, fresh_lookup_self]
    have hl2x : h2.memo.lookup x = none := by rw [← hh2, fresh_lookup_other _ _ _ _ hn]; exact hmx
    have c0 : deepcopy (fuel + 1) h2 a = .ok (h2, h.cells.length) :=
      deepcopy_memo _ _ _ _ hl2a (by intro m hm; rw [hg2a] at hm; cases hm) (by intro m hm; rw [hg2a] at hm; cases hm) (by intro m hm; rw [hg2a] at hm; cases hm)
    have d0 := deepList_cons _ _ _ _ _ _ _ _ c0 (deepList_nil fuel _)
    have hne : ([h.cells.length] == [a]) = false := by
      have : h.cells.length ≠ a := by omega
      simp [this]
    have ct := deepcopy_tuple_new (fuel + 2) h2 h2 x [a] [h.cells.length] hg2x hl2x d0 hl2x hne
    have d1 := deepList_cons _ _ _ _ _ _ _ _ ct (deepList_nil (fuel + 2) _)
    rw [hlen, ← hh2] at d1
    have cl := deepcopy_list (fuel + 4) h a [x] ha hma _ _ (by rw [hh2] at d1 ⊢; exact d1)
    have d2 := deepList_cons _ _ _ _ _ _ _ _ cl (deepList_nil (fuel + 4) _)
    generalize hh4 : (h2.fresh (.tuple [h.cells.length]) x).set h.cells.length (.list [h.cells.length + 1]) = h4 at d2
    have hl4 : h4.memo.lookup x = some (h.cells.length + 1) := by
      rw [← hh4, set_memo, fresh_lookup_self, hlen]
    refine ⟨_, deepcopy_tuple_memo (fuel + 6) h h4 x _ [a] _ hc hmx d2 hl4, ?_, ?_⟩
    · rw [← hh4, get_set_other _ _ _ _ (by omega)]
      have := fresh_get_new h2 (.tuple [h.cells.length]) x
      rwa [hlen] at this
    · rw [← hh4]
      apply get_set_same
      rw [fresh_len]; omega

theorem deepcopy_hooked (fuel : Nat) (h h1 h5 h6 h7 : Heap) (x n : Nat) (c : Option (Option PyExc))
    (k : BuildKind) (args a' : List Nat) (s : Option Nat) (li : Option (ItemsIter Nat))
    (di : Option (ItemsIter (Nat × Nat))) (ss : Option (Option PyExc))
    (hc : h.get x = .hooked c none (some (.tuple n none k args s li di ss))) (hm : h.memo.lookup x = none)
    (hn1 : ¬ n < 2) (hn2 : ¬ n > 5) (e1 : deepList fuel h args = .ok (h1, a'))
    (e2 : deepState fuel (h1.fresh (freshOf k a') x) h1.cells.length s ss = .ok h5)
    (e4 : deepAppend fuel h5 h1.cells.length ((li.map (·.items)).getD []) = .ok h6)
    (f4 : li.bind (·.fail) = none)
    (e5 : deepSetItems fuel h6 h1.cells.length ((di.map (·.items)).getD []) = .ok h7)
    (f5 : di.bind (·.fail) = none) :
    deepcopy (fuel + 1) h x = .ok (h7, h1.cells.length) := by
  rw [deepcopy]
  simp only [hc, hm]
  simp only [Heap.fresh] at e2
  simp [Heap.alloc] at e2
  simp [reconArity, hn1, hn2, e1, Heap.alloc, e2, e4, f4, e5, f5]

/-- The steps of `_reconstruct` with `deep` true, in the source's order. The argument count is checked by the call,
before anything is copied. The arguments are copied before `func` runs, so a failing copy hides a failing
constructor, and a failing constructor comes after the copies. -/
def ReconstructDeepSteps : Prop :=
  ∀ (fuel : Nat) (h h1 : Heap) (x n : Nat) (c : Option (Option PyExc)) (fail : Option PyExc) (k : BuildKind)
    (args a' : List Nat) (s : Option Nat) (li : Option (ItemsIter Nat)) (di : Option (ItemsIter (Nat × Nat)))
    (ss : Option (Option PyExc)) (e : PyExc),
    h.get x = .hooked c none (some (.tuple n fail k args s li di ss)) → h.memo.lookup x = none →
    ((n < 2 ∨ n > 5) → (deepcopy (fuel + 1) h x).raises "TypeError") ∧
    (2 ≤ n → n ≤ 5 → deepList fuel h args = .error e → deepcopy (fuel + 1) h x = .error e) ∧
    (2 ≤ n → n ≤ 5 → deepList fuel h args = .ok (h1, a') → fail = some e → deepcopy (fuel + 1) h x = .error e)

theorem reconstructDeepSteps_proven : ReconstructDeepSteps := by
  intro fuel h h1 x n c fail k args a' s li di ss e hc hm
  refine ⟨?_, ?_, ?_⟩
  · intro hn
    rw [deepcopy]
    simp only [hc, hm]
    rcases hn with hn | hn
    · exact ⟨_, by simp [reconArity, hn]; rfl, rfl⟩
    · have h2 : ¬ n < 2 := by omega
      exact ⟨_, by simp [reconArity, h2, hn]; rfl, rfl⟩
  · intro h2 h3 h4
    have h5 : ¬ n < 2 := by omega
    have h6 : ¬ n > 5 := by omega
    rw [deepcopy]
    simp only [hc, hm]
    simp [reconArity, h5, h6, h4]
  · intro h2 h3 h4 h7
    have h5 : ¬ n < 2 := by omega
    have h6 : ¬ n > 5 := by omega
    rw [deepcopy]
    simp only [hc, hm]
    simp [reconArity, h5, h6, h4, h7]

/-- `memo[id(x)] = y` comes before the state is copied, Lib/copy.py:248-253: an object whose state refers back to it
gets a copy whose state refers to the copy. With the two lines swapped the state copy would recurse for ever. -/
def ReconstructMemoFirst : Prop :=
  ∀ (fuel : Nat) (h : Heap) (x st n : Nat) (c : Option (Option PyExc)), 2 ≤ n → n ≤ 5 → x < h.cells.length →
    h.get x = .hooked c none (some (.tuple n none .inst [] (some st) none none (some none))) →
    h.get st = .list [x] → h.memo.lookup x = none → h.memo.lookup st = none →
    ∃ h', deepcopy (fuel + 6) h x = .ok (h', h.cells.length) ∧
      h'.get h.cells.length = .inst [(.name "__state__", h.cells.length + 1)] ∧
      h'.get (h.cells.length + 1) = .list [h.cells.length]

theorem reconstructMemoFirst_proven : ReconstructMemoFirst := by
  intro fuel h x st n c hn1 hn2 hx hc hs hmx hms
  have hst := get_of_list h st _ hs
  have hne : st ≠ x := by
    intro he; rw [he, hc] at hs; cases hs
  have hf : freshOf .inst [] = .inst [] := rfl
  generalize hh2 : h.fresh (.inst []) x = h2
  have hlen : h2.cells.length = h.cells.length + 1 := by rw [← hh2, fresh_len]
  have hg2 : h2.get st = .list [x] := by rw [← hh2, fresh_get_old _ _ _ _ hst]; exact hs
  have hl2 : h2.memo.lookup st = none := by rw [← hh2, fresh_lookup_other _ _ _ _ hne]; exact hms
  generalize hh3 : h2.fresh (.list []) st = h3
  have hl3x : h3.memo.lookup x = some h.cells.length := by
    rw [← hh3, fresh_lookup_other _ _ _ _ hne.symm, ← hh2, fresh_lookup_self]
  have hg3x : h3.get x = .hooked c none (some (.tuple n none .inst [] (some st) none none (some none))) := by
    rw [← hh3, fresh_get_old _ _ _ _ (by omega), ← hh2, fresh_get_old _ _ _ _ hx]
    exact hc
  have c0 : deepcopy (fuel + 2) h3 x = .ok (h3, h.cells.length) :=
    deepcopy_memo _ _ _ _ hl3x (by intro m hm; rw [hg3x] at hm; cases hm) (by intro m hm; rw [hg3x] at hm; cases hm) (by intro m hm; rw [hg3x] at hm; cases hm)
  have d0 := deepList_cons _ _ _ _ _ _ _ _ c0 (deepList_nil (fuel + 1) _)
  have cl := deepcopy_list (fuel + 3) h2 st [x] hg2 hl2 _ _ (by rw [hh3]; exact d0)
  generalize hh4 : h3.set h2.cells.length (.list [h.cells.length]) = h4 at cl
  have hlen3 : h3.cells.length = h.cells.length + 2 := by rw [← hh3, fresh_len, hlen]
  have hlen4 : h4.cells.length = h.cells.length + 2 := by rw [← hh4, set_len, hlen3]
  have hg4y : h4.get h.cells.length = .inst [] := by
    rw [← hh4, get_set_other _ _ _ _ (by omega), ← hh3, fresh_get_old _ _ _ _ (by omega), ← hh2, fresh_get_new]
  have hg4s : h4.get (h.cells.length + 1) = .list [h.cells.length] := by
    rw [← hh4, hlen.symm]
    apply get_set_same
    omega
  rw [hlen] at cl
  generalize hh5 : h4.set h.cells.length (.inst [(.name "__state__", h.cells.length + 1)]) = h5
  have hsn : noneCell h2 st = false := by simp [noneCell, hg2]
  have eo : deepState (fuel + 5) (h.fresh (freshOf .inst []) x) h.cells.length (some st) (some none) = .ok h5 := by
    rw [hf, hh2, ← hh5]
    simp [deepState, hsn, cl, stateApply, setstateOf, setAttrOf, hg4y, storeItem]
  have ea : deepAppend (fuel + 5) h5 h.cells.length [] = .ok h5 := by simp [deepAppend]
  have es : deepSetItems (fuel + 5) h5 h.cells.length [] = .ok h5 := by simp [deepSetItems]
  have hd := deepcopy_hooked (fuel + 5) h h h5 h5 h5 x n c .inst [] [] (some st) none none (some none) hc hmx
    (by omega) (by omega) (deepList_nil _ _) eo ea rfl es rfl
  refine ⟨_, hd, ?_, ?_⟩
  · rw [← hh5]
    apply get_set_same
    omega
  · rw [← hh5, get_set_other _ _ _ _ (by omega)]
    exact hg4s

theorem fold_appendTo (y : Nat) : ∀ (l : List Nat) (h : Heap) (old : List Nat), h.get y = .list old →
    y < h.cells.length →
    ∃ h', appendAll h y l = .ok h' ∧ h'.get y = .list (old ++ l) ∧ ∀ z, z ≠ y → h'.get z = h.get z
  | [], h, old, hg, _ => ⟨h, rfl, by simpa using hg, fun _ _ => rfl⟩
  | i :: l, h, old, hg, hy => by
    have h1 : appendTo h y i = .ok (h.set y (.list (old ++ [i]))) := by simp [appendTo, hg]
    obtain ⟨h', e, g, o⟩ := fold_appendTo y l (h.set y (.list (old ++ [i]))) (old ++ [i])
      (get_set_same _ _ _ hy) (by rw [set_len]; exact hy)
    refine ⟨h', by simp only [appendAll, h1]; exact e, by simpa using g, ?_⟩
    intro z hz
    rw [o z hz, get_set_other _ _ _ _ hz]

/-- `dictiter` stores on atoms with pairwise unequal keys, none equal to a key already in `y`: every pair goes at the end,
in order. -/
theorem fold_setItemOf (y : Nat) : ∀ (l : List (Nat × Nat)) (h : Heap) (old : List (Nat × Nat)),
    h.get y = .dict old → y < h.cells.length →
    (∀ p ∈ old ++ l, ∃ n, h.get p.1 = .atom n) → List.Pairwise (fun p q => h.get p.1 ≠ h.get q.1) (old ++ l) →
    ∃ h', setAll h y l = .ok h' ∧ h'.get y = .dict (old ++ l) ∧ ∀ z, z ≠ y → h'.get z = h.get z
  | [], h, old, hg, _, _, _ => ⟨h, rfl, by simpa using hg, fun _ _ => rfl⟩
  | (k, v) :: l, h, old, hg, hy, ha, hp => by
    obtain ⟨n, hn⟩ := ha (k, v) (by simp)
    have hs : dictSet h old k v = .ok (old ++ [(k, v)]) := by
      apply dictSet_atom_fresh h old k v n hn
      intro q hq
      refine ⟨ha q (by simp [hq]), ?_⟩
      rw [← hn]
      exact (List.pairwise_append.1 hp).2.2 q hq (k, v) (by simp)
    have h1 : setItemOf h y k v = .ok (h.set y (.dict (old ++ [(k, v)]))) := by simp [setItemOf, hg, hs]
    have hne : ∀ q ∈ old ++ (k, v) :: l, q.1 ≠ y := by
      intro q hq e
      obtain ⟨m, hm⟩ := ha q hq
      rw [e, hg] at hm
      cases hm
    have hkey : ∀ q ∈ old ++ (k, v) :: l, (h.set y (.dict (old ++ [(k, v)]))).get q.1 = h.get q.1 :=
      fun q hq => get_set_other _ _ _ _ (hne q hq)
    have e : old ++ [(k, v)] ++ l = old ++ (k, v) :: l := by simp
    obtain ⟨h', e', g, o⟩ := fold_setItemOf y l (h.set y (.dict (old ++ [(k, v)]))) (old ++ [(k, v)])
      (get_set_same _ _ _ hy) (by rw [set_len]; exact hy)
      (by rw [e]; intro q hq; rw [hkey q hq]; exact ha q hq)
      (by rw [e]; exact hp.imp_of_mem (fun ha' hb' r => by rw [hkey _ ha', hkey _ hb']; exact r))
    refine ⟨h', by simp only [setAll, h1]; exact e', by rw [e] at g; exact g, ?_⟩
    intro z hz
    rw [o z hz, get_set_other _ _ _ _ hz]

/-- The tail of `_reconstruct`, on the object `y`. `listiter` appends every item, in order, and nothing else changes;
an iterator that raises after its items raises after they are stored. `dictiter` stores every pair with
`y[key] = value`, Lib/copy.py:281 and :284, so pairs with pairwise unequal keys go at the end in order, while a key equal
to one already stored (two atoms of one value) keeps that key's place and key object and takes the new value, and an
unhashable key is the `TypeError` of the store. `listiter` runs before `dictiter`, so when both raise, the
`listiter` error comes out. A state that is not `None` goes to `__setstate__`, which stores it as a dict store does (a new
name at the end, an existing one in place), and whose exception
propagates; a state that is `None` is as if there were none, so even a raising `__setstate__` is not called. A
`dictiter` on an object without `__setitem__` is a `TypeError`. Every key in the unequal-keys case is an atom, and
"unequal" is the invariant a real `dict` keeps. -/
def ReconRestItems : Prop :=
  ∀ (h : Heap) (y st : Nat) (old l : List Nat) (oldD d : List (Nat × Nat)) (a pre post : List (AttrKey × Nat))
    (e : PyExc) (li : Option (ItemsIter Nat)) (di : Option (ItemsIter (Nat × Nat))) (p : Nat × Nat)
    (k1 v1 k2 v2 w : Nat) (n : Int) (ul : List Nat) (f : Option PyExc) (ss : Option (Option PyExc)),
    y < h.cells.length →
    (h.get y = .list old → ∃ h', reconRest h y none (some ⟨l, none⟩) none none = .ok h' ∧
      h'.get y = .list (old ++ l) ∧ ∀ z, z ≠ y → h'.get z = h.get z) ∧
    (h.get y = .list old → reconRest h y none (some ⟨l, some e⟩) none none = .error e) ∧
    (h.get y = .list old → reconRest h y none (some ⟨l, some e⟩) (some ⟨d, f⟩) none = .error e) ∧
    (h.get y = .dict oldD → (∀ q ∈ oldD ++ d, ∃ m, h.get q.1 = .atom m) →
      List.Pairwise (fun q r => h.get q.1 ≠ h.get r.1) (oldD ++ d) →
      ∃ h', reconRest h y none none (some ⟨d, none⟩) none = .ok h' ∧ h'.get y = .dict (oldD ++ d) ∧
      ∀ z, z ≠ y → h'.get z = h.get z) ∧
    (h.get y = .dict oldD → (∀ q ∈ oldD ++ d, ∃ m, h.get q.1 = .atom m) →
      List.Pairwise (fun q r => h.get q.1 ≠ h.get r.1) (oldD ++ d) →
      reconRest h y none none (some ⟨d, some e⟩) none = .error e) ∧
    (h.get y = .dict oldD → h.get k1 = .atom n → h.get k2 = .atom n →
      (∀ q ∈ oldD, (∃ m, h.get q.1 = .atom m) ∧ h.get q.1 ≠ .atom n) →
      reconRest h y none none (some ⟨[(k1, v1), (k2, v2)], none⟩) none =
        .ok (h.set y (.dict (oldD ++ [(k1, v2)])))) ∧
    (h.get y = .dict oldD → h.get p.1 = .list ul →
      reconRest h y none none (some ⟨p :: d, f⟩) none =
        .error (.typeError "cannot use 'list' as a dict key (unhashable type: 'list')")) ∧
    (h.get y = .inst a → noneCell h st = false → (∀ q ∈ a, q.1 ≠ .name "__state__") →
      reconRest h y (some st) none none (some none) = .ok (h.set y (.inst (a ++ [(.name "__state__", st)])))) ∧
    (h.get y = .inst (pre ++ (.name "__state__", w) :: post) → noneCell h st = false →
      (∀ q ∈ pre, q.1 ≠ .name "__state__") →
      reconRest h y (some st) none none (some none) =
        .ok (h.set y (.inst (pre ++ (.name "__state__", st) :: post)))) ∧
    (noneCell h st = false → reconRest h y (some st) li di (some (some e)) = .error e) ∧
    (noneCell h st = true → reconRest h y (some st) li di ss = reconRest h y none li di ss) ∧
    (h.get y = .list [] → h.get p.1 = .atom n → n ≠ 0 → n ≤ 9223372036854775807 → -9223372036854775808 ≤ n →
      reconRest h y none none (some ⟨p :: d, f⟩) none = .error (.indexError "list assignment index out of range")) ∧
    ((∀ m, h.get y ≠ .dict m) → (∀ m, h.get y ≠ .list m) →
      (reconRest h y none none (some ⟨p :: d, f⟩) none).raises "TypeError")

theorem reconRestItems_proven : ReconRestItems := by
  intro h y st old l oldD d a pre post e li di p k1 v1 k2 v2 w n ul f ss hy
  obtain ⟨pk, pv⟩ := p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hg
    obtain ⟨h', e1, g, o⟩ := fold_appendTo y l h old hg hy
    exact ⟨h', by simp [reconRest, e1], g, o⟩
  · intro hg
    obtain ⟨h', e1, g, o⟩ := fold_appendTo y l h old hg hy
    simp [reconRest, e1]
  · intro hg
    obtain ⟨h', e1, g, o⟩ := fold_appendTo y l h old hg hy
    simp [reconRest, e1]
  · intro hg ha hp
    obtain ⟨h', e1, g, o⟩ := fold_setItemOf y d h oldD hg hy ha hp
    exact ⟨h', by simp [reconRest, e1], g, o⟩
  · intro hg ha hp
    obtain ⟨h', e1, g, o⟩ := fold_setItemOf y d h oldD hg hy ha hp
    simp [reconRest, e1]
  · intro hg hk1 hk2 ho
    have s1 : setItemOf h y k1 v1 = .ok (h.set y (.dict (oldD ++ [(k1, v1)]))) := by
      simp [setItemOf, hg, dictSet_atom_fresh h oldD k1 v1 n hk1 ho]
    have hny : ∀ i m, h.get i = .atom m → i ≠ y := by
      intro i m hi e
      rw [e, hg] at hi
      cases hi
    have g1 : ∀ i m, h.get i = .atom m → (h.set y (.dict (oldD ++ [(k1, v1)]))).get i = .atom m := by
      intro i m hi
      rw [get_set_other _ _ _ _ (hny i m hi)]
      exact hi
    have s2 : setItemOf (h.set y (.dict (oldD ++ [(k1, v1)]))) y k2 v2 =
        .ok ((h.set y (.dict (oldD ++ [(k1, v1)]))).set y (.dict (oldD ++ [(k1, v2)]))) := by
      have hk2' := g1 k2 n hk2
      have hd : dictSet (h.set y (.dict (oldD ++ [(k1, v1)]))) (oldD ++ [(k1, v1)]) k2 v2 =
          .ok (oldD ++ [(k1, v2)]) := by
        simp only [dictSet, storeKey_atom _ k2 n hk2']
        apply storeItem_hit
        · intro q hq
          obtain ⟨⟨m, hm⟩, hne⟩ := ho q hq
          have hq2 : q.1 ≠ k2 := by
            intro e
            rw [e, hk2] at hne
            exact hne rfl
          have hmn : m ≠ n := by
            intro e
            rw [e] at hm
            exact hne hm
          rw [show eqFuel (h.set y (.dict (oldD ++ [(k1, v1)]))) =
              (2 * (h.set y (.dict (oldD ++ [(k1, v1)]))).cells.length + 1) + 1 from rfl,
            pyEq_atoms _ _ _ _ m n (g1 _ _ hm) hk2']
          simp [hq2, hmn]
        · rw [show eqFuel (h.set y (.dict (oldD ++ [(k1, v1)]))) =
              (2 * (h.set y (.dict (oldD ++ [(k1, v1)]))).cells.length + 1) + 1 from rfl,
            pyEq_atoms _ _ _ _ n n (g1 _ _ hk1) hk2']
          simp
      simp [setItemOf, get_set_same _ _ _ hy, hd]
    have hset : (h.set y (.dict (oldD ++ [(k1, v1)]))).set y (.dict (oldD ++ [(k1, v2)])) =
        h.set y (.dict (oldD ++ [(k1, v2)])) := by
      simp [Heap.set]
    simp only [reconRest, setAll, s1, s2, hset]
  · intro hg hl
    have h1 : setItemOf h y pk pv =
        .error (.typeError "cannot use 'list' as a dict key (unhashable type: 'list')") := by
      simp [setItemOf, hg, dictSet, storeKey, keyHashErr, cellName, hl] <;> first | rfl | decide
    simp [reconRest, setAll, h1]
  · intro hg hn hq
    have hst : storeItem (akEq h) a (.name "__state__") st = .ok (a ++ [(.name "__state__", st)]) :=
      storeItem_miss _ _ _ a (fun q hq' => akEq_name_ne h q.1 _ (hq q hq'))
    simp [reconRest, hn, stateApply, setstateOf, setAttrOf, hg, hst]
  · intro hg hn hq
    have hst : storeItem (akEq h) (pre ++ (.name "__state__", w) :: post) (.name "__state__") st =
        .ok (pre ++ (.name "__state__", st) :: post) :=
      storeItem_hit _ _ _ _ _ post pre (fun q hq' => akEq_name_ne h q.1 _ (hq q hq')) (by simp [akEq])
    simp [reconRest, hn, stateApply, setstateOf, setAttrOf, hg, hst]
  · intro hn
    simp [reconRest, hn, stateApply, setstateOf]
  · intro hn
    simp [reconRest, hn]
  · intro hg hk h0 hlo hhi
    have h1 : setItemOf h y pk pv = .error (.indexError "list assignment index out of range") := by
      have : ¬ (n > 9223372036854775807 ∨ n < -9223372036854775808) := by omega
      have hs : listSet [] n pv = none := by
        unfold listSet
        by_cases hn : n < 0
        · simp [hn]
        · simp [hn]
      simp only [setItemOf, hg, hk, h0, this, ite_false, hs]
    simp [reconRest, setAll, h1]
  · intro hg hl
    have h1 : setItemOf h y pk pv = .error (.typeError "~object does not support item assignment") := by
      unfold setItemOf
      cases hv : h.get y with
      | dict m => exact absurd hv (hg m)
      | list m => exact absurd hv (hl m)
      | _ => rfl
    refine ⟨.typeError "~object does not support item assignment", ?_, rfl⟩
    simp [reconRest, setAll, h1]

/-- `_reconstruct` with `deep` true and a state that is `None`: the state is not copied and `__setstate__` is not
called, even one that would raise, Lib/copy.py:252; the copy is the object the constructor made, in `memo`. With a
state that is not `None`, the copy of the state goes to `__setstate__` whatever it is, and its exception comes out. -/
def DeepcopyStateNone : Prop :=
  ∀ (fuel : Nat) (h h1 : Heap) (x st s' n : Nat) (c : Option (Option PyExc)) (e : PyExc),
    2 ≤ n → n ≤ 5 → h.get x = .hooked c none (some (.tuple n none .inst [] (some st) none none (some (some e)))) →
    h.memo.lookup x = none → st < h.cells.length →
    (noneCell h st = true → deepcopy (fuel + 2) h x = .ok (h.fresh (.inst []) x, h.cells.length)) ∧
    (noneCell h st = false → deepcopy fuel (h.fresh (.inst []) x) st = .ok (h1, s') →
      deepcopy (fuel + 2) h x = .error e)

theorem deepcopyStateNone_proven : DeepcopyStateNone := by
  intro fuel h h1 x st s' n c e hn1 hn2 hc hm hst
  have hsame : noneCell (h.fresh (.inst []) x) st = noneCell h st := by
    simp [noneCell, fresh_get_old _ _ _ _ hst]
  refine ⟨?_, ?_⟩
  · intro hnone
    have e2 : deepState (fuel + 1) (h.fresh (freshOf .inst []) x) h.cells.length (some st) (some (some e)) =
        .ok (h.fresh (.inst []) x) := by
      have : freshOf .inst [] = .inst [] := rfl
      rw [this]
      simp [deepState, hsame, hnone]
    have e4 : deepAppend (fuel + 1) (h.fresh (.inst []) x) h.cells.length [] = .ok (h.fresh (.inst []) x) := by
      simp [deepAppend]
    have e5 : deepSetItems (fuel + 1) (h.fresh (.inst []) x) h.cells.length [] = .ok (h.fresh (.inst []) x) := by
      simp [deepSetItems]
    exact deepcopy_hooked (fuel + 1) h h _ _ _ x n c .inst [] [] (some st) none none (some (some e)) hc hm
      (by omega) (by omega) (deepList_nil _ _) e2 e4 rfl e5 rfl
  · intro hnone hd
    have h3 : ¬ n < 2 := by omega
    have h4 : ¬ n > 5 := by omega
    have hsame' : noneCell ((h.alloc (.inst [])).1.remember x h.cells.length) st = false := by
      have := hsame
      simp only [Heap.fresh] at this
      rw [this, hnone]
    simp only [Heap.fresh] at hd
    rw [deepcopy]
    simp only [hc, hm]
    simp [reconArity, h3, h4, deepList, freshOf, deepState, Heap.alloc] at hd hsame' ⊢
    simp [hsame', hd, stateApply, setstateOf]

/-- `listiter` and `dictiter` are iterators, and one that raises after its items makes the deep copy raise too, after
the items are in, Lib/copy.py:270-272 and :278-281; `listiter` is read first, so when both raise its error wins. -/
def DeepcopyIterFails : Prop :=
  ∀ (fuel : Nat) (h : Heap) (x n : Nat) (c : Option (Option PyExc)) (e : PyExc),
    2 ≤ n → n ≤ 5 → h.memo.lookup x = none →
    (h.get x = .hooked c none (some (.tuple n none .list [] none (some ⟨[], some e⟩) none none)) →
      deepcopy (fuel + 2) h x = .error e) ∧
    (h.get x = .hooked c none (some (.tuple n none .dict [] none none (some ⟨[], some e⟩) none)) →
      deepcopy (fuel + 2) h x = .error e) ∧
    (∀ e2, h.get x = .hooked c none (some (.tuple n none .list [] none (some ⟨[], some e⟩) (some ⟨[], some e2⟩) none)) →
      deepcopy (fuel + 2) h x = .error e)

theorem deepcopyIterFails_proven : DeepcopyIterFails := by
  intro fuel h x n c e hn1 hn2 hm
  have h3 : ¬ n < 2 := by omega
  have h4 : ¬ n > 5 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    rw [deepcopy]
    simp [hc, hm, reconArity, h3, h4, deepList, deepState, deepAppend]
  · intro hc
    rw [deepcopy]
    simp [hc, hm, reconArity, h3, h4, deepList, deepState, deepAppend, deepSetItems]
  · intro e2 hc
    rw [deepcopy]
    simp [hc, hm, reconArity, h3, h4, deepList, deepState, deepAppend]

/-- The heap of `a = A(); a.m = a.f0`: the instance holds its own bound method as the attribute `m`. -/
def methodAliasHeap : Heap := ⟨[.inst [(.name "m", 1)], .method 0 0], []⟩

/-- `deepcopy(a.m)` in the model: the instance is copied to cell 2, whose `m` is the method copied through it (cell 3),
and then `_deepcopy_method` makes a second method (cell 4), the result. -/
def methodAliasCopy : Heap :=
  ⟨[.inst [(.name "m", 1)], .method 0 0, .inst [(.name "m", 3)], .method 0 2, .method 0 2],
    [(1, 4), (1, 3), (0, 2)]⟩

/-- `deepcopy` keeps shared structure: the memo is there so that an object reached twice is copied once ("keeping a
`memo` dictionary of objects already copied during the current copying pass", Doc/library/copy.rst:64). So a bound
method whose `__self__` holds the method itself under some name is copied to a method whose `__self__` holds the copy
under that name, as `_deepcopy_tuple` ensures for a tuple, Lib/copy.py:184-187 (the read at :185). False: `_deepcopy_method`, :220-221,
copies `__self__` first, which copies the method once through that attribute and records it in `memo`, and then builds
a second method without reading `memo` again, so the copy's `__self__.m` is a different method from the copy. -/
def DeepcopyMethodAliasing : Prop :=
  ∀ (fuel : Nat) (h h' : Heap) (x f s y : Nat) (attrs : List (AttrKey × Nat)) (k : String),
    h.get x = .method f s → h.get s = .inst attrs → attrs.lookup (.name k) = some x → h.memo = [] →
    deepcopy fuel h x = .ok (h', y) →
    ∃ s' attrs', h'.get y = .method f s' ∧ h'.get s' = .inst attrs' ∧ attrs'.lookup (.name k) = some y

theorem deepcopyMethodAliasing_refuted : ¬DeepcopyMethodAliasing := by
  intro H
  have hd : deepcopy 10 methodAliasHeap 1 = .ok (methodAliasCopy, 4) := by
    simp [deepcopy, deepAttrs, methodAliasHeap, methodAliasCopy, Heap.get, Heap.alloc, Heap.remember, Heap.set,
      setAttrOf, List.lookup, deepKey, storeItem]
  obtain ⟨s', attrs', h1, h2, h3⟩ := H 10 methodAliasHeap methodAliasCopy 1 0 0 4 [(.name "m", 1)] "m" rfl rfl rfl rfl hd
  have e1 : methodAliasCopy.get 4 = .method 0 2 := rfl
  rw [e1] at h1
  cases h1
  have e2 : methodAliasCopy.get 2 = .inst [(.name "m", 3)] := rfl
  rw [e2] at h2
  cases h2
  exact absurd h3 (by decide)

/-- The paths of `deepcopy` past the dispatch table, Lib/copy.py:128-162, for an object not in `memo`. A class with
another metaclass is its own copy (`issubclass(cls, type)`, :132-133) and is not memoized (:159). A succeeding
`__deepcopy__` gives a new object, recorded in `memo` (:135-137, :159-160). A reduce string means `x` itself, with no
memo entry (:153-154); a raising reductor propagates; with no reductor at all, `copy.Error` (:151-152). A memo entry
answers before any of them (:125-126). An atom (`int` or `None`), a `str` and a class whose type is `type` are returned
as they are before `memo` is read at all (:118-119 before :125), whatever `memo` holds for them. -/
def DeepcopyPaths : Prop :=
  ∀ (fuel : Nat) (h : Heap) (x y m : Nat) (c : Option (Option PyExc)) (r : Option RvSpec) (e : PyExc) (n : Int)
    (t : String),
    (h.get x = .atom n → deepcopy (fuel + 1) h x = .ok (h, x)) ∧
    (h.get x = .str t → deepcopy (fuel + 1) h x = .ok (h, x)) ∧
    (h.get x = .cls m → deepcopy (fuel + 1) h x = .ok (h, x)) ∧
    (h.get x = .metaCls m → h.memo.lookup x = none → deepcopy (fuel + 1) h x = .ok (h, x)) ∧
    (h.get x = .metaCls m → h.memo.lookup x = some y → deepcopy (fuel + 1) h x = .ok (h, y)) ∧
    (h.get x = .hooked c (some none) r → h.memo.lookup x = none →
      deepcopy (fuel + 1) h x = .ok ((h.alloc (.atom 1)).1.remember x h.cells.length, h.cells.length)) ∧
    (h.get x = .hooked c none (some .str) → h.memo.lookup x = none → deepcopy (fuel + 1) h x = .ok (h, x)) ∧
    (h.get x = .hooked c none (some (.raises e)) → h.memo.lookup x = none → deepcopy (fuel + 1) h x = .error e) ∧
    (h.get x = .hooked c none none → h.memo.lookup x = none → deepcopy (fuel + 1) h x = .error (uncopyable true))

theorem deepcopyPaths_proven : DeepcopyPaths := by
  intro fuel h x y m c r e n t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc; rw [deepcopy]; simp [hc]
  · intro hc; rw [deepcopy]; simp [hc]
  · intro hc; rw [deepcopy]; simp [hc]
  · intro hc hm; rw [deepcopy]; simp [hc, hm]
  · intro hc hm; rw [deepcopy]; simp [hc, hm]
  · intro hc hm; rw [deepcopy]; simp [hc, hm, Heap.alloc]
  · intro hc hm; rw [deepcopy]; simp [hc, hm]
  · intro hc hm; rw [deepcopy]; simp [hc, hm]
  · intro hc hm; rw [deepcopy]; simp [hc, hm]
