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
    (hd : deepPairs fuel (h.fresh (.dict []) x) items = .ok (h3, ys)) :
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

theorem deepcopy_atom (fuel : Nat) (h : Heap) (x : Nat) (n : Int) (hc : h.get x = .atom n) :
    deepcopy (fuel + 1) h x = .ok (h, x) := by
  simp [deepcopy, hc]

theorem deepcopy_memo (fuel : Nat) (h : Heap) (x y : Nat) (hl : h.memo.lookup x = some y)
    (ha : ∀ m, h.get x ≠ .atom m) (hc : ∀ m, h.get x ≠ .cls m) : deepcopy (fuel + 1) h x = .ok (h, y) :=
  (deepcopyMemo_proven fuel h x y 0).2.1 hl ha hc

theorem deepList_nil (fuel : Nat) (h : Heap) : deepList (fuel + 1) h [] = .ok (h, []) := by simp [deepList]

theorem deepList_cons (fuel : Nat) (h h1 h2 : Heap) (a y : Nat) (as ys : List Nat)
    (e1 : deepcopy fuel h a = .ok (h1, y)) (e2 : deepList fuel h1 as = .ok (h2, ys)) :
    deepList (fuel + 1) h (a :: as) = .ok (h2, y :: ys) := by
  simp [deepList, e1, e2]

theorem deepPairs_atoms (h : Heap) : ∀ (fuel : Nat) (l : List (Nat × Nat)),
    (∀ p ∈ l, (∃ n, h.get p.1 = .atom n) ∧ ∃ n, h.get p.2 = .atom n) → l.length ≤ fuel →
    deepPairs (fuel + 1) h l = .ok (h, l)
  | _, [], _, _ => by simp [deepPairs]
  | 0, _ :: _, _, hl => by simp at hl
  | fuel + 1, (k, v) :: r, ha, hl => by
    obtain ⟨⟨n, hn⟩, ⟨m, hm⟩⟩ := ha (k, v) (by simp)
    have h1 : deepcopy (fuel + 1) h v = .ok (h, v) := deepcopy_atom _ _ _ _ hm
    have h2 : deepcopy (fuel + 1) h k = .ok (h, k) := deepcopy_atom _ _ _ _ hn
    have h3 := deepPairs_atoms h fuel r (fun p hp => ha p (List.mem_cons_of_mem _ hp)) (by simpa using hl)
    simp [deepPairs, h1, h2, h3]

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

/-- `_deepcopy_dict` on a dict of atoms: a new dict, recorded in `memo`, with the same items. -/
def DeepcopyDictExact : Prop :=
  ∀ (fuel : Nat) (h : Heap) (x : Nat) (items : List (Nat × Nat)), h.get x = .dict items → h.memo.lookup x = none →
    (∀ p ∈ items, ((∃ n, h.get p.1 = .atom n) ∧ p.1 < h.cells.length) ∧
      ((∃ n, h.get p.2 = .atom n) ∧ p.2 < h.cells.length)) → items.length ≤ fuel →
    ∃ h', deepcopy (fuel + 2) h x = .ok (h', h.cells.length) ∧ h'.get h.cells.length = .dict items ∧
      h'.memo.lookup x = some h.cells.length

theorem deepcopyDictExact_proven : DeepcopyDictExact := by
  intro fuel h x items hc hm ha hl
  have ha2 : ∀ p ∈ items, (∃ n, (h.fresh (.dict []) x).get p.1 = .atom n) ∧
      ∃ n, (h.fresh (.dict []) x).get p.2 = .atom n := by
    intro p hi
    obtain ⟨⟨⟨n, hn⟩, h1⟩, ⟨⟨m, hm⟩, h3⟩⟩ := ha p hi
    exact ⟨⟨n, by rw [fresh_get_old _ _ _ _ h1]; exact hn⟩, ⟨m, by rw [fresh_get_old _ _ _ _ h3]; exact hm⟩⟩
  have hd := deepPairs_atoms _ fuel items ha2 hl
  refine ⟨_, deepcopy_dict (fuel + 1) h x items hc hm _ _ hd, ?_, ?_⟩
  · apply get_set_same
    rw [fresh_len]; omega
  · rw [set_memo, fresh_lookup_self]

/-- The order inside the copy of a dict, and the reverse order in `_reconstruct`. `y[deepcopy(key, memo)] =
deepcopy(value, memo)` evaluates its right side first, so at Lib/copy.py:200 a failing value hides a failing key. The
explicit lines of `_reconstruct`, :279-281, copy the key first. Inside `deepList`, a failing item stops the list. -/
def DeepCopyOrder : Prop :=
  ∀ (fuel : Nat) (h h1 : Heap) (k v y a v' : Nat) (r : List (Nat × Nat)) (as : List Nat) (e : PyExc),
    (deepcopy fuel h v = .error e → deepPairs (fuel + 1) h ((k, v) :: r) = .error e) ∧
    (deepcopy fuel h v = .ok (h1, v') → deepcopy fuel h1 k = .error e →
      deepPairs (fuel + 1) h ((k, v) :: r) = .error e) ∧
    (deepcopy fuel h k = .error e → deepSetItems (fuel + 1) h y ((k, v) :: r) = .error e) ∧
    (deepcopy fuel h a = .error e → deepList (fuel + 1) h (a :: as) = .error e) ∧
    (deepcopy fuel h a = .error e → deepAppend (fuel + 1) h y (a :: as) = .error e)

theorem deepCopyOrder_proven : DeepCopyOrder := by
  intro fuel h h1 k v y a v' r as e
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
    deepcopy_memo _ _ _ _ hl3 (by intro m hm; rw [hg3] at hm; cases hm) (by intro m hm; rw [hg3] at hm; cases hm)
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
the second `memo` read at Lib/copy.py:184: for `t = ([t],)`, the inner call builds the one copy, the outer call finds
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
      deepcopy_memo _ _ _ _ hl2a (by intro m hm; rw [hg2a] at hm; cases hm) (by intro m hm; rw [hg2a] at hm; cases hm)
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

theorem deepcopy_hooked (fuel : Nat) (h h1 h4 h5 h6 h7 : Heap) (x n : Nat) (c : Option (Option PyExc))
    (k : BuildKind) (args a' : List Nat) (s st : Option Nat) (li : Option (List Nat))
    (di : Option (List (Nat × Nat))) (ss : Option (Option PyExc))
    (hc : h.get x = .hooked c none (some (.tuple n none k args s li di ss))) (hm : h.memo.lookup x = none)
    (hn1 : ¬ n < 2) (hn2 : ¬ n > 5) (e1 : deepList fuel h args = .ok (h1, a'))
    (e2 : deepOpt fuel (h1.fresh (freshOf k a') x) s = .ok (h4, st))
    (e3 : reconRest h4 h1.cells.length st none none ss = .ok h5)
    (e4 : deepAppend fuel h5 h1.cells.length (li.getD []) = .ok h6)
    (e5 : deepSetItems fuel h6 h1.cells.length (di.getD []) = .ok h7) :
    deepcopy (fuel + 1) h x = .ok (h7, h1.cells.length) := by
  rw [deepcopy]
  simp only [hc, hm]
  simp only [Heap.fresh] at e2
  simp [Heap.alloc] at e2
  simp [reconArity, hn1, hn2, e1, Heap.alloc, e2, e3, e4, e5]

/-- The steps of `_reconstruct` with `deep` true, in the source's order. The argument count is checked by the call,
before anything is copied. The arguments are copied before `func` runs, so a failing copy hides a failing
constructor, and a failing constructor comes after the copies. -/
def ReconstructDeepSteps : Prop :=
  ∀ (fuel : Nat) (h h1 : Heap) (x n : Nat) (c : Option (Option PyExc)) (fail : Option PyExc) (k : BuildKind)
    (args a' : List Nat) (s : Option Nat) (li : Option (List Nat)) (di : Option (List (Nat × Nat)))
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
      h'.get h.cells.length = .inst [("__state__", h.cells.length + 1)] ∧
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
    deepcopy_memo _ _ _ _ hl3x (by intro m hm; rw [hg3x] at hm; cases hm) (by intro m hm; rw [hg3x] at hm; cases hm)
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
  have eo : deepOpt (fuel + 5) (h.fresh (freshOf .inst []) x) (some st) = .ok (h4, some (h.cells.length + 1)) := by
    rw [hf, hh2]
    simp [deepOpt, cl]
  generalize hh5 : h4.set h.cells.length (.inst [("__state__", h.cells.length + 1)]) = h5
  have er : reconRest h4 h.cells.length (some (h.cells.length + 1)) none none (some none) = .ok h5 := by
    rw [← hh5]
    simp [reconRest, setstateOf, setAttrOf, hg4y]
  have ea : deepAppend (fuel + 5) h5 h.cells.length [] = .ok h5 := by simp [deepAppend]
  have es : deepSetItems (fuel + 5) h5 h.cells.length [] = .ok h5 := by simp [deepSetItems]
  have hd := deepcopy_hooked (fuel + 5) h h h4 h5 h5 h5 x n c .inst [] [] (some st) (some (h.cells.length + 1))
    none none (some none) hc hmx (by omega) (by omega) (deepList_nil _ _) eo er ea es
  refine ⟨_, hd, ?_, ?_⟩
  · rw [← hh5]
    apply get_set_same
    omega
  · rw [← hh5, get_set_other _ _ _ _ (by omega)]
    exact hg4s

theorem fold_appendTo (y : Nat) : ∀ (l : List Nat) (h : Heap) (old : List Nat), h.get y = .list old →
    y < h.cells.length →
    ∃ h', l.foldl (fun acc i =>
        match acc with
        | .error e => .error e
        | .ok h => appendTo h y i) (Except.ok h : Py Heap) = .ok h' ∧
      h'.get y = .list (old ++ l) ∧ ∀ z, z ≠ y → h'.get z = h.get z
  | [], h, old, hg, _ => ⟨h, rfl, by simpa using hg, fun _ _ => rfl⟩
  | i :: l, h, old, hg, hy => by
    have h1 : appendTo h y i = .ok (h.set y (.list (old ++ [i]))) := by simp [appendTo, hg]
    obtain ⟨h', e, g, o⟩ := fold_appendTo y l (h.set y (.list (old ++ [i]))) (old ++ [i])
      (get_set_same _ _ _ hy) (by rw [set_len]; exact hy)
    refine ⟨h', by simp only [List.foldl, h1]; exact e, by simpa using g, ?_⟩
    intro z hz
    rw [o z hz, get_set_other _ _ _ _ hz]

theorem fold_setItemOf (y : Nat) : ∀ (l : List (Nat × Nat)) (h : Heap) (old : List (Nat × Nat)),
    h.get y = .dict old → y < h.cells.length →
    ∃ h', l.foldl (fun acc p =>
        match acc with
        | .error e => .error e
        | .ok h => setItemOf h y p.1 p.2) (Except.ok h : Py Heap) = .ok h' ∧
      h'.get y = .dict (old ++ l) ∧ ∀ z, z ≠ y → h'.get z = h.get z
  | [], h, old, hg, _ => ⟨h, rfl, by simpa using hg, fun _ _ => rfl⟩
  | p :: l, h, old, hg, hy => by
    have h1 : setItemOf h y p.1 p.2 = .ok (h.set y (.dict (old ++ [p]))) := by simp [setItemOf, hg]
    obtain ⟨h', e, g, o⟩ := fold_setItemOf y l (h.set y (.dict (old ++ [p]))) (old ++ [p])
      (get_set_same _ _ _ hy) (by rw [set_len]; exact hy)
    refine ⟨h', by simp only [List.foldl, h1]; exact e, by simpa using g, ?_⟩
    intro z hz
    rw [o z hz, get_set_other _ _ _ _ hz]

/-- The tail of `_reconstruct`, on the object `y`: `listiter` appends every item, in order, `dictiter` stores every
pair, in order, and nothing else changes; `__setstate__` gets the state; a `__setstate__` that raises stops it before
either iterator is read; and a `dictiter` on an object without `__setitem__` is a `TypeError`. -/
def ReconRestItems : Prop :=
  ∀ (h : Heap) (y st : Nat) (old l : List Nat) (oldD d : List (Nat × Nat)) (a : List (String × Nat)) (e : PyExc)
    (li : Option (List Nat)) (di : Option (List (Nat × Nat))) (p : Nat × Nat),
    y < h.cells.length →
    (h.get y = .list old → ∃ h', reconRest h y none (some l) none none = .ok h' ∧ h'.get y = .list (old ++ l) ∧
      ∀ z, z ≠ y → h'.get z = h.get z) ∧
    (h.get y = .dict oldD → ∃ h', reconRest h y none none (some d) none = .ok h' ∧ h'.get y = .dict (oldD ++ d) ∧
      ∀ z, z ≠ y → h'.get z = h.get z) ∧
    (h.get y = .inst a → reconRest h y (some st) none none (some none) =
      .ok (h.set y (.inst (a.filter (fun q => q.1 ≠ "__state__") ++ [("__state__", st)])))) ∧
    reconRest h y (some st) li di (some (some e)) = .error e ∧
    ((∀ m, h.get y ≠ .dict m) → (reconRest h y none none (some (p :: d)) none).raises "TypeError")

theorem reconRestItems_proven : ReconRestItems := by
  intro h y st old l oldD d a e li di p hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hg
    obtain ⟨h', e1, g, o⟩ := fold_appendTo y l h old hg hy
    refine ⟨h', ?_, g, o⟩
    simp only [reconRest]
    split
    · next e0 he => exact absurd (he.symm.trans e1) (by simp)
    · next h4 he => exact he.symm.trans e1
  · intro hg
    obtain ⟨h', e1, g, o⟩ := fold_setItemOf y d h oldD hg hy
    exact ⟨h', by simp only [reconRest]; exact e1, g, o⟩
  · intro hg
    simp [reconRest, setstateOf, setAttrOf, hg]
  · simp [reconRest, setstateOf]
  · intro hg
    have h1 : setItemOf h y p.1 p.2 = .error (.typeError "~object does not support item assignment") := by
      unfold setItemOf
      cases hv : h.get y with
      | dict m => exact absurd hv (hg m)
      | _ => rfl
    have h2 : ∀ (t : List (Nat × Nat)), t.foldl (fun acc q =>
        match acc with
        | .error e => .error e
        | .ok h => setItemOf h y q.1 q.2) (Except.error (.typeError "~object does not support item assignment") : Py Heap) =
        .error (.typeError "~object does not support item assignment") := by
      intro t
      induction t with
      | nil => rfl
      | cons _ _ ih => simpa [List.foldl] using ih
    refine ⟨.typeError "~object does not support item assignment", ?_, rfl⟩
    simp only [reconRest, List.foldl, h1]
    exact h2 d
