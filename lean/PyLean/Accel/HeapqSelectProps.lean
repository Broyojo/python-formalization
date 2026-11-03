import PyLean.Accel.HeapqSelectSimK

/-!
Registry properties of `nsmallest` / `nlargest` (Lib/heapq.py:477-593) over the fallible model
of `HeapqSelect.lean`.
-/

namespace PyLean.Accel.Heapq

open PyLean

variable {α : Type} [DecidableEq α] [Inhabited α]

/-- The key, as a function (`key=None` is the identity). -/
def kOf (κ : Option (α → α)) (a : α) : α :=
  match κ with
  | none => a
  | some f => f a

/-! ### `n == 1`: `min()` / `max()` -/

theorem minMaxLoop_sim (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (hr : Accel.StrictWeak r)
    (κ : Option (α → α)) (large : Bool) :
    ∀ (fuel p : Nat) (b : Int), 1 ≤ b → p ≤ xs.length → xs.length - p < fuel →
      ((minMaxLoop (hEnv xs r lr) large (κ.map pureKey) .it fuel
          (some (dcd xs b, kOf κ (dcd xs b)))).run p).1 =
        .ok (some (dcd xs (((codes xs).drop p).foldl (fun best y =>
          if decide ((sS3 xs r (kOf κ) large).kf y < (sS3 xs r (kOf κ) large).kf best) then y else best) b))) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; omega
  | succ fuel ih =>
    intro p b hb hp hf
    simp only [minMaxLoop]
    rw [Eff.run_bind_ok (nextOpt_hEnv xs r lr p)]
    by_cases hlt : p < xs.length
    · rw [List.getElem?_eq_getElem hlt, if_pos hlt, codes_drop xs p hlt]
      simp only [List.foldl_cons]
      have happ : applyK (κ.map pureKey) xs[p] = pure (kOf κ xs[p]) := by
        cases κ <;> rfl
      rw [happ, Eff.pure_bind]
      have hk1 : kOf κ xs[p] = keyOf xs (kOf κ) ((p + 1 : Nat) : Int) := (keyOf_succ xs (kOf κ) p hlt).symm
      have hk2 : kOf κ (dcd xs b) = keyOf xs (kOf κ) b := (keyOf_pos xs (kOf κ) b hb).symm
      have hc : cmpBest (hEnv xs r lr) large (kOf κ xs[p]) (kOf κ (dcd xs b)) =
          pure (decide ((sS3 xs r (kOf κ) large).kf ((p + 1 : Nat) : Int) < (sS3 xs r (kOf κ) large).kf b)) := by
        rw [hk1, hk2]
        cases large
        · show pure (r _ _) = _
          rw [rkK_spec hr xs (kOf κ) _ _]; rfl
        · show pure (r _ _) = _
          rw [rkK_spec hr xs (kOf κ) _ _]
          simp only [sS3, if_true]
          congr 1; simp only [decide_eq_decide]; omega
      rw [hc, Eff.pure_bind]
      by_cases hk : (sS3 xs r (kOf κ) large).kf ((p + 1 : Nat) : Int) < (sS3 xs r (kOf κ) large).kf b
      · rw [if_pos (by simpa using hk), if_pos (by simpa using hk), ← dcd_succ xs p hlt]
        exact ih (p + 1) _ (by omega) (by omega) (by omega)
      · rw [if_neg (by simpa using hk), if_neg (by simpa using hk)]
        exact ih (p + 1) b hb (by omega) (by omega)
    · rw [List.getElem?_eq_none (by omega), if_neg hlt, codes_drop_nil xs p (by omega)]
      rfl

theorem minMax_honest (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (hr : Accel.StrictWeak r)
    (κ : Option (α → α)) (large : Bool) (fuel : Nat) (hf : xs.length < fuel) (w : Nat) :
    ((do
        let it ← (hEnv xs r lr).iter .src
        let r ← minMax (hEnv xs r lr) large (κ.map pureKey) fuel it
        pure r.toList : Eff Nat PyExc (List α)).run w).1 =
      .ok ((xs.mergeSort (fun a b => if large then !r (kOf κ a) (kOf κ b) else !r (kOf κ b) (kOf κ a))).take 1) := by
  rw [Eff.run_bind_ok (iter_src_hEnv xs r lr w)]
  simp only [minMax, Eff.bind_assoc]
  rw [Eff.run_bind_ok (iter_it_hEnv xs r lr 0)]
  rw [← stableSort_dcdK xs hr (kOf κ) large]
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp only [minMaxLoop, Eff.bind_assoc]
    rw [Eff.run_bind_ok (nextOpt_hEnv xs r lr 0)]
    cases xs with
    | nil => simp [codes, Accel.stableSort, Eff.run_bind]
    | cons x xs' =>
      rw [show (x :: xs')[0]? = some x from rfl, if_pos (by simp)]
      dsimp only
      have happ : applyK (κ.map pureKey) x = pure (kOf κ x) := by cases κ <;> rfl
      rw [happ, Eff.pure_bind]
      have hx : x = dcd (x :: xs') ((0 + 1 : Nat) : Int) := (dcd_succ (x :: xs') 0 (by simp)).symm
      rw [show (x, kOf κ x) = (dcd (x :: xs') ((0 + 1 : Nat) : Int), kOf κ (dcd (x :: xs') ((0 + 1 : Nat) : Int)))
        by rw [← hx]]
      rcases hrun : (minMaxLoop (hEnv (x :: xs') r lr) large (κ.map pureKey) HO.it fuel
          (some (dcd (x :: xs') ((0 + 1 : Nat) : Int), kOf κ (dcd (x :: xs') ((0 + 1 : Nat) : Int))))).run 1
        with ⟨res, w'⟩
      have hm := minMaxLoop_sim (x :: xs') r lr hr κ large fuel 1 ((0 + 1 : Nat) : Int) (by omega) (by simp)
        (by simp at hf ⊢; omega)
      rw [hrun] at hm
      simp only at hm
      subst hm
      rw [Eff.run_bind_ok hrun]
      -- the spec's `min`: the first item of the stable sort
      have hcodes : codes (x :: xs') = ((0 + 1 : Nat) : Int) :: (codes (x :: xs')).drop 1 := by
        rw [← codes_drop (x :: xs') 0 (by simp)]; rfl
      have hmin := Accel.pyMinMax_eq (fun a b => decide (a < b)) (some (sS3 (x :: xs') r (kOf κ) large).kf)
        (sS3 (x :: xs') r (kOf κ) large).kf (fun a b => rfl) (codes (x :: xs'))
      rw [hcodes] at hmin ⊢
      simp only [Accel.pyMinMax, Accel.applyKey] at hmin
      show (Except.ok [dcd (x :: xs') _] : Except PyExc (List α)) = _
      rw [← List.map_take, ← Accel.take_one_head, ← hmin]
      rfl

/-! ### `n >= len(iterable)`: `sorted()` -/

theorem mapM_pureKey (κ : α → α) : ∀ (l : List α) (w : Nat), (effMap (pureKey κ) l).run w = (.ok (l.map κ), w)
  | [], _ => rfl
  | x :: l, w => by
    simp only [effMap]
    rw [Eff.run_bind_ok (show (pureKey κ x).run w = (.ok (κ x), w) from rfl),
      Eff.run_bind_ok (mapM_pureKey κ l w)]
    rfl

theorem mem_zip_map {f : α → α} : ∀ (l : List α) (p : α × α), p ∈ (l.map f).zip l → p.1 = f p.2
  | [], _, h => by simp at h
  | x :: l, p, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_zip_map l p h

theorem sorted_honest (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (hr : Accel.StrictWeak r)
    (So : Sorter Nat) (hSo : SortOk So) (κ : Option (α → α)) (large : Bool) (w : Nat) :
    ((pySortedBy (hEnv xs r lr) So (κ.map pureKey) large .src).run w).1 =
      .ok (xs.mergeSort (fun a b => if large then !r (kOf κ a) (kOf κ b) else !r (kOf κ b) (kOf κ a))) := by
  cases κ with
  | none =>
    show ((So.sort (fun a b => pure (r a b)) large xs).run w).1 = _
    rw [hSo _ r large xs w hr]
    cases large <;> rfl
  | some f =>
    show ((do
        let ks ← effMap (pureKey f) xs
        let s ← So.sort (fun a b => (pure (r a.1 b.1) : Eff Nat PyExc Bool)) large (ks.zip xs)
        pure (s.map (·.2)) : Eff Nat PyExc (List α)).run w).1 = _
    rw [Eff.run_bind_ok (mapM_pureKey f xs w),
      Eff.run_bind_ok (hSo (α × α) (fun a b => r a.1 b.1) large ((xs.map f).zip xs) w
        (StrictWeak.pullback hr Prod.fst))]
    show Except.ok (List.map (·.2) (if large then ((xs.map f).zip xs).mergeSort (fun a b => !r a.1 b.1)
      else ((xs.map f).zip xs).mergeSort (fun a b => !r b.1 a.1))) = _
    have hsnd : ((xs.map f).zip xs).map Prod.snd = xs := by
      rw [List.map_snd_zip]; simp
    congr 1
    cases large
    · try simp only [Bool.false_eq_true, ↓reduceIte]
      rw [List.map_mergeSort (s := fun a b => !r (f b) (f a)) (fun a ha b hb => by
        rw [mem_zip_map xs a ha, mem_zip_map xs b hb]), hsnd]
      rfl
    · try simp only [↓reduceIte]
      rw [List.map_mergeSort (s := fun a b => !r (f a) (f b)) (fun a ha b hb => by
        rw [mem_zip_map xs a ha, mem_zip_map xs b hb]), hsnd]
      rfl

/-! ### Registry properties -/

/-- `len(iterable)` reports the true count, or raises an exception the source catches (a
`TypeError` or `AttributeError`). -/
def LenTrue (xs : List α) (lenRes : Except PyExc Nat) : Prop :=
  lenRes = .ok xs.length ∨
    ∃ e, lenRes = .error e ∧ (isA builtinHier e "TypeError" || isA builtinHier e "AttributeError") = true

/-- **`nsmallest` / `nlargest` are the sorted prefix.** For every element type, every `<` that
is a strict weak order (with `==` its equivalence, and `>` its reverse), every key (`None` or
a pure function), every `n >= 0`, both heap implementations (`impl`: the C heap functions or
the Python ones), any `list.sort` that is a correct stable sort, and any iterable that yields
`xs` and whose `len()` is the count or is not there:

`nsmallest(n, iterable, key) == sorted(iterable, key=key)[:n]` and
`nlargest(n, iterable, key) == sorted(iterable, key=key, reverse=True)[:n]`,
ties included, through all three paths (`n == 1` with `min()`/`max()`, `n >= len` with
`sorted()`, and the heap with its `(elem, order)` / `(key, order, elem)` tuples).

Source: the docstrings, Lib/heapq.py:477-481, :537-541 ("Equivalent to: ..."), and
Doc/library/heapq.rst. Negative `n` is excluded (python/cpython#57483). `==` inconsistent with
`<` is out of scope: the hypotheses are the language reference's consistency rules for a total
ordering (Doc/reference/expressions.rst:2201-2237: `x < y` and `y > x` agree, and `x < y` is
`not x >= y`, so `==` holds exactly when neither is `<`); python/cpython#158718 asked about
breaking them. -/
def NSelectIsSortedPrefix : Prop :=
  ∀ (α : Type) [DecidableEq α] [Inhabited α] (xs : List α) (r : α → α → Bool) (κ : Option (α → α))
    (n : Int) (impl large : Bool) (So : Sorter Nat) (lenRes : Except PyExc Nat) (fuel w0 : Nat),
    Accel.StrictWeak r → SortOk So → 0 ≤ n → xs.length < fuel → LenTrue xs lenRes →
    ((nSelect (hEnv xs r lenRes) So impl large fuel n .src (κ.map pureKey)).run w0).1 =
      .ok ((xs.mergeSort (fun a b => if large then !r (kOf κ a) (kOf κ b) else !r (kOf κ b) (kOf κ a))).take
        n.toNat)

theorem selHeap_honest (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (hr : Accel.StrictWeak r)
    (So : Sorter Nat) (hSo : SortOk So) (impl large : Bool) (fuel : Nat) (n : Int) (hn : 0 ≤ n)
    (hf : xs.length < fuel) (κ : Option (α → α)) (w : Nat) :
    ((selHeap (hEnv xs r lr) So impl large fuel n .src (κ.map pureKey)).run w).1 =
      .ok ((xs.mergeSort (fun a b => if large then !r (kOf κ a) (kOf κ b) else !r (kOf κ b) (kOf κ a))).take
        n.toNat) := by
  cases κ with
  | none => exact selHeap_none xs r lr hr So hSo impl large fuel n hn hf w
  | some f => exact selHeap_key xs r f lr hr So hSo impl large fuel n hn hf w

theorem nSelectIsSortedPrefix_proven : NSelectIsSortedPrefix := by
  intro α _ _ xs r κ n impl large So lenRes fuel w0 hr hSo hn hf hlen
  simp only [nSelect]
  by_cases h1 : n = 1
  · rw [if_pos h1, h1]
    exact minMax_honest xs r lenRes hr κ large fuel hf w0
  · rw [if_neg h1]
    simp only [Eff.run_bind, Eff.attempt]
    rcases hlen with hl | ⟨e, hl, hc⟩
    · subst hl
      rw [show ((hEnv xs r (.ok xs.length)).len .src).run w0 = (.ok xs.length, w0) from rfl]
      simp only
      by_cases h2 : n ≥ (xs.length : Int)
      · rw [if_pos h2, sorted_honest xs r _ hr So hSo κ large w0]
        rw [List.take_of_length_le (by simp; omega)]
      · rw [if_neg h2]
        exact selHeap_honest xs r _ hr So hSo impl large fuel n hn hf κ w0
    · subst hl
      rw [show ((hEnv xs r (.error e)).len .src).run w0 = (.error e, w0) from rfl]
      simp only
      rw [if_pos (show (isA (hEnv xs r (.error e)).hier e "TypeError" ||
        isA (hEnv xs r (.error e)).hier e "AttributeError") = true from hc)]
      exact selHeap_honest xs r _ hr So hSo impl large fuel n hn hf κ w0

/-- A sorter that satisfies `SortOk`: a witness for the refutations. -/
def pureSorter (W : Type) : Sorter W where
  sort cmp rev l := ⟨fun w =>
    let c := fun a b => match ((cmp a b).run w).1 with
      | .ok c => c
      | .error _ => false
    (.ok (if rev then l.mergeSort (fun a b => !c a b) else l.mergeSort (fun a b => !c b a)), w)⟩

theorem pureSorter_ok (W : Type) : SortOk (pureSorter W) := by
  intro β rr rev l w _
  rfl

/-- The same equivalence for every `len()` result. True on 3.14.7, which sliced
`sorted(...)[:n]`; 3.15 returns `sorted(iterable)` whole when `n >= len(iterable)`. -/
def NSelectAnyLen : Prop :=
  ∀ (α : Type) [DecidableEq α] [Inhabited α] (xs : List α) (r : α → α → Bool) (κ : Option (α → α))
    (n : Int) (impl large : Bool) (So : Sorter Nat) (size fuel w0 : Nat),
    Accel.StrictWeak r → SortOk So → 0 ≤ n → xs.length < fuel →
    ((nSelect (hEnv xs r (.ok size)) So impl large fuel n .src (κ.map pureKey)).run w0).1 =
      .ok ((xs.mergeSort (fun a b => if large then !r (kOf κ a) (kOf κ b) else !r (kOf κ b) (kOf κ a))).take
        n.toNat)

/-- `nsmallest(2, it)` for an `it` that yields `3, 1, 2` and reports `len(it) == 0` returns
all three items. -/
theorem nSelectAnyLen_refuted : ¬ NSelectAnyLen := by
  intro h
  have := h Int [3, 1, 2] intLtB none 2 false false (pureSorter Nat) 0 10 0 strictWeak_intLtB
    (pureSorter_ok Nat) (by decide) (by decide)
  have hres : ((nSelect (hEnv [3, 1, 2] intLtB (.ok 0)) (pureSorter Nat) false false 10 2 .src
      ((none : Option (Int → Int)).map pureKey)).run 0).1 =
      .ok ([3, 1, 2].mergeSort (fun a b => !intLtB b a)) := rfl
  rw [hres] at this
  have hl := congrArg (fun r => match r with | .ok l => l.length | .error _ => 0) this
  simp only [List.length_mergeSort, List.length_take] at hl
  revert hl
  decide

end PyLean.Accel.Heapq
