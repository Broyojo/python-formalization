import PyLean.Accel.SelectProps

/-!
`heapq.merge` against `sorted(itertools.chain(*iterables), key=key, reverse=reverse)`.

The state of the merge is the list `rs` of the remaining items of every input.
The heap holds one entry per non-empty input (`mEntries`). The emitted item is
the root, which is the first item of the stable sort of `rs.flatten`: it has
the smallest key among the heads (hence among all remaining items, the inputs
being sorted), and every input before it has a strictly larger head key.
-/

namespace PyLean.Accel

open PyLean

/-- The heap entry of input `i` with remaining items `r` (Lib/heapq.py:366, :390). -/
def entOf (f : Int → Int) (dir : Int) (i : Nat) : List Int → Option MEntry
  | [] => none
  | v :: rest => some { kv := f v, order := i * dir, value := v, rest := rest }

/-- The mEntries of the non-empty inputs, numbered from `k`. -/
def mEntries (f : Int → Int) (dir : Int) (rs : List (List Int)) (k : Nat) : List MEntry :=
  (rs.zipIdx k).filterMap (fun p => entOf f dir p.2 p.1)

theorem mEntries_nil (f : Int → Int) (dir : Int) (k : Nat) : mEntries f dir [] k = [] := rfl

theorem mEntries_cons (f : Int → Int) (dir : Int) (r : List Int) (rs : List (List Int)) (k : Nat) :
    mEntries f dir (r :: rs) k = (entOf f dir k r).toList ++ mEntries f dir rs (k + 1) := by
  simp only [mEntries, List.zipIdx_cons, List.filterMap_cons]
  cases entOf f dir k r <;> rfl

theorem mEntries_append (f : Int → Int) (dir : Int) :
    ∀ (A B : List (List Int)) (k : Nat), mEntries f dir (A ++ B) k = mEntries f dir A k ++ mEntries f dir B (k + A.length)
  | [], B, k => by simp [mEntries_nil]
  | r :: A, B, k => by
    rw [List.cons_append, mEntries_cons, mEntries_cons, mEntries_append f dir A B (k + 1)]
    simp only [List.append_assoc, List.length_cons]
    congr 3; omega

theorem mEntries_eq_nil (f : Int → Int) (dir : Int) :
    ∀ (rs : List (List Int)) (k : Nat), mEntries f dir rs k = [] → rs.flatten = []
  | [], _, _ => rfl
  | r :: rs, k, h => by
    rw [mEntries_cons] at h
    simp only [List.append_eq_nil_iff] at h
    cases r with
    | nil => simpa using mEntries_eq_nil f dir rs (k + 1) h.2
    | cons v rest => simp [entOf] at h

theorem mem_entries (f : Int → Int) (dir : Int) :
    ∀ (rs : List (List Int)) (k : Nat) (s : MEntry), s ∈ mEntries f dir rs k →
      ∃ i x t, i < rs.length ∧ rs[i]? = some (x :: t) ∧
        s = { kv := f x, order := ((k + i : Nat) : Int) * dir, value := x, rest := t }
  | [], _, _, h => by simp [mEntries_nil] at h
  | r :: rs, k, s, h => by
    rw [mEntries_cons] at h
    rcases List.mem_append.1 h with h | h
    · cases r with
      | nil => simp [entOf] at h
      | cons x t =>
        simp [entOf] at h
        exact ⟨0, x, t, by simp, by simp, by simp [h]⟩
    · obtain ⟨i, x, t, hi, hr, hs⟩ := mem_entries f dir rs (k + 1) s h
      exact ⟨i + 1, x, t, by simp; omega, by simpa using hr, by rw [hs]; congr 2; omega⟩

theorem entry_mem (f : Int → Int) (dir : Int) (rs : List (List Int)) (i : Nat) (x : Int) (t : List Int)
    (hr : rs[i]? = some (x :: t)) :
    ({ kv := f x, order := (i : Int) * dir, value := x, rest := t } : MEntry) ∈ mEntries f dir rs 0 := by
  have hi : i < rs.length := by
    rcases Nat.lt_or_ge i rs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hr; cases hr
  have hdec : rs = rs.take i ++ (x :: t) :: rs.drop (i + 1) := by
    have h1 : rs[i] = x :: t := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hr)
    conv => lhs; rw [← List.take_append_drop i rs]
    rw [List.drop_eq_getElem_cons hi, h1]
  rw [hdec, mEntries_append, mEntries_cons]
  simp only [List.length_take, Nat.zero_add, show min i rs.length = i by omega, entOf]
  simp

/-! ### The stable sort facts -/

theorem stableSort_extract (kf : Int → Int) (A B : List Int) (x : Int)
    (hA : ∀ y ∈ A, kf x < kf y) (hB : ∀ y ∈ B, kf x ≤ kf y) :
    stableSort kf (A ++ x :: B) = x :: stableSort kf (A ++ B) := by
  apply stableSort_eq
  have hs := stableSort_spec kf (A ++ B)
  refine ⟨List.pairwise_cons.2 ⟨?_, hs.1⟩, ?_⟩
  · intro y hy
    rw [(stableSort_perm kf _).mem_iff, List.mem_append] at hy
    rcases hy with hy | hy
    · exact Int.le_of_lt (hA y hy)
    · exact hB y hy
  · intro k
    rw [List.filter_cons, hs.2 k, List.filter_append, List.filter_append, List.filter_cons]
    by_cases hk : kf x = k
    · have hnil : A.filter (fun e => kf e == k) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy; have := hA y hy; simp; omega
      simp [hk, hnil]
    · simp [hk]

theorem stableSort_of_sorted (kf : Int → Int) (l : List Int) (h : l.Pairwise (fun a b => kf a ≤ kf b)) :
    stableSort kf l = l :=
  stableSort_eq kf l l ⟨h, fun _ => rfl⟩

/-! ### Entry comparisons -/

theorem strictWeak_entLt : StrictWeak entLt where
  irrefl a := strictWeak_lt2.irrefl _
  trans a b c h1 h2 := strictWeak_lt2.trans _ _ _ h1 h2
  negTrans a b c h := strictWeak_lt2.negTrans _ (b.kv, b.order) _ h

/-- The heap order of `merge`, its direction, and the ascending sort key it encodes. -/
def mLt (reverse : Bool) : MEntry → MEntry → Bool := if reverse then maxLt entLt else entLt
def mDir (reverse : Bool) : Int := if reverse then -1 else 1
def mKf (reverse : Bool) (f : Int → Int) (v : Int) : Int := if reverse then -f v else f v

theorem strictWeak_mLt (reverse : Bool) : StrictWeak (mLt reverse) := by
  cases reverse
  · exact strictWeak_entLt
  · exact strictWeak_entLt.maxLt

/-- `lt e_j e_i = false` for the mEntries of inputs `j ≠ i` means: input `j`'s head has a
larger key, or the same key and `j > i`. -/
theorem mLt_false (reverse : Bool) (f : Int → Int) (i j : Nat) (x y : Int) (t u : List Int)
    (h : mLt reverse { kv := f y, order := (j : Int) * mDir reverse, value := y, rest := u }
      { kv := f x, order := (i : Int) * mDir reverse, value := x, rest := t } = false) :
    mKf reverse f x < mKf reverse f y ∨ (mKf reverse f x = mKf reverse f y ∧ i ≤ j) := by
  cases reverse
  · simp [mLt, entLt, lt2, mDir, mKf] at h ⊢
    omega
  · simp [mLt, maxLt, entLt, lt2, mDir, mKf] at h ⊢
    omega

/-! ### The loop -/

theorem pyHeappop_fst {α : Type} [Inhabited α] (lt : α → α → Bool) (heap : List α) (v : α) (h' : List α)
    (h : pyHeappop lt heap = .ok (v, h')) : v = at! heap 0 := by
  simp only [pyHeappop] at h
  split at h
  · cases h
  · rename_i last hl
    split at h
    · rename_i hne
      cases h
      obtain ⟨d0, dt, hd⟩ := List.exists_cons_of_ne_nil hne
      have : heap = heap.dropLast ++ [last] := by
        rw [List.getLast?_eq_some_iff] at hl
        obtain ⟨ys, rfl⟩ := hl
        simp
      rw [hd]; conv => rhs; rw [this, hd]
      rfl
    · cases h
      rename_i hne
      simp only [Decidable.not_not] at hne
      rw [List.getLast?_eq_some_iff] at hl
      obtain ⟨ys, rfl⟩ := hl
      simp at hne; subst hne; rfl

theorem pyHeapreplace_fst {α : Type} [Inhabited α] (lt : α → α → Bool) (heap : List α) (item v : α)
    (h' : List α) (h : pyHeapreplace lt heap item = .ok (v, h')) : v = at! heap 0 := by
  simp only [pyHeapreplace] at h
  split at h
  · cases h
  · cases h; rfl

theorem mergeLoop_spec (reverse : Bool) (f : Int → Int) :
    ∀ (fuel : Nat) (rs : List (List Int)) (heap : List MEntry),
      (rs.map List.length).sum < fuel →
      (∀ r ∈ rs, r.Pairwise (fun u v => mKf reverse f u ≤ mKf reverse f v)) →
      heap.Perm (mEntries f (mDir reverse) rs 0) → IsHeap (mLt reverse) heap →
      mergeLoop (mLt reverse) f fuel heap = .ok (stableSort (mKf reverse f) rs.flatten) := by
  intro fuel
  induction fuel with
  | zero => intro rs heap h; omega
  | succ fuel ih =>
    intro rs heap hfuel hsorted hp hh
    have hlt := strictWeak_mLt reverse
    simp only [mergeLoop]
    split
    · rename_i hlen
      -- the root and its input
      have hne : heap ≠ [] := by intro h; subst h; simp at hlen
      have hs_mem : at! heap 0 ∈ heap := by
        obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne; simp [at!]
      obtain ⟨i, x, t, hi, hri, hs⟩ := mem_entries f _ rs 0 _ (hp.mem_iff.1 hs_mem)
      simp only [Nat.zero_add] at hs
      have hrs_i : rs[i] = x :: t := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hri)
      have hdec : rs = rs.take i ++ (x :: t) :: rs.drop (i + 1) := by
        conv => lhs; rw [← List.take_append_drop i rs]
        rw [List.drop_eq_getElem_cons hi, hrs_i]
      let rs' := rs.take i ++ t :: rs.drop (i + 1)
      have hEdec : mEntries f (mDir reverse) rs 0 =
          mEntries f (mDir reverse) (rs.take i) 0 ++ (at! heap 0) :: mEntries f (mDir reverse) (rs.drop (i + 1)) (i + 1) := by
        conv => lhs; rw [hdec]
        rw [mEntries_append, mEntries_cons]
        simp only [List.length_take, Nat.zero_add, show min i rs.length = i by omega, entOf, hs]
        simp
      have hEdec' : mEntries f (mDir reverse) rs' 0 =
          mEntries f (mDir reverse) (rs.take i) 0 ++ (entOf f (mDir reverse) i t).toList ++
            mEntries f (mDir reverse) (rs.drop (i + 1)) (i + 1) := by
        simp only [rs']
        rw [mEntries_append, mEntries_cons]
        simp only [List.length_take, Nat.zero_add, show min i rs.length = i by omega, List.append_assoc]
      -- minimality of the root
      have hmin := root_min_mem hlt heap hh
      have hheads : ∀ (j : Nat) (y : Int) (u : List Int), rs[j]? = some (y :: u) → j ≠ i →
          mKf reverse f x < mKf reverse f y ∨ (mKf reverse f x = mKf reverse f y ∧ i ≤ j) := by
        intro j y u hj hji
        have hm := hmin _ (hp.mem_iff.2 (entry_mem f _ rs j y u hj))
        rw [hs] at hm
        exact mLt_false reverse f i j x y t u hm
      -- sortedness of each input
      have hsorted_get : ∀ (j : Nat) (y : Int) (u : List Int), rs[j]? = some (y :: u) → ∀ z ∈ y :: u, mKf reverse f y ≤ mKf reverse f z := by
        intro j y u hj z hz
        have hmem : y :: u ∈ rs := List.mem_of_getElem? hj
        rcases List.mem_cons.1 hz with rfl | hz
        · exact Int.le_refl _
        · exact (List.pairwise_cons.1 (hsorted _ hmem)).1 z hz
      -- the extraction
      have hA : ∀ z ∈ (rs.take i).flatten, mKf reverse f x < mKf reverse f z := by
        intro z hz
        obtain ⟨r, hr, hzr⟩ := List.mem_flatten.1 hz
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hr
        simp only [List.length_take] at hj
        have hrj : rs[j]? = some (rs.take i)[j] := by
          rw [List.getElem_take]; exact List.getElem?_eq_getElem (by omega)
        cases hq : (rs.take i)[j] with
        | nil => rw [hq] at hzr; cases hzr
        | cons y u =>
          rw [hq] at hrj hzr
          have h1 := hheads j y u hrj (by omega)
          have h2 := hsorted_get j y u hrj z hzr
          omega
      have hB : ∀ z ∈ t ++ (rs.drop (i + 1)).flatten, mKf reverse f x ≤ mKf reverse f z := by
        intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · exact hsorted_get i x t hri z (by simp [hz])
        · obtain ⟨r, hr, hzr⟩ := List.mem_flatten.1 hz
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hr
          simp only [List.length_drop] at hj
          have hrj : rs[i + 1 + j]? = some (rs.drop (i + 1))[j] := by
            rw [List.getElem_drop]; exact List.getElem?_eq_getElem (by omega)
          cases hq : (rs.drop (i + 1))[j] with
          | nil => rw [hq] at hzr; cases hzr
          | cons y u =>
            rw [hq] at hrj hzr
            have h1 := hheads (i + 1 + j) y u hrj (by omega)
            have h2 := hsorted_get (i + 1 + j) y u hrj z hzr
            omega
      have hflat : rs.flatten = (rs.take i).flatten ++ x :: (t ++ (rs.drop (i + 1)).flatten) := by
        conv => lhs; rw [hdec]
        simp
      have hflat' : rs'.flatten = (rs.take i).flatten ++ (t ++ (rs.drop (i + 1)).flatten) := by
        simp [rs']
      have hextract : stableSort (mKf reverse f) rs.flatten = x :: stableSort (mKf reverse f) rs'.flatten := by
        rw [hflat, hflat', stableSort_extract _ _ _ x hA hB]
      -- the inputs after the step
      have hfuel' : (rs'.map List.length).sum < fuel := by
        have e1 : (rs.map List.length).sum = (rs'.map List.length).sum + 1 := by
          conv => lhs; rw [hdec]
          simp [rs']; omega
        omega
      have hsorted' : ∀ r ∈ rs', r.Pairwise (fun u v => mKf reverse f u ≤ mKf reverse f v) := by
        intro r hr
        simp only [rs', List.mem_append, List.mem_cons] at hr
        rcases hr with hr | rfl | hr
        · exact hsorted r (List.mem_of_mem_take hr)
        · exact (List.pairwise_cons.1 (hsorted _ (List.mem_of_getElem? hri))).2
        · exact hsorted r (List.mem_of_mem_drop hr)
      have hsv : (at! heap 0).value = x := by rw [hs]
      have hsr : (at! heap 0).rest = t := by rw [hs]
      rw [hextract, hsr]
      cases t with
      | nil =>
        simp only
        obtain ⟨v, h', hpop, hh', hperm, -⟩ := pyHeappop_correct hlt heap hh hne
        have hv := pyHeappop_fst _ _ _ _ hpop
        rw [hpop]
        simp only [bind, Except.bind, pure, Except.pure]
        have hp' : h'.Perm (mEntries f (mDir reverse) rs' 0) := by
          rw [hEdec']
          simp only [entOf, Option.toList, List.append_nil]
          have : (v :: h').Perm (v :: (mEntries f (mDir reverse) (rs.take i) 0 ++
              mEntries f (mDir reverse) (rs.drop (i + 1)) (i + 1))) := by
            refine hperm.trans (hp.trans ?_)
            rw [hEdec, hv]
            exact List.perm_middle
          exact (List.perm_cons _).1 this
        rw [ih rs' h' hfuel' hsorted' hp' hh', hsv]
      | cons v' t' =>
        simp only
        let s' : MEntry := { at! heap 0 with kv := f v', value := v', rest := t' }
        obtain ⟨v, h', hrep, hh', hperm, -⟩ := pyHeapreplace_correct hlt heap s' hh hne
        have hv := pyHeapreplace_fst _ _ _ _ _ hrep
        rw [hrep]
        simp only [bind, Except.bind, pure, Except.pure]
        have hs' : s' = { kv := f v', order := (i : Int) * mDir reverse, value := v', rest := t' } := by
          simp only [s', hs]
        have hp' : h'.Perm (mEntries f (mDir reverse) rs' 0) := by
          rw [hEdec']
          simp only [entOf, Option.toList, List.append_assoc, List.singleton_append]
          rw [← hs']
          have : (v :: h').Perm (v :: (mEntries f (mDir reverse) (rs.take i) 0 ++
              s' :: mEntries f (mDir reverse) (rs.drop (i + 1)) (i + 1))) := by
            refine hperm.trans ((List.Perm.cons _ hp).trans ?_)
            rw [hEdec, hv]
            exact (List.Perm.cons _ List.perm_middle).trans ((List.Perm.swap _ _ _).trans
              (List.Perm.cons _ List.perm_middle.symm))
          exact (List.perm_cons _).1 this
        rw [ih rs' h' hfuel' hsorted' hp' hh', hsv]
    · rename_i hlen
      cases heap with
      | nil =>
        have := mEntries_eq_nil f _ rs 0 (List.Perm.nil_eq hp).symm
        rw [this, stableSort_nil]
      | cons s tl =>
        cases tl with
        | cons _ _ => exact absurd hlen (by simp)
        | nil => ?_
        have hs_mem : s ∈ mEntries f (mDir reverse) rs 0 := hp.mem_iff.1 (by simp)
        obtain ⟨i, x, t, hi, hri, hs⟩ := mem_entries f _ rs 0 _ hs_mem
        simp only [Nat.zero_add] at hs
        have hrs_i : rs[i] = x :: t := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hri)
        have hdec : rs = rs.take i ++ (x :: t) :: rs.drop (i + 1) := by
          conv => lhs; rw [← List.take_append_drop i rs]
          rw [List.drop_eq_getElem_cons hi, hrs_i]
        have hE : mEntries f (mDir reverse) rs 0 =
            mEntries f (mDir reverse) (rs.take i) 0 ++ s :: mEntries f (mDir reverse) (rs.drop (i + 1)) (i + 1) := by
          conv => lhs; rw [hdec]
          rw [mEntries_append, mEntries_cons]
          simp only [List.length_take, Nat.zero_add, show min i rs.length = i by omega, entOf, hs]
          simp
        have hlen1 : (mEntries f (mDir reverse) (rs.take i) 0).length +
            (mEntries f (mDir reverse) (rs.drop (i + 1)) (i + 1)).length = 0 := by
          have := hp.length_eq
          rw [hE] at this
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          omega
        have hA := mEntries_eq_nil f (mDir reverse) (rs.take i) 0 (List.eq_nil_of_length_eq_zero (by omega))
        have hB := mEntries_eq_nil f (mDir reverse) (rs.drop (i + 1)) (i + 1)
          (List.eq_nil_of_length_eq_zero (by omega))
        have hflat : rs.flatten = x :: t := by
          conv => lhs; rw [hdec]
          simp only [List.flatten_append, List.flatten_cons, hA, hB]
          simp
        rw [hflat, stableSort_of_sorted _ _ (hsorted _ (List.mem_of_getElem? hri)), hs]

/-! ### The property -/

theorem mergeIsSorted_proven : MergeIsSorted := by
  intro its key reverse hsorted
  have hs' : ∀ r ∈ its, r.Pairwise (fun u v => mKf reverse (applyKey key) u ≤ mKf reverse (applyKey key) v) := by
    intro r hr
    have := hsorted r hr
    cases reverse
    · simpa [mKf, SortedBy] using this
    · simp only [SortedRevBy, if_true] at this
      exact this.imp (fun h => by simp only [mKf, if_true]; omega)
  have hheap := pyHeapify_correct (strictWeak_mLt reverse) (mEntries (applyKey key) (mDir reverse) its 0)
  have hm : merge its key reverse =
      mergeLoop (mLt reverse) (applyKey key) ((its.map List.length).sum + 1)
        (pyHeapify (mLt reverse) (mEntries (applyKey key) (mDir reverse) its 0)) := by
    cases reverse <;> rfl
  rw [hm, mergeLoop_spec reverse (applyKey key) _ its _ (by omega) hs' hheap.2 hheap.1]
  cases reverse
  · rfl
  · simp only [if_true]
    rw [pySortedRev_eq]
    rfl

end PyLean.Accel
