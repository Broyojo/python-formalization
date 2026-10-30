import PyLean.Accel.StableSort
import PyLean.Accel.HeapProps

/-!
The heap-selection loop shared by `nsmallest` and `nlargest`
(Lib/heapq.py:499-535 and :559-593), abstracted over the decorated tuple type.

Items are decorated as `dec e order`; the heap is a max-heap for `lt` holding
the `n` best items so far, `top` is the comparison key of its root, and an
item replaces the root when its key is strictly better. `kf` is the ascending
sort key the decoration encodes (`key` for `nsmallest`, `-key` for
`nlargest`) and `tagf order` the tie-break, which grows by one per insertion.
The proof compares the heap with a reference list `L` (the heap's items in
`lt` order) whose items are `take n` of the stable sort of the prefix seen.
-/

namespace PyLean.Accel

open PyLean

variable {β : Type} [Inhabited β]

structure SelSpec (β : Type) where
  lt : β → β → Bool
  dec : Int → Int → β
  eOf : β → Int
  topOf : β → Int
  kf : Int → Int
  tagf : Int → Int
  ostep : Int → Int
  ord0 : Nat → Int

structure SelSpec.Good (S : SelSpec β) : Prop where
  sw : StrictWeak S.lt
  eOf_dec : ∀ e o, S.eOf (S.dec e o) = e
  topOf_dec : ∀ e o, S.topOf (S.dec e o) = S.kf e
  lt_dec : ∀ e e' o o', S.tagf o ≠ S.tagf o' →
    S.lt (S.dec e o) (S.dec e' o') = decide (S.kf e < S.kf e' ∨ (S.kf e = S.kf e' ∧ S.tagf o < S.tagf o'))
  lt_key : ∀ e e' o o', S.kf e' < S.kf e → S.lt (S.dec e o) (S.dec e' o') = false
  tag_step : ∀ o, S.tagf (S.ostep o) = S.tagf o + 1
  tag_ord0 : ∀ i : Nat, S.tagf (S.ord0 i) = i

/-- The `for elem in it` loop. -/
def selLoop (S : SelSpec β) (result : List β) (top order : Int) : List Int → Py (List β)
  | [] => .ok result
  | e :: rest =>
    if S.kf e < top then do
      let (_, result) ← pyHeapreplace (maxLt S.lt) result (S.dec e order)
      selLoop S result (S.topOf (at! result 0)) (S.ostep order) rest
    else selLoop S result top order rest

/-- Decorate the first `n` items, heapify, run the loop, sort, undecorate. -/
def selAlgo (S : SelSpec β) (n : Nat) (order0 : Int) (it : List Int) : Py (List Int) := do
  let result := (it.take n).zipIdx.map (fun (e, i) => S.dec e (S.ord0 i))
  if result = [] then return []
  let result := pyHeapify (maxLt S.lt) result
  let top := S.topOf (at! result 0)
  let result ← selLoop S result top order0 (it.drop n)
  let result := result.mergeSort (fun a b => !S.lt b a)
  return result.map S.eOf

/-- Insert `t` after every item `lt`-below it. -/
def insT (lt : β → β → Bool) (t : β) : List β → List β
  | [] => [t]
  | a :: L => if lt a t then a :: insT lt t L else t :: a :: L

theorem insT_perm (lt : β → β → Bool) (t : β) : ∀ L : List β, (insT lt t L).Perm (t :: L)
  | [] => List.Perm.refl _
  | a :: L => by
    simp only [insT]
    split
    · exact (List.Perm.cons a (insT_perm lt t L)).trans (List.Perm.swap t a L)
    · exact List.Perm.refl _

theorem mem_insT (lt : β → β → Bool) (t x : β) (L : List β) : x ∈ insT lt t L ↔ x = t ∨ x ∈ L := by
  rw [(insT_perm lt t L).mem_iff]; simp

theorem pairwise_insT {lt : β → β → Bool} (hlt : StrictWeak lt) (t : β) :
    ∀ L : List β, L.Pairwise (fun a b => lt a b = true) →
      (∀ a ∈ L, lt a t = true ∨ lt t a = true) →
      (insT lt t L).Pairwise (fun a b => lt a b = true)
  | [], _, _ => by simp [insT]
  | a :: L, h, hc => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    simp only [insT]
    split
    · rename_i hat
      refine List.pairwise_cons.2 ⟨?_, pairwise_insT hlt t L h2 (fun b hb => hc b (by simp [hb]))⟩
      intro x hx
      rcases (mem_insT lt t x L).1 hx with rfl | hx
      · exact hat
      · exact h1 x hx
    · rename_i hat
      have hta : lt t a = true := by
        rcases hc a (by simp) with h | h
        · exact absurd h hat
        · exact h
      refine List.pairwise_cons.2 ⟨?_, h⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hta
      · exact hlt.trans _ _ _ hta (h1 x hx)

/-- Items in `L` are decorations with tags below `T`. -/
def Dec (S : SelSpec β) (L : List β) (T : Int) : Prop :=
  ∀ t ∈ L, ∃ e o, t = S.dec e o ∧ S.tagf o < T

theorem Dec.mono {S : SelSpec β} {L : List β} {T T' : Int} (h : Dec S L T) (hT : T ≤ T') :
    Dec S L T' := fun t ht => by
  obtain ⟨e, o, rfl, h⟩ := h t ht; exact ⟨e, o, rfl, by omega⟩

/-- A new decoration (tag `T`) compares with old ones by key, ties going to the old. -/
theorem lt_new {S : SelSpec β} (hS : S.Good) (e e' o o' : Int) (h : S.tagf o' < S.tagf o) :
    S.lt (S.dec e' o') (S.dec e o) = decide (S.kf e' ≤ S.kf e) := by
  rw [hS.lt_dec e' e o' o (by omega)]
  apply decide_eq_decide.2; omega

theorem lt_new' {S : SelSpec β} (hS : S.Good) (e e' o o' : Int) (h : S.tagf o' < S.tagf o) :
    S.lt (S.dec e o) (S.dec e' o') = decide (S.kf e < S.kf e') := by
  rw [hS.lt_dec e e' o o' (by omega)]
  apply decide_eq_decide.2; omega

theorem map_insT {S : SelSpec β} (hS : S.Good) (e o : Int) :
    ∀ L : List β, Dec S L (S.tagf o) →
      (insT S.lt (S.dec e o) L).map S.eOf = insS S.kf e (L.map S.eOf)
  | [], _ => by simp [insT, insS, hS.eOf_dec]
  | a :: L, h => by
    obtain ⟨e', o', rfl, ho⟩ := h a List.mem_cons_self
    simp only [insT, List.map_cons, insS, hS.eOf_dec, lt_new hS e e' o o' ho, decide_eq_true_eq]
    split
    · simp only [List.map_cons, hS.eOf_dec]
      rw [map_insT hS e o L (fun t ht => h t (by simp [ht]))]
    · simp [hS.eOf_dec]

theorem insT_comparable {S : SelSpec β} (hS : S.Good) (e o : Int) (L : List β) (h : Dec S L (S.tagf o)) :
    ∀ a ∈ L, S.lt a (S.dec e o) = true ∨ S.lt (S.dec e o) a = true := by
  intro a ha
  obtain ⟨e', o', rfl, ho⟩ := h a ha
  rw [lt_new hS e e' o o' ho, lt_new' hS e e' o o' ho]
  by_cases hk : S.kf e' ≤ S.kf e
  · left; simpa using hk
  · right; simp; omega

theorem pairwise_mem_total {lt : β → β → Bool} (L : List β) (h : L.Pairwise (fun a b => lt a b = true))
    (a b : β) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) : lt a b = true ∨ lt b a = true := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hb
  rw [List.pairwise_iff_getElem] at h
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exact Or.inl (h i j hi hj hij)
  · exact absurd rfl hab
  · exact Or.inr (h j i hj hi hij)

theorem lt_last {lt : β → β → Bool} {L : List β} (hL : L.Pairwise (fun a b => lt a b = true))
    (t : β) (ht : t ∈ L) (hne : L ≠ []) (htz : t ≠ L.getLast hne) : lt t (L.getLast hne) = true := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ht
  have hil : i < L.length - 1 := by
    rcases Nat.lt_or_ge i (L.length - 1) with h | h
    · exact h
    · exfalso; apply htz; rw [List.getLast_eq_getElem]; congr 1; omega
  have := List.pairwise_iff_getElem.1 hL i (L.length - 1) hi (by omega) hil
  rw [← List.getLast_eq_getElem hne] at this
  exact this

/-- The root of a max-heap holding the items of a strictly sorted `L` is its last item. -/
theorem root_eq_last {lt : β → β → Bool} (hlt : StrictWeak lt) (heap L : List β)
    (hp : heap.Perm L) (hh : IsHeap (maxLt lt) heap) (hL : L.Pairwise (fun a b => lt a b = true))
    (hne : L ≠ []) : at! heap 0 = L.getLast hne := by
  have hmin := root_min_mem hlt.maxLt heap hh
  have h0 : at! heap 0 ∈ L := by
    have : heap ≠ [] := fun h => hne (List.eq_nil_of_length_eq_zero (by rw [← hp.length_eq, h]; rfl))
    rw [← hp.mem_iff]
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil this
    simp [at!]
  have hz : L.getLast hne ∈ heap := hp.mem_iff.2 (List.getLast_mem hne)
  apply Classical.byContradiction
  intro hne'
  have hlast := hmin _ hz
  simp only [maxLt] at hlast
  -- at! heap 0 is strictly before the last item in L
  obtain ⟨i, hi, hiq⟩ := List.mem_iff_getElem.1 h0
  have hil : i < L.length - 1 := by
    rcases Nat.lt_or_ge i (L.length - 1) with h | h
    · exact h
    · exfalso; apply hne'
      rw [← hiq, List.getLast_eq_getElem]
      congr 1; omega
  have := List.pairwise_iff_getElem.1 hL i (L.length - 1) hi (by omega) hil
  rw [hiq, ← List.getLast_eq_getElem hne] at this
  rw [this] at hlast; cases hlast

theorem mem_dropLast_of_ne {L : List β} (hne : L ≠ []) (x : β) (hx : x ∈ L) (hxz : x ≠ L.getLast hne) :
    x ∈ L.dropLast := by
  have := List.dropLast_concat_getLast hne
  rw [← this] at hx
  simp at hx
  rcases hx with hx | hx
  · exact hx
  · exact absurd hx hxz

theorem pairwise_lt_le {lt : β → β → Bool} (hlt : StrictWeak lt) (L : List β)
    (h : L.Pairwise (fun a b => lt a b = true)) : L.Pairwise (fun a b => (!lt b a) = true) :=
  h.imp (fun hab => by simp [hlt.asymm _ _ hab])

/-- The loop invariant. -/
theorem selLoop_spec {S : SelSpec β} (hS : S.Good) (n : Nat) (hn : 1 ≤ n) :
    ∀ (rest : List Int) (heap L : List β) (order : Int) (P : List Int),
      heap.Perm L → IsHeap (maxLt S.lt) heap → L.Pairwise (fun a b => S.lt a b = true) →
      Dec S L (S.tagf order) → L.map S.eOf = (stableSort S.kf P).take n → L.length = n →
      ∃ heap' L', selLoop S heap (S.topOf (at! heap 0)) order rest = .ok heap' ∧
        heap'.Perm L' ∧ L'.Pairwise (fun a b => S.lt a b = true) ∧
        L'.map S.eOf = (stableSort S.kf (P ++ rest)).take n := by
  intro rest
  induction rest with
  | nil =>
    intro heap L order P hp _ hL _ hm _
    exact ⟨heap, L, rfl, hp, hL, by simpa using hm⟩
  | cons e rest ih =>
    intro heap L order P hp hh hL hdec hm hlen
    have hne : L ≠ [] := by intro h; subst h; simp at hlen; omega
    have hroot := root_eq_last hS.sw heap L hp hh hL hne
    obtain ⟨ez, oz, hz, hoz⟩ := hdec _ (List.getLast_mem hne)
    have htop : S.topOf (at! heap 0) = S.kf ez := by rw [hroot, hz, hS.topOf_dec]
    have hP : P ++ e :: rest = (P ++ [e]) ++ rest := by simp
    -- the reference after one more item
    have href : (stableSort S.kf (P ++ [e])).take n = (insS S.kf e (L.map S.eOf)).take n := by
      rw [take_stableSort_snoc, ← hm]
    have hLz : L = L.dropLast ++ [L.getLast hne] := (List.dropLast_concat_getLast hne).symm
    simp only [selLoop, htop]
    split
    · -- replace the root
      rename_i hlt
      have hheap_ne : heap ≠ [] :=
        fun h => hne (List.eq_nil_of_length_eq_zero (by rw [← hp.length_eq, h]; rfl))
      obtain ⟨v, h', hrep, hh', hperm, -⟩ :=
        pyHeapreplace_correct hS.sw.maxLt heap (S.dec e order) hh hheap_ne
      have hv : v = L.getLast hne := by
        simp only [pyHeapreplace, if_neg hheap_ne] at hrep
        cases hrep; exact hroot
      subst hv
      simp only [hrep, bind, Except.bind]
      let L' := insT S.lt (S.dec e order) L.dropLast
      have hdecD : Dec S L.dropLast (S.tagf order) :=
        fun t ht => hdec t (List.dropLast_subset _ ht)
      have hp' : h'.Perm L' := by
        have hDz : (L.dropLast ++ [L.getLast hne]).Perm (L.getLast hne :: L.dropLast) :=
          List.perm_append_comm
        have e1 : (S.dec e order :: L).Perm (L.getLast hne :: L') := by
          have h0 : S.dec e order :: L = S.dec e order :: (L.dropLast ++ [L.getLast hne]) := by
            rw [List.dropLast_concat_getLast hne]
          rw [h0]
          exact ((List.Perm.cons _ hDz).trans (List.Perm.swap _ _ _)).trans
            (List.Perm.cons _ (insT_perm _ _ _).symm)
        have h1 : (L.getLast hne :: h').Perm (L.getLast hne :: L') :=
          hperm.trans ((List.Perm.cons _ hp).trans e1)
        exact (List.perm_cons _).1 h1
      have hL' : L'.Pairwise (fun a b => S.lt a b = true) :=
        pairwise_insT hS.sw _ _ (hL.sublist (List.dropLast_sublist L))
          (insT_comparable hS e order _ hdecD)
      have hdec' : Dec S L' (S.tagf (S.ostep order)) := by
        intro t ht
        rcases (mem_insT _ _ _ _).1 ht with rfl | ht
        · exact ⟨e, order, rfl, by rw [hS.tag_step]; omega⟩
        · obtain ⟨e', o', rfl, h⟩ := hdecD t ht
          exact ⟨e', o', rfl, by rw [hS.tag_step]; omega⟩
      have hm' : L'.map S.eOf = (stableSort S.kf (P ++ [e])).take n := by
        rw [href, map_insT hS e order _ hdecD]
        have hlast : L.map S.eOf = L.dropLast.map S.eOf ++ [ez] := by
          conv => lhs; rw [hLz]
          simp [hz, hS.eOf_dec]
        rw [hlast, insS_before_last S.kf e ez (by omega)]
        rw [List.take_append_of_le_length (by rw [length_insS]; simp; omega)]
        rw [List.take_of_length_le (by rw [length_insS]; simp; omega)]
      have hlen' : L'.length = n := by
        rw [(insT_perm _ _ _).length_eq]; simp; omega
      obtain ⟨heap'', L'', r1, r2, r3, r4⟩ :=
        ih h' L' (S.ostep order) (P ++ [e]) hp' hh' hL' hdec' hm' hlen'
      exact ⟨heap'', L'', r1, r2, r3, by rw [hP]; exact r4⟩
    · -- keep the heap
      rename_i hge
      have hm' : L.map S.eOf = (stableSort S.kf (P ++ [e])).take n := by
        rw [href]
        have hall : ∀ x ∈ L.map S.eOf, S.kf x ≤ S.kf e := by
          intro x hx
          obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
          by_cases htz : t = L.getLast hne
          · subst htz; rw [hz, hS.eOf_dec]; omega
          · have hzt := lt_last hL t ht hne htz
            obtain ⟨et, ot, rfl, -⟩ := hdec _ ht
            rw [hz] at hzt
            rw [hS.eOf_dec]
            by_cases hk : S.kf ez < S.kf et
            · rw [hS.lt_key _ _ _ _ hk] at hzt; cases hzt
            · omega
        rw [insS_of_all_le S.kf e _ hall]
        rw [List.take_append_of_le_length (by simp; omega)]
        rw [List.take_of_length_le (by simp; omega)]
      obtain ⟨heap'', L'', r1, r2, r3, r4⟩ :=
        ih heap L order (P ++ [e]) hp hh hL hdec hm' hlen
      exact ⟨heap'', L'', htop ▸ r1, r2, r3, by rw [hP]; exact r4⟩

/-- Sorting the heap by `lt` gives the reference list back. -/
theorem sort_eq_ref {lt : β → β → Bool} (hlt : StrictWeak lt) (heap L : List β) (hp : heap.Perm L)
    (hL : L.Pairwise (fun a b => lt a b = true)) : heap.mergeSort (fun a b => !lt b a) = L := by
  have trans : ∀ a b c : β, (!lt b a) = true → (!lt c b) = true → (!lt c a) = true := by
    intro a b c h1 h2
    simp only [Bool.not_eq_true'] at *
    exact hlt.le_trans _ _ _ h1 h2
  have total : ∀ a b : β, ((!lt b a) || (!lt a b)) = true := by
    intro a b
    cases h : lt a b
    · simp
    · simp [hlt.asymm _ _ h]
  apply List.Perm.eq_of_pairwise (le := fun a b => (!lt b a) = true)
  · intro a b ha hb h1 h2
    have ha' : a ∈ L := ((List.mergeSort_perm heap _).trans hp).mem_iff.1 ha
    apply Classical.byContradiction
    intro hab
    rcases pairwise_mem_total L hL a b ha' hb hab with h | h
    · simp [h] at h2
    · simp [h] at h1
  · exact List.pairwise_mergeSort trans total heap
  · exact pairwise_lt_le hlt L hL
  · exact (List.mergeSort_perm heap _).trans hp

/-- The decorated first `n` items, inserted one by one, form the reference list. -/
theorem init_ref {S : SelSpec β} (hS : S.Good) :
    ∀ (xs : List Int) (k : Nat) (L : List β) (P : List Int),
      L.Pairwise (fun a b => S.lt a b = true) → Dec S L k → L.map S.eOf = stableSort S.kf P →
      let L' := (xs.zipIdx k).foldl (fun L p => insT S.lt (S.dec p.1 (S.ord0 p.2)) L) L
      L'.Pairwise (fun a b => S.lt a b = true) ∧ Dec S L' (k + xs.length) ∧
        L'.map S.eOf = stableSort S.kf (P ++ xs) ∧
        L'.Perm (L ++ (xs.zipIdx k).map (fun p => S.dec p.1 (S.ord0 p.2))) := by
  intro xs
  induction xs with
  | nil => intro k L P h1 h2 h3; simp [h1, h2, h3]
  | cons x xs ih =>
    intro k L P h1 h2 h3
    simp only [List.zipIdx_cons, List.foldl_cons]
    have hd : Dec S L (S.tagf (S.ord0 k)) := by rw [hS.tag_ord0]; exact h2
    have q1 := pairwise_insT hS.sw (S.dec x (S.ord0 k)) L h1 (insT_comparable hS x _ L hd)
    have q2 : Dec S (insT S.lt (S.dec x (S.ord0 k)) L) ((k + 1 : Nat) : Int) := by
      intro t ht
      rcases (mem_insT _ _ _ _).1 ht with rfl | ht
      · exact ⟨x, S.ord0 k, rfl, by rw [hS.tag_ord0]; omega⟩
      · obtain ⟨e', o', rfl, h⟩ := h2 t ht
        exact ⟨e', o', rfl, by omega⟩
    have q3 : (insT S.lt (S.dec x (S.ord0 k)) L).map S.eOf = stableSort S.kf (P ++ [x]) := by
      rw [map_insT hS x _ L hd, h3, stableSort_append_single]
    obtain ⟨r1, r2, r3, r4⟩ := ih (k + 1) _ (P ++ [x]) q1 q2 q3
    refine ⟨r1, by simp at r2 ⊢; exact r2.mono (by omega), by simpa using r3, ?_⟩
    refine r4.trans ?_
    simp only [List.map_cons, List.append_assoc, List.singleton_append] at *
    refine List.Perm.trans (List.Perm.append_right _ (insT_perm _ _ _)) ?_
    simp only [List.cons_append]
    exact List.perm_middle.symm

theorem foldl_insT_map {S : SelSpec β} (xs : List (Int × Nat)) :
    (xs.map (fun p => S.dec p.1 (S.ord0 p.2))).foldl (fun L t => insT S.lt t L) [] =
      xs.foldl (fun L p => insT S.lt (S.dec p.1 (S.ord0 p.2)) L) [] := by
  rw [List.foldl_map]

/-- The selection algorithm returns `take n` of the stable sort. -/
theorem selAlgo_spec {S : SelSpec β} (hS : S.Good) (n : Nat) (order0 : Int)
    (h0 : S.tagf order0 = n) (it : List Int) :
    selAlgo S n order0 it = .ok ((stableSort S.kf it).take n) := by
  simp only [selAlgo]
  have hzip : ((it.take n).zipIdx.map (fun x => S.dec x.1 (S.ord0 x.2))) =
      ((it.take n).zipIdx.map (fun p => S.dec p.1 (S.ord0 p.2))) := rfl
  split
  · rename_i hr
    simp only [List.map_eq_nil_iff, List.zipIdx_eq_nil_iff, List.take_eq_nil_iff] at hr
    rcases hr with rfl | rfl
    · simp [pure, Except.pure]
    · simp [stableSort_nil, pure, Except.pure]
  · rename_i hr
    obtain ⟨i1, i2, i3, i4⟩ := init_ref hS (it.take n) 0 [] [] (by simp) (by intro t ht; simp at ht)
      (by simp [stableSort_nil])
    simp only [List.nil_append] at i3 i4
    generalize hL0 : (List.zipIdx (List.take n it)).foldl
      (fun L p => insT S.lt (S.dec p.1 (S.ord0 p.2)) L) [] = L0 at i1 i2 i3 i4
    have hheap := pyHeapify_correct hS.sw.maxLt ((it.take n).zipIdx.map (fun p => S.dec p.1 (S.ord0 p.2)))
    have hp0 : (pyHeapify (maxLt S.lt) ((it.take n).zipIdx.map (fun p => S.dec p.1 (S.ord0 p.2)))).Perm L0 :=
      hheap.2.trans i4.symm
    have hn1 : 1 ≤ n := by
      cases n with
      | zero => simp at hr
      | succ n => omega
    have hlen_ss : ∀ l, (stableSort S.kf l).length = l.length :=
      fun l => (stableSort_perm S.kf l).length_eq
    by_cases hrest : it.drop n = []
    · rw [hrest]
      simp only [selLoop, bind, Except.bind, pure, Except.pure]
      rw [sort_eq_ref hS.sw _ L0 hp0 i1, i3]
      have hle : it.length ≤ n := List.drop_eq_nil_iff.1 hrest
      rw [List.take_of_length_le hle, List.take_of_length_le (l := stableSort S.kf it)
        (by rw [hlen_ss]; exact hle)]
    · have hgt : n < it.length := by
        rcases Nat.lt_or_ge n it.length with h | h
        · exact h
        · exact absurd (List.drop_eq_nil_iff.2 h) hrest
      have htl : (it.take n).length = n := by simp; omega
      have hLlen : L0.length = n := by rw [i4.length_eq]; simp; omega
      have hd0 : Dec S L0 (S.tagf order0) := by
        rw [h0]; intro t ht
        obtain ⟨e', o', rfl, h⟩ := i2 t ht
        exact ⟨e', o', rfl, by simp at h; omega⟩
      have hm0 : L0.map S.eOf = (stableSort S.kf (it.take n)).take n := by
        rw [i3, List.take_of_length_le (l := stableSort S.kf (it.take n)) (by rw [hlen_ss, htl]; omega)]
      obtain ⟨heap', L', r1, r2, r3, r4⟩ :=
        selLoop_spec hS n hn1 (it.drop n) _ L0 order0 (it.take n) hp0 hheap.1 i1 hd0 hm0 hLlen
      rw [List.take_append_drop] at r4
      simp only [r1, bind, Except.bind, pure, Except.pure]
      rw [sort_eq_ref hS.sw _ L' r2 r3, r4]

end PyLean.Accel
