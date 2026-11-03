import PyLean.ListSort.FalliblePerm

/-! # The merges and the main loop with a comparison that may raise: still permutations -/

namespace PyLean.ListSort

open PyLean

variable {α : Type}

theorem loLoopF_perm (lt : PLt α) :
    ∀ (fuel : Nat) (g : Bool) (mg ac bc : Nat) (out A B : List α) (ms : MS),
      (loLoopF lt fuel g mg ac bc out A B ms).1.Perm (out ++ A ++ B) := by
  intro fuel
  induction fuel with
  | zero => intro g mg ac bc out A B ms; simp [loLoopF]
  | succ fuel ih =>
    intro g mg ac bc out A B ms
    cases g with
    | false =>
      rcases A with _ | ⟨a, A'⟩ <;> rcases B with _ | ⟨b, B'⟩ <;> simp only [loLoopF]
      all_goals try simp
      generalize isltF lt ms b a = C
      obtain ⟨c, ms1⟩ := C
      rcases c with e | c
      · simp only; perm_count
      cases c
      · simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · perm_count
        · split
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
      · simp only [↓reduceIte]
        split
        · subst_vars; perm_count
        · split
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
    | true =>
      rcases B with _ | ⟨b, B'⟩ <;> simp only [loLoopF]
      · simp
      generalize gallopRightF lt b _ _ _ _ = G
      obtain ⟨k, ms1⟩ := G
      rcases k with e | k
      · simp only; perm_count
      simp only
      conv => rhs; rw [← List.take_append_drop k A]
      generalize A.take k = A0
      generalize A.drop k = A1
      split
      · perm_count
      split
      · perm_count
      split
      · subst_vars; perm_count
      rcases A1 with _ | ⟨a, A'⟩
      · simp only; perm_count
      simp only
      generalize gallopLeftF lt a _ _ _ _ = G
      obtain ⟨k2, ms2⟩ := G
      rcases k2 with e | k2
      · simp only; perm_count
      simp only
      conv => rhs; rw [← List.take_append_drop k2 B']
      generalize B'.take k2 = B0
      generalize B'.drop k2 = B1
      split
      · perm_count
      split
      · perm_count
      split
      · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
      · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)

theorem mergeLoF_perm (lt : PLt α) (A B : List α) (ms : MS) :
    (mergeLoF lt A B ms).1.Perm (A ++ B) := by
  rcases B with _ | ⟨b, B'⟩ <;> simp only [mergeLoF]
  · simp
  split
  · subst_vars; perm_count
  split
  · perm_count
  · exact (loLoopF_perm lt _ _ _ _ _ _ _ _ _).trans (by perm_count)

theorem hiLoopF_perm (lt : PLt α) :
    ∀ (fuel : Nat) (g : Bool) (mg ac bc : Nat) (out Ar Br : List α) (ms : MS),
      (hiLoopF lt fuel g mg ac bc out Ar Br ms).1.Perm (Ar ++ Br ++ out) := by
  intro fuel
  induction fuel with
  | zero => intro g mg ac bc out Ar Br ms; simp only [hiLoopF]; perm_count
  | succ fuel ih =>
    intro g mg ac bc out Ar Br ms
    cases g with
    | false =>
      rcases Ar with _ | ⟨a, Ar'⟩ <;> rcases Br with _ | ⟨b, Br'⟩ <;> simp only [hiLoopF]
      all_goals first | perm_count | skip
      generalize isltF lt ms b a = C
      obtain ⟨c, ms1⟩ := C
      rcases c with e | c
      · simp only; perm_count
      cases c
      · simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · perm_count
        · split
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
      · simp only [↓reduceIte]
        split
        · subst_vars; perm_count
        · split
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
    | true =>
      rcases Br with _ | ⟨b, Br'⟩ <;> simp only [hiLoopF]
      · perm_count
      generalize gallopRightF lt b _ _ _ _ = G
      obtain ⟨k0, ms1⟩ := G
      rcases k0 with e | k0
      · simp only; perm_count
      simp only
      generalize Ar.length - k0 = k
      conv => rhs; rw [← List.take_append_drop k Ar]
      generalize Ar.take k = A0
      generalize Ar.drop k = A1
      split
      · obtain ⟨_, rfl⟩ := ‹_ ∧ _›; perm_count
      split
      · perm_count
      rcases A1 with _ | ⟨a, Ar'⟩
      · simp only; perm_count
      simp only
      generalize gallopLeftF lt a _ _ _ _ = G
      obtain ⟨k2, ms2⟩ := G
      rcases k2 with e | k2
      · simp only; perm_count
      simp only
      generalize Br'.length - k2 = kb
      conv => rhs; rw [← List.take_append_drop kb Br']
      generalize Br'.take kb = B0
      generalize Br'.drop kb = B1
      split
      · perm_count
      split
      · obtain ⟨_, rfl⟩ := ‹_ ∧ _›; perm_count
      split
      · perm_count
      split
      · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
      · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)

theorem mergeHiF_perm (lt : PLt α) (A B : List α) (ms : MS) :
    (mergeHiF lt A B ms).1.Perm (A ++ B) := by
  simp only [mergeHiF]
  have hA : A = A.reverse.reverse := by simp
  generalize hR : A.reverse = Ar at hA
  subst hA
  rcases Ar with _ | ⟨a, Ar'⟩
  · simp
  simp only
  split
  · subst_vars; perm_count
  split
  · perm_count
  · exact (hiLoopF_perm lt _ _ _ _ _ _ _ _ _).trans (by perm_count)

theorem mergeAtF_perm (lt : PLt α) (A B : List α) (ms : MS) :
    (mergeAtF lt A B ms).1.Perm (A ++ B) := by
  rcases B with _ | ⟨b0, B'⟩ <;> simp only [mergeAtF]
  · simp
  generalize gallopRightF lt b0 _ _ _ _ = G
  obtain ⟨k, ms1⟩ := G
  rcases k with e | k
  · exact List.Perm.refl _
  simp only
  conv => rhs; rw [← List.take_append_drop k A]
  generalize A.take k = A0
  generalize A.drop k = A1
  split
  · next h => rw [List.getLast?_eq_none_iff] at h; perm_count
  rename_i alast _
  generalize gallopLeftF lt alast _ _ _ _ = G
  obtain ⟨nb, ms2⟩ := G
  rcases nb with e | nb
  · simp only; perm_count
  simp only
  split
  · perm_count
  generalize hBB : b0 :: B' = BB
  conv => rhs; rw [← List.take_append_drop nb BB]
  generalize BB.take nb = B0
  generalize BB.drop nb = B1
  split
  · exact (((mergeLoF_perm lt A1 B0 _).append_left A0).append_right B1).trans (by perm_count)
  · exact (((mergeHiF_perm lt A1 B0 _).append_left A0).append_right B1).trans (by perm_count)

theorem mergeAtArrF_perm (lt : PLt α) (base na nb : Nat) (st : FRes α) :
    (mergeAtArrF lt base na nb st).1.Perm st.1 := by
  obtain ⟨arr, ms, e0⟩ := st
  cases e0 with
  | some e => exact List.Perm.refl _
  | none =>
    simp only [mergeAtArrF]
    have hm := mergeAtF_perm lt ((arr.drop base).take na) ((arr.drop (base + na)).take nb) ms
    generalize mergeAtF lt _ _ ms = M at hm
    obtain ⟨m, ms', e⟩ := M
    simp only at hm ⊢
    refine ((hm.append_left _).append_right _).trans ?_
    have e : arr = arr.take base ++ ((arr.drop base).take na ++ ((arr.drop (base + na)).take nb ++
        arr.drop (base + na + nb))) := by
      conv => lhs; rw [← List.take_append_drop base arr]
      congr 1
      conv => lhs; rw [← List.take_append_drop na (arr.drop base)]
      congr 1
      rw [List.drop_drop]
      conv => lhs; rw [← List.take_append_drop nb (arr.drop (base + na))]
      rw [List.drop_drop]
    conv => rhs; rw [e]
    simp only [List.append_assoc]
    exact List.Perm.refl _

/-! ## The main loop -/

theorem sortStepF_perm (lt : PLt α) (xs : List α) (N pos : Nat) (st : Sorter α)
    (hNx : xs.length = N) (hperm : st.arr.Perm xs) (hpos : pos < N) :
    (sortStepF lt N pos st).1.arr.Perm xs ∧
      ((sortStepF lt N pos st).2.2 = none →
        1 ≤ (sortStepF lt N pos st).2.1 ∧ pos + (sortStepF lt N pos st).2.1 ≤ N) := by
  have hlen : st.arr.length = N := by rw [hperm.length_eq, hNx]
  have hdl : (st.arr.drop pos).length = N - pos := by simp [hlen]
  have hcr := countRunF_perm lt (st.arr.drop pos) st.ms
  have hsplit : ∀ rest : List α, rest.Perm (st.arr.drop pos) → (st.arr.take pos ++ rest).Perm xs := by
    intro rest hr
    refine List.Perm.trans ?_ hperm
    conv => rhs; rw [← List.take_append_drop pos st.arr]
    exact hr.append_left _
  simp only [sortStepF]
  generalize countRunF lt (st.arr.drop pos) st.ms = CR at hcr
  obtain ⟨n0, rest0, ms0, e0⟩ := CR
  simp only at hcr
  obtain ⟨hp0, hn⟩ := hcr
  cases e0 with
  | some e => exact ⟨hsplit _ hp0, fun h => by simp at h⟩
  | none =>
    have hne : st.arr.drop pos ≠ [] := by intro h; rw [h] at hdl; simp at hdl; omega
    obtain ⟨hn0, hn0'⟩ := hn rfl hne
    rw [hdl] at hn0'
    simp only
    generalize minrunNext st.mr = MR
    obtain ⟨minrun, mr⟩ := MR
    simp only
    have hrun : ∃ n rest ms e, (if n0 < minrun then
        ((if N - pos ≤ minrun then N - pos else minrun),
          (binarysortF lt rest0 (if N - pos ≤ minrun then N - pos else minrun) n0 ms0).1,
          (binarysortF lt rest0 (if N - pos ≤ minrun then N - pos else minrun) n0 ms0).2.1,
          (binarysortF lt rest0 (if N - pos ≤ minrun then N - pos else minrun) n0 ms0).2.2)
        else (n0, rest0, ms0, none)) = (n, rest, ms, e) ∧ 1 ≤ n ∧ n ≤ N - pos ∧
          rest.Perm (st.arr.drop pos) := by
      split
      · refine ⟨_, _, _, _, rfl, by split <;> omega, by split <;> omega, ?_⟩
        refine (binarysortF_perm lt rest0 _ n0 ms0 ?_).trans hp0
        have : n0 ≠ 0 := by omega
        simp only [this, ↓reduceIte]; split <;> omega
      · exact ⟨_, _, _, _, rfl, hn0, hn0', hp0⟩
    obtain ⟨n, rest, ms, e, hEq2, hn1, hn2, hrp⟩ := hrun
    have hlet : (if n0 < minrun then
        (let force := if N - pos ≤ minrun then N - pos else minrun
         let (rest, ms, e) := binarysortF lt rest0 force n0 ms0
         (force, rest, ms, e))
        else (n0, rest0, ms0, none)) = (n, rest, ms, e) := by
      rw [← hEq2]
    rw [hlet]
    cases e with
    | some e => exact ⟨hsplit _ hrp, fun h => by simp at h⟩
    | none =>
      simp only
      have hpres := foundNewRun_pres (mergeAtArrF lt) (fun s => s.1.Perm xs)
        (fun b na nb s hs => (mergeAtArrF_perm lt b na nb s).trans hs) N n st.stk
        (st.arr.take pos ++ rest, ms, none) (hsplit _ hrp)
      generalize foundNewRun (mergeAtArrF lt) N n st.stk (st.arr.take pos ++ rest, ms, none) = F at hpres
      obtain ⟨stk', arr', ms', e'⟩ := F
      exact ⟨hpres, fun _ => ⟨hn1, by omega⟩⟩

theorem sortLoopF_perm (lt : PLt α) (xs : List α) (N : Nat) (hNx : xs.length = N) :
    ∀ (fuel pos : Nat) (st : Sorter α), st.arr.Perm xs → pos < N →
      (sortLoopF lt N fuel pos st).1.arr.Perm xs
  | 0, pos, st, h, _ => by simpa [sortLoopF] using h
  | fuel + 1, pos, st, h, hp => by
    simp only [sortLoopF]
    have hs := sortStepF_perm lt xs N pos st hNx h hp
    generalize sortStepF lt N pos st = S at hs
    obtain ⟨st', n, e⟩ := S
    simp only at hs ⊢
    cases e with
    | some e => exact hs.1
    | none =>
      simp only
      split
      · rename_i hc
        exact sortLoopF_perm lt xs N hNx fuel (pos + n) st' hs.1 hc.1
      · exact hs.1

/-- **Permutation even on error.** For every comparison, raising or not, consistent or not, and every
`reverse`: the list after `list.sort` holds a permutation of its items, whether the sort finished or a
comparison raised partway (listobject.c:1829-1831, :3176-3202). -/
def SortPermOnError : Prop :=
  ∀ (α : Type) (lt : PLt α) (xs : List α) (reverse : Bool), (listSortCntF lt xs reverse).1.Perm xs

theorem sortCoreF_perm (lt : PLt α) (xs : List α) : (sortCoreF lt xs).1.arr.Perm xs := by
  unfold sortCoreF
  dsimp only
  split
  · exact List.Perm.refl _
  · have h := sortLoopF_perm lt xs xs.length rfl xs.length 0
      { arr := xs, ms := {}, stk := [], pushOk := true, mr := mergeInitMr xs.length }
      (List.Perm.refl _) (by omega)
    generalize sortLoopF lt xs.length xs.length 0 _ = R at h
    obtain ⟨st, e⟩ := R
    simp only at h
    cases e with
    | some e => exact h
    | none =>
      simp only
      have hfc := forceCollapse_pres (mergeAtArrF lt) (fun s => s.1.Perm xs)
        (fun b na nb s hs => (mergeAtArrF_perm lt b na nb s).trans hs) _ st.stk (st.arr, st.ms, none)
        (Nat.le_refl _) h
      generalize forceCollapse (mergeAtArrF lt) st.stk (st.arr, st.ms, none) = F at hfc
      obtain ⟨stk', arr', ms', e'⟩ := F
      exact hfc

theorem sortPermOnError_proven : SortPermOnError := by
  intro α lt xs reverse
  unfold listSortCntF
  split
  · exact List.Perm.refl _
  · simp only
    have h := sortCoreF_perm lt (if reverse then xs.reverse else xs)
    generalize sortCoreF lt (if reverse then xs.reverse else xs) = R at h
    obtain ⟨st, e⟩ := R
    simp only at h ⊢
    cases reverse
    · simpa using h
    · simp only [↓reduceIte] at h ⊢
      exact (List.reverse_perm _).trans (h.trans (List.reverse_perm _))

end PyLean.ListSort
