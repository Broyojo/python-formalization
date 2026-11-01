import PyLean.ListSort.Stack

/-!
# Nothing is lost or duplicated, whatever `<` does

Every step of the model permutes the array, for an arbitrary comparison
function `lt` (inconsistent, random-looking or not): `count_run`, `binarysort`,
`merge_lo`, `merge_hi`, `merge_at`. Run lengths stay in range. These facts are
all the stack-bound theorem needs from the data part of the sort.
-/

namespace PyLean.ListSort

variable {α : Type}

open Classical in
theorem perm_of_count {l1 l2 : List α} (h : ∀ x, l1.count x = l2.count x) : l1.Perm l2 :=
  List.perm_iff_count.2 h

open Classical in
theorem count_take_drop (k : Nat) (l : List α) (x : α) :
    l.count x = (l.take k).count x + (l.drop k).count x := by
  conv => lhs; rw [← List.take_append_drop k l]
  rw [List.count_append]

macro "perm_count" : tactic => `(tactic| ((try subst_vars); apply perm_of_count; intro x; (try simp only [List.count_append, List.count_cons, List.count_nil, List.count_reverse] at *); (first | done | omega)))

/-- `perm_count` with the extra `take`/`drop` splittings `l = l.take k ++ l.drop k`. -/
macro "perm_count_td" ts:term,* : tactic => `(tactic| (apply perm_of_count; intro x; (have := fun (k : Nat) (l : List _) => count_take_drop k l x); simp only [List.count_append, List.count_cons, List.count_nil, List.count_reverse] at *; $[(have := this $ts)];*; (try omega)))

/-! ## count_run -/

theorem ascTake_spec (lt : α → α → Bool) :
    ∀ (prev : α) (rest : List α) (ms : MS),
      (ascTake lt prev rest ms).1 ++ (ascTake lt prev rest ms).2.1 = rest
  | _, [], _ => rfl
  | prev, z :: rest, ms => by
    simp only [ascTake]
    split
    · rfl
    · simp [ascTake_spec lt z rest]

theorem descLoop_perm (lt : α → α → Bool) :
    ∀ (done grp : List α) (prev : α) (rest : List α) (ms : MS),
      ((descLoop lt done grp prev rest ms).1 ++ (descLoop lt done grp prev rest ms).2.1).Perm
        (done ++ grp ++ rest)
  | done, grp, _, [], ms => by simp only [descLoop]; perm_count
  | done, grp, prev, z :: rest, ms => by
    simp only [descLoop]
    split
    · have := descLoop_perm lt (done ++ grp.reverse) [z] z rest
        (islt lt ms z prev).2
      refine this.trans ?_
      perm_count
    · split
      · perm_count
      · have := descLoop_perm lt done (grp ++ [z]) z rest
          (islt lt (islt lt ms z prev).2 prev z).2
        refine this.trans ?_
        perm_count

theorem descLoop_len (lt : α → α → Bool) :
    ∀ (done grp : List α) (prev : α) (rest : List α) (ms : MS),
      done.length + grp.length ≤ (descLoop lt done grp prev rest ms).1.length
  | done, grp, _, [], ms => by simp [descLoop]
  | done, grp, prev, z :: rest, ms => by
    simp only [descLoop]
    split
    · have := descLoop_len lt (done ++ grp.reverse) [z] z rest (islt lt ms z prev).2
      simp at this ⊢; omega
    · split
      · simp
      · have := descLoop_len lt done (grp ++ [z]) z rest (islt lt (islt lt ms z prev).2 prev z).2
        simp at this ⊢; omega

theorem countRun_perm (lt : α → α → Bool) (xs : List α) (ms : MS) :
    (countRun lt xs ms).2.1.Perm xs ∧ (xs ≠ [] → 1 ≤ (countRun lt xs ms).1) ∧
      (countRun lt xs ms).1 ≤ xs.length := by
  match xs with
  | [] => simp [countRun]
  | x0 :: rest =>
    simp only [countRun]
    have hsp := ascTake_spec lt x0 rest ms
    generalize ascTake lt x0 rest ms = A at hsp
    obtain ⟨t, r, ms1⟩ := A
    simp only at hsp
    subst hsp
    match r with
    | [] => simp
    | y :: r' =>
      simp only
      generalize hE : (if (x0 :: t).length > 1 then
          islt lt ms1 x0 ((x0 :: t).getLast (by simp)) else (false, ms1)) = E
      obtain ⟨early, ms2⟩ := E
      cases early
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hd := descLoop_perm lt (x0 :: t).reverse [y] y r' ms2
        have hdl := descLoop_len lt (x0 :: t).reverse [y] y r' ms2
        generalize descLoop lt (x0 :: t).reverse [y] y r' ms2 = D at hd hdl
        obtain ⟨pre, r2, ms3⟩ := D
        simp only at hd
        have hpre : pre ≠ [] := by
          intro h; subst h; simp at hdl
        match hrun : pre.reverse with
        | [] => simp at hrun; exact absurd hrun hpre
        | w :: ws =>
          simp only
          have hsp2 := ascTake_spec lt ((w :: ws).getLast (by simp)) r2 ms3
          generalize ascTake lt ((w :: ws).getLast (by simp)) r2 ms3 = E2 at hsp2
          obtain ⟨e, r3, ms4⟩ := E2
          simp only at hsp2
          subst hsp2
          have hl := hd.length_eq
          have hrl : (w :: ws).length = pre.length := by rw [← hrun]; simp
          refine ⟨?_, fun _ => by simp; omega, ?_⟩
          · have hp : (pre.reverse ++ e ++ r3).Perm (pre ++ (e ++ r3)) := by perm_count
            rw [hrun] at hp
            refine hp.trans ?_
            refine hd.trans ?_
            perm_count
          · simp at hl hrl ⊢; omega
      · simp

/-! ## binarysort -/

theorem binLoop_le (test : Nat → MS → Bool × MS) :
    ∀ (fuel lo hi : Nat) (ms : MS), lo ≤ hi → lo ≤ (binLoop test fuel lo hi ms).1 ∧
      (binLoop test fuel lo hi ms).1 ≤ hi
  | 0, lo, hi, ms, h => by simp [binLoop]; omega
  | fuel + 1, lo, hi, ms, h => by
    simp only [binLoop]
    split
    · split
      · have := binLoop_le test fuel (lo + (hi - lo) / 2 + 1) hi (test (lo + (hi - lo) / 2) ms).2 (by omega); omega
      · have := binLoop_le test fuel lo (lo + (hi - lo) / 2) (test (lo + (hi - lo) / 2) ms).2 (by omega); omega
    · simp; omega

theorem bsInsert_perm (lt : α → α → Bool) (sorted : List α) (p : α) (ms : MS) :
    (bsInsert lt sorted p ms).1.Perm (sorted ++ [p]) := by
  simp only [bsInsert]
  generalize binLoop _ _ _ _ _ = R
  obtain ⟨l, ms'⟩ := R
  simp only
  apply perm_of_count; intro x
  have := count_take_drop l sorted x
  simp only [List.count_append, List.count_cons, List.count_nil] at *
  omega

theorem bsLoop_perm (lt : α → α → Bool) :
    ∀ (sorted ps : List α) (ms : MS), (bsLoop lt sorted ps ms).1.Perm (sorted ++ ps)
  | sorted, [], ms => by simp [bsLoop]
  | sorted, p :: ps, ms => by
    simp only [bsLoop]
    refine (bsLoop_perm lt _ ps _).trans ?_
    have := bsInsert_perm lt sorted p ms
    refine (this.append_right ps).trans ?_
    simp

theorem binarysort_perm (lt : α → α → Bool) (a : List α) (n ok : Nat) (ms : MS)
    (h : (if ok = 0 then 1 else ok) ≤ n) : (binarysort lt a n ok ms).1.Perm a := by
  simp only [binarysort]
  generalize hk : (if ok = 0 then 1 else ok) = k at h
  have := bsLoop_perm lt (a.take k) ((a.take n).drop k) ms
  generalize bsLoop lt (a.take k) ((a.take n).drop k) ms = R at this
  obtain ⟨s, ms'⟩ := R
  simp only at this ⊢
  refine (this.append_right _).trans ?_
  have e : a.take k ++ (a.take n).drop k = a.take n := by
    conv => rhs; rw [← List.take_append_drop k (a.take n)]
    rw [List.take_take, Nat.min_eq_left h]
  rw [e, List.take_append_drop]

/-! ## merge_lo / merge_hi / merge_at -/

theorem loLoop_perm (lt : α → α → Bool) :
    ∀ (fuel : Nat) (g : Bool) (mg ac bc : Nat) (out A B : List α) (ms : MS),
      (loLoop lt fuel g mg ac bc out A B ms).1.Perm (out ++ A ++ B) := by
  intro fuel
  induction fuel with
  | zero => intro g mg ac bc out A B ms; simp [loLoop]
  | succ fuel ih =>
    intro g mg ac bc out A B ms
    cases g with
    | false =>
      rcases A with _ | ⟨a, A'⟩ <;> rcases B with _ | ⟨b, B'⟩ <;> simp only [loLoop, islt]
      all_goals try simp
      split
      · split
        · subst_vars; perm_count
        · split
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
      · split
        · perm_count
        · split
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
    | true =>
      rcases B with _ | ⟨b, B'⟩ <;> simp only [loLoop]
      · simp
      generalize gallopRight lt b _ _ _ _ = G
      obtain ⟨k, ms1⟩ := G
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
      generalize gallopLeft lt a _ _ _ _ = G
      obtain ⟨k2, ms2⟩ := G
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

theorem mergeLo_perm (lt : α → α → Bool) (A B : List α) (ms : MS) :
    (mergeLo lt A B ms).1.Perm (A ++ B) := by
  rcases B with _ | ⟨b, B'⟩ <;> simp only [mergeLo]
  · simp
  split
  · subst_vars; perm_count
  split
  · perm_count
  · exact (loLoop_perm lt _ _ _ _ _ _ _ _ _).trans (by perm_count)

theorem hiLoop_perm (lt : α → α → Bool) :
    ∀ (fuel : Nat) (g : Bool) (mg ac bc : Nat) (out Ar Br : List α) (ms : MS),
      (hiLoop lt fuel g mg ac bc out Ar Br ms).1.Perm (Ar ++ Br ++ out) := by
  intro fuel
  induction fuel with
  | zero => intro g mg ac bc out Ar Br ms; simp only [hiLoop]; perm_count
  | succ fuel ih =>
    intro g mg ac bc out Ar Br ms
    cases g with
    | false =>
      rcases Ar with _ | ⟨a, Ar'⟩ <;> rcases Br with _ | ⟨b, Br'⟩ <;> simp only [hiLoop, islt]
      all_goals first | perm_count | skip
      by_cases hc : lt b a = true
      · simp only [hc, ↓reduceIte]
        split
        · subst_vars; perm_count
        · split
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        split
        · perm_count
        · split
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
          · exact (ih _ _ _ _ _ _ _ _).trans (by perm_count)
    | true =>
      rcases Br with _ | ⟨b, Br'⟩ <;> simp only [hiLoop]
      · perm_count
      generalize gallopRight lt b _ _ _ _ = G
      obtain ⟨k0, ms1⟩ := G
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
      generalize gallopLeft lt a _ _ _ _ = G
      obtain ⟨k2, ms2⟩ := G
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

theorem mergeHi_perm (lt : α → α → Bool) (A B : List α) (ms : MS) :
    (mergeHi lt A B ms).1.Perm (A ++ B) := by
  simp only [mergeHi]
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
  · exact (hiLoop_perm lt _ _ _ _ _ _ _ _ _).trans (by perm_count)

theorem mergeAt_perm (lt : α → α → Bool) (A B : List α) (ms : MS) :
    (mergeAt lt A B ms).1.Perm (A ++ B) := by
  rcases B with _ | ⟨b0, B'⟩ <;> simp only [mergeAt]
  · simp
  generalize gallopRight lt b0 _ _ _ _ = G
  obtain ⟨k, ms1⟩ := G
  simp only
  conv => rhs; rw [← List.take_append_drop k A]
  generalize A.take k = A0
  generalize A.drop k = A1
  split
  · next h => rw [List.getLast?_eq_none_iff] at h; perm_count
  rename_i alast _
  generalize gallopLeft lt alast _ _ _ _ = G
  obtain ⟨nb, ms2⟩ := G
  simp only
  split
  · perm_count
  generalize hBB : b0 :: B' = BB
  conv => rhs; rw [← List.take_append_drop nb BB]
  generalize BB.take nb = B0
  generalize BB.drop nb = B1
  split
  · exact (((mergeLo_perm lt A1 B0 _).append_left A0).append_right B1).trans (by perm_count)
  · exact (((mergeHi_perm lt A1 B0 _).append_left A0).append_right B1).trans (by perm_count)

theorem mergeAtArr_perm (lt : α → α → Bool) (base na nb : Nat) (st : List α × MS) :
    (mergeAtArr lt base na nb st).1.Perm st.1 := by
  obtain ⟨arr, ms⟩ := st
  simp only [mergeAtArr]
  have hm := mergeAt_perm lt ((arr.drop base).take na) ((arr.drop (base + na)).take nb) ms
  generalize mergeAt lt _ _ ms = M at hm
  obtain ⟨m, ms'⟩ := M
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

end PyLean.ListSort
