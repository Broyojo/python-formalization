import PyLean.ListSort.Search

/-!
# `merge_lo` is a stable merge

Preconditions, as established by `merge_at` (`listobject.c:2341-2346`, `:2645-2660`): both
runs sorted, the first item of B strictly below the first of A, and the last
item of A strictly above every item of B. Then `merge_lo` produces the stable
sort of `A ++ B`, whatever `min_gallop` is.
-/

namespace PyLean.ListSort

variable {α : Type}

theorem sorted_single (kf : α → Int) (x : α) : Sorted kf [x] := by simp [Sorted]

theorem sorted_sublist {kf : α → Int} {l l' : List α} (h : l'.Sublist l) (hs : Sorted kf l) :
    Sorted kf l' := hs.sublist h

theorem sorted_tail {kf : α → Int} {a : α} {l : List α} (h : Sorted kf (a :: l)) : Sorted kf l :=
  (sorted_cons.1 h).2

/-- Splitting a sorted `A` at the first item above/at `b`. -/
structure Split (kf : α → Int) (A T D : List α) (p : α → Bool) : Prop where
  eq : A = T ++ D
  sT : Sorted kf T
  sD : Sorted kf D
  TD : ∀ x ∈ T, ∀ y ∈ D, kf x ≤ kf y
  pT : ∀ x ∈ T, p x = true
  pD : ∀ x ∈ D, p x = false

theorem split_of (kf : α → Int) (A : List α) (p : α → Bool) (hs : Sorted kf A)
    (hp : A.Pairwise (fun x y => p y = true → p x = true)) :
    Split kf A (A.takeWhile p) (A.dropWhile p) p := by
  have e := (List.takeWhile_append_dropWhile (p := p) (l := A)).symm
  have hs' := hs
  rw [e] at hs'
  obtain ⟨h1, h2, h3⟩ := sorted_append.1 hs'
  exact ⟨e, h1, h2, h3, takeWhile_all p A, dropWhile_all_not p A hp⟩

/-- The common tail of the galloping branches of `merge_lo`. -/
theorem lo_gallop_compose (kf : α → Int) {T D A'' T2 D2 Rest : List α} {a b : α}
    (hT : Sorted kf T) (hTb : ∀ x ∈ T, kf x ≤ kf b) (hTD : ∀ x ∈ T, ∀ y ∈ D, kf x ≤ kf y)
    (hD : Sorted kf D) (hbD : ∀ x ∈ D, kf b < kf x) (hDa : D = a :: A'')
    (hB : Sorted kf (T2 ++ D2)) (hbB : ∀ y ∈ T2 ++ D2, kf b ≤ kf y)
    (hT2 : ∀ y ∈ T2, kf y < kf a) (hD2 : ∀ y ∈ D2, kf a ≤ kf y)
    (hR : SS kf (A'' ++ D2) Rest) :
    SS kf (T ++ D ++ (b :: (T2 ++ D2))) (T ++ (b :: (T2 ++ (a :: Rest)))) := by
  subst hDa
  obtain ⟨hT2s, hD2s, hT2D2⟩ := sorted_append.1 hB
  have hA'' : ∀ y ∈ A'', kf a ≤ kf y := (sorted_cons.1 hD).1
  have s1 : SS kf ((a :: A'') ++ D2) (a :: Rest) := by
    have := ss_prefix (X := [a]) (sorted_single kf a)
      (fun x hx y hy => by
        simp at hx; subst hx
        rcases List.mem_append.1 hy with hy | hy
        · exact hA'' y hy
        · exact hD2 y hy) hR
    simpa using this
  have s2 : SS kf ((a :: A'') ++ T2 ++ D2) (T2 ++ (a :: Rest)) :=
    ss_mid_prefix hT2s
      (fun x hx y hy => by
        have := hT2 x hx
        rcases List.mem_cons.1 hy with rfl | hy
        · exact this
        · have := hA'' y hy; omega)
      hT2D2 s1
  have s3 : SS kf ((a :: A'') ++ [b] ++ (T2 ++ D2)) (b :: (T2 ++ (a :: Rest))) := by
    have := ss_mid_prefix (A := a :: A'') (X := [b]) (Y := T2 ++ D2) (sorted_single kf b)
      (fun x hx y hy => by simp at hx; subst hx; exact hbD y hy)
      (fun x hx y hy => by simp at hx; subst hx; exact hbB y hy)
      (by simpa using s2)
    simpa using this
  have s4 := ss_prefix (X := T) hT
    (fun x hx y hy => by
      rcases List.mem_append.1 hy with hy | hy
      · rcases List.mem_append.1 hy with hy | hy
        · exact hTD x hx y hy
        · simp at hy; subst hy; exact hTb x hx
      · have := hTb x hx; have := hbB y hy; omega) s3
  simpa using s4

theorem loLoop_spec (kf : α → Int) :
    ∀ (fuel : Nat) (g : Bool) (mg ac bc : Nat) (out A B : List α) (ms : MS),
      Sorted kf A → Sorted kf B → 2 ≤ A.length → B ≠ [] →
      (∀ b ∈ B, ∀ x, A.getLast? = some x → kf b < kf x) → A.length + B.length ≤ fuel →
      ∃ R, (loLoop (ltOf kf) fuel g mg ac bc out A B ms).1 = out ++ R ∧ SS kf (A ++ B) R := by
  intro fuel
  induction fuel with
  | zero => intro g mg ac bc out A B ms _ _ hA _ _ hf; omega
  | succ fuel ih =>
    intro g mg ac bc out A B ms hA hB hlA hBne hlast hf
    cases g with
    | false =>
      match A, B, hlA, hBne with
      | a :: A', b :: B', hlA, _ =>
        simp only [loLoop, islt, ltOf]
        have haA : ∀ y ∈ A', kf a ≤ kf y := (sorted_cons.1 hA).1
        have hbB : ∀ y ∈ B', kf b ≤ kf y := (sorted_cons.1 hB).1
        by_cases hc : kf b < kf a
        · simp only [hc, decide_true, ↓reduceIte]
          have hbA : ∀ y ∈ a :: A', kf b < kf y := by
            intro y hy; rcases List.mem_cons.1 hy with rfl | hy
            · exact hc
            · have := haA y hy; omega
          split
          · rename_i hB'; subst hB'
            refine ⟨b :: a :: A', by simp, ?_⟩
            have := ss_mid_prefix (A := a :: A') (X := [b]) (Y := []) (sorted_single kf b)
              (fun x hx y hy => by simp at hx; subst hx; exact hbA y hy) (by simp) (by simpa using Sorted.ss hA)
            simpa using this
          · rename_i hB'
            have hrec : ∀ g' mg' ac' bc', ∃ R, (loLoop (ltOf kf) fuel g' mg' ac' bc' (out ++ [b]) (a :: A') B'
                { ms with ncmp := ms.ncmp + 1 }).1 = out ++ [b] ++ R ∧ SS kf (a :: A' ++ B') R :=
              fun g' mg' ac' bc' => ih _ _ _ _ _ _ _ _ hA (sorted_tail hB) hlA hB'
                (fun y hy x hx => hlast y (by simp [hy]) x hx) (by simp at hf ⊢; omega)
            have hfin : ∀ R, SS kf (a :: A' ++ B') R → SS kf (a :: A' ++ b :: B') (b :: R) := by
              intro R hR
              have := ss_mid_prefix (A := a :: A') (X := [b]) (Y := B') (sorted_single kf b)
                (fun x hx y hy => by simp at hx; subst hx; exact hbA y hy)
                (fun x hx y hy => by simp at hx; subst hx; exact hbB y hy) hR
              simpa using this
            split
            · obtain ⟨R, h1, h2⟩ := hrec true (mg + 1) 0 0
              exact ⟨b :: R, by simp [h1], hfin R h2⟩
            · obtain ⟨R, h1, h2⟩ := hrec false mg 0 (bc + 1)
              exact ⟨b :: R, by simp [h1], hfin R h2⟩
        · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
          have hab : ∀ y ∈ A' ++ b :: B', kf a ≤ kf y := by
            intro y hy
            rcases List.mem_append.1 hy with hy | hy
            · exact haA y hy
            · rcases List.mem_cons.1 hy with rfl | hy
              · omega
              · have := hbB y hy; omega
          split
          · rename_i hA'
            obtain ⟨x, rfl⟩ : ∃ x, A' = [x] := by
              match A', hA' with
              | [x], _ => exact ⟨x, rfl⟩
            refine ⟨a :: (b :: B' ++ [x]), by simp, ?_⟩
            have hsw : SS kf ([x] ++ b :: B') (b :: B' ++ [x]) :=
              ss_swap (Sorted.ss (sorted_single kf x)) (Sorted.ss hB)
                (fun y hy z hz => by simp at hz; subst hz; exact hlast y hy z (by simp))
            have := ss_prefix (X := [a]) (sorted_single kf a)
              (fun x hx y hy => by simp at hx; subst hx; exact hab y hy) hsw
            simpa using this
          · rename_i hA'
            have hA'2 : 2 ≤ A'.length := by
              have : A'.length ≠ 0 := by intro h; simp at hlA; omega
              omega
            have hrec : ∀ g' mg' ac' bc', ∃ R, (loLoop (ltOf kf) fuel g' mg' ac' bc' (out ++ [a]) A' (b :: B')
                { ms with ncmp := ms.ncmp + 1 }).1 = out ++ [a] ++ R ∧ SS kf (A' ++ b :: B') R :=
              fun g' mg' ac' bc' => ih _ _ _ _ _ _ _ _ (sorted_tail hA) hB hA'2 (by simp)
                (fun y hy x hx => hlast y hy x (by
                  cases A' with
                  | nil => simp at hA'2
                  | cons c A'' => rw [List.getLast?_cons_cons]; exact hx))
                (by simp at hf ⊢; omega)
            have hfin : ∀ R, SS kf (A' ++ b :: B') R → SS kf (a :: A' ++ b :: B') (a :: R) := by
              intro R hR
              have := ss_prefix (X := [a]) (sorted_single kf a)
                (fun x hx y hy => by simp at hx; subst hx; exact hab y hy) hR
              simpa using this
            split
            · obtain ⟨R, h1, h2⟩ := hrec true (mg + 1) 0 0
              exact ⟨a :: R, by simp [h1], hfin R h2⟩
            · obtain ⟨R, h1, h2⟩ := hrec false mg (ac + 1) 0
              exact ⟨a :: R, by simp [h1], hfin R h2⟩
    | true =>
      match B, hBne with
      | b :: B', _ =>
        simp only [loLoop]
        rw [gallopRight_spec kf b A _ 0 _ hA
          (fun i hi => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]) (by omega)]
        have hsp := split_of kf A _ hA (sorted_pairwise_le kf b hA)
        rw [(take_drop_of_takeWhile _ A).1, (take_drop_of_takeWhile _ A).2]
        generalize A.takeWhile (fun x => decide (kf x ≤ kf b)) = T at hsp
        generalize A.dropWhile (fun x => decide (kf x ≤ kf b)) = D at hsp
        obtain ⟨hAe, hTs, hDs, hTD, hpT, hpD⟩ := hsp
        subst hAe
        have hTb : ∀ x ∈ T, kf x ≤ kf b := fun x hx => by simpa using hpT x hx
        have hbD : ∀ x ∈ D, kf b < kf x := fun x hx => by have := hpD x hx; simp at this; omega
        have hbB : ∀ y ∈ B', kf b ≤ kf y := (sorted_cons.1 hB).1
        have hlastD : ∀ x, D.getLast? = some x → ∀ y ∈ b :: B', kf y < kf x := by
          intro x hx y hy
          exact hlast y hy x (by rw [List.getLast?_append, hx]; rfl)
        have hsortTB : Sorted kf (T ++ b :: B') := by
          refine sorted_append.2 ⟨hTs, hB, fun t ht y hy => ?_⟩
          have := hTb t ht
          rcases List.mem_cons.1 hy with rfl | hy
          · exact this
          · have := hbB y hy; omega
        by_cases hk1 : T.length ≠ 0 ∧ D.length = 1
        · -- CopyB after the first gallop
          simp only [hk1, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
          obtain ⟨x, rfl⟩ : ∃ x, D = [x] := by
            match D, hk1.2 with
            | [x], _ => exact ⟨x, rfl⟩
          refine ⟨T ++ (b :: B' ++ [x]), by simp, ?_⟩
          have hsw : SS kf ([x] ++ b :: B') (b :: B' ++ [x]) :=
            ss_swap (Sorted.ss (sorted_single kf x)) (Sorted.ss hB)
              (fun y hy z hz => by simp at hz; subst hz; exact hlastD z rfl y hy)
          have := ss_prefix (X := T) hTs
            (fun t ht y hy => by
              rcases List.mem_append.1 hy with hy | hy
              · exact hTD t ht y hy
              · have := hTb t ht
                rcases List.mem_cons.1 hy with rfl | hy
                · exact this
                · have := hbB y hy; omega) hsw
          simpa using this
        simp only [hk1, ↓reduceIte]
        by_cases hk0 : T.length ≠ 0 ∧ D.length = 0
        · simp only [hk0, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
          have hD0 : D = [] := List.eq_nil_of_length_eq_zero hk0.2
          subst hD0
          exact ⟨T ++ b :: B', by simp, by simpa using Sorted.ss hsortTB⟩
        simp only [hk0, ↓reduceIte]
        -- copy B[0]
        by_cases hB' : B' = []
        · simp only [hB', ↓reduceIte]
          subst hB'
          refine ⟨T ++ (b :: D), by simp, ?_⟩
          have hsw : SS kf (D ++ [b]) ([b] ++ D) :=
            ss_swap (Sorted.ss hDs) (Sorted.ss (sorted_single kf b))
              (fun y hy z hz => by simp at hy; subst hy; exact hbD z hz)
          have := ss_prefix (X := T) hTs
            (fun t ht y hy => by
              rcases List.mem_append.1 hy with hy | hy
              · exact hTD t ht y hy
              · simp at hy; subst hy; exact hTb t ht) hsw
          simpa using this
        simp only [hB', ↓reduceIte]
        match D, hDs, hTD, hbD, hlastD, hk1, hk0, hlA, hf with
        | [], _, _, _, _, _, _, _, _ =>
          simp only
          exact ⟨T ++ (b :: B'), by simp, by simpa using Sorted.ss hsortTB⟩
        | a :: A'', hDs, hTD, hbD, hlastD, hk1, hk0, hlA, hf =>
          simp only
          have hB's : Sorted kf B' := sorted_tail hB
          rw [gallopLeft_spec kf a B' _ 0 _ hB's
            (fun i hi => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
            (by cases B' <;> simp_all)]
          have hsp2 := split_of kf B' _ hB's (sorted_pairwise_lt kf a hB's)
          rw [(take_drop_of_takeWhile _ B').1, (take_drop_of_takeWhile _ B').2]
          generalize B'.takeWhile (fun x => decide (kf x < kf a)) = T2 at hsp2
          generalize B'.dropWhile (fun x => decide (kf x < kf a)) = D2 at hsp2
          obtain ⟨hBe, hT2s, hD2s, hT2D2, hpT2, hpD2⟩ := hsp2
          have hT2a : ∀ y ∈ T2, kf y < kf a := fun y hy => by simpa using hpT2 y hy
          have hD2a : ∀ y ∈ D2, kf a ≤ kf y := fun y hy => by have := hpD2 y hy; simp at this; omega
          have hbB2 : ∀ y ∈ T2 ++ D2, kf b ≤ kf y := fun y hy => hbB y (hBe ▸ hy)
          have hB2s : Sorted kf (T2 ++ D2) := hBe ▸ hB's
          have compose := fun Rest (hR : SS kf (A'' ++ D2) Rest) =>
            lo_gallop_compose kf hTs hTb hTD hDs hbD rfl hB2s hbB2 hT2a hD2a hR
          have hlastB : ∀ y ∈ D2, ∀ x, (a :: A'').getLast? = some x → kf y < kf x :=
            fun y hy x hx => hlastD x hx y (by rw [hBe]; simp [hy])
          rw [hBe]
          by_cases hk2 : T2.length ≠ 0 ∧ D2 = []
          · -- nb == 0 after the second gallop
            simp only [hk2, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
            obtain ⟨_, rfl⟩ := hk2
            refine ⟨T ++ (b :: (T2 ++ (a :: A''))), by simp, ?_⟩
            have := compose A'' (by simpa using Sorted.ss (sorted_tail hDs))
            simpa using this
          simp only [hk2, ↓reduceIte]
          -- copy A[0]
          by_cases hA'' : A''.length = 1
          · -- CopyB
            simp only [hA'', ↓reduceIte]
            obtain ⟨x, rfl⟩ : ∃ x, A'' = [x] := by
              match A'', hA'' with
              | [x], _ => exact ⟨x, rfl⟩
            refine ⟨T ++ (b :: (T2 ++ (a :: (D2 ++ [x])))), by simp, ?_⟩
            have hsw : SS kf ([x] ++ D2) (D2 ++ [x]) :=
              ss_swap (Sorted.ss (sorted_single kf x)) (Sorted.ss hD2s)
                (fun y hy z hz => by simp at hz; subst hz; exact hlastB y hy z (by simp))
            simpa using compose _ hsw
          simp only [hA'', ↓reduceIte]
          have hlen : 2 ≤ A''.length := by
            rcases A'' with _ | ⟨c, A3⟩
            · exfalso
              simp only [List.length_append, List.length_cons, List.length_nil, ne_eq, Nat.zero_add,
                and_true] at hk1 hlA
              omega
            · simp only [List.length_cons] at hA'' ⊢; omega
          have hD2ne : D2 ≠ [] := by
            intro h; subst h
            have hT20 : T2.length = 0 := by simp only [ne_eq, and_true] at hk2; omega
            have : T2 = [] := List.eq_nil_of_length_eq_zero hT20
            subst this; simp at hBe; exact hB' hBe
          have key : ∀ (g' : Bool) (mg' : Nat) (out' : List α) (ms' : MS),
              out' = out ++ (T ++ (b :: (T2 ++ [a]))) →
              ∃ R, (loLoop (ltOf kf) fuel g' mg' 0 0 out' A'' D2 ms').1 = out ++ R ∧
                SS kf (T ++ a :: A'' ++ b :: (T2 ++ D2)) R := by
            intro g' mg' out' ms' hout
            obtain ⟨R, h1, h2⟩ := ih g' mg' 0 0 out' A'' D2 ms' (sorted_tail hDs) hD2s hlen hD2ne
              (fun y hy x hx => hlastB y hy x (by
                cases A'' with
                | nil => simp at hlen
                | cons c A3 => rw [List.getLast?_cons_cons]; exact hx))
              (by
                have := congrArg List.length hBe
                simp only [List.length_append, List.length_cons] at hf this ⊢; omega)
            exact ⟨T ++ (b :: (T2 ++ (a :: R))), by rw [h1, hout]; simp, by simpa using compose R h2⟩
          split
          · exact key _ _ _ _ (by simp)
          · exact key _ _ _ _ (by simp)

/-- `merge_lo` under the preconditions `merge_at` establishes. -/
theorem mergeLo_spec (kf : α → Int) (A B : List α) (ms : MS) (hA : Sorted kf A) (hB : Sorted kf B)
    (hAne : A ≠ []) (hfirst : ∀ b, B.head? = some b → ∀ y ∈ A, kf b < kf y)
    (hlast : ∀ b ∈ B, ∀ x, A.getLast? = some x → kf b < kf x) (hBne : B ≠ []) :
    SS kf (A ++ B) (mergeLo (ltOf kf) A B ms).1 := by
  match B, hBne with
  | b :: B', _ =>
    have hbA : ∀ y ∈ A, kf b < kf y := hfirst b rfl
    have hbB : ∀ y ∈ B', kf b ≤ kf y := (sorted_cons.1 hB).1
    simp only [mergeLo]
    have hfin : ∀ R, SS kf (A ++ B') R → SS kf (A ++ b :: B') (b :: R) := by
      intro R hR
      have := ss_mid_prefix (A := A) (X := [b]) (Y := B') (sorted_single kf b)
        (fun x hx y hy => by simp at hx; subst hx; exact hbA y hy)
        (fun x hx y hy => by simp at hx; subst hx; exact hbB y hy) hR
      simpa using this
    split
    · rename_i hB'; subst hB'
      simpa using hfin A (by simpa using Sorted.ss hA)
    split
    · rename_i hB' hA1
      obtain ⟨x, rfl⟩ : ∃ x, A = [x] := by
        match A, hA1 with
        | [x], _ => exact ⟨x, rfl⟩
      have := ss_swap (Sorted.ss (sorted_single kf x)) (Sorted.ss hB)
        (fun y hy z hz => by simp at hz; subst hz; exact hlast y hy z (by simp))
      simpa using this
    · rename_i hB' hA1
      have h2 : 2 ≤ A.length := by
        have : A.length ≠ 0 := fun h => hAne (List.eq_nil_of_length_eq_zero h)
        omega
      obtain ⟨R, h1, h2⟩ := loLoop_spec kf (A.length + (b :: B').length + 1) false ms.minGallop 0 0 [b] A B' ms
        hA (sorted_tail hB) h2 hB'
        (fun y hy x hx => hlast y (by simp [hy]) x hx) (by simp only [List.length_cons]; omega)
      rw [h1]
      simpa using hfin R h2

end PyLean.ListSort
