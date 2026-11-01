import PyLean.ListSort.Search
import PyLean.ListSort.Perm

/-!
# `count_run` leaves the stable sort of the run

For a consistent comparison, `count_run` returns `n` with the first `n` items of
the slice replaced by their stable sort (an ascending run, or a descending run
whose all-equal groups keep their order, plus an ascending extension), and the
rest untouched (`countRun_spec`).
-/

namespace PyLean.ListSort

variable {α : Type}

theorem le_getLast_of_sorted (kf : α → Int) :
    ∀ (L : List α) (h : L ≠ []), Sorted kf L → ∀ x ∈ L, kf x ≤ kf (L.getLast h) := by
  intro L h hs x hx
  have e := List.dropLast_concat_getLast h
  rw [← e] at hs hx
  obtain ⟨_, _, h3⟩ := sorted_append.1 hs
  rcases List.mem_append.1 hx with hx | hx
  · exact h3 x hx _ (by simp)
  · simp at hx; rw [hx]; exact Int.le_refl _

theorem ascTake_sorted (kf : α → Int) :
    ∀ (prev : α) (rest : List α) (ms : MS),
      Sorted kf (prev :: (ascTake (ltOf kf) prev rest ms).1) ∧
        ∀ z r', (ascTake (ltOf kf) prev rest ms).2.1 = z :: r' →
          kf z < kf ((prev :: (ascTake (ltOf kf) prev rest ms).1).getLast (by simp))
  | prev, [], ms => by simp [ascTake, Sorted]
  | prev, z :: rest, ms => by
    simp only [ascTake, islt, ltOf]
    by_cases hc : kf z < kf prev
    · simp only [hc, decide_true, ↓reduceIte]
      refine ⟨by simp [Sorted], ?_⟩
      intro z' r' h; simp at h; obtain ⟨rfl, rfl⟩ := h; simpa using hc
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
      have ih := ascTake_sorted kf z rest { ms with ncmp := ms.ncmp + 1 }
      refine ⟨?_, ?_⟩
      · apply sorted_cons.2 ⟨?_, ih.1⟩
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · omega
        · have := (sorted_cons.1 ih.1).1 y hy; omega
      · intro z' r' h
        have := ih.2 z' r' h
        simpa [List.getLast_cons] using this

theorem descLoop_spec (kf : α → Int) :
    ∀ (rest done grp : List α) (prev : α) (ms : MS) (D : List α), SS kf D done.reverse →
      (∀ g ∈ grp, kf g = kf prev) → (∀ d ∈ D, kf prev < kf d) →
      ∃ c, rest = c ++ (descLoop (ltOf kf) done grp prev rest ms).2.1 ∧
        SS kf (D ++ grp ++ c) (descLoop (ltOf kf) done grp prev rest ms).1.reverse
  | [], done, grp, prev, ms, D, hD, hg, hlt => by
    refine ⟨[], by simp [descLoop], ?_⟩
    simp only [descLoop, List.reverse_append, List.reverse_reverse, List.append_nil]
    exact ss_swap hD (Sorted.ss (sorted_of_const hg)) (fun x hx y hy => by rw [hg x hx]; exact hlt y hy)
  | z :: rest, done, grp, prev, ms, D, hD, hg, hlt => by
    have hstep : SS kf (D ++ grp) (done ++ grp.reverse).reverse := by
      simp only [List.reverse_append, List.reverse_reverse]
      exact ss_swap hD (Sorted.ss (sorted_of_const hg)) (fun x hx y hy => by rw [hg x hx]; exact hlt y hy)
    simp only [descLoop, islt, ltOf]
    by_cases hc : kf z < kf prev
    · simp only [hc, decide_true, ↓reduceIte]
      obtain ⟨c, hc1, hc2⟩ := descLoop_spec kf rest (done ++ grp.reverse) [z] z
        { minGallop := ms.minGallop, ncmp := ms.ncmp + 1 } (D ++ grp) hstep
        (by simp) (by
          intro d hd
          rcases List.mem_append.1 hd with hd | hd
          · have := hlt d hd; omega
          · rw [hg d hd]; exact hc)
      refine ⟨z :: c, by simp [← hc1], ?_⟩
      simpa using hc2
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hd : kf prev < kf z
      · simp only [hd, decide_true, ↓reduceIte]
        exact ⟨[], by simp, by simpa using hstep⟩
      · simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte]
        have heq : kf z = kf prev := by omega
        obtain ⟨c, hc1, hc2⟩ := descLoop_spec kf rest done (grp ++ [z]) z
          { minGallop := ms.minGallop, ncmp := ms.ncmp + 1 + 1 } D hD
          (by
            intro g hg'
            rcases List.mem_append.1 hg' with hg' | hg'
            · rw [hg g hg', heq]
            · simp at hg'; rw [hg'])
          (by intro d hd; rw [heq]; exact hlt d hd)
        refine ⟨z :: c, by simp [← hc1], ?_⟩
        simpa using hc2

/-- `count_run` on a non-empty slice `xs` returns `n` and leaves the stable sort
of `xs[:n]` followed by `xs[n:]`. -/
theorem countRun_spec (kf : α → Int) (xs : List α) (ms : MS) (hne : xs ≠ []) :
    ∃ R, (countRun (ltOf kf) xs ms).2.1 = R ++ xs.drop (countRun (ltOf kf) xs ms).1 ∧
      SS kf (xs.take (countRun (ltOf kf) xs ms).1) R := by
  match xs, hne with
  | x0 :: rest, _ =>
    simp only [countRun]
    have hsp := ascTake_spec (ltOf kf) x0 rest ms
    have hso := ascTake_sorted kf x0 rest ms
    generalize ascTake (ltOf kf) x0 rest ms = A at hsp hso
    obtain ⟨t, r, ms1⟩ := A
    simp only at hsp hso
    subst hsp
    obtain ⟨hsort, hbrk⟩ := hso
    match r, hbrk with
    | [], _ =>
      refine ⟨x0 :: t, by simp, ?_⟩
      simpa using Sorted.ss hsort
    | y :: r', hbrk =>
      have hy := hbrk y r' rfl
      simp only
      -- all of `asc` has key `kf x0` unless the early return fires
      have hcases : ∃ early ms2, (if (x0 :: t).length > 1 then
          islt (ltOf kf) ms1 x0 ((x0 :: t).getLast (by simp)) else (false, ms1)) = (early, ms2) ∧
          (early = false → ∀ a ∈ x0 :: t, kf a = kf x0) := by
        split
        · refine ⟨_, _, rfl, fun he a ha => ?_⟩
          simp only [islt, ltOf, decide_eq_false_iff_not] at he
          have h1 := le_getLast_of_sorted kf (x0 :: t) (by simp) hsort a ha
          have h2 : kf x0 ≤ kf a := by
            rcases List.mem_cons.1 ha with rfl | ha
            · exact Int.le_refl _
            · exact (sorted_cons.1 hsort).1 a ha
          omega
        · rename_i hlen
          refine ⟨_, _, rfl, fun _ a ha => ?_⟩
          have : t = [] := by cases t <;> simp_all
          subst this; simp at ha; rw [ha]
      obtain ⟨early, ms2, hE, hall⟩ := hcases
      rw [hE]
      cases early with
      | true =>
        simp only [↓reduceIte]
        refine ⟨x0 :: t, ?_, ?_⟩
        · simp
        · have : (x0 :: (t ++ y :: r')).take (x0 :: t).length = x0 :: t := by simp
          rw [this]; exact Sorted.ss hsort
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hall := hall rfl
        have hD : SS kf (x0 :: t) (x0 :: t).reverse.reverse := by
          rw [List.reverse_reverse]; exact Sorted.ss hsort
        have hlast : kf ((x0 :: t).getLast (by simp)) = kf x0 := hall _ (List.getLast_mem _)
        obtain ⟨c, hc1, hc2⟩ := descLoop_spec kf r' (x0 :: t).reverse [y] y ms2 (x0 :: t) hD
          (by simp) (by intro d hd; rw [hall d hd]; omega)
        generalize descLoop (ltOf kf) (x0 :: t).reverse [y] y r' ms2 = Dl at hc1 hc2
        obtain ⟨pre, r2, ms3⟩ := Dl
        simp only at hc1 hc2 ⊢
        subst hc1
        match hrun : pre.reverse, hc2 with
        | [], hc2 => have := hc2.length; simp at this
        | w :: ws, hc2 =>
          simp only
          have hsp2 := ascTake_spec (ltOf kf) ((w :: ws).getLast (by simp)) r2 ms3
          have hso2 := ascTake_sorted kf ((w :: ws).getLast (by simp)) r2 ms3
          generalize ascTake (ltOf kf) ((w :: ws).getLast (by simp)) r2 ms3 = E at hsp2 hso2
          obtain ⟨e, r3, ms4⟩ := E
          simp only at hsp2 hso2
          subst hsp2
          have hlen := hc2.length
          refine ⟨(w :: ws) ++ e, ?_, ?_⟩
          · have hxs : x0 :: (t ++ y :: (c ++ (e ++ r3))) = (x0 :: t ++ [y] ++ c ++ e) ++ r3 := by simp
            have : (x0 :: (t ++ y :: (c ++ (e ++ r3)))).drop ((w :: ws).length + e.length) = r3 := by
              rw [hxs, List.drop_left' (by rw [hlen]; simp; omega)]
            rw [this, List.append_assoc]
          · have hxs : x0 :: (t ++ y :: (c ++ (e ++ r3))) = (x0 :: t ++ [y] ++ c ++ e) ++ r3 := by simp
            have : (x0 :: (t ++ y :: (c ++ (e ++ r3)))).take ((w :: ws).length + e.length) =
                (x0 :: t ++ [y] ++ c) ++ e := by
              rw [hxs, List.take_left' (by rw [hlen]; simp; omega)]
            rw [this]
            have hes : Sorted kf e := (sorted_cons.1 hso2.1).2
            apply ss_suffix hes _ hc2
            intro a ha b hb
            have h1 := le_getLast_of_sorted kf (w :: ws) (by simp) hc2.1 a ((hc2.2.mem a).1 ha)
            have h2 := (sorted_cons.1 hso2.1).1 b hb
            omega

end PyLean.ListSort
