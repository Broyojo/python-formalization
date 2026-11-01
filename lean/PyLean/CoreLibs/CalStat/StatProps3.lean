import PyLean.CoreLibs.CalStat.StatProps2

/-! Properties of the `statistics` mirror, continued: the medians and `median_grouped` over items
with an integer key (the same theorems `ListSort` proves `sorted` for), `mode` and `multimode` over
any equivalence, and `quantiles`. -/

namespace PyLean.CoreLibs.CalStat

open PyLean PyLean.ListSort

theorem pick_eq {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    pick l i = l[i] := by
  simp [pick, List.getD, List.getElem?_eq_getElem h]

theorem count_prefix {α : Type} (s : List α) (p : α → Bool) (k : Nat) (hk : k ≤ s.length)
    (h : ∀ (i : Nat) (hi : i < s.length), i < k → p s[i] = true) : k ≤ s.countP p := by
  have e : s = s.take k ++ s.drop k := (List.take_append_drop k s).symm
  have h1 : (s.take k).countP p = (s.take k).length := by
    apply List.countP_eq_length.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.length_take] at hi
    rw [List.getElem_take]
    exact h i (by omega) (by omega)
  have h2 : s.countP p = (s.take k).countP p + (s.drop k).countP p := by
    conv => lhs; rw [e]
    exact List.countP_append
  simp only [List.length_take] at h1
  omega

theorem count_suffix {α : Type} (s : List α) (p : α → Bool) (k : Nat) (hk : k ≤ s.length)
    (h : ∀ (i : Nat) (hi : i < s.length), k ≤ i → p s[i] = true) : s.length - k ≤ s.countP p := by
  have e : s = s.take k ++ s.drop k := (List.take_append_drop k s).symm
  have h1 : (s.drop k).countP p = (s.drop k).length := by
    apply List.countP_eq_length.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.length_drop] at hi
    rw [List.getElem_drop]
    exact h (k + i) (by omega) (by omega)
  have h2 : s.countP p = (s.take k).countP p + (s.drop k).countP p := by
    conv => lhs; rw [e]
    exact List.countP_append
  simp only [List.length_drop] at h1
  omega

theorem sorted_key {α : Type} {kf : α → Int} {s : List α} (hs : s.Pairwise (fun a b => kf a ≤ kf b))
    (i j : Nat) (hj : j < s.length) (hij : i ≤ j) : kf s[i] ≤ kf s[j] := by
  by_cases h : i = j
  · subst h; exact Int.le_refl _
  · exact List.pairwise_iff_getElem.mp hs i j (by omega) hj (by omega)

/-- `median_low` and `median_high` of data with an integer key: they are items of the data, in order,
the same item for odd sizes, and each really is a median: at least half of the items are `<=` the
high median and at least half are `>=` the low median. `median` is the middle item for an odd
size and the average of the two for an even size. The element type is arbitrary. -/
def MedianOrder : Prop :=
  ∀ (α : Type) [Inhabited α] (kf : α → Int) (xs : List α), xs ≠ [] →
    let s := listSort (ltOf kf) xs
    ∃ lo hi, medianLowSorted s = .ok lo ∧ medianHighSorted s = .ok hi ∧
      lo ∈ xs ∧ hi ∈ xs ∧ kf lo ≤ kf hi ∧ (xs.length % 2 = 1 → lo = hi) ∧
      xs.length ≤ 2 * xs.countP (fun e => decide (kf e ≤ kf hi)) ∧
      xs.length ≤ 2 * xs.countP (fun e => decide (kf lo ≤ kf e)) ∧
      ∀ avg : α → α → Py α,
        medianSorted avg s = if xs.length % 2 = 1 then .ok lo else avg lo hi

theorem medianOrder_proven : MedianOrder := by
  intro α _ kf xs hne s
  obtain ⟨hs, hp, -⟩ := sortIsStableSort_proven α kf xs
  have hlen : s.length = xs.length := hp.length_eq
  have hn := length_ne xs hne
  have hmid : s.length / 2 < s.length := by omega
  let li := if s.length % 2 = 1 then s.length / 2 else s.length / 2 - 1
  have hli : li ≤ s.length / 2 := by
    simp only [li]; split <;> omega
  have hlo : pick s li = s[li]'(by omega) := pick_eq _ _ (by omega)
  have hhi : pick s (s.length / 2) = s[s.length / 2] := pick_eq _ _ hmid
  have hs0 : s.length ≠ 0 := by omega
  have hmem : ∀ x ∈ s, x ∈ xs := fun x hx => hp.mem_iff.mp hx
  refine ⟨s[li]'(by omega), s[s.length / 2], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [medianLowSorted, hs0, if_false]
    by_cases h1 : s.length % 2 = 1
    · simp only [h1, if_true]
      rw [← hlo]; simp only [li, h1, if_true]
    · simp only [h1, if_false]
      rw [← hlo]; simp only [li, h1, if_false]
  · simp only [medianHighSorted, hs0, if_false, hhi]
  · exact hmem _ (List.getElem_mem _)
  · exact hmem _ (List.getElem_mem _)
  · exact sorted_key hs _ _ hmid hli
  · intro h1
    have : li = s.length / 2 := by simp only [li]; rw [if_pos (by omega)]
    simp only [this]
  · have h := count_prefix s (fun e => decide (kf e ≤ kf s[s.length / 2])) (s.length / 2 + 1)
      (by omega) (fun i hi hk => by
        simpa using sorted_key hs i (s.length / 2) hmid (by omega))
    rw [hp.countP_eq] at h
    omega
  · have h := count_suffix s (fun e => decide (kf (s[li]'(by omega)) ≤ kf e)) li (by omega)
      (fun i hi hk => by simpa using sorted_key hs li i hi hk)
    rw [hp.countP_eq] at h
    have : s.length - li ≥ (s.length + 1) / 2 := by
      simp only [li]; split <;> omega
    omega
  · intro avg
    simp only [medianSorted, hs0, if_false, hlen.symm]
    by_cases h1 : s.length % 2 = 1
    · simp only [h1, if_true, hhi]
      congr 2
      simp only [li, h1, if_true]
    · simp only [h1, if_false, hhi]
      rw [show pick s (s.length / 2 - 1) = s[li]'(by omega) by
        rw [← hlo]; simp only [li, h1, if_false]]

/-! ## `median_grouped` -/

theorem bl_le {α : Type} (lt : α → α → Bool) (a : List α) (x : α) (t : Nat)
    (h : ∀ (k : Nat) (hk : k < a.length), t ≤ k → lt a[k] x = false) :
    ∀ f lo hi, lo ≤ t → hi ≤ a.length → bisectLeftGo lt a x f lo hi ≤ t := by
  intro f
  induction f with
  | zero => intro lo hi h1 _; exact h1
  | succ f ih =>
    intro lo hi h1 h2
    simp only [bisectLeftGo]
    split
    · rename_i hlt
      have hm : (lo + hi) / 2 < a.length := by omega
      rw [List.getElem?_eq_getElem hm]
      simp only
      split
      · rename_i hv
        have : (lo + hi) / 2 < t := by
          refine Classical.byContradiction fun hc => ?_
          have := h _ hm (by omega)
          rw [this] at hv
          cases hv
        exact ih _ _ (by omega) h2
      · exact ih _ _ h1 (by omega)
    · exact h1

theorem br_gt {α : Type} (lt : α → α → Bool) (a : List α) (x : α) (t : Nat)
    (h : ∀ (k : Nat) (hk : k < a.length), k ≤ t → lt x a[k] = false) :
    ∀ f lo hi, t < hi → hi ≤ a.length → hi - lo < f →
      t < bisectRightGo lt a x f lo hi ∧ bisectRightGo lt a x f lo hi ≤ max lo a.length := by
  intro f
  induction f with
  | zero => intro lo hi _ _ h3; omega
  | succ f ih =>
    intro lo hi h1 h2 h3
    simp only [bisectRightGo]
    split
    · rename_i hlt
      have hm : (lo + hi) / 2 < a.length := by omega
      rw [List.getElem?_eq_getElem hm]
      simp only
      split
      · rename_i hv
        have : t < (lo + hi) / 2 := by
          refine Classical.byContradiction fun hc => ?_
          have := h _ hm (by omega)
          rw [this] at hv
          cases hv
        exact ih _ _ this (by omega) (by omega)
      · have := ih ((lo + hi) / 2 + 1) hi h1 h2 (by omega)
        omega
    · omega

/-- In `median_grouped` over sorted data the run of the middle value is never empty: with
`(i, j)` the bisections of statistics.py:449-450, `i <= n//2 < j <= n`, so the `f = j - i` the
formula divides by is positive and `ZeroDivisionError` cannot come out of ordered data.
(A NaN in the data can break this, since `sorted` then does not give sorted output.) Empty data
raises. -/
def GroupedBounds : Prop :=
  (∀ (α : Type) [Inhabited α] (kf : α → Int) (xs : List α), xs ≠ [] →
    let s := listSort (ltOf kf) xs
    let b := groupedBounds (ltOf kf) s
    b.1 ≤ s.length / 2 ∧ s.length / 2 < b.2 ∧ b.2 ≤ s.length) ∧
  (∀ i : Val, medianGrouped [] i = .error (.named "StatisticsError" "no median for empty data"))

theorem groupedBounds_proven : GroupedBounds := by
  refine ⟨?_, fun _ => by rfl⟩
  intro α _ kf xs hne s b
  obtain ⟨hs, hp, -⟩ := sortIsStableSort_proven α kf xs
  have hlen : s.length = xs.length := hp.length_eq
  have hn := length_ne xs hne
  have hmid : s.length / 2 < s.length := by omega
  have hx : pick s (s.length / 2) = s[s.length / 2] := pick_eq _ _ hmid
  have h1 : ∀ (k : Nat) (hk : k < s.length), s.length / 2 ≤ k →
      ltOf kf s[k] (pick s (s.length / 2)) = false := by
    intro k hk hle
    rw [hx]
    have h' : kf s[s.length / 2] ≤ kf s[k] := sorted_key hs _ _ hk hle
    simp only [ltOf, decide_eq_false_iff_not]
    exact Int.not_lt.mpr h'
  have h2 : ∀ (k : Nat) (hk : k < s.length), k ≤ s.length / 2 →
      ltOf kf (pick s (s.length / 2)) s[k] = false := by
    intro k hk hle
    rw [hx]
    have h' : kf s[k] ≤ kf s[s.length / 2] := sorted_key hs _ _ hmid hle
    simp only [ltOf, decide_eq_false_iff_not]
    exact Int.not_lt.mpr h'
  have hi := bl_le (ltOf kf) s _ _ h1 (s.length + 1) 0 s.length (by omega) (Nat.le_refl _)
  have hj := br_gt (ltOf kf) s _ _ h2 (s.length + 1)
    (bisectLeftGo (ltOf kf) s (pick s (s.length / 2)) (s.length + 1) 0 s.length) s.length hmid
    (Nat.le_refl _) (by omega)
  have hb1 : b.1 = bisectLeftGo (ltOf kf) s (pick s (s.length / 2)) (s.length + 1) 0 s.length := rfl
  have hb2 : b.2 = bisectRightGo (ltOf kf) s (pick s (s.length / 2)) (s.length + 1) b.1 s.length := rfl
  rw [← hb1] at hi hj
  rw [← hb2] at hj
  omega

/-! ## `mode`, `multimode` -/

theorem list_snoc_ind {α : Type} {P : List α → Prop} (h0 : P [])
    (h1 : ∀ D x, P D → P (D ++ [x])) (l : List α) : P l := by
  have key : ∀ r : List α, P r.reverse := by
    intro r
    induction r with
    | nil => exact h0
    | cons a as ih => simpa using h1 _ a ih
  simpa using key l.reverse

section Mode

variable {α : Type} (eq : α → α → Bool)

theorem keys_add (c : List (α × Nat)) (x : α) :
    (counterAdd eq c x).map Prod.fst =
      if c.any (fun p => eq p.1 x) then c.map Prod.fst else c.map Prod.fst ++ [x] := by
  induction c with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨k, n⟩ := p
    simp only [counterAdd, List.any_cons]
    by_cases h : eq k x = true
    · simp [h]
    · simp only [h, Bool.false_eq_true, if_false, List.map_cons, Bool.false_or, ih]
      split <;> simp

/-- The invariant of a `Counter` over data `D`. -/
structure CounterInv (D : List α) (c : List (α × Nat)) : Prop where
  count : ∀ p ∈ c, p.2 = D.countP (eq p.1)
  covers : ∀ y ∈ D, ∃ p ∈ c, eq p.1 y = true
  distinct : (c.map Prod.fst).Pairwise (fun a b => eq a b = false)

variable (hrefl : ∀ a, eq a a = true) (hsymm : ∀ a b, eq a b = eq b a)
  (htrans : ∀ a b c, eq a b = true → eq b c = true → eq a c = true)

include hsymm htrans in
theorem countP_congr (D : List α) (a b : α) (h : eq a b = true) :
    D.countP (eq a) = D.countP (eq b) := by
  apply List.countP_congr
  intro x _
  constructor
  · intro h1
    exact htrans b a x (by rw [hsymm]; exact h) h1
  · intro h1
    exact htrans a b x h h1

include hrefl hsymm htrans in
theorem count_add (D : List α) (x : α) (c : List (α × Nat))
    (h1 : ∀ p ∈ c, p.2 = D.countP (eq p.1))
    (h3 : (c.map Prod.fst).Pairwise (fun a b => eq a b = false))
    (h4 : c.any (fun p => eq p.1 x) = false → D.countP (eq x) = 0) :
    ∀ p ∈ counterAdd eq c x, p.2 = (D ++ [x]).countP (eq p.1) := by
  induction c with
  | nil =>
    intro p hp
    simp only [counterAdd, List.mem_singleton] at hp
    subst hp
    simp only [List.countP_append, List.countP_cons, List.countP_nil, hrefl, if_true]
    have := h4 rfl
    omega
  | cons q qs ih =>
    obtain ⟨k, n⟩ := q
    intro p hp
    simp only [counterAdd] at hp
    have hk := h1 (k, n) (by simp)
    simp only at hk
    simp only [List.map_cons, List.pairwise_cons] at h3
    by_cases hx : eq k x = true
    · rw [if_pos hx] at hp
      rcases List.mem_cons.mp hp with rfl | hm
      · simp only [List.countP_append, List.countP_cons, List.countP_nil, hx, if_true]
        omega
      · have hne : eq p.1 x = false := by
          refine Bool.eq_false_iff.mpr fun hc => ?_
          have : eq k p.1 = true := htrans k x p.1 hx (by rw [hsymm]; exact hc)
          have h5 := h3.1 p.1 (List.mem_map_of_mem hm)
          rw [this] at h5
          cases h5
        have := h1 p (List.mem_cons_of_mem _ hm)
        simp only [List.countP_append, List.countP_cons, List.countP_nil, hne, Bool.false_eq_true,
          if_false]
        omega
    · rw [if_neg hx] at hp
      have hxf : eq k x = false := by simpa using hx
      rcases List.mem_cons.mp hp with rfl | hm
      · simp only [List.countP_append, List.countP_cons, List.countP_nil, hxf, Bool.false_eq_true,
          if_false]
        omega
      · refine ih (fun q hq => h1 q (List.mem_cons_of_mem _ hq)) h3.2 ?_ p hm
        intro hany
        exact h4 (by simp only [List.any_cons, hxf, Bool.false_or]; exact hany)

include hrefl hsymm htrans in
theorem counter_inv (D : List α) : CounterInv eq D (counterOf eq D) := by
  refine list_snoc_ind (P := fun D => CounterInv eq D (counterOf eq D)) ?_ ?_ D
  · exact ⟨by simp [counterOf], by simp, by simp [counterOf]⟩
  · intro D x ih
    have hc : counterOf eq (D ++ [x]) = counterAdd eq (counterOf eq D) x := by
      simp [counterOf, List.foldl_append]
    rw [hc]
    generalize counterOf eq D = c at ih
    refine ⟨?_, ?_, ?_⟩
    · apply count_add eq hrefl hsymm htrans D x c ih.count ih.distinct
      intro hany
      apply List.countP_eq_zero.mpr
      intro y hy he
      obtain ⟨p, hp, hpy⟩ := ih.covers y hy
      have : eq p.1 x = true := htrans _ y _ hpy (by rw [hsymm]; exact he)
      have h2 : c.any (fun p => eq p.1 x) = true := List.any_eq_true.mpr ⟨p, hp, this⟩
      rw [hany] at h2
      cases h2
    · have hkeys := keys_add eq c x
      intro y hy
      have hmemkey : ∀ k ∈ c.map Prod.fst, ∃ p ∈ counterAdd eq c x, p.1 = k := by
        intro k hk
        have : k ∈ (counterAdd eq c x).map Prod.fst := by
          rw [hkeys]
          split <;> simp [hk]
        simpa using this
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨p, hp, hpy⟩ := ih.covers y hy
        obtain ⟨q, hq, hqk⟩ := hmemkey p.1 (List.mem_map_of_mem hp)
        exact ⟨q, hq, by rw [hqk]; exact hpy⟩
      · simp only [List.mem_singleton] at hy
        subst hy
        by_cases hany : c.any (fun p => eq p.1 y) = true
        · obtain ⟨p, hp, hpy⟩ := List.any_eq_true.mp hany
          obtain ⟨q, hq, hqk⟩ := hmemkey p.1 (List.mem_map_of_mem hp)
          exact ⟨q, hq, by rw [hqk]; exact hpy⟩
        · have : y ∈ (counterAdd eq c y).map Prod.fst := by
            rw [hkeys, if_neg hany]
            simp
          simp only [List.mem_map] at this
          obtain ⟨q, hq, hqk⟩ := this
          exact ⟨q, hq, by rw [hqk]; exact hrefl y⟩
    · rw [keys_add]
      split
      · exact ih.distinct
      · rename_i hany
        rw [List.pairwise_append]
        refine ⟨ih.distinct, by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        simp only [List.mem_map] at ha
        obtain ⟨p, hp, rfl⟩ := ha
        refine Bool.eq_false_iff.mpr fun hc => hany ?_
        exact List.any_eq_true.mpr ⟨p, hp, hc⟩

theorem find_keys (P : α → Bool) (hP : ∀ a b, eq a b = true → P a = P b) (D : List α) :
    D.find? P = ((counterOf eq D).map Prod.fst).find? P := by
  refine list_snoc_ind (P := fun D => D.find? P = ((counterOf eq D).map Prod.fst).find? P) rfl ?_ D
  · intro D x ih
    have hc : counterOf eq (D ++ [x]) = counterAdd eq (counterOf eq D) x := by
      simp [counterOf, List.foldl_append]
    rw [hc, keys_add, List.find?_append, ih]
    generalize counterOf eq D = c
    split
    · rename_i hany
      obtain ⟨p, hp, hpx⟩ := List.any_eq_true.mp hany
      by_cases hx : P x = true
      · have hk : P p.1 = true := by rw [hP _ _ hpx]; exact hx
        have hsome : (c.map Prod.fst).find? P ≠ none := by
          intro hn
          have := List.find?_eq_none.mp hn p.1 (List.mem_map_of_mem hp)
          rw [hk] at this
          exact this rfl
        cases hf : (c.map Prod.fst).find? P with
        | none => exact absurd hf hsome
        | some v => rfl
      · have : [x].find? P = none := by simp [List.find?, hx]
        rw [this]
        simp
    · rw [List.find?_append]

end Mode

theorem firstMax_split {α : Type} (rest : List (α × Nat)) (b : α × Nat) :
    ∃ pre r post, b :: rest = pre ++ r :: post ∧
      rest.foldl (fun best x => if x.2 > best.2 then x else best) b = r ∧
      (∀ y ∈ pre, y.2 < r.2) ∧ (∀ y ∈ post, y.2 ≤ r.2) := by
  induction rest generalizing b with
  | nil => exact ⟨[], b, [], rfl, rfl, by simp, by simp⟩
  | cons x xs ih =>
    simp only [List.foldl_cons]
    by_cases hx : x.2 > b.2
    · obtain ⟨pre, r, post, h1, h2, h3, h4⟩ := ih x
      rw [if_pos hx]
      refine ⟨b :: pre, r, post, by rw [List.cons_append, ← h1], h2, ?_, h4⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · have : x.2 ≤ r.2 := by
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at h1
            rw [h1.1]; omega
          | cons u us =>
            simp only [List.cons_append, List.cons.injEq] at h1
            have := h3 u (by simp)
            rw [h1.1]; omega
        omega
      · exact h3 y hy
    · rw [if_neg hx]
      obtain ⟨pre, r, post, h1, h2, h3, h4⟩ := ih b
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        refine ⟨[], b, x :: xs, rfl, h2, by simp, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · exact h4 y hy
      | cons u us =>
        simp only [List.cons_append, List.cons.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        refine ⟨b :: x :: us, r, post, rfl, h2, ?_, h4⟩
        intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with h | h | hy
        · rw [h]; exact h3 _ (by simp)
        · have := h3 _ (List.mem_cons_self)
          rw [h]
          omega
        · exact h3 y (List.mem_cons_of_mem _ hy)

theorem foldl_max_eq (l : List Nat) (init : Nat) (M : Nat) (h : ∀ y ∈ l, y ≤ M) (hi : init ≤ M)
    (hm : M ∈ l ∨ init = M) : l.foldl max init = M := by
  induction l generalizing init with
  | nil =>
    rcases hm with hm | hm
    · simp at hm
    · exact hm
  | cons a as ih =>
    simp only [List.foldl_cons]
    have ha := h a (by simp)
    apply ih (max init a) (fun y hy => h y (List.mem_cons_of_mem _ hy)) (by omega)
    rcases hm with hm | hm
    · rcases List.mem_cons.mp hm with hma | hmas
      · right; omega
      · left; exact hmas
    · right; omega

/-- `mode` and `multimode` for hashable items with `==` an equivalence (so NaNs are left out):
`multimode` lists exactly the items of maximal count, each class once, `mode` is its first item,
and that is the first such item encountered in the data, as the docstring says. Empty data: `mode`
raises and `multimode` gives `[]`. -/
def ModeSpec : Prop :=
  ∀ (α : Type) (eq : α → α → Bool), (∀ a, eq a a = true) → (∀ a b, eq a b = eq b a) →
    (∀ a b c, eq a b = true → eq b c = true → eq a c = true) →
    mode eq ([] : List α) = .error (.named "StatisticsError" "no mode for empty data") ∧
    multimode eq ([] : List α) = [] ∧
    ∀ data : List α, data ≠ [] → ∃ m ms, multimode eq data = m :: ms ∧ mode eq data = .ok m ∧
      (∀ y ∈ data, data.countP (eq y) ≤ data.countP (eq m)) ∧
      (∀ x ∈ m :: ms, data.countP (eq x) = data.countP (eq m)) ∧
      (∀ y ∈ data, data.countP (eq y) = data.countP (eq m) → ∃ x ∈ m :: ms, eq x y = true) ∧
      data.find? (fun y => data.countP (eq y) == data.countP (eq m)) = some m

theorem modeSpec_proven : ModeSpec := by
  intro α eq hrefl hsymm htrans
  refine ⟨rfl, rfl, ?_⟩
  intro data hne
  have inv := counter_inv eq hrefl hsymm htrans data
  have hcne : counterOf eq data ≠ [] := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil data hne
    obtain ⟨p, hp, -⟩ := inv.covers x hx
    intro h
    rw [h] at hp
    simp at hp
  have hfind := find_keys eq (fun y => data.countP (eq y) == (0 : Nat))
  generalize hc : counterOf eq data = c at inv hcne
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hcne
  obtain ⟨pre, r, post, h1, h2, h3, h4⟩ := firstMax_split rest a
  have hmemc : ∀ p, p ∈ pre ++ r :: post → p ∈ a :: rest := fun p hp => by rw [h1]; exact hp
  have hrc : r ∈ a :: rest := hmemc r (by simp)
  have hle : ∀ p ∈ a :: rest, p.2 ≤ r.2 := by
    intro p hp
    rw [h1] at hp
    rcases List.mem_append.mp hp with hp | hp
    · have := h3 p hp; omega
    · rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · exact h4 p hp
  have hmax : ((a :: rest).map Prod.snd).foldl max 0 = r.2 := by
    apply foldl_max_eq _ _ _ _ (by omega) (Or.inl _)
    · intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨p, hp, rfl⟩ := hy
      exact hle p hp
    · exact List.mem_map_of_mem hrc
  have hfilter : (a :: rest).filter (fun p => p.2 == r.2) = r :: post.filter (fun p => p.2 == r.2) := by
    rw [h1, List.filter_append, List.filter_cons]
    have : pre.filter (fun p => p.2 == r.2) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro y hy
      have := h3 y hy
      simp only [beq_iff_eq]
      omega
    simp [this]
  have hmode : mode eq data = .ok r.1 := by
    simp only [mode, hc, firstMax, h2]
  have hmulti : multimode eq data = r.1 :: (post.filter (fun p => p.2 == r.2)).map Prod.fst := by
    unfold multimode
    rw [hc]
    show ((a :: rest).filter (fun p => p.2 == ((a :: rest).map (·.2)).foldl max 0)).map (·.1) = _
    have hmax' : ((a :: rest).map (·.2)).foldl max 0 = r.2 := hmax
    rw [hmax', hfilter]
    rfl
  have hM : data.countP (eq r.1) = r.2 := (inv.count r hrc).symm
  refine ⟨r.1, _, hmulti, hmode, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨p, hp, hpy⟩ := inv.covers y hy
    rw [hM, ← countP_congr eq hsymm htrans data p.1 y hpy, ← inv.count p hp]
    exact hle p hp
  · intro x hx
    rw [hM]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hM
    · simp only [List.mem_map, List.mem_filter, beq_iff_eq] at hx
      obtain ⟨p, ⟨hp, hpr⟩, rfl⟩ := hx
      rw [← inv.count p (hmemc p (by simp [hp])), hpr]
  · intro y hy hcount
    obtain ⟨p, hp, hpy⟩ := inv.covers y hy
    have hp2 : p.2 = r.2 := by
      rw [inv.count p hp, countP_congr eq hsymm htrans data p.1 y hpy, hcount, hM]
    rw [h1] at hp
    rcases List.mem_append.mp hp with hp | hp
    · have := h3 p hp; omega
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨p.1, by simp, hpy⟩
      · refine ⟨p.1, ?_, hpy⟩
        simp only [List.mem_cons, List.mem_map, List.mem_filter, beq_iff_eq]
        exact Or.inr ⟨p, ⟨hp, hp2⟩, rfl⟩
  · rw [hM]
    have hP : ∀ u v, eq u v = true →
        (fun y => data.countP (eq y) == r.2) u = (fun y => data.countP (eq y) == r.2) v := by
      intro u v h
      simp only [countP_congr eq hsymm htrans data u v h]
    rw [find_keys eq _ hP data, hc, h1, List.map_append, List.find?_append, List.map_cons,
      List.find?_cons]
    have hnone : (pre.map Prod.fst).find? (fun y => data.countP (eq y) == r.2) = none := by
      apply List.find?_eq_none.mpr
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      have h5 := h3 p hp
      rw [← inv.count p (hmemc p (by simp [hp]))]
      simp only [beq_iff_eq]
      omega
    rw [hnone, hM]
    first
      | done
      | simp

/-! ## `quantiles` -/

theorem pick_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (i : Nat)
    (h : i < l.length) : pick (l.map f) i = f (pick l i) := by
  rw [pick_eq _ _ (by simpa using h), pick_eq _ _ h]
  simp

theorem vdiv_frac_intI (s : Rat) (n : Int) (hn : n ≠ 0) :
    vdiv (.frac s) (.int n) = .ok (.frac (s / (n : Rat))) := by
  have : (n : Rat) ≠ 0 := by simpa using hn
  simp only [vdiv, arith, divOp]
  rw [if_neg this]

theorem interp_bounds (a b N D : Rat) (hab : a ≤ b) (hN : 0 < N) (h0 : 0 ≤ D) (h1 : D ≤ N) :
    a ≤ (a * (N - D) + b * D) / N ∧ (a * (N - D) + b * D) / N ≤ b := by
  have h2 : 0 ≤ (b - a) * D := Rat.mul_nonneg (by grind) h0
  have h3 : 0 ≤ (b - a) * (N - D) := Rat.mul_nonneg (by grind) (by grind)
  constructor
  · refine Rat.not_lt.mp ?_
    rw [Rat.div_lt_iff hN]
    grind
  · refine Rat.not_lt.mp ?_
    rw [Rat.lt_div_iff hN]
    grind

theorem sortedQ {s : List Rat} (hs : s.Pairwise (· ≤ ·)) (i j : Nat) (hj : j < s.length)
    (hij : i ≤ j) : pick s i ≤ pick s j := by
  rw [pick_eq _ _ (by omega), pick_eq _ _ hj]
  by_cases h : i = j
  · subst h; exact Rat.le_refl
  · exact List.pairwise_iff_getElem.mp hs i j (by omega) hj (by omega)

theorem quantInc_eq (vs : List Rat) (n i m j δ : Int) (h2 : 2 ≤ vs.length) (h1 : 1 ≤ i) (hin : i < n)
    (hmm : m = (vs.length : Int) - 1) (hj : j = (i * m) / n) (hδ : δ = (i * m) % n) :
    0 ≤ j ∧ j.toNat + 1 < vs.length ∧ 0 ≤ δ ∧ δ < n ∧
      quantInclusive (vs.map .frac) n m i = .ok (.frac ((pick vs j.toNat * ((n - δ : Int) : Rat) +
        pick vs (j.toNat + 1) * (δ : Rat)) / (n : Rat))) := by
  have hn : 0 < n := by omega
  have hm : 0 < m := by omega
  have hp : 0 ≤ i * m := Int.mul_nonneg (by omega) (by omega)
  have hj0 : 0 ≤ j := by rw [hj]; exact Int.ediv_nonneg hp (by omega)
  have hlt : i * m < m * n := by
    rw [Int.mul_comm i m]
    exact Int.mul_lt_mul_of_pos_left hin hm
  have hjm : j < m := by rw [hj]; exact Int.ediv_lt_of_lt_mul hn hlt
  have hd0 : 0 ≤ δ := by rw [hδ]; exact Int.emod_nonneg _ (by omega)
  have hd1 : δ < n := by rw [hδ]; exact Int.emod_lt_of_pos _ hn
  have hidx : j.toNat + 1 < vs.length := by omega
  refine ⟨hj0, hidx, hd0, hd1, ?_⟩
  subst hj hδ
  simp only [quantInclusive, bind, Except.bind]
  rw [pick_map _ _ _ (by omega), pick_map _ _ _ hidx]
  have e1 : ∀ (x : Rat) (d : Int), vmul (.frac x) (.int d) = .ok (.frac (x * (d : Rat))) := fun _ _ => rfl
  have e3 : ∀ x y : Rat, vadd (.frac x) (.frac y) = .ok (.frac (x + y)) := fun _ _ => rfl
  simp only [e1, e3, vdiv_frac_intI _ n (by omega)]

/-- `quantiles(method='inclusive')` of sorted `Fraction` data: the indices stay in range for every
`1 <= i < n`, so no `IndexError` and no extrapolation: each cut point is the linear
interpolation between two neighbouring data points, hence between the minimum and the maximum
("The minimum value is treated as the 0th percentile and the maximum value as the 100th"). -/
def QuantilesInclusive : Prop :=
  ∀ (vs : List Rat) (n i : Int), vs.Pairwise (· ≤ ·) → 2 ≤ vs.length → 1 ≤ i → i < n →
    let m : Int := (vs.length : Int) - 1
    let j := (i * m) / n
    j.toNat + 1 < vs.length ∧ ∃ r, quantInclusive (vs.map .frac) n m i = .ok (.frac r) ∧
      pick vs j.toNat ≤ r ∧ r ≤ pick vs (j.toNat + 1) ∧
      pick vs 0 ≤ r ∧ r ≤ pick vs (vs.length - 1)

theorem quantilesInclusive_proven : QuantilesInclusive := by
  intro vs n i hs h2 h1 hin m j
  obtain ⟨hj0, hidx, hd0, hd1, heq⟩ := quantInc_eq vs n i m j ((i * m) % n) h2 h1 hin rfl rfl rfl
  refine ⟨hidx, _, heq, ?_⟩
  have hab := sortedQ hs j.toNat (j.toNat + 1) hidx (by omega)
  have hN : (0 : Rat) < (n : Rat) := Rat.intCast_pos.mpr (by omega)
  have hD0 : (0 : Rat) ≤ (((i * m) % n : Int) : Rat) := Rat.intCast_nonneg.mpr hd0
  have hD1 : (((i * m) % n : Int) : Rat) ≤ (n : Rat) := Rat.intCast_le_intCast.mpr (by omega)
  rw [Rat.intCast_sub]
  obtain ⟨b1, b2⟩ := interp_bounds _ _ _ _ hab hN hD0 hD1
  have l0 := sortedQ hs 0 j.toNat (by omega) (by omega)
  have l1 := sortedQ hs (j.toNat + 1) (vs.length - 1) (by omega) (by omega)
  exact ⟨b1, b2, Rat.le_trans l0 b1, Rat.le_trans b2 l1⟩

theorem quantExc_eq (vs : List Rat) (n i ld m j0 j δ : Int) (h2 : 2 ≤ vs.length) (hn : 0 < n)
    (hld : ld = vs.length) (hm : m = ld + 1) (hj0 : j0 = (i * m) / n)
    (hj : j = if j0 < 1 then 1 else if j0 > ld - 1 then ld - 1 else j0) (hδ : δ = i * m - j * n) :
    1 ≤ j ∧ j ≤ ld - 1 ∧
      quantExclusive (vs.map .frac) n ld m i = .ok (.frac ((pick vs (j.toNat - 1) * ((n - δ : Int) : Rat) +
        pick vs j.toNat * (δ : Rat)) / (n : Rat))) := by
  have hr1 : 1 ≤ j ∧ j ≤ ld - 1 := by
    rw [hj]
    split
    · omega
    · split <;> omega
  refine ⟨hr1.1, hr1.2, ?_⟩
  have hi1 : j.toNat < vs.length := by omega
  have hi0 : j.toNat - 1 < vs.length := by omega
  subst hj0 hj hδ
  simp only [quantExclusive, bind, Except.bind]
  rw [pick_map _ _ _ hi0, pick_map _ _ _ hi1]
  have e1 : ∀ (x : Rat) (d : Int), vmul (.frac x) (.int d) = .ok (.frac (x * (d : Rat))) := fun _ _ => rfl
  have e3 : ∀ x y : Rat, vadd (.frac x) (.frac y) = .ok (.frac (x + y)) := fun _ _ => rfl
  simp only [e1, e3, vdiv_frac_intI _ n (by omega)]

/-- `quantiles(method='exclusive')` of sorted `Fraction` data: the clamp at statistics.py:1217 keeps
`1 <= j <= len(data) - 1`, so both indices are valid for all `n`, also where `m*i/n` falls outside the
data; between the data points (`1 <= i*m//n <= len-1`) the cut point is the interpolation between the
neighbours. -/
def QuantilesExclusive : Prop :=
  ∀ (vs : List Rat) (n i : Int), vs.Pairwise (· ≤ ·) → 2 ≤ vs.length → 1 ≤ i → i < n →
    let ld : Int := vs.length
    let m := ld + 1
    let j0 := (i * m) / n
    let j : Int := if j0 < 1 then 1 else if j0 > ld - 1 then ld - 1 else j0
    1 ≤ j ∧ j ≤ ld - 1 ∧ ∃ r, quantExclusive (vs.map .frac) n ld m i = .ok (.frac r) ∧
      (1 ≤ j0 → j0 ≤ ld - 1 → pick vs (j.toNat - 1) ≤ r ∧ r ≤ pick vs j.toNat)

theorem quantilesExclusive_proven : QuantilesExclusive := by
  intro vs n i hs h2 h1 hin ld m j0 j
  have hn : 0 < n := by omega
  obtain ⟨hj1, hj2, heq⟩ := quantExc_eq vs n i ld m j0 j (i * m - j * n) h2 hn rfl rfl rfl rfl rfl
  refine ⟨hj1, hj2, _, heq, ?_⟩
  intro h3 h4
  have hjj : j = j0 := by
    simp only [j]
    rw [if_neg (by omega), if_neg (by omega)]
  have hab := sortedQ hs (j.toNat - 1) j.toNat (by omega) (by omega)
  have hN : (0 : Rat) < (n : Rat) := Rat.intCast_pos.mpr hn
  have hdiv := Int.emod_add_mul_ediv (i * m) n
  have hd : i * m - j * n = (i * m) % n := by
    rw [hjj]
    simp only [j0]
    rw [Int.mul_comm ((i * m) / n) n]
    omega
  have hd0 : 0 ≤ i * m - j * n := by rw [hd]; exact Int.emod_nonneg _ (by omega)
  have hd1 : i * m - j * n < n := by rw [hd]; exact Int.emod_lt_of_pos _ hn
  have hD0 : (0 : Rat) ≤ ((i * m - j * n : Int) : Rat) := Rat.intCast_nonneg.mpr hd0
  have hD1 : ((i * m - j * n : Int) : Rat) ≤ (n : Rat) := Rat.intCast_le_intCast.mpr (by omega)
  rw [Rat.intCast_sub n (i * m - j * n)]
  exact interp_bounds _ _ _ _ hab hN hD0 hD1

theorem pySorted_fracs (qs : List Rat) : ∃ rs : List Rat, pySorted (fracs qs) = .ok (fracs rs) ∧
    rs.length = qs.length := by
  by_cases h : (fracs qs).length ≥ 2
  · have hfind : (fracs qs).find? isDecNan = none := by
      apply List.find?_eq_none.mpr
      intro x hx
      simp only [fracs, List.mem_map] at hx
      obtain ⟨q, _, rfl⟩ := hx
      simp [isDecNan, Val.toN]
    have hall : (fracs qs).all (fun x => x.v.ordered) = true := by
      apply List.all_eq_true.mpr
      intro x hx
      simp only [fracs, List.mem_map] at hx
      obtain ⟨q, _, rfl⟩ := hx
      rfl
    have hperm := permAnyCompare_proven PyN (fun a b => vlt a.v b.v) (fracs qs) false
    generalize hl : listSort (fun a b => vlt a.v b.v) (fracs qs) false = l at hperm
    have hform : ∀ x ∈ l, (Val.frac (exactQ x.v)).toN = x := by
      intro x hx
      have := hperm.mem_iff.mp hx
      simp only [fracs, List.mem_map] at this
      obtain ⟨q, _, rfl⟩ := this
      rfl
    have hfr : fracs (l.map (fun x => exactQ x.v)) = l := by
      simp only [fracs, List.map_map]
      conv => rhs; rw [← List.map_id l]
      exact List.map_congr_left hform
    refine ⟨l.map (fun x => exactQ x.v), ?_, ?_⟩
    · unfold pySorted
      rw [if_pos h, hfind]
      simp only [hall, Bool.or_true, if_true]
      rw [hfr]
      exact congrArg Except.ok hl
    · simp only [List.length_map]
      rw [hperm.length_eq]
      simp [fracs]
  · refine ⟨qs, ?_, rfl⟩
    simp only [pySorted, h, if_false]

/-- The shape of `quantiles`: `n < 1` and empty data raise; one data point is repeated `n - 1` times;
two or more `Fraction`s give `n - 1` cut points with either method. -/
def QuantilesShape : Prop :=
  (∀ (d : List PyN) (n : Int) (me : String), n < 1 →
    quantiles d n me = .error (.named "StatisticsError" "n must be at least 1")) ∧
  (∀ (n : Int) (me : String), 1 ≤ n →
    quantiles [] n me = .error (.named "StatisticsError" "must have at least one data point")) ∧
  (∀ (qs : List Rat) (n : Int) (me : String), 1 ≤ n → 2 ≤ qs.length →
    (me = "inclusive" ∨ me = "exclusive") →
    ∃ r, quantiles (fracs qs) n me = .ok r ∧ r.length = (n - 1).toNat)

theorem mem_rangeI {a b x : Int} (h : x ∈ rangeI a b) : a ≤ x ∧ x < b := by
  simp only [rangeI, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  omega

theorem quantilesShape_proven : QuantilesShape := by
  refine ⟨?_, ?_, ?_⟩
  · intro d n me h
    simp [quantiles, h, bind, Except.bind, throw, throwThe, MonadExcept.throw]
    rfl
  · intro n me h
    have : ¬ n < 1 := by omega
    simp [quantiles, this, pySorted, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExcept.throw]
    rfl
  · intro qs n me h1 h2 hme
    obtain ⟨rs, hr, hlen⟩ := pySorted_fracs qs
    have hl : 2 ≤ rs.length := by omega
    have hvals : (fracs rs).map (·.v) = rs.map .frac := fracs_vals rs
    have hflen : (fracs rs).length = rs.length := by simp [fracs]
    have hn1 : ¬ n < 1 := by omega
    have hlt : ¬ ((rs.length : Int) < 2) := by omega
    have hrange : (rangeI 1 n).length = (n - 1).toNat := rangeI_length 1 n
    rcases hme with rfl | rfl
    · obtain ⟨r, hm, hrl, -⟩ := mapM_exists
        (fun i => Val.toN <$> quantInclusive (rs.map .frac) n ((rs.length : Int) - 1) i)
        (rangeI 1 n) (fun _ => True) (fun i hi => by
          obtain ⟨h3, h4⟩ := mem_rangeI hi
          obtain ⟨-, -, -, -, he⟩ := quantInc_eq rs n i _ _ _ hl h3 h4 rfl rfl rfl
          exact ⟨_, by rw [he]; rfl, trivial⟩)
      refine ⟨r, ?_, by omega⟩
      simp only [quantiles, hn1, if_false, bind, Except.bind, hr, hvals, hflen, hlt, if_true, hm,
        pure, Except.pure]
    · obtain ⟨r, hm, hrl, -⟩ := mapM_exists
        (fun i => Val.toN <$> quantExclusive (rs.map .frac) n (rs.length : Int) ((rs.length : Int) + 1) i)
        (rangeI 1 n) (fun _ => True) (fun i hi => by
          obtain ⟨h3, h4⟩ := mem_rangeI hi
          obtain ⟨-, -, he⟩ := quantExc_eq rs n i _ _ _ _ _ hl (by omega) rfl rfl rfl rfl rfl
          exact ⟨_, by rw [he]; rfl, trivial⟩)
      refine ⟨r, ?_, by omega⟩
      have hne : ("exclusive" = "inclusive") = False := by simp
      simp only [quantiles, hn1, if_false, bind, Except.bind, hr, hvals, hflen, hlt, hne, if_true, hm,
        pure, Except.pure]

/-- `method` should be checked: an unknown method raises `ValueError` whenever there is data. -/
def QuantilesMethodChecked : Prop :=
  ∀ (data : List PyN) (n : Int) (me : String), 1 ≤ n → data ≠ [] →
    me ≠ "inclusive" → me ≠ "exclusive" → (quantiles data n me).raises "ValueError"

/-- The single-point shortcut at statistics.py:1198-1201 returns before the method is looked at. -/
theorem quantilesMethodChecked_refuted : ¬QuantilesMethodChecked := by
  intro h
  obtain ⟨e, he, hc⟩ := h [(Val.int 1).toN] 4 "bogus" (by decide) (by simp) (by decide) (by decide)
  have : quantiles [(Val.int 1).toN] 4 "bogus" =
      .ok [(Val.int 1).toN, (Val.int 1).toN, (Val.int 1).toN] := by decide +kernel
  rw [this] at he
  cases he

end PyLean.CoreLibs.CalStat
