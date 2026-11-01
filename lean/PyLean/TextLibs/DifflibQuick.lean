import PyLean.TextLibs.DifflibBlocks

/-!
`get_grouped_opcodes` on a new matcher, and `quick_ratio` as an upper bound on `ratio`.
-/

namespace PyLean.TextLibs.Difflib

open PyLean

/-- The opcodes that change something. -/
def nonEq (l : List Op) : List Op := l.filter (fun o => o.1 != .equal)

theorem nonEq_append (a b : List Op) : nonEq (a ++ b) = nonEq a ++ nonEq b := by simp [nonEq]

theorem nonEq_reverse_cons (o : Op) (g : List Op) : nonEq (o :: g).reverse = nonEq g.reverse ++ nonEq [o] := by
  simp [nonEq]

theorem nonEq_equal (i1 i2 j1 j2 : Nat) : nonEq [(.equal, i1, i2, j1, j2)] = [] := by
  simp [nonEq]

theorem fixFirst_ne (n : Nat) (l : List Op) : nonEq (fixFirst n l) = nonEq l := by
  cases l with
  | nil => rfl
  | cons o r =>
    obtain ⟨t, i1, i2, j1, j2⟩ := o
    cases t <;> simp [fixFirst, nonEq]

theorem fixLast_ne (n : Nat) : ∀ l : List Op, nonEq (fixLast n l) = nonEq l := by
  intro l
  induction l with
  | nil => rfl
  | cons o r ih =>
    cases r with
    | nil =>
      obtain ⟨t, i1, i2, j1, j2⟩ := o
      cases t <;> simp [fixLast, nonEq]
    | cons x y =>
      have e : fixLast n (o :: x :: y) = o :: fixLast n (x :: y) := by
        obtain ⟨t, i1, i2, j1, j2⟩ := o
        cases t <;> simp [fixLast]
      rw [e]
      have e2 : ∀ (a : Op) (l : List Op), nonEq (a :: l) = nonEq [a] ++ nonEq l := fun a l => nonEq_append [a] l
      rw [e2, ih, ← e2]

theorem group_ne (n : Nat) : ∀ (codes : List Op) (done : List (List Op)) (group : List Op),
    nonEq (groupLoop n codes done group).1.flatten ++ nonEq (groupLoop n codes done group).2.reverse =
      nonEq done.flatten ++ nonEq group.reverse ++ nonEq codes := by
  intro codes
  induction codes with
  | nil => intro done group; simp [groupLoop, nonEq]
  | cons o r ih =>
    intro done group
    obtain ⟨t, i1, i2, j1, j2⟩ := o
    simp only [groupLoop]
    have e2 : ∀ (a : Op) (l : List Op), nonEq (a :: l) = nonEq [a] ++ nonEq l := fun a l => nonEq_append [a] l
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨rfl, _⟩ := hc
      rw [ih]
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, nonEq_append,
        List.reverse_reverse, List.reverse_cons, List.reverse_nil, List.nil_append, nonEq_equal,
        List.append_assoc]
      rw [e2 (.equal, i1, i2, j1, j2) r, nonEq_equal]
      simp
    · rw [ih, nonEq_reverse_cons, e2 (t, i1, i2, j1, j2) r]
      simp [List.append_assoc]

theorem close_ne (g : List Op) : nonEq (closeGroup g).flatten = nonEq g.reverse := by
  cases g with
  | nil => rfl
  | cons o r =>
    cases r with
    | nil =>
      obtain ⟨t, i1, i2, j1, j2⟩ := o
      cases t <;> simp [closeGroup, nonEq]
    | cons x y =>
      have : closeGroup (o :: x :: y) = [(o :: x :: y).reverse] := by
        obtain ⟨t, i1, i2, j1, j2⟩ := o
        cases t <;> simp [closeGroup]
      rw [this]
      simp

/-- An `equal` of at most `2n`. -/
def Small (n : Nat) (g : List Op) : Prop := ∀ o ∈ g, o.1 = .equal → o.2.2.1 - o.2.1 ≤ 2 * n

theorem group_small (n : Nat) : ∀ (codes : List Op) (done : List (List Op)) (group : List Op),
    (∀ g ∈ done, Small n g) → Small n group →
    (∀ g ∈ (groupLoop n codes done group).1, Small n g) ∧ Small n (groupLoop n codes done group).2 := by
  intro codes
  induction codes with
  | nil => intro done group h1 h2; exact ⟨h1, h2⟩
  | cons o r ih =>
    intro done group h1 h2
    obtain ⟨t, i1, i2, j1, j2⟩ := o
    simp only [groupLoop]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨rfl, _⟩ := hc
      refine ih _ _ ?_ ?_
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact h1 g hg
        · simp only [List.mem_singleton] at hg
          subst hg
          intro o ho _
          simp only [List.mem_reverse, List.mem_cons] at ho
          rcases ho with rfl | ho
          · simp only; omega
          · exact h2 o ho ‹_›
      · intro o ho _
        simp only [List.mem_singleton] at ho
        subst ho
        simp only
        omega
    · rename_i hc
      refine ih _ _ h1 ?_
      intro o ho ht
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · simp only at ht
        subst ht
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, true_and] at hc
        simp only
        omega
      · exact h2 o ho ht

theorem close_small (n : Nat) (g : List Op) (h : Small n g) : ∀ x ∈ closeGroup g, Small n x := by
  have key : Small n g.reverse := fun o ho => h o (List.mem_reverse.mp ho)
  intro x hx
  cases g with
  | nil => simp [closeGroup] at hx
  | cons o r =>
    cases r with
    | nil =>
      obtain ⟨t, i1, i2, j1, j2⟩ := o
      cases t <;> simp [closeGroup] at hx <;> (subst hx; exact key)
    | cons a b =>
      have : closeGroup (o :: a :: b) = [(o :: a :: b).reverse] := by
        obtain ⟨t, i1, i2, j1, j2⟩ := o
        cases t <;> simp [closeGroup]
      rw [this] at hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact key

theorem grouped_of (s s1 : SM) (ops : List Op) (n : Nat) (h : getOpcodes s = .ok (s1, ops)) :
    ∃ s2 gs, getGrouped s n = .ok (s2, gs) ∧ nonEq gs.flatten = nonEq ops ∧ ∀ g ∈ gs, Small n g := by
  generalize hc : fixLast n (fixFirst n (if ops.isEmpty then [(Tag.equal, 0, 1, 0, 1)] else ops)) = codes
  refine ⟨if ops.isEmpty then s1 else { s1 with opcodes := some codes }, (groupLoop n codes [] []).1 ++
    closeGroup (groupLoop n codes [] []).2, ?_, ?_, ?_⟩
  · simp only [getGrouped, h, hc]
  · have h1 : nonEq codes = nonEq ops := by
      rw [← hc, fixLast_ne, fixFirst_ne]
      cases he : ops.isEmpty with
      | true =>
        have : ops = [] := by simpa using he
        subst this
        rfl
      | false => simp
    have h2 := group_ne n codes [] []
    simp only [List.flatten_nil, List.reverse_nil] at h2
    simp only [List.flatten_append, nonEq_append, close_ne]
    rw [h2, ← h1]
    simp [nonEq]
  · have h2 := group_small n codes [] [] (by simp) (by simp [Small])
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h2.1 g hg
    · exact close_small n _ h2.2 g hg

/-- `get_grouped_opcodes` on a new matcher, as `unified_diff` uses it: every change is in a group, in
order, and no `equal` in a group is longer than `2n`. -/
def GroupedLaw : Prop :=
  ∀ (isjunk : Option (Nat → Py Bool)) (a b : List Nat) (auto : Bool) (s : SM) (n : Nat), make isjunk a b auto = .ok s →
    ∃ s1 ops s2 gs, getOpcodes s = .ok (s1, ops) ∧ getGrouped s n = .ok (s2, gs) ∧
      nonEq gs.flatten = nonEq ops ∧ ∀ g ∈ gs, Small n g

theorem groupedLaw_proven : GroupedLaw := by
  intro isjunk a b auto s n h
  obtain ⟨hr, rfl, rfl⟩ := make_ready _ _ _ _ _ h
  obtain ⟨hb, ho⟩ := make_fresh _ _ _ _ _ h
  obtain ⟨l, h1, _, _⟩ := getBlocks_ok s hr hb
  have h2 := getOpcodes_of s _ _ ho h1
  obtain ⟨s2, gs, g1, g2, g3⟩ := grouped_of s _ _ n h2
  exact ⟨_, _, s2, gs, h2, g1, g2, g3⟩

/-! ### `quick_ratio` -/

/-- `numb`, `Lib/difflib.py:642-645`. -/
def bud (full : List (Nat × Nat)) (avail : List (Nat × Int)) (x : Nat) : Int :=
  match avail.lookup x with
  | some v => v
  | none => ((full.lookup x).getD 0 : Nat)

theorem quick_cons (full : List (Nat × Nat)) (e : Nat) (r : List Nat) (avail : List (Nat × Int)) (m : Nat) :
    quickLoop full (e :: r) avail m =
      quickLoop full r ((e, bud full avail e - 1) :: avail) (if bud full avail e > 0 then m + 1 else m) := rfl

theorem bud_cons (full : List (Nat × Nat)) (avail : List (Nat × Int)) (e x : Nat) (v : Int) :
    bud full ((e, v) :: avail) x = if x = e then v else bud full avail x := by
  by_cases h : x = e
  · subst h; simp [bud]
  · have : (x == e) = false := by simpa using h
    simp [bud, List.lookup, this, h]

theorem quick_ge (full : List (Nat × Nat)) : ∀ (a : List Nat) (avail : List (Nat × Int)) (m : Nat) (C : List Nat),
    C.Sublist a → (∀ x, C.count x = 0 ∨ (C.count x : Int) ≤ bud full avail x) →
    m + C.length ≤ quickLoop full a avail m := by
  intro a
  induction a with
  | nil =>
    intro avail m C hs _
    have : C = [] := List.sublist_nil.mp hs
    subst this
    simp [quickLoop]
  | cons e r ih =>
    intro avail m C hs hc
    rw [quick_cons]
    have hce := hc e
    generalize hf : bud full avail e = f at hce ⊢
    by_cases hpos : f > 0
    · rw [if_pos hpos]
      by_cases hmem : e ∈ C
      · have hsub : (C.erase e).Sublist r := by
          cases hs with
          | cons _ h => exact (List.erase_sublist).trans h
          | cons_cons _ h => simpa using h
        have h2 : 0 < C.count e := List.count_pos_iff.mpr hmem
        have := ih ((e, f - 1) :: avail) (m + 1) (C.erase e) hsub (by
          intro x
          rw [bud_cons]
          by_cases hx : x = e
          · subst hx
            rw [if_pos rfl, List.count_erase_self]
            omega
          · rw [if_neg hx, List.count_erase_of_ne hx]
            exact hc x)
        have hl := List.length_erase_of_mem hmem
        have h3 : 0 < C.length := List.length_pos_of_mem hmem
        omega
      · have hsub : C.Sublist r := by
          cases hs with
          | cons _ h => exact h
          | cons_cons _ h => exact absurd (by simp) hmem
        have := ih ((e, f - 1) :: avail) (m + 1) C hsub (by
          intro x
          rw [bud_cons]
          by_cases hx : x = e
          · subst hx
            exact .inl (List.count_eq_zero_of_not_mem hmem)
          · rw [if_neg hx]
            exact hc x)
        omega
    · rw [if_neg hpos]
      have hmem : e ∉ C := by
        intro hm
        have h2 : 0 < C.count e := List.count_pos_iff.mpr hm
        omega
      have hsub : C.Sublist r := by
        cases hs with
        | cons _ h => exact h
        | cons_cons _ h => exact absurd (by simp) hmem
      exact ih ((e, f - 1) :: avail) m C hsub (by
        intro x
        rw [bud_cons]
        by_cases hx : x = e
        · subst hx
          exact .inl (List.count_eq_zero_of_not_mem hmem)
        · rw [if_neg hx]
          exact hc x)

theorem countB_lookup : ∀ (b : List Nat) (m : List (Nat × Nat)) (x : Nat),
    ((countB b m).lookup x).getD 0 = (m.lookup x).getD 0 + b.count x := by
  intro b
  induction b with
  | nil => intro m x; simp [countB]
  | cons e r ih =>
    intro m x
    simp only [countB]
    rw [ih]
    by_cases h : x = e
    · subst h
      simp [List.lookup, List.count_cons]
      omega
    · have h1 : (x == e) = false := by simpa using h
      have h2 : (e == x) = false := by simpa using (Ne.symm h)
      simp [List.lookup, List.count_cons, h1, h2]

theorem drop_add_sublist (a : List Nat) (i p : Nat) : (a.drop (i + p)).Sublist (a.drop i) := by
  rw [← List.drop_drop]
  exact List.drop_sublist _ _

theorem chain_sub (a b : List Nat) : ∀ (l : List T) (i j : Nat), ChainFrom a b i j l →
    ∃ C : List Nat, C.length = sumBlocks l ∧ C.Sublist (a.drop i) ∧ C.Sublist (b.drop j) := by
  intro l
  induction l with
  | nil => intro _ _ _; exact ⟨[], rfl, List.nil_sublist _, List.nil_sublist _⟩
  | cons t r ih =>
    intro i j h
    obtain ⟨x, y, k⟩ := t
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    obtain ⟨C, c1, c2, c3⟩ := ih _ _ h5
    have hS : (a.drop x).take k = (b.drop y).take k := by
      apply List.ext_getElem?
      intro t
      by_cases ht : t < k
      · have := h4.2.2 t ht
        simpa [List.getElem?_take, ht] using this
      · simp [List.getElem?_take, ht]
    have hA : ((a.drop x).take k ++ C).Sublist (a.drop x) := by
      have e : a.drop x = (a.drop x).take k ++ a.drop (x + k) := by
        conv => lhs; rw [← List.take_append_drop k (a.drop x)]
        rw [List.drop_drop]
      rw [e]
      have e2 : ((a.drop x).take k ++ a.drop (x + k)).take k = (a.drop x).take k := by
        rw [← e]
      rw [e2]
      exact List.Sublist.append (List.Sublist.refl _) c2
    have hB : ((b.drop y).take k ++ C).Sublist (b.drop y) := by
      have e : b.drop y = (b.drop y).take k ++ b.drop (y + k) := by
        conv => lhs; rw [← List.take_append_drop k (b.drop y)]
        rw [List.drop_drop]
      rw [e]
      have e2 : ((b.drop y).take k ++ b.drop (y + k)).take k = (b.drop y).take k := by
        rw [← e]
      rw [e2]
      exact List.Sublist.append (List.Sublist.refl _) c3
    refine ⟨(a.drop x).take k ++ C, ?_, ?_, ?_⟩
    · have := h4.1
      simp only [List.length_append, List.length_take, List.length_drop, sumBlocks, c1]
      omega
    · have e : x = i + (x - i) := by omega
      exact hA.trans (by rw [e]; exact drop_add_sublist a i (x - i))
    · have e : y = j + (y - j) := by omega
      rw [hS]
      exact hB.trans (by rw [e]; exact drop_add_sublist b j (y - j))

/-- Docstring of `quick_ratio`: "an upper bound on ratio()", exactly, as counts of matches, on a new matcher. -/
def QuickBound : Prop :=
  ∀ (isjunk : Option (Nat → Py Bool)) (a b : List Nat) (auto : Bool) (s : SM), make isjunk a b auto = .ok s →
    ∃ s' m l, ratioPair s = .ok (s', m, l) ∧ m ≤ (quickPair s).2.1

theorem quickBound_proven : QuickBound := by
  intro isjunk a b auto s h
  obtain ⟨hr, rfl, rfl⟩ := make_ready _ _ _ _ _ h
  obtain ⟨hb, _⟩ := make_fresh _ _ _ _ _ h
  have hfull : s.fullb = none := (chainB_spec _ _ (make_ok _ _ _ _ _ h)).2.2.2.2.2.1
  obtain ⟨l, h1, h2, _⟩ := getBlocks_ok s hr hb
  refine ⟨_, _, _, ratioPair_of s _ _ h1, ?_⟩
  obtain ⟨C, c1, c2, c3⟩ := chain_sub _ _ l 0 0 h2
  simp only [List.drop_zero] at c2 c3
  have hq := quick_ge (countB s.b []) s.a [] 0 C c2 (by
    intro x
    have h3 := countB_lookup s.b [] x
    have h4 := c3.count_le x
    simp only [List.lookup, Option.getD_none, Nat.zero_add] at h3
    right
    simp only [bud, List.lookup]
    rw [h3]
    omega)
  simp only [quickPair, hfull]
  rw [sumBlocks_append]
  simp only [sumBlocks]
  omega

/-! ### `set_seqs` -/

theorem chainB_congr (x y : SM) (h1 : x.a = y.a) (h2 : x.b = y.b) (h3 : x.isjunk = y.isjunk) (h4 : x.autojunk = y.autojunk)
    (h5 : x.blocks = y.blocks) (h6 : x.opcodes = y.opcodes) (h7 : x.fullb = y.fullb) :
    (chainB x).2 = (chainB y).2 ∧ ((chainB y).2 = .ok () → (chainB x).1 = (chainB y).1) := by
  cases x
  cases y
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  simp only [chainB]
  split
  · rename_i he
    simp [he]
  · rename_i he
    simp [he]

/-- `set_seqs` on a matcher, with new objects, leaves what `__init__` would on those sequences, caches
included, and raises what `__init__` would raise. So nothing of the old sequences survives. -/
def SetSeqsFresh : Prop :=
  ∀ (isjunk : Option (Nat → Py Bool)) (a b a' b' : List Nat) (auto : Bool) (s : SM), make isjunk a b auto = .ok s →
    match make isjunk a' b' auto with
    | .ok s' => setSeqs s a' b' false false = (s', .ok ())
    | .error e => (setSeqs s a' b' false false).2 = .error e

theorem setSeqsFresh_proven : SetSeqsFresh := by
  intro isjunk a b a' b' auto s h
  obtain ⟨_, _, _, _, _, _, hj, ha⟩ := chainB_spec _ _ (make_ok _ _ _ _ _ h)
  simp only at hj ha
  obtain ⟨c1, c2⟩ := chainB_congr
    { s with a := a', blocks := none, opcodes := none, b := b', fullb := none }
    { a := a', b := b', isjunk, autojunk := auto, blocks := none, opcodes := none, fullb := none }
    rfl rfl hj ha rfl rfl rfl
  simp only [setSeqs, setSeq1, setSeq2, Bool.false_eq_true, if_false]
  unfold make
  simp only [setSeq2, Bool.false_eq_true, if_false]
  generalize hr : chainB { a := a', b := b', isjunk, autojunk := auto, blocks := none, opcodes := none, fullb := none } = r at c1 c2
  obtain ⟨st, res⟩ := r
  cases res with
  | error e => simpa using c1
  | ok u =>
    cases u
    have h1 := c2 rfl
    simp only at h1 c1
    exact Prod.ext h1 c1

end PyLean.TextLibs.Difflib
