import PyLean.TextLibs.DifflibTextProps

/-!
A hunk of `unified_diff` is a correct piece of a patch: its context and removed lines are the slice of `a`
that its header names, and its context and added lines the slice of `b`. This needs the groups of
`get_grouped_opcodes` to be runs of opcodes with no gap, which trimming the context keeps them.
-/

namespace PyLean.TextLibs.Difflib

open PyLean

set_option linter.unusedSimpArgs false

variable (a b : List LineO)

/-- An opcode in range, whose tag says what the two slices are. Trimming can leave an `equal` empty. -/
def Seg : Op → Prop
  | (t, i1, i2, j1, j2) =>
    i1 ≤ i2 ∧ i2 ≤ a.length ∧ j1 ≤ j2 ∧ j2 ≤ b.length ∧
      match t with
      | .equal => i2 - i1 = j2 - j1 ∧ sliceL a i1 i2 = sliceL b j1 j2
      | .delete => j1 = j2
      | .insert => i1 = i2
      | .replace => True

/-- Each opcode starts where the one before it stopped. -/
def Chn : List Op → Prop
  | [] => True
  | [_] => True
  | (_, _, i2, _, j2) :: (t, i1, i3, j1, j3) :: r => i2 = i1 ∧ j2 = j1 ∧ Chn ((t, i1, i3, j1, j3) :: r)

theorem chn_tail {x : Op} {r : List Op} (h : Chn (x :: r)) : Chn r := by
  obtain ⟨_, _, _, _, _⟩ := x
  cases r with
  | nil => trivial
  | cons y t =>
    obtain ⟨_, _, _, _, _⟩ := y
    exact h.2.2

/-- A run of opcodes that is `l`, then `x`. -/
theorem chn_snoc : ∀ (l : List Op) (x : Op), Chn l → (∀ p, l.getLast? = some p → p.2.2.1 = x.2.1 ∧ p.2.2.2.2 = x.2.2.2.1) →
    Chn (l ++ [x]) := by
  intro l
  induction l with
  | nil => intro x _ _; trivial
  | cons y r ih =>
    intro x h1 h2
    obtain ⟨t, i1, i2, j1, j2⟩ := y
    cases r with
    | nil =>
      obtain ⟨t2, a1, a2, b1, b2⟩ := x
      obtain ⟨e1, e2⟩ := h2 _ rfl
      simp only at e1 e2
      exact ⟨e1, e2, trivial⟩
    | cons z r' =>
      obtain ⟨t2, a1, a2, b1, b2⟩ := z
      obtain ⟨e1, e2, e3⟩ := h1
      refine ⟨e1, e2, ?_⟩
      apply ih x e3
      intro p hp
      exact h2 p (by simpa [List.getLast?_cons_cons] using hp)

theorem cover_seg (L : Lawful lineOps (a ++ b)) : ∀ (ops : List Op) (i j : Nat),
    Cover (a.map (cls lineOps (a ++ b))) (b.map (cls lineOps (a ++ b))) i j ops → (∀ o ∈ ops, Seg a b o) ∧ Chn ops := by
  intro ops
  induction ops with
  | nil => intro _ _ _; exact ⟨by simp, trivial⟩
  | cons op r ih =>
    intro i j hc
    obtain ⟨t, i1, i2, j1, j2⟩ := op
    simp only [Cover, List.length_map] at hc
    obtain ⟨rfl, rfl, h3, h4, h5, h6⟩ := hc
    obtain ⟨r1, r2⟩ := ih i2 j2 h6
    constructor
    · intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · cases t with
        | equal =>
          simp only [TagOk] at h5
          obtain ⟨q1, q2, q3⟩ := h5
          have hs := eqs_slice line_eq ((eqsO_iff L _ _ _).mpr q3)
          rw [show i1 + (i2 - i1) = i2 by omega, show j1 + (i2 - i1) = j2 by omega] at hs
          exact ⟨by omega, h3, by omega, h4, q2, hs⟩
        | replace =>
          simp only [TagOk] at h5
          exact ⟨by omega, h3, by omega, h4, trivial⟩
        | delete =>
          simp only [TagOk] at h5
          obtain ⟨q1, rfl⟩ := h5
          exact ⟨by omega, h3, Nat.le_refl _, h4, rfl⟩
        | insert =>
          simp only [TagOk] at h5
          obtain ⟨rfl, q1⟩ := h5
          exact ⟨Nat.le_refl _, h3, by omega, h4, rfl⟩
      · exact r1 o ho
    · cases r with
      | nil => trivial
      | cons y t' =>
        obtain ⟨t2, a1, a2, b1, b2⟩ := y
        simp only [Cover] at h6
        exact ⟨h6.1.symm, h6.2.1.symm, r2⟩

theorem len_slice {β : Type} (l : List β) (i j : Nat) (h : j ≤ l.length) : (sliceL l i j).length = j - i := by
  simp only [sliceL, List.length_take, List.length_drop]
  omega

/-- Cutting an `equal` at the same place on both sides leaves two `equal`s. -/
theorem cut_eq (i1 i2 j1 j2 d : Nat) (h1 : i2 ≤ a.length) (h2 : j2 ≤ b.length) (hd : d ≤ i2 - i1) (hl : i2 - i1 = j2 - j1)
    (hs : sliceL a i1 i2 = sliceL b j1 j2) (h3 : i1 ≤ i2) (h4 : j1 ≤ j2) :
    sliceL a i1 (i1 + d) = sliceL b j1 (j1 + d) ∧ sliceL a (i1 + d) i2 = sliceL b (j1 + d) j2 := by
  have e1 := slice_join a i1 (i1 + d) i2 (by omega) (by omega)
  have e2 := slice_join b j1 (j1 + d) j2 (by omega) (by omega)
  rw [hs, ← e2] at e1
  have l1 : (sliceL a i1 (i1 + d)).length = (sliceL b j1 (j1 + d)).length := by
    rw [len_slice _ _ _ (by omega), len_slice _ _ _ (by omega)]
    omega
  exact List.append_inj e1 l1

theorem seg_front {t : Tag} {i1 i2 j1 j2 n : Nat} (h : Seg a b (.equal, i1, i2, j1, j2)) :
    Seg a b (.equal, max i1 (i2 - n), i2, max j1 (j2 - n), j2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hd : max i1 (i2 - n) = i1 + (max i1 (i2 - n) - i1) := by omega
  have hd2 : max j1 (j2 - n) = j1 + (max i1 (i2 - n) - i1) := by omega
  obtain ⟨_, e⟩ := cut_eq a b i1 i2 j1 j2 (max i1 (i2 - n) - i1) h2 h4 (by omega) h5 h6 h1 h3
  rw [← hd, ← hd2] at e
  exact ⟨by omega, h2, by omega, h4, by omega, e⟩

theorem seg_back {i1 i2 j1 j2 n : Nat} (h : Seg a b (.equal, i1, i2, j1, j2)) :
    Seg a b (.equal, i1, min i2 (i1 + n), j1, min j2 (j1 + n)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hd : min i2 (i1 + n) = i1 + (min i2 (i1 + n) - i1) := by omega
  have hd2 : min j2 (j1 + n) = j1 + (min i2 (i1 + n) - i1) := by omega
  obtain ⟨e, _⟩ := cut_eq a b i1 i2 j1 j2 (min i2 (i1 + n) - i1) h2 h4 (by omega) h5 h6 h1 h3
  rw [← hd, ← hd2] at e
  exact ⟨by omega, by omega, by omega, by omega, by omega, e⟩

theorem fixFirst_ok (n : Nat) : ∀ l : List Op, (∀ o ∈ l, Seg a b o) → Chn l → (∀ o ∈ fixFirst n l, Seg a b o) ∧ Chn (fixFirst n l) := by
  intro l h1 h2
  match l, h1, h2 with
  | [], _, _ => exact ⟨by simp [fixFirst], trivial⟩
  | (.equal, i1, i2, j1, j2) :: r, h1, h2 =>
    simp only [fixFirst]
    constructor
    · intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact seg_front a b (t := .equal) (h1 _ (by simp))
      · exact h1 o (by simp [ho])
    · cases r with
      | nil => trivial
      | cons y t =>
        obtain ⟨_, _, _, _, _⟩ := y
        exact h2
  | (.replace, i1, i2, j1, j2) :: r, h1, h2 => exact ⟨h1, h2⟩
  | (.delete, i1, i2, j1, j2) :: r, h1, h2 => exact ⟨h1, h2⟩
  | (.insert, i1, i2, j1, j2) :: r, h1, h2 => exact ⟨h1, h2⟩

theorem fixLast_head (n : Nat) (y : Op) (t : List Op) :
    ∃ y' r', fixLast n (y :: t) = y' :: r' ∧ y'.2.1 = y.2.1 ∧ y'.2.2.2.1 = y.2.2.2.1 := by
  obtain ⟨t0, i1, i2, j1, j2⟩ := y
  cases t with
  | nil => cases t0 <;> exact ⟨_, _, rfl, rfl, rfl⟩
  | cons z r => cases t0 <;> exact ⟨_, _, rfl, rfl, rfl⟩

theorem fixLast_ok (n : Nat) : ∀ l : List Op, (∀ o ∈ l, Seg a b o) → Chn l → (∀ o ∈ fixLast n l, Seg a b o) ∧ Chn (fixLast n l) := by
  intro l
  induction l with
  | nil => intro _ _; exact ⟨by simp [fixLast], trivial⟩
  | cons x r ih =>
    intro h1 h2
    cases r with
    | nil =>
      obtain ⟨t, i1, i2, j1, j2⟩ := x
      cases t with
      | equal =>
        refine ⟨?_, trivial⟩
        intro o ho
        simp only [fixLast, List.mem_singleton] at ho
        subst ho
        exact seg_back a b (h1 _ (by simp))
      | replace => exact ⟨h1, trivial⟩
      | delete => exact ⟨h1, trivial⟩
      | insert => exact ⟨h1, trivial⟩
    | cons y t =>
      have ht := ih (fun o ho => h1 o (by simp [ho])) (chn_tail h2)
      have e : fixLast n (x :: y :: t) = x :: fixLast n (y :: t) := by
        obtain ⟨t0, _, _, _, _⟩ := x
        cases t0 <;> rfl
      rw [e]
      constructor
      · intro o ho
        rcases List.mem_cons.mp ho with rfl | ho
        · exact h1 _ (by simp)
        · exact ht.1 o ho
      · obtain ⟨y', r', e1, e2, e3⟩ := fixLast_head n y t
        rw [e1] at ht ⊢
        obtain ⟨_, _, _, _, _⟩ := x
        obtain ⟨_, _, _, _, _⟩ := y'
        obtain ⟨_, _, _, _, _⟩ := y
        simp only at e2 e3
        exact ⟨h2.1.trans e2.symm, h2.2.1.trans e3.symm, ht.2⟩

/-- A group that is a run of good opcodes. -/
def GrpOK (g : List Op) : Prop := g ≠ [] ∧ Chn g ∧ ∀ o ∈ g, Seg a b o

/-- The open group, newest first, ends where the rest of the opcodes start. -/
def Link (group codes : List Op) : Prop :=
  ∀ p q, group.head? = some p → codes.head? = some q → p.2.2.1 = q.2.1 ∧ p.2.2.2.2 = q.2.2.2.1

theorem group_ok (n : Nat) : ∀ (codes : List Op) (done : List (List Op)) (group : List Op),
    (∀ o ∈ codes, Seg a b o) → Chn codes → (∀ g ∈ done, GrpOK a b g) → Chn group.reverse → (∀ o ∈ group, Seg a b o) →
    Link group codes →
    (∀ g ∈ (groupLoop n codes done group).1, GrpOK a b g) ∧ Chn (groupLoop n codes done group).2.reverse ∧
      ∀ o ∈ (groupLoop n codes done group).2, Seg a b o := by
  intro codes
  induction codes with
  | nil => intro done group _ _ h3 h4 h5 _; exact ⟨h3, h4, h5⟩
  | cons op r ih =>
    intro done group h1 h2 h3 h4 h5 h6
    obtain ⟨t, i1, i2, j1, j2⟩ := op
    have hop : Seg a b (t, i1, i2, j1, j2) := h1 _ (by simp)
    have hr : ∀ o ∈ r, Seg a b o := fun o ho => h1 o (by simp [ho])
    have hc := chn_tail h2
    have snoc : ∀ x : Op, x.2.1 = i1 → x.2.2.2.1 = j1 → Chn (x :: group).reverse := by
      intro x e1 e2
      rw [List.reverse_cons]
      apply chn_snoc _ _ h4
      intro p hp
      have hq : group.head? = some p := by
        simpa [List.getLast?_reverse] using hp
      obtain ⟨e3, e4⟩ := h6 p _ hq rfl
      exact ⟨e3.trans e1.symm, e4.trans e2.symm⟩
    simp only [groupLoop]
    split
    · rename_i hb
      have ht : t = .equal := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        exact hb.1
      subst ht
      have hx := seg_back a b (n := n) hop
      refine ih _ _ hr hc ?_ trivial ?_ ?_
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact h3 g hg
        · simp only [List.mem_singleton] at hg
          subst hg
          refine ⟨by simp, snoc _ rfl rfl, ?_⟩
          intro o ho
          rcases List.mem_cons.mp (List.mem_reverse.mp ho) with rfl | ho
          · exact hx
          · exact h5 o ho
      · intro o ho
        simp only [List.mem_singleton] at ho
        subst ho
        exact seg_front a b (t := .equal) hop
      · intro p q hp hq
        simp only [List.head?_cons, Option.some.injEq] at hp
        subst hp
        cases r with
        | nil => cases hq
        | cons z w =>
          obtain ⟨_, _, _, _, _⟩ := z
          simp only [List.head?_cons, Option.some.injEq] at hq
          subst hq
          exact ⟨h2.1, h2.2.1⟩
    · refine ih _ _ hr hc h3 (snoc _ rfl rfl) ?_ ?_
      · intro o ho
        rcases List.mem_cons.mp ho with rfl | ho
        · exact hop
        · exact h5 o ho
      · intro p q hp hq
        simp only [List.head?_cons, Option.some.injEq] at hp
        subst hp
        cases r with
        | nil => cases hq
        | cons z w =>
          obtain ⟨_, _, _, _, _⟩ := z
          simp only [List.head?_cons, Option.some.injEq] at hq
          subst hq
          exact ⟨h2.1, h2.2.1⟩

theorem close_ok (g : List Op) (h1 : Chn g.reverse) (h2 : ∀ o ∈ g, Seg a b o) : ∀ x ∈ closeGroup g, GrpOK a b x := by
  intro x hx
  match g, hx with
  | [], hx => simp [closeGroup] at hx
  | [(t, i1, i2, j1, j2)], hx =>
    cases t with
    | equal => simp [closeGroup] at hx
    | replace =>
      simp only [closeGroup, List.mem_singleton] at hx
      subst hx
      exact ⟨by simp, by simpa using h1, fun o ho => h2 o (by simpa using ho)⟩
    | delete =>
      simp only [closeGroup, List.mem_singleton] at hx
      subst hx
      exact ⟨by simp, by simpa using h1, fun o ho => h2 o (by simpa using ho)⟩
    | insert =>
      simp only [closeGroup, List.mem_singleton] at hx
      subst hx
      exact ⟨by simp, by simpa using h1, fun o ho => h2 o (by simpa using ho)⟩
  | y :: z :: t, hx =>
    have e : closeGroup (y :: z :: t) = [(y :: z :: t).reverse] := by
      obtain ⟨t0, _, _, _, _⟩ := y
      cases t0 <;> rfl
    rw [e, List.mem_singleton] at hx
    subst hx
    refine ⟨by simp, h1, fun o ho => h2 o (List.mem_reverse.mp ho)⟩

/-! ### The two sides of a hunk -/

/-- The lines of a hunk that belong to one side, without their first character. -/
def sideOf (c : Nat) (body : List Str) : List Str :=
  body.filterMap fun l =>
    match l with
    | x :: r => if x == 32 || x == c then some r else none
    | [] => none

theorem side_append (c : Nat) (x y : List Str) : sideOf c (x ++ y) = sideOf c x ++ sideOf c y := by
  simp [sideOf, List.filterMap_append]

theorem side_map (c t : Nat) (keep : Bool) (h : (t == 32 || t == c) = keep) : ∀ l : List LineO,
    sideOf c (l.map fun x => t :: x.text) = if keep then l.map LineO.text else [] := by
  intro l
  induction l with
  | nil => cases keep <;> rfl
  | cons x r ih =>
    simp only [sideOf, List.map_cons, List.filterMap_cons, h] at ih ⊢
    rw [ih]
    cases keep <;> simp

theorem op_old (x : Op) (h : Seg a b x) : sideOf 45 (bodyU a b [x]) = (sliceL a x.2.1 x.2.2.1).map LineO.text := by
  obtain ⟨t, i1, i2, j1, j2⟩ := x
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have m1 := side_map 45 45 true (by decide) (sliceL a i1 i2)
  have m2 := side_map 45 43 false (by decide) (sliceL b j1 j2)
  have m3 := side_map 45 32 true (by decide) (sliceL a i1 i2)
  simp only [Bool.false_eq_true, if_false, if_true] at m1 m2 m3
  cases t with
  | equal => simp only [bodyU, List.append_nil, m3]
  | replace => simp only [bodyU, List.append_nil, side_append, m1, m2]
  | delete => simp only [bodyU, List.append_nil, m1]
  | insert =>
    simp only at h5
    subst h5
    simp only [bodyU, List.append_nil, m2, slice_empty a i1 i1 (Nat.le_refl _), List.map_nil]

theorem op_new (x : Op) (h : Seg a b x) : sideOf 43 (bodyU a b [x]) = (sliceL b x.2.2.2.1 x.2.2.2.2).map LineO.text := by
  obtain ⟨t, i1, i2, j1, j2⟩ := x
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have m1 := side_map 43 45 false (by decide) (sliceL a i1 i2)
  have m2 := side_map 43 43 true (by decide) (sliceL b j1 j2)
  have m3 := side_map 43 32 true (by decide) (sliceL a i1 i2)
  simp only [Bool.false_eq_true, if_false, if_true] at m1 m2 m3
  cases t with
  | equal =>
    simp only at h5
    simp only [bodyU, List.append_nil]
    rw [m3, h5.2]
  | replace => simp only [bodyU, List.append_nil, side_append, m1, m2, List.nil_append]
  | delete =>
    simp only at h5
    subst h5
    simp only [bodyU, List.append_nil, m1, slice_empty b j1 j1 (Nat.le_refl _), List.map_nil]
  | insert => simp only [bodyU, List.append_nil, m2]

def dflt : Op := (.equal, 0, 0, 0, 0)

theorem body_cons (x : Op) (r : List Op) : bodyU a b (x :: r) = bodyU a b [x] ++ bodyU a b r := by
  obtain ⟨t, i1, i2, j1, j2⟩ := x
  simp [bodyU]

/-- The body of a run of opcodes gives both slices it covers. -/
theorem sides : ∀ (g : List Op), g ≠ [] → Chn g → (∀ o ∈ g, Seg a b o) →
    sideOf 45 (bodyU a b g) = (sliceL a (g.headD dflt).2.1 (g.getLastD dflt).2.2.1).map LineO.text ∧
    sideOf 43 (bodyU a b g) = (sliceL b (g.headD dflt).2.2.2.1 (g.getLastD dflt).2.2.2.2).map LineO.text ∧
    (g.headD dflt).2.1 ≤ (g.getLastD dflt).2.2.1 ∧ (g.headD dflt).2.2.2.1 ≤ (g.getLastD dflt).2.2.2.2 := by
  intro g
  induction g with
  | nil => intro h; exact absurd rfl h
  | cons x r ih =>
    intro _ hc hs
    have hx := hs x (by simp)
    cases r with
    | nil =>
      obtain ⟨t, i1, i2, j1, j2⟩ := x
      exact ⟨op_old a b _ hx, op_new a b _ hx, hx.1, hx.2.2.1⟩
    | cons y t =>
      obtain ⟨g1, g2, g3, g4⟩ := ih (by simp) (chn_tail hc) (fun o ho => hs o (by simp [ho]))
      rw [body_cons, side_append, side_append, op_old a b x hx, op_new a b x hx, g1, g2]
      have el : ((x :: y :: t).getLastD dflt) = ((y :: t).getLastD dflt) := by
        simp [List.getLastD_cons]
      obtain ⟨t0, i1, i2, j1, j2⟩ := x
      obtain ⟨t1, a1, a2, b1, b2⟩ := y
      obtain ⟨e1, e2, _⟩ := hc
      subst e1 e2
      simp only [List.headD_cons] at g1 g2 g3 g4 ⊢
      rw [el]
      obtain ⟨h1, h2, h3, h4, _⟩ := hx
      rw [← List.map_append, ← List.map_append, slice_join _ _ _ _ h1 g3, slice_join _ _ _ _ h3 g4]
      exact ⟨rfl, rfl, by omega, by omega⟩

/-- A hunk of `unified_diff`, for any two lists of `str` and any `n`: its context and removed lines are
`a[i1:i2]`, and its context and added lines are `b[j1:j2]`, for the first and last opcodes of the group, which
are what the `@@` line prints. So the hunks are a patch, and with `GroupedLawO` no change is left out. -/
def HunkSides : Prop :=
  ∀ (a b : List Str) (n : Nat) (s s2 : SMO LineO) (gs : List (List Op)),
    makeO lineOps none (a.map .str) (b.map .str) true = .ok s → getGroupedO lineOps s n = (s2, .ok gs) →
    ∀ g ∈ gs,
      sideOf 45 (bodyU (a.map .str) (b.map .str) g) = sliceL a (g.headD dflt).2.1 (g.getLastD dflt).2.2.1 ∧
      sideOf 43 (bodyU (a.map .str) (b.map .str) g) = sliceL b (g.headD dflt).2.2.2.1 (g.getLastD dflt).2.2.2.2

theorem text_slice (l : List Str) (i j : Nat) : (sliceL (l.map LineO.str) i j).map LineO.text = sliceL l i j := by
  simp [sliceL, ← List.map_drop, ← List.map_take, Function.comp_def, LineO.text]

theorem groups_good (a b : List Str) (n : Nat) (s s2 : SMO LineO) (gs : List (List Op))
    (hs : makeO lineOps none (a.map .str) (b.map .str) true = .ok s) (hg : getGroupedO lineOps s n = (s2, .ok gs)) :
    ∀ g ∈ gs, GrpOK (a.map .str) (b.map .str) g := by
  intro g hin
  have L : Lawful lineOps (a.map LineO.str ++ b.map LineO.str) := by
    apply lineOps_lawful
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨u, _, rfl⟩ := List.mem_map.mp h
      exact ⟨u, rfl⟩
    · obtain ⟨u, _, rfl⟩ := List.mem_map.mp h
      exact ⟨u, rfl⟩
  obtain ⟨s', ops, e3, e4⟩ := opcodesLawO_proven _ lineOps none _ _ true s L hs
  obtain ⟨c1, c2⟩ := cover_seg _ _ L ops 0 0 e4
  simp only [getGroupedO, e3, Prod.mk.injEq, Except.ok.injEq] at hg
  obtain ⟨_, rfl⟩ := hg
  cases he : ops.isEmpty with
  | true =>
    have hn : ops = [] := by simpa using he
    subst hn
    exfalso
    simp only [List.isEmpty_nil, if_true] at hin
    cases n with
    | zero => simp [fixFirst, fixLast, groupLoop, closeGroup] at hin
    | succ m =>
      have e1 : (1 - (m + 1)) = 0 := by omega
      have e2 : min 1 (0 + (m + 1)) = 1 := by omega
      simp [fixFirst, fixLast, groupLoop, closeGroup, e1, e2] at hin
  | false =>
    simp only [he, Bool.false_eq_true, if_false] at hin
    obtain ⟨f1, f2⟩ := fixFirst_ok _ _ n ops c1 c2
    obtain ⟨f3, f4⟩ := fixLast_ok _ _ n _ f1 f2
    obtain ⟨g1, g2, g3⟩ := group_ok _ _ n _ [] [] f3 f4 (by simp) trivial (by simp) (by intro p q hp; cases hp)
    rcases List.mem_append.mp hin with h | h
    · exact g1 g h
    · exact close_ok _ _ _ g2 g3 g h

theorem hunkSides_proven : HunkSides := by
  intro a b n s s2 gs hs hg g hin
  have hok := groups_good a b n s s2 gs hs hg g hin
  obtain ⟨r1, r2, _, _⟩ := sides _ _ g hok.1 hok.2.1 hok.2.2
  rw [text_slice] at r1 r2
  exact ⟨r1, r2⟩

/-! ### `context_diff` -/

theorem plus_str (p : Str) : ∀ l : List Str, plusLines p (l.map .str) = (l.map (p ++ ·), .ok ()) := by
  intro l
  induction l with
  | nil => rfl
  | cons x r ih =>
    simp only [List.map_cons, plusLines, ih, Emit.and]
    rfl

theorem slice_str (l : List Str) (i j : Nat) : sliceL (l.map LineO.str) i j = (sliceL l i j).map LineO.str := by
  simp [sliceL, ← List.map_drop, ← List.map_take]

theorem prefix_len (t : Tag) : (prefixC t).length = 2 := by
  cases t <;> decide

theorem drop_prefix (t : Tag) (l : List Str) : (l.map (prefixC t ++ ·)).map (·.drop 2) = l := by
  have : ∀ x : Str, (prefixC t ++ x).drop 2 = x := fun x => List.drop_left' (prefix_len t)
  simp [Function.comp_def, this]

/-- Each side of a run of opcodes, as `context_diff` prints it, without its two-character prefixes. -/
theorem sideA_ok (a b : List Str) : ∀ g : List Op, g ≠ [] → Chn g → (∀ o ∈ g, Seg (a.map .str) (b.map .str) o) →
    ∃ o, sideA (a.map .str) g = (o, .ok ()) ∧ o.map (·.drop 2) = sliceL a (g.headD dflt).2.1 (g.getLastD dflt).2.2.1 ∧
      (g.headD dflt).2.1 ≤ (g.getLastD dflt).2.2.1 := by
  intro g
  induction g with
  | nil => intro h; exact absurd rfl h
  | cons x r ih =>
    intro _ hc hs
    have hx := hs x (by simp)
    obtain ⟨t, i1, i2, j1, j2⟩ := x
    obtain ⟨h1, h2, h3, h4, h5⟩ := hx
    have step : ∀ (o : List Str) (i3 : Nat), sideA (a.map .str) r = (o, .ok ()) → i2 ≤ i3 →
        o.map (·.drop 2) = sliceL a i2 i3 →
        ∃ o', sideA (a.map .str) ((t, i1, i2, j1, j2) :: r) = (o', .ok ()) ∧ o'.map (·.drop 2) = sliceL a i1 i3 := by
      intro o i3 e1 e2 e3
      have common : ∀ tg : Tag, (tg != .insert) = true →
          ∃ o', sideA (a.map .str) ((tg, i1, i2, j1, j2) :: r) = (o', .ok ()) ∧ o'.map (·.drop 2) = sliceL a i1 i3 := by
        intro tg ht
        refine ⟨(sliceL a i1 i2).map (prefixC tg ++ ·) ++ o, ?_, ?_⟩
        · simp [sideA, ht, e1, slice_str, plus_str, Emit.and]
        · rw [List.map_append, drop_prefix, e3, slice_join _ _ _ _ h1 e2]
      cases t with
      | insert =>
        simp only at h5
        subst h5
        exact ⟨o, by simp [sideA, e1], by simpa using e3⟩
      | equal => exact common _ rfl
      | replace => exact common _ rfl
      | delete => exact common _ rfl
    cases r with
    | nil =>
      obtain ⟨o', e1, e2⟩ := step [] i2 rfl (Nat.le_refl _) (by rw [slice_empty _ _ _ (Nat.le_refl _)]; rfl)
      exact ⟨o', e1, e2, h1⟩
    | cons y t' =>
      obtain ⟨o, g1, g2, g3⟩ := ih (by simp) (chn_tail hc) (fun o ho => hs o (by simp [ho]))
      obtain ⟨t1, a1, a2, b1, b2⟩ := y
      obtain ⟨e1, e2, _⟩ := hc
      subst e1 e2
      simp only [List.headD_cons] at g2 g3 ⊢
      obtain ⟨o', e3, e4⟩ := step o _ g1 g3 g2
      have el : (((t, i1, i2, j1, j2) :: (t1, i2, a2, j2, b2) :: t').getLastD dflt) = (((t1, i2, a2, j2, b2) :: t').getLastD dflt) := by
        simp [List.getLastD_cons]
      rw [el]
      exact ⟨o', e3, e4, by omega⟩

theorem sideB_ok (a b : List Str) : ∀ g : List Op, g ≠ [] → Chn g → (∀ o ∈ g, Seg (a.map .str) (b.map .str) o) →
    ∃ o, sideB (b.map .str) g = (o, .ok ()) ∧ o.map (·.drop 2) = sliceL b (g.headD dflt).2.2.2.1 (g.getLastD dflt).2.2.2.2 ∧
      (g.headD dflt).2.2.2.1 ≤ (g.getLastD dflt).2.2.2.2 := by
  intro g
  induction g with
  | nil => intro h; exact absurd rfl h
  | cons x r ih =>
    intro _ hc hs
    have hx := hs x (by simp)
    obtain ⟨t, i1, i2, j1, j2⟩ := x
    obtain ⟨h1, h2, h3, h4, h5⟩ := hx
    have step : ∀ (o : List Str) (i3 : Nat), sideB (b.map .str) r = (o, .ok ()) → j2 ≤ i3 →
        o.map (·.drop 2) = sliceL b j2 i3 →
        ∃ o', sideB (b.map .str) ((t, i1, i2, j1, j2) :: r) = (o', .ok ()) ∧ o'.map (·.drop 2) = sliceL b j1 i3 := by
      intro o i3 e1 e2 e3
      have common : ∀ tg : Tag, (tg != .delete) = true →
          ∃ o', sideB (b.map .str) ((tg, i1, i2, j1, j2) :: r) = (o', .ok ()) ∧ o'.map (·.drop 2) = sliceL b j1 i3 := by
        intro tg ht
        refine ⟨(sliceL b j1 j2).map (prefixC tg ++ ·) ++ o, ?_, ?_⟩
        · simp [sideB, ht, e1, slice_str, plus_str, Emit.and]
        · rw [List.map_append, drop_prefix, e3, slice_join _ _ _ _ h3 e2]
      cases t with
      | delete =>
        simp only at h5
        subst h5
        exact ⟨o, by simp [sideB, e1], by simpa using e3⟩
      | equal => exact common _ rfl
      | replace => exact common _ rfl
      | insert => exact common _ rfl
    cases r with
    | nil =>
      obtain ⟨o', e1, e2⟩ := step [] j2 rfl (Nat.le_refl _) (by rw [slice_empty _ _ _ (Nat.le_refl _)]; rfl)
      exact ⟨o', e1, e2, h3⟩
    | cons y t' =>
      obtain ⟨o, g1, g2, g3⟩ := ih (by simp) (chn_tail hc) (fun o ho => hs o (by simp [ho]))
      obtain ⟨t1, a1, a2, b1, b2⟩ := y
      obtain ⟨e1, e2, _⟩ := hc
      subst e1 e2
      simp only [List.headD_cons] at g2 g3 ⊢
      obtain ⟨o', e3, e4⟩ := step o _ g1 g3 g2
      have el : (((t, i1, i2, j1, j2) :: (t1, i2, a2, j2, b2) :: t').getLastD dflt) = (((t1, i2, a2, j2, b2) :: t').getLastD dflt) := by
        simp [List.getLastD_cons]
      rw [el]
      exact ⟨o', e3, e4, by omega⟩

/-- The two sides of a hunk of `context_diff`, for any two lists of `str` and any `n`: without their prefixes
they are the slices of `a` and `b` that the group covers. -/
def ContextSides : Prop :=
  ∀ (a b : List Str) (n : Nat) (s s2 : SMO LineO) (gs : List (List Op)),
    makeO lineOps none (a.map .str) (b.map .str) true = .ok s → getGroupedO lineOps s n = (s2, .ok gs) →
    ∀ g ∈ gs, ∃ o1 o2, sideA (a.map .str) g = (o1, .ok ()) ∧ sideB (b.map .str) g = (o2, .ok ()) ∧
      o1.map (·.drop 2) = sliceL a (g.headD dflt).2.1 (g.getLastD dflt).2.2.1 ∧
      o2.map (·.drop 2) = sliceL b (g.headD dflt).2.2.2.1 (g.getLastD dflt).2.2.2.2

theorem contextSides_proven : ContextSides := by
  intro a b n s s2 gs hs hg g hin
  have hok := groups_good a b n s s2 gs hs hg g hin
  obtain ⟨o1, e1, e2, _⟩ := sideA_ok a b g hok.1 hok.2.1 hok.2.2
  obtain ⟨o2, e3, e4, _⟩ := sideB_ok a b g hok.1 hok.2.1 hok.2.2
  exact ⟨o1, o2, e1, e3, e2, e4⟩

end PyLean.TextLibs.Difflib
