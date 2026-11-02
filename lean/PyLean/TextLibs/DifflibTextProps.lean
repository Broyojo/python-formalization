import PyLean.TextLibs.DifflibText
import PyLean.TextLibs.DifflibObjLaws

/-!
`restore` undoes `ndiff`, whatever the matchers chose, and `unified_diff` and `context_diff` report every
difference. The proofs go through `OpcodesLawO` and `GroupedLawO`, and the floats of `_fancy_replace` do
not enter: its choice of a synch pair is free as far as `restore` goes.
-/

namespace PyLean.TextLibs.Difflib

open PyLean

set_option linter.unusedSimpArgs false

/-! ### Slices -/

theorem slice_empty {β : Type} (l : List β) (i j : Nat) (h : j ≤ i) : sliceL l i j = [] := by
  simp [sliceL, show j - i = 0 by omega]

theorem slice_join {β : Type} (l : List β) (i j k : Nat) (h1 : i ≤ j) (h2 : j ≤ k) :
    sliceL l i j ++ sliceL l j k = sliceL l i k := by
  simp only [sliceL]
  have e : k - i = (j - i) + (k - j) := by omega
  rw [e, List.take_add, List.drop_drop]
  have e2 : i + (j - i) = j := by omega
  rw [e2]

theorem slice_one {β : Type} [Inhabited β] (d : β) (l : List β) (i : Nat) (h : i < l.length) :
    sliceL l i (i + 1) = [l.getD i d] := by
  have e : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons h
  have e2 : l.getD i d = l[i] := by simp [h]
  simp only [sliceL, show i + 1 - i = 1 by omega]
  rw [e2, e]
  rfl

theorem slice_end {β : Type} (l : List β) (i : Nat) (h : l.length ≤ i) : sliceL l i l.length = [] :=
  slice_empty l i _ h

/-! ### `restore` -/

def tM : Str := [45, 32]
def tP : Str := [43, 32]

theorem restore_append (tag : Str) (x y : List Str) : restoreL tag (x ++ y) = restoreL tag x ++ restoreL tag y := by
  simp [restoreL, List.filterMap_append]

theorem restore_tagged (tag : Str) (t : Nat) (keep : Bool) (h : ([t, 32] == [32, 32] || [t, 32] == tag) = keep) :
    ∀ l : List Str, restoreL tag (l.map fun x => t :: 32 :: x) = if keep then l else [] := by
  intro l
  induction l with
  | nil => cases keep <;> rfl
  | cons x r ih =>
    simp only [restoreL, List.map_cons, List.filterMap_cons, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero, h] at ih ⊢
    rw [ih]
    cases keep <;> simp

theorem rM45 (x : List Str) (lo hi : Nat) : restoreL tM (dump 45 x lo hi) = sliceL x lo hi := by
  simpa [dump] using restore_tagged tM 45 true (by decide) (sliceL x lo hi)
theorem rM43 (x : List Str) (lo hi : Nat) : restoreL tM (dump 43 x lo hi) = [] := by
  simpa [dump] using restore_tagged tM 43 false (by decide) (sliceL x lo hi)
theorem rM32 (x : List Str) (lo hi : Nat) : restoreL tM (dump 32 x lo hi) = sliceL x lo hi := by
  simpa [dump] using restore_tagged tM 32 true (by decide) (sliceL x lo hi)
theorem rP45 (x : List Str) (lo hi : Nat) : restoreL tP (dump 45 x lo hi) = [] := by
  simpa [dump] using restore_tagged tP 45 false (by decide) (sliceL x lo hi)
theorem rP43 (x : List Str) (lo hi : Nat) : restoreL tP (dump 43 x lo hi) = sliceL x lo hi := by
  simpa [dump] using restore_tagged tP 43 true (by decide) (sliceL x lo hi)
theorem rP32 (x : List Str) (lo hi : Nat) : restoreL tP (dump 32 x lo hi) = sliceL x lo hi := by
  simpa [dump] using restore_tagged tP 32 true (by decide) (sliceL x lo hi)

theorem helper_M (a b : List Str) (alo ahi blo bhi : Nat) : restoreL tM (fancyHelper a alo ahi b blo bhi) = sliceL a alo ahi := by
  simp only [fancyHelper, plainReplace]
  split
  · split
    · split
      · rw [restore_append, rM43, rM45]; rfl
      · rw [restore_append, rM45, rM43, List.append_nil]
    · exact rM45 _ _ _
  · rename_i h
    rw [slice_empty a alo ahi (by omega)]
    split
    · exact rM43 _ _ _
    · rfl

theorem helper_P (a b : List Str) (alo ahi blo bhi : Nat) : restoreL tP (fancyHelper a alo ahi b blo bhi) = sliceL b blo bhi := by
  simp only [fancyHelper, plainReplace]
  split
  · split
    · split
      · rw [restore_append, rP43, rP45, List.append_nil]
      · rw [restore_append, rP45, rP43]; rfl
    · rename_i h1 h2
      rw [slice_empty b blo bhi (by omega)]
      exact rP45 _ _ _
  · split
    · exact rP43 _ _ _
    · rename_i h1 h2
      rw [slice_empty b blo bhi (by omega)]
      rfl

theorem q_M (x y s t : Str) : restoreL tM (qformat x y s t) = [x] := by
  simp only [qformat]
  split <;> split <;> simp [restoreL, tM]

theorem q_P (x y s t : Str) : restoreL tP (qformat x y s t) = [y] := by
  simp only [qformat]
  split <;> split <;> simp [restoreL, tP]

theorem same_M (x : Str) : restoreL tM [32 :: 32 :: x] = [x] := by simp [restoreL, tM]
theorem same_P (x : Str) : restoreL tP [32 :: 32 :: x] = [x] := by simp [restoreL, tP]

/-- The `i` that `innerBest` settles on is one it was given. -/
theorem inner_mem (a : List Str) : ∀ (is : List Nat) (s : SMO Nat) (bi : Option Nat) (br : Binary64.F64)
    (s' : SMO Nat) (i : Nat) (r : Binary64.F64), innerBest a s is bi br = .ok (s', some i, r) → i ∈ is ∨ bi = some i := by
  intro is
  induction is with
  | nil =>
    intro s bi br s' i r h
    simp only [innerBest, Except.ok.injEq, Prod.mk.injEq] at h
    exact Or.inr h.2.1
  | cons x t ih =>
    intro s bi br s' i r h
    simp only [innerBest] at h
    have up : ∀ (s2 : SMO Nat) (b2 : Option Nat) (r2 : Binary64.F64), (b2 = bi ∨ b2 = some x) → innerBest a s2 t b2 r2 = .ok (s', some i, r) →
        i ∈ x :: t ∨ bi = some i := by
      intro s2 b2 r2 hb he
      rcases ih s2 b2 r2 s' i r he with h1 | h1
      · exact Or.inl (List.mem_cons_of_mem _ h1)
      · rcases hb with rfl | rfl
        · exact Or.inr h1
        · have : x = i := by simpa using h1
          exact Or.inl (by simp [this])
    split at h
    · exact up _ _ _ (Or.inl rfl) h
    · split at h
      · cases h
      · split at h
        · exact up _ _ _ (Or.inl rfl) h
        · split at h
          · cases h
          · split at h
            · exact up _ _ _ (Or.inr rfl) h
            · exact up _ _ _ (Or.inl rfl) h

theorem stitch {β : Type} (A R S T U V : List β) (x : β) (g : R ++ S = T) (hA : [x] ++ T = U) (hB : A ++ U = V) :
    A ++ [x] ++ R ++ S = V := by
  subst g hA hB
  simp

/-- A run of the `for j` loop, as far as `restore` sees it: it covers `a[di:di']` and `b[dj:dj']`. -/
theorem fancy_restore (a b : List Str) (alo ahi blo bhi : Nat) (hA : ahi ≤ a.length) (hB : bhi ≤ b.length) :
    ∀ (fuel j : Nat) (s : SMO Nat) (di dj di' dj' : Nat) (out : List Str), j + fuel = bhi → di ≤ ahi → dj ≤ j →
      fancyLoop a b alo ahi blo fuel j s di dj = (out, .ok (di', dj')) →
      di ≤ di' ∧ di' ≤ ahi ∧ dj ≤ dj' ∧ dj' ≤ bhi ∧
        restoreL tM out ++ sliceL a di' ahi = sliceL a di ahi ∧ restoreL tP out ++ sliceL b dj' bhi = sliceL b dj bhi := by
  intro fuel
  induction fuel with
  | zero =>
    intro j s di dj di' dj' out h1 h2 h3 h
    simp only [fancyLoop, Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, h2, Nat.le_refl _, by omega, rfl, rfl⟩
  | succ f ih =>
    intro j s di dj di' dj' out h1 h2 h3 h
    simp only [fancyLoop] at h
    split at h
    · cases (Prod.mk.inj h).2
    · rename_i s1 _
      split at h
      · simp only [Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨Nat.le_refl _, h2, Nat.le_refl _, by omega, rfl, rfl⟩
      · rename_i hr
        generalize hI : innerBest a s1 (List.range' (max (alo + (j - blo) - 10) di)
          (min (alo + (j - blo) + 11) ahi - max (alo + (j - blo) - 10) di)) none fancyCutoff = res at h
        rcases res with e | ⟨s2, _ | bi, r⟩
        · cases (Prod.mk.inj h).2
        · exact ih (j + 1) _ di dj di' dj' out (by omega) h2 (by omega) h
        · simp only at h
          have hm := inner_mem a _ s1 none _ s2 bi _ hI
          have hbi : bi ∈ List.range' (max (alo + (j - blo) - 10) di) (min (alo + (j - blo) + 11) ahi - max (alo + (j - blo) - 10) di) := by
            rcases hm with hm | hm
            · exact hm
            · cases hm
          have hb2 := List.mem_range'_1.mp hbi
          have l1 : di ≤ bi := by omega
          have l2 : bi < ahi := by omega
          have sA := slice_join a di bi ahi l1 (by omega)
          have sB := slice_join b dj j bhi h3 (by omega)
          have oA := slice_join a bi (bi + 1) ahi (by omega) (by omega)
          have oB := slice_join b j (j + 1) bhi (by omega) (by omega)
          rw [slice_one [] a bi (by omega)] at oA
          rw [slice_one [] b j (by omega)] at oB
          split at h
          · split at h
            · cases (Prod.mk.inj h).2
            · split at h
              · cases (Prod.mk.inj h).2
              · simp only [Prod.mk.injEq] at h
                obtain ⟨rfl, h4⟩ := h
                obtain ⟨g1, g2, g3, g4, g5, g6⟩ := ih (j + 1) _ (bi + 1) (j + 1) di' dj' _ (by omega) (by omega) (Nat.le_refl _)
                  (Prod.ext rfl h4)
                refine ⟨by omega, g2, by omega, g4, ?_, ?_⟩
                · rw [restore_append, restore_append, helper_M, q_M]
                  exact stitch _ _ _ _ _ _ _ g5 oA sA
                · rw [restore_append, restore_append, helper_P, q_P]
                  exact stitch _ _ _ _ _ _ _ g6 oB sB
          · rename_i hne
            have he : a.getD bi [] = b.getD j [] := by simpa using hne
            simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, h4⟩ := h
            obtain ⟨g1, g2, g3, g4, g5, g6⟩ := ih (j + 1) _ (bi + 1) (j + 1) di' dj' _ (by omega) (by omega) (Nat.le_refl _)
              (Prod.ext rfl h4)
            refine ⟨by omega, g2, by omega, g4, ?_, ?_⟩
            · rw [restore_append, restore_append, helper_M, same_M]
              exact stitch _ _ _ _ _ _ _ g5 oA sA
            · rw [restore_append, restore_append, helper_P, same_P, he]
              exact stitch _ _ _ _ _ _ _ g6 oB sB

theorem fancy_replace (cj : Option (Nat → Py Bool)) (a b : List Str) (alo ahi blo bhi : Nat) (out : List Str) (hA : ahi ≤ a.length)
    (hB : bhi ≤ b.length) (h1 : alo ≤ ahi) (h2 : blo ≤ bhi) (h : fancyReplace cj a alo ahi b blo bhi = (out, .ok ())) :
    restoreL tM out = sliceL a alo ahi ∧ restoreL tP out = sliceL b blo bhi := by
  simp only [fancyReplace] at h
  split at h
  · cases (Prod.mk.inj h).2
  · rename_i s _
    generalize hx : fancyLoop a b alo ahi blo (bhi - blo) blo s alo blo = x at h
    obtain ⟨o, r⟩ := x
    simp only at h
    cases r with
    | error e => cases (Prod.mk.inj h).2
    | ok v =>
      obtain ⟨di, dj⟩ := v
      simp only [Prod.mk.injEq, and_true] at h
      subst h
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := fancy_restore a b alo ahi blo bhi hA hB _ blo s alo blo di dj o (by omega) h1 (Nat.le_refl _) hx
      rw [restore_append, restore_append, helper_M, helper_P]
      exact ⟨g5, g6⟩

theorem emit_and {x y : Emit} {out : List Str} (h : Emit.and x y = (out, .ok ())) : ∃ o1 o2, x = (o1, .ok ()) ∧ y = (o2, .ok ()) ∧ out = o1 ++ o2 := by
  obtain ⟨o1, r⟩ := x
  simp only [Emit.and] at h
  cases r with
  | error e => cases (Prod.mk.inj h).2
  | ok u =>
    cases u
    obtain ⟨o2, r2⟩ := y
    simp only [Prod.mk.injEq] at h
    exact ⟨o1, o2, rfl, by rw [h.2], h.1.symm⟩

/-- `__eq__` of `str` is `=`, so a match under `__eq__` is the same slice. -/
theorem eqs_slice {α : Type} {o : Ops α} {a b : List α} (he : ∀ x y, o.eq x y = .ok true → x = y) {i j k : Nat}
    (h : EqsO o a b i j k) : sliceL a i (i + k) = sliceL b j (j + k) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [sliceL, show i + k - i = k by omega, show j + k - j = k by omega]
  apply List.ext_getElem?
  intro t
  by_cases ht : t < k
  · obtain ⟨x, y, e1, e2, e3⟩ := h3 t ht
    simp only [List.getElem?_take, ht, if_true, List.getElem?_drop, e1, e2]
    rw [he _ _ e3]
  · simp [List.getElem?_take, ht]

theorem strOps_lawful (xs : List Str) : Lawful strOps xs where
  hash_ok _ _ := ⟨0, rfl⟩
  eq_ok x _ y _ := ⟨decide (x = y), rfl⟩
  refl x _ := by simp [strOps]
  symm x _ y _ := by simp [strOps, eq_comm]
  trans x _ y _ z _ h1 h2 := by
    simp only [strOps, Except.ok.injEq, decide_eq_true_eq] at h1 h2 ⊢
    exact h1.trans h2
  hash_eq _ _ _ _ _ := rfl
  same_eq x _ y _ h := by simpa [strOps] using h

theorem str_eq (x y : Str) (h : strOps.eq x y = .ok true) : x = y := by
  simpa [strOps] using h

theorem compare_restore (cj : Option (Nat → Py Bool)) (a b : List Str) :
    ∀ (ops : List Op) (i j : Nat) (out : List Str),
      Cover (a.map (cls strOps (a ++ b))) (b.map (cls strOps (a ++ b))) i j ops → compareOps cj a b ops = (out, .ok ()) →
      restoreL tM out = sliceL a i a.length ∧ restoreL tP out = sliceL b j b.length := by
  intro ops
  induction ops with
  | nil =>
    intro i j out hc h
    simp only [compareOps, Prod.mk.injEq, and_true] at h
    subst h
    simp only [Cover, List.length_map] at hc
    obtain ⟨rfl, rfl⟩ := hc
    rw [slice_end _ _ (Nat.le_refl _), slice_end _ _ (Nat.le_refl _)]
    exact ⟨rfl, rfl⟩
  | cons op r ih =>
    intro i j out hc h
    obtain ⟨t, i1, i2, j1, j2⟩ := op
    simp only [Cover, List.length_map] at hc
    obtain ⟨rfl, rfl, h3, h4, h5, h6⟩ := hc
    simp only [compareOps] at h
    obtain ⟨o1, o2, e1, e2, rfl⟩ := emit_and h
    obtain ⟨r1, r2⟩ := ih i2 j2 o2 h6 e2
    rw [restore_append, restore_append, r1, r2]
    cases t with
    | replace =>
      simp only [TagOk] at h5
      obtain ⟨q1, q2⟩ := fancy_replace cj a b i1 i2 j1 j2 o1 h3 h4 (by omega) (by omega) e1
      rw [q1, q2, slice_join _ _ _ _ (by omega) h3, slice_join _ _ _ _ (by omega) h4]
      exact ⟨rfl, rfl⟩
    | delete =>
      simp only [TagOk] at h5
      obtain ⟨q1, rfl⟩ := h5
      simp only [Prod.mk.injEq, and_true] at e1
      subst e1
      rw [rM45, rP45, slice_join _ _ _ _ (by omega) h3]
      exact ⟨rfl, rfl⟩
    | insert =>
      simp only [TagOk] at h5
      obtain ⟨rfl, q1⟩ := h5
      simp only [Prod.mk.injEq, and_true] at e1
      subst e1
      rw [rM43, rP43, slice_join _ _ _ _ (by omega) h4]
      exact ⟨rfl, rfl⟩
    | equal =>
      simp only [TagOk] at h5
      obtain ⟨q1, q2, q3⟩ := h5
      simp only [Prod.mk.injEq, and_true] at e1
      subst e1
      have hs := eqs_slice str_eq ((eqsO_iff (strOps_lawful _) _ _ _).mpr q3)
      rw [show i1 + (i2 - i1) = i2 by omega, show j1 + (i2 - i1) = j2 by omega] at hs
      rw [rM32, rP32, slice_join _ _ _ _ (by omega) h3, hs, slice_join _ _ _ _ (by omega) h4]
      exact ⟨rfl, rfl⟩

/-- `restore(ndiff(a, b), 1) == a` and `restore(ndiff(a, b), 2) == b`, for all lists of `str`, any `linejunk`
and any `charjunk`, when `ndiff` runs to its end. The docstring of `restore` says "extract lines originating
from file 1 or 2". The lines may look like delta lines themselves: the prefix is added to every line. -/
def RestoreRoundTrip : Prop :=
  ∀ (lj : Option (Str → Py Bool)) (cj : Option (Nat → Py Bool)) (a b out : List Str), compareO lj cj a b = (out, .ok ()) →
    restoreO out 1 = .ok a ∧ restoreO out 2 = .ok b

theorem restoreRoundTrip_proven : RestoreRoundTrip := by
  intro lj cj a b out h
  simp only [compareO] at h
  split at h
  · cases (Prod.mk.inj h).2
  · rename_i s hm
    obtain ⟨s', ops, e1, e2⟩ := opcodesLawO_proven Str strOps lj a b true s (strOps_lawful _) hm
    simp only [e1] at h
    obtain ⟨r1, r2⟩ := compare_restore cj a b ops 0 0 out e2 h
    have ha : sliceL a 0 a.length = a := by simp [sliceL]
    have hb : sliceL b 0 b.length = b := by simp [sliceL]
    rw [ha] at r1
    rw [hb] at r2
    simp only [restoreO, show (1 : Int) = 1 from rfl, if_true]
    refine ⟨congrArg _ r1, ?_⟩
    simp only [show ¬ ((2 : Int) = 1) by omega, if_false, show (2 : Int) = 2 from rfl, if_true]
    exact congrArg _ r2

/-! ### `unified_diff` and `context_diff` -/

theorem make_total {α : Type} {o : Ops α} {a b : List α} (L : Lawful o (a ++ b)) (auto : Bool) :
    ∃ s, makeO o none a b auto = .ok s := by
  obtain ⟨b1, _, _⟩ := build_val L b 0 [] (fun _ h => mem_right h) (by intro e he; simp at he)
  cases hm : makeO o none a b auto with
  | ok s => exact ⟨s, rfl⟩
  | error e => simp [makeO, setSeq2O, chainBO, b1, junkStepO] at hm

theorem lineOps_lawful (xs : List LineO) (h : ∀ x ∈ xs, ∃ s, x = .str s) : Lawful lineOps xs where
  hash_ok x hx := by
    obtain ⟨s, rfl⟩ := h x hx
    exact ⟨0, rfl⟩
  eq_ok x _ y _ := ⟨decide (x = y), rfl⟩
  refl x _ := by simp [lineOps]
  symm x _ y _ := by simp [lineOps, eq_comm]
  trans x _ y _ z _ h1 h2 := by
    simp only [lineOps, Except.ok.injEq, decide_eq_true_eq] at h1 h2 ⊢
    exact h1.trans h2
  hash_eq x hx y hy e := by
    obtain ⟨s, rfl⟩ := h x hx
    obtain ⟨t, rfl⟩ := h y hy
    rfl
  same_eq x _ y _ e := by simpa [lineOps] using e

theorem line_eq (x y : LineO) (h : lineOps.eq x y = .ok true) : x = y := by
  simpa [lineOps] using h

/-- Opcodes that hold no change mean the rest of the two sequences is the same. -/
theorem cover_same {α : Type} {o : Ops α} {a b : List α} (L : Lawful o (a ++ b)) (he : ∀ x y, o.eq x y = .ok true → x = y) :
    ∀ (ops : List Op) (i j : Nat), Cover (a.map (cls o (a ++ b))) (b.map (cls o (a ++ b))) i j ops → nonEq ops = [] →
      sliceL a i a.length = sliceL b j b.length := by
  intro ops
  induction ops with
  | nil =>
    intro i j hc _
    simp only [Cover, List.length_map] at hc
    obtain ⟨rfl, rfl⟩ := hc
    rw [slice_end _ _ (Nat.le_refl _), slice_end _ _ (Nat.le_refl _)]
  | cons op r ih =>
    intro i j hc hn
    obtain ⟨t, i1, i2, j1, j2⟩ := op
    simp only [Cover, List.length_map] at hc
    obtain ⟨rfl, rfl, h3, h4, h5, h6⟩ := hc
    have ht : t = .equal := by
      cases t with
      | equal => rfl
      | replace => simp [nonEq] at hn
      | delete => simp [nonEq] at hn
      | insert => simp [nonEq] at hn
    subst ht
    have hr : nonEq r = [] := by simpa [nonEq] using hn
    simp only [TagOk] at h5
    obtain ⟨q1, q2, q3⟩ := h5
    have hs := eqs_slice he ((eqsO_iff L _ _ _).mpr q3)
    rw [show i1 + (i2 - i1) = i2 by omega, show j1 + (i2 - i1) = j2 by omega] at hs
    rw [← slice_join a i1 i2 a.length (by omega) h3, ← slice_join b j1 j2 b.length (by omega) h4, hs, ih i2 j2 h6 hr]

theorem check_strs (a b : List Str) (f t fd td lt : Str) :
    checkTypes (.lines (a.map .str)) (.lines (b.map .str)) [.str f, .str t, .str fd, .str td, .str lt] = .ok () := by
  have h1 : ∀ l : List Str, checkFirst (.lines (l.map .str)) = .ok () := by
    intro l
    cases l <;> rfl
  simp only [checkTypes, h1, checkSeq, checkArgs]
  rfl

/-- The groups of two different lists of `str` are not empty. -/
theorem groups_of (a b : List Str) (n : Nat) (hne : a ≠ b) :
    ∃ s gs s2, makeO lineOps none (a.map LineO.str) (b.map LineO.str) true = .ok s ∧
      getGroupedO lineOps s n = (s2, .ok gs) ∧ gs ≠ [] := by
  have L : Lawful lineOps (a.map LineO.str ++ b.map LineO.str) := by
    apply lineOps_lawful
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨s, _, rfl⟩ := List.mem_map.mp h
      exact ⟨s, rfl⟩
    · obtain ⟨s, _, rfl⟩ := List.mem_map.mp h
      exact ⟨s, rfl⟩
  obtain ⟨s, hs⟩ := make_total L true
  obtain ⟨s1, ops, s2, gs, e1, e2, r1, _⟩ := groupedLawO_proven _ lineOps none _ _ true s n L hs
  obtain ⟨s', ops', e3, e4⟩ := opcodesLawO_proven _ lineOps none _ _ true s L hs
  rw [e1] at e3
  obtain ⟨rfl, h7⟩ := Prod.mk.inj e3
  have h8 : ops = ops' := by simpa using h7
  subst h8
  refine ⟨s, gs, s2, hs, e2, ?_⟩
  rintro rfl
  have hn : nonEq ops = [] := by rw [← r1]; rfl
  have hsl := cover_same L line_eq ops 0 0 e4 hn
  have e5 : ∀ l : List LineO, sliceL l 0 l.length = l := by intro l; simp [sliceL]
  rw [e5, e5] at hsl
  have := congrArg (List.map LineO.text) hsl
  exact hne (by simpa [LineO.text, Function.comp_def] using this)

/-- `unified_diff` and `context_diff` report something for any two different lists of `str`, in any
context width: a diff with no output means the same lines. The other direction, that the same lines give no
output, is `.open` as `SameLinesNoDiff`. -/
def DiffDetects : Prop :=
  ∀ (a b : List Str) (f t fd td lt : Str) (n : Nat), a ≠ b →
    (∃ out, unifiedDiff (.lines (a.map .str)) (.lines (b.map .str)) (.str f) (.str t) (.str fd) (.str td) n (.str lt) = .ok out ∧ out ≠ []) ∧
    (contextDiff (.lines (a.map .str)) (.lines (b.map .str)) (.str f) (.str t) (.str fd) (.str td) n (.str lt)).1 ≠ []

theorem diffDetects_proven : DiffDetects := by
  intro a b f t fd td lt n hne
  obtain ⟨s, gs, s2, h1, h2, h3⟩ := groups_of a b n hne
  have h4 := check_strs a b f t fd td lt
  have hg : gs.isEmpty = false := by
    cases gs with
    | nil => exact absurd rfl h3
    | cons _ _ => rfl
  constructor
  · refine ⟨[toStr "--- " ++ f ++ dateOf fd ++ lt, toStr "+++ " ++ t ++ dateOf td ++ lt] ++
      gs.flatMap (hunkU (a.map .str) (b.map .str) lt), ?_, by simp⟩
    simp only [unifiedDiff, h4, bind, Except.bind, seqLines, h1, h2, textOf, hg, Bool.false_eq_true, if_false, pure, Except.pure]
  · simp only [contextDiff, h4, seqLines, h1, h2, textOf, hg, Bool.false_eq_true, if_false, Emit.and]
    simp

/-- The same lines give no output. Held on CPython in 60000 runs, popular lines included: `b2j` loses a popular
line, but the extension loops of `find_longest_match` go over it. A proof has to show that every box on the
diagonal keeps to the diagonal, which `FindLongestDoc` does not give when lines are popular. -/
def SameLinesNoDiff : Prop :=
  ∀ (a : List Str) (f t fd td lt : Str) (n : Nat),
    unifiedDiff (.lines (a.map .str)) (.lines (a.map .str)) (.str f) (.str t) (.str fd) (.str td) n (.str lt) = .ok []

/-- `unified_diff` refuses what `context_diff` refuses, as `_check_types` means them to: its comment says the
alternative is garbled output. It does not: the f-strings that came with `color` format any object, so lines
after the first are not checked, while `'- ' + line` in `context_diff` raises. -/
def DiffTwinsRefuse : Prop :=
  ∀ (a b : SeqArg) (f t fd td lt : TextArg) (n : Nat) (e : PyExc), (contextDiff a b f t fd td n lt).2 = .error e →
    ∃ e', unifiedDiff a b f t fd td n lt = .error e'

theorem diffTwinsRefuse_refuted : ¬DiffTwinsRefuse := by
  intro h
  let a : SeqArg := .lines [.str [97], .other "bytes" (toStr "b'x'") true]
  let b : SeqArg := .lines [.str [97], .other "bytes" (toStr "b'y'") true]
  obtain ⟨e', h1⟩ := h a b (.str []) (.str []) (.str []) (.str []) (.str []) 3 _ (by rfl)
  have h2 : ∃ out, unifiedDiff a b (.str []) (.str []) (.str []) (.str []) 3 (.str []) = .ok out := ⟨_, by rfl⟩
  obtain ⟨out, h3⟩ := h2
  rw [h3] at h1
  cases h1

/-! ### `IS_LINE_JUNK` -/

def nsp (c : Nat) : Bool := !PyLean.UnicodeObj.isSpace c

theorem filter_drop (l : List Nat) : (l.dropWhile PyLean.UnicodeObj.isSpace).filter nsp = l.filter nsp := by
  induction l with
  | nil => rfl
  | cons x r ih =>
    simp only [List.dropWhile_cons]
    cases hs : PyLean.UnicodeObj.isSpace x with
    | true =>
      have : nsp x = false := by simp [nsp, hs]
      simp [ih, this, hs]
    | false => simp [hs]

theorem filter_strip (l : List Nat) : (stripS l).filter nsp = l.filter nsp := by
  simp only [stripS, rstripS]
  rw [List.filter_reverse, filter_drop, List.filter_reverse, List.reverse_reverse, filter_drop]

/-- The docstring of `IS_LINE_JUNK`: "if `line` is blank or contains a single '#'", where the rest of the line
is white space. -/
def IsLineJunkDoc : Prop :=
  ∀ l : Str, isLineJunk l = true ↔ l.filter nsp = [] ∨ l.filter nsp = [35]

theorem strip_head (l : List Nat) : ∀ x r, l.dropWhile PyLean.UnicodeObj.isSpace = x :: r → nsp x = true := by
  induction l with
  | nil => intro x r h; simp at h
  | cons y t ih =>
    intro x r h
    simp only [List.dropWhile_cons] at h
    cases hs : PyLean.UnicodeObj.isSpace y with
    | true =>
      rw [hs] at h
      exact ih x r (by simpa using h)
    | false =>
      rw [hs] at h
      simp only [Bool.false_eq_true, if_false, List.cons.injEq] at h
      obtain ⟨rfl, _⟩ := h
      simp [nsp, hs]

theorem isLineJunkDoc_proven : IsLineJunkDoc := by
  intro l
  have h1 := filter_strip l
  simp only [isLineJunk]
  generalize hs : stripS l = s at h1
  rw [← h1]
  have ends : ∀ x r, s = x :: r → nsp x = true ∧ ∀ y t, r = t ++ [y] → nsp y = true := by
    intro x r e
    have hd : (l.dropWhile PyLean.UnicodeObj.isSpace).reverse.dropWhile PyLean.UnicodeObj.isSpace = (x :: r).reverse := by
      rw [← e, ← hs]
      simp [stripS, rstripS]
    constructor
    · generalize hw : l.dropWhile PyLean.UnicodeObj.isSpace = w at hd
      have h2 := List.dropWhile_suffix PyLean.UnicodeObj.isSpace (l := w.reverse)
      rw [hd] at h2
      have h3 : x :: r <+: w := by
        have := List.reverse_prefix.mpr h2
        simpa using this
      obtain ⟨u, rfl⟩ := h3
      exact strip_head l x (r ++ u) (by simpa using hw)
    · intro y t ert
      have : (x :: r).reverse = y :: (x :: t).reverse := by simp [ert]
      rw [this] at hd
      exact strip_head _ _ _ hd
  constructor
  · intro h
    simp only [Bool.or_eq_true, List.isEmpty_iff, beq_iff_eq] at h
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by decide +kernel)
  · intro h
    simp only [Bool.or_eq_true, List.isEmpty_iff, beq_iff_eq]
    cases s with
    | nil => exact Or.inl rfl
    | cons x r =>
      obtain ⟨e1, e2⟩ := ends x r rfl
      rw [List.filter_cons_of_pos e1] at h
      rcases h with h | h
      · cases h
      · simp only [List.cons.injEq] at h
        obtain ⟨rfl, h3⟩ := h
        right
        cases hr : r.reverse with
        | nil =>
          have : r = [] := by simpa using hr
          rw [this]
        | cons y t =>
          have er : r = t.reverse ++ [y] := by
            have := congrArg List.reverse hr
            simpa using this
          have hy := e2 y _ er
          have hm : y ∈ r.filter nsp := List.mem_filter.mpr ⟨by simp [er], hy⟩
          rw [h3] at hm
          cases hm

end PyLean.TextLibs.Difflib
