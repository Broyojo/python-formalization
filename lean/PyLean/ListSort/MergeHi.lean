import PyLean.ListSort.MergeLo
import PyLean.ListSort.CountRun

/-!
# `merge_hi` is a stable merge

The mirror image of `MergeLo.lean`. The model keeps the unmerged parts of the
runs reversed (`Ar`, `Br`), so `A = Ar.reverse`, `B = Br.reverse`; the gallops
search `A` from its right end (`hint = na - 1`).
-/

namespace PyLean.ListSort

variable {α : Type}

theorem getD_rev (Ar : List α) (d : α) (i : Nat) (hi : i < Ar.reverse.length) :
    Ar.getD (Ar.length - 1 - i) d = Ar.reverse[i] := by
  rw [List.getElem_reverse]
  simp only [List.length_reverse] at hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show Ar.length - 1 - i < Ar.length by omega)]

theorem gallopRight_rev (kf : α → Int) (b : α) (Ar : List α) (ms : MS) (hs : Sorted kf Ar.reverse)
    (hne : Ar ≠ []) :
    (gallopRight (ltOf kf) b (fun i => Ar.getD (Ar.length - 1 - i) b) Ar.length (Ar.length - 1) ms).1 =
      (Ar.reverse.takeWhile (fun x => decide (kf x ≤ kf b))).length := by
  have hl : 0 < Ar.length := List.length_pos_iff.2 hne
  have := gallopRight_spec kf b Ar.reverse (fun i => Ar.getD (Ar.length - 1 - i) b) (Ar.length - 1) ms hs
    (fun i hi => getD_rev Ar b i hi) (by simp; omega)
  simpa only [List.length_reverse] using this

theorem gallopLeft_rev (kf : α → Int) (a : α) (Br : List α) (ms : MS) (hs : Sorted kf Br.reverse)
    (hne : Br ≠ []) :
    (gallopLeft (ltOf kf) a (fun i => Br.getD (Br.length - 1 - i) a) Br.length (Br.length - 1) ms).1 =
      (Br.reverse.takeWhile (fun x => decide (kf x < kf a))).length := by
  have hl : 0 < Br.length := List.length_pos_iff.2 hne
  have := gallopLeft_spec kf a Br.reverse (fun i => Br.getD (Br.length - 1 - i) a) (Br.length - 1) ms hs
    (fun i hi => getD_rev Br a i hi) (by simp; omega)
  simpa only [List.length_reverse] using this

theorem rev_split {Ar T D : List α} (h : Ar.reverse = T ++ D) :
    Ar = D.reverse ++ T.reverse ∧ Ar.length - T.length = D.length := by
  have e : Ar = D.reverse ++ T.reverse := by rw [← List.reverse_append, ← h, List.reverse_reverse]
  refine ⟨e, ?_⟩
  rw [e]; simp

/-- The common tail of the galloping branches of `merge_hi`. -/
theorem hi_gallop_compose (kf : α → Int) {A'' D T2 D2 Rest : List α} {a b : α}
    (hT : Sorted kf (A'' ++ [a])) (hTb : ∀ x ∈ A'' ++ [a], kf x ≤ kf b)
    (hTD : ∀ x ∈ A'' ++ [a], ∀ y ∈ D, kf x ≤ kf y)
    (hD : Sorted kf D) (hbD : ∀ x ∈ D, kf b < kf x)
    (hB : Sorted kf (T2 ++ D2)) (hBb : ∀ y ∈ T2 ++ D2, kf y ≤ kf b)
    (hT2 : ∀ y ∈ T2, kf y < kf a) (hD2 : ∀ y ∈ D2, kf a ≤ kf y)
    (hR : SS kf (A'' ++ T2) Rest) :
    SS kf ((A'' ++ [a]) ++ D ++ (T2 ++ D2 ++ [b])) (Rest ++ [a] ++ D2 ++ [b] ++ D) := by
  obtain ⟨hT2s, hD2s, hT2D2⟩ := sorted_append.1 hB
  have hA''a : ∀ x ∈ A'', kf x ≤ kf a := fun x hx => (sorted_append.1 hT).2.2 x hx a (by simp)
  have s1 : SS kf (A'' ++ [a] ++ T2) (Rest ++ [a]) :=
    ss_mid_suffix (sorted_single kf a)
      (fun x hx y hy => by simp at hy; subst hy; exact hA''a x hx)
      (fun x hx y hy => by simp at hy; subst hy; exact hT2 x hx) hR
  have s2 : SS kf (A'' ++ [a] ++ T2 ++ D2) (Rest ++ [a] ++ D2) :=
    ss_suffix hD2s
      (fun y hy x hx => by
        rcases List.mem_append.1 hy with hy | hy
        · have := hD2 x hx
          rcases List.mem_append.1 hy with hy | hy
          · have := hA''a y hy; omega
          · simp at hy; subst hy; omega
        · exact hT2D2 y hy x hx) s1
  have s3 : SS kf (A'' ++ [a] ++ T2 ++ D2 ++ [b]) (Rest ++ [a] ++ D2 ++ [b]) :=
    ss_suffix (sorted_single kf b)
      (fun y hy x hx => by
        simp at hx; subst hx
        rcases List.mem_append.1 hy with hy | hy
        · rcases List.mem_append.1 hy with hy | hy
          · rcases List.mem_append.1 hy with hy | hy
            · exact hTb y (by simp [hy])
            · simp at hy; subst hy; exact hTb y (by simp)
          · exact hBb y (by simp [hy])
        · exact hBb y (by simp [hy])) s2
  have s4 := ss_mid_suffix (A := A'' ++ [a]) (X := D) (B := T2 ++ D2 ++ [b]) hD
    (fun x hx y hy => hTD x hx y hy)
    (fun x hx y hy => by
      have := hbD y hy
      rcases List.mem_append.1 hx with hx | hx
      · have := hBb x hx; omega
      · simp at hx; subst hx; omega)
    (by simpa using s3)
  simpa using s4

theorem hiLoop_spec (kf : α → Int) :
    ∀ (fuel : Nat) (g : Bool) (mg ac bc : Nat) (out Ar Br : List α) (ms : MS),
      Sorted kf Ar.reverse → Sorted kf Br.reverse → Ar ≠ [] → 2 ≤ Br.length →
      (∀ b0, Br.getLast? = some b0 → ∀ y ∈ Ar, kf b0 < kf y) → Ar.length + Br.length ≤ fuel →
      ∃ R, (hiLoop (ltOf kf) fuel g mg ac bc out Ar Br ms).1 = R ++ out ∧
        SS kf (Ar.reverse ++ Br.reverse) R := by
  intro fuel
  induction fuel with
  | zero => intro g mg ac bc out Ar Br ms _ _ _ hB _ hf; omega
  | succ fuel ih =>
    intro g mg ac bc out Ar Br ms hA hB hAne hlB hfirst hf
    cases g with
    | false =>
      match Ar, Br, hAne, hlB with
      | a :: Ar', b :: Br', _, hlB =>
        simp only [hiLoop, islt, ltOf]
        simp only [List.reverse_cons] at hA hB
        have haA : ∀ y ∈ Ar'.reverse, kf y ≤ kf a := fun y hy => (sorted_append.1 hA).2.2 y hy a (by simp)
        have hbB : ∀ y ∈ Br'.reverse, kf y ≤ kf b := fun y hy => (sorted_append.1 hB).2.2 y hy b (by simp)
        have hb0 : ∀ b0, Br'.getLast? = some b0 → ∀ y ∈ a :: Ar', kf b0 < kf y := by
          intro b0 h y hy
          apply hfirst b0 _ y hy
          cases Br' with
          | nil => simp at hlB
          | cons c Br'' => rw [List.getLast?_cons_cons]; exact h
        by_cases hc : kf b < kf a
        · simp only [hc, decide_true, ↓reduceIte]
          have hBa : ∀ y ∈ Br'.reverse ++ [b], kf y < kf a := by
            intro y hy
            rcases List.mem_append.1 hy with hy | hy
            · have := hbB y hy; omega
            · simp at hy; subst hy; exact hc
          split
          · rename_i hA'; subst hA'
            refine ⟨Br'.reverse ++ [b] ++ [a], by simp, ?_⟩
            have := ss_swap (Sorted.ss (sorted_single kf a)) (Sorted.ss hB)
              (fun x hx y hy => by simp at hy; subst hy; exact hBa x hx)
            simpa using this
          · rename_i hA'
            have key : ∀ g' mg' ac' bc' (ms' : MS), ∃ R, (hiLoop (ltOf kf) fuel g' mg' ac' bc' (a :: out) Ar'
                (b :: Br') ms').1 = R ++ (a :: out) ∧ SS kf (Ar'.reverse ++ (b :: Br').reverse) R :=
              fun g' mg' ac' bc' ms' => ih _ _ _ _ _ _ _ _ (sorted_append.1 hA).1
                (by simpa using hB) hA' (by simpa using hlB)
                (fun b0 h y hy => hfirst b0 h y (by simp [hy])) (by simp at hf ⊢; omega)
            have hfin : ∀ R, SS kf (Ar'.reverse ++ (b :: Br').reverse) R →
                SS kf (Ar'.reverse ++ [a] ++ (Br'.reverse ++ [b])) (R ++ [a]) := by
              intro R hR
              exact ss_mid_suffix (sorted_single kf a)
                (fun x hx y hy => by simp at hy; subst hy; exact haA x hx)
                (fun x hx y hy => by simp at hy; subst hy; exact hBa x hx) (by simpa using hR)
            split
            · obtain ⟨R, h1, h2⟩ := key true _ _ _ _
              exact ⟨R ++ [a], by rw [h1]; simp, by simpa using hfin R h2⟩
            · obtain ⟨R, h1, h2⟩ := key false _ _ _ _
              exact ⟨R ++ [a], by rw [h1]; simp, by simpa using hfin R h2⟩
        · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
          have hAb : ∀ y ∈ Ar'.reverse ++ [a], kf y ≤ kf b := by
            intro y hy
            rcases List.mem_append.1 hy with hy | hy
            · have := haA y hy; omega
            · simp at hy; subst hy; omega
          split
          · rename_i hB1
            obtain ⟨b0, rfl⟩ : ∃ b0, Br' = [b0] := by
              match Br', hB1 with
              | [x], _ => exact ⟨x, rfl⟩
            refine ⟨[b0] ++ (Ar'.reverse ++ [a]) ++ [b], by simp, ?_⟩
            have hsw : SS kf ((Ar'.reverse ++ [a]) ++ [b0]) ([b0] ++ (Ar'.reverse ++ [a])) :=
              ss_swap (Sorted.ss hA) (Sorted.ss (sorted_single kf b0))
                (fun x hx y hy => by
                  simp at hx; subst hx
                  exact hfirst x (by simp) y (by simp at hy ⊢; exact hy.symm))
            have := ss_suffix (X := [b]) (sorted_single kf b)
              (fun y hy x hx => by
                simp at hx; subst hx
                rcases List.mem_append.1 hy with hy | hy
                · exact hAb y hy
                · simp at hy; subst hy; exact hbB y (by simp)) hsw
            simpa using this
          · rename_i hB1
            have hlB' : 2 ≤ Br'.length := by
              have : Br'.length ≠ 0 := by simp at hlB; omega
              omega
            have key : ∀ g' mg' ac' bc' (ms' : MS), ∃ R, (hiLoop (ltOf kf) fuel g' mg' ac' bc' (b :: out)
                (a :: Ar') Br' ms').1 = R ++ (b :: out) ∧ SS kf ((a :: Ar').reverse ++ Br'.reverse) R :=
              fun g' mg' ac' bc' ms' => ih _ _ _ _ _ _ _ _ (by simpa using hA)
                (sorted_append.1 hB).1 (by simp) hlB' hb0 (by simp at hf ⊢; omega)
            have hfin : ∀ R, SS kf ((a :: Ar').reverse ++ Br'.reverse) R →
                SS kf (Ar'.reverse ++ [a] ++ (Br'.reverse ++ [b])) (R ++ [b]) := by
              intro R hR
              have := ss_suffix (X := [b]) (sorted_single kf b)
                (fun y hy x hx => by
                  simp at hx; subst hx
                  rcases List.mem_append.1 hy with hy | hy
                  · exact hAb y (by simpa using hy)
                  · exact hbB y hy) hR
              simpa using this
            split
            · obtain ⟨R, h1, h2⟩ := key true _ _ _ _
              exact ⟨R ++ [b], by rw [h1]; simp, by simpa using hfin R h2⟩
            · obtain ⟨R, h1, h2⟩ := key false _ _ _ _
              exact ⟨R ++ [b], by rw [h1]; simp, by simpa using hfin R h2⟩
    | true =>
      match Br, hlB with
      | b :: Br', hlB =>
        simp only [hiLoop]
        rw [gallopRight_rev kf b Ar _ hA hAne]
        have hsp := split_of kf Ar.reverse _ hA (sorted_pairwise_le kf b hA)
        generalize Ar.reverse.takeWhile (fun x => decide (kf x ≤ kf b)) = T at hsp
        generalize Ar.reverse.dropWhile (fun x => decide (kf x ≤ kf b)) = D at hsp
        obtain ⟨hAe, hTs, hDs, hTD, hpT, hpD⟩ := hsp
        obtain ⟨hAr, hlen⟩ := rev_split hAe
        rw [hlen]
        subst hAr
        have hTb : ∀ x ∈ T, kf x ≤ kf b := fun x hx => by simpa using hpT x hx
        have hbD : ∀ x ∈ D, kf b < kf x := fun x hx => by have := hpD x hx; simp at this; omega
        simp only [List.reverse_cons] at hB
        have hbB : ∀ y ∈ Br'.reverse, kf y ≤ kf b := fun y hy => (sorted_append.1 hB).2.2 y hy b (by simp)
        have htk : (D.reverse ++ T.reverse).take D.length = D.reverse :=
          List.take_left' (by simp)
        have hdr : (D.reverse ++ T.reverse).drop D.length = T.reverse :=
          List.drop_left' (by simp)
        rw [htk, hdr, List.reverse_reverse]
        have hb0 : ∀ b0, Br'.getLast? = some b0 → ∀ y ∈ T ++ D, kf b0 < kf y := by
          intro b0 h y hy
          apply hfirst b0 _ y (by simp at hy ⊢; exact hy.symm)
          cases Br' with
          | nil => simp at hlB
          | cons c Br'' => rw [List.getLast?_cons_cons]; exact h
        have hBD : ∀ y ∈ Br'.reverse ++ [b], ∀ x ∈ D, kf y < kf x := by
          intro y hy x hx
          have := hbD x hx
          rcases List.mem_append.1 hy with hy | hy
          · have := hbB y hy; omega
          · simp at hy; subst hy; exact this
        by_cases hk1 : D.length ≠ 0 ∧ T.reverse = []
        · simp only [hk1, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
          have hT0 : T = [] := List.reverse_eq_nil_iff.1 hk1.2
          subst hT0
          refine ⟨Br'.reverse ++ [b] ++ D, by simp, ?_⟩
          have := ss_swap (Sorted.ss hDs) (Sorted.ss hB) (fun x hx y hy => hBD x hx y hy)
          simpa using this
        simp only [hk1, ↓reduceIte]
        -- copy *ssb
        by_cases hB1 : Br'.length = 1
        · simp only [hB1, ↓reduceIte]
          obtain ⟨b0, rfl⟩ : ∃ b0, Br' = [b0] := by
            match Br', hB1 with
            | [x], _ => exact ⟨x, rfl⟩
          refine ⟨[b0] ++ T ++ [b] ++ D, by simp, ?_⟩
          have hsw : SS kf (T ++ [b0]) ([b0] ++ T) :=
            ss_swap (Sorted.ss hTs) (Sorted.ss (sorted_single kf b0))
              (fun x hx y hy => by simp at hx; subst hx; exact hb0 x (by simp) y (by simp [hy]))
          have s1 : SS kf (T ++ [b0] ++ [b]) ([b0] ++ T ++ [b]) :=
            ss_suffix (sorted_single kf b)
              (fun y hy x hx => by
                simp at hx; subst hx
                rcases List.mem_append.1 hy with hy | hy
                · exact hTb y hy
                · simp at hy; subst hy; exact hbB y (by simp)) hsw
          have := ss_mid_suffix (A := T) (X := D) (B := [b0] ++ [b]) hDs hTD
            (fun x hx y hy => hBD x (by simpa using hx) y hy) (by simpa using s1)
          simpa using this
        simp only [hB1, ↓reduceIte]
        match hTr : T.reverse with
        | [] =>
          simp only
          have hT0 : T = [] := List.reverse_eq_nil_iff.1 hTr
          subst hT0
          refine ⟨Br'.reverse ++ [b] ++ D, by simp, ?_⟩
          have := ss_swap (Sorted.ss hDs) (Sorted.ss hB) (fun x hx y hy => hBD x hx y hy)
          simpa using this
        | a :: Ar'' =>
          simp only
          have hTe : T = Ar''.reverse ++ [a] := by
            rw [← List.reverse_reverse T, hTr]; simp
          subst hTe
          have hBr'ne : Br' ≠ [] := by intro h; subst h; simp at hlB
          have hB's : Sorted kf Br'.reverse := (sorted_append.1 hB).1
          rw [gallopLeft_rev kf a Br' _ hB's hBr'ne]
          have hsp2 := split_of kf Br'.reverse _ hB's (sorted_pairwise_lt kf a hB's)
          generalize Br'.reverse.takeWhile (fun x => decide (kf x < kf a)) = T2 at hsp2
          generalize Br'.reverse.dropWhile (fun x => decide (kf x < kf a)) = D2 at hsp2
          obtain ⟨hBe, hT2s, hD2s, hT2D2, hpT2, hpD2⟩ := hsp2
          obtain ⟨hBr, hlen2⟩ := rev_split hBe
          rw [hlen2]
          have hT2a : ∀ y ∈ T2, kf y < kf a := fun y hy => by simpa using hpT2 y hy
          have hD2a : ∀ y ∈ D2, kf a ≤ kf y := fun y hy => by have := hpD2 y hy; simp at this; omega
          have hBb2 : ∀ y ∈ T2 ++ D2, kf y ≤ kf b := fun y hy => hbB y (by rw [hBe]; exact hy)
          have hB2s : Sorted kf (T2 ++ D2) := hBe ▸ hB's
          have compose := fun Rest (hR : SS kf (Ar''.reverse ++ T2) Rest) =>
            hi_gallop_compose kf hTs hTb hTD hDs hbD hB2s hBb2 hT2a hD2a hR
          -- the first item of B is the first of T2 when T2 is non-empty
          have hfirstT2 : ∀ b0, T2.reverse.getLast? = some b0 → ∀ y ∈ Ar''.reverse ++ [a] ++ D, kf b0 < kf y := by
            intro b0 h y hy
            apply hb0 b0 _ y hy
            rw [hBr, List.getLast?_append, h]
            rfl
          subst hBr
          have htk2 : (D2.reverse ++ T2.reverse).take D2.length = D2.reverse := List.take_left' (by simp)
          have hdr2 : (D2.reverse ++ T2.reverse).drop D2.length = T2.reverse := List.drop_left' (by simp)
          rw [htk2, hdr2, List.reverse_reverse]
          by_cases hk2 : D2.length ≠ 0 ∧ T2.reverse.length = 1
          · simp only [hk2, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
            obtain ⟨b0, hb0e⟩ : ∃ b0, T2 = [b0] := by
              have hl1 : T2.length = 1 := by simpa using hk2.2
              match T2, hl1 with
              | [x], _ => exact ⟨x, rfl⟩
            subst hb0e
            refine ⟨[b0] ++ Ar''.reverse ++ [a] ++ D2 ++ [b] ++ D, by simp, ?_⟩
            have hsw : SS kf (Ar''.reverse ++ [b0]) ([b0] ++ Ar''.reverse) :=
              ss_swap (Sorted.ss (sorted_append.1 hTs).1) (Sorted.ss (sorted_single kf b0))
                (fun x hx y hy => by
                  simp at hx; subst hx
                  exact hfirstT2 x (by simp) y (by simp [hy]))
            simpa using compose _ hsw
          simp only [hk2, ↓reduceIte]
          by_cases hk3 : D2.length ≠ 0 ∧ T2.reverse = []
          · simp only [hk3, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
            have hT20 : T2 = [] := List.reverse_eq_nil_iff.1 hk3.2
            subst hT20
            refine ⟨Ar''.reverse ++ [a] ++ D2 ++ [b] ++ D, by simp, ?_⟩
            simpa using compose Ar''.reverse (by simpa using Sorted.ss (sorted_append.1 hTs).1)
          simp only [hk3, ↓reduceIte]
          by_cases hA0 : Ar'' = []
          · simp only [hA0, ↓reduceIte]
            subst hA0
            refine ⟨T2 ++ [a] ++ D2 ++ [b] ++ D, by simp, ?_⟩
            simpa using compose T2 (by simpa using Sorted.ss hT2s)
          simp only [hA0, ↓reduceIte]
          have hlT2 : 2 ≤ T2.reverse.length := by
            have e1 : T2.reverse = [] ↔ T2.length = 0 := by simp
            simp only [List.length_reverse, List.length_append, List.length_cons, ne_eq, e1] at hk2 hk3 hB1 hlB ⊢
            omega
          have key : ∀ (g' : Bool) (mg' : Nat) (out' : List α) (ms' : MS),
              out' = a :: (D2 ++ (b :: (D ++ out))) →
              ∃ R, (hiLoop (ltOf kf) fuel g' mg' 0 0 out' Ar'' T2.reverse ms').1 = R ++ out ∧
                SS kf ((D.reverse ++ a :: Ar'').reverse ++ (b :: (D2.reverse ++ T2.reverse)).reverse) R := by
            intro g' mg' out' ms' hout
            obtain ⟨R, h1, h2⟩ := ih g' mg' 0 0 out' Ar'' T2.reverse ms' (sorted_append.1 hTs).1
              (by simpa using hT2s) hA0 hlT2
              (fun b0 h y hy => hfirstT2 b0 h y (by simp [hy]))
              (by simp only [List.length_append, List.length_reverse, List.length_cons] at hf ⊢; omega)
            have hE : (D.reverse ++ a :: Ar'').reverse ++ (b :: (D2.reverse ++ T2.reverse)).reverse =
                (Ar''.reverse ++ [a]) ++ D ++ (T2 ++ D2 ++ [b]) := by simp
            refine ⟨R ++ [a] ++ D2 ++ [b] ++ D, by rw [h1, hout]; simp, ?_⟩
            rw [hE]
            simpa using compose R (by simpa using h2)
          split
          · exact key _ _ _ _ rfl
          · exact key _ _ _ _ rfl

/-- `merge_hi` under the preconditions `merge_at` establishes. -/
theorem mergeHi_spec (kf : α → Int) (A B : List α) (ms : MS) (hA : Sorted kf A) (hB : Sorted kf B)
    (hAne : A ≠ []) (hfirst : ∀ b, B.head? = some b → ∀ y ∈ A, kf b < kf y)
    (hlast : ∀ b ∈ B, ∀ x, A.getLast? = some x → kf b < kf x) (hBne : B ≠ []) :
    SS kf (A ++ B) (mergeHi (ltOf kf) A B ms).1 := by
  simp only [mergeHi]
  match hAr : A.reverse with
  | [] => simp at hAr; exact absurd hAr hAne
  | a :: Ar' =>
    simp only
    have hAe : A = Ar'.reverse ++ [a] := by rw [← List.reverse_reverse A, hAr]; simp
    subst hAe
    have hBa : ∀ y ∈ B, kf y < kf a := fun y hy => hlast y hy a (by simp)
    have haA : ∀ y ∈ Ar'.reverse, kf y ≤ kf a := fun y hy => (sorted_append.1 hA).2.2 y hy a (by simp)
    split
    · rename_i hA'; subst hA'
      have := ss_swap (Sorted.ss (sorted_single kf a)) (Sorted.ss hB)
        (fun x hx y hy => by simp at hy; subst hy; exact hBa x hx)
      simpa using this
    split
    · rename_i _ hB1
      obtain ⟨b0, rfl⟩ : ∃ b0, B = [b0] := by
        match B, hB1 with
        | [x], _ => exact ⟨x, rfl⟩
      have := ss_swap (Sorted.ss hA) (Sorted.ss (sorted_single kf b0))
        (fun x hx y hy => by simp at hx; subst hx; exact hfirst x rfl y hy)
      simpa using this
    · rename_i hA' hB1
      have hlB : 2 ≤ B.reverse.length := by
        have : B.length ≠ 0 := fun h => hBne (List.eq_nil_of_length_eq_zero h)
        simp; omega
      obtain ⟨R, h1, h2⟩ := hiLoop_spec kf ((Ar'.reverse ++ [a]).length + B.length + 1) false
        ms.minGallop 0 0 [a] Ar' B.reverse ms (sorted_append.1 hA).1 (by simpa using hB) hA' hlB
        (fun b0 h y hy => hfirst b0 (by rw [List.getLast?_reverse] at h; exact h) y (by simp [hy]))
        (by simp; omega)
      rw [h1]
      have := ss_mid_suffix (A := Ar'.reverse) (X := [a]) (B := B) (sorted_single kf a)
        (fun x hx y hy => by simp at hy; subst hy; exact haA x hx)
        (fun x hx y hy => by simp at hy; subst hy; exact hBa x hx) (by simpa using h2)
      simpa using this

/-- `merge_at` merges two sorted adjacent runs into their stable sort, for every
merge state. -/
theorem mergeAt_spec (kf : α → Int) (A B : List α) (ms : MS) (hA : Sorted kf A) (hB : Sorted kf B)
    (hAne : A ≠ []) (hBne : B ≠ []) : SS kf (A ++ B) (mergeAt (ltOf kf) A B ms).1 := by
  match B, hBne with
  | b0 :: B', _ =>
    simp only [mergeAt]
    rw [gallopRight_spec kf b0 A _ 0 _ hA
      (fun i hi => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      (List.length_pos_iff.2 hAne)]
    have hsp := split_of kf A _ hA (sorted_pairwise_le kf b0 hA)
    rw [(take_drop_of_takeWhile _ A).1, (take_drop_of_takeWhile _ A).2]
    generalize A.takeWhile (fun x => decide (kf x ≤ kf b0)) = T at hsp
    generalize A.dropWhile (fun x => decide (kf x ≤ kf b0)) = D at hsp
    obtain ⟨hAe, hTs, hDs, hTD, hpT, hpD⟩ := hsp
    subst hAe
    have hTb : ∀ x ∈ T, kf x ≤ kf b0 := fun x hx => by simpa using hpT x hx
    have hbD : ∀ x ∈ D, kf b0 < kf x := fun x hx => by have := hpD x hx; simp at this; omega
    have hbB : ∀ y ∈ B', kf b0 ≤ kf y := (sorted_cons.1 hB).1
    have hTB : ∀ x ∈ T, ∀ y ∈ b0 :: B', kf x ≤ kf y := by
      intro x hx y hy
      have := hTb x hx
      rcases List.mem_cons.1 hy with rfl | hy
      · exact this
      · have := hbB y hy; omega
    match hD : D.getLast? with
    | none =>
      simp only
      rw [List.getLast?_eq_none_iff] at hD
      subst hD
      simpa using Sorted.ss (sorted_append.2 ⟨hTs, hB, hTB⟩)
    | some alast =>
      simp only
      have hDne : D ≠ [] := by intro h; subst h; simp at hD
      have hDl : ∀ x ∈ D, kf x ≤ kf alast := by
        intro x hx
        have h1 := le_getLast_of_sorted kf D hDne hDs x hx
        have h2 : D.getLast hDne = alast := by
          rw [List.getLast?_eq_some_getLast hDne] at hD; exact Option.some.inj hD
        rw [h2] at h1; exact h1
      rw [gallopLeft_spec kf alast (b0 :: B') _ _ _ hB
        (fun i hi => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]) (by simp)]
      have hsp2 := split_of kf (b0 :: B') _ hB (sorted_pairwise_lt kf alast hB)
      rw [(take_drop_of_takeWhile _ (b0 :: B')).1, (take_drop_of_takeWhile _ (b0 :: B')).2]
      generalize (b0 :: B').takeWhile (fun x => decide (kf x < kf alast)) = T2 at hsp2
      generalize (b0 :: B').dropWhile (fun x => decide (kf x < kf alast)) = D2 at hsp2
      obtain ⟨hBe, hT2s, hD2s, hT2D2, hpT2, hpD2⟩ := hsp2
      rw [hBe]
      have hT2a : ∀ y ∈ T2, kf y < kf alast := fun y hy => by simpa using hpT2 y hy
      have hD2a : ∀ y ∈ D2, kf alast ≤ kf y := fun y hy => by have := hpD2 y hy; simp at this; omega
      split
      · rename_i h0
        have hT20 : T2 = [] := List.eq_nil_of_length_eq_zero h0
        subst hT20
        simp only [List.nil_append] at hBe ⊢
        apply Sorted.ss
        refine sorted_append.2 ⟨sorted_append.2 ⟨hTs, hDs, hTD⟩, hD2s, fun x hx y hy => ?_⟩
        rcases List.mem_append.1 hx with hx | hx
        · exact hTB x hx y (by rw [hBe]; exact hy)
        · have := hDl x hx; have := hD2a y hy; omega
      · rename_i h0
        have hT2ne : T2 ≠ [] := fun h => h0 (by simp [h])
        have hT2h : T2.head? = some b0 := by
          cases T2 with
          | nil => exact absurd rfl hT2ne
          | cons c T2' => simp at hBe ⊢; exact hBe.1.symm
        have hfirst : ∀ b, T2.head? = some b → ∀ y ∈ D, kf b < kf y := by
          intro b h y hy; rw [hT2h] at h; cases h; exact hbD y hy
        have hlastT2 : ∀ b ∈ T2, ∀ x, D.getLast? = some x → kf b < kf x := by
          intro b hb x hx; rw [hD] at hx; cases hx; exact hT2a b hb
        have hm : ∀ ms', SS kf (D ++ T2) (if D.length ≤ T2.length then mergeLo (ltOf kf) D T2 ms'
            else mergeHi (ltOf kf) D T2 ms').1 := by
          intro ms'
          split
          · exact mergeLo_spec kf D T2 ms' hDs hT2s hDne hfirst hlastT2 hT2ne
          · exact mergeHi_spec kf D T2 ms' hDs hT2s hDne hfirst hlastT2 hT2ne
        have fin : ∀ P : List α × MS, SS kf (D ++ T2) P.1 →
            SS kf (T ++ D ++ (T2 ++ D2)) (T ++ P.1 ++ D2) := by
          intro P hMs
          generalize P.1 = m at hMs ⊢
          have s1 : SS kf (D ++ T2 ++ D2) (m ++ D2) :=
            ss_suffix hD2s (fun y hy x hx => by
              rcases List.mem_append.1 hy with hy | hy
              · have := hDl y hy; have := hD2a x hx; omega
              · exact hT2D2 y hy x hx) hMs
          have s2 := ss_prefix (X := T) hTs (fun x hx y hy => by
            rcases List.mem_append.1 hy with hy | hy
            · rcases List.mem_append.1 hy with hy | hy
              · exact hTD x hx y hy
              · exact hTB x hx y (by rw [hBe]; simp [hy])
            · exact hTB x hx y (by rw [hBe]; simp [hy])) s1
          simpa using s2
        exact fin _ (hm _)

end PyLean.ListSort
