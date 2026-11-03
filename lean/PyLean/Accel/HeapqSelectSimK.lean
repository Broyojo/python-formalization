import PyLean.Accel.HeapqSelectSim

/-!
The keyed heap path of `nsmallest` / `nlargest` (`(key(elem), order, elem)` tuples), as the
generic selection on codes. Keys are ranked in the universe `default :: κ default :: xs.map κ`,
which holds the key of every code (`keyOf`; code `0` decodes to the tuple `default`).
-/

namespace PyLean.Accel.Heapq

open PyLean

variable {α : Type} [DecidableEq α] [Inhabited α]

def keyOf (xs : List α) (κ : α → α) (c : Int) : α := if c.toNat = 0 then default else κ (dcd xs c)

def φ3 (xs : List α) (κ : α → α) (t : Int × Int) : α × Int × α := (keyOf xs κ t.1, t.2, dcd xs t.1)

theorem φ3_default (xs : List α) (κ : α → α) : φ3 xs κ default = default := by
  simp [φ3, keyOf, dcd]; rfl

def KU (xs : List α) (κ : α → α) : List α := default :: κ default :: xs.map κ

theorem keyOf_mem (xs : List α) (κ : α → α) (c : Int) : keyOf xs κ c ∈ KU xs κ := by
  simp only [keyOf, KU]
  split
  · simp
  · have := dcd_mem xs c
    rcases List.mem_cons.1 this with h | h
    · rw [h]; simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem h))

theorem keyOf_pos (xs : List α) (κ : α → α) (c : Int) (h : 1 ≤ c) : keyOf xs κ c = κ (dcd xs c) := by
  simp only [keyOf]; rw [if_neg (by omega)]

def rkK (r : α → α → Bool) (xs : List α) (κ : α → α) (a : α) : Int := (rank r (KU xs κ) a : Int)

theorem rkK_spec {r : α → α → Bool} (hr : Accel.StrictWeak r) (xs : List α) (κ : α → α) (c c' : Int) :
    r (keyOf xs κ c) (keyOf xs κ c') = decide (rkK r xs κ (keyOf xs κ c) < rkK r xs κ (keyOf xs κ c')) := by
  rw [rank_spec hr _ (keyOf_mem xs κ c) (keyOf_mem xs κ c')]
  simp [rkK]

/-- The selection spec for the keyed branch. -/
def sS3 (xs : List α) (r : α → α → Bool) (κ : α → α) (large : Bool) : Accel.SelSpec (Int × Int) where
  lt := if large then Accel.maxLt (fun a b => lt3P r (φ3 xs κ a) (φ3 xs κ b))
    else fun a b => lt3P r (φ3 xs κ a) (φ3 xs κ b)
  dec e o := (e, o)
  eOf t := t.1
  topOf t := if large then -rkK r xs κ (keyOf xs κ t.1) else rkK r xs κ (keyOf xs κ t.1)
  kf e := if large then -rkK r xs κ (keyOf xs κ e) else rkK r xs κ (keyOf xs κ e)
  tagf o := if large then -o else o
  ostep o := if large then o - 1 else o + 1
  ord0 i := if large then -(i : Int) else (i : Int)

theorem lexInt_ne (o o' : Int) (b : Bool) (h : o ≠ o') :
    (intLtB o o' || (!intLtB o o' && !intLtB o' o && b)) = decide (o < o') := by
  simp only [intLtB]
  by_cases h2 : o < o'
  · simp [h2]
  · have : o' < o := by omega
    simp [h2, this]

theorem sS3_good {r : α → α → Bool} (hr : Accel.StrictWeak r) (xs : List α) (κ : α → α) (large : Bool) :
    (sS3 xs r κ large).Good where
  sw := by
    cases large
    · exact StrictWeak.pullback (strictWeak_lt3P hr) (φ3 xs κ)
    · exact (StrictWeak.pullback (strictWeak_lt3P hr) (φ3 xs κ)).maxLt
  eOf_dec _ _ := rfl
  topOf_dec _ _ := rfl
  lt_dec e e' o o' ho := by
    have h1 := rkK_spec hr xs κ e e'
    have h2 := rkK_spec hr xs κ e' e
    cases large
    · have ho' : o ≠ o' := by simpa [sS3] using ho
      simp only [sS3, Bool.false_eq_true, if_false, lt3P, lexLt, φ3]
      rw [lexInt_ne o o' _ ho']
      rw [lex_rank r hr _ _ _ _ h1 h2]
      exact bool_lex _ _ _ _
    · have ho' : o' ≠ o := by simp [sS3] at ho; omega
      simp only [sS3, if_true, Accel.maxLt, lt3P, lexLt, φ3]
      rw [lexInt_ne o' o _ ho']
      rw [lex_rank r hr _ _ _ _ h2 h1]
      exact bool_lex_neg _ _ _ _
  lt_key e e' o o' h := by
    have h1 := rkK_spec hr xs κ e e'
    have h2 := rkK_spec hr xs κ e' e
    cases large
    · simp only [sS3, Bool.false_eq_true, if_false] at h ⊢
      simp only [lt3P, lexLt, φ3, h1, h2]
      have : ¬ rkK r xs κ (keyOf xs κ e) < rkK r xs κ (keyOf xs κ e') := by omega
      simp [this, h]
    · simp only [sS3, if_true] at h ⊢
      simp only [Accel.maxLt, lt3P, lexLt, φ3, h1, h2]
      have : ¬ rkK r xs κ (keyOf xs κ e') < rkK r xs κ (keyOf xs κ e) := by omega
      have h' : rkK r xs κ (keyOf xs κ e) < rkK r xs κ (keyOf xs κ e') := by omega
      simp [this, h']
  tag_step o := by cases large <;> simp [sS3] <;> omega
  tag_ord0 i := by cases large <;> simp [sS3]

theorem heapOrd_sS3 (xs : List α) (r : α → α → Bool) (κ : α → α) (large : Bool) (a b : Int × Int) :
    heapOrd (!large) (lt3P r) (φ3 xs κ a) (φ3 xs κ b) = Accel.maxLt (sS3 xs r κ large).lt a b := by
  cases large <;> rfl

theorem lt3_hEnv_fun (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (hr : Accel.StrictWeak r) :
    lt3 (hEnv xs r lr) = fun a b => pure (lt3P r a b) :=
  funext fun a => funext fun b => lt3_hEnv xs r lr hr a b

theorem keyOf_succ (xs : List α) (κ : α → α) (p : Nat) (h : p < xs.length) :
    keyOf xs κ ((p + 1 : Nat) : Int) = κ xs[p] := by
  rw [keyOf_pos xs κ _ (by omega), dcd_succ xs p h]

theorem selLoop3_sim (xs : List α) (r : α → α → Bool) (κ : α → α) (lr : Except PyExc Nat)
    (hr : Accel.StrictWeak r) (impl large : Bool) :
    ∀ (fuel p : Nat) (R : List (Int × Int)) (t order : Int), R ≠ [] → p ≤ xs.length →
      xs.length - p < fuel →
      ∃ R', Accel.selLoop (sS3 xs r κ large) R ((sS3 xs r κ large).topOf (t, 0)) order ((codes xs).drop p) = .ok R' ∧
        ((selLoop3 (hEnv xs r lr) impl large (pureKey κ) .it fuel (R.map (φ3 xs κ)) (keyOf xs κ t) order).run p).1 =
          .ok (R'.map (φ3 xs κ)) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro p R t order hR hp hf
    simp only [selLoop3]
    rw [Eff.run_bind_ok (nextOpt_hEnv xs r lr p)]
    by_cases hlt : p < xs.length
    · rw [List.getElem?_eq_getElem hlt, if_pos hlt, codes_drop xs p hlt]
      simp only [pureKey, Eff.pure_bind]
      have hk0 : κ xs[p] = keyOf xs κ ((p + 1 : Nat) : Int) := (keyOf_succ xs κ p hlt).symm
      have hcond : (if large then r (keyOf xs κ t) (κ xs[p]) else r (κ xs[p]) (keyOf xs κ t)) =
          decide ((sS3 xs r κ large).kf ((p + 1 : Nat) : Int) < (sS3 xs r κ large).topOf (t, 0)) := by
        rw [hk0]
        cases large
        · simp only [sS3, Bool.false_eq_true, if_false]; exact rkK_spec hr xs κ _ _
        · simp only [sS3, if_true]; rw [rkK_spec hr xs κ _ _]; simp only [decide_eq_decide]; omega
      have hc : cmpTop (hEnv xs r lr) large (keyOf xs κ t) (κ xs[p]) =
          pure (decide ((sS3 xs r κ large).kf ((p + 1 : Nat) : Int) < (sS3 xs r κ large).topOf (t, 0))) := by
        rw [← hcond]; cases large <;> rfl
      rw [hc, Eff.pure_bind]
      simp only [Accel.selLoop]
      by_cases hk : (sS3 xs r κ large).kf ((p + 1 : Nat) : Int) < (sS3 xs r κ large).topOf (t, 0)
      · rw [if_pos hk, if_pos (by simpa using hk), lt3_hEnv_fun xs r lr hr]
        have hne : R.map (φ3 xs κ) ≠ [] := by simpa using hR
        rw [Eff.run_bind_ok (hHeapreplace_pure impl (!large) (lt3P r) _ _ _ hne), reraise_ok,
          Eff.pure_bind]
        simp only
        have hold : Accel.pyHeapreplace (Accel.maxLt (sS3 xs r κ large).lt) R
            ((sS3 xs r κ large).dec ((p + 1 : Nat) : Int) order) =
            .ok (Accel.at! R 0, Accel.pySiftup (Accel.maxLt (sS3 xs r κ large).lt)
              (R.set 0 (((p + 1 : Nat) : Int), order)) 0) := by
          cases R with
          | nil => exact absurd rfl hR
          | cons y ys => rfl
        rw [hold]
        simp only [bind, Except.bind]
        have hmap : Accel.pySiftup (heapOrd (!large) (lt3P r)) ((R.map (φ3 xs κ)).set 0 (κ xs[p], order, xs[p])) 0 =
            (Accel.pySiftup (Accel.maxLt (sS3 xs r κ large).lt) (R.set 0 (((p + 1 : Nat) : Int), order)) 0).map
              (φ3 xs κ) := by
          rw [show (κ xs[p], order, xs[p]) = φ3 xs κ (((p + 1 : Nat) : Int), order) by
            simp only [φ3, keyOf_succ xs κ p hlt, dcd_succ xs p hlt], ← List.map_set]
          exact pySiftup_map (φ3 xs κ) (φ3_default xs κ) _ _ (heapOrd_sS3 xs r κ large) _ _
        rw [hmap, at!_map' (φ3 xs κ) (φ3_default xs κ)]
        obtain ⟨R2, hR2def⟩ : ∃ R2, R2 = Accel.pySiftup (Accel.maxLt (sS3 xs r κ large).lt)
            (R.set 0 (((p + 1 : Nat) : Int), order)) 0 := ⟨_, rfl⟩
        rw [← hR2def]
        have hR2 : R2 ≠ [] := by
          apply List.ne_nil_of_length_pos
          rw [hR2def, Accel.pySiftup_length, List.length_set]
          exact List.length_pos_iff.2 hR
        obtain ⟨R', h1, h2⟩ := ih (p + 1) R2 (Accel.at! R2 0).1
          (if large then order - 1 else order + 1) hR2 (by omega) (by omega)
        refine ⟨R', ?_, ?_⟩
        · rw [← h1]; cases large <;> rfl
        · exact h2
      · rw [if_neg hk, if_neg (by simpa using hk)]
        exact ih (p + 1) R t order hR (by omega) (by omega)
    · rw [List.getElem?_eq_none (by omega), if_neg hlt, codes_drop_nil xs p (by omega)]
      exact ⟨R, rfl, rfl⟩

theorem kf_sS3_le (xs : List α) {r : α → α → Bool} (hr : Accel.StrictWeak r) (κ : α → α) (large : Bool)
    (a b : Int) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    decide ((sS3 xs r κ large).kf a ≤ (sS3 xs r κ large).kf b) =
      (if large then !r (κ (dcd xs a)) (κ (dcd xs b)) else !r (κ (dcd xs b)) (κ (dcd xs a))) := by
  rw [← keyOf_pos xs κ a ha, ← keyOf_pos xs κ b hb]
  cases large
  · show decide (rkK r xs κ (keyOf xs κ a) ≤ rkK r xs κ (keyOf xs κ b)) = !r (keyOf xs κ b) (keyOf xs κ a)
    rw [rkK_spec hr xs κ b a]; exact decide_le_not _ _
  · show decide (-rkK r xs κ (keyOf xs κ a) ≤ -rkK r xs κ (keyOf xs κ b)) = !r (keyOf xs κ a) (keyOf xs κ b)
    rw [rkK_spec hr xs κ a b]; exact decide_neg_le_not _ _

theorem stableSort_dcdK (xs : List α) {r : α → α → Bool} (hr : Accel.StrictWeak r) (κ : α → α) (large : Bool) :
    (Accel.stableSort (sS3 xs r κ large).kf (codes xs)).map (dcd xs) =
      xs.mergeSort (fun a b => if large then !r (κ a) (κ b) else !r (κ b) (κ a)) := by
  simp only [Accel.stableSort]
  rw [List.map_mergeSort (s := fun a b => if large then !r (κ a) (κ b) else !r (κ b) (κ a))
    (fun a ha b hb => kf_sS3_le xs hr κ large a b (codes_pos xs a ha) (codes_pos xs b hb)), codes_map]

theorem selHeap_key (xs : List α) (r : α → α → Bool) (κ : α → α) (lr : Except PyExc Nat)
    (hr : Accel.StrictWeak r) (So : Sorter Nat) (hSo : SortOk So) (impl large : Bool) (fuel : Nat) (n : Int)
    (hn : 0 ≤ n) (hf : xs.length < fuel) (w0 : Nat) :
    ((selHeap (hEnv xs r lr) So impl large fuel n .src (some (pureKey κ))).run w0).1 =
      .ok ((xs.mergeSort (fun a b => if large then !r (κ a) (κ b) else !r (κ b) (κ a))).take n.toNat) := by
  let S := sS3 xs r κ large
  have hS := sS3_good hr xs κ large
  have h0 : S.tagf (if large then -n else n) = n.toNat := by
    cases large <;> simp [S, sS3] <;> omega
  have hspec := Accel.selAlgo_spec hS n.toNat (if large then -n else n) h0 (codes xs)
  rw [← stableSort_dcdK xs hr κ large, ← List.map_take]
  rw [show (Except.ok (((Accel.stableSort S.kf (codes xs)).take n.toNat).map (dcd xs)) : Except PyExc (List α)) =
    (Accel.selAlgo S n.toNat (if large then -n else n) (codes xs)).map (List.map (dcd xs)) by rw [hspec]; rfl]
  clear hspec
  simp only [selHeap]
  rw [Eff.run_bind_ok (iter_src_hEnv xs r lr w0), Eff.run_bind_ok (iter_it_hEnv xs r lr 0),
    Eff.run_bind_ok (takeNKey_hEnv xs r lr κ n.toNat 0)]
  simp only [List.drop_zero, Nat.zero_add]
  have hfirst : ((xs.take n.toNat).map (fun x => (κ x, x))).zipIdx.map
      (fun (p : (α × α) × Nat) => (p.1.1, (if large then -(p.2 : Int) else (p.2 : Int)), p.1.2)) =
      (((codes xs).take n.toNat).zipIdx.map (fun (p : Int × Nat) => S.dec p.1 (S.ord0 p.2))).map (φ3 xs κ) := by
    conv => lhs; rw [← codes_map xs]
    rw [← List.map_take, List.map_map, List.zipIdx_map, List.map_map, List.map_map]
    apply List.map_congr_left
    intro p hp
    have hc : 1 ≤ p.1 := codes_pos xs p.1 (List.mem_of_mem_take (List.fst_mem_of_mem_zipIdx hp))
    simp only [Function.comp, Prod.map, φ3, S, sS3, keyOf_pos xs κ p.1 hc]
    rfl
  rw [hfirst]
  simp only [Accel.selAlgo]
  generalize ((codes xs).take n.toNat).zipIdx.map (fun (p : Int × Nat) => S.dec p.1 (S.ord0 p.2)) = R0
  by_cases hR0 : R0 = []
  · subst hR0; rfl
  · have hne : (R0.map (φ3 xs κ)).isEmpty = false := by
      cases R0 with
      | nil => exact absurd rfl hR0
      | cons _ _ => rfl
    rw [hne, if_neg hR0]
    simp only [Bool.false_eq_true, if_false]
    rw [lt3_hEnv_fun xs r lr hr, Eff.run_bind_ok (hHeapify_pure impl (!large) (lt3P r) _ _), reraise_ok,
      Eff.pure_bind]
    simp only
    rw [pyHeapify_map (φ3 xs κ) (φ3_default xs κ) _ _ (heapOrd_sS3 xs r κ large),
      at!_map' (φ3 xs κ) (φ3_default xs κ), Eff.run_bind_ok (iter_it_hEnv xs r lr _)]
    generalize hH : Accel.pyHeapify (Accel.maxLt S.lt) R0 = H
    have hHne : H ≠ [] := by
      rw [← hH]; apply List.ne_nil_of_length_pos
      rw [pyHeapify_length']; exact List.length_pos_iff.2 hR0
    rw [show (φ3 xs κ (Accel.at! H 0)).1 = keyOf xs κ (Accel.at! H 0).1 from rfl]
    generalize hp : min n.toNat (xs.length - 0) = p
    obtain ⟨R', h1, h2⟩ := selLoop3_sim xs r κ lr hr impl large fuel p H
      (Accel.at! H 0).1 (if large then -n else n) hHne (by omega) (by omega)
    have hdrop : (codes xs).drop p = (codes xs).drop n.toNat := by
      by_cases hk : n.toNat ≤ xs.length
      · congr 1; omega
      · rw [codes_drop_nil xs _ (by omega), codes_drop_nil xs _ (by omega)]
    rw [hdrop] at h1
    rcases hrun : (selLoop3 (hEnv xs r lr) impl large (pureKey κ) .it fuel (H.map (φ3 xs κ))
        (keyOf xs κ (Accel.at! H 0).1) (if large then -n else n)).run p with ⟨res, w2⟩
    rw [hrun] at h2
    simp only at h2
    subst h2
    rw [Eff.run_bind_ok hrun]
    have htop : S.topOf (Accel.at! H 0) = S.topOf ((Accel.at! H 0).1, 0) := rfl
    rw [htop, h1]
    rw [Eff.run_bind_ok (hSo _ (lt3P r) large _ w2 (strictWeak_lt3P hr))]
    show (Except.ok (List.map (fun x => x.2.2) (if large then (R'.map (φ3 xs κ)).mergeSort (fun a b => !lt3P r a b)
        else (R'.map (φ3 xs κ)).mergeSort (fun a b => !lt3P r b a))) : Except PyExc (List α)) =
      Except.ok (List.map (dcd xs) (List.map S.eOf (R'.mergeSort fun a b => !S.lt b a)))
    congr 1
    have hms : (if large then (R'.map (φ3 xs κ)).mergeSort (fun a b => !lt3P r a b)
        else (R'.map (φ3 xs κ)).mergeSort (fun a b => !lt3P r b a)) =
        (R'.mergeSort (fun a b => !S.lt b a)).map (φ3 xs κ) := by
      cases large
      · exact (List.map_mergeSort (f := φ3 xs κ) (s := fun a b => !lt3P r b a) (fun a _ b _ => rfl)).symm
      · exact (List.map_mergeSort (f := φ3 xs κ) (s := fun a b => !lt3P r a b) (fun a _ b _ => rfl)).symm
    rw [hms, List.map_map, List.map_map]
    rfl

end PyLean.Accel.Heapq
