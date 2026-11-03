import PyLean.Accel.HeapqSelectHonest

/-!
The honest `nsmallest` / `nlargest` runs as the generic selection algorithm of
`Selection.lean` on int codes. Item `i` of `xs` has code `i + 1`; `dcd` decodes (code `0` and
anything out of range is `default`). The order on codes is the order on what they decode to,
read through the rank of the decoded item in the finite universe `default :: xs` (or of its
key in `default :: κ default :: xs.map κ`), so the generic theorem `selAlgo_spec` applies
with int keys although the elements are any type with a strict weak order.
-/

namespace PyLean.Accel.Heapq

open PyLean

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ### Codes -/

def dcd (xs : List α) (c : Int) : α := (default :: xs).getD c.toNat default

def codes (xs : List α) : List Int := (List.range xs.length).map (fun i => ((i + 1 : Nat) : Int))

theorem dcd_mem (xs : List α) (c : Int) : dcd xs c ∈ (default :: xs) := by
  simp only [dcd, List.getD_eq_getElem?_getD]
  cases h : (default :: xs)[c.toNat]? with
  | none => simp
  | some x => exact List.mem_of_getElem? h

theorem dcd_succ (xs : List α) (i : Nat) (h : i < xs.length) : dcd xs ((i + 1 : Nat) : Int) = xs[i] := by
  simp [dcd, List.getD_eq_getElem?_getD, h]

theorem codes_map (xs : List α) : (codes xs).map (dcd xs) = xs := by
  apply List.ext_getElem (by simp [codes])
  intro i h1 h2
  simp only [codes, List.map_map, List.getElem_map, List.getElem_range, Function.comp]
  exact dcd_succ xs i h2

theorem codes_length (xs : List α) : (codes xs).length = xs.length := by simp [codes]

theorem codes_drop (xs : List α) (p : Nat) (hp : p < xs.length) :
    (codes xs).drop p = ((p + 1 : Nat) : Int) :: (codes xs).drop (p + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [codes_length]; exact hp)]
  simp [codes]

theorem codes_drop_nil (xs : List α) (p : Nat) (hp : xs.length ≤ p) : (codes xs).drop p = [] :=
  List.drop_eq_nil_of_le (by rw [codes_length]; exact hp)

theorem codes_pos (xs : List α) (c : Int) (h : c ∈ codes xs) : 1 ≤ c := by
  simp only [codes, List.mem_map, List.mem_range] at h
  obtain ⟨i, _, rfl⟩ := h; omega

/-! ### The key-less decoration -/

def φ2 (xs : List α) (t : Int × Int) : α × Int := (dcd xs t.1, t.2)

theorem φ2_default (xs : List α) : φ2 xs default = default := rfl

def rkX (r : α → α → Bool) (xs : List α) (a : α) : Int := (rank r (default :: xs) a : Int)

/-- The selection spec for `nsmallest` (`large = false`) and `nlargest` without a key. -/
def sS2 (xs : List α) (r : α → α → Bool) (large : Bool) : Accel.SelSpec (Int × Int) where
  lt := if large then Accel.maxLt (fun a b => lt2P r (φ2 xs a) (φ2 xs b))
    else fun a b => lt2P r (φ2 xs a) (φ2 xs b)
  dec e o := (e, o)
  eOf t := t.1
  topOf t := if large then -rkX r xs (dcd xs t.1) else rkX r xs (dcd xs t.1)
  kf e := if large then -rkX r xs (dcd xs e) else rkX r xs (dcd xs e)
  tagf o := if large then -o else o
  ostep o := if large then o - 1 else o + 1
  ord0 i := if large then -(i : Int) else (i : Int)

theorem rkX_spec {r : α → α → Bool} (hr : Accel.StrictWeak r) (xs : List α) (c c' : Int) :
    r (dcd xs c) (dcd xs c') = decide (rkX r xs (dcd xs c) < rkX r xs (dcd xs c')) := by
  rw [rank_spec hr _ (dcd_mem xs c) (dcd_mem xs c')]
  simp [rkX]

theorem lex_rank (r : α → α → Bool) (hr : Accel.StrictWeak r) (a b : α) (ka kb : Int)
    (h1 : r a b = decide (ka < kb)) (h2 : r b a = decide (kb < ka)) (s : Bool) :
    (r a b || (!r a b && !r b a && s)) = (decide (ka < kb) || (decide (ka = kb) && s)) := by
  rw [h1, h2]
  by_cases h : ka < kb
  · simp [h]
  · by_cases h' : kb < ka
    · have : ka ≠ kb := by omega
      simp [h, h', this]
    · have : ka = kb := by omega
      simp [h, h', this]

theorem bool_lex (x y a b : Int) :
    (decide (x < y) || (decide (x = y) && decide (a < b))) = decide (x < y ∨ (x = y ∧ a < b)) := by
  by_cases h1 : x < y <;> by_cases h2 : x = y <;> by_cases h3 : a < b <;> simp [*]

theorem bool_lex_neg (x y a b : Int) :
    (decide (y < x) || (decide (y = x) && decide (b < a))) = decide (-x < -y ∨ (-x = -y ∧ -a < -b)) := by
  by_cases h1 : y < x <;> by_cases h2 : y = x <;> by_cases h3 : b < a <;> simp [*] <;> omega

theorem sS2_good {r : α → α → Bool} (hr : Accel.StrictWeak r) (xs : List α) (large : Bool) :
    (sS2 xs r large).Good where
  sw := by
    cases large
    · exact StrictWeak.pullback (strictWeak_lt2P hr) (φ2 xs)
    · exact (StrictWeak.pullback (strictWeak_lt2P hr) (φ2 xs)).maxLt
  eOf_dec _ _ := rfl
  topOf_dec _ _ := rfl
  lt_dec e e' o o' ho := by
    have h1 := rkX_spec hr xs e e'
    have h2 := rkX_spec hr xs e' e
    cases large
    · simp only [sS2, Bool.false_eq_true, if_false, lt2P, lexLt, φ2, intLtB]
      rw [lex_rank r hr _ _ _ _ h1 h2]
      exact bool_lex _ _ _ _
    · simp only [sS2, if_true, Accel.maxLt, lt2P, lexLt, φ2, intLtB]
      rw [lex_rank r hr _ _ _ _ h2 h1]
      exact bool_lex_neg _ _ _ _
  lt_key e e' o o' h := by
    have h1 := rkX_spec hr xs e e'
    have h2 := rkX_spec hr xs e' e
    cases large
    · simp only [sS2, Bool.false_eq_true, if_false] at h ⊢
      simp only [lt2P, lexLt, φ2, h1, h2]
      have : ¬ rkX r xs (dcd xs e) < rkX r xs (dcd xs e') := by omega
      simp [this, h]
    · simp only [sS2, if_true] at h ⊢
      simp only [Accel.maxLt, lt2P, lexLt, φ2, h1, h2]
      have : ¬ rkX r xs (dcd xs e') < rkX r xs (dcd xs e) := by omega
      have h' : rkX r xs (dcd xs e) < rkX r xs (dcd xs e') := by omega
      simp [this, h']
  tag_step o := by cases large <;> simp [sS2] <;> omega
  tag_ord0 i := by cases large <;> simp [sS2]

/-- The heap comparison of the model, on decoded items, is the spec's `maxLt lt`. -/
theorem heapOrd_sS2 (xs : List α) (r : α → α → Bool) (large : Bool) (a b : Int × Int) :
    heapOrd (!large) (lt2P r) (φ2 xs a) (φ2 xs b) = Accel.maxLt (sS2 xs r large).lt a b := by
  cases large <;> rfl

theorem lt2_hEnv_fun (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (hr : Accel.StrictWeak r) :
    lt2 (hEnv xs r lr) = fun a b => pure (lt2P r a b) :=
  funext fun a => funext fun b => lt2_hEnv xs r lr hr a b

theorem reraise_ok {W β γ : Type} (g : γ) (l : List β) :
    (reraise (W := W) ((.ok g : Except PyExc γ), l)) = pure (g, l) := rfl

theorem selLoop2_sim (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (hr : Accel.StrictWeak r)
    (impl large : Bool) :
    ∀ (fuel p : Nat) (R : List (Int × Int)) (t order : Int), R ≠ [] → p ≤ xs.length →
      xs.length - p < fuel →
      ∃ R', Accel.selLoop (sS2 xs r large) R ((sS2 xs r large).topOf (t, 0)) order ((codes xs).drop p) = .ok R' ∧
        ((selLoop2 (hEnv xs r lr) impl large .it fuel (R.map (φ2 xs)) (dcd xs t) order).run p).1 =
          .ok (R'.map (φ2 xs)) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro p R t order hR hp hf
    simp only [selLoop2]
    rw [Eff.run_bind_ok (nextOpt_hEnv xs r lr p)]
    by_cases hlt : p < xs.length
    · rw [List.getElem?_eq_getElem hlt, if_pos hlt, codes_drop xs p hlt]
      simp only
      have hx : xs[p] = dcd xs ((p + 1 : Nat) : Int) := (dcd_succ xs p hlt).symm
      -- the comparison against `top`, and the spec's `S.kf e < top`
      have hcond : (if large then r (dcd xs t) xs[p] else r xs[p] (dcd xs t)) =
          decide ((sS2 xs r large).kf ((p + 1 : Nat) : Int) < (sS2 xs r large).topOf (t, 0)) := by
        rw [hx]
        cases large
        · simp only [sS2, Bool.false_eq_true, if_false]; exact rkX_spec hr xs _ _
        · simp only [sS2, if_true]; rw [rkX_spec hr xs _ _]; simp only [decide_eq_decide]; omega
      have hc : cmpTop (hEnv xs r lr) large (dcd xs t) xs[p] =
          pure (decide ((sS2 xs r large).kf ((p + 1 : Nat) : Int) < (sS2 xs r large).topOf (t, 0))) := by
        rw [← hcond]; cases large <;> rfl
      rw [hc, Eff.pure_bind]
      simp only [Accel.selLoop]
      by_cases hk : (sS2 xs r large).kf ((p + 1 : Nat) : Int) < (sS2 xs r large).topOf (t, 0)
      · rw [if_pos hk, if_pos (by simpa using hk), lt2_hEnv_fun xs r lr hr]
        have hne : R.map (φ2 xs) ≠ [] := by simpa using hR
        rw [Eff.run_bind_ok (hHeapreplace_pure impl (!large) (lt2P r) _ _ _ hne), reraise_ok,
          Eff.pure_bind]
        simp only
        -- the spec's heapreplace
        have hold : Accel.pyHeapreplace (Accel.maxLt (sS2 xs r large).lt) R
            ((sS2 xs r large).dec ((p + 1 : Nat) : Int) order) =
            .ok (Accel.at! R 0, Accel.pySiftup (Accel.maxLt (sS2 xs r large).lt)
              (R.set 0 (((p + 1 : Nat) : Int), order)) 0) := by
          cases R with
          | nil => exact absurd rfl hR
          | cons y ys => rfl
        rw [hold]
        simp only [bind, Except.bind]
        have hmap : Accel.pySiftup (heapOrd (!large) (lt2P r)) ((R.map (φ2 xs)).set 0 (xs[p], order)) 0 =
            (Accel.pySiftup (Accel.maxLt (sS2 xs r large).lt) (R.set 0 (((p + 1 : Nat) : Int), order)) 0).map
              (φ2 xs) := by
          rw [hx, show (dcd xs ((p + 1 : Nat) : Int), order) = φ2 xs (((p + 1 : Nat) : Int), order) from rfl,
            ← List.map_set]
          exact pySiftup_map (φ2 xs) (φ2_default xs) _ _ (heapOrd_sS2 xs r large) _ _
        rw [hmap, at!_map' (φ2 xs) (φ2_default xs)]
        obtain ⟨R2, hR2def⟩ : ∃ R2, R2 = Accel.pySiftup (Accel.maxLt (sS2 xs r large).lt)
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

theorem pyHeapify_length' {β : Type} [Inhabited β] (lt : β → β → Bool) (l : List β) :
    (Accel.pyHeapify lt l).length = l.length := by
  simp only [Accel.pyHeapify]; exact Accel.foldl_siftup_length lt _ l

theorem iter_src_hEnv (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (w : Nat) :
    ((hEnv xs r lr).iter .src).run w = (.ok .it, 0) := rfl

theorem iter_it_hEnv (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (w : Nat) :
    ((hEnv xs r lr).iter .it).run w = (.ok .it, w) := rfl

/-- The stable sort by rank, decoded, is the stable sort by `r`. -/
theorem decide_le_not (x y : Int) : decide (x ≤ y) = !decide (y < x) := by
  by_cases h : y < x
  · have : ¬ x ≤ y := by omega
    simp [h, this]
  · have : x ≤ y := by omega
    simp [h, this]

theorem decide_neg_le_not (x y : Int) : decide (-x ≤ -y) = !decide (x < y) := by
  by_cases h : x < y
  · have : ¬ -x ≤ -y := by omega
    simp [h, this]
  · have : -x ≤ -y := by omega
    simp [h, this]

theorem kf_sS2_le (xs : List α) {r : α → α → Bool} (hr : Accel.StrictWeak r) (large : Bool) (a b : Int) :
    decide ((sS2 xs r large).kf a ≤ (sS2 xs r large).kf b) =
      (if large then !r (dcd xs a) (dcd xs b) else !r (dcd xs b) (dcd xs a)) := by
  cases large
  · show decide (rkX r xs (dcd xs a) ≤ rkX r xs (dcd xs b)) = !r (dcd xs b) (dcd xs a)
    rw [rkX_spec hr xs b a]; exact decide_le_not _ _
  · show decide (-rkX r xs (dcd xs a) ≤ -rkX r xs (dcd xs b)) = !r (dcd xs a) (dcd xs b)
    rw [rkX_spec hr xs a b]; exact decide_neg_le_not _ _

/-- The stable sort by rank, decoded, is the stable sort by `r`. -/
theorem stableSort_dcd (xs : List α) {r : α → α → Bool} (hr : Accel.StrictWeak r) (large : Bool) :
    (Accel.stableSort (sS2 xs r large).kf (codes xs)).map (dcd xs) =
      xs.mergeSort (fun a b => if large then !r a b else !r b a) := by
  simp only [Accel.stableSort]
  rw [List.map_mergeSort (s := fun a b => if large then !r a b else !r b a)
    (fun a _ b _ => kf_sS2_le xs hr large a b), codes_map]

theorem selHeap_none (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (hr : Accel.StrictWeak r)
    (So : Sorter Nat) (hSo : SortOk So) (impl large : Bool) (fuel : Nat) (n : Int) (hn : 0 ≤ n)
    (hf : xs.length < fuel) (w0 : Nat) :
    ((selHeap (hEnv xs r lr) So impl large fuel n .src none).run w0).1 =
      .ok ((xs.mergeSort (fun a b => if large then !r a b else !r b a)).take n.toNat) := by
  let S := sS2 xs r large
  have hS := sS2_good hr xs large
  have h0 : S.tagf (if large then -n else n) = n.toNat := by
    cases large <;> simp [S, sS2] <;> omega
  have hspec := Accel.selAlgo_spec hS n.toNat (if large then -n else n) h0 (codes xs)
  rw [← stableSort_dcd xs hr large, ← List.map_take]
  rw [show (Except.ok (((Accel.stableSort S.kf (codes xs)).take n.toNat).map (dcd xs)) : Except PyExc (List α)) =
    (Accel.selAlgo S n.toNat (if large then -n else n) (codes xs)).map (List.map (dcd xs)) by rw [hspec]; rfl]
  clear hspec
  -- run both
  simp only [selHeap]
  rw [Eff.run_bind_ok (iter_src_hEnv xs r lr w0), Eff.run_bind_ok (iter_it_hEnv xs r lr 0),
    Eff.run_bind_ok (takeN_hEnv xs r lr n.toNat 0)]
  simp only [List.drop_zero, Nat.zero_add]
  have hfirst : (xs.take n.toNat).zipIdx.map (fun (p : α × Nat) => (p.1, if large then -(p.2 : Int) else (p.2 : Int))) =
      (((codes xs).take n.toNat).zipIdx.map (fun (p : Int × Nat) => S.dec p.1 (S.ord0 p.2))).map (φ2 xs) := by
    rw [← codes_map xs, ← List.map_take, List.zipIdx_map, List.map_map, List.map_map]
    rw [codes_map xs]
    apply List.map_congr_left
    intro p _
    rfl
  rw [hfirst]
  simp only [Accel.selAlgo]
  generalize ((codes xs).take n.toNat).zipIdx.map (fun (p : Int × Nat) => S.dec p.1 (S.ord0 p.2)) = R0
  by_cases hR0 : R0 = []
  · subst hR0; rfl
  · have hne : (R0.map (φ2 xs)).isEmpty = false := by
      cases R0 with
      | nil => exact absurd rfl hR0
      | cons _ _ => rfl
    rw [hne, if_neg hR0]
    simp only [Bool.false_eq_true, if_false]
    rw [lt2_hEnv_fun xs r lr hr, Eff.run_bind_ok (hHeapify_pure impl (!large) (lt2P r) _ _), reraise_ok,
      Eff.pure_bind]
    simp only
    rw [pyHeapify_map (φ2 xs) (φ2_default xs) _ _ (heapOrd_sS2 xs r large), at!_map' (φ2 xs) (φ2_default xs),
      Eff.run_bind_ok (iter_it_hEnv xs r lr _)]
    generalize hH : Accel.pyHeapify (Accel.maxLt S.lt) R0 = H
    have hHne : H ≠ [] := by
      rw [← hH]; apply List.ne_nil_of_length_pos
      rw [pyHeapify_length']; exact List.length_pos_iff.2 hR0
    rw [show (φ2 xs (Accel.at! H 0)).1 = dcd xs (Accel.at! H 0).1 from rfl]
    generalize hp : min n.toNat (xs.length - 0) = p
    obtain ⟨R', h1, h2⟩ := selLoop2_sim xs r lr hr impl large fuel p H
      (Accel.at! H 0).1 (if large then -n else n) hHne (by omega) (by omega)
    have hdrop : (codes xs).drop p = (codes xs).drop n.toNat := by
      by_cases hk : n.toNat ≤ xs.length
      · congr 1; omega
      · rw [codes_drop_nil xs _ (by omega), codes_drop_nil xs _ (by omega)]
    rw [hdrop] at h1
    rcases hrun : (selLoop2 (hEnv xs r lr) impl large .it fuel (H.map (φ2 xs)) (dcd xs (Accel.at! H 0).1)
        (if large then -n else n)).run p with ⟨res, w2⟩
    rw [hrun] at h2
    simp only at h2
    subst h2
    rw [Eff.run_bind_ok hrun]
    have htop : S.topOf (Accel.at! H 0) = S.topOf ((Accel.at! H 0).1, 0) := rfl
    rw [htop, h1]
    -- the sort
    rw [Eff.run_bind_ok (hSo _ (lt2P r) large _ w2 (strictWeak_lt2P hr))]
    show (Except.ok (List.map (fun x => x.fst) (if large then (R'.map (φ2 xs)).mergeSort (fun a b => !lt2P r a b)
        else (R'.map (φ2 xs)).mergeSort (fun a b => !lt2P r b a))) : Except PyExc (List α)) =
      Except.ok (List.map (dcd xs) (List.map S.eOf (R'.mergeSort fun a b => !S.lt b a)))
    congr 1
    have hms : (if large then (R'.map (φ2 xs)).mergeSort (fun a b => !lt2P r a b)
        else (R'.map (φ2 xs)).mergeSort (fun a b => !lt2P r b a)) =
        (R'.mergeSort (fun a b => !S.lt b a)).map (φ2 xs) := by
      cases large
      · exact (List.map_mergeSort (f := φ2 xs) (s := fun a b => !lt2P r b a) (fun a _ b _ => rfl)).symm
      · exact (List.map_mergeSort (f := φ2 xs) (s := fun a b => !lt2P r a b) (fun a _ b _ => rfl)).symm
    rw [hms, List.map_map, List.map_map]
    rfl

end PyLean.Accel.Heapq
