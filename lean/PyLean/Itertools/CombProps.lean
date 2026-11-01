import PyLean.Itertools.Combinatorics
import PyLean.Itertools.IsliceProps

/-!
`combinations`, `combinations_with_replacement` and `permutations`: the C index
machines run in lockstep with the doc generators (C spends one extra unit of
fuel on its first `next()`), layered by the range of `r`.
-/

namespace PyLean.Itertools

open PyLean

/-- Same items, and both or neither end with an exception (messages differ
between C and the doc code, which raises bare or Python-level errors). -/
def runAgree {α : Type} (a b : Run α) : Prop := a.1 = b.1 ∧ a.2.isSome = b.2.isSome

instance {α : Type} [DecidableEq α] (a b : Run α) : Decidable (runAgree a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## combinations -/

theorem combScan_eq (n r : Nat) (idx : List Nat) (hr : r ≤ n) :
    ∀ k, cCombScan n r idx k = docCombScan n (r : Int) idx k
  | 0 => rfl
  | k + 1 => by
    simp only [cCombScan, docCombScan]
    have : ((ix idx k : Nat) : Int) ≠ (k : Int) + n - r ↔ ¬ ix idx k = k + n - r := by omega
    by_cases h : ix idx k = k + n - r
    · simp only [h, ↓reduceIte, combScan_eq n r idx hr k]
      have : ¬ (((k + n - r : Nat) : Int) ≠ (k : Int) + n - r) := by omega
      simp [this]
    · have : ((ix idx k : Nat) : Int) ≠ (k : Int) + n - r := by omega
      simp [h, this]

theorem combFill_eq : ∀ (j k : Nat) (idx : List Nat), cCombFill j k idx = docCombFill j k idx
  | _, 0, _ => rfl
  | j, k + 1, idx => by simp only [cCombFill, docCombFill, combFill_eq (j + 1) k]

theorem combLoop_eq (pool : List Int) (r : Nat) (hr : r ≤ pool.length) :
    ∀ (fuel : Nat) (idx : List Nat),
      drain cCombinationsNext fuel
          { pool := pool, indices := idx, r := r, started := true, stopped := false } =
        docCombLoop pool (r : Int) fuel idx
  | 0, _ => rfl
  | fuel + 1, idx => by
    simp only [drain, cCombinationsNext, docCombLoop, Int.toNat_natCast, Bool.false_eq_true,
      ↓reduceIte, Bool.not_true, combScan_eq pool.length r idx hr]
    cases docCombScan pool.length (r : Int) idx r with
    | none => rfl
    | some i =>
      simp only [combFill_eq, Run.cons]
      rw [combLoop_eq pool r hr fuel]

theorem mallocLimit_eq : mallocLimit = 140737488355328 := by decide

/-- `tupleNewOk` is monotone. -/
theorem tupleNewOk_mono {a b : Int} (h : tupleNewOk b = true) (h0 : 0 ≤ a) (hab : a ≤ b) :
    tupleNewOk a = true := by
  simp only [tupleNewOk, mallocLimit_eq, ssizeMax_eq, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  omega

theorem memNewOk_of_tuple {a : Int} (h : tupleNewOk a = true) (h0 : 0 ≤ a) : memNewOk a = true := by
  simp only [tupleNewOk, memNewOk, mallocLimit_eq, ssizeMax_eq, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  omega

/-! ## combinations_with_replacement -/

theorem cwrScan_eq (n : Nat) (idx : List Nat) : ∀ k, cCwrScan n idx k = docCwrScan n idx k
  | 0 => rfl
  | k + 1 => by
    simp only [cCwrScan, docCwrScan]
    by_cases h : ((ix idx k : Nat) : Int) = (n : Int) - 1
    · simp [h, cwrScan_eq n idx k]
    · simp [h]

theorem cwrFill_eq (v : Nat) : ∀ (k i : Nat) (idx : List Nat), i + k = idx.length →
    cCwrFill v i k idx = idx.take i ++ List.replicate k v
  | 0, i, idx, h => by
    obtain rfl : i = idx.length := by omega
    simp [cCwrFill]
  | k + 1, i, idx, h => by
    simp only [cCwrFill]
    rw [cwrFill_eq v k (i + 1) _ (by simp; omega), List.set_eq_take_append_cons_drop,
      if_pos (by omega)]
    have hl : (idx.take i).length = i := by simp; omega
    rw [List.take_append, hl, List.take_of_length_le (by omega), show i + 1 - i = 1 by omega]
    simp [List.replicate_succ]

theorem cwrFill_length (v : Nat) : ∀ (k i : Nat) (idx : List Nat), (cCwrFill v i k idx).length = idx.length
  | 0, _, _ => rfl
  | k + 1, i, idx => by simp only [cCwrFill]; rw [cwrFill_length v k (i + 1)]; simp

theorem docCwrScan_lt (n : Nat) (idx : List Nat) : ∀ k i, docCwrScan n idx k = some i → i < k
  | 0, _, h => by simp [docCwrScan] at h
  | k + 1, i, h => by
    simp only [docCwrScan] at h
    split at h
    · simp at h; omega
    · have := docCwrScan_lt n idx k i h; omega

theorem cwrLoop_eq (pool : List Int) (r : Nat) :
    ∀ (fuel : Nat) (idx : List Nat), idx.length = r →
      drain cCwrNext fuel
          { pool := pool, indices := idx, r := r, started := true, stopped := false } =
        docCwrLoop pool (r : Int) fuel idx
  | 0, _, _ => rfl
  | fuel + 1, idx, hl => by
    simp only [drain, cCwrNext, docCwrLoop, Int.toNat_natCast, Bool.false_eq_true,
      ↓reduceIte, Bool.not_true, cwrScan_eq pool.length idx r]
    cases hs : docCwrScan pool.length idx r with
    | none => rfl
    | some i =>
      have hi : i < r := docCwrScan_lt _ _ _ _ hs
      have hf := cwrFill_eq (ix idx i + 1) (r - i) i idx (by omega)
      simp only [hf, Run.cons]
      rw [cwrLoop_eq pool r fuel _ (by simp; omega)]

/-! ## permutations -/

theorem ix_eq (idx : List Nat) (i : Nat) (h : i < idx.length) : ix idx i = idx[i] := by
  simp [ix, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The C shifting loop: positions `j .. n-2` take their right neighbour. -/
theorem permGo_eq : ∀ (k j : Nat) (idx : List Nat), j + k + 1 = idx.length →
    cPermRotate.go j k idx = idx.take j ++ idx.drop (j + 1) ++ idx.drop (j + k)
  | 0, j, idx, h => by
    simp only [cPermRotate.go, Nat.add_zero]
    rw [List.drop_of_length_le (l := idx) (i := j + 1) (by omega)]
    simp
  | k + 1, j, idx, h => by
    simp only [cPermRotate.go]
    rw [permGo_eq k (j + 1) _ (by simp; omega)]
    rw [ix_eq idx (j + 1) (by omega)]
    rw [List.take_set, List.drop_set, List.drop_set, if_pos (by omega), if_pos (by omega)]
    rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
    rw [List.set_append, if_neg (by simp; omega)]
    simp only [List.length_take, Option.toList_some, show min j idx.length = j by omega,
      Nat.sub_self, List.set_cons_zero, List.set_nil]
    rw [List.drop_eq_getElem_cons (l := idx) (i := j + 1) (by omega),
      show j + 1 + k = j + (k + 1) by omega]
    simp

theorem permRotate_eq (n i : Nat) (idx : List Nat) (hl : idx.length = n) (hi : i < n) :
    cPermRotate n i idx = idx.take i ++ (idx.drop (i + 1) ++ (idx.drop i).take 1) := by
  simp only [cPermRotate]
  rw [permGo_eq (n - 1 - i) i idx (by omega), show i + (n - 1 - i) = n - 1 by omega,
    List.drop_eq_getElem_cons (l := idx) (i := n - 1) (by omega),
    List.drop_of_length_le (l := idx) (i := n - 1 + 1) (by omega)]
  rw [List.set_append, if_neg (by simp; omega)]
  simp only [List.length_append, List.length_take, List.length_drop,
    show min i idx.length + (idx.length - (i + 1)) = n - 1 by omega, Nat.sub_self,
    List.set_cons_zero, ix_eq idx i (by omega)]
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_cancel_left_eq,
    List.cons.injEq, true_and]
  rw [List.drop_eq_getElem_cons (l := idx) (i := i) (by omega), List.take_succ_cons, List.take_zero]

theorem permRotate_length (n i : Nat) (idx : List Nat) (hl : idx.length = n) (hi : i < n) :
    (cPermRotate n i idx).length = n := by
  rw [permRotate_eq n i idx hl hi]; simp; omega

/-- C's loop result, read as the doc's. -/
def permRes : Option (List Nat × List Int) ⊕ (List Nat × List Int) → (List Nat × List Int) ⊕ Unit
  | .inl (some x) => .inl x
  | .inl none => .inr ()
  | .inr _ => .inr ()

theorem permLoop_eq (n : Nat) : ∀ (i : Nat) (idx : List Nat) (cyc : List Int),
    idx.length = n → i ≤ cyc.length → i ≤ n →
    permRes (cPermLoop n i idx cyc) = docPermLoop n i idx cyc
  | 0, _, _, _, _, _ => rfl
  | i + 1, idx, cyc, hl, hc, hn => by
    simp only [cPermLoop, docPermLoop]
    have hget : (cyc.set i (cyc.getD i 0 - 1)).getD i 0 = cyc.getD i 0 - 1 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_set, show i < cyc.length by omega]
    rw [hget]
    by_cases hz : cyc.getD i 0 - 1 = 0
    · simp only [hz, ↓reduceIte]
      rw [permLoop_eq n i _ _ (permRotate_length n i idx hl (by omega)) (by simp; omega) (by omega),
        permRotate_eq n i idx hl (by omega)]
    · simp only [hz, ↓reduceIte, permRes]

theorem docPermLoop_length (n : Nat) : ∀ (i : Nat) (idx : List Nat) (cyc : List Int) (x : List Nat × List Int),
    idx.length = n → i ≤ cyc.length → i ≤ n → docPermLoop n i idx cyc = .inl x →
    x.1.length = n ∧ x.2.length = cyc.length
  | 0, _, _, _, _, _, _, h => by simp [docPermLoop] at h
  | i + 1, idx, cyc, x, hl, hc, hn, h => by
    simp only [docPermLoop] at h
    split at h
    · have := docPermLoop_length n i _ _ x (by simp; omega) (by simp; omega) (by omega) h
      simpa using this
    · simp only [Sum.inl.injEq] at h
      subst h
      simp [hl]

theorem permOuter_eq (pool : List Int) (r : Nat) (hr : r ≤ pool.length) :
    ∀ (fuel : Nat) (idx : List Nat) (cyc : List Int), idx.length = pool.length → cyc.length = r →
      drain cPermutationsNext fuel
          { pool := pool, indices := idx, cycles := cyc, r := r, started := true, stopped := false } =
        docPermOuter pool (r : Int) fuel idx cyc
  | 0, _, _, _, _ => rfl
  | fuel + 1, idx, cyc, hl, hc => by
    simp only [drain, cPermutationsNext, docPermOuter, Bool.false_eq_true, ↓reduceIte, Bool.not_true,
      Int.toNat_natCast]
    by_cases hn : pool.length = 0
    · simp [hn, Run.ok]
    · simp only [hn, ↓reduceIte]
      have heq := permLoop_eq pool.length r idx cyc hl (by omega) hr
      cases hc' : cPermLoop pool.length r idx cyc with
      | inl o =>
        cases o with
        | none => rw [hc'] at heq; simp only [permRes] at heq; rw [← heq]; rfl
        | some x =>
          rw [hc'] at heq; simp only [permRes] at heq; rw [← heq]
          obtain ⟨x1, x2⟩ := x
          have hlen := docPermLoop_length pool.length r idx cyc (x1, x2) hl (by omega) hr heq.symm
          simp only [Run.cons, pySliceTo, show ((r : Nat) : Int) ≥ 0 by omega, ↓reduceIte,
            Int.toNat_natCast]
          rw [permOuter_eq pool r hr fuel x1 x2 hlen.1 (by rw [hlen.2]; exact hc)]
      | inr y => rw [hc'] at heq; simp only [permRes] at heq; rw [← heq]; rfl

/-! ## Layered properties -/

theorem asSsize_ok {r : Int} (h0 : ssizeMin ≤ r) (h1 : r ≤ ssizeMax) : asSsize r = .ok r := by
  simp [asSsize, h0, h1]

theorem memNewOk_le {r : Int} (h : memNewOk r = true) : r ≤ ssizeMax := by
  simp only [memNewOk, mallocLimit_eq, ssizeMax_eq, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  omega

theorem listRepeatCheck_ok {r : Int} (h0 : 0 ≤ r) (h : memNewOk r = true) : listRepeatCheck 1 r = .ok () := by
  have h1 := memNewOk_le h
  simp only [listRepeatCheck]
  have hmin : ¬ (r < ssizeMin ∨ r > ssizeMax) := by rw [ssizeMin_eq]; omega
  rw [if_neg hmin]
  by_cases hr : r ≤ 0
  · simp [hr]
  · have h2 : ¬ ((1 : Nat) = 0 ∨ r ≤ 0) := by omega
    rw [if_neg h2]
    have : ¬ (((1 : Nat) : Int) > ssizeMax / r) := by
      have : ssizeMax / r ≥ 1 := Int.le_ediv_of_mul_le (by omega) (by omega)
      omega
    rw [if_neg this]
    have : ((1 : Nat) : Int) * r = r := by omega
    rw [this, h]; rfl

/-- The three `r`-taking combinatoric iterators agree with their doc
equivalents (C gets one more unit of fuel for its first `next()`);
`permutations` is checked both with `r` and with `r=None`. -/
def combAgree (pool : List Int) (r : Int) (fuel : Nat) : Prop :=
  runAgree (cCombinationsF (fuel + 1) pool r) (docCombinationsF fuel pool r) ∧
  runAgree (cCwrF (fuel + 1) pool r) (docCwrF fuel pool r) ∧
  runAgree (cPermutationsF (fuel + 1) pool (some r)) (docPermutationsF fuel pool (some r)) ∧
  runAgree (cPermutationsF (fuel + 1) pool none) (docPermutationsF fuel pool none)

/-- Broad: every int `r`. The pool is a tuple in memory (`tupleNewOk`, type invariant). -/
def CombDocAgree : Prop :=
  ∀ (pool : List Int) (r : Int) (fuel : Nat), tupleNewOk pool.length = true → combAgree pool r fuel

theorem combDocAgree_refuted : ¬CombDocAgree := by
  intro h
  have := (h [1, 2, 3] (-1) 3 (by decide)).1
  revert this
  decide

/-- Narrowed to `r >= 0`. -/
def CombDocAgreeNonneg : Prop :=
  ∀ (pool : List Int) (r : Int) (fuel : Nat), tupleNewOk pool.length = true → 0 ≤ r →
    combAgree pool r fuel

theorem combDocAgreeNonneg_refuted : ¬CombDocAgreeNonneg := by
  intro h
  have := (h [1, 2, 3] (2 ^ 63) 3 (by decide) (by decide)).1
  revert this
  decide

/-- Narrowed to `0 <= r <= sys.maxsize`. -/
def CombDocAgreeSsize : Prop :=
  ∀ (pool : List Int) (r : Int) (fuel : Nat), tupleNewOk pool.length = true → 0 ≤ r → r ≤ ssizeMax →
    combAgree pool r fuel

theorem combDocAgreeSsize_refuted : ¬CombDocAgreeSsize := by
  intro h
  have := (h [1, 2, 3] (2 ^ 63 - 1) 3 (by decide) (by decide) (by decide)).1
  revert this
  decide

/-- Narrowed to `r` whose index array and result tuple can be allocated. -/
def CombDocAgreeAlloc : Prop :=
  ∀ (pool : List Int) (r : Int) (fuel : Nat), tupleNewOk pool.length = true → 0 ≤ r →
    memNewOk r = true → tupleNewOk r = true → combAgree pool r fuel

theorem runAgree_of_eq {α : Type} {a b : Run α} (h : a = b) : runAgree a b := by
  subst h; exact ⟨rfl, rfl⟩

theorem combDocAgreeAlloc_proven : CombDocAgreeAlloc := by
  intro pool r fuel hp h0 hm ht
  have hle := memNewOk_le hm
  have hmin : ssizeMin ≤ r := by rw [ssizeMin_eq]; omega
  have hpn : memNewOk (pool.length : Int) = true := memNewOk_of_tuple hp (by omega)
  have hrn : ((r.toNat : Nat) : Int) = r := Int.toNat_of_nonneg h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- combinations
    apply runAgree_of_eq
    simp only [cCombinationsF, cCombinationsNew, asSsize_ok hmin hle, docCombinationsF]
    simp only [bind, Except.bind, show ¬ r < 0 by omega, ↓reduceIte, hm, Bool.not_true,
      Bool.false_eq_true, pure, Except.pure]
    by_cases hrn' : r > pool.length
    · simp [hrn', drain, cCombinationsNext, Run.ok]
    · simp only [hrn', decide_false, drain, cCombinationsNext, Bool.false_eq_true, ↓reduceIte,
        Bool.not_false, hrn, ht, Bool.not_true]
      have := combLoop_eq pool r.toNat (by omega) fuel (List.range r.toNat)
      rw [hrn] at this
      rw [this]; rfl
  · -- combinations_with_replacement
    apply runAgree_of_eq
    simp only [cCwrF, cCwrNew, asSsize_ok hmin hle, docCwrF]
    simp only [bind, Except.bind, show ¬ r < 0 by omega, ↓reduceIte, hm, Bool.not_true,
      Bool.false_eq_true, pure, Except.pure]
    by_cases hz : pool.length = 0 ∧ r ≠ 0
    · have : (pool.length == 0 && r != 0) = true := by
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne]; omega
      simp [hz, this, drain, cCwrNext, Run.ok]
    · have : (pool.length == 0 && r != 0) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]; omega
      simp only [hz, this, ↓reduceIte, listRepeatCheck_ok h0 hm, drain, cCwrNext, Bool.false_eq_true,
        Bool.not_false, hrn, ht, Bool.not_true]
      have := cwrLoop_eq pool r.toNat fuel (List.replicate r.toNat 0) (by simp)
      rw [hrn] at this
      rw [this]; rfl
  · -- permutations(pool, r)
    apply runAgree_of_eq
    simp only [cPermutationsF, cPermutationsNew, asSsize_ok hmin hle, docPermutationsF, Option.getD]
    simp only [bind, Except.bind, show ¬ r < 0 by omega, ↓reduceIte, hm, hpn, Bool.not_true,
      Bool.or_false, Bool.false_eq_true, pure, Except.pure]
    by_cases hrn' : r > pool.length
    · simp [hrn', drain, cPermutationsNext, Run.ok]
    · simp only [hrn', decide_false, drain, cPermutationsNext, Bool.false_eq_true, ↓reduceIte,
        Bool.not_false, hrn, ht, Bool.not_true]
      have := permOuter_eq pool r.toNat (by omega) fuel (List.range pool.length)
        ((List.range r.toNat).map (fun (i : Nat) => (pool.length : Int) - (i : Int))) (by simp) (by simp)
      rw [hrn] at this
      rw [this]
      simp [pySliceTo, h0, Run.cons]
  · -- permutations(pool)
    apply runAgree_of_eq
    simp only [cPermutationsF, cPermutationsNew, docPermutationsF, Option.getD]
    simp only [bind, Except.bind, show ¬ (pool.length : Int) < 0 by omega, ↓reduceIte, hpn,
      Bool.not_true, Bool.or_false, Bool.false_eq_true, pure, Except.pure, Int.lt_irrefl, decide_false,
      drain, cPermutationsNext, Bool.not_false, Int.toNat_natCast, hp]
    have := permOuter_eq pool pool.length (by omega) fuel (List.range pool.length)
      ((List.range pool.length).map (fun (i : Nat) => (pool.length : Int) - (i : Int))) (by simp) (by simp)
    rw [this]
    simp [pySliceTo, Run.cons]

end PyLean.Itertools
