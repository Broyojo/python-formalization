import PyLean.Itertools.Simple

/-!
The non-combinatoric C iterators drain to exactly the doc generators' output.
-/

namespace PyLean.Itertools

open PyLean

/-! ## accumulate -/

theorem accLoop_eq (f : Int → Int → Int) : ∀ (fuel : Nat) (xs : List Int) (t : Int), xs.length < fuel →
    drain (cAccumulateNext f) fuel { it := xs, total := some t, initial := none } =
      Run.ok (docAccumulateLoop f t xs)
  | 0, _, _, h => by simp at h
  | fuel + 1, [], t, _ => by simp [drain, cAccumulateNext, pop, docAccumulateLoop, Run.ok]
  | fuel + 1, x :: xs, t, h => by
    simp only [drain, cAccumulateNext, pop, docAccumulateLoop]
    rw [accLoop_eq f fuel xs (f t x) (by simp at h; omega)]
    rfl

theorem accumulate_eq (f : Int → Int → Int) (init : Option Int) (l : List Int) :
    cAccumulate f init l = docAccumulate f init l := by
  simp only [cAccumulate, docAccumulate]
  cases init with
  | some t =>
    rw [drain_succ]
    simp only [cAccumulateNext]
    rw [accLoop_eq f (l.length + 1) l t (by omega)]
    rfl
  | none =>
    cases l with
    | nil => simp [drain, cAccumulateNext, pop, Run.ok]
    | cons x xs =>
      rw [drain_succ]
      simp only [cAccumulateNext, pop]
      rw [accLoop_eq f _ xs x (by simp; omega)]
      rfl

/-! ## chain -/

def chainTotal (src : List (List Int)) (act : Option (List Int)) : Nat :=
  (act.getD []).length + (src.map List.length).sum

/-- One `next()` of `chain`: what remains to be produced. -/
theorem chainLoop_step : ∀ (src : List (List Int)) (act : Option (List Int)),
    (cChainLoop src act = .stop { source := none, active := none } ∧ (act.getD [] ++ src.flatten) = []) ∨
    (∃ x src' act', cChainLoop src act = .yield x { source := some src', active := act' } ∧
      act.getD [] ++ src.flatten = x :: (act'.getD [] ++ src'.flatten) ∧
      chainTotal src' act' + 1 = chainTotal src act)
  | src, some (x :: xs) => Or.inr ⟨x, src, some xs, by simp [cChainLoop], by simp, by simp [chainTotal]; omega⟩
  | [], some [] => Or.inl ⟨by simp [cChainLoop], by simp⟩
  | [], none => Or.inl ⟨by simp [cChainLoop], by simp⟩
  | it :: src, some [] => by
    rcases chainLoop_step src (some it) with ⟨h1, h2⟩ | ⟨x, src', act', h1, h2, h3⟩
    · exact Or.inl ⟨by simp [cChainLoop, h1], by simpa using h2⟩
    · exact Or.inr ⟨x, src', act', by simp [cChainLoop, h1], by simpa using h2,
        by simp [chainTotal] at h3 ⊢; omega⟩
  | it :: src, none => by
    rcases chainLoop_step src (some it) with ⟨h1, h2⟩ | ⟨x, src', act', h1, h2, h3⟩
    · exact Or.inl ⟨by simp [cChainLoop, h1], by simpa using h2⟩
    · exact Or.inr ⟨x, src', act', by simp [cChainLoop, h1], by simpa using h2,
        by simp [chainTotal] at h3 ⊢; omega⟩

theorem chainDrain_eq : ∀ (fuel : Nat) (src : List (List Int)) (act : Option (List Int)),
    chainTotal src act < fuel →
    drain cChainNext fuel { source := some src, active := act } = Run.ok (act.getD [] ++ src.flatten)
  | 0, _, _, h => by simp at h
  | fuel + 1, src, act, h => by
    rcases chainLoop_step src act with ⟨h1, h2⟩ | ⟨x, src', act', h1, h2, h3⟩
    · simp [drain, cChainNext, h1, h2, Run.ok]
    · simp only [drain, cChainNext, h1, h2]
      rw [chainDrain_eq fuel src' act' (by omega)]
      rfl

theorem chain_eq (ls : List (List Int)) : cChain ls = docChain ls := by
  simp only [cChain, docChain]
  rw [chainDrain_eq _ ls none (by simp [chainTotal])]
  simp

/-! ## compress -/

theorem compressGo_step : ∀ (d s : List Int),
    (∃ s', cCompressNext.go d s = .stop s' ∧ ((d.zip s).filter (fun p => truthy p.2)).map Prod.fst = []) ∨
    (∃ x d' s', cCompressNext.go d s = .yield x (d', s') ∧
      ((d.zip s).filter (fun p => truthy p.2)).map Prod.fst =
        x :: ((d'.zip s').filter (fun p => truthy p.2)).map Prod.fst ∧ d'.length < d.length)
  | [], s => Or.inl ⟨([], s), by simp [cCompressNext.go], by simp⟩
  | _ :: d, [] => Or.inl ⟨(d, []), by simp [cCompressNext.go], by simp⟩
  | x :: d, y :: s => by
    by_cases hy : truthy y = true
    · exact Or.inr ⟨x, d, s, by simp [cCompressNext.go, hy], by simp [hy], by simp⟩
    · rcases compressGo_step d s with ⟨s', h1, h2⟩ | ⟨z, d', s', h1, h2, h3⟩
      · exact Or.inl ⟨s', by simp [cCompressNext.go, hy, h1], by simp [hy, h2]⟩
      · exact Or.inr ⟨z, d', s', by simp [cCompressNext.go, hy, h1], by simp [hy, h2], by simp; omega⟩

theorem compressDrain_eq : ∀ (fuel : Nat) (d s : List Int), d.length < fuel →
    drain cCompressNext fuel (d, s) = Run.ok (((d.zip s).filter (fun p => truthy p.2)).map Prod.fst)
  | 0, _, _, h => by simp at h
  | fuel + 1, d, s, h => by
    rcases compressGo_step d s with ⟨s', h1, h2⟩ | ⟨x, d', s', h1, h2, h3⟩
    · simp [drain, cCompressNext, h1, h2, Run.ok]
    · simp only [drain, cCompressNext, h1, h2]
      rw [compressDrain_eq fuel d' s' (by omega)]
      rfl

theorem compress_eq (d s : List Int) : cCompress d s = docCompress d s := by
  simp only [cCompress, docCompress]
  rw [compressDrain_eq _ d s (by omega)]

/-! ## dropwhile, takewhile, filterfalse -/

theorem dropTrue_eq (pred : Int → Bool) : ∀ (fuel : Nat) (xs : List Int), xs.length < fuel →
    drain (cDropwhileNext pred) fuel (xs, true) = Run.ok xs
  | 0, _, h => by simp at h
  | fuel + 1, [], _ => by simp [drain, cDropwhileNext, Run.ok]
  | fuel + 1, x :: xs, h => by
    simp only [drain, cDropwhileNext]
    rw [dropTrue_eq pred fuel xs (by simp at h; omega)]
    rfl

theorem dropFalse_eq (pred : Int → Bool) : ∀ (fuel : Nat) (xs : List Int), xs.length < fuel →
    drain (cDropwhileNext pred) fuel (xs, false) = Run.ok (docDropwhile.go pred xs)
  | 0, _, h => by simp at h
  | fuel + 1, [], _ => by simp [drain, cDropwhileNext, docDropwhile.go, Run.ok]
  | fuel + 1, x :: xs, h => by
    by_cases hp : pred x = true
    · have := dropFalse_eq pred (fuel + 1) xs (by simp at h; omega)
      simp only [drain, cDropwhileNext, hp, ↓reduceIte, docDropwhile.go, Bool.not_true,
        Bool.false_eq_true] at this ⊢
      exact this
    · simp only [drain, cDropwhileNext, hp, ↓reduceIte, docDropwhile.go, Bool.false_eq_true,
        Bool.not_false]
      rw [dropTrue_eq pred fuel xs (by simp at h; omega)]
      rfl

theorem dropwhile_eq (pred : Int → Bool) (l : List Int) : cDropwhile pred l = docDropwhile pred l := by
  simp only [cDropwhile, docDropwhile]
  exact dropFalse_eq pred _ l (by omega)

theorem takewhile_drain : ∀ (pred : Int → Bool) (fuel : Nat) (xs : List Int), xs.length < fuel →
    drain (cTakewhileNext pred) fuel (xs, false) = Run.ok (docTakewhile.go pred xs)
  | _, 0, _, h => by simp at h
  | _, fuel + 1, [], _ => by simp [drain, cTakewhileNext, docTakewhile.go, Run.ok]
  | pred, fuel + 1, x :: xs, h => by
    by_cases hp : pred x = true
    · simp only [drain, cTakewhileNext, hp, ↓reduceIte, docTakewhile.go, Bool.not_true,
        Bool.false_eq_true]
      rw [takewhile_drain pred fuel xs (by simp at h; omega)]
      rfl
    · simp [drain, cTakewhileNext, hp, docTakewhile.go, Run.ok]

theorem takewhile_eq (pred : Int → Bool) (l : List Int) : cTakewhile pred l = docTakewhile pred l := by
  simp only [cTakewhile, docTakewhile]
  exact takewhile_drain pred _ l (by omega)

theorem filterfalse_drain (pred : Option (Int → Bool)) : ∀ (fuel : Nat) (xs : List Int), xs.length < fuel →
    drain (cFilterfalseNext pred) fuel xs = Run.ok (xs.filter (fun x => !ffTest pred x))
  | 0, _, h => by simp at h
  | fuel + 1, [], _ => by simp [drain, cFilterfalseNext, Run.ok]
  | fuel + 1, x :: xs, h => by
    by_cases hp : ffTest pred x = true
    · have := filterfalse_drain pred (fuel + 1) xs (by simp at h; omega)
      rw [drain_succ] at this ⊢
      simp only [cFilterfalseNext, hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at this ⊢
      rw [this]; simp [hp]
    · rw [drain_succ]
      simp only [cFilterfalseNext, hp, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
      rw [filterfalse_drain pred fuel xs (by simp at h; omega)]
      simp [hp, Run.ok]

theorem filterfalse_eq (pred : Option (Int → Bool)) (l : List Int) :
    cFilterfalse pred l = docFilterfalse pred l := by
  simp only [cFilterfalse, docFilterfalse]
  rw [filterfalse_drain pred _ l (by omega)]
  cases pred <;> rfl

/-! ## pairwise, starmap -/

theorem pairwiseDrain : ∀ (fuel : Nat) (xs : List Int) (a : Int), xs.length < fuel →
    drain cPairwiseNext fuel { it := some xs, old := some a } = Run.ok (docPairwiseLoop a xs)
  | 0, _, _, h => by simp at h
  | fuel + 1, [], a, _ => by simp [drain, cPairwiseNext, pop, docPairwiseLoop, Run.ok]
  | fuel + 1, b :: xs, a, h => by
    simp only [drain, cPairwiseNext, pop, docPairwiseLoop]
    rw [pairwiseDrain fuel xs b (by simp at h; omega)]
    rfl

theorem pairwise_eq (l : List Int) : cPairwise l = docPairwise l := by
  simp only [cPairwise, docPairwise]
  cases l with
  | nil => simp [drain, cPairwiseNext, pop, Run.ok]
  | cons a xs =>
    cases xs with
    | nil => simp [drain, cPairwiseNext, pop, docPairwiseLoop, Run.ok]
    | cons b xs =>
      rw [drain_succ]
      simp only [cPairwiseNext, pop, docPairwiseLoop]
      rw [pairwiseDrain _ xs b (by simp; omega)]
      rfl

theorem starmapDrain (func : List Int → Int) : ∀ (fuel : Nat) (xs : List (List Int)), xs.length < fuel →
    drain (cStarmapNext func) fuel xs = Run.ok (xs.map func)
  | 0, _, h => by simp at h
  | fuel + 1, [], _ => by simp [drain, cStarmapNext, Run.ok]
  | fuel + 1, x :: xs, h => by
    simp only [drain, cStarmapNext]
    rw [starmapDrain func fuel xs (by simp at h; omega)]
    rfl

theorem starmap_eq (func : List Int → Int) (l : List (List Int)) :
    cStarmap func l = docStarmap func l := by
  simp only [cStarmap, docStarmap]
  exact starmapDrain func _ l (by omega)

/-! ## zip_longest -/

theorem zipRow_eq (fill : Option Int) : ∀ (its : List (Option (List Int))) (na : Nat),
    cZipLongestRow fill its na = docZipLongestRow fill its na
  | [], _ => rfl
  | none :: its, na => by simp only [cZipLongestRow, docZipLongestRow, zipRow_eq fill its]
  | some [] :: its, na => by simp only [cZipLongestRow, docZipLongestRow, pop, zipRow_eq fill its]
  | some (x :: l) :: its, na => by simp only [cZipLongestRow, docZipLongestRow, pop, zipRow_eq fill its]

theorem docZipRow_length (fill : Option Int) : ∀ (its : List (Option (List Int))) (na : Nat) row its' na',
    0 < na → docZipLongestRow fill its na = some (row, its', na') → its'.length = its.length ∧ 0 < na'
  | [], na, row, its', na', h0, h => by
    simp [docZipLongestRow] at h; obtain ⟨-, rfl, rfl⟩ := h; simp; omega
  | none :: its, na, row, its', na', h0, h => by
    simp only [docZipLongestRow, bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i x hx
      obtain ⟨r1, i1, n1⟩ := x
      simp at h; obtain ⟨-, rfl, rfl⟩ := h
      have := docZipRow_length fill its na r1 i1 n1 h0 hx
      simp; omega
  | some [] :: its, na, row, its', na', h0, h => by
    simp only [docZipLongestRow, bind, Option.bind] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hna x hx
        obtain ⟨r1, i1, n1⟩ := x
        simp at h; obtain ⟨-, rfl, rfl⟩ := h
        have := docZipRow_length fill its (na - 1) r1 i1 n1 (by omega) hx
        simp; omega
  | some (y :: l) :: its, na, row, its', na', h0, h => by
    simp only [docZipLongestRow, bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i x hx
      obtain ⟨r1, i1, n1⟩ := x
      simp at h; obtain ⟨-, rfl, rfl⟩ := h
      have := docZipRow_length fill its na r1 i1 n1 h0 hx
      simp; omega

theorem zipLoop_eq (fill : Option Int) : ∀ (fuel : Nat) (its : List (Option (List Int))) (na : Nat),
    0 < its.length → 0 < na →
    drain cZipLongestNext fuel { its := its, numactive := na, fill := fill } = docZipLongestLoop fill fuel its na
  | 0, _, _, _, _ => rfl
  | fuel + 1, its, na, hl, hn => by
    rw [drain_succ]
    simp only [cZipLongestNext, docZipLongestLoop, show its.length ≠ 0 by omega, show na ≠ 0 by omega,
      ↓reduceIte, zipRow_eq]
    cases hr : docZipLongestRow fill its na with
    | none => rfl
    | some x =>
      obtain ⟨row, its', na'⟩ := x
      have := docZipRow_length fill its na row its' na' hn hr
      simp only [Run.cons]
      rw [zipLoop_eq fill fuel its' na' (by omega) this.2]

theorem zipLongest_eq (ls : List (List Int)) (fill : Option Int) :
    cZipLongest ls fill = docZipLongest ls fill := by
  simp only [cZipLongest, docZipLongest]
  by_cases h : ls.length = 0
  · have : ls = [] := List.eq_nil_of_length_eq_zero h
    subst this; rfl
  · simp only [h, ↓reduceIte]
    exact zipLoop_eq fill _ _ _ (by simp; omega) (by omega)

/-! ## cycle -/

/-- Cycling over the saved copy from position `j`. -/
theorem cycleSaved_eq (l : List Int) (hl : l ≠ []) : ∀ (k j : Nat), j < l.length →
    takeN cCycleNext k { it := none, saved := l, index := j } = Run.ok (docCycleSaved l k (l.drop j))
  | 0, _, _ => rfl
  | k + 1, j, hj => by
    have hne : l.length ≠ 0 := by simp [hl]
    simp only [takeN, cCycleNext, show ¬ ((j : Int) < 0) by omega, ↓reduceIte, hne]
    rw [List.drop_eq_getElem_cons hj]
    simp only [docCycleSaved, Int.toNat_natCast]
    by_cases hj1 : j + 1 < l.length
    · have : ¬ ((j : Int) + 1 ≥ (l.length : Int)) := by omega
      simp only [this, ↓reduceIte]
      have ih := cycleSaved_eq l hl k (j + 1) hj1
      rw [show ((j : Int) + 1) = ((j + 1 : Nat) : Int) by omega, ih]
      simp [Run.ok, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    · have : ((j : Int) + 1 ≥ (l.length : Int)) := by omega
      simp only [this, ↓reduceIte]
      have ih := cycleSaved_eq l hl k 0 (by omega)
      rw [show ((0 : Int)) = ((0 : Nat) : Int) by rfl, ih]
      rw [List.drop_of_length_le (l := l) (i := j + 1) (by omega)]
      cases l with
      | nil => simp at hl
      | cons y ys =>
        cases k with
        | zero => simp [docCycleSaved, Run.ok, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        | succ k => simp [docCycleSaved, Run.ok, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem cycleFirst_eq (l : List Int) : ∀ (k : Nat) (xs sv : List Int), sv ++ xs = l →
    takeN cCycleNext k { it := some xs, saved := sv, index := -1 } =
      Run.ok (xs.take k ++ docCycleSaved l (k - min k xs.length) [])
  | 0, _, _, _ => by simp [takeN, Run.ok, docCycleSaved]
  | k + 1, [], sv, h => by
    simp only [List.append_nil] at h
    subst h
    by_cases hsv : sv = []
    · subst hsv; simp [takeN, cCycleNext, Option.bind, pop, Run.ok, docCycleSaved]
    · have h1 : takeN cCycleNext (k + 1) { it := some [], saved := sv, index := -1 } =
          takeN cCycleNext (k + 1) { it := none, saved := sv, index := ((0 : Nat) : Int) } := by
        simp [takeN, cCycleNext, Option.bind, pop]
      rw [h1, cycleSaved_eq sv hsv (k + 1) 0 (by cases sv with | nil => contradiction | cons _ _ => simp)]
      cases sv with
      | nil => contradiction
      | cons y ys => simp [docCycleSaved, Run.ok]
  | k + 1, x :: xs, sv, h => by
    simp only [takeN, cCycleNext, show (-1 : Int) < 0 by omega, ↓reduceIte, Option.bind, pop]
    rw [cycleFirst_eq l k xs (sv ++ [x]) (by simp [← h])]
    simp [Run.ok, Run.cons]

theorem cycle_eq (l : List Int) (k : Nat) : cCycle l k = docCycle l k := by
  simp only [cCycle, docCycle]
  rw [cycleFirst_eq l k l [] (by simp)]
  simp [List.length_take]

/-! ## The property -/

/-- Every non-combinatoric C iterator drains to exactly what its doc
equivalent produces (for `cycle`, the first `k` items, every `k`). -/
def SimpleDocAgree : Prop :=
  (∀ (f : Int → Int → Int) (init : Option Int) (l : List Int),
    cAccumulate f init l = docAccumulate f init l) ∧
  (∀ ls : List (List Int), cChain ls = docChain ls) ∧
  (∀ d s : List Int, cCompress d s = docCompress d s) ∧
  (∀ (l : List Int) (k : Nat), cCycle l k = docCycle l k) ∧
  (∀ (p : Int → Bool) (l : List Int), cDropwhile p l = docDropwhile p l) ∧
  (∀ (p : Int → Bool) (l : List Int), cTakewhile p l = docTakewhile p l) ∧
  (∀ (p : Option (Int → Bool)) (l : List Int), cFilterfalse p l = docFilterfalse p l) ∧
  (∀ l : List Int, cPairwise l = docPairwise l) ∧
  (∀ (f : List Int → Int) (l : List (List Int)), cStarmap f l = docStarmap f l) ∧
  (∀ (ls : List (List Int)) (fill : Option Int), cZipLongest ls fill = docZipLongest ls fill)

theorem simpleDocAgree_proven : SimpleDocAgree :=
  ⟨accumulate_eq, chain_eq, compress_eq, cycle_eq, dropwhile_eq, takewhile_eq, filterfalse_eq,
    pairwise_eq, starmap_eq, zipLongest_eq⟩

end PyLean.Itertools
