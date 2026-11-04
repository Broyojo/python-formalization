import PyLean.Sequences.ArrayLimits

/-!
`count`, `index`, `in` and `remove` of `array.array` with a comparison whose `__eq__` runs
Python code that may change the array (`ReCmp`, `ArrayReModel`). The four loops re-read
`Py_SIZE(self)` before every item (arraymodule.c:1354, 1401, 1426, 1451), so the items compared
after the code ran are those of the array it left.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

theorem arrGet_lt (a : Arr) (i : Nat) (h : i < a.items.length) :
    a.get i = tcGetitem a.tc a.items[i] := by
  unfold Arr.get; rw [ix_getElem _ _ h]

/-! ### `count` -/

theorem countReLoop_stop (cmp : ReCmp) (a : Arr) (i c : Int) (fuel : Nat)
    (h : (a.items.length : Int) ≤ i) : countReLoop cmp (fuel + 1) i c a = (a, .ok c) := by
  rw [countReLoop, iteF (by omega)]

/-- `m` iterations over items of `a` whose comparison leaves `a` alone. -/
theorem countReLoop_seg (cmp : ReCmp) (a : Arr) (eq : PyVal → Py Bool) :
    ∀ (m i : Nat) (c : Int) (fuel : Nat), i + m ≤ a.items.length →
      (∀ (k : Nat) x, i ≤ k → k < i + m → cmp k a x = (a, eq x)) →
      countReLoop cmp (fuel + m) i c a =
        match countRef a.tc eq ((a.items.drop i).take m) with
        | .error e => (a, .error e)
        | .ok c' => countReLoop cmp fuel ((i + m : Nat) : Int) (c + c') a := by
  intro m
  induction m with
  | zero => intro i c fuel _ _; simp [countRef]
  | succ m ih =>
    intro i c fuel hle hc
    have hlt : i < a.items.length := by omega
    rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons]
    show countReLoop cmp ((fuel + m) + 1) i c a = _
    rw [countReLoop, iteT (by omega), arrGet_lt a i hlt]
    simp only [countRef]
    cases tcGetitem a.tc a.items[i] with
    | error e => rfl
    | ok v =>
      simp only
      rw [hc i v (Nat.le_refl _) (by omega)]
      cases eq v with
      | error e => rfl
      | ok b =>
        simp only
        rw [show ((i : Int) + 1) = ((i + 1 : Nat) : Int) by omega,
          ih (i + 1) _ fuel (by omega) (fun k x h1 h2 => hc k x (by omega) (by omega))]
        cases countRef a.tc eq ((a.items.drop (i + 1)).take m) with
        | error e => rfl
        | ok r =>
          simp only [Except.map]
          have e1 : ((i + 1 + m : Nat) : Int) = ((i + (m + 1) : Nat) : Int) := by omega
          have e2 : (if b = true then c + 1 else c) + r = c + ((if b = true then 1 else 0) + r) := by
            cases b <;> simp <;> omega
          rw [e1, e2]

/-- From item `i` on, over an array whose comparisons leave it alone. -/
theorem countReLoop_tail (cmp : ReCmp) (b : Arr) (eq : PyVal → Py Bool) (i : Nat) (c : Int) (fuel : Nat)
    (hf : b.items.length - i < fuel) (hc : ∀ (k : Nat) x, i ≤ k → cmp k b x = (b, eq x)) :
    countReLoop cmp fuel i c b = (b, (countRef b.tc eq (b.items.drop i)).map (fun r => c + r)) := by
  by_cases hi : i ≤ b.items.length
  · obtain ⟨f, rfl⟩ : ∃ f, fuel = (f + 1) + (b.items.length - i) :=
      ⟨fuel - (b.items.length - i) - 1, by omega⟩
    rw [countReLoop_seg cmp b eq (b.items.length - i) i c (f + 1) (by omega)
      (fun k x h1 _ => hc k x h1), List.take_of_length_le (by simp)]
    cases countRef b.tc eq (b.items.drop i) with
    | error e => rfl
    | ok r => simp only [Except.map]; rw [countReLoop_stop _ _ _ _ _ (by omega)]
  · obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [countReLoop_stop _ _ _ _ _ (by omega), List.drop_eq_nil_of_le (by omega)]
    simp [countRef, Except.map]

/-! ### The scan of `index`, `in`, `remove` -/

theorem scanRe_stop (cmp : ReCmp) (st : Option Int) (a : Arr) (i : Int) (fuel : Nat)
    (h : (a.items.length : Int) ≤ i) : scanRe cmp st (fuel + 1) i a = (a, .ok none) := by
  rw [scanRe, iteF (by omega)]

theorem scanRe_seg (cmp : ReCmp) (st : Option Int) (a : Arr) (eq : PyVal → Py Bool) :
    ∀ (m i : Nat) (fuel : Nat), i + m ≤ a.items.length →
      (∀ k : Nat, i ≤ k → k < i + m → stopOk st k = true) →
      (∀ (k : Nat) x, i ≤ k → k < i + m → cmp k a x = (a, eq x)) →
      scanRe cmp st (fuel + m) i a =
        match searchRef a.tc eq ((a.items.drop i).take m) i with
        | .error e => (a, .error e)
        | .ok (some p) => (a, .ok (some (p : Int)))
        | .ok none => scanRe cmp st fuel ((i + m : Nat) : Int) a := by
  intro m
  induction m with
  | zero => intro i fuel _ _ _; simp [searchRef]
  | succ m ih =>
    intro i fuel hle hs hc
    have hlt : i < a.items.length := by omega
    rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons]
    show scanRe cmp st ((fuel + m) + 1) i a = _
    rw [scanRe, iteT ⟨hs i (Nat.le_refl _) (by omega), by omega⟩, arrGet_lt a i hlt]
    simp only [searchRef]
    cases tcGetitem a.tc a.items[i] with
    | error e => rfl
    | ok v =>
      simp only
      rw [hc i v (Nat.le_refl _) (by omega)]
      cases eq v with
      | error e => rfl
      | ok b =>
        cases b with
        | true => rfl
        | false =>
          simp only
          rw [show ((i : Int) + 1) = ((i + 1 : Nat) : Int) by omega,
            ih (i + 1) fuel (by omega) (fun k h1 h2 => hs k (by omega) (by omega))
              (fun k x h1 h2 => hc k x (by omega) (by omega)),
            show i + 1 + m = i + (m + 1) by omega]

theorem scanRe_tail (cmp : ReCmp) (st : Option Int) (b : Arr) (eq : PyVal → Py Bool) (i : Nat) (fuel : Nat)
    (hf : b.items.length - i < fuel) (hs : ∀ k : Nat, i ≤ k → k < b.items.length → stopOk st k = true)
    (hc : ∀ (k : Nat) x, i ≤ k → cmp k b x = (b, eq x)) :
    scanRe cmp st fuel i b =
      (b, (searchRef b.tc eq (b.items.drop i) i).map (Option.map (fun n : Nat => (n : Int)))) := by
  by_cases hi : i ≤ b.items.length
  · obtain ⟨f, rfl⟩ : ∃ f, fuel = (f + 1) + (b.items.length - i) :=
      ⟨fuel - (b.items.length - i) - 1, by omega⟩
    rw [scanRe_seg cmp st b eq (b.items.length - i) i (f + 1) (by omega)
      (fun k h1 h2 => hs k h1 (by omega)) (fun k x h1 _ => hc k x h1), List.take_of_length_le (by simp)]
    cases searchRef b.tc eq (b.items.drop i) i with
    | error e => rfl
    | ok r =>
      cases r with
      | some p => rfl
      | none => simp only [Except.map, Option.map]; rw [scanRe_stop _ _ _ _ _ (by omega)]
  · obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [scanRe_stop _ _ _ _ _ (by omega), List.drop_eq_nil_of_le (by omega)]
    simp [searchRef, Except.map]

/-! ### A comparison that leaves the array alone -/

theorem stopOk_none (k : Int) : stopOk none k = true := rfl

/-- With a comparison that changes nothing, the re-entrant scan is `arrScan`. -/
theorem scanRe_pure_arrScan (eqv : PyVal → Py Bool) (a : Arr) (stop : Int) :
    ∀ (f1 f2 : Nat) (i : Int), ((a.items.length : Int) - i).toNat < f1 →
      ((a.items.length : Int) - i).toNat < f2 →
      scanRe (ReCmp.pure eqv) (some stop) f1 i a = (a, arrScan a eqv stop f2 i) := by
  intro f1
  induction f1 with
  | zero => intro f2 i h; omega
  | succ f1 ih =>
    intro f2 i h1 h2
    obtain ⟨f2, rfl⟩ : ∃ f, f2 = f + 1 := ⟨f2 - 1, by omega⟩
    rw [scanRe, arrScan]
    simp only [stopOk, decide_eq_true_eq]
    by_cases hc : i < stop ∧ i < (a.items.length : Int)
    · rw [iteT hc, iteT hc]
      cases a.get i with
      | error e => rfl
      | ok x =>
        simp only [ReCmp.pure]
        cases eqv x with
        | error e => rfl
        | ok b =>
          cases b with
          | true => rfl
          | false => exact ih f2 (i + 1) (by omega) (by omega)
    · rw [iteF hc, iteF hc]

theorem arrCountRe_pure (eqv : PyVal → Py Bool) (a : Arr) (hl : (a.items.length : Int) ≤ ssizeMax) :
    arrCountRe (ReCmp.pure eqv) a = (a, arrCount a eqv) := by
  unfold arrCountRe arrCount
  have h := countReLoop_tail (ReCmp.pure eqv) a eqv 0 0 searchFuel
    (by unfold searchFuel; unfold ssizeMax at hl; omega) (fun _ _ _ => rfl)
  rw [show ((0:Nat):Int) = 0 from rfl] at h
  have h2 := arrCountLoop_ref a eqv a.items.length 0 0 (by omega)
  rw [show ((0:Nat):Int) = 0 from rfl] at h2
  rw [h, h2]

theorem arrContainsRe_pure (eqv : PyVal → Py Bool) (a : Arr) (hl : (a.items.length : Int) ≤ ssizeMax) :
    arrContainsRe (ReCmp.pure eqv) a = (a, arrContains a eqv) := by
  unfold arrContainsRe arrContains
  have h := scanRe_tail (ReCmp.pure eqv) none a eqv 0 searchFuel
    (by unfold searchFuel; unfold ssizeMax at hl; omega) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [show ((0:Nat):Int) = 0 from rfl] at h
  rw [h]
  have h2 := arrScan_ref a eqv a.items.length (Int.le_refl _) a.items.length 0 (by omega)
  rw [show ((0:Nat):Int) = 0 from rfl] at h2
  rw [h2]
  cases searchRef a.tc eqv (a.items.drop 0) 0 with
  | error e => rfl
  | ok r => cases r <;> rfl

theorem arrRemoveRe_pure (eqv : PyVal → Py Bool) (a : Arr) (hl : (a.items.length : Int) ≤ ssizeMax) :
    arrRemoveRe (ReCmp.pure eqv) a =
      match arrRemove a eqv with
      | .ok a' => (a', .ok ())
      | .error e => (a, .error e) := by
  unfold arrRemoveRe arrRemove
  have h := scanRe_tail (ReCmp.pure eqv) none a eqv 0 searchFuel
    (by unfold searchFuel; unfold ssizeMax at hl; omega) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [show ((0:Nat):Int) = 0 from rfl] at h
  rw [h]
  have h2 := arrScan_ref a eqv a.items.length (Int.le_refl _) a.items.length 0 (by omega)
  rw [show ((0:Nat):Int) = 0 from rfl] at h2
  rw [h2]
  cases searchRef a.tc eqv (a.items.drop 0) 0 with
  | error e => rfl
  | ok r =>
    cases r with
    | none => rfl
    | some p =>
      simp only [Except.map, Option.map]
      cases arrDelSlice a p (p + 1) <;> rfl

theorem arrIndexRe_pure (eqv : PyVal → Py Bool) (a : Arr) (start stop : Option Int)
    (hl : (a.items.length : Int) ≤ ssizeMax) :
    arrIndexRe (ReCmp.pure eqv) a start stop = (a, arrIndex a eqv start stop) := by
  unfold arrIndexRe arrIndex
  dsimp only
  generalize hs : (if sliceIndex (start.getD 0) < 0 then
      (if sliceIndex (start.getD 0) + (a.items.length : Int) < 0 then 0
       else sliceIndex (start.getD 0) + a.items.length)
    else sliceIndex (start.getD 0)) = s
  have hs0 : 0 ≤ s := by rw [← hs]; split <;> (try split) <;> omega
  rw [scanRe_pure_arrScan eqv a _ searchFuel (a.items.length + 1) s
    (by unfold searchFuel; unfold ssizeMax at hl; omega) (by omega)]
  cases arrScan a eqv _ (a.items.length + 1) s with
  | error e => rfl
  | ok r => cases r <;> rfl

/-! ### A comparison that changes the array -/

/-- The scan when the comparison of item `j` leaves the array `b` and every other leaves the
array alone: the items before `j` of `a`, item `j`, then the items after `j` of `b`. -/
def scanSplit (a b : Arr) (eq : PyVal → Py Bool) (j : Nat) (rj : PyVal → Py Bool) :
    Arr × Py (Option Int) :=
  match searchRef a.tc eq (a.items.take j) 0 with
  | .error e => (a, .error e)
  | .ok (some p) => (a, .ok (some (p : Int)))
  | .ok none =>
    match a.get j with
    | .error e => (a, .error e)
    | .ok x =>
      match rj x with
      | .error e => (b, .error e)
      | .ok true => (b, .ok (some j))
      | .ok false => (b, (searchRef b.tc eq (b.items.drop (j + 1)) (j + 1)).map
          (Option.map (fun n : Nat => (n : Int))))

/-- `count`, `index` (no bounds), `in` and `remove`, for every array `a`, every index `j` of
it and every comparison that leaves the array alone (comparing like `eq`, which may raise)
except at item `j`, where its code leaves any array `b` (the comparison `rj` may raise): the
loops read the size anew before every item, so they compare the items of `a` before `j`, then
item `j`, then the items of `b` after `j`, as many as `b` has. A comparison that clears or
shrinks the array to `j + 1` items or fewer ends the loop; one that grows it makes the loop
compare the new items; a size read once would instead compare the later items of `a`'s
length, reading past a shrunk array. `count` counts the true comparisons; `index` and `in`
stop at the first; `remove` then deletes item `j` of `b` with `array_del_slice`, which deletes
nothing when `b` has `j` items or fewer, and raises `BufferError` (array `b` kept) while `b` is
exported. An exception of a read or a comparison ends each with the array as the code left
it. Hypothesis: `len(a), len(b) <= PY_SSIZE_T_MAX` (an array's size is a `Py_ssize_t`). -/
def ArraySearchReentrant : Prop :=
  ∀ (a b : Arr) (eq rj : PyVal → Py Bool) (j : Nat) (cmp : ReCmp),
    (a.items.length : Int) ≤ ssizeMax → (b.items.length : Int) ≤ ssizeMax → j < a.items.length →
    (∀ (k : Nat) x, k < j → cmp k a x = (a, eq x)) →
    (∀ x, cmp j a x = (b, rj x)) →
    (∀ (k : Nat) x, j < k → cmp k b x = (b, eq x)) →
    arrCountRe cmp a =
      (match countRef a.tc eq (a.items.take j) with
       | .error e => (a, .error e)
       | .ok c0 =>
         match a.get j with
         | .error e => (a, .error e)
         | .ok x =>
           match rj x with
           | .error e => (b, .error e)
           | .ok t => (b, (countRef b.tc eq (b.items.drop (j + 1))).map
               (fun c1 => c0 + (if t then 1 else 0) + c1))) ∧
    arrIndexRe cmp a none none =
      (match scanSplit a b eq j rj with
       | (c, .error e) => (c, .error e)
       | (c, .ok (some i)) => (c, .ok i)
       | (c, .ok none) => (c, .error (.valueError "array.index(x): x not in array"))) ∧
    arrContainsRe cmp a = ((scanSplit a b eq j rj).1, (scanSplit a b eq j rj).2.map Option.isSome) ∧
    arrRemoveRe cmp a =
      (match scanSplit a b eq j rj with
       | (c, .error e) => (c, .error e)
       | (c, .ok (some i)) =>
         match arrDelSlice c i (i + 1) with
         | .ok c' => (c', .ok ())
         | .error e => (c, .error e)
       | (c, .ok none) => (c, .error (.valueError "array.remove(x): x not in array")))

/-- The scan of `index`/`in`/`remove` under the hypotheses of `ArraySearchReentrant`. -/
theorem scanRe_split (a b : Arr) (eq rj : PyVal → Py Bool) (j : Nat) (cmp : ReCmp) (st : Option Int)
    (hb : (b.items.length : Int) ≤ ssizeMax) (hj : j < a.items.length)
    (hs : ∀ k : Int, k < a.items.length ∨ k < b.items.length → stopOk st k = true)
    (hpre : ∀ (k : Nat) x, k < j → cmp k a x = (a, eq x)) (hat : ∀ x, cmp j a x = (b, rj x))
    (hpost : ∀ (k : Nat) x, j < k → cmp k b x = (b, eq x)) (ha : (a.items.length : Int) ≤ ssizeMax) :
    scanRe cmp st searchFuel 0 a = scanSplit a b eq j rj := by
  have hF : searchFuel = (searchFuel - j - 1 + 1) + j := by
    unfold searchFuel; unfold ssizeMax at ha; omega
  have hseg := scanRe_seg cmp st a eq j 0 (searchFuel - j - 1 + 1) (by omega)
    (fun k _ h2 => hs k (by left; omega)) (fun k x _ h => hpre k x (by omega))
  rw [show ((0:Nat):Int) = 0 from rfl] at hseg
  rw [hF, hseg]
  unfold scanSplit
  simp only [Nat.zero_add, List.drop_zero]
  cases searchRef a.tc eq (a.items.take j) 0 with
  | error e => rfl
  | ok r =>
    cases r with
    | some p => rfl
    | none =>
      simp only
      rw [scanRe, iteT ⟨hs j (by left; omega), by omega⟩]
      cases a.get j with
      | error e => rfl
      | ok x =>
        simp only
        rw [hat x]
        cases rj x with
        | error e => rfl
        | ok t =>
          cases t with
          | true => rfl
          | false =>
            simp only
            rw [show ((j : Int) + 1) = ((j + 1 : Nat) : Int) by omega]
            exact scanRe_tail cmp st b eq (j + 1) _
              (by unfold searchFuel; unfold ssizeMax at ha hb; omega)
              (fun k _ h2 => hs k (by right; omega)) (fun k x h => hpost k x (by omega))

theorem arraySearchReentrant_proven : ArraySearchReentrant := by
  intro a b eq rj j cmp ha hb hj hpre hat hpost
  have hsn : ∀ k : Int, k < a.items.length ∨ k < b.items.length → stopOk none k = true :=
    fun _ _ => rfl
  have hsm : ∀ k : Int, k < a.items.length ∨ k < b.items.length → stopOk (some ssizeMax) k = true := by
    intro k hk; simp only [stopOk, decide_eq_true_eq]; omega
  have hscanN := scanRe_split a b eq rj j cmp none hb hj hsn hpre hat hpost ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold arrCountRe
    have hF : searchFuel = (searchFuel - j - 1 + 1) + j := by
      unfold searchFuel; unfold ssizeMax at ha; omega
    have hseg := countReLoop_seg cmp a eq j 0 0 (searchFuel - j - 1 + 1) (by omega)
      (fun k x _ h => hpre k x (by omega))
    rw [show ((0:Nat):Int) = 0 from rfl] at hseg
    rw [hF, hseg]
    simp only [Nat.zero_add, List.drop_zero]
    cases countRef a.tc eq (a.items.take j) with
    | error e => rfl
    | ok c0 =>
      simp only
      rw [countReLoop, iteT (by omega)]
      cases a.get j with
      | error e => rfl
      | ok x =>
        simp only
        rw [hat x]
        cases rj x with
        | error e => rfl
        | ok t =>
          simp only
          rw [show ((j : Int) + 1) = ((j + 1 : Nat) : Int) by omega,
            countReLoop_tail cmp b eq (j + 1) _ _ (by unfold searchFuel; unfold ssizeMax at ha hb; omega)
              (fun k x h => hpost k x (by omega))]
          cases countRef b.tc eq (b.items.drop (j + 1)) with
          | error e => rfl
          | ok r =>
            have h2 : (if t = true then 0 + c0 + 1 else 0 + c0) + r = c0 + (if t = true then 1 else 0) + r := by
              cases t <;> simp <;> omega
            simp only [Except.map, h2]
  · unfold arrIndexRe
    dsimp only
    have e0 : sliceIndex ((none : Option Int).getD 0) = 0 := by
      simp only [Option.getD_none, sliceIndex, RangeSlice.clampSsize]
      rw [iteF (by decide), iteF (by decide)]
    have e1 : sliceIndex ((none : Option Int).getD ssizeMax) = ssizeMax := by
      simp only [Option.getD_none, sliceIndex, RangeSlice.clampSsize]
      rw [iteF (by decide), iteF (by decide)]
    simp only [e0, e1, show ¬ ((0 : Int) < 0) by decide, show ¬ (ssizeMax < 0) by decide, ite_false]
    rw [scanRe_split a b eq rj j cmp (some ssizeMax) hb hj hsm hpre hat hpost ha]
    rcases scanSplit a b eq j rj with ⟨c, e | _ | i⟩ <;> rfl
  · unfold arrContainsRe
    rw [hscanN]
  · unfold arrRemoveRe
    rw [hscanN]
    rcases scanSplit a b eq j rj with ⟨c, e | _ | i⟩ <;> rfl

end PyLean.Sequences
