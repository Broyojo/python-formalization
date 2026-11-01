import PyLean.Itertools.Simple

/-!
The non-combinatoric C iterators drain to exactly the doc generators' output,
over any element type, for inputs that are not iterable or raise, and for
callbacks that raise.
-/

namespace PyLean.Itertools

open PyLean

variable {α β : Type}

/-! ## accumulate -/

theorem accLoop_eq (f : α → α → Py α) (err : Option PyExc) : ∀ (fuel : Nat) (xs : List α) (t : α),
    xs.length < fuel →
    drain (cAccumulateNext f) fuel { it := ⟨xs, err⟩, total := some t, initial := none } =
      docAccumulateLoop f err t xs
  | 0, _, _, h => by simp at h
  | fuel + 1, [], t, _ => by
    rw [drain_succ]
    cases err <;> simp [cAccumulateNext, Src.next, docAccumulateLoop]
  | fuel + 1, x :: xs, t, h => by
    rw [drain_succ]
    simp only [cAccumulateNext, Src.next, docAccumulateLoop]
    cases hf : f t x with
    | error e => rfl
    | ok v =>
      simp only
      rw [accLoop_eq f err fuel xs v (by simp at h; omega)]
      rfl

theorem accumulate_eq (f : α → α → Py α) (init : Option α) (o : Obj α) :
    cAccumulate f init o = docAccumulate f init o := by
  cases o with
  | notIterable ty => rfl
  | iter l err =>
    simp only [cAccumulate, cAccumulateNew, docAccumulate, getIter, Obj.len]
    cases init with
    | some t =>
      rw [drain_succ]
      simp only [cAccumulateNext]
      rw [accLoop_eq f err (l.length + 1) l t (by omega)]
      rfl
    | none =>
      cases l with
      | nil =>
        rw [drain_succ]
        cases err <;> simp [cAccumulateNext, Src.next]
      | cons x xs =>
        rw [drain_succ]
        simp only [cAccumulateNext, Src.next]
        rw [accLoop_eq f err _ xs x (by simp; omega)]
        rfl

/-! ## chain -/

theorem chainLen_cons (o : Obj α) (src : List (Obj α)) : chainLen (o :: src) = o.len + chainLen src := by
  simp [chainLen]

theorem chain_drain (serr : Option PyExc) : ∀ fuel : Nat,
    (∀ src : List (Obj α), chainLen src < fuel →
      drain cChainNext fuel { source := some ⟨src, serr⟩, active := none } = docChainLoop serr src) ∧
    (∀ (src : List (Obj α)) (l : List α) (e : Option PyExc), l.length + chainLen src < fuel →
      drain cChainNext fuel { source := some ⟨src, serr⟩, active := some ⟨l, e⟩ } =
        match e with
        | some e => (l, some e)
        | none => Run.prepend l (docChainLoop serr src))
  | 0 => ⟨fun _ h => by simp at h, fun _ _ _ h => by simp at h⟩
  | fuel + 1 => by
    obtain ⟨_, ih2⟩ := chain_drain serr fuel
    have d1 : ∀ src : List (Obj α), chainLen src < fuel + 1 →
        drain cChainNext (fuel + 1) { source := some ⟨src, serr⟩, active := none } =
          docChainLoop serr src := by
      intro src
      induction src with
      | nil =>
        intro _
        rw [drain_succ]
        cases serr <;> simp [cChainNext, cChainPull, docChainLoop]
      | cons o src ih =>
        intro h
        rw [chainLen_cons] at h
        cases o with
        | notIterable ty =>
          rw [drain_succ]
          simp [cChainNext, cChainPull, docChainLoop, getIter, Run.err]
        | iter l e =>
          simp only [Obj.len] at h
          cases l with
          | cons x xs =>
            have h2 := ih2 src xs e (by simp at h; omega)
            rw [drain_succ]
            simp only [cChainNext, cChainPull, docChainLoop, getIter, Src.next]
            rw [h2]
            cases e <;> simp [Run.prepend]
          | nil =>
            cases e with
            | some e =>
              rw [drain_succ]
              simp [cChainNext, cChainPull, docChainLoop, getIter, Src.next]
            | none =>
              have h3 := ih (by simp at h; omega)
              rw [drain_succ] at h3 ⊢
              simp only [cChainNext, cChainPull, docChainLoop, getIter, Src.next, Run.prepend] at h3 ⊢
              simpa using h3
    refine ⟨d1, ?_⟩
    intro src l e h
    cases l with
    | cons x xs =>
      have h2 := ih2 src xs e (by simp at h; omega)
      rw [drain_succ]
      simp only [cChainNext, Src.next]
      rw [h2]
      cases e <;> simp [Run.prepend]
    | nil =>
      cases e with
      | some e =>
        rw [drain_succ]
        simp [cChainNext, Src.next]
      | none =>
        have h3 := d1 src (by simp at h; omega)
        rw [drain_succ] at h3 ⊢
        simp only [cChainNext, Src.next, Run.prepend] at h3 ⊢
        simpa using h3

theorem chain_eq (args : List (Obj α)) : cChain args = docChain args := by
  simp only [cChain, cChainRun, cChainNew, chainNewInternal, docChain, ↓reduceIte, Bool.false_eq_true]
  exact (chain_drain none _).1 args (by omega)

theorem chainFrom_eq (arg : Obj (Obj α)) : cChainFrom arg = docChainFrom arg := by
  cases arg with
  | notIterable ty => rfl
  | iter ls serr =>
    simp only [cChainFrom, cChainRun, cChainFromIterable, chainNewInternal, docChainFrom, getIter]
    exact (chain_drain serr _).1 ls (by omega)

/-! ## compress -/

theorem compressDrain (truth : β → Py Bool) (derr : Option PyExc) : ∀ (fuel : Nat) (d : List α) (sel : Src β),
    d.length < fuel →
    drain (cCompressNext truth) fuel ((⟨d, derr⟩ : Src α), sel) = docCompressLoop truth derr d sel
  | 0, _, _, h => by simp at h
  | fuel + 1, [], sel, _ => by
    rw [drain_succ]
    cases derr <;> simp [cCompressNext, cCompressLoop, docCompressLoop]
  | fuel + 1, x :: d, sel, h => by
    rw [drain_succ]
    simp only [cCompressNext, cCompressLoop, docCompressLoop]
    cases hs : sel.next with
    | done => rfl
    | fail e rest => rfl
    | item y sel' =>
      simp only
      cases ht : truth y with
      | error e => rfl
      | ok b =>
        cases b with
        | true =>
          simp only
          rw [compressDrain truth derr fuel d sel' (by simp at h; omega)]
          rfl
        | false =>
          have h3 := compressDrain truth derr (fuel + 1) d sel' (by simp at h; omega)
          rw [drain_succ] at h3
          exact h3

theorem compress_eq (truth : β → Py Bool) (d : Obj α) (s : Obj β) :
    cCompress truth d s = docCompress truth d s := by
  cases d with
  | notIterable ty => rfl
  | iter l derr =>
    cases s with
    | notIterable ty => rfl
    | iter m serr =>
      simp only [cCompress, cCompressNew, docCompress, getIter, Obj.len]
      exact compressDrain truth derr _ l _ (by omega)

/-! ## dropwhile, takewhile, filterfalse -/

theorem dropTrue_eq (pred : α → Py Bool) (err : Option PyExc) : ∀ (fuel : Nat) (xs : List α),
    xs.length < fuel → drain (cDropwhileNext pred) fuel ((⟨xs, err⟩ : Src α), true) = (xs, err)
  | 0, _, h => by simp at h
  | fuel + 1, [], _ => by
    rw [drain_succ]
    cases err <;> simp [cDropwhileNext]
  | fuel + 1, x :: xs, h => by
    rw [drain_succ]
    simp only [cDropwhileNext]
    rw [dropTrue_eq pred err fuel xs (by simp at h; omega)]

theorem dropFalse_eq (pred : α → Py Bool) (err : Option PyExc) : ∀ (fuel : Nat) (xs : List α),
    xs.length < fuel →
    drain (cDropwhileNext pred) fuel ((⟨xs, err⟩ : Src α), false) = docDropwhile.go pred err xs
  | 0, _, h => by simp at h
  | fuel + 1, [], _ => by
    rw [drain_succ]
    cases err <;> simp [cDropwhileNext, docDropwhile.go]
  | fuel + 1, x :: xs, h => by
    have h3 := dropFalse_eq pred err (fuel + 1) xs (by simp at h; omega)
    rw [drain_succ] at h3 ⊢
    simp only [cDropwhileNext, docDropwhile.go]
    cases hp : pred x with
    | error e => rfl
    | ok b =>
      cases b with
      | true => exact h3
      | false =>
        simp only
        rw [dropTrue_eq pred err fuel xs (by simp at h; omega)]

theorem dropwhile_eq (pred : α → Py Bool) (o : Obj α) : cDropwhile pred o = docDropwhile pred o := by
  cases o with
  | notIterable ty => rfl
  | iter l err =>
    simp only [cDropwhile, cIterNew, docDropwhile, getIter, Obj.len]
    exact dropFalse_eq pred err _ l (by omega)

theorem takewhile_drain (pred : α → Py Bool) (err : Option PyExc) : ∀ (fuel : Nat) (xs : List α),
    xs.length < fuel →
    drain (cTakewhileNext pred) fuel ((⟨xs, err⟩ : Src α), false) = docTakewhile.go pred err xs
  | 0, _, h => by simp at h
  | fuel + 1, [], _ => by
    rw [drain_succ]
    cases err <;> simp [cTakewhileNext, Src.next, docTakewhile.go]
  | fuel + 1, x :: xs, h => by
    rw [drain_succ]
    simp only [cTakewhileNext, Src.next, docTakewhile.go]
    cases hp : pred x with
    | error e => rfl
    | ok b =>
      cases b with
      | false => rfl
      | true =>
        simp only
        rw [takewhile_drain pred err fuel xs (by simp at h; omega)]
        rfl

theorem takewhile_eq (pred : α → Py Bool) (o : Obj α) : cTakewhile pred o = docTakewhile pred o := by
  cases o with
  | notIterable ty => rfl
  | iter l err =>
    simp only [cTakewhile, cIterNew, docTakewhile, getIter, Obj.len]
    exact takewhile_drain pred err _ l (by omega)

theorem filterfalse_drain (truth : α → Py Bool) (pred : Option (α → Py Bool)) (err : Option PyExc) :
    ∀ (fuel : Nat) (xs : List α), xs.length < fuel →
    drain (cFilterfalseNext truth pred) fuel ⟨xs, err⟩ = docFilterfalse.go (ffTest truth pred) err xs
  | 0, _, h => by simp at h
  | fuel + 1, [], _ => by
    rw [drain_succ]
    cases err <;> simp [cFilterfalseNext, docFilterfalse.go]
  | fuel + 1, x :: xs, h => by
    have h3 := filterfalse_drain truth pred err (fuel + 1) xs (by simp at h; omega)
    rw [drain_succ] at h3 ⊢
    simp only [cFilterfalseNext, docFilterfalse.go]
    cases hp : ffTest truth pred x with
    | error e => rfl
    | ok b =>
      cases b with
      | true => exact h3
      | false =>
        simp only
        rw [filterfalse_drain truth pred err fuel xs (by simp at h; omega)]
        rfl

theorem ffTest_getD (truth : α → Py Bool) (pred : Option (α → Py Bool)) :
    ffTest truth pred = pred.getD truth := by
  cases pred <;> rfl

theorem filterfalse_eq (truth : α → Py Bool) (pred : Option (α → Py Bool)) (o : Obj α) :
    cFilterfalse truth pred o = docFilterfalse truth pred o := by
  cases o with
  | notIterable ty => rfl
  | iter l err =>
    simp only [cFilterfalse, cIterNew, docFilterfalse, getIter, Obj.len]
    rw [← ffTest_getD]
    exact filterfalse_drain truth pred err _ l (by omega)

/-! ## pairwise, starmap -/

theorem pairwiseDrain (err : Option PyExc) : ∀ (fuel : Nat) (xs : List α) (a : α), xs.length < fuel →
    drain cPairwiseNext fuel { it := some ⟨xs, err⟩, old := some a } = docPairwiseLoop err a xs
  | 0, _, _, h => by simp at h
  | fuel + 1, [], a, _ => by
    rw [drain_succ]
    cases err <;> simp [cPairwiseNext, cPairwiseNew2, Src.next, docPairwiseLoop]
  | fuel + 1, b :: xs, a, h => by
    rw [drain_succ]
    simp only [cPairwiseNext, cPairwiseNew2, Src.next, docPairwiseLoop]
    rw [pairwiseDrain err fuel xs b (by simp at h; omega)]
    rfl

theorem pairwise_eq (o : Obj α) : cPairwise o = docPairwise o := by
  cases o with
  | notIterable ty => rfl
  | iter l err =>
    simp only [cPairwise, cPairwiseNew, docPairwise, getIter, Obj.len]
    cases l with
    | nil =>
      rw [drain_succ]
      cases err <;> simp [cPairwiseNext, Src.next]
    | cons a xs =>
      cases xs with
      | nil =>
        rw [drain_succ]
        cases err <;> simp [cPairwiseNext, cPairwiseNew2, Src.next, docPairwiseLoop]
      | cons b xs =>
        rw [drain_succ]
        simp only [cPairwiseNext, cPairwiseNew2, Src.next, docPairwiseLoop]
        rw [pairwiseDrain err _ xs b (by simp; omega)]
        rfl

/-- Items and exception class of a run. -/
def Run.cls (r : Run α) : List α × Option String := (r.1, r.2.map PyExc.className)

theorem starmapDrain (func : List α → Py β) (err : Option PyExc) : ∀ (fuel : Nat) (xs : List (Obj α)),
    xs.length < fuel →
    (drain (cStarmapNext func) fuel ⟨xs, err⟩).cls = (docStarmapLoop func err xs).cls
  | 0, _, h => by simp at h
  | fuel + 1, [], _ => by
    rw [drain_succ]
    cases err <;> simp [cStarmapNext, Src.next, docStarmapLoop]
  | fuel + 1, x :: xs, h => by
    have ih := starmapDrain func err fuel xs (by simp at h; omega)
    rw [drain_succ]
    simp only [cStarmapNext, Src.next, docStarmapLoop]
    cases x with
    | notIterable ty => simp [tupleOf, docStarArgs, Run.err, Run.cls, PyExc.className]
    | iter l e =>
      cases e with
      | some e => simp [tupleOf, docStarArgs, Run.err]
      | none =>
        simp only [tupleOf, docStarArgs]
        cases hf : func l with
        | error e => rfl
        | ok r =>
          simp only [Run.cons, Run.cls] at ih ⊢
          simpa using ih

theorem starmap_cls (func : List α → Py β) (o : Obj (Obj α)) :
    (cStarmap func o).cls = (docStarmap func o).cls := by
  cases o with
  | notIterable ty => rfl
  | iter l err =>
    simp only [cStarmap, cIterNew, docStarmap, getIter, Obj.len]
    exact starmapDrain func err _ l (by omega)

/-! ## zip_longest -/

theorem zipRow_eq (fill : Option α) : ∀ (its : List (Option (Src α))) (na : Nat),
    cZipLongestRow fill its na = docZipLongestRow fill its na
  | [], _ => rfl
  | none :: its, na => by simp only [cZipLongestRow, docZipLongestRow, zipRow_eq fill its]
  | some ⟨[], none⟩ :: its, na => by
    simp only [cZipLongestRow, docZipLongestRow, Src.next, zipRow_eq fill its]
  | some ⟨[], some e⟩ :: its, na => by simp only [cZipLongestRow, docZipLongestRow, Src.next]
  | some ⟨x :: l, e⟩ :: its, na => by
    simp only [cZipLongestRow, docZipLongestRow, Src.next, zipRow_eq fill its]

theorem RowRes.cons_row {v : Option α} {it : Option (Src α)} {r : RowRes α} {a b c}
    (h : r.cons v it = .row a b c) : ∃ a' b', r = .row a' b' c ∧ b = it :: b' := by
  cases r with
  | row a' b' c' =>
    simp only [RowRes.cons, RowRes.row.injEq] at h
    obtain ⟨_, rfl, rfl⟩ := h
    exact ⟨_, _, rfl, rfl⟩
  | stop => simp [RowRes.cons] at h
  | raise e => simp [RowRes.cons] at h

theorem docZipRow_length (fill : Option α) : ∀ (its : List (Option (Src α))) (na : Nat) row its' na',
    0 < na → docZipLongestRow fill its na = .row row its' na' → its'.length = its.length ∧ 0 < na'
  | [], na, row, its', na', h0, h => by
    simp [docZipLongestRow] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact ⟨rfl, h0⟩
  | none :: its, na, row, its', na', h0, h => by
    simp only [docZipLongestRow] at h
    obtain ⟨a, b, h1, rfl⟩ := RowRes.cons_row h
    have := docZipRow_length fill its na a b na' h0 h1
    simp [this.1, this.2]
  | some ⟨[], none⟩ :: its, na, row, its', na', h0, h => by
    simp only [docZipLongestRow] at h
    split at h
    · simp at h
    · obtain ⟨a, b, h1, rfl⟩ := RowRes.cons_row h
      have := docZipRow_length fill its (na - 1) a b na' (by omega) h1
      simp [this.1, this.2]
  | some ⟨[], some e⟩ :: its, na, row, its', na', h0, h => by simp [docZipLongestRow] at h
  | some ⟨x :: l, e⟩ :: its, na, row, its', na', h0, h => by
    simp only [docZipLongestRow] at h
    obtain ⟨a, b, h1, rfl⟩ := RowRes.cons_row h
    have := docZipRow_length fill its na a b na' h0 h1
    simp [this.1, this.2]

theorem zipLoop_eq (fill : Option α) : ∀ (fuel : Nat) (its : List (Option (Src α))) (na : Nat),
    0 < its.length → 0 < na →
    drain cZipLongestNext fuel { its := its, numactive := na, fill := fill } = docZipLongestLoop fill fuel its na
  | 0, _, _, _, _ => rfl
  | fuel + 1, its, na, hl, hn => by
    rw [drain_succ]
    simp only [cZipLongestNext, docZipLongestLoop, show its.length ≠ 0 by omega, show na ≠ 0 by omega,
      ↓reduceIte, zipRow_eq]
    cases hr : docZipLongestRow fill its na with
    | stop => rfl
    | raise e => rfl
    | row row its' na' =>
      have := docZipRow_length fill its na row its' na' hn hr
      simp only [Run.cons]
      rw [zipLoop_eq fill fuel its' na' (by omega) this.2]

theorem zipLongest_eq (args : List (Obj α)) (kw : List (String × Option α)) (fill : Option α)
    (hkw : zipFill kw = .ok fill) : cZipLongest args kw = docZipLongest args fill := by
  simp only [cZipLongest, cZipLongestNew, docZipLongest, hkw]
  cases hm : args.mapM getIter with
  | error e => rfl
  | ok its =>
    have hl := mapM_length getIter args its hm
    simp only
    by_cases h : args.length = 0
    · have : args = [] := List.eq_nil_of_length_eq_zero h
      subst this
      have : its = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      subst this
      rfl
    · simp only [h, ↓reduceIte]
      exact zipLoop_eq fill _ _ _ (by simp; omega) (by omega)

/-! ## cycle -/

/-- Cycling over the saved copy from position `j`. -/
theorem cycleSaved_eq [Inhabited α] (l : List α) (hl : l ≠ []) : ∀ (k j : Nat), j < l.length →
    takeN cCycleNext k { it := none, saved := l, index := j } = Run.ok (docCycleSaved l k (l.drop j))
  | 0, _, _ => rfl
  | k + 1, j, hj => by
    have hne : l.length ≠ 0 := by simp [hl]
    have hget : l.getD j default = l[j] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp only [takeN, cCycleNext, show ¬ ((j : Int) < 0) by omega, ↓reduceIte, cCycleSaved, hne]
    rw [List.drop_eq_getElem_cons hj]
    simp only [docCycleSaved, Int.toNat_natCast, hget]
    by_cases hj1 : j + 1 < l.length
    · have : ¬ ((j : Int) + 1 ≥ (l.length : Int)) := by omega
      simp only [this, ↓reduceIte]
      have ih := cycleSaved_eq l hl k (j + 1) hj1
      rw [show ((j : Int) + 1) = ((j + 1 : Nat) : Int) by omega, ih]
      simp [Run.ok]
    · have : ((j : Int) + 1 ≥ (l.length : Int)) := by omega
      simp only [this, ↓reduceIte]
      have ih := cycleSaved_eq l hl k 0 (by omega)
      rw [show ((0 : Int)) = ((0 : Nat) : Int) by rfl, ih]
      rw [List.drop_of_length_le (l := l) (i := j + 1) (by omega)]
      cases l with
      | nil => simp at hl
      | cons y ys =>
        cases k with
        | zero => simp [docCycleSaved, Run.ok]
        | succ k => simp [docCycleSaved, Run.ok]

theorem cycleFirst_eq [Inhabited α] (l : List α) (err : Option PyExc) :
    ∀ (k : Nat) (xs sv : List α), sv ++ xs = l →
    takeN cCycleNext k { it := some ⟨xs, err⟩, saved := sv, index := -1 } =
      if k ≤ xs.length then Run.ok (xs.take k)
      else match err with
        | some e => (xs, some e)
        | none => Run.ok (xs.take k ++ docCycleSaved l (k - min k xs.length) [])
  | 0, xs, _, _ => by simp [takeN, Run.ok]
  | k + 1, [], sv, h => by
    simp only [List.append_nil] at h
    subst h
    cases err with
    | some e => simp [takeN, cCycleNext, Src.next]
    | none =>
      by_cases hsv : sv = []
      · subst hsv; simp [takeN, cCycleNext, cCycleSaved, Src.next, Run.ok, docCycleSaved]
      · have h1 : takeN cCycleNext (k + 1) { it := some ⟨[], none⟩, saved := sv, index := -1 } =
            takeN cCycleNext (k + 1) { it := none, saved := sv, index := ((0 : Nat) : Int) } := by
          simp [takeN, cCycleNext, Src.next]
        rw [h1, cycleSaved_eq sv hsv (k + 1) 0 (by cases sv with | nil => contradiction | cons _ _ => simp)]
        cases sv with
        | nil => contradiction
        | cons y ys => simp [docCycleSaved, Run.ok]
  | k + 1, x :: xs, sv, h => by
    simp only [takeN, cCycleNext, show (-1 : Int) < 0 by omega, ↓reduceIte, Src.next]
    rw [cycleFirst_eq l err k xs (sv ++ [x]) (by simp [← h])]
    by_cases hk : k ≤ xs.length
    · simp [hk, Run.ok]
    · simp only [hk, ↓reduceIte, List.length_cons, show ¬ (k + 1 ≤ xs.length + 1) by omega]
      cases err <;> simp [Run.ok]

theorem cycle_eq [Inhabited α] (o : Obj α) (k : Nat) : cCycle o k = docCycle o k := by
  cases o with
  | notIterable ty => rfl
  | iter l err =>
    simp only [cCycle, cCycleNew, docCycle, getIter]
    rw [cycleFirst_eq l err k l [] (by simp)]
    by_cases hk : k ≤ l.length
    · simp [hk]
    · simp only [hk, ↓reduceIte]
      cases err with
      | some e => simp [List.take_of_length_le (show l.length ≤ k by omega)]
      | none => simp [List.length_take]

/-! ## The property -/

/-- Every non-combinatoric C iterator drains to exactly what its doc equivalent
produces, the same items and the same exception, for inputs of any element
type that are not iterable or raise after their items and callbacks that
raise (for `cycle`, the first `k` items, every `k`; for `starmap` the exception
class, since the call's own message names the function). -/
def SimpleDocAgree : Prop :=
  ∀ (α β : Type),
  (∀ (f : α → α → Py α) (init : Option α) (o : Obj α), cAccumulate f init o = docAccumulate f init o) ∧
  (∀ args : List (Obj α), cChain args = docChain args) ∧
  (∀ arg : Obj (Obj α), cChainFrom arg = docChainFrom arg) ∧
  (∀ (truth : β → Py Bool) (d : Obj α) (s : Obj β), cCompress truth d s = docCompress truth d s) ∧
  (∀ (_ : Inhabited α) (o : Obj α) (k : Nat), cCycle o k = docCycle o k) ∧
  (∀ (p : α → Py Bool) (o : Obj α), cDropwhile p o = docDropwhile p o) ∧
  (∀ (p : α → Py Bool) (o : Obj α), cTakewhile p o = docTakewhile p o) ∧
  (∀ (truth : α → Py Bool) (p : Option (α → Py Bool)) (o : Obj α),
    cFilterfalse truth p o = docFilterfalse truth p o) ∧
  (∀ o : Obj α, cPairwise o = docPairwise o) ∧
  (∀ (f : List α → Py β) (o : Obj (Obj α)), (cStarmap f o).cls = (docStarmap f o).cls) ∧
  (∀ (args : List (Obj α)) (kw : List (String × Option α)) (fill : Option α),
    zipFill kw = .ok fill → cZipLongest args kw = docZipLongest args fill)

theorem simpleDocAgree_proven : SimpleDocAgree := fun _ _ =>
  ⟨accumulate_eq, chain_eq, chainFrom_eq, compress_eq, fun _ => cycle_eq, dropwhile_eq, takewhile_eq,
    filterfalse_eq, pairwise_eq, starmap_cls, zipLongest_eq⟩

/-- The constructors reject a non-iterable input with
`TypeError: 'T' object is not iterable`; `chain` and `chain.from_iterable` differ:
`chain(x)` only fails at `next()`, `from_iterable(x)` at once. Keywords that the
constructors do not take raise `TypeError`. -/
def CtorErrors : Prop :=
  ∀ (α β : Type) (ty : String),
    let e : PyExc := .typeError s!"'{ty}' object is not iterable"
    (∀ (initial : Option α), cAccumulateNew (.notIterable ty) initial = .error e) ∧
    (∀ (n : Int) (strict : Bool), asSsize n = .ok n → 1 ≤ n → cBatchedNew (α := α) (.notIterable ty) n strict = .error e) ∧
    (cCycleNew (α := α) (.notIterable ty) = .error e) ∧
    (cIterNew (α := α) (.notIterable ty) = .error e) ∧
    (cPairwiseNew (α := α) (.notIterable ty) = .error e) ∧
    (∀ (s : Obj β), cCompressNew (α := α) (.notIterable ty) s = .error e) ∧
    (∀ (d : Src α) (o : Obj α), getIter o = .ok d → cCompressNew o (β := β) (.notIterable ty) = .error e) ∧
    (cChainFromIterable (α := α) (.notIterable ty) = .error e) ∧
    (∀ (args : List (Obj α)), ∃ s, cChainNew args false = .ok s) ∧
    (∀ (args : List (Obj α)), cChainNew args true = .error (.typeError "chain() takes no keyword arguments")) ∧
    (∀ (args : List (Obj α)), ∃ s, cChainNew args true true = .ok s) ∧
    (∀ (k : String) (v : Option α), k ≠ "fillvalue" → ∀ (args : List (Obj α)),
      cZipLongestNew args [(k, v)] = .error (.typeError "zip_longest() got an unexpected keyword argument"))

theorem ctorErrors_proven : CtorErrors := by
  intro α β ty
  refine ⟨fun _ => rfl, ?_, rfl, rfl, rfl, fun _ => rfl, ?_, rfl, fun _ => ⟨_, rfl⟩, fun _ => rfl, fun _ => ⟨_, rfl⟩, ?_⟩
  · intro n strict h h1
    simp [cBatchedNew, h, show ¬ n < 1 by omega, getIter]
  · intro d o h
    simp only [cCompressNew, h]
    rfl
  · intro k v hk args
    have : zipFill [(k, v)] = .error (.typeError "zip_longest() got an unexpected keyword argument") := by
      simp only [zipFill]
      split
      · simp at *
      · rename_i heq; simp at heq; exact absurd heq.1 hk
      · rfl
    simp [cZipLongestNew, this]

end PyLean.Itertools
