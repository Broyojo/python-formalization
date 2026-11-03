import PyLean.ListSort.FalliblePerm2

/-!
# With a comparison that never raises, the fallible sort is the sort

`pureLt f` is a comparison that returns `f x y` and never raises. Each function of `Fallible.lean`,
given `pureLt f`, computes what its `Model.lean` counterpart computes with `f`, and reports no
exception. So every theorem about the model (stability, the comparison count, the stack bound) is a
theorem about the success path of the fallible one.
-/

namespace PyLean.ListSort

open PyLean

variable {α : Type}

/-- A comparison that never raises. -/
def pureLt (f : α → α → Bool) : PLt α := fun x y => .ok (f x y)

theorem binLoopF_lift (testF : Nat → MS → Py Bool × MS) (test : Nat → MS → Bool × MS)
    (h : ∀ m ms, testF m ms = (.ok (test m ms).1, (test m ms).2)) :
    ∀ (fuel lo hi : Nat) (ms : MS),
      binLoopF testF fuel lo hi ms = (.ok (binLoop test fuel lo hi ms).1, (binLoop test fuel lo hi ms).2) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi ms; rfl
  | succ fuel ih =>
    intro lo hi ms
    simp only [binLoopF, binLoop]
    split
    · rw [h]
      generalize test (lo + (hi - lo) / 2) ms = T
      obtain ⟨c, ms'⟩ := T
      cases c <;> simp [ih]
    · rfl

theorem gallopUpF_lift (testF : Nat → MS → Py Bool × MS) (test : Nat → MS → Bool × MS)
    (h : ∀ m ms, testF m ms = (.ok (test m ms).1, (test m ms).2)) (hint maxofs : Nat) :
    ∀ (fuel lastofs ofs : Nat) (ms : MS),
      gallopUpF testF hint maxofs fuel lastofs ofs ms =
        (.ok ((gallopUp test hint maxofs fuel lastofs ofs ms).1, (gallopUp test hint maxofs fuel lastofs ofs ms).2.1),
          (gallopUp test hint maxofs fuel lastofs ofs ms).2.2) := by
  intro fuel
  induction fuel with
  | zero => intro lastofs ofs ms; rfl
  | succ fuel ih =>
    intro lastofs ofs ms
    simp only [gallopUpF, gallopUp]
    split
    · rw [h]
      generalize test (hint + ofs) ms = T
      obtain ⟨c, ms'⟩ := T
      cases c <;> simp [ih]
    · rfl

theorem gallopDownF_lift (testF : Nat → MS → Py Bool × MS) (test : Nat → MS → Bool × MS)
    (h : ∀ m ms, testF m ms = (.ok (test m ms).1, (test m ms).2)) (hint maxofs : Nat) :
    ∀ (fuel lastofs ofs : Nat) (ms : MS),
      gallopDownF testF hint maxofs fuel lastofs ofs ms =
        (.ok ((gallopDown test hint maxofs fuel lastofs ofs ms).1, (gallopDown test hint maxofs fuel lastofs ofs ms).2.1),
          (gallopDown test hint maxofs fuel lastofs ofs ms).2.2) := by
  intro fuel
  induction fuel with
  | zero => intro lastofs ofs ms; rfl
  | succ fuel ih =>
    intro lastofs ofs ms
    simp only [gallopDownF, gallopDown]
    split
    · rw [h]
      generalize test (hint - ofs) ms = T
      obtain ⟨c, ms'⟩ := T
      cases c <;> simp [ih]
    · rfl

theorem gallopCoreF_lift (testF : Nat → MS → Py Bool × MS) (test : Nat → MS → Bool × MS)
    (h : ∀ m ms, testF m ms = (.ok (test m ms).1, (test m ms).2)) (n hint : Nat) (ms : MS) :
    gallopCoreF testF n hint ms = (.ok (gallopCore test n hint ms).1, (gallopCore test n hint ms).2) := by
  simp only [gallopCoreF, gallopCore]
  rw [h]
  generalize test hint ms = T
  obtain ⟨c, ms'⟩ := T
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [gallopDownF_lift testF test h]
    generalize gallopDown test hint (hint + 1) (n + 1) 0 1 ms' = G
    obtain ⟨lastofs, ofs, ms2⟩ := G
    simp only
    exact binLoopF_lift testF test h _ _ _ _
  · simp only [↓reduceIte]
    rw [gallopUpF_lift testF test h]
    generalize gallopUp test hint (n - hint) (n + 1) 0 1 ms' = G
    obtain ⟨lastofs, ofs, ms2⟩ := G
    simp only
    exact binLoopF_lift testF test h _ _ _ _

theorem gallopLeftF_pure (f : α → α → Bool) (key : α) (get : Nat → α) (n hint : Nat) (ms : MS) :
    gallopLeftF (pureLt f) key get n hint ms =
      (.ok (gallopLeft f key get n hint ms).1, (gallopLeft f key get n hint ms).2) :=
  gallopCoreF_lift _ (fun i ms => islt f ms (get i) key) (fun _ _ => rfl) n hint ms

theorem gallopRightF_pure (f : α → α → Bool) (key : α) (get : Nat → α) (n hint : Nat) (ms : MS) :
    gallopRightF (pureLt f) key get n hint ms =
      (.ok (gallopRight f key get n hint ms).1, (gallopRight f key get n hint ms).2) :=
  gallopCoreF_lift _ (fun i ms => let (c, ms) := islt f ms key (get i); (!c, ms)) (fun _ _ => rfl) n hint ms

/-! ## binarysort and count_run -/

theorem bsInsertF_pure (f : α → α → Bool) (sorted : List α) (p : α) (ms : MS) :
    bsInsertF (pureLt f) sorted p ms = (.ok (bsInsert f sorted p ms).1, (bsInsert f sorted p ms).2) := by
  simp only [bsInsertF, bsInsert]
  rw [binLoopF_lift (fun m ms => notF (isltF (pureLt f) ms p (sorted.getD m p))) (fun m ms => let (c, ms) := islt f ms p (sorted.getD m p); (!c, ms)) (fun _ _ => rfl)]

theorem bsLoopF_pure (f : α → α → Bool) :
    ∀ (sorted ps : List α) (ms : MS),
      bsLoopF (pureLt f) sorted ps ms = ((bsLoop f sorted ps ms).1, (bsLoop f sorted ps ms).2, none)
  | sorted, [], ms => rfl
  | sorted, p :: ps, ms => by
    simp only [bsLoopF, bsLoop, bsInsertF_pure]
    exact bsLoopF_pure f _ ps _

theorem binarysortF_pure (f : α → α → Bool) (a : List α) (n ok : Nat) (ms : MS) :
    binarysortF (pureLt f) a n ok ms =
      ((binarysort f a n ok ms).1, (binarysort f a n ok ms).2, none) := by
  simp only [binarysortF, binarysort, bsLoopF_pure]

theorem ascTakeF_pure (f : α → α → Bool) :
    ∀ (prev : α) (rest : List α) (ms : MS),
      ascTakeF (pureLt f) prev rest ms =
        ((ascTake f prev rest ms).1, (ascTake f prev rest ms).2.1, (ascTake f prev rest ms).2.2, none)
  | _, [], _ => rfl
  | prev, z :: rest, ms => by
    simp only [ascTakeF, ascTake, isltF, islt, pureLt]
    by_cases hf : f z prev = true
    · simp only [hf, ↓reduceIte]
    · have hf' : f z prev = false := by simpa using hf
      simp only [hf', Bool.false_eq_true, ↓reduceIte]
      rw [ascTakeF_pure f z rest]

theorem descLoopF_pure (f : α → α → Bool) :
    ∀ (done grp : List α) (prev : α) (rest : List α) (ms : MS),
      descLoopF (pureLt f) done grp prev rest ms =
        ((descLoop f done grp prev rest ms).1, (descLoop f done grp prev rest ms).2.1,
          (descLoop f done grp prev rest ms).2.2, none)
  | done, grp, _, [], ms => rfl
  | done, grp, prev, z :: rest, ms => by
    simp only [descLoopF, descLoop, isltF, islt, pureLt]
    by_cases hf : f z prev = true
    · simp only [hf, ↓reduceIte]
      exact descLoopF_pure f _ _ _ rest _
    · have hf' : f z prev = false := by simpa using hf
      simp only [hf', Bool.false_eq_true, ↓reduceIte]
      by_cases hg : f prev z = true
      · simp only [hg, ↓reduceIte]
      · have hg' : f prev z = false := by simpa using hg
        simp only [hg', Bool.false_eq_true, ↓reduceIte]
        exact descLoopF_pure f _ _ _ rest _

theorem countRunF_pure (f : α → α → Bool) (xs : List α) (ms : MS) :
    countRunF (pureLt f) xs ms =
      ((countRun f xs ms).1, (countRun f xs ms).2.1, (countRun f xs ms).2.2, none) := by
  match xs with
  | [] => rfl
  | x0 :: rest =>
    simp only [countRunF, countRun, ascTakeF_pure]
    generalize ascTake f x0 rest ms = A
    obtain ⟨t, r, ms1⟩ := A
    simp only
    match r with
    | [] => rfl
    | y :: r' =>
      simp only
      by_cases hl : (x0 :: t).length > 1
      · simp only [hl, ↓reduceIte, isltF, islt, pureLt]
        cases f x0 ((x0 :: t).getLast (by simp))
        · simp only [Bool.false_eq_true, ↓reduceIte, descLoopF_pure]
          generalize descLoop f (x0 :: t).reverse [y] y r' _ = D
          obtain ⟨pre, r2, ms3⟩ := D
          simp only
          match hrun : pre.reverse with
          | [] => rfl
          | w :: ws => simp only [ascTakeF_pure]
        · rfl
      · simp only [hl, ↓reduceIte, Bool.false_eq_true, descLoopF_pure]
        generalize descLoop f (x0 :: t).reverse [y] y r' _ = D
        obtain ⟨pre, r2, ms3⟩ := D
        simp only
        match hrun : pre.reverse with
        | [] => rfl
        | w :: ws => simp only [ascTakeF_pure]

end PyLean.ListSort
