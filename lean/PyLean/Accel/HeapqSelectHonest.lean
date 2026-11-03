import PyLean.Accel.HeapqSelectBase

/-!
An honest environment for `nsmallest` / `nlargest`: one iterable whose `iter()` gives a fresh
iterator over `xs` (like a list), comparisons that are a pure strict weak order `r` with `==`
its equivalence, and a pure key. The world is the iterator's position. Under it, the effectful
models reduce step by step to the pure heap functions of `Heap.lean`.
-/

namespace PyLean.Accel.Heapq

open PyLean

/-- The iterable and its iterator. -/
inductive HO where
  | src
  | it
  deriving DecidableEq

instance : Inhabited HO := ⟨.src⟩

variable {α : Type} [DecidableEq α] [Inhabited α]

/-- Honest callbacks: `<` is `r`, `>` is `r` reversed, `==` is "neither is `<`", `iter(src)`
starts a fresh pass over `xs`, `next` yields `xs` then `StopIteration`, `len(src)` is
`lenRes`, `list(src)` is `xs`. -/
def hEnv (xs : List α) (r : α → α → Bool) (lenRes : Except PyExc Nat) : SEnv Nat α HO where
  lt a b := pure (r a b)
  gt a b := pure (r b a)
  eq a b := pure (!r a b && !r b a)
  iter o := match o with
    | .src => ⟨fun _ => (.ok .it, 0)⟩
    | .it => pure .it
  next o := match o with
    | .src => Eff.raise (.typeError "'list' object is not an iterator")
    | .it => ⟨fun p => match xs[p]? with
      | some x => (.ok x, p + 1)
      | none => (.error .stopIteration, p)⟩
  len o := match o with
    | .src => ⟨fun w => (lenRes, w)⟩
    | .it => Eff.raise (.typeError "object of type 'list_iterator' has no len()")
  toList o := match o with
    | .src => pure xs
    | .it => ⟨fun p => (.ok (xs.drop p), xs.length)⟩
  selfOf o := pure o
  hier := builtinHier

def pureKey (κ : α → α) : α → Eff Nat PyExc α := fun x => pure (κ x)

/-- `list.sort` is correct: for a comparison that is a pure strict weak order it returns the
stable sort (ascending, or descending with equal items in their original order for
`reverse=True`) and runs no other code. This is what `list_sort_impl` guarantees (a stable
sort), assumed here as a contract on the parameter `So`. -/
def SortOk {W : Type} (So : Sorter W) : Prop :=
  ∀ (β : Type) (rr : β → β → Bool) (rev : Bool) (l : List β) (w : W), Accel.StrictWeak rr →
    (So.sort (fun a b => (pure (rr a b) : Eff W PyExc Bool)) rev l).run w =
      (.ok (if rev then l.mergeSort (fun a b => !rr a b) else l.mergeSort (fun a b => !rr b a)), w)

/-! ### Pure comparisons -/

/-- `(a, o) < (b, o')` under the honest callbacks. -/
def lt2P (r : α → α → Bool) (x y : α × Int) : Bool := lexLt r intLtB x y

/-- `(k, o, e) < (k', o', e')` under the honest callbacks. -/
def lt3P (r : α → α → Bool) (x y : α × Int × α) : Bool := lexLt r (lexLt intLtB r) x y

theorem byOrder_eq (o o' : Int) : (if o = o' then false else decide (o < o')) = intLtB o o' := by
  by_cases h : o = o'
  · subst h; simp [intLtB]
  · simp [h, intLtB]

theorem lexInt_eq {r : α → α → Bool} (o o' : Int) (e e' : α) :
    lexLt intLtB r (o, e) (o', e') = if o = o' then r e e' else decide (o < o') := by
  simp only [lexLt, intLtB]
  by_cases h : o = o'
  · subst h; simp
  · simp only [if_neg h]
    by_cases h2 : o < o'
    · simp [h2]
    · have : o' < o := by omega
      simp [h2, this]

theorem byOrderE_eq {W : Type} (o o' : Int) :
    (if o = o' then (pure false : Eff W PyExc Bool) else pure (decide (o < o'))) = pure (intLtB o o') := by
  rw [← byOrder_eq]; split <;> rfl

theorem lt2_hEnv (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (hr : Accel.StrictWeak r)
    (x y : α × Int) : lt2 (hEnv xs r lr) x y = pure (lt2P r x y) := by
  obtain ⟨a, o⟩ := x; obtain ⟨b, o'⟩ := y
  simp only [lt2, lt2P, lexLt, byOrderE_eq]
  by_cases hab : a = b
  · subst hab
    simp [hr.irrefl]
  · simp only [if_neg hab]
    show (pure (!r a b && !r b a) >>= _ : Eff Nat PyExc Bool) = _
    rw [Eff.pure_bind]
    cases h1 : r a b <;> cases h2 : r b a <;> simp [hEnv, h1, h2]

theorem lt3_hEnv (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (hr : Accel.StrictWeak r)
    (x y : α × Int × α) : lt3 (hEnv xs r lr) x y = pure (lt3P r x y) := by
  obtain ⟨a, o, e⟩ := x; obtain ⟨b, o', e'⟩ := y
  have hel : (if e = e' then (pure false : Eff Nat PyExc Bool) else do
      let q ← (hEnv xs r lr).eq e e'
      if q then pure false else (hEnv xs r lr).lt e e') = pure (r e e') := by
    by_cases he : e = e'
    · subst he; simp [hr.irrefl]
    · simp only [if_neg he]
      show (pure (!r e e' && !r e' e) >>= _ : Eff Nat PyExc Bool) = _
      rw [Eff.pure_bind]
      cases h1 : r e e' <;> cases h2 : r e' e <;> simp [hEnv, h1, h2]
  have hbo : (if o = o' then (if e = e' then (pure false : Eff Nat PyExc Bool) else do
      let q ← (hEnv xs r lr).eq e e'
      if q then pure false else (hEnv xs r lr).lt e e') else pure (decide (o < o'))) =
      pure (lexLt intLtB r (o, e) (o', e')) := by
    rw [lexInt_eq]
    by_cases ho : o = o'
    · simp only [if_pos ho, hel]
    · simp only [if_neg ho]
  simp only [lt3, lt3P]
  rw [hbo]
  simp only [lexLt]
  by_cases hab : a = b
  · subst hab
    simp [hr.irrefl]
  · simp only [if_neg hab]
    show (pure (!r a b && !r b a) >>= _ : Eff Nat PyExc Bool) = _
    rw [Eff.pure_bind]
    cases h1 : r a b <;> cases h2 : r b a <;> simp [hEnv, h1, h2]

theorem strictWeak_lt2P {r : α → α → Bool} (hr : Accel.StrictWeak r) : Accel.StrictWeak (lt2P r) :=
  StrictWeak.lex hr strictWeak_intLtB

theorem strictWeak_lt3P {r : α → α → Bool} (hr : Accel.StrictWeak r) : Accel.StrictWeak (lt3P r) :=
  StrictWeak.lex hr (StrictWeak.lex strictWeak_intLtB hr)

/-! ### Iteration -/

theorem isA_stop : isA builtinHier .stopIteration "StopIteration" = true := by decide

theorem nextOpt_ok {W O : Type} (E : SEnv W α O) (it : O) (w w' : W) (x : α)
    (h : (E.next it).run w = (.ok x, w')) : (nextOpt E it).run w = (.ok (some x), w') := by
  simp [nextOpt, Eff.attempt, h]

theorem nextOpt_stop {W O : Type} (E : SEnv W α O) (it : O) (w w' : W) (e : PyExc)
    (h : (E.next it).run w = (.error e, w')) (hs : isA E.hier e "StopIteration" = true) :
    (nextOpt E it).run w = (.ok none, w') := by
  simp [nextOpt, Eff.attempt, h, hs]

theorem nextOpt_err {W O : Type} (E : SEnv W α O) (it : O) (w w' : W) (e : PyExc)
    (h : (E.next it).run w = (.error e, w')) (hs : isA E.hier e "StopIteration" = false) :
    (nextOpt E it).run w = (.error e, w') := by
  simp [nextOpt, Eff.attempt, h, hs]

theorem nextOpt_hEnv (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (p : Nat) :
    (nextOpt (hEnv xs r lr) .it).run p = (.ok xs[p]?, if p < xs.length then p + 1 else p) := by
  cases h : xs[p]? with
  | none =>
    have : ¬ p < xs.length := by
      intro hp; rw [List.getElem?_eq_getElem hp] at h; cases h
    rw [if_neg this]
    exact nextOpt_stop _ _ _ _ .stopIteration (by simp [hEnv, h]) isA_stop
  | some x =>
    have : p < xs.length := by
      rcases Nat.lt_or_ge p xs.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at h; cases h
    rw [if_pos this]
    exact nextOpt_ok _ _ _ _ x (by simp [hEnv, h])

theorem takeN_hEnv (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) :
    ∀ (k p : Nat), (takeN (hEnv xs r lr) .it k).run p =
      (.ok ((xs.drop p).take k), p + min k (xs.length - p)) := by
  intro k
  induction k with
  | zero => intro p; simp [takeN]
  | succ k ih =>
    intro p
    simp only [takeN, Eff.run_bind, nextOpt_hEnv]
    by_cases hp : p < xs.length
    · rw [List.getElem?_eq_getElem hp, if_pos hp]
      simp only [Eff.run_bind, ih]
      simp only [Eff.run_pure]
      refine Prod.ext ?_ ?_
      · simp only
        rw [List.drop_eq_getElem_cons hp, List.take_succ_cons]
        try simp
      · simp only; omega
    · rw [List.getElem?_eq_none (by omega), if_neg hp]
      simp only [Eff.run_pure]
      refine Prod.ext ?_ ?_
      · simp [List.drop_eq_nil_of_le (by omega : xs.length ≤ p)]
      · simp only; omega

theorem takeNKey_hEnv (xs : List α) (r : α → α → Bool) (lr : Except PyExc Nat) (κ : α → α) :
    ∀ (k p : Nat), (takeNKey (hEnv xs r lr) (pureKey κ) .it k).run p =
      (.ok (((xs.drop p).take k).map (fun x => (κ x, x))), p + min k (xs.length - p)) := by
  intro k
  induction k with
  | zero => intro p; simp [takeNKey]
  | succ k ih =>
    intro p
    simp only [takeNKey, Eff.run_bind, nextOpt_hEnv]
    by_cases hp : p < xs.length
    · rw [List.getElem?_eq_getElem hp, if_pos hp]
      simp only [pureKey, Eff.run_bind, Eff.run_pure, ih]
      refine Prod.ext ?_ ?_
      · simp only
        rw [List.drop_eq_getElem_cons hp, List.take_succ_cons]
        try simp
      · simp only; omega
    · rw [List.getElem?_eq_none (by omega), if_neg hp]
      simp only [Eff.run_pure]
      refine Prod.ext ?_ ?_
      · simp [List.drop_eq_nil_of_le (by omega : xs.length ≤ p)]
      · simp only; omega

/-! ### The heap functions with a pure comparison -/

variable {β : Type} [Inhabited β]

theorem hHeapify_pure {W : Type} (impl mx : Bool) (f : β → β → Bool) (l : List β) (w : W) :
    (hHeapify impl mx (fun a b => (pure (f a b) : Eff W PyExc Bool)) l).run w =
      (.ok (.ok (), Accel.pyHeapify (heapOrd mx f) l), w) := by
  have hc : liftCmp (W := W) (fun a b => (pure (f a b) : Eff W PyExc Bool)) = pureCmp f := rfl
  cases impl
  · simp only [hHeapify, Bool.false_eq_true, if_false, hc, onList]
    rw [pyHeapify_pure mx f ⟨w, l⟩]
  · simp only [hHeapify, if_true, hc, onListC]
    rw [cHeapify_pure mx f "list" ⟨w, l⟩]
    rfl

theorem hHeapreplace_pure {W : Type} (impl mx : Bool) (f : β → β → Bool) (l : List β) (item : β) (w : W)
    (hne : l ≠ []) :
    (hHeapreplace impl mx (fun a b => (pure (f a b) : Eff W PyExc Bool)) l item).run w =
      (.ok (.ok (Accel.at! l 0), Accel.pySiftup (heapOrd mx f) (l.set 0 item) 0), w) := by
  have hc : liftCmp (W := W) (fun a b => (pure (f a b) : Eff W PyExc Bool)) = pureCmp f := rfl
  have hold : Accel.pyHeapreplace (heapOrd mx f) l item =
      .ok (Accel.at! l 0, Accel.pySiftup (heapOrd mx f) (l.set 0 item) 0) := by
    cases l with
    | nil => exact absurd rfl hne
    | cons y ys => rfl
  have hpy := pyHeapreplace_pure mx f item (⟨w, l⟩ : HW W β)
  rw [hold] at hpy
  cases impl
  · simp only [hHeapreplace, Bool.false_eq_true, if_false, hc, onList]
    rw [hpy]
  · simp only [hHeapreplace, if_true, hc, onListC]
    have hag := replace_agree mx (fun a b s => (.ok (f a b), s)) "list" item (⟨w, l⟩ : HW W β)
    change Agree l ((cHeapreplace mx (pureCmp f) ⟨true, "list"⟩ item).run ⟨w, l⟩)
      ((pyHeapreplace listSeq (pureCmp f) mx item).run ⟨w, l⟩) at hag
    rw [hpy] at hag
    rcases hcr : (cHeapreplace mx (pureCmp f) ⟨true, "list"⟩ item).run ⟨w, l⟩ with ⟨rc, wc⟩
    rw [hcr] at hag
    cases rc with
    | ok v => obtain ⟨rfl, rfl⟩ := hag; rfl
    | error e => cases e <;> exact hag.elim

theorem hHeappop_pure {W : Type} (impl mx : Bool) (f : β → β → Bool) (l : List β) (w : W) (v : β) (l' : List β)
    (hpy : Accel.pyHeappop (heapOrd mx f) l = .ok (v, l')) :
    (hHeappop impl mx (fun a b => (pure (f a b) : Eff W PyExc Bool)) l).run w = (.ok (.ok v, l'), w) := by
  have hc : liftCmp (W := W) (fun a b => (pure (f a b) : Eff W PyExc Bool)) = pureCmp f := rfl
  have hp := pyHeappop_pure mx f (⟨w, l⟩ : HW W β)
  rw [hpy] at hp
  cases impl
  · simp only [hHeappop, Bool.false_eq_true, if_false, hc, onList]
    rw [hp]
  · simp only [hHeappop, if_true, hc, onListC]
    have hag := pop_agree mx (fun a b s => (.ok (f a b), s)) "list" (⟨w, l⟩ : HW W β)
    change Agree l ((cHeappop mx (pureCmp f) ⟨true, "list"⟩).run ⟨w, l⟩)
      ((pyHeappop listSeq (pureCmp f) mx).run ⟨w, l⟩) at hag
    rw [hp] at hag
    rcases hcr : (cHeappop mx (pureCmp f) ⟨true, "list"⟩).run ⟨w, l⟩ with ⟨rc, wc⟩
    rw [hcr] at hag
    cases rc with
    | ok v => obtain ⟨rfl, rfl⟩ := hag; rfl
    | error e => cases e <;> exact hag.elim

end PyLean.Accel.Heapq
