import PyLean.CoreLibs.Functools.Compare

/-!
Properties of `total_ordering` and `cmp_to_key`.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-- The truth of a comparison under a strict order `lt`. -/
def truthOf {α : Type} [DecidableEq α] (lt : α → α → Bool) (o : OrdOp) (a b : α) : Bool :=
  match o with
  | .lt => lt a b
  | .le => lt a b || decide (a = b)
  | .gt => lt b a
  | .ge => lt b a || decide (a = b)

/-- A class of real `bool` results whose root comes from a total order. -/
def primsOf {α : Type} [DecidableEq α] (lt : α → α → Bool) (root : OrdOp) : OrdPrims α Bool :=
  ⟨fun a b => .ok (.val (truthOf lt root a b)), fun a b => .ok (decide (a = b)),
    fun a b => .ok (!decide (a = b)), fun r => .ok r, id⟩

/-- `lt` is a strict total order: the precondition of `total_ordering`, whose docs say it does not
apply to partial orders. -/
structure StrictTotal {α : Type} (lt : α → α → Bool) : Prop where
  irrefl : ∀ a, lt a a = false
  asymm : ∀ a b, lt a b = true → lt b a = false
  total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true

/-- Each of the twelve generated methods gives the right answer for a totally ordered class, from
each root. -/
def TotalOrderingCorrect : Prop :=
  ∀ (α : Type) [DecidableEq α] (lt : α → α → Bool), StrictTotal lt →
    ∀ (root o : OrdOp) (s : Shape) (a b : α), (o, s) ∈ convert root →
      derived (primsOf lt root) s a b = .ok (.val (truthOf lt o a b))

theorem totalOrderingCorrect_proven : TotalOrderingCorrect := by
  intro α _ lt hlt root o s a b hmem
  have c1 : lt a b = true → lt b a = false := hlt.asymm a b
  have c2 : decide (a = b) = true → lt a b = false ∧ lt b a = false := by
    intro h
    have : a = b := by simpa using h
    subst this
    exact ⟨hlt.irrefl a, hlt.irrefl a⟩
  have c3 : decide (a = b) = false → lt a b = true ∨ lt b a = true := by
    intro h
    exact hlt.total a b (by simpa using h)
  cases root <;> simp only [convert, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem <;>
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [derived, primsOf, truthOf, bind, Except.bind, pure, Except.pure, Functor.map,
      Except.map, id] <;>
    cases hx : lt a b <;> cases hy : lt b a <;> cases he : decide (a = b) <;> simp_all

/-- What the source's `or` and `and` return, for result objects of any type: `_le_from_lt`-shaped
methods return a truthy `op_result` itself, `_lt_from_le`-shaped ones a falsy `op_result` itself, and
otherwise the raw `==` or `!=` result, unconverted; the `not`-shaped ones return a real `bool`. An
exception from the root or from the truth test escapes, and `NotImplemented` passes through without
touching anything else. This is what a class with non-`bool` comparison results observes. -/
def DerivedKeepsResults : Prop :=
  ∀ (α ρ : Type) (P : OrdPrims α ρ) (a b : α) (op : ρ) (s : Shape),
    (P.root a b = .ok (.val op) → P.truth op = .ok true →
      derived P .orEq a b = .ok (.val op) ∧
      derived P .andNe a b = (.val <$> P.ne a b) ∧
      derived P .notAndNe a b = .ok (.val (P.ofBool false)) ∧
      derived P .notOrEq a b = (.val <$> P.eq a b) ∧
      derived P .notOp a b = .ok (.val (P.ofBool false))) ∧
    (P.root a b = .ok (.val op) → P.truth op = .ok false →
      derived P .orEq a b = (.val <$> P.eq a b) ∧
      derived P .andNe a b = .ok (.val op) ∧
      derived P .notAndNe a b = (.val <$> P.ne a b) ∧
      derived P .notOrEq a b = .ok (.val (P.ofBool true)) ∧
      derived P .notOp a b = .ok (.val (P.ofBool true))) ∧
    (∀ e, P.root a b = .error e → derived P s a b = .error e) ∧
    (∀ e, P.root a b = .ok (.val op) → P.truth op = .error e → derived P s a b = .error e) ∧
    (P.root a b = .ok .notImplemented → derived P s a b = .ok .notImplemented)

theorem derivedKeepsResults_proven : DerivedKeepsResults := by
  intro α ρ P a b op s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2
    simp [derived, h1, h2, bind, Except.bind, pure, Except.pure]
  · intro h1 h2
    simp [derived, h1, h2, bind, Except.bind, pure, Except.pure]
  · intro e h
    simp [derived, h, bind, Except.bind]
  · intro e h1 h2
    cases s <;> simp [derived, h1, h2, bind, Except.bind]
  · intro h
    simp [derived, h, bind, Except.bind, pure, Except.pure]

/-- The root found for each class: `max` of the method names prefers `__lt__`, then `__le__`, `__gt__`,
`__ge__`, the comment at Lib/functools.py:194, and this agrees with string order. -/
theorem maxRoot_is_max : ∀ (roots : List OrdOp) (r : OrdOp), maxRoot roots = some r →
    r ∈ roots ∧ ∀ o ∈ roots, ¬ (r.name < o.name) := by
  intro roots r h
  have names : ∀ a b : OrdOp, (a = .lt ∨ (a = .le ∧ b ≠ .lt) ∨ (a = .gt ∧ b ≠ .lt ∧ b ≠ .le) ∨
      (a = .ge ∧ b = .ge)) → ¬ (a.name < b.name) := by
    intro a b hab
    rcases hab with rfl | ⟨rfl, h1⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, rfl⟩
    · cases b <;> decide
    · cases b
      · exact absurd rfl h1
      all_goals decide
    · cases b
      · exact absurd rfl h1
      · exact absurd rfl h2
      all_goals decide
    · decide
  unfold maxRoot at h
  by_cases h1 : OrdOp.lt ∈ roots
  · rw [if_pos h1] at h
    cases h
    exact ⟨h1, fun o _ => names _ _ (Or.inl rfl)⟩
  rw [if_neg h1] at h
  have nl : ∀ o ∈ roots, o ≠ .lt := fun o ho e => h1 (e ▸ ho)
  by_cases h2 : OrdOp.le ∈ roots
  · rw [if_pos h2] at h
    cases h
    exact ⟨h2, fun o ho => names _ _ (Or.inr (Or.inl ⟨rfl, nl o ho⟩))⟩
  rw [if_neg h2] at h
  have nl2 : ∀ o ∈ roots, o ≠ .le := fun o ho e => h2 (e ▸ ho)
  by_cases h3 : OrdOp.gt ∈ roots
  · rw [if_pos h3] at h
    cases h
    exact ⟨h3, fun o ho => names _ _ (Or.inr (Or.inr (Or.inl ⟨rfl, nl o ho, nl2 o ho⟩)))⟩
  rw [if_neg h3] at h
  have nl3 : ∀ o ∈ roots, o ≠ .gt := fun o ho e => h3 (e ▸ ho)
  by_cases h4 : OrdOp.ge ∈ roots
  · rw [if_pos h4] at h
    cases h
    refine ⟨h4, fun o ho => names _ _ (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩)))⟩
    cases o
    · exact absurd rfl (nl _ ho)
    · exact absurd rfl (nl2 _ ho)
    · exact absurd rfl (nl3 _ ho)
    · rfl
  · rw [if_neg h4] at h
    cases h

theorem rootsOf_mem (c : OrdClass) : ∀ (os roots : List OrdOp), rootsOf c os = .ok roots →
    ∀ o, o ∈ roots ↔ (o ∈ os ∧ ∃ a, c.attr o = .ok a ∧ a ≠ c.objectAttr o)
  | [], roots, h, o => by
    simp only [rootsOf, Except.ok.injEq] at h
    subst h
    simp
  | x :: xs, roots, h, o => by
    simp only [rootsOf, bind, Except.bind] at h
    cases ha : c.attr x with
    | error e => simp [ha] at h
    | ok a =>
      simp only [ha] at h
      cases hr : rootsOf c xs with
      | error e => simp [hr] at h
      | ok rest =>
        simp only [hr, pure, Except.pure, Except.ok.injEq] at h
        subst h
        have ih := rootsOf_mem c xs rest hr o
        by_cases hne : a != c.objectAttr x
        · have hne' : a ≠ c.objectAttr x := by simpa using hne
          simp only [hne, ite_true, List.mem_cons, ih]
          constructor
          · rintro (rfl | ⟨h1, h2⟩)
            · exact ⟨Or.inl rfl, a, ha, hne'⟩
            · exact ⟨Or.inr h1, h2⟩
          · rintro ⟨rfl | h1, h2⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨h1, h2⟩
        · have heq : a = c.objectAttr x := by simpa using hne
          simp only [hne, Bool.false_eq_true, ite_false, ih, List.mem_cons]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨Or.inr h1, h2⟩
          · rintro ⟨rfl | h1, ⟨b, h2, h3⟩⟩
            · rw [ha] at h2
              cases h2
              exact absurd heq h3
            · exact ⟨h1, b, h2, h3⟩

/-- `total_ordering(cls)`: a comparison that differs from `object`'s counts as a root, inherited or not
(the note in the docs); with none it raises `ValueError`; the root is the greatest name; and when every
`setattr` succeeds, every comparison ends up defined, with exactly the missing ones added. A refused
`setattr` escapes, in `TotalOrderingExact`. -/
def TotalOrderingFills : Prop :=
  (∀ c : OrdClass, (∀ o, c.attr o = .ok (c.objectAttr o)) →
    totalOrdering c = .error (.valueError "must define at least one ordering operation: < > <= >=")) ∧
  (∀ (c : OrdClass) (root : OrdOp) (added : List (OrdOp × Shape)), totalOrdering c = .ok (root, added) →
    (∃ a, c.attr root = .ok a ∧ a ≠ c.objectAttr root) ∧
    ∀ o, o ∈ added.map Prod.fst → ∀ a, c.attr o = .ok a → a = c.objectAttr o) ∧
  (∀ c : OrdClass, (∀ o s, c.setAttr o s = .ok ()) → (∃ o a, c.attr o = .ok a ∧ a ≠ c.objectAttr o) →
    (∀ o, ∃ a, c.attr o = .ok a) →
    ∃ root added, totalOrdering c = .ok (root, added) ∧
      ∀ o, (∃ a, c.attr o = .ok a ∧ a ≠ c.objectAttr o) ∨ o ∈ added.map Prod.fst)

theorem convert_covers (r : OrdOp) : ∀ o : OrdOp, o = r ∨ o ∈ (convert r).map Prod.fst := by
  intro o
  cases r <;> cases o <;> simp [convert]

theorem addMissing_ok (c : OrdClass) (roots : List OrdOp) (hs : ∀ o s, c.setAttr o s = .ok ()) :
    ∀ l : List (OrdOp × Shape), addMissing c roots l = .ok (l.filter (fun p => decide (p.1 ∉ roots)))
  | [] => rfl
  | (o, s) :: rest => by
    have ih := addMissing_ok c roots hs rest
    by_cases h : o ∈ roots
    · simp [addMissing, h, ih]
    · simp [addMissing, h, ih, hs, bind, Except.bind, pure, Except.pure]

theorem addMissing_mem (c : OrdClass) (roots : List OrdOp) :
    ∀ (l : List (OrdOp × Shape)) (added : List (OrdOp × Shape)), addMissing c roots l = .ok added →
    ∀ o ∈ added.map Prod.fst, o ∉ roots
  | [], added, h, o, ho => by
    simp only [addMissing, Except.ok.injEq] at h
    subst h
    cases ho
  | (x, s) :: rest, added, h, o, ho => by
    simp only [addMissing] at h
    by_cases hx : x ∈ roots
    · rw [if_pos hx] at h
      exact addMissing_mem c roots rest added h o ho
    · rw [if_neg hx] at h
      simp only [bind, Except.bind] at h
      cases hs : c.setAttr x s with
      | error e => simp [hs] at h
      | ok u =>
        simp only [hs] at h
        cases hm : addMissing c roots rest with
        | error e => simp [hm] at h
        | ok more =>
          simp only [hm, pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [List.map_cons] at ho
          rcases List.mem_cons.mp ho with rfl | ho
          · exact hx
          · exact addMissing_mem c roots rest more hm o ho

theorem totalOrderingFills_proven : TotalOrderingFills := by
  refine ⟨?_, ?_, ?_⟩
  · intro c h
    have hr : rootsOf c ordOps = .ok [] := by
      simp [rootsOf, ordOps, h, bind, Except.bind, pure, Except.pure]
    simp [totalOrdering, hr, maxRoot, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw]
  · intro c root added h
    simp only [totalOrdering, bind, Except.bind] at h
    cases hr : rootsOf c ordOps with
    | error e => simp [hr] at h
    | ok roots =>
      simp only [hr] at h
      cases hm : maxRoot roots with
      | none => simp [hm, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at h
      | some r =>
        simp only [hm] at h
        cases ha : addMissing c roots (convert r) with
        | error e => simp [ha] at h
        | ok more =>
          simp only [ha, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hmem := (maxRoot_is_max roots r hm).1
          refine ⟨((rootsOf_mem c ordOps roots hr r).mp hmem).2, ?_⟩
          intro o ho a hoa
          have hnot := addMissing_mem c roots _ more ha o ho
          by_cases e : a = c.objectAttr o
          · exact e
          · exact absurd ((rootsOf_mem c ordOps roots hr o).mpr
              ⟨by cases o <;> simp [ordOps], a, hoa, e⟩) hnot
  · intro c hs ⟨o0, a0, h0, hne⟩ hall
    have hrok : ∃ roots, rootsOf c ordOps = .ok roots := by
      have aux : ∀ l : List OrdOp, ∃ rs, rootsOf c l = .ok rs := by
        intro l
        induction l with
        | nil => exact ⟨[], rfl⟩
        | cons x xs ih =>
          obtain ⟨rs, hrs⟩ := ih
          obtain ⟨a, ha⟩ := hall x
          refine ⟨if a != c.objectAttr x then x :: rs else rs, ?_⟩
          simp only [rootsOf, ha, hrs, bind, Except.bind, pure, Except.pure]
          first | rfl | skip
      exact aux _
    obtain ⟨roots, hr⟩ := hrok
    have hin : o0 ∈ roots := (rootsOf_mem c ordOps roots hr o0).mpr
      ⟨by cases o0 <;> simp [ordOps], a0, h0, hne⟩
    have hsome : ∃ r, maxRoot roots = some r := by
      unfold maxRoot
      split
      · exact ⟨_, rfl⟩
      split
      · exact ⟨_, rfl⟩
      split
      · exact ⟨_, rfl⟩
      split
      · exact ⟨_, rfl⟩
      next h1 h2 h3 h4 =>
        cases o0
        · exact absurd hin h1
        · exact absurd hin h2
        · exact absurd hin h3
        · exact absurd hin h4
    obtain ⟨r, hm⟩ := hsome
    have hrm := (maxRoot_is_max roots r hm).1
    refine ⟨r, (convert r).filter (fun p => decide (p.1 ∉ roots)), ?_, ?_⟩
    · simp only [totalOrdering, hr, hm, addMissing_ok c roots hs, bind, Except.bind, pure,
        Except.pure]
      first | rfl | skip
    intro o
    by_cases ho : o ∈ roots
    · exact Or.inl ((rootsOf_mem c ordOps roots hr o).mp ho).2
    · right
      rcases convert_covers r o with rfl | h
      · exact absurd hrm ho
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
        exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simpa using ho⟩, rfl⟩

/-! ### `cmp_to_key` -/

/-- Two key objects compare the same way in both twins when the result type is lawful: `!=` of the
result is the negation of the truth of `==`, as for `int`, `float` and `Fraction`. The law is the
hypothesis because the twins really differ without it. Holds for any `mycmp`, which may raise. -/
def CmpToKeyTwinsLawful : Prop :=
  ∀ (α ρ τ : Type) (K : KeyOps ρ τ) (mycmp : α → α → Py ρ) (op : CmpOp) (x y : α),
    (∀ r, K.cmp0 r .ne = do pure (K.ofBool (!(← K.truth (← K.cmp0 r .eq))))) →
    keyCompareC K mycmp op (some x) (.key (some y)) = keyComparePy K mycmp op (some x) (.key (some y))

theorem cmpToKeyTwinsLawful_proven : CmpToKeyTwinsLawful := by
  intro α ρ τ K mycmp op x y hlaw
  simp only [keyCompareC, keyComparePy, bind, Except.bind, pure, Except.pure]
  cases h : mycmp x y with
  | error e => rfl
  | ok r =>
    cases op <;> simp only
    have := hlaw r
    simp only [bind, Except.bind, pure, Except.pure] at this
    rw [this]

/-- `K(a) op K(b)` follows the sign of `mycmp(a, b)` for all six operators, for an `int` result, in
both twins. `cmp_to_key` docs: "a comparison function ... returns a negative number". -/
def CmpToKeySign : Prop :=
  ∀ (α : Type) (mycmp : α → α → Py Int) (x y : α) (r : Int), mycmp x y = .ok r →
    let K : KeyOps Int Bool := ⟨fun r o => .ok (match o with
      | .lt => decide (r < 0) | .le => decide (r ≤ 0) | .eq => decide (r = 0)
      | .ne => decide (r ≠ 0) | .gt => decide (r > 0) | .ge => decide (r ≥ 0)), fun b => .ok b, id⟩
    keyComparePy K mycmp .lt (some x) (.key (some y)) = .ok (decide (r < 0)) ∧
    keyComparePy K mycmp .ne (some x) (.key (some y)) = .ok (decide (r ≠ 0)) ∧
    keyCompareC K mycmp .ge (some x) (.key (some y)) = .ok (decide (r ≥ 0)) ∧
    keyCompareC K mycmp .ne (some x) (.key (some y)) = .ok (decide (r ≠ 0))

theorem cmpToKeySign_proven : CmpToKeySign := by
  intro α mycmp x y r h K
  simp [keyComparePy, keyCompareC, K, h, bind, Except.bind, pure, Except.pure]

/-- The two `cmp_to_key` agree on every right operand with an `obj`. False: C tests the exact type, so
`K(1) < Duck()` raises `TypeError` where the Python class reads `.obj` and answers. -/
def CmpToKeyTwinsOnDuck : Prop :=
  ∀ (mycmp : Nat → Nat → Py Int) (op : CmpOp) (x y : Nat),
    let K : KeyOps Int Bool := ⟨fun r _ => .ok (decide (r < 0)), fun b => .ok b, id⟩
    keyCompareC K mycmp op (some x) (.duck y) = keyComparePy K mycmp op (some x) (.duck y)

theorem cmpToKeyTwinsOnDuck_refuted : ¬CmpToKeyTwinsOnDuck := by
  intro h
  have := h (fun _ _ => .ok (-1)) .lt 1 2
  simp [keyCompareC, keyComparePy, bind, Except.bind, pure, Except.pure] at this

/-- `!=` on two key objects is the same in both twins for any result type. False: Python negates the
truth of `==`, C compares with `!=`, so a result whose `__ne__` is not the negation of its `__eq__`, or
a non-`bool` result, differs. -/
def CmpToKeyTwinsOnNe : Prop :=
  ∀ (K : KeyOps Nat Nat) (mycmp : Nat → Nat → Py Nat) (x y : Nat),
    keyCompareC K mycmp .ne (some x) (.key (some y)) =
      keyComparePy K mycmp .ne (some x) (.key (some y))

theorem cmpToKeyTwinsOnNe_refuted : ¬CmpToKeyTwinsOnNe := by
  intro h
  have := h ⟨fun _ o => .ok (if o = .ne then 7 else 1), fun _ => .ok true, fun b => if b then 1 else 0⟩
    (fun _ _ => .ok 0) 1 2
  simp [keyCompareC, keyComparePy, bind, Except.bind, pure, Except.pure] at this

/-- Construction takes one argument, positional or `obj=`, and refuses anything else, in both twins. -/
def KeyNewOneArgument : Prop :=
  ∀ (α : Type) (a b : α),
    keyNew [a] [] = .ok a ∧ keyNew [] [("obj", a)] = .ok a ∧
    (keyNew ([] : List α) []).raises "TypeError" ∧ (keyNew [a, b] []).raises "TypeError" ∧
    (keyNew [a] [("obj", b)]).raises "TypeError"

theorem keyNewOneArgument_proven : KeyNewOneArgument :=
  fun _ _ _ => ⟨rfl, rfl, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

end PyLean.CoreLibs.Functools
