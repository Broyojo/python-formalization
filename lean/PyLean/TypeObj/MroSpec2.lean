import PyLean.TypeObj.MroSpec
import PyLean.TypeObj.PropsTypeNew

/-!
Exact statements for the rest of class creation's base and metaclass logic:
`_PyType_CalculateMetaclass`, `find_best_base`, `set_mro_error` and the error paths of
`mro_implementation_unlocked` with `class_name` and `check_duplicates`
(`Objects/typeobject.c`, CPython 3.15.2).
-/

namespace PyLean.TypeObj

/-! ## `_PyType_CalculateMetaclass` -/

/-- **The metaclass calculation, exactly.** `Objects/typeobject.c:4213-4244`:
* the result is the starting metaclass or the metaclass of a base, and under the subtype
  order (a type invariant of C3 hierarchies) a subclass of every one of them;
* the calculation fails exactly when some base's metaclass is unrelated to the winner of the
  bases before it. This depends on order: with `M3(M1, M2)`, `class C(A1, A2, A3)` (metaclasses
  `M1, M2, M3`) is a conflict although `M3` is below all three, while `class C(A3, A1, A2)`
  gives `M3` (both checked on CPython 3.15.2);
* `calculateMetaclass` raises the exact message of `:4238-4242` on failure. -/
def MetaclassExact : Prop :=
  ∀ (w : World) (start : Addr) (bases : List Val),
    (∀ r, calculateMetaclassLoop w start bases = some r →
      (r = start ∨ ∃ b ∈ bases, r = typeOf w b) ∧
      (SubtypeOrder w → isSubtype w r start = true ∧ ∀ b ∈ bases, isSubtype w r (typeOf w b) = true)) ∧
    (calculateMetaclassLoop w start bases = none ↔
      ∃ pre b post win, bases = pre ++ b :: post ∧ calculateMetaclassLoop w start pre = some win ∧
        isSubtype w win (typeOf w b) = false ∧ isSubtype w (typeOf w b) win = false) ∧
    (∀ r, calculateMetaclassLoop w start bases = some r → calculateMetaclass start bases w = .ok r w) ∧
    (calculateMetaclassLoop w start bases = none →
      calculateMetaclass start bases w = (typeErr "metaclass conflict: the metaclass of a derived class must be a (non-strict) subclass of the metaclasses of all its bases" : M Addr) w)

theorem calcMeta_mem (w : World) :
    ∀ (bases : List Val) (start r : Addr), calculateMetaclassLoop w start bases = some r →
      r = start ∨ ∃ b ∈ bases, r = typeOf w b := by
  intro bases
  induction bases with
  | nil => intro start r h; simp [calculateMetaclassLoop] at h; exact Or.inl h.symm
  | cons b rest ih =>
    intro start r h
    simp only [calculateMetaclassLoop] at h
    split at h
    · rcases ih start r h with h1 | ⟨x, hx, h1⟩
      · exact Or.inl h1
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, h1⟩
    · split at h
      · rcases ih _ r h with h1 | ⟨x, hx, h1⟩
        · exact Or.inr ⟨b, List.mem_cons_self, h1⟩
        · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, h1⟩
      · simp at h

theorem calcMeta_none_iff (w : World) :
    ∀ (bases : List Val) (start : Addr), calculateMetaclassLoop w start bases = none ↔
      ∃ pre b post win, bases = pre ++ b :: post ∧ calculateMetaclassLoop w start pre = some win ∧
        isSubtype w win (typeOf w b) = false ∧ isSubtype w (typeOf w b) win = false := by
  intro bases
  induction bases with
  | nil =>
    intro start
    simp only [calculateMetaclassLoop, reduceCtorEq, false_iff]
    rintro ⟨pre, b, post, win, h, _⟩
    cases pre <;> simp at h
  | cons b rest ih =>
    intro start
    constructor
    · intro h
      simp only [calculateMetaclassLoop] at h
      by_cases h1 : isSubtype w start (typeOf w b) = true
      · simp only [h1, ite_true] at h
        obtain ⟨pre, x, post, win, h2, h3, h4, h5⟩ := (ih start).mp h
        refine ⟨b :: pre, x, post, win, by simp [h2], ?_, h4, h5⟩
        simp [calculateMetaclassLoop, h1, h3]
      · simp only [h1, Bool.false_eq_true, ite_false] at h
        by_cases h2 : isSubtype w (typeOf w b) start = true
        · simp only [h2, ite_true] at h
          obtain ⟨pre, x, post, win, h3, h4, h5, h6⟩ := (ih _).mp h
          refine ⟨b :: pre, x, post, win, by simp [h3], ?_, h5, h6⟩
          simp [calculateMetaclassLoop, h1, h2, h4]
        · exact ⟨[], b, rest, start, rfl, rfl, by simpa using h1, by simpa using h2⟩
    · rintro ⟨pre, x, post, win, h1, h2, h3, h4⟩
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        simp only [calculateMetaclassLoop, Option.some.injEq] at h2
        subst h2
        simp [calculateMetaclassLoop, h3, h4]
      | cons p pre' =>
        simp only [List.cons_append, List.cons.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        simp only [calculateMetaclassLoop] at h2 ⊢
        split
        · rename_i hs
          simp only [hs, ite_true] at h2
          exact (ih start).mpr ⟨pre', x, post, win, rfl, h2, h3, h4⟩
        · rename_i hs
          simp only [hs, Bool.false_eq_true, ite_false] at h2
          split
          · rename_i hs2
            simp only [hs2, ite_true] at h2
            exact (ih _).mpr ⟨pre', x, post, win, rfl, h2, h3, h4⟩
          · rename_i hs2
            simp [hs2] at h2

theorem metaclassExact_proven : MetaclassExact := by
  intro w start bases
  refine ⟨?_, calcMeta_none_iff w bases start, ?_, ?_⟩
  · intro r h
    exact ⟨calcMeta_mem w bases start r h, fun ho => metaclassWinner_proven w bases start r ho h⟩
  · intro r h
    simp [calculateMetaclass, h]
  · intro h
    simp [calculateMetaclass, h]

/-! ## `find_best_base` -/

/-- `solid_base(base_i)` of a base, `0` for a value that is not a class. -/
def solidOf (w : World) (x : Val) : Addr :=
  match asType w x with
  | some t => solidBase w t
  | none => 0

/-- The base is a class that allows subclassing (`Py_TPFLAGS_BASETYPE`). -/
def Acceptable (w : World) (x : Val) : Prop :=
  ∃ t, asType w x = some t ∧ (tdata w t).baseType = true

def Comparable (w : World) (a b : Addr) : Prop :=
  isSubtype w a b = true ∨ isSubtype w b a = true

/-- The solid base of `x` is a subclass of the solid base of every item of `L`. -/
def IsMinSolid (w : World) (L : List Val) (x : Val) : Prop :=
  ∀ z ∈ L, isSubtype w (solidOf w x) (solidOf w z) = true

/-- Two solid bases with a common subclass are related. Only solid bases (`solid_base` of some
class): two unrelated plain classes `A`, `B` do share the subclass `class C(A, B)`. A type
invariant of hierarchies built by `type_new`: `find_best_base` refuses a class whose bases have
unrelated solid bases (the lay-out conflict), so every solid base above a class lies on the
`tp_base` chain of its own solid base, and those chains form a tree. -/
def TreeOrder (w : World) : Prop :=
  ∀ s t c, isSubtype w c (solidBase w s) = true → isSubtype w c (solidBase w t) = true →
    Comparable w (solidBase w s) (solidBase w t)

theorem solidOf_of (w : World) (x : Val) (t : Addr) (h : asType w x = some t) :
    solidOf w x = solidBase w t := by simp [solidOf, h]

theorem asType_self (w : World) (x : Val) (t : Addr) (h : asType w x = some t) :
    asType w (.obj t) = some t := by
  rw [← asType_obj w x t h]; exact h

theorem bestBase_first (w : World) (ho : SubtypeOrder w) :
    ∀ (xs P : List Val) (win base r : Addr),
      (∀ z ∈ P, Acceptable w z) →
      (∀ z ∈ P, isSubtype w win (solidOf w z) = true) →
      (∃ pre post, P = pre ++ .obj base :: post ∧ asType w (.obj base) = some base ∧
        solidBase w base = win ∧ ∀ y ∈ pre, ¬ IsMinSolid w P y) →
      bestBaseLoop w xs (some win) (some base) = .ok r →
      (∀ z ∈ P ++ xs, Acceptable w z) ∧
      ∃ pre post, P ++ xs = pre ++ .obj r :: post ∧ asType w (.obj r) = some r ∧
        IsMinSolid w (P ++ xs) (.obj r) ∧ ∀ y ∈ pre, ¬ IsMinSolid w (P ++ xs) y := by
  intro xs
  induction xs with
  | nil =>
    intro P win base r hacc hwin ⟨pre, post, hP, hab, hsb, hpre⟩ h
    simp only [bestBaseLoop, Except.ok.injEq] at h
    subst h
    simp only [List.append_nil]
    refine ⟨hacc, pre, post, hP, hab, ?_, hpre⟩
    intro z hz
    rw [solidOf_of w _ _ hab, hsb]
    exact hwin z hz
  | cons x rest ih =>
    intro P win base r hacc hwin ⟨pre, post, hP, hab, hsb, hpre⟩ h
    simp only [bestBaseLoop] at h
    cases hx : asType w x with
    | none => rw [hx] at h; simp at h
    | some bi =>
      rw [hx] at h
      simp only at h
      by_cases hbt : (tdata w bi).baseType = true
      · simp only [hbt, Bool.not_true, Bool.false_eq_true, ite_false] at h
        have haccx : Acceptable w x := ⟨bi, hx, hbt⟩
        have hacc' : ∀ z ∈ P ++ [x], Acceptable w z := by
          intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hacc z hz
          · simp at hz; subst hz; exact haccx
        have hsx : solidOf w x = solidBase w bi := solidOf_of w x bi hx
        have hassoc : P ++ x :: rest = (P ++ [x]) ++ rest := by simp
        by_cases h1 : isSubtype w win (solidBase w bi) = true
        · simp only [h1, ite_true] at h
          have := ih (P ++ [x]) win base r hacc' ?_ ?_ h
          · rw [hassoc]; exact this
          · intro z hz
            rcases List.mem_append.mp hz with hz | hz
            · exact hwin z hz
            · simp at hz; subst hz; rw [hsx]; exact h1
          · refine ⟨pre, post ++ [x], by simp [hP], hab, hsb, ?_⟩
            intro y hy hmin
            exact hpre y hy (fun z hz => hmin z (List.mem_append_left _ hz))
        · have h1' : isSubtype w win (solidBase w bi) = false := by simpa using h1
          simp only [h1', Bool.false_eq_true, ite_false] at h
          by_cases h2 : isSubtype w (solidBase w bi) win = true
          · simp only [h2, ite_true] at h
            have := ih (P ++ [x]) (solidBase w bi) bi r hacc' ?_ ?_ h
            · rw [hassoc]; exact this
            · intro z hz
              rcases List.mem_append.mp hz with hz | hz
              · exact ho.2 _ _ _ h2 (hwin z hz)
              · simp at hz; subst hz; rw [hsx]; exact ho.1 _
            · refine ⟨P, [], by rw [asType_obj w x bi hx], asType_self w x bi hx, rfl, ?_⟩
              intro y hy hmin
              have hyx := hmin x (by simp)
              rw [hsx] at hyx
              exact h1 (ho.2 _ _ _ (hwin y hy) hyx)
          · simp [h2] at h
      · have hbt' : (tdata w bi).baseType = false := by simpa using hbt
        simp [hbt'] at h

theorem bestBase_chain_ok (w : World) :
    ∀ (xs : List Val) (win base : Addr), (∀ z ∈ xs, Acceptable w z) →
      (∀ z ∈ xs, Comparable w win (solidOf w z)) →
      (∀ y ∈ xs, ∀ z ∈ xs, Comparable w (solidOf w y) (solidOf w z)) →
      ∃ r, bestBaseLoop w xs (some win) (some base) = .ok r := by
  intro xs
  induction xs with
  | nil => intro win base _ _ _; exact ⟨base, rfl⟩
  | cons x rest ih =>
    intro win base hacc hcmp hpair
    obtain ⟨bi, hx, hbt⟩ := hacc x List.mem_cons_self
    have hsx : solidOf w x = solidBase w bi := solidOf_of w x bi hx
    have hacc' := fun z hz => hacc z (List.mem_cons_of_mem x hz)
    have hpair' := fun y hy z hz => hpair y (List.mem_cons_of_mem x hy) z (List.mem_cons_of_mem x hz)
    simp only [bestBaseLoop, hx, hbt, Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases h1 : isSubtype w win (solidBase w bi) = true
    · simp only [h1, ite_true]
      exact ih win base hacc' (fun z hz => hcmp z (List.mem_cons_of_mem x hz)) hpair'
    · have h2 : isSubtype w (solidBase w bi) win = true := by
        rcases hcmp x List.mem_cons_self with h | h
        · rw [hsx] at h; exact absurd h h1
        · rw [hsx] at h; exact h
      simp only [h1, Bool.false_eq_true, ite_false, h2, ite_true]
      refine ih _ bi hacc' ?_ hpair'
      intro z hz
      have := hpair x List.mem_cons_self z (List.mem_cons_of_mem x hz)
      rw [hsx] at this
      exact this

theorem bestBase_err_layout (w : World) :
    ∀ (xs : List Val) (win base : Addr) (m : String), (∀ z ∈ xs, Acceptable w z) →
      bestBaseLoop w xs (some win) (some base) = .error m →
      m = "multiple bases have instance lay-out conflict" := by
  intro xs
  induction xs with
  | nil => intro win base m _ h; simp [bestBaseLoop] at h
  | cons x rest ih =>
    intro win base m hacc h
    obtain ⟨bi, hx, hbt⟩ := hacc x List.mem_cons_self
    have hacc' := fun z hz => hacc z (List.mem_cons_of_mem x hz)
    simp only [bestBaseLoop, hx, hbt, Bool.not_true, Bool.false_eq_true, ite_false] at h
    split at h
    · exact ih _ _ m hacc' h
    · split at h
      · exact ih _ _ m hacc' h
      · simp only [Except.error.injEq] at h
        exact h.symm

theorem bestBase_prefix (w : World) (x : Val) (post : List Val) :
    ∀ (pre : List Val) (st bs : Option Addr), (∀ y ∈ pre, Acceptable w y) →
      (∀ y ∈ pre, ∀ z ∈ pre, Comparable w (solidOf w y) (solidOf w z)) →
      (∀ win, st = some win → ∀ y ∈ pre, Comparable w win (solidOf w y)) →
      ∃ st' bs', bestBaseLoop w (pre ++ x :: post) st bs = bestBaseLoop w (x :: post) st' bs' := by
  intro pre
  induction pre with
  | nil => intro st bs _ _ _; exact ⟨st, bs, rfl⟩
  | cons y rest ih =>
    intro st bs hacc hpair hst
    obtain ⟨bi, hy, hbt⟩ := hacc y List.mem_cons_self
    have hsy : solidOf w y = solidBase w bi := solidOf_of w y bi hy
    have hacc' := fun z hz => hacc z (List.mem_cons_of_mem y hz)
    have hpair' := fun a ha b hb => hpair a (List.mem_cons_of_mem y ha) b (List.mem_cons_of_mem y hb)
    have hnew : ∀ win, win = solidBase w bi → ∀ z ∈ rest, Comparable w win (solidOf w z) := by
      intro win hw z hz
      have := hpair y List.mem_cons_self z (List.mem_cons_of_mem y hz)
      rw [hsy, ← hw] at this
      exact this
    simp only [List.cons_append, bestBaseLoop, hy, hbt, Bool.not_true, Bool.false_eq_true, ite_false]
    cases st with
    | none =>
      simp only
      exact ih _ _ hacc' hpair' (fun win h => hnew win (Option.some.inj h).symm)
    | some win =>
      simp only
      have hold : ∀ z ∈ rest, Comparable w win (solidOf w z) :=
        fun z hz => hst win rfl z (List.mem_cons_of_mem y hz)
      by_cases h1 : isSubtype w win (solidBase w bi) = true
      · simp only [h1, ite_true]
        exact ih _ _ hacc' hpair' (fun v hv => by cases hv; exact hold)
      · have h2 : isSubtype w (solidBase w bi) win = true := by
          rcases hst win rfl y List.mem_cons_self with h | h
          · rw [hsy] at h; exact absurd h h1
          · rw [hsy] at h; exact h
        simp only [h1, Bool.false_eq_true, ite_false, h2, ite_true]
        exact ih _ _ hacc' hpair' (fun v hv => hnew v (Option.some.inj hv).symm)

/-- **`find_best_base`, exactly.** `Objects/typeobject.c:3743-3797`, under the subtype order
(reflexive and transitive, a type invariant of C3 hierarchies):
* a result `r` is a base, every base is an acceptable class, the solid base of `r` is a
  subclass of the solid base of every base, and `r` is the **first** base with that property
  ("This is the first one that's on the path to the 'solid base'", `:3743-3744`): with
  `class P: pass`, `class Q: pass`, `type('C', (P, Q), {}).__base__` is `P`, and with
  `(P, int)` it is `int` (checked on 3.15.2);
* acceptable bases whose solid bases are pairwise related always succeed, however many;
* acceptable bases two of which have unrelated solid bases fail with the exact layout-conflict
  message, when solid bases form a tree (`TreeOrder`, a type invariant);
* the first base that is not a class, or does not allow subclassing, gives its exact message
  (`:3760-3764`, `:3772-3776`), whatever follows. -/
def FindBestBaseExact : Prop :=
  ∀ (w : World) (bases : List Val), SubtypeOrder w →
    (∀ r, bestBaseLoop w bases none none = .ok r →
      (∀ z ∈ bases, Acceptable w z) ∧
      ∃ pre post, bases = pre ++ .obj r :: post ∧ asType w (.obj r) = some r ∧
        IsMinSolid w bases (.obj r) ∧ ∀ y ∈ pre, ¬ IsMinSolid w bases y) ∧
    (bases ≠ [] → (∀ z ∈ bases, Acceptable w z) →
      (∀ y ∈ bases, ∀ z ∈ bases, Comparable w (solidOf w y) (solidOf w z)) →
      ∃ r, bestBaseLoop w bases none none = .ok r) ∧
    (TreeOrder w → (∀ z ∈ bases, Acceptable w z) →
      (∃ y ∈ bases, ∃ z ∈ bases, ¬ Comparable w (solidOf w y) (solidOf w z)) →
      bestBaseLoop w bases none none = .error "multiple bases have instance lay-out conflict") ∧
    (∀ pre x post, bases = pre ++ x :: post → (∀ y ∈ pre, Acceptable w y) →
      (∀ y ∈ pre, ∀ z ∈ pre, Comparable w (solidOf w y) (solidOf w z)) →
      (asType w x = none → bestBaseLoop w bases none none = .error s!"bases must be types; got '{objFQN w x}'") ∧
      (∀ t, asType w x = some t → (tdata w t).baseType = false →
        bestBaseLoop w bases none none =
          .error s!"type '{trunc 100 (tpName w t)}' is not an acceptable base type"))

theorem bestBase_first_top (w : World) (ho : SubtypeOrder w) (bases : List Val) (r : Addr)
    (h : bestBaseLoop w bases none none = .ok r) :
    (∀ z ∈ bases, Acceptable w z) ∧
      ∃ pre post, bases = pre ++ .obj r :: post ∧ asType w (.obj r) = some r ∧
        IsMinSolid w bases (.obj r) ∧ ∀ y ∈ pre, ¬ IsMinSolid w bases y := by
  cases bases with
  | nil => simp [bestBaseLoop] at h
  | cons x rest =>
    simp only [bestBaseLoop] at h
    cases hx : asType w x with
    | none => rw [hx] at h; simp at h
    | some bi =>
      rw [hx] at h
      simp only at h
      by_cases hbt : (tdata w bi).baseType = true
      · simp only [hbt, Bool.not_true, Bool.false_eq_true, ite_false] at h
        have hsx : solidOf w x = solidBase w bi := solidOf_of w x bi hx
        have := bestBase_first w ho rest [x] (solidBase w bi) bi r
          (by intro z hz; simp at hz; subst hz; exact ⟨bi, hx, hbt⟩)
          (by intro z hz; simp at hz; subst hz; rw [hsx]; exact ho.1 _)
          ⟨[], [], by rw [asType_obj w x bi hx]; rfl, asType_self w x bi hx, rfl, by simp⟩ h
        simpa using this
      · have hbt' : (tdata w bi).baseType = false := by simpa using hbt
        simp [hbt'] at h

theorem findBestBaseExact_proven : FindBestBaseExact := by
  intro w bases ho
  refine ⟨fun r h => bestBase_first_top w ho bases r h, ?_, ?_, ?_⟩
  · intro hne hacc hpair
    cases bases with
    | nil => exact absurd rfl hne
    | cons x rest =>
      obtain ⟨bi, hx, hbt⟩ := hacc x List.mem_cons_self
      have hsx : solidOf w x = solidBase w bi := solidOf_of w x bi hx
      simp only [bestBaseLoop, hx, hbt, Bool.not_true, Bool.false_eq_true, ite_false]
      refine bestBase_chain_ok w rest _ bi (fun z hz => hacc z (List.mem_cons_of_mem x hz)) ?_
        (fun y hy z hz => hpair y (List.mem_cons_of_mem x hy) z (List.mem_cons_of_mem x hz))
      intro z hz
      have := hpair x List.mem_cons_self z (List.mem_cons_of_mem x hz)
      rw [hsx] at this
      exact this
  · intro htree hacc ⟨y, hy, z, hz, hyz⟩
    cases hr : bestBaseLoop w bases none none with
    | ok r =>
      obtain ⟨_, pre, post, _, _, hmin, _⟩ := bestBase_first_top w ho bases r hr
      obtain ⟨by', hy', _⟩ := hacc y hy
      obtain ⟨bz, hz', _⟩ := hacc z hz
      have h1 := hmin y hy
      have h2 := hmin z hz
      rw [solidOf_of w y by' hy'] at h1 hyz
      rw [solidOf_of w z bz hz'] at h2 hyz
      exact absurd (htree _ _ _ h1 h2) hyz
    | error m =>
      cases bases with
      | nil => simp at hy
      | cons x rest =>
        obtain ⟨bi, hx, hbt⟩ := hacc x List.mem_cons_self
        simp only [bestBaseLoop, hx, hbt, Bool.not_true, Bool.false_eq_true, ite_false] at hr
        rw [bestBase_err_layout w rest _ bi m (fun z hz => hacc z (List.mem_cons_of_mem x hz)) hr]
  · intro pre x post hb hacc hpair
    obtain ⟨st, bs, heq⟩ := bestBase_prefix w x post pre none none hacc hpair (by simp)
    rw [hb, heq]
    refine ⟨fun hx => by simp [bestBaseLoop, hx], fun t hx hbt => by simp [bestBaseLoop, hx, hbt]⟩

/-! ## `set_mro_error` -/

/-- The candidate names joined by `,`, as the loop writes them. -/
def commaJoin : List (List Char) → List Char
  | [] => []
  | [x] => x
  | x :: y :: r => x ++ ',' :: commaJoin (y :: r)

theorem utf8Bytes_append (a b : List Char) : utf8Bytes (a ++ b) = utf8Bytes a + utf8Bytes b := by
  simp [utf8Bytes]

theorem cutUtf8_of_le : ∀ (l : List Char) (n : Nat), utf8Bytes l ≤ n → cutUtf8 n l = l := by
  intro l
  induction l with
  | nil => intro n _; simp [cutUtf8]
  | cons c cs ih =>
    intro n h
    simp only [utf8Bytes, List.map_cons, List.sum_cons] at h
    have h1 : c.utf8Size ≤ n := by omega
    simp only [cutUtf8, h1, ite_true]
    rw [ih (n - c.utf8Size) (by simp only [utf8Bytes]; omega)]

theorem dedupKeep_eq_loop : ∀ (l seen : List Addr),
    dedupKeep l seen = List.eraseDupsBy.loop (· == ·) l seen := by
  intro l
  induction l with
  | nil => intro seen; simp [dedupKeep, List.eraseDupsBy.loop]
  | cons x xs ih =>
    intro seen
    simp only [dedupKeep, List.eraseDupsBy.loop]
    have : seen.contains x = seen.any (fun b => x == b) := by
      induction seen with
      | nil => rfl
      | cons s ss ihs =>
        simp only [List.contains_cons, List.any_cons, ihs]
    rw [this]
    cases seen.any (fun b => x == b) <;> simp [ih]

theorem dedupKeep_eraseDups (l : List Addr) : dedupKeep l [] = l.eraseDups := by
  rw [dedupKeep_eq_loop]; rfl

/-- What `" %s"` writes for a class whose `__name__` is `v`: a space, then the text of a `str`
(a subclass included) up to its first NUL, or `?` for anything else. -/
def mroNameText (w : World) (v : Val) : List Char := ' ' :: (cStr ((strOf w v).getD "?")).toList

theorem char_utf8Size_pos (c : Char) : 0 < c.utf8Size := Char.utf8Size_pos c

/-- A cut at `n` bytes of `P ++ X` stops inside `P` when `P` has at least `n` bytes. -/
theorem cutUtf8_append_of_ge : ∀ (P X : List Char) (n : Nat), n ≤ utf8Bytes P →
    cutUtf8 n (P ++ X) = cutUtf8 n P := by
  intro P
  induction P with
  | nil =>
    intro X n h
    simp only [utf8Bytes, List.map_nil, List.sum_nil, Nat.le_zero] at h
    subst h
    cases X with
    | nil => rfl
    | cons c cs =>
      have := char_utf8Size_pos c
      have h0 : ¬ c.utf8Size ≤ 0 := by omega
      simp [cutUtf8, h0]
  | cons c cs ih =>
    intro X n h
    simp only [utf8Bytes, List.map_cons, List.sum_cons] at h
    simp only [List.cons_append, cutUtf8]
    split
    · rw [ih X (n - c.utf8Size) (by simp only [utf8Bytes]; omega)]
    · rfl

theorem cutUtf8_prefix_of_ge (P L : List Char) (n : Nat) (hp : P <+: L) (h : n ≤ utf8Bytes P) :
    cutUtf8 n L = cutUtf8 n P := by
  obtain ⟨X, rfl⟩ := hp
  exact cutUtf8_append_of_ge P X n h

theorem utf8Bytes_eq_zero (X : List Char) (h : utf8Bytes X = 0) : X = [] := by
  cases X with
  | nil => rfl
  | cons c cs =>
    have := char_utf8Size_pos c
    simp only [utf8Bytes, List.map_cons, List.sum_cons] at h; omega

theorem dedupKeep_head : ∀ (l seen : List Addr), ∃ ys, dedupKeep l seen = seen.reverse ++ ys := by
  intro l
  induction l with
  | nil => intro seen; exact ⟨[], by simp [dedupKeep]⟩
  | cons x xs ih =>
    intro seen
    simp only [dedupKeep]
    split
    · exact ih seen
    · obtain ⟨ys, h⟩ := ih (x :: seen)
      exact ⟨x :: ys, by rw [h]; simp⟩

theorem setMroErrorLoop_extends (rt : Rt) (w : World) (nm : Addr → Val)
    (hn : ∀ c, rt.getOptionalAttr (.obj c) "__name__" w = .ok (some (nm c)) w) :
    ∀ (cands : List Addr) (off : Nat) (text : List Char),
      ∃ X, setMroErrorLoop rt cands off text w = .ok (text ++ X) w := by
  intro cands
  induction cands with
  | nil => intro off text; exact ⟨[], by simp [setMroErrorLoop]⟩
  | cons c cs ih =>
    intro off text
    have hcls : classNameOf rt (.obj c) w = .ok (strOf w (nm c)) w := by
      simp [classNameOf, hn c]
    rw [setMroErrorLoop]
    by_cases hlt : off < 1000
    · simp only [hlt, ite_true, M.bind_app, hcls]
      split
      · obtain ⟨X, hX⟩ := ih (off + utf8Bytes (" " ++ cStr ((strOf w (nm c)).getD "?")).toList + 1)
          (text ++ (" " ++ cStr ((strOf w (nm c)).getD "?")).toList ++ [','])
        exact ⟨(" " ++ cStr ((strOf w (nm c)).getD "?")).toList ++ [','] ++ X, by rw [hX]; simp⟩
      · obtain ⟨X, hX⟩ := ih (off + utf8Bytes (" " ++ cStr ((strOf w (nm c)).getD "?")).toList)
          (text ++ (" " ++ cStr ((strOf w (nm c)).getD "?")).toList)
        exact ⟨(" " ++ cStr ((strOf w (nm c)).getD "?")).toList ++ X, by rw [hX]; simp⟩
    · exact ⟨[], by simp [hlt]⟩

/-- The loop's text agrees with the whole text on its first 999 bytes: either it is the whole
text, or both start with a common prefix of at least 999 bytes. -/
theorem setMroErrorLoop_text (rt : Rt) (w : World) (nm : Addr → Val)
    (hn : ∀ c, rt.getOptionalAttr (.obj c) "__name__" w = .ok (some (nm c)) w) :
    ∀ (cands : List Addr) (off : Nat) (text r : List Char), off = utf8Bytes text →
      setMroErrorLoop rt cands off text w = .ok r w →
      r = text ++ commaJoin (cands.map (fun c => mroNameText w (nm c))) ∨
        ∃ P, P <+: text ++ commaJoin (cands.map (fun c => mroNameText w (nm c))) ∧ P <+: r ∧
          999 ≤ utf8Bytes P := by
  intro cands
  induction cands with
  | nil =>
    intro off text r _ h
    simp only [setMroErrorLoop, M.pure_app, R.ok.injEq] at h
    left; simp [h.1, commaJoin]
  | cons c cs ih =>
    intro off text r hoff h
    have hcls : classNameOf rt (.obj c) w = .ok (strOf w (nm c)) w := by
      simp [classNameOf, hn c]
    have hs : (" " ++ cStr ((strOf w (nm c)).getD "?")).toList = mroNameText w (nm c) := by
      simp [mroNameText]
    rw [setMroErrorLoop] at h
    by_cases hlt : off < 1000
    · simp only [hlt, ite_true, M.bind_app, hcls, hs] at h
      split at h
      · rename_i hc
        have hne := hc.1
        obtain ⟨d, ds, rfl⟩ : ∃ d ds, cs = d :: ds := by
          cases cs with
          | nil => exact absurd rfl hne
          | cons d ds => exact ⟨d, ds, rfl⟩
        have key : text ++ commaJoin ((c :: d :: ds).map (fun c => mroNameText w (nm c))) =
            text ++ mroNameText w (nm c) ++ [','] ++
              commaJoin ((d :: ds).map (fun c => mroNameText w (nm c))) := by
          simp [commaJoin]
        rw [key]
        have hc2 : utf8Bytes [','] = 1 := by simp [utf8Bytes]; rfl
        exact ih _ _ r (by rw [utf8Bytes_append, utf8Bytes_append, hc2, hoff]) h
      · rename_i hc
        cases cs with
        | nil =>
          have key : text ++ commaJoin ([c].map (fun c => mroNameText w (nm c))) =
              text ++ mroNameText w (nm c) ++
                commaJoin (([] : List Addr).map (fun c => mroNameText w (nm c))) := by
            simp [commaJoin]
          rw [key]
          exact ih _ _ r (by rw [utf8Bytes_append, hoff]) h
        | cons d ds =>
          have hge : 999 ≤ utf8Bytes (text ++ mroNameText w (nm c)) := by
            rw [utf8Bytes_append, ← hoff]
            exact Nat.le_of_not_lt (fun hcon => hc ⟨by simp, by omega⟩)
          right
          refine ⟨text ++ mroNameText w (nm c),
            ⟨',' :: commaJoin ((d :: ds).map (fun c => mroNameText w (nm c))), ?_⟩, ?_, hge⟩
          · simp [commaJoin]
          · obtain ⟨X, hX⟩ := setMroErrorLoop_extends rt w nm hn (d :: ds)
              (off + utf8Bytes (mroNameText w (nm c))) (text ++ mroNameText w (nm c))
            rw [hX] at h
            simp only [R.ok.injEq] at h
            exact ⟨X, h.1⟩
    · rw [if_neg hlt] at h
      simp only [M.pure_app, R.ok.injEq] at h
      right
      refine ⟨text, ⟨_, rfl⟩, ⟨[], by simp [h.1]⟩, by omega⟩

/-- **The MRO conflict message, exactly.** `set_mro_error`, `Objects/typeobject.c:3350-3398`:
* the candidates are the heads of the remaining lists, once each, in first-seen order (a dict,
  keyed by class identity, `:3358-3366`);
* each is named by `class_name` (`:3373`): `" %s"` of a `str` `__name__` (a `str` subclass
  included), which a NUL ends, and `" ?"` for a `__name__` that is not a `str` (`:3380-3382`;
  checked on 3.15.2: a metaclass property `__name__` returning `42` gives `bases ?, B`, one
  returning `'a\x00b'` gives `bases a, B3`); names are joined by `,`;
* the `TypeError` is the first 999 bytes of `"Cannot create a consistent method resolution order
  (MRO) for bases"` followed by those names (`char buf[1000]`, `:3353`; two 600-character names
  give a 999-character message on 3.15.2), whenever that cut falls between characters;
* an exception from the first candidate's `__name__` is what `set_mro_error` leaves raised, with
  no `TypeError` (`:3384-3388`; a raising metaclass property gives that `KeyError` on 3.15.2).
Precondition of the message clause: the `__name__` lookups run no code that changes the world.
Scope: candidate hashing by identity (a metaclass `__hash__` that re-enters is the bug record
`typeobj-set-mro-error-borrowed-mro`); a cut inside a multi-byte character, where CPython raises
`UnicodeDecodeError`, is not modelled; a `str` with a lone surrogate, where `PyUnicode_AsUTF8`
fails, cannot be a Lean `String`. -/
def SetMroErrorExact : Prop :=
  (∀ (rt : Rt) (rests : List (List Addr)) (w : World) (nm : Addr → Val),
    (∀ c, rt.getOptionalAttr (.obj c) "__name__" w = .ok (some (nm c)) w) →
    let full := "Cannot create a consistent method resolution order (MRO) for bases".toList ++
      commaJoin ((rests.filterMap List.head?).eraseDups.map (fun c => mroNameText w (nm c)))
    (utf8Bytes full ≤ 999 ∨ utf8Bytes (cutUtf8 999 full) = 999) →
    (setMroError rt rests : M Unit) w = (typeErr (String.ofList (cutUtf8 999 full)) : M Unit) w) ∧
  (∀ (rt : Rt) (rests : List (List Addr)) (w : World) (c : Addr) (e : PyErr) (w1 : World),
    (rests.filterMap List.head?).head? = some c →
    rt.getOptionalAttr (.obj c) "__name__" w = .err e w1 →
    (setMroError rt rests : M Unit) w = .err e w1)

theorem setMroErrorExact_proven : SetMroErrorExact := by
  refine ⟨?_, ?_⟩
  · intro rt rests w nm hn
    dsimp only
    intro hlen
    simp only [setMroError, dedupKeep_eraseDups]
    revert hlen
    generalize "Cannot create a consistent method resolution order (MRO) for bases".toList = pre
    intro hlen
    obtain ⟨X, hX⟩ := setMroErrorLoop_extends rt w nm hn ((rests.filterMap List.head?).eraseDups)
      (utf8Bytes pre) pre
    have htext := setMroErrorLoop_text rt w nm hn ((rests.filterMap List.head?).eraseDups)
      _ _ _ rfl hX
    simp only [M.bind_app, hX]
    generalize hF : pre ++ commaJoin ((rests.filterMap List.head?).eraseDups.map
      (fun c => mroNameText w (nm c))) = F at hlen htext ⊢
    have hcut : cutUtf8 999 (pre ++ X) = cutUtf8 999 F ∧
        (utf8Bytes (pre ++ X) ≤ 999 ∨ utf8Bytes (cutUtf8 999 (pre ++ X)) = 999) := by
      rcases htext with h | ⟨P, hPF, hPr, hP⟩
      · rw [h]; exact ⟨rfl, hlen⟩
      · have e1 := cutUtf8_prefix_of_ge P (pre ++ X) 999 hPr hP
        have e2 := cutUtf8_prefix_of_ge P F 999 hPF hP
        refine ⟨by rw [e1, e2], Or.inr ?_⟩
        rw [e1]
        rcases hlen with hl | hl
        · obtain ⟨Y, rfl⟩ := hPF
          rw [utf8Bytes_append] at hl
          have hl' : utf8Bytes P ≤ 999 := by omega
          rw [cutUtf8_of_le _ 999 hl']; omega
        · rw [e2] at hl; exact hl
    have hc : ((pre ++ X).map Char.utf8Size).sum ≤ 999 ∨
        ((cutUtf8 999 (pre ++ X)).map Char.utf8Size).sum = 999 := hcut.2
    rw [if_pos hc, hcut.1]
  · intro rt rests w c e w1 hc he
    obtain ⟨ds, hds⟩ : ∃ ds, dedupKeep (rests.filterMap List.head?) [] = c :: ds := by
      cases hl : rests.filterMap List.head? with
      | nil => rw [hl] at hc; simp at hc
      | cons x xs =>
        rw [hl] at hc
        simp only [List.head?_cons, Option.some.injEq] at hc
        subst hc
        obtain ⟨ys, h⟩ := dedupKeep_head xs [x]
        exact ⟨ys, by simp [dedupKeep, h]⟩
    have hcls : classNameOf rt (.obj c) w = .err e w1 := by simp [classNameOf, he]
    have hlt : utf8Bytes "Cannot create a consistent method resolution order (MRO) for bases".toList < 1000 := by
      decide
    simp only [setMroError, M.bind_app, hds, setMroErrorLoop, hlt, ite_true, hcls]

/-! ## `mro_implementation_unlocked` with `class_name` -/

/-- **Every error of `mro_implementation_unlocked`.** On the class `t` of world `w`:
* a base with NULL `tp_mro` gives `"Cannot extend an incomplete type '%.100s'"` (`:3484-3488`);
* a duplicate base `d` gives `"duplicate base class %U"` with `class_name(d)` (`:3322-3329`):
  the `__name__` of `d` if it is a `str`, the bare message for a non-`str` `__name__`, and the
  repr of `d` when `__name__` is missing (`class_name`, `:3299-3307`); an exception from the
  lookup propagates;
* a conflict raises what `set_mro_error` raises;
* a success returns the MRO with the world unchanged. -/
def MroImplementationErrors : Prop :=
  ∀ (rt : Rt) (t : Addr) (w : World),
    let lin := mroImpl t (fun b => (tdata w b).mro) (tdata w t).bases
    (∀ b, lin = .incomplete b →
      mroImplementation rt t w = (typeErr s!"Cannot extend an incomplete type '{trunc 100 (tpName w b)}'" : M (List Addr)) w) ∧
    (∀ d v w', lin = .duplicate d → rt.getOptionalAttr (.obj d) "__name__" w = .ok (some v) w' →
      mroImplementation rt t w =
        (match strOf w' v with
         | some n => (typeErr s!"duplicate base class {n}" : M (List Addr))
         | none => typeErr "duplicate base class") w') ∧
    (∀ d w' s w'', lin = .duplicate d → rt.getOptionalAttr (.obj d) "__name__" w = .ok none w' →
      rt.repr (.obj d) w' = .ok s w'' →
      mroImplementation rt t w = (typeErr s!"duplicate base class {s}" : M (List Addr)) w'') ∧
    (∀ d e w', lin = .duplicate d → rt.getOptionalAttr (.obj d) "__name__" w = .err e w' →
      mroImplementation rt t w = .err e w') ∧
    (∀ r, lin = .conflict r → mroImplementation rt t w = setMroError rt r w) ∧
    (∀ m, lin = .ok m → mroImplementation rt t w = .ok m w)

theorem mroImplementationErrors_proven : MroImplementationErrors := by
  intro rt t w lin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b h; simp only [lin] at h; simp [mroImplementation, h]
  · intro d v w' h hv
    simp only [lin] at h
    simp only [mroImplementation, M.bind_app, getW_app, h, classNameOf, hv]
    cases strOf w' v <;> rfl
  · intro d w' s w'' h hv hr
    simp only [lin] at h
    simp [mroImplementation, h, classNameOf, hv, hr, Functor.map, M.bind, M.pure]
  · intro d e w' h hv
    simp only [lin] at h
    simp [mroImplementation, h, classNameOf, hv]
  · intro r h; simp only [lin] at h; simp [mroImplementation, h]
  · intro m h; simp only [lin] at h; simp [mroImplementation, h]

end PyLean.TypeObj
