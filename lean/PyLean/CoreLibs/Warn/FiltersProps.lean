import PyLean.CoreLibs.Warn.Filters
import PyLean.CoreLibs.Warn.Props

/-!
Properties of the filters-list API (`Filters.lean`).
-/

namespace PyLean.CoreLibs.Warn

open PyLean

/-! ## `list.remove` and `in` -/

/-- Every element's `==` against `it` gives a bool. -/
def EqTotal (it : FItem) (xs : List Elem) : Prop := ∀ e ∈ xs, ∃ b, elemEq it e = .ok b

/-- The outcome of `e == it` when it does not raise. -/
def eqB (it : FItem) (e : Elem) : Bool :=
  match elemEq it e with
  | .ok b => b
  | .error _ => false

theorem pyRemove_spec (it : FItem) (xs : List Elem) (h : EqTotal it xs) :
    pyRemove it xs = .ok (if xs.any (eqB it) then some (xs.eraseP (eqB it)) else none) := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨b, hb⟩ := h e (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    have hq : eqB it e = b := by simp [eqB, hb]
    cases b
    · cases hany : es.any (eqB it) <;>
        simp [pyRemove, hb, ih', hany, bind, Except.bind, pure, Except.pure, List.any_cons, hq,
          List.eraseP_cons]
    · simp [pyRemove, hb, bind, Except.bind, pure, Except.pure, List.any_cons, hq, List.eraseP_cons]

theorem pyContains_spec (it : FItem) (xs : List Elem) (h : EqTotal it xs) :
    pyContains it xs = .ok (xs.any (eqB it)) := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨b, hb⟩ := h e (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    have hq : eqB it e = b := by simp [eqB, hb]
    cases b <;> simp [pyContains, hb, ih', bind, Except.bind, pure, Except.pure, hq]

/-- The list after `_add_filter`: first and without its first duplicate, or appended unless
present. -/
def addSpec (it : FItem) (ap : Bool) (xs : List Elem) : List Elem :=
  if ap then (if xs.any (eqB it) then xs else xs ++ [.item it]) else .item it :: xs.eraseP (eqB it)

theorem addFilter_list (H : Hier) (it : FItem) (ap : Bool) (xs : List Elem) (v : Int) (h : EqTotal it xs) :
    addFilter H it ap ⟨.list xs, v⟩ = .ok ⟨.list (addSpec it ap xs), v + 1⟩ := by
  cases ap
  · cases hany : xs.any (eqB it)
    · have hx : xs.eraseP (eqB it) = xs := by
        apply List.eraseP_of_forall_not
        intro e he hq
        have := List.any_eq_false.mp hany e he
        simp_all
      simp [addFilter, pyRemove_spec it xs h, hany, hx, addSpec, bind, Except.bind, pure, Except.pure]
    · simp [addFilter, pyRemove_spec it xs h, hany, addSpec, bind, Except.bind, pure, Except.pure]
  · cases hany : xs.any (eqB it) <;>
      simp [addFilter, pyContains_spec it xs h, hany, addSpec, bind, Except.bind, pure, Except.pure]

theorem addFilter_ver (H : Hier) (it : FItem) (ap : Bool) (s s' : FState) (h : addFilter H it ap s = .ok s') :
    s'.ver = s.ver + 1 := by
  unfold addFilter at h
  cases hc : s.cont with
  | deleted =>
    by_cases ha : isA H noFilters "AttributeError" = true
    · simp only [hc, deletedOk, ha, if_true, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      rw [← h]
    · simp [hc, deletedOk, ha, bind, Except.bind] at h
  | raises e =>
    by_cases ha : isA H e "AttributeError" = true
    · simp only [hc, deletedOk, ha, if_true, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      rw [← h]
    · simp [hc, deletedOk, ha, bind, Except.bind] at h
  | list xs =>
    cases ap
    · cases hr : pyRemove it xs with
      | ok r =>
        simp only [hc, hr, bind, Except.bind, pure, Except.pure, Bool.not_false, if_true,
          Except.ok.injEq] at h
        rw [← h]
      | error e =>
        by_cases hv : isA H e "ValueError" = true
        · simp only [hc, hr, hv, if_true, bind, Except.bind, pure, Except.pure, Bool.not_false,
            Except.ok.injEq] at h
          rw [← h]
        · simp [hc, hr, hv, bind, Except.bind] at h
    · cases hr : pyContains it xs with
      | error e => simp [hc, hr, bind, Except.bind] at h
      | ok b => cases b <;> simp only [hc, hr, bind, Except.bind, pure, Except.pure, Bool.not_true,
          Bool.false_eq_true, if_false, if_true, Except.ok.injEq] at h <;> rw [← h]
  | tuple xs =>
    cases ap
    · simp [hc, bind, Except.bind] at h
    · cases hr : pyContains it xs with
      | error e => simp [hc, hr, bind, Except.bind] at h
      | ok b => cases b <;> simp [hc, hr, bind, Except.bind, pure, Except.pure] at h <;> rw [← h]

/-! ## `filterwarnings` -/

/-- The item `filterwarnings` builds from valid arguments. -/
def fwItem (a m : String) (cat : Nat) (md : String) (ln : Int) : FItem :=
  ⟨a, if m.isEmpty then none else some ⟨m, true⟩, cat, if md.isEmpty then none else some ⟨md, false⟩, ln⟩

/-- The documented arguments (the docstring, :256-265): one of the seven actions, a message regex,
a Warning subclass, a module regex, an int line `>= 0`. -/
def FwValid (E : FEnv) (a : ActA) (m : StrA) (cat : Nat) (md : StrA) (ln : IntA) : Prop :=
  (∃ s, a = .str s ∧ s ∈ actionNames) ∧ (∃ s, m = .str s ∧ (s.isEmpty = false → E.compile s true = .ok ())) ∧
  E.isType cat = true ∧ E.isWarn cat = true ∧
  (∃ s, md = .str s ∧ (s.isEmpty = false → E.compile s false = .ok ())) ∧ (∃ v, ln = .int v ∧ 0 ≤ v)

theorem compileOpt_ok (E : FEnv) (p : String) (ci : Bool)
    (h : p.isEmpty = false → E.compile p ci = .ok ()) :
    compileOpt E p ci = .ok (if p.isEmpty then none else some ⟨p, ci⟩) := by
  unfold compileOpt
  cases hp : p.isEmpty
  · simp [h hp, bind, Except.bind, pure, Except.pure]
  · rfl

theorem compileOpt_okE (E : FEnv) (p : String) (ci : Bool) (r : Option Rx)
    (h : compileOpt E p ci = .ok r) : p.isEmpty = false → E.compile p ci = .ok () := by
  intro hp
  unfold compileOpt at h
  simp only [hp, Bool.false_eq_true, if_false, bind, Except.bind] at h
  cases hc : E.compile p ci with
  | error e => simp [hc] at h
  | ok u => rfl

theorem fwPrep_valid (E : FEnv) a m cat md ln (it : FItem) (h : fwPrep E a m cat md ln = .ok it) :
    FwValid E a m cat md ln := by
  unfold fwPrep at h
  cases a with
  | unhashable tp => simp [pure, Except.pure, bind, Except.bind, checkAction, bind, Except.bind] at h
  | obj r => simp [pure, Except.pure, bind, Except.bind, checkAction, bind, Except.bind] at h
  | str s =>
    by_cases hsa : s ∈ actionNames
    · simp only [pure, Except.pure, bind, Except.bind, checkAction, hsa, if_true, bind, Except.bind] at h
      cases m with
      | obj => simp [pure, Except.pure, bind, Except.bind] at h
      | str ms =>
        simp only [pure, Except.pure, bind, Except.bind] at h
        cases htw : (E.isType cat && E.isWarn cat)
        · simp [pure, Except.pure, bind, Except.bind, htw] at h
        · simp only [pure, Except.pure, bind, Except.bind, htw, Bool.not_true, Bool.false_eq_true, if_false] at h
          cases md with
          | obj => simp [pure, Except.pure, bind, Except.bind] at h
          | str mds =>
            simp only [pure, Except.pure, bind, Except.bind] at h
            cases ln with
            | obj => simp [pure, Except.pure, bind, Except.bind, checkLineno] at h
            | int l =>
              by_cases hl0 : l < 0
              · simp [pure, Except.pure, bind, Except.bind, checkLineno, hl0] at h
              · simp only [pure, Except.pure, bind, Except.bind, checkLineno, hl0, if_false] at h
                cases hc1 : compileOpt E ms true with
                | error e => simp [pure, Except.pure, bind, Except.bind, hc1] at h
                | ok r1 =>
                  simp only [pure, Except.pure, bind, Except.bind, hc1] at h
                  cases hc2 : compileOpt E mds false with
                  | error e => simp [pure, Except.pure, bind, Except.bind, hc2] at h
                  | ok r2 =>
                    simp only [Bool.and_eq_true] at htw
                    exact ⟨⟨s, rfl, hsa⟩, ⟨ms, rfl, compileOpt_okE E ms true r1 hc1⟩, htw.1, htw.2,
                      ⟨mds, rfl, compileOpt_okE E mds false r2 hc2⟩, ⟨l, rfl, by omega⟩⟩
    · simp [pure, Except.pure, bind, Except.bind, checkAction, hsa, bind, Except.bind] at h

theorem fwPrep_of_valid (E : FEnv) (s ms mds : String) cat (l : Int)
    (hv : FwValid E (.str s) (.str ms) cat (.str mds) (.int l)) :
    fwPrep E (.str s) (.str ms) cat (.str mds) (.int l) = .ok (fwItem s ms cat mds l) := by
  obtain ⟨⟨s', hs', hsa⟩, ⟨ms', hms', hc1⟩, ht, hw, ⟨mds', hmds', hc2⟩, ⟨l', hl', hl0⟩⟩ := hv
  cases hs'; cases hms'; cases hmds'; cases hl'
  have hcl : ¬ l < 0 := by omega
  simp [fwPrep, checkAction, hsa, checkLineno, hcl, compileOpt_ok E ms true hc1,
    compileOpt_ok E mds false hc2, ht, hw, bind, Except.bind, pure, Except.pure, fwItem]

/-- `filterwarnings` on a filters list whose elements' `==` against the new item does not raise:
it succeeds exactly for the documented arguments, and then the new item is first and the first
element equal to it is gone ("Remove possible duplicate filters, so new one will be placed in
correct place", :324-325), or with `append` it is last unless an equal element is present; the
version moves on by exactly one. -/
def FilterwarningsSpec : Prop :=
  ∀ (E : FEnv) a m cat md ln ap xs v,
    (∀ it, EqTotal it xs) →
    ((∃ s', filterwarnings E a m cat md ln ap ⟨.list xs, v⟩ = .ok s') ↔ FwValid E a m cat md ln) ∧
    (∀ s ms mds l, a = .str s → m = .str ms → md = .str mds → ln = .int l → FwValid E a m cat md ln →
      filterwarnings E a m cat md ln ap ⟨.list xs, v⟩ =
        .ok ⟨.list (addSpec (fwItem s ms cat mds l) ap xs), v + 1⟩)

theorem filterwarningsSpec_proven : FilterwarningsSpec := by
  intro E a m cat md ln ap xs v htot
  have hgood : ∀ s ms mds l, a = .str s → m = .str ms → md = .str mds → ln = .int l →
      FwValid E a m cat md ln →
      filterwarnings E a m cat md ln ap ⟨.list xs, v⟩ =
        .ok ⟨.list (addSpec (fwItem s ms cat mds l) ap xs), v + 1⟩ := by
    intro s ms mds l ha hm hmd hl hv
    subst ha hm hmd hl
    simp [filterwarnings, fwPrep_of_valid E s ms mds cat l hv, bind, Except.bind,
      addFilter_list _ _ ap xs v (htot _)]
  refine ⟨⟨?_, ?_⟩, hgood⟩
  · rintro ⟨s', hs'⟩
    unfold filterwarnings at hs'
    cases hp : fwPrep E a m cat md ln with
    | error e => simp [hp, bind, Except.bind] at hs'
    | ok it => exact fwPrep_valid E a m cat md ln it hp
  · intro hv
    have hv' := hv
    obtain ⟨⟨s, hs, _⟩, ⟨ms, hms, _⟩, _, _, ⟨mds, hmds, _⟩, ⟨l, hl, _⟩⟩ := hv'
    exact ⟨_, hgood s ms mds l hs hms hmds hl hv⟩

/-! ## `simplefilter` against `filterwarnings` -/

/-- The docstring of `simplefilter` (:295-302) and the documentation: "a simple entry ... The
meaning of the function parameters is as for filterwarnings()". So `simplefilter(a, c, l, ap)`
does what `filterwarnings(a, '', c, '', l, ap)` does, for every argument and state. -/
def SimpleIsFilter : Prop :=
  ∀ (E : FEnv) a cat ln ap s, simplefilter E.hier a cat ln ap s = filterwarnings E a (.str "") cat (.str "") ln ap s

/-- With a category that is a Warning subclass (the documented argument), they agree. -/
def SimpleIsFilterWarnCat : Prop :=
  ∀ (E : FEnv) a cat ln ap s, E.isType cat = true → E.isWarn cat = true →
    simplefilter E.hier a cat ln ap s = filterwarnings E a (.str "") cat (.str "") ln ap s

theorem simpleIsFilterWarnCat_proven : SimpleIsFilterWarnCat := by
  intro E a cat ln ap s ht hw
  have hp : sfPrep a cat ln = fwPrep E a (.str "") cat (.str "") ln := by
    unfold sfPrep fwPrep
    cases checkAction a with
    | error e => rfl
    | ok x =>
      simp only [bind, Except.bind, ht, hw, Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false]
      cases checkLineno ln with
      | error e => rfl
      | ok l => rfl
  simp [simplefilter, filterwarnings, hp]

/-- `simplefilter` checks no category: `simplefilter('ignore', 5)` installs `('ignore', None, 5,
None, 0)`, which `filterwarnings` refuses (python/cpython#125893), and every later warning that
reaches it fails in `issubclass` (C `PyObject_IsSubclass`, _warnings.c:512). -/
theorem simpleIsFilter_refuted : ¬ SimpleIsFilter := fun h =>
  refute (h ⟨fun _ _ => .ok (), fun _ => false, fun _ => false, builtinHier⟩ (.str "ignore") 12 (.int 0) false
    ⟨.list [], 1⟩)
    (x := .ok ⟨.list [.item ⟨"ignore", none, 12, none, 0⟩], 2⟩)
    (y := .error (.typeError "category must be a Warning subclass")) (by rfl) (by rfl)
    (by simp)

/-! ## `resetwarnings` and `_add_filter`'s `except ValueError` -/

/-- `resetwarnings()` "clear[s] the list of warning filters, so that no filters are active": on a
list it leaves the empty list (and the version moves on); a tuple refuses item deletion and is
left as it was; with `warnings.filters` deleted the fresh `[]` of `_GlobalContext._filters` is
emptied and nothing changes (for the plain `AttributeError`, in every relation CPython can have),
and a module `__getattr__` that raises an exception under `AttributeError` does the same, while
any other exception from it propagates (measured on 3.15.2 with `KeyError`). -/
def ResetSpec : Prop :=
  ∀ H : Hier,
  (∀ xs v, resetwarnings H ⟨.list xs, v⟩ = .ok ⟨.list [], v + 1⟩) ∧
  (∀ xs v, ∃ e, resetwarnings H ⟨.tuple xs, v⟩ = .error e ∧ e.className = "TypeError") ∧
  (HierOk H → ∀ v, resetwarnings H ⟨.deleted, v⟩ = .ok ⟨.deleted, v + 1⟩) ∧
  (∀ e v, isA H e "AttributeError" = true → resetwarnings H ⟨.raises e, v⟩ = .ok ⟨.raises e, v + 1⟩) ∧
  (∀ e v, isA H e "AttributeError" = false → resetwarnings H ⟨.raises e, v⟩ = .error e)

theorem noFilters_caught (H : Hier) (h : HierOk H) : isA H noFilters "AttributeError" = true :=
  (h "AttributeError" "AttributeError" (by decide)).trans (by decide)

theorem resetSpec_proven : ResetSpec := by
  intro H
  refine ⟨fun _ _ => rfl, fun _ _ => ⟨_, rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro hk v; simp [resetwarnings, deletedOk, noFilters_caught H hk, Except.map]
  · intro e v h; simp [resetwarnings, deletedOk, h, Except.map]
  · intro e v h; simp [resetwarnings, deletedOk, h, Except.map]

/-- `try: filters.remove(item) except ValueError: pass` (:326-329) also catches an exception of a
class `c` with `H.sub c "ValueError"` (`ValueError` in its MRO: every builtin subclass such as
`UnicodeError`, `io.UnsupportedOperation`, a user class whose MRO contains it) that an element's
`__eq__` raises: the remove stops there, the new item goes in front anyway, and the elements (the
raising one included) stay; any other exception propagates and changes nothing (also a class under
`UnicodeEncodeError` whose custom `mro()` leaves `ValueError` out). Stated for a list whose first
element raises, for every class relation `H`, with no hypothesis on it. -/
def AddFilterValueError : Prop :=
  ∀ (H : Hier) it id e xs v,
    (isA H e "ValueError" = true → addFilter H it false ⟨.list (.other id (.error e) :: xs), v⟩ =
      .ok ⟨.list (.item it :: .other id (.error e) :: xs), v + 1⟩) ∧
    (isA H e "ValueError" = false → addFilter H it false ⟨.list (.other id (.error e) :: xs), v⟩ = .error e)

theorem addFilterValueError_proven : AddFilterValueError := by
  intro H it id e xs v
  constructor
  · intro h; simp [addFilter, pyRemove, elemEq, bind, Except.bind, pure, Except.pure, h]
  · intro h; simp [addFilter, pyRemove, elemEq, bind, Except.bind, pure, Except.pure, h]

/-! ## The version -/

/-- Every successful mutation of the filters through the API moves the version on by exactly one,
so that `already_warned` (_warnings.c:616-632) and `warn_explicit` (_py_warnings.py:570-572)
clear every registry made before it: `filterwarnings`, `simplefilter`, `resetwarnings` on any
container, `_filters_mutated` from a thread that can take the lock, and C
`_filters_mutated_lock_held` whenever it succeeds. -/
def VersionBumps : Prop :=
  (∀ E a m cat md ln ap s s', filterwarnings E a m cat md ln ap s = .ok s' → s'.ver = s.ver + 1) ∧
  (∀ H a cat ln ap s s', simplefilter H a cat ln ap s = .ok s' → s'.ver = s.ver + 1) ∧
  (∀ H s s', resetwarnings H s = .ok s' → s'.ver = s.ver + 1) ∧
  (∀ t l v, (l.owner = none → l.level = 0) → (l.owner = none ∨ l.owner = some t) →
    cFiltersMutated t l v = some (.ok (l, v + 1))) ∧
  (∀ l v v', cMutatedLockHeld l v = .ok v' → v' = v + 1)

theorem versionBumps_proven : VersionBumps := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro E a m cat md ln ap s s' h
    unfold filterwarnings at h
    cases hp : fwPrep E a m cat md ln with
    | error e => simp [hp, bind, Except.bind] at h
    | ok it => simp only [hp, bind, Except.bind] at h; exact addFilter_ver _ _ _ _ _ h
  · intro H a cat ln ap s s' h
    unfold simplefilter at h
    cases hp : sfPrep a cat ln with
    | error e => simp [hp, bind, Except.bind] at h
    | ok it => simp only [hp, bind, Except.bind] at h; exact addFilter_ver _ _ _ _ _ h
  · intro H s s' h
    unfold resetwarnings at h
    split at h
    · simp at h; rw [← h]
    · unfold deletedOk at h; split at h <;> simp [Except.map] at h; rw [← h]
    · unfold deletedOk at h; split at h <;> simp [Except.map] at h; rw [← h]
    · simp at h
  · intro t l v hinv hl
    obtain ⟨o, lv⟩ := l
    simp only at hl hinv
    rcases hl with rfl | rfl
    · have := hinv rfl
      subst this
      simp [cFiltersMutated, cAcquire, cMutatedLockHeld, cRelease, bind, Except.bind, pure, Except.pure]
    · simp [cFiltersMutated, cAcquire, cMutatedLockHeld, cRelease, bind, Except.bind, pure, Except.pure]
  · intro l v v' h
    unfold cMutatedLockHeld at h
    split at h <;> simp at h
    omega

/-! ## The lock -/

/-- The C lock (a recursive mutex, Python/lock.c:402-454), for every thread `t` and state: `t` can
take it exactly when no other thread holds it, and releasing right after gives the state back
(up to the owner of a free lock); `_release_lock` from `t` is refused exactly when `t` does not
hold it (another thread holding it is not enough); and C `_filters_mutated_lock_held` refuses
exactly when no thread holds the lock (`PyMutex_IsLocked`). -/
def LockSpec : Prop :=
  (∀ t l, (cAcquire t l).isSome ↔ (l.owner = none ∨ l.owner = some t)) ∧
  (∀ t l l', cAcquire t l = some l' → cRelease t l' = .ok (if l.owner = none then ⟨none, 0⟩ else l)) ∧
  (∀ t l, (∃ e, cRelease t l = .error e) ↔ l.owner ≠ some t) ∧
  (∀ l v, (∃ e, cMutatedLockHeld l v = .error e) ↔ l.owner = none)

theorem lockSpec_proven : LockSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t l
    obtain ⟨o, lv⟩ := l
    cases o with
    | none => simp [cAcquire]
    | some u =>
      by_cases h : u = t
      · simp [cAcquire, h]
      · simp only [cAcquire, h, if_false, Option.isSome_none, Bool.false_eq_true, false_iff]
        simp only [reduceCtorEq, Option.some.injEq, false_or]
        exact h
  · intro t l l' h
    obtain ⟨o, lv⟩ := l
    cases o with
    | none => simp [cAcquire] at h; subst h; simp [cRelease]
    | some u =>
      by_cases hu : u = t
      · subst hu; simp [cAcquire] at h; subst h; simp [cRelease]
      · simp [cAcquire, hu] at h
  · intro t l
    unfold cRelease
    by_cases h : l.owner = some t
    · simp only [h, if_true, ne_eq, not_true_eq_false, iff_false]
      split <;> simp
    · simp [h]
  · intro l v; unfold cMutatedLockHeld; split <;> simp_all

/-- Under C's precondition ("the lock must be held by the caller", _warnings.c:1368), the twins of
`_filters_mutated_lock_held` agree: both move the version on by one. -/
def MutatedLockHeldTwins : Prop :=
  ∀ l v, l.owner ≠ none → cMutatedLockHeld l v = .ok (pyMutatedLockHeld v)

theorem mutatedLockHeldTwins_proven : MutatedLockHeldTwins := by
  intro l v h
  simp [cMutatedLockHeld, pyMutatedLockHeld, Option.isNone_iff_eq_none, h]

/-! ## The initial filters -/

/-- A compiled pattern as a filter pattern: its `match` is `R`, C code (`re.Pattern.match`). -/
def rxPat (R : Rx → String → Py Bool) (r : Rx) : Pat := .regex (R r) true (.typeError "~expected string")

def elemItem (R : Rx → String → Py Bool) : Elem → Item
  | .item f => .tuple ⟨.str f.action, f.msg.map (rxPat R), f.cat, f.mod.map (rxPat R), .int f.ln⟩
  | .other _ _ => .other (.typeError "~cannot unpack")

/-- The filters `_setup_defaults` leaves on an empty list, as items. -/
def pyDefaults (E : FEnv) (R : Rx → String → Py Bool) (K : DefaultCats) : List Item :=
  match setupDefaults E false K ⟨.list [], 0⟩ with
  | .ok ⟨.list xs, _⟩ => xs.map (elemItem R)
  | _ => []

/-- The action a filters list picks for a call: the matching filter's (`none` when none does). -/
def pickC (E : Env) (c : Call) (ln : Int) (fs : List Item) (m : String) : Py (Option AV) :=
  (cFind E false c ln (.str m) "filters" 0 fs).map (fun f => f.map (·.action))

def pickPy (E : Env) (c : Call) (ln : Int) (fs : List Item) : Py (Option AV) :=
  (pyFind E c ln fs).map (fun f => f.map (·.action))

/-- The environment of the defaults: the four categories are Warning classes, `__main__` compiles,
and its pattern matches what starts with `__main__` (`re.match` of a literal). -/
def DefaultsEnv (E : FEnv) (R : Rx → String → Py Bool) (K : DefaultCats) : Prop :=
  E.isType K.deprecation = true ∧ E.isWarn K.deprecation = true ∧ E.isType K.pending = true ∧
  E.isWarn K.pending = true ∧ E.isType K.importW = true ∧ E.isWarn K.importW = true ∧
  E.isType K.resource = true ∧ E.isWarn K.resource = true ∧
  E.compile "__main__" false = .ok () ∧
  (∀ s, R ⟨"__main__", false⟩ s = .ok (s.toList.take 8 == "__main__".toList)) ∧
  K.deprecation ≠ K.pending ∧ K.deprecation ≠ K.importW ∧ K.deprecation ≠ K.resource ∧
  K.pending ≠ K.importW ∧ K.pending ≠ K.resource ∧ K.importW ≠ K.resource

/-- Without `_warnings`, `_setup_defaults` (_py_warnings.py:920-928) stands in for C's
`init_filters` (_warnings.c:101-132): for every module name both lists pick the same filter
action for every warning. Refuted: C's `'__main__'` filter is a plain str that must equal the
module name (`check_matched`, :186-195); Python's is `re.compile('__main__')`, which matches every
module name that starts with `__main__`. -/
def DefaultsTwin : Prop :=
  ∀ (FE : FEnv) R K (E : Env) (c : Call) ln (m : String), DefaultsEnv FE R K → EnvOk E →
    c.module = .some m → pickC E c ln (initFilters false K) m = pickPy E c ln (pyDefaults FE R K)

/-- For module names that are `__main__` or do not start with it, they agree. -/
def DefaultsTwinNarrow : Prop :=
  ∀ (FE : FEnv) R K (E : Env) (c : Call) ln (m : String), DefaultsEnv FE R K → EnvOk E →
    c.module = .some m → (m.toList.take 8 == "__main__".toList) = (m == "__main__") →
    pickC E c ln (initFilters false K) m = pickPy E c ln (pyDefaults FE R K)

theorem pyDefaults_eq (FE : FEnv) (R : Rx → String → Py Bool) (K : DefaultCats) (h : DefaultsEnv FE R K) :
    pyDefaults FE R K =
      [.tuple ⟨.str "default", none, K.deprecation, some (rxPat R ⟨"__main__", false⟩), .int 0⟩,
       .tuple ⟨.str "ignore", none, K.deprecation, none, .int 0⟩,
       .tuple ⟨.str "ignore", none, K.pending, none, .int 0⟩,
       .tuple ⟨.str "ignore", none, K.importW, none, .int 0⟩,
       .tuple ⟨.str "ignore", none, K.resource, none, .int 0⟩] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hc, _, d1, d2, d3, d4, d5, d6⟩ := h
  have hne : ("__main__" : String).isEmpty = false := by decide
  have he : ("" : String).isEmpty = true := by decide
  simp [pyDefaults, setupDefaults, filterwarnings, simplefilter, fwPrep, sfPrep, checkAction,
    checkLineno, actionNames, compileOpt, hc, h1, h2, h3, h4, h5, h6, h7, h8, addFilter, pyContains,
    elemEq, bind, Except.bind, pure, Except.pure, elemItem, rxPat, hne, he, d1, d2, d3, d4, d5, d6,
    Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6]

theorem defaultsTwinNarrow_proven : DefaultsTwinNarrow := by
  intro FE R K E c ln m h he hm hmain
  rw [pyDefaults_eq FE R K h]
  obtain ⟨_, _, _, _, _, _, _, _, _, hR, _⟩ := h
  obtain ⟨hs, _⟩ := he
  obtain ⟨b0, hb0⟩ := hs c.cat K.deprecation
  obtain ⟨b1, hb1⟩ := hs c.cat K.pending
  obtain ⟨b2, hb2⟩ := hs c.cat K.importW
  obtain ⟨b3, hb3⟩ := hs c.cat K.resource
  have hfit : ¬ ((0 : Int) > ssizeMax ∨ (0 : Int) < -ssizeMax - 1) := by simp [ssizeMax]
  unfold pickC pickPy
  simp only [initFilters, Bool.false_eq_true, if_false, createFilter, Option.map_some, Option.map_none,
    cFind, cFilterMatches, pyFind, pyFilterMatches, checkMatched, pyMsgOk, pyModOk, hm, pyMatch,
    cIsSub, hb0, hb1, hb2, hb3, asSsize, hfit, rxPat, hR, hmain, if_false, pyLnOk,
    bind, Except.bind, pure, Except.pure, Bool.false_and, Bool.not_false, Except.map, callPat]
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases hmm : (m == "__main__") <;> simp [hmm]

def defFE : FEnv := ⟨fun _ _ => .ok (), fun _ => true, fun _ => true, builtinHier⟩
def defR : Rx → String → Py Bool := fun _ s => .ok (s.toList.take 8 == "__main__".toList)
def defK : DefaultCats := ⟨3, 6, 7, 8⟩
def defE : Env := ⟨fun a b => .ok (decide (a = b)), fun _ _ => false, fun _ _ => .ok false, .call (.ok ()) (.ok ()),
  builtinHier, .ok ()⟩
def defCall : Call := ⟨"x", 3, "a.py", .int 1, .some "__main__x", .ok (), .none, .ok (), false, .own⟩

theorem defEnv : DefaultsEnv defFE defR defK :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-- A `DeprecationWarning` from module `__main__x`: C ignores it, Python shows it once. -/
theorem defaultsTwin_refuted : ¬ DefaultsTwin := fun h =>
  refute (h defFE defR defK defE defCall 1 "__main__x" defEnv
    ⟨fun _ _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩, ⟨_, _, rfl⟩, rfl⟩ rfl)
    (x := .ok (some (.str "ignore"))) (y := .ok (some (.str "default"))) (by rfl)
    (by rw [pyDefaults_eq defFE defR defK defEnv]; rfl) (by simp)

end PyLean.CoreLibs.Warn
