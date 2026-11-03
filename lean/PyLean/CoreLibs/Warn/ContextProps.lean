import PyLean.CoreLibs.Warn.Context
import PyLean.CoreLibs.Warn.FiltersProps

/-!
Properties of `catch_warnings` and the contexts (`Context.lean`).
-/

namespace PyLean.CoreLibs.Warn

open PyLean

/-- Every reference the state holds is below `next` (fresh references are new). -/
def Fresh (st : MState) : Prop :=
  (∀ r, st.filters = some r → r < st.next) ∧
  (∀ c, st.ctxv = .ctx c → c < st.next ∧ (st.ctxs c).filters < st.next)

/-- Replace the contents of the list `_get_filters()` designates (what `filterwarnings`,
`simplefilter` and `resetwarnings` do inside the block). -/
def editFilters (useCtx : Bool) (f : List Elem → List Elem) (st : MState) : MState :=
  match ctxFilters st (getContext useCtx st) with
  | some r => { st with lists := upd st.lists r (f (st.lists r)) }
  | none => st

/-- `catch_warnings` "copies and, upon exit, restores the warnings filter and the showwarning()
function" (Doc/library/warnings.rst), in both context modes: for a `catch_warnings` that was not
entered, whose `action` (if any) `simplefilter` accepts, in a state whose references are fresh and
(without contexts) whose `warnings.filters` exists, `__enter__` succeeds; whatever the block does
to the filters it sees, `__exit__` succeeds and `_get_filters()` is what it was before, and
`showwarning` (and without contexts `_showwarnmsg_impl`) are back. A second `__enter__` of the
same object raises `RuntimeError` and changes nothing. -/
def CatchRestores : Prop :=
  ∀ (useCtx : Bool) (cw : CW) (st : MState) (f : List Elem → List Elem) sw,
    cw.entered = false → Fresh st → st.showwarning = some sw →
    (useCtx = false → st.filters ≠ none) →
    (∀ a c ln ap, cw.filter = some (a, c, ln, ap) → ∃ it, sfPrep a c ln = .ok it) →
    ∃ cw' st1 log, cwEnter useCtx cw st = (cw', st1, .ok log) ∧
      (cwEnter useCtx cw' st1).2.2 = .error (.named "RuntimeError" s!"Cannot enter {cwRepr cw'} twice") ∧
      (cwEnter useCtx cw' st1).2.1 = st1 ∧
      let st2 := editFilters useCtx f st1
      ∃ st3, cwExit useCtx cw' st2 = (st3, .ok ()) ∧
        getFilters useCtx st3 = getFilters useCtx st ∧ st3.showwarning = some sw ∧
        (useCtx = false → st3.showImpl = st.showImpl ∧ st3.filters = st.filters) ∧
        st3.ver = st2.ver + 1

theorem upd_ne {α : Type} (f : Nat → α) (k i : Nat) (v : α) (h : i ≠ k) : upd f k v i = f i := by
  simp [upd, h]

theorem upd_eq {α : Type} (f : Nat → α) (k : Nat) (v : α) : upd f k v k = v := by
  simp [upd]


/-- `__enter__` that raises leaves the module as it was (a `with` statement does not call
`__exit__` then). Refuted: the `simplefilter` call for `action` comes last (:723-724), after the
filters were copied and, with `record=True`, `_showwarnmsg_impl` replaced. -/
def EnterAtomic : Prop :=
  ∀ (useCtx : Bool) (cw : CW) (st : MState) e, (cwEnter useCtx cw st).2.2 = .error e →
    (cwEnter useCtx cw st).2.1.showImpl = st.showImpl ∧
    (cwEnter useCtx cw st).2.1.filters = st.filters ∧
    (cwEnter useCtx cw st).2.1.ctxv = st.ctxv

def st0 : MState :=
  MState.mk (fun _ => []) (fun _ => []) 1 (some 0) (some .showOrig) .implOrig (some .fmtOrig) 0 .unset
    (fun _ => ⟨0, none⟩) (some (.ok ())) []

def cwBogus : CW := cwInit "catch_warnings" true none (some (.str "bogus")) 0 (.int 0) false

theorem enterAtomic_refuted : ¬ EnterAtomic := fun h =>
  refute (h false cwBogus st0 (.valueError "invalid action: 'bogus'") (by rfl)).1
    (x := .logAppend 2) (y := .implOrig) (by rfl) rfl (by simp)

/-- After that failed `__enter__`, a warning shown through `_showwarnmsg` goes to the record list
nobody holds instead of `sys.stderr`. -/
theorem failedEnter_swallows :
    (showwarnmsg false 7 (cwEnter false cwBogus st0).2.1).map (·.out) = .ok [.logged 2] := by
  rfl

/-- A `catch_warnings(record=True)` block records every warning shown through `_showwarnmsg` in
the list `__enter__` returned and writes none (the documentation: "warnings are recorded ... and
appended to a list"), in both modes; with contexts, when `_showwarnmsg_impl` is the module's own. -/
def RecordCaptures : Prop :=
  ∀ (useCtx : Bool) (cw : CW) (st : MState) cw' st1 l (m : Nat),
    cw.record = true → (useCtx = true → st.showImpl = .implOrig) →
    cwEnter useCtx cw st = (cw', st1, .ok (some l)) → cw.filter = none →
    ∃ st2, showwarnmsg useCtx m st1 = .ok st2 ∧ st2.logs l = st1.logs l ++ [m] ∧
      st2.out = st1.out ++ [.logged l]

theorem recordCaptures_proven : RecordCaptures := by
  intro useCtx cw st cw' st1 l m hrec himpl hen hnf
  unfold cwEnter at hen
  split at hen
  · simp at hen
  · cases useCtx
    · cases hf : st.filters with
      | none => simp [hf] at hen
      | some r =>
        cases hsw : st.showwarning with
        | none => simp [hf, hsw] at hen
        | some sw =>
          simp only [hf, hsw, hrec, hnf, if_true, Bool.false_eq_true, if_false] at hen
          simp only [Prod.mk.injEq] at hen
          obtain ⟨_, hst, hl⟩ := hen
          simp only [Except.ok.injEq, Option.some.injEq] at hl
          subst hst hl
          simp [showwarnmsg, callImpl, upd]
    · cases hsw : st.showwarning with
      | none => simp [hsw, newContext] at hen
      | some sw =>
        simp only [newContext, hsw, hrec, hnf, if_true] at hen
        simp only [Prod.mk.injEq] at hen
        obtain ⟨_, hst, hl⟩ := hen
        simp only [Except.ok.injEq, Option.some.injEq] at hl
        subst hst hl
        have hi := himpl rfl
        simp [showwarnmsg, callImpl, hi, showImplOrig, getContext, ctxLog, upd]


/-! ## The list C searches against `_get_filters()` -/

/-- C `get_filter` and Python `warn_explicit` search the same list: C's (the context's
`_filters`, else `warnings.filters`) is `_get_filters()`, in context mode, or without contexts
while no context is set; provided `warnings.filters` exists. -/
def FilterListTwins : Prop :=
  ∀ (useCtx : Bool) (st : MState) cached, (useCtx = true ∨ st.ctxv = .unset) → st.filters ≠ none →
    (cFilterList st cached).1 = getFilters useCtx st

theorem filterListTwins_proven : FilterListTwins := by
  intro useCtx st cached hu hf
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hf
  unfold cFilterList getFilters getContext ctxFilters
  cases useCtx <;> cases hc : st.ctxv <;> simp_all

/-- Without the condition on `warnings.filters`: refuted, when it was deleted C searches the list
it read last (`get_warnings_filters` keeps `st->filters`, :346-353) and Python the empty list of
`_GlobalContext._filters` (:76-80). -/
def FilterListTwinsAny : Prop :=
  ∀ (useCtx : Bool) (st : MState) cached, (useCtx = true ∨ st.ctxv = .unset) →
    (cFilterList st cached).1 = getFilters useCtx st

theorem filterListTwinsAny_refuted : ¬ FilterListTwinsAny := fun h => by
  have e := congrArg List.length
    (h false { st0 with filters := none, lists := fun _ => [.other 0 (.ok false)] } 0 (Or.inr rfl))
  simp [cFilterList, getFilters, getContext, ctxFilters, st0] at e

end PyLean.CoreLibs.Warn
