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
function" (Doc/library/warnings.rst), in both context modes: for every `catch_warnings(...)` whose
`action` (if any) `simplefilter` accepts, in a state whose references are fresh and (without
contexts) whose `warnings.filters` exists, `__enter__` succeeds and (with no action) the block sees
a copy of the filters, a new list with the same contents; a second `__enter__` of the same object
raises `RuntimeError` and changes nothing; whatever the block does to the filters it sees,
`__exit__` succeeds, `_get_filters()` is what it was before, and `showwarning` (and without
contexts `warnings.filters` and `_showwarnmsg_impl`) are back. -/
def CatchRestores : Prop :=
  ∀ (useCtx : Bool) (name : String) (record : Bool) (om : Nat) (action : Option ActA)
    (cat : Nat) (ln : IntA) (ap : Bool) (st : MState) (f : List Elem → List Elem) (sw : Fn),
    Fresh st → st.showwarning = some sw → (useCtx = false → st.filters ≠ none) →
    (∀ a, action = some a → ∃ it, sfPrep a cat ln = .ok it) →
    (∀ it, EqTotal it (getFilters useCtx st)) →
    ∃ cw' st1 log, cwEnter useCtx (cwInit name record om action cat ln ap) st = (cw', st1, .ok log) ∧
      (action = none → getFilters useCtx st1 = getFilters useCtx st ∧
        ctxFilters st1 (getContext useCtx st1) ≠ ctxFilters st (getContext useCtx st)) ∧
      cwEnter useCtx cw' st1 = (cw', st1, match cwRepr cw' st.sysWarnings st.modRepr with
        | .ok r => .error (.named "RuntimeError" s!"Cannot enter {r} twice")
        | .error e => .error e) ∧
      ∃ st3, cwExit useCtx cw' (editFilters useCtx f st1) = (st3, .ok ()) ∧
        getFilters useCtx st3 = getFilters useCtx st ∧ st3.showwarning = some sw ∧
        (useCtx = false → st3.showImpl = st.showImpl ∧ st3.filters = st.filters) ∧
        st3.ver = (editFilters useCtx f st1).ver + 1

theorem upd_ne {α : Type} (f : Nat → α) (k i : Nat) (v : α) (h : i ≠ k) : upd f k v i = f i := by
  simp [upd, h]

theorem upd_eq {α : Type} (f : Nat → α) (k : Nat) (v : α) : upd f k v k = v := by
  simp [upd]

set_option maxHeartbeats 2000000 in
theorem catchRestores_proven : CatchRestores := by
  intro useCtx name record om action cat ln ap st f sw hfr hsw hfl hact htot
  obtain ⟨lists, logs, next, filters, showwarning, showImpl, formatwarning, ver, ctxv, ctxs, stderr,
    out, tuples, hier, sysW, modR⟩ := st
  obtain ⟨hf1, hf2⟩ := hfr
  simp only at hsw hf1 hf2 hfl htot
  subst hsw
  cases useCtx
  · obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (hfl rfl)
    subst hr
    have hrn : r < next := hf1 r rfl
    have hne : r ≠ next := Nat.ne_of_lt hrn
    have hgf : getFilters false ⟨lists, logs, next, some r, some sw, showImpl, formatwarning, ver, ctxv,
        ctxs, stderr, out, tuples, hier, sysW, modR⟩ = lists r := rfl
    rw [hgf] at htot ⊢
    cases action with
    | none =>
      cases record <;>
      refine ⟨_, _, _, rfl, fun _ => ⟨?_, ?_⟩, rfl, _, rfl, ?_, rfl, fun _ => ⟨rfl, rfl⟩, rfl⟩ <;>
      simp [getFilters, getContext, ctxFilters, editFilters, upd, hne, Ne.symm hne]
    | some a =>
      obtain ⟨it, hit⟩ := hact a rfl
      have hsf : ∀ (st' : MState), st'.lists next = lists r → st'.filters = some next →
          simplefilter hier a cat ln ap (curFState false st') =
            .ok ⟨.list (addSpec it ap (lists r)), st'.ver + 1⟩ := by
        intro st' hl hfs
        simp [simplefilter, hit, curFState, getContext, ctxFilters, hfs, hl, bind, Except.bind,
          addFilter_list _ it ap (lists r) st'.ver (htot it)]
      cases record
      · have hE := (show cwEnter false (cwInit name false om (some a) cat ln ap) ⟨lists, logs, next, some r, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ = _ from by
          simp only [cwEnter, cwInit, Option.map_some, Bool.false_eq_true, if_false]
          rw [hsf _ (by simp [upd]) rfl])
        rw [hE]
        refine ⟨_, _, _, rfl, fun h => by simp at h, rfl, _, rfl, ?_, rfl, fun _ => ⟨rfl, rfl⟩, rfl⟩
        simp [getFilters, getContext, ctxFilters, editFilters, putFState, upd, hne]
      · have hE := (show cwEnter false (cwInit name true om (some a) cat ln ap) ⟨lists, logs, next, some r, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ = _ from by
          simp only [cwEnter, cwInit, Option.map_some, if_true, Bool.false_eq_true, if_false]
          rw [hsf _ (by simp [upd]) rfl])
        rw [hE]
        refine ⟨_, _, _, rfl, fun h => by simp at h, rfl, _, rfl, ?_, rfl, fun _ => ⟨rfl, rfl⟩, rfl⟩
        simp [getFilters, getContext, ctxFilters, editFilters, putFState, upd, hne]
  · -- with contexts: the old context's filters, and the facts the exit needs about them
    have hold : ∀ r, ctxFilters ⟨lists, logs, next, filters, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ (getContext true ⟨lists, logs, next, filters, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩) = some r → r < next := by
      intro r hr
      cases ctxv with
      | ctx c0 =>
        simp only [ctxFilters, getContext] at hr
        rw [← Option.some.inj hr]; exact (hf2 c0 rfl).2
      | _ => simp only [ctxFilters, getContext] at hr; exact hf1 r hr
    have hctx : ∀ c0, getContext true ⟨lists, logs, next, filters, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ = .ctx c0 → c0 < next := by
      intro c0 h
      cases ctxv with
      | ctx c1 => simp only [getContext] at h; injection h with h; subst h; exact (hf2 c1 rfl).1
      | _ => simp [getContext] at h
    generalize hO : getContext true ⟨lists, logs, next, filters, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ = old at hold hctx
    have hnu : old ≠ .unset := by rw [← hO]; cases ctxv <;> simp [getContext]
    have hgf : getFilters true ⟨lists, logs, next, filters, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ = (match ctxFilters ⟨lists, logs, next, filters, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ old with | some r => lists r | none => []) := by
      simp only [getFilters, hO]; rfl
    rw [hgf] at htot ⊢
    -- the old context as seen after the exit, whatever happened in between below `next`
    have hback : ∀ (st3 : MState), st3.ctxv = old → st3.filters = filters →
        (∀ i, i < next → st3.lists i = lists i) → (∀ c, c < next → st3.ctxs c = ctxs c) →
        getFilters true st3 = (match ctxFilters ⟨lists, logs, next, filters, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ old with | some r => lists r | none => []) := by
      intro st3 hv hfs hl hc
      have hg3 : getContext true st3 = old := by
        simp only [getContext, hv]; cases old <;> simp_all
      simp only [getFilters, hg3]
      cases old with
      | unset => exact absurd rfl hnu
      | global =>
        simp only [ctxFilters, hfs]
        cases hfr : filters with
        | none => rfl
        | some r => simp only; exact hl r (hold r (by simp [ctxFilters, hfr]))
      | ctx c0 =>
        have hc0 := hctx c0 rfl
        simp only [ctxFilters, hc c0 hc0]
        exact hl _ (hold _ (by simp [ctxFilters]))
    have hsf : ∀ a it (st' : MState), sfPrep a cat ln = .ok it →
        ctxFilters st' (getContext true st') = some next → st'.lists next = (match ctxFilters ⟨lists, logs, next, filters, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ old with | some r => lists r | none => []) →
        simplefilter hier a cat ln ap (curFState true st') =
          .ok ⟨.list (addSpec it ap (match ctxFilters ⟨lists, logs, next, filters, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ old with | some r => lists r | none => [])), st'.ver + 1⟩ := by
      intro a it st' hit hc hl
      simp [simplefilter, hit, curFState, hc, hl, bind, Except.bind, addFilter_list _ it ap _ st'.ver (htot it)]
    cases action with
    | none =>
      cases record
      · refine ⟨_, _, _, rfl, fun _ => ⟨?_, ?_⟩, rfl, _, rfl, ?_, rfl, fun h => by simp at h, rfl⟩
        · simp [getFilters, getContext, ctxFilters, newContext, upd, cwInit]
          rw [← hO]; rfl
        · rw [hO]
          generalize hR : ctxFilters ⟨lists, logs, next, filters, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ old = R
          cases R with
          | none => simp [getContext, ctxFilters, newContext, upd, cwInit]
          | some r =>
            have hr := hold r hR
            simp [getContext, ctxFilters, newContext, upd, cwInit]
            exact fun h => Nat.lt_irrefl _ (h ▸ hr)
        · apply hback
          · exact hO
          · rfl
          · intro i hi
            have h1 : i ≠ next := by omega
            have h2 : i ≠ next + 2 := by omega
            simp [cwExit, editFilters, getContext, ctxFilters, newContext, upd, cwInit, h1, h2]
          · intro c hc
            have h1 : c ≠ next + 1 := by omega
            simp [cwExit, editFilters, getContext, ctxFilters, newContext, upd, cwInit, h1]
      · refine ⟨_, _, _, rfl, fun _ => ⟨?_, ?_⟩, rfl, _, rfl, ?_, rfl, fun h => by simp at h, rfl⟩
        · simp [getFilters, getContext, ctxFilters, newContext, upd, cwInit]
          rw [← hO]; rfl
        · rw [hO]
          generalize hR : ctxFilters ⟨lists, logs, next, filters, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ old = R
          cases R with
          | none => simp [getContext, ctxFilters, newContext, upd, cwInit]
          | some r =>
            have hr := hold r hR
            simp [getContext, ctxFilters, newContext, upd, cwInit]
            exact fun h => Nat.lt_irrefl _ (h ▸ hr)
        · apply hback
          · exact hO
          · rfl
          · intro i hi
            have h1 : i ≠ next := by omega
            have h2 : i ≠ next + 2 := by omega
            simp [cwExit, editFilters, getContext, ctxFilters, newContext, upd, cwInit, h1, h2]
          · intro c hc
            have h1 : c ≠ next + 1 := by omega
            simp [cwExit, editFilters, getContext, ctxFilters, newContext, upd, cwInit, h1]
    | some a =>
      obtain ⟨it, hit⟩ := hact a rfl
      cases record
      · have hE := (show cwEnter true (cwInit name false om (some a) cat ln ap) ⟨lists, logs, next, filters, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ = _ from by
          simp only [cwEnter, cwInit, Option.map_some, if_true, Bool.false_eq_true, if_false, newContext]
          rewrite [hsf a it _ hit (by simp [getContext, ctxFilters, newContext, upd])
            (by simp only [newContext, upd, if_true]; rw [hO]; try rfl)]
          simp only [putFState, getContext, ctxFilters, upd, if_true]
          try rfl)
        rw [hE]
        refine ⟨_, _, _, rfl, fun h => by simp at h, rfl, _, rfl, ?_, rfl, fun h => by simp at h, rfl⟩
        apply hback
        · rw [← hO]; rfl
        · rfl
        · intro i hi
          have h1 : i ≠ next := by omega
          have h2 : i ≠ next + 2 := by omega
          simp [cwExit, editFilters, putFState, getContext, ctxFilters, newContext, upd, h1, h2]
        · intro c hc
          have h1 : c ≠ next + 1 := by omega
          simp [cwExit, editFilters, putFState, getContext, ctxFilters, newContext, upd, h1]
      · have hE := (show cwEnter true (cwInit name true om (some a) cat ln ap) ⟨lists, logs, next, filters, some sw, showImpl, formatwarning, ver, ctxv, ctxs, stderr, out, tuples, hier, sysW, modR⟩ = _ from by
          simp only [cwEnter, cwInit, Option.map_some, if_true, Bool.false_eq_true, if_false, newContext]
          rewrite [hsf a it _ hit (by simp [getContext, ctxFilters, newContext, upd])
            (by simp only [newContext, upd, if_true]; rw [hO]; try rfl)]
          simp only [putFState, getContext, ctxFilters, upd, if_true]
          try rfl)
        rw [hE]
        refine ⟨_, _, _, rfl, fun h => by simp at h, rfl, _, rfl, ?_, rfl, fun h => by simp at h, rfl⟩
        apply hback
        · rw [← hO]; rfl
        · rfl
        · intro i hi
          have h1 : i ≠ next := by omega
          have h2 : i ≠ next + 2 := by omega
          simp [cwExit, editFilters, putFState, getContext, ctxFilters, newContext, upd, h1, h2]
        · intro c hc
          have h1 : c ≠ next + 1 := by omega
          simp [cwExit, editFilters, putFState, getContext, ctxFilters, newContext, upd, h1]


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
    (fun _ => ⟨0, none⟩) (some (.ok ())) [] (fun _ => false) builtinHier (some 0) ⟨fun _ => "<W>", fun _ => none⟩

def cwBogus : CW := cwInit "catch_warnings" true 0 (some (.str "bogus")) 0 (.int 0) false

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
  · simp only [Prod.mk.injEq] at hen
    obtain ⟨_, _, h3⟩ := hen
    split at h3 <;> simp at h3
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


/-! ## Showing a warning -/

/-- `_showwarnmsg` (:217-233) and `_showwarnmsg_impl` (:133-150): a replaced `showwarning` is
called instead of the implementation, and an exception it raises propagates (:230-231); a
non-callable one raises `TypeError`; a deleted one is looked up through the module's `__getattr__`
under `except AttributeError` (:219-222): an exception whose class is not under `AttributeError`
propagates, one that is (the plain `AttributeError` of a module with no `__getattr__` among them,
`plainDeleted_caught`) goes on like the original `showwarning` to `_showwarnmsg_impl`. That formats
the text outside record mode (a replaced `formatwarning` that raises propagates, :145; a deleted
one goes through `_formatwarnmsg`'s own `except AttributeError`, :242-245, the same way) and
writes it to `sys.stderr`: lost when `sys.stderr` is `None` or the
write raises an exception of a class `c` with `st.hier.sub c "OSError"`, that is with `OSError` in
its MRO (`except OSError`, :146-150; so `BrokenPipeError`, `io.UnsupportedOperation`, a user class
whose MRO contains `OSError`), written when it succeeds, and any other exception from the write
propagates (a class whose custom `mro()` leaves `OSError` out included). -/
def ShowDispatch : Prop :=
  ∀ (useCtx : Bool) (m : Nat) (st : MState),
    (∀ i, st.showwarning = some (.user i) → showwarnmsg useCtx m st = .ok { st with out := st.out ++ [.hook i] }) ∧
    (∀ i e, st.showwarning = some (.userRaises i e) → showwarnmsg useCtx m st = .error e) ∧
    (st.showwarning = some .noncallable → ∃ e, showwarnmsg useCtx m st = .error e ∧ e.className = "TypeError") ∧
    (st.showwarning = none → isA st.hier (modAttrErr st "showwarning") "AttributeError" = false →
      showwarnmsg useCtx m st = .error (modAttrErr st "showwarning")) ∧
    ((st.showwarning = some .showOrig ∨
        (st.showwarning = none ∧ isA st.hier (modAttrErr st "showwarning") "AttributeError" = true)) →
      st.showImpl = .implOrig → ctxLog st (getContext useCtx st) = none →
      (st.stderr = none → showwarnmsg useCtx m st = .ok { st with out := st.out ++ [.lost] }) ∧
      (∀ i e w, st.stderr = some w → st.formatwarning = some (.userRaises i e) →
        showwarnmsg useCtx m st = .error e) ∧
      (∀ w, st.stderr = some w → st.formatwarning = none →
        isA st.hier (modAttrErr st "formatwarning") "AttributeError" = false →
        showwarnmsg useCtx m st = .error (modAttrErr st "formatwarning")) ∧
      ((st.formatwarning = some .fmtOrig ∨
          (st.formatwarning = none ∧ isA st.hier (modAttrErr st "formatwarning") "AttributeError" = true)) →
        (st.stderr = some (.ok ()) → showwarnmsg useCtx m st = .ok { st with out := st.out ++ [.written] }) ∧
        (∀ e, st.stderr = some (.error e) → isA st.hier e "OSError" = true →
          showwarnmsg useCtx m st = .ok { st with out := st.out ++ [.lost] }) ∧
        (∀ e, st.stderr = some (.error e) → isA st.hier e "OSError" = false →
          showwarnmsg useCtx m st = .error e)))

theorem showDispatch_proven : ShowDispatch := by
  intro useCtx m st
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i h; simp [showwarnmsg, h]
  · intro i e h; simp [showwarnmsg, h]
  · intro h; exact ⟨_, by simp [showwarnmsg, h]; rfl, rfl⟩
  · intro h he; simp [showwarnmsg, h, he]
  · intro hsw himpl hlog
    have hcall : showwarnmsg useCtx m st = writeOut st := by
      rcases hsw with h | ⟨h, he⟩
      · simp [showwarnmsg, h, callImpl, himpl, showImplOrig, hlog]
      · simp [showwarnmsg, h, he, callImpl, himpl, showImplOrig, hlog]
    rw [hcall]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h; simp [writeOut, h]
    · intro i e w h hf; simp [writeOut, h, hf]
    · intro w h hf he; simp [writeOut, h, hf, he]
    · intro hfmt
      refine ⟨?_, ?_, ?_⟩
      · intro h
        rcases hfmt with hf | ⟨hf, he⟩
        · simp [writeOut, h, hf]
        · simp [writeOut, h, hf, he]
      · intro e h he
        rcases hfmt with hf | ⟨hf, hf2⟩
        · simp [writeOut, h, hf, he]
        · simp [writeOut, h, hf, hf2, he]
      · intro e h he
        rcases hfmt with hf | ⟨hf, hf2⟩
        · simp [writeOut, h, hf, he]
        · simp [writeOut, h, hf, hf2, he]

/-- In every relation CPython can have, the `AttributeError` a module with no `__getattr__` raises
for a missing attribute is caught by `except AttributeError`. -/
theorem plainDeleted_caught (st : MState) (a : String) (hk : HierOk st.hier) (hn : st.modGetattr a = none) :
    isA st.hier (modAttrErr st a) "AttributeError" = true := by
  simp only [modAttrErr, hn, isA, PyExc.className]
  exact (hk "AttributeError" "AttributeError" (by decide)).trans (by decide)

/-- In every relation CPython can have, `BrokenPipeError` is an `OSError`: a `sys.stderr` whose
`write` raises it loses the warning. -/
theorem brokenPipe_isOSError (H : Hier) (h : HierOk H) : isA H (.named "BrokenPipeError" "x") "OSError" = true :=
  (h "BrokenPipeError" "OSError" (by decide)).trans (by decide)

/-! ## A nested `catch_warnings` inside a recording one -/

/-- A `catch_warnings()` inside a `catch_warnings(record=True)` still records into the outer list,
in both modes: with contexts `_Context.copy` passes the log on (:59-60); without, the inner
`__enter__` leaves `_showwarnmsg_impl` (the outer `log.append`) alone. For an outer object whose
`__enter__` succeeds with a log (and, with contexts, the module's own `_showwarnmsg_impl`), every
inner `catch_warnings` with no action and no record that enters, and every warning shown through
`_showwarnmsg` then. -/
def NestedRecord : Prop :=
  ∀ (useCtx : Bool) (cw : CW) (st : MState) cw' st1 l (name : String) (om : Nat) cat ln ap
    (m : Nat),
    cw.record = true → (useCtx = true → st.showImpl = .implOrig) → cw.filter = none →
    cwEnter useCtx cw st = (cw', st1, .ok (some l)) →
    ∃ cw2 st2, cwEnter useCtx (cwInit name false om none cat ln ap) st1 = (cw2, st2, .ok none) ∧
      ∃ st3, showwarnmsg useCtx m st2 = .ok st3 ∧ st3.logs l = st2.logs l ++ [m]

theorem nestedRecord_proven : NestedRecord := by
  intro useCtx cw st cw' st1 l name om cat ln ap m hrec himpl hnf hen
  unfold cwEnter at hen
  split at hen
  · simp only [Prod.mk.injEq] at hen
    obtain ⟨_, _, h3⟩ := hen
    split at h3 <;> simp at h3
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
          refine ⟨_, _, rfl, ?_⟩
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
        refine ⟨_, _, rfl, ?_⟩
        simp [showwarnmsg, callImpl, hi, showImplOrig, getContext, ctxLog, upd, newContext]

/-! ## `__exit__` of an object never entered -/

/-- `catch_warnings.__repr__` (:689-696), for every `catch_warnings` whose `_module` is `md`: with
`sys.modules['warnings']` missing it raises `KeyError` (:693); with it there, the args are
`record=True` when recording and `module=<repr>` exactly when `md` is not that module, tested
when `repr` runs. -/
def ReprSpec : Prop :=
  ∀ (name : String) (record : Bool) (md : Nat) action cat ln ap (mr : Nat → String),
    let cw := cwInit name record md action cat ln ap
    cwRepr cw none mr = .error (.keyError "'warnings'") ∧
    cwRepr cw (some md) mr = .ok s!"{name}({if record then "record=True" else ""})" ∧
    (∀ w, w ≠ md → cwRepr cw (some w) mr =
      .ok s!"{name}({if record then s!"record=True, module={mr md}" else s!"module={mr md}"})")

theorem reprSpec_proven : ReprSpec := by
  intro name record md action cat ln ap mr
  refine ⟨rfl, ?_, ?_⟩
  · cases record <;> simp only [cwRepr, cwInit, ite_true, Bool.false_eq_true, if_false, List.append_nil,
      List.nil_append] <;> rfl
  · intro w hw
    have : md ≠ w := fun h => hw h.symm
    cases record <;> simp only [cwRepr, cwInit, this, ite_true, ite_false, if_false, Bool.false_eq_true,
      List.nil_append, List.singleton_append] <;> rfl

/-- `__exit__` of a `catch_warnings` that was never entered raises `RuntimeError` naming it by its
`repr` (:728-729; a `KeyError` from that `repr` propagates instead) and changes nothing, in both
modes. -/
def ExitNotEntered : Prop :=
  ∀ (useCtx : Bool) (name : String) (record : Bool) (md : Nat) (action : Option ActA) cat ln ap (st : MState),
    cwExit useCtx (cwInit name record md action cat ln ap) st =
      (st, match cwRepr (cwInit name record md action cat ln ap) st.sysWarnings st.modRepr with
        | .ok r => .error (.named "RuntimeError" s!"Cannot exit {r} without entering first")
        | .error e => .error e)

theorem exitNotEntered_proven : ExitNotEntered := by
  intro useCtx name record md action cat ln ap st
  rfl

/-! ## The list C searches against `_get_filters()` -/

/-- C `get_filter` and Python `warn_explicit` search the same list: C's (the context's
`_filters`, else `warnings.filters`) is `_get_filters()`, in context mode, or without contexts
while no context is set; provided `warnings.filters` exists and no filters container is a tuple. -/
def FilterListTwins : Prop :=
  ∀ (useCtx : Bool) (st : MState) cached, (useCtx = true ∨ st.ctxv = .unset) → st.filters ≠ none →
    (∀ r, st.tuples r = false) → (cFilterList st cached).map (·.1) = .ok (getFilters useCtx st)

theorem filterListTwins_proven : FilterListTwins := by
  intro useCtx st cached hu hf ht
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hf
  unfold cFilterList getFilters getContext ctxFilters
  cases useCtx <;> cases hc : st.ctxv <;> simp_all [Except.map]

/-- Without the condition on `warnings.filters`: refuted, when it was deleted C searches the list
it read last (`get_warnings_filters` keeps `st->filters`, :346-353) and Python the empty list of
`_GlobalContext._filters` (:76-80). -/
def FilterListTwinsAny : Prop :=
  ∀ (useCtx : Bool) (st : MState) cached, (useCtx = true ∨ st.ctxv = .unset) → (∀ r, st.tuples r = false) →
    (cFilterList st cached).map (·.1) = .ok (getFilters useCtx st)

theorem filterListTwinsAny_refuted : ¬ FilterListTwinsAny := fun h => by
  have e := congrArg (fun r => (r.map List.length : Py Nat))
    (h false { st0 with filters := none, lists := fun _ => [.other 0 (.ok false)] } 0 (Or.inr rfl) (fun _ => rfl))
  simp [cFilterList, getFilters, getContext, ctxFilters, st0, Except.map] at e

/-- Without the condition on tuples: refuted, C's `get_warnings_filters` (:356-360) and
`get_warnings_context_filters` (:332-337) refuse a tuple; Python's `for item in ...` iterates it. -/
def FilterListTwinsTuple : Prop :=
  ∀ (useCtx : Bool) (st : MState) cached, (useCtx = true ∨ st.ctxv = .unset) → st.filters ≠ none →
    (cFilterList st cached).map (·.1) = .ok (getFilters useCtx st)

theorem filterListTwinsTuple_refuted : ¬ FilterListTwinsTuple := fun h => by
  have e := h false { st0 with tuples := fun _ => true } 0 (Or.inr rfl) (by simp [st0])
  simp [cFilterList, st0, Except.map] at e

end PyLean.CoreLibs.Warn
