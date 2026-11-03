import PyLean.CoreLibs.Warn.Filters

/-!
`catch_warnings` and the warnings contexts, Lib/_py_warnings.py (CPython 3.15.2): `_Context`
(`__init__` :53-55, `copy` :57-61, `_record_warning` :63-64), `_GlobalContext` (`__init__`
:68-69, `_filters` :72-80), `_get_context` (:89-95), `_set_context` (:98-100), `_new_context`
(:103-108), `_get_filters` (:111-114), `showwarning` (:121-124), `_showwarnmsg_impl` (:133-150),
`_showwarnmsg` (:217-233), `_formatwarnmsg` (:240-251), `catch_warnings` (`__init__` :675-687,
`__repr__` :689-696, `__enter__` :698-725, `__exit__` :727-737); and how C picks the filters list,
Python/_warnings.c: `get_warnings_context` (:303-315), `get_warnings_context_filters` (:318-339),
`get_warnings_filters` (:343-362).

Scope:
* The module is the `warnings` module (`catch_warnings(module=...)` with another module is the
  testing hook the docstring describes; only its identity, for `repr`, is kept). `_use_context` is a parameter.
* Lists are references into a heap; the filters lists hold `Elem`s, a record log holds message ids.
  `warnings.filters` is a list or deleted; a reference can be marked a tuple, which only C's list
  check (`cFilterList`) reads (`Filters.lean` covers the tuple for the filter functions).
* A module attribute that holds a function: the original `showwarning` (`_showwarning_orig`), the
  original `_showwarnmsg_impl`, the original `formatwarning`, a record log's `append`, another
  callable (a user hook, called with the message), or a non-callable object; `showwarning` and
  `formatwarning` can also be deleted.
* `_formatwarnmsg_impl`'s text is not modelled (only that something is written); writing to the file can
  succeed, raise `OSError` (swallowed), or raise something else.
* The lock is held around each body (`with _wm._lock:`); `_filters_mutated_lock_held` therefore
  succeeds and bumps the version.
-/

namespace PyLean.CoreLibs.Warn

open PyLean

abbrev Ref := Nat

inductive Fn where
  | showOrig
  | implOrig
  | fmtOrig
  | logAppend (log : Ref)
  | user (id : Nat)
  | userRaises (id : Nat) (e : PyExc)
  | noncallable
  deriving DecidableEq, Repr

/-- A `_Context`: its `_filters` list and its `log` (a list, or `None`). -/
structure Ctx where
  filters : Ref
  log : Option Ref
  deriving DecidableEq, Repr

/-- What `_warnings_context.get()` finds: nothing (`LookupError`), `_global_context`, or a
`_Context`. -/
inductive CtxV where
  | unset
  | global
  | ctx (c : Nat)
  deriving DecidableEq, Repr

/-- What happened to a shown warning: appended to a log, written to the file (the text a
callback), lost (`sys.stderr` is `None`, or the write raised `OSError`), or passed to a user hook. -/
inductive Shown where
  | logged (log : Ref)
  | written
  | lost
  | hook (id : Nat)
  deriving DecidableEq, Repr

structure MState where
  /-- the filters lists -/
  lists : Ref → List Elem
  /-- the record logs -/
  logs : Ref → List Nat
  /-- the next fresh reference (lists, logs and contexts share it) -/
  next : Nat
  filters : Option Ref
  showwarning : Option Fn
  showImpl : Fn
  formatwarning : Option Fn
  ver : Int
  ctxv : CtxV
  ctxs : Nat → Ctx
  /-- `sys.stderr`: `none` when it is `None`; else what `write` does -/
  stderr : Option (Py Unit)
  /-- what the shown warnings did, oldest first -/
  out : List Shown
  /-- which references are tuples rather than lists (only C's list check reads it) -/
  tuples : Ref → Bool
  /-- the exception class relation (`PyType_IsSubtype`) -/
  hier : Hier
  /-- `sys.modules['warnings']`, by object id (`none` when it is missing) -/
  sysWarnings : Option Nat
  /-- `repr()` of a module object -/
  modRepr : Nat → String

def upd {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α := fun i => if i = k then v else f i

def noFilters : PyExc := .named "AttributeError" "module 'warnings' has no attribute 'filters'"

/-! ## Contexts -/

/-- `_get_context()`, :89-95. -/
def getContext (useCtx : Bool) (st : MState) : CtxV :=
  if !useCtx then .global
  else match st.ctxv with
    | .unset => .global
    | v => v

/-- The list `context._filters` names: a `_Context`'s list, or for `_global_context` (:72-80)
`warnings.filters`, or a fresh `[]` when it was deleted (`none`). -/
def ctxFilters (st : MState) : CtxV → Option Ref
  | .ctx c => some (st.ctxs c).filters
  | _ => st.filters

/-- The log of a context: `_GlobalContext.__init__` sets `None` and nothing sets it later. -/
def ctxLog (st : MState) : CtxV → Option Ref
  | .ctx c => (st.ctxs c).log
  | _ => none

/-- `_get_filters()`, :111-114, as its contents. -/
def getFilters (useCtx : Bool) (st : MState) : List Elem :=
  match ctxFilters st (getContext useCtx st) with
  | some r => st.lists r
  | none => []

/-- `_new_context()`, :103-108: `old.copy()` (:57-61) is a `_Context` over a copy of the old
filters (`_Context.__init__`, :53-55, starts with no log) that shares the old log; it becomes the
current context. Returns the old context and the new one. -/
def newContext (st : MState) : MState × CtxV × Nat :=
  let old := getContext true st
  let content := match ctxFilters st old with
    | some r => st.lists r
    | none => []
  let lr := st.next
  let c := st.next + 1
  let st' := { st with lists := upd st.lists lr content, next := st.next + 2,
                       ctxs := upd st.ctxs c ⟨lr, ctxLog st old⟩, ctxv := .ctx c }
  (st', old, c)

/-! ## Showing a warning -/

/-- Writing the text to `sys.stderr`, :138-150 (`msg.file` is `None` here, as `warn_explicit`
makes it). -/
def writeOut (st : MState) : Py MState :=
  match st.stderr with
  | none => .ok { st with out := st.out ++ [.lost] }
  | some w =>
    -- `text = _wm._formatwarnmsg(msg)`, :145, outside the `try`
    match st.formatwarning with
    | some .noncallable => .error (.typeError "'int' object is not callable")
    | some (.userRaises _ e) => .error e
    | _ =>
    match w with
    | .ok () => .ok { st with out := st.out ++ [.written] }
    | .error e =>
      -- `except OSError: pass`, :148-150
      if isA st.hier e "OSError" then .ok { st with out := st.out ++ [.lost] } else .error e

/-- `_showwarnmsg_impl(msg)`, :133-150: the context's log, if any, takes it
(`_record_warning`, :63-64). -/
def showImplOrig (useCtx : Bool) (msg : Nat) (st : MState) : Py MState :=
  match ctxLog st (getContext useCtx st) with
  | some l => .ok { st with logs := upd st.logs l (st.logs l ++ [msg]), out := st.out ++ [.logged l] }
  | none => writeOut st

/-- Calling what `_wm._showwarnmsg_impl` holds. -/
def callImpl (useCtx : Bool) (msg : Nat) (st : MState) : Py MState :=
  match st.showImpl with
  | .implOrig => showImplOrig useCtx msg st
  | .logAppend l => .ok { st with logs := upd st.logs l (st.logs l ++ [msg]), out := st.out ++ [.logged l] }
  | .user i => .ok { st with out := st.out ++ [.hook i] }
  | .userRaises _ e => .error e
  | .noncallable => .error (.typeError "'int' object is not callable")
  -- `showwarning` itself is a valid `_showwarnmsg_impl` only through `showwarning(...)`'s
  -- arguments; the other originals are not message hooks
  | _ => .error (.typeError "~takes positional arguments")

/-- `_showwarnmsg(msg)`, :217-233: a replaced `showwarning` is called; otherwise (also when it was
deleted) `_showwarnmsg_impl`. `showwarning` (:121-124) calls `_showwarnmsg_impl` too. -/
def showwarnmsg (useCtx : Bool) (msg : Nat) (st : MState) : Py MState :=
  match st.showwarning with
  | none | some .showOrig => callImpl useCtx msg st
  | some .noncallable => .error (.typeError "warnings.showwarning() must be set to a function or method")
  | some (.user i) => .ok { st with out := st.out ++ [.hook i] }
  -- `sw(msg.message, ...)` raising: the exception propagates, :230-231
  | some (.userRaises _ e) => .error e
  | some _ => .error (.typeError "~takes positional arguments")

/-! ## `catch_warnings` -/

/-- A `catch_warnings` object: its arguments, whether it was entered, and what `__enter__` saved. -/
structure CW where
  name : String
  record : Bool
  /-- `self._module`, by object id -/
  module : Nat
  filter : Option (ActA × Nat × IntA × Bool)
  entered : Bool
  savedFilters : Option Ref
  savedImpl : Fn
  savedShow : Option Fn
  savedCtx : CtxV

/-- `self._module = sys.modules['warnings'] if module is None else module`, :682. -/
def cwModuleOf (module : Option Nat) (sysWarnings : Option Nat) : Py Nat :=
  match module with
  | some m => .ok m
  | none => match sysWarnings with
    | some w => .ok w
    | none => .error (.keyError "'warnings'")

/-- `catch_warnings.__init__`, :675-687, with `self._module` resolved (`cwModuleOf`). -/
def cwInit (name : String) (record : Bool) (module : Nat)
    (action : Option ActA) (category : Nat) (lineno : IntA) (append : Bool) : CW :=
  { name := name, record := record, module := module,
    filter := action.map (fun a => (a, category, lineno, append)), entered := false,
    savedFilters := none, savedImpl := .implOrig, savedShow := none, savedCtx := .unset }

/-- `catch_warnings.__repr__`, :689-696: `self._module is not sys.modules['warnings']` is tested
when `repr` runs (a missing `sys.modules['warnings']` raises `KeyError`); `name` is
`type(self).__name__`. -/
def cwRepr (cw : CW) (sysWarnings : Option Nat) (modRepr : Nat → String) : Py String :=
  let a1 := if cw.record then ["record=True"] else []
  match sysWarnings with
  | none => .error (.keyError "'warnings'")
  | some w =>
    let args := a1 ++ (if cw.module = w then [] else [s!"module={modRepr cw.module}"])
    .ok s!"{cw.name}({", ".intercalate args})"

/-- The filters state `simplefilter` works on: the current filters list. -/
def curFState (useCtx : Bool) (st : MState) : FState :=
  ⟨match ctxFilters st (getContext useCtx st) with
    | some r => .list (st.lists r)
    | none => .deleted, st.ver⟩

/-- Writing a filters state back to the list it came from. -/
def putFState (useCtx : Bool) (st : MState) (fs : FState) : MState :=
  match ctxFilters st (getContext useCtx st), fs.cont with
  | some r, .list xs => { st with lists := upd st.lists r xs, ver := fs.ver }
  | _, _ => { st with ver := fs.ver }

def noShowAttr : PyExc := .named "AttributeError" "module 'warnings' has no attribute 'showwarning'"
def noSavedFilters : PyExc := .named "AttributeError" "'catch_warnings' object has no attribute '_filters'"

/-- `catch_warnings.__enter__`, :698-725: the object and the state it leaves, and the log it
returns or the exception it raises. Nothing is undone when it raises. -/
def cwEnter (useCtx : Bool) (cw : CW) (st : MState) : CW × MState × Py (Option Ref) :=
  if cw.entered then
    (cw, st, match cwRepr cw st.sysWarnings st.modRepr with
      | .ok r => .error (.named "RuntimeError" s!"Cannot enter {r} twice")
      | .error e => .error e)
  else
  let cw := { cw with entered := true }
  -- with _wm._lock:
  let step : Py (CW × MState × Option Nat) := if useCtx then
      let (st', old, c) := newContext st
      .ok ({ cw with savedCtx := old }, st', some c)
    else match st.filters with
      | none => .error noFilters
      | some r =>
        let r' := st.next
        .ok ({ cw with savedFilters := some r, savedImpl := st.showImpl },
             { st with lists := upd st.lists r' (st.lists r), next := st.next + 1, filters := some r' },
             none)
  match step with
  | .error e => (cw, st, .error e)
  | .ok (cw, st, ctx) =>
  match st.showwarning with
  | none => (cw, st, .error noShowAttr)
  | some sw =>
  let cw := { cw with savedShow := some sw }
  let st := { st with ver := st.ver + 1 }
  let (st, log) : MState × Option Ref := if cw.record then
      let l := st.next
      let st := { st with logs := upd st.logs l [], next := st.next + 1 }
      let st := match ctx with
        | some c => { st with ctxs := upd st.ctxs c { st.ctxs c with log := some l } }
        | none => { st with showImpl := .logAppend l }
      ({ st with showwarning := some .showOrig }, some l)
    else (st, none)
  -- the lock is released; then the filter
  match cw.filter with
  | none => (cw, st, .ok log)
  | some (a, c, ln, ap) =>
    match simplefilter st.hier a c ln ap (curFState useCtx st) with
    | .ok fs => (cw, putFState useCtx st fs, .ok log)
    | .error e => (cw, st, .error e)

def noSavedShow : PyExc := .named "AttributeError" "'catch_warnings' object has no attribute '_showwarning'"

/-- `catch_warnings.__exit__`, :727-737: the state it leaves and how it ends. -/
def cwExit (useCtx : Bool) (cw : CW) (st : MState) : MState × Py Unit :=
  if !cw.entered then
    (st, match cwRepr cw st.sysWarnings st.modRepr with
      | .ok r => .error (.named "RuntimeError" s!"Cannot exit {r} without entering first")
      | .error e => .error e)
  else
  let step : Py MState := if useCtx then .ok { st with ctxv := cw.savedCtx }
    else match cw.savedFilters with
      | none => .error noSavedFilters
      | some r => .ok { st with filters := some r, showImpl := cw.savedImpl }
  match step with
  | .error e => (st, .error e)
  | .ok st =>
  match cw.savedShow with
  | none => (st, .error noSavedShow)
  | some sw => ({ st with showwarning := some sw, ver := st.ver + 1 }, .ok ())

/-! ## The list C searches -/

/-- How C reaches the filters list, `get_filter` :551-587: the context variable's `_filters`
(`get_warnings_context_filters`, :318-339, through `get_warnings_context`, :303-315), else
`warnings.filters` (`get_warnings_filters`, :343-362), which when deleted falls back to the list
C cached the last time it read one (`cached`). The result's name is the one an item error
message uses. -/
def cFilterList (st : MState) (cached : Ref) : Py (List Elem × String) :=
  match st.ctxv with
  | .unset =>
    match st.filters with
    | some r =>
      if st.tuples r then .error (.valueError "_warnings.filters must be a list")
      else .ok (st.lists r, "filters")
    | none => .ok (st.lists cached, "filters")
  | v =>
    match ctxFilters st v with
    | some r =>
      if st.tuples r then .error (.valueError "_filters of warnings._warnings_context must be a list")
      else .ok (st.lists r, "_warnings_context _filters")
    | none => .ok ([], "_warnings_context _filters")

end PyLean.CoreLibs.Warn
