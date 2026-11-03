import PyLean.Registry
import PyLean.TypeObj.PropsAttr
import PyLean.TypeObj.ExcFreelist

/-!
Properties of `Objects/exceptions.c`, quantified over every world and, where user code can
run, over every `rt : Rt`.

A hypothesis in a statement is one of three things, and each docstring says which:

* a type invariant of an exception object (`self` holds an exception payload at a valid
  address; the `object` member of a `UnicodeEncodeError`; ...);
* the case the statement is about (`args` has one element, the matcher accepts `exc`);
* for the group recursion, the documented contract of `derive` and the fact that
  `.exceptions` is read-only (`SplitHyp`).
-/

namespace PyLean.TypeObj

open PyLean.Registry

/-! ## Heap lemmas -/

theorem get_setCell_same (w : World) (a : Addr) (c : Cell) (h : a < w.heap.size) :
    (w.setCell a c).get a = c := by
  simp [World.get, World.setCell, Array.getD, h]

theorem get_setCell_ne (w : World) (a b : Addr) (c : Cell) (h : a ≠ b) :
    (w.setCell a c).get b = w.get b := by
  simp only [World.get, World.setCell]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  simp [Array.getElem?_setIfInBounds, h]

theorem size_setCell (w : World) (a : Addr) (c : Cell) :
    (w.setCell a c).heap.size = w.heap.size := by
  simp [World.setCell]

/-- `self` is an exception object at a valid address: the type invariant of every method of
`BaseException`. -/
structure IsExc (w : World) (a : Addr) (d : ExcData) : Prop where
  size : a < w.heap.size
  body : payloadOf w (.obj a) = some (.exc d)

theorem IsExc.cell {w : World} {a : Addr} {d : ExcData} (h : IsExc w a d) :
    ∃ o : Obj, w.get a = .val o ∧ o.body = .exc d := by
  have hb := h.body
  simp only [payloadOf] at hb
  cases hc : w.get a with
  | ty c t => simp [hc] at hb
  | val o =>
    simp [hc] at hb
    exact ⟨o, rfl, hb⟩

/-- The world after `excUpdate`. -/
def excUpdW (w : World) (a : Addr) (f : ExcData → ExcData) : World :=
  match w.get a with
  | .val o =>
    w.setCell a (.val (match o.body with
      | .exc d => { o with body := .exc (f d) }
      | _ => o))
  | .ty _ _ => w

theorem excUpdate_app (w : World) (a : Addr) (f : ExcData → ExcData) :
    excUpdate (.obj a) f w = .ok () (excUpdW w a f) := by
  simp only [excUpdate, modObj, excUpdW, modW_app]
  rfl

theorem IsExc.update {w : World} {a : Addr} {d : ExcData} (h : IsExc w a d)
    (f : ExcData → ExcData) : IsExc (excUpdW w a f) a (f d) := by
  obtain ⟨o, hc, hb⟩ := h.cell
  constructor
  · simp [excUpdW, hc, size_setCell, h.size]
  · simp [excUpdW, hc, hb, payloadOf, get_setCell_same _ _ _ h.size]

theorem IsExc.data {w : World} {a : Addr} {d : ExcData} (h : IsExc w a d) :
    excDataOf w (.obj a) = d := by
  simp [excDataOf, h.body]

theorem excUpdW_data {w : World} {a : Addr} {d : ExcData} (h : IsExc w a d)
    (f : ExcData → ExcData) : excDataOf (excUpdW w a f) (.obj a) = f d :=
  (h.update f).data

/-! ## `BaseException` -/

/-- **`str(e)` follows `e.args`.** No argument gives `""`, one argument gives `str` of that
argument, more give `str` of the tuple. -/
def BaseExceptionStrArgs : Prop :=
  ∀ (rt : Rt) (w : World) (v : Val),
    baseExceptionStr rt v w =
      (match excArgs w v with
       | [] => (pure (Val.str "") : M Val)
       | [x] => Val.str <$> rt.str x
       | xs => Val.str <$> rt.str (.tuple xs)) w

theorem baseExceptionStrArgs_proven : BaseExceptionStrArgs := by
  intro rt w v
  rfl

/-- **`repr(e)` follows `e.args`**: `Name(x)` for one argument, `Name` then the repr of the
tuple otherwise, and `Name` is the last dotted part of `tp_name`. -/
def BaseExceptionReprArgs : Prop :=
  ∀ (rt : Rt) (w : World) (v : Val),
    baseExceptionRepr rt v w =
      (match excArgs w v with
       | [x] => (do
         let r ← rt.repr x
         pure (Val.str s!"{pyTypeName w (typeOf w v)}({r})") : M Val)
       | xs => do
         let r ← rt.repr (.tuple xs)
         pure (Val.str (pyTypeName w (typeOf w v) ++ r))) w

theorem baseExceptionReprArgs_proven : BaseExceptionReprArgs := by
  intro rt w v
  rfl

/-- **`KeyError` differs from `BaseException` in exactly one case**: a single argument is
shown with `repr`, anything else as `BaseException_str` would. -/
def KeyErrorStrOneArg : Prop :=
  ∀ (rt : Rt) (w : World) (v : Val),
    keyErrorStr rt v w =
      (match excArgs w v with
       | [x] => Val.str <$> rt.repr x
       | _ => baseExceptionStr rt v) w

theorem keyErrorStrOneArg_proven : KeyErrorStrOneArg := by
  intro rt w v
  rfl

/-- **`BaseException_vectorcall` is `tp_new` followed by `tp_init`.** The fast path of the
exact builtin classes and the generic `type_call` path build the same object when no
keywords are passed: same class, same fields. -/
def BaseExceptionVectorcallTwin : Prop :=
  ∀ (w : World) (t : Addr) (args : List Val),
    ∃ (v : Val) (w1 w2 : World),
      (do
        let r ← baseExceptionNew t args
        baseExceptionInit r args []
        pure r) w = .ok v w1 ∧
      baseExceptionVectorcall t args [] w = .ok v w2 ∧
      typeOf w1 v = typeOf w2 v ∧ excDataOf w1 v = excDataOf w2 v

theorem alloc_app (w : World) (t : Addr) (b : Payload) :
    alloc t b w = .ok (.obj w.heap.size)
      { w with heap := w.heap.push (.val { cls := t, body := b }) } := rfl

theorem get_push_size (w : World) (c : Cell) :
    World.get { w with heap := w.heap.push c } w.heap.size = c := by
  simp [World.get, Array.getD]

theorem get_push_lt (w : World) (c : Cell) {a : Addr} (h : a < w.heap.size) :
    World.get { w with heap := w.heap.push c } a = w.get a := by
  have hne : a ≠ w.heap.size := Nat.ne_of_lt h
  simp only [World.get]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  simp [Array.getElem?_push, hne]

theorem isExc_alloc (w : World) (t : Addr) (d : ExcData) :
    IsExc { w with heap := w.heap.push (.val { cls := t, body := .exc d }) } w.heap.size d := by
  constructor
  · simp
  · simp [payloadOf, get_push_size]

theorem baseExceptionVectorcallTwin_proven : BaseExceptionVectorcallTwin := by
  intro w t args
  let c : Cell := .val { cls := t, body := .exc { args := args } }
  let w0 : World := { w with heap := w.heap.push c }
  have hx : IsExc w0 w.heap.size { args := args } := isExc_alloc w t { args := args }
  obtain ⟨o, hc, hb⟩ := hx.cell
  refine ⟨.obj w.heap.size, excUpdW w0 w.heap.size (fun d => { d with args := args }), w0, ?_, ?_, ?_, ?_⟩
  · simp only [baseExceptionNew, baseExceptionInit, argNoKeywords, M.bind_app, alloc_app, getW_app]
    have : excUpdate (.obj w.heap.size) (fun d => { d with args := args }) w0 =
        .ok () (excUpdW w0 w.heap.size (fun d => { d with args := args })) := excUpdate_app _ _ _
    simp only [w0, c] at this
    simp [this, w0, c]
  · simp only [baseExceptionVectorcall, argNoKwnames, M.bind_app, getW_app]
    simp [alloc_app, w0, c]
  · have h1 : typeOf (excUpdW w0 w.heap.size (fun d => { d with args := args })) (.obj w.heap.size)
        = o.cls := by
      simp [typeOf, excUpdW, hc, hb, get_setCell_same _ _ _ hx.size]
    have h2 : typeOf w0 (.obj w.heap.size) = o.cls := by simp [typeOf, hc]
    rw [h1, h2]
  · rw [excUpdW_data hx, hx.data]

/-- **`__reduce__` is `(type, args)` plus the instance dict when one exists.** -/
def BaseExceptionReduceShape : Prop :=
  ∀ (w : World) (v : Val),
    baseExceptionReduce v w =
      .ok (.tuple ([.obj (typeOf w v), .tuple (excArgs w v)] ++
        (instDictAddr w v).toList.map Val.obj)) w

theorem baseExceptionReduceShape_proven : BaseExceptionReduceShape := by
  intro w v
  simp only [baseExceptionReduce, M.bind_app, getW_app]
  cases h : instDictAddr w v <;> simp

/-- **`__setstate__` sets each item of the dict, reading the dict as it is now.** `None` is a
no-op and anything but a dict is a `TypeError` with the world unchanged (`:241-245`). A dict is
walked by position (`PyDict_Next`, `:246`): each turn reads position `i` of the dict in the
current world, so an item a `__setattr__` adds is set too; the end of the dict ends the loop; a
non-string key is the `TypeError` of `PyObject_SetAttr`; a failing set is the result
(`:252-254`); a successful one goes on at `i + 1` in the world it left. Last, with exact str keys
and a `__setattr__` that leaves the dict alone, `__setstate__(d)` is exactly
`setattr(self, k, v)` for every item in order, so a version that skips items or sets nothing
fails. The `es.length < excIterFuel` hypothesis is the model's loop bound, not a Python limit. -/
def BaseExceptionSetstateLive : Prop :=
  (∀ (rt : Rt) (self : Val) (w : World), baseExceptionSetstate rt self .none w = .ok .none w) ∧
  (∀ (rt : Rt) (self state : Val) (w : World), state.is .none = false →
    dictOf w state = none →
    baseExceptionSetstate rt self state w =
      .err (.exc B.TypeError "state is not a dictionary" none) w) ∧
  (∀ (rt : Rt) (self state : Val) (fuel i : Nat) (w : World),
    ((dictOf w state).getD [])[i]? = none → setstateLoop rt self state (fuel + 1) i w = .ok () w) ∧
  (∀ (rt : Rt) (self state k v : Val) (fuel i : Nat) (w : World),
    ((dictOf w state).getD [])[i]? = some (k, v) → strOf w k = none →
    setstateLoop rt self state (fuel + 1) i w =
      .err (.exc B.TypeError s!"attribute name must be string, not '{trunc 200 (typeName w k)}'" none) w) ∧
  (∀ (rt : Rt) (self state k v : Val) (n : Name) (fuel i : Nat) (w w1 : World),
    ((dictOf w state).getD [])[i]? = some (k, v) → strOf w k = some n →
    rt.setAttr self n (some v) w = .ok () w1 →
    setstateLoop rt self state (fuel + 1) i w = setstateLoop rt self state fuel (i + 1) w1) ∧
  (∀ (rt : Rt) (self state k v : Val) (n : Name) (fuel i : Nat) (e : PyErr) (w w1 : World),
    ((dictOf w state).getD [])[i]? = some (k, v) → strOf w k = some n →
    rt.setAttr self n (some v) w = .err e w1 →
    setstateLoop rt self state (fuel + 1) i w = .err e w1) ∧
  (∀ (rt : Rt) (self state : Val) (es : List (Name × Val)) (w : World),
    state.is .none = false → dictOf w state = some (es.map fun p => (Val.str p.1, p.2)) →
    es.length < excIterFuel →
    (∀ (n : Name) (v : Val) (w w' : World), rt.setAttr self n (some v) w = .ok () w' →
      dictOf w' state = dictOf w state) →
    baseExceptionSetstate rt self state w =
      (do es.forM (fun p => rt.setAttr self p.1 (some p.2)); pure Val.none) w)

theorem listForM_cons {α : Type} (f : α → M PUnit) (a : α) (as : List α) :
    List.forM (a :: as) f = (f a >>= fun _ => List.forM as f) := rfl

theorem listForM_nil {α : Type} (f : α → M PUnit) : List.forM [] f = pure () := rfl

theorem setstateLoop_fold (rt : Rt) (self state : Val) (es : List (Name × Val))
    (hfr : ∀ (n : Name) (v : Val) (w w' : World), rt.setAttr self n (some v) w = .ok () w' →
      dictOf w' state = dictOf w state) :
    ∀ (fuel i : Nat) (w : World), dictOf w state = some (es.map fun p => (Val.str p.1, p.2)) →
      (es.drop i).length < fuel →
      setstateLoop rt self state fuel i w = (es.drop i).forM (fun p => rt.setAttr self p.1 (some p.2)) w := by
  intro fuel
  induction fuel with
  | zero => intro i w _ h; omega
  | succ f ih =>
    intro i w hd hl
    by_cases hi : i < es.length
    · have hdrop : es.drop i = es[i] :: es.drop (i + 1) := List.drop_eq_getElem_cons hi
      have hget : ((dictOf w state).getD [])[i]? = some (Val.str es[i].1, es[i].2) := by
        simp [hd, hi]
      rw [hdrop]
      simp only [setstateLoop, M.bind_app, getW_app, hget, strOf, listForM_cons]
      cases hs : rt.setAttr self es[i].1 (some es[i].2) w with
      | ok u w1 =>
        simp only
        have hd1 : dictOf w1 state = some (es.map fun p => (Val.str p.1, p.2)) := by
          rw [hfr _ _ _ _ hs, hd]
        have hl1 : (es.drop (i + 1)).length < f := by
          rw [hdrop] at hl
          simp at hl
          simp
          omega
        exact ih (i + 1) w1 hd1 hl1
      | err e w1 => simp
    · have hge : es.length ≤ i := by omega
      have hget : ((dictOf w state).getD [])[i]? = none := by simp [hd, hge]
      simp [setstateLoop, hget, List.drop_eq_nil_of_le hge, listForM_nil]

theorem baseExceptionSetstateLive_proven : BaseExceptionSetstateLive := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rt self w
    simp [baseExceptionSetstate, Val.is]
  · intro rt self state w h1 h2
    simp [baseExceptionSetstate, h1, h2, typeErr, raiseC]
  · intro rt self state fuel i w h
    simp [setstateLoop, h]
  · intro rt self state k v fuel i w h hk
    simp [setstateLoop, h, hk, typeErr, raiseC]
  · intro rt self state k v n fuel i w w1 h hk hs
    simp [setstateLoop, h, hk, hs]
  · intro rt self state k v n fuel i e w w1 h hk hs
    simp [setstateLoop, h, hk, hs]
  · intro rt self state es w hn hd hl hfr
    simp only [baseExceptionSetstate, hn, M.bind_app, getW_app, hd, Bool.false_eq_true, if_false]
    rw [setstateLoop_fold rt self state es hfr excIterFuel 0 w hd (by simpa using hl)]
    simp

/-- **`__traceback__` takes a traceback or `None` and nothing else**: any other value is a
`TypeError` with the world unchanged, deleting is a `TypeError`, and `with_traceback` returns
`self`. -/
def TracebackSetterChecks : Prop :=
  (∀ (self v : Val) (w : World), tracebackCheck w v = false → v.is .none = false →
    baseExceptionTracebackSet self (some v) w =
      .err (.exc B.TypeError "__traceback__ must be a traceback or None" none) w) ∧
  (∀ (self : Val) (w : World), baseExceptionTracebackSet self none w =
    .err (.exc B.TypeError "__traceback__ may not be deleted" none) w) ∧
  (∀ (self tb r : Val) (w w' : World), baseExceptionWithTraceback self tb w = .ok r w' → r = self)

theorem tracebackSetterChecks_proven : TracebackSetterChecks := by
  refine ⟨?_, ?_, ?_⟩
  · intro self v w h1 h2
    simp [baseExceptionTracebackSet, h1, h2, typeErr, raiseC]
  · intro self w
    simp [baseExceptionTracebackSet, typeErr, raiseC]
  · intro self tb r w w' h
    simp only [baseExceptionWithTraceback, M.bind_app] at h
    cases h1 : baseExceptionTracebackSet self (some tb) w with
    | ok a w1 =>
      simp only [h1] at h
      simp at h
      exact h.1.symm
    | err e w1 => simp [h1] at h

/-- **`__cause__` always sets `__suppress_context__`.** Every successful assignment, `None`
included, stores the value (`None` as NULL) and sets the flag. -/
def CauseSetsSuppressContext : Prop :=
  ∀ (a : Addr) (d : ExcData) (value : Val) (w w' : World),
    IsExc w a d →
    baseExceptionCauseSet (.obj a) (some value) w = .ok () w' →
    (excDataOf w' (.obj a)).suppressContext = true ∧
    (excDataOf w' (.obj a)).cause = (if value.is .none then none else some value)

theorem causeSetsSuppressContext_proven : CauseSetsSuppressContext := by
  intro a d value w w' hx h
  simp only [baseExceptionCauseSet, M.bind_app, getW_app] at h
  by_cases hn : value.is .none = true
  · simp only [hn, if_true, pyExceptionSetCause, excUpdate_app] at h
    simp at h
    subst h
    simp [excUpdW_data hx, hn]
  · have hn' : value.is .none = false := by simpa using hn
    by_cases hi : excInstanceCheck w value = true
    · simp [hn', hi, pyExceptionSetCause, excUpdate_app] at h
      subst h
      simp [excUpdW_data hx, hn']
    · have hi' : excInstanceCheck w value = false := by simpa using hi
      simp [hn', hi', typeErr, raiseC] at h

/-- **`__context__` assignment touches nothing else**: `__suppress_context__` and `__cause__`
keep their values. -/
def ContextSetKeepsSuppress : Prop :=
  ∀ (a : Addr) (d : ExcData) (value : Val) (w w' : World),
    IsExc w a d →
    baseExceptionContextSet (.obj a) (some value) w = .ok () w' →
    (excDataOf w' (.obj a)).suppressContext = d.suppressContext ∧
    (excDataOf w' (.obj a)).cause = d.cause ∧
    (excDataOf w' (.obj a)).context = (if value.is .none then none else some value)

theorem contextSetKeepsSuppress_proven : ContextSetKeepsSuppress := by
  intro a d value w w' hx h
  simp only [baseExceptionContextSet, M.bind_app, getW_app] at h
  by_cases hn : value.is .none = true
  · simp only [hn, if_true, pyExceptionSetContext, excUpdate_app] at h
    simp at h
    subst h
    simp [excUpdW_data hx, hn]
  · have hn' : value.is .none = false := by simpa using hn
    by_cases hi : excInstanceCheck w value = true
    · simp [hn', hi, pyExceptionSetContext, excUpdate_app] at h
      subst h
      simp [excUpdW_data hx, hn']
    · have hi' : excInstanceCheck w value = false := by simpa using hi
      simp [hn', hi', typeErr, raiseC] at h

/-- **`__suppress_context__` is a strict bool member**: `Py_T_BOOL` stores `True` and `False`
and rejects every other value, and the member cannot be deleted. -/
def SuppressContextOnlyBool : Prop :=
  (∀ (a : Addr) (d : ExcData) (b : Bool) (w w' : World), IsExc w a d →
    suppressContextSet (.obj a) (some (.bool b)) w = .ok () w' →
    (excDataOf w' (.obj a)).suppressContext = b) ∧
  (∀ (self v : Val) (w : World), (∀ b, v ≠ .bool b) →
    suppressContextSet self (some v) w =
      .err (.exc B.TypeError "attribute value type must be bool" none) w) ∧
  (∀ (self : Val) (w : World), suppressContextSet self none w =
    .err (.exc B.TypeError "can't delete numeric/char attribute" none) w)

theorem suppressContextOnlyBool_proven : SuppressContextOnlyBool := by
  refine ⟨?_, ?_, ?_⟩
  · intro a d b w w' hx h
    simp only [suppressContextSet, excUpdate_app] at h
    simp at h
    subst h
    simp [excUpdW_data hx]
  · intro self v w hv
    cases v with
    | bool b => exact absurd rfl (hv b)
    | _ => simp [suppressContextSet, typeErr, raiseC]
  · intro self w
    simp [suppressContextSet, typeErr, raiseC]

/-- **`e.args = x` stores `tuple(x)`**, whatever `x` is: on success the `args` field is what
`PySequence_Tuple` returned. Deleting is a `TypeError`. -/
def ArgsSetStoresTuple : Prop :=
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (xs : List Val) (w w1 w' : World),
    excSeqTuple rt (.tuple xs) w = .ok xs w1 → IsExc w1 a d →
    baseExceptionArgsSet rt (.obj a) (some (.tuple xs)) w = .ok () w' →
    excArgs w' (.obj a) = xs) ∧
  (∀ (rt : Rt) (self : Val) (w : World), baseExceptionArgsSet rt self none w =
    .err (.exc B.TypeError "args may not be deleted" none) w)

theorem argsSetStoresTuple_proven : ArgsSetStoresTuple := by
  refine ⟨?_, ?_⟩
  · intro rt a d xs w w1 w' hs hx h
    simp only [baseExceptionArgsSet, M.bind_app, hs, excUpdate_app] at h
    simp at h
    subst h
    simp [excArgs, excUpdW_data hx]
  · intro rt self w
    simp [baseExceptionArgsSet, typeErr, raiseC]

/-- **`add_note` appends.** A non-`str` note is a `TypeError` before anything happens. When
`__notes__` exists and is a list, the list ends with the note and keeps what it held. The
lookup of `__notes__` may run any user code. -/
def AddNoteAppends : Prop :=
  (∀ (rt : Rt) (self note : Val) (w : World), strOf w note = none →
    baseExceptionAddNote rt self note w =
      .err (.exc B.TypeError s!"add_note() argument must be str, not {excArgName w note}" none) w) ∧
  (∀ (rt : Rt) (self note : Val) (l : Addr) (o : Obj) (xs : List Val) (w w1 : World),
    (strOf w note).isSome →
    rt.getOptionalAttr self "__notes__" w = .ok (some (.obj l)) w1 →
    w1.get l = .val o → o.body = .list xs → l < w1.heap.size →
    ∃ w', baseExceptionAddNote rt self note w = .ok .none w' ∧
      listOf w' (.obj l) = some (xs ++ [note]))

theorem addNoteAppends_proven : AddNoteAppends := by
  refine ⟨?_, ?_⟩
  · intro rt self note w h
    simp [baseExceptionAddNote, h, typeErr, raiseC]
  · intro rt self note l o xs w w1 hs hg hc hb hl
    have hlist : listOf w1 (.obj l) = some xs := by simp [listOf, payloadOf, hc, hb]
    refine ⟨w1.setCell l (.val { o with body := .list (xs ++ [note]) }), ?_, ?_⟩
    · simp only [baseExceptionAddNote, M.bind_app, getW_app]
      have hs' : (strOf w note).isNone = false := by
        cases h : strOf w note <;> simp_all
      simp [hs', hg, modObj, hlist, hc, hb]
    · simp [listOf, payloadOf, get_setCell_same _ _ _ hl]

/-- **The thin C API reads what it wrote.** `PyException_SetCause`, `SetContext`, `SetArgs`
and `SetTraceback` are read back unchanged by the matching getters; the traceback setter
takes a traceback object. -/
def PyExceptionApiRoundTrip : Prop :=
  ∀ (a : Addr) (d : ExcData) (w : World), IsExc w a d →
    (∀ (c : Option Val) (w' : World), pyExceptionSetCause (.obj a) c w = .ok () w' →
      pyExceptionGetCause w' (.obj a) = c) ∧
    (∀ (c : Option Val) (w' : World), pyExceptionSetContext (.obj a) c w = .ok () w' →
      pyExceptionGetContext w' (.obj a) = c) ∧
    (∀ (xs : List Val) (w' : World), pyExceptionSetArgs (.obj a) xs w = .ok () w' →
      pyExceptionGetArgs w' (.obj a) = .tuple xs) ∧
    (∀ (t : Val) (w' : World), tracebackCheck w t = true → t ≠ .none →
      baseExceptionTracebackSet (.obj a) (some t) w = .ok () w' →
      pyExceptionGetTraceback w' (.obj a) = some t)

theorem pyExceptionApiRoundTrip_proven : PyExceptionApiRoundTrip := by
  intro a d w hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c w' h
    simp only [pyExceptionSetCause, excUpdate_app] at h
    simp at h
    subst h
    simp [pyExceptionGetCause, excUpdW_data hx]
  · intro c w' h
    simp only [pyExceptionSetContext, excUpdate_app] at h
    simp at h
    subst h
    simp [pyExceptionGetContext, excUpdW_data hx]
  · intro xs w' h
    simp only [pyExceptionSetArgs, excUpdate_app] at h
    simp at h
    subst h
    simp [pyExceptionGetArgs, excArgs, excUpdW_data hx]
  · intro t w' ht hn h
    simp only [baseExceptionTracebackSet, M.bind_app, getW_app, ht, if_true, excUpdate_app] at h
    simp at h
    subst h
    cases t with
    | none => exact absurd rfl hn
    | _ => simp [pyExceptionGetTraceback, excUpdW_data hx]

/-! ## `StopIteration`, `SystemExit` -/

/-- **`StopIteration.value` is the first argument or `None`**, on every `__init__`. -/
def StopIterationValue : Prop :=
  ∀ (a : Addr) (d : ExcData) (args : List Val) (w w' : World), IsExc w a d →
    stopIterationInit (.obj a) args [] w = .ok () w' →
    excArgs w' (.obj a) = args ∧
    memGet (excDataOf w' (.obj a)) "value" = some (args.headD .none)

theorem memGet_memSet_same (d : ExcData) (n : Name) (v : Val) :
    memGet (memSet n (some v) d) n = some v := by
  simp only [memGet, memSet]
  induction d.members with
  | nil => simp [NameDict.set, NameDict.get?]
  | cons p ps ih =>
    obtain ⟨k, x⟩ := p
    by_cases h : k = n
    · subst h
      simp [NameDict.set, NameDict.get?]
    · have h' : (k == n) = false := by simpa using h
      simp [NameDict.set, NameDict.get?, h', ih]

theorem stopIterationValue_proven : StopIterationValue := by
  intro a d args w w' hx h
  simp only [stopIterationInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app] at h
  simp [excUpdate_app] at h
  subst h
  have h1 := hx.update (fun d => { d with args := args })
  constructor
  · simp [excArgs, excUpdW_data h1, memSet]
  · simp only [excUpdW_data h1]
    rw [List.headD_eq_head?_getD]
    exact memGet_memSet_same _ _ _

/-- **`SystemExit.code` follows the arguments**: unchanged with none, the argument with one,
the whole tuple with more. -/
def SystemExitCode : Prop :=
  ∀ (a : Addr) (d : ExcData) (args : List Val) (w w' : World), IsExc w a d →
    systemExitInit (.obj a) args [] w = .ok () w' →
    excArgs w' (.obj a) = args ∧
    memGet (excDataOf w' (.obj a)) "code" =
      (match args with
       | [] => memGet d "code"
       | [x] => some x
       | xs => some (.tuple xs))

theorem systemExitCode_proven : SystemExitCode := by
  intro a d args w w' hx h
  simp only [systemExitInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app] at h
  simp [excUpdate_app] at h
  have h1 := hx.update (fun d => { d with args := args })
  match args, h with
  | [], h =>
    simp at h
    subst h
    simp [excArgs, excUpdW_data hx, memGet]
  | [x], h =>
    simp [excUpdate_app] at h
    subst h
    constructor
    · simp [excArgs, excUpdW_data h1, memSet]
    · simp only [excUpdW_data h1]
      exact memGet_memSet_same _ _ _
  | x :: y :: zs, h =>
    simp [excUpdate_app] at h
    subst h
    constructor
    · simp [excArgs, excUpdW_data h1, memSet]
    · simp only [excUpdW_data h1]
      exact memGet_memSet_same _ _ _

end PyLean.TypeObj
