import PyLean.TypeObj.ExcPropsBase

/-!
More properties of `BaseException`, `Objects/exceptions.c:52-505`: the success values of `__new__`
and the setters, and the refusals that `ExcPropsBase` leaves out.
-/

namespace PyLean.TypeObj

/-! ## `%.200s` -/

theorem truncUtf8_prefix (n : Nat) (cs : List Char) : truncUtf8 n cs <+: cs := by
  induction cs generalizing n with
  | nil => simp [truncUtf8]
  | cons c cs ih =>
    unfold truncUtf8
    split
    · exact List.cons_prefix_cons.mpr ⟨rfl, ih _⟩
    · exact List.nil_prefix

/-- The UTF-8 length of a list of characters. -/
def utf8Len (cs : List Char) : Nat := (cs.map Char.utf8Size).sum

theorem truncUtf8_fits (n : Nat) (cs : List Char) : utf8Len (truncUtf8 n cs) ≤ n := by
  induction cs generalizing n with
  | nil => simp [truncUtf8, utf8Len]
  | cons c cs ih =>
    unfold truncUtf8
    split
    · rename_i h
      have := ih (n - c.utf8Size)
      simp only [utf8Len, List.map_cons, List.sum_cons] at this ⊢
      omega
    · simp [utf8Len]

/-- Maximality: either every character was kept, or the next one does not fit. -/
theorem truncUtf8_max (n : Nat) (cs : List Char) :
    truncUtf8 n cs = cs ∨
      ∃ c rest, cs.drop (truncUtf8 n cs).length = c :: rest ∧
        n < utf8Len (truncUtf8 n cs) + c.utf8Size := by
  induction cs generalizing n with
  | nil => simp [truncUtf8]
  | cons c cs ih =>
    unfold truncUtf8
    split
    · rename_i h
      rcases ih (n - c.utf8Size) with he | ⟨d, rest, hd, hlt⟩
      · left; rw [he]
      · right
        refine ⟨d, rest, ?_, ?_⟩
        · simpa using hd
        · simp only [utf8Len, List.map_cons, List.sum_cons] at hlt ⊢
          omega
    · rename_i h
      right
      exact ⟨c, cs, by simp, by simp [utf8Len]; omega⟩

/-! ## `BaseException_new`, `BaseException_init`, `BaseException_vectorcall` -/

/-- **`BaseException.__new__` stores `args` and nothing else.** The new object has class `t`,
the given `args`, a NULL traceback, cause and context, `suppress_context` 0, no notes, no
members and no instance dict (`:56-68`), and no keyword is looked at. This is what a subclass
whose `__init__` does not call `super().__init__` sees: `args` is set by `__new__` alone. -/
def BaseExceptionNewStores : Prop :=
  ∀ (w : World) (t : Addr) (args : List Val), ∃ (a : Addr) (w' : World),
    baseExceptionNew t args w = .ok (.obj a) w' ∧ IsExc w' a { args := args } ∧
    typeOf w' (.obj a) = t ∧ instDictAddr w' (.obj a) = none ∧
    (excDataOf w' (.obj a)).traceback = .none ∧ (excDataOf w' (.obj a)).cause = none ∧
    (excDataOf w' (.obj a)).context = none ∧ (excDataOf w' (.obj a)).suppressContext = false ∧
    excArgs w' (.obj a) = args

theorem baseExceptionNewStores_proven : BaseExceptionNewStores := by
  intro w t args
  have hx := isExc_alloc w t { args := args }
  refine ⟨w.heap.size, _, by simp [baseExceptionNew, alloc_app], hx, ?_, ?_, ?_⟩
  · simp [typeOf, get_push_size]
  · simp [instDictAddr, get_push_size]
  · simp [hx.data, excArgs]

/-- **`BaseException.__init__` refuses keywords and otherwise replaces `args`.** Any keyword is
`TypeError: <tp_name>() takes no keyword arguments` with the name cut by `%.200s` (the longest
prefix of whole characters that fits in 200 bytes, by `truncUtf8_prefix`, `_fits` and `_max`),
before anything is changed; with no keyword, `args` is replaced and every other field kept. -/
def BaseExceptionInitKw : Prop :=
  (∀ (self : Val) (args : List Val) (kw : Kw) (w : World), kw ≠ [] →
    baseExceptionInit self args kw w =
      .err (.exc B.TypeError (noKwMsg (typeName w self)) none) w) ∧
  (∀ (a : Addr) (d : ExcData) (args : List Val) (w : World), IsExc w a d →
    ∃ w', baseExceptionInit (.obj a) args [] w = .ok () w' ∧
      excDataOf w' (.obj a) = { d with args := args })

theorem baseExceptionInitKw_proven : BaseExceptionInitKw := by
  refine ⟨?_, ?_⟩
  · intro self args kw w hk
    have : kw.isEmpty = false := by cases kw <;> simp_all
    simp [baseExceptionInit, argNoKeywords, this, typeErr, raiseC]
  · intro a d args w hx
    refine ⟨excUpdW w a (fun d => { d with args := args }), ?_, excUpdW_data hx _⟩
    simp [baseExceptionInit, argNoKeywords, excUpdate_app]

/-- **`BaseException_vectorcall` refuses keyword names with the whole name** (`%s` in
`_PyArg_NoKwnames`, `Python/getargs.c:2991`) before allocating, and with none builds the object
`BaseException_new` builds. -/
def BaseExceptionVectorcallKw : Prop :=
  (∀ (t : Addr) (args : List Val) (kw : Kw) (w : World), kw ≠ [] →
    baseExceptionVectorcall t args kw w =
      .err (.exc B.TypeError s!"{tpName w t}() takes no keyword arguments" none) w) ∧
  (∀ (t : Addr) (args : List Val) (w : World),
    baseExceptionVectorcall t args [] w = baseExceptionNew t args w)

theorem baseExceptionVectorcallKw_proven : BaseExceptionVectorcallKw := by
  refine ⟨?_, ?_⟩
  · intro t args kw w hk
    have : kw.isEmpty = false := by cases kw <;> simp_all
    simp [baseExceptionVectorcall, argNoKwnames, this, typeErr, raiseC]
  · intro t args w
    simp [baseExceptionVectorcall, argNoKwnames, baseExceptionNew]

/-! ## `__traceback__` and `with_traceback` -/

/-- **`__traceback__ = tb` stores it, `= None` clears it, anything else is refused**, and
`with_traceback(tb)` is the same assignment followed by `return self`. On success every other
field is unchanged, and the getter reads the stored value back (`None` for NULL). -/
def TracebackSetStores : Prop :=
  ∀ (a : Addr) (d : ExcData) (w : World), IsExc w a d →
    (∀ tb : Val, tracebackCheck w tb = true →
      baseExceptionTracebackSet (.obj a) (some tb) w = .ok () (excUpdW w a fun d => { d with traceback := tb }) ∧
      baseExceptionWithTraceback (.obj a) tb w = .ok (.obj a) (excUpdW w a fun d => { d with traceback := tb }) ∧
      excDataOf (excUpdW w a fun d => { d with traceback := tb }) (.obj a) = { d with traceback := tb } ∧
      baseExceptionTracebackGet (excDataOf (excUpdW w a fun d => { d with traceback := tb }) (.obj a)) = tb) ∧
    (baseExceptionTracebackSet (.obj a) (some .none) w = .ok () (excUpdW w a fun d => { d with traceback := .none }) ∧
      baseExceptionWithTraceback (.obj a) .none w = .ok (.obj a) (excUpdW w a fun d => { d with traceback := .none }) ∧
      baseExceptionTracebackGet (excDataOf (excUpdW w a fun d => { d with traceback := .none }) (.obj a)) = .none) ∧
    (∀ v : Val, tracebackCheck w v = false → v ≠ .none →
      baseExceptionWithTraceback (.obj a) v w =
        .err (.exc B.TypeError "__traceback__ must be a traceback or None" none) w)

theorem tracebackCheck_none (w : World) : tracebackCheck w .none = false := by
  simp [tracebackCheck, typeOf]
  decide

theorem tracebackSetStores_proven : TracebackSetStores := by
  intro a d w hx
  refine ⟨?_, ?_, ?_⟩
  · intro tb ht
    refine ⟨?_, ?_, excUpdW_data hx _, ?_⟩
    · simp [baseExceptionTracebackSet, ht, excUpdate_app]
    · simp [baseExceptionWithTraceback, baseExceptionTracebackSet, ht, excUpdate_app]
    · simp [baseExceptionTracebackGet, excUpdW_data hx]
  · refine ⟨?_, ?_, ?_⟩
    · simp [baseExceptionTracebackSet, tracebackCheck_none, Val.is, excUpdate_app]
    · simp [baseExceptionWithTraceback, baseExceptionTracebackSet, tracebackCheck_none, Val.is,
        excUpdate_app]
    · simp [baseExceptionTracebackGet, excUpdW_data hx]
  · intro v hv hn
    have hn' : v.is .none = false := by
      cases v <;> simp_all [Val.is]
    simp [baseExceptionWithTraceback, baseExceptionTracebackSet, hv, hn', typeErr, raiseC]

/-! ## `__context__` and `__cause__` -/

/-- **`__context__` and `__cause__` cannot be deleted, and take only `None` or an exception.**
`del e.__context__` and `del e.__cause__` are `TypeError`s (`:442-444`, `:486-488`), as is a value
that is not an exception instance (`:447-450`, `:491-494`); all leave the world alone. -/
def ChainSetRefusals : Prop :=
  (∀ (self : Val) (w : World), baseExceptionContextSet self none w =
    .err (.exc B.TypeError "__context__ may not be deleted" none) w) ∧
  (∀ (self : Val) (w : World), baseExceptionCauseSet self none w =
    .err (.exc B.TypeError "__cause__ may not be deleted" none) w) ∧
  (∀ (self v : Val) (w : World), v ≠ .none → excInstanceCheck w v = false →
    baseExceptionContextSet self (some v) w =
      .err (.exc B.TypeError "exception context must be None or derive from BaseException" none) w) ∧
  (∀ (self v : Val) (w : World), v ≠ .none → excInstanceCheck w v = false →
    baseExceptionCauseSet self (some v) w =
      .err (.exc B.TypeError "exception cause must be None or derive from BaseException" none) w)

theorem chainSetRefusals_proven : ChainSetRefusals := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro self w
    simp [baseExceptionContextSet, typeErr, raiseC]
  · intro self w
    simp [baseExceptionCauseSet, typeErr, raiseC]
  · intro self v w hn hi
    have hn' : v.is .none = false := by cases v <;> simp_all [Val.is]
    simp [baseExceptionContextSet, hn', hi, typeErr, raiseC]
  · intro self v w hn hi
    have hn' : v.is .none = false := by cases v <;> simp_all [Val.is]
    simp [baseExceptionCauseSet, hn', hi, typeErr, raiseC]

/-! ## `args` -/

/-- The items an iterator yields before it is exhausted, and the world it leaves. -/
inductive Yields (rt : Rt) (it : Val) : List Val → World → World → Prop where
  | nil {w w' : World} : rt.iterNext it w = .ok none w' → Yields rt it [] w w'
  | cons {x : Val} {xs : List Val} {w w1 w2 : World} :
      rt.iterNext it w = .ok (some x) w1 → Yields rt it xs w1 w2 → Yields rt it (x :: xs) w w2

theorem excCollect_yields {rt : Rt} {it : Val} {xs : List Val} {w w' : World}
    (h : Yields rt it xs w w') : ∀ fuel, xs.length < fuel → excCollect rt it fuel w = .ok xs w' := by
  induction h with
  | nil hn =>
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ f => simp [excCollect, hn]
  | cons hn _ ih =>
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ f =>
      simp only [List.length_cons] at hf
      simp [excCollect, hn, ih f (by omega)]

/-- **`e.args = x` stores `tuple(x)` and `e.args` reads it back.** `PySequence_Tuple` (`:360`)
takes an exact tuple as it is and an exact list's items without running code; anything else is
iterated: `iter(x)`, then `next` until exhaustion, in the worlds each step leaves. A raise from
`iter` or from any `next` is the setter's result, with no write. On success the getter returns the
tuple of those items and the other fields are kept. `xs.length < excIterFuel` is the model's loop
bound, not a Python limit; `IsExc w1 a d` says `self` is still an exception after the iteration
(a type invariant: no code can change an object's layout). -/
def ArgsSetGet : Prop :=
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (v : Val) (xs : List Val) (w w1 : World),
    excSeqTuple rt v w = .ok xs w1 → IsExc w1 a d →
    baseExceptionArgsSet rt (.obj a) (some v) w = .ok () (excUpdW w1 a fun d => { d with args := xs }) ∧
    excDataOf (excUpdW w1 a fun d => { d with args := xs }) (.obj a) = { d with args := xs } ∧
    baseExceptionArgsGet (excDataOf (excUpdW w1 a fun d => { d with args := xs }) (.obj a)) = .tuple xs) ∧
  (∀ (rt : Rt) (self v : Val) (e : PyErr) (w w1 : World), excSeqTuple rt v w = .err e w1 →
    baseExceptionArgsSet rt self (some v) w = .err e w1) ∧
  (∀ (rt : Rt) (xs : List Val) (w : World), excSeqTuple rt (.tuple xs) w = .ok xs w) ∧
  (∀ (rt : Rt) (l : Addr) (o : Obj) (xs : List Val) (w : World),
    w.get l = .val o → o.cls = B.list → o.body = .list xs → excSeqTuple rt (.obj l) w = .ok xs w) ∧
  (∀ (rt : Rt) (v it : Val) (xs : List Val) (w w1 w2 : World),
    (∀ ys, v ≠ .tuple ys) → typeOf w v ≠ B.list →
    rt.getIter v w = .ok it w1 → Yields rt it xs w1 w2 → xs.length < excIterFuel →
    excSeqTuple rt v w = .ok xs w2) ∧
  (∀ (rt : Rt) (v : Val) (e : PyErr) (w w1 : World),
    (∀ ys, v ≠ .tuple ys) → typeOf w v ≠ B.list → rt.getIter v w = .err e w1 →
    excSeqTuple rt v w = .err e w1) ∧
  (∀ (rt : Rt) (v it : Val) (pre : List Val) (e : PyErr) (w w1 w2 w3 : World),
    (∀ ys, v ≠ .tuple ys) → typeOf w v ≠ B.list →
    rt.getIter v w = .ok it w1 → Yields' rt it pre w1 w2 → rt.iterNext it w2 = .err e w3 →
    pre.length < excIterFuel →
    excSeqTuple rt v w = .err e w3)
where
  /-- `pre` yielded, iterator not yet exhausted. -/
  Yields' (rt : Rt) (it : Val) : List Val → World → World → Prop
    | [], w, w' => w = w'
    | x :: xs, w, w' => ∃ w1, rt.iterNext it w = .ok (some x) w1 ∧ Yields' rt it xs w1 w'

theorem excCollect_raise {rt : Rt} {it : Val} {e : PyErr} :
    ∀ (pre : List Val) (w w2 w3 : World), ArgsSetGet.Yields' rt it pre w w2 →
      rt.iterNext it w2 = .err e w3 → ∀ fuel, pre.length < fuel → excCollect rt it fuel w = .err e w3 := by
  intro pre
  induction pre with
  | nil =>
    intro w w2 w3 hy hn fuel hf
    simp only [ArgsSetGet.Yields'] at hy
    subst hy
    cases fuel with
    | zero => simp at hf
    | succ f => simp [excCollect, hn]
  | cons x xs ih =>
    intro w w2 w3 hy hn fuel hf
    obtain ⟨w1, h1, hy⟩ := hy
    cases fuel with
    | zero => simp at hf
    | succ f =>
      simp only [List.length_cons] at hf
      simp [excCollect, h1, ih w1 w2 w3 hy hn f (by omega)]

theorem excSeqTuple_iter (rt : Rt) (v : Val) (w : World) (hv : ∀ ys, v ≠ .tuple ys)
    (hl : typeOf w v ≠ B.list) :
    excSeqTuple rt v w = (do let it ← rt.getIter v; excCollect rt it excIterFuel) w := by
  have hb : (typeOf w v == B.list) = false := by simpa using hl
  unfold excSeqTuple
  split
  · rename_i ys; exact absurd rfl (hv ys)
  · simp only [M.bind_app, getW_app]
    cases listOf w v <;> simp [hb]

theorem argsSetGet_proven : ArgsSetGet := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rt a d v xs w w1 hs hx
    refine ⟨?_, excUpdW_data hx _, ?_⟩
    · simp [baseExceptionArgsSet, hs, excUpdate_app]
    · simp [baseExceptionArgsGet, excUpdW_data hx]
  · intro rt self v e w w1 hs
    simp [baseExceptionArgsSet, hs]
  · intro rt xs w
    rfl
  · intro rt l o xs w hc hcls hb
    simp [excSeqTuple, listOf, payloadOf, hc, hb, typeOf, hcls]
  · intro rt v it xs w w1 w2 hv hl hi hy hf
    rw [excSeqTuple_iter rt v w hv hl]
    simp [hi, excCollect_yields hy _ hf]
  · intro rt v e w w1 hv hl hi
    rw [excSeqTuple_iter rt v w hv hl]
    simp [hi]
  · intro rt v it pre e w w1 w2 w3 hv hl hi hy hn hf
    rw [excSeqTuple_iter rt v w hv hl]
    simp [hi, excCollect_raise pre w1 w2 w3 hy hn _ hf]

/-! ## `add_note` -/

/-- **`add_note` creates `__notes__` when it is missing and refuses one that is not a list.**
After the `str` check, a failed `__notes__` lookup is the result. When the lookup finds nothing,
a new empty list is made and assigned with `setattr` (which may run a user `__setattr__`, and that
may change the list); if that fails, it is the result; otherwise the list ends with the note
(`:297-306`, `:312`). When `__notes__` is found and is not a list, the result is
`TypeError: Cannot add note: __notes__ is not a list` (`:307-311`), with nothing changed after
the lookup. -/
def AddNoteBranches : Prop :=
  (∀ (rt : Rt) (self note : Val) (e : PyErr) (w w1 : World), (strOf w note).isSome →
    rt.getOptionalAttr self "__notes__" w = .err e w1 → baseExceptionAddNote rt self note w = .err e w1) ∧
  (∀ (rt : Rt) (self note : Val) (w w1 w2 : World) (o : Obj) (ys : List Val),
    (strOf w note).isSome → rt.getOptionalAttr self "__notes__" w = .ok none w1 →
    rt.setAttr self "__notes__" (some (.obj w1.heap.size))
      { w1 with heap := w1.heap.push (.val { cls := B.list, body := .list [] }) } = .ok () w2 →
    w2.get w1.heap.size = .val o → o.body = .list ys → w1.heap.size < w2.heap.size →
    ∃ w', baseExceptionAddNote rt self note w = .ok .none w' ∧
      listOf w' (.obj w1.heap.size) = some (ys ++ [note])) ∧
  (∀ (rt : Rt) (self note : Val) (e : PyErr) (w w1 w2 : World),
    (strOf w note).isSome → rt.getOptionalAttr self "__notes__" w = .ok none w1 →
    rt.setAttr self "__notes__" (some (.obj w1.heap.size))
      { w1 with heap := w1.heap.push (.val { cls := B.list, body := .list [] }) } = .err e w2 →
    baseExceptionAddNote rt self note w = .err e w2) ∧
  (∀ (rt : Rt) (self note n : Val) (w w1 : World),
    (strOf w note).isSome → rt.getOptionalAttr self "__notes__" w = .ok (some n) w1 →
    listOf w1 n = none →
    baseExceptionAddNote rt self note w =
      .err (.exc B.TypeError "Cannot add note: __notes__ is not a list" none) w1)

theorem addNoteBranches_proven : AddNoteBranches := by
  have hs' : ∀ (w : World) (note : Val), (strOf w note).isSome → (strOf w note).isNone = false := by
    intro w note h; cases hh : strOf w note <;> simp_all
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro rt self note e w w1 hs hg
    simp only [baseExceptionAddNote, M.bind_app, getW_app]
    simp [hs' w note hs, hg]
  · intro rt self note w w1 w2 o ys hs hg hset hc hb hl
    have hlist : listOf w2 (.obj w1.heap.size) = some ys := by simp [listOf, payloadOf, hc, hb]
    refine ⟨w2.setCell w1.heap.size (.val { o with body := .list (ys ++ [note]) }), ?_, ?_⟩
    · simp only [baseExceptionAddNote, M.bind_app, getW_app]
      simp [hs' w note hs, hg, alloc_app, allocCell, hset, modObj, hlist, hc]
    · simp [listOf, payloadOf, get_setCell_same _ _ _ hl]
  · intro rt self note e w w1 w2 hs hg hset
    simp only [baseExceptionAddNote, M.bind_app, getW_app]
    simp [hs' w note hs, hg, alloc_app, allocCell, hset]
  · intro rt self note n w w1 hs hg hl
    simp only [baseExceptionAddNote, M.bind_app, getW_app]
    simp [hs' w note hs, hg, hl, typeErr, raiseC]

/-! ## `BaseException_clear`, seen through the `MemoryError` freelist -/

/-- **`BaseException_clear` empties the references and keeps the rest.** A `MemoryError` taken
from the freelist has no args, notes, traceback, cause or context (`:128-133`), whatever the dead
object held; its `suppress_context` and other fields are what the dead object had, which is the
refuted `typeobj-exc-memoryerror-freelist-fresh`. An identity `clear` fails the first part. -/
def BaseExceptionClearFields : Prop :=
  ∀ (d : ExcData) (s : MemFreelist) (b : Bool) (args : List Val), s.length < memerrorsSave →
    ∃ r, (getMemoryError b args (memoryErrorDealloc true d s)).1 = .reused r ∧
      r.args = [] ∧ r.notes = none ∧ r.traceback = .none ∧ r.cause = none ∧ r.context = none ∧
      r.suppressContext = d.suppressContext ∧ r.members = d.members

theorem baseExceptionClearFields_proven : BaseExceptionClearFields := by
  intro d s b args hs
  refine ⟨{ baseExceptionClear d with args := [] }, ?_, ?_⟩
  · simp [memoryErrorDealloc, hs, getMemoryError]
  · simp [baseExceptionClear]

end PyLean.TypeObj
