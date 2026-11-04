import PyLean.Itertools.TeeProps

/-!
`tee` with its re-entry guard: this is the mirror of
`teedataobject_getitem_lock_held` (Modules/itertoolsmodule.c:780-805), its
wrapper `teedataobject_getitem` (:808-815) and `tee_next` (:948-971, GIL build),
with the input able to call back into the tees. `hooks` holds, for successive
items, the operations performed after the item is taken and before it is returned
(as a `map` function does); they run through `tsRun`, the function that runs
top-level operations. The caller catches what they raise.

`GroupbyTee.lean` has the same functions without `running`, which is what the
simulation of the doc's linked list in `TeeProps.lean` runs on; `tsFold_pure`
shows the two coincide when nothing re-enters.

Also here: `itertools._tee` on an input that is not a tee, and `tee_clear` and
`tee_dealloc` with their weakref callbacks.
-/

namespace PyLean.Itertools

open PyLean

variable {α : Type} [Inhabited α]

/-- `RuntimeError` of :792-793. -/
def teeReenterError : PyExc := .named "RuntimeError" "cannot re-enter the tee iterator"

/-- The chain of `teedataobject`s as in `CTee`, with `running` (:734), the blocks
whose `tdo->running` is set; what successive `__next__` calls do; and the results
so far. -/
structure TeeS (α : Type) where
  it : Src α
  blocks : List (List α)
  tees : List (Nat × Nat)
  running : List Nat := []
  hooks : List (List TeeOp) := []
  log : List (NextRes α) := []

/-- `teedataobject_jumplink` (:769-778) as used by `tee_next` (:957-964). -/
def tsJump (t : TeeS α) (b i : Nat) : TeeS α × Nat × Nat :=
  if i ≥ LINKCELLS then
    let t := if b + 1 < t.blocks.length then t else { t with blocks := t.blocks ++ [[]] }
    (t, b + 1, 0)
  else (t, b, i)

/-- The Python code the input runs for an item. -/
def tsHook (run : List TeeOp → TeeS α → TeeS α) (t : TeeS α) : TeeS α :=
  match t.hooks with
  | [] => t
  | h :: hs => run h { t with hooks := hs }

/-- `teedataobject_getitem_lock_held` (:781-805) and the `to->index++` of
`tee_next` (:965-969): a stored value (:786-787), or for the lead iterator the
guard (:791-795), then `PyIter_Next` with `running` set (:796-798), which is
cleared before its result is looked at, so also when it failed. -/
def tsGetitem (run : List TeeOp → TeeS α → TeeS α) (t : TeeS α) (k b i : Nat) : NextRes α × TeeS α :=
  let blk := t.blocks.getD b []
  if i < blk.length then
    (.val (blk.getD i default), { t with tees := t.tees.set k (b, i + 1) })
  else if t.running.contains b then
    (.exc teeReenterError, t)
  else
    match t.it.next with
    | .done => (.stop, t)
    | .fail e rest => (.exc e, { t with it := rest })
    | .item v rest =>
      let t := tsHook run { t with it := rest, running := b :: t.running }
      let t := { t with running := t.running.erase b }
      (.val v, { t with blocks := t.blocks.set b (t.blocks.getD b [] ++ [v]),
                        tees := t.tees.set k (b, i + 1) })

/-- `tee_next` (:948-971, GIL build). -/
def tsNext (run : List TeeOp → TeeS α → TeeS α) (t : TeeS α) (k : Nat) : NextRes α × TeeS α :=
  let (b, i) := t.tees.getD k (0, 0)
  let (t, b, i) := tsJump t b i
  tsGetitem run { t with tees := t.tees.set k (b, i) } k b i

/-- One operation. As in `cTeeOps`, an index with no tee behind it is skipped; a
result joins the log when its call returns, so what a hook did comes first. -/
def tsOp (run : List TeeOp → TeeS α → TeeS α) : TeeOp → TeeS α → TeeS α
  | .next k, t =>
    if k < t.tees.length then
      let (r, t) := tsNext run t k
      { t with log := t.log ++ [r] }
    else t
  | .tee k m, t =>
    if k < t.tees.length then { t with tees := t.tees ++ List.replicate m (t.tees.getD k (0, 0)) }
    else t
  | .copy k, t =>
    if k < t.tees.length then { t with tees := t.tees ++ [t.tees.getD k (0, 0)] } else t
  | .ctor k, t =>
    -- `tee_fromiterable` on a tee copies it (:1059-1062)
    if k < t.tees.length then { t with tees := t.tees ++ [t.tees.getD k (0, 0)] } else t

def tsFold (run : List TeeOp → TeeS α → TeeS α) (ops : List TeeOp) (t : TeeS α) : TeeS α :=
  ops.foldl (fun t op => tsOp run op t) t

/-- Runs operations. Each hook is used once, so `hooks.length + 1` levels are
enough. -/
def tsRun : Nat → List TeeOp → TeeS α → TeeS α
  | 0, _, t => t
  | d + 1, ops, t => tsFold (tsRun d) ops t

/-- `tee_fromiterable` (:1051-1082) on an input that is not a tee: one fresh
block (`teedataobject_newinternal`, :752-766, `running = 0`), one iterator. A tee
input is the `ctor` operation. -/
def teeFromIterable (iterable : Obj α) (hooks : List (List TeeOp)) : Py (TeeS α) :=
  match getIter iterable with
  | .error e => .error e
  | .ok it => .ok { it := it, blocks := [[]], tees := [(0, 0)], hooks := hooks }

/-- The results of running `ops`, then the number of items pulled. -/
def tsResult (it : Src α) (hooks : List (List TeeOp)) (ops : List TeeOp) (t : TeeS α) :
    List (NextRes α) × Nat :=
  let t' := tsRun (hooks.length + 1) ops t
  (t'.log, it.items.length - t'.it.items.length)

/-- `itertools_tee_impl` (:1161-1196) on a non-tee input: `n` through the
`Py_ssize_t(allow_negative=False)` converter (Modules/clinic/itertoolsmodule.c.h:338-352),
`n == 0` returns `()` without touching the iterable, then
`tee_fromiterable` and `n - 1` calls of `tee_copy`. -/
def cTeeR (iterable : Obj α) (n : Int) (hooks : List (List TeeOp)) (ops : List TeeOp) :
    Py (List (NextRes α) × Nat) :=
  match asSsize n with
  | .error e => .error e
  | .ok n =>
    if n < 0 then .error (.valueError "n cannot be negative")
    else if !tupleNewOk n then .error memoryError
    else if n = 0 then .ok ([], 0)
    else match teeFromIterable iterable hooks with
      | .error e => .error e
      | .ok t => .ok (tsResult t.it hooks ops { t with tees := List.replicate n.toNat (0, 0) })

/-- `itertools__tee_impl` (:1093-1098) on an input that is not a tee. -/
def cTeeWrap (iterable : Obj α) (hooks : List (List TeeOp)) (ops : List TeeOp) :
    Py (List (NextRes α) × Nat) :=
  match teeFromIterable iterable hooks with
  | .error e => .error e
  | .ok t => .ok (tsResult t.it hooks ops t)

/-! ## When nothing re-enters this is the model of `GroupbyTee.lean` -/

/-- A `CTee` with nothing running and no hooks. -/
def ofC (c : CTee α) (log : List (NextRes α)) : TeeS α :=
  { it := c.it, blocks := c.blocks, tees := c.tees, log := log }

section Pure

variable (run : List TeeOp → TeeS α → TeeS α)

theorem tsGetitem_pure (c : CTee α) (log : List (NextRes α)) (k b i : Nat) :
    tsGetitem run (ofC c log) k b i = ((teeGetitem c k b i).1, ofC (teeGetitem c k b i).2 log) := by
  simp only [tsGetitem, teeGetitem, ofC, List.contains_nil, Bool.false_eq_true, if_false, tsHook]
  split
  · rfl
  · cases h : c.it.next <;> simp [ofC]

theorem tsNext_pure (c : CTee α) (log : List (NextRes α)) (k : Nat) :
    tsNext run (ofC c log) k = ((cTeeNext c k).1, ofC (cTeeNext c k).2 log) := by
  simp only [tsNext, cTeeNext, ofC, tsJump, teeJump]
  by_cases hi : (c.tees.getD k (0, 0)).2 ≥ LINKCELLS
  · by_cases hb : (c.tees.getD k (0, 0)).1 + 1 < c.blocks.length
    · simp only [hi, hb, if_true]
      exact tsGetitem_pure run ⟨c.it, c.blocks, c.tees.set k ((c.tees.getD k (0, 0)).1 + 1, 0)⟩ log k _ _
    · simp only [hi, hb, if_true, if_false]
      exact tsGetitem_pure run ⟨c.it, c.blocks ++ [[]], c.tees.set k ((c.tees.getD k (0, 0)).1 + 1, 0)⟩ log k _ _
  · simp only [hi, if_false]
    exact tsGetitem_pure run
      ⟨c.it, c.blocks, c.tees.set k ((c.tees.getD k (0, 0)).1, (c.tees.getD k (0, 0)).2)⟩ log k _ _

theorem tsFold_cons (op : TeeOp) (ops : List TeeOp) (t : TeeS α) :
    tsFold run (op :: ops) t = tsFold run ops (tsOp run op t) := rfl

/-- With no hooks the two models give the same results, the same way. -/
theorem tsFold_pure : ∀ (ops : List TeeOp) (c : CTee α) (log : List (NextRes α)),
    tsFold run ops (ofC c log) = ofC (cTeeOps c ops).2 (log ++ (cTeeOps c ops).1)
  | [], c, log => by simp [tsFold, cTeeOps]
  | .next k :: ops, c, log => by
    rw [tsFold_cons]
    by_cases hk : k < c.tees.length
    · have hs : tsOp run (.next k) (ofC c log) =
          ofC (cTeeNext c k).2 (log ++ [(cTeeNext c k).1]) := by
        simp only [tsOp, ofC] at *
        simp only [hk, if_true]
        have := tsNext_pure run c log k
        simp only [ofC] at this
        rw [this]
      rw [hs, tsFold_pure ops]
      simp [cTeeOps, hk]
    · have hs : tsOp run (.next k) (ofC c log) = ofC c log := by simp [tsOp, ofC, hk]
      rw [hs, tsFold_pure ops]
      simp [cTeeOps, hk]
  | .tee k m :: ops, c, log => by
    rw [tsFold_cons]
    by_cases hk : k < c.tees.length
    · have hs : tsOp run (.tee k m) (ofC c log) =
          ofC { c with tees := c.tees ++ List.replicate m (c.tees.getD k (0, 0)) } log := by
        simp [tsOp, ofC, hk]
      rw [hs, tsFold_pure ops]
      simp [cTeeOps, hk]
    · have hs : tsOp run (.tee k m) (ofC c log) = ofC c log := by simp [tsOp, ofC, hk]
      rw [hs, tsFold_pure ops]
      simp [cTeeOps, hk]
  | .copy k :: ops, c, log => by
    rw [tsFold_cons]
    by_cases hk : k < c.tees.length
    · have hs : tsOp run (.copy k) (ofC c log) =
          ofC { c with tees := c.tees ++ [c.tees.getD k (0, 0)] } log := by
        simp [tsOp, ofC, hk]
      rw [hs, tsFold_pure ops]
      simp [cTeeOps, hk]
    · have hs : tsOp run (.copy k) (ofC c log) = ofC c log := by simp [tsOp, ofC, hk]
      rw [hs, tsFold_pure ops]
      simp [cTeeOps, hk]
  | .ctor k :: ops, c, log => by
    rw [tsFold_cons]
    by_cases hk : k < c.tees.length
    · have hs : tsOp run (.ctor k) (ofC c log) =
          ofC { c with tees := c.tees ++ [c.tees.getD k (0, 0)] } log := by
        simp [tsOp, ofC, hk]
      rw [hs, tsFold_pure ops]
      simp [cTeeOps, hk]
    · have hs : tsOp run (.ctor k) (ofC c log) = ofC c log := by simp [tsOp, ofC, hk]
      rw [hs, tsFold_pure ops]
      simp [cTeeOps, hk]

end Pure

theorem cTeeR_pure (o : Obj α) (n : Int) (ops : List TeeOp) : cTeeR o n [] ops = cTee o n ops := by
  simp only [cTeeR, cTee, teeFromIterable]
  cases ha : asSsize n with
  | error e => rfl
  | ok v =>
    simp only
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · cases hi : getIter o with
          | error e => rfl
          | ok it =>
            simp only [tsResult, tsRun, List.length_nil]
            have h := tsFold_pure (α := α) (fun _ t => t) ops
              { it := it, blocks := [[]], tees := List.replicate v.toNat (0, 0) } []
            simp only [ofC] at h
            rw [h]
            simp [ofC]

/-! ## Properties -/

/-- `TeeDocAgree` for this model: with an input that does not re-enter, for every
`n` whose tuple fits, every input object and interleaving of operations, the
results and the items pulled are those of the doc's linked list. The hypothesis
that nothing re-enters is a precondition: the doc's pure Python `_tee` has no
guard, so a re-entrant input behaves differently there. -/
def TeeDocAgreeR : Prop :=
  ∀ (α : Type) [Inhabited α] (o : Obj α) (n : Int) (ops : List TeeOp), (0 ≤ n → tupleNewOk n = true) →
    pyAgree (cTeeR o n [] ops) (docTee o n ops)

theorem teeDocAgreeR_proven : TeeDocAgreeR := by
  intro α _ o n ops h
  rw [cTeeR_pure]
  exact teeDocAgree_proven α o n ops h

/-- A preserved `running` under a hook gives one for `tsGetitem`, whatever the hook. -/
theorem tsGetitem_running (run : List TeeOp → TeeS α → TeeS α)
    (hrun : ∀ ops t, (run ops t).running = t.running) (t : TeeS α) (k b i : Nat) :
    (tsGetitem run t k b i).2.running = t.running := by
  have hh : ∀ rest : Src α, (tsHook run { t with it := rest, running := b :: t.running }).running =
      b :: t.running := by
    intro rest
    simp only [tsHook]
    split
    · rfl
    · rw [hrun]
  simp only [tsGetitem]
  split
  · rfl
  · split
    · rfl
    · cases hn : t.it.next <;> simp [hh]

theorem tsNext_running (run : List TeeOp → TeeS α → TeeS α)
    (hrun : ∀ ops t, (run ops t).running = t.running) (t : TeeS α) (k : Nat) :
    (tsNext run t k).2.running = t.running := by
  simp only [tsNext, tsJump]
  by_cases hi : (t.tees.getD k (0, 0)).2 ≥ LINKCELLS
  · by_cases hb : (t.tees.getD k (0, 0)).1 + 1 < t.blocks.length
    · simp only [hi, hb, if_true]
      exact tsGetitem_running run hrun _ _ _ _
    · simp only [hi, hb, if_true, if_false]
      exact tsGetitem_running run hrun _ _ _ _
  · simp only [hi, if_false]
    exact tsGetitem_running run hrun _ _ _ _

theorem tsOp_running (run : List TeeOp → TeeS α → TeeS α)
    (hrun : ∀ ops t, (run ops t).running = t.running) (op : TeeOp) (t : TeeS α) :
    (tsOp run op t).running = t.running := by
  cases op with
  | next k =>
    simp only [tsOp]
    split
    · exact tsNext_running run hrun t k
    · rfl
  | tee k m => simp only [tsOp]; split <;> rfl
  | copy k => simp only [tsOp]; split <;> rfl
  | ctor k => simp only [tsOp]; split <;> rfl

theorem tsFold_running (run : List TeeOp → TeeS α → TeeS α)
    (hrun : ∀ ops t, (run ops t).running = t.running) :
    ∀ (ops : List TeeOp) (t : TeeS α), (tsFold run ops t).running = t.running
  | [], _ => rfl
  | op :: ops, t => by
    rw [tsFold_cons, tsFold_running run hrun ops, tsOp_running run hrun]

theorem tsRun_running : ∀ (d : Nat) (ops : List TeeOp) (t : TeeS α), (tsRun d ops t).running = t.running
  | 0, _, _ => rfl
  | d + 1, ops, t => tsFold_running (tsRun d) (tsRun_running d) ops t

/-- The flag cannot stick: for every state, hook and sequence of operations,
including inputs that raise and hooks that hit the guard, `running` ends as it
began (:796-798 clears it before looking at the result). So no later `next()`
gets a spurious `RuntimeError`. -/
def TeeRunningBalanced : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Nat) (ops : List TeeOp) (t : TeeS α),
    (tsRun d ops t).running = t.running

theorem teeRunningBalanced_proven : TeeRunningBalanced := by
  intro α _ d ops t
  exact tsRun_running d ops t

/-- The guard, for every state: `next()` on a tee at the frontier of a block whose
pull is in progress raises `RuntimeError` and takes nothing (:791-795). And it is
reached: an input whose `__next__` calls `next()` on the other tee gets that
exception, after which the outer `next()` still delivers its item. -/
def TeeReentryGuard : Prop :=
  (∀ (α : Type) [Inhabited α] (run : List TeeOp → TeeS α → TeeS α) (t : TeeS α) (k b i : Nat),
    k < t.tees.length → t.tees.getD k (0, 0) = (b, i) → i < LINKCELLS →
    (t.blocks.getD b []).length ≤ i → t.running.contains b = true →
    tsNext run t k = (.exc teeReenterError, t)) ∧
  (∀ (x y : Nat), cTeeR (.iter [x, y] none) 2 [[.next 1]] [.next 0] =
    .ok ([.exc teeReenterError, .val x], 1))

theorem teeReentryGuard_proven : TeeReentryGuard := by
  constructor
  · intro α _ run t k b i hk ht hi hl hr
    have hset : t.tees.set k (b, i) = t.tees := by
      rw [← ht]
      simp [List.set_eq_of_length_le, hk, List.getD_eq_getElem?_getD]
    have hge : ¬ i ≥ LINKCELLS := by omega
    simp only [tsNext, ht, tsJump, hge, if_false, tsGetitem, hset]
    have : ¬ i < (t.blocks.getD b []).length := by omega
    rw [if_neg this, if_pos hr]
  · intro x y
    rfl

/-- `itertools._tee(x)` on an input that is not a tee is `tee(x, 1)[0]`, for every
input, hook and sequence of operations; a non-iterable fails with `iter()`'s
TypeError. -/
def TeeWrapIsTeeOne : Prop :=
  ∀ (α : Type) [Inhabited α] (o : Obj α) (hooks : List (List TeeOp)) (ops : List TeeOp),
    cTeeWrap o hooks ops = cTeeR o 1 hooks ops ∧
    (∀ ty, o = .notIterable ty → cTeeWrap o hooks ops = .error (.typeError s!"'{ty}' object is not iterable"))

theorem teeWrapIsTeeOne_proven : TeeWrapIsTeeOne := by
  intro α _ o hooks ops
  constructor
  · have h1 : asSsize (1 : Int) = .ok 1 := asSsize_ok (by decide) (by decide)
    simp only [cTeeWrap, cTeeR, h1]
    simp only [show ¬ ((1 : Int) < 0) by decide, if_false]
    have h2 : tupleNewOk (1 : Int) = true := by decide
    simp only [h2, Bool.not_true, Bool.false_eq_true, if_false, show ¬ ((1 : Int) = 0) by decide]
    cases h : teeFromIterable o hooks with
    | error e => rfl
    | ok t =>
      have hT : t.tees = [(0, 0)] := by
        simp only [teeFromIterable] at h
        cases hi : getIter o with
        | error e => simp [hi] at h
        | ok it =>
          simp only [hi, Except.ok.injEq] at h
          rw [← h]
      simp [List.replicate, hT.symm]
  · intro ty h
    subst h
    rfl

/-! ## `tee_clear`, `tee_dealloc` -/

/-- An entry of `to->weakreflist`: `weakref.ref(t)` without a callback, or a
reference with callback number `id`. Proxies are not modelled. -/
inductive WRef where
  | basic
  | cb (id : Nat)
  deriving Repr, DecidableEq

/-- `insert_weakref` (Objects/weakrefobject.c:378-401) with `try_reuse_basic_ref`:
the basic reference is shared and stays at the head; a reference with a callback
goes right after it, or at the head when there is none. So the newest reference
with a callback comes first. -/
def wrInsert : WRef → List WRef → List WRef
  | .basic, .basic :: rest => .basic :: rest
  | .basic, l => .basic :: l
  | .cb i, .basic :: rest => .basic :: .cb i :: rest
  | .cb i, l => .cb i :: l

/-- What happened during the clear: a callback ran, seeing its reference already
dead, and if it raised, the exception went to `sys.unraisablehook`. -/
inductive ClearEvent where
  | called (id : Nat)
  | unraisable (id : Nat) (e : PyExc)
  deriving Repr, DecidableEq

/-- `PyObject_ClearWeakRefs` (Objects/weakrefobject.c:1036-1117): every reference
is cleared first (:1057-1066, :1085-1103), then the callbacks run in list order
(:1105-1111), and `handle_callback` (:1016-1027) does not let an exception out. -/
def clearWeakRefs (cb : Nat → Py Unit) : List WRef → List ClearEvent
  | [] => []
  | .basic :: rest => clearWeakRefs cb rest
  | .cb i :: rest =>
    (match cb i with
      | .ok _ => [.called i]
      | .error e => [.called i, .unraisable i e]) ++ clearWeakRefs cb rest

/-- The parts of a `teeobject` these two functions touch (:741-747). -/
structure TeeObj (β : Type) where
  dataobj : Option β
  weakreflist : List WRef

/-- `tee_clear` (:1101-1108): the callbacks run while `dataobj` is still set. It
returns 0 whatever they did. -/
def teeClear {β : Type} (cb : Nat → Py Unit) (t : TeeObj β) : TeeObj β × List ClearEvent :=
  let ev := if t.weakreflist != [] then clearWeakRefs cb t.weakreflist else []
  ({ dataobj := none, weakreflist := [] }, ev)

/-- `tee_dealloc` (:1111-1118): `tee_clear`; `PyObject_GC_UnTrack`, `PyObject_GC_Del`
and the type's reference have no effect a Python program sees here. -/
def teeDealloc {β : Type} (cb : Nat → Py Unit) (t : TeeObj β) : List ClearEvent := (teeClear cb t).2

/-- The callback ids that ran, in order. -/
def calledIds : List ClearEvent → List Nat
  | [] => []
  | .called i :: l => i :: calledIds l
  | .unraisable _ _ :: l => calledIds l

/-- The callback ids of a weakref list, in order. -/
def wrIds : List WRef → List Nat
  | [] => []
  | .basic :: l => wrIds l
  | .cb i :: l => i :: wrIds l

theorem wrIds_insert (w : WRef) (l : List WRef) :
    wrIds (wrInsert w l) = (match w with | .basic => wrIds l | .cb i => i :: wrIds l) := by
  cases w with
  | basic =>
    cases l with
    | nil => rfl
    | cons h t => cases h <;> rfl
  | cb i =>
    cases l with
    | nil => rfl
    | cons h t => cases h <;> rfl

theorem wrIds_build (refs : List WRef) (l : List WRef) :
    wrIds (refs.foldl (fun acc w => wrInsert w acc) l) = (wrIds refs).reverse ++ wrIds l := by
  induction refs generalizing l with
  | nil => simp [wrIds]
  | cons w rest ih =>
    simp only [List.foldl_cons]
    rw [ih, wrIds_insert]
    cases w <;> simp [wrIds]

theorem calledIds_clear (cb : Nat → Py Unit) : ∀ l : List WRef, calledIds (clearWeakRefs cb l) = wrIds l
  | [] => rfl
  | .basic :: l => by simp [clearWeakRefs, wrIds, calledIds_clear cb l]
  | .cb i :: l => by
    simp only [clearWeakRefs, wrIds]
    cases h : cb i <;> simp [calledIds, calledIds_clear cb l]

theorem clear_nonempty (cb : Nat → Py Unit) (l : List WRef) :
    (if l != [] then clearWeakRefs cb l else []) = clearWeakRefs cb l := by
  cases l <;> simp [clearWeakRefs]

/-- For references created in any order and any callbacks, which may raise:
destroying a tee runs each callback once, newest first, whether or not the others
raised; nothing raises out of it; `dataobj` and the list end up cleared; and a
second `tee_clear` runs nothing. -/
def TeeClearCallbacks : Prop :=
  ∀ (β : Type) (cb : Nat → Py Unit) (d : Option β) (refs : List WRef),
    let t : TeeObj β := ⟨d, refs.foldl (fun acc w => wrInsert w acc) []⟩
    calledIds (teeDealloc cb t) = (wrIds refs).reverse ∧
    (teeClear cb t).1.dataobj = none ∧ (teeClear cb t).1.weakreflist = [] ∧
    (teeClear cb (teeClear cb t).1).2 = []

theorem teeClearCallbacks_proven : TeeClearCallbacks := by
  intro β cb d refs
  have h := wrIds_build refs []
  simp only [wrIds, List.append_nil] at h
  refine ⟨?_, rfl, rfl, by simp [teeClear]⟩
  simp only [teeDealloc, teeClear, clear_nonempty, calledIds_clear, h]

end PyLean.Itertools
