import PyLean.TypeObj.ExcPropsGroup

/-!
More properties of `BaseExceptionGroup`, `Objects/exceptions.c:882-1738`: what `__new__` stores
and refuses, the list form of `repr`, the matcher's tuple case and predicate branch, the
`__notes__` copy of `exceptiongroup_subset`, and the `except*` helpers.
-/

namespace PyLean.TypeObj

/-! ## `BaseExceptionGroup_new` -/

theorem argCount_eq (f : String) (n : Nat) (w : World) :
    argCount (some f) n n n w = .ok () w := by
  simp [argCount]

theorem argU_ok (f : Option String) (i : Nat) (v : Val) (s : String) (w : World)
    (h : strOf w v = some s) : argU f i v w = .ok () w := by
  simp [argU, h]

/-- **`BaseExceptionGroup.__new__` refuses, in order**: a count other than two
(`PyArg_ParseTuple`'s arity error, `:892-897`), a message that is not a `str` (format `U`), and a
second argument that is not a sequence (`:899-904`), each before any user code runs. -/
def EgNewRefusals : Prop :=
  (∀ (rt : Rt) (t : Addr) (args : List Val) (w : World), args.length ≠ 2 →
    baseExceptionGroupNew rt t args w =
      .err (.exc B.TypeError
        s!"BaseExceptionGroup.__new__() takes exactly 2 arguments ({args.length} given)" none) w) ∧
  (∀ (rt : Rt) (t : Addr) (m ex : Val) (w : World), strOf w m = none →
    baseExceptionGroupNew rt t [m, ex] w =
      .err (.exc B.TypeError
        s!"BaseExceptionGroup.__new__() argument 1 must be str, not {excArgName w m}" none) w) ∧
  (∀ (rt : Rt) (t : Addr) (m ex : Val) (s : String) (w : World), strOf w m = some s →
    excSeqCheck w ex = false →
    baseExceptionGroupNew rt t [m, ex] w =
      .err (.exc B.TypeError "second argument (exceptions) must be a sequence" none) w)

theorem egNewRefusals_proven : EgNewRefusals := by
  refine ⟨?_, ?_, ?_⟩
  · intro rt t args w h
    have h1 : (decide (args.length < 2) || decide (2 < args.length)) = true := by
      simp; omega
    have hlt : ¬ args.length < 2 → 2 < args.length := by omega
    simp only [baseExceptionGroupNew, egNewParse, argCount, M.bind_app]
    by_cases h2 : args.length < 2
    · simp [h2, typeErr, raiseC]
      rfl
    · simp [h2, hlt h2, typeErr, raiseC]
      rfl
  · intro rt t m ex w h
    simp [baseExceptionGroupNew, egNewParse, argCount_eq, argU, h, typeErr, raiseC]
    rfl
  · intro rt t m ex s w h1 h2
    simp only [baseExceptionGroupNew, egNewParse, M.bind_app, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.reduceAdd, argCount_eq]
    simp [argU_ok _ _ _ _ _ h1, h2, typeErr, raiseC]

/-- **What `BaseExceptionGroup.__new__` stores.** On success the new object has the class the
checks chose, `args` as passed (`BaseException_new`, `:993`), the message, the items of
`tuple(exceptions)` and no saved string when `exceptions` is a list or a tuple; for any other
sequence the `repr` taken before the conversion is saved (`:906-916`), so `repr(eg)` shows the
sequence as it was. The conversion and the `isinstance` checks may run user code; each step runs
in the world the previous one left. A version that refuses every nested `BaseException`, or
stores the wrong items, fails. -/
def EgNewStores : Prop :=
  (∀ (rt : Rt) (t : Addr) (m ex : Val) (s : String) (xs : List Val) (nested : Bool) (cls : Addr)
      (w w1 w2 : World),
    strOf w m = some s → excSeqCheck w ex = true →
    ((listOf w ex).isSome || (tupleOf w ex).isSome) = true →
    excSeqTuple rt ex w = .ok xs w1 → xs ≠ [] → egCheckItems rt 0 false xs w1 = .ok nested w2 →
    egChooseClass t nested w2 = .ok cls w2 →
    ∃ w', baseExceptionGroupNew rt t [m, ex] w = .ok (.obj w2.heap.size) w' ∧
      IsExc w' w2.heap.size { args := [m, ex], egMessage := some m, egExceptions := xs } ∧
      typeOf w' (.obj w2.heap.size) = cls) ∧
  (∀ (rt : Rt) (t : Addr) (m ex : Val) (s r : String) (xs : List Val) (nested : Bool) (cls : Addr)
      (w w0 w1 w2 : World),
    strOf w m = some s → excSeqCheck w ex = true →
    ((listOf w ex).isSome || (tupleOf w ex).isSome) = false →
    rt.repr ex w = .ok r w0 →
    excSeqTuple rt ex w0 = .ok xs w1 → xs ≠ [] → egCheckItems rt 0 false xs w1 = .ok nested w2 →
    egChooseClass t nested w2 = .ok cls w2 →
    ∃ w', baseExceptionGroupNew rt t [m, ex] w = .ok (.obj w2.heap.size) w' ∧
      IsExc w' w2.heap.size
        { args := [m, ex], egMessage := some m, egExceptions := xs, egExcsStr := some r } ∧
      typeOf w' (.obj w2.heap.size) = cls)

theorem egNewStores_proven : EgNewStores := by
  refine ⟨?_, ?_⟩
  · intro rt t m ex s xs nested cls w w1 w2 hs hq hl h1 hne h2 h3
    have hne' : xs.isEmpty = false := by cases xs <;> simp_all
    refine ⟨_, ?_, isExc_alloc w2 cls _, by simp [typeOf, get_push_size]⟩
    simp only [baseExceptionGroupNew, egNewParse, M.bind_app, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.reduceAdd, argCount_eq, getW_app]
    simp [argU_ok _ _ _ _ _ hs, hq, hl, h1, hne, h2, h3, alloc_app]
  · intro rt t m ex s r xs nested cls w w0 w1 w2 hs hq hl h0 h1 hne h2 h3
    have hne' : xs.isEmpty = false := by cases xs <;> simp_all
    refine ⟨_, ?_, isExc_alloc w2 cls _, by simp [typeOf, get_push_size]⟩
    simp only [baseExceptionGroupNew, egNewParse, M.bind_app, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.reduceAdd, argCount_eq, getW_app]
    simp [argU_ok _ _ _ _ _ hs, hq, hl, h0, h1, hne, h2, h3, alloc_app]

/-! ## `repr` -/

/-- **`repr(eg)` shows a list when `args[1]` is a list.** With no saved string, two `args` and a
list second, the exceptions are shown as a new list of `eg.exceptions` (`:1099-1107`), not as the
tuple: `ExceptionGroup('m', [ValueError(1)])`. With `EgReprAnyArgs`, both forms are pinned. -/
def EgReprListForm : Prop :=
  ∀ (rt : Rt) (self a0 a1 : Val) (r m : String) (w w1 w2 : World),
    (excDataOf w self).egExcsStr = none → (excDataOf w self).args = [a0, a1] →
    (listOf w a1).isSome = true →
    rt.repr (.obj w.heap.size)
        { w with heap := w.heap.push (.val { cls := B.list, body := .list (excDataOf w self).egExceptions }) } =
      .ok r w1 →
    rt.repr ((excDataOf w self).egMessage.getD .none) w1 = .ok m w2 →
    baseExceptionGroupRepr rt self w = .ok (.str s!"{pyTypeName w1 (typeOf w1 self)}({m}, {r})") w2

theorem egReprListForm_proven : EgReprListForm := by
  intro rt self a0 a1 r m w w1 w2 h1 h2 h3 h4 h5
  have hl : egArgsShowList w (excDataOf w self) = true := by
    simp [egArgsShowList, h2, h3]
  simp only [baseExceptionGroupRepr, M.bind_app, getW_app, h1, hl, if_true, alloc_app]
  simp only [h4, h5]
  rfl

/-! ## The matcher -/

/-- **`get_matcher_type` refuses a tuple holding a non-class**, and any other value that is
neither a non-class callable nor an exception class (`:1260-1275`): every item must pass
`PyExceptionClass_Check`, so `(ValueError, 1)` is refused even though one item is a class. The
hypotheses are what the builtin `tuple` type is: not callable, not a class. -/
def GetMatcherTypeRefuses : Prop :=
  (∀ (xs : List Val) (w : World), excCallableCheck w (.tuple xs) = false →
    excClassCheck w (.tuple xs) = false → xs.all (excClassCheck w) = false →
    getMatcherType (.tuple xs) w = .err (.exc B.TypeError
      "expected an exception type, a tuple of exception types, or a callable (other than a class)" none) w) ∧
  (∀ (v : Val) (w : World), (∀ xs, v ≠ .tuple xs) →
    (excCallableCheck w v && !typeCheck w v) = false → excClassCheck w v = false →
    getMatcherType v w = .err (.exc B.TypeError
      "expected an exception type, a tuple of exception types, or a callable (other than a class)" none) w)

theorem getMatcherTypeRefuses_proven : GetMatcherTypeRefuses := by
  refine ⟨?_, ?_⟩
  · intro xs w h1 h2 h3
    have h3' : ¬ ∀ x ∈ xs, excClassCheck w x = true := by
      intro h
      rw [List.all_eq_true.mpr h] at h3
      cases h3
    simp only [getMatcherType, M.bind_app, getW_app, h1, h2, Bool.false_and, Bool.false_eq_true,
      if_false]
    simp [List.all_eq_true, h3', typeErr, raiseC]
  · intro v w h1 h2 h3
    have h2' : ¬ (excCallableCheck w v = true ∧ typeCheck w v = false) := by
      intro ⟨a, b⟩; simp [a, b] at h2
    cases v with
    | tuple xs => exact absurd rfl (h1 xs)
    | _ => simp [getMatcherType, h2', h3, typeErr, raiseC]

/-- **The predicate branch of `exceptiongroup_split_check_match`**: the predicate is called with
the exception, and its result's truth value is the answer (`:1289-1298`); a raise from the call
or from `bool()` of the result is the result, in the world it left. Matching by type runs no code
and, for a tuple, tests each class (`PyErr_GivenExceptionMatches`). -/
def SplitCheckMatchBranches : Prop :=
  (∀ (rt : Rt) (exc mv r : Val) (b : Bool) (w w1 w2 : World),
    rt.call mv [exc] [] w = .ok r w1 → rt.isTrue r w1 = .ok b w2 →
    splitCheckMatch rt exc .byPredicate mv w = .ok b w2) ∧
  (∀ (rt : Rt) (exc mv : Val) (e : PyErr) (w w1 : World),
    rt.call mv [exc] [] w = .err e w1 → splitCheckMatch rt exc .byPredicate mv w = .err e w1) ∧
  (∀ (rt : Rt) (exc mv r : Val) (e : PyErr) (w w1 w2 : World),
    rt.call mv [exc] [] w = .ok r w1 → rt.isTrue r w1 = .err e w2 →
    splitCheckMatch rt exc .byPredicate mv w = .err e w2) ∧
  (∀ (rt : Rt) (exc : Val) (xs : List Val) (w : World),
    splitCheckMatch rt exc .byType (.tuple xs) w = .ok (xs.any (givenMatchesClass w exc)) w)

theorem splitCheckMatchBranches_proven : SplitCheckMatchBranches := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro rt exc mv r b w w1 w2 h1 h2
    simp [splitCheckMatch, h1, h2]
  · intro rt exc mv e w w1 h1
    simp [splitCheckMatch, h1]
  · intro rt exc mv r e w w1 w2 h1 h2
    simp [splitCheckMatch, h1, h2]
  · intro rt exc xs w
    simp [splitCheckMatch, givenExceptionMatches, tupleOf]

/-! ## `exceptiongroup_subset`: the `__notes__` copy -/

/-- **The parts get a copy of `__notes__`.** After `derive` returned a group and the metadata
was copied, `orig.__notes__` is read; when it is a sequence, a new list of its items is assigned
to the new group with `setattr` (`:1198-1215`), and a failure there is the result; a missing or
non-sequence `__notes__` is skipped (`:1216-1222`); a failed read is the result. A subset that
never copies notes fails the first part, for an `rt` whose `setattr` leaves a mark. -/
def SubsetCopiesNotes : Prop :=
  ∀ (rt : Rt) (orig x g : Val) (xs : List Val) (w w1 w2 : World),
    callMethodO rt orig "derive" (.obj w.heap.size)
      { w with heap := w.heap.push (.val { cls := B.list, body := .list (x :: xs) }) } = .ok g w1 →
    egCheck w1 g = true → subsetCopyMeta orig g w1 = .ok () w2 →
    (∀ (n : Val) (c : List Val) (w3 w4 w5 : World),
      rt.getOptionalAttr orig "__notes__" w2 = .ok (some n) w3 → excSeqCheck w3 n = true →
      excSeqList rt n w3 = .ok c w4 →
      rt.setAttr g "__notes__" (some (.obj w4.heap.size))
        { w4 with heap := w4.heap.push (.val { cls := B.list, body := .list c }) } = .ok () w5 →
      exceptiongroupSubset rt orig (x :: xs) w = .ok (some g) w5) ∧
    (∀ (n : Val) (c : List Val) (e : PyErr) (w3 w4 w5 : World),
      rt.getOptionalAttr orig "__notes__" w2 = .ok (some n) w3 → excSeqCheck w3 n = true →
      excSeqList rt n w3 = .ok c w4 →
      rt.setAttr g "__notes__" (some (.obj w4.heap.size))
        { w4 with heap := w4.heap.push (.val { cls := B.list, body := .list c }) } = .err e w5 →
      exceptiongroupSubset rt orig (x :: xs) w = .err e w5) ∧
    (∀ (n : Val) (w3 : World),
      rt.getOptionalAttr orig "__notes__" w2 = .ok (some n) w3 → excSeqCheck w3 n = false →
      exceptiongroupSubset rt orig (x :: xs) w = .ok (some g) w3) ∧
    (∀ (w3 : World), rt.getOptionalAttr orig "__notes__" w2 = .ok none w3 →
      exceptiongroupSubset rt orig (x :: xs) w = .ok (some g) w3) ∧
    (∀ (e : PyErr) (w3 : World), rt.getOptionalAttr orig "__notes__" w2 = .err e w3 →
      exceptiongroupSubset rt orig (x :: xs) w = .err e w3)

theorem subsetCopiesNotes_proven : SubsetCopiesNotes := by
  intro rt orig x g xs w w1 w2 hd hg hm
  have hE : (x :: xs).isEmpty = false := rfl
  have hp :
      (exceptiongroupSubset rt orig (x :: xs) w) =
        ((subsetCopyMeta orig g >>= fun _ => rt.getOptionalAttr orig "__notes__" >>= fun n =>
          match n with
          | none => pure (some g)
          | some notes => do
            let w ← getW
            if excSeqCheck w notes then
              let c ← excSeqList rt notes
              let cv ← alloc B.list (.list c)
              rt.setAttr g "__notes__" (some cv)
              pure (some g)
            else pure (some g)) w1) := by
    simp only [exceptiongroupSubset, hE, M.bind_app]
    simp only [Bool.false_eq_true, if_false, M.bind_app]
    rw [alloc_app]
    dsimp only
    rw [hd]
    dsimp only
    simp [hg]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n c w3 w4 w5 h1 h2 h3 h4
    rw [hp]
    simp [hm, h1, h2, h3, alloc_app, h4]
  · intro n c e w3 w4 w5 h1 h2 h3 h4
    rw [hp]
    simp [hm, h1, h2, h3, alloc_app, h4]
  · intro n w3 h1 h2
    rw [hp]
    simp [hm, h1, h2]
  · intro w3 h1
    rw [hp]
    simp [hm, h1]
  · intro e w3 h1
    rw [hp]
    simp [hm, h1]

/-! ## `except*`: metadata, projection, `_PyExc_PrepReraiseStar` -/

/-- **`is_same_exception_metadata` is pointer equality of the four fields** (`:1589-1592`): it is
true exactly when `notes`, `__traceback__`, `__cause__` and `__context__` are the same objects (or
both NULL), so a re-raise with a new traceback, cause or context counts as a new exception. -/
def SameMetadataIff : Prop :=
  ∀ (w : World) (e1 e2 : Val),
    isSameExceptionMetadata w e1 e2 = true ↔
      (sameRef (excDataOf w e1).notes (excDataOf w e2).notes = true ∧
       (excDataOf w e1).traceback.is (excDataOf w e2).traceback = true ∧
       sameRef (excDataOf w e1).cause (excDataOf w e2).cause = true ∧
       sameRef (excDataOf w e1).context (excDataOf w e2).context = true)

theorem sameMetadataIff_proven : SameMetadataIff := by
  intro w e1 e2
  simp [isSameExceptionMetadata, Bool.and_eq_true, and_assoc]

theorem splitRec_ids_leaf (rt : Rt) (ids : List Val) (mv : Val) (f : Nat) (k : Val) (w : World)
    (hk : egCheck w k = false) :
    splitRecursive rt (.instanceIds ids) mv false (f + 1) k w =
      .ok (if ids.any (Val.is · k) then (some k, none) else (none, none)) w := by
  rw [splitRecursive]
  by_cases hm : ids.any (Val.is · k) = true
  · simp [splitCheckMatch, hk, hm]
  · simp [splitCheckMatch, hk, hm]

/-- One level of the instance-ids recursion over items that are leaves keeps those in `ids`. -/
theorem splitKids_ids (rt : Rt) (ids : List Val) (mv : Val) (f : Nat) (w : World) :
    ∀ (kids ml : List Val), (∀ k ∈ kids, egCheck w k = false) →
      splitKids (splitRecursive rt (.instanceIds ids) mv false (f + 1)) kids ml [] w =
        .ok (ml ++ kids.filter (fun k => ids.any (Val.is · k)), []) w := by
  intro kids
  induction kids with
  | nil => intro ml _; simp [splitKids]
  | cons k ks ih =>
    intro ml hk
    have hk1 : egCheck w k = false := hk k (by simp)
    have hks : ∀ k' ∈ ks, egCheck w k' = false := fun k' h => hk k' (by simp [h])
    have hstep := splitRec_ids_leaf rt ids mv f k w hk1
    by_cases hm : ids.any (Val.is · k) = true
    · have e1 : splitKids (splitRecursive rt (.instanceIds ids) mv false (f + 1)) (k :: ks) ml [] w =
          splitKids (splitRecursive rt (.instanceIds ids) mv false (f + 1)) ks (ml ++ [k]) [] w := by
        simp [splitKids, hstep, hm]
      rw [e1, ih _ hks]
      simp [List.filter_cons, hm]
    · have e1 : splitKids (splitRecursive rt (.instanceIds ids) mv false (f + 1)) (k :: ks) ml [] w =
          splitKids (splitRecursive rt (.instanceIds ids) mv false (f + 1)) ks ml [] w := by
        simp [splitKids, hstep, hm]
      rw [e1, ih _ hks]
      simp [List.filter_cons, hm]

theorem splitRec_ids_group (rt : Rt) (ids : List Val) (mv eg : Val) (f : Nat) (w : World)
    (hg : egCheck w eg = true) (hk : ∀ k ∈ (excDataOf w eg).egExceptions, egCheck w k = false) :
    splitRecursive rt (.instanceIds ids) mv false (f + 2) eg w =
      (do
        let r ← exceptiongroupSubset rt eg
          ((excDataOf w eg).egExceptions.filter (fun k => ids.any (Val.is · k)))
        pure (r, (none : Option Val))) w := by
  rw [splitRecursive]
  simp only [splitCheckMatch, M.bind_app, getW_app, hg, if_true, Bool.false_eq_true, if_false,
    Bool.not_true, M.pure_app]
  rw [splitKids_ids rt ids mv f w _ [] hk]
  simp

/-- **`exception_group_projection` keeps the leaves whose ids it collected.** On a group whose
items are leaves, with `ids` the leaves collected from `keep` (`:1553-1562`), the projection is
`exceptiongroup_subset` of the group's items that are in `ids`, in their order: `derive` is called
on exactly them, the metadata of `eg` is copied, and no kept leaf gives `None` (`:1574-1575`). A
projection that returns `eg`, or `None`, fails. -/
def ProjectionLeafGroup : Prop :=
  ∀ (rt : Rt) (eg : Val) (keep ids : List Val) (w : World),
    egCheck w eg = true → (∀ k ∈ (excDataOf w eg).egExceptions, egCheck w k = false) →
    collectLeafIdsList (collectLeafIds w excRecFuel) keep w = .ok ids w →
    exceptionGroupProjection rt eg keep w =
      (do
        let r ← exceptiongroupSubset rt eg
          ((excDataOf w eg).egExceptions.filter (fun k => ids.any (Val.is · k)))
        pure (r.getD .none)) w

theorem projectionLeafGroup_proven : ProjectionLeafGroup := by
  intro rt eg keep ids w hg hk hc
  have hf : excRecFuel = 1998 + 2 := rfl
  simp only [exceptionGroupProjection, M.bind_app, getW_app, hc]
  rw [hf, splitRec_ids_group rt ids .none eg 1998 w hg hk]
  simp only [M.bind_app]
  cases exceptiongroupSubset rt eg ((excDataOf w eg).egExceptions.filter (fun k => ids.any (Val.is · k))) w <;> rfl

/-- **`_PyExc_PrepReraiseStar` on a group**: the non-`None` entries are split into re-raised
(same metadata as `orig`) and raised; the re-raised ones are projected onto `orig`
(`:1652-1669`). With nothing raised the projection is the result; otherwise the projection (when
not `None`) is appended to the raised list, and a list of more than one is wrapped by
`_PyExc_CreateExceptionGroup("", list)`, a single one returned as is (`:1674-1696`). A failure of
the projection is the result. -/
def PrepReraiseStarGroup : Prop :=
  ∀ (rt : Rt) (orig : Val) (excs : List Val) (w : World), excs ≠ [] → egCheck w orig = true →
    let live := excs.filter (fun e => !e.is .none)
    let reraised := live.filter (fun e => isSameExceptionMetadata w e orig)
    let raised := live.filter (fun e => !isSameExceptionMetadata w e orig)
    (∀ (r : Val) (w1 : World), exceptionGroupProjection rt orig reraised w = .ok r w1 →
      (raised = [] → excPrepReraiseStar rt orig excs w = .ok r w1) ∧
      (∀ x, raised = [x] → r.is .none = true → excPrepReraiseStar rt orig excs w = .ok x w1) ∧
      (raised ≠ [] →
        let l := if r.is .none then raised else raised ++ [r]
        1 < l.length →
        excPrepReraiseStar rt orig excs w =
          createExceptionGroup rt "" (.obj w1.heap.size)
            { w1 with heap := w1.heap.push (.val { cls := B.list, body := .list l }) })) ∧
    (∀ (e : PyErr) (w1 : World), exceptionGroupProjection rt orig reraised w = .err e w1 →
      excPrepReraiseStar rt orig excs w = .err e w1)

theorem prepReraiseStarGroup_proven : PrepReraiseStarGroup := by
  intro rt orig excs w hne hg
  dsimp only
  have hE : excs.isEmpty = false := by cases excs <;> simp_all
  refine ⟨?_, ?_⟩
  · intro r w1 hp
    refine ⟨?_, ?_, ?_⟩
    · intro h0
      simp only [excPrepReraiseStar, hE, M.bind_app, getW_app, hg, Bool.not_true,
        Bool.false_eq_true, if_false]
      rw [hp]
      simp [h0]
    · intro x h1 hn
      simp only [excPrepReraiseStar, hE, M.bind_app, getW_app, hg, Bool.not_true,
        Bool.false_eq_true, if_false]
      rw [hp]
      simp [h1, hn]
    · intro hr hl
      have hr' : (excs.filter (fun e => !e.is .none)).filter
          (fun e => !isSameExceptionMetadata w e orig) ≠ [] := hr
      simp only [excPrepReraiseStar, hE, M.bind_app, getW_app, hg, Bool.not_true,
        Bool.false_eq_true, if_false]
      rw [hp]
      simp only [List.isEmpty_iff, hr', if_false, gt_iff_lt, hl, if_true, alloc_app]
      rfl
  · intro e w1 hp
    simp only [excPrepReraiseStar, hE, M.bind_app, getW_app, hg, Bool.not_true,
      Bool.false_eq_true, if_false]
    rw [hp]

theorem firstNonExc_none (w : World) : ∀ (i : Nat) (xs : List Val),
    (∀ y ∈ xs, (excInstanceCheck w y || y.is .none) = true) → firstNonExc w i xs = none := by
  intro i xs
  induction xs generalizing i with
  | nil => intro _; rfl
  | cons y ys ih =>
    intro h
    have hy := h y (by simp)
    simp [firstNonExc, hy, ih (i + 1) (fun z hz => h z (by simp [hz]))]

theorem firstNonExc_at (w : World) (x : Val) (post : List Val)
    (hx : (excInstanceCheck w x || x.is .none) = false) : ∀ (i : Nat) (pre : List Val),
    (∀ y ∈ pre, (excInstanceCheck w y || y.is .none) = true) →
    firstNonExc w i (pre ++ x :: post) = some (i + pre.length) := by
  intro i pre
  induction pre generalizing i with
  | nil => intro _; simp [firstNonExc, hx]
  | cons y ys ih =>
    intro h
    have hy := h y (by simp)
    simp only [List.cons_append, firstNonExc, hy, if_true]
    rw [ih (i + 1) (fun z hz => h z (by simp [hz]))]
    simp
    omega

/-- **`PyUnstable_Exc_PrepReraiseStar` names the first bad item, then hands over.** After the
`orig` and list checks, the first item that is neither an exception nor `None` is
`TypeError: item i of excs is not an exception` with its index (`:1716-1724`); when every item
passes and `orig` has a traceback, the result is `_PyExc_PrepReraiseStar(orig, excs)` itself
(`:1737`), so a wrapper that returns `None` after its checks fails. -/
def PrepReraiseStarHandOff : Prop :=
  (∀ (rt : Rt) (orig excs x : Val) (pre post : List Val) (w : World),
    excInstanceCheck w orig = true → listOf w excs = some (pre ++ x :: post) →
    (∀ y ∈ pre, (excInstanceCheck w y || y.is .none) = true) →
    (excInstanceCheck w x || x.is .none) = false →
    pyUnstableExcPrepReraiseStar rt orig excs w =
      .err (.exc B.TypeError s!"item {pre.length} of excs is not an exception" none) w) ∧
  (∀ (rt : Rt) (orig excs tb : Val) (xs : List Val) (w : World),
    excInstanceCheck w orig = true → listOf w excs = some xs →
    (∀ y ∈ xs, (excInstanceCheck w y || y.is .none) = true) →
    pyExceptionGetTraceback w orig = some tb →
    pyUnstableExcPrepReraiseStar rt orig excs w = excPrepReraiseStar rt orig xs w)

theorem prepReraiseStarHandOff_proven : PrepReraiseStarHandOff := by
  refine ⟨?_, ?_⟩
  · intro rt orig excs x pre post w ho hl hpre hx
    have := firstNonExc_at w x post hx 0 pre hpre
    simp [pyUnstableExcPrepReraiseStar, ho, hl, this, typeErr, raiseC]
  · intro rt orig excs tb xs w ho hl hall ht
    simp [pyUnstableExcPrepReraiseStar, ho, hl, firstNonExc_none w 0 xs hall, ht]

end PyLean.TypeObj
