import PyLean.TypeObj.ExcPropsSplit

/-!
`split` and `subgroup` succeed, not only "if they succeed, the result is right".

Every statement in `ExcPropsSplit` reads "`splitRecursive ... = .ok (m, r) w'` implies ...", which
a function that fails on any partly matching group satisfies. `SplitComputesSpec` closes that: it
says the recursion returns, and returns `specSplit`. The steps that run user code can fail, and
then `split` does too, so the steps have to be assumed to succeed. `SplitTotalHyp` says so, under a
world invariant `I` so that the assumption does not have to hold of arbitrary worlds.

`SplitHypsInhabited` shows the two sets of hypotheses can be met together, on a group that matches
in part, by the real `subsetCopyMeta`, `callMethodO` and `exceptiongroupSubset` around a small
`rt`. Without it, the theorems could be vacuous.
-/

namespace PyLean.TypeObj

/-- The steps of the recursion that can fail in fact succeed, in worlds satisfying `I`. `I` is
preserved by each of them; it holds what user code leaves true. `copyMeta` holds because the only way
for `subsetCopyMeta` to fail is a `traceback` field that is neither a traceback nor `None`, which
the `__traceback__` setter excludes. -/
structure SplitTotalHyp (rt : Rt) (mt : MatcherType) (mv : Val) (I : World → Prop) : Prop where
  /-- The matcher does not raise. -/
  check : ∀ exc w, I w → ∃ b w', splitCheckMatch rt exc mt mv w = .ok b w' ∧ I w'
  /-- Allocating the list handed to `derive`, or the copy of the notes, keeps `I`. -/
  alloc : ∀ w xs, I w → I { w with heap := w.heap.push (.val { cls := B.list, body := .list xs }) }
  /-- `derive` does not raise, and returns a group. -/
  derive : ∀ orig xs lst w, I w → listOf w lst = some xs →
    ∃ g w', callMethodO rt orig "derive" lst w = .ok g w' ∧ egCheck w' g = true ∧ I w'
  /-- Copying the traceback, context and cause of the original group succeeds. -/
  copyMeta : ∀ orig a w, I w → a < w.heap.size →
    ∃ w', subsetCopyMeta orig (.obj a) w = .ok () w' ∧ I w'
  /-- Reading `__notes__` does not raise. -/
  notesGet : ∀ orig w, I w → ∃ r w', rt.getOptionalAttr orig "__notes__" w = .ok r w' ∧ I w'
  /-- Listing a `__notes__` sequence does not raise. -/
  notesList : ∀ orig n w0 w, I w → rt.getOptionalAttr orig "__notes__" w0 = .ok (some n) w →
    excSeqCheck w n = true → ∃ c w', excSeqList rt n w = .ok c w' ∧ I w'
  /-- Writing `__notes__` on the new group does not raise. -/
  notesSet : ∀ eg c w, I w → ∃ w', rt.setAttr eg "__notes__" c w = .ok () w' ∧ I w'

theorem subset_total {rt : Rt} {mt : MatcherType} {mv : Val} {p : Val → Bool} {I : World → Prop}
    (H : SplitHyp rt mt mv p) (T : SplitTotalHyp rt mt mv I) (orig : Val) (xs : List Val)
    (w : World) (hI : I w) :
    ∃ res w', exceptiongroupSubset rt orig xs w = .ok res w' ∧ I w' := by
  cases xs with
  | nil => exact ⟨none, w, by simp [exceptiongroupSubset], hI⟩
  | cons x xs' =>
    have hl := listOf_alloc w (x :: xs')
    obtain ⟨g, w2, hd, hgrp, hI2⟩ := T.derive orig _ _ _ (T.alloc w (x :: xs') hI) hl
    obtain ⟨_, hn, _⟩ := H.derive _ _ _ _ _ _ hl hd
    cases g with
    | obj a =>
      obtain ⟨w3, hm, hI3⟩ := T.copyMeta orig a w2 hI2 hn.1
      obtain ⟨n, w4, ho, hI4⟩ := T.notesGet orig w3 hI3
      cases n with
      | none =>
        refine ⟨some (.obj a), w4, ?_, hI4⟩
        simp only [exceptiongroupSubset, List.isEmpty_cons, Bool.false_eq_true, if_false,
          M.bind_app, alloc_app]
        rw [hd]
        simp [hgrp, hm, ho]
      | some ns =>
        by_cases hq : excSeqCheck w4 ns = true
        · obtain ⟨c, w5, hL, hI5⟩ := T.notesList orig ns w3 w4 hI4 ho hq
          obtain ⟨w6, hset, hI6⟩ := T.notesSet (.obj a) (some (.obj w5.heap.size))
            { w5 with heap := w5.heap.push (.val { cls := B.list, body := .list c }) }
            (T.alloc w5 c hI5)
          refine ⟨some (.obj a), w6, ?_, hI6⟩
          simp only [exceptiongroupSubset, List.isEmpty_cons, Bool.false_eq_true, if_false,
            M.bind_app, alloc_app]
          rw [hd]
          simp [hgrp, hm, ho, hq, hL, alloc_app, hset]
        · refine ⟨some (.obj a), w4, ?_, hI4⟩
          simp only [exceptiongroupSubset, List.isEmpty_cons, Bool.false_eq_true, if_false,
            M.bind_app, alloc_app]
          rw [hd]
          simp [hgrp, hm, ho, hq]
    | _ => exact hn.elim

theorem kids_total {I : World → Prop} (f : Nat) (rec : Val → M (Option Val × Option Val))
    (IH : ∀ exc w, I w → Valid w f exc →
      ∃ m r w', rec exc w = .ok (m, r) w' ∧ I w' ∧ Ext w w') :
    ∀ (es ml rl : List Val) (w : World), I w → (∀ e ∈ es, Valid w f e) →
      ∃ ml' rl' w', splitKids rec es ml rl w = .ok (ml', rl') w' ∧ I w' := by
  intro es
  induction es with
  | nil => exact fun ml rl w hI _ => ⟨ml, rl, w, by simp [splitKids], hI⟩
  | cons e es ih =>
    intro ml rl w hI he
    obtain ⟨m, r, w1, hrec, hI1, hx⟩ := IH e w hI (he e List.mem_cons_self)
    obtain ⟨ml', rl', w', h, hI'⟩ := ih (ml ++ m.toList) (rl ++ r.toList) w1 hI1
      (fun y hy => Valid.mono hx _ _ (he y (List.mem_cons_of_mem _ hy)))
    refine ⟨ml', rl', w', ?_, hI'⟩
    simp only [splitKids, M.bind_app, hrec]
    exact h

theorem split_total {rt : Rt} {mt : MatcherType} {mv : Val} {p : Val → Bool} {I : World → Prop}
    (H : SplitHyp rt mt mv p) (T : SplitTotalHyp rt mt mv I) (cr : Bool) :
    ∀ (f : Nat) (exc : Val) (w : World), I w → Valid w f exc →
      ∃ m r w', splitRecursive rt mt mv cr f exc w = .ok (m, r) w' ∧ I w' := by
  intro f
  induction f with
  | zero => exact fun _ _ _ hv => hv.elim
  | succ f ih =>
    intro exc w hI hv
    obtain ⟨b, w1, hc, hI1⟩ := T.check exc w hI
    obtain ⟨_, hext⟩ := H.check _ _ _ _ hc
    cases b with
    | true =>
      exact ⟨some exc, none, w1, by simp [splitRecursive, hc], hI1⟩
    | false =>
      by_cases hg : egCheck w1 exc = true
      · have hg0 : egCheck w exc = true := by rw [← egCheck_stable hext hv.1]; exact hg
        have hkv : ∀ e ∈ (excDataOf w1 exc).egExceptions, Valid w1 f e := by
          have hkw : (excDataOf w1 exc).egExceptions = egKids w exc := egKids_stable hext hv.1
          rw [hkw]
          exact fun e he => Valid.mono hext _ _ (hv.2 hg0 e he)
        have IH' : ∀ exc w, I w → Valid w f exc →
            ∃ m r w', splitRecursive rt mt mv cr f exc w = .ok (m, r) w' ∧ I w' ∧ Ext w w' := by
          intro e u hu hve
          obtain ⟨m, r, u', hr, hu'⟩ := ih e u hu hve
          exact ⟨m, r, u', hr, hu', (split_spec H cr f e u m r u' hve hr).1⟩
        obtain ⟨ml, rl, w2, hk, hI2⟩ :=
          kids_total f _ IH' (excDataOf w1 exc).egExceptions [] [] w1 hI1 hkv
        obtain ⟨mres, w3, hs, hI3⟩ := subset_total H T exc ml w2 hI2
        cases cr with
        | false =>
          refine ⟨mres, none, w3, ?_, hI3⟩
          simp [splitRecursive, hc, hg, hk, hs]
        | true =>
          obtain ⟨rres, w4, hr, hI4⟩ := subset_total H T exc rl w3 hI3
          refine ⟨mres, rres, w4, ?_, hI4⟩
          simp [splitRecursive, hc, hg, hk, hs, hr]
      · have hg' : egCheck w1 exc = false := by simpa using hg
        exact ⟨none, if cr then some exc else none, w1, by simp [splitRecursive, hc, hg'], hI1⟩

/-- **`split` and `subgroup` return, and return `specSplit`.** Under `SplitHyp` and
`SplitTotalHyp`, on a group of depth below the fuel, the recursion with `construct_rest` succeeds
with exactly the two parts `specSplit` gives, the recursion without it succeeds with the first
part and no rest, and `BaseExceptionGroup.split` wraps the two parts in a tuple. `Valid`,
`SplitHyp` and `SplitTotalHyp` are the preconditions; the matcher is free, so this covers groups
that match in part, which a function succeeding only on a full match cannot satisfy. -/
def SplitComputesSpec : Prop :=
  ∀ (rt : Rt) (mt : MatcherType) (mv : Val) (p : Val → Bool) (I : World → Prop),
    SplitHyp rt mt mv p → SplitTotalHyp rt mt mv I →
    (∀ (f : Nat) (exc : Val) (w : World), I w → Valid w f exc →
      (∃ m r w', splitRecursive rt mt mv true f exc w = .ok (m, r) w' ∧
        m.map (shapeW w' f) = (specSplit w p f exc).1 ∧
        r.map (shapeW w' f) = (specSplit w p f exc).2) ∧
      (∃ m w', splitRecursive rt mt mv false f exc w = .ok (m, none) w' ∧
        m.map (shapeW w' f) = (specSplit w p f exc).1)) ∧
    (∀ (self : Val) (w : World), I w → Valid w excRecFuel self →
      getMatcherType mv w = .ok mt w →
      (∃ (m r : Option Val) (w' : World), baseExceptionGroupSplit rt self mv w =
          .ok (.tuple [m.getD .none, r.getD .none]) w' ∧
        m.map (shapeW w' excRecFuel) = (specSplit w p excRecFuel self).1 ∧
        r.map (shapeW w' excRecFuel) = (specSplit w p excRecFuel self).2) ∧
      (∃ (m : Option Val) (w' : World), baseExceptionGroupSubgroup rt self mv w = .ok (m.getD .none) w' ∧
        m.map (shapeW w' excRecFuel) = (specSplit w p excRecFuel self).1))

theorem splitComputesSpec_proven : SplitComputesSpec := by
  intro rt mt mv p I H T
  have key : ∀ (f : Nat) (exc : Val) (w : World), I w → Valid w f exc →
      (∃ m r w', splitRecursive rt mt mv true f exc w = .ok (m, r) w' ∧
        m.map (shapeW w' f) = (specSplit w p f exc).1 ∧
        r.map (shapeW w' f) = (specSplit w p f exc).2) ∧
      (∃ m w', splitRecursive rt mt mv false f exc w = .ok (m, none) w' ∧
        m.map (shapeW w' f) = (specSplit w p f exc).1) := by
    intro f exc w hI hv
    constructor
    · obtain ⟨m, r, w', h, _⟩ := split_total H T true f exc w hI hv
      obtain ⟨_, h1, h2⟩ := split_spec H true f exc w m r w' hv h
      simp only [if_true] at h2
      exact ⟨m, r, w', h, h1.shape, h2.shape⟩
    · obtain ⟨m, r, w', h, _⟩ := split_total H T false f exc w hI hv
      obtain ⟨_, h1, h2⟩ := split_spec H false f exc w m r w' hv h
      simp only [Bool.false_eq_true, if_false] at h2
      have hr : r = none := by
        cases r with
        | none => rfl
        | some _ => exact h2.elim
      subst hr
      exact ⟨m, w', h, h1.shape⟩
  refine ⟨key, ?_⟩
  intro self w hI hv hm
  obtain ⟨⟨m, r, w', h, h1, h2⟩, ⟨m2, w2, h3, h4⟩⟩ := key excRecFuel self w hI hv
  constructor
  · refine ⟨m, r, w', ?_, h1, h2⟩
    simp only [baseExceptionGroupSplit, M.bind_app, hm, h]
    simp
  · refine ⟨m2, w2, ?_, h4⟩
    simp only [baseExceptionGroupSubgroup, M.bind_app, hm, h3]
    simp

/-- **The failure paths propagate.** A matcher that raises makes the recursion raise the same
exception, and `derive` returning something other than a group is the `TypeError` of
`Objects/exceptions.c:1179-1183`, never a silently wrong result. No hypothesis: this is what
`SplitTotalHyp` excludes, so it covers the other side of `SplitComputesSpec`. -/
def SplitPropagatesFailures : Prop :=
  (∀ (rt : Rt) (mt : MatcherType) (mv : Val) (cr : Bool) (f : Nat) (exc : Val) (w : World)
      (e : PyErr) (w1 : World),
    splitCheckMatch rt exc mt mv w = .err e w1 →
    splitRecursive rt mt mv cr (f + 1) exc w = .err e w1) ∧
  (∀ (rt : Rt) (orig : Val) (xs : List Val) (w : World) (g : Val) (w1 : World), xs ≠ [] →
    callMethodO rt orig "derive" (.obj w.heap.size)
      { w with heap := w.heap.push (.val { cls := B.list, body := .list xs }) } = .ok g w1 →
    egCheck w1 g = false →
    exceptiongroupSubset rt orig xs w =
      .err (.exc B.TypeError "derive must return an instance of BaseExceptionGroup" none) w1)

theorem splitPropagatesFailures_proven : SplitPropagatesFailures := by
  constructor
  · intro rt mt mv cr f exc w e w1 h
    simp [splitRecursive, h]
  · intro rt orig xs w g w1 hx hd hg
    cases xs with
    | nil => exact absurd rfl hx
    | cons x xs' =>
      simp only [exceptiongroupSubset, List.isEmpty_cons, Bool.false_eq_true, if_false,
        M.bind_app, alloc_app]
      rw [hd]
      simp [hg, typeErr, raiseC]

/-! ## The hypotheses can be met -/

/-- What the witness `rt` asks of a world. -/
def WitnessInv (w : World) : Prop :=
  (tdata w B.BaseExceptionGroup).mro = some [B.BaseExceptionGroup] ∧
    (slotOf w B.noneType .tp_call).isSome = true ∧
    ∀ v, (excDataOf w v).traceback = .none

theorem get_push_ne (w : World) (c : Cell) {a : Addr} (h : a ≠ w.heap.size) :
    World.get { w with heap := w.heap.push c } a = w.get a := by
  simp only [World.get]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  simp [Array.getElem?_push, h]

theorem tdata_push (w : World) (o : Obj) (t : Addr) :
    tdata { w with heap := w.heap.push (.val o) } t = tdata w t := by
  by_cases h : t = w.heap.size
  · subst h
    have hd : w.get w.heap.size = default := by
      simp only [World.get]
      rw [Array.getD_eq_getD_getElem?]
      simp
    simp only [tdata]
    rw [get_push_size, hd]
    rfl
  · simp only [tdata, get_push_ne w _ h]

theorem traceback_push (w : World) (o : Obj) (ho : ∀ d, o.body = .exc d → d.traceback = .none)
    (h : ∀ v, (excDataOf w v).traceback = .none) (v : Val) :
    (excDataOf { w with heap := w.heap.push (.val o) } v).traceback = .none := by
  cases v with
  | obj a =>
    by_cases ha : a = w.heap.size
    · subst ha
      simp only [excDataOf, payloadOf, get_push_size]
      cases hb : o.body with
      | exc d => exact ho d hb
      | _ => rfl
    · have := h (.obj a)
      simpa only [excDataOf, payloadOf, get_push_ne w _ ha] using this
  | _ => rfl

theorem traceback_excUpdW (w : World) (a : Addr) (f : ExcData → ExcData)
    (hf : ∀ d, (f d).traceback = d.traceback) (ha : a < w.heap.size)
    (h : ∀ v, (excDataOf w v).traceback = .none) (v : Val) :
    (excDataOf (excUpdW w a f) v).traceback = .none := by
  cases v with
  | obj b =>
    by_cases hab : a = b
    · subst hab
      have h0 := h (.obj a)
      cases hc : w.get a with
      | ty c d =>
        simp only [excUpdW, hc]
        exact h0
      | val o =>
        rw [excUpdW_val f hc]
        simp only [excDataOf, payloadOf, get_setCell_same _ _ _ ha, updObj]
        simp only [excDataOf, payloadOf, hc] at h0
        cases hb : o.body with
        | exc d =>
          simp only [hb] at h0
          simp [hf, h0]
        | _ => simp [hb]
    · have := h (.obj b)
      simpa only [excDataOf, payloadOf, get_excUpdW_ne _ _ _ _ hab] using this
  | _ => rfl

theorem WitnessInv.push {w : World} (h : WitnessInv w) (o : Obj)
    (ho : ∀ d, o.body = .exc d → d.traceback = .none) :
    WitnessInv { w with heap := w.heap.push (.val o) } := by
  refine ⟨?_, ?_, traceback_push w o ho h.2.2⟩
  · rw [tdata_push]; exact h.1
  · simp only [slotOf, tdata_push]; exact h.2.1

theorem WitnessInv.update {w : World} (h : WitnessInv w) (a : Addr) (f : ExcData → ExcData)
    (hf : ∀ d, (f d).traceback = d.traceback) (ha : a < w.heap.size) :
    WitnessInv (excUpdW w a f) := by
  refine ⟨?_, ?_, traceback_excUpdW w a f hf ha h.2.2⟩
  · rw [tdata_excUpdW _ _ _ _ ha]; exact h.1
  · simp only [slotOf, tdata_excUpdW _ _ _ _ ha]; exact h.2.1

/-- The body of the group the witness's `derive` builds. -/
def witnessGroup (xs : List Val) : Obj :=
  { cls := B.BaseExceptionGroup, body := .exc { egExceptions := xs } }

/-- The matcher is `q`, called through `rt.call` as `exceptiongroup_split_check_match` does on a
callable `.int _`; `derive` is `None` and builds a group of the list it is given, when the world has
the class; `__notes__` is absent. -/
def witnessRt (q : Val → Bool) : Rt :=
  { (default : Rt) with
    call := fun f args _ w =>
      match f, args with
      | .int _, [x] => .ok (.bool (q x)) w
      | .none, [l] =>
        match listOf w l with
        | some xs =>
          if (tdata w B.BaseExceptionGroup).mro = some [B.BaseExceptionGroup] then
            .ok (.obj w.heap.size) { w with heap := w.heap.push (.val (witnessGroup xs)) }
          else .err .fuel w
        | none => .err .fuel w
      | _, _ => .err .fuel w
    getAttr := fun _ _ w => .ok .none w
    getOptionalAttr := fun _ _ w => .ok none w
    setAttr := fun _ _ _ w => .ok () w
    isTrue := fun v w =>
      match v with
      | .bool b => .ok b w
      | _ => .err .fuel w
    getIter := fun _ w => .err .fuel w }

theorem witness_check (q : Val → Bool) (n : Int) (exc : Val) (w : World) :
    splitCheckMatch (witnessRt q) exc .byPredicate (.int n) w = .ok (q exc) w := by
  simp only [splitCheckMatch, M.bind_app]
  simp [witnessRt]

theorem witness_derive (q : Val → Bool) (orig lst : Val) (xs : List Val) (w : World)
    (hl : listOf w lst = some xs) (hc : excCallableCheck w .none = true)
    (hm : (tdata w B.BaseExceptionGroup).mro = some [B.BaseExceptionGroup]) :
    callMethodO (witnessRt q) orig "derive" lst w =
      .ok (.obj w.heap.size) { w with heap := w.heap.push (.val (witnessGroup xs)) } := by
  simp only [callMethodO, M.bind_app, getW_app]
  simp [witnessRt, hc, hl, hm]

theorem witness_notesList (q : Val → Bool) (n : Val) (w : World) (c : List Val) (w' : World)
    (h : excSeqList (witnessRt q) n w = .ok c w') : Ext w w' := by
  cases hl : listOf w n <;> cases hb : (typeOf w n == B.list) <;> cases n <;>
    simp only [excSeqList, M.bind_app, getW_app, hl, hb] at h <;>
    first
    | (simp [witnessRt] at h; done)
    | (simp at h; rw [← h.2]; exact Ext.refl _)

theorem witness_hyp (q : Val → Bool) (n : Int) :
    SplitHyp (witnessRt q) .byPredicate (.int n) q := by
  constructor
  · intro exc w b w' h
    rw [witness_check] at h
    simp at h
    exact ⟨h.1.symm, h.2 ▸ Ext.refl _⟩
  · intro orig xs lst w g w' hl h
    by_cases hc : excCallableCheck w .none = true
    · by_cases hm : (tdata w B.BaseExceptionGroup).mro = some [B.BaseExceptionGroup]
      · rw [witness_derive q orig lst xs w hl hc hm] at h
        simp at h
        obtain ⟨h1, h2⟩ := h
        subst h1 h2
        refine ⟨ext_push w _, ⟨?_, ?_⟩, ?_⟩
        · simp
        · simp [typeOf, get_push_size, witnessGroup, tdata_push, hm]
        · intro _
          simp [egKids, excDataOf, payloadOf, get_push_size, witnessGroup]
      · simp only [callMethodO, M.bind_app, getW_app] at h
        simp [witnessRt, hc, hl, hm] at h
    · have hc' : excCallableCheck w .none = false := by simpa using hc
      have hg : (witnessRt q).getAttr orig "derive" w = .ok .none w := rfl
      simp only [callMethodO, M.bind_app, hg, getW_app] at h
      simp [hc', typeErr, raiseC] at h
  · intro orig w r w' h
    simp [witnessRt] at h
    rw [← h.2]
    exact Ext.refl _
  · intro n w c w' h
    exact witness_notesList q n w c w' h
  · intro eg c w w' h
    simp [witnessRt] at h
    rw [← h]
    exact Ext.refl _

theorem witness_total (q : Val → Bool) (n : Int) :
    SplitTotalHyp (witnessRt q) .byPredicate (.int n) WitnessInv := by
  constructor
  · intro exc w hI
    exact ⟨_, _, witness_check q n exc w, hI⟩
  · intro w xs hI
    exact hI.push _ (by intro d h; simp at h)
  · intro orig xs lst w hI hl
    refine ⟨_, _, witness_derive q orig lst xs w hl hI.2.1 hI.1, ?_,
      hI.push _ (by intro d h; simp [witnessGroup] at h; subst h; rfl)⟩
    simp [egCheck, isSubtype, typeOf, get_push_size, witnessGroup, tdata_push, hI.1]
  · intro orig a w hI ha
    have ht : pyExceptionGetTraceback w orig = none := by
      simp [pyExceptionGetTraceback, hI.2.2 orig]
    refine ⟨excUpdW (excUpdW w a fun d => { d with context := pyExceptionGetContext w orig }) a
        fun d => { d with suppressContext := true, cause := pyExceptionGetCause w orig }, ?_,
      (hI.update a (fun d => { d with context := pyExceptionGetContext w orig }) (fun _ => rfl)
        ha).update a (fun d => { d with suppressContext := true, cause := pyExceptionGetCause w orig })
          (fun _ => rfl) (by rw [size_excUpdW]; exact ha)⟩
    simp [subsetCopyMeta, ht, pyExceptionSetContext, pyExceptionSetCause, excUpdate_app]
  · intro orig w hI
    exact ⟨none, w, rfl, hI⟩
  · intro orig ns w0 w _ h _
    simp [witnessRt] at h
  · intro eg c w hI
    exact ⟨w, rfl, hI⟩

/-- A world with the class of groups, a callable-typed `None`, a group at 60 and two leaves. -/
def witnessWorld : World :=
  { heap := (((((Array.replicate 63 (default : Cell))
      |>.setIfInBounds B.BaseExceptionGroup (.ty 0 { mro := some [B.BaseExceptionGroup] }))
      |>.setIfInBounds B.noneType (.ty 0 { mro := some [B.noneType], slots := [(.tp_call, .generic)] }))
      |>.setIfInBounds 60 (.val (witnessGroup [.obj 61, .obj 62])))
      |>.setIfInBounds 61 (.val { cls := B.noneType }))
      |>.setIfInBounds 62 (.val { cls := B.noneType }) }

theorem witnessWorld_inv : WitnessInv witnessWorld := by
  refine ⟨by decide, by decide, ?_⟩
  have small : ∀ a, a < 63 → ((excDataOf witnessWorld (.obj a)).traceback.is .none) = true := by
    decide
  intro v
  cases v with
  | obj a =>
    by_cases ha : a < 63
    · have := small a ha
      revert this
      cases (excDataOf witnessWorld (.obj a)).traceback <;> simp [Val.is]
    · have hd : witnessWorld.get a = default := by
        simp only [World.get]
        rw [Array.getD_eq_getD_getElem?]
        have hs : witnessWorld.heap.size = 63 := by decide
        rw [Array.getElem?_eq_none (show witnessWorld.heap.size ≤ a by rw [hs]; exact Nat.le_of_not_lt ha)]
        rfl
      simp [excDataOf, payloadOf, hd]
      rfl
  | _ => rfl

/-- **The hypotheses of `SplitComputesSpec` can be met** on a group that matches in part: both
parts of `specSplit` are present, so `SplitComputesSpec` is not vacuous, and a recursion that
succeeds only on a full match contradicts it. -/
def SplitHypsInhabited : Prop :=
  ∃ (rt : Rt) (mv : Val) (p : Val → Bool) (I : World → Prop) (w : World) (exc : Val),
    SplitHyp rt .byPredicate mv p ∧ SplitTotalHyp rt .byPredicate mv I ∧ I w ∧ Valid w 3 exc ∧
    (specSplit w p 3 exc).1.isSome = true ∧ (specSplit w p 3 exc).2.isSome = true

theorem splitHypsInhabited_proven : SplitHypsInhabited := by
  let q : Val → Bool := fun v => v.is (.obj 61)
  refine ⟨witnessRt q, .int 0, q, WitnessInv, witnessWorld, .obj 60, witness_hyp q 0,
    witness_total q 0, witnessWorld_inv, ?_, by decide, by decide⟩
  have hleaf : ∀ a, a = 61 ∨ a = 62 → Valid witnessWorld 2 (.obj a) := by
    intro a ha
    rcases ha with rfl | rfl
    · exact ⟨⟨by decide, by decide⟩, fun hg => absurd hg (by decide)⟩
    · exact ⟨⟨by decide, by decide⟩, fun hg => absurd hg (by decide)⟩
  refine ⟨⟨by decide, by decide⟩, fun _ k hk => ?_⟩
  have hk' : egKids witnessWorld (.obj 60) = [.obj 61, .obj 62] := rfl
  rw [hk'] at hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact hleaf 61 (.inl rfl)
  · exact hleaf 62 (.inr rfl)

end PyLean.TypeObj
