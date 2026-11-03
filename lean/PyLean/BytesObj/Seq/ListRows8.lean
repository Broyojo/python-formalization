import PyLean.BytesObj.Seq.ListRows7

/-!
List iterators' length hints and `__setstate__` on every branch, `list.__init__(iterable)` and
`list(x)`, and the NotImplemented of `list_richcompare_impl` (Objects/listobject.c, CPython 3.15.2).
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α ρ : Type}

/-- `list_richcompare_impl(v, w, op)` with the operands' types: `none` is an object that is not a list;
`Py_RETURN_NOTIMPLEMENTED` (:3464-3465) is the outer `none`. -/
def listRichcompareAny (E : ElemOps α ρ) (cmp : Cmp2 α) (final : Final α ρ) (fuel : Nat) (op : CmpOp)
    (v w : Option (List α)) : Option (Py ρ × (List α × List α)) :=
  match v, w with
  | some v, some w => some (listRichcompare E cmp final fuel op v w)
  | _, _ => none

/-- The list iterators' `__length_hint__` on every branch (listobject.c:4112-4124, :4267-4276), for
every list and iterator state: a forward iterator reports what is left, `0` once exhausted (`index < 0`)
and `0` when the list has shrunk below its index (the `len >= 0` test, :4120); a reversed one reports
`index + 1`, `0` when the list has shrunk to `index + 1` items or fewer than that (:4273), and `0` once
`it_seq` is `NULL`. `__setstate__` (:4132-4147, :4284-4299) clips the new index to `[-1, len]`, and for
`reversed` to `[-1, len - 1]`, so `reversed([1, 2, 3]).__setstate__(10)` then `next()` gives `3`; on an
exhausted iterator it does nothing. -/
def ListIterStates : Prop :=
  ∀ (α : Type) (it : ListIter) (l : List α) (s : Int),
    (0 ≤ it.index → it.index ≤ l.length → listIterLen it l = l.length - it.index) ∧
    ((l.length : Int) < it.index → listIterLen it l = 0) ∧
    (it.index < 0 → listIterLen it l = 0) ∧
    (it.alive = true → it.index + 1 ≤ l.length → listRevIterLen it l = it.index + 1) ∧
    (it.alive = true → (l.length : Int) < it.index + 1 → listRevIterLen it l = 0) ∧
    (it.alive = false → listRevIterLen it l = 0) ∧
    (ssizeMin ≤ s → s ≤ ssizeMax → it.alive = true →
      listIterSetstate it l s = .ok { it with index := max (-1) (min s l.length) } ∧
      listRevIterSetstate it l s = .ok { it with index := max (-1) (min s ((l.length : Int) - 1)) }) ∧
    (ssizeMin ≤ s → s ≤ ssizeMax → it.alive = false →
      listIterSetstate it l s = .ok it ∧ listRevIterSetstate it l s = .ok it) ∧
    listIterSetstateObj it l none = .error (.typeError "an integer is required") ∧
    listRevIterSetstateObj it l none = .error (.typeError "an integer is required") ∧
    (∀ (x : α), (l ++ [x]).length ≤ s → s ≤ ssizeMax →
      ∃ it', listRevIterSetstate ⟨0, true⟩ (l ++ [x]) s = .ok it' ∧
        listRevIterNext it' (l ++ [x]) = .ok (some x, { it' with index := it'.index - 1 }))

theorem listIterStates_proven : ListIterStates := by
  intro α it l s
  have hM : ssizeMax = 9223372036854775807 := by decide
  have hm : ssizeMin = -9223372036854775808 := by decide
  refine ⟨fun h0 h1 => ?_, fun h => ?_, fun h => ?_, fun ha h => ?_, fun ha h => ?_, fun ha => ?_,
    fun h0 h1 ha => ?_, fun h0 h1 ha => ?_, rfl, rfl, fun x h0 h1 => ?_⟩
  · unfold listIterLen; rw [if_pos h0]; simp only; rw [if_pos (by omega)]
  · unfold listIterLen; split
    · simp only; rw [if_neg (by omega)]
    · rfl
  · unfold listIterLen; rw [if_neg (by omega)]
  · unfold listRevIterLen; simp only [ha]; rw [if_neg (by simp; omega)]
  · unfold listRevIterLen; simp only [ha]; rw [if_pos (by simp; omega)]
  · unfold listRevIterLen; simp only [ha]; rfl
  · have hc : PyLean.Sequences.asSsize s = .ok s := by
      unfold PyLean.Sequences.asSsize; rw [if_pos ⟨h0, h1⟩]
    constructor
    · simp only [listIterSetstate, hc, bind, Except.bind, ha, ↓reduceIte, pure, Except.pure]
      congr 2
      split <;> (try split) <;> omega
    · simp only [listRevIterSetstate, hc, bind, Except.bind, ha, ↓reduceIte, pure, Except.pure]
      congr 2
      split <;> (try split) <;> omega
  · have hc : PyLean.Sequences.asSsize s = .ok s := by
      unfold PyLean.Sequences.asSsize; rw [if_pos ⟨h0, h1⟩]
    have ha' : ¬ (it.alive = true) := by simp [ha]
    constructor
    · simp only [listIterSetstate, hc, bind, Except.bind, ha, Bool.false_eq_true, ↓reduceIte]
    · simp only [listRevIterSetstate, hc, bind, Except.bind, ha, Bool.false_eq_true, ↓reduceIte]
  · have hc : PyLean.Sequences.asSsize s = .ok s := by
      unfold PyLean.Sequences.asSsize; rw [if_pos ⟨by omega, h1⟩]
    have hl : ((l ++ [x]).length : Int) = l.length + 1 := by simp
    refine ⟨⟨l.length, true⟩, ?_, ?_⟩
    · simp only [listRevIterSetstate, hc, bind, Except.bind, ↓reduceIte, pure, Except.pure]
      congr 2
      rw [hl] at h0 ⊢
      split <;> (try split) <;> omega
    · have hv : validIndex (l.length : Int) (l ++ [x]).length = true := by
        rw [validIndex_eq _ _ (by omega) (by omega) (by omega) (by rw [hl]; omega)]
        simp only [decide_eq_true_eq, List.length_append, List.length_singleton]
        omega
      have hs : slot (l ++ [x]) (l.length : Int) = some x := by
        rw [slot_nat]; simp
      simp only [listRevIterNext, listGetItemRef, hv, ↓reduceIte, hs]
      rw [if_neg (by omega)]
      rfl

/-- `list.__init__(iterable)` (listobject.c:3543-3565) and `list(iterable)` (`list_vectorcall`,
:3567-3590) with an iterable: the old items are dropped, then the list holds the iterable's items, for
a list or tuple argument (the fast path) and every list up to `PY_SSIZE_T_MAX / 16` items; a
non-iterable raises `TypeError` after the clear. `list(x)` is that `__init__` on a new empty list; the
richcompare of a non-list operand is `NotImplemented` (:3464-3465), either side. -/
def ListInitIterable : Prop :=
  ∀ (α ρ : Type) (o : LObj α) (s : List α) (name : String) (E : ElemOps α ρ) (cmp : Cmp2 α)
    (final : Final α ρ) (fuel : Nat) (op : CmpOp) (v : List α), o.WF → (s.length : Int) ≤ ssizeMax / 16 →
    (listInit o (some (.fast s))).2 = none ∧ (listInit o (some (.fast s))).1.items = s ∧
    listVectorcall [.fast s] 0 = .ok (listInit (LObj.empty : LObj α) (some (.fast s))).1 ∧
    ((listVectorcall [.fast s] 0).map LObj.items = .ok s) ∧
    listVectorcall [(.notIterable name : ExtArg α)] 0 = .error (.typeError s!"'{name}' object is not iterable") ∧
    listRichcompareAny E cmp final fuel op (some v) none = none ∧
    listRichcompareAny E cmp final fuel op none (some v) = none ∧
    listRichcompareAny E cmp final fuel op (some v) (some s) = some (listRichcompare E cmp final fuel op v s)

theorem listInit_fast (o : LObj α) (s : List α) (hw : o.WF) (hb : (s.length : Int) ≤ ssizeMax / 16) :
    ∃ o', listInit o (some (.fast s)) = (o', none) ∧ o'.items = s := by
  have hc : (if o.hasItems then listClear o else o) = LObj.empty := by
    split
    · exact listClear_empty o hw
    · rename_i hh
      have hh' : o.hasItems = false := by simpa using hh
      obtain ⟨hi, ha⟩ := wf_noitems hw hh'
      cases o; simp_all [LObj.empty]
  have he := (listExtendFast_spec (LObj.empty : LObj α) s empty_wf).1 (by simpa [LObj.empty] using hb)
  obtain ⟨o', h1, h2, -⟩ := he
  refine ⟨o', ?_, by simpa [LObj.empty] using h2⟩
  simp only [listInit, hc, listExtend, liftRes, h1]

theorem listInitIterable_proven : ListInitIterable := by
  intro α ρ o s name E cmp final fuel op v hw hb
  obtain ⟨o', h1, h2⟩ := listInit_fast o s hw hb
  obtain ⟨o0, h01, h02⟩ := listInit_fast (LObj.empty : LObj α) s empty_wf hb
  have hv : listVectorcall [.fast s] 0 = .ok (listInit (LObj.empty : LObj α) (some (.fast s))).1 := by
    simp only [listVectorcall, h01]; rfl
  refine ⟨by rw [h1], by rw [h1]; exact h2, hv, by rw [hv, h01]; simp [Except.map, h02], ?_, rfl, rfl, rfl⟩
  simp [listVectorcall, listInit, listExtend, LObj.empty]

end PyLean.BytesObj.Seq
