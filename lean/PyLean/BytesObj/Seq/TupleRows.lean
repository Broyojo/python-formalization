import PyLean.BytesObj.Seq.TupleCall
import PyLean.BytesObj.Seq.ListRows
import PyLean.BytesObj.Seq.ReprProps
import PyLean.BytesObj.Seq.IterProps
import PyLean.BytesObj.Seq.HashProps

/-!
`tuple` on every branch of the functions whose earlier statements covered only their success path
(Objects/tupleobject.c, CPython 3.15.2): `tuple(iterable)` over a fallible iterator, `tuple.__new__`
for a subclass, the argument checks of `tuple(...)`, `NotImplemented` for a non-tuple operand, the
dispatch of `t[item]`, `__reduce__` and `__setstate__` of the iterator, `hash` and `repr` with raising
elements, `tuple.index`'s `ValueError`, `tuple_slice` and `PyTuple_GetSlice`, `__getnewargs__`, and the
C API `PyTuple_New`, `PyTuple_SetItem` and `_PyTuple_Resize` with the hash cache.
-/

namespace PyLean.BytesObj.Seq

open PyLean
open PyLean.RangeSlice (Slice)

variable {α ρ : Type}

/-! ## `tuple(iterable)` -/

theorem steal_spec (xs : List α) (h : (xs.length : Int) ≤ tupleLimit) :
    tupleFromArraySteal xs = .ok (if xs = [] then .empty else .fresh { items := xs, tracked := true }) := by
  by_cases he : xs = []
  · subst he; simp [tupleFromArraySteal]
  · have h0 : xs.length ≠ 0 := fun hz => he (List.length_eq_zero_iff.mp hz)
    simp only [tupleFromArraySteal, h0, if_false, tupleAlloc_ok _ (by omega) h, he]

theorem asTupleAndClear_steal (o : LObj α) (h : o.hasItems = true) :
    (match listAsTupleAndClear o with
      | .ok (r, _) => (.ok r : Py (TRes α))
      | .error e => .error e) = tupleFromArraySteal o.items := by
  simp only [listAsTupleAndClear, h, Bool.not_true, Bool.false_eq_true, if_false]
  cases tupleFromArraySteal o.items <;> rfl

/-- The list phase of `PySequence_Tuple` stores every further item and ends as
`_PyTuple_FromArraySteal` of all of them, or with the iterator's exception. -/
theorem seqTupleList_spec (next : Nat → Option (Py α)) : ∀ (ys : List α) (fuel k : Nat) (o : LObj α),
    o.WF → o.items ≠ [] → ys.length < fuel → ((o.items.length + ys.length : Nat) : Int) < ssizeMax / 16 →
    (∀ j (hj : j < ys.length), next (k + j) = some (.ok ys[j])) →
    (next (k + ys.length) = none → seqTupleList next fuel k o = tupleFromArraySteal (o.items ++ ys)) ∧
    (∀ e, next (k + ys.length) = some (.error e) → seqTupleList next fuel k o = .error e)
  | [], fuel, k, o, hw, hne, hf, _, _ => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hhas : o.hasItems = true := by
      apply hw.array
      have := hw.covers
      have : 0 < o.items.length := List.length_pos_iff.mpr hne
      omega
    refine ⟨fun hn => ?_, fun e he => ?_⟩
    · simp only [List.length_nil, Nat.add_zero] at hn
      simp only [seqTupleList, hn, List.append_nil]
      exact asTupleAndClear_steal o hhas
    · simp only [List.length_nil, Nat.add_zero] at he
      simp only [seqTupleList, he]
  | y :: ys, fuel, k, o, hw, hne, hf, hb, hn => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have h0 : next k = some (.ok y) := by
      have := hn 0 (by simp)
      simpa only [Nat.add_zero, List.getElem_cons_zero] using this
    have hg : listCanGrow o (o.items.length + 1) :=
      canGrow_small o _ (by omega) (by simp at hb; omega)
    obtain ⟨o', ho', hi', hw'⟩ := (listAppend_spec o y hw).1 hg
    have hne' : o'.items ≠ [] := by rw [hi']; simp
    have hb' : ((o'.items.length + ys.length : Nat) : Int) < ssizeMax / 16 := by
      rw [hi']; simp at hb ⊢; omega
    have hn' : ∀ j (hj : j < ys.length), next (k + 1 + j) = some (.ok ys[j]) := by
      intro j hj
      have := hn (j + 1) (by simp; omega)
      rw [show k + 1 + j = k + (j + 1) by omega]
      simpa using this
    obtain ⟨r1, r2⟩ := seqTupleList_spec next ys f (k + 1) o' hw' hne' (by simp at hf; omega) hb' hn'
    have hk : k + 1 + ys.length = k + (y :: ys).length := by simp; omega
    rw [hk] at r1 r2
    have hstep : seqTupleList next (f + 1) k o = seqTupleList next f (k + 1) o' := by
      simp only [seqTupleList, h0, ho']
    refine ⟨fun h => ?_, fun e h => ?_⟩
    · rw [hstep, r1 h, hi']; simp
    · rw [hstep, r2 e h]

/-- The buffer phase: up to 8 items in the buffer, then the list phase with the 8 in a 16-slot list. -/
theorem seqTupleBuf_spec (next : Nat → Option (Py α)) (fuel : Nat) : ∀ (n : Nat) (buf ys : List α),
    buf.length + n = 8 → (∀ j (hj : j < ys.length), next (buf.length + j) = some (.ok ys[j])) →
    ys.length < fuel → ((buf.length + ys.length : Nat) : Int) < ssizeMax / 16 →
    (next (buf.length + ys.length) = none →
      seqTupleBuf next fuel n buf.length buf = tupleFromArraySteal (buf ++ ys)) ∧
    (∀ e, next (buf.length + ys.length) = some (.error e) →
      seqTupleBuf next fuel n buf.length buf = .error e)
  | 0, buf, ys, h8, hn, hf, hb => by
    have hw : ({ items := buf, allocated := 16, hasItems := true } : LObj α).WF :=
      ⟨by show (0 : Int) ≤ 16; decide, by simp; omega, fun _ => rfl, by show (16 : Int) ≤ ssizeMax / 8; decide⟩
    have hne : buf ≠ [] := fun e => by simp [e] at h8
    exact seqTupleList_spec next ys fuel buf.length { items := buf, allocated := 16, hasItems := true }
      hw hne hf hb hn
  | n + 1, buf, [], h8, hn, hf, hb => by
    refine ⟨fun h => ?_, fun e h => ?_⟩
    · simp only [List.length_nil, Nat.add_zero] at h
      simp only [seqTupleBuf, h, List.append_nil]
    · simp only [List.length_nil, Nat.add_zero] at h
      simp only [seqTupleBuf, h]
  | n + 1, buf, y :: ys, h8, hn, hf, hb => by
    have h0 : next buf.length = some (.ok y) := by
      have := hn 0 (by simp)
      simpa only [Nat.add_zero, List.getElem_cons_zero] using this
    have hl : (buf ++ [y]).length = buf.length + 1 := by simp
    have hn' : ∀ j (hj : j < ys.length), next ((buf ++ [y]).length + j) = some (.ok ys[j]) := by
      intro j hj
      have := hn (j + 1) (by simp; omega)
      rw [hl, show buf.length + 1 + j = buf.length + (j + 1) by omega]
      simpa using this
    obtain ⟨r1, r2⟩ := seqTupleBuf_spec next fuel n (buf ++ [y]) ys (by rw [hl]; omega) hn'
      (by simp at hf; omega) (by rw [hl]; simp at hb ⊢; omega)
    have hk : (buf ++ [y]).length + ys.length = buf.length + (y :: ys).length := by rw [hl]; simp; omega
    rw [hk] at r1 r2
    have hstep : seqTupleBuf next fuel (n + 1) buf.length buf =
        seqTupleBuf next fuel n (buf ++ [y]).length (buf ++ [y]) := by
      rw [hl]; simp only [seqTupleBuf, h0]
    refine ⟨fun h => ?_, fun e h => ?_⟩
    · rw [hstep, r1 h]; simp
    · rw [hstep, r2 e h]

/-- `tuple(iterable)` and `tuple.__new__(type, iterable)` (`tuple_new_impl`, tupleobject.c:807-820,
with `PySequence_Tuple`, Objects/abstract.c:2004-2078) for every argument, and `tuple(...)`'s argument
checks (`tuple_vectorcall`, tupleobject.c:822-841):

* `tuple()` is the singleton; `tuple(t)` is `t` for an exact tuple, `tuple(l)` is `PyList_AsTuple`;
* a non-iterable raises `TypeError("'<type>' object is not iterable")`, and the exception of
  `PyObject_GetIter` (a raising `__iter__`) is the result;
* for every iterator that yields `xs` and then stops, the result is a tuple of `xs` (the singleton
  for none), tracked; if it raises instead of stopping, at any call and in either phase of the C
  loop (the 8-slot buffer or the list after it), that exception is the result;
* the iterator's `__length_hint__` is never asked;
* for a subclass, `tuple_subtype_new` is `tuple(iterable)` copied into a fresh instance of the
  subclass, with no cached hash and tracked, even with no argument (not the singleton), and with the
  exception of `tuple(iterable)` when that fails;
* `tuple(...)` refuses keyword arguments before it counts the positional ones, and more than one
  positional argument with `TypeError("tuple expected at most 1 argument, got N")`.

Hypotheses: the iterator stops after fewer than `PY_SSIZE_T_MAX / 16` items (past that
`list_resize` may raise `MemoryError`, far beyond any memory), and `fuel` exceeds its item count
(`fuel` bounds the model's loop, it is not a Python quantity). `<type>` is cut by `%.200s`. -/
def TupleNewIterable : Prop :=
  ∀ (α : Type) (mt : α → Bool) (fuel : Nat) (t : Tup α) (l : List α) (name : String) (e : PyExc)
    (src : TIter α) (xs : List α) (it : Option (TupArg α)) (args : List (TupArg α)) (a : TupArg α)
    (nkw : Nat),
    tupleNewExact mt fuel (none : Option (TupArg α)) = .ok .empty ∧
    tupleNewExact mt fuel (some (.exactTuple t)) = .ok (.arg 0) ∧
    tupleNewExact mt fuel (some (.exactList l)) = tupleFromArray mt l ∧
    tupleNewExact mt fuel (some (.notIterable name : TupArg α)) =
      .error (.typeError s!"'{trunc200 name}' object is not iterable") ∧
    tupleNewExact mt fuel (some (.iter (.error e) : TupArg α)) = .error e ∧
    ((∀ j (hj : j < xs.length), src.next j = some (.ok xs[j])) → xs.length < fuel →
      (xs.length : Int) < ssizeMax / 16 →
      (src.next xs.length = none → tupleNewExact mt fuel (some (.iter (.ok src))) =
        .ok (if xs = [] then .empty else .fresh { items := xs, tracked := true })) ∧
      (src.next xs.length = some (.error e) → tupleNewExact mt fuel (some (.iter (.ok src))) = .error e)) ∧
    (∀ h, tupleNewExact mt fuel (some (.iter (.ok { src with hint := h }))) =
      tupleNewExact mt fuel (some (.iter (.ok src)))) ∧
    tupleNewImpl mt fuel true it = tupleNewExact mt fuel it ∧
    (∀ e', tupleNewExact mt fuel it = .error e' → tupleNewImpl mt fuel false it = .error e') ∧
    (∀ r, tupleNewExact mt fuel it = .ok r → tupleNewImpl mt fuel false it =
      .ok (.fresh { items := r.items (TupArg.selfItems it) [], exact := false, tracked := true, hash := -1 })) ∧
    tupleNewImpl mt fuel false (none : Option (TupArg α)) =
      .ok (.fresh { items := [], exact := false, tracked := true, hash := -1 }) ∧
    tupleNewImpl mt fuel false (some (.exactTuple t)) =
      .ok (.fresh { items := t.items, exact := false, tracked := true, hash := -1 }) ∧
    (nkw ≠ 0 → tupleVectorcall mt fuel args nkw = .error (.typeError "tuple() takes no keyword arguments")) ∧
    (2 ≤ args.length → tupleVectorcall mt fuel args 0 =
      .error (.typeError s!"tuple expected at most 1 argument, got {args.length}")) ∧
    tupleVectorcall mt fuel [a] 0 = tupleNewExact mt fuel (some a) ∧
    tupleVectorcall mt fuel ([] : List (TupArg α)) 0 = .ok .empty

theorem tupleNewIterable_proven : TupleNewIterable := by
  intro α mt fuel t l name e src xs it args a nkw
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun hn hf hb => ?_, fun h => rfl, rfl, fun e' h => ?_, fun r h => ?_,
    rfl, rfl, fun h => ?_, fun h => ?_, rfl, rfl⟩
  · have hlim : (xs.length : Int) ≤ tupleLimit := by
      have : ssizeMax / 16 ≤ tupleLimit := by decide
      omega
    obtain ⟨r1, r2⟩ := seqTupleBuf_spec src.next fuel 8 [] xs (by simp) (by simpa using hn) hf (by simpa using hb)
    simp only [List.length_nil, Nat.zero_add, List.nil_append] at r1 r2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · show seqTupleBuf src.next fuel 8 0 [] = _
      rw [r1 h, steal_spec xs hlim]
    · exact r2 e h
  · simp only [tupleNewImpl, Bool.not_false, if_true, tupleSubtypeNew, h]
  · simp only [tupleNewImpl, Bool.not_false, if_true, tupleSubtypeNew, h]
  · simp [tupleVectorcall, h]
  · have h1 : ¬ args.length ≤ 1 := by omega
    simp [tupleVectorcall, show args.length > 1 by omega]

/-! ## Rich comparison and `t[item]` -/

/-- `tuple_richcompare` (tupleobject.c:737-788) returns `NotImplemented` (the outer `none`) when either
operand is not a tuple (:744-745), so `(1,).__eq__([1])` is `NotImplemented` and Python then tries the
reflected method; for two tuples, subclass instances included, it is the item comparison
`tupleRichcompare`, which `CompareAgree` and `CompareReflexive` pin. -/
def TupleRichcompareAny : Prop :=
  ∀ (α ρ : Type) (E : ElemOps α ρ) (op : CmpOp) (v w : List α),
    tupleRichcompareAny E op (some v) none = none ∧
    tupleRichcompareAny E op none (some w) = none ∧
    tupleRichcompareAny E op (none : Option (List α)) none = none ∧
    tupleRichcompareAny E op (some v) (some w) = some (tupleRichcompare E op v w)

theorem tupleRichcompareAny_proven : TupleRichcompareAny := by
  intro α ρ E op v w
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `t[item]`, `tuple_subscript` (tupleobject.c:900-954), on every arm:

* an object with `__index__` runs it first (:905): if it raises, that exception; if its value does
  not fit `Py_ssize_t`, `IndexError("cannot fit '<type>' into an index-sized integer")`; otherwise a
  negative index has the size added (:908-909), and the result is the item there, or
  `IndexError("tuple index out of range")` outside `[-len, len)` (`tuple_item`, :434-443);
* an `int` (a subclass too) is the same with no code run;
* a slice is `tupleGetSlice` (:911-946), which `SliceReads` pins;
* anything else is `TypeError("tuple indices must be integers or slices, not <type>")` (:948-952).

Hypothesis: a tuple has at most `PY_SSIZE_T_MAX` items (type invariant). `<type>` is cut by
`%.200s` (`trunc200`). -/
def TupleSubscriptDispatch : Prop :=
  ∀ (α : Type) (a : Tup α) (tp : String) (r : Py Int) (s : Slice),
    (a.items.length : Int) ≤ ssizeMax →
    (∀ e, r = .error e → tupleSubscript a (.index tp r) = .error e) ∧
    (∀ n, r = .ok n →
      (¬ (ssizeMin ≤ n ∧ n ≤ ssizeMax) → tupleSubscript a (.index tp r) =
        .error (.indexError s!"cannot fit '{trunc200 tp}' into an index-sized integer")) ∧
      (-(a.items.length : Int) ≤ n → n < a.items.length →
        ∃ x, a.items[(if n < 0 then n + (a.items.length : Int) else n).toNat]? = some x ∧
          tupleSubscript a (.index tp r) = .ok (.inl x)) ∧
      (ssizeMin ≤ n → n ≤ ssizeMax → ¬ (-(a.items.length : Int) ≤ n ∧ n < a.items.length) →
        tupleSubscript a (.index tp r) = .error (.indexError "tuple index out of range"))) ∧
    (∀ n, tupleSubscript a (.int n tp) = tupleSubscript a (.index tp (.ok n))) ∧
    (∀ x, tupleGetSlice a s = .ok x → tupleSubscript a (.slice s) = .ok (.inr x)) ∧
    (∀ e, tupleGetSlice a s = .error e → tupleSubscript a (.slice s) = .error e) ∧
    tupleSubscript a (.other tp) =
      .error (.typeError s!"tuple indices must be integers or slices, not {trunc200 tp}")

theorem tupleSubscriptDispatch_proven : TupleSubscriptDispatch := by
  intro α a tp r s hl
  have hM : ssizeMax = 9223372036854775807 := by decide
  have hm : ssizeMin = -9223372036854775808 := by decide
  refine ⟨fun e h => ?_, fun n h => ⟨fun hn => ?_, fun h3 h4 => ?_, fun h1 h2 h3 => ?_⟩,
    fun n => rfl, fun x h => ?_, fun e h => ?_, rfl⟩
  · subst h; rfl
  · subst h; simp only [tupleSubscript, tupleSubscript.idxArm, asSsizeIndexError, if_neg hn]
  · subst h
    have hfit : ssizeMin ≤ n ∧ n ≤ ssizeMax := by omega
    have hk0 : 0 ≤ (if n < 0 then n + (a.items.length : Int) else n) := by split <;> omega
    have hk1 : (if n < 0 then n + (a.items.length : Int) else n) < a.items.length := by split <;> omega
    generalize hk : (if n < 0 then n + (a.items.length : Int) else n) = k at hk0 hk1
    have hlt : k.toNat < a.items.length := by omega
    refine ⟨a.items[k.toNat], List.getElem?_eq_getElem hlt, ?_⟩
    simp only [tupleSubscript, tupleSubscript.idxArm, asSsizeIndexError, if_pos hfit, hk, tupleItem]
    rw [if_neg (by omega)]
    simp [slot, hk0, List.getElem?_eq_getElem hlt]
  · subst h
    have hout : ¬ (0 ≤ (if n < 0 then n + (a.items.length : Int) else n) ∧
        (if n < 0 then n + (a.items.length : Int) else n) < a.items.length) := by
      intro hh; apply h3; split at hh <;> omega
    simp only [tupleSubscript, tupleSubscript.idxArm, asSsizeIndexError, if_pos (And.intro h1 h2), tupleItem]
    rw [if_pos (by omega)]
  · simp only [tupleSubscript, h]
  · simp only [tupleSubscript, h]

/-! ## The iterator's `__reduce__` and `__setstate__` -/

/-- `tupleiter_reduce` (tupleobject.c:1195-1214) and `tupleiter_setstate` (:1216-1231) on every branch,
for every builtins lookup (one that runs code, such as a key whose `__eq__` exhausts the iterator, as
in gh-101765, or fails):

* the lookup runs first, and its result names the callable; `it_seq` and the index are read from
  the iterator as the lookup left it: a live iterator gives `(iter, (seq,), index)` with the whole
  tuple and the index, an exhausted one `(iter, ((),))`, and a failed lookup is the result;
* `__setstate__(s)` for an int `s` in `Py_ssize_t` sets the index of a live iterator to
  `max(0, min(s, len))` and leaves an exhausted one alone; an int outside `Py_ssize_t` raises
  `OverflowError`, and a non-int `TypeError("an integer is required")`;
* so unpickling `__reduce__` rebuilds the very iterator state, for every reachable state
  (`0 <= index <= len`, the invariant `tuple_iter`, `tupleiter_next` and `tupleiter_setstate` keep),
  and an exhausted iterator rebuilds as `iter(())`. -/
def TupleIterReduceForm : Prop :=
  ∀ (α β : Type) (g : TupleIter α → Py β × TupleIter α) (it : TupleIter α) (s : Int) (c : β),
    (∀ c it', g it = (.ok c, it') → tupleIterReduce g it =
      (.ok (match it'.seq with | some q => .live c q it'.index | none => .empty c), it')) ∧
    (∀ e it', g it = (.error e, it') → tupleIterReduce g it = (.error e, it')) ∧
    (∀ q, it.seq = some q → ssizeMin ≤ s → s ≤ ssizeMax →
      tupleIterSetstate it s = .ok { it with index := max 0 (min s q.length) }) ∧
    (it.seq = none → ssizeMin ≤ s → s ≤ ssizeMax → tupleIterSetstate it s = .ok it) ∧
    (¬ (ssizeMin ≤ s ∧ s ≤ ssizeMax) →
      tupleIterSetstate it s = .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
    tupleIterSetstateObj it none = .error (.typeError "an integer is required") ∧
    (∀ q, it.seq = some q → 0 ≤ it.index → it.index ≤ q.length → (q.length : Int) ≤ ssizeMax →
      tupleIterReduce (fun i => (.ok c, i)) it = (.ok (.live c q it.index), it) ∧
      tupleIterRebuild (TIterReduce.live c q it.index) = .ok it) ∧
    (it.seq = none → tupleIterReduce (fun i => (.ok c, i)) it = (.ok (.empty c), it) ∧
      tupleIterRebuild (TIterReduce.empty c : TIterReduce β α) = .ok (tupleIter []))

theorem tupleIterReduceForm_proven : TupleIterReduceForm := by
  intro α β g it s c
  have hM : ssizeMax = 9223372036854775807 := by decide
  have hm : ssizeMin = -9223372036854775808 := by decide
  refine ⟨fun c it' h => ?_, fun e it' h => ?_, fun q hq h0 h1 => ?_, fun hq h0 h1 => ?_, fun h => ?_, rfl,
    fun q hq h0 h1 h2 => ?_, fun hq => ?_⟩
  · simp only [tupleIterReduce, h]
    split <;> simp_all
  · simp only [tupleIterReduce, h]
  · have ha : PyLean.Sequences.asSsize s = .ok s := by
      unfold PyLean.Sequences.asSsize; rw [if_pos ⟨h0, h1⟩]
    simp only [tupleIterSetstate, ha, hq, bind, Except.bind, pure, Except.pure]
    congr 2
    split <;> (try split) <;> omega
  · have ha : PyLean.Sequences.asSsize s = .ok s := by
      unfold PyLean.Sequences.asSsize; rw [if_pos ⟨h0, h1⟩]
    simp only [tupleIterSetstate, ha, hq, bind, Except.bind]
  · have ha : PyLean.Sequences.asSsize s =
        .error (.overflowError "Python int too large to convert to C ssize_t") := by
      unfold PyLean.Sequences.asSsize; rw [if_neg h]
    simp only [tupleIterSetstate, ha, bind, Except.bind]
  · refine ⟨by simp [tupleIterReduce, hq], ?_⟩
    have ha : PyLean.Sequences.asSsize it.index = .ok it.index := by
      unfold PyLean.Sequences.asSsize; rw [if_pos ⟨by omega, by omega⟩]
    obtain ⟨i, sq⟩ := it
    simp only at hq h0 h1
    subst hq
    simp only [tupleIterRebuild, tupleIterSetstate, tupleIter, ha, bind, Except.bind, pure, Except.pure]
    rw [if_neg (by omega), if_neg (by omega)]
  · exact ⟨by simp [tupleIterReduce, hq], rfl⟩

/-! ## `hash` -/

/-- `hash(t)` with no cached value is the loop, for every element type and every element hash
(`tuple_hash`, tupleobject.c:371-414):

* when every element hashes, to a value other than `-1`, the result is
  `hashFinish(hashRounds(lanes, XXPRIME_5), len)` as a `Py_hash_t`, which is cached in `ob_hash`;
* the first element whose `__hash__` raises ends the loop with that exception (:393-397), whatever
  the elements after it would do, and nothing is cached;
* an element hash of `-1` reported as a success, which only a broken C `tp_hash` gives, ends it the
  same way with no exception set (C tests `lane == (Py_uhash_t)-1`, :394);
* a cached hash is returned without asking any element.

With `TupleHashOneLane`, which is about `hashRounds` and `hashFinish`, this pins the xxHash rounds of
every successful hash; an always-raising `tuple_hash` fails the first clause. -/
def TupleHashLoop : Prop :=
  ∀ (α : Type) (hashE : α → Py Int) (t : Tup α) (hs : List Int) (pre post : List α) (x : α) (e : PyExc)
    (h : Int),
    (toUhash t.hash = U64 - 1 → t.items.map hashE = hs.map .ok → (∀ v ∈ hs, toUhash v ≠ U64 - 1) →
      tupleHash hashE t =
        .ok (toHash (hashFinish (hashRounds (hs.map toUhash) XXP5) t.items.length),
             { t with hash := toHash (hashFinish (hashRounds (hs.map toUhash) XXP5) t.items.length) })) ∧
    (toUhash t.hash = U64 - 1 → t.items = pre ++ x :: post → pre.map hashE = hs.map .ok →
      (∀ v ∈ hs, toUhash v ≠ U64 - 1) →
      (hashE x = .error e → tupleHash hashE t = .error e) ∧
      (hashE x = .ok h → toUhash h = U64 - 1 → tupleHash hashE t = .error hashNoExc)) ∧
    (toUhash t.hash ≠ U64 - 1 → tupleHash hashE t = .ok (t.hash, t))

theorem hashLoop_map (hashE : α → Py Int) : ∀ (xs : List α) (hs : List Int) (acc : Nat),
    xs.map hashE = hs.map .ok → (∀ v ∈ hs, toUhash v ≠ U64 - 1) →
    hashLoop hashE xs acc = .ok (hashRounds (hs.map toUhash) acc)
  | [], [], acc, _, _ => by simp [hashLoop, hashRounds_nil]
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | x :: xs, v :: vs, acc, h, hm => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [hashLoop, h.1, if_neg (hm v (by simp)), List.map_cons, hashRounds_cons]
    exact hashLoop_map hashE xs vs _ h.2 (fun w hw => hm w (List.mem_cons_of_mem _ hw))

theorem hashLoop_stop (hashE : α → Py Int) (x : α) (post : List α) (r : Py Nat)
    (hx : ∀ acc, hashLoop hashE (x :: post) acc = r) : ∀ (pre : List α) (hs : List Int) (acc : Nat),
    pre.map hashE = hs.map .ok → (∀ v ∈ hs, toUhash v ≠ U64 - 1) →
    hashLoop hashE (pre ++ x :: post) acc = r
  | [], [], acc, _, _ => by simpa using hx acc
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | y :: ys, v :: vs, acc, h, hm => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.cons_append, hashLoop, h.1, if_neg (hm v (by simp))]
    exact hashLoop_stop hashE x post r hx ys vs _ h.2 (fun w hw => hm w (List.mem_cons_of_mem _ hw))

theorem tupleHashLoop_proven : TupleHashLoop := by
  intro α hashE t hs pre post x e h
  refine ⟨fun hc hm hn => ?_, fun hc hi hm hn => ⟨fun hx => ?_, fun hx h1 => ?_⟩, fun hc => ?_⟩
  · unfold tupleHash
    rw [if_neg (by simp [hc]), hashLoop_map hashE t.items hs XXP5 hm hn]
  · unfold tupleHash
    rw [if_neg (by simp [hc]), hi,
      hashLoop_stop hashE x post (.error e) (fun acc => by simp [hashLoop, hx]) pre hs XXP5 hm hn]
  · unfold tupleHash
    rw [if_neg (by simp [hc]), hi,
      hashLoop_stop hashE x post (.error hashNoExc) (fun acc => by simp [hashLoop, hx, h1]) pre hs XXP5 hm hn]
  · unfold tupleHash
    rw [if_pos hc]

/-! ## `repr` -/

theorem tupleReprLoop_err (elem : α → Py String) (strs : α → String) (x : α) (post : List α) (e : PyExc)
    (hx : elem x = .error e) : ∀ (pre : List α) (i : Nat) (acc : String),
    (∀ y ∈ pre, elem y = .ok (strs y)) → tupleReprLoop elem i (pre ++ x :: post) acc = .error e
  | [], i, acc, _ => by simp [tupleReprLoop, hx]
  | y :: ys, i, acc, h => by
    simp only [List.cons_append, tupleReprLoop, h y (by simp)]
    exact tupleReprLoop_err elem strs x post e hx ys (i + 1) _ (fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- `repr(t)`, `tuple_repr` (tupleobject.c:285-353), on its failure paths, for every element type and
every element `__repr__`: `()` for the empty tuple before `Py_ReprEnter` is asked (:290-292); `(...)`
for a tuple already being printed (:298-301); the exception when `Py_ReprEnter` fails (:300); and the
exception of the first element whose `__repr__` raises (or returns a non-string), whatever comes after
it (:332-334, `goto error`, :349-352). `tupleRepr` is the case where `Py_ReprEnter` succeeds. The
text of a successful `repr` is `ReprShape`. -/
def TupleReprErrors : Prop :=
  ∀ (α : Type) (elem : α → Py String) (strs : α → String) (enter : Py Bool) (items pre post : List α)
    (x : α) (e : PyExc) (b : Bool),
    tupleReprE elem (.ok b) items = tupleRepr elem b items ∧
    tupleReprE elem enter [] = .ok "()" ∧
    (items ≠ [] → tupleReprE elem (.error e) items = .error e) ∧
    (items ≠ [] → tupleReprE elem (.ok true) items = .ok "(...)") ∧
    ((∀ y ∈ pre, elem y = .ok (strs y)) → elem x = .error e →
      tupleReprE elem (.ok false) (pre ++ x :: post) = .error e)

theorem tupleReprErrors_proven : TupleReprErrors := by
  intro α elem strs enter items pre post x e b
  refine ⟨?_, rfl, fun h => ?_, fun h => ?_, fun hp hx => ?_⟩
  · unfold tupleReprE tupleRepr
    cases b <;> rfl
  · have : items.length ≠ 0 := fun hz => h (List.length_eq_zero_iff.mp hz)
    simp [tupleReprE, this]
  · have : items.length ≠ 0 := fun hz => h (List.length_eq_zero_iff.mp hz)
    simp [tupleReprE, this]
  · have : (pre ++ x :: post).length ≠ 0 := by simp
    simp only [tupleReprE, this, if_false, tupleReprBody,
      tupleReprLoop_err elem strs x post e hx pre 0 "(" hp]

/-! ## `tuple.index` -/

theorem tupleIndexLoop_none (E : ElemOps α ρ) (value : α) (stop : Int) : ∀ (xs : List α) (i : Int),
    (∀ (k : Nat) x, xs[k]? = some x → i + k < stop → richBool E .eq x value = .ok false) →
    tupleIndexLoop E value stop xs i = .ok none
  | [], i, _ => rfl
  | x :: xs, i, h => by
    unfold tupleIndexLoop
    split
    · have h0 := h 0 x rfl (by simpa using ‹i < stop›)
      rw [h0]
      exact tupleIndexLoop_none E value stop xs (i + 1) (fun k y hy hs =>
        h (k + 1) y (by simpa using hy) (by push_cast; omega))
    · rfl

theorem tupleIndexLoop_hit (E : ElemOps α ρ) (value : α) (stop : Int) (r : Py (Option Int)) :
    ∀ (m : Nat) (xs : List α) (i : Int) (y : α), xs[m]? = some y → i + m < stop →
    (∀ (k : Nat) x, k < m → xs[k]? = some x → richBool E .eq x value = .ok false) →
    (richBool E .eq y value = .ok true → r = .ok (some (i + m))) →
    (∀ e, richBool E .eq y value = .error e → r = .error e) →
    richBool E .eq y value ≠ .ok false →
    tupleIndexLoop E value stop xs i = r
  | _, [], _, _, hy, _, _, _, _, _ => by simp at hy
  | 0, x :: xs, i, y, hy, hs, _, ht, he, hnf => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
    subst hy
    unfold tupleIndexLoop
    rw [if_pos (by simpa using hs)]
    cases hc : richBool E .eq x value with
    | error err => rw [he err hc]
    | ok b =>
      cases b
      · exact absurd hc hnf
      · rw [ht hc]; simp
  | m + 1, x :: xs, i, y, hy, hs, hpre, ht, he, hnf => by
    unfold tupleIndexLoop
    rw [if_pos (by omega)]
    rw [hpre 0 x (by omega) rfl]
    exact tupleIndexLoop_hit E value stop r m xs (i + 1) y (by simpa using hy) (by push_cast at hs ⊢; omega)
      (fun k z hk hz => hpre (k + 1) z (by omega) (by simpa using hz))
      (fun h => by rw [ht h]; congr 2; push_cast; omega) he hnf

/-- `t.index(value, start, stop)`, `tuple_index_impl` (tupleobject.c:672-699), for every element type,
comparison (including raising ones) and bounds, with `(s, e)` the clipped bounds (:679-689,
`tupleIndexBounds`): the first position `i` in `[s, e)` whose item compares equal is the result, a
comparison that raises before one is found is the result, and when no item in that range compares
equal the result is `ValueError("tuple.index(x): x not in tuple")` (:697), as the docstring says
("Raises ValueError if the value is not present"); a `-1` for an absent value fails it. -/
def TupleIndexResult : Prop :=
  ∀ (α ρ : Type) (E : ElemOps α ρ) (t : List α) (value : α) (start stop : Option Int) (i : Nat) (y : α)
    (err : PyExc),
    let b := tupleIndexBounds t.length start stop
    ((∀ (k : Nat) x, t[k]? = some x → b.1 ≤ k → (k : Int) < b.2 → richBool E .eq x value = .ok false) →
      tupleIndex E t value start stop = .error (.valueError "tuple.index(x): x not in tuple")) ∧
    (t[i]? = some y → b.1 ≤ i → (i : Int) < b.2 →
      (∀ (k : Nat) x, k < i → b.1 ≤ k → t[k]? = some x → richBool E .eq x value = .ok false) →
      (richBool E .eq y value = .ok true → tupleIndex E t value start stop = .ok i) ∧
      (richBool E .eq y value = .error err → tupleIndex E t value start stop = .error err))

theorem tupleIndexBounds_start (n : Int) (start stop : Option Int) : 0 ≤ (tupleIndexBounds n start stop).1 := by
  unfold tupleIndexBounds
  simp only
  split
  · split <;> omega
  · omega

theorem tupleIndexResult_proven : TupleIndexResult := by
  intro α ρ E t value start stop i y err b
  have hs0 : 0 ≤ b.1 := tupleIndexBounds_start _ _ _
  have hb : tupleIndexBounds t.length start stop = (b.1, b.2) := rfl
  have hdrop : ∀ k : Nat, (t.drop b.1.toNat)[k]? = t[b.1.toNat + k]? := fun k => List.getElem?_drop ..
  refine ⟨fun hall => ?_, fun hy h1 h2 hpre => ⟨fun ht => ?_, fun he => ?_⟩⟩
  · have hn : tupleIndexLoop E value b.2 (t.drop b.1.toNat) b.1 = .ok none := by
      apply tupleIndexLoop_none
      intro k x hx hlt
      rw [hdrop] at hx
      exact hall _ x hx (by omega) (by push_cast; omega)
    simp only [tupleIndex, hb, hn]
  · have hy' : (t.drop b.1.toNat)[i - b.1.toNat]? = some y := by
      rw [hdrop, show b.1.toNat + (i - b.1.toNat) = i by omega]; exact hy
    have hl := tupleIndexLoop_hit E value b.2 (.ok (some (i : Int))) (i - b.1.toNat) (t.drop b.1.toNat) b.1 y
      hy' (by omega) (fun k x hk hx => by rw [hdrop] at hx; exact hpre _ x (by omega) (by omega) hx)
      (fun _ => by congr 2; omega) (fun e h => by rw [ht] at h; cases h) (by rw [ht]; simp)
    simp only [tupleIndex, hb, hl]
  · have hy' : (t.drop b.1.toNat)[i - b.1.toNat]? = some y := by
      rw [hdrop, show b.1.toNat + (i - b.1.toNat) = i by omega]; exact hy
    have hl := tupleIndexLoop_hit E value b.2 (.error err) (i - b.1.toNat) (t.drop b.1.toNat) b.1 y
      hy' (by omega) (fun k x hk hx => by rw [hdrop] at hx; exact hpre _ x (by omega) (by omega) hx)
      (fun h => by rw [he] at h; cases h) (fun e h => by rw [he] at h; cases h; rfl) (by rw [he]; simp)
    simp only [tupleIndex, hb, hl]

/-! ## `tuple_slice` and `PyTuple_GetSlice` -/

theorem fromArray_sub (mt : α → Bool) (L : List α) (h : (L.length : Int) ≤ tupleLimit) :
    tupleFromArray mt L = .ok (if L = [] then .empty else .fresh { items := L, tracked := L.any mt }) := by
  by_cases he : L = []
  · subst he; simp [tupleFromArray]
  · have h0 : L.length ≠ 0 := fun hz => he (List.length_eq_zero_iff.mp hz)
    simp only [tupleFromArray, h0, if_false, tupleAlloc_ok _ (by omega) h, he]

/-- `tuple_slice(a, ilow, ihigh)` (tupleobject.c:518-532) and `PyTuple_GetSlice(op, i, j)` (:553-561)
for every tuple and every pair of `Py_ssize_t` indices: with `lo = max(ilow, 0)` and
`hi = max(min(ihigh, len), lo)` (:522-527), the whole of an exact tuple is the tuple itself (:528-530);
otherwise the result is `PyTuple_FromArray` of the items at `lo, ..., hi - 1` (:531): the singleton
when there are none, and a fresh tuple of them, tracked iff one of them may be, otherwise.
`PyTuple_GetSlice` refuses `NULL` or a non-tuple with `SystemError` (:556-559), does not count a
negative index from the end ("Indexing from the end of the tuple is not supported",
Doc/c-api/tuple.rst), so it is the slice from `0`; and for non-negative indices it has the items of
`p[low:high]`, the Python expression the documentation names. Hypothesis: the tuple's length is one
`tuple_alloc` gives (type invariant). -/
def TupleSliceSpec : Prop :=
  ∀ (α : Type) (mt : α → Bool) (a : Tup α) (i j : Int),
    (a.items.length : Int) ≤ tupleLimit →
    let n : Int := a.items.length
    let lo := max i 0
    let hi := max (min j n) lo
    let L := (a.items.drop lo.toNat).take (hi - lo).toNat
    tupleSlice mt a i j = .ok (if lo = 0 ∧ hi = n ∧ a.exact = true then .arg 0
      else if L = [] then .empty else .fresh { items := L, tracked := L.any mt }) ∧
    (∀ k : Nat, L[k]? = if lo + k < hi then a.items[lo.toNat + k]? else none) ∧
    pyTupleGetSlice mt (none : Option (Tup α)) i j = .error systemError ∧
    pyTupleGetSlice mt (some a) i j = tupleSlice mt a i j ∧
    (i < 0 → pyTupleGetSlice mt (some a) i j = pyTupleGetSlice mt (some a) 0 j) ∧
    (a.exact = true → 0 ≤ i → 0 ≤ j → i ≤ ssizeMax → j ≤ ssizeMax →
      ∃ r r', pyTupleGetSlice mt (some a) i j = .ok r ∧ tupleGetSlice a ⟨some i, some j, none⟩ = .ok r' ∧
        r.items a.items [] = r'.items a.items [])

theorem tupleSlice_eq (mt : α → Bool) (a : Tup α) (i j : Int) (hl : (a.items.length : Int) ≤ tupleLimit)
    (L : List α) (hL : L = (a.items.drop (max i 0).toNat).take (max (min j a.items.length) (max i 0) - max i 0).toNat) :
    tupleSlice mt a i j = .ok (if max i 0 = 0 ∧ max (min j a.items.length) (max i 0) = a.items.length ∧
        a.exact = true then .arg 0
      else if L = [] then .empty else .fresh { items := L, tracked := L.any mt }) := by
  have e1 : (if i < 0 then 0 else i) = max i 0 := by split <;> omega
  have e2 : (if (if j > (a.items.length : Int) then (a.items.length : Int) else j) < max i 0 then max i 0
      else (if j > (a.items.length : Int) then (a.items.length : Int) else j)) =
      max (min j a.items.length) (max i 0) := by split <;> split <;> omega
  unfold tupleSlice
  simp only [e1, e2]
  split
  · rfl
  · rw [← hL]
    apply fromArray_sub
    rw [hL]
    simp only [List.length_take, List.length_drop]
    omega

theorem tupleSliceSpec_proven : TupleSliceSpec := by
  intro α mt a i j hl n lo hi L
  have hM : ssizeMax = 9223372036854775807 := by decide
  have hs := tupleSlice_eq mt a i j hl L rfl
  refine ⟨hs, fun k => ?_, rfl, rfl, fun h => ?_, fun he h0 h1 h2 h3 => ?_⟩
  · show ((a.items.drop lo.toNat).take (hi - lo).toNat)[k]? = _
    rw [List.getElem?_take, List.getElem?_drop]
    by_cases hk : k < (hi - lo).toNat
    · rw [if_pos hk, if_pos (by omega)]
    · rw [if_neg hk, if_neg (by omega)]
  · show tupleSlice mt a i j = tupleSlice mt a 0 j
    have : max i 0 = max (0 : Int) 0 := by omega
    rw [hs, tupleSlice_eq mt a 0 j hl L (by rw [← this])]
    rw [this]
  · have hl' : (a.items.length : Int) ≤ (ssizeMax - tupleBase) / 8 := hl
    obtain ⟨rb, rg, hb1, hb2, hb3⟩ := tupleBinarySlice_proven α mt a (some i) (some j) he hl'
    refine ⟨_, rg, hs, hb2, ?_⟩
    rw [← hb3]
    have hLdef : L = (a.items.drop (max i 0).toNat).take
        (max (min j (a.items.length : Int)) (max i 0) - max i 0).toNat := rfl
    rw [hLdef]
    have ha1 : RangeSlice.adjustOne i a.items.length 1 = min i a.items.length := by
      unfold RangeSlice.adjustOne; split <;> (try split) <;> omega
    have ha2 : RangeSlice.adjustOne j a.items.length 1 = min j a.items.length := by
      unfold RangeSlice.adjustOne; split <;> (try split) <;> omega
    have c1 : ¬ i < ssizeMin := by unfold ssizeMin; omega
    have c2 : ¬ i > ssizeMax := by omega
    have c3 : ¬ j < ssizeMin := by unfold ssizeMin; omega
    have c4 : ¬ j > ssizeMax := by omega
    have hu : unpackIndices (a.items.length : Int) ⟨some i, some j, none⟩ =
        (min i a.items.length, min j a.items.length) := by
      have hc1 : RangeSlice.clampSsize i = i := by
        unfold RangeSlice.clampSsize; rw [if_neg c1, if_neg c2]
      have hc2 : RangeSlice.clampSsize j = j := by
        unfold RangeSlice.clampSsize; rw [if_neg c3, if_neg c4]
      simp [unpackIndices, hc1, hc2, RangeSlice.adjustIndices, ha1, ha2]
    have hbin : tupleBinarySlice mt a ⟨some i, some j, none⟩ =
        if min i (a.items.length : Int) = 0 ∧ min j (a.items.length : Int) = a.items.length then .ok (.arg 0)
        else tupleFromArray mt ((a.items.drop (min i (a.items.length : Int)).toNat).take
          ((if min j (a.items.length : Int) < min i a.items.length then min i a.items.length
            else min j a.items.length) - min i a.items.length).toNat) := by
      simp only [tupleBinarySlice, hu]
    rw [hbin] at hb1
    generalize hA : a.items = A at hb1 hl ⊢
    have hmi : max i 0 = i := by omega
    simp only [hmi, he, and_true]
    by_cases cb : min i (A.length : Int) = 0 ∧ min j (A.length : Int) = A.length
    · rw [if_pos cb] at hb1
      cases hb1
      by_cases ca : i = 0 ∧ max (min j (A.length : Int)) i = A.length
      · rw [if_pos ca]
      · rw [if_neg ca]
        have hn : A.length = 0 := by omega
        have hA0 : A = [] := List.length_eq_zero_iff.mp hn
        subst hA0
        simp [TRes.items]
    · rw [if_neg cb, fromArray_sub _ _ (by simp only [List.length_take, List.length_drop]; omega)] at hb1
      cases hb1
      have ca : ¬ (i = 0 ∧ max (min j (A.length : Int)) i = A.length) := by
        intro hh; apply cb; omega
      rw [if_neg ca]
      have hL : (A.drop i.toNat).take (max (min j (A.length : Int)) i - i).toNat =
          (A.drop (min i (A.length : Int)).toNat).take
            ((if min j (A.length : Int) < min i A.length then min i A.length else min j A.length) -
              min i A.length).toNat := by
        by_cases hi : i ≤ A.length
        · have e1 : min i (A.length : Int) = i := by omega
          rw [e1]
          congr 2
          split <;> omega
        · have d1 : A.drop i.toNat = [] := List.drop_eq_nil_of_le (by omega)
          have d2 : A.drop (min i (A.length : Int)).toNat = [] := List.drop_eq_nil_of_le (by omega)
          rw [d1, d2]
          simp
      rw [hL]

end PyLean.BytesObj.Seq
