import PyLean.BytesObj.Seq.ListRows3

/-!
`list.extend`, `l += x`, `list(x)` and `PyList_Extend` through `_list_extend` (Objects/listobject.c,
CPython 3.15.2): the exact-type dispatch, the dict paths, and the generic iterator whose callbacks
may change the list.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α : Type}

theorem pairLoop_ok (pair : α → α → Py α) (f : α → α → α) :
    ∀ (ps : List (α × α)) (q : LObj α), (∀ p ∈ ps, pair p.1 p.2 = .ok (f p.1 p.2)) →
      pairLoop pair ps q = ({ q with items := q.items ++ ps.map (fun p => f p.1 p.2) }, none)
  | [], q, _ => by simp [pairLoop]
  | (k, v) :: rest, q, h => by
    have hk : pair k v = .ok (f k v) := h (k, v) (by simp)
    simp only [pairLoop, hk]
    rw [pairLoop_ok pair f rest _ (fun p hp => h p (by simp [hp]))]
    simp

theorem pairLoop_err (pair : α → α → Py α) (f : α → α → α) (k v : α) (e : PyExc) (post : List (α × α))
    (hkv : pair k v = .error e) :
    ∀ (pre : List (α × α)) (q : LObj α), (∀ p ∈ pre, pair p.1 p.2 = .ok (f p.1 p.2)) →
      pairLoop pair (pre ++ (k, v) :: post) q = ({ q with items := q.items ++ pre.map (fun p => f p.1 p.2) }, some e)
  | [], q, _ => by simp [pairLoop, hkv]
  | (a, b) :: rest, q, h => by
    have hk : pair a b = .ok (f a b) := h (a, b) (by simp)
    simp only [List.cons_append, pairLoop, hk]
    rw [pairLoop_err pair f k v e post hkv rest _ (fun p hp => h p (by simp [hp]))]
    simp

/-- `_list_extend` (listobject.c:1477-1532) and its branches, for every list with its invariant:

* the type tests are exact (`PyList_CheckExact`, `PyTuple_CheckExact`, `PyAnySet_CheckExact`,
  `PyDict_CheckExact`): an instance of a subclass, which may define its own `__iter__`, goes to
  `list_extend_iter_lock_held` with its class's iterator, not to a fast path; `l.extend(l)` is
  `l *= 2`;
* an exact dict and its keys view store the keys, its values view the values (`which_item`,
  :1418, :1434), each with success forced up to `PY_SSIZE_T_MAX / 16` items;
* the items view stores a tuple per entry; when `_PyTuple_FromPair` fails at an entry, the list keeps
  its old items and the pairs already built, and the error propagates (:1463-1466);
* `list_extend_iter_lock_held` calls `PyObject_GetIter`, then the length hint, and reads `m` after the
  hint ran (:1316);
* a failed append in the drain returns the list as the iterator left it, with the items already
  appended (:1356-1357);
* each `tp_iternext` is followed by a reread of the size (:1350), so an iterator that appends `z` to the
  list before yielding each `x` leaves `old ++ [z, x₀, z, x₁, ...]`; a loop that wrote at a cursor
  computed before the iterator ran would overwrite the `z`s. -/
def ListExtendDispatch : Prop :=
  ∀ (α : Type) (o : LObj α) (fuel : Nat) (items keys values : List α) (src : IterFx α)
    (pair : α → α → Py α), o.WF →
    listExtendAny o fuel (.list false items src) = listExtendIterFx o src fuel ∧
    listExtendAny o fuel (.tuple false items src) = listExtendIterFx o src fuel ∧
    listExtendAny o fuel (.set false items src) = listExtendIterFx o src fuel ∧
    listExtendAny o fuel (.dict false keys values src) = listExtendIterFx o src fuel ∧
    listExtendAny o fuel (.list true items src) = liftRes o (listExtendFast o items) ∧
    listExtendAny o fuel (.tuple true items src) = liftRes o (listExtendFast o items) ∧
    listExtendAny o fuel (.set true items src) = liftRes o (listExtendSized o items) ∧
    listExtendAny o fuel .same = liftRes o (listInplaceRepeat o 2) ∧
    ((o.items.length + keys.length : Int) ≤ ssizeMax / 16 →
      (∃ o', listExtendAny o fuel (.dict true keys values src) = (o', none) ∧ o'.items = o.items ++ keys) ∧
      (∃ o', listExtendAny o fuel (.keys keys values) = (o', none) ∧ o'.items = o.items ++ keys)) ∧
    ((o.items.length + values.length : Int) ≤ ssizeMax / 16 →
      ∃ o', listExtendAny o fuel (.values keys values) = (o', none) ∧ o'.items = o.items ++ values) ∧
    (∀ (f : α → α → α), keys.length = values.length → (o.items.length + keys.length : Int) ≤ ssizeMax / 16 →
      (∀ p ∈ keys.zip values, pair p.1 p.2 = .ok (f p.1 p.2)) →
      (listExtendAny o fuel (.items keys values pair)).2 = none ∧
      (listExtendAny o fuel (.items keys values pair)).1.items =
        o.items ++ (keys.zip values).map (fun p => f p.1 p.2)) ∧
    (∀ (f : α → α → α) (pre post : List (α × α)) (k v : α) (e : PyExc),
      keys.zip values = pre ++ (k, v) :: post → (o.items.length + keys.length : Int) ≤ ssizeMax / 16 →
      (∀ p ∈ pre, pair p.1 p.2 = .ok (f p.1 p.2)) → pair k v = .error e →
      (listExtendAny o fuel (.items keys values pair)).2 = some e ∧
      (listExtendAny o fuel (.items keys values pair)).1.items = o.items ++ pre.map (fun p => f p.1 p.2)) ∧
    (∀ (o0 o1 : LObj α) (n : Int), src.getIter o = (.ok (), o0) → src.hint o0 = (.ok n, o1) →
      listExtendIterFx o src fuel =
        match extendRoom o1 n with
        | .error e => (o1, some e)
        | .ok o2 => drainFx src fuel 0 o2) ∧
    (∀ (f k : Nat) (p p' : LObj α) (x : α), src.next k p = (some (.ok x), p') → p'.WF →
      ¬ ((p'.items.length : Int) < p'.allocated) → ¬ listCanGrow p' (p'.items.length + 1) →
      drainFx src (f + 1) k p = (p', some memoryError))

theorem listResize_small_ok (o : LObj α) (r : Int) (hw : o.WF) (h0 : 0 ≤ r) (h : r ≤ ssizeMax / 16) :
    ∃ a b, listResize o.allocated o.hasItems o.items.length r = .ok (a, b) := by
  have hc := canGrow_small o r h0 h
  obtain ⟨⟨a, b⟩, hr⟩ := (listResize_ok_iff o.allocated o.hasItems o.items.length r h0 hw.nonneg).1 hc
  exact ⟨a, b, hr⟩

theorem listExtendDispatch_proven : ListExtendDispatch := by
  intro α o fuel items keys values src pair hw
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun hb => ⟨?_, ?_⟩, fun hb => ?_, fun f hlen hb hp => ?_,
    fun f pre post k v e hz hb hp hkv => ?_, fun o0 o1 n hg hh => ?_, fun f k p p' x hn hw' hr hc => ?_⟩
  · obtain ⟨o', h1, h2, -⟩ := (listExtendSized_spec o keys hw).1 hb
    refine ⟨o', ?_, h2⟩
    show liftRes o (listExtendSized o (if 0 = 0 then keys else values)) = _
    rw [if_pos rfl, h1]; rfl
  · obtain ⟨o', h1, h2, -⟩ := (listExtendSized_spec o keys hw).1 hb
    refine ⟨o', ?_, h2⟩
    show liftRes o (listExtendSized o (if 0 = 0 then keys else values)) = _
    rw [if_pos rfl, h1]; rfl
  · obtain ⟨o', h1, h2, -⟩ := (listExtendSized_spec o values hw).1 hb
    refine ⟨o', ?_, h2⟩
    show liftRes o (listExtendSized o (if 1 = 0 then keys else values)) = _
    rw [if_neg (by decide), h1]; rfl
  · show (listExtendDictItems o keys values pair).2 = none ∧ (listExtendDictItems o keys values pair).1.items = _
    unfold listExtendDictItems
    simp only
    by_cases h0 : (o.items.length : Int) + keys.length = 0
    · have hk : keys = [] := List.length_eq_zero_iff.mp (by omega)
      rw [if_pos h0]
      simp [hk]
    rw [if_neg h0]
    obtain ⟨a, b, hr⟩ := listResize_small_ok o ((o.items.length : Int) + keys.length) hw (by omega) hb
    rw [hr]
    simp only
    rw [pairLoop_ok pair f _ _ hp]
    exact ⟨rfl, rfl⟩
  · show (listExtendDictItems o keys values pair).2 = some e ∧ (listExtendDictItems o keys values pair).1.items = _
    have hne : keys ≠ [] := by
      intro hk; rw [hk] at hz; simp at hz
    have h0 : ¬ ((o.items.length : Int) + keys.length = 0) := by
      have : keys.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
      omega
    unfold listExtendDictItems
    simp only
    rw [if_neg h0]
    obtain ⟨a, b, hr⟩ := listResize_small_ok o ((o.items.length : Int) + keys.length) hw (by omega) hb
    rw [hr]
    simp only
    rw [hz, pairLoop_err pair f k v e post hkv pre _ hp]
    exact ⟨rfl, rfl⟩
  · unfold listExtendIterFx
    rw [hg]
    simp only
    rw [hh]
    rfl
  · simp only [drainFx, hn]
    rw [if_neg hr, (listAppend_spec p' x hw').2 hc]

theorem extendCutBack_ok (p : LObj α) (hw : p.WF) :
    (extendCutBack p).2 = none ∧ (extendCutBack p).1.items = p.items := by
  unfold extendCutBack
  split
  · obtain ⟨⟨a, b⟩, hr⟩ := (listResizeExact_proven p.allocated p.hasItems p.items.length p.items.length
      hw.nonneg (by omega)).2.2.2.2.2.1 (by omega)
    rw [hr]
    exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- `list.extend` from an iterator that appends `z` to the list before it yields each item, for every
list with its invariant and every such iterator: because `list_extend_iter_lock_held` rereads
`Py_SIZE(self)` and `allocated` after each `tp_iternext` (listobject.c:1350), each `z` lands before the
item that follows it, and the result is `old ++ [z, x₀, z, x₁, ...]`. A drain that stored the items at a
cursor taken before the iterator ran would overwrite the `z`s. Hypotheses: the iterator's effect keeps
the list's invariant, and the total stays below `PY_SSIZE_T_MAX / 16` items (no `MemoryError`). -/
def ListExtendIterReentrant : Prop :=
  ∀ (α : Type) (src : IterFx α) (xs : List α) (z : α) (fuel : Nat) (o : LObj α),
    (∀ (k : Nat) (hk : k < xs.length) (p : LObj α), p.WF → (src.next k p).1 = some (.ok xs[k]) ∧
      ((src.next k p).2).items = p.items ++ [z] ∧ ((src.next k p).2).WF) →
    (∀ p, src.next xs.length p = (none, p)) →
    o.WF → xs.length < fuel → ((o.items.length + 2 * xs.length : Nat) : Int) ≤ ssizeMax / 16 →
    (drainFx src fuel 0 o).2 = none ∧
    (drainFx src fuel 0 o).1.items = o.items ++ (xs.map (fun x => [z, x])).flatten

theorem drainFx_interleave (src : IterFx α) (xs : List α) (z : α)
    (hs : ∀ (k : Nat) (hk : k < xs.length) (p : LObj α), p.WF → (src.next k p).1 = some (.ok xs[k]) ∧
      ((src.next k p).2).items = p.items ++ [z] ∧ ((src.next k p).2).WF)
    (he : ∀ p, src.next xs.length p = (none, p)) :
    ∀ (f k : Nat) (p : LObj α), p.WF → k ≤ xs.length → xs.length - k < f →
      ((p.items.length + 2 * (xs.length - k) : Nat) : Int) ≤ ssizeMax / 16 →
      (drainFx src f k p).2 = none ∧
      (drainFx src f k p).1.items = p.items ++ ((xs.drop k).map (fun x => [z, x])).flatten := by
  intro f
  induction f with
  | zero => intro k p _ _ h; omega
  | succ f ih =>
    intro k p hw hk hf hb
    by_cases hlt : k < xs.length
    · obtain ⟨h1, h2, h3⟩ := hs k hlt p hw
      have hn : src.next k p = (some (.ok xs[k]), (src.next k p).2) := by rw [← h1]
      generalize hq : (src.next k p).2 = q at hn h2 h3
      have hdrop : xs.drop k = xs[k] :: xs.drop (k + 1) := List.drop_eq_getElem_cons hlt
      have hql : q.items.length = p.items.length + 1 := by rw [h2]; simp
      simp only [drainFx, hn]
      by_cases hr : (q.items.length : Int) < q.allocated
      · rw [if_pos hr]
        have hcov : (((q.items ++ [xs[k]]).length : Nat) : Int) ≤ q.allocated := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        have hw2 : ({ q with items := q.items ++ [xs[k]] } : LObj α).WF :=
          ⟨h3.nonneg, hcov, h3.array, h3.bytes⟩
        have hb2 : ((({ q with items := q.items ++ [xs[k]] } : LObj α).items.length +
            2 * (xs.length - (k + 1)) : Nat) : Int) ≤ ssizeMax / 16 := by
          show (((q.items ++ [xs[k]]).length + 2 * (xs.length - (k + 1)) : Nat) : Int) ≤ ssizeMax / 16
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        obtain ⟨r1, r2⟩ := ih (k + 1) _ hw2 (by omega) (by omega) hb2
        refine ⟨r1, ?_⟩
        rw [r2]
        show (q.items ++ [xs[k]]) ++ _ = _
        rw [h2, hdrop]
        simp only [List.map_cons, List.flatten_cons, List.append_assoc, List.cons_append, List.nil_append]
      · rw [if_neg hr]
        obtain ⟨o', a1, a2, a3⟩ := (listAppend_spec q xs[k] h3).1
          (canGrow_small q _ (by omega) (by omega))
        rw [a1]
        simp only
        have hb2 : ((o'.items.length + 2 * (xs.length - (k + 1)) : Nat) : Int) ≤ ssizeMax / 16 := by
          rw [a2]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        obtain ⟨r1, r2⟩ := ih (k + 1) o' a3 (by omega) (by omega) hb2
        refine ⟨r1, ?_⟩
        rw [r2, a2, h2, hdrop]
        simp only [List.map_cons, List.flatten_cons, List.append_assoc, List.cons_append, List.nil_append]
    · have hkl : k = xs.length := by omega
      subst hkl
      simp only [drainFx, he]
      obtain ⟨c1, c2⟩ := extendCutBack_ok p hw
      refine ⟨c1, ?_⟩
      rw [c2, List.drop_eq_nil_of_le (by omega)]
      simp

theorem listExtendIterReentrant_proven : ListExtendIterReentrant := by
  intro α src xs z fuel o hs he hw hf hb
  have := drainFx_interleave src xs z hs he fuel 0 o hw (by omega) (by omega) (by simpa using hb)
  simpa using this

end PyLean.BytesObj.Seq
