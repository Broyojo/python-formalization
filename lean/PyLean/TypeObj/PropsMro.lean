import PyLean.TypeObj.PropsCall

/-!
C3 and class-creation properties. The C3 statements are over classes as addresses and hold
for every hierarchy; `C3Monotonic` is the single-step statement and `C3MonotonicTransitive`
the one the comment at `Objects/typeobject.c:3135` makes: the MRO of a class extends the MRO
of each of its superclasses without reordering, for any depth of inheritance.
-/

namespace PyLean.TypeObj

/-- **Local precedence**: the MRO keeps the bases in their declared order. -/
def C3LocalPrecedence : Prop :=
  ∀ (self : Addr) (baseMro : Addr → Option (List Addr)) (bases mro : List Addr),
    c3Merge self baseMro bases = .ok mro → ∃ m, mro = self :: m ∧ bases.Sublist m

theorem c3LocalPrecedence_proven : C3LocalPrecedence := by
  intro self baseMro bases mro h
  obtain ⟨m, h1, h2, _⟩ := c3Merge_order self baseMro bases mro h
  exact ⟨m, h1, h2⟩

/-- **Monotonicity, one level**: the MRO extends the MRO of each base without reordering. -/
def C3Monotonic : Prop :=
  ∀ (self : Addr) (baseMro : Addr → Option (List Addr)) (bases mro : List Addr),
    c3Merge self baseMro bases = .ok mro →
    ∃ m, mro = self :: m ∧ ∀ b ∈ bases, ((baseMro b).getD []).Sublist m

theorem c3Monotonic_proven : C3Monotonic := by
  intro self baseMro bases mro h
  obtain ⟨m, h1, _, h3⟩ := c3Merge_order self baseMro bases mro h
  exact ⟨m, h1, h3⟩

/-- `pmerge` needs no fuel limit: it stops within the number of items. -/
def C3Terminates : Prop :=
  ∀ (rests : List (List Addr)) (fuel : Nat), totalLen rests < fuel → pmerge fuel rests ≠ .fuel

theorem c3Terminates_proven : C3Terminates := fun rests fuel h => pmerge_total fuel rests h

/-- **No duplicates**: linearizing duplicate-free MROs and a duplicate-free tuple of bases
gives a list without repeats. -/
def C3NoDuplicates : Prop :=
  ∀ (fuel : Nat) (rests : List (List Addr)) (m : List Addr),
    pmerge fuel rests = .ok m → (∀ r ∈ rests, r.Nodup) → m.Nodup

theorem c3NoDuplicates_proven : C3NoDuplicates := fun fuel rests m h hnd =>
  pmerge_nodup fuel rests m h hnd

/-- Every merged class came from an input, and every input class is merged: the merge is
exact. -/
def C3Complete : Prop :=
  ∀ (fuel : Nat) (rests : List (List Addr)) (m : List Addr),
    pmerge fuel rests = .ok m → ∀ x, x ∈ m ↔ ∃ r ∈ rests, x ∈ r

theorem c3Complete_proven : C3Complete := by
  intro fuel rests m h x
  constructor
  · exact pmerge_mem fuel rests m h x
  · rintro ⟨r, hr, hx⟩
    exact (pmerge_sublist fuel rests m h r hr).mem hx

/-- The fast path for one base agrees with the general algorithm, on an MRO that starts
with the base and has no repeats. -/
def C3FastPathAgrees : Prop :=
  ∀ (self b : Addr) (baseMro : Addr → Option (List Addr)) (m : List Addr),
    baseMro b = some (b :: m) → (b :: m).Nodup →
    mroImpl self baseMro [b] = c3Merge self baseMro [b]

theorem c3FastPathAgrees_proven : C3FastPathAgrees := by
  intro self b baseMro m hm hnd
  rw [fast_slow_agree self b baseMro m hm hnd]
  simp [mroImpl, firstIncomplete, hm]

/-- **The failure rule**: `pmerge` fails exactly when lists remain and each head is in the
tail of some list, so no candidate exists. -/
def C3FailureRule : Prop :=
  ∀ (fuel : Nat) (rests r : List (List Addr)),
    pmerge fuel rests = .conflict r →
    candidateOf r r = none ∧ r.all List.isEmpty = false

theorem c3FailureRule_proven : C3FailureRule := by
  intro fuel rests r h
  induction fuel generalizing rests with
  | zero => simp [pmerge] at h
  | succ n ih =>
    simp only [pmerge] at h
    cases hc : candidateOf rests rests with
    | some c =>
      rw [hc] at h
      simp only at h
      cases hp : pmerge n (advance c rests) with
      | ok m => rw [hp] at h; simp at h
      | conflict r' =>
        rw [hp] at h
        simp only [Merge.conflict.injEq] at h
        subst h
        exact ih _ hp
      | fuel => rw [hp] at h; simp at h
    | none =>
      rw [hc] at h
      simp only at h
      by_cases ha : rests.all List.isEmpty = true
      · simp [ha] at h
      · have ha' : rests.all List.isEmpty = false := by simpa using ha
        simp only [ha', Bool.false_eq_true, ite_false, Merge.conflict.injEq] at h
        subst h
        exact ⟨hc, ha'⟩

/-- `check_duplicates` catches any repeated base. -/
def C3DuplicateBaseRejected : Prop :=
  ∀ (l : List Addr), l.Nodup → firstDuplicate l = none

theorem c3DuplicateBaseRejected_proven : C3DuplicateBaseRejected := by
  intro l h
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ∉ xs := (List.nodup_cons.mp h).1
    simp [firstDuplicate, hx, ih (List.nodup_cons.mp h).2]

/-- A hierarchy linearized by `mro_implementation`: every class's MRO is what the algorithm
returns from its bases, and `rank` witnesses that inheritance is acyclic. Both are type
invariants of classes made by `type_new` with the default `mro()`. -/
structure Linearized (bases mro : Addr → List Addr) (rank : Addr → Nat) : Prop where
  ok : ∀ t, mroImpl t (fun b => some (mro b)) (bases t) = .ok (mro t)
  acyclic : ∀ t, ∀ b ∈ bases t, rank b < rank t

theorem mem_mro_step (bases mro : Addr → List Addr) (t s : Addr)
    (h : mroImpl t (fun b => some (mro b)) (bases t) = .ok (mro t)) (hs : s ∈ mro t) :
    s = t ∨ ∃ b ∈ bases t, s = b ∨ s ∈ mro b := by
  simp only [mroImpl] at h
  cases hi : firstIncomplete (fun b => some (mro b)) (bases t) with
  | some b => rw [hi] at h; simp at h
  | none =>
    rw [hi] at h
    simp only at h
    cases hb : bases t with
    | nil =>
      rw [hb] at h
      simp only [c3Merge, firstDuplicate, toMerge, List.map_nil, List.nil_append] at h
      have hp : pmerge (totalLen ([[]] : List (List Addr)) + 1) [[]] = (.ok [] : Merge Addr) := by
        simp [pmerge, candidateOf]
      rw [hp] at h
      simp only [Lin.ok.injEq] at h
      rw [← h] at hs
      simp at hs
      exact Or.inl hs
    | cons b rest =>
      cases rest with
      | nil =>
        rw [hb] at h
        simp only [Option.getD_some, Lin.ok.injEq] at h
        rw [← h] at hs
        rcases List.mem_cons.mp hs with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨b, by simp, Or.inr h1⟩
      | cons c more =>
        rw [hb] at h
        simp only at h
        simp only [c3Merge] at h
        cases hd : firstDuplicate (b :: c :: more) with
        | some d => rw [hd] at h; simp at h
        | none =>
          rw [hd] at h
          simp only at h
          cases hp : pmerge (totalLen (toMerge (fun b => some (mro b)) (b :: c :: more)) + 1)
              (toMerge (fun b => some (mro b)) (b :: c :: more)) with
          | conflict r => rw [hp] at h; simp at h
          | fuel => rw [hp] at h; simp at h
          | ok m =>
            rw [hp] at h
            simp only [Lin.ok.injEq] at h
            rw [← h] at hs
            rcases List.mem_cons.mp hs with h1 | h1
            · exact Or.inl h1
            · obtain ⟨r, hr, hx⟩ := pmerge_mem _ _ _ hp s h1
              simp only [toMerge, List.mem_append, List.mem_map, List.mem_singleton,
                Option.getD_some] at hr
              rcases hr with ⟨x, hx1, rfl⟩ | rfl
              · exact Or.inr ⟨x, hx1, Or.inr hx⟩
              · exact Or.inr ⟨s, hx, Or.inl rfl⟩

theorem base_mro_sublist (bases mro : Addr → List Addr) (t b : Addr)
    (h : mroImpl t (fun b => some (mro b)) (bases t) = .ok (mro t)) (hb : b ∈ bases t) :
    (mro b).Sublist (mro t) := by
  simp only [mroImpl] at h
  cases hi : firstIncomplete (fun b => some (mro b)) (bases t) with
  | some x => rw [hi] at h; simp at h
  | none =>
    rw [hi] at h
    simp only at h
    cases hbs : bases t with
    | nil => rw [hbs] at hb; simp at hb
    | cons x rest =>
      cases rest with
      | nil =>
        rw [hbs] at h hb
        simp only [List.mem_singleton] at hb
        subst hb
        simp only [Option.getD_some, Lin.ok.injEq] at h
        rw [← h]
        exact List.sublist_cons_self _ _
      | cons c more =>
        rw [hbs] at h hb
        simp only at h
        obtain ⟨m, h1, _, h3⟩ := c3Merge_order t _ _ _ h
        rw [h1]
        have := h3 b hb
        simp only [Option.getD_some] at this
        exact this.cons t

theorem self_head (bases mro : Addr → List Addr) (t : Addr)
    (h : mroImpl t (fun b => some (mro b)) (bases t) = .ok (mro t)) :
    ∃ m, mro t = t :: m := by
  simp only [mroImpl] at h
  cases hi : firstIncomplete (fun b => some (mro b)) (bases t) with
  | some x => rw [hi] at h; simp at h
  | none =>
    rw [hi] at h
    simp only at h
    split at h
    · simp only [Lin.ok.injEq] at h
      exact ⟨_, h.symm⟩
    · simp only [c3Merge] at h
      split at h
      · simp at h
      · split at h
        · rename_i m _
          simp only [Lin.ok.injEq] at h
          exact ⟨m, h.symm⟩
        · simp at h
        · simp at h

/-- **Monotonicity at every depth**: in a linearized hierarchy, for every class `s` in the
MRO of `t`, the MRO of `s` is a sublist of the MRO of `t`: the promise of
`Objects/typeobject.c:3135-3137`. Together with `pmerge_nodup` this says that if `A`
precedes `B` in the MRO of a class, it does so in the MRO of every subclass. -/
def C3MonotonicTransitive : Prop :=
  ∀ (bases mro : Addr → List Addr) (rank : Addr → Nat), Linearized bases mro rank →
    ∀ t s, s ∈ mro t → (mro s).Sublist (mro t)

theorem c3MonotonicTransitive_proven : C3MonotonicTransitive := by
  intro bases mro rank hl
  have key : ∀ n t s, rank t = n → s ∈ mro t → (mro s).Sublist (mro t) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro t s hr hs
      rcases mem_mro_step bases mro t s (hl.ok t) hs with rfl | ⟨b, hb, h⟩
      · exact List.Sublist.refl _
      · have hbt := base_mro_sublist bases mro t b (hl.ok t) hb
        rcases h with rfl | h
        · exact hbt
        · have := ih (rank b) (by have := hl.acyclic t b hb; omega) b s rfl h
          exact this.trans hbt
  intro t s hs
  exact key _ t s rfl hs

/-- In a linearized hierarchy each class heads its own MRO. -/
def C3SelfHead : Prop :=
  ∀ (bases mro : Addr → List Addr) (rank : Addr → Nat), Linearized bases mro rank →
    ∀ t, ∃ m, mro t = t :: m

theorem c3SelfHead_proven : C3SelfHead := fun bases mro _ hl t =>
  self_head bases mro t (hl.ok t)

/-! ## Metaclass and base selection -/

/-- `isSubtype` is reflexive on `a` and transitive: a type invariant of classes with C3
MROs, by `C3MonotonicTransitive` and `C3SelfHead`. -/
def SubtypeOrder (w : World) : Prop :=
  (∀ a, isSubtype w a a = true) ∧
  (∀ a b c, isSubtype w a b = true → isSubtype w b c = true → isSubtype w a c = true)

/-- **The winner is the most derived metaclass**: the result of
`_PyType_CalculateMetaclass` is a subclass of the starting metaclass and of the metaclass
of each base. -/
def MetaclassWinner : Prop :=
  ∀ (w : World) (bases : List Val) (start r : Addr), SubtypeOrder w →
    calculateMetaclassLoop w start bases = some r →
    isSubtype w r start = true ∧ ∀ b ∈ bases, isSubtype w r (typeOf w b) = true

theorem metaclassWinner_proven : MetaclassWinner := by
  intro w bases start r ho h
  induction bases generalizing start with
  | nil =>
    simp only [calculateMetaclassLoop, Option.some.injEq] at h
    subst h
    exact ⟨ho.1 _, by simp⟩
  | cons b rest ih =>
    simp only [calculateMetaclassLoop] at h
    split at h
    · rename_i h1
      obtain ⟨h2, h3⟩ := ih start h
      refine ⟨h2, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ho.2 _ _ _ h2 h1
      · exact h3 x hx
    · split at h
      · rename_i h1 h2
        obtain ⟨h3, h4⟩ := ih (typeOf w b) h
        refine ⟨ho.2 _ _ _ h3 h2, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h3
        · exact h4 x hx
      · simp at h

/-- **A metaclass conflict is real**: failure means two metaclasses, neither a subclass of
the other. -/
def MetaclassConflictReal : Prop :=
  ∀ (w : World) (bases : List Val) (start : Addr),
    calculateMetaclassLoop w start bases = none →
    ∃ win b, b ∈ bases ∧ isSubtype w win (typeOf w b) = false ∧
      isSubtype w (typeOf w b) win = false

theorem metaclassConflictReal_proven : MetaclassConflictReal := by
  intro w bases start h
  induction bases generalizing start with
  | nil => simp [calculateMetaclassLoop] at h
  | cons b rest ih =>
    simp only [calculateMetaclassLoop] at h
    split at h
    · obtain ⟨win, x, hx, h1, h2⟩ := ih start h
      exact ⟨win, x, List.mem_cons_of_mem _ hx, h1, h2⟩
    · rename_i h1
      split at h
      · obtain ⟨win, x, hx, h3, h4⟩ := ih _ h
        exact ⟨win, x, List.mem_cons_of_mem _ hx, h3, h4⟩
      · rename_i h2
        exact ⟨start, b, by simp, by simpa using h1, by simpa using h2⟩

/-- **`__eq__` without `__hash__` makes instances unhashable**: `type_ready_set_hash`
installs `PyObject_HashNotImplemented` and `__hash__ = None`, `Objects/typeobject.c:8781`.
Precondition: `t` is a heap type object and its `tp_hash` is NULL, which `inherit_slots`
guarantees when the class dict has `__eq__` and no `__hash__`. -/
def HashNoneWhenEqDefined : Prop :=
  ∀ (t : Addr) (c : Addr) (d : TypeData) (w w' : World),
    w.get t = .ty c d → t < w.heap.size →
    slotOf w t .tp_hash = none → NameDict.contains d.dict "__hash__" = false →
    typeReadySetHash t w = .ok () w' →
    NameDict.get? (tdata w' t).dict "__hash__" = some .none ∧
      slotOf w' t .tp_hash = some .hashNotImpl

theorem get_setCell (w : World) (t : Addr) (c : Cell) (h : t < w.heap.size) :
    (w.setCell t c).get t = c := by
  simp [World.get, World.setCell, Array.getD, h]

theorem NameDict.get?_set_same (d : NameDict) (n : Name) (v : Val) :
    NameDict.get? (NameDict.set d n v) n = some v := by
  induction d with
  | nil => simp [NameDict.set, NameDict.get?]
  | cons p rest ih =>
    obtain ⟨k, x⟩ := p
    by_cases hk : k = n
    · simp [NameDict.set, NameDict.get?, hk]
    · simp [NameDict.set, NameDict.get?, hk, ih]

theorem hashNoneWhenEqDefined_proven : HashNoneWhenEqDefined := by
  intro t c d w w' hg hs h1 h2 he
  have htd : tdata w t = d := by simp [tdata, hg]
  have hcnt : NameDict.contains (tdata w t).dict "__hash__" = false := by rw [htd]; exact h2
  simp only [typeReadySetHash, M.bind_app, getW_app, h1, Option.isNone_none, hcnt,
    Bool.not_false, Bool.and_self, ite_true, modType, modW_app, R.ok.injEq, hg] at he
  obtain ⟨_, rfl⟩ := he
  have hget := get_setCell w t (.ty c { d with
      dict := NameDict.set d.dict "__hash__" .none
      slots := setSlot d.slots .tp_hash (some .hashNotImpl) }) hs
  have htd' : tdata (w.setCell t (.ty c { d with
      dict := NameDict.set d.dict "__hash__" .none
      slots := setSlot d.slots .tp_hash (some .hashNotImpl) })) t = { d with
      dict := NameDict.set d.dict "__hash__" .none
      slots := setSlot d.slots .tp_hash (some .hashNotImpl) } := by
    simp [tdata, hget]
  constructor
  · rw [htd']
    exact NameDict.get?_set_same _ _ _
  · simp only [slotOf]
    rw [htd']
    simp [setSlot]

/-- `inherit_slots` copies `tp_richcompare` and `tp_hash` together, and only when the class
defines neither `__eq__` nor `__hash__`, `Objects/typeobject.c:8383-8394`: a class defining
`__eq__` does not inherit `tp_hash`. -/
def OverridesHashBlocksInherit : Prop :=
  ∀ (w : World) (t : Addr) (n : Name),
    (n = "__eq__" ∨ n = "__hash__") → NameDict.contains (tdata w t).dict n = true →
    overridesHash w t = true

theorem overridesHashBlocksInherit_proven : OverridesHashBlocksInherit := by
  intro w t n hn h
  rcases hn with rfl | rfl <;> simp [overridesHash, h]

/-- `__slots__ = ('__dict__', '__dict__')` fails: the second name finds `add_dict` set,
`Objects/typeobject.c:3990`. -/
def IsDunderNameShape : Prop :=
  ∀ (n : Name), isDunderName n = true →
    n.toList.length > 4 ∧ n.toList.take 2 = ['_', '_']

theorem isDunderNameShape_proven : IsDunderNameShape := by
  intro n h
  simp only [isDunderName, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2⟩

/-- `_Py_Mangle` leaves dunder names and names without a leading `__` unchanged. -/
def MangleKeepsDunders : Prop :=
  ∀ (cls name : String),
    (name.toList.take 2 ≠ ['_', '_'] ∨ name.toList.drop (name.toList.length - 2) = ['_', '_']) →
    pyMangle cls name = name

theorem mangleKeepsDunders_proven : MangleKeepsDunders := by
  intro cls name h
  rcases h with h | h
  · simp [pyMangle, h]
  · simp [pyMangle, h]

/-- A `__slots__` name that is also a class attribute raises `ValueError`, except the three
names the compiler inserts, `Objects/typeobject.c:4043-4060`. -/
def SlotNotesIdentifier : Prop :=
  ∀ (s : Val) (w : World),
    strOf w s = none →
    validIdentifier s w =
      (typeErr s!"__slots__ items must be strings, not '{trunc 200 (typeName w s)}'" : M String) w

theorem slotNotesIdentifier_proven : SlotNotesIdentifier := by
  intro s w h
  simp [validIdentifier, h]

end PyLean.TypeObj
