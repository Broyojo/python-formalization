import PyLean.TextLibs.EtreePath

/-!
The attribute dictionary of a C `Element` (Modules/_elementtree.c), CPython 3.15.2.

`self->extra->attrib` is NULL (no attributes yet), or whatever object was stored there. The
`PyDict_*` calls of `get`, `set`, `keys` and `items` are only defined on a dict or frozendict
(`PyAnyDict_Check`); on anything else they fail with `SystemError: bad argument to internal
function` (`PyErr_BadInternalCall`). 3.15's `attrib` setter and `Element()` check for a dict or
frozendict; `__setstate__` stores what it is given.

Keys and values are str. A missing `extra` and an `extra` whose attrib is NULL behave alike for
every function here except the getter, which creates both. `Element()` is modelled with a
positional `attrib` only (no keyword attributes).
-/

namespace PyLean.TextLibs.Etree

open PyLean

/-- The object in the attrib slot. -/
inductive AObj where
  | dict (items : List (S × S))
  | frozen (items : List (S × S))
  /-- Any other object, by type name. -/
  | other (tyName : String)
  deriving Repr, DecidableEq

/-- `self->extra` absent, or present with its attrib slot (`none` is NULL). -/
abbrev Slot := Option (Option AObj)

def AObj.items : AObj → List (S × S)
  | .dict i => i
  | .frozen i => i
  | .other _ => []

def badCall : PyExc := .named "SystemError" "~Objects/dictobject.c: bad argument to internal function"

/-- `dict[k] = v` on insertion-ordered items. -/
def dictSet (items : List (S × S)) (k v : S) : List (S × S) :=
  if items.any (·.1 == k) then items.map fun (a, b) => if a == k then (a, v) else (a, b) else items ++ [(k, v)]

/-- `Element(tag, attrib)`, :417-470: a non-dict attrib is refused; a nonempty one is copied
into a new dict (`_PyDict_CopyAsDict`), an empty one leaves no `extra`. -/
def initC (attrib : Option AObj) : Py Slot :=
  match attrib with
  | none => .ok none
  | some (.other t) => .error (.typeError s!"Element() argument 2 must be dict or frozendict, not {t}")
  | some a => .ok (if a.items = [] then none else some (some (.dict a.items)))

/-- The `attrib` setter, :2127-2143. -/
def setAttribC (s : Slot) (v : AObj) : Py Slot :=
  match v with
  | .other t => .error (.typeError s!"attrib must be dict or frozendict, not {t}")
  | v => let _ := s; .ok (some (some v))

/-- The `attrib` getter, :2078-2087 with `element_get_attrib`, :558-571: create `extra` and an
empty dict as needed. -/
def getAttribC (s : Slot) : Slot × AObj :=
  match s with
  | some (some a) => (s, a)
  | _ => (some (some (.dict [])), .dict [])

/-- `Element.get(key, default)`, :1453-1466: `PyDict_GetItemWithError`. -/
def getC (s : Slot) (k : S) (dflt : Option S) : Py (Option S) :=
  match s with
  | some (some (.other _)) => .error badCall
  | some (some a) => .ok (match (a.items.find? (·.1 == k)) with | some (_, v) => some v | none => dflt)
  | _ => .ok dflt

/-- `Element.set(key, value)`, :1754-1773: `PyDict_SetItem` on the (created) attrib. -/
def setC (s : Slot) (k v : S) : Slot × Py Unit :=
  let (s, a) := getAttribC s
  match a with
  | .dict i => (some (some (.dict (dictSet i k v))), .ok ())
  | .frozen _ => (s, .error (.typeError "frozendict object does not support item assignment"))
  | .other _ => (s, .error badCall)

/-- `Element.keys()` and `items()`, :1600-1621: `PyDict_Keys` / `PyDict_Items`. -/
def itemsC (s : Slot) : Py (List (S × S)) :=
  match s with
  | some (some (.other _)) => .error badCall
  | some (some a) => .ok a.items
  | _ => .ok []

/-- The `_children` entry of a pickled state. -/
inductive ChildArg where
  /-- A list of Elements. -/
  | ok
  | notList
  /-- A list holding a non-Element. -/
  | badItem
  deriving Repr, DecidableEq

/-- The state dict given to `__setstate__`: which keys it has (`extraKey` for any key outside
tag, attrib, text, tail, _children). -/
structure State where
  hasTag : Bool
  attrib : Option AObj
  children : Option ChildArg
  extraKey : Bool

/-- `__setstate__(state)` on an exact dict, :1172-1188 with `element_setstate_from_Python`,
:1140-1163, and `element_setstate_from_attributes`, :1049-1133, for the attrib slot: keyword
parsing first, then the tag, then children (which keep the old attrib), then
`Py_XSETREF(self->extra->attrib, Py_XNewRef(attrib))`, which stores any object, or NULL when the
state has children but no attrib. -/
def setstateC (s : Slot) (st : State) : Slot × Py Unit :=
  if st.extraKey then (s, .error (.typeError "~invalid keyword argument"))
  else if !st.hasTag then (s, .error (.typeError "tag may not be NULL"))
  else match st.children, st.attrib with
    | none, none => (s, .ok ())
    | some .notList, _ => (s, .error (.typeError "'_children' is not a list"))
    | some .badItem, _ => (some (s.getD none), .error (.typeError "~expected an Element"))
    | _, a => (some a, .ok ())

/-- The argument of `__setstate__`: an exact dict (its keys as `State`), or another object. -/
inductive StateArg where
  | dict (st : State)
  | other

/-- `_elementtree_Element___setstate___impl`, :1176-1188: anything but an exact dict is refused. -/
def setstateEntryC (s : Slot) (a : StateArg) : Slot × Py Unit :=
  match a with
  | .other => (s, .error (.typeError "~Don't know how to unpickle as an Element"))
  | .dict st => setstateC s st

/-! ## Properties -/

/-- The attrib slot holds NULL, a dict or a frozendict. -/
def SlotOk : Slot → Prop
  | some (some (.other _)) => False
  | _ => True

/-- Under the invariant, `get`, `set`, `keys` and `items` never raise `SystemError`. -/
def NoBadCall : Prop :=
  ∀ (s : Slot) (k v : S) (d : Option S), SlotOk s →
    getC s k d ≠ .error badCall ∧ (setC s k v).2 ≠ .error badCall ∧ itemsC s ≠ .error badCall

theorem noBadCall_proven : NoBadCall := by
  intro s k v d hs
  rcases s with _ | _ | a
  · simp [getC, setC, getAttribC, itemsC]
  · simp [getC, setC, getAttribC, itemsC]
  · cases a <;> simp_all [SlotOk, getC, setC, getAttribC, itemsC, badCall]

/-- `Element()`, the `attrib` setter and getter, and `set` keep the invariant. -/
def AttribInvariant : Prop :=
  (∀ a s', initC a = .ok s' → SlotOk s') ∧
  (∀ s v s', SlotOk s → setAttribC s v = .ok s' → SlotOk s') ∧
  (∀ s, SlotOk s → SlotOk (getAttribC s).1) ∧
  (∀ s k v, SlotOk s → SlotOk (setC s k v).1)

theorem attribInvariant_proven : AttribInvariant := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a s' h
    rcases a with _ | ⟨i⟩ | ⟨i⟩ | ⟨t⟩ <;> simp [initC] at h <;> subst h <;> (try split) <;> simp [SlotOk]
  · intro s v s' _ h
    rcases v with ⟨i⟩ | ⟨i⟩ | ⟨t⟩ <;> simp [setAttribC] at h <;> subst h <;> simp [SlotOk]
  · intro s hs
    rcases s with _ | _ | a <;> simp_all [getAttribC, SlotOk]
  · intro s k v hs
    rcases s with _ | _ | a
    · simp [setC, getAttribC, SlotOk]
    · simp [setC, getAttribC, SlotOk]
    · cases a <;> simp_all [setC, getAttribC, SlotOk]

/-- `__setstate__` keeps the invariant too. -/
def SetstateKeepsAttrib : Prop := ∀ s st, SlotOk s → SlotOk (setstateEntryC s (.dict st)).1

/-- `e.__setstate__({'tag': 'x', 'attrib': ()})` stores a tuple, after which `e.get('k')` raises
`SystemError`. -/
theorem setstateKeepsAttrib_refuted : ¬ SetstateKeepsAttrib := by
  intro h
  have := h none ⟨true, some (.other "tuple"), none, false⟩ trivial
  simp [setstateEntryC, setstateC, SlotOk] at this

/-- And the failure that follows. -/
theorem setstate_then_get :
    getC (setstateC none ⟨true, some (.other "tuple"), none, false⟩).1 [107] none = .error badCall := rfl

/-! ## Dictionary behaviour -/

/-- The attributes as `items()` lists them. -/
def slotItems (s : Slot) : List (S × S) :=
  match s with
  | some (some a) => a.items
  | _ => []

/-- The replacement step of `dictSet`. -/
def repl (k v : S) (p : S × S) : S × S := if p.1 == k then (p.1, v) else p

theorem dictSet_eq (items : List (S × S)) (k v : S) :
    dictSet items k v = if items.any (·.1 == k) then items.map (repl k v) else items ++ [(k, v)] := by
  unfold dictSet repl; congr 1

theorem find_repl_self (k v : S) : ∀ ps : List (S × S), ps.any (·.1 == k) = true →
    (ps.map (repl k v)).find? (·.1 == k) = some (k, v)
  | [], h => by simp at h
  | p :: ps, h => by
    by_cases hak : p.1 = k
    · have : repl k v p = (k, v) := by simp [repl, hak]
      rw [List.map_cons, List.find?_cons, this]; simp
    · have hr : repl k v p = p := by simp [repl, hak]
      have hab : (p.1 == k) = false := by simpa using hak
      have hps : ps.any (·.1 == k) = true := by
        simp only [List.any_cons, hab, Bool.false_or] at h; exact h
      rw [List.map_cons, List.find?_cons, hr]
      simp only [hab]
      exact find_repl_self k v ps hps

theorem find_repl_other (k k' v : S) (hk : k' ≠ k) : ∀ ps : List (S × S),
    (ps.map (repl k v)).find? (·.1 == k') = ps.find? (·.1 == k')
  | [] => rfl
  | p :: ps => by
    have h1 : (repl k v p).1 = p.1 := by unfold repl; split <;> rfl
    by_cases hp : p.1 = k'
    · have hr : repl k v p = p := by
        unfold repl; have : (p.1 == k) = false := by simp; rw [hp]; exact hk
        simp [this]
      rw [List.map_cons, List.find?_cons, List.find?_cons, hr]
      have : (p.1 == k') = true := by simp [hp]
      simp only [this]
    · have : (p.1 == k') = false := by simpa using hp
      have this' : ((repl k v p).1 == k') = false := by rw [h1]; exact this
      rw [List.map_cons, List.find?_cons, List.find?_cons]
      simp only [this, this']
      exact find_repl_other k k' v hk ps

theorem find_dictSet (items : List (S × S)) (k v : S) :
    (dictSet items k v).find? (·.1 == k) = some (k, v) := by
  rw [dictSet_eq]
  split
  · rename_i hany; exact find_repl_self k v items hany
  · rename_i hany
    rw [List.find?_append]
    have : items.find? (·.1 == k) = none := by
      rw [List.find?_eq_none]; intro x hx
      simp only [Bool.not_eq_true, List.any_eq_false] at hany
      simpa using hany x hx
    simp [this]

theorem find_dictSet_other (items : List (S × S)) (k k' v : S) (hk : k' ≠ k) :
    (dictSet items k v).find? (·.1 == k') = items.find? (·.1 == k') := by
  rw [dictSet_eq]
  split
  · exact find_repl_other k k' v hk items
  · rw [List.find?_append]
    cases h : items.find? (·.1 == k') with
    | some x => simp
    | none => simp [Ne.symm hk]

/-- For every element whose attrib slot is NULL, a dict or a frozendict, and all keys and values:
after a successful `set(k, v)`, `get(k)` returns `v`, `get` of any other key is unchanged and
`keys()`/`items()` list the attributes with `k` set to `v` (in insertion order); `set` succeeds
unless the slot holds a frozendict, where it raises `TypeError` and changes nothing; the `attrib`
getter returns the object that is stored, and a second call returns the same object and slot;
`items()` lists what the getter returns; and the setter stores exactly the dict or frozendict it is
given. -/
def AttribDict : Prop :=
  ∀ (s : Slot) (k k' v : S) (d : Option S), SlotOk s →
    ((setC s k v).2 = .ok () →
      getC (setC s k v).1 k d = .ok (some v) ∧
      (k' ≠ k → getC (setC s k v).1 k' d = getC s k' d) ∧
      itemsC (setC s k v).1 = .ok (dictSet (slotItems s) k v)) ∧
    ((∀ i, s ≠ some (some (.frozen i))) → (setC s k v).2 = .ok ()) ∧
    (∀ i, s = some (some (.frozen i)) →
      setC s k v = (s, .error (.typeError "frozendict object does not support item assignment"))) ∧
    (getAttribC (getAttribC s).1 = getAttribC s) ∧
    itemsC (getAttribC s).1 = .ok (getAttribC s).2.items ∧
    (∀ a s', (∀ t, a ≠ .other t) → setAttribC s a = .ok s' → getAttribC s' = (s', a))

theorem attribDict_proven : AttribDict := by
  intro s k k' v d hs
  have setter : ∀ (s : Slot) (a : AObj) s', (∀ t, a ≠ .other t) → setAttribC s a = .ok s' →
      getAttribC s' = (s', a) := by
    intro s a s' ha h
    rcases a with ⟨j⟩ | ⟨j⟩ | ⟨t⟩
    · simp [setAttribC] at h; subst h; rfl
    · simp [setAttribC] at h; subst h; rfl
    · exact absurd rfl (ha t)
  rcases s with _ | _ | a
  · refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun _ => ?_, fun j h => ?_, ?_, ?_, setter _⟩
    · simp [setC, getAttribC, getC, AObj.items, find_dictSet]
    · intro hk; simp [setC, getAttribC, getC, AObj.items, find_dictSet_other _ _ _ _ hk]
    · simp [setC, getAttribC, itemsC, AObj.items, slotItems, dictSet]
    · simp [setC, getAttribC]
    · simp at h
    · simp [getAttribC]
    · simp [getAttribC, itemsC, AObj.items]
  · refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun _ => ?_, fun j h => ?_, ?_, ?_, setter _⟩
    · simp [setC, getAttribC, getC, AObj.items, find_dictSet]
    · intro hk; simp [setC, getAttribC, getC, AObj.items, find_dictSet_other _ _ _ _ hk]
    · simp [setC, getAttribC, itemsC, AObj.items, slotItems, dictSet]
    · simp [setC, getAttribC]
    · simp at h
    · simp [getAttribC]
    · simp [getAttribC, itemsC, AObj.items]
  · rcases a with ⟨i⟩ | ⟨i⟩ | ⟨t⟩
    · refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun _ => ?_, fun j h => ?_, ?_, ?_, setter _⟩
      · simp [setC, getAttribC, getC, AObj.items, find_dictSet]
      · intro hk; simp [setC, getAttribC, getC, AObj.items, find_dictSet_other _ _ _ _ hk]
      · simp [setC, getAttribC, itemsC, AObj.items, slotItems]
      · simp [setC, getAttribC]
      · simp at h
      · simp [getAttribC]
      · simp [getAttribC, itemsC]
    · refine ⟨fun h => ?_, fun h => ?_, fun j hj => ?_, ?_, ?_, setter _⟩
      · simp [setC, getAttribC] at h
      · exact absurd rfl (h i)
      · simp at hj; subst hj; simp [setC, getAttribC]
      · simp [getAttribC]
      · simp [getAttribC, itemsC]
    · simp [SlotOk] at hs

/-- `__setstate__` of anything but an exact dict raises `TypeError` and changes nothing; on a dict
whose keys are only `tag` (and `attrib`), it stores the given attrib. -/
def SetstateEntry : Prop :=
  (∀ s, setstateEntryC s .other = (s, .error (.typeError "~Don't know how to unpickle as an Element"))) ∧
  (∀ s a, setstateEntryC s (.dict ⟨true, some a, none, false⟩) = (some (some a), .ok ()))

theorem setstateEntry_proven : SetstateEntry :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

end PyLean.TextLibs.Etree
