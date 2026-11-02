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
def SetstateKeepsAttrib : Prop := ∀ s st, SlotOk s → SlotOk (setstateC s st).1

/-- `e.__setstate__({'tag': 'x', 'attrib': ()})` stores a tuple, after which `e.get('k')` raises
`SystemError`. -/
theorem setstateKeepsAttrib_refuted : ¬ SetstateKeepsAttrib := by
  intro h
  have := h none ⟨true, some (.other "tuple"), none, false⟩ trivial
  simp [setstateC, SlotOk] at this

/-- And the failure that follows. -/
theorem setstate_then_get :
    getC (setstateC none ⟨true, some (.other "tuple"), none, false⟩).1 [107] none = .error badCall := rfl

end PyLean.TextLibs.Etree
