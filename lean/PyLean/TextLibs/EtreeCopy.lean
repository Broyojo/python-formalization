import PyLean.TextLibs.EtreeAttrib

/-!
`copy.copy(element)`: the C accelerator's `Element.__copy__` (Modules/_elementtree.c:763-797,
with `create_new_element`, :329-352) against the pure-Python twin's `__copy__`
(Lib/xml/etree/ElementTree.py:189-194, through `makeelement`, :178-187, and `__init__`, :167-173).

Attribute dicts live in a heap and an element holds a reference, so sharing is visible. The C
element's slot may be NULL (`none`); the twin always holds a dict. Tags, keys and values are str;
text, tail and children are copied by reference in both twins and are left out.
-/

namespace PyLean.TextLibs.Etree

open PyLean

/-- An element: its class (`sub` for a subclass of Element) and its attrib reference. -/
structure CElem where
  tag : S
  sub : Bool
  attrib : Option Nat
  deriving Repr, DecidableEq

abbrev Heap := List (List (S × S))

def Heap.get (h : Heap) (r : Nat) : List (S × S) := h.getD r []

def Heap.alloc (h : Heap) (d : List (S × S)) : Heap × Nat := (h ++ [d], h.length)

def Heap.put (h : Heap) (r : Nat) (d : List (S × S)) : Heap := h.set r d

/-- `Element.__copy__` in C: `create_new_element(st, self->tag, attrib)` makes an exact Element
and, for a non-empty attrib, `create_extra(self, attrib)` stores that same dict. -/
def copyC (h : Heap) (e : CElem) : Heap × CElem :=
  let attrib := match e.attrib with
    | some r => if h.get r = [] then none else some r
    | none => none
  (h, { tag := e.tag, sub := false, attrib := attrib })

/-- `Element.set(key, value)` in C, :1754-1773: `element_get_attrib` creates a dict for a NULL
slot. -/
def setCE (h : Heap) (e : CElem) (k v : S) : Heap × CElem :=
  match e.attrib with
  | some r => (h.put r (dictSet (h.get r) k v), e)
  | none => let (h, r) := h.alloc [(k, v)]; (h, { e with attrib := some r })

/-- The attributes an element shows. -/
def attrsOf (h : Heap) (e : CElem) : List (S × S) := match e.attrib with | some r => h.get r | none => []

/-- The twin's `__copy__`: `self.makeelement(self.tag, self.attrib)` is
`self.__class__(tag, attrib)`, whose `__init__` builds `{**attrib, **extra}`, a new dict. -/
def copyPy (h : Heap) (e : CElem) : Heap × CElem :=
  let (h, r) := h.alloc (attrsOf h e)
  (h, { tag := e.tag, sub := e.sub, attrib := some r })

/-- The twin's `set`: `self.attrib[key] = value`. -/
def setPyE (h : Heap) (e : CElem) (k v : S) : Heap × CElem := setCE h e k v

/-- Setting an attribute on a shallow copy leaves the original's attributes as they were. -/
def CopyIndependentC : Prop :=
  ∀ (h : Heap) (e : CElem) (k v : S),
    let (h1, c) := copyC h e
    let (h2, _) := setCE h1 c k v
    attrsOf h2 e = attrsOf h e

/-- `c = copy.copy(Element('r', {'k': 'v'})); c.set('z', '1')` gives the original `z` too. -/
theorem copyIndependentC_refuted : ¬ CopyIndependentC := by
  intro hc
  have := hc [[(lit "k", lit "v")]] ⟨lit "r", false, some 0⟩ (lit "z") (lit "1")
  revert this
  decide

/-- The same for the twin, on a heap whose references are allocated. -/
def CopyIndependentPy : Prop :=
  ∀ (h : Heap) (e : CElem) (k v : S), (∀ r, e.attrib = some r → r < h.length) →
    let (h1, c) := copyPy h e
    let (h2, _) := setPyE h1 c k v
    attrsOf h2 e = attrsOf h e

theorem copyIndependentPy_proven : CopyIndependentPy := by
  intro h e k v hr
  simp only [copyPy, Heap.alloc, setPyE, setCE, attrsOf]
  cases ha : e.attrib with
  | none => rfl
  | some r =>
    have hlt := hr r ha
    simp only [Heap.put, Heap.get]
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), List.getElem?_append_left hlt,
      ← List.getD_eq_getElem?_getD]

/-- A copy has the original's class. -/
def CopyKeepsClassC : Prop := ∀ (h : Heap) (e : CElem), (copyC h e).2.sub = e.sub

/-- `copy.copy(Sub('r'))` is an exact `Element`. -/
theorem copyKeepsClassC_refuted : ¬ CopyKeepsClassC := by
  intro hc
  have := hc [] ⟨lit "r", true, none⟩
  revert this
  decide

def CopyKeepsClassPy : Prop := ∀ (h : Heap) (e : CElem), (copyPy h e).2.sub = e.sub

theorem copyKeepsClassPy_proven : CopyKeepsClassPy := fun _ _ => rfl

end PyLean.TextLibs.Etree
