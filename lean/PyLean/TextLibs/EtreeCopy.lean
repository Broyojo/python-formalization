import PyLean.TextLibs.EtreeAttrib

/-!
`copy.copy(element)`: the C accelerator's `Element.__copy__` (Modules/_elementtree.c:763-797,
with `create_new_element`, :329-352) against the pure-Python twin's `__copy__`
(Lib/xml/etree/ElementTree.py:189-194, through `makeelement`, :178-187, and `__init__`, :167-173).

Attribute dicts live in a heap and an element holds a reference, so sharing is visible. The C
element's slot may be NULL (`none`); the twin always holds a dict. Tags, keys and values are str;
text and tail are values; children are element references, copied by reference in both twins.

Scope: allocation failure (`element_resize`) is not modelled; attribs are dicts (an empty
frozendict, which `create_new_element`'s exact-dict emptiness test treats as non-empty, is out of
scope); the twin's `__init__` is the base class's, and `elem[:] = self` copies children that are
Elements (the element invariant), so its type check passes.
-/

namespace PyLean.TextLibs.Etree

open PyLean

/-- An element: its class (`sub` for a subclass of Element), its attrib reference, text, tail
and children (references). -/
structure CElem where
  tag : S
  sub : Bool
  attrib : Option Nat
  text : Option S := none
  tail : Option S := none
  kids : List Nat := []
  deriving Repr, DecidableEq

abbrev Heap := List (List (S × S))

def Heap.get (h : Heap) (r : Nat) : List (S × S) := h.getD r []

def Heap.alloc (h : Heap) (d : List (S × S)) : Heap × Nat := (h ++ [d], h.length)

def Heap.put (h : Heap) (r : Nat) (d : List (S × S)) : Heap := h.set r d

/-- `Element.__copy__` in C, :763-797: `create_new_element(st, self->tag, attrib)` makes an exact
Element and, for a non-empty attrib, `create_extra(self, attrib)` stores that same dict; then text
and tail are copied with their join flag, and the children by reference, in order. -/
def copyC (h : Heap) (e : CElem) : Heap × CElem :=
  let attrib := match e.attrib with
    | some r => if h.get r = [] then none else some r
    | none => none
  (h, { tag := e.tag, sub := false, attrib := attrib, text := e.text, tail := e.tail, kids := e.kids })

/-- `Element.set(key, value)` in C, :1754-1773: `element_get_attrib` creates a dict for a NULL
slot. -/
def setCE (h : Heap) (e : CElem) (k v : S) : Heap × CElem :=
  match e.attrib with
  | some r => (h.put r (dictSet (h.get r) k v), e)
  | none => let (h, r) := h.alloc [(k, v)]; (h, { e with attrib := some r })

/-- The attributes an element shows. -/
def attrsOf (h : Heap) (e : CElem) : List (S × S) := match e.attrib with | some r => h.get r | none => []

/-- The twin's `makeelement(tag, attrib)`, ElementTree.py:178-187: `self.__class__(tag, attrib)`,
whose `__init__` builds `{**attrib, **extra}`, a new dict. -/
def makeelementPy (h : Heap) (e : CElem) (tag : S) (attrib : List (S × S)) : Heap × CElem :=
  let (h, r) := h.alloc attrib
  (h, { tag := tag, sub := e.sub, attrib := some r })

/-- The twin's `__copy__`, ElementTree.py:189-194: `makeelement(self.tag, self.attrib)`, then text,
tail, and `elem[:] = self`. -/
def copyPy (h : Heap) (e : CElem) : Heap × CElem :=
  let (h, c) := makeelementPy h e e.tag (attrsOf h e)
  (h, { c with text := e.text, tail := e.tail, kids := e.kids })

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
  have := hc [[(lit "k", lit "v")]] { tag := lit "r", sub := false, attrib := some 0 } (lit "z") (lit "1")
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
  simp only [copyPy, makeelementPy, Heap.alloc, setPyE, setCE, attrsOf]
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
  have := hc [] { tag := lit "r", sub := true, attrib := none }
  revert this
  decide

def CopyKeepsClassPy : Prop := ∀ (h : Heap) (e : CElem), (copyPy h e).2.sub = e.sub

theorem copyKeepsClassPy_proven : CopyKeepsClassPy := fun _ _ => rfl

/-- A shallow copy, in either twin, has the original's tag, text, tail and children (the same
elements, in order) and shows the original's attributes; the twin's copy also keeps the class. -/
def CopyShallow : Prop :=
  ∀ (h : Heap) (e : CElem),
    ((copyC h e).2.tag = e.tag ∧ (copyC h e).2.text = e.text ∧ (copyC h e).2.tail = e.tail ∧
      (copyC h e).2.kids = e.kids ∧ attrsOf (copyC h e).1 (copyC h e).2 = attrsOf h e) ∧
    ((copyPy h e).2.tag = e.tag ∧ (copyPy h e).2.text = e.text ∧ (copyPy h e).2.tail = e.tail ∧
      (copyPy h e).2.kids = e.kids ∧ (copyPy h e).2.sub = e.sub ∧
      attrsOf (copyPy h e).1 (copyPy h e).2 = attrsOf h e)

theorem copyShallow_proven : CopyShallow := by
  intro h e
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩⟩
  · simp only [copyC, attrsOf]
    cases ha : e.attrib with
    | none => rfl
    | some r =>
      by_cases he : h.get r = []
      · simp [he]
      · simp [he]
  · simp [copyPy, makeelementPy, Heap.alloc, attrsOf, Heap.get]

end PyLean.TextLibs.Etree
