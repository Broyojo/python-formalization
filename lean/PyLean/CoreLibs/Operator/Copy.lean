import PyLean.Core

/-!
`Lib/copy.py` (CPython 3.15.2), on a heap of objects, so that identity is a cell number and `memo` a real table.
`__copy__`, `__deepcopy__`, `__reduce_ex__`, the constructor in a reduce value, `__setstate__`, `append` and
`__setitem__` can all fail, and `_reconstruct` is one function with the `deep` flag of the source.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

/-- What a reduce value builds with `func(*args)`. -/
inductive BuildKind where
  | inst | list | dict
  deriving Repr, DecidableEq

/-- An iterator of a reduce value: it yields `items`, and then its next `next()` raises `fail` if that is set, or
ends. Scope: the items of a `dictiter` are pairs, as the pickle protocol asks; an item that does not unpack into two is
not modelled. -/
structure ItemsIter (α : Type) where
  items : List α
  fail : Option PyExc
  deriving Repr, DecidableEq

/-- What `reductor(4)` gives. -/
inductive RvSpec where
  /-- A string: a global, so `x` itself. -/
  | str
  /-- The reductor raises. -/
  | raises (e : PyExc)
  /-- A tuple. `size` is its length; `func` is the constructor, raising `fail` if that is set; `setstate` is `y`'s
  `__setstate__`, raising if the inner value is set. `state` `none` is a `None` in the tuple or no item there. -/
  | tuple (size : Nat) (fail : Option PyExc) (kind : BuildKind) (args : List Nat) (state : Option Nat)
      (listiter : Option (ItemsIter Nat)) (dictiter : Option (ItemsIter (Nat × Nat)))
      (setstate : Option (Option PyExc))
  deriving Repr, DecidableEq

/-- A key of an instance's `__dict__`. Every `str` key is a `name` (setattr's names and a `str` object that
`__dict__.update` stores alike); any other key object is `obj`, its cell, and compares with `pyEq`, so two keys merge
exactly when the dict would merge them. -/
inductive AttrKey where
  | name (s : String)
  | obj (k : Nat)
  deriving Repr, DecidableEq

/-- An object on the heap. `hooked` is an instance of a class with its own protocol: `copier` is `__copy__`,
`deepcopier` is `__deepcopy__`, each raising if the inner value is set, and returning a fresh atom otherwise;
`reduce` is what `__reduce_ex__` gives, `none` for an object that has neither it nor `__reduce__`. `inst` is a plain
instance, which `object.__reduce_ex__` copies through `copyreg.__newobj__`. The atom `0` is `None`; other atoms are
`int`s. An `inst`'s attributes are its `__dict__` in insertion order. A `method`'s function has the `__name__`
`methName func`; the class of the model's instances defines function `0` and nothing else defines any. -/
inductive Cell where
  | atom (n : Int)
  /-- A `str`, atomic for both copies, Lib/copy.py:103 and :165. -/
  | str (s : String)
  | list (items : List Nat)
  | tuple (items : List Nat)
  | dict (items : List (Nat × Nat))
  /-- A `frozendict`: `copy` returns it, Lib/copy.py:103-104, and `deepcopy` builds a new one, :205-218. -/
  | fdict (items : List (Nat × Nat))
  | inst (attrs : List (AttrKey × Nat))
  | method (func self : Nat)
  /-- A class whose type is `type`, which `deepcopy` returns at Lib/copy.py:118, before reading `memo`. -/
  | cls (id : Nat)
  /-- A class with another metaclass: `issubclass(cls, type)`, reached at Lib/copy.py:132 after the `memo` lookup. -/
  | metaCls (id : Nat)
  | hooked (copier deepcopier : Option (Option PyExc)) (reduce : Option RvSpec)
  deriving Repr, DecidableEq, Inhabited

/-- The state of a run. `memo` maps an id to its copy. -/
structure Heap where
  cells : List Cell
  memo : List (Nat × Nat)
  deriving Repr, DecidableEq

def Heap.get (h : Heap) (i : Nat) : Cell := h.cells.getD i (.atom 0)

def Heap.alloc (h : Heap) (c : Cell) : Heap × Nat :=
  ({ h with cells := h.cells ++ [c] }, h.cells.length)

def Heap.set (h : Heap) (i : Nat) (c : Cell) : Heap :=
  { h with cells := h.cells.set i c }

def Heap.remember (h : Heap) (x y : Nat) : Heap := { h with memo := (x, y) :: h.memo }

/-- Attribute names of `args` and of dict keys, as the model stores them in an instance. -/
def attrName (k : Nat) : String := "k" ++ toString k

/-- `_reconstruct`'s first lines with `size` checked: the call `_reconstruct(x, memo, *rv)` takes `func` and `args`
and three more, Lib/copy.py:242-244. -/
def reconArity (size : Nat) : Option PyExc :=
  if size < 2 then some (.typeError "~_reconstruct() missing required positional arguments")
  else if size > 5 then some (.typeError "~_reconstruct() takes too many positional arguments")
  else none

/-- `y.append(item)`, Lib/copy.py:272 and :275. -/
def appendTo (h : Heap) (y item : Nat) : Py Heap :=
  match h.get y with
  | .list l => .ok (h.set y (.list (l ++ [item])))
  | _ => .error (.named "AttributeError" "~object has no attribute 'append'")

/-- What makes `hash(k)` fail: the type that has no hash. A tuple hashes its items in order, and a `frozendict` the
values of its items in order, Objects/dictobject.c:8425-8432 (its keys were hashed when it was built). -/
def keyHashErr : Nat → Heap → Nat → Option String
  | 0, _, _ => none
  | f + 1, h, k =>
    match h.get k with
    | .list _ => some "list"
    | .dict _ => some "dict"
    | .tuple items => items.findSome? (keyHashErr f h)
    | .fdict items => items.findSome? (fun p => keyHashErr f h p.2)
    | _ => none

def cellName : Cell → String
  | .list _ => "list"
  | .dict _ => "dict"
  | .tuple _ => "tuple"
  | .fdict _ => "frozendict"
  | _ => "object"

/-- The `TypeError` of storing `k` as a dict key, which a key's copy can meet when `memo` holds something mutable for it. -/
def storeKey (h : Heap) (k : Nat) : Option PyExc :=
  (keyHashErr 8 h k).map fun u => .typeError s!"cannot use '{cellName (h.get k)}' as a dict key (unhashable type: '{u}')"

/-- `tuple_richcompare` for `==`, Objects/tupleobject.c:764-781: the items in order until one differs, then the
lengths. The list version, Objects/listobject.c:3470-3499, checks the lengths first; with no error in between the two
agree, and the list one is `seqEq` behind a length test. `eq` is `PyObject_RichCompareBool`. -/
def seqEq (eq : Nat → Nat → Py Bool) : List Nat → List Nat → Py Bool
  | [], [] => .ok true
  | a :: as, b :: bs =>
    match eq a b with
    | .error e => .error e
    | .ok false => .ok false
    | .ok true => seqEq eq as bs
  | _, _ => .ok false

/-- A lookup in a dict's items: the first stored key that compares equal to `k`, the stored key on the left as in
`compare_generic`, Objects/dictobject.c:1187-1199. -/
def mapFind (eq : Nat → Nat → Py Bool) (k : Nat) : List (Nat × Nat) → Py (Option Nat)
  | [] => .ok none
  | (k0, v0) :: rest =>
    match eq k0 k with
    | .error e => .error e
    | .ok true => .ok (some v0)
    | .ok false => mapFind eq k rest

/-- `dict_equal_lock_held`, Objects/dictobject.c:4622-4681: the sizes, then every item of `a` looked up in `b` and the two
values compared, stopping at the first difference. -/
def mapEq (eq : Nat → Nat → Py Bool) (a b : List (Nat × Nat)) : Py Bool :=
  if a.length ≠ b.length then .ok false else
  let rec go : List (Nat × Nat) → Py Bool
    | [] => .ok true
    | (k, av) :: rest =>
      match mapFind eq k b with
      | .error e => .error e
      | .ok none => .ok false
      | .ok (some bv) =>
        match eq av bv with
        | .error e => .error e
        | .ok false => .ok false
        | .ok true => go rest
  go a

/-- `PyObject_RichCompareBool(a, b, Py_EQ)`, Objects/object.c:1122-1148, on the model's objects: the same object is
equal to itself before anything is called, :1129-1131. An atom is an `int` and compares by value; a tuple and a list
item by item (`seqEq`); a `str` by its text; a `dict` and a `frozendict` by their items, either with either (`dict_richcompare`,
Objects/dictobject.c:4695-4712, takes any dict); a bound method by its function and then the identity of its `__self__`,
Objects/classobject.c:239-242; a class cell by its `id`. Everything else (`inst`, `hooked`, `metaCls`) has the default
`__eq__`, identity only. Scope limit: no object in this universe has its own `__eq__`, so an `__eq__` that raises, or
that disagrees with `__hash__`, is out of scope; so is the `RecursionError` of comparing two distinct cyclic
structures, which the model reports as `modelFuel`. -/
def pyEq : Nat → Heap → Nat → Nat → Py Bool
  | 0, _, _, _ => .error .modelFuel
  | f + 1, h, a, b =>
    if a = b then .ok true else
    match h.get a, h.get b with
    | .atom m, .atom n => .ok (m == n)
    | .str s, .str t => .ok (s == t)
    | .tuple xs, .tuple ys => seqEq (pyEq f h) xs ys
    | .list xs, .list ys => if xs.length ≠ ys.length then .ok false else seqEq (pyEq f h) xs ys
    | .dict d, .dict e => mapEq (pyEq f h) d e
    | .dict d, .fdict e => mapEq (pyEq f h) d e
    | .fdict d, .dict e => mapEq (pyEq f h) d e
    | .fdict d, .fdict e => mapEq (pyEq f h) d e
    | .method fa sa, .method fb sb => .ok (fa == fb && sa == sb)
    | .cls m, .cls n => .ok (m == n)
    | _, _ => .ok false

/-- Enough depth for any comparison on an acyclic graph of `h`. -/
def eqFuel (h : Heap) : Nat := 2 * h.cells.length + 2

/-- `insertdict`, Objects/dictobject.c:2001-2049, on a dict's items in insertion order: a stored key equal to `k`
keeps its place and its own key object and takes the new value (`replace_value`, :2041); otherwise the pair goes at the
end (`insert_combined_dict`, :2033). CPython compares only keys of equal hash; in this universe equal objects have
equal hashes and no comparison raises, so comparing every key in order gives the same dict. -/
def storeItem {α : Type} (eq : α → α → Py Bool) : List (α × Nat) → α → Nat → Py (List (α × Nat))
  | [], k, v => .ok [(k, v)]
  | (k0, v0) :: rest, k, v =>
    match eq k0 k with
    | .error e => .error e
    | .ok true => .ok ((k0, v) :: rest)
    | .ok false =>
      match storeItem eq rest k v with
      | .error e => .error e
      | .ok r => .ok ((k0, v0) :: r)

/-- `d[k] = v` on a `dict` with items `d`: the hash first, whose failure is `storeKey`'s `TypeError`, then the store. -/
def dictSet (h : Heap) (d : List (Nat × Nat)) (k v : Nat) : Py (List (Nat × Nat)) :=
  match storeKey h k with
  | some e => .error e
  | none => storeItem (pyEq (eqFuel h) h) d k v

/-- `l[n] = v` once the index is a `Py_ssize_t`: a negative index counts from the end, and one outside the list is
`none`, the `IndexError`. -/
def listSet (l : List Nat) (n : Int) (v : Nat) : Option (List Nat) :=
  let i : Int := if n < 0 then n + l.length else n
  if 0 ≤ i ∧ i < l.length then some (l.set i.toNat v) else none

/-- `y[key] = value`, Lib/copy.py:281 and :284. A dict hashes the key and stores (`dictSet`). A list takes an `int`
index, `list_ass_subscript_lock_held`, Objects/listobject.c:3758-3765 (counted from the end when negative) and
`list_ass_item_lock_held`, :1158-1164; any other key is the `TypeError` of :3910-3913 (here `None`, the atom `0`, and
every non-atom; there are no slices). Anything else has no `__setitem__`. -/
def setItemOf (h : Heap) (y k v : Nat) : Py Heap :=
  match h.get y with
  | .dict l =>
    match dictSet h l k v with
    | .error e => .error e
    | .ok l' => .ok (h.set y (.dict l'))
  | .list l =>
    match h.get k with
    | .atom n =>
      if n = 0 then .error (.typeError "list indices must be integers or slices, not NoneType")
      else if n > 9223372036854775807 ∨ n < -9223372036854775808 then
        .error (.indexError "~cannot fit 'int' into an index-sized integer")
      else
        match listSet l n v with
        | some l' => .ok (h.set y (.list l'))
        | none => .error (.indexError "list assignment index out of range")
    | _ => .error (.typeError "~list indices must be integers or slices")
  | _ => .error (.typeError "~object does not support item assignment")

/-- Key equality in an instance's `__dict__`: names by their text, other keys by `pyEq`, a name and another key
never (no other object here equals a `str`). -/
def akEq (h : Heap) : AttrKey → AttrKey → Py Bool
  | .name s, .name t => .ok (s == t)
  | .obj a, .obj b => pyEq (eqFuel h) h a b
  | _, _ => .ok false

/-- Store `v` under `k` in an instance's `__dict__`: `setattr`'s store, `__setstate__`'s, and one item of
`__dict__.update`. It is a dict store, `insertdict` as in `storeItem`: a key already there keeps its place and takes
the value. Anything but an instance has no `__dict__`. -/
def setAttrOf (h : Heap) (y : Nat) (k : AttrKey) (v : Nat) : Py Heap :=
  match h.get y with
  | .inst a =>
    match storeItem (akEq h) a k v with
    | .error e => .error e
    | .ok a' => .ok (h.set y (.inst a'))
  | _ => .error (.named "AttributeError" "~object has no attribute '__dict__'")

/-- The key an object makes in an instance's `__dict__`: a `str` is a name, anything else itself. -/
def attrKey (h : Heap) (k : Nat) : AttrKey :=
  match h.get k with
  | .str s => .name s
  | _ => .obj k

def noneCell (h : Heap) (s : Nat) : Bool :=
  match h.get s with
  | .atom 0 => true
  | _ => false

/-- The items of a `dict` or `frozendict` merged into `y.__dict__`, Objects/dictobject.c:3994-3995 (its keys are
hashable already). -/
def updateFrom (y : Nat) : Heap → List (Nat × Nat) → Py Heap
  | h, [] => .ok h
  | h, (k, v) :: rest =>
    match setAttrOf h y (attrKey h k) v with
    | .error e => .error e
    | .ok h => updateFrom y h rest

/-- One element of a sequence of pairs as `PySequence_Fast` sees it, Objects/dictobject.c:4081-4104: a tuple or a list
is itself, a `dict` or `frozendict` the list of its keys, a `str` its characters (new one-character strings); anything
else is not iterable. Two items make the pair; any other length is the `ValueError`. -/
def pairOf (h : Heap) (i e : Nat) : Py (Heap × Nat × Nat) :=
  let len (n : Nat) : PyExc :=
    .valueError s!"dictionary update sequence element #{i} has length {n}; 2 is required"
  match h.get e with
  | .tuple [k, v] | .list [k, v] => .ok (h, k, v)
  | .tuple l | .list l => .error (len l.length)
  | .dict d | .fdict d =>
    match d with
    | [(k, _), (v, _)] => .ok (h, k, v)
    | _ => .error (len d.length)
  | .str s =>
    match s.toList with
    | [a, b] =>
      let h1 := (h.alloc (.str (String.singleton a))).1
      .ok ((h1.alloc (.str (String.singleton b))).1, h.cells.length, h1.cells.length)
    | l => .error (len l.length)
  | _ => .error (.typeError "object is not iterable")

/-- `merge_from_seq2_lock_held`, Objects/dictobject.c:4052-4112, into `y.__dict__`: element by element, the pair, then
the store, whose key must hash (`storeKey`). -/
def updateSeq (y : Nat) : Nat → Heap → List Nat → Py Heap
  | _, h, [] => .ok h
  | i, h, e :: rest =>
    match pairOf h i e with
    | .error x => .error x
    | .ok (h1, k, v) =>
      match storeKey h1 k with
      | some x => .error x
      | none =>
        match setAttrOf h1 y (attrKey h1 k) v with
        | .error x => .error x
        | .ok h2 => updateSeq y (i + 1) h2 rest

/-- `y.__dict__.update(s)` on an instance `y`: `dict_update_arg`, Objects/dictobject.c:3992-4005. A `dict` or a
`frozendict` merges (no other object here has `keys`); anything else is a sequence of pairs, and a non-iterable is the
`TypeError` of `PyObject_GetIter`, :4064-4066. A `str` iterates its characters, each one long. -/
def dictUpdate (h : Heap) (y s : Nat) : Py Heap :=
  match h.get s with
  | .dict items | .fdict items => updateFrom y h items
  | .list xs | .tuple xs => updateSeq y 0 h xs
  | .str t =>
    if t.isEmpty then .ok h
    else .error (.valueError "dictionary update sequence element #0 has length 1; 2 is required")
  | _ => .error (.typeError "~object is not iterable")

/-- `for key, value in slotstate.items(): setattr(y, key, value)`, Lib/copy.py:265-266. `PyObject_SetAttr` wants a
`str` name before it looks at `y`; an object without `__dict__` cannot take a new attribute. -/
def slotSet (y : Nat) : Heap → List (Nat × Nat) → Py Heap
  | h, [] => .ok h
  | h, (k, v) :: rest =>
    match h.get k with
    | .str s =>
      match h.get y with
      | .inst _ =>
        match setAttrOf h y (.name s) v with
        | .error e => .error e
        | .ok h => slotSet y h rest
      | _ => .error (.named "AttributeError" "~object has no attribute and no __dict__ for setting new attributes")
    | _ => .error (.typeError "~attribute name must be string")

/-- `isinstance(state, tuple) and len(state) == 2`, Lib/copy.py:258-261: `(state, slotstate)`, or the state alone. -/
def stateSplit (h : Heap) (st : Nat) : Nat × Option Nat :=
  match h.get st with
  | .tuple [a, b] => (a, some b)
  | _ => (st, none)

/-- The state step without `__setstate__`, Lib/copy.py:258-266, on a state that is not `None` and already copied: a
two-item tuple is `(state, slotstate)`. A state that is not `None` reads `y.__dict__` first, so an object without one
is an `AttributeError` whatever the state, then `update` takes it; a slot state that is not `None` needs `items`. -/
def stateStep (h : Heap) (y st : Nat) : Py Heap :=
  let s := (stateSplit h st).1
  let slot := (stateSplit h st).2
  let h1 : Py Heap :=
    if noneCell h s then .ok h else
    match h.get y with
    | .inst _ => dictUpdate h y s
    | _ => .error (.named "AttributeError" "~object has no attribute '__dict__'")
  match h1 with
  | .error e => .error e
  | .ok h2 =>
    match slot with
    | none => .ok h2
    | some b =>
      if noneCell h2 b then .ok h2 else
      match h2.get b with
      | .dict items | .fdict items => slotSet y h2 items
      | _ => .error (.named "AttributeError" "~object has no attribute 'items'")

/-- `y.__setstate__(state)`. The model stores it, so that it can be observed. -/
def setstateOf (h : Heap) (y st : Nat) (fail : Option PyExc) : Py Heap :=
  match fail with
  | some e => .error e
  | none => setAttrOf h y (.name "__state__") st

/-- Lib/copy.py:255-266 on a state that is not `None`: `__setstate__` if `y` has one, else the default step. -/
def stateApply (h : Heap) (y st : Nat) (setstate : Option (Option PyExc)) : Py Heap :=
  match setstate with
  | some f => setstateOf h y st f
  | none => stateStep h y st

def freshOf (kind : BuildKind) (args : List Nat) : Cell :=
  match kind with
  | .inst => .inst (args.zipIdx.map (fun p => (.name (attrName p.2), p.1)))
  | .list => .list []
  | .dict => .dict []

/-- `for item in listiter: y.append(item)`, Lib/copy.py:274-275, over the items the iterator yields. -/
def appendAll (h : Heap) (y : Nat) : List Nat → Py Heap
  | [] => .ok h
  | i :: rest =>
    match appendTo h y i with
    | .error e => .error e
    | .ok h1 => appendAll h1 y rest

/-- `for key, value in dictiter: y[key] = value`, Lib/copy.py:283-284, over the pairs the iterator yields. -/
def setAll (h : Heap) (y : Nat) : List (Nat × Nat) → Py Heap
  | [] => .ok h
  | (k, v) :: rest =>
    match setItemOf h y k v with
    | .error e => .error e
    | .ok h1 => setAll h1 y rest

/-- The steps of `_reconstruct` after `y` exists, when `deep` is false: nothing is copied. Lib/copy.py:252-285. The
state is used only if it is not `None` (:252); each iterator's items go in, in order, and then the iterator's own
failure, if it has one, comes out. -/
def reconRest (h : Heap) (y : Nat) (state : Option Nat) (listiter : Option (ItemsIter Nat))
    (dictiter : Option (ItemsIter (Nat × Nat))) (setstate : Option (Option PyExc)) : Py Heap :=
  let h1 : Py Heap :=
    match state with
    | none => .ok h
    | some st => if noneCell h st then .ok h else stateApply h y st setstate
  match h1 with
  | .error e => .error e
  | .ok h2 =>
    let h3 : Py Heap :=
      match listiter with
      | none => .ok h2
      | some it =>
        match appendAll h2 y it.items with
        | .error e => .error e
        | .ok h => match it.fail with
          | some e => .error e
          | none => .ok h
    match h3 with
    | .error e => .error e
    | .ok h4 =>
      match dictiter with
      | none => .ok h4
      | some it =>
        match setAll h4 y it.items with
        | .error e => .error e
        | .ok h => match it.fail with
          | some e => .error e
          | none => .ok h

/-- `_reconstruct(x, None, *rv)`, Lib/copy.py:242-285, with `deep` false, on a tuple of that shape. -/
def reconShallow (h : Heap) (r : RvSpec) (x : Nat) : Py (Heap × Nat) :=
  match r with
  | .str => .ok (h, x)
  | .raises e => .error e
  | .tuple size fail kind args state listiter dictiter setstate =>
    match reconArity size with
    | some e => .error e
    | none =>
      match fail with
      | some e => .error e
      | none =>
        let (h1, y) := h.alloc (freshOf kind args)
        match reconRest h1 y state listiter dictiter setstate with
        | .error e => .error e
        | .ok h2 => .ok (h2, y)

/-- `copy.Error` of `copy`, Lib/copy.py:96, and of `deepcopy`, :151. -/
def uncopyable (deep : Bool) : PyExc :=
  .named "Error" (if deep then "~un(deep)copyable object of type" else "~un(shallow)copyable object of type")

/-- The `__name__` of a method's function. -/
def methName (f : Nat) : String := "f" ++ toString f

/-- `getattr(self, name)` for the `__name__` of a method's function: an instance's own `__dict__` entry of that name
wins over the class's function, a non-data descriptor, which is bound anew; any other object, and an instance whose class
does not define the name, has no such attribute. -/
def getMethodAttr (h : Heap) (f s : Nat) : Py (Heap × Nat) :=
  match h.get s with
  | .inst a =>
    match a.lookup (.name (methName f)) with
    | some v => .ok (h, v)
    | none =>
      if f = 0 then .ok (h.alloc (.method f s))
      else .error (.named "AttributeError" "~object has no attribute")
  | _ => .error (.named "AttributeError" "~object has no attribute")

/-- `copy(x)`, Lib/copy.py:62-100. `tuple` is atomic here and only here. A bound method has no `__copy__`, so it goes
through `method.__reduce__`, Objects/classobject.c:90-116, which gives `(getattr, (self, name))` (no name here is
private, so no mangling, :99-111), and `_reconstruct` makes `getattr(self, name)`. -/
def copyShallow (h : Heap) (x : Nat) : Py (Heap × Nat) :=
  match h.get x with
  | .atom _ | .str _ | .tuple _ | .fdict _ | .cls _ | .metaCls _ => .ok (h, x)
  | .list l => let (h1, y) := h.alloc (.list l); .ok (h1, y)
  | .dict l => let (h1, y) := h.alloc (.dict l); .ok (h1, y)
  | .inst a => let (h1, y) := h.alloc (.inst a); .ok (h1, y)
  | .method f s => getMethodAttr h f s
  | .hooked copier _ reduce =>
    match copier with
    | some (some e) => .error e
    | some none => let (h1, y) := h.alloc (.atom 1); .ok (h1, y)
    | none =>
      match reduce with
      | none => .error (uncopyable false)
      | some r => reconShallow h r x

mutual
  /-- `deepcopy(x, memo)`, Lib/copy.py:110-162, with the dispatch table of `_deepcopy_list`, :171-177,
  `_deepcopy_tuple`, :180-194, `_deepcopy_dict`, :197-202, and `_deepcopy_method`, :220-221. -/
  def deepcopy : Nat → Heap → Nat → Py (Heap × Nat)
    | 0, _, _ => .error .modelFuel
    | fuel + 1, h, x =>
      match h.get x with
      | .atom _ | .str _ | .cls _ => .ok (h, x)
      | c =>
        match h.memo.lookup x with
        | some y => .ok (h, y)
        | none =>
          match c with
          | .list items =>
            let (h1, y) := h.alloc (.list [])
            let h2 := h1.remember x y
            match deepList fuel h2 items with
            | .error e => .error e
            | .ok (h3, ys) => .ok (h3.set y (.list ys), y)
          | .tuple items =>
            match deepList fuel h items with
            | .error e => .error e
            | .ok (h1, ys) =>
              match h1.memo.lookup x with
              | some y => .ok (h1, y)
              | none =>
                if ys == items then .ok (h1, x)
                else
                  let (h2, y) := h1.alloc (.tuple ys)
                  .ok (h2.remember x y, y)
          | .dict items =>
            let (h1, y) := h.alloc (.dict [])
            let h2 := h1.remember x y
            match deepPairs fuel h2 [] items with
            | .error e => .error e
            | .ok (h3, ys) => .ok (h3.set y (.dict ys), y)
          | .fdict items =>
            -- `_deepcopy_frozendict`, Lib/copy.py:205-218: nothing is in `memo` during the copies, and a recursive
            -- structure may have put a copy there, which wins; the result is always a new object
            match deepPairs fuel h [] items with
            | .error e => .error e
            | .ok (h1, ys) =>
              match h1.memo.lookup x with
              | some y => .ok (h1, y)
              | none =>
                let (h2, y) := h1.alloc (.fdict ys)
                .ok (h2.remember x y, y)
          | .method f s =>
            match deepcopy fuel h s with
            | .error e => .error e
            | .ok (h1, s') =>
              let (h2, y) := h1.alloc (.method f s')
              .ok (h2.remember x y, y)
          | .cls _ | .metaCls _ => .ok (h, x)
          | .inst attrs =>
            -- `copyreg.__newobj__`, with the attributes as the state
            let (h1, y) := h.alloc (.inst [])
            let h2 := h1.remember x y
            match deepAttrs fuel h2 y attrs with
            | .error e => .error e
            | .ok h3 => .ok (h3, y)
          | .hooked _ deepcopier reduce =>
            match deepcopier with
            | some (some e) => .error e
            | some none =>
              let (h1, y) := h.alloc (.atom 1)
              .ok (h1.remember x y, y)
            | none =>
              match reduce with
              | none => .error (uncopyable true)
              | some .str => .ok (h, x)
              | some (.raises e) => .error e
              | some (.tuple size fail kind args state listiter dictiter setstate) =>
                match reconArity size with
                | some e => .error e
                | none =>
                  match deepList fuel h args with
                  | .error e => .error e
                  | .ok (h1, args') =>
                    match fail with
                    | some e => .error e
                    | none =>
                      let (h2, y) := h1.alloc (freshOf kind args')
                      let h3 := h2.remember x y
                      match deepState fuel h3 y state setstate with
                      | .error e => .error e
                      | .ok h5 =>
                        match deepAppend fuel h5 y ((listiter.map (·.items)).getD []) with
                        | .error e => .error e
                        | .ok h6 =>
                          match listiter.bind (·.fail) with
                          | some e => .error e
                          | none =>
                            match deepSetItems fuel h6 y ((dictiter.map (·.items)).getD []) with
                            | .error e => .error e
                            | .ok h7 =>
                              match dictiter.bind (·.fail) with
                              | some e => .error e
                              | none => .ok (h7, y)
          | .atom _ | .str _ => .ok (h, x)

  /-- `for a in x: append(deepcopy(a, memo))`. -/
  def deepList : Nat → Heap → List Nat → Py (Heap × List Nat)
    | 0, _, _ => .error .modelFuel
    | _ + 1, h, [] => .ok (h, [])
    | fuel + 1, h, a :: as =>
      match deepcopy fuel h a with
      | .error e => .error e
      | .ok (h1, y) =>
        match deepList fuel h1 as with
        | .error e => .error e
        | .ok (h2, ys) => .ok (h2, y :: ys)

  /-- `for key, value in x.items(): y[deepcopy(key, memo)] = deepcopy(value, memo)`, Lib/copy.py:200-201 and
  :207-208, with `acc` the items of `y` so far. An assignment evaluates its right side first, so the value is copied
  before the key; the store is `dictSet`, so two keys whose copies are equal (two different source keys that `memo`
  sends to one object, say) make one item. -/
  def deepPairs : Nat → Heap → List (Nat × Nat) → List (Nat × Nat) → Py (Heap × List (Nat × Nat))
    | 0, _, _, _ => .error .modelFuel
    | _ + 1, h, acc, [] => .ok (h, acc)
    | fuel + 1, h, acc, (k, v) :: rest =>
      match deepcopy fuel h v with
      | .error e => .error e
      | .ok (h1, v') =>
        match deepcopy fuel h1 k with
        | .error e => .error e
        | .ok (h2, k') =>
          match dictSet h2 acc k' v' with
          | .error e => .error e
          | .ok acc' => deepPairs fuel h2 acc' rest

  /-- The state of a plain instance, copied and stored attribute by attribute. -/
  def deepAttrs : Nat → Heap → Nat → List (AttrKey × Nat) → Py Heap
    | 0, _, _, _ => .error .modelFuel
    | _ + 1, h, _, [] => .ok h
    | fuel + 1, h, y, (k, v) :: rest =>
      match deepcopy fuel h v with
      | .error e => .error e
      | .ok (h1, v') =>
        match deepKey fuel h1 k with
        | .error e => .error e
        | .ok (h2, k') =>
          match setAttrOf h2 y k' v' with
          | .error e => .error e
          | .ok h3 => deepAttrs fuel h3 y rest

  /-- The copy of a `__dict__` key, value first as in `_deepcopy_dict`, Lib/copy.py:201: a `str` is atomic, any
  other key is deep-copied. -/
  def deepKey : Nat → Heap → AttrKey → Py (Heap × AttrKey)
    | _, h, .name s => .ok (h, .name s)
    | 0, _, .obj _ => .error .modelFuel
    | fuel + 1, h, .obj c =>
      match deepcopy fuel h c with
      | .error e => .error e
      | .ok (h1, c') => .ok (h1, attrKey h1 c')

  /-- Lib/copy.py:252-256 with `deep` true: a state that is not `None` is copied, and then the copy, whatever it is
  (`None` too), goes to `__setstate__` or to the default step. -/
  def deepState : Nat → Heap → Nat → Option Nat → Option (Option PyExc) → Py Heap
    | _, h, _, none, _ => .ok h
    | fuel, h, y, some s, ss =>
      if noneCell h s then .ok h else
      match fuel with
      | 0 => .error .modelFuel
      | f + 1 =>
        match deepcopy f h s with
        | .error e => .error e
        | .ok (h1, s') => stateApply h1 y s' ss

  /-- `for item in listiter: item = deepcopy(item, memo); y.append(item)`, Lib/copy.py:270-272. -/
  def deepAppend : Nat → Heap → Nat → List Nat → Py Heap
    | 0, _, _, _ => .error .modelFuel
    | _ + 1, h, _, [] => .ok h
    | fuel + 1, h, y, i :: rest =>
      match deepcopy fuel h i with
      | .error e => .error e
      | .ok (h1, i') =>
        match appendTo h1 y i' with
        | .error e => .error e
        | .ok h2 => deepAppend fuel h2 y rest

  /-- The same for `dictiter`, Lib/copy.py:278-281: the key, the value, then the store. -/
  def deepSetItems : Nat → Heap → Nat → List (Nat × Nat) → Py Heap
    | 0, _, _, _ => .error .modelFuel
    | _ + 1, h, _, [] => .ok h
    | fuel + 1, h, y, (k, v) :: rest =>
      match deepcopy fuel h k with
      | .error e => .error e
      | .ok (h1, k') =>
        match deepcopy fuel h1 v with
        | .error e => .error e
        | .ok (h2, v') =>
          match setItemOf h2 y k' v' with
          | .error e => .error e
          | .ok h3 => deepSetItems fuel h3 y rest
end

/-- `pickle` accepts two to six items, Modules/_pickle.c `save_reduce`. -/
def pickleReduceOk (n : Nat) : Bool := decide (2 ≤ n) && decide (n ≤ 6)

/-- A class as `replace` sees it: its `__name__`, and its `__replace__` attribute: `none` when it has none,
`some none` when it is set to `None`, `some (some f)` for a callable `f(obj, changes)`. -/
structure ReplaceCls (β α : Type) where
  name : String
  replace : Option (Option (β → List (String × α) → Py β))

/-- `replace(obj, /, **changes)`, Lib/copy.py:290-300: `cls = obj.__class__` (`clsOf`, so an instance that overrides
`__class__` is covered), `getattr(cls, '__replace__', None)`, which an attribute set to `None` also gives, the
`TypeError` with the class's name, and otherwise the call `func(obj, **changes)`. -/
def replaceOp {β α : Type} (clsOf : β → ReplaceCls β α) (obj : β) (changes : List (String × α)) : Py β :=
  let cls := clsOf obj
  let func := cls.replace.getD none
  match func with
  | none => .error (.typeError s!"replace() does not support {cls.name} objects")
  | some f => f obj changes

end PyLean.CoreLibs.Operator
