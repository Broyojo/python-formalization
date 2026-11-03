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

/-- What `reductor(4)` gives. -/
inductive RvSpec where
  /-- A string: a global, so `x` itself. -/
  | str
  /-- The reductor raises. -/
  | raises (e : PyExc)
  /-- A tuple. `size` is its length; `func` is the constructor, raising `fail` if that is set; `setstate` is `y`'s
  `__setstate__`, raising if the inner value is set. -/
  | tuple (size : Nat) (fail : Option PyExc) (kind : BuildKind) (args : List Nat) (state : Option Nat)
      (listiter : Option (List Nat)) (dictiter : Option (List (Nat × Nat))) (setstate : Option (Option PyExc))
  deriving Repr, DecidableEq

/-- An object on the heap. `hooked` is an instance of a class with its own protocol: `copier` is `__copy__`,
`deepcopier` is `__deepcopy__`, each raising if the inner value is set, and returning a fresh atom otherwise;
`reduce` is what `__reduce_ex__` gives, `none` for an object that has neither it nor `__reduce__`. `inst` is a plain
instance, which `object.__reduce_ex__` copies through `copyreg.__newobj__`. -/
inductive Cell where
  | atom (n : Int)
  | list (items : List Nat)
  | tuple (items : List Nat)
  | dict (items : List (Nat × Nat))
  /-- A `frozendict`: `copy` returns it, Lib/copy.py:103-104, and `deepcopy` builds a new one, :205-218. -/
  | fdict (items : List (Nat × Nat))
  | inst (attrs : List (String × Nat))
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
item by item (`seqEq`); a `dict` and a `frozendict` by their items, either with either (`dict_richcompare`,
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
def storeItem (eq : Nat → Nat → Py Bool) : List (Nat × Nat) → Nat → Nat → Py (List (Nat × Nat))
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

/-- `y[key] = value`, Lib/copy.py:281 and :284: an object that is not a dict has no `__setitem__`, before the key is
hashed. -/
def setItemOf (h : Heap) (y k v : Nat) : Py Heap :=
  match h.get y with
  | .dict l =>
    match dictSet h l k v with
    | .error e => .error e
    | .ok l' => .ok (h.set y (.dict l'))
  | _ => .error (.typeError "~object does not support item assignment")

/-- `setattr(y, key, value)`, and one entry of `y.__dict__.update(state)`. -/
def setAttrOf (h : Heap) (y : Nat) (k : String) (v : Nat) : Py Heap :=
  match h.get y with
  | .inst a => .ok (h.set y (.inst ((a.filter (fun p => p.1 ≠ k)) ++ [(k, v)])))
  | _ => .error (.named "AttributeError" "~object has no attribute '__dict__'")

def updateFrom (y : Nat) : Heap → List (Nat × Nat) → Py Heap
  | h, [] => .ok h
  | h, (k, v) :: rest =>
    match setAttrOf h y (attrName k) v with
    | .error e => .error e
    | .ok h => updateFrom y h rest

def noneCell (h : Heap) (s : Nat) : Bool :=
  match h.get s with
  | .atom 0 => true
  | _ => false

/-- The state step without `__setstate__`, Lib/copy.py:258-266, on a state that is already copied: a two-item tuple
is `(state, slotstate)`; the state goes through `__dict__.update`, the slot state through `setattr`. `None` is the
atom `0` in the model's graphs. -/
def stateStep (h : Heap) (y st : Nat) : Py Heap :=
  let update (h : Heap) (s : Nat) : Py Heap :=
    match h.get s with
    | .dict items => updateFrom y h items
    | _ => .error (.typeError "~object is not iterable")
  match h.get st with
  | .tuple [a, b] =>
    let h1 : Py Heap := if noneCell h a then .ok h else update h a
    match h1 with
    | .error e => .error e
    | .ok h2 =>
      if noneCell h b then .ok h2 else
      match h2.get b with
      | .dict items => updateFrom y h2 items
      | _ => .error (.named "AttributeError" "~object has no attribute 'items'")
  | _ => if noneCell h st then .ok h else update h st

/-- `y.__setstate__(state)`. The model stores it, so that it can be observed. -/
def setstateOf (h : Heap) (y st : Nat) (fail : Option PyExc) : Py Heap :=
  match fail with
  | some e => .error e
  | none => setAttrOf h y "__state__" st

def freshOf (kind : BuildKind) (args : List Nat) : Cell :=
  match kind with
  | .inst => .inst (args.zipIdx.map (fun p => (attrName p.2, p.1)))
  | .list => .list []
  | .dict => .dict []

/-- The steps of `_reconstruct` after `y` exists, when `deep` is false: nothing is copied. Lib/copy.py:252-285. -/
def reconRest (h : Heap) (y : Nat) (state : Option Nat) (listiter : Option (List Nat))
    (dictiter : Option (List (Nat × Nat))) (setstate : Option (Option PyExc)) : Py Heap :=
  let h1 : Py Heap :=
    match state with
    | none => .ok h
    | some st =>
      match setstate with
      | some f => setstateOf h y st f
      | none => stateStep h y st
  match h1 with
  | .error e => .error e
  | .ok h2 =>
    let appendAll (h : Heap) (l : List Nat) : Py Heap :=
      l.foldl (fun acc i =>
        match acc with
        | .error e => .error e
        | .ok h => appendTo h y i) (.ok h)
    let h3 : Py Heap :=
      match listiter with
      | none => .ok h2
      | some l => appendAll h2 l
    match h3 with
    | .error e => .error e
    | .ok h4 =>
      match dictiter with
      | none => .ok h4
      | some l =>
        l.foldl (fun acc p =>
          match acc with
          | .error e => .error e
          | .ok h => setItemOf h y p.1 p.2) (.ok h4)

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

/-- `copy(x)`, Lib/copy.py:62-100. `tuple` is atomic here and only here. -/
def copyShallow (h : Heap) (x : Nat) : Py (Heap × Nat) :=
  match h.get x with
  | .atom _ | .tuple _ | .fdict _ | .cls _ | .metaCls _ => .ok (h, x)
  | .list l => let (h1, y) := h.alloc (.list l); .ok (h1, y)
  | .dict l => let (h1, y) := h.alloc (.dict l); .ok (h1, y)
  | .inst a => let (h1, y) := h.alloc (.inst a); .ok (h1, y)
  | .method f s => let (h1, y) := h.alloc (.method f s); .ok (h1, y)
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
      | .atom _ | .cls _ => .ok (h, x)
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
                      match deepOpt fuel h3 state with
                      | .error e => .error e
                      | .ok (h4, st') =>
                        match reconRest h4 y st' none none setstate with
                        | .error e => .error e
                        | .ok h5 =>
                          match deepAppend fuel h5 y (listiter.getD []) with
                          | .error e => .error e
                          | .ok h6 =>
                            match deepSetItems fuel h6 y (dictiter.getD []) with
                            | .error e => .error e
                            | .ok h7 => .ok (h7, y)
          | .atom _ => .ok (h, x)

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
  def deepAttrs : Nat → Heap → Nat → List (String × Nat) → Py Heap
    | 0, _, _, _ => .error .modelFuel
    | _ + 1, h, _, [] => .ok h
    | fuel + 1, h, y, (k, v) :: rest =>
      match deepcopy fuel h v with
      | .error e => .error e
      | .ok (h1, v') =>
        match setAttrOf h1 y k v' with
        | .error e => .error e
        | .ok h2 => deepAttrs fuel h2 y rest

  def deepOpt : Nat → Heap → Option Nat → Py (Heap × Option Nat)
    | _, h, none => .ok (h, none)
    | 0, _, some _ => .error .modelFuel
    | fuel + 1, h, some s =>
      match deepcopy fuel h s with
      | .error e => .error e
      | .ok (h1, s') => .ok (h1, some s')

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

/-- `replace(obj, **changes)`, Lib/copy.py:290-300: the class's `__replace__`, called, or `TypeError`. -/
def replaceOp {β : Type} (meth : Option (Py β)) (cls : String) : Py β :=
  match meth with
  | some r => r
  | none => .error (.typeError s!"replace() does not support {cls} objects")

end PyLean.CoreLibs.Operator
