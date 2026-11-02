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

/-- `y[key] = value`, Lib/copy.py:281 and :284. -/
def setItemOf (h : Heap) (y k v : Nat) : Py Heap :=
  match h.get y with
  | .dict l => .ok (h.set y (.dict (l ++ [(k, v)])))
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

/-- What makes `hash(k)` fail: the type that has no hash. -/
def keyHashErr : Nat → Heap → Nat → Option String
  | 0, _, _ => none
  | f + 1, h, k =>
    match h.get k with
    | .list _ => some "list"
    | .dict _ => some "dict"
    | .tuple items => items.findSome? (keyHashErr f h)
    | _ => none

def cellName : Cell → String
  | .list _ => "list"
  | .dict _ => "dict"
  | .tuple _ => "tuple"
  | _ => "object"

/-- The `TypeError` of storing `k` as a dict key, which a key's copy can meet when `memo` holds something mutable for it. -/
def storeKey (h : Heap) (k : Nat) : Option PyExc :=
  (keyHashErr 8 h k).map fun u => .typeError s!"cannot use '{cellName (h.get k)}' as a dict key (unhashable type: '{u}')"

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
            match deepPairs fuel h2 items with
            | .error e => .error e
            | .ok (h3, ys) => .ok (h3.set y (.dict ys), y)
          | .fdict items =>
            -- `_deepcopy_frozendict`, Lib/copy.py:205-218: nothing is in `memo` during the copies, and a recursive
            -- structure may have put a copy there, which wins; the result is always a new object
            match deepPairs fuel h items with
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

  /-- `y[deepcopy(key, memo)] = deepcopy(value, memo)`, Lib/copy.py:200. An assignment evaluates its right side
  first, so the value is copied before the key. -/
  def deepPairs : Nat → Heap → List (Nat × Nat) → Py (Heap × List (Nat × Nat))
    | 0, _, _ => .error .modelFuel
    | _ + 1, h, [] => .ok (h, [])
    | fuel + 1, h, (k, v) :: rest =>
      match deepcopy fuel h v with
      | .error e => .error e
      | .ok (h1, v') =>
        match deepcopy fuel h1 k with
        | .error e => .error e
        | .ok (h2, k') =>
          match storeKey h2 k' with
          | some e => .error e
          | none =>
            match deepPairs fuel h2 rest with
            | .error e => .error e
            | .ok (h3, ys) => .ok (h3, (k', v') :: ys)

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
