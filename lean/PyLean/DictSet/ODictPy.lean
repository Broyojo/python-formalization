import PyLean.DictSet.ODict

/-!
The pure-Python `OrderedDict` of `Lib/collections/__init__.py` (CPython 3.14.7), the twin of
`Objects/odictobject.c`. Line numbers refer to that file. It is a dict plus `self.__map`
(key to link) plus a circular doubly linked list of `_Link`s with a sentinel. Links are kept
on a heap with explicit `prev`/`next`, because `popitem` and `clear` leave the removed links'
pointers in place while `__delitem__` and `pop` clear them, and a running generator sees the
difference.
-/

namespace PyLean.DictSet

open PyLean

/-- `_Link` (:66). `key` is `none` on the sentinel, `prev`/`next` are `none` once cleared. -/
structure Link (K : Type) where
  key : Option K
  prev : Option Nat
  next : Option Nat
  deriving Repr, Inhabited

/-- An instance. `heap` is every link ever made, by id; id 0 is `self.__root`. -/
structure PyOD (K V : Type) where
  d : PyDict K V
  map : PyDict K Nat
  heap : List (Link K) := [⟨none, some 0, some 0⟩]
  deriving Repr, Inhabited

abbrev PM (K V : Type) := M (PyOD K V)

variable {K V : Type}

namespace PyOD

def link (o : PyOD K V) (i : Nat) : Link K := o.heap.getD i ⟨none, none, none⟩
def setLink (o : PyOD K V) (i : Nat) (f : Link K → Link K) : PyOD K V :=
  { o with heap := o.heap.set i (f (o.link i)) }
def setNext (o : PyOD K V) (i n : Nat) : PyOD K V := o.setLink i fun l => { l with next := some n }
def setPrev (o : PyOD K V) (i n : Nat) : PyOD K V := o.setLink i fun l => { l with prev := some n }

/-- The keys, walking from the sentinel (`__iter__`, :146-153, with no mutation). -/
def walk (o : PyOD K V) : Nat → Nat → List K
  | 0, _ => []
  | f + 1, i =>
    match o.link i with
    | ⟨some k, _, some n⟩ => k :: walk o f n
    | _ => []

def keysList (o : PyOD K V) : List K :=
  match (o.link 0).next with
  | some n => o.walk o.heap.length n
  | none => []

/-- `self` is empty as a dict. -/
def isEmpty (o : PyOD K V) : Bool := o.d.used == 0

/-- Unlink: `link_prev.next = link_next; link_next.prev = link_prev`. -/
def unlink (o : PyOD K V) (i : Nat) : PyOD K V :=
  match (o.link i).prev, (o.link i).next with
  | some p, some n => (o.setNext p n).setPrev n p
  | _, _ => o

end PyOD

def onD {α : Type} (m : DM K V α) : PM K V α := fun o =>
  match m o.d with
  | (r, d') => (r, { o with d := d' })

def onMap {α : Type} (m : DM K Nat α) : PM K V α := fun o =>
  match m o.map with
  | (r, d') => (r, { o with map := d' })

section
variable [DecidableEq K] (P : Proto K (PyDict K V)) (Q : Proto K (PyDict K Nat))

/-- `OrderedDict.__setitem__` (:119-131). -/
def pyodSetItem (key : K) (value : V) : PM K V Unit := do
  let inSelf ← onD (pyDictContains P key)
  if !inSelf then
    let o ← M.get
    let id := o.heap.length
    onMap (dictSetItem Q key id)
    let o ← M.get
    let root := 0
    let last := (o.link root).prev.getD root
    let l : Link K := ⟨some key, some last, some root⟩
    let o := { o with heap := o.heap ++ [l] }
    M.put ((o.setNext last id).setPrev root id)
  onD (dictSetItem P key value)

/-- Remove the link of `key` from `__map` and unlink it, clearing its pointers
(:138-144, :252-258). -/
def pyodDropLink (key : K) : PM K V Unit := do
  let id ← onMap (dictPopDefault Q key none)
  let o ← M.get
  M.put ((o.unlink id).setLink id fun l => { l with prev := none, next := none })

/-- `OrderedDict.__delitem__` (:133-144). -/
def pyodDelItem (key : K) : PM K V Unit := do
  onD (dictDelItem P key)
  pyodDropLink Q key

/-- `OrderedDict.clear` (:164-169): removed links keep their pointers. -/
def pyodClear (o : PyOD K V) : PyOD K V :=
  ((({ o with map := dictClear o.map, d := dictClear o.d } : PyOD K V).setNext 0 0).setPrev 0 0)

/-- `OrderedDict.popitem` (:171-192). -/
def pyodPopitem (last : Bool) : PM K V (K × V) := do
  let o ← M.get
  if o.isEmpty then M.throw (.keyError "'dictionary is empty'")
  let root := 0
  let (link, o') :=
    if last then
      let link := (o.link root).prev.getD root
      let linkPrev := (o.link link).prev.getD root
      (link, (o.setNext linkPrev root).setPrev root linkPrev)
    else
      let link := (o.link root).next.getD root
      let linkNext := (o.link link).next.getD root
      (link, (o.setNext root linkNext).setPrev linkNext root)
  M.put o'
  match (o'.link link).key with
  | none => M.throw (.keyError "'dictionary is empty'")
  | some key =>
    onMap (dictDelItem Q key)
    let value ← onD (dictPopDefault P key none)
    return (key, value)

/-- `OrderedDict.move_to_end` (:194-217). -/
def pyodMoveToEnd (key : K) (last : Bool) : PM K V Unit := do
  let link ← onMap (dictSubscript Q none key)
  let o ← M.get
  let o := o.unlink link
  let root := 0
  if last then
    let l := (o.link root).prev.getD root
    M.put (((o.setLink link fun x => { x with prev := some l, next := some root }).setPrev root link).setNext l link)
  else
    let first := (o.link root).next.getD root
    M.put (((o.setLink link fun x => { x with prev := some root, next := some first }).setPrev first link).setNext root link)

/-- `OrderedDict.pop` (:245-265). -/
def pyodPop (key : K) (dflt : Option V) : PM K V V := do
  match ← onD (pyDictPop P true key) with
  | some result =>
    pyodDropLink Q key
    return result
  | none =>
    match dflt with
    | some d => return d
    | none => M.throw (keyErr P key)

/-- `OrderedDict.setdefault` (:267-275). -/
def pyodSetdefault (key : K) (dflt : V) : PM K V V := do
  let inSelf ← onD (pyDictContains P key)
  if inSelf then onD (dictSubscript P none key)
  else
    pyodSetItem P Q key dflt
    return dflt

/-- `self[key] = other[key]` for each key. -/
def pyodKeysLoop (getitem : K → Py V) : List K → Option PyExc → PM K V Unit
  | [], stop =>
    match stop with
    | some e => M.throw e
    | none => pure ()
  | key :: rest, stop => do
    let value ← M.lift (getitem key)
    pyodSetItem P Q key value
    pyodKeysLoop getitem rest stop

/-- `for key, value in other: self[key] = value` (`_collections_abc.py:980-982`):
`UNPACK_SEQUENCE`'s own messages. -/
def pyodPairsLoop : List (PairItem K V) → Option PyExc → PM K V Unit
  | [], stop =>
    match stop with
    | some e => M.throw e
    | none => pure ()
  | item :: rest, stop => do
    match item with
    | .notIter e => M.throw e
    | .wrong 0 => M.throw (.valueError "not enough values to unpack (expected 2, got 0)")
    | .wrong 1 => M.throw (.valueError "not enough values to unpack (expected 2, got 1)")
    | .wrong n => M.throw (.valueError s!"too many values to unpack (expected 2, got {n})")
    | .pair k v => pyodSetItem P Q k v
    pyodPairsLoop rest stop

/-- `MutableMapping.update` (`Lib/_collections_abc.py:965-984`), `OrderedDict.update`,
`OrderedDict.__init__` (:113-117). `.itemsObj` objects have no `keys`, so here only their
iteration counts: this is where the twin differs from `mutablemapping_update_arg`. -/
def pyodUpdateArg (arg : ODictArg K V) : PM K V Unit :=
  match arg with
  | .exact d =>
    pyodKeysLoop P Q (fun k => (dictSubscript P none k d).1) (dictKeysList d) none
  | .keysObj keys getitem =>
    match keys.getIter with
    | some e => M.throw e
    | none => pyodKeysLoop P Q getitem keys.items keys.stop
  | .itemsObj _ it | .pairs it =>
    match it.getIter with
    | some e => M.throw e
    | none => pyodPairsLoop P Q it.items it.stop

def pyodUpdate (arg : Option (ODictArg K V)) (kwargs : List (K × V)) : PM K V Unit := do
  match arg with
  | some a => pyodUpdateArg P Q a
  | none => pure ()
  for (k, v) in kwargs do
    pyodSetItem P Q k v

/-- `OrderedDict.__ior__` (:326-328). -/
def pyodIor (other : ODictArg K V) : PM K V Unit := pyodUpdateArg P Q other

/-- A new empty instance (`__new__`, :104-111). -/
def pyodNew (ident : Nat) : PyOD K V := { d := { ident }, map := { ident := ident + 1 } }

/-- `OrderedDict.copy` (:304-306), `self.__class__(self)`, the left half of `__or__`
(:330-335): keys in link order, values through `__getitem__`. -/
def pyodCopyInto (o : PyOD K V) : PM K V Unit :=
  pyodKeysLoop P Q (fun k => (dictSubscript P none k o.d).1) o.keysList none

def pyodCopy (o : PyOD K V) (id : Nat) : Py (PyOD K V) :=
  match pyodCopyInto P Q o (pyodNew id) with
  | (.ok _, r) => .ok r
  | (.error e, _) => .error e

/-- `OrderedDict.__or__` (:330-335). -/
def pyodOr (o : PyOD K V) (id : Nat) (other : ODictArg K V) : Py (PyOD K V) :=
  match (do pyodCopyInto P Q o; pyodUpdateArg P Q other : PM K V Unit) (pyodNew id) with
  | (.ok _, r) => .ok r
  | (.error e, _) => .error e

/-- `OrderedDict.__eq__` (:317-324) on two instances: `all(map(_eq, self, other))` uses
`operator.eq`, which has no identity shortcut, unlike `_odict_keys_equal`. `plainEq` is `==`. -/
def pyodEq (veq : V → V → Py Bool) (plainEq : K → K → Py Bool) (a b : PyOD K V) : Py Bool :=
  match (dictEqual P veq a.d b.d).1 with
  | .error e => .error e
  | .ok false => .ok false
  | .ok true =>
    let rec go : List K → List K → Py Bool
      | x :: xs, y :: ys =>
        match plainEq x y with
        | .error e => .error e
        | .ok false => .ok false
        | .ok true => go xs ys
      | _, _ => .ok true
    go a.keysList b.keysList

/-- `OrderedDict.fromkeys` (:309-315). -/
def pyodFromkeys (id : Nat) (it : Iterable K) (value : V) : Py (PyOD K V) :=
  let run : PM K V Unit := do
    match it.getIter with
    | some e => M.throw e
    | none =>
      for key in it.items do
        pyodSetItem P Q key value
      match it.stop with
      | some e => M.throw e
      | none => pure ()
  match run (pyodNew id) with
  | (.ok _, r) => .ok r
  | (.error e, _) => .error e

end

/-- The generator of `__iter__`/`__reversed__` (:146-162) and of the views (:71-84). -/
inductive GenState where
  | fresh
  | at_ (link : Nat)
  | done
  deriving Repr, Inhabited, DecidableEq

structure PyODGen where
  state : GenState := .fresh
  rev : Bool := false
  deriving Repr, Inhabited

/-- `next(gen)`: `curr = curr.next` on resumption, then `curr.key`; a link whose pointers
were cleared gives `curr = None` and `None.key` raises, killing the generator. -/
def pyodGenNext (o : PyOD K V) (g : PyODGen) : Py (Option K) × PyODGen :=
  let step (i : Nat) : Py (Option K) × PyODGen :=
    if i == 0 then (.ok none, { g with state := .done })
    else
      match (o.link i).key with
      | some k => (.ok (some k), { g with state := .at_ i })
      | none => (.ok none, { g with state := .done })
  let dir (l : Link K) := if g.rev then l.prev else l.next
  match g.state with
  | .done => (.ok none, g)
  | .fresh =>
    match dir (o.link 0) with
    | some n => step n
    | none => (.ok none, { g with state := .done })
  | .at_ i =>
    match dir (o.link i) with
    | some n => step n
    | none =>
      (.error (attributeError "'NoneType' object has no attribute 'key'"), { g with state := .done })

end PyLean.DictSet
