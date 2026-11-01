import PyLean.Sequences.Common

/-!
`collections.defaultdict`, the `_count_elements` helper of `Counter` and
`_tuplegetter` (`Modules/_collectionsmodule.c`, CPython 3.14.7).

`dict` itself belongs to `Objects/dictobject.c`; here a dict is its items in
insertion order, over key and value types `κ`, `ν`, where `κ` has decidable
equality standing for "same hash and `==`". That is the assumption under which
`dict` is a finite map: `__hash__` and `__eq__` of the keys are pure and
consistent, and do not mutate the dict.
-/

namespace PyLean.Sequences

open PyLean

variable {κ ν : Type}

/-- A dict's items in insertion order. -/
abbrev PyDict (κ ν : Type) := List (κ × ν)

/-- `d.get(k)`. -/
def dictGet [DecidableEq κ] (d : PyDict κ ν) (k : κ) : Option ν := d.lookup k

/-- `d[k] = v`: a known key keeps its place. -/
def dictSet [DecidableEq κ] : PyDict κ ν → κ → ν → PyDict κ ν
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v =>
    if k' = k then (k, v) :: rest else (k', v') :: dictSet rest k v

/-- `d.update(other)`. -/
def dictUpdate [DecidableEq κ] (d other : PyDict κ ν) : PyDict κ ν :=
  other.foldl (fun d kv => dictSet d kv.1 kv.2) d

/-- The factory of a defaultdict. `null` is the C `NULL` of `dd.__init__()` and a
fresh object; `none` is an explicit `None`. A callable runs on the items, which it
may change, and returns a value or raises. -/
inductive Factory (κ ν : Type) where
  | null
  | none
  | call (repr : String) (run : PyDict κ ν → Py ν × PyDict κ ν)

structure DefDict (κ ν : Type) where
  items : PyDict κ ν
  factory : Factory κ ν
  tname : String

namespace DefDict

variable [DecidableEq κ]

/-- `defdict_missing` (_collectionsmodule.c:2234-2256). `keyRepr` renders the key:
`PyErr_SetObject(KeyError, (key,))` unpacks the tuple into the arguments, so even a
tuple key raises `KeyError(key)`. `PyDict_SetDefaultRef` keeps a value the factory
itself stored under `key`. -/
def missing (dd : DefDict κ ν) (keyRepr : κ → String) (key : κ) : Py ν × DefDict κ ν :=
  match dd.factory with
  | .null | .none => (.error (.keyError (keyRepr key)), dd)
  | .call _ run =>
    match run dd.items with
    | (.error e, items) => (.error e, { dd with items })
    | (.ok v, items) =>
      match dictGet items key with
      | some old => (.ok old, { dd with items })
      | Option.none => (.ok v, { dd with items := dictSet items key v })

/-- `dd[key]`: `dict_subscript` finds the item, else calls `__missing__`. -/
def getitem (dd : DefDict κ ν) (keyRepr : κ → String) (key : κ) : Py ν × DefDict κ ν :=
  match dictGet dd.items key with
  | some v => (.ok v, dd)
  | Option.none => dd.missing keyRepr key

/-- `new_defdict` (_collectionsmodule.c:2259-2264):
`type(dd)(dd.default_factory, arg)`. A NULL factory is passed as `None`. -/
def newFrom (dd : DefDict κ ν) (arg : PyDict κ ν) : DefDict κ ν :=
  { items := dictUpdate [] arg
    factory := match dd.factory with | .null => .none | f => f
    tname := dd.tname }

/-- `dd.copy()`, `dd.__copy__()` (`defdict_copy`, _collectionsmodule.c:2269-2276). -/
def copy (dd : DefDict κ ν) : DefDict κ ν := dd.newFrom dd.items

/-- `dd.__reduce__()` (`defdict_reduce`, _collectionsmodule.c:2279-2332):
`(type(dd), args, None, None, iter(dd.items()))`. `args` is empty for a NULL or
`None` factory, else `(factory,)`; here the factory's repr stands for it. -/
def reduce (dd : DefDict κ ν) : Option String × PyDict κ ν :=
  match dd.factory with
  | .null | .none => (Option.none, dd.items)
  | .call r _ => (some r, dd.items)

/-- `repr(dd)` (`defdict_repr`, _collectionsmodule.c:2374-2410). `base` is
`dict.__repr__`, `entered` is `Py_ReprEnter` finding the factory being printed. -/
def repr (dd : DefDict κ ν) (base : PyDict κ ν → String) (entered : Bool) : String :=
  let defrepr := match dd.factory with
    | .null | .none => if entered then "..." else "None"
    | .call r _ => if entered then "..." else r
  s!"{dd.tname}({defrepr}, {base dd.items})"

/-- The first argument of `defaultdict(...)`. -/
inductive FactoryArg (κ ν : Type) where
  /-- No positional argument. -/
  | absent
  | given (f : Factory κ ν)
  /-- Neither callable nor `None`. -/
  | bad

/-- `dd.__init__(first, *rest, **kw)` (`defdict_init`, _collectionsmodule.c:2464-2492).
`rest` is what `dict.__init__(dd, *rest, **kw)` adds, or its exception. The factory
is replaced before `dict.__init__` runs. -/
def init (dd : DefDict κ ν) (first : FactoryArg κ ν) (rest : Py (PyDict κ ν)) : Py Unit × DefDict κ ν :=
  match first with
  | .bad => (.error (.typeError "first argument must be callable or None"), dd)
  | _ =>
    let f := match first with
      | .given f => f
      | _ => .null
    let dd := { dd with factory := f }
    match rest with
    | .error e => (.error e, dd)
    | .ok kvs => (.ok (), { dd with items := dictUpdate dd.items kvs })

/-- An operand of `|`. -/
inductive Operand (κ ν : Type) where
  | dd (d : DefDict κ ν)
  | plain (items : PyDict κ ν)
  | notDict

/-- The items of an operand, if it is a dict. -/
def Operand.items? : Operand κ ν → Option (PyDict κ ν)
  | .dd d => some d.items
  | .plain i => some i
  | .notDict => Option.none

/-- `left | right` (`defdict_or`, _collectionsmodule.c:2413-2444): `none` is
`NotImplemented`. One operand is a defaultdict (the slot's precondition); the result
has its type and factory: `new_defdict(self, left)`, then `PyDict_Update(new, right)`. -/
def orOp (left right : Operand κ ν) : Option (DefDict κ ν) :=
  let self? := match left, right with
    | .dd d, _ => some d
    | _, .dd d => some d
    | _, _ => Option.none
  match self?, left.items?, right.items? with
  | some self, some l, some r =>
    let new := self.newFrom l
    some { new with items := dictUpdate new.items r }
  | _, _, _ => Option.none

end DefDict

/-! ### `_count_elements` -/

/-- The fast path of `_collections__count_elements_impl`
(_collectionsmodule.c:2578-2620), `mapping` a dict whose `get` and `__setitem__` are
`dict`'s. `hash` is `_PyObject_HashFast`, `add1` is `PyNumber_Add(oldval, one)`. -/
def countFast [DecidableEq κ] (hash : κ → Py Unit) (add1 : ν → Py ν) (one : ν) :
    List κ → PyDict κ ν → Py Unit × PyDict κ ν
  | [], d => (.ok (), d)
  | k :: ks, d =>
    match hash k with
    | .error e => (.error e, d)
    | .ok () =>
      match dictGet d k with
      | none => countFast hash add1 one ks (dictSet d k one)
      | some old =>
        match add1 old with
        | .error e => (.error e, d)
        | .ok v => countFast hash add1 one ks (dictSet d k v)

/-- The slow path (_collectionsmodule.c:2622-2646), any mapping `σ`: `mget s k` is
`bound_get(key, zero)`, `mset s k v` is `PyObject_SetItem`, `isZero` is the test
`oldval == zero` of identity with the int 0, which skips the addition. -/
def countSlow {σ : Type} (mget : σ → κ → Py ν × σ) (mset : σ → κ → ν → Py Unit × σ)
    (isZero : ν → Bool) (add1 : ν → Py ν) (one : ν) : List κ → σ → Py Unit × σ
  | [], s => (.ok (), s)
  | k :: ks, s =>
    match mget s k with
    | (.error e, s) => (.error e, s)
    | (.ok old, s) =>
      match (if isZero old then .ok one else add1 old) with
      | .error e => (.error e, s)
      | .ok v =>
        match mset s k v with
        | (.error e, s) => (.error e, s)
        | (.ok (), s) => countSlow mget mset isZero add1 one ks s

/-- The pure-Python twin, `Lib/collections/__init__.py:540-544`:
`mapping[elem] = mapping_get(elem, 0) + 1`. -/
def countPy {σ : Type} (mget : σ → κ → Py ν × σ) (mset : σ → κ → ν → Py Unit × σ)
    (add1 : ν → Py ν) : List κ → σ → Py Unit × σ
  | [], s => (.ok (), s)
  | k :: ks, s =>
    match mget s k with
    | (.error e, s) => (.error e, s)
    | (.ok old, s) =>
      match add1 old with
      | .error e => (.error e, s)
      | .ok v =>
        match mset s k v with
        | (.error e, s) => (.error e, s)
        | (.ok (), s) => countPy mget mset add1 ks s

/-- The mapping operations of a real dict, as the slow path sees them: `get` hashes
the key, and returns the default `zero` for a missing key. -/
def dictMget [DecidableEq κ] (hash : κ → Py Unit) (zero : ν) (d : PyDict κ ν) (k : κ) :
    Py ν × PyDict κ ν :=
  match hash k with
  | .error e => (.error e, d)
  | .ok () => (.ok ((dictGet d k).getD zero), d)

def dictMset [DecidableEq κ] (d : PyDict κ ν) (k : κ) (v : ν) : Py Unit × PyDict κ ν :=
  (.ok (), dictSet d k v)

/-- The iterator's own end, then the error: `_count_elements` returns NULL when an
exception is set after the loop (_collectionsmodule.c:2649-2656), so an iterator
that raises leaves the counts it reached. -/
def countFinish (src : Option PyExc) (r : Py Unit) : Py Unit :=
  match r with
  | .error e => .error e
  | .ok () =>
    match src with
    | none | some .stopIteration => .ok ()
    | some e => .error e

/-- `_collections._count_elements(mapping, iterable)` for a `dict` mapping
(`_collections__count_elements_impl`, _collectionsmodule.c:2545-2657). -/
def countDict [DecidableEq κ] (hash : κ → Py Unit) (add1 : ν → Py ν) (one : ν)
    (src : PyIterable κ) (d : PyDict κ ν) : Py Unit × PyDict κ ν :=
  match src with
  | .notIterable t => (.error (notIterableErr t), d)
  | .iter ks e =>
    let (r, d) := countFast hash add1 one ks d
    (countFinish e r, d)

/-- The same for any other mapping. -/
def countMapping {σ : Type} (mget : σ → κ → Py ν × σ) (mset : σ → κ → ν → Py Unit × σ)
    (isZero : ν → Bool) (add1 : ν → Py ν) (one : ν) (src : PyIterable κ) (s : σ) : Py Unit × σ :=
  match src with
  | .notIterable t => (.error (notIterableErr t), s)
  | .iter ks e =>
    let (r, s) := countSlow mget mset isZero add1 one ks s
    (countFinish e r, s)

/-! ### `_tuplegetter` -/

/-- `_tuplegetterobject` (_collectionsmodule.c:2660-2664): `doc` is any object. -/
structure TupleGetter (δ : Type) where
  index : Int
  doc : δ

/-- `obj` of `tuplegetter_descr_get`. -/
inductive TGObj (α : Type) where
  | null
  | none
  | tuple (xs : List α)
  | other (tname : String)

/-- `_tuplegetter(index, doc)` (`tuplegetter_new_impl`, _collectionsmodule.c:2679-2690),
with the clinic's `Py_ssize_t`. -/
def tuplegetterNew {δ : Type} (index : Int) (doc : δ) : Py (TupleGetter δ) := do
  let i ← asSsize index
  return ⟨i, doc⟩

/-- `tuplegetter_descr_get` (_collectionsmodule.c:2693-2720): `.ok none` is the
descriptor itself. -/
def tuplegetterGet {α δ : Type} [Inhabited α] (g : TupleGetter δ) (obj : TGObj α) : Py (Option α) :=
  match obj with
  | .null | .none => .ok none
  | .other t =>
    .error (.typeError s!"descriptor for index '{g.index}' for tuple subclasses doesn't apply to '{t}' object")
  | .tuple xs =>
    if !validIndex g.index xs.length then .error (.indexError "tuple index out of range")
    else .ok (some (ix xs g.index))

/-- `tuplegetter_descr_set` (_collectionsmodule.c:2723-2731): always raises. -/
def tuplegetterSet {α : Type} (value : Option α) : PyExc :=
  match value with
  | none => .named "AttributeError" "can't delete attribute"
  | some _ => .named "AttributeError" "can't set attribute"

/-- `tuplegetter_reduce` (_collectionsmodule.c:2761-2766): `(type(g), (index, doc))`. -/
def tuplegetterReduce {δ : Type} (g : TupleGetter δ) : Int × δ := (g.index, g.doc)

/-- `tuplegetter_repr` (_collectionsmodule.c:2769-2775). -/
def tuplegetterRepr {δ : Type} (g : TupleGetter δ) (docRepr : δ → String) : String :=
  s!"_tuplegetter({g.index}, {docRepr g.doc})"

end PyLean.Sequences
