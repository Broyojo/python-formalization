import PyLean.Sequences.Common

/-!
`collections.defaultdict`, the `_count_elements` helper of `Counter` and
`_tuplegetter` (`Modules/_collectionsmodule.c`, CPython 3.15.2).

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
may change, and returns a value or raises; `repr` is its `repr()`, which may raise. -/
inductive Factory (κ ν : Type) where
  | null
  | none
  | call (repr : Py String) (run : PyDict κ ν → Py ν × PyDict κ ν)

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

/-- An entry of the tuple `dd.__reduce__()` returns. -/
inductive RedItem (κ ν : Type) where
  /-- `type(dd)`, by name. -/
  | type (tname : String)
  /-- The argument tuple for it. -/
  | args (fs : List (Factory κ ν))
  | none
  /-- An iterator that will yield `xs`, then end with `e` (`Option.none`: exhaustion). -/
  | iter (xs : List (κ × ν)) (e : Option PyExc)

/-- `dd.__reduce__()` (`defdict_reduce`, _collectionsmodule.c:2279-2332). `items` is the
outcome of `PyObject_CallMethodNoArgs(dd, "items")` (:2315-2319): a subclass may override
`items`, which may raise, return a non-iterable or any iterable (for `dict.items` it is
`.ok (.iter dd.items none)`). The args are `()` for a NULL or `None` factory, else
`(factory,)` (:2309-2312); `PyObject_GetIter` (:2320-2325) runs on the result, and the
5-tuple `(type(dd), args, None, None, iter)` is built at :2326-2327. -/
def reduce (dd : DefDict κ ν) (items : Py (PyIterable (κ × ν))) : Py (List (RedItem κ ν)) :=
  let args : List (Factory κ ν) := match dd.factory with
    | .null | .none => []
    | f => [f]
  match items with
  | .error e => .error e
  | .ok (.notIterable t) => .error (notIterableErr t)
  | .ok (.iter xs e) => .ok [.type dd.tname, .args args, .none, .none, .iter xs e]

/-- `repr(dd)` (`defdict_repr`, _collectionsmodule.c:2374-2410). `base` is
`PyDict_Type.tp_repr` of the items (:2380-2382), computed first and able to raise (an
item's `repr` raising). A NULL factory prints `None` without `Py_ReprEnter`
(:2383-2384). Otherwise `entered` is `Py_ReprEnter(factory)` (:2387): `.ok true` when the
factory is already being printed (`...`, :2393), an exception when it fails
(:2389-2392); else `PyObject_Repr(factory)` (:2396), which may raise (:2400-2402). -/
def repr (dd : DefDict κ ν) (base : PyDict κ ν → Py String) (entered : Py Bool) : Py String := do
  let baserepr ← base dd.items
  let defrepr ← match dd.factory with
    | .null => pure "None"
    | f => do
      let status ← entered
      if status then pure "..."
      else match f with
        | .call r _ => r
        | _ => pure "None"
  return s!"{dd.tname}({defrepr}, {baserepr})"

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
  /-- A `frozendict`, new in 3.15: `PyAnyDict_Check` accepts it. -/
  | frozen (items : PyDict κ ν)
  | notDict

/-- The items of an operand, if it is a dict. -/
def Operand.items? : Operand κ ν → Option (PyDict κ ν)
  | .dd d => some d.items
  | .plain i => some i
  | .frozen i => some i
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

/-- One `PyIter_Next(it)` call of `_count_elements` over mapping state `σ`: the iterator
runs arbitrary code, which may change the mapping, then yields a key or raises. -/
abbrev KeyNext (κ σ : Type) := σ → Py κ × σ

/-- The keys of a list iterator, which does not touch the mapping. -/
def pureKeys {κ σ : Type} (ks : List κ) : List (KeyNext κ σ) := ks.map (fun k s => (.ok k, s))

/-- The end of the loop at `key == NULL`, then `if (PyErr_Occurred()) return NULL`
(_collectionsmodule.c:2654-2656): `PyIter_Next` has already cleared a `StopIteration`
(Objects/abstract.c:2886-2889), any other exception propagates. -/
def iterEnd (e : PyExc) : Py Unit :=
  match e with
  | .stopIteration => .ok ()
  | e => .error e

/-- The fast path of `_collections__count_elements_impl` (_collectionsmodule.c:2575-2617),
`mapping` a dict whose `get` and `__setitem__` are `dict`'s. `hash` is `_PyObject_HashFast`
(the key's `__hash__` and `__eq__` are pure, the assumption that makes a dict a finite map);
`add1 d old` is `PyNumber_Add(oldval, one)`, which runs arbitrary code that may mutate or
clear the dict (the case the comment at :2604-2606 guards), and the result is stored into
the dict as `__add__` left it (:2612). -/
def countFast [DecidableEq κ] (hash : κ → Py Unit) (add1 : PyDict κ ν → ν → Py ν × PyDict κ ν)
    (one : ν) : List (KeyNext κ (PyDict κ ν)) → PyDict κ ν → Py Unit × PyDict κ ν
  | [], d => (.ok (), d)
  | nx :: rest, d =>
    match nx d with
    | (.error e, d) => (iterEnd e, d)
    | (.ok k, d) =>
      match hash k with
      | .error e => (.error e, d)
      | .ok () =>
        match dictGet d k with
        | none => countFast hash add1 one rest (dictSet d k one)
        | some old =>
          match add1 d old with
          | (.error e, d) => (.error e, d)
          | (.ok v, d) => countFast hash add1 one rest (dictSet d k v)

/-- The slow path (_collectionsmodule.c:2620-2645), any mapping state `σ`: `mget s k` is
`bound_get(key, zero)`, `mset s k v` is `PyObject_SetItem`, `isZero` is the test
`oldval == zero` of identity with the int 0, which skips the addition; `add1` may change
the mapping, as in `countFast`. -/
def countSlow {σ : Type} (mget : σ → κ → Py ν × σ) (mset : σ → κ → ν → Py Unit × σ)
    (isZero : ν → Bool) (add1 : σ → ν → Py ν × σ) (one : ν) : List (KeyNext κ σ) → σ → Py Unit × σ
  | [], s => (.ok (), s)
  | nx :: rest, s =>
    match nx s with
    | (.error e, s) => (iterEnd e, s)
    | (.ok k, s) =>
      match mget s k with
      | (.error e, s) => (.error e, s)
      | (.ok old, s) =>
        match (if isZero old then (.ok one, s) else add1 s old) with
        | (.error e, s) => (.error e, s)
        | (.ok v, s) =>
          match mset s k v with
          | (.error e, s) => (.error e, s)
          | (.ok (), s) => countSlow mget mset isZero add1 one rest s

/-- The pure-Python twin, `Lib/collections/__init__.py:540-544`:
`for elem in iterable: mapping[elem] = mapping_get(elem, 0) + 1`. -/
def countPy {σ : Type} (mget : σ → κ → Py ν × σ) (mset : σ → κ → ν → Py Unit × σ)
    (add1 : σ → ν → Py ν × σ) : List (KeyNext κ σ) → σ → Py Unit × σ
  | [], s => (.ok (), s)
  | nx :: rest, s =>
    match nx s with
    | (.error e, s) => (iterEnd e, s)
    | (.ok k, s) =>
      match mget s k with
      | (.error e, s) => (.error e, s)
      | (.ok old, s) =>
        match add1 s old with
        | (.error e, s) => (.error e, s)
        | (.ok v, s) =>
          match mset s k v with
          | (.error e, s) => (.error e, s)
          | (.ok (), s) => countPy mget mset add1 rest s

/-- The mapping operations of a real dict, as the slow path sees them: `get` hashes
the key, and returns the default `zero` for a missing key. -/
def dictMget [DecidableEq κ] (hash : κ → Py Unit) (zero : ν) (d : PyDict κ ν) (k : κ) :
    Py ν × PyDict κ ν :=
  match hash k with
  | .error e => (.error e, d)
  | .ok () => (.ok ((dictGet d k).getD zero), d)

def dictMset [DecidableEq κ] (d : PyDict κ ν) (k : κ) (v : ν) : Py Unit × PyDict κ ν :=
  (.ok (), dictSet d k v)

/-- The iterable argument: `PyObject_GetIter` fails for a non-iterable
(_collectionsmodule.c:2559-2561), otherwise the `PyIter_Next` calls in order. -/
inductive KeySrc (κ σ : Type) where
  | notIterable (tname : String)
  | iter (nexts : List (KeyNext κ σ))

/-- A `PyIterable` of keys as a `KeySrc`: the keys, then a call raising the end exception. -/
def KeySrc.ofIterable {κ σ : Type} : PyIterable κ → KeySrc κ σ
  | .notIterable t => .notIterable t
  | .iter ks e => .iter (pureKeys ks ++ match e with
      | none => []
      | some e => [fun s => (.error e, s)])

/-- `_collections._count_elements(mapping, iterable)` for a `dict` mapping
(`_collections__count_elements_impl`, _collectionsmodule.c:2545-2657). -/
def countDict [DecidableEq κ] (hash : κ → Py Unit) (add1 : PyDict κ ν → ν → Py ν × PyDict κ ν)
    (one : ν) (src : KeySrc κ (PyDict κ ν)) (d : PyDict κ ν) : Py Unit × PyDict κ ν :=
  match src with
  | .notIterable t => (.error (notIterableErr t), d)
  | .iter nexts => countFast hash add1 one nexts d

/-- The same for any other mapping: `bound` is `PyObject_GetAttr(mapping, "get")`
(:2620-2622), which fails for a mapping without `get`. -/
def countMapping {σ : Type} (bound : Py Unit) (mget : σ → κ → Py ν × σ) (mset : σ → κ → ν → Py Unit × σ)
    (isZero : ν → Bool) (add1 : σ → ν → Py ν × σ) (one : ν) (src : KeySrc κ σ) (s : σ) :
    Py Unit × σ :=
  match src with
  | .notIterable t => (.error (notIterableErr t), s)
  | .iter nexts =>
    match bound with
    | .error e => (.error e, s)
    | .ok () => countSlow mget mset isZero add1 one nexts s

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

/-- `tuplegetter_descr_set` (_collectionsmodule.c:2723-2731): always raises;
`value == NULL` is a deletion (`none`). -/
def tuplegetterSet {α : Type} (value : Option α) : PyExc :=
  match value with
  | none => .named "AttributeError" "can't delete attribute"
  | some _ => .named "AttributeError" "can't set attribute"

/-- `tuplegetter_reduce` (_collectionsmodule.c:2761-2766): `(type(g), (index, doc))`. -/
def tuplegetterReduce {δ : Type} (g : TupleGetter δ) : Int × δ := (g.index, g.doc)

/-- `tuplegetter_repr` (_collectionsmodule.c:2769-2775):
`PyUnicode_FromFormat("%s(%zd, %R)", _PyType_Name(type), index, doc)`. The type is not
subclassable (no `Py_TPFLAGS_BASETYPE`, :2804-2805), so the name is `_tuplegetter`;
`%zd` is the decimal index, and `%R` calls `repr(doc)`, which may raise. -/
def tuplegetterRepr {δ : Type} (g : TupleGetter δ) (docRepr : δ → Py String) : Py String := do
  let r ← docRepr g.doc
  return s!"_tuplegetter({g.index}, {r})"

end PyLean.Sequences
