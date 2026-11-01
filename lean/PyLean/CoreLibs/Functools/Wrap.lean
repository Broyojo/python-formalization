import PyLean.CoreLibs.Functools.Dispatch

/-!
`update_wrapper`, `wraps`, `cached_property`, `singledispatchmethod`, the deprecation wrapper of `reduce`, and
the decorator layer of `lru_cache`: Lib/functools.py:35-77, 579-597, 726-728, 995-1085, 1094-1153.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-- An object as its attributes. -/
abbrev Attrs (α : Type) := List (String × α)

/-- `d[k] = v`: an existing key keeps its position. -/
def setAttr {α : Type} (o : Attrs α) (k : String) (v : α) : Attrs α :=
  if o.any (fun p => p.1 == k) then o.map (fun p => if p.1 == k then (k, v) else p) else o ++ [(k, v)]

/-- `dict.update`. -/
def dictUpdate {α : Type} (d e : Attrs α) : Attrs α := e.foldl (fun acc p => setAttr acc p.1 p.2) d

/-- The object written to. Its attributes live in `dict`, so `__dict__` and `setattr` see the same table,
unless `hasDict` is false, as with `__slots__`, when `setattr` goes to `slots`. `setFail` is an exception from
`setattr`, for a read-only attribute, and `others` holds any other dict-valued attribute `updated` may name. -/
structure Wrapper (α : Type) where
  dict : Attrs α
  hasDict : Bool := true
  slots : Attrs α := []
  setFail : String → Option PyExc := fun _ => none
  others : Attrs (Attrs α) := []

/-- The object read from. `read` is `getattr`: `none` is `AttributeError`, and any other exception is one.
`dictOf` is `getattr(wrapped, attr, {})`, with the `{}` default written `none`. -/
structure Wrapped (α : Type) where
  read : String → Py (Option α)
  dictOf : String → Py (Option (Attrs α))

def wrapperSet {α : Type} (w : Wrapper α) (k : String) (v : α) : Py (Wrapper α) :=
  match w.setFail k with
  | some e => .error e
  | none =>
    if w.hasDict then .ok { w with dict := setAttr w.dict k v }
    else .ok { w with slots := setAttr w.slots k v }

/-- The first loop of `update_wrapper`, Lib/functools.py:49-56. -/
def assignLoop {α : Type} (wrapped : Wrapped α) : List String → Wrapper α → Py (Wrapper α)
  | [], w => .ok w
  | a :: rest, w =>
    match wrapped.read a with
    | .error e => .error e
    | .ok none => assignLoop wrapped rest w
    | .ok (some v) =>
      match wrapperSet w a v with
      | .error e => .error e
      | .ok w => assignLoop wrapped rest w

/-- The second loop, Lib/functools.py:57-58: `getattr(wrapper, attr).update(getattr(wrapped, attr, {}))`. The
target is read first, so a missing one raises before `wrapped` is read. -/
def updateLoop {α : Type} (wrapped : Wrapped α) : List String → Wrapper α → Py (Wrapper α)
  | [], w => .ok w
  | a :: rest, w =>
    let target : Option (Attrs α) :=
      if a == "__dict__" then (if w.hasDict then some w.dict else none) else w.others.lookup a
    match target with
    | none => .error (.named "AttributeError" "~object has no attribute")
    | some d =>
      match wrapped.dictOf a with
      | .error e => .error e
      | .ok o =>
        let d' := dictUpdate d (o.getD [])
        let w := if a == "__dict__" then { w with dict := d' }
          else { w with others := setAttr w.others a d' }
        updateLoop wrapped rest w

/-- `update_wrapper`, Lib/functools.py:35-63. `self` is the wrapped object as an attribute value, and the
assignment at :61 comes last so that `__dict__` cannot overwrite it. -/
def updateWrapper {α : Type} (w : Wrapper α) (wrapped : Wrapped α) (self : α)
    (assigned updated : List String) : Py (Wrapper α) :=
  match assignLoop wrapped assigned w with
  | .error e => .error e
  | .ok w =>
    match updateLoop wrapped updated w with
    | .error e => .error e
    | .ok w => wrapperSet w "__wrapped__" self

/-- `WRAPPER_ASSIGNMENTS`, Lib/functools.py:30-31. -/
def wrapperAssignments : List String :=
  ["__module__", "__name__", "__qualname__", "__doc__", "__annotate__", "__type_params__"]

/-- `WRAPPER_UPDATES`, Lib/functools.py:32. -/
def wrapperUpdates : List String := ["__dict__"]

/-- The arguments of `update_wrapper` as objects a `partial` can hold. -/
inductive WArg (α : Type) where
  | wrapper (w : Wrapper α)
  | wrapped (w : Wrapped α) (self : α)
  | names (l : List String)

/-- `update_wrapper`'s own identity, for the `Called` that `partial` makes. -/
def updateWrapperId : Nat := 35

/-- Running a `Called` of `update_wrapper`: the keyword names are the parameters. -/
def runUpdateWrapper {α : Type} (c : Called (WArg α)) : Py (Wrapper α) :=
  match c.id, c.args, c.kw.lookup "wrapped", c.kw.lookup "assigned", c.kw.lookup "updated" with
  | 35, [.wrapper w], some (.wrapped d self), some (.names a), some (.names u) =>
    updateWrapper w d self a u
  | _, _, _, _, _ => .error (.typeError "~update_wrapper() got unexpected arguments")

/-- `wraps`, Lib/functools.py:65-77: `partial(update_wrapper, wrapped=..., assigned=..., updated=...)`. -/
def wraps {α : Type} (wrapped : Wrapped α) (self : α) (assigned updated : List String) : Py (Fn (WArg α)) :=
  partialNewC none (.base updateWrapperId) []
    [("wrapped", .val (.wrapped wrapped self)), ("assigned", .val (.names assigned)),
      ("updated", .val (.names updated))]

/-- `wraps(...)(wrapper)`. -/
def wrapsCall {α : Type} (p : Fn (WArg α)) (w : Wrapper α) : Py (Wrapper α) :=
  match callFn p [.wrapper w] [] with
  | .error e => .error e
  | .ok c => runUpdateWrapper c

/-! ### `lru_cache` as a decorator -/

/-- What `lru_cache(...)(f)` builds. -/
structure LruRec where
  mode : LruMode
  /-- `wrapper.cache_parameters()`, :595 and :587. -/
  maxsize : Option Int
  typed : Bool
  deriving Repr, DecidableEq

/-- `lru_cache(maxsize, typed)`, Lib/functools.py:579-597, applied to a user function, with the twin's
`_lru_cache_wrapper` given as `mode`. `update_wrapper` follows in the same call; it reads `f`, and any
failure of it is `fail`. -/
def lruDecorate (mode : Option Int → Py LruMode) (arg : MaxsizeArg) (typed : Bool) (fail : Option PyExc) :
    Py LruRec :=
  match lruCacheArg arg with
  | .error e => .error e
  | .ok m =>
    match mode m with
    | .error e => .error e
    | .ok w =>
      match fail with
      | some e => .error e
      | none => .ok ⟨w, m, typed⟩

/-- `cache(user_function)`, Lib/functools.py:726-728. -/
def cacheDecorate (mode : Option Int → Py LruMode) (fail : Option PyExc) : Py LruRec :=
  lruDecorate mode .none false fail

/-! ### `_warn_python_reduce_kwargs` -/

/-- The `wrapper` of `_warn_python_reduce_kwargs`, Lib/functools.py:1141-1152. `warn` is `warnings.warn(...)`,
which raises under `-W error`, and `call` is `py_reduce(*args, **kwargs)`, run after it. The second component
says whether it warned. -/
def reduceWarnWrapper {β : Type} (kwnames : List String) (warn : Py Unit) (call : Py β) : Py β × Bool :=
  if kwnames.contains "function" || kwnames.contains "sequence" then
    match warn with
    | .error e => (.error e, true)
    | .ok _ => (call, true)
  else (call, false)

/-! ### `cached_property` -/

/-- What `instance.__dict__` is. `frozen` raises `TypeError` on item assignment, as a `mappingproxy` does. -/
inductive InstDict (α : Type) where
  | none
  | dict (d : Attrs α) (frozen : Bool)

/-- A `cached_property`. `read` gives `func.__doc__` and `func.__module__`. -/
structure CachedProp (α : Type) where
  /-- The function: it gets the instance's dict, which it may change, and gives the value and the dict. -/
  func : Attrs α → Py (α × Attrs α)
  attrname : Option String
  doc : α
  module : α

/-- `cached_property.__init__`, Lib/functools.py:1095-1099: reading `__doc__` or `__module__` may fail,
`AttributeError` included, and the object is not built. -/
def cachedNew {α : Type} (func : Attrs α → Py (α × Attrs α)) (read : String → Py (Option α)) :
    Py (CachedProp α) :=
  match read "__doc__" with
  | .error e => .error e
  | .ok none => .error (.named "AttributeError" "~object has no attribute '__doc__'")
  | .ok (some d) =>
    match read "__module__" with
    | .error e => .error e
    | .ok none => .error (.named "AttributeError" "~object has no attribute '__module__'")
    | .ok (some m) => .ok ⟨func, none, d, m⟩

/-- `cached_property.__set_name__`, Lib/functools.py:1101-1108. -/
def setName (attrname : Option String) (name : String) : Py (Option String) :=
  match attrname with
  | none => .ok (some name)
  | some a =>
    if name ≠ a then
      .error (.typeError
        "~Cannot assign the same cached_property to two different names")
    else .ok (some a)

/-- What `cached_property.__get__` gives. -/
inductive CachedOut (α : Type) where
  | self
  /-- The value, and the instance dict afterwards. -/
  | val (v : α) (d : Attrs α)

/-- `cached_property.__get__`, Lib/functools.py:1110-1135. `obj` is `none` for class access. The
function may have stored under the same name while it ran; the store at :1128 overwrites it. -/
def cachedGet {α : Type} (c : CachedProp α) (obj : Option (InstDict α)) : Py (CachedOut α) :=
  match obj with
  | none => .ok .self
  | some inst =>
    match c.attrname with
    | none =>
      .error (.typeError "Cannot use cached_property instance without calling __set_name__ on it.")
    | some name =>
      match inst with
      | .none => .error (.typeError "~No '__dict__' attribute on instance")
      | .dict d frozen =>
        match d.lookup name with
        | some v => .ok (.val v d)
        | none =>
          match c.func d with
          | .error e => .error e
          | .ok (v, d') =>
            if frozen then
              .error (.typeError "~The '__dict__' attribute does not support item assignment")
            else .ok (.val v (setAttr d' name v))

/-! ### `singledispatchmethod` -/

/-- What a `singledispatchmethod` wraps. `read` gives attributes for `__qualname__`, `__name__`, `__module__`,
`__doc__`, `__annotate__`, `__type_params__`, with `none` for `AttributeError`. -/
structure SdmFunc (α : Type) where
  callable : Bool
  hasGet : Bool
  read : String → Py (Option String)
  dictOf : String → Py (Option (Attrs String))
  abstract : Py (Option α)
  impl : MKind α

/-- `singledispatchmethod(func)`. -/
structure Sdm (α : Type) where
  dispatcher : Dispatcher (MKind α)
  func : SdmFunc α
  /-- The wrapper of `singledispatch`, after `update_wrapper`. -/
  wrapper : Wrapper String

/-- `singledispatch(func)` as `singledispatchmethod` runs it: `funcname` at :984 and `update_wrapper` at :990. -/
def sdmDispatcher {α : Type} (object : Cls) (f : SdmFunc α) : Py (Dispatcher (MKind α) × Wrapper String) :=
  match singledispatch object f.impl (f.read "__name__") with
  | .error e => .error e
  | .ok d =>
    match updateWrapper { dict := [] } ⟨f.read, f.dictOf⟩ "<func>" wrapperAssignments wrapperUpdates with
    | .error e => .error e
    | .ok w => .ok (d, w)

/-- `singledispatchmethod.__init__`, Lib/functools.py:1001-1006. -/
def sdmNew {α : Type} (object : Cls) (f : SdmFunc α) : Py (Sdm α) :=
  if !f.callable && !f.hasGet then .error (.typeError "~is not callable or a descriptor") else
  match sdmDispatcher object f with
  | .error e => .error e
  | .ok (d, w) => .ok ⟨d, f, w⟩

/-- `singledispatchmethod.register`, Lib/functools.py:1008-1013: `func=method`. -/
def sdmRegister {α : Type} (W : World) (tok : Nat) (s : Sdm α) (cls : RegFirst (MKind α))
    (method : Option (MKind α)) : Py (Registered (MKind α) × Sdm α) :=
  match register W tok s.dispatcher cls method with
  | .error e => .error e
  | .ok (r, d) => .ok (r, { s with dispatcher := d })

/-- `singledispatchmethod.__isabstractmethod__`, Lib/functools.py:1018-1020: `none` for the default `False`. -/
def sdmIsAbstract {α : Type} (s : Sdm α) : Py (Option α) := s.func.abstract

/-- `name = x.__qualname__`, falling back to `__name__`, then to `'?'`, on `AttributeError` only:
Lib/functools.py:1023-1029, and :1051-1057 through `__getattr__`. -/
def nameOf (read : String → Py (Option String)) : Py String :=
  match read "__qualname__" with
  | .error e => .error e
  | .ok (some q) => .ok q
  | .ok none =>
    match read "__name__" with
    | .error e => .error e
    | .ok (some n) => .ok n
    | .ok none => .ok "?"

/-- `singledispatchmethod.__repr__`, Lib/functools.py:1022-1030. -/
def sdmRepr {α : Type} (s : Sdm α) : Py String :=
  match nameOf s.func.read with
  | .error e => .error e
  | .ok n => .ok ("<single dispatch method descriptor " ++ n ++ ">")

/-- `_singledispatchmethod_get(unbound, obj, cls)`. `module` and `doc` are the instance attributes it sets,
`none` when the read raised `AttributeError`. -/
structure SdmGet (α : Type) where
  unbound : Sdm α
  obj : Option α
  cls : α
  module : Option String
  doc : Option String

/-- `singledispatchmethod.__get__`, :1015-1016, with `_singledispatchmethod_get.__init__`, :1033-1048. -/
def sdmGet {α : Type} (s : Sdm α) (obj : Option α) (cls : α) : Py (SdmGet α) :=
  match s.func.read "__module__" with
  | .error e => .error e
  | .ok m =>
    match s.func.read "__doc__" with
    | .error e => .error e
    | .ok d => .ok ⟨s, obj, cls, m, d⟩

/-- `_singledispatchmethod_get.__getattr__`, Lib/functools.py:1071-1077: a bare `AttributeError` outside the
five names, and a read of the function inside them. -/
def sdmGetattr {α : Type} (g : SdmGet α) (name : String) : Py (Option String) :=
  if name ∉ ["__name__", "__qualname__", "__isabstractmethod__", "__annotations__", "__type_params__"] then
    .ok none
  else g.unbound.func.read name

/-- `_singledispatchmethod_get.__repr__`, Lib/functools.py:1050-1061. -/
def sdmGetRepr {α : Type} (g : SdmGet α) (repr : α → Py String) : Py String :=
  match nameOf (sdmGetattr g) with
  | .error e => .error e
  | .ok n =>
    match g.obj with
    | none => .ok ("<single dispatch method " ++ n ++ ">")
    | some o =>
      match repr o with
      | .error e => .error e
      | .ok r => .ok ("<bound single dispatch method " ++ n ++ " of " ++ r ++ ">")

/-- `impl.__get__(obj, cls)(*args, **kwargs)`, the end of Lib/functools.py:1069. There is no fallback for an
object without `__get__`, which `__init__` accepts when it is callable. -/
def implCall {α : Type} (impl : MKind α) (obj : Option α) (cls : α) (args : List α)
    (kw : List (String × α)) : Py (Called α) :=
  match impl with
  | .fn id =>
    match obj with
    | none => .ok ⟨id, args, kw⟩
    | some o => .ok ⟨id, o :: args, kw⟩
  | .classm id => .ok ⟨id, cls :: args, kw⟩
  | .staticm id => .ok ⟨id, args, kw⟩
  | .obj _ => .error (.named "AttributeError" "~object has no attribute '__get__'")
  | .partialObj f => callFn (descrGet f obj) args kw
  | .custom get _ call =>
    match get obj with
    | .error e => .error e
    | .ok none => callFn call args kw
    | .ok (some nf) => callFn nf args kw

/-- `_singledispatchmethod_get.__call__`, Lib/functools.py:1063-1069. `classes` is `args[0].__class__`. -/
def sdmCall {α : Type} (W : World) (fuel tok : Nat) (g : SdmGet α) (classOf : α → Cls) (args : List α)
    (kw : List (String × α)) : Py (Called α) × Dispatcher (MKind α) :=
  let d := g.unbound.dispatcher
  match args with
  | [] =>
    match g.unbound.func.read "__name__" with
    | .error e => (.error e, d)
    | .ok n =>
      (.error (.typeError ((n.getD "singledispatchmethod method") ++
        " requires at least 1 positional argument")), d)
  | a :: _ =>
    match dispatch W fuel tok d (classOf a) with
    | (.error e, d) => (.error e, d)
    | (.ok none, d) => (.error (.named "AttributeError" "'NoneType' object has no attribute '__get__'"), d)
    | (.ok (some impl), d) => (implCall impl g.obj g.cls args kw, d)

/-- `_singledispatchmethod_get.__wrapped__`, :1079-1081. -/
def sdmWrapped {α : Type} (g : SdmGet α) : SdmFunc α := g.unbound.func

/-- `_singledispatchmethod_get.register`, :1083-1085: the bound `register` of the `singledispatchmethod`. -/
def sdmGetRegister {α : Type} (W : World) (tok : Nat) (g : SdmGet α) :
    RegFirst (MKind α) → Option (MKind α) → Py (Registered (MKind α) × Sdm α) :=
  sdmRegister W tok g.unbound

end PyLean.CoreLibs.Functools
