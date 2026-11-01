import PyLean.Core

/-!
`Lib/types.py`, CPython 3.14.7, everything below the `_types` import fallback (lines 79-343).

`O` is an abstract universe of Python objects and `Ops` the operations `types.py` applies to them
(`isinstance(x, type)`, `type(x)`, `issubclass`, `hasattr(x, "__mro_entries__")`, ...), so class
creation is a mirror of the algorithm over data, not over one concrete class. `NS` is the prepared
namespace and `R` the result of calling the metaclass. `update_bases` from Python/bltinmodule.c is
modelled next to `resolve_bases` because the two implement the same PEP 560 step.
-/

namespace PyLean.CoreLibs.Misc.Types

open PyLean

/-- What `types.py` asks of objects. -/
structure Ops (O NS R : Type) where
  /-- `isinstance(x, type)` -/
  isType : O → Bool
  /-- `type(x)` -/
  typeOf : O → O
  /-- `issubclass(a, b)` -/
  issubclass : O → O → Py Bool
  /-- `getattr(x, "__mro_entries__", None)`: the call returns `some l` for a tuple and `none`
  for anything else. -/
  mroEntries : O → Option (List O → Py (Option (List O)))
  /-- The builtin `type`. -/
  typeObj : O
  /-- `getattr(meta, "__prepare__", None)`. -/
  prepare : O → Option (String → List O → List (String × O) → Py NS)
  /-- `{}` -/
  emptyNs : NS
  /-- `ns['__orig_bases__'] = bases` -/
  setOrig : NS → List O → Py NS
  /-- `meta(name, bases, ns, **kwds)` -/
  callMeta : O → String → List O → NS → List (String × O) → Py R

variable {O NS R : Type}

/-- `new_bases[i:i+1] = new_base`. -/
def splice (l : List O) (i : Nat) (nb : List O) : List O := l.take i ++ nb ++ l.drop (i + 1)

/-- The `for i, base in enumerate(bases):` loop of `resolve_bases`, Lib/types.py:101-112. -/
def resolveLoop (ops : Ops O NS R) (bases : List O) :
    Nat → List O → List O → Bool → Int → Py (List O × Bool)
  | _, [], new, updated, _ => .ok (new, updated)
  | i, base :: rest, new, updated, shift =>
    if ops.isType base then resolveLoop ops bases (i + 1) rest new updated shift
    else
      match ops.mroEntries base with
      | none => resolveLoop ops bases (i + 1) rest new updated shift
      | some f =>
        match f bases with
        | .error e => .error e
        | .ok none => .error (.typeError "__mro_entries__ must return a tuple")
        | .ok (some nb) =>
          resolveLoop ops bases (i + 1) rest (splice new (i + shift).toNat nb) true
            (shift + nb.length - 1)

/-- `resolve_bases`, Lib/types.py:96-115. `none` is `return bases`, the same object; `some l` is
the new tuple. -/
def resolveBases (ops : Ops O NS R) (bases : List O) : Py (Option (List O)) :=
  match resolveLoop ops bases 0 bases bases false 0 with
  | .error e => .error e
  | .ok (_, false) => .ok none
  | .ok (new, true) => .ok (some new)

/-- The `for` loop of `update_bases`, Python/bltinmodule.c:35-86: `newBases` is `new_bases` once a
replacement has been made. -/
def updateLoop (ops : Ops O NS R) (bases : List O) :
    List O → List O → Option (List O) → Py (Option (List O))
  | [], _, new => .ok new
  | base :: rest, before, new =>
    let keep := new.map (· ++ [base])
    if ops.isType base then updateLoop ops bases rest (before ++ [base]) keep
    else
      match ops.mroEntries base with
      | none => updateLoop ops bases rest (before ++ [base]) keep
      | some f =>
        match f bases with
        | .error e => .error e
        | .ok none => .error (.typeError "__mro_entries__ must return a tuple")
        | .ok (some nb) =>
          let start := new.getD before
          updateLoop ops bases rest (before ++ [base]) (some (start ++ nb))

/-- `update_bases`, Python/bltinmodule.c:29-98. -/
def updateBases (ops : Ops O NS R) (bases : List O) : Py (Option (List O)) :=
  updateLoop ops bases bases [] none

/-- The `for base in bases:` loop of `_calculate_meta`, Lib/types.py:152-163. -/
def calcLoop (ops : Ops O NS R) : O → List O → Py O
  | winner, [] => .ok winner
  | winner, base :: rest =>
    let baseMeta := ops.typeOf base
    match ops.issubclass winner baseMeta with
    | .error e => .error e
    | .ok true => calcLoop ops winner rest
    | .ok false =>
      match ops.issubclass baseMeta winner with
      | .error e => .error e
      | .ok true => calcLoop ops baseMeta rest
      | .ok false => .error (.typeError
          ("metaclass conflict: the metaclass of a derived class must be a (non-strict) " ++
           "subclass of the metaclasses of all its bases"))

/-- `_calculate_meta`, Lib/types.py:149-164. -/
def calculateMeta (ops : Ops O NS R) (mcs : O) (bases : List O) : Py O := calcLoop ops mcs bases

/-- `kwds.pop('metaclass')` on a dict: the value and the remaining items in order. -/
def popMeta : List (String × O) → Option O × List (String × O)
  | [] => (none, [])
  | (k, v) :: rest =>
    if k = "metaclass" then (some v, rest)
    else
      let (m, r) := popMeta rest
      (m, (k, v) :: r)

/-- `prepare_class`, Lib/types.py:117-147. Returns `(meta, ns, kwds)`. -/
def prepareClass (ops : Ops O NS R) (name : String) (bases : List O)
    (kwds : Option (List (String × O))) : Py (O × NS × List (String × O)) :=
  let kwds := kwds.getD []
  let (popped, kwds) := popMeta kwds
  let mcs := match popped with
    | some m => m
    | none =>
      match bases with
      | b :: _ => ops.typeOf b
      | [] => ops.typeObj
  let rest (mcs : O) : Py (O × NS × List (String × O)) :=
    match ops.prepare mcs with
    | some p =>
      match p name bases kwds with
      | .error e => .error e
      | .ok ns => .ok (mcs, ns, kwds)
    | none => .ok (mcs, ops.emptyNs, kwds)
  if ops.isType mcs then
    match calculateMeta ops mcs bases with
    | .error e => .error e
    | .ok mcs => rest mcs
  else rest mcs

/-- `new_class`, Lib/types.py:86-94. -/
def newClass (ops : Ops O NS R) (name : String) (bases : List O)
    (kwds : Option (List (String × O))) (execBody : Option (NS → Py NS)) : Py R :=
  match resolveBases ops bases with
  | .error e => .error e
  | .ok resolved =>
    let rbases := resolved.getD bases
    match prepareClass ops name rbases kwds with
    | .error e => .error e
    | .ok (mcs, ns, kwds) =>
      let body : Py NS := match execBody with
        | some f => f ns
        | none => .ok ns
      match body with
      | .error e => .error e
      | .ok ns =>
        let orig : Py NS := if resolved.isSome then ops.setOrig ns bases else .ok ns
        match orig with
        | .error e => .error e
        | .ok ns => ops.callMeta mcs name rbases ns kwds

/-- What `get_original_bases` reads from `cls`. `dict` is `cls.__dict__.get("__orig_bases__")` when
`cls.__dict__` exists, `bases` is `cls.__bases__` when it exists. -/
structure ClsLike (V : Type) where
  typeName : String
  hasDict : Bool
  origBases : Option V
  bases : Option V

/-- `get_original_bases`, Lib/types.py:167-192. The default argument `cls.__bases__` is evaluated
before `.get` runs, so a missing `__bases__` raises even when `__orig_bases__` is present. -/
def getOriginalBases {V : Type} (cls : ClsLike V) : Py V :=
  let exc : PyExc := .typeError s!"Expected an instance of type, not '{cls.typeName}'"
  if !cls.hasDict then .error exc
  else
    match cls.bases with
    | none => .error exc
    | some b =>
      match cls.origBases with
      | some o => .ok o
      | none => .ok b

/-! ### `DynamicClassAttribute` -/

/-- The attributes of a `DynamicClassAttribute`, Lib/types.py:213-221. -/
structure DCA (F : Type) where
  fget : Option F
  fset : Option F
  fdel : Option F
  doc : Option String
  overwriteDoc : Bool
  isAbstract : Bool

/-- What `types.py` reads from a function: `.__doc__` and `.__isabstractmethod__`. -/
structure FnOps (F : Type) where
  docOf : F → Option String
  abstractOf : F → Bool
  /-- `None.__doc__`, reached by `fget.__doc__` when `fget` is `None`. -/
  noneDoc : Option String

/-- `doc or x`: `None` and `""` are false. -/
def docOr (doc : Option String) (x : Option String) : Option String :=
  match doc with
  | some d => if d = "" then x else some d
  | none => x

variable {F : Type}

/-- `fget.__doc__`, with `None` for a missing function. -/
def fgetDoc (o : FnOps F) : Option F → Option String
  | some f => o.docOf f
  | none => o.noneDoc

/-- `DynamicClassAttribute.__init__`, Lib/types.py:213-221. `doc or fget.__doc__` reads
`fget.__doc__` only when `doc` is false; the read cannot fail. -/
def DCA.init (o : FnOps F) (fget fset fdel : Option F := none) (doc : Option String := none) :
    DCA F :=
  { fget, fset, fdel
    doc := docOr doc (fgetDoc o fget)
    overwriteDoc := doc.isNone
    isAbstract := match fget with
      | some f => o.abstractOf f
      | none => false }

/-- `__get__`'s two exits that are not a call. -/
inductive GetRes (F V : Type) where
  | self
  | value (v : V)

/-- `raise AttributeError(msg)`. -/
def attrErr (msg : String) : PyExc := .named "AttributeError" msg

/-- `DynamicClassAttribute.__get__`, Lib/types.py:223-230. `call` is `fget(instance)`; `instance =
none` is access through the class. -/
def DCA.get {I V : Type} (d : DCA F) (call : F → I → Py V) (inst : Option I) :
    Py (GetRes F V) :=
  match inst with
  | none =>
    if d.isAbstract then .ok .self else .error (attrErr "")
  | some i =>
    match d.fget with
    | none => .error (attrErr "unreadable attribute")
    | some f =>
      match call f i with
      | .error e => .error e
      | .ok v => .ok (.value v)

/-- `DynamicClassAttribute.__set__`, Lib/types.py:232-235. -/
def DCA.set {I V : Type} (d : DCA F) (call : F → I → V → Py Unit) (i : I) (v : V) : Py Unit :=
  match d.fset with
  | none => .error (attrErr "can't set attribute")
  | some f => call f i v

/-- `DynamicClassAttribute.__delete__`, Lib/types.py:237-240. -/
def DCA.delete {I : Type} (d : DCA F) (call : F → I → Py Unit) (i : I) : Py Unit :=
  match d.fdel with
  | none => .error (attrErr "can't delete attribute")
  | some f => call f i

/-- `DynamicClassAttribute.getter`, Lib/types.py:242-246. -/
def DCA.getter (o : FnOps F) (d : DCA F) (fget : F) : DCA F :=
  let fdoc := if d.overwriteDoc then o.docOf fget else none
  let result := DCA.init o (some fget) d.fset d.fdel (docOr fdoc d.doc)
  { result with overwriteDoc := d.overwriteDoc }

/-- `DynamicClassAttribute.setter`, Lib/types.py:248-251. -/
def DCA.setter (o : FnOps F) (d : DCA F) (fset : F) : DCA F :=
  let result := DCA.init o d.fget (some fset) d.fdel d.doc
  { result with overwriteDoc := d.overwriteDoc }

/-- `DynamicClassAttribute.deleter`, Lib/types.py:253-256. -/
def DCA.deleter (o : FnOps F) (d : DCA F) (fdel : F) : DCA F :=
  let result := DCA.init o d.fget d.fset (some fdel) d.doc
  { result with overwriteDoc := d.overwriteDoc }

/-! ### `_GeneratorWrapper` and `coroutine` -/

/-- What `_GeneratorWrapper` delegates to. `G` is the state of the wrapped object. -/
structure GenObj (G V : Type) where
  send : G → V → G × Py V
  throw : G → V → List V → G × Py V
  close : G → G × Py V
  next : G → G × Py V
  giCode : G → Py V
  giFrame : G → Py V
  giRunning : G → Py V
  giYieldfrom : G → Py V
  giSuspended : G → Py V

/-- A `_GeneratorWrapper`, Lib/types.py:260-264. `name` and `qualname` are the `getattr(gen, ...,
None)` reads. -/
structure Wrapper (G : Type) where
  wrapped : G
  isgen : Bool
  name : Option String
  qualname : Option String

variable {G V : Type}

/-- `_GeneratorWrapper.__init__`, Lib/types.py:260-264. -/
def Wrapper.init (g : G) (isgen : Bool) (name qualname : Option String) : Wrapper G :=
  { wrapped := g, isgen, name, qualname }

/-- `_GeneratorWrapper.send`, Lib/types.py:265-266. -/
def Wrapper.send (o : GenObj G V) (w : Wrapper G) (val : V) : Wrapper G × Py V :=
  let (g, r) := o.send w.wrapped val
  ({ w with wrapped := g }, r)

/-- `_GeneratorWrapper.throw`, Lib/types.py:267-268. -/
def Wrapper.throw (o : GenObj G V) (w : Wrapper G) (tp : V) (rest : List V) : Wrapper G × Py V :=
  let (g, r) := o.throw w.wrapped tp rest
  ({ w with wrapped := g }, r)

/-- `_GeneratorWrapper.close`, Lib/types.py:269-270. -/
def Wrapper.close (o : GenObj G V) (w : Wrapper G) : Wrapper G × Py V :=
  let (g, r) := o.close w.wrapped
  ({ w with wrapped := g }, r)

/-- `_GeneratorWrapper.__next__`, Lib/types.py:297-298. -/
def Wrapper.next (o : GenObj G V) (w : Wrapper G) : Wrapper G × Py V :=
  let (g, r) := o.next w.wrapped
  ({ w with wrapped := g }, r)

/-- `_GeneratorWrapper.gi_code`, Lib/types.py:271-273. -/
def Wrapper.giCode (o : GenObj G V) (w : Wrapper G) : Py V := o.giCode w.wrapped
/-- `_GeneratorWrapper.gi_frame`, Lib/types.py:274-276. -/
def Wrapper.giFrame (o : GenObj G V) (w : Wrapper G) : Py V := o.giFrame w.wrapped
/-- `_GeneratorWrapper.gi_running`, Lib/types.py:277-279. -/
def Wrapper.giRunning (o : GenObj G V) (w : Wrapper G) : Py V := o.giRunning w.wrapped
/-- `_GeneratorWrapper.gi_yieldfrom`, Lib/types.py:280-282. -/
def Wrapper.giYieldfrom (o : GenObj G V) (w : Wrapper G) : Py V := o.giYieldfrom w.wrapped
/-- `_GeneratorWrapper.gi_suspended`, Lib/types.py:283-285. -/
def Wrapper.giSuspended (o : GenObj G V) (w : Wrapper G) : Py V := o.giSuspended w.wrapped

/-- `_GeneratorWrapper.__iter__`, Lib/types.py:299-302: `.inl` is `self.__wrapped`, `.inr` is
`self`. -/
def Wrapper.iter (w : Wrapper G) : G ⊕ Wrapper G :=
  if w.isgen then .inl w.wrapped else .inr w

/-- `func` as `coroutine` sees it. `function` is `func.__class__ is FunctionType and
getattr(func, '__code__', None).__class__ is CodeType`; `flags` is `func.__code__.co_flags`. -/
structure CoFunc where
  callable : Bool
  function : Bool
  flags : Nat
  deriving Repr, DecidableEq

/-- What `coroutine(func)` returns. -/
inductive CoResult where
  /-- `return func`, unchanged -/
  | same
  /-- `return func` after `func.__code__ = co.replace(co_flags=co.co_flags | 0x100)` -/
  | flagged (flags : Nat)
  /-- `return wrapped` -/
  | wrapped
  deriving Repr, DecidableEq

/-- `coroutine`, Lib/types.py:305-353, down to the point where `wrapped` is returned. -/
def coroutine (f : CoFunc) : Py CoResult :=
  if !f.callable then .error (.typeError "types.coroutine() expects a callable")
  else if f.function then
    if f.flags &&& 0x180 ≠ 0 then .ok .same
    else if f.flags &&& 0x20 ≠ 0 then .ok (.flagged (f.flags ||| 0x100))
    else .ok .wrapped
  else .ok .wrapped

/-- The object `func(*args)` returned, as `wrapped` classifies it. -/
structure CoValue where
  isCoroutineType : Bool
  isGeneratorType : Bool
  /-- `coro.gi_code.co_flags`, for a generator -/
  flags : Nat
  /-- `isinstance(coro, _collections_abc.Generator)` -/
  isGenerator : Bool
  /-- `isinstance(coro, _collections_abc.Coroutine)` -/
  isCoroutine : Bool
  deriving Repr, DecidableEq

/-- `wrapped(*args, **kwargs)` after `func` returned: does it wrap? Lib/types.py:339-351. -/
def wrappedWraps (c : CoValue) : Bool :=
  if c.isCoroutineType || (c.isGeneratorType && (c.flags &&& 0x100 != 0)) then false
  else if c.isGenerator && !c.isCoroutine then true
  else false

end PyLean.CoreLibs.Misc.Types
