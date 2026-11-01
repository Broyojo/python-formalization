import PyLean.CoreLibs.Functools.Partial

/-!
`singledispatch`, Lib/functools.py:731-991. The class hierarchy is data, and `issubclass` is fallible,
because it runs `__subclasscheck__` and `__subclasshook__`.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

abbrev Cls := Nat

/-- A class hierarchy as data. An element of `registry.keys()` need not be a class: `isType` is
`hasattr(typ, '__mro__')` and `isAlias` is `isinstance(typ, GenericAlias)`. -/
structure World where
  bases : Cls → List Cls
  mro : Cls → List Cls
  /-- `issubclass(a, b)`, which may raise from an ABC hook. -/
  isSub : Cls → Cls → Py Bool
  /-- `hasattr(cls, '__abstractmethods__')`. -/
  isAbc : Cls → Bool
  /-- `cls.__subclasses__()`. -/
  subclasses : Cls → List Cls
  isType : Cls → Bool
  isAlias : Cls → Bool

/-- A list comprehension with a fallible condition. -/
def filterPy {α : Type} (p : α → Py Bool) : List α → Py (List α)
  | [] => .ok []
  | x :: xs =>
    match p x with
    | .error e => .error e
    | .ok b =>
      match filterPy p xs with
      | .error e => .error e
      | .ok r => .ok (if b then x :: r else r)

/-- `any(...)` with a fallible body, which stops at the first `True`. -/
def anyPy {α : Type} (p : α → Py Bool) : List α → Py Bool
  | [] => .ok false
  | x :: xs =>
    match p x with
    | .error e => .error e
    | .ok true => .ok true
    | .ok false => anyPy p xs

/-- The first sequence head not in the tail of any sequence, Lib/functools.py:746-753. -/
def candidateOf (seqs : List (List Cls)) : Option Cls :=
  seqs.findSome? (fun s =>
    match s with
    | [] => none
    | c :: _ => if seqs.any (fun t => t.tail.contains c) then none else some c)

/-- `_c3_merge`, Lib/functools.py:735-760. -/
def c3Merge : (fuel : Nat) → List (List Cls) → Py (List Cls)
  | 0, _ => .error .modelFuel
  | fuel + 1, seqs =>
    let seqs := seqs.filter (fun s => !s.isEmpty)
    if seqs.isEmpty then .ok []
    else
      match candidateOf seqs with
      | none => .error (.named "RuntimeError" "Inconsistent hierarchy")
      | some c => do
        let rest ← c3Merge fuel (seqs.map (fun s => if s.head? = some c then s.tail else s))
        pure (c :: rest)

/-- The last index-plus-one of a base with `__abstractmethods__`, Lib/functools.py:779-784. -/
def boundaryOf (W : World) (bases : List Cls) : Nat :=
  match (bases.reverse.zipIdx.find? (fun p => W.isAbc p.1)) with
  | some (_, i) => bases.length - i
  | none => 0

/-- The test at Lib/functools.py:790-792: `cls` introduces the behaviour of `base`. -/
def introduces (W : World) (cls base : Cls) : Py Bool :=
  match W.isSub cls base with
  | .error e => .error e
  | .ok false => .ok false
  | .ok true =>
    match anyPy (fun b => W.isSub b base) (W.bases cls) with
    | .error e => .error e
    | .ok a => .ok !a

/-- `_c3_mro`, Lib/functools.py:762-805. The three loops run in order, so an `issubclass` failure happens
before any recursion. -/
def c3Mro (W : World) : (fuel : Nat) → Cls → List Cls → Py (List Cls)
  | 0, _, _ => .error .modelFuel
  | fuel + 1, cls, abcs => do
    let bases := W.bases cls
    let boundary := boundaryOf W bases
    let explicitBases := bases.take boundary
    let otherBases := bases.drop boundary
    let abstractBases ← filterPy (introduces W cls) abcs
    let abcs' := abstractBases.foldl List.erase abcs
    let e ← mapPy (fun b => c3Mro W fuel b abcs') explicitBases
    let a ← mapPy (fun b => c3Mro W fuel b abcs') abstractBases
    let o ← mapPy (fun b => c3Mro W fuel b abcs') otherBases
    let seqs := [[cls]] ++ e ++ a ++ o ++ [explicitBases] ++ [abstractBases] ++ [otherBases]
    -- each pass removes at least one element
    c3Merge ((seqs.map List.length).sum + 1) seqs

/-- `is_related` of `_compose_mro`, Lib/functools.py:816-819. -/
def isRelated (W : World) (cls typ : Cls) : Py Bool :=
  if typ ∈ W.mro cls ∨ !W.isType typ ∨ W.isAlias typ then .ok false else W.isSub cls typ

/-- `is_strict_base` of `_compose_mro`, Lib/functools.py:823-827. -/
def isStrictBase (W : World) (types : List Cls) (typ : Cls) : Bool :=
  types.any (fun other => typ != other && (W.mro other).contains typ)

/-- The inner loop of `_compose_mro`, Lib/functools.py:834-837, in the order of `__subclasses__()`. -/
def foundFor (W : World) (cls : Cls) (types : List Cls) (typ : Cls) : Py (List (List Cls)) := do
  let subs ← filterPy (fun sub =>
    if sub ∈ W.mro cls then .ok false else W.isSub cls sub) (W.subclasses typ)
  pure (subs.map (fun sub => (W.mro sub).filter (fun s => types.contains s)))

/-- One round of the outer loop, Lib/functools.py:833-846. `found.sort(key=len, reverse=True)` is stable. -/
def composeStep (W : World) (cls : Cls) (types : List Cls) (acc : List Cls) (typ : Cls) : Py (List Cls) := do
  let found ← foundFor W cls types typ
  if found.isEmpty then pure (acc ++ [typ])
  else
    let sorted := found.mergeSort (fun a b => a.length ≥ b.length)
    pure (sorted.foldl (fun acc sub =>
      sub.foldl (fun acc s => if s ∈ acc then acc else acc ++ [s]) acc) acc)

def foldPy {α β : Type} (f : α → β → Py α) : α → List β → Py α
  | a, [] => .ok a
  | a, b :: bs =>
    match f a b with
    | .error e => .error e
    | .ok a' => foldPy f a' bs

/-- `_compose_mro` before the final call, Lib/functools.py:814-846: the ABCs to insert. -/
def composeAbcs (W : World) (cls : Cls) (types : List Cls) : Py (List Cls) := do
  let types ← filterPy (isRelated W cls) types
  let types' := types.filter (fun t => !isStrictBase W types t)
  foldPy (composeStep W cls types') [] types'

/-- `_compose_mro`, Lib/functools.py:807-847. -/
def composeMro (W : World) (fuel : Nat) (cls : Cls) (types : List Cls) : Py (List Cls) := do
  c3Mro W fuel cls (← composeAbcs W cls types)

/-- The registry, in insertion order. -/
abbrev Registry (ι : Type) := List (Cls × ι)

/-- The loop of `_find_impl`, Lib/functools.py:861-872: it stops at the element after the match. -/
def findLoop {ι : Type} (W : World) (cls : Cls) (reg : Registry ι) :
    Option Cls → List Cls → Py (Option Cls)
  | m, [] => .ok m
  | some m, t :: _ =>
    if (reg.lookup t).isSome && !(W.mro cls).contains t && !(W.mro cls).contains m then
      match W.isSub m t with
      | .error e => .error e
      | .ok true => .ok (some m)
      | .ok false => .error (.named "RuntimeError" "~Ambiguous dispatch")
    else .ok (some m)
  | none, t :: rest =>
    if (reg.lookup t).isSome then findLoop W cls reg (some t) rest
    else findLoop W cls reg none rest

/-- `_find_impl`, Lib/functools.py:849-873. -/
def findImpl {ι : Type} (W : World) (fuel : Nat) (cls : Cls) (reg : Registry ι) : Py (Option ι) := do
  let mro ← composeMro W fuel cls (reg.map Prod.fst)
  let m ← findLoop W cls reg none mro
  pure (m.bind (fun c => reg.lookup c))

/-- The closure state of `singledispatch`, Lib/functools.py:889-891, and `funcname`, :984. -/
structure Dispatcher (ι : Type) where
  registry : Registry ι
  cache : List (Cls × Option ι)
  token : Option Nat
  name : String := "singledispatch function"

/-- `registry[c] = i`: an existing key keeps its position. -/
def regSet {ι : Type} : Registry ι → Cls → ι → Registry ι
  | [], c, i => [(c, i)]
  | p :: ps, c, i => if p.1 == c then (c, i) :: ps else p :: regSet ps c i

/-- A value `register` stores under: one class, or a union of classes. -/
inductive RegArg where
  | cls (c : Cls)
  | union (cs : List Cls)
  deriving Repr, DecidableEq

/-- The end of `register`, Lib/functools.py:968-976. A `types.UnionType` has no
`__abstractmethods__`, so the test at :973 is false for a union, whatever its members are. -/
def regStore {ι : Type} (W : World) (abcToken : Nat) (d : Dispatcher ι) (arg : RegArg) (f : ι) :
    Dispatcher ι :=
  let registry := match arg with
    | .union cs => cs.foldl (fun r c => regSet r c f) d.registry
    | .cls c => regSet d.registry c f
  let hasAbstract := match arg with
    | .union _ => false
    | .cls c => W.isAbc c
  let token := if d.token.isNone && hasAbstract then some abcToken else d.token
  { d with registry, cache := [], token }

/-- A value as `_is_valid_dispatch_type` and the annotation checks see it. -/
inductive TypeVal where
  | cls (c : Cls)
  /-- A `UnionType`, its `__args__` with `none` for one that is not a class. -/
  | union (args : List (Option Cls))
  | forwardRef
  | other
  deriving Repr, DecidableEq

/-- `_is_valid_dispatch_type`, Lib/functools.py:916-920, with what `register` then stores. -/
def validType : TypeVal → Option RegArg
  | .cls c => some (.cls c)
  | .union args => (args.mapM id).map RegArg.union
  | _ => none

/-- The first argument of `register`. -/
inductive RegFirst (ι : Type) where
  /-- A class or a union, or anything else that is not usable as a function. -/
  | val (t : TypeVal)
  /-- A function: `__annotate__` is absent or `None` when `hints` is `none`; otherwise `hints` is what
  `get_type_hints(func, format=Format.FORWARDREF)` gives, in order, and may raise. `f` is the function. -/
  | func (f : ι) (hints : Option (Py (List (String × TypeVal))))

/-- What `register` returns. -/
inductive Registered (ι : Type) where
  | func (f : ι)
  /-- `lambda f: register(cls, f)`. -/
  | decorator (arg : RegArg)

/-- `register(cls, func=None)`, Lib/functools.py:922-976. `next(iter(...))` on no hints is a bare
`StopIteration`. The first hint is taken whatever its name is, so `'return'` and a later parameter count. -/
def register {ι : Type} (W : World) (abcToken : Nat) (d : Dispatcher ι) (cls : RegFirst ι)
    (func : Option ι) : Py (Registered ι × Dispatcher ι) :=
  let store (arg : RegArg) (f : ι) : Py (Registered ι × Dispatcher ι) :=
    .ok (.func f, regStore W abcToken d arg f)
  match cls with
  | .val t =>
    match validType t with
    | some arg =>
      match func with
      | none => .ok (.decorator arg, d)
      | some f => store arg f
    | none =>
      match func with
      | some _ => .error (.typeError "~Invalid first argument to `register()`. is not a class or union type.")
      | none =>
        .error (.typeError "~Invalid first argument to `register()`: Use either `@register(some_class)`")
  | .func f hints =>
    match func with
    | some _ => .error (.typeError "~Invalid first argument to `register()`. is not a class or union type.")
    | none =>
      match hints with
      | none =>
        .error (.typeError "~Invalid first argument to `register()`: Use either `@register(some_class)`")
      | some h =>
        match h with
        | .error e => .error e
        | .ok [] => .error .stopIteration
        | .ok ((_, t) :: _) =>
          match validType t with
          | some arg => store arg f
          | none =>
            match t with
            | .union _ => .error (.typeError "~Invalid annotation: not all arguments are classes.")
            | .forwardRef => .error (.typeError "~Invalid annotation: is an unresolved forward reference.")
            | _ => .error (.typeError "~Invalid annotation: is not a class.")

/-- The token check at the top of `dispatch`, Lib/functools.py:901-905. -/
def tokenSync {ι : Type} (abcToken : Nat) (d : Dispatcher ι) : Dispatcher ι :=
  match d.token with
  | some t => if t ≠ abcToken then { d with cache := [], token := some abcToken } else d
  | none => d

/-- The cache lookup of `dispatch`, Lib/functools.py:906-913. -/
def dispatchCached {ι : Type} (W : World) (fuel : Nat) (d : Dispatcher ι) (cls : Cls) :
    Py (Option ι) × Dispatcher ι :=
  match d.cache.lookup cls with
  | some i => (.ok i, d)
  | none =>
    match d.registry.lookup cls with
    | some i => (.ok (some i), { d with cache := (cls, some i) :: d.cache })
    | none =>
      match findImpl W fuel cls d.registry with
      | .error e => (.error e, d)
      | .ok i => (.ok i, { d with cache := (cls, i) :: d.cache })

/-- `dispatch(cls)`, Lib/functools.py:893-914. `abcToken` is `get_cache_token()`. -/
def dispatch {ι : Type} (W : World) (fuel abcToken : Nat) (d : Dispatcher ι) (cls : Cls) :
    Py (Option ι) × Dispatcher ι :=
  dispatchCached W fuel (tokenSync abcToken d) cls

/-- The `wrapper` of `singledispatch`, Lib/functools.py:978-982: the class of the first positional argument
selects the implementation, and no positional argument is a `TypeError`. -/
def dispatchCall {ι : Type} (W : World) (fuel abcToken : Nat) (d : Dispatcher ι)
    (firstArg : Option Cls) : Py (Option ι) × Dispatcher ι :=
  match firstArg with
  | none => (.error (.typeError s!"{d.name} requires at least 1 positional argument"), d)
  | some c => dispatch W fuel abcToken d c

/-- `singledispatch(func)`, Lib/functools.py:984-985: `funcname` from `getattr(func, '__name__', ...)`, which
may raise, and `registry[object] = func`. -/
def newDispatcher {ι : Type} (object : Cls) (func : ι) : Dispatcher ι :=
  { registry := [(object, func)], cache := [], token := none }

def singledispatch {ι : Type} (object : Cls) (func : ι) (nameAttr : Py (Option String)) : Py (Dispatcher ι) :=
  match nameAttr with
  | .error e => .error e
  | .ok n => .ok ⟨[(object, func)], [], none, n.getD "singledispatch function"⟩

end PyLean.CoreLibs.Functools
