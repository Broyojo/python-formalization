import PyLean.CoreLibs.EnumDC.Model

/-!
`Lib/dataclasses.py` (CPython 3.14.7): `_get_field`, `_process_class` up to the point where methods are generated, what the
generated `__init__`, `__eq__`, the ordering methods and the frozen `__setattr__` do, `replace`, `asdict`, `astuple` and
the checks of `make_dataclass`. Values of fields are `int`s, except in `asdict` and `astuple`, which have a tree of their
own. String annotations (`_is_type`), `__slots__` beyond its checks, `__doc__` and `__annotate__` are not mirrored.
-/

namespace PyLean.CoreLibs.EnumDC

open PyLean

/-- `_field_type`. -/
inductive FKind where
  | plain
  | classVar
  | initVar
  deriving Repr, DecidableEq, Inhabited

/-- A `Field`. -/
structure DField where
  name : String := ""
  kind : FKind := .plain
  /-- `default`, with `none` for `MISSING`. -/
  dflt : Option Int := none
  /-- `f.default.__class__.__hash__ is None`. -/
  unhash : Bool := false
  /-- `default_factory`, by the value it returns. -/
  factory : Option Int := none
  init : Bool := true
  repr : Bool := true
  hash : Option Bool := none
  compare : Bool := true
  /-- `kw_only`, with `none` for `MISSING`. -/
  kwOnly : Option Bool := none
  deriving Repr, DecidableEq, Inhabited

/-- `field(...)`, Lib/dataclasses.py:409-412. -/
def mkField (f : DField) : Py DField :=
  if f.dflt.isSome && f.factory.isSome then .error (.valueError "cannot specify both default and default_factory")
  else .ok f

/-- `getattr(cls, name, MISSING)`, as `_get_field` reads it. -/
inductive ClsAttr where
  | missing
  /-- A `member_descriptor`: a field in `__slots__`. -/
  | slot
  | value (v : Int) (unhash : Bool)
  | field (f : DField)
  deriving Repr, DecidableEq, Inhabited

/-- `_get_field`, Lib/dataclasses.py:825-920. `k` is what `_is_classvar` and `_is_initvar` decide. -/
def getField (attr : ClsAttr) (name : String) (k : FKind) (defaultKw : Bool) : Py DField :=
  let f0 : DField := match attr with
    | .field f => f
    | .value v u => { dflt := some v, unhash := u }
    | _ => {}
  let f : DField := { f0 with name := name, kind := k }
  if k != .plain && f.factory.isSome then .error (.typeError s!"field {name} cannot have a default factory")
  else if k == .classVar && f.kwOnly.isSome then
    .error (.typeError s!"field {name} is a ClassVar but specifies kw_only")
  else
    let f' : DField := if k != .classVar && f.kwOnly.isNone then { f with kwOnly := some defaultKw } else f
    if k == .plain && f'.dflt.isSome && f'.unhash then
      .error (.valueError s!"~mutable default for field {name} is not allowed: use default_factory")
    else .ok f'

/-- One annotation of the class. -/
inductive AnnKind where
  /-- `_: KW_ONLY`. -/
  | kwMarker
  | field (k : FKind)
  deriving Repr, DecidableEq, Inhabited

structure Ann where
  name : String
  kind : AnnKind
  attr : ClsAttr
  deriving Repr, DecidableEq, Inhabited

/-- The loop over `cls_annotations`, Lib/dataclasses.py:1051-1066. -/
def scanAnns : List Ann → Bool → Bool → Py (List DField)
  | [], _, _ => .ok []
  | a :: r, kw, seen =>
    match a.kind with
    | .kwMarker =>
      if seen then .error (.typeError s!"'{a.name}' is KW_ONLY, but KW_ONLY has already been specified")
      else scanAnns r true true
    | .field k =>
      match getField a.attr a.name k kw with
      | .error e => .error e
      | .ok f =>
        match scanAnns r kw seen with
        | .error e => .error e
        | .ok l => .ok (f :: l)

/-- `fields[f.name] = f`: a name keeps its place. -/
def fieldsPut (m : List DField) (f : DField) : List DField :=
  if m.any (fun x => x.name == f.name) then m.map (fun x => if x.name == f.name then f else x) else m ++ [f]

structure DParams where
  init : Bool := true
  repr : Bool := true
  eq : Bool := true
  order : Bool := false
  unsafeHash : Bool := false
  frozen : Bool := false
  matchArgs : Bool := true
  kwOnly : Bool := false
  slots : Bool := false
  weakrefSlot : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- What the class defines itself, read from `cls.__dict__`. -/
structure DClass where
  name : String := "C"
  params : DParams := {}
  /-- The dataclass bases in reversed MRO order, with their fields and `frozen`. -/
  bases : List (List DField × Bool) := []
  anns : List Ann := []
  /-- A `Field` in the class that has no annotation. -/
  stray : Option String := none
  /-- `__hash__` in `cls.__dict__`: `none` if absent, `some false` for `None`, and `some true` for a function. -/
  hashAttr : Option Bool := none
  /-- Names in `cls.__dict__`. -/
  defined : List String := []
  /-- `__slots__` in `cls.__dict__`. -/
  hasSlots : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- The frozen state of the bases, Lib/dataclasses.py:1013-1030: `any_frozen_base` and `all_frozen_bases`. -/
def anyFrozen (bases : List (List DField × Bool)) : Bool := bases.any (·.2)
def allFrozen (bases : List (List DField × Bool)) : Bool := bases.all (·.2)

/-- `_init_fn`'s check, Lib/dataclasses.py:680-688. -/
def initCheck : Option String → List DField → Py Unit
  | _, [] => .ok ()
  | seen, f :: r =>
    if f.init then
      if f.dflt.isSome || f.factory.isSome then initCheck (some f.name) r
      else
        match seen with
        | some s => .error (.typeError s!"non-default argument '{f.name}' follows default argument '{s}'")
        | none => initCheck none r
    else initCheck seen r

/-- `_fields_in_init_order`, Lib/dataclasses.py:415-421, on real and pseudo-fields. -/
def initFields (fs : List DField) : List DField × List DField :=
  (fs.filter (fun f => f.init && f.kwOnly != some true), fs.filter (fun f => f.init && f.kwOnly == some true))

/-- The methods `_process_class` generates, in the order of `add_fn`. The second part is `overwrite_error`. -/
def methodNames (p : DParams) : List (String × Option String) :=
  (if p.init then [("__init__", none)] else []) ++
  (if p.repr then [("__repr__", none)] else []) ++
  (if p.eq then [("__eq__", none)] else []) ++
  (if p.order then
    [("__lt__", some " Consider using functools.total_ordering"), ("__le__", some " Consider using functools.total_ordering"),
     ("__gt__", some " Consider using functools.total_ordering"), ("__ge__", some " Consider using functools.total_ordering")]
   else []) ++
  (if p.frozen then [("__setattr__", some ""), ("__delattr__", some "")] else [])

/-- `add_fns_to_class`, Lib/dataclasses.py:510-533, by way of `_set_new_attribute`, :922-928: an existing attribute is kept,
and is an error for a method with an `overwrite_error`. The result is the methods that went in. -/
def addFns (cls : String) (defined : List String) : List (String × Option String) → Py (List String)
  | [] => .ok []
  | (n, e) :: r =>
    if defined.contains n then
      match e with
      | some extra => .error (.typeError s!"Cannot overwrite attribute {n} in class {cls}{extra}")
      | none => addFns cls defined r
    else
      match addFns cls defined r with
      | .error e => .error e
      | .ok l => .ok (n :: l)

/-- A class after `_process_class`. -/
structure DInfo where
  params : DParams
  fields : List DField
  std : List DField
  kw : List DField
  generated : List String
  hash : HashAction
  matchArgs : Option (List String)
  deriving Repr, DecidableEq

/-- `field_list`: real fields only. -/
def DInfo.real (i : DInfo) : List DField := i.fields.filter (fun f => f.kind == .plain)

/-- `has_explicit_hash`, Lib/dataclasses.py:1113-1115. -/
def explicitHash (c : DClass) : Bool :=
  match c.hashAttr with
  | none => false
  | some true => true
  | some false => !c.defined.contains "__eq__"

/-- The fields of the bases and of the class, Lib/dataclasses.py:1018-1069. -/
def allFields (c : DClass) (own : List DField) : List DField :=
  own.foldl fieldsPut (c.bases.foldl (fun m b => b.1.foldl fieldsPut m) [])

/-- `_process_class`, Lib/dataclasses.py:986-1243, in the order of its failures. -/
def processClass (c : DClass) : Py DInfo :=
  match scanAnns c.anns c.params.kwOnly false with
  | .error e => .error e
  | .ok own =>
    let p := c.params
    let fields := allFields c own
    match c.stray with
    | some n => .error (.typeError s!"'{n}' is a field but has no type annotation")
    | none =>
    if !c.bases.isEmpty && anyFrozen c.bases && !p.frozen then
      .error (.typeError "cannot inherit non-frozen dataclass from a frozen one")
    else if !c.bases.isEmpty && !allFrozen c.bases && p.frozen then
      .error (.typeError "cannot inherit frozen dataclass from a non-frozen one")
    else if p.order && !p.eq then .error (.valueError "eq must be true if order is true")
    else
      let all := fields.filter (fun f => f.kind != .classVar)
      let (std, kw) := initFields all
      match (if p.init then initCheck none std else .ok ()) with
      | .error e => .error e
      | .ok () =>
        let action := hashAction p.unsafeHash p.eq p.frozen (explicitHash c)
        if action == .exception then .error (.typeError s!"Cannot overwrite attribute __hash__ in class {c.name}")
        else
          match addFns c.name c.defined (methodNames p) with
          | .error e => .error e
          | .ok gen =>
            if p.weakrefSlot && !p.slots then .error (.typeError "weakref_slot is True but slots is False")
            else if p.slots && c.hasSlots then .error (.typeError s!"{c.name} already specifies __slots__")
            else .ok { params := p, fields := fields, std := std, kw := kw, generated := gen, hash := action,
                       matchArgs := if p.matchArgs && !c.defined.contains "__match_args__"
                         then some (std.map (·.name)) else none }

/-! ### The generated `__init__` -/

/-- The parameters of `__init__` bound by the interpreter. All its failures are `TypeError`. -/
def bindArgs (std kw : List DField) (args : List Int) (kwargs : List (String × Int)) :
    Py (List (String × Int)) :=
  if args.length > std.length then .error (.typeError "~takes positional arguments but more were given")
  else
    let names := (std ++ kw).map (·.name)
    let given := (std.take args.length).map (·.name)
    if kwargs.any (fun p => !names.contains p.1) then .error (.typeError "~got an unexpected keyword argument")
    else if kwargs.any (fun p => given.contains p.1) then .error (.typeError "~got multiple values for argument")
    else
      let bound := given.zip args ++ kwargs
      if (std ++ kw).any (fun f => f.dflt.isNone && f.factory.isNone && (bound.lookup f.name).isNone) then
        .error (.typeError "~missing required argument")
      else .ok bound

/-- The value `_field_init`, Lib/dataclasses.py:591-648, gives a field, or `none` where it assigns nothing. -/
def fieldValue (slots : Bool) (bound : List (String × Int)) (f : DField) : Option Int :=
  match f.factory with
  | some n => if f.init then some ((bound.lookup f.name).getD n) else some n
  | none =>
    if f.init then
      match f.dflt with
      | none => bound.lookup f.name
      | some d => some ((bound.lookup f.name).getD d)
    else if slots then f.dflt
    else none

/-- An instance: its attributes, and what `__post_init__` was called with. -/
structure DObj where
  attrs : List (String × Int) := []
  post : Option (List Int) := none
  deriving Repr, DecidableEq, Inhabited

/-- The body of `__init__`, Lib/dataclasses.py:696-707. An `InitVar` is not assigned. -/
def initBody (i : DInfo) (hasPost : Bool) (bound : List (String × Int)) : DObj :=
  let all := i.fields.filter (fun f => f.kind != .classVar)
  { attrs := (all.filter (fun f => f.kind == .plain)).filterMap (fun f =>
      (fieldValue i.params.slots bound f).map (fun v => (f.name, v)))
    post := if hasPost then some ((all.filter (fun f => f.kind == .initVar)).filterMap
      (fun f => fieldValue i.params.slots bound f)) else none }

/-- `C(*args, **kwargs)`. The call of `__post_init__` at Lib/dataclasses.py:705-707 names every `InitVar`, and one with
`init=False` is not a parameter of `__init__`, so it is a `NameError` when the instance is made. -/
def callInit (i : DInfo) (hasPost : Bool) (args : List Int) (kwargs : List (String × Int)) : Py DObj :=
  match bindArgs i.std i.kw args kwargs with
  | .error e => .error e
  | .ok bound =>
    match i.fields.find? (fun f => f.kind == .initVar && !f.init) with
    | some f => if hasPost then .error (.named "NameError" s!"name '{f.name}' is not defined") else .ok (initBody i hasPost bound)
    | none => .ok (initBody i hasPost bound)

/-- `getattr(obj, name)`: the instance, then the default in the class. -/
def getAttrD (i : DInfo) (o : DObj) (name : String) : Py Int :=
  match o.attrs.lookup name with
  | some v => .ok v
  | none =>
    if i.params.slots && i.real.any (fun f => f.name == name) then .error (.named "AttributeError" ("~" ++ name))
    else
      match (i.fields.find? (fun f => f.name == name)).bind DField.dflt with
      | some v => .ok v
      | none => .error (.named "AttributeError" ("~" ++ name))

/-- The loop of `_replace`, Lib/dataclasses.py:1789-1806. -/
def replaceLoop (i : DInfo) (o : DObj) : List DField → List (String × Int) → Py (List (String × Int))
  | [], ch => .ok ch
  | f :: r, ch =>
    if f.kind == .classVar then replaceLoop i o r ch
    else if !f.init then
      if (ch.lookup f.name).isSome then
        .error (.typeError s!"field {f.name} is declared with init=False, it cannot be specified with replace()")
      else replaceLoop i o r ch
    else if (ch.lookup f.name).isNone then
      if f.kind == .initVar && f.dflt.isNone then
        .error (.typeError s!"InitVar '{f.name}' must be specified with replace()")
      else
        match getAttrD i o f.name with
        | .error e => .error e
        | .ok v => replaceLoop i o r (ch ++ [(f.name, v)])
    else replaceLoop i o r ch

/-- `replace(obj, **changes)`, Lib/dataclasses.py:1763-1813. -/
def dcReplace (i : DInfo) (hasPost : Bool) (o : DObj) (changes : List (String × Int)) : Py DObj :=
  match replaceLoop i o i.fields changes with
  | .error e => .error e
  | .ok kw => callInit i hasPost [] kw

/-! ### `__eq__`, the ordering methods, `__hash__`, frozen -/

/-- `a and b and c`, Lib/dataclasses.py:1171: the first falsy result, or the last, lazily. `terms` hold each `==` as a
result and its truth; `terms` being empty is the `True` of the source, here `whenEmpty`. -/
def andChain {α : Type} (whenEmpty : α) : List (Py (α × Bool)) → Py α
  | [] => .ok whenEmpty
  | [t] =>
    match t with
    | .error e => .error e
    | .ok (x, _) => .ok x
  | t :: r =>
    match t with
    | .error e => .error e
    | .ok (x, b) => if b then andChain whenEmpty r else .ok x

/-- The generated `__eq__`, Lib/dataclasses.py:1172-1178. The outer `none` is `NotImplemented`. `yes` is `True`. -/
def dcEq {α : Type} (yes : α) (isSame sameClass : Bool) (terms : List (Py (α × Bool))) : Option (Py α) :=
  if isSame then some (.ok yes)
  else if sameClass then some (andChain yes terms)
  else none

/-- Lists of `int`s compared as tuples are. -/
def tupLt : List Int → List Int → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: r, b :: s => if a == b then tupLt r s else decide (a < b)

/-- The generated `__lt__`, `__le__`, `__gt__`, `__ge__`, Lib/dataclasses.py:1185-1199: the values of the fields with
`compare`, as tuples. `none` is `NotImplemented`. -/
def dcOrder (op : String) (sameClass : Bool) (a b : List Int) : Option Bool :=
  if !sameClass then none
  else
    some (match op with
      | "lt" => tupLt a b
      | "le" => tupLt a b || a == b
      | "gt" => tupLt b a
      | _ => tupLt b a || a == b)

/-- `_hash_add`, Lib/dataclasses.py:943-949: the fields of `hash(...)`. -/
def hashFields (fs : List DField) : List DField :=
  fs.filter (fun f => match f.hash with
    | none => f.compare
    | some h => h)

/-- `_frozen_set_del_attr`, Lib/dataclasses.py:728-748: `exact` is `type(self) is __class__`. -/
def frozenSet (exact : Bool) (fields : List String) (name : String) : Py Unit :=
  if exact || fields.contains name then .error (.named "FrozenInstanceError" s!"cannot assign to field '{name}'")
  else .ok ()

def frozenDel (exact : Bool) (fields : List String) (name : String) : Py Unit :=
  if exact || fields.contains name then .error (.named "FrozenInstanceError" s!"cannot delete field '{name}'")
  else .ok ()

/-! ### `make_dataclass` -/

/-- An item of `fields`. -/
inductive MakeItem where
  | name (s : String)
  /-- `(name, type)` or `(name, type, Field)`. -/
  | named (s : String)
  /-- A name that is not a `str`. -/
  | notStr
  /-- An item of another length. -/
  | bad
  deriving Repr, DecidableEq, Inhabited

/-- `str.isidentifier`, for ASCII. -/
def isIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: r => (c.isAlpha || c == '_') && r.all (fun x => x.isAlphanum || x == '_')

/-- `keyword.kwlist`, Lib/keyword.py. -/
def kwList : List String :=
  ["False", "None", "True", "and", "as", "assert", "async", "await", "break", "class", "continue", "def", "del",
   "elif", "else", "except", "finally", "for", "from", "global", "if", "import", "in", "is", "lambda", "nonlocal",
   "not", "or", "pass", "raise", "return", "try", "while", "with", "yield"]

/-- The loop of `make_dataclass`, Lib/dataclasses.py:1674-1694. -/
def makeNames : List MakeItem → List String → Py (List String)
  | [], seen => .ok seen
  | it :: r, seen =>
    let check (n : String) : Py (List String) :=
      if !isIdent n then .error (.typeError s!"Field names must be valid identifiers: '{n}'")
      else if kwList.contains n then .error (.typeError s!"Field names must not be keywords: '{n}'")
      else if seen.contains n then .error (.typeError s!"Field name duplicated: '{n}'")
      else makeNames r (seen ++ [n])
    match it with
    | .name n => check n
    | .named n => check n
    | .notStr => .error (.typeError "~Field names must be valid identifiers")
    | .bad => .error (.typeError "~Invalid field")

/-! ### `asdict` and `astuple` -/

/-- A value of a field, as `asdict` and `astuple` see it. -/
inductive DV where
  | atom (n : Int)
  | str (s : String)
  /-- An object for `copy.deepcopy`, hashable. -/
  | copied (n : Int)
  /-- The same, not hashable. -/
  | unhash (n : Int)
  | list (l : List DV)
  | tuple (l : List DV)
  | dict (ks vs : List DV)
  /-- A dataclass instance, frozen when it is a key. -/
  | inst (names : List String) (vals : List DV)
  /-- A `namedtuple`. -/
  | named (l : List DV)
  /-- A subclass of `list`, of `tuple`, of `dict`, without `default_factory`. -/
  | listSub (l : List DV)
  | tupleSub (l : List DV)
  | dictSub (ks vs : List DV)
  | defaultDict (ks vs : List DV)
  | counter (ks vs : List DV)
  deriving Repr, BEq, Inhabited

mutual
  /-- `hash(v)` does not raise. -/
  def DV.hashable : DV → Bool
    | .atom _ | .str _ | .copied _ => true
    | .tuple l | .named l | .tupleSub l => DV.allHashable l
    | .inst _ vals => DV.allHashable vals
    | _ => false

  def DV.allHashable : List DV → Bool
    | [] => true
    | v :: r => v.hashable && DV.allHashable r
end

/-- `d[k] = v`, keeping the first place of a key. -/
def dvPut (m : List (DV × DV)) (k v : DV) : List (DV × DV) :=
  if m.any (fun p => p.1 == k) then m.map (fun p => if p.1 == k then (p.1, v) else p) else m ++ [(k, v)]

/-- A `dict` from pairs: a key that is not hashable is a `TypeError`, as Lib/dataclasses.py:1528 meets it. -/
def dvPairs (ks vs : List DV) : Py (List (DV × DV)) :=
  if ks.all DV.hashable then .ok ((ks.zip vs).foldl (fun m p => dvPut m p.1 p.2) [])
  else .error (.typeError "~unhashable type")

/-- `Counter(pairs)`: the pairs are the elements, so each is a key, with a count. -/
def dvCounter (ks vs : List DV) : Py DV :=
  let els := (ks.zip vs).map (fun p => DV.tuple [p.1, p.2])
  if els.all DV.hashable then
    let m := els.foldl (fun (m : List (DV × Int)) e =>
      if m.any (fun p => p.1 == e) then m.map (fun p => if p.1 == e then (p.1, p.2 + 1) else p) else m ++ [(e, 1)]) []
    .ok (.counter (m.map Prod.fst) (m.map (fun p => DV.atom p.2)))
  else .error (.typeError "~unhashable type")

/-- `dict_factory`. -/
inductive DictFact where
  /-- The builtin: the fast path. -/
  | dict
  /-- `lambda p: dict(p)`. -/
  | dictLike
  /-- `list`. -/
  | list
  deriving Repr, DecidableEq, Inhabited

def wrapDict (mk : List DV → List DV → DV) (r : Py (List (DV × DV))) : Py DV :=
  match r with
  | .error e => .error e
  | .ok m => .ok (mk (m.map Prod.fst) (m.map Prod.snd))

mutual
  /-- `_asdict_inner`, Lib/dataclasses.py:1508-1573. -/
  def asdictV (fact : DictFact) : DV → Py DV
    | .atom n => .ok (.atom n)
    | .str s => .ok (.str s)
    | .inst names vals =>
      match asdictL fact vals with
      | .error e => .error e
      | .ok r =>
        let ks := names.map DV.str
        match fact with
        | .dict | .dictLike => .ok (.dict ks r)
        | .list => .ok (.list ((ks.zip r).map (fun p => DV.tuple [p.1, p.2])))
    | .list l =>
      match asdictL fact l with
      | .error e => .error e
      | .ok r => .ok (.list r)
    | .dict ks vs =>
      match asdictL fact ks, asdictL fact vs with
      | .ok k, .ok v => wrapDict .dict (dvPairs k v)
      | .error e, _ => .error e
      | _, .error e => .error e
    | .tuple l =>
      match asdictL fact l with
      | .error e => .error e
      | .ok r => .ok (.tuple r)
    | .named l =>
      match asdictL fact l with
      | .error e => .error e
      | .ok r => .ok (.named r)
    | .tupleSub l =>
      match asdictL fact l with
      | .error e => .error e
      | .ok r => .ok (.tupleSub r)
    | .defaultDict ks vs =>
      match asdictL fact ks, asdictL fact vs with
      | .ok k, .ok v => wrapDict .defaultDict (dvPairs k v)
      | .error e, _ => .error e
      | _, .error e => .error e
    | .dictSub ks vs =>
      match asdictL fact ks, asdictL fact vs with
      | .ok k, .ok v => wrapDict .dictSub (dvPairs k v)
      | .error e, _ => .error e
      | _, .error e => .error e
    | .counter ks vs =>
      match asdictL fact ks, asdictL fact vs with
      | .ok k, .ok v => dvCounter k v
      | .error e, _ => .error e
      | _, .error e => .error e
    | .listSub l =>
      match asdictL fact l with
      | .error e => .error e
      | .ok r => .ok (.listSub r)
    | .copied n => .ok (.copied n)
    | .unhash n => .ok (.unhash n)

  def asdictL (fact : DictFact) : List DV → Py (List DV)
    | [] => .ok []
    | v :: r =>
      match asdictV fact v with
      | .error e => .error e
      | .ok x =>
        match asdictL fact r with
        | .error e => .error e
        | .ok l => .ok (x :: l)
end

/-- `tuple_factory`. -/
inductive TupFact where
  | tuple
  | list
  deriving Repr, DecidableEq, Inhabited

mutual
  /-- `_astuple_inner`, Lib/dataclasses.py:1600-1633. -/
  def astupleV (fact : TupFact) : DV → Py DV
    | .atom n => .ok (.atom n)
    | .str s => .ok (.str s)
    | .inst _ vals =>
      match astupleL fact vals with
      | .error e => .error e
      | .ok r =>
        match fact with
        | .tuple => .ok (.tuple r)
        | .list => .ok (.list r)
    | .named l =>
      match astupleL fact l with
      | .error e => .error e
      | .ok r => .ok (.named r)
    | .list l =>
      match astupleL fact l with
      | .error e => .error e
      | .ok r => .ok (.list r)
    | .tuple l =>
      match astupleL fact l with
      | .error e => .error e
      | .ok r => .ok (.tuple r)
    | .listSub l =>
      match astupleL fact l with
      | .error e => .error e
      | .ok r => .ok (.listSub r)
    | .tupleSub l =>
      match astupleL fact l with
      | .error e => .error e
      | .ok r => .ok (.tupleSub r)
    | .defaultDict ks vs =>
      match astupleL fact ks, astupleL fact vs with
      | .ok k, .ok v => wrapDict .defaultDict (dvPairs k v)
      | .error e, _ => .error e
      | _, .error e => .error e
    | .dict ks vs =>
      match astupleL fact ks, astupleL fact vs with
      | .ok k, .ok v => wrapDict .dict (dvPairs k v)
      | .error e, _ => .error e
      | _, .error e => .error e
    | .dictSub ks vs =>
      match astupleL fact ks, astupleL fact vs with
      | .ok k, .ok v => wrapDict .dictSub (dvPairs k v)
      | .error e, _ => .error e
      | _, .error e => .error e
    | .counter ks vs =>
      match astupleL fact ks, astupleL fact vs with
      | .ok k, .ok v => dvCounter k v
      | .error e, _ => .error e
      | _, .error e => .error e
    | .copied n => .ok (.copied n)
    | .unhash n => .ok (.unhash n)

  def astupleL (fact : TupFact) : List DV → Py (List DV)
    | [] => .ok []
    | v :: r =>
      match astupleV fact v with
      | .error e => .error e
      | .ok x =>
        match astupleL fact r with
        | .error e => .error e
        | .ok l => .ok (x :: l)
end

end PyLean.CoreLibs.EnumDC
