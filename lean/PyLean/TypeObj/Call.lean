import PyLean.TypeObj.Reduce
import PyLean.LongObj.FromString

/-!
Calling: function argument binding (`initialize_locals`, `Python/ceval.c:1738`), `tp_new`
and `tp_init` of the builtin types, `object_new`/`object_init`, `type_call`, the slot
wrappers of `Objects/typeobject.c:9956-10510`, `tp_new_wrapper`, bound methods, builtin
functions and the `PyGetSetDef` tables. `pyCall` at the end is `PyObject_Call`.
-/

namespace PyLean.TypeObj

/-! ## Argument binding -/

/-- The locals of a call: one optional value per parameter, the `*args` values, and the
`**kwargs` items. -/
structure Bound where
  slots : List (Option Val)
  varargs : List Val
  kwdict : NameDict
  deriving Repr, Inhabited

/-- Parameter names, positional and keyword-only: `co_varnames[:total_args]`. -/
def FuncData.paramNames (f : FuncData) : List Name := f.varnames.take (f.argcount + f.kwonly)

/-- Index of `n` in `names`, from `start`: the keyword search at `Python/ceval.c:1822`. -/
def findParam (names : List Name) (start : Nat) (n : Name) : Option Nat :=
  ((names.drop start).findIdx? (· == n)).map (· + start)

/-- `format_missing`, `Python/ceval.c:1514`. -/
def formatMissing (kind qualname : String) (names : List String) : String :=
  let nameStr := match names with
    | [a] => a
    | [a, b] => s!"{a} and {b}"
    | _ =>
      let n := names.length
      let tail := s!", {names[n - 2]!}, and {names[n - 1]!}"
      ", ".intercalate (names.take (n - 2)) ++ tail
  s!"{qualname}() missing {names.length} required {kind} argument{if names.length == 1 then "" else "s"}: {nameStr}"

/-- `missing_arguments`, `Python/ceval.c:1577`. `defcount = none` is keyword-only. -/
def missingArguments (f : FuncData) (slots : List (Option Val)) (defcount : Option Nat) : String :=
  let (kind, start, stop) := match defcount with
    | some d => ("positional", 0, f.argcount - d)
    | none => ("keyword-only", f.argcount, f.argcount + f.kwonly)
  let idx := (List.range (stop - start)).map (· + start)
  let miss := idx.filter fun i => (slots.getD i none).isNone
  formatMissing kind f.qualname (miss.map fun i => reprStr (f.varnames.getD i ""))

/-- `atleast`, `Python/ceval.c:1635`. -/
def tooManyAtLeast (f : FuncData) : Int := (f.argcount : Int) - f.defaults.length

/-- `too_many_positional`, `Python/ceval.c:1616`. -/
def tooManyPositional (f : FuncData) (givenN : Nat) (slots : List (Option Val)) : String :=
  let kwonlyGiven := ((slots.drop f.argcount).filter Option.isSome).length
  let defcount := f.defaults.length
  let (plural, sig) :=
    if defcount != 0 then (true, s!"from {tooManyAtLeast f} to {f.argcount}")
    else (f.argcount != 1, toString f.argcount)
  let kwonlySig :=
    if kwonlyGiven != 0 then
      s!" positional argument{if givenN != 1 then "s" else ""} (and {kwonlyGiven} keyword-only argument{if kwonlyGiven != 1 then "s" else ""})"
    else ""
  s!"{f.qualname}() takes {sig} positional argument{if plural then "s" else ""} but {givenN}{kwonlySig} {if givenN == 1 && kwonlyGiven == 0 then "was" else "were"} given"

/-- `positional_only_passed_as_keyword`, `Python/ceval.c:1674`. -/
def posonlyConflicts (f : FuncData) (kw : Kw) : List Name :=
  (f.varnames.take f.posonly).flatMap fun p => (kw.filter (·.1 == p)).map (·.1)

/-- Handle one keyword, `Python/ceval.c:1806-1902`. -/
def bindKeyword (f : FuncData) (allKw : Kw) (b : Bound) (kv : Name × Val) : Except String Bound :=
  let (keyword, value) := kv
  let total := f.argcount + f.kwonly
  match findParam (f.varnames.take total) f.posonly keyword with
  | some j =>
    if (b.slots.getD j none).isSome then
      .error s!"{f.qualname}() got multiple values for argument '{keyword}'"
    else .ok { b with slots := b.slots.set j (some value) }
  | none =>
    if f.hasVarkw then .ok { b with kwdict := NameDict.set b.kwdict keyword value }
    else if f.posonly != 0 && !(posonlyConflicts f allKw).isEmpty then
      .error s!"{f.qualname}() got some positional-only arguments passed as keyword arguments: '{", ".intercalate (posonlyConflicts f allKw)}'"
    else .error s!"{f.qualname}() got an unexpected keyword argument '{keyword}'"

/-- The `for` loop over keywords, `Python/ceval.c:1806`. -/
def bindKeywords (f : FuncData) (allKw : Kw) : Bound → Kw → Except String Bound
  | b, [] => .ok b
  | b, kv :: rest =>
    match bindKeyword f allKw b kv with
    | .ok b' => bindKeywords f allKw b' rest
    | .error e => .error e

/-- Fill defaults for positional parameters, `Python/ceval.c:1913-1940`. `m` is a signed
`Py_ssize_t`: assigning `__defaults__` can make it negative. -/
def fillDefaults (f : FuncData) (argc : Nat) (n : Nat) (b : Bound) : Except String Bound :=
  if argc < f.argcount then
    let defcount := f.defaults.length
    let m : Int := (f.argcount : Int) - defcount
    let missing := ((List.range (m.toNat - argc)).map (· + argc)).filter fun i =>
      (b.slots.getD i none).isNone
    if !missing.isEmpty then .error (missingArguments f b.slots (some defcount))
    else
      let start : Nat := if (n : Int) > m then ((n : Int) - m).toNat else 0
      let idx := (List.range (defcount - start)).map (· + start)
      let slots := idx.foldl (fun s (i : Nat) =>
        let k := (m + (i : Int)).toNat
        if (s.getD k none).isNone then s.set k (f.defaults[i]?) else s) b.slots
      .ok { b with slots := slots }
  else .ok b

/-- `PyDict_GetItemRef(func_kwdefaults, name)`: a `str` key in a dict that can hold anything, so
a key of the same hash runs its `__eq__`. -/
def kwdefaultLookup (rt : Rt) (d : Val) (name : Name) : M (Option Val) := do
  match d with
  | .obj a =>
    match ← dictProbe rt a (.str name) (strHash name) iterFuel 0 with
    | some i =>
      let w ← getW
      pure (((dictEntries w a)[i]?).map (·.2))
    | none => pure none
  | _ => gap%

/-- The loop of `Python/ceval.c:1943-1966`, over the keyword-only parameters. -/
def fillKwLoop (rt : Rt) (f : FuncData) : List Nat → List (Option Val) → M (List (Option Val))
  | [], s => pure s
  | i :: is, s => do
    if (s.getD i none).isSome then return ← fillKwLoop rt f is s
    match f.kwdefaultsObj with
    | none => fillKwLoop rt f is s
    | some d =>
      match ← kwdefaultLookup rt d (f.varnames.getD i "") with
      | some v => fillKwLoop rt f is (s.set i (some v))
      | none => fillKwLoop rt f is s

/-- Fill keyword-only defaults, `Python/ceval.c:1943-1966`. -/
def fillKwdefaults (rt : Rt) (f : FuncData) (b : Bound) : M Bound := do
  if f.kwonly > 0 then
    let idx := (List.range f.kwonly).map (· + f.argcount)
    let slots ← fillKwLoop rt f idx b.slots
    if idx.any fun i => (slots.getD i none).isNone then
      typeErr (missingArguments f slots none)
    pure { b with slots := slots }
  else pure b

/-- `initialize_locals`, `Python/ceval.c:1738`, up to the keyword-only defaults. The error string
is the `TypeError` message. Keyword names are strings, so the `keywords must be strings` branch
is outside this signature; a "Did you mean" suggestion (`_Py_CalculateSuggestions`) is not
modelled. -/
def bindArgs (f : FuncData) (args : List Val) (kw : Kw) : Except String Bound :=
  let total := f.argcount + f.kwonly
  let n := min args.length f.argcount
  let slots := (args.take n).map some ++ List.replicate (total - n) none
  let b0 : Bound :=
    { slots := slots, varargs := if f.hasVarargs then args.drop n else [], kwdict := [] }
  match bindKeywords f kw b0 kw with
  | .error e => .error e
  | .ok b1 =>
    if args.length > f.argcount && !f.hasVarargs then
      .error (tooManyPositional f args.length b1.slots)
    else
      fillDefaults f args.length n b1

/-- The locals handed to the code object. -/
def boundLocals (f : FuncData) (b : Bound) (kwv : Option Val) : NameDict :=
  let params := (f.varnames.take (f.argcount + f.kwonly)).zip b.slots
  let base := params.filterMap fun (n, v) => v.map (n, ·)
  let i := f.argcount + f.kwonly
  let withVar := if f.hasVarargs then base ++ [(f.varnames.getD i "", Val.tuple b.varargs)] else base
  match kwv with
  | some d =>
    withVar ++ [(f.varnames.getD (if f.hasVarargs then i + 1 else i) "", d)]
  | none => withVar

/-- `_PyFunction_Vectorcall` through the eval loop (`Objects/call.c:402`). -/
def functionCall (rt : Rt) (self : Val) (f : FuncData) (args : List Val) (kw : Kw) : M Val := do
  match bindArgs f args kw with
  | .error m => typeErr m
  | .ok b =>
    let b ← fillKwdefaults rt f b
    let kwv ←
      if f.hasVarkw then
        some <$> alloc B.dict (.dict (b.kwdict.map fun (k, v) => (Val.str k, v)))
      else pure none
    rt.exec f.code self (boundLocals f b kwv)

/-! ## `tp_new`, `tp_init` -/

/-- `excess_args`, `Objects/typeobject.c:7435`. -/
def excessArgs (args : List Val) (kw : Kw) : Bool := !args.isEmpty || !kw.isEmpty

/-- `object_init`, `Objects/typeobject.c:7442`. -/
def objectInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  let w ← getW
  let tp := typeOf w self
  if excessArgs args kw then
    if slotOf w tp .tp_init != some (.c .object) then
      typeErr "object.__init__() takes exactly one argument (the instance to initialize)"
    if slotOf w tp .tp_new == some (.c .object) then
      typeErr s!"{trunc 200 (tpName w tp)}.__init__() takes exactly one argument (the instance to initialize)"

/-- The payload `tp_alloc` gives a new instance of `t`, by its builtin ancestor. -/
def freshBody (w : World) (t : Addr) : Payload :=
  if isSubtype w t B.BaseException then .exc {}
  else if isSubtype w t B.list then .list []
  else if isSubtype w t B.dict then .dict []
  else if isSubtype w t B.property then .property .none .none .none .none none false
  else if isSubtype w t B.classmethod then .classmethod .none
  else if isSubtype w t B.staticmethod then .staticmethod .none
  else if isSubtype w t B.super then .super none none none
  else .plain

/-- Sort by code points, as `list.sort` orders exact `str` items (`unsafe_latin_compare` or
`unicode_compare`, no Python code). -/
def sortStrs (names : List String) : List String :=
  names.mergeSort fun a b => decide (strCompare a.toList b.toList ≤ 0)

/-- `PyList_Sort` of the `__abstractmethods__` items, `Objects/typeobject.c:7493`, where the model
can say what it does. Exact `str` items sort by code point; one item needs no comparison; two exact
`int`s compare by value (`unsafe_long_compare`); two items of different types make the one
comparison of `count_run` (`Objects/listobject.c:2003-2005`), `items[1] < items[0]` through
`safe_object_compare` (`PyObject_RichCompareBool`, which for `<` is `PyObject_RichCompare` and
`PyObject_IsTrue`), and are swapped when it holds. Longer mixed lists, and two non-`str` items of one
type, run `unsafe_object_compare` and the merge, which the model does not follow (`gap%`). -/
def sortAbstractItems (rt : Rt) (items : List Val) : M (List Val) := do
  let w ← getW
  let strs := items.filterMap fun x => match x with
    | .str s => some s
    | _ => none
  if strs.length == items.length then pure ((sortStrs strs).map Val.str)
  else
    match items with
    | [] | [_] => pure items
    | [.int a, .int b] => pure (if b < a then [.int b, .int a] else [.int a, .int b])
    | [a, b] =>
      if typeOf w a == typeOf w b then gap%
      else
        let r ← rt.richCompare b a .lt
        let lt ← rt.isTrue r
        pure (if lt then [b, a] else [a, b])
    | _ => gap%

/-- `PyUnicode_Join("', '", sorted)`, `Objects/typeobject.c:7502`: the first item that is not a
`str` raises, at its index in the sorted list. -/
def joinAbstract (w : World) (items : List Val) : M (List String) :=
  match items.findIdx? (fun x => (strOf w x).isNone) with
  | some i =>
    typeErr s!"sequence item {i}: expected str instance, {trunc 80 (typeName w (items.getD i .none))} found"
  | none => pure (items.filterMap (strOf w))

/-- `"', '".join(sorted(type.__abstractmethods__))` of the abstract method error,
`Objects/typeobject.c:7484-7502`: `type_abstractmethods`, `PySequence_List`, `PyList_Sort`, then
`PyUnicode_Join`. The sort runs first, so `['a', 1]` raises the `'<' not supported` `TypeError`
(checked on 3.15.2), and a join error names the index in sorted order. -/
def abstractNames (rt : Rt) (t : Addr) : M (List String) := do
  let w ← getW
  match NameDict.get? (tdata w t).dict "__abstractmethods__" with
  | none => raiseC B.AttributeError "__abstractmethods__"
  | some am =>
    let items ← pySequenceList rt am
    let sorted ← sortAbstractItems rt items
    let w ← getW
    joinAbstract w sorted

/-- `object_new`, `Objects/typeobject.c:7462`. -/
def objectNew (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  let w ← getW
  if excessArgs args kw then
    if slotOf w t .tp_new != some (.c .object) then
      typeErr "object.__new__() takes exactly one argument (the type to instantiate)"
    if slotOf w t .tp_init == some (.c .object) then
      typeErr s!"{trunc 200 (tpName w t)}() takes no arguments"
  if (tdata w t).isAbstract then
    let names ← abstractNames rt t
    let w ← getW
    typeErr s!"Can't instantiate abstract class {tpName w t} without an implementation for abstract method{if names.length > 1 then "s" else ""} '{"', '".intercalate names}'"
  alloc t (freshBody w t)

/-- `_PyArg_NoKeywords(name, kw)`. -/
def noKeywords (name : String) (kw : Kw) : M Unit :=
  unless kw.isEmpty do typeErr s!"{name}() takes no keyword arguments"

/-- `PyArg_UnpackTuple(args, name, lo, hi)`: the arity message. -/
def unpackTuple (name : String) (lo hi : Nat) (n : Nat) : M Unit := do
  if n < lo then
    if lo == hi then
      typeErr s!"{name} expected {lo} argument{if lo == 1 then "" else "s"}, got {n}"
    else typeErr s!"{name} expected at least {lo} argument{if lo == 1 then "" else "s"}, got {n}"
  if n > hi then
    if lo == hi then
      typeErr s!"{name} expected {hi} argument{if hi == 1 then "" else "s"}, got {n}"
    else typeErr s!"{name} expected at most {hi} argument{if hi == 1 then "" else "s"}, got {n}"

/-- The type name in a `PyArg_Parse` conversion error: `None` is written `None`
(`_PyArg_BadArgument`, `Python/getargs.c`). -/
def argTypeName (w : World) (v : Val) : String :=
  if v.is .none then "None" else typeName w v

/-- Allocate a subclass instance holding builtin value `v`, as `long_subtype_new` and
friends do; the exact type stays immediate. -/
def boxValue (t exact : Addr) (v : Val) : M Val :=
  if t == exact then pure v else alloc t (.boxed v)

/-- `PyLong_FromUnicodeObject`, through the mirror in `LongObj.FromString`. The limit of 4300
digits is the default; beyond 6000 digits C calls `_pylong`, which is not reached here. -/
def longFromStr (s : String) (base : Int) : M Val :=
  match PyLean.LongObj.pyLongFromUnicodeObject (fun _ => .error .modelFuel) 4300
      (s.toList.map (·.toNat)) base with
  | .ok v => pure (.int v.toInt)
  | .error (.valueError m) => valueErr (if m.startsWith "~" then (m.drop 1).toString else m)
  | .error _ => gap%

/-- `long_new_impl`, `Objects/longobject.c:5975`, through the clinic parser: `x` is positional and
`base` may be either. -/
def longNew (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  if args.length + kw.length > 2 then
    typeErr s!"int() takes at most 2 arguments ({args.length + kw.length} given)"
  for (k, _) in kw do
    if k != "base" then typeErr s!"int() got an unexpected keyword argument '{k}'"
  let x? := args.head?
  let obase : Option Val := match args, kw with
    | [_, b], _ => some b
    | _, (_, b) :: _ => some b
    | _, [] => none
  match x?, obase with
  | none, none => boxValue t B.int (.int 0)
  | none, some _ => typeErr "int() missing string argument"
  | some x, none =>
    let r ← pyNumberLong rt x
    boxValue t B.int r
  | some x, some b =>
    let base ← numberAsSsize rt b none
    if (base != 0 && base < 2) || base > 36 then
      valueErr "int() base must be >= 2 and <= 36, or 0"
    let w ← getW
    match strOf w x with
    | some s =>
      let r ← longFromStr s base
      boxValue t B.int r
    | none => typeErr "int() can't convert non-string with explicit base"

/-- `bool_new`, `Objects/boolobject.c`. -/
def boolNew (rt : Rt) (args : List Val) (kw : Kw) : M Val := do
  noKeywords "bool" kw
  unpackTuple "bool" 0 1 args.length
  match args with
  | [] => pure (.bool false)
  | x :: _ => .bool <$> rt.isTrue x

/-- `unicode_new`, `Objects/clinic/unicodeobject.c.h:1853`, and `unicode_new_impl`: `object`,
`encoding` and `errors` by position or keyword. -/
def strNew (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  if args.length + kw.length > 3 then
    typeErr s!"str() takes at most 3 arguments ({args.length + kw.length} given)"
  for (k, _) in kw do
    if !["object", "encoding", "errors"].contains k then
      typeErr s!"str() got an unexpected keyword argument '{k}'"
  let names := ["object", "encoding", "errors"]
  for (k, i) in names.zipIdx do
    if i < args.length && (kw.find? (·.1 == k)).isSome then
      typeErr s!"argument for str() given by name ('{k}') and position ({i + 1})"
  let arg (i : Nat) (k : String) : Option Val :=
    match args[i]? with
    | some v => some v
    | none => (kw.find? (·.1 == k)).map (·.2)
  let x := arg 0 "object"
  let e := arg 1 "encoding"
  let er := arg 2 "errors"
  let w ← getW
  match e with
  | some v =>
    if (strOf w v).isNone then
      typeErr s!"str() argument 'encoding' must be str, not {argTypeName w v}"
  | none => pure ()
  match er with
  | some v =>
    if (strOf w v).isNone then
      typeErr s!"str() argument 'errors' must be str, not {argTypeName w v}"
  | none => pure ()
  match x, e, er with
  | none, _, _ => boxValue t B.str (.str "")
  | some o, none, none =>
    -- `unicode_new_impl`, `Objects/unicodeobject.c:13902-13912`: `str(x)` is `PyObject_Str(x)`
    -- itself, so a `str` subclass instance from `__str__` comes back as it is; a subclass of
    -- `str` gets a copy of the text (`unicode_subtype_new`).
    if t == B.str then pyStrObj rt o
    else
      let s ← rt.str o
      boxValue t B.str (.str s)
  | some o, _, _ =>
    match strOf w o with
    | some _ => typeErr "decoding str is not supported"
    | none =>
      typeErr s!"decoding to str: need a bytes-like object, {trunc 80 (typeName w o)} found"

/-- `tuple_new`, `Objects/tupleobject.c`. -/
def tupleNew (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  -- `tuple_new`, `Objects/clinic/tupleobject.c.h`: keywords are refused unless a subclass has
  -- a `tp_init` of its own to take them.
  let w ← getW
  if t == B.tuple || slotOf w t .tp_init == slotOf w B.tuple .tp_init then noKeywords "tuple" kw
  unpackTuple "tuple" 0 1 args.length
  match args with
  | [] => boxValue t B.tuple (.tuple [])
  | x :: _ =>
    let xs ← pySequenceTuple rt x
    boxValue t B.tuple (.tuple xs)

/-- `list___init__`: `self[:] = iterable`. -/
def listInit (rt : Rt) (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  noKeywords "list" kw
  unpackTuple "list" 0 1 args.length
  match args, self with
  | [], .obj a => modObj a fun o => { o with body := .list [] }
  | x :: _, .obj a =>
    -- `list___init___impl`, `Objects/listobject.c:3554-3560`: clear, then `_list_extend`.
    modObj a fun o => { o with body := .list [] }
    listExtend rt self a x
  | _, _ => gap%

/-- `dict_update_common`, `Objects/dictobject.c:4008`: the argument, then the keywords, are merged
into `self`, which keeps what it held. -/
def dictUpdateCommon (rt : Rt) (self : Val) (args : List Val) (kw : Kw) (name : String) : M Unit := do
  unpackTuple name 0 1 args.length
  match self with
  | .obj a =>
    match args with
    | [] => pure ()
    | x :: _ => dictUpdateArg rt a x
    for (k, v) in kw do
      dictInsert rt a (.str k) (strHash k) v
  | _ => gap%

/-- `dict_init`. -/
def dictInit (rt : Rt) (self : Val) (args : List Val) (kw : Kw) : M Unit :=
  dictUpdateCommon rt self args kw "dict"

/-- `frozendict_new`, `Objects/dictobject.c:8469`: the update runs on an object nothing else can
see yet, here a `dict` that then changes its payload. -/
def frozendictNew (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  let d ← alloc B.dict (.dict [])
  dictUpdateCommon rt d args kw "frozendict"
  match d with
  | .obj a =>
    modObj a fun o => { o with cls := t, body := .frozen ((match o.body with
      | .dict es => es
      | _ => [])) }
    pure d
  | _ => gap%

/-- `property_init_impl`, `Objects/descrobject.c:1861`, with the clinic argument
parsing. -/
def propertyInit (rt : Rt) (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  let names := ["fget", "fset", "fdel", "doc"]
  if args.length + kw.length > 4 then
    typeErr s!"property() takes at most 4 arguments ({args.length + kw.length} given)"
  let mut vals : NameDict := (names.zip args)
  for (k, v) in kw do
    if !names.contains k then
      typeErr s!"property() got an unexpected keyword argument '{k}'"
    if NameDict.contains vals k then
      typeErr s!"argument for property() given by name ('{k}') and position ({(names.findIdx (· == k)) + 1})"
    vals := NameDict.set vals k v
  let g := fun (n : Name) => (NameDict.get? vals n).getD .none
  let doc := NameDict.get? vals "doc"
  let fget := g "fget"
  let (propDoc, getterDoc) ←
    match doc with
    | some d =>
      if d.is .none then
        match fget with
        | .none => pure ((none : Option Val), false)
        | _ =>
          match ← rt.getOptionalAttr fget "__doc__" with
          | some .none | none => pure (none, false)
          | some x => pure (some x, true)
      else pure (some d, false)
    | none =>
      match fget with
      | .none => pure (none, false)
      | _ =>
        match ← rt.getOptionalAttr fget "__doc__" with
        | some .none | none => pure (none, false)
        | some x => pure (some x, true)
  let w ← getW
  match self with
  | .obj a =>
    if typeOf w self == B.property then
      modObj a fun o =>
        { o with body := .property fget (g "fset") (g "fdel") (propDoc.getD .none) none getterDoc }
    else
      modObj a fun o =>
        { o with body := .property fget (g "fset") (g "fdel") .none none getterDoc }
      let set := rt.setAttr self "__doc__" (some (propDoc.getD .none))
      if getterDoc then set
      else catchMatch B.AttributeError set (pure ())
  | _ => gap%

/-- `cm_new`, `sm_new`, `Objects/funcobject.c:1557`, `:1819`: `__new__` takes the callable, so a
subclass that skips `__init__` still has one. -/
def descrWrapNew (rt : Rt) (name : String) (t : Addr) (args : List Val) (kw : Kw)
    (mk : Val → Payload) : M Val := do
  noKeywords name kw
  unpackTuple name 1 1 args.length
  match args with
  | [c] =>
    let v ← alloc t (mk c)
    functoolsWraps rt v c
    pure v
  | _ => gap%

/-- `cm_init`, `sm_init`, `Objects/funcobject.c:1580`, `:1842`, and `cm_set_callable`, `sm_set_callable`
(`:1544`, `:1806`): the callable of `cm_new` is not set again, so nothing is copied twice. -/
def descrWrapInit (rt : Rt) (name : String) (self : Val) (args : List Val) (kw : Kw)
    (mk : Val → Payload) : M Unit := do
  noKeywords name kw
  unpackTuple name 1 1 args.length
  let w ← getW
  match args, self with
  | [c], .obj a =>
    let cur := match payloadOf w self with
      | some (.classmethod f) | some (.staticmethod f) => some f
      | _ => none
    if cur.any (·.is c) then return ()
    modObj a fun o => { o with body := mk c }
    functoolsWraps rt self c
  | _, _ => gap%

/-- `super_init`/`super_init_impl`, `Objects/typeobject.c:13003`, `:13019`, with two
explicit arguments. Zero-argument `super()` needs the caller's frame: see `superZero`. -/
def superInit (rt : Rt) (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  noKeywords "super" kw
  let w ← getW
  match args.length with
  -- `super_init_without_args` reads the caller's frame, which the `Rt` does not carry.
  | 0 => gap%
  | 1 | 2 =>
    let arg0 := args.headD .none
    match asType w arg0 with
    | none =>
      -- `PyArg_ParseTuple(args, "|O!O:super", &PyType_Type, ...)`, `:13010`.
      typeErr s!"super() argument 1 must be type, not {argTypeName w arg0}"
    | some ty =>
      let obj := match args with
        | [_, o] => if o.is .none then none else some o
        | _ => none
      let objType ← match obj with
        | some o => some <$> supercheck rt ty o
        | none => pure none
      match self with
      | .obj a => modObj a fun o => { o with body := .super (some ty) obj objType }
      | _ => gap%
  | n => typeErr s!"super() takes at most 2 arguments ({n} given)"

/-- `super_vectorcall`, `Objects/typeobject.c:13090`: `super(...)` on exact `super` skips
`tp_new` and `tp_init`, with messages of its own. -/
def superVectorcall (rt : Rt) (args : List Val) (kw : Kw) : M Val := do
  unless kw.isEmpty do typeErr "super() takes no keyword arguments"
  if args.length > 2 then typeErr s!"super() expected at most 2 arguments, got {args.length}"
  let w ← getW
  let su ← alloc B.super (freshBody w B.super)
  match args with
  | [] => gap%
  | arg0 :: _ =>
    match asType w arg0 with
    | none =>
      typeErr s!"super() argument 1 must be a type, not {trunc 200 (typeName w arg0)}"
    | some _ =>
      superInit rt su args []
      pure su

/-- `slot_tp_new`, `Objects/typeobject.c:11297`. -/
def slotTpNew (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  let func ← rt.getAttr (.obj t) "__new__"
  rt.call func (.obj t :: args) kw

/-- Call the `tp_new` function `f`. -/
def callTpNew (rt : Rt) (f : SlotFn) (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  let w ← getW
  match f with
  | .generic => slotTpNew rt t args kw
  | .c .object => objectNew rt t args kw
  | .c .type => typeNew rt t args kw
  | .c .int => longNew rt t args kw
  | .c .bool => boolNew rt args kw
  | .c .float =>
    noKeywords "float" kw
    unpackTuple "float" 0 1 args.length
    -- `float_new_impl`, `Objects/floatobject.c:1567`: only exact `float` calls for the string
    -- path directly, and a subclass copies the value (`float_subtype_new`).
    let r ← match args with
      | [] => mkFloat (PyLean.Binary64.F64.zero false)
      | x :: _ =>
        if typeOf w x == B.str then floatFromString rt x else pyNumberFloat rt x
    if t == B.float then pure r
    else
      let w ← getW
      match floatOf w r with
      | some v => alloc t (.boxed (.float v.bits))
      | none => gap%
  | .c .str => strNew rt t args kw
  | .c .tuple => tupleNew rt t args kw
  | .c .method =>
    -- `method_new_impl`, `Objects/classobject.c:195`.
    noKeywords "method" kw
    unpackTuple "method" 2 2 args.length
    match args with
    | [func, inst] =>
      if !excCallableCheck w func then typeErr "first argument must be callable"
      if inst.is .none then typeErr "instance must not be None"
      alloc B.method (.bound func inst)
    | _ => gap%
  | .c .mappingproxy =>
    -- `mappingproxy_new_impl`, `Objects/descrobject.c:1287`, and the check at `:1264`.
    let m ← match args, kw with
      | [x], [] | [], [("mapping", x)] => pure x
      | _, _ =>
        if args.length + kw.length > 1 then
          typeErr s!"mappingproxy() takes at most 1 argument ({args.length + kw.length} given)"
        else typeErr "mappingproxy() missing required argument 'mapping' (pos 1)"
    if (slotOf w (typeOf w m) .mp_subscript).isNone || isSubtype w (typeOf w m) B.list ||
        isSubtype w (typeOf w m) B.tuple then
      typeErr s!"mappingproxy() argument must be a mapping, not {typeName w m}"
    alloc B.mappingproxy (.proxy m)
  | .c .frozendict => frozendictNew rt t args kw
  | .c .classmethod => descrWrapNew rt "classmethod" t args kw .classmethod
  | .c .staticmethod => descrWrapNew rt "staticmethod" t args kw .staticmethod
  | .c .list | .c .dict | .c .property | .c .super =>
    alloc t (freshBody w t)
  | .c .none =>
    if excessArgs args kw then typeErr "NoneType takes no arguments" else pure .none
  | .c .notImpl =>
    if excessArgs args kw then typeErr "NotImplementedType takes no arguments" else pure .notImpl
  | .c e => if isExcFamily e then excTpNew rt e t args kw else gap%
  | _ => gap%

/-- `type_init`, `Objects/typeobject.c:4175`. -/
def typeInit (args : List Val) (kw : Kw) : M Unit := do
  if !kw.isEmpty && args.length == 1 then
    typeErr "type.__init__() takes no keyword arguments"
  if args.length != 1 && args.length != 3 then
    typeErr "type.__init__() takes 1 or 3 arguments"

/-- `slot_tp_init`, `Objects/typeobject.c:11280`. -/
def slotTpInit (rt : Rt) (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  let res ← callMethod rt self "__init__" args kw
  let w ← getW
  unless res.is .none do
    typeErr s!"__init__() should return None, not '{trunc 200 (typeName w res)}'"

/-- Call the `tp_init` function `f`. -/
def callTpInit (rt : Rt) (f : SlotFn) (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  match f with
  | .generic => slotTpInit rt self args kw
  | .c .object => objectInit self args kw
  | .c .type => typeInit args kw
  | .c .list => listInit rt self args kw
  | .c .dict => dictInit rt self args kw
  | .c .property => propertyInit rt self args kw
  | .c .classmethod => descrWrapInit rt "classmethod" self args kw .classmethod
  | .c .staticmethod => descrWrapInit rt "staticmethod" self args kw .staticmethod
  | .c .super => superInit rt self args kw
  | .c e => if isExcFamily e then excTpInit rt e self args kw else gap%
  | _ => gap%

/-- `type_call`, `Objects/typeobject.c:2471`. -/
def typeCall (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  let w ← getW
  if t == B.type then
    match args with
    | [x] =>
      if kw.isEmpty then return .obj (typeOf w x)
    | _ => pure ()
    if args.length != 3 then typeErr "type() takes 1 or 3 arguments"
  match slotOf w t .tp_new with
  | none => typeErr s!"cannot create '{tpName w t}' instances"
  | some f =>
    let obj ← callTpNew rt f t args kw
    let w ← getW
    unless isSubtype w (typeOf w obj) t do return obj
    match slotOf w (typeOf w obj) .tp_init with
    | some g =>
      callTpInit rt g obj args kw
      pure obj
    | none => pure obj

/-- `tp_new_wrapper`, `Objects/typeobject.c:10513`. -/
def tpNewWrapper (rt : Rt) (ty : Addr) (args : List Val) (kw : Kw) : M Val := do
  let w ← getW
  let tn := tpName w ty
  match args with
  | [] => typeErr s!"{tn}.__new__(): not enough arguments"
  | arg0 :: rest =>
    match asType w arg0 with
    | none => typeErr s!"{tn}.__new__(X): X is not a type object ({typeName w arg0})"
    | some sub =>
      let sn := tpName w sub
      unless isSubtype w sub ty do
        typeErr s!"{tn}.__new__({sn}): {sn} is not a subtype of {tn}"
      -- staticbase: the most derived base that is not a heap type, :10554
      let rec walk : Nat → Option Addr → Option Addr
        | 0, s => s
        | n + 1, s =>
          match s with
          | none => none
          | some x =>
            if slotOf w x .tp_new == some .generic then walk n (tdata w x).base else some x
      match walk w.heap.size (some sub) with
      | some sb =>
        if slotOf w sb .tp_new != slotOf w ty .tp_new then
          if (slotOf w sb .tp_new).isNone then
            typeErr s!"cannot create '{sn}' instances"
          typeErr s!"{tn}.__new__({sn}) is not safe, use {tpName w sb}.__new__()"
      | none => pure ()
      match slotOf w ty .tp_new with
      | some f => callTpNew rt f sub rest kw
      | none => gap%

/-! ## Slot wrappers -/

/-- The message of `check_num_args`, `Objects/typeobject.c:9921`. -/
def argCountMsg (n got : Nat) : String :=
  s!"expected {n} argument{if n == 1 then "" else "s"}, got {got}"

/-- `check_num_args`, `Objects/typeobject.c:9912`. -/
def checkNumArgs (args : List Val) (n : Nat) : M Unit := do
  unless args.length == n do
    typeErr (argCountMsg n args.length)

/-- `wrap_*` arity: `check_pow_args`, `Objects/typeobject.c:9928`. -/
def checkPowArgs (args : List Val) : M Unit := do
  unless args.length == 1 || args.length == 2 do
    typeErr s!"expected 1 or 2 arguments, got {args.length}"

/-- `getindex`, `Objects/typeobject.c:10089`. -/
def getIndex (rt : Rt) (self arg : Val) : M Int := do
  let i ← numberAsSsize rt arg (some B.OverflowError)
  if i < 0 then
    let w ← getW
    match slotIn w self .sq_length with
    | some f =>
      let n ← callLen rt f self
      pure (i + n)
    | none => pure i
  else pure i

/-- The slot-compare in `hackcheck_unlocked`, `Objects/typeobject.c:10222`. -/
def hackcheck (self : Val) (func : SlotFn) (what : String) : M Unit := do
  let w ← getW
  if !typeCheck w self then return
  let t := typeOf w self
  match (tdata w t).mro with
  | none => pure ()
  | some mro =>
    let own := slotOf w t .tp_setattro
    let defining := (mro.reverse.find? fun b =>
        slotOf w b .tp_setattro != some .generic && slotOf w b .tp_setattro == own).getD t
    let rec chain : Nat → Option Addr → M Unit
      | 0, _ | _, none => pure ()
      | n + 1, some b =>
        let s := slotOf w b .tp_setattro
        if s == some func then pure ()
        else if s != some .generic then
          typeErr s!"can't apply this {what} to {tpName w t} object"
        else chain n (tdata w b).base
    chain w.heap.size (some defining)

/-- Attribute names passed to slot functions directly must be strings
(`PyObject_GenericGetAttr`, `Objects/object.c:1902`). -/
def attrName (v : Val) : M Name := do
  let w ← getW
  match strOf w v with
  | some s => pure s
  | none => typeErr s!"attribute name must be string, not '{trunc 200 (typeName w v)}'"

/-- A one-operand wrapped slot, `wrap_unaryfunc`, `Objects/typeobject.c:10063`. -/
def wrapUnary (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) : M Val := do
  match p.slot with
  | .tp_repr => callRepr rt f self
  | .tp_str => callStr rt f self
  | .tp_iter => callIter rt f self
  | .nb_negative | .nb_positive | .nb_absolute | .nb_invert | .nb_int | .nb_index =>
    callUnaryNb rt p.slot p.name f self
  | .nb_float => callUnaryNb rt p.slot p.name f self
  | .am_await | .am_aiter | .am_anext => gap%
  | _ => gap%

/-- `wrapperdescr_raw_call`'s dispatch on the wrapper function,
`Objects/typeobject.c:9956-10510`. -/
def wrapperApply (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) (args : List Val)
    (kw : Kw) : M Val := do
  match p.wrapper with
  | none => gap%
  | some .call => rt.tpCall f self args kw
  | some .init =>
    callTpInit rt f self args kw
    pure .none
  | some wr =>
    unless kw.isEmpty do typeErr s!"wrapper {p.name}() takes no keyword arguments"
    match wr with
    | .unary =>
      checkNumArgs args 0
      wrapUnary rt p f self
    | .len =>
      checkNumArgs args 0
      .int <$> callLen rt f self
    | .inquiry =>
      checkNumArgs args 0
      match f with
      | .generic => .bool <$> slotNbBool rt self
      | _ => .bool <$> rt.isTrue self
    | .hash =>
      checkNumArgs args 0
      .int <$> callHash rt f self
    | .binary | .binaryL =>
      checkNumArgs args 1
      let other := args.headD .none
      match p.slot with
      | .tp_getattro =>
        let n ← attrName other
        callGetattro rt f self n
      | .mp_subscript => callMpSubscript rt f self other
      | .sq_concat => callSqConcat rt f self other
      | .sq_inplace_concat => callSqInplaceConcat rt f self other
      | s =>
        if s.group == .number then
          match f, wr with
          | .generic, .binary => vectorcallMethod rt p.name [self, other]
          -- `nb_inplace_or` of `dict` and of `mappingproxy`.
          | .c .dict, .binary | .c .mappingproxy, .binary =>
            if p.name == "__ior__" then binaryIop1.callInplace rt f p.name self other
            else callNbBinary rt s f self other
          | _, _ => callNbBinary rt s f self other
        else gap%
    | .binaryR =>
      checkNumArgs args 1
      callNbBinary rt p.slot f (args.headD .none) self
    | .ternary =>
      checkPowArgs args
      let other := args.headD .none
      let third := args.getD 1 .none
      match p.slot with
      | .nb_inplace_power =>
        match f with
        | .generic => vectorcallMethod rt "__ipow__" [self, other]
        | _ => gap%
      | _ => callNbPower rt f self other third
    | .ternaryR =>
      checkPowArgs args
      callNbPower rt f (args.headD .none) self (args.getD 1 .none)
    | .richcmp op =>
      checkNumArgs args 1
      callRichcompare rt f self (args.headD .none) op
    | .next =>
      checkNumArgs args 0
      match ← callIterNext rt f self with
      | some r => pure r
      | none => raise (.exc B.StopIteration "" none)
    | .descrGet =>
      unpackTuple "__get__" 1 2 args.length
      let obj := args.headD .none
      let ty := args.getD 1 .none
      let obj' := if obj.is .none then none else some obj
      let ty' := if ty.is .none then none else some ty
      if obj'.isNone && ty'.isNone then typeErr "__get__(None, None) is invalid"
      callDescrGet rt f self obj' ty'
    | .descrSet =>
      unpackTuple "__set__" 2 2 args.length
      callDescrSet rt f self (args.headD .none) (some (args.getD 1 .none))
      pure .none
    | .descrDelete =>
      checkNumArgs args 1
      callDescrSet rt f self (args.headD .none) none
      pure .none
    | .setattr =>
      unpackTuple "__setattr__" 2 2 args.length
      hackcheck self f "__setattr__"
      let w ← getW
      -- `type_setattro` tests immutability before the name, `Objects/typeobject.c:6808`.
      if f == .c .type && (match self with
          | .obj t => (tdata w t).immutable
          | _ => false) then
        let r ← rt.repr (args.headD .none)
        typeErr s!"cannot set {r} attribute of immutable type '{(match self with
          | .obj t => tpName w t
          | _ => "")}'"
      let n ← attrName (args.headD .none)
      callSetattro rt f self n (some (args.getD 1 .none))
      pure .none
    | .delattr =>
      checkNumArgs args 1
      hackcheck self f "__delattr__"
      let w ← getW
      if f == .c .type && (match self with
          | .obj t => (tdata w t).immutable
          | _ => false) then
        let r ← rt.repr (args.headD .none)
        typeErr s!"cannot set {r} attribute of immutable type '{(match self with
          | .obj t => tpName w t
          | _ => "")}'"
      let n ← attrName (args.headD .none)
      callSetattro rt f self n none
      pure .none
    | .indexArg =>
      checkNumArgs args 1
      let i ← numberAsSsize rt (args.headD .none) (some B.OverflowError)
      if p.slot == .sq_inplace_repeat then callSqInplaceRepeat f self i
      else callSqRepeat f self i
    | .sqItem =>
      checkNumArgs args 1
      let i ← getIndex rt self (args.headD .none)
      callSqItem rt f self i
    | .sqSetitem =>
      unpackTuple "__setitem__" 2 2 args.length
      let i ← getIndex rt self (args.headD .none)
      callAssSubscript rt f self (.int i) (some (args.getD 1 .none))
      pure .none
    | .sqDelitem =>
      checkNumArgs args 1
      let i ← getIndex rt self (args.headD .none)
      callAssSubscript rt f self (.int i) none
      pure .none
    | .objobj =>
      checkNumArgs args 1
      .bool <$> callContains rt f self (args.headD .none)
    | .objobjarg =>
      unpackTuple "__setitem__" 2 2 args.length
      callAssSubscript rt f self (args.headD .none) (some (args.getD 1 .none))
      pure .none
    | .delitem =>
      checkNumArgs args 1
      callAssSubscript rt f self (args.headD .none) none
      pure .none
    | _ => gap%

/-- `wrapperdescr_call`, `Objects/descrobject.c:536`. -/
def wrapperdescrCall (rt : Rt) (owner : Addr) (p : SlotDef) (f : SlotFn) (args : List Val)
    (kw : Kw) : M Val := do
  let w ← getW
  match args with
  | [] => typeErr s!"descriptor '{p.name}' of '{trunc 100 (tpName w owner)}' object needs an argument"
  | self :: rest =>
    unless isSubtype w (typeOf w self) owner do
      typeErr s!"descriptor '{p.name}' requires a '{trunc 100 (tpName w owner)}' object but received a '{trunc 100 (typeName w self)}'"
    wrapperApply rt p f self rest kw

/-! ## Builtin functions -/

/-- `object.__dir__` and `type.__dir__`: `merge_class_dict`, `Objects/typeobject.c:7134`,
over the static hierarchy. -/
def classDictKeys (w : World) (t : Addr) : List Name :=
  ((tdata w t).mro.getD []).flatMap fun c => (tdata w c).dict.map (·.1)

/-- `object___format___impl`, `Objects/typeobject.c:8501-8513`: `PyObject_Str(self)` for an empty
spec, the object it returns (a `str` subclass instance stays one). -/
def objectFormat (rt : Rt) (self : Val) (spec : String) : M Val := do
  let w ← getW
  if spec.length > 0 then
    typeErr s!"unsupported format string passed to {trunc 200 (typeName w self)}.__format__"
  pyStrObj rt self

/-- `PyObject_Format`, `Objects/abstract.c:853`. -/
def pyFormat (rt : Rt) (obj : Val) (spec : Option Val) : M Val := do
  let w ← getW
  let specS : Option String := match spec with
    | some s => strOf w s
    | none => none
  if spec.isSome && specS.isNone then
    systemErr s!"Format specifier must be a string, not {trunc 200 (typeName w (spec.getD .none))}"
  if specS.getD "" == "" then
    match obj with
    | .str _ => return obj
    | .int _ => return .str (← rt.str obj)
    | _ => pure ()
  let specV : Val := spec.getD (.str "")
  match ← lookupSpecial rt obj "__format__" with
  | none => typeErr s!"Type {trunc 100 (typeName w obj)} doesn't define __format__"
  | some m =>
    let r ← rt.call m [specV] []
    let w ← getW
    match strOf w r with
    | some _ => pure r
    | none => typeErr s!"{objFQN w obj}.__format__() must return a str, not {objFQN w r}"

/-- `dir(obj)` for the object protocol, `_dir_object`, `Objects/object.c:2235`. -/
def pyDir (rt : Rt) (obj : Val) : M Val := do
  let w ← getW
  match ← lookupSpecial rt obj "__dir__" with
  | none => typeErr "object does not provide __dir__"
  | some d =>
    let r ← rt.call d [] []
    let items ← pySequenceList rt r
    let w' ← getW
    let names := items.filterMap (strOf w')
    if names.length != items.length then gap%
    let sorted := names.mergeSort fun a b => decide (strCompare a.toList b.toList ≤ 0)
    let _ := w
    alloc B.list (.list (sorted.map Val.str))

/-- The `doc` argument of `property_copy`, `Objects/descrobject.c:1804-1810`. -/
def copyDocArg (getterDoc : Bool) (g doc : Val) : Val :=
  if getterDoc && !g.is .none then .none else doc

/-- `property_copy`, `Objects/descrobject.c:1786`. -/
def propertyCopy (rt : Rt) (old : Val) (get set del : Option Val) : M Val := do
  let w ← getW
  match propertyFields w old with
  | none => gap%
  | some (g, s, d, doc, name, getterDoc) =>
    let pick (x : Option Val) (dflt : Val) : Val :=
      match x with
      | none | some .none => dflt
      | some v => v
    let g' := pick get g
    let s' := pick set s
    let d' := pick del d
    let docArg : Val := copyDocArg getterDoc g' doc
    let n ← rt.call (.obj (typeOf w old)) [g', s', d', docArg] []
    let w ← getW
    match n, payloadOf w n with
    | .obj a, some (.property g2 s2 d2 doc2 _ gd2) =>
      modObj a fun o => { o with body := .property g2 s2 d2 doc2 name gd2 }
      pure n
    | _, _ => pure n

/-- `type_mro_impl`, `Objects/typeobject.c:3575`. -/
def typeMroImpl (rt : Rt) (self : Val) : M Val := do
  match self with
  | .obj t =>
    let m ← mroImplementation rt t
    alloc B.list (.list (m.map Val.obj))
  | _ => gap%

/-- `_PyObject_FunctionStr` of a builtin, `Objects/object.c:962`, via `meth_get__qualname__`,
`Objects/methodobject.c:231`. -/
def builtinFuncStr (w : World) (name : String) (self : Option Val) : String :=
  match self with
  | none => name ++ "()"
  | some s =>
    let t := match asType w s with
      | some a => a
      | none => typeOf w s
    s!"{typeQualname w t}.{name}()"

/-- `cfunction_check_kwargs` and the argument counts of `cfunction_vectorcall_NOARGS` and
`_O`, `Objects/methodobject.c:407`, `:487`, `:515`. -/
def checkBuiltinArgs (b : Builtin) (self : Option Val) (args : List Val) (kw : Kw)
    (owner : Option Addr) : M Unit := do
  let w ← getW
  let (n, conv) := builtinConv b
  let fs := match owner with
    | some o => s!"{typeQualname w o}.{n}()"
    | none => builtinFuncStr w n self
  match conv with
  | .keywords => pure ()
  | .fast => unless kw.isEmpty do typeErr s!"{fs} takes no keyword arguments"
  | .noargs =>
    unless kw.isEmpty do typeErr s!"{fs} takes no keyword arguments"
    unless args.isEmpty do typeErr s!"{fs} takes no arguments ({args.length} given)"
  | .o =>
    unless kw.isEmpty do typeErr s!"{fs} takes no keyword arguments"
    unless args.length == 1 do
      typeErr s!"{fs} takes exactly one argument ({args.length} given)"

/-- `(getattr, (obj, name))`, the tuple `Py_BuildValue("N(OO)", ...)` makes in the `__reduce__` of
methods and descriptors. -/
def reduceToGetattr (obj name : Val) : M Val := do
  let g ← alloc B.builtinFn (.builtin .getattr none)
  pure (.tuple [g, .tuple [obj, name]])

/-- `_Py_IsPrivateName`, `Python/symtable.c:3311`. -/
def isPrivateName (n : String) : Bool :=
  let c := n.toList
  c.length ≥ 3 && c.take 2 == ['_', '_'] && c.drop (c.length - 2) != ['_', '_']

/-- `method___reduce___impl`, `Objects/classobject.c:91`. -/
def methodReduce (rt : Rt) (self : Val) : M Val := do
  let w ← getW
  match payloadOf w self with
  | some (.bound func s) =>
    let name ← rt.getAttr func "__name__"
    let w ← getW
    match strOf w name with
    | some n =>
      if isPrivateName n then
        let cls := match asType w s with
          | some t => t
          | none => typeOf w s
        reduceToGetattr s (.str (pyMangle (pyTypeName w cls) n))
      else reduceToGetattr s name
    | none => reduceToGetattr s name
  | _ => gap%

/-- `meth_reduce`, `Objects/methodobject.c:192`. -/
def methReduce (self : Val) : M Val := do
  let w ← getW
  match payloadOf w self with
  | some (.builtin b s) =>
    match builtinName b, s with
    | some n, none => pure (.str n)
    | some n, some x => reduceToGetattr x (.str n)
    | none, _ => gap%
  | _ => gap%

/-- `wrapper_reduce`, `Objects/descrobject.c:1393`. -/
def wrapperReduce (self : Val) : M Val := do
  let w ← getW
  match payloadOf w self with
  | some (.methodWrapper d s) =>
    match payloadOf w d with
    | some (.wrapperDescr _ p _) => reduceToGetattr s (.str p.name)
    | _ => gap%
  | _ => gap%

/-- `d_type` and `d_name` of a descriptor. -/
def descrInfo (w : World) (d : Val) : Option (Addr × Name) :=
  match payloadOf w d with
  | some (.wrapperDescr o p _) => some (o, p.name)
  | some (.methodDescr o nm _) | some (.classmethodDescr o nm _) => some (o, nm)
  | some (.memberDescr o nm _) | some (.getsetDescr o nm _) => some (o, nm)
  | _ => none

/-- `descr_reduce`, `Objects/descrobject.c:630`. -/
def descrReduce (self : Val) : M Val := do
  let w ← getW
  match descrInfo w self with
  | some (o, nm) => reduceToGetattr (.obj o) (.str nm)
  | none => gap%

/-- Call a `Builtin`. `self` is `m_self`; methods receive their instance there. -/
def callBuiltin (rt : Rt) (b : Builtin) (self : Option Val) (args : List Val) (kw : Kw)
    (owner : Option Addr := none) : M Val := do
  checkBuiltinArgs b self args kw owner
  let w ← getW
  let selfV := self.getD .none
  match b with
  | .stub n => gapAt s!"stub:{n}"
  | .excMethod n => excMethod rt n selfV args kw
  | .tpNewWrapper ty => tpNewWrapper rt ty args kw
  | .objectInitSubclass => pure .none
  | .objectSubclasshook => pure .notImpl
  | .classGetitem => alloc B.genericAlias .plain
  | .objectFormat =>
    match args with
    | [s] =>
      match strOf w s with
      | some sp =>
        objectFormat rt selfV sp
      | none => typeErr s!"__format__() argument must be str, not {argTypeName w s}"
    | _ => gap%
  | .numDunderFormat =>
    -- `int.__format__` and `float.__format__`, `_PyLong_FormatAdvancedWriter` and
    -- `_PyFloat_FormatAdvancedWriter`, `Objects/unicode_formatter.c:1828`, `:1890`: an empty
    -- spec is the `str` of the number, and type `s` is `unknown_presentation_type` (`:1880`,
    -- `:1923`). Other specs belong to `LongObj` and `Binary64`.
    match args with
    | [s] =>
      match strOf w s with
      | some "" => .str <$> rt.str selfV
      | some "s" =>
        valueErr s!"Unknown format code 's' for object of type '{trunc 200 (typeName w selfV)}'"
      | some _ => gap%
      | none => typeErr s!"__format__() argument must be str, not {argTypeName w s}"
    | _ => gap%
  | .strDunderFormat =>
    -- `unicode___format___impl` through `_PyUnicode_FormatAdvancedWriter`,
    -- `Objects/unicode_formatter.c:1792`: an empty spec is `PyObject_Str`, and spec `s` takes the
    -- fast path of `format_string_internal`, which hands back the object itself, subclass and all. Other specs belong
    -- to `UnicodeObj`.
    match args with
    | [s] =>
      match strOf w s with
      | some "" => .str <$> rt.str selfV
      | some "s" =>
        match strOf w selfV with
        | some _ => pure selfV
        | none => gap%
      | some _ => gap%
      | none => typeErr s!"__format__() argument must be str, not {argTypeName w s}"
    | _ => gap%
  | .objectDir => objectDirImpl rt selfV
  | .typeDir => typeDirImpl rt selfV
  | .floatMethod "fromhex" =>
    -- `float_fromhex`, `Objects/floatobject.c`: a subclass is called with the result.
    match args with
    | [a] =>
      match strOf w a with
      -- `PyUnicode_AsUTF8AndSize` on a non-str: `PyErr_BadArgument`.
      | none => typeErr "bad argument type for built-in operation"
      | some s =>
        let x ← pyToM (PyLean.Binary64.float_fromhex (s.toList.map (·.toNat)))
        let r ← mkFloat x
        if selfV.is (.obj B.float) then pure r else rt.call selfV [r] []
    | _ => gap%
  | .floatMethod n =>
    match floatOf w selfV with
    | none => gap%
    | some x =>
      match n with
      | "is_integer" => pure (.bool (PyLean.Binary64.float_is_integer x))
      | "__trunc__" => .int <$> pyToM (PyLean.Binary64.float_trunc x)
      | "__floor__" => .int <$> pyToM (PyLean.Binary64.float_floor x)
      | "__ceil__" => .int <$> pyToM (PyLean.Binary64.float_ceil x)
      | "conjugate" => if typeOf w selfV == B.float then pure selfV else mkFloat x
      | "__getnewargs__" =>
        let v ← mkFloat x
        pure (.tuple [v])
      | "hex" => pure (.str (PyLean.Binary64.float_hex x))
      | "as_integer_ratio" =>
        let (a, b) ← pyToM (PyLean.Binary64.float_as_integer_ratio x)
        pure (.tuple [.int a, .int b])
      | "__round__" =>
        -- `float___round___impl`, `Objects/floatobject.c`.
        unpackTuple "__round__" 0 1 args.length
        match args with
        | [] | [.none] => .int <$> pyToM (PyLean.Binary64.float_round_int x)
        | d :: _ =>
          let nd ← numberAsSsize rt d none
          let r ← pyToM (PyLean.Binary64.float_round_ndigits x nd)
          mkFloat r
      | _ => gap%
  | .proxyCall n =>
    -- `mappingproxy_keys` and the others, `Objects/descrobject.c:1112-1165`.
    let m ← proxyMapping selfV
    if n == "get" then
      unless args.length == 1 || args.length == 2 do
        typeErr s!"get expected {if args.isEmpty then "at least 1 argument" else "at most 2 arguments"}, got {args.length}"
      let f ← rt.getAttr m "get"
      rt.call f (if args.length == 1 then args ++ [.none] else args) []
    else
      let f ← rt.getAttr m n
      rt.call f [] []
  | .typeMro => typeMroImpl rt selfV
  | .typeSubclasses =>
    match selfV with
    | .obj t =>
      -- The subclasses of a static type depend on what the interpreter has imported.
      if !(tdata w t).heap then gap% else
      alloc B.list (.list ((tdata w t).subclasses.map Val.obj))
    | _ => gap%
  | .typePrepare => alloc B.dict (.dict [])
  | .objectSizeof =>
    -- `object___sizeof___impl`, `Objects/typeobject.c:8522`, for fixed-size objects.
    let d := tdata w (typeOf w selfV)
    if d.itemsize != 0 then gap% else pure (.int d.basicsize)
  | .typeInstancecheck =>
    match args with
    | [i] => .bool <$> objectIsinstance rt i selfV
    | _ => typeErr s!"__instancecheck__() takes exactly one argument ({args.length} given)"
  | .typeSubclasscheck =>
    match args with
    | [i] => .bool <$> recursiveIssubclass rt i selfV
    | _ => typeErr s!"__subclasscheck__() takes exactly one argument ({args.length} given)"
  | .isinstance =>
    match args with
    | [i, c] => .bool <$> pyIsInstance rt i c
    | _ => typeErr s!"isinstance expected 2 arguments, got {args.length}"
  | .issubclass =>
    match args with
    | [d, c] => .bool <$> pyIsSubclass rt d c
    | _ => typeErr s!"issubclass expected 2 arguments, got {args.length}"
  | .getattr =>
    match args with
    | [o, n] => do
      let nm ← attrName n
      rt.getAttr o nm
    | [o, n, d] => do
      let nm ← attrName n
      pure ((← rt.getOptionalAttr o nm).getD d)
    | _ => typeErr s!"getattr expected at least 2 arguments, got {args.length}"
  | .setattr =>
    match args with
    | [o, n, v] => do
      let nm ← attrName n
      rt.setAttr o nm (some v)
      pure .none
    | _ => typeErr s!"setattr expected 3 arguments, got {args.length}"
  | .delattr =>
    match args with
    | [o, n] => do
      let nm ← attrName n
      rt.setAttr o nm none
      pure .none
    | _ => typeErr s!"delattr expected 2 arguments, got {args.length}"
  | .hasattr =>
    match args with
    | [o, n] => do
      let nm ← attrName n
      pure (.bool (← rt.getOptionalAttr o nm).isSome)
    | _ => typeErr s!"hasattr expected 2 arguments, got {args.length}"
  | .len =>
    match args with
    | [o] => .int <$> pyObjectSize rt o
    | _ => typeErr s!"len() takes exactly one argument ({args.length} given)"
  | .iter =>
    match args with
    | [o] => rt.getIter o
    | _ => gap%
  | .next =>
    match args with
    | [it] =>
      if !pyIterCheck w it then
        typeErr s!"'{trunc 200 (typeName w it)}' object is not an iterator"
      match ← rt.iterNext it with
      | some v => pure v
      | none => raise (.exc B.StopIteration "" none)
    | [it, d] =>
      if !pyIterCheck w it then
        typeErr s!"'{trunc 200 (typeName w it)}' object is not an iterator"
      pure ((← rt.iterNext it).getD d)
    | _ => typeErr s!"next expected at least 1 argument, got {args.length}"
  | .repr =>
    match args with
    | [o] => .str <$> rt.repr o
    | _ => typeErr s!"repr() takes exactly one argument ({args.length} given)"
  | .hash =>
    match args with
    | [o] => .int <$> rt.hash o
    | _ => typeErr s!"hash() takes exactly one argument ({args.length} given)"
  | .hashProbe =>
    match args with
    | [o] =>
      let h ← rt.hash o
      let w ← getW
      if slotOf w (typeOf w o) .tp_hash == some .generic || (intOf w o).isSome then
        pure (.int h)
      else pure (.str "<h>")
    | _ => gap%
  | .callable =>
    match args with
    | [o] => pure (.bool (slotOf w (typeOf w o) .tp_call).isSome)
    | _ => typeErr s!"callable() takes exactly one argument ({args.length} given)"
  | .dir =>
    match args with
    | [o] => pyDir rt o
    | _ => gap%
  | .abs =>
    match args with
    | [o] => pyNumberAbsolute rt o
    | _ => typeErr s!"abs() takes exactly one argument ({args.length} given)"
  | .countOf | .indexOf =>
    -- `_operator_countOf_impl` and `_operator_indexOf_impl`, `Modules/_operator.c`, after
    -- `_PyArg_CheckPositional(name, nargs, 2, 2)`.
    let (nm, op) := if b matches .countOf then ("countOf", IterSearchOp.count)
      else ("indexOf", IterSearchOp.index)
    match args with
    | [a, c] => .int <$> pySequenceIterSearch rt a c op
    | _ => typeErr s!"{nm} expected 2 arguments, got {args.length}"
  | .divmod =>
    match args with
    | [a, c] => binaryOp rt a c .nb_divmod "divmod()"
    | _ => typeErr s!"divmod expected 2 arguments, got {args.length}"
  | .pow =>
    match args with
    | [a, c] => pyNumberPower rt a c .none
    | [a, c, m] => pyNumberPower rt a c m
    | _ => gap%
  | .format =>
    match args with
    | [o] => pyFormat rt o none
    | [o, s] => pyFormat rt o (some s)
    | _ => gap%
  | .propertyGetter =>
    match args with
    | [g] => propertyCopy rt selfV (some g) none none
    | _ => typeErr s!"getter() takes exactly one argument ({args.length} given)"
  | .propertySetter =>
    match args with
    | [g] => propertyCopy rt selfV none (some g) none
    | _ => typeErr s!"setter() takes exactly one argument ({args.length} given)"
  | .propertyDeleter =>
    match args with
    | [g] => propertyCopy rt selfV none none (some g)
    | _ => typeErr s!"deleter() takes exactly one argument ({args.length} given)"
  | .propertySetName =>
    match args, selfV with
    | [_, name], .obj a =>
      modObj a fun o =>
        match o.body with
        | .property g s d doc _ gd => { o with body := .property g s d doc (some name) gd }
        | _ => o
      pure .none
    | _, _ =>
      typeErr s!"__set_name__() takes 2 positional arguments but {args.length} were given"
  | .dunderGetitem =>
    match args with
    | [k] =>
      match slotIn w selfV .mp_subscript with
      | some _ =>
        callMpSubscript rt (if (dictOf w selfV).isSome then .c .dict else .c .list) selfV k
      | none => gap%
    | _ => typeErr s!"__getitem__() takes exactly one argument ({args.length} given)"
  | .dunderContains =>
    match args with
    | [k] => .bool <$> callContains rt (.c .dict) selfV k
    | _ => typeErr s!"__contains__() takes exactly one argument ({args.length} given)"
  | .dictKeysMethod =>
    -- `dict_keys_impl`, `Objects/dictobject.c:7010`: the view keeps a reference to the dict.
    alloc B.dictKeys (.seqIter (some selfV) 0)
  | .iterLengthHint =>
    match selfV with
    | .obj a =>
      match w.get a with
      | .val { body := .seqIter none _, .. } => pure (.int 0)
      | .val { body := .seqIter (some seq) i, .. } =>
        if typeOf w selfV == B.seqIter then
          -- `iter_len`, `Objects/iterobject.c:86`: the object's own `__len__` is called.
          if hasLen w seq then
            let n ← pySequenceSize rt seq
            pure (.int (if n - i ≥ 0 then n - i else 0))
          else pure .notImpl
        else
          -- `listiter_len`, `Objects/listobject.c:4113`, `tupleiter_len`,
          -- `Objects/tupleobject.c:1177`, `unicodeiter_len`, `Objects/unicodeobject.c:14676`,
          -- and `dictiter_len`, `Objects/dictobject.c:5637`, read the size directly.
          let n : Int := match seq, listOf w seq, strOf w seq with
            | .tuple xs, _, _ => xs.length
            | _, some xs, _ => xs.length
            | _, _, some s => s.length
            | _, _, _ => 0
          pure (.int (if n - i ≥ 0 then n - i else 0))
      | _ => gap%
    | _ => gap%
  | .objectGetstate => objectGetstateDefault rt selfV false
  | .objectReduce => commonReduce rt selfV 0
  | .objectReduceEx =>
    match args with
    | [p] => objectReduceEx rt selfV (← longAsInt rt p)
    | _ => gap%
  | .getnewargs =>
    -- `long_getnewargs`, `unicode_getnewargs`, `tuple_getnewargs`: a tuple of the plain value.
    match selfV, intOf w selfV, strOf w selfV, tupleOf w selfV with
    | _, some i, _, _ => pure (.tuple [.int i])
    | _, _, some t, _ => pure (.tuple [.str t])
    | _, _, _, some xs => pure (.tuple [.tuple xs])
    | _, _, _, _ => gap%
  | .reduceName s => pure (.str s)
  | .reduceBound => methodReduce rt selfV
  | .reduceCFunction => methReduce selfV
  | .reduceWrapper => wrapperReduce selfV
  | .reduceDescr => descrReduce selfV
  | .listAppend =>
    match args, selfV with
    | [x], .obj a =>
      modObj a fun o =>
        match o.body with
        | .list xs => { o with body := .list (xs ++ [x]) }
        | _ => o
      pure .none
    | _, _ => gap%
  | _ => gap%

/-! ## Getsets and static members -/

/-- `type_get_doc`, `Objects/typeobject.c:2090`, for heap types. -/
def typeGetDoc (rt : Rt) (t : Addr) : M Val := do
  let w ← getW
  match NameDict.get? (tdata w t).dict "__doc__" with
  | none => pure .none
  | some r =>
    -- `type_get_doc`, `Objects/typeobject.c`: a static type answers from `tp_doc`. The model has
    -- that text only where it is also the dict entry, not where the entry is a descriptor.
    if !(tdata w t).heap && (slotOf w (typeOf w r) .tp_descr_get).isSome then gap% else
    match slotOf w (typeOf w r) .tp_descr_get with
    | some g => callDescrGet rt g r none (some (.obj t))
    | none => pure r

/-- `_PyType_Name`: the part after the last dot. -/
def typeShortName (w : World) (t : Addr) : String := typeQualname w t

/-- `_PyObject_SetDict`, `Objects/typeobject.c:4060`. -/
def objectSetDict (obj : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match value with
  | some v =>
    if (dictOf w v).isNone then
      typeErr s!"__dict__ must be set to a dictionary, not a '{trunc 200 (typeName w v)}'"
  | none => pure ()
  if (tdata w (typeOf w obj)).dictoffset == 0 then attrErr "This object has no __dict__"
  match obj, value with
  | .obj a, none => modObj a fun o => { o with dict := none }
  | .obj a, some (.obj d) => modObj a fun o => { o with dict := some d }
  | _, _ => gap%

/-- `descr_get`: a value found in a class dict is bound with no object. -/
def bindToType (rt : Rt) (r : Val) (t : Addr) : M Val := do
  let w ← getW
  match slotOf w (typeOf w r) .tp_descr_get with
  | some g => callDescrGet rt g r none (some (.obj t))
  | none => pure r

/-- `type_get_annotate`, `Objects/typeobject.c:2129`: `__annotate__`, then `__annotate_func__`.
With neither, reading stores `None` under `__annotate_func__`, which the class dict then shows. -/
def typeGetAnnotate (rt : Rt) (t : Addr) : M Val := do
  let w ← getW
  let d := tdata w t
  if !d.heap then attrErr s!"type object '{tpName w t}' has no attribute '__annotate__'"
  let found := match NameDict.get? d.dict "__annotate__" with
    | some a => some a
    | none => NameDict.get? d.dict "__annotate_func__"
  match found with
  | some a => bindToType rt a t
  | none =>
    modType t fun d => { d with dict := NameDict.set d.dict "__annotate_func__" .none }
    pure .none

/-- `type_get_annotations`, `Objects/typeobject.c:2208`: `__annotations__`, then
`__annotations_cache__`, then a call of `__annotate__` whose result is cached. -/
def typeGetAnnotations (rt : Rt) (t : Addr) : M Val := do
  let w ← getW
  let d := tdata w t
  if !d.heap then attrErr s!"type object '{tpName w t}' has no attribute '__annotations__'"
  let found := match NameDict.get? d.dict "__annotations__" with
    | some a => some a
    | none => NameDict.get? d.dict "__annotations_cache__"
  match found with
  | some a => bindToType rt a t
  | none =>
    let annotate ← rt.getAttr (.obj t) "__annotate__"
    let w ← getW
    let ann ← if excCallableCheck w annotate then do
        let r ← rt.call annotate [.int 1] []
        let w ← getW
        if (dictOf w r).isNone then
          typeErr s!"__annotate__() must return a dict, not {objFQN w r}"
        pure r
      else alloc B.dict (.dict [])
    modType t fun d => { d with dict := NameDict.set d.dict "__annotations_cache__" ann }
    pure ann

/-- `type_set_annotate`, `Objects/typeobject.c:2169`. -/
def typeSetAnnotate (t : Addr) (value : Option Val) : M Unit := do
  let w ← getW
  match value with
  | none => typeErr "cannot delete __annotate__ attribute"
  | some v =>
    if (tdata w t).immutable then
      typeErr s!"cannot set '__annotate__' attribute of immutable type '{tpName w t}'"
    if !v.is .none && !excCallableCheck w v then
      typeErr "__annotate__ must be callable or None"
    modType t fun d =>
      let nd := NameDict.set d.dict "__annotate_func__" v
      { d with dict := if v.is .none then nd else NameDict.erase nd "__annotations_cache__" }

/-- `type_set_annotations`, `Objects/typeobject.c:2279`. -/
def typeSetAnnotations (t : Addr) (value : Option Val) : M Unit := do
  let w ← getW
  let d := tdata w t
  if d.immutable then
    typeErr s!"cannot set '__annotations__' attribute of immutable type '{tpName w t}'"
  let key := if NameDict.contains d.dict "__annotations__" then "__annotations__"
    else "__annotations_cache__"
  match value with
  | some v =>
    modType t fun d =>
      let nd := NameDict.set d.dict key v
      { d with dict := if key == "__annotations__" then NameDict.erase nd "__annotations_cache__" else nd }
  | none =>
    if !NameDict.contains d.dict key then attrErr "__annotations__"
    modType t fun d =>
      { d with dict := NameDict.erase (NameDict.erase d.dict key) "__annotations_cache__" }
  modType t fun d =>
    { d with dict := NameDict.erase (NameDict.erase d.dict "__annotate_func__") "__annotate__" }

/-- `function___annotations___get_impl`, `Objects/funcobject.c:967`, with
`func_get_annotation_dict`, `:539`. The result is kept on the function. -/
def funcGetAnnotations (rt : Rt) (fn : Addr) (f : FuncData) : M Val := do
  let w ← getW
  let store (d : Val) (g : FuncData) : M Val := do
    modObj fn fun o => { o with body := .func { g with annotations := some d } }
    pure d
  match f.annotations, f.annotate with
  | some d, _ => pure d
  | none, some a =>
    if excCallableCheck w a then
      let r ← rt.call a [.int 1] []
      let w ← getW
      if (dictOf w r).isNone then
        typeErr s!"__annotate__() must return a dict, not {objFQN w r}"
      match payloadOf w (.obj fn) with
      | some (.func g) => store r g
      | _ => gap%
    else
      let d ← alloc B.dict (.dict [])
      store d f
  | none, none =>
    let d ← alloc B.dict (.dict [])
    store d f

/-- `descriptor_get_wrapped_attribute`, `Objects/funcobject.c:1412`: the descriptor's own
`__dict__`, else the wrapped callable's attribute, which is then cached there. -/
def wrappedAttrGet (rt : Rt) (wrapped obj : Val) (n : Name) : M Val := do
  let dv ← genericGetDict obj
  let w ← getW
  match dv with
  | .obj d =>
    match dictLookup (dictEntries w d) (.str n) with
    | some r => pure r
    | none =>
      let r ← rt.getAttr wrapped n
      dictSetAt rt d (.str n) r
      pure r
  | _ => gap%

/-- `descriptor_set_wrapped_attribute`, `Objects/funcobject.c:1442`. -/
def wrappedAttrSet (rt : Rt) (obj : Val) (n : Name) (value : Option Val) (tn : String) : M Unit := do
  let dv ← genericGetDict obj
  match value, dv with
  | none, .obj _ =>
    catchMatch B.KeyError (callAssSubscript rt (.c .dict) dv (.str n) none)
      (attrErr s!"'{trunc 200 tn}' object has no attribute '{n}'")
  | some v, .obj d => dictSetAt rt d (.str n) v
  | _, _ => gap%

/-- `PyObject_GenericSetDict`, `Objects/object.c:2125`: unlike `subtype_setdict`, it refuses to
delete. -/
def genericSetDict (obj : Val) (value : Option Val) : M Unit := do
  if value.isNone then typeErr "cannot delete __dict__"
  objectSetDict obj value

/-- `get_builtin_base_with_dict`, `Objects/typeobject.c:4005`: the first static class with a dict
along `tp_base`. -/
def builtinBaseWithDict (w : World) : Nat → Addr → Option Addr
  | 0, _ => none
  | fuel + 1, t =>
    match (tdata w t).base with
    | none => none
    | some b =>
      if (tdata w t).dictoffset != 0 && !(tdata w t).heap then some t
      else builtinBaseWithDict w fuel b

/-- `get_dict_descriptor`, `Objects/typeobject.c:4017`. -/
def dictDescriptor (w : World) (base : Addr) : Option Val :=
  match findInMro w base "__dict__" with
  | some d => if isDataDescr w d then some d else none
  | none => none

/-- `raise_dict_descr_error`, `Objects/typeobject.c:4029`. -/
def raiseDictDescrError {α : Type} (obj : Val) : M α := do
  let w ← getW
  typeErr s!"this __dict__ descriptor does not support '{trunc 200 (typeName w obj)}' objects"

/-- `subtype_dict`, `Objects/typeobject.c:4037`: a static base keeps its own `__dict__`. -/
def subtypeDict (rt : Rt) (obj : Val) : M Val := do
  let w ← getW
  match builtinBaseWithDict w w.heap.size (typeOf w obj) with
  | some base =>
    match dictDescriptor w base with
    | none => raiseDictDescrError obj
    | some descr =>
      match slotOf w (typeOf w descr) .tp_descr_get with
      | none => raiseDictDescrError obj
      | some f => callDescrGet rt f descr (some obj) (some (.obj (typeOf w obj)))
  | none => genericGetDict obj

/-- `subtype_setdict`, `Objects/typeobject.c:4086`. -/
def subtypeSetdict (rt : Rt) (obj : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match builtinBaseWithDict w w.heap.size (typeOf w obj) with
  | some base =>
    match dictDescriptor w base with
    | none => raiseDictDescrError obj
    | some descr =>
      match slotOf w (typeOf w descr) .tp_descr_set with
      | none => raiseDictDescrError obj
      | some f => callDescrSet rt f descr obj value
  | none => objectSetDict obj value

/-- The getters of `func_getsetlist`, `Objects/funcobject.c:1060`. The fields hold the objects that
were assigned, and NULL reads as `None`, or `()` for `__type_params__`. -/
def functionAttrGet (rt : Rt) (obj : Val) (f : FuncData) (n : Name) : M Val := do
  if n == "__name__" then return f.nameObj.getD (.str f.name)
  if n == "__qualname__" then return f.qualnameObj.getD (.str f.qualname)
  if n == "__module__" then return f.module
  if n == "__doc__" then return f.doc
  if n == "__defaults__" then return f.defaultsObj.getD .none
  if n == "__kwdefaults__" then return f.kwdefaultsObj.getD .none
  if n == "__dict__" then return ← genericGetDict obj
  if n == "__annotate__" then return f.annotate.getD .none
  if n == "__annotations__" then
    match obj with
    | .obj fn => return ← funcGetAnnotations rt fn f
    | _ => gap%
  if n == "__type_params__" then return f.typeParams.getD (.tuple [])
  gap%

/-- The setters of `func_getsetlist`, `Objects/funcobject.c:1060`. -/
def functionAttrSet (obj : Val) (a : Addr) (f : FuncData) (n : Name) (value : Option Val) :
    M Unit := do
  let w ← getW
  let setF (g : FuncData) : M Unit := modObj a fun o => { o with body := .func g }
  if n == "__name__" then
    -- `func_set_name`, `Objects/funcobject.c:716`.
    match value with
    | some v =>
      match strOf w v with
      | some s => return ← setF { f with name := s, nameObj := some v }
      | none => typeErr "__name__ must be set to a string object"
    | none => typeErr "__name__ must be set to a string object"
  if n == "__qualname__" then
    -- `func_set_qualname`, `Objects/funcobject.c:743`.
    match value with
    | some v =>
      match strOf w v with
      | some s => return ← setF { f with qualname := s, qualnameObj := some v }
      | none => typeErr "__qualname__ must be set to a string object"
    | none => typeErr "__qualname__ must be set to a string object"
  if n == "__module__" then return ← setF { f with module := value.getD .none }
  if n == "__doc__" then return ← setF { f with doc := value.getD .none }
  if n == "__defaults__" then
    -- `func_set_defaults`, `Objects/funcobject.c:827`.
    match value with
    | none | some .none => return ← setF { f with defaults := [], defaultsObj := none }
    | some v =>
      match tupleOf w v with
      | some xs => return ← setF { f with defaults := xs, defaultsObj := some v }
      | none => typeErr "__defaults__ must be set to a tuple object"
  if n == "__kwdefaults__" then
    -- `func_set_kwdefaults`, `Objects/funcobject.c:875`.
    match value with
    | none | some .none => return ← setF { f with kwdefaultsObj := none }
    | some v =>
      match dictOf w v with
      | some _ => return ← setF { f with kwdefaultsObj := some v }
      | none => typeErr "__kwdefaults__ must be set to a dict object"
  if n == "__annotate__" then
    -- `function___annotate___set_impl`, `Objects/funcobject.c:934`.
    match value with
    | none => typeErr "__annotate__ cannot be deleted"
    | some v =>
      if v.is .none then return ← setF { f with annotate := some v }
      if excCallableCheck w v then
        return ← setF { f with annotate := some v, annotations := none }
      typeErr "__annotate__ must be callable or None"
  if n == "__annotations__" then
    -- `function___annotations___set_impl`, `Objects/funcobject.c:989`.
    let v := match value with
      | some x => if x.is .none then none else some x
      | none => none
    match v with
    | some x =>
      if (dictOf w x).isNone then typeErr "__annotations__ must be set to a dict object"
    | none => pure ()
    return ← setF { f with annotations := v, annotate := none }
  if n == "__type_params__" then
    -- `function___type_params___set_impl`, `Objects/funcobject.c:1035`.
    match value with
    | some x =>
      if (tupleOf w x).isNone then typeErr "__type_params__ must be set to a tuple"
      return ← setF { f with typeParams := some x }
    | none => typeErr "__type_params__ must be set to a tuple"
  if n == "__dict__" then return ← genericSetDict obj value
  gap%

/-- Getter of the `PyGetSetDef`/`PyMemberDef` named `n` on static type `owner`. -/
def getsetGetImpl (rt : Rt) (owner : Addr) (n : Name) (obj : Val) : M Val := do
  let w ← getW
  let tA := match obj with
    | .obj a => a
    | _ => 0
  if owner == B.object && n == "__class__" then return .obj (typeOf w obj)
  if owner == B.object && n == "__dict__" then return ← subtypeDict rt obj
  if owner == B.object && n == "__weakref__" then
    -- `subtype_getweakref`, `Objects/typeobject.c:4109`. Weak references are not modelled, and
    -- `tp_subclasses` holds one to every class.
    if (tdata w (typeOf w obj)).weaklistoffset == 0 then
      attrErr "This object has no __weakref__"
    if typeCheck w obj then gap%
    return .none
  if owner == B.type then
    let d := tdata w tA
    if n == "__name__" then return .str (if d.heap then d.name else typeShortName w tA)
    if n == "__qualname__" then return .str (typeQualname w tA)
    if n == "__bases__" then return .tuple (d.bases.map Val.obj)
    if n == "__mro__" then
      return match d.mro with
        | some m => .tuple (m.map Val.obj)
        | none => .none
    if n == "__base__" then
      return match d.base with
        | some b => .obj b
        | none => .none
    if n == "__module__" then
      if d.heap then
        match NameDict.get? d.dict "__module__" with
        | some m => return m
        | none => attrErr "__module__"
      else
        -- `type_module`, `Objects/typeobject.c`: what `tp_name` has before its last dot.
        let parts := d.name.splitOn "."
        return .str (if parts.length > 1 then ".".intercalate parts.dropLast else "builtins")
    if n == "__abstractmethods__" then
      if tA == B.type then attrErr "__abstractmethods__"
      match NameDict.get? d.dict "__abstractmethods__" with
      | some m => return m
      | none => attrErr "__abstractmethods__"
    if n == "__dict__" then return ← alloc B.mappingproxy (.typeDictProxy tA)
    if n == "__doc__" then return ← typeGetDoc rt tA
    if n == "__basicsize__" then return .int d.basicsize
    if n == "__itemsize__" then return .int d.itemsize
    if n == "__dictoffset__" then return .int d.dictoffset
    if n == "__weakrefoffset__" then return .int d.weaklistoffset
    if n == "__annotate__" then return ← typeGetAnnotate rt tA
    if n == "__annotations__" then return ← typeGetAnnotations rt tA
    if n == "__type_params__" then
      -- `type_get_type_params`, `Objects/typeobject.c:2351`.
      if tA == B.type then return .tuple []
      return (NameDict.get? d.dict "__type_params__").getD (.tuple [])
    gap%
  if owner == B.function then
    match payloadOf w obj with
    | some (.func f) => return ← functionAttrGet rt obj f n
    | _ => gap%
  if owner == B.method then
    match payloadOf w obj with
    | some (.bound f s) =>
      if n == "__func__" then return f
      if n == "__self__" then return s
      if n == "__doc__" then return ← rt.getAttr f "__doc__"
      gap%
    | _ => gap%
  if owner == B.classmethod || owner == B.staticmethod then
    let inner := match payloadOf w obj with
      | some (.classmethod f) | some (.staticmethod f) => f
      | _ => .none
    if n == "__func__" || n == "__wrapped__" then return inner
    if n == "__isabstractmethod__" then
      return .bool (← isAbstract rt inner)
    if n == "__dict__" then return ← genericGetDict obj
    if n == "__annotations__" || n == "__annotate__" then
      return ← wrappedAttrGet rt inner obj n
    gap%
  if owner == B.property then
    match propertyFields w obj with
    | some (g, s, d, doc, name, _) =>
      if n == "fget" then return g
      if n == "fset" then return s
      if n == "fdel" then return d
      if n == "__doc__" then return doc
      if n == "__name__" then
        match ← propertyName rt g name with
        | some x => return x
        | none => attrErr "'property' object has no attribute '__name__'"
      if n == "__isabstractmethod__" then
        if ← isAbstract rt g then return .bool true
        if ← isAbstract rt s then return .bool true
        return .bool (← isAbstract rt d)
      gap%
    | none => gap%
  if owner == B.super then
    match payloadOf w obj with
    | some (.super ty o ot) =>
      if n == "__thisclass__" then return (ty.map Val.obj).getD .none
      if n == "__self__" then return o.getD .none
      if n == "__self_class__" then return (ot.map Val.obj).getD .none
      gap%
    | _ => gap%
  if isSubtype w owner B.BaseException then return ← excGetsetGet rt owner n obj
  if owner == B.int then
    let i := (intOf w obj).getD 0
    if n == "real" || n == "numerator" then return .int i
    if n == "imag" then return .int 0
    if n == "denominator" then return .int 1
    gap%
  if owner == B.wrapperDescr || owner == B.methodDescr || owner == B.memberDescr ||
      owner == B.getsetDescr || owner == B.classmethodDescr then
    -- `d_type`, `d_name`, and `calculate_qualname`, `Objects/descrobject.c:593`.
    match descrInfo w obj with
    | some (o, nm) =>
      if n == "__objclass__" then return .obj o
      if n == "__name__" then return .str nm
      if n == "__qualname__" then return .str s!"{typeQualname w o}.{nm}"
      gap%
    | none => gap%
  if owner == B.builtinFn then
    match payloadOf w obj with
    | some (.builtin b self) =>
      match builtinName b with
      | none => gap%
      | some nm =>
        if n == "__name__" then return .str nm
        -- `m_self` of a function of `builtins` is that module, which the model does not have.
        if n == "__self__" then
          match self with
          | some s => return s
          | none => gap%
        if n == "__module__" then
          return match self with
            | some _ => .none
            | none => .str "builtins"
        if n == "__qualname__" then
          -- `meth_get__qualname__`, `Objects/methodobject.c:231`.
          match self with
          | none => return .str nm
          | some s =>
            let ty : Val := if typeCheck w s then s else .obj (typeOf w s)
            let q ← rt.getAttr ty "__qualname__"
            let w ← getW
            match strOf w q with
            | some t => return .str s!"{t}.{nm}"
            | none => typeErr "<method>.__class__.__qualname__ is not a unicode object"
        gap%
    | _ => gap%
  if owner == B.methodWrapper then
    -- `wrapper_objclass`, `wrapper_name`, `wrapper_qualname`, `Objects/descrobject.c:1411-1446`.
    match payloadOf w obj with
    | some (.methodWrapper d s) =>
      match payloadOf w d with
      | some (.wrapperDescr o p _) =>
        if n == "__self__" then return s
        if n == "__name__" then return .str p.name
        if n == "__objclass__" then return .obj o
        if n == "__qualname__" then return .str s!"{typeQualname w o}.{p.name}"
        gap%
      | _ => gap%
    | _ => gap%
  if owner == B.float then
    -- `float_getreal` and `float_getimag`, `Objects/floatobject.c`.
    match floatOf w obj with
    | some x =>
      if n == "real" then
        return ← if typeOf w obj == B.float then pure obj else mkFloat x
      if n == "imag" then return ← mkFloat (PyLean.Binary64.F64.zero false)
      gap%
    | none => gap%
  if owner == B.dictKeys && n == "mapping" then
    -- `dictview_mapping`, `Objects/dictobject.c:6457`.
    match payloadOf w obj with
    | some (.seqIter (some d) _) => return ← alloc B.mappingproxy (.proxy d)
    | _ => gap%
  gap%
where
  /-- `_PyObject_IsAbstract`, `Objects/object.c:1252`. -/
  isAbstract (rt : Rt) (o : Val) : M Bool := do
    match o with
    | .none => pure false
    | _ =>
      match ← rt.getOptionalAttr o "__isabstractmethod__" with
      | some x => rt.isTrue x
      | none => pure false

/-- Setter of the `PyGetSetDef`/`PyMemberDef` named `n` on static type `owner`. -/
def getsetSetImpl (rt : Rt) (owner : Addr) (n : Name) (obj : Val) (value : Option Val) :
    M Unit := do
  let w ← getW
  let tA := match obj with
    | .obj a => a
    | _ => 0
  if owner == B.object && n == "__class__" then return ← objectSetClass rt obj value
  if owner == B.object && n == "__dict__" then return ← subtypeSetdict rt obj value
  if owner == B.type then
    if n == "__name__" then
      checkSetSpecial tA value "__name__"
      match value with
      | some v =>
        match strOf w v with
        | none =>
          typeErr s!"can only assign string to {tpName w tA}.__name__, not '{typeName w v}'"
        | some s =>
          if s.contains (Char.ofNat 0) then
            valueErr "type name must not contain null characters"
          return ← modType tA fun d => { d with name := s }
      | none => gap%
    if n == "__qualname__" then
      checkSetSpecial tA value "__qualname__"
      match value with
      | some v =>
        match strOf w v with
        | none =>
          typeErr s!"can only assign string to {tpName w tA}.__qualname__, not '{typeName w v}'"
        | some s => return ← modType tA fun d => { d with qualname := s }
      | none => gap%
    if n == "__module__" then
      checkSetSpecial tA value "__module__"
      return ← modType tA fun d =>
        let nd := NameDict.set (NameDict.erase d.dict "__firstlineno__") "__module__" (value.getD .none)
        { d with dict := nd }
    if n == "__doc__" then
      checkSetSpecial tA value "__doc__"
      return ← modType tA fun d => { d with dict := NameDict.set d.dict "__doc__" (value.getD .none) }
    if n == "__bases__" then return ← typeSetBases rt tA value
    if n == "__abstractmethods__" then
      match value with
      | some v =>
        let abs ← rt.isTrue v
        return ← modType tA fun d =>
          { d with dict := NameDict.set d.dict "__abstractmethods__" v, isAbstract := abs }
      | none =>
        if !NameDict.contains (tdata w tA).dict "__abstractmethods__" then
          attrErr "__abstractmethods__"
        return ← modType tA fun d =>
          { d with dict := NameDict.erase d.dict "__abstractmethods__", isAbstract := false }
    if n == "__annotate__" then return ← typeSetAnnotate tA value
    if n == "__annotations__" then return ← typeSetAnnotations tA value
    if n == "__type_params__" then
      -- `type_set_type_params`, `Objects/typeobject.c:2366`.
      checkSetSpecial tA value "__type_params__"
      return ← modType tA fun d =>
        { d with dict := NameDict.set d.dict "__type_params__" (value.getD .none) }
    gap%
  if owner == B.classmethod || owner == B.staticmethod then
    if n == "__annotations__" || n == "__annotate__" then
      let tn := if owner == B.classmethod then "classmethod" else "staticmethod"
      return ← wrappedAttrSet rt obj n value tn
    if n == "__dict__" then return ← genericSetDict obj value
    gap%
  if owner == B.function then
    match payloadOf w obj, obj with
    | some (.func f), .obj a => return ← functionAttrSet obj a f n value
    | _, _ => gap%
  if isSubtype w owner B.BaseException then return ← excGetsetSet rt owner n obj value
  if owner == B.property then
    match payloadOf w obj, obj with
    | some (.property g s d doc name gd), .obj a =>
      if n == "__doc__" then
        return ← modObj a fun o =>
          { o with body := .property g s d (value.getD .none) name gd }
      if n == "__name__" then
        return ← modObj a fun o => { o with body := .property g s d doc value gd }
      gap%
    | _, _ => gap%
  gap%

/-! ## `PyObject_Call` -/

/-- `slot_tp_call`, `Objects/typeobject.c:11042`. -/
def slotTpCall (rt : Rt) (self : Val) (args : List Val) (kw : Kw) : M Val :=
  callMethod rt self "__call__" args kw

/-- `method_check_args`, `Objects/descrobject.c:267`. -/
def methodCheckArgs (owner : Addr) (name : Name) (args : List Val) (kw : Kw) : M Unit := do
  let w ← getW
  let fs := s!"{tpName w owner}.{name}()"
  match args with
  | [] => typeErr s!"unbound method {fs} needs an argument"
  | self :: _ =>
    descrCheck owner name self
    unless kw.isEmpty do typeErr s!"{fs} takes no keyword arguments"

/-- Apply the `tp_call` function `s` to `f`. -/
def callTpCall (rt : Rt) (s : SlotFn) (f : Val) (args : List Val) (kw : Kw) : M Val := do
  let w ← getW
  match s with
  | .generic => slotTpCall rt f args kw
  | .c .type =>
    match f with
    | .obj t =>
      -- `tp_vectorcall` is not inherited, so only exact `super` goes this way.
      typeCall rt t args kw
    | _ => gap%
  | .c .function =>
    match payloadOf w f with
    | some (.func fd) => functionCall rt f fd args kw
    | _ => gap%
  | .c .method =>
    match payloadOf w f with
    | some (.bound func self) => rt.call func (self :: args) kw
    | _ => gap%
  | .c .builtinFn =>
    match payloadOf w f with
    | some (.builtin b self) => callBuiltin rt b self args kw
    | _ => gap%
  | .c .wrapperDescr =>
    match payloadOf w f with
    | some (.wrapperDescr o p g) => wrapperdescrCall rt o p g args kw
    | _ => gap%
  | .c .methodWrapper =>
    match payloadOf w f with
    | some (.methodWrapper d self) =>
      match payloadOf w d with
      | some (.wrapperDescr _ p g) => wrapperApply rt p g self args kw
      | _ => gap%
    | _ => gap%
  | .c .methodDescr =>
    match payloadOf w f with
    | some (.methodDescr o n b) =>
      -- A stub's calling convention is not known, so what it says of keywords is not either.
      methodCheckArgs o n args (match b with
        | .stub _ => []
        | _ => kw)
      callBuiltin rt b (some (args.headD .none)) (args.drop 1) kw (some o)
    | _ => gap%
  | .c .classmethodDescr =>
    match payloadOf w f with
    | some (.classmethodDescr o n b) =>
      match args with
      | [] => typeErr s!"descriptor '{n}' of '{trunc 100 (tpName w o)}' object needs an argument"
      | self :: rest =>
        let bound ← classmethodGet o n b none (some self)
        rt.call bound rest kw
    | _ => gap%
  | .c .staticmethod =>
    match payloadOf w f with
    | some (.staticmethod g) => rt.call g args kw
    | _ => gap%
  | _ => gap%

/-- `_PyObject_Call`, `Objects/call.c:333`, on the `tp_call` slot; the vectorcall entry
points of functions and methods behave the same. -/
def pyCall (rt : Rt) (f : Val) (args : List Val) (kw : Kw) : M Val := do
  let w ← getW
  let tp := typeOf w f
  match slotOf w tp .tp_call with
  | none => typeErr s!"'{trunc 200 (tpName w tp)}' object is not callable"
  | some s =>
    -- `tp_vectorcall`: a direct call of `super` or `type`, not `type.__call__`, which is
    -- `type_call`. It is not inherited, so a subclass goes through `tp_new` and `tp_init`.
    match f with
    | .obj t =>
      if t == B.super then superVectorcall rt args kw
      else if t == B.type && args.length == 1 && !kw.isEmpty then
        typeErr "type() takes no keyword arguments"
      else callTpCall rt s f args kw
    | _ => callTpCall rt s f args kw

end PyLean.TypeObj
