import PyLean.TypeObj.TypeNew

/-!
Calling: function argument binding (`initialize_locals`, `Python/ceval.c:1681`), `tp_new`
and `tp_init` of the builtin types, `object_new`/`object_init`, `type_call`, the slot
wrappers of `Objects/typeobject.c:9264-9818`, `tp_new_wrapper`, bound methods, builtin
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

/-- Index of `n` in `names`, from `start`: the keyword search at `Python/ceval.c:1765`. -/
def findParam (names : List Name) (start : Nat) (n : Name) : Option Nat :=
  ((names.drop start).findIdx? (· == n)).map (· + start)

/-- `format_missing`, `Python/ceval.c:1389`. -/
def formatMissing (kind qualname : String) (names : List String) : String :=
  let nameStr := match names with
    | [a] => a
    | [a, b] => s!"{a} and {b}"
    | _ =>
      let n := names.length
      let tail := s!", {names[n - 2]!}, and {names[n - 1]!}"
      ", ".intercalate (names.take (n - 2)) ++ tail
  s!"{qualname}() missing {names.length} required {kind} argument{if names.length == 1 then "" else "s"}: {nameStr}"

/-- `missing_arguments`, `Python/ceval.c:1452`. `defcount = none` is keyword-only. -/
def missingArguments (f : FuncData) (slots : List (Option Val)) (defcount : Option Nat) : String :=
  let (kind, start, stop) := match defcount with
    | some d => ("positional", 0, f.argcount - d)
    | none => ("keyword-only", f.argcount, f.argcount + f.kwonly)
  let idx := (List.range (stop - start)).map (· + start)
  let miss := idx.filter fun i => (slots.getD i none).isNone
  formatMissing kind f.qualname (miss.map fun i => reprStr (f.varnames.getD i ""))

/-- `atleast`, `Python/ceval.c:1510`. -/
def tooManyAtLeast (f : FuncData) : Int := (f.argcount : Int) - f.defaults.length

/-- `too_many_positional`, `Python/ceval.c:1491`. -/
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

/-- `positional_only_passed_as_keyword`, `Python/ceval.c:1549`. -/
def posonlyConflicts (f : FuncData) (kw : Kw) : List Name :=
  (f.varnames.take f.posonly).flatMap fun p => (kw.filter (·.1 == p)).map (·.1)

/-- Handle one keyword, `Python/ceval.c:1749-1845`. -/
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

/-- The `for` loop over keywords, `Python/ceval.c:1749`. -/
def bindKeywords (f : FuncData) (allKw : Kw) : Bound → Kw → Except String Bound
  | b, [] => .ok b
  | b, kv :: rest =>
    match bindKeyword f allKw b kv with
    | .ok b' => bindKeywords f allKw b' rest
    | .error e => .error e

/-- Fill defaults for positional parameters, `Python/ceval.c:1856-1883`. `m` is a signed
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

/-- Fill keyword-only defaults, `Python/ceval.c:1886-1909`. -/
def fillKwdefaults (f : FuncData) (b : Bound) : Except String Bound :=
  if f.kwonly > 0 then
    let idx := (List.range f.kwonly).map (· + f.argcount)
    let slots := idx.foldl (fun s i =>
      if (s.getD i none).isSome then s
      else match NameDict.get? f.kwdefaults (f.varnames.getD i "") with
        | some d => s.set i (some d)
        | none => s) b.slots
    let b' := { b with slots := slots }
    if idx.any fun i => (slots.getD i none).isNone then
      .error (missingArguments f slots none)
    else .ok b'
  else .ok b

/-- `initialize_locals`, `Python/ceval.c:1681`. The error string is the `TypeError`
message. Keyword names are strings, so the `keywords must be strings` branch is outside
this signature; a "Did you mean" suggestion (`_Py_CalculateSuggestions`) is not
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
      match fillDefaults f args.length n b1 with
      | .error e => .error e
      | .ok b2 => fillKwdefaults f b2

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
    let kwv ←
      if f.hasVarkw then
        some <$> alloc B.dict (.dict (b.kwdict.map fun (k, v) => (Val.str k, v)))
      else pure none
    rt.exec f.code self (boundLocals f b kwv)

/-! ## `tp_new`, `tp_init` -/

/-- `excess_args`, `Objects/typeobject.c:6825`. -/
def excessArgs (args : List Val) (kw : Kw) : Bool := !args.isEmpty || !kw.isEmpty

/-- `object_init`, `Objects/typeobject.c:6832`. -/
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

/-- `join(sorted(names))` of the abstract method error, `Objects/typeobject.c:6874-6892`. -/
def abstractNames (rt : Rt) (t : Addr) : M (List String) := do
  let w ← getW
  match NameDict.get? (tdata w t).dict "__abstractmethods__" with
  | none => raiseC B.AttributeError "__abstractmethods__"
  | some am =>
    let items ← pySequenceList rt am
    let w ← getW
    let names := items.filterMap (strOf w)
    if names.length != items.length then
      -- `PyList_Sort` of mixed or non-str items, then `PyUnicode_Join`.
      match items.findIdx? (fun x => (strOf w x).isNone) with
      | some i =>
        typeErr s!"sequence item {i}: expected str instance, {trunc 80 (typeName w (items.getD i .none))} found"
      | none => unmodelled
    pure (names.mergeSort fun a b => decide (strCompare a.toList b.toList ≤ 0))

/-- `object_new`, `Objects/typeobject.c:6852`. -/
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

/-- Allocate a subclass instance holding builtin value `v`, as `long_subtype_new` and
friends do; the exact type stays immediate. -/
def boxValue (t exact : Addr) (v : Val) : M Val :=
  if t == exact then pure v else alloc t (.boxed v)

/-- `long_new`, `Objects/longobject.c`: one positional argument. -/
def longNew (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  if !kw.isEmpty then unmodelled
  match args with
  | [] => boxValue t B.int (.int 0)
  | [x] =>
    let r ← pyNumberLong rt x
    boxValue t B.int r
  | [_, _] => typeErr "int() can't convert non-string with explicit base"
  | _ => typeErr s!"int expected at most 2 arguments, got {args.length}"

/-- `bool_new`, `Objects/boolobject.c`. -/
def boolNew (rt : Rt) (args : List Val) (kw : Kw) : M Val := do
  noKeywords "bool" kw
  unpackTuple "bool" 0 1 args.length
  match args with
  | [] => pure (.bool false)
  | x :: _ => .bool <$> rt.isTrue x

/-- `unicode_new` with one or no argument. -/
def strNew (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  if !kw.isEmpty then unmodelled
  match args with
  | [] => boxValue t B.str (.str "")
  | [x] =>
    let s ← rt.str x
    boxValue t B.str (.str s)
  | _ => unmodelled

/-- `tuple_new`, `Objects/tupleobject.c`. -/
def tupleNew (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  if t == B.tuple then noKeywords "tuple" kw
  else if !kw.isEmpty then unmodelled
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
    let xs ← pySequenceList rt x
    modObj a fun o => { o with body := .list xs }
  | _, _ => unmodelled

/-- `dict_init` with no argument or a dict argument, and string keywords. -/
def dictInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  let w ← getW
  unpackTuple "dict" 0 1 args.length
  let base ← match args with
    | [] => pure []
    | x :: _ =>
      match dictOf w x with
      | some es => pure es
      | none => unmodelled
  let all := kw.foldl (fun es (k, v) => dictSetEntry es (.str k) v) base
  match self with
  | .obj a => modObj a fun o => { o with body := .dict all }
  | _ => unmodelled

/-- `property_init_impl`, `Objects/descrobject.c:1837`, with the clinic argument
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
  | _ => unmodelled

/-- `functools_wraps`, `Objects/funcobject.c:1403`: copy `__module__`, `__name__`,
`__qualname__`, `__doc__` onto the wrapper, then its `__dict__` gets `__wrapped__`... in
3.14 the function copies four attributes through `functools_copy_attr`. -/
def functoolsWraps (rt : Rt) (wrapper wrapped : Val) : M Unit := do
  for n in ["__module__", "__name__", "__qualname__", "__doc__"] do
    match ← rt.getOptionalAttr wrapped n with
    | some v => rt.setAttr wrapper n (some v)
    | none => pure ()

/-- `cm_init`, `sm_init`, `Objects/funcobject.c:1574`, `:1818`. -/
def descrWrapInit (rt : Rt) (name : String) (self : Val) (args : List Val) (kw : Kw)
    (mk : Val → Payload) : M Unit := do
  noKeywords name kw
  unpackTuple name 1 1 args.length
  match args, self with
  | [c], .obj a =>
    modObj a fun o => { o with body := mk c }
    functoolsWraps rt self c
  | _, _ => unmodelled

/-- `super_init`/`super_init_impl`, `Objects/typeobject.c:12150`, `:12166`, with two
explicit arguments. Zero-argument `super()` needs the caller's frame: see `superZero`. -/
def superInit (rt : Rt) (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  noKeywords "super" kw
  let w ← getW
  match args.length with
  | 0 => runtimeErr "super(): no current frame"
  | 1 | 2 =>
    let arg0 := args.headD .none
    match asType w arg0 with
    | none => typeErr s!"super() argument 1 must be a type, not {trunc 200 (typeName w arg0)}"
    | some ty =>
      let obj := match args with
        | [_, o] => if o.is .none then none else some o
        | _ => none
      let objType ← match obj with
        | some o => some <$> supercheck rt ty o
        | none => pure none
      match self with
      | .obj a => modObj a fun o => { o with body := .super (some ty) obj objType }
      | _ => unmodelled
  | n => typeErr s!"super() expected at most 2 arguments, got {n}"

/-- `slot_tp_new`, `Objects/typeobject.c:10587`. -/
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
  | .c .str => strNew rt t args kw
  | .c .tuple => tupleNew rt t args kw
  | .c .list | .c .dict | .c .property | .c .classmethod | .c .staticmethod | .c .super =>
    alloc t (freshBody w t)
  | .c .none =>
    if excessArgs args kw then typeErr "NoneType takes no arguments" else pure .none
  | .c .notImpl =>
    if excessArgs args kw then typeErr "NotImplementedType takes no arguments" else pure .notImpl
  | .c e => if isExcFamily e then excTpNew rt e t args kw else unmodelled
  | _ => unmodelled

/-- `type_init`, `Objects/typeobject.c:3883`. -/
def typeInit (args : List Val) (kw : Kw) : M Unit := do
  if !kw.isEmpty && args.length == 1 then
    typeErr "type.__init__() takes no keyword arguments"
  if args.length != 1 && args.length != 3 then
    typeErr "type.__init__() takes 1 or 3 arguments"

/-- `slot_tp_init`, `Objects/typeobject.c:10570`. -/
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
  | .c .dict => dictInit self args kw
  | .c .property => propertyInit rt self args kw
  | .c .classmethod => descrWrapInit rt "classmethod" self args kw .classmethod
  | .c .staticmethod => descrWrapInit rt "staticmethod" self args kw .staticmethod
  | .c .super => superInit rt self args kw
  | .c e => if isExcFamily e then excTpInit rt e self args kw else unmodelled
  | _ => unmodelled

/-- `type_call`, `Objects/typeobject.c:2331`. -/
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

/-- `tp_new_wrapper`, `Objects/typeobject.c:9821`. -/
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
      -- staticbase: the most derived base that is not a heap type, :9862
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
      | none => unmodelled

/-! ## Slot wrappers -/

/-- The message of `check_num_args`, `Objects/typeobject.c:9229`. -/
def argCountMsg (n got : Nat) : String :=
  s!"expected {n} argument{if n == 1 then "" else "s"}, got {got}"

/-- `check_num_args`, `Objects/typeobject.c:9220`. -/
def checkNumArgs (args : List Val) (n : Nat) : M Unit := do
  unless args.length == n do
    typeErr (argCountMsg n args.length)

/-- `wrap_*` arity: `check_pow_args`, `Objects/typeobject.c:9236`. -/
def checkPowArgs (args : List Val) : M Unit := do
  unless args.length == 1 || args.length == 2 do
    typeErr s!"expected 1 or 2 arguments, got {args.length}"

/-- `getindex`, `Objects/typeobject.c:9397`. -/
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

/-- The slot-compare in `hackcheck_unlocked`, `Objects/typeobject.c:9530`. -/
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
(`PyObject_GenericGetAttr`, `Objects/object.c:1823`). -/
def attrName (v : Val) : M Name := do
  let w ← getW
  match strOf w v with
  | some s => pure s
  | none => typeErr s!"attribute name must be string, not '{trunc 200 (typeName w v)}'"

/-- A one-operand wrapped slot, `wrap_unaryfunc`, `Objects/typeobject.c:9371`. -/
def wrapUnary (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) : M Val := do
  match p.slot with
  | .tp_repr => callRepr rt f self
  | .tp_str => callStr rt f self
  | .tp_iter => callIter rt f self
  | .nb_negative | .nb_positive | .nb_absolute | .nb_invert | .nb_int | .nb_index =>
    callUnaryNb rt p.slot p.name f self
  | .nb_float =>
    match f with
    | .generic => vectorcallMethod rt "__float__" [self]
    | _ => unmodelled
  | .am_await | .am_aiter | .am_anext => unmodelled
  | _ => unmodelled

/-- `wrapperdescr_raw_call`'s dispatch on the wrapper function,
`Objects/typeobject.c:9264-9818`. -/
def wrapperApply (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) (args : List Val)
    (kw : Kw) : M Val := do
  match p.wrapper with
  | none => unmodelled
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
      | .sq_inplace_concat => unmodelled
      | s =>
        if s.group == .number then
          match f, wr with
          | .generic, .binary => vectorcallMethod rt p.name [self, other]
          | _, _ => callNbBinary rt s f self other
        else unmodelled
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
        | _ => unmodelled
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
      let n ← attrName (args.headD .none)
      callSetattro rt f self n (some (args.getD 1 .none))
      pure .none
    | .delattr =>
      checkNumArgs args 1
      hackcheck self f "__delattr__"
      let n ← attrName (args.headD .none)
      callSetattro rt f self n none
      pure .none
    | .indexArg =>
      checkNumArgs args 1
      let i ← numberAsSsize rt (args.headD .none) (some B.OverflowError)
      callSqRepeat f self i
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
    | _ => unmodelled

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

/-- `object.__dir__` and `type.__dir__`: `merge_class_dict`, `Objects/typeobject.c:6524`,
over the static hierarchy. -/
def classDictKeys (w : World) (t : Addr) : List Name :=
  ((tdata w t).mro.getD []).flatMap fun c => (tdata w c).dict.map (·.1)

/-- `object___format___impl`, `Objects/typeobject.c:7875`. -/
def objectFormat (rt : Rt) (self : Val) (spec : String) : M Val := do
  let w ← getW
  if spec.length > 0 then
    typeErr s!"unsupported format string passed to {trunc 200 (typeName w self)}.__format__"
  .str <$> rt.str self

/-- `PyObject_Format`, `Objects/abstract.c:843`. -/
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
    | none => typeErr s!"__format__ must return a str, not {trunc 200 (typeName w r)}"

/-- `dir(obj)` for the object protocol, `_dir_object`, `Objects/object.c:2156`. -/
def pyDir (rt : Rt) (obj : Val) : M Val := do
  let w ← getW
  match ← lookupSpecial rt obj "__dir__" with
  | none => typeErr "object does not provide __dir__"
  | some d =>
    let r ← rt.call d [] []
    let items ← pySequenceList rt r
    let w' ← getW
    let names := items.filterMap (strOf w')
    if names.length != items.length then unmodelled
    let sorted := names.mergeSort fun a b => decide (strCompare a.toList b.toList ≤ 0)
    let _ := w
    alloc B.list (.list (sorted.map Val.str))

/-- The `doc` argument of `property_copy`, `Objects/descrobject.c:1780-1786`. -/
def copyDocArg (getterDoc : Bool) (g doc : Val) : Val :=
  if getterDoc && !g.is .none then .none else doc

/-- `property_copy`, `Objects/descrobject.c:1762`. -/
def propertyCopy (rt : Rt) (old : Val) (get set del : Option Val) : M Val := do
  let w ← getW
  match propertyFields w old with
  | none => unmodelled
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

/-- `type_mro_impl`, `Objects/typeobject.c:3434`. -/
def typeMroImpl (rt : Rt) (self : Val) : M Val := do
  match self with
  | .obj t =>
    let m ← mroImplementation rt t
    alloc B.list (.list (m.map Val.obj))
  | _ => unmodelled

/-- The calling convention of a builtin: `METH_NOARGS`, `METH_O`, `METH_FASTCALL` without
keywords, or keywords accepted. -/
inductive MethConv where
  | noargs | o | fast | keywords

/-- `ml_name` and `ml_flags` of a `Builtin`. -/
def builtinConv : Builtin → String × MethConv
  | .objectInitSubclass => ("__init_subclass__", .noargs)
  | .objectSubclasshook => ("__subclasshook__", .o)
  | .objectFormat => ("__format__", .o)
  | .objectDir => ("__dir__", .noargs)
  | .objectSizeof => ("__sizeof__", .noargs)
  | .objectGetstate => ("__getstate__", .noargs)
  | .objectReduce => ("__reduce__", .noargs)
  | .objectReduceEx => ("__reduce_ex__", .o)
  | .classGetitem => ("__class_getitem__", .o)
  | .typeMro => ("mro", .noargs)
  | .typeSubclasses => ("__subclasses__", .noargs)
  | .typeInstancecheck => ("__instancecheck__", .o)
  | .typeSubclasscheck => ("__subclasscheck__", .o)
  | .typeDir => ("__dir__", .noargs)
  | .typeSizeof => ("__sizeof__", .noargs)
  | .isinstance => ("isinstance", .fast)
  | .issubclass => ("issubclass", .fast)
  | .getattr => ("getattr", .fast)
  | .setattr => ("setattr", .fast)
  | .delattr => ("delattr", .fast)
  | .hasattr => ("hasattr", .fast)
  | .len => ("len", .o)
  | .iter => ("iter", .fast)
  | .next => ("next", .fast)
  | .repr => ("repr", .o)
  | .hash => ("hash", .o)
  | .callable => ("callable", .o)
  | .dir => ("dir", .fast)
  | .abs => ("abs", .o)
  | .divmod => ("divmod", .fast)
  | .format => ("format", .fast)
  | .propertyGetter => ("getter", .o)
  | .propertySetter => ("setter", .o)
  | .propertyDeleter => ("deleter", .o)
  | .listAppend => ("append", .o)
  | .dunderGetitem => ("__getitem__", .o)
  | .dunderContains => ("__contains__", .o)
  | _ => ("", .keywords)

/-- `_PyObject_FunctionStr` of a builtin, `Objects/object.c:959`, via `meth_get__qualname__`,
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
def checkBuiltinArgs (b : Builtin) (self : Option Val) (args : List Val) (kw : Kw) : M Unit := do
  let w ← getW
  let (n, conv) := builtinConv b
  let fs := builtinFuncStr w n self
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

/-- Call a `Builtin`. `self` is `m_self`; methods receive their instance there. -/
def callBuiltin (rt : Rt) (b : Builtin) (self : Option Val) (args : List Val) (kw : Kw) :
    M Val := do
  checkBuiltinArgs b self args kw
  let w ← getW
  let selfV := self.getD .none
  match b with
  | .stub _ => unmodelled
  | .excMethod n => excMethod rt n selfV args kw
  | .tpNewWrapper ty => tpNewWrapper rt ty args kw
  | .objectInitSubclass => pure .none
  | .objectSubclasshook => pure .notImpl
  | .classGetitem => alloc B.genericAlias .plain
  | .objectFormat =>
    match args with
    | [s] =>
      match strOf w s with
      | some sp => objectFormat rt selfV sp
      | none => typeErr s!"__format__() argument must be str, not {typeName w s}"
    | _ => unmodelled
  | .objectDir =>
    let inst : List Val := match instDictAddr w selfV with
      | some da => ((dictOf w (.obj da)).getD []).map (·.1)
      | none => []
    let keys := inst ++ (classDictKeys w (typeOf w selfV)).map Val.str
    let names := keys.filterMap (strOf w)
    alloc B.list (.list (names.eraseDups.map Val.str))
  | .typeDir =>
    match selfV with
    | .obj t => alloc B.list (.list ((classDictKeys w t).eraseDups.map Val.str))
    | _ => unmodelled
  | .typeMro => typeMroImpl rt selfV
  | .typeSubclasses =>
    match selfV with
    | .obj t => alloc B.list (.list ((tdata w t).subclasses.map Val.obj))
    | _ => unmodelled
  | .typePrepare => alloc B.dict (.dict [])
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
    | _ => unmodelled
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
    | _ => unmodelled
  | .callable =>
    match args with
    | [o] => pure (.bool (slotOf w (typeOf w o) .tp_call).isSome)
    | _ => typeErr s!"callable() takes exactly one argument ({args.length} given)"
  | .dir =>
    match args with
    | [o] => pyDir rt o
    | _ => unmodelled
  | .abs =>
    match args with
    | [o] => pyNumberAbsolute rt o
    | _ => typeErr s!"abs() takes exactly one argument ({args.length} given)"
  | .divmod =>
    match args with
    | [a, c] => binaryOp rt a c .nb_divmod "divmod()"
    | _ => typeErr s!"divmod expected 2 arguments, got {args.length}"
  | .pow =>
    match args with
    | [a, c] => pyNumberPower rt a c .none
    | [a, c, m] => pyNumberPower rt a c m
    | _ => unmodelled
  | .format =>
    match args with
    | [o] => pyFormat rt o none
    | [o, s] => pyFormat rt o (some s)
    | _ => unmodelled
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
      | none => unmodelled
    | _ => typeErr s!"__getitem__() takes exactly one argument ({args.length} given)"
  | .dunderContains =>
    match args with
    | [k] => .bool <$> callContains rt (.c .dict) selfV k
    | _ => typeErr s!"__contains__() takes exactly one argument ({args.length} given)"
  | .listAppend =>
    match args, selfV with
    | [x], .obj a =>
      modObj a fun o =>
        match o.body with
        | .list xs => { o with body := .list (xs ++ [x]) }
        | _ => o
      pure .none
    | _, _ => unmodelled
  | _ => unmodelled

/-! ## Getsets and static members -/

/-- `type_get_doc`, `Objects/typeobject.c:1951`, for heap types. -/
def typeGetDoc (rt : Rt) (t : Addr) : M Val := do
  let w ← getW
  match NameDict.get? (tdata w t).dict "__doc__" with
  | none => pure .none
  | some r =>
    match slotOf w (typeOf w r) .tp_descr_get with
    | some g => callDescrGet rt g r none (some (.obj t))
    | none => pure r

/-- `_PyType_Name`: the part after the last dot. -/
def typeShortName (w : World) (t : Addr) : String := typeQualname w t

/-- The `__dict__` getter of an instance, `subtype_dict`, `Objects/typeobject.c:3742`,
via `PyObject_GenericGetDict`, `Objects/dictobject.c:7607`. -/
def genericGetDict (obj : Val) : M Val := do
  let w ← getW
  if hasDictPtr w obj then
    let d ← ensureDict obj
    pure (.obj d)
  else attrErr "This object has no __dict__"

/-- `_PyObject_SetDict`, `Objects/typeobject.c:3765`. -/
def objectSetDict (obj : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match value with
  | none =>
    match obj with
    | .obj a => modObj a fun o => { o with dict := none }
    | _ => unmodelled
  | some v =>
    match dictOf w v, v, obj with
    | some _, .obj d, .obj a => modObj a fun o => { o with dict := some d }
    | _, _, _ =>
      typeErr s!"__dict__ must be set to a dictionary, not a '{trunc 200 (typeName w v)}'"

/-- Getter of the `PyGetSetDef`/`PyMemberDef` named `n` on static type `owner`. -/
def getsetGetImpl (rt : Rt) (owner : Addr) (n : Name) (obj : Val) : M Val := do
  let w ← getW
  let tA := match obj with
    | .obj a => a
    | _ => 0
  if owner == B.object && n == "__class__" then return .obj (typeOf w obj)
  if (tdata w owner).heap then
    if n == "__dict__" then return ← genericGetDict obj
    if n == "__weakref__" then
      if (tdata w (typeOf w obj)).weaklistoffset == 0 then
        attrErr "This object has no __weakref__"
      return .none
    unmodelled
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
      else return .str "builtins"
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
    unmodelled
  if owner == B.function then
    match payloadOf w obj with
    | some (.func f) =>
      if n == "__name__" then return .str f.name
      if n == "__qualname__" then return .str f.qualname
      if n == "__module__" then return f.module
      if n == "__doc__" then return f.doc
      if n == "__defaults__" then
        return if f.defaultsSet then .tuple f.defaults else .none
      if n == "__kwdefaults__" then
        return ← if f.kwdefaultsSet then
            alloc B.dict (.dict (f.kwdefaults.map fun (k, v) => (Val.str k, v)))
          else pure .none
      if n == "__dict__" then return ← genericGetDict obj
      unmodelled
    | _ => unmodelled
  if owner == B.method then
    match payloadOf w obj with
    | some (.bound f s) =>
      if n == "__func__" then return f
      if n == "__self__" then return s
      if n == "__doc__" then return ← rt.getAttr f "__doc__"
      unmodelled
    | _ => unmodelled
  if owner == B.classmethod || owner == B.staticmethod then
    let inner := match payloadOf w obj with
      | some (.classmethod f) | some (.staticmethod f) => f
      | _ => .none
    if n == "__func__" || n == "__wrapped__" then return inner
    if n == "__isabstractmethod__" then
      return .bool (← isAbstract rt inner)
    if n == "__dict__" then return ← genericGetDict obj
    unmodelled
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
      unmodelled
    | none => unmodelled
  if owner == B.super then
    match payloadOf w obj with
    | some (.super ty o ot) =>
      if n == "__thisclass__" then return (ty.map Val.obj).getD .none
      if n == "__self__" then return o.getD .none
      if n == "__self_class__" then return (ot.map Val.obj).getD .none
      unmodelled
    | _ => unmodelled
  if isSubtype w owner B.BaseException then return ← excGetsetGet rt owner n obj
  if owner == B.int then
    let i := (intOf w obj).getD 0
    if n == "real" || n == "numerator" then return .int i
    if n == "imag" then return .int 0
    if n == "denominator" then return .int 1
    unmodelled
  if owner == B.wrapperDescr || owner == B.methodDescr then
    match payloadOf w obj with
    | some (.wrapperDescr o p _) =>
      if n == "__objclass__" then return .obj o
      if n == "__name__" then return .str p.name
      unmodelled
    | some (.methodDescr o nm _) =>
      if n == "__objclass__" then return .obj o
      if n == "__name__" then return .str nm
      unmodelled
    | _ => unmodelled
  unmodelled
where
  /-- `_PyObject_IsAbstract`, `Objects/object.c:1235`. -/
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
  if owner == B.object && n == "__class__" then return ← objectSetClass obj value
  if (tdata w owner).heap then
    if n == "__dict__" then return ← objectSetDict obj value
    unmodelled
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
      | none => unmodelled
    if n == "__qualname__" then
      checkSetSpecial tA value "__qualname__"
      match value with
      | some v =>
        match strOf w v with
        | none =>
          typeErr s!"can only assign string to {tpName w tA}.__qualname__, not '{typeName w v}'"
        | some s => return ← modType tA fun d => { d with qualname := s }
      | none => unmodelled
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
    unmodelled
  if owner == B.function then
    match payloadOf w obj, obj with
    | some (.func f), .obj a =>
      let setF (g : FuncData) : M Unit := modObj a fun o => { o with body := .func g }
      if n == "__name__" then
        match value with
        | some v =>
          match strOf w v with
          | some s => return ← setF { f with name := s }
          | none => typeErr "__name__ must be set to a string object"
        | none => typeErr "__name__ must be set to a string object"
      if n == "__qualname__" then
        match value with
        | some v =>
          match strOf w v with
          | some s => return ← setF { f with qualname := s }
          | none => typeErr "__qualname__ must be set to a string object"
        | none => typeErr "__qualname__ must be set to a string object"
      if n == "__module__" then return ← setF { f with module := value.getD .none }
      if n == "__doc__" then return ← setF { f with doc := value.getD .none }
      if n == "__defaults__" then
        match value with
        | none | some .none => return ← setF { f with defaults := [], defaultsSet := false }
        | some v =>
          match tupleOf w v with
          | some xs => return ← setF { f with defaults := xs, defaultsSet := true }
          | none => typeErr "__defaults__ must be set to a tuple object"
      if n == "__kwdefaults__" then
        match value with
        | none | some .none => return ← setF { f with kwdefaults := [], kwdefaultsSet := false }
        | some v =>
          match dictOf w v with
          | some es =>
            let d := es.filterMap fun (k, x) =>
              match k with
              | .str n => some (n, x)
              | _ => none
            return ← setF { f with kwdefaults := d, kwdefaultsSet := true }
          | none => typeErr "__kwdefaults__ must be set to a dict object"
      unmodelled
    | _, _ => unmodelled
  if isSubtype w owner B.BaseException then return ← excGetsetSet rt owner n obj value
  if owner == B.property then
    match payloadOf w obj, obj with
    | some (.property g s d doc name gd), .obj a =>
      if n == "__doc__" then
        return ← modObj a fun o =>
          { o with body := .property g s d (value.getD .none) name gd }
      if n == "__name__" then
        return ← modObj a fun o => { o with body := .property g s d doc value gd }
      unmodelled
    | _, _ => unmodelled
  unmodelled

/-! ## `PyObject_Call` -/

/-- `slot_tp_call`, `Objects/typeobject.c:10341`. -/
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
    | .obj t => typeCall rt t args kw
    | _ => unmodelled
  | .c .function =>
    match payloadOf w f with
    | some (.func fd) => functionCall rt f fd args kw
    | _ => unmodelled
  | .c .method =>
    match payloadOf w f with
    | some (.bound func self) => rt.call func (self :: args) kw
    | _ => unmodelled
  | .c .builtinFn =>
    match payloadOf w f with
    | some (.builtin b self) => callBuiltin rt b self args kw
    | _ => unmodelled
  | .c .wrapperDescr =>
    match payloadOf w f with
    | some (.wrapperDescr o p g) => wrapperdescrCall rt o p g args kw
    | _ => unmodelled
  | .c .methodWrapper =>
    match payloadOf w f with
    | some (.methodWrapper d self) =>
      match payloadOf w d with
      | some (.wrapperDescr _ p g) => wrapperApply rt p g self args kw
      | _ => unmodelled
    | _ => unmodelled
  | .c .methodDescr =>
    match payloadOf w f with
    | some (.methodDescr o n b) =>
      methodCheckArgs o n args kw
      callBuiltin rt b (some (args.headD .none)) (args.drop 1) kw
    | _ => unmodelled
  | .c .classmethodDescr =>
    match payloadOf w f with
    | some (.classmethodDescr o n b) =>
      match args with
      | [] => typeErr s!"descriptor '{n}' of '{trunc 100 (tpName w o)}' object needs an argument"
      | self :: rest =>
        let bound ← classmethodGet o n b none (some self)
        rt.call bound rest kw
    | _ => unmodelled
  | .c .staticmethod =>
    match payloadOf w f with
    | some (.staticmethod g) => rt.call g args kw
    | _ => unmodelled
  | _ => unmodelled

/-- `_PyObject_Call`, `Objects/call.c:333`, on the `tp_call` slot; the vectorcall entry
points of functions and methods behave the same. -/
def pyCall (rt : Rt) (f : Val) (args : List Val) (kw : Kw) : M Val := do
  let w ← getW
  let tp := typeOf w f
  match slotOf w tp .tp_call with
  | none => typeErr s!"'{trunc 200 (tpName w tp)}' object is not callable"
  | some s => callTpCall rt s f args kw

end PyLean.TypeObj
