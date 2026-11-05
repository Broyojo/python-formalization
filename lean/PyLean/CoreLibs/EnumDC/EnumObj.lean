import PyLean.CoreLibs.EnumDC.EnumClass

/-!
The parts of Lib/enum.py (CPython 3.15.2) that run Python code on values the module does not know: `hash`, `==`, `<`,
`+ 1`, `bit_length` and `__index__` of a member value, each able to raise. The value type is abstract, `α`, with its
operations in `Ops α`; a theorem quantifies over every `Ops`. `evOps` is the instance for the `EV` values of
`EnumClass.lean`, and `pvOps` the instance for `PV`, ints, strs and instances of the difftest's class `K`, whose
`__hash__` and `__eq__` raise on request.

Scope: an operation is a function of its operands, so a `__hash__` or `__eq__` that changes state (the class being
built, or its own answer on a second call) is not modelled, nor the restart of a dict probe that such a change causes
(Objects/dictobject.c:1198-1203).
-/

namespace PyLean.CoreLibs.EnumDC

open PyLean

/-- The operations enum.py runs on a value. -/
structure Ops (α : Type) where
  /-- `a is b`. -/
  same : α → α → Bool
  /-- `hash(a)`: `TypeError` for an unhashable value, or what a `__hash__` raises. -/
  hash : α → Py Int
  /-- `bool(a == b)`: the rich comparison, reflected operand included, then its truth value. -/
  eq : α → α → Py Bool
  /-- `bool(a < b)`. -/
  lt : α → α → Py Bool
  /-- `bool(a > b)`. -/
  gt : α → α → Py Bool
  /-- `isinstance(a, int)`, with the value. -/
  asInt : α → Option Int
  /-- The `int` object `n`. -/
  ofInt : Int → α
  /-- `a + 1`. -/
  succ : α → Py α
  /-- `operator.index(a)`, as `range` reads its bounds. -/
  index : α → Py Int
  /-- `a.bit_length()`. -/
  bitLength : α → Py Nat
  /-- `type(a).__qualname__`, for messages. -/
  typeName : α → String
  /-- `bool(a)`. -/
  truth : α → Py Bool
  /-- `repr(a)`, as `%r` runs it. -/
  repr : α → Py String
  /-- The bases of each exception class of the program, builtin or its own, for `except`. -/
  excParent : String → List String

variable {α β : Type}

/-- `isinstance(e, cls)`: what `except cls:` catches, subclasses included. -/
def Ops.isInst (o : Ops α) (e : PyExc) (cls : String) : Bool := excIs o.excParent e cls

/-- `PyObject_RichCompareBool(a, b, Py_EQ)`, Objects/object.c: `True` for the same object, else `a == b`. -/
def Ops.req (o : Ops α) (a b : α) : Py Bool := if o.same a b then .ok true else o.eq a b

/-- The probe of a dict for key `k` with hash `h`: the entries in insertion order, which is the order of a probe
among keys of one hash, and for each `compare_generic`, Objects/dictobject.c:1182-1207: the same object, or the same
hash and `stored == k`, whose exception goes out. A stored key's hash is the hash it was stored with. -/
def Ops.dictFind (o : Ops α) (k : α) (h : Int) : List (α × β) → Py (Option β)
  | [] => .ok none
  | (k', v) :: r =>
    if o.same k' k then .ok (some v)
    else
      match o.hash k' with
      | .ok h' =>
        if h' = h then
          match o.eq k' k with
          | .error e => .error e
          | .ok true => .ok (some v)
          | .ok false => o.dictFind k h r
        else o.dictFind k h r
      | .error _ => o.dictFind k h r

/-- The exception a dict or a set gives when hashing a key raises, Objects/dictobject.c:2442-2460 and
Objects/setobject.c:346-359: an exact `TypeError` is replaced by "cannot use 'T' as a dict key (msg)", or "a set
element"; any other exception is kept. -/
def Ops.keyExc (o : Ops α) (what : String) (k : α) : PyExc → PyExc
  | .typeError m => .typeError s!"cannot use '{o.typeName k}' as a {what} ({m})"
  | e => e

/-- A dict or set lookup: `hash(k)`, then the probe. -/
def Ops.lookupIn (o : Ops α) (what : String) (d : List (α × β)) (k : α) : Py (Option β) :=
  match o.hash k with
  | .error e => .error (o.keyExc what k e)
  | .ok h => o.dictFind k h d

/-- `d.get(k)` without the default, `d[k]`, `k in d`: `none` is the `KeyError` of `d[k]`. -/
def Ops.dictGet (o : Ops α) (d : List (α × β)) (k : α) : Py (Option β) := o.lookupIn "dict key" d k

/-- `d.setdefault(k, v)`: the dict after, and what it returns. -/
def Ops.setDefault (o : Ops α) (d : List (α × β)) (k : α) (v : β) : Py (List (α × β) × β) :=
  match o.dictGet d k with
  | .error e => .error e
  | .ok (some w) => .ok (d, w)
  | .ok none => .ok (d ++ [(k, v)], v)

/-- `x in l` for a list, Objects/listobject.c:677-693: `item == x` for each item, the item on the left. -/
def Ops.listIn (o : Ops α) (x : α) : List α → Py Bool
  | [] => .ok false
  | y :: r =>
    match o.req y x with
    | .error e => .error e
    | .ok true => .ok true
    | .ok false => o.listIn x r

/-- `dict.setdefault(k, []).append(v)`, keyed by a member name. -/
def appendToG : List (Name × List α) → Name → α → List (Name × List α)
  | [], k, v => [(k, [v])]
  | (a, l) :: r, k, v => if a == k then (a, l ++ [v]) :: r else (a, l) :: appendToG r k v

/-! ### The class -/

/-- `EnumType`'s tables over values of type `α`. A member is known by its `_name_`. -/
structure EClassG (α : Type) where
  /-- An `issubclass(enum_class, Flag)`. -/
  isFlag : Bool := false
  memberNames : List Name := []
  /-- `_member_map_`: each name, aliases too, with the `_name_` of its member. -/
  memberMap : List (Name × Name) := []
  /-- The `_value_` of each member. -/
  values : List (Name × α) := []
  /-- `_value2member_map_`. -/
  value2member : List (α × Name) := []
  hashableValues : List α := []
  unhashableValues : List α := []
  unhashableMap : List (Name × List α) := []
  /-- `_flag_mask_`, `_singles_mask_`, `_all_bits_`: Python ints, so a negative member value is kept as it is. -/
  flagMask : Int := 0
  singlesMask : Int := 0
  allBits : Int := 0
  deriving DecidableEq

/-- The `EV` class as one over `EV` values. -/
def EClass.toG (c : EClass) : EClassG EV :=
  { isFlag := c.kind == .flag, memberNames := c.memberNames, memberMap := c.memberMap, values := c.values,
    value2member := c.value2member, hashableValues := c.hashableValues, unhashableValues := c.unhashableValues,
    unhashableMap := c.unhashableMap, flagMask := c.flagMask, singlesMask := c.singlesMask, allBits := c.allBits }

/-- `cls[name]`, `EnumType.__getitem__`, Lib/enum.py:800-804. -/
def EClassG.getItem (c : EClassG α) (name : Name) : Py Name :=
  match c.memberMap.lookup name with
  | some m => .ok m
  | none => .error (.keyError "~name")

/-- `EnumType._add_member_`, Lib/enum.py:1072-1075, :1115. -/
def EClassG.addToMap (c : EClassG α) (name member : Name) : Py (EClassG α) :=
  match c.memberMap.lookup name with
  | some m => if m != member then .error (.named "NameError" "~is already bound") else .ok c
  | none => .ok { c with memberMap := c.memberMap ++ [(name, member)] }

/-- `_is_single_bit`, Lib/enum.py:91-98, on any `int`: zero is not, and for a negative `num`, `num & (num - 1)` is
negative, so not zero. -/
def isSingleBitInt (n : Int) : Bool := if n ≤ 0 then false else isSingleBit n.toNat

/-- `int.bit_length()`. -/
def intBitLength (n : Int) : Nat := bitLength n.natAbs

/-! ### `_proto_member.__set_name__`, Lib/enum.py:240-325 -/

/-- How the class makes one member, Lib/enum.py:247-273: what `_new_member_`, `_member_type_` and `__init__` do with
`args`, the value or the items of a tuple value, wrapped once more for a `tuple` mixin (:248-254). Each is user or mixin
code, so each is a hook that can raise. -/
structure Maker (α : Type) where
  /-- `enum_class._new_member_(enum_class[, *args])`: what it raises, or the member, with the `_value_` it set. -/
  newMember : Py (Option α) := .ok none
  /-- `enum_class._member_type_ is object`. -/
  plain : Bool := true
  /-- `enum_class._member_type_(*args)`. -/
  callType : Py α := .error (.typeError "~not called")
  /-- `enum_member.__init__(*args)`. -/
  init : Py Unit := .ok ()

/-- The `_value_` of the new member, Lib/enum.py:255-269: what `__new__` set, else the value itself for a plain
class, else `_member_type_(*args)`, whose `Exception` becomes the `TypeError` of :264-268, while a `BaseException` that is
not an `Exception` goes out as it is. Then `__init__`, :273. -/
def Maker.memberValue (o : Ops α) (mk : Maker α) (value : α) : Py α :=
  let v : Py α :=
    match mk.newMember with
    | .error e => .error e
    | .ok (some v) => .ok v
    | .ok none =>
      if mk.plain then .ok value
      else
        match mk.callType with
        | .ok v => .ok v
        | .error e =>
          if o.isInst e "Exception" then .error (.typeError "_value_ not set in __new__, unable to create it")
          else .error e
  match v with
  | .error e => .error e
  | .ok v =>
    match mk.init with
    | .error e => .error e
    | .ok () => .ok v

/-- The masks of a `Flag`, Lib/enum.py:276-281: an `int` value is or-ed in. -/
def EClassG.flagUpdate (o : Ops α) (c : EClassG α) (v : α) : EClassG α :=
  if c.isFlag then
    let c1 := match o.asInt v with
      | some n => { c with flagMask := twos (· ||| ·) c.flagMask n,
                           singlesMask := if isSingleBitInt n then twos (· ||| ·) c.singlesMask n else c.singlesMask }
      | none => c
    { c1 with allBits := 2 ^ intBitLength c1.flagMask - 1 }
  else c

/-- The linear search of :290-294: the first canonical member whose `_value_ == value`; no identity shortcut, the
member's value on the left. -/
def EClassG.firstEqual (o : Ops α) (c : EClassG α) (v : α) : List (Name × Name) → Py (Option Name)
  | [] => .ok none
  | (_, m) :: r =>
    match c.values.lookup m with
    | none => c.firstEqual o v r
    | some x =>
      match o.eq x v with
      | .error e => .error e
      | .ok true => .ok (some m)
      | .ok false => c.firstEqual o v r

/-- The alias search, Lib/enum.py:283-296. `some m` is the member with this value; `none` is the `KeyError` of :295,
or a `KeyError` (or an instance of a subclass) from `__hash__` or `__eq__`, all caught at :296. A `TypeError` from the fast lookup goes to the linear
search; a `TypeError` raised there, inside the handler, goes out. -/
def EClassG.aliasOf (o : Ops α) (c : EClassG α) (v : α) : Py (Option Name) :=
  let linear : Py (Option Name) :=
    match c.firstEqual o v c.memberMap with
    | .error e => if o.isInst e "KeyError" then .ok none else .error e
    | .ok r => .ok r
  match o.dictGet c.value2member v with
  | .ok r => .ok r
  | .error e =>
    if o.isInst e "TypeError" then linear
    else if o.isInst e "KeyError" then .ok none
    else .error e

/-- The value tables, Lib/enum.py:313-325: `setdefault`, then `value not in _hashable_values_`; a `TypeError` from
either, after `setdefault` has stored the value or not, puts the value in the unhashable lists. -/
def EClassG.noteValue (o : Ops α) (c : EClassG α) (name member : Name) (v : α) : Py (EClassG α) :=
  let unh (c' : EClassG α) : EClassG α :=
    { c' with unhashableValues := c'.unhashableValues ++ [v], unhashableMap := appendToG c'.unhashableMap name v }
  match o.setDefault c.value2member v member with
  | .error e => if o.isInst e "TypeError" then .ok (unh c) else .error e
  | .ok (d, _) =>
    let c1 := { c with value2member := d }
    match o.listIn v c.hashableValues with
    | .error e => if o.isInst e "TypeError" then .ok (unh c1) else .error e
    | .ok true => .ok c1
    | .ok false => .ok { c1 with hashableValues := c.hashableValues ++ [v] }

/-- `_proto_member.__set_name__`, Lib/enum.py:240-325, for the member `name` with the body value `value`. -/
def EClassG.setName (o : Ops α) (mk : Maker α) (c : EClassG α) (name : Name) (value : α) : Py (EClassG α) :=
  match mk.memberValue o value with
  | .error e => .error e
  | .ok v =>
    let c1 := c.flagUpdate o v
    match c1.aliasOf o v with
    | .error e => .error e
    | .ok (some m) =>
      match c1.addToMap name m with
      | .error e => .error e
      | .ok c2 => c2.noteValue o name m v
    | .ok none =>
      let keeps : Bool := !c1.isFlag || (match o.asInt v with
        | some n => isSingleBitInt n
        | none => false)
      let c2 := { c1 with memberNames := if keeps then c1.memberNames ++ [name] else c1.memberNames,
                          values := c1.values ++ [(name, v)] }
      match c2.addToMap name name with
      | .error e => .error e
      | .ok c3 => c3.noteValue o name name v

/-- The `__set_name__` calls of `type.__new__`, in definition order, with the maker of each member. -/
def EClassG.build (o : Ops α) (mk : α → Maker α) (c : EClassG α) : List (Name × α) → Py (EClassG α)
  | [] => .ok c
  | (n, v) :: r =>
    match c.setName o (mk v) n v with
    | .error e => .error e
    | .ok c' => c'.build o mk r

/-- The `EV` class back from the generic one, its kind kept. -/
def EClass.ofG (c : EClass) (g : EClassG EV) : EClass :=
  { c with memberNames := g.memberNames, memberMap := g.memberMap, values := g.values, value2member := g.value2member,
           hashableValues := g.hashableValues, unhashableValues := g.unhashableValues, unhashableMap := g.unhashableMap }

/-! ### `Enum.__new__`, Lib/enum.py:1175-1234 -/

/-- The first unhashable list holding the value, `value in unhashable_values`, :1192-1194. -/
def firstHolding (o : Ops α) (v : α) : List (Name × List α) → Py (Option Name)
  | [] => .ok none
  | (n, l) :: r =>
    match o.listIn v l with
    | .error e => .error e
    | .ok true => .ok (some n)
    | .ok false => firstHolding o v r

/-- The second loop, :1195-1196: `value == member._value_`, the value on the left, for each name of `_member_map_`. -/
def EClassG.firstByValue (o : Ops α) (c : EClassG α) (v : α) : List (Name × Name) → Py (Option Name)
  | [] => .ok none
  | (n, m) :: r =>
    match c.values.lookup m with
    | none => c.firstByValue o v r
    | some x =>
      match o.eq v x with
      | .error e => .error e
      | .ok true => .ok (some n)
      | .ok false => c.firstByValue o v r

/-- The long search, :1191-1196: a name found by either loop is looked up again with `cls[name]`. Any exception
goes out: the loops run inside the `except TypeError` handler. -/
def EClassG.longSearch (o : Ops α) (c : EClassG α) (v : α) : Py (Option Name) :=
  let byName (r : Py (Option Name)) (k : Py (Option Name)) : Py (Option Name) :=
    match r with
    | .error e => .error e
    | .ok (some n) =>
      match c.getItem n with
      | .error e => .error e
      | .ok m => .ok (some m)
    | .ok none => k
  byName (firstHolding o v c.unhashableMap) (byName (c.firstByValue o v c.memberMap) (.ok none))

/-- After the searches, :1197-1234: no members is a `TypeError`, and otherwise `_missing_` decides. When its result is
not a member, :1220 builds `ValueError("%r is not a valid %s" % (value, ...))` first, so the value's `repr` (`rv`) runs
and its exception goes out instead. The `%r` of a result that is not a member, :1225, is of the model's opaque object,
whose `repr` does not fail. -/
def EClassG.afterSearch (c : EClassG α) (inProgress : Bool) (rv : Py String) (miss : MissingRet) : Py Name :=
  if c.memberMap.isEmpty then
    if inProgress then .error (.typeError "do not use `super().__new__; call the appropriate __new__ directly")
    else .error (.typeError "~has no members defined")
  else
    match miss with
    | .member n => .ok n
    | .none => withRepr rv (.valueError "~is not a valid enum value")
    | .other => withRepr rv (.typeError "~error in _missing_: returned instead of None or a valid member")
    | .raises e => withRepr rv e

/-- `Enum.__new__`, Lib/enum.py:1175-1234, for a class that is not a `Flag`. `self` is `type(value) is cls`. The
`try` at :1184-1196 passes on a `KeyError` from the lookup, the hash or `==`, and searches on a `TypeError`. -/
def EClassG.enumNew (o : Ops α) (c : EClassG α) (self : Option Name) (v : α) (inProgress : Bool)
    (miss : MissingRet) : Py Name :=
  match self with
  | some m => .ok m
  | none =>
    match o.dictGet c.value2member v with
    | .ok (some n) => .ok n
    | .ok none => c.afterSearch inProgress (o.repr v) miss
    | .error e =>
      if o.isInst e "KeyError" then c.afterSearch inProgress (o.repr v) miss
      else if o.isInst e "TypeError" then
        match c.longSearch o v with
        | .error e' => .error e'
        | .ok (some n) => .ok n
        | .ok none => c.afterSearch inProgress (o.repr v) miss
      else .error e

/-! ### `Enum._add_value_alias_`, Lib/enum.py:1239-1262 -/

/-- The first member, by `_member_map_.values()`, whose `_value_ == value`, :1248-1249. -/
def EClassG.firstMemberEq (o : Ops α) (c : EClassG α) (v : α) : List (Name × Name) → Py (Option Name)
  | [] => .ok none
  | (_, m) :: r =>
    match c.values.lookup m with
    | none => c.firstMemberEq o v r
    | some x =>
      match o.eq x v with
      | .error e => .error e
      | .ok true => .ok (some m)
      | .ok false => c.firstMemberEq o v r

/-- The end, :1253-1262: `setdefault` and the append, or on a `TypeError` the unhashable lists under `self.name`. -/
def EClassG.bindValue (o : Ops α) (c : EClassG α) (memberName : Name → Name) (self : Name) (v : α) :
    Py (EClassG α) :=
  match o.setDefault c.value2member v self with
  | .error e =>
    if o.isInst e "TypeError" then
      .ok { c with unhashableValues := c.unhashableValues ++ [v],
                   unhashableMap := appendToG c.unhashableMap (memberName self) v }
    else .error e
  | .ok (d, _) => .ok { c with value2member := d, hashableValues := c.hashableValues ++ [v] }

/-- `Enum._add_value_alias_`, Lib/enum.py:1239-1262. `value in map` and the two reads of `map[value]` at :1242-1244
give one answer, as `hash` and `==` are functions. In the `except TypeError` branch the `ValueError` of :1251 is
formatted with `map[value]`, which raises that `TypeError` again, so the `TypeError` comes out instead. -/
def EClassG.addValueAlias (o : Ops α) (c : EClassG α) (memberName : Name → Name) (self : Name) (v : α) :
    Py (EClassG α) :=
  match o.dictGet c.value2member v with
  | .ok (some m) =>
    if m != self then
      -- `'%r is already bound: %r' % (value, member)`: the value's `repr`, then the member's, `<C.A: repr(_value_)>`
      match o.repr v with
      | .error e => .error e
      | .ok _ =>
        match (c.values.lookup m).map o.repr with
        | some (.error e) => .error e
        | _ => .error (.valueError "~is already bound")
    else .ok c
  | .ok none => c.bindValue o memberName self v
  | .error e =>
    if o.isInst e "TypeError" then
      match c.firstMemberEq o v c.memberMap with
      | .error e' => .error e'
      | .ok (some m) => if m != self then .error e else .ok c
      | .ok none => c.bindValue o memberName self v
    else .error e

/-! ### `EnumType.__contains__`, Lib/enum.py:750-769, and `Flag._missing_` on any value -/

/-- `Flag._missing_`, Lib/enum.py:1476-1569: a value that is not an `int` is the `ValueError` of :1482-1485, formatted with
`%r`, so an exception of its `repr` goes out instead; an `int` (of a subclass too) goes on with its `repr`. -/
def FlagCls.missingOf (o : Ops α) (c : FlagCls) (v : α) : Py FlagVal :=
  match o.asInt v with
  | none => withRepr (o.repr v) (.valueError s!"~is not a valid {c.name}")
  | some i => c.missingR (o.repr v) i

/-- `value in cls._unhashable_values_ or value in cls._hashable_values_`, :766-769. -/
def inLists (o : Ops α) (unh hashable : List α) (v : α) : Py Bool :=
  match o.listIn v unh with
  | .error e => .error e
  | .ok true => .ok true
  | .ok false => o.listIn v hashable

/-- `EnumType.__contains__`, Lib/enum.py:750-769. `isMember` is `isinstance(value, cls)`; `flag` is the class when it
is a `Flag`, whose `_missing_` decides unless it raises `ValueError`. -/
def containsG (o : Ops α) (isMember : Bool) (flag : Option FlagCls) (unh hashable : List α) (v : α) : Py Bool :=
  if isMember then .ok true
  else
    match flag with
    | none => inLists o unh hashable v
    | some c =>
      match c.missingOf o v with
      | .ok (.flag _ _) => .ok true
      | .ok (.plain _) => .ok false
      | .error e => if o.isInst e "ValueError" then inLists o unh hashable v else .error e

/-- `value in F` for a `Flag` class: its `_hashable_values_` are the `int` values of its members, and its
`_unhashable_values_` is empty. -/
def FlagCls.containsOf (o : Ops α) (c : FlagCls) (isMember : Bool) (v : α) : Py Bool :=
  containsG o isMember (some c) [] (c.members.map (fun p => o.ofInt (p.2 : Int))) v

/-! ### `verify.__call__`, Lib/enum.py:1968-2046 -/

/-- What `verify(...)` is called on. -/
inductive VTarget where
  /-- A subclass of `Enum`; `flag` for a subclass of `Flag`. -/
  | enum (flag : Bool)
  /-- A class that is not an `Enum`. -/
  | cls
  /-- Not a class, for which `issubclass` raises. -/
  | notCls
  deriving Repr, DecidableEq, Inhabited

/-- `set(it)`, Objects/setobject.c `set_add_entry`: each value hashed and probed as a dict key, the new ones added. The
set is kept in insertion order; its iteration order is a separate argument. -/
def Ops.setOf (o : Ops α) : List α → List (α × Unit) → Py (List (α × Unit))
  | [], s => .ok s
  | v :: r, s =>
    match o.lookupIn "set element" s v with
    | .error e => .error e
    | .ok (some _) => o.setOf r s
    | .ok none => o.setOf r (s ++ [(v, ())])

/-- `v in s` for a set. -/
def Ops.setIn (o : Ops α) (s : List (α × Unit)) (v : α) : Py Bool :=
  match o.lookupIn "set element" s v with
  | .error e => .error e
  | .ok r => .ok r.isSome

/-- `min(l)` with `cmp = (· < ·)`, `max(l)` with `(· > ·)`, Python/bltinmodule.c `min_max`: the first item, replaced by
each later item for which `cmp item current` holds. A comparison's exception goes out. -/
def extremum (cmp : α → α → Py Bool) : α → List α → Py α
  | cur, [] => .ok cur
  | cur, x :: r =>
    match cmp x cur with
    | .error e => .error e
    | .ok true => extremum cmp x r
    | .ok false => extremum cmp cur r

/-- `for i in is: if i not in values: missing.append(i)`, Lib/enum.py:1996-2004. -/
def Ops.missingFrom (o : Ops α) (s : List (α × Unit)) : List Int → Py (List Int)
  | [] => .ok []
  | i :: r =>
    match o.setIn s (o.ofInt i) with
    | .error e => .error e
    | .ok true => o.missingFrom s r
    | .ok false =>
      match o.missingFrom s r with
      | .error e => .error e
      | .ok m => .ok (i :: m)

/-- The `ValueError` of :2007-2010, cut at 256 characters. -/
def continuousMsg (flag : Bool) (clsName : String) (missing : List Int) : String :=
  String.ofList ((s!"invalid {if flag then "flag" else "enum"} '{clsName}': missing values " ++
    ", ".intercalate (missing.map toString)).toList.take 256)

/-- The `CONTINUOUS` check, Lib/enum.py:1989-2010. `vals` are `e.value` for the members; `order` is the iteration order
of the set, which depends on the hashes. `range(a, b)` reads `a` before `b`. -/
def verifyContinuousG (o : Ops α) (order : List α → List α) (flag : Bool) (clsName : String) (vals : List α) :
    Py Unit :=
  match o.setOf vals [] with
  | .error e => .error e
  | .ok s =>
    if s.length < 2 then .ok ()
    else
      match order (s.map Prod.fst) with
      | [] => .ok ()
      | x :: r =>
        match extremum o.lt x r with
        | .error e => .error e
        | .ok low =>
          match extremum o.gt x r with
          | .error e => .error e
          | .ok high =>
            let probes : Py (List Int) :=
              if flag then
                match o.bitLength low with
                | .error e => .error e
                | .ok bl =>
                  match o.bitLength high with
                  | .error e => .error e
                  | .ok bh => .ok ((intRange (bl : Int) ((bh : Int) - 1)).map (fun i => (2 : Int) ^ i.toNat))
              else
                match o.succ low with
                | .error e => .error e
                | .ok l1 =>
                  match o.index l1 with
                  | .error e => .error e
                  | .ok a =>
                    match o.index high with
                    | .error e => .error e
                    | .ok b => .ok (intRange a b)
            match probes with
            | .error e => .error e
            | .ok ps =>
              match o.missingFrom s ps with
              | .error e => .error e
              | .ok [] => .ok ()
              | .ok m => .error (.valueError (continuousMsg flag clsName m))

/-- `[e.value for e in enumeration]`: the values of the members of `_member_names_`. -/
def EClassG.memberValues (c : EClassG α) : List α := c.memberNames.filterMap (fun n => c.values.lookup n)

/-- The `UNIQUE` check, Lib/enum.py:1978-1988: `name != member.name` for an entry of `__members__`. -/
def EClassG.verifyUnique (c : EClassG α) (memberName : Name → Name) : Py Unit :=
  if c.memberMap.any (fun p => p.1 != memberName p.2) then .error (.valueError "~aliases found in") else .ok ()

/-- `list(_iter_bits_lsb(value))`, :2025, for a value that `value < 0` let through: an `int` gives its bits, :122-125; for
anything else `while num:` takes its truth value, and a true one meets `~num` at :123, the `TypeError` of a type without
`__invert__`. -/
def Ops.bitsOfValue (o : Ops α) (v : α) : Py (List Nat) :=
  match o.asInt v with
  | some n => .ok (bitsOf n.toNat)
  | none =>
    match o.truth v with
    | .error e => .error e
    | .ok false => .ok []
    | .ok true => .error (.typeError s!"bad operand type for unary ~: '{o.typeName v}'")

/-- `[v for v in values if v not in member_values]`, :2026, each `int` compared with the member values by `==`. -/
def Ops.notIn (o : Ops α) (mvals : List α) : List Nat → Py (List Nat)
  | [] => .ok []
  | b :: r =>
    match o.listIn (o.ofInt (b : Int)) mvals with
    | .error e => .error e
    | .ok true => o.notIn mvals r
    | .ok false =>
      match o.notIn mvals r with
      | .error e => .error e
      | .ok l => .ok (b :: l)

/-- One entry of `_member_map_` in `NAMED_FLAGS`, :2018-2026: a name of `_member_names_` is skipped, then
`alias.value < 0` (which can raise), then the bits of the value that no member value equals. -/
def EClassG.missedBits (o : Ops α) (c : EClassG α) (p : Name × Name) : Py (List Nat) :=
  if c.memberNames.contains p.1 then .ok []
  else
    match c.values.lookup p.2 with
    | none => .ok []
    | some v =>
      match o.lt v (o.ofInt 0) with
      | .error e => .error e
      | .ok true => .ok []
      | .ok false =>
        match o.bitsOfValue v with
        | .error e => .error e
        | .ok bs => o.notIn c.memberValues bs

/-- The loop of :2018-2030 over `_member_map_`, in order: whether an entry missed a bit. -/
def EClassG.namedLoop (o : Ops α) (c : EClassG α) : List (Name × Name) → Py Bool
  | [] => .ok false
  | p :: r =>
    match c.missedBits o p with
    | .error e => .error e
    | .ok bs =>
      match c.namedLoop o r with
      | .error e => .error e
      | .ok b => .ok (!bs.isEmpty || b)

/-- The `NAMED_FLAGS` check, Lib/enum.py:2012-2045. -/
def EClassG.verifyNamed (o : Ops α) (c : EClassG α) : Py Unit :=
  match c.namedLoop o c.memberMap with
  | .error e => .error e
  | .ok true => .error (.valueError "~invalid Flag")
  | .ok false => .ok ()

def verifyOneG (o : Ops α) (order : List α → List α) (c : EClassG α) (memberName : Name → Name)
    (flag : Bool) (clsName : String) : Check → Py Unit
  | .unique => c.verifyUnique memberName
  | .continuous => verifyContinuousG o order flag clsName c.memberValues
  | .named => c.verifyNamed o

def verifyAllG (o : Ops α) (order : List α → List α) (c : EClassG α) (memberName : Name → Name)
    (flag : Bool) (clsName : String) : List Check → Py Unit
  | [] => .ok ()
  | k :: r =>
    match verifyOneG o order c memberName flag clsName k with
    | .error e => .error e
    | .ok () => verifyAllG o order c memberName flag clsName r

/-- `verify.__call__`, Lib/enum.py:1968-2046: `enumeration.__name__` is read first, :1970, then `issubclass`, which
raises for what is not a class, then the checks in order. -/
def verifyCallG (o : Ops α) (order : List α → List α) (c : EClassG α) (memberName : Name → Name)
    (name : Py String) (target : VTarget) (checks : List Check) : Py Unit :=
  match name with
  | .error e => .error e
  | .ok clsName =>
    match target with
    | .notCls => .error (.typeError "issubclass() arg 1 must be a class")
    | .cls => .error (.typeError "the 'verify' decorator only works with Enum and Flag")
    | .enum flag => verifyAllG o order c memberName flag clsName checks

/-! ### `Flag._generate_next_value_`, Lib/enum.py:1437-1453 -/

/-- `Flag._generate_next_value_`: `start`, or `1` for `None`, for the first member; then `2 ** (_high_bit(max) + 1)`,
where `_high_bit` is `bit_length() - 1` and any `Exception` from it is the `TypeError` of :1449-1452, whose message
formats the value with `%r`, so an exception of its `repr` goes out instead. -/
def flagGenerateG (o : Ops α) (start : Option α) (count : Nat) (last : List α) : Py α :=
  if count = 0 then .ok (start.getD (o.ofInt 1))
  else
    match last with
    | [] => .error (.valueError "max() iterable argument is empty")
    | x :: r =>
      match extremum o.gt x r with
      | .error e => .error e
      | .ok m =>
        match o.bitLength m with
        | .error e =>
          if o.isInst e "Exception" then withRepr (o.repr m) (.typeError "~invalid flag value") else .error e
        | .ok b => .ok (o.ofInt ((2 : Int) ^ b))

/-! ### Iterating a `Flag` value, Lib/enum.py:1456-1473, :1581-1585 -/

/-- An entry of a `Flag` class's `_value2member_map_`: a member, or a pseudo-member that `_missing_` stored at :1566. -/
inductive MapEntry where
  | member (name : String) (value : Nat)
  | pseudo (value : Nat) (name : Option String)
  deriving Repr, DecidableEq, Inhabited

def MapEntry.toVal : MapEntry → FlagVal
  | .member n v => .flag v (some n)
  | .pseudo v n => .flag v n

/-- `_value2member_map_.get(v)` for `v ≥ 0`. The members were stored first, at class creation; `cache` holds the
pseudo-members stored since, by value. -/
def FlagCls.mapGet (c : FlagCls) (cache : List (Nat × Option String)) (v : Nat) : Option MapEntry :=
  match c.memberOf v with
  | some n => some (.member n v)
  | none => (cache.lookup v).map (fun n => .pseudo v n)

/-- `Flag._iter_member_by_value_`, :1456-1461: `_value2member_map_.get(val)` for each bit of `value & _flag_mask_`, from
the lowest; `none` is the `None` that `get` gives for a bit nothing has. -/
def FlagCls.byValue (c : FlagCls) (cache : List (Nat × Option String)) (value : Nat) : List (Option MapEntry) :=
  (bitsOf (value &&& c.flagMask)).map (c.mapGet cache)

/-- `_iter_member_` is `_iter_member_by_value_` unless the member values, in definition order, are not sorted,
Lib/enum.py:663-667. The members iterated are the canonical ones with a single bit. -/
def FlagCls.valueOrdered (c : FlagCls) : Bool :=
  decide (((c.canonical.filter (fun p => isSingleBit p.2)).map Prod.snd).Pairwise (· ≤ ·))

/-- The key `m._sort_order_` of `_iter_member_by_def_`, :1472: set on members at :274, absent on `None` and on a
pseudo-member, so `AttributeError`. -/
def FlagCls.sortKey (c : FlagCls) : Option MapEntry → Option PyExc
  | some (.member _ _) => none
  | some (.pseudo _ _) => some (.named "AttributeError" s!"'{c.name}' object has no attribute '_sort_order_'")
  | none => some (.named "AttributeError" "'NoneType' object has no attribute '_sort_order_'")

/-- `Flag._iter_member_by_def_`, :1466-1473: `sorted` takes every key first, in order, so the first entry without one
raises; otherwise the keys are the members' places in `_member_names_`, which are distinct, and the members come in
definition order. -/
def FlagCls.byDef (c : FlagCls) (cache : List (Nat × Option String)) (value : Nat) : Py (List (Option MapEntry)) :=
  let l := c.byValue cache value
  match l.findSome? c.sortKey with
  | some e => .error e
  | none => .ok ((c.canonical.filter (fun p => isSingleBit p.2 && l.contains (some (.member p.1 p.2)))).map
      (fun p => some (.member p.1 p.2)))

/-- `Flag.__iter__`, :1581-1585: `_iter_member_(self._value_)`. -/
def FlagCls.iterC (c : FlagCls) (cache : List (Nat × Option String)) (value : Nat) : Py (List (Option MapEntry)) :=
  if c.valueOrdered then .ok (c.byValue cache value) else c.byDef cache value

/-- `F(v)`, and the pseudo-member `_missing_` stores with `setdefault` at :1566 when no entry has its value. -/
def FlagCls.callC (c : FlagCls) (cache : List (Nat × Option String)) (v : Int) :
    Py (FlagVal × List (Nat × Option String)) :=
  match c.call v with
  | .error e => .error e
  | .ok (.plain p) => .ok (.plain p, cache)
  | .ok (.flag n name) =>
    match c.mapGet cache n with
    | some _ => .ok (.flag n name, cache)
    | none => .ok (.flag n name, cache ++ [(n, name)])

/-- Calls in turn, the cache carried along. -/
def FlagCls.callsC (c : FlagCls) : List (Nat × Option String) → List Int → Py (List (Nat × Option String))
  | cache, [] => .ok cache
  | cache, v :: r =>
    match c.callC cache v with
    | .error e => .error e
    | .ok (_, cache') => c.callsC cache' r

/-! ### `_iter_bits_lsb`, Lib/enum.py:115-125 -/

/-- The argument of `_iter_bits_lsb`: an `int`, or an `Enum` member with an `int` value, and its `repr`. -/
inductive BitsArg where
  | int (n : Int)
  | member (value : Int) (repr : String)
  deriving Repr, DecidableEq, Inhabited

/-- `repr(original)`. -/
def BitsArg.repr : BitsArg → String
  | .int n => toString n
  | .member _ r => r

/-- `_iter_bits_lsb`, run to the end, as `list()` does: a member is replaced by its value, :118-119, a negative value is
the `ValueError` of :120-121, and the loop of :122-125 yields `num & (~num + 1)`, the lowest bit, until `num` is 0. -/
def iterBitsLsb (a : BitsArg) : Py (List Nat) :=
  let num : Int := match a with
    | .int n => n
    | .member v _ => v
  if num < 0 then .error (.valueError s!"{a.repr} is not a positive integer")
  else .ok (bitsOf num.toNat)

/-! ### `EnumType.__call__`, Lib/enum.py:701-748 -/

/-- The keywords of `EnumType.__call__`, :701: `type`, `start`, `boundary`, `module`, `qualname`, as objects (`none` for
`None`). -/
structure CallKw where
  type : Option Nat := none
  start : Atom := .int 1
  boundary : Option Nat := none
  module : Option String := none
  qualname : Option String := none
  deriving Repr, DecidableEq, Inhabited

/-- What `EnumType.__call__` does when it does not raise. -/
inductive CallOut where
  /-- The member that `Enum.__new__` found. -/
  | member (n : Name)
  /-- `cls._create_(class_name=value, names=..., module=, qualname=, type=, start=, boundary=)`, :740-748: the functional
  API, with `names` `None` when not given, every keyword passed on, and the further positional values dropped. -/
  | create (className : Atom) (names : Option Atom) (kw : CallKw)
  deriving Repr, DecidableEq, Inhabited

/-- `EnumType.__call__`, Lib/enum.py:701-748. `more` are the positional arguments after `value`, `names` first, and
`kw` the keywords. A class with members looks up `value`, or the tuple `(value, names) + values`, whatever the keywords;
one without raises only when neither `names` nor `type` is given, :735. -/
def enumCallG (o : Ops EV) (c : EClass) (self : Option Name) (value : Atom) (more : List Atom) (kw : CallKw)
    (miss : MissingRet) : Py CallOut :=
  if !c.memberMap.isEmpty then
    match c.toG.enumNew o self (if more.isEmpty then .atom value else .tup (value :: more)) false miss with
    | .error e => .error e
    | .ok n => .ok (.member n)
  else if more.isEmpty && kw.type.isNone then .error (.typeError "~has no members; specify `names=()`")
  else .ok (.create value more.head? kw)

/-! ### Instances: the `EV` values, and the difftest's `PV` values -/

/-- `type(v).__name__`. -/
def EV.typeName : EV → String
  | .atom (.int _) => "int"
  | .atom (.str _) => "str"
  | .atom (.obj _) => "object"
  | .atom (.list _) => "list"
  | .atom (.auto _) => "auto"
  | .tup _ => "tuple"
  | .names _ => "list"
  | .member _ => "member"
  | .nonmember _ => "nonmember"
  | .descr _ => "Descr"
  | .inner _ => "type"
  | .gen _ => "function"

/-- An order comparison of two `EV` values, exact for `int` and `str`; other kinds are not compared by the cases
the difftest makes, and are given the `TypeError` of two kinds without an order. -/
def evCmp (sym : String) (f : Int → Int → Bool) (g : String → String → Bool) (a b : EV) : Py Bool :=
  match a, b with
  | .atom (.int x), .atom (.int y) => .ok (f x y)
  | .atom (.str x), .atom (.str y) => .ok (g x y)
  | _, _ => .error (.typeError s!"'{sym}' not supported between instances of '{a.typeName}' and '{b.typeName}'")

/-- The operations on `EV` values: `==` is equality of the values (no `EV` value has an `__eq__` that raises), and a
hashable value hashes, its hash value being one, which only decides which entries `==` is tried on. -/
def evOps : Ops EV where
  same _ _ := false
  hash v := if v.hashable then .ok 0 else .error (.typeError "unhashable type: 'list'")
  eq a b := .ok (decide (a = b))
  lt := evCmp "<" (fun x y => decide (x < y)) (fun x y => decide (x < y))
  gt := evCmp ">" (fun x y => decide (x > y)) (fun x y => decide (x > y))
  asInt
    | .atom (.int n) => some n
    | _ => none
  ofInt n := .atom (.int n)
  succ
    | .atom (.int n) => .ok (.atom (.int (n + 1)))
    | .atom (.str _) => .error (.typeError "can only concatenate str (not \"int\") to str")
    | v => .error (.typeError s!"~unsupported operand type(s) for +: '{v.typeName}' and 'int'")
  index
    | .atom (.int n) => .ok n
    | v => .error (.typeError s!"'{v.typeName}' object cannot be interpreted as an integer")
  bitLength
    | .atom (.int n) => .ok (intBitLength n)
    | v => .error (.named "AttributeError" s!"'{v.typeName}' object has no attribute 'bit_length'")
  typeName := EV.typeName
  truth
    | .atom (.int n) => .ok (n != 0)
    | .atom (.str s) => .ok (s != "")
    | _ => .ok true
  repr _ := .ok ""
  excParent := builtinParent

/-- A value of the difftest's fallible cases. -/
inductive PV where
  | int (n : Int)
  | str (s : String)
  /-- `K(k, he, ee)` of difftest/corelibs_diff.py: `__hash__` is `hash(k)` unless `he` names the class of exception it
  raises, `__eq__` compares `k` with an `int` or another `K` unless `ee` names one; `i` tells instances apart for `is`. -/
  | key (k : Int) (he ee : Option String) (i : Nat)
  /-- The list `[i]`, a new object each time. -/
  | list (i : Nat)
  /-- `RObj(re)`: an object with no comparison, no `bit_length`, and a `__repr__` raising the exception `re` names. -/
  | robj (re : String) (i : Nat)
  /-- `RI(n, re)`: a subclass of `int` of value `n` whose `__repr__` raises the exception `re` names. -/
  | rint (n : Int) (re : String)
  deriving Repr, DecidableEq, Inhabited

def PV.typeName : PV → String
  | .int _ => "int"
  | .str _ => "str"
  | .key _ _ _ _ => "K"
  | .list _ => "list"
  | .robj _ _ => "RObj"
  | .rint _ _ => "RI"

/-- An `RI` compares and hashes as the `int` it is. -/
def PV.norm : PV → PV
  | .rint n _ => .int n
  | v => v

/-- `hash(n)` for an `int`, Objects/longobject.c `long_hash`: the value modulo `2**61 - 1`, sign kept, `-1` made `-2`. -/
def intHash (n : Int) : Int :=
  let p : Int := 2 ^ 61 - 1
  if 0 ≤ n then n % p
  else
    let r := -((-n) % p)
    if r = -1 then -2 else r

/-- The exception `K` raises: `cls(msg)`. -/
def pvExc (cls msg : String) : PyExc :=
  match cls with
  | "KeyError" => .keyError s!"'{msg}'"
  | "KSub" => .named "KSub" s!"'{msg}'"
  | "KT" => .named "KT" s!"'{msg}'"
  | "TypeError" => .typeError msg
  | "ValueError" => .valueError msg
  | c => .named c msg

/-- `a == b`: `K.__eq__` on the left, or reflected when the left operand gives `NotImplemented`; `False` when both do. -/
def pvEq0 : PV → PV → Py Bool
  | .key k _ ee _, b =>
    match ee with
    | some x => .error (pvExc x "eq")
    | none =>
      match b with
      | .key k' _ _ _ => .ok (k' == k)
      | .int n => .ok (n == k)
      | _ => .ok false
  | .int n, .key k _ ee _ =>
    match ee with
    | some x => .error (pvExc x "eq")
    | none => .ok (n == k)
  | .str _, .key _ _ ee _ =>
    match ee with
    | some x => .error (pvExc x "eq")
    | none => .ok false
  | .list _, .key _ _ ee _ =>
    match ee with
    | some x => .error (pvExc x "eq")
    | none => .ok false
  | .robj _ _, .key _ _ ee _ =>
    match ee with
    | some x => .error (pvExc x "eq")
    | none => .ok false
  | .int a, .int b => .ok (a == b)
  | .str a, .str b => .ok (a == b)
  | .list a, .list b => .ok (a == b)
  | _, _ => .ok false

def pvEq (a b : PV) : Py Bool := pvEq0 a.norm b.norm

/-- `a < b` (`gt` false) or `a > b` (`gt` true): `K` compares its key with a `K` or an `int`, reflected on the right. -/
def pvCmp (gt : Bool) (a b : PV) : Py Bool :=
  let sym := if gt then ">" else "<"
  let r (x y : Int) : Bool := if gt then decide (x > y) else decide (x < y)
  match a.norm, b.norm with
  | .int x, .int y => .ok (r x y)
  | .str x, .str y => .ok (if gt then decide (x > y) else decide (x < y))
  | .list x, .list y => .ok (r (x : Int) (y : Int))
  | .key x _ _ _, .key y _ _ _ => .ok (r x y)
  | .key x _ _ _, .int y => .ok (r x y)
  | .int x, .key y _ _ _ => .ok (r x y)
  | _, _ => .error (.typeError s!"'{sym}' not supported between instances of '{a.typeName}' and '{b.typeName}'")

def pvOps : Ops PV where
  same
    | .key _ _ _ i, .key _ _ _ j => i == j
    | .int a, .int b => a == b
    | .str a, .str b => a == b
    | _, _ => false
  hash
    | .int n => .ok (intHash n)
    -- `hash('')` is 0, Objects/unicodeobject.c `unicode_hash`; any other `str` hash is randomized, and is given a
    -- value outside the range of `int` hashes, which a randomized hash meets with probability about 2**-62
    | .str s => .ok (if s = "" then 0 else 2 ^ 62 + s.length)
    | .key k he _ _ =>
      match he with
      | some x => .error (pvExc x "hash")
      | none => .ok (intHash k)
    | .list _ => .error (.typeError "unhashable type: 'list'")
    | .robj _ i => .ok (2 ^ 62 + 1000 + i)
    | .rint n _ => .ok (intHash n)
  eq := pvEq
  lt := pvCmp false
  gt := pvCmp true
  asInt
    | .int n => some n
    | .rint n _ => some n
    | _ => none
  ofInt n := .int n
  succ
    | .int n => .ok (.int (n + 1))
    | .rint n _ => .ok (.int (n + 1))
    | .robj _ _ => .error (.typeError "unsupported operand type(s) for +: 'RObj' and 'int'")
    | .str _ => .error (.typeError "can only concatenate str (not \"int\") to str")
    | .list _ => .error (.typeError "can only concatenate list (not \"int\") to list")
    | .key _ _ _ _ => .error (.typeError "unsupported operand type(s) for +: 'K' and 'int'")
  index
    | .int n => .ok n
    | .rint n _ => .ok n
    | v => .error (.typeError s!"'{v.typeName}' object cannot be interpreted as an integer")
  bitLength
    | .int n => .ok (intBitLength n)
    | .rint n _ => .ok (intBitLength n)
    | v => .error (.named "AttributeError" s!"'{v.typeName}' object has no attribute 'bit_length'")
  typeName := PV.typeName
  truth
    | .int n => .ok (n != 0)
    | .rint n _ => .ok (n != 0)
    | .str s => .ok (s != "")
    | _ => .ok true
  repr
    | .robj re _ => .error (pvExc re "repr")
    | .rint _ re => .error (pvExc re "repr")
    | _ => .ok ""
  excParent
    | "KSub" => ["KeyError"]
    | "TSub" => ["TypeError"]
    | "KT" => ["KeyError", "TypeError"]
    | "BExc" => ["BaseException"]
    | c => builtinParent c

end PyLean.CoreLibs.EnumDC
