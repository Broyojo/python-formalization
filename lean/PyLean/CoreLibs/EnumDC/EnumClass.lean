import PyLean.CoreLibs.EnumDC.Model

/-!
Building an `Enum` class and looking values up in it: `EnumDict`, Lib/enum.py:328-457, `_proto_member.__set_name__`,
:240-325, the parts of `EnumType.__new__`, :481-693, that decide members and `_order_`, `_add_member_`, :1070-1115,
`Enum.__new__`, :1175-1234, `EnumType.__contains__`, :750-769, the functional API `_create_`, :853-907, the operators
of `Flag`, :1571-1657, `unique`, :1676-1689, and `verify`, :1968-2046.

Not mirrored: a mixed-in data type other than `str`, `__init_subclass__`, `_find_new_` and `_get_mixins_` (a class
here is a plain `Enum`, a `Flag` or a `StrEnum`), and the state a failed `__setitem__` leaves behind, since a failing
class body does not go on. A negative member value in a `Flag` class is outside the model.
-/

namespace PyLean.CoreLibs.EnumDC

open PyLean

abbrev Name := List Char

/-- A value in a class body that is not a wrapper. -/
inductive Atom where
  | int (n : Int)
  | str (s : String)
  /-- A hashable object without an order; `id` decides equality. -/
  | obj (id : Nat)
  /-- A list, so unhashable, holding `id`. -/
  | list (id : Nat)
  /-- `auto()`, with its `value` when it was given one. -/
  | auto (v : Option Int)
  deriving Repr, DecidableEq, Inhabited

/-- What `_generate_next_value` holds. `absent` is the attribute missing: `EnumDict.__init__` does not set it. -/
inductive Gen where
  | absent
  | enum
  | strEnum
  | flag
  | const (a : Atom)
  | raises (e : PyExc)
  deriving Repr, DecidableEq, Inhabited

/-- A value in a class body. -/
inductive EV where
  | atom (a : Atom)
  /-- A tuple; a tuple holding a tuple or a wrapper is not modelled. -/
  | tup (items : List Atom)
  | member (v : EV)
  | nonmember (v : EV)
  /-- Something with `__get__`, `__set__` or `__delete__`. -/
  | descr (id : Nat)
  /-- A class defined in the body. -/
  | inner (id : Nat)
  /-- A list of names, for `_ignore_` and `_order_`. -/
  | names (l : List Name)
  /-- A function given as `_generate_next_value_`. -/
  | gen (g : Gen)
  deriving Repr, DecidableEq, Inhabited

def Atom.isAuto : Atom → Bool
  | .auto _ => true
  | _ => false

def Atom.hashable : Atom → Bool
  | .list _ => false
  | _ => true

/-- `hash(value)` succeeds. A tuple is as hashable as its items. -/
def EV.hashable : EV → Bool
  | .atom a => a.hashable
  | .tup l => l.all Atom.hashable
  | .names _ => false
  | _ => true

/-! ### `_generate_next_value_` -/

/-- Which values `sorted` and `max` can compare with each other: ints, strings, tuples of ints and lists. Tuples of
anything else are treated as having no order, which is exact for the tuples the difftest gives. -/
def sortRank : EV → Option Nat
  | .atom (.int _) => some 0
  | .atom (.str _) => some 1
  | .atom (.list _) => some 3
  | .tup l => if l.all (fun a => match a with
      | .int _ => true
      | _ => false) then some 2 else none
  | _ => none

/-- `sorted(l)` does not raise. One item is not compared at all, and every item of a longer list is compared with
another, so one pair without an order raises. -/
def sortable : List EV → Bool
  | [] => true
  | [_] => true
  | x :: xs => (sortRank x).isSome && xs.all (fun y => sortRank y == sortRank x)

def intsOf (l : List EV) : List Int :=
  l.filterMap (fun v => match v with
    | .atom (.int n) => some n
    | _ => none)

/-- `Enum._generate_next_value_`, Lib/enum.py:1265-1283. -/
def enumGenerate (start : Int) (last : List EV) : Py Atom :=
  if last.isEmpty then .ok (.int start)
  else if !sortable last then .error (.typeError "unable to sort non-numeric values")
  else
    match intsOf last with
    | [] => .error (.typeError "~unable to increment")
    | i :: is => .ok (.int (is.foldl max i + 1))

/-- `Flag._generate_next_value_`, Lib/enum.py:1437-1453. -/
def flagGenerate (start : Int) (count : Nat) (last : List EV) : Py Atom :=
  if count = 0 then .ok (.int start)
  else if last.isEmpty then .error (.valueError "~max() iterable argument is empty")
  else if !sortable last then .error (.typeError "~not supported between instances")
  else
    match intsOf last with
    | [] => .error (.typeError "~invalid flag value")
    | i :: is => .ok (.int (2 ^ bitLength (is.foldl max i).natAbs))

def Gen.call (g : Gen) (name : Name) (start : Int) (count : Nat) (last : List EV) : Py Atom :=
  match g with
  | .absent => .error (.named "AttributeError" "'EnumDict' object has no attribute '_generate_next_value'")
  | .enum => enumGenerate start last
  | .strEnum => .ok (.str (String.ofList (name.map Char.toLower)))
  | .flag => flagGenerate start count last
  | .const a => .ok a
  | .raises e => .error e

/-! ### `EnumDict` -/

/-- The namespace of a class body. -/
structure EnumDict where
  items : List (Name × EV) := []
  /-- `_member_names`. -/
  memberNames : List Name := []
  lastValues : List EV := []
  ignore : List Name := []
  autoCalled : Bool := false
  /-- `_cls_name`. -/
  clsName : Option Name := none
  /-- `_generate_next_value`. -/
  gen : Gen := .absent
  deriving Repr, DecidableEq, Inhabited

def dictSet (l : List (Name × EV)) (k : Name) (v : EV) : List (Name × EV) :=
  if l.any (fun p => p.1 == k) then l.map (fun p => if p.1 == k then (k, v) else p) else l ++ [(k, v)]

def EnumDict.has (d : EnumDict) (k : Name) : Bool := d.items.any (fun p => p.1 == k)

def EnumDict.store (d : EnumDict) (k : Name) (v : EV) : EnumDict := { d with items := dictSet d.items k v }

/-- The sunder names that are allowed, Lib/enum.py:356-364. -/
def allowedSunder : List Name :=
  ["_order_".toList, "_generate_next_value_".toList, "_numeric_repr_".toList, "_missing_".toList, "_ignore_".toList,
   "_iter_member_".toList, "_iter_member_by_value_".toList, "_iter_member_by_def_".toList, "_add_alias_".toList,
   "_add_value_alias_".toList]

def sunderReserved (key : Name) : Bool :=
  !(allowedSunder.contains key) && !("_repr_".toList.isPrefixOf key)

/-- The ASCII separators of `.replace(',', ' ').split()`. -/
def isSep (c : Char) : Bool :=
  c == ' ' || c == ',' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'

def splitGo : List Char → Name → List Name
  | [], cur => if cur.isEmpty then [] else [cur.reverse]
  | c :: r, cur =>
    if isSep c then
      if cur.isEmpty then splitGo r [] else cur.reverse :: splitGo r []
    else splitGo r (c :: cur)

/-- `value.replace(',', ' ').split()`, Lib/enum.py:377, :651, :872. -/
def splitNames (s : List Char) : List Name := splitGo s []

/-- The `_ignore_` branch, Lib/enum.py:376-379. A list is taken as a list of names; the id of `.list` is not a name. -/
def ignoreList : EV → Py (List Name)
  | .atom (.str s) => .ok (splitNames s.toList)
  | .names l => .ok l
  | .atom (.list _) => .ok []
  | .tup _ => .ok []
  | _ => .error (.typeError "~object is not iterable")

/-- `_generate_next_value = value`, Lib/enum.py:373-374. Calling anything but a function fails. -/
def genOf : EV → Gen
  | .gen g => g
  | _ => .raises (.typeError "~object is not callable")

/-- The loop over a tuple with `auto` in it, Lib/enum.py:420-430: each `auto` sees the values of those before it. -/
def autoLoop (g : Gen) (key : Name) (count : Nat) : List Atom → List EV → Bool → Py (List Atom × List EV × Bool)
  | [], last, called => .ok ([], last, called)
  | .auto a :: rest, last, called =>
    match a with
    | some x =>
      match autoLoop g key count rest (last ++ [.atom (.int x)]) called with
      | .error e => .error e
      | .ok (vals, l, c) => .ok (.int x :: vals, l, c)
    | none =>
      match g.call key 1 count last with
      | .error e => .error e
      | .ok x =>
        match autoLoop g key count rest (last ++ [.atom x]) true with
        | .error e => .error e
        | .ok (vals, l, c) => .ok (x :: vals, l, c)
  | v :: rest, last, called =>
    match autoLoop g key count rest last called with
    | .error e => .error e
    | .ok (vals, l, c) => .ok (v :: vals, l, c)

/-- A value that is stored as it is, Lib/enum.py:440-442. -/
def EnumDict.addMember (d : EnumDict) (key : Name) (value : EV) : EnumDict :=
  { d.store key value with memberNames := d.memberNames ++ [key], lastValues := d.lastValues ++ [value] }

/-- `value`, with its `auto`s replaced, Lib/enum.py:412-442. -/
def EnumDict.addAuto (d : EnumDict) (key : Name) (single : Bool) (l : List Atom) : Py EnumDict :=
  match autoLoop d.gen key d.memberNames.length l d.lastValues d.autoCalled with
  | .error e => .error e
  | .ok (vals, last, called) =>
    let v := if single then EV.atom (vals.headD default) else .tup vals
    .ok { d.store key v with memberNames := d.memberNames ++ [key], lastValues := last, autoCalled := called }

/-- The last branch of `__setitem__`, Lib/enum.py:404-442: a new member. -/
def EnumDict.storeMember (d : EnumDict) (key : Name) (value0 : EV) : Py EnumDict :=
  if d.has key then .error (.typeError "~already defined as") else
  let value := match value0 with
    | .member v => v
    | v => v
  match value with
  | .atom (.auto a) => d.addAuto key true [.auto a]
  | .tup l => if l.any Atom.isAuto then d.addAuto key false l else .ok (d.addMember key value)
  | _ => .ok (d.addMember key value)

def EnumDict.privateName (d : EnumDict) (key : Name) : Bool :=
  match d.clsName with
  | some c => isPrivate c key
  | none => false

/-- `_is_internal_class`, Lib/enum.py:69-76, for the classes of the model, which are all defined in the body. -/
def EnumDict.internal (d : EnumDict) : Bool := d.clsName.isSome

/-- The branches of `__setitem__` for a name that is ordinary, Lib/enum.py:395-442. -/
def EnumDict.setValue (d : EnumDict) (key : Name) (value : EV) : Py EnumDict :=
  match value with
  | .nonmember v => .ok (d.store key v)
  | .descr _ => .ok (d.store key value)
  | .gen _ => .ok (d.store key value)
  | .inner _ => if d.internal then .ok (d.store key value) else d.storeMember key value
  | _ => d.storeMember key value

/-- `EnumDict.__setitem__`, Lib/enum.py:343-443, in the order of its branches. -/
def EnumDict.set (d : EnumDict) (key : Name) (value : EV) : Py EnumDict :=
  if d.privateName key then .ok (d.store key value)
  else if isSunder key then
    if sunderReserved key then .error (.valueError "~_sunder_ names are reserved for future Enum use")
    else if key == "_generate_next_value_".toList then
      if d.autoCalled then .error (.typeError "_generate_next_value_ must be defined before members")
      else .ok ({ d with gen := genOf value }.store key value)
    else if key == "_ignore_".toList then
      match ignoreList value with
      | .error e => .error e
      | .ok l =>
        if l.any d.memberNames.contains then .error (.valueError "~_ignore_ cannot specify already set names")
        else .ok ({ d with ignore := l }.store key (.names l))
    else .ok (d.store key value)
  else if isDunder key then
    .ok (d.store (if key == "__order__".toList then "_order_".toList else key) value)
  else if d.memberNames.contains key then .error (.typeError "~already defined as")
  else if d.ignore.contains key then .ok (d.store key value)
  else d.setValue key value

/-- `EnumDict.__init__`, Lib/enum.py:335-341, and the `__setitem__` of `EnumType.__prepare__`, :472-478. `first` is the
`_generate_next_value_` of the base enum. -/
def enumPrepare (cls : Name) (first : Gen) : Py EnumDict :=
  ({ clsName := some cls } : EnumDict).set "_generate_next_value_".toList (.gen first)

/-- The items of a sequence one at a time, with the state at a failure, since `EnumDict.update` goes on after one. -/
def EnumDict.setAll (d : EnumDict) : List (Name × EV) → EnumDict × Option PyExc
  | [] => (d, none)
  | (k, v) :: r =>
    match d.set k v with
    | .error e => (d, some e)
    | .ok d' => d'.setAll r

/-- The `members` of `EnumDict.update`. -/
inductive UpdateArg where
  /-- Something with `keys()`. -/
  | mapping (items : List (Name × EV))
  /-- An iterable of pairs. -/
  | pairs (items : List (Name × EV))
  deriving Repr, DecidableEq

/-- `for name, value in members`, Lib/enum.py:454-455, when `members` is a mapping: a key is unpacked, so one of two
characters assigns the second to the first, and any other is a `ValueError`. -/
def EnumDict.unpackKeys (d : EnumDict) : List Name → Py EnumDict
  | [] => .ok d
  | [a, b] :: r =>
    match d.set [a] (.atom (.str (String.ofList [b]))) with
    | .error e => .error e
    | .ok d' => d'.unpackKeys r
  | _ :: _ => .error (.valueError "~values to unpack")

/-- `EnumDict.update`, Lib/enum.py:449-457: the `except AttributeError` covers the loop over `keys()` too, so an
`AttributeError` from `__setitem__` restarts the loop on the iteration of the mapping. -/
def EnumDict.update (d : EnumDict) (members : UpdateArg) (more : List (Name × EV)) : Py EnumDict :=
  let first : Py EnumDict :=
    match members with
    | .mapping items =>
      match d.setAll items with
      | (d', none) => .ok d'
      | (d', some e) => if e.className == "AttributeError" then d'.unpackKeys (items.map Prod.fst) else .error e
    | .pairs ps =>
      match d.setAll ps with
      | (d', none) => .ok d'
      | (_, some e) => .error e
  match first with
  | .error e => .error e
  | .ok d' =>
    match d'.setAll more with
    | (d'', none) => .ok d''
    | (_, some e) => .error e

/-! ### The class -/

/-- Which class is being built. -/
inductive EKind where
  | plain
  | flag
  | strEnum
  deriving Repr, DecidableEq, Inhabited

/-- `EnumType`'s tables. A member is known by its `_name_`. -/
structure EClass where
  kind : EKind := .plain
  /-- `_member_names_`. -/
  memberNames : List Name := []
  /-- `_member_map_`: each name, aliases too, with the `_name_` of its member. -/
  memberMap : List (Name × Name) := []
  /-- The `_value_` of each member. -/
  values : List (Name × EV) := []
  /-- `_value2member_map_`. -/
  value2member : List (EV × Name) := []
  /-- `_hashable_values_`. -/
  hashableValues : List EV := []
  /-- `_unhashable_values_`. -/
  unhashableValues : List EV := []
  /-- `_unhashable_values_map_`. -/
  unhashableMap : List (Name × List EV) := []
  /-- `_flag_mask_`, `_singles_mask_` and `_all_bits_`. -/
  flagMask : Nat := 0
  singlesMask : Nat := 0
  allBits : Nat := 0
  deriving Repr, DecidableEq, Inhabited

def EClass.valueOf (c : EClass) (n : Name) : Option EV := c.values.lookup n

/-- The first member with this value, Lib/enum.py:290-293 and :1194-1196. -/
def EClass.findEqual (c : EClass) (v : EV) : Option Name :=
  (c.memberMap.find? (fun p => c.valueOf p.2 == some v)).map Prod.snd

/-- The lookup that decides aliases, Lib/enum.py:286-295. -/
def EClass.aliasOf (c : EClass) (v : EV) : Option Name :=
  if v.hashable then c.value2member.lookup v else c.findEqual v

/-- `StrEnum.__new__`, Lib/enum.py:1376-1395. With two or three values, `str(*values)` decodes, and no value of the
model is bytes, so it fails. -/
def strEnumNew (values : List Atom) : Py String :=
  if values.length > 3 then .error (.typeError "~too many arguments for str()")
  else
    match values with
    | [] => .ok ""
    | [a] =>
      match a with
      | .str s => .ok s
      | _ => .error (.typeError "~is not a string")
    | _ :: b :: r =>
      match b with
      | .str _ =>
        match r with
        | [] | [.str _] => .error (.typeError "~decoding")
        | _ => .error (.typeError "~errors must be a string")
      | _ => .error (.typeError "~encoding must be a string")

/-- `enum_member._value_`, Lib/enum.py:247-270. -/
def memberValue (k : EKind) (v : EV) : Py EV :=
  match k with
  | .strEnum =>
    let args := match v with
      | .tup l => l
      | .atom a => [a]
      | _ => [.obj 0]
    match strEnumNew args with
    | .error e => .error e
    | .ok s => .ok (.atom (.str s))
  | _ => .ok v

/-- The masks of a `Flag`, Lib/enum.py:276-281. -/
def EClass.flagUpdate (c : EClass) (v : EV) : EClass :=
  match c.kind, v with
  | .flag, .atom (.int n) =>
    let fm := c.flagMask ||| n.toNat
    { c with flagMask := fm, singlesMask := if isSingleBit n.toNat then c.singlesMask ||| n.toNat else c.singlesMask,
             allBits := 2 ^ bitLength fm - 1 }
  | .flag, _ => { c with allBits := 2 ^ bitLength c.flagMask - 1 }
  | _, _ => c

/-- A value that gets into `_member_names_` when no member has it, Lib/enum.py:299-312. -/
def keepsName (k : EKind) (v : EV) : Bool :=
  match k, v with
  | .flag, .atom (.int n) => isSingleBit n.toNat
  | .flag, _ => false
  | _, _ => true

/-- `EnumType._add_member_`, Lib/enum.py:1072-1075, :1115. -/
def EClass.addToMap (c : EClass) (name member : Name) : Py EClass :=
  match c.memberMap.lookup name with
  | some m => if m != member then .error (.named "NameError" "~is already bound") else .ok c
  | none => .ok { c with memberMap := c.memberMap ++ [(name, member)] }

/-- What a base of the class holds under a name, Lib/enum.py:1082-1096. -/
inductive BaseAttr where
  | absent
  | prop
  | descr
  | plain
  deriving Repr, DecidableEq, Inhabited

/-- The redirect of `_add_member_`: `_attr_type` and `_cls_type` as an index into `__mro__[1:]`. -/
structure Scan where
  found : Bool := false
  attrType : Option String := none
  clsIndex : Option Nat := none
  deriving Repr, DecidableEq, Inhabited

/-- The scan of `cls.__mro__[1:]`, Lib/enum.py:1081-1096. -/
def scanBases (i : Nat) (s : Scan) : List BaseAttr → Scan
  | [] => s
  | .absent :: r => scanBases (i + 1) s r
  | .prop :: _ => { found := true, attrType := some "enum", clsIndex := some i }
  | .descr :: r =>
    scanBases (i + 1) { found := true, attrType := s.attrType <|> some "desc", clsIndex := s.clsIndex <|> some i } r
  | .plain :: r => scanBases (i + 1) { s with attrType := some "attr", clsIndex := some i } r

/-- `dict.setdefault(k, []).append(v)`. -/
def appendTo : List (Name × List EV) → Name → EV → List (Name × List EV)
  | [], k, v => [(k, [v])]
  | (a, l) :: r, k, v => if a == k then (a, l ++ [v]) :: r else (a, l) :: appendTo r k v

/-- `dict.setdefault(k, v)`. -/
def setDefault (l : List (EV × Name)) (k : EV) (v : Name) : List (EV × Name) :=
  if (l.lookup k).isSome then l else l ++ [(k, v)]

/-- The value tables, Lib/enum.py:315-325. -/
def EClass.noteValue (c : EClass) (name member : Name) (value : EV) : EClass :=
  if value.hashable then
    { c with value2member := setDefault c.value2member value member,
             hashableValues := if c.hashableValues.contains value then c.hashableValues
                               else c.hashableValues ++ [value] }
  else
    { c with unhashableValues := c.unhashableValues ++ [value],
             unhashableMap := appendTo c.unhashableMap name value }

/-- The class after a new member, Lib/enum.py:304, :312. -/
def EClass.newMember (c : EClass) (name : Name) (value : EV) : EClass :=
  { c with memberNames := if keepsName c.kind value then c.memberNames ++ [name] else c.memberNames,
           values := c.values ++ [(name, value)] }

/-- `_proto_member.__set_name__`, Lib/enum.py:240-325. -/
def EClass.setName (c : EClass) (name : Name) (raw : EV) : Py EClass :=
  match memberValue c.kind raw with
  | .error e => .error e
  | .ok value =>
    let c1 := c.flagUpdate value
    match c1.aliasOf value with
    | some m =>
      match c1.addToMap name m with
      | .error e => .error e
      | .ok c2 => .ok (c2.noteValue name m value)
    | none =>
      match (c1.newMember name value).addToMap name name with
      | .error e => .error e
      | .ok c2 => .ok (c2.noteValue name name value)

/-- The `__set_name__` calls of `type.__new__`, in definition order. -/
def EClass.build (c : EClass) : List (Name × EV) → Py EClass
  | [] => .ok c
  | (n, v) :: r =>
    match c.setName n v with
    | .error e => .error e
    | .ok c' => c'.build r

/-- `_order_` as a list, Lib/enum.py:649-651. -/
def orderList : Option EV → Option (List Name)
  | some (.atom (.str s)) => some (splitNames s.toList)
  | some (.names l) => some l
  | _ => none

def isSingleValue : Option EV → Bool
  | some (.atom (.int n)) => isSingleBit n.toNat
  | _ => false

/-- The `_order_` steps, Lib/enum.py:668-691. -/
def EClass.checkOrder (c : EClass) (order : Option (List Name)) : Py Unit :=
  match order with
  | none => .ok ()
  | some o =>
    let inMap (x : Name) : Bool := (c.memberMap.lookup x).isSome
    let o2 := if c.kind == .flag then
        o.filter (fun x => !inMap x || isSingleValue (((c.memberMap.lookup x).bind c.valueOf)))
      else o
    if o2.isEmpty then .ok ()
    else
      let o3 := o2.filter (fun x => !inMap x || c.memberNames.contains x)
      if o3 != c.memberNames then .error (.typeError "~member order does not match _order_") else .ok ()

/-- The parts of `EnumType.__new__`, Lib/enum.py:481-693, that decide the members: `_ignore_`, the illegal names,
`_order_`, and the `__set_name__` calls. -/
def enumTypeNew (k : EKind) (d : EnumDict) : Py EClass :=
  let ignore := d.ignore ++ ["_ignore_".toList]
  let items := d.items.filter (fun p => !ignore.contains p.1)
  if d.memberNames.contains "mro".toList || d.memberNames.contains [] then
    .error (.valueError "~invalid enum member name(s)")
  else
    let order := items.lookup "_order_".toList
    let members := d.memberNames.map (fun n => (n, (items.lookup n).getD default))
    match ({ kind := k } : EClass).build members with
    | .error e => .error e
    | .ok c =>
      match c.checkOrder (orderList order) with
      | .error e => .error e
      | .ok () => .ok c

/-! ### Lookups -/

/-- What `_missing_` did. -/
inductive MissingRet where
  /-- `None`, as `Enum._missing_`, Lib/enum.py:1285-1287. -/
  | none
  /-- A member of the class. -/
  | member (name : Name)
  /-- Something else. -/
  | other
  /-- An exception of this class. -/
  | raises (e : PyExc)
  deriving Repr, DecidableEq, Inhabited

/-- The long search for an unhashable value, Lib/enum.py:1191-1196. -/
def EClass.search (c : EClass) (v : EV) : Py (Option Name) :=
  match c.unhashableMap.find? (fun p => p.2.contains v) with
  | some p =>
    match c.memberMap.lookup p.1 with
    | some m => .ok (some m)
    | none => .error (.keyError "~name")
  | none => .ok (c.findEqual v)

def EClass.found (c : EClass) (v : EV) : Py (Option Name) :=
  if v.hashable then .ok (c.value2member.lookup v) else c.search v

/-- `Enum.__new__`, Lib/enum.py:1175-1234, for a class that is not a `Flag`. `self` is `type(value) is cls`, and
`inProgress` the `_%s__in_progress` attribute, set while the class is being built. -/
def enumNew (c : EClass) (self : Option Name) (v : EV) (inProgress : Bool) (miss : MissingRet) : Py Name :=
  match self with
  | some m => .ok m
  | none =>
    match c.found v with
    | .error e => .error e
    | .ok (some n) => .ok n
    | .ok none =>
      if c.memberMap.isEmpty then
        if inProgress then .error (.typeError "do not use `super().__new__; call the appropriate __new__ directly")
        else .error (.typeError "~has no members defined")
      else
        match miss with
        | .member n => .ok n
        | .none => .error (.valueError "~is not a valid enum value")
        | .other => .error (.typeError "~error in _missing_: returned instead of None or a valid member")
        | .raises e => .error e

/-- `EnumType.__call__`, Lib/enum.py:729-739. `none` is the functional API, `_create_`, reached with `names` on a class
without members. -/
def enumCall (c : EClass) (self : Option Name) (value : Atom) (more : List Atom) (miss : MissingRet) :
    Option (Py Name) :=
  if !c.memberMap.isEmpty then
    some (enumNew c self (if more.isEmpty then .atom value else .tup (value :: more)) false miss)
  else if more.isEmpty then some (.error (.typeError "~has no members; specify `names=()`"))
  else none

/-- `EnumType.__contains__`, Lib/enum.py:758-769, for a class that is not a `Flag`. Both lists use `==`, so an
unhashable value does not raise. -/
def enumContains (c : EClass) (isMember : Bool) (value : EV) : Bool :=
  isMember || c.unhashableValues.contains value || c.hashableValues.contains value

/-- `EnumType.__contains__`, Lib/enum.py:760-769, for a `Flag` class. `none` is a value that is not an `int`, for
which `_missing_` raises `ValueError`, and which is in neither list. -/
def FlagCls.classContains (c : FlagCls) (value : Option Int) : Bool :=
  match value with
  | none => false
  | some i =>
    match c.missing i with
    | .ok (.flag _ _) => true
    | .ok (.plain _) => false
    | .error _ => c.members.any (fun p => (p.2 : Int) == i)

/-- `EnumType.__getitem__`, Lib/enum.py:800-804. -/
def EClass.getItem (c : EClass) (name : Name) : Py Name :=
  match c.memberMap.lookup name with
  | some m => .ok m
  | none => .error (.keyError "~name")

/-- `EnumType.__iter__`, Lib/enum.py:806-810: `_member_map_[name]` for the names of `_member_names_`. -/
def EClass.iter (c : EClass) : List Name := c.memberNames.filterMap (fun n => c.memberMap.lookup n)

/-- `EnumType.__reversed__`, Lib/enum.py:834-838. -/
def EClass.reversed (c : EClass) : List Name := c.memberNames.reverse.filterMap (fun n => c.memberMap.lookup n)

/-- `EnumType.__len__`, Lib/enum.py:812-816. -/
def EClass.len (c : EClass) : Nat := c.memberNames.length

/-- `EnumType.__setattr__`, Lib/enum.py:840-851. -/
def EClass.setAttr (c : EClass) (name : Name) : Py Unit :=
  if (c.memberMap.lookup name).isSome then .error (.named "AttributeError" "~cannot reassign member") else .ok ()

/-- `EnumType.__delattr__`, Lib/enum.py:771-776. `attrs` are the other attributes of the class. -/
def EClass.delAttr (c : EClass) (attrs : List Name) (name : Name) : Py Unit :=
  if (c.memberMap.lookup name).isSome then .error (.named "AttributeError" "~cannot delete member")
  else if attrs.contains name then .ok ()
  else .error (.named "AttributeError" "~")

/-- `Enum._add_alias_`, Lib/enum.py:1236-1237: `_add_member_`. -/
def EClass.addAlias (c : EClass) (self name : Name) : Py EClass := c.addToMap name self

/-- The end of `Enum._add_value_alias_`, Lib/enum.py:1253-1262. `memberName` is `member.name`, which is `_name_` unless
the class defines a `name` of its own: :1262 reads `self.name`, and `Enum.__new__` then looks that up with `cls[name]`. -/
def EClass.bindValue (c : EClass) (memberName : Name → Name) (self : Name) (value : EV) : EClass :=
  if value.hashable then
    { c with value2member := setDefault c.value2member value self, hashableValues := c.hashableValues ++ [value] }
  else
    { c with unhashableValues := c.unhashableValues ++ [value],
             unhashableMap := appendTo c.unhashableMap (memberName self) value }

/-- `Enum._add_value_alias_`, Lib/enum.py:1239-1262. At :1251 the `ValueError` is built with
`cls._value2member_map_[value]`, on an unhashable value, so a `TypeError` comes out instead. -/
def EClass.addValueAlias (c : EClass) (memberName : Name → Name) (self : Name) (value : EV) : Py EClass :=
  if value.hashable then
    match c.value2member.lookup value with
    | some m => if m != self then .error (.valueError "~is already bound") else .ok c
    | none => .ok (c.bindValue memberName self value)
  else
    match c.findEqual value with
    | some m => if m != self then .error (.typeError "~unhashable") else .ok c
    | none => .ok (c.bindValue memberName self value)

/-! ### The functional API -/

/-- `names` of `_create_`. -/
inductive Names where
  | text (s : List Char)
  | seq (l : List Name)
  | pairs (l : List (Name × EV))
  deriving Repr, DecidableEq, Inhabited

/-- The values of `_create_`, Lib/enum.py:875-879: `count` from `enumerate`, not the number of members, and a list of
its own. -/
def createPairs (g : Gen) (start : Int) (count : Nat) (last : List EV) : List Name → Py (List (Name × EV))
  | [] => .ok []
  | n :: r =>
    match g.call n start count last with
    | .error e => .error e
    | .ok a =>
      match createPairs g start (count + 1) (last ++ [.atom a]) r with
      | .error e => .error e
      | .ok rest => .ok ((n, .atom a) :: rest)

/-- `EnumType._create_`, Lib/enum.py:853-907. `first` is `first_enum._generate_next_value_`. -/
def enumCreate (k : EKind) (first : Gen) (cls : Name) (start : Int) (names : Names) : Py EClass :=
  let pairs : Py (List (Name × EV)) := match names with
    | .text s => createPairs first start 0 [] (splitNames s)
    | .seq l => createPairs first start 0 [] l
    | .pairs l => .ok l
  match pairs with
  | .error e => .error e
  | .ok ps =>
    match enumPrepare cls first with
    | .error e => .error e
    | .ok d =>
      match d.setAll ps with
      | (_, some e) => .error e
      | (d', none) => enumTypeNew k d'

/-! ### `Flag` operators -/

/-- The right operand of a `Flag` operator. -/
inductive FlagArg where
  /-- An instance of the class; `none` when its `_value_` is `None`. -/
  | same (v : Option Nat)
  /-- An instance of the mixed-in type, `int` for an `IntFlag`. -/
  | mixin (v : Int)
  /-- Anything else. -/
  | other
  deriving Repr, DecidableEq, Inhabited

/-- `Flag._get_value`, Lib/enum.py:1608-1613: the outer `none` is `NotImplemented`. -/
def getValue (intMixin : Bool) : FlagArg → Option (Option Int)
  | .same v => some (v.map Int.ofNat)
  | .mixin v => if intMixin then some (some v) else none
  | .other => none

/-- A bit operation on two Python ints, through two's complement on enough bits. -/
def twos (op : Nat → Nat → Nat) (a b : Int) : Int :=
  let w := bitLength a.natAbs + bitLength b.natAbs + 2
  let m : Int := 2 ^ w
  let r : Int := (op (a % m).toNat (b % m).toNat : Nat)
  if r * 2 ≥ m then r - m else r

/-- `Flag.__or__`, `__and__`, `__xor__`, Lib/enum.py:1615-1646, and their reflected names, :1659-1661: `NotImplemented`,
the check of both values for `None`, and the class called on the bit operation. -/
def flagBin (c : FlagCls) (intMixin : Bool) (op : Nat → Nat → Nat) (self : Option Nat) (other : FlagArg) :
    Option (Py FlagVal) :=
  match getValue intMixin other with
  | none => none
  | some o =>
    match self, o with
    | some s, some v => some (c.call (twos op s v))
    | _, _ => some (.error (.typeError "~cannot be combined with other flags"))

/-- `Flag.__invert__`, Lib/enum.py:1648-1657, with its `_inverted_` cache. -/
def flagInvert (c : FlagCls) (cached : Option FlagVal) (self : Option Nat) : Py (FlagVal × Option FlagVal) :=
  match self with
  | none => .error (.typeError "~cannot be inverted")
  | some a =>
    match cached with
    | some v => .ok (v, cached)
    | none =>
      match c.invert a with
      | .error e => .error e
      | .ok v => .ok (v, some v)

/-- `Flag.__contains__`, Lib/enum.py:1571-1579: an object of another class is a `TypeError`. -/
def flagIn (self : Nat) (other : FlagArg) : Py Bool :=
  match other with
  | .same (some o) => .ok (flagContains self o)
  | _ => .error (.typeError "~unsupported operand type(s) for 'in'")

/-- `Flag.__bool__`, Lib/enum.py:1605-1606. -/
def flagBool (self : Nat) : Bool := self != 0

/-! ### `unique` and `verify` -/

/-- `unique`, Lib/enum.py:1676-1689. It compares `name` with `member.name`, not `member._name_`. -/
def EClass.unique (c : EClass) (memberName : Name → Name) : Py Unit :=
  if c.memberMap.any (fun p => p.1 != memberName p.2) then .error (.valueError "~duplicate values found in")
  else .ok ()

/-- The `UNIQUE` check, Lib/enum.py:1978-1988. -/
def EClass.verifyUnique (c : EClass) (memberName : Name → Name) : Py Unit :=
  if c.memberMap.any (fun p => p.1 != memberName p.2) then .error (.valueError "~aliases found in") else .ok ()

/-- `[e.value for e in enumeration]`. -/
def EClass.intValues (c : EClass) : List Int :=
  c.memberNames.filterMap (fun n => match c.valueOf n with
    | some (.atom (.int i)) => some i
    | _ => none)

/-- The integers from `a` up to, and not including, `b`. -/
def intRange (a b : Int) : List Int := (List.range (b - a).toNat).map (fun (i : Nat) => a + (i : Int))

/-- The `CONTINUOUS` check, Lib/enum.py:1989-2010, on `int` values. -/
def EClass.verifyContinuous (c : EClass) : Py Unit :=
  match c.intValues with
  | [] => .ok ()
  | i :: is =>
    let low := is.foldl min i
    let high := is.foldl max i
    if low = high then .ok ()
    else
      let values := i :: is
      let missing : List Int :=
        if c.kind == .flag then
          (intRange (bitLength low.natAbs) (bitLength high.natAbs - 1)).filter
            (fun k => !values.contains (2 ^ k.toNat))
        else (intRange (low + 1) high).filter (fun k => !values.contains k)
      if missing.isEmpty then .ok () else .error (.valueError "~missing values")

/-- An alias with a bit that is not the value of a member, Lib/enum.py:2018-2030. A negative value has `toNat` 0, and
so no bits, which is the `continue` at :2022-2024. -/
def EClass.missesName (c : EClass) (p : Name × Name) : Bool :=
  if c.memberNames.contains p.1 then false else
  match c.valueOf p.2 with
  | some (.atom (.int v)) => (bitsOf v.toNat).any (fun b => !c.intValues.contains (b : Int))
  | _ => false

/-- The `NAMED_FLAGS` check, Lib/enum.py:2012-2045, on `int` values. -/
def EClass.verifyNamed (c : EClass) : Py Unit :=
  if c.memberMap.any c.missesName then .error (.valueError "~invalid Flag") else .ok ()

/-- One of the checks of `verify`. -/
inductive Check where
  | unique
  | continuous
  | named
  deriving Repr, DecidableEq, Inhabited

def EClass.verifyOne (c : EClass) (memberName : Name → Name) : Check → Py Unit
  | .unique => c.verifyUnique memberName
  | .continuous => c.verifyContinuous
  | .named => c.verifyNamed

def EClass.verifyAll (c : EClass) (memberName : Name → Name) : List Check → Py Unit
  | [] => .ok ()
  | k :: r =>
    match c.verifyOne memberName k with
    | .error e => .error e
    | .ok () => c.verifyAll memberName r

/-- `verify.__call__`, Lib/enum.py:1968-2046. `isEnum` is `issubclass(enumeration, Enum)`. -/
def EClass.verifyCall (c : EClass) (isEnum : Bool) (memberName : Name → Name) (checks : List Check) : Py Unit :=
  if !isEnum then .error (.typeError "the 'verify' decorator only works with Enum and Flag")
  else c.verifyAll memberName checks

end PyLean.CoreLibs.EnumDC
