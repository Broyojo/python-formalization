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

/-- The right operand of `fmt % args`: a tuple supplies its items, anything else is one argument. Each is given as the
result of the conversion formatting runs on it (`repr` for `%r`). -/
inductive FmtArgs where
  | one (r : Py String)
  | tuple (rs : List (Py String))

/-- The conversions of `fmt % (a, b, ...)` past the first `k`, Objects/unicode_format.c: each takes the next item
(`unicode_format_getnextarg`, :95-113, "not enough arguments" when none is left) and runs its conversion, the first
exception going out; items left over at the end are "not all arguments converted" (:1094-1101). -/
def fmtItems (total : Nat) : Nat → List (Py String) → Py Unit
  | 0, [] => .ok ()
  | 0, rest => .error (.typeError
      s!"not all arguments converted during string formatting (required {total - rest.length}, got {total})")
  | _ + 1, [] => .error (.typeError s!"not enough arguments for format string (got {total})")
  | k + 1, r :: rest =>
    match r with
    | .error e => .error e
    | .ok _ => fmtItems total k rest

/-- `fmt % args` for a format with `n` conversions and no mapping key, Objects/unicode_format.c:1050-1102. A single
argument is consumed by the first conversion (`unicode_format_getnextarg`, :97-113); a second conversion then has none.
With no conversion, `n = 0`, a single argument is left over, the `TypeError` of :1094-1101, only when it is not a
mapping: `PyMapping_Check` (:1062-1065), true of a `dict`, a `list` or a `bytes`, turns that check off, so `'x' % {}` is
`'x'`. `.one` does not say which, so `pyFormat 0 (.one r)` is right only for an argument that is not a mapping. No
caller passes `n = 0`: every format this model runs has one conversion. -/
def pyFormat (n : Nat) : FmtArgs → Py Unit
  | .one r =>
    match n with
    | 0 => .error (.typeError "not all arguments converted during string formatting (required 0, got 1)")
    | k + 1 =>
      match r with
      | .error e => .error e
      | .ok _ => if k = 0 then .ok () else .error (.typeError "not enough arguments for format string (got 1)")
  | .tuple rs => fmtItems rs.length n rs

/-- `raise E(fmt % args)`: formatting runs first (`r`), and its exception goes out instead of `e`. -/
def withRepr {γ β : Type} (r : Py γ) (e : PyExc) : Py β :=
  match r with
  | .error e' => .error e'
  | .ok _ => .error e

@[simp] theorem withRepr_ne_ok {γ β : Type} (r : Py γ) (e : PyExc) (s : β) : ((withRepr r e : Py β) = .ok s) = False := by
  cases r <;> simp [withRepr]

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
  /-- `RObj(re)` of the difftest: an object whose `__repr__` raises the exception class `re` names; `id` tells instances
  apart. -/
  | robj (re : String) (id : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The exception `cls(msg)` of a test object. -/
def pvExc (cls msg : String) : PyExc :=
  match cls with
  | "KeyError" => .keyError s!"'{msg}'"
  | "KSub" => .named "KSub" s!"'{msg}'"
  | "KT" => .named "KT" s!"'{msg}'"
  | "TypeError" => .typeError msg
  | "ValueError" => .valueError msg
  | c => .named c msg

/-- `repr(v)`: only an `RObj` runs code that raises. -/
def EV.repr : EV → Py String
  | .robj re _ => .error (pvExc re "repr")
  | _ => .ok ""

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

/-- The name of a tuple item of `_ignore_`: only a `str` can equal a key. -/
def Atom.ignoreName : Atom → Option Name
  | .str s => some s.toList
  | _ => none

/-- The `_ignore_` branch, Lib/enum.py:376-381: a `str` is split, anything else is `list(value)`, and `set(value)` at
:381 hashes the items. A list of names is itself; the model's list `[i]` holds an `int`, which no key equals; a tuple
gives its items, of which only a `str` can be a key, and an unhashable item is the `TypeError` of `set`. -/
def ignoreList : EV → Py (List Name)
  | .atom (.str s) => .ok (splitNames s.toList)
  | .names l => .ok l
  | .atom (.list _) => .ok []
  | .tup l => if l.all Atom.hashable then .ok (l.filterMap Atom.ignoreName) else .error (.typeError "~unhashable type")
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

/-- `'%r already defined as %r' % (key, self[key])`, :392 and :406: the `repr` of the key (a `str`) and of what the
namespace holds under it, whose exception goes out instead of the `TypeError`. -/
def EnumDict.storedRepr (d : EnumDict) (key : Name) : Py String :=
  match d.items.lookup key with
  | some v => v.repr
  | none => .ok ""

/-- The last branch of `__setitem__`, Lib/enum.py:404-442: a new member. -/
def EnumDict.storeMember (d : EnumDict) (key : Name) (value0 : EV) : Py EnumDict :=
  if d.has key then withRepr (d.storedRepr key) (.typeError "~already defined as") else
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
  else if d.memberNames.contains key then withRepr (d.storedRepr key) (.typeError "~already defined as")
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

/-- The bases of a builtin exception class, for the classes the model raises. -/
def builtinParent : String → List String
  | "KeyError" | "IndexError" => ["LookupError"]
  | "UnicodeDecodeError" => ["UnicodeError"]
  | "UnicodeError" => ["ValueError"]
  | "OverflowError" | "ZeroDivisionError" => ["ArithmeticError"]
  | "LookupError" | "TypeError" | "ValueError" | "AttributeError" | "RuntimeError" | "NameError" | "ArithmeticError"
  | "AssertionError" => ["Exception"]
  | "Exception" => ["BaseException"]
  | _ => []

/-- `issubclass(c, cls)`: `cls` is `c` or an ancestor through any of the bases `parent` gives (all of `c.__mro__`). -/
def subclassOf (parent : String → List String) : Nat → String → String → Bool
  | 0, _, _ => false
  | f + 1, c, cls => c == cls || (parent c).any (fun p => subclassOf parent f p cls)

/-- `isinstance(e, cls)`, the test of `except cls:`, which catches subclasses too. Ancestors are followed to a depth of
1000 classes; a deeper exception class hierarchy is not modelled. -/
def excIs (parent : String → List String) (e : PyExc) (cls : String) : Bool := subclassOf parent 1000 e.className cls

/-- `EnumDict.update`, Lib/enum.py:449-457: the `except AttributeError` covers the loop over `keys()` too, so an
`AttributeError` from `__setitem__` restarts the loop on the iteration of the mapping. -/
def EnumDict.update (d : EnumDict) (members : UpdateArg) (more : List (Name × EV)) : Py EnumDict :=
  let first : Py EnumDict :=
    match members with
    | .mapping items =>
      match d.setAll items with
      | (d', none) => .ok d'
      | (d', some e) =>
        if excIs builtinParent e "AttributeError" then d'.unpackKeys (items.map Prod.fst) else .error e
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
  /-- The class's own `__repr__`, if it defines one: what `repr(member)` gives for each member, by its `_name_`: a string,
  its exception, or the `TypeError` of Objects/object.c:791-796 for a result that is not a `str`. -/
  ownRepr : Option (Name → Py String) := none
  deriving Inhabited

def EClass.valueOf (c : EClass) (n : Name) : Option EV := c.values.lookup n

/-- The first member with this value, Lib/enum.py:290-293 and :1194-1196. -/
def EClass.findEqual (c : EClass) (v : EV) : Option Name :=
  (c.memberMap.find? (fun p => c.valueOf p.2 == some v)).map Prod.snd

/-- The lookup that decides aliases, Lib/enum.py:286-295. -/
def EClass.aliasOf (c : EClass) (v : EV) : Option Name :=
  if v.hashable then c.value2member.lookup v else c.findEqual v

/-! ### `StrEnum.__new__`, Lib/enum.py:1376-1395 -/

/-- An argument of `StrEnum.__new__`: an exact `str`, a `bytes`, or anything else. A subclass of `str` with its own
`__str__` is not modelled. -/
inductive SArg (α : Type) where
  | str (s : String)
  | bytes (b : List Nat)
  /-- Any other object with the buffer protocol, such as a `bytearray` or a `memoryview`. -/
  | buffer (b : List Nat)
  | other (x : α)
  deriving Repr, DecidableEq

/-- `bytes.decode(encoding, errors)`: the codec lookup and the decoder. -/
abbrev Codec := List Nat → String → String → Py String

/-- `str(b, encoding, errors)` for a `bytes`, Objects/unicodeobject.c:3480-3489, or another buffer, :3498-3515: an empty one is `''` before
any codec lookup (in a release build without `-X dev`, :532-536), anything else goes to the codec. -/
def strDecode (codec : Codec) (bs : List Nat) (enc errors : String) : Py String :=
  if bs = [] then .ok "" else codec bs enc errors

/-- `repr(x)` of an argument: only an object of another type runs code of its own. -/
def SArg.repr {α : Type} (reprA : α → Py String) : SArg α → Py String
  | .other x => reprA x
  | _ => .ok ""

/-- An argument as the right operand of `%` with no tuple around it, as at :1391: a tuple object supplies its items. -/
def SArg.fmtOne {α : Type} (tupA : α → Option (List α)) (reprA : α → Py String) : SArg α → FmtArgs
  | .other x =>
    match tupA x with
    | some xs => .tuple (xs.map reprA)
    | none => .one (reprA x)
  | _ => .one (.ok "")

/-- `repr` of a tuple of arguments: each item in turn, the first exception going out. -/
def SArg.reprAll {α : Type} (reprA : α → Py String) : List (SArg α) → Py Unit
  | [] => .ok ()
  | x :: r =>
    match x.repr reprA with
    | .error e => .error e
    | .ok _ => SArg.reprAll reprA r


/-- `str(a, encoding, errors)`, Objects/unicodeobject.c `PyUnicode_FromEncodedObject`: a buffer is decoded, a `str` is
the `TypeError` "decoding str is not supported", anything else the `TypeError` of a missing buffer. -/
def strDecodeArg (codec : Codec) {α : Type} (a : SArg α) (enc er : String) : Py String :=
  match a with
  | .bytes bs => strDecode codec bs enc er
  | .buffer bs => strDecode codec bs enc er
  | .str _ => .error (.typeError "decoding str is not supported")
  | .other _ => .error (.typeError "~decoding to str: need a bytes-like object")

/-- `StrEnum.__new__`, Lib/enum.py:1376-1395: the checks of :1378-1391 in order, then `str(*values)` at :1392. With no
argument that is `''`, with one `str` that `str`; with an encoding, and `errors` (`'strict'` when not given), a `bytes` is
decoded by the codec, a `str` is the `TypeError` "decoding str is not supported", and anything else the `TypeError` of
`PyUnicode_FromEncodedObject`, Objects/unicodeobject.c. -/
def strEnumNewG (codec : Codec) {α : Type} (tupA : α → Option (List α)) (reprA : α → Py String)
    (values : List (SArg α)) : Py String :=
  if values.length > 3 then withRepr (SArg.reprAll reprA values) (.typeError "~too many arguments for str()")
  else
    match values with
    | [] => .ok ""
    | [a] =>
      match a with
      | .str s => .ok s
      | _ => withRepr (a.repr reprA) (.typeError "~is not a string")
    | a :: b :: r =>
      match b with
      | .str enc =>
        match r with
        | [] => strDecodeArg codec a enc "strict"
        | [.str er] => strDecodeArg codec a enc er
        | [c] => withRepr (pyFormat 1 (c.fmtOne tupA reprA)) (.typeError "~errors must be a string")
        | _ => .error (.typeError "~errors must be a string")
      | _ => withRepr (b.repr reprA) (.typeError "~encoding must be a string")

/-- The ASCII and Latin-1 codecs, for the difftest: any other encoding is unknown, and the error handler is looked up
only when a byte does not decode, with `strict`, `ignore` and `replace` known and any other name taken as unknown (the
names the difftest uses are). -/
def pyCodec : Codec := fun bs enc errors =>
  if enc = "latin-1" then .ok (String.ofList (bs.map Char.ofNat))
  else if enc = "ascii" then
    if bs.all (· < 128) then .ok (String.ofList (bs.map Char.ofNat))
    else if errors = "strict" then .error (.named "UnicodeDecodeError" "~'ascii' codec can't decode")
    else if errors = "ignore" then .ok (String.ofList ((bs.filter (· < 128)).map Char.ofNat))
    else if errors = "replace" then
      .ok (String.ofList (bs.map (fun b => if b < 128 then Char.ofNat b else '�')))
    else .error (.named "LookupError" s!"unknown error handler name '{errors}'")
  else .error (.named "LookupError" s!"unknown encoding: {enc}")

/-- `Atom` as an argument of `StrEnum.__new__`: no `Atom` is a `bytes`. -/
def Atom.toSArg : Atom → SArg Atom
  | .str s => .str s
  | a => .other a

/-- `StrEnum.__new__` on the values of a class body, which are not `bytes`. -/
def strEnumNew (values : List Atom) : Py String :=
  strEnumNewG pyCodec (fun _ => none) (fun _ => .ok "") (values.map Atom.toSArg)

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

/-- `repr(member)`: the class's own `__repr__`, whatever it does, or else `Enum.__repr__`, Lib/enum.py:1289-1291,
`<C.A: repr(_value_)>`, which runs the value's `repr`. -/
def EClass.memberRepr (c : EClass) (m : Name) : Py String :=
  match c.ownRepr with
  | some r => r m
  | none =>
    match c.valueOf m with
    | some v => v.repr
    | none => .ok ""

/-- `EnumType._add_member_`, :1072-1075, :1115: `'%r is already bound: %r' % (name, cls._member_map_[name])` formats the
member already bound, whose `repr` can raise instead of the `NameError`. -/
def EClass.addToMap (c : EClass) (name member : Name) : Py EClass :=
  match c.memberMap.lookup name with
  | some m => if m != member then withRepr (c.memberRepr m) (.named "NameError" "~is already bound") else .ok c
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
  /-- Something else, with its `repr`. -/
  | other (rr : Py String)
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
        | .other _ => .error (.typeError "~error in _missing_: returned instead of None or a valid member")
        | .raises e => .error e

/-- `EnumType.__contains__`, Lib/enum.py:758-769, for a class that is not a `Flag`. Both lists use `==`, so an
unhashable value does not raise. -/
def enumContains (c : EClass) (isMember : Bool) (value : EV) : Bool :=
  isMember || c.unhashableValues.contains value || c.hashableValues.contains value

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

/-- `f"{m}"`, for the member `m` whose `_value_` is `None` (a class has at most one: a second `None` is an alias of it,
:283-296). `FORMAT_SIMPLE`, Python/bytecodes.c:5883-5897, calls `PyObject_Format(m, NULL)`, Objects/abstract.c:853-909,
which runs `type(m).__format__(m, '')`: the class's own, else `Enum.__format__`, Lib/enum.py:1325-1326,
`str.__format__(str(m), '')`, so the class's own `__str__`, else `Flag.__str__`, :1598-1603, which returns `'F.A'`. -/
def FlagCls.fmtNone (c : FlagCls) : Py String :=
  match c.ownFormat with
  | some r => r
  | none =>
    match c.ownStr with
    | some r => r
    | none => .ok ""

/-- `Flag.__or__`, `__and__`, `__xor__`, Lib/enum.py:1615-1646, and their reflected names, :1659-1661: `NotImplemented`,
the check of `self`, then `other`, for a `None` value, whose `TypeError` is built with the f-string of :1622, :1633 and
:1644, which runs the class's `__format__` or `__str__` on that member first, and the class called on the bit
operation. -/
def flagBin (c : FlagCls) (intMixin : Bool) (op : Nat → Nat → Nat) (self : Option Nat) (other : FlagArg) :
    Option (Py FlagVal) :=
  match getValue intMixin other with
  | none => none
  | some o =>
    match self, o with
    | some s, some v => some (c.call (twos op s v))
    | _, _ => some (withRepr c.fmtNone (.typeError "~cannot be combined with other flags"))

/-- `Flag.__invert__`, Lib/enum.py:1648-1657, with its `_inverted_` cache; the `TypeError` of a `None` value is built
with the f-string of :1650. -/
def flagInvert (c : FlagCls) (cached : Option FlagVal) (self : Option Nat) : Py (FlagVal × Option FlagVal) :=
  match self with
  | none => withRepr c.fmtNone (.typeError "~cannot be inverted")
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

end PyLean.CoreLibs.EnumDC
