import PyLean.Core

/-!
`Lib/enum.py` and `Lib/dataclasses.py` (CPython 3.14.7): a `Flag` class and a dataclass as data, and
mirrors of the algorithms on them. Python's `&` with a non-negative mask on a possibly negative `int`
is `andMask`. The metaclass machinery that builds the class object is not modelled here.
-/

namespace PyLean.CoreLibs.EnumDC

open PyLean

/-! ### Name classification, Lib/enum.py:46-88 -/

/-- `_is_dunder`, Lib/enum.py:46-55. -/
def isDunder (name : List Char) : Bool :=
  name.length > 4 && name.take 2 == ['_', '_'] && name.reverse.take 2 == ['_', '_'] &&
    name[2]? != some '_' && name.reverse[2]? != some '_'

/-- `_is_sunder`, Lib/enum.py:57-66. -/
def isSunder (name : List Char) : Bool :=
  name.length > 2 && name.head? == some '_' && name.reverse.head? == some '_' &&
    name[1]? != some '_' && name.reverse[1]? != some '_'

/-- `_is_private`, Lib/enum.py:77-88. -/
def isPrivate (cls name : List Char) : Bool :=
  let pattern := ['_'] ++ cls ++ ['_', '_']
  name.length > pattern.length && pattern.isPrefixOf name &&
    (name.reverse[0]? != some '_' || name.reverse[1]? != some '_')

/-! ### Bits -/

/-- `_is_single_bit`, Lib/enum.py:90-97: `num &= num - 1`. -/
def isSingleBit (num : Nat) : Bool :=
  if num = 0 then false else (num &&& (num - 1)) == 0

/-- `_high_bit`, Lib/enum.py:639-643. -/
def highBit (value : Nat) : Int := (bitLength value : Int) - 1

def lowBitAux : (fuel : Nat) → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n % 2 = 1 then 1 else 2 * lowBitAux f (n / 2)

/-- The lowest set bit, `num & (~num + 1)`. -/
def lowBit (n : Nat) : Nat := lowBitAux (bitLength n) n

/-- `_iter_bits_lsb`, Lib/enum.py:114-124, for a non-negative `num`: `num ^= b` until zero. -/
def iterBits : (fuel : Nat) → Nat → List Nat
  | 0, _ => []
  | fuel + 1, num =>
    if num = 0 then [] else
      let b := lowBit num
      b :: iterBits fuel (num ^^^ b)

def bitsOf (n : Nat) : List Nat := iterBits (bitLength n + 1) n

/-- Python `v & m` for a non-negative mask `m`. -/
def andMask (v : Int) (m : Nat) : Nat := (v % (2 ^ bitLength m : Nat)).toNat &&& m

/-- `FlagBoundary`, Lib/enum.py:1394-1397. -/
inductive Boundary where
  | strict | conform | eject | keep
  deriving Repr, DecidableEq, Inhabited

/-- A `Flag` class: its members, aliases included, in definition order. Members have values `>= 0`. -/
structure FlagCls where
  name : String
  members : List (String × Nat)
  boundary : Boundary
  deriving Repr, DecidableEq, Inhabited

/-- `_flag_mask_`, Lib/enum.py:277. -/
def FlagCls.flagMask (c : FlagCls) : Nat := c.members.foldl (fun m p => m ||| p.2) 0

/-- `_singles_mask_`, Lib/enum.py:278-279. -/
def FlagCls.singlesMask (c : FlagCls) : Nat :=
  c.members.foldl (fun m p => if isSingleBit p.2 then m ||| p.2 else m) 0

/-- `_all_bits_`, Lib/enum.py:280. -/
def FlagCls.allBits (c : FlagCls) : Nat := 2 ^ bitLength c.flagMask - 1

/-- `_value2member_map_`: the first member with this value, the rest being aliases. -/
def FlagCls.memberOf (c : FlagCls) (v : Nat) : Option String :=
  (c.members.find? (fun p => p.2 == v)).map Prod.fst

/-- The canonical members, in definition order, one per value. -/
def FlagCls.canonical (c : FlagCls) : List (String × Nat) :=
  c.members.filter (fun p => c.memberOf p.2 == some p.1)

/-- A value of a `Flag` class, or the plain `int` of an ejected value. -/
inductive FlagVal where
  | flag (value : Nat) (name : Option String)
  | plain (v : Int)
  deriving Repr, DecidableEq, Inhabited

/-- `Flag._iter_member_by_value_`, Lib/enum.py:1428-1433, and `_iter_member_by_def_`, :1438-1445: the
members for the bits of `value & _flag_mask_`, in value order, or in definition order for a class
whose members are not sorted, Lib/enum.py:640-642. `none` is `_value2member_map_.get(val)` failing. -/
def FlagCls.iterMembers (c : FlagCls) (value : Nat) : List (Option (String × Nat)) :=
  let byValue := (bitsOf (value &&& c.flagMask)).map (fun v => (c.memberOf v).map (fun n => (n, v)))
  let values := (c.canonical.filter (fun p => isSingleBit p.2)).map Prod.snd
  if decide (values.Pairwise (· ≤ ·)) then byValue
  else
    (c.canonical.filterMap (fun p =>
      if (bitsOf (value &&& c.flagMask)).contains p.2 then some (some p) else none)) ++
    (byValue.filter Option.isNone)

/-- The name loop of `Flag._missing_`, Lib/enum.py:1510-1529. -/
def FlagCls.nameOf (c : FlagCls) (value memberValue aliases : Nat) : Py (Option String) :=
  if memberValue != 0 || aliases != 0 then
    let first := (c.iterMembers memberValue).filterMap id
    let all :=
      if aliases != 0 then
        let v := memberValue ||| aliases
        first ++ (c.canonical.filter (fun p =>
          !first.contains p && p.2 != 0 && (p.2 &&& v) == p.2))
      else first
    let combined := all.foldl (fun m p => m ||| p.2) 0
    let value' := if aliases != 0 then memberValue ||| aliases else value
    let unknown := value' ^^^ combined
    let joined := "|".intercalate (all.map Prod.fst)
    if combined == 0 then .ok none
    else if unknown != 0 && c.boundary == .strict then
      .error (.valueError s!"~no members with value {unknown}")
    else if unknown != 0 then .ok (some s!"{joined}|{unknown}")
    else .ok (some joined)
  else .ok none

/-- `Flag._missing_`, Lib/enum.py:1448-1538, for an `int`. The pseudo-member is identified by its value
and name, so the singleton bookkeeping at :1535-1537 has no effect here. -/
def FlagCls.missing (c : FlagCls) (value : Int) : Py FlagVal := do
  let fm := c.flagMask
  let sm := c.singlesMask
  let ab := c.allBits
  let abi : Int := ab
  let oob := !(-abi - 1 ≤ value ∧ value ≤ abi) || andMask value (ab ^^^ fm) != 0
  let v1 : Int ← if oob then
      match c.boundary with
      | .strict => throw (.valueError "~invalid value")
      | .conform => pure (andMask value fm : Int)
      | .eject => return .plain value
      | .keep =>
        if value < 0 then
          pure ((max (ab + 1) (2 ^ bitLength value.natAbs) : Nat) + value)
        else pure value
    else pure value
  let v2 : Nat := (if v1 < 0 then abi + 1 + v1 else v1).toNat
  let unknown := notAnd fm v2
  let aliases := notAnd sm v2
  let memberValue := v2 &&& sm
  if unknown != 0 && c.boundary != .keep then throw (.valueError "~unknown values")
  let name ← c.nameOf v2 memberValue aliases
  -- `_value2member_map_.setdefault(value, pseudo_member)`, :1535: an existing member wins
  pure (.flag v2 (match c.memberOf v2 with
    | some n => some n
    | none => name))

/-- `Color(value)`: `Enum.__new__`, Lib/enum.py:1147-1206, for a `Flag` and an `int`: the value map, then
`_missing_`. -/
def FlagCls.call (c : FlagCls) (value : Int) : Py FlagVal :=
  if value ≥ 0 then
    match c.memberOf value.toNat with
    | some n => .ok (.flag value.toNat (some n))
    | none => c.missing value
  else c.missing value

/-- `Flag.__or__`, `__and__`, `__xor__`, Lib/enum.py:1584-1615, on two values of the class. -/
def FlagCls.orOp (c : FlagCls) (a b : Nat) : Py FlagVal := c.call (a ||| b : Nat)
def FlagCls.andOp (c : FlagCls) (a b : Nat) : Py FlagVal := c.call (a &&& b : Nat)
def FlagCls.xorOp (c : FlagCls) (a b : Nat) : Py FlagVal := c.call (a ^^^ b : Nat)

/-- `Flag.__invert__`, Lib/enum.py:1617-1626, without the cache: `~value` for `EJECT` and `KEEP`, and
`_singles_mask_ & ~value` otherwise. -/
def FlagCls.invert (c : FlagCls) (a : Nat) : Py FlagVal :=
  match c.boundary with
  | .eject | .keep => c.call (-(a : Int) - 1)
  | .strict | .conform => c.call (notAnd a c.singlesMask : Nat)

/-- `Flag.__contains__`, Lib/enum.py:1540-1548. -/
def flagContains (self other : Nat) : Bool := (other &&& self) == other

/-- `Flag.__len__`, Lib/enum.py:1556-1557: `self._value_.bit_count()`. -/
def bitCount (n : Nat) : Nat := (bitsOf n).length

/-- `Flag.__repr__`, Lib/enum.py:1559-1565. -/
def flagRepr (cls : String) (name : Option String) (value : Nat) : String :=
  match name with
  | none => s!"<{cls}: {value}>"
  | some n => s!"<{cls}.{n}: {value}>"

/-- `Flag.__str__`, Lib/enum.py:1567-1572. -/
def flagStr (cls : String) (name : Option String) (value : Nat) : String :=
  match name with
  | none => s!"{cls}({value})"
  | some n => s!"{cls}.{n}"

/-- `Flag._generate_next_value_`, Lib/enum.py:1409-1425. -/
def flagNext (start : Option Nat) (count : Nat) (last : List Nat) : Nat :=
  if count = 0 then start.getD 1
  else 2 ^ ((highBit (last.foldl max 0) + 1).toNat)

/-- `Enum._generate_next_value_`, Lib/enum.py:1237-1255, on `int` values. -/
def enumNext (start : Int) (last : List Int) : Int :=
  match last with
  | [] => start
  | x :: xs => xs.foldl max x + 1

/-- `unique`, Lib/enum.py:1645-1658: the `(alias, name)` pairs. -/
def aliasPairs (members : List (String × Nat)) : List (String × String) :=
  members.filterMap (fun p =>
    match (members.find? (fun q => q.2 == p.2)) with
    | some q => if q.1 != p.1 then some (p.1, q.1) else none
    | none => none)

/-! ### Dataclasses -/

/-- `_hash_action`, Lib/dataclasses.py:955-980. -/
inductive HashAction where
  | none | setNone | add | exception
  deriving Repr, DecidableEq

/-- The table, line by line. -/
def hashAction : Bool → Bool → Bool → Bool → HashAction
  | false, false, false, false => .none
  | false, false, false, true => .none
  | false, false, true, false => .none
  | false, false, true, true => .none
  | false, true, false, false => .setNone
  | false, true, false, true => .none
  | false, true, true, false => .add
  | false, true, true, true => .none
  | true, false, false, false => .add
  | true, false, false, true => .exception
  | true, false, true, false => .add
  | true, false, true, true => .exception
  | true, true, false, false => .add
  | true, true, false, true => .exception
  | true, true, true, false => .add
  | true, true, true, true => .exception

/-- A field spec, as `_process_class` sees it. -/
structure FieldSpec where
  name : String
  hasDefault : Bool := false
  init : Bool := true
  kwOnly : Bool := false
  compare : Bool := true
  /-- 0 is a plain field, 1 `ClassVar`, 2 `InitVar`. -/
  kind : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- `field(default=..., default_factory=...)`, Lib/dataclasses.py:408-409. -/
def fieldCheck (hasDefault hasFactory : Bool) : Py Unit :=
  if hasDefault && hasFactory then
    .error (.valueError "cannot specify both default and default_factory")
  else .ok ()

/-- `_fields_in_init_order`, Lib/dataclasses.py:415-421. -/
def initOrder (fs : List FieldSpec) : List FieldSpec × List FieldSpec :=
  (fs.filter (fun f => f.init && !f.kwOnly), fs.filter (fun f => f.init && f.kwOnly))

/-- The check at the top of `_init_fn`, Lib/dataclasses.py:680-688, on the standard fields. -/
def initDefaultOrder : Option String → List FieldSpec → Py Unit
  | _, [] => .ok ()
  | seen, f :: fs =>
    if f.init then
      if f.hasDefault then initDefaultOrder (some f.name) fs
      else
        match seen with
        | some s =>
          .error (.typeError s!"non-default argument '{f.name}' follows default argument '{s}'")
        | none => initDefaultOrder none fs
    else initDefaultOrder seen fs

/-- `_tuple_str`, Lib/dataclasses.py:424-433. -/
def tupleStr (obj : String) (names : List String) : String :=
  if names.isEmpty then "()"
  else s!"({",".intercalate (names.map fun n => obj ++ "." ++ n)},)"

/-- `fields()`, Lib/dataclasses.py:1454-1469: pseudo-fields are left out. -/
def fieldsOf (fs : List FieldSpec) : List FieldSpec := fs.filter (fun f => f.kind == 0)

/-- One step of the loop of `_replace`, Lib/dataclasses.py:1788-1805. -/
def replaceStep {α : Type} (changes : List (String × α)) (get : String → α)
    (acc : List (String × α)) (f : FieldSpec) : Py (List (String × α)) :=
  if f.kind == 1 then .ok acc
  else if !f.init then
    if (changes.lookup f.name).isSome then
      .error (.typeError
        s!"field {f.name} is declared with init=False, it cannot be specified with replace()")
    else .ok acc
  else if (changes.lookup f.name).isNone then
    if f.kind == 2 && !f.hasDefault then
      .error (.typeError s!"InitVar '{f.name}' must be specified with replace()")
    else .ok (acc ++ [(f.name, get f.name)])
  else .ok acc

/-- `_replace`, Lib/dataclasses.py:1782-1813: the keyword arguments of the new `__init__` call. `get` is
`getattr(self, f.name)`, and `changes` the caller's keywords. -/
def replaceArgs {α : Type} (fs : List FieldSpec) (get : String → α) (changes : List (String × α)) :
    Py (List (String × α)) :=
  fs.foldlM (replaceStep changes get) changes

/-- The decorator checks at Lib/dataclasses.py:1096-1102 and :1120. -/
def decoratorCheck (order eq frozen anyFrozenBase hasBase : Bool) : Py Unit :=
  if hasBase && anyFrozenBase && !frozen then
    .error (.typeError "cannot inherit non-frozen dataclass from a frozen one")
  else if hasBase && !anyFrozenBase && frozen then
    .error (.typeError "cannot inherit frozen dataclass from a non-frozen one")
  else if order && !eq then .error (.valueError "eq must be true if order is true")
  else .ok ()

end PyLean.CoreLibs.EnumDC
