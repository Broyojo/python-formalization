import PyLean.StrSearch.Model
import PyLean.RangeSlice.Model
import PyLean.Sequences.Common

/-!
`collections.UserString`, Lib/collections/__init__.py:1418-1667 (CPython 3.15.2).

A `str` is its code points (`PyLean.StrSearch.Seq`). The search, split, strip, replace and pad
methods use the mirrors of Objects/unicodeobject.c in `PyLean.StrSearch`. What depends on the
Unicode database or the format mini-languages (case mapping, `isalpha`, ..., `encode`, `%`,
`str.format`, `translate`, `hash`, `repr`, `int()`) is the abstract `UniOps`: for those the
wrapper's dispatch is modelled and the delegate is a parameter.

Scope: a `str` subclass is merged with `str` (`SArg.str`): `__init__` stores it as is
(`isinstance(seq, str)`, :1421) and the methods see only its text, so a subclass overriding `str`
methods or dunders is out of scope, as list subclasses overriding comparisons are in
`UserListG.lean`.

The point of the model is the first lines of each method: which argument is unwrapped with
`if isinstance(x, UserString): x = x.data`, which result is wrapped in `self.__class__`. The
arguments therefore carry their Python kind (`SArg`), and `str`'s own argument check is
written out, with its `TypeError`.
-/

namespace PyLean.CoreLibs.Coll

open PyLean
open PyLean.StrSearch
open PyLean.RangeSlice (Slice listSlicePositions)

/-- A `UserString`: `self.data`, and `type(self).__name__`. -/
structure US where
  cls : String
  data : Seq
  deriving Repr, DecidableEq

/-- An argument of a `str`-like parameter: a `str`, a `UserString`, or anything else (`ty` is the
type name, `text` is `str(obj)`). -/
inductive SArg where
  | str (s : Seq)
  | user (s : Seq)
  | other (ty : String) (text : Seq)
  deriving Repr, DecidableEq

/-- `type(a).__name__`. -/
def SArg.ty : SArg → String
  | .str _ => "str"
  | .user _ => "UserString"
  | .other ty _ => ty

/-- `%T` of an argument: the fully qualified name of its type. -/
def SArg.fullTy : SArg → String
  | .user _ => "collections.UserString"
  | a => a.ty

/-- `if isinstance(x, UserString): x = x.data`. -/
def unwrap : SArg → SArg
  | .user s => .str s
  | a => a

/-- Pass a `str` as the equivalent `UserString`. -/
def SArg.wrap : SArg → SArg
  | .str s => .user s
  | a => a

/-! ### `str`'s argument checks -/

/-- The separator of `partition`/`rpartition`, `ensure_unicode`. -/
def needStr (a : SArg) : Py Seq :=
  match a with
  | .str s => .ok s
  | a => .error (.typeError s!"must be str, not {a.fullTy}")

/-- `sep` of `split`/`rsplit`: `None` or a `str`. -/
def needSep : Option SArg → Py (Option Seq)
  | none => .ok none
  | some (.str s) => .ok (some s)
  | some a => .error (.typeError s!"must be str or None, not {a.ty}")

/-- `chars` of `strip`: `do_argstrip`, unicodeobject.c. -/
def needChars (name : String) : Option SArg → Py (Option Seq)
  | none => .ok none
  | some (.str s) => .ok (some s)
  | some _ => .error (.typeError s!"{name} arg must be None or str")

/-- `fillchar`: `convert_uc`, unicodeobject.c. -/
def needFill : Option SArg → Py Nat
  | none => .ok 32
  | some (.str [c]) => .ok c
  | some (.str _) => .error (.typeError "The fill character must be exactly one character long")
  | some a => .error (.typeError s!"The fill character must be a unicode character, not {a.ty}")

/-- The positional `str` arguments of `count`, `find`, `index`, `replace` and
`removeprefix`, Argument Clinic. -/
def needArg (fn : String) (a : SArg) : Py Seq :=
  match a with
  | .str s => .ok s
  | a => .error (.typeError s!"{fn} must be str, not {if a.ty = "NoneType" then "None" else a.ty}")  -- getargs.c:666-669

/-- `prefix`/`suffix` of `startswith`/`endswith`: a `str` or a tuple of `str`. -/
inductive AffixArg where
  | one (a : SArg)
  | tuple (ps : List Seq)
  deriving Repr, DecidableEq

def needAffix (name : String) : AffixArg → Py Affix
  | .tuple ps => .ok (.tuple ps)
  | .one (.str s) => .ok (.one s)
  | .one a => .error (.typeError s!"{name} first arg must be str or a tuple of str, not {a.ty}")

/-- `AffixArg` holding a `UserString` for a `str`. -/
def AffixArg.wrap : AffixArg → AffixArg
  | .one a => .one a.wrap
  | a => a

/-- `sub in s` on `str`, `PyUnicode_Contains`. -/
def strContains (s : Seq) (a : SArg) : Py Bool :=
  match a with
  | .str t => .ok (decide (strFind s t none none ≥ 0))
  | a => .error (.typeError s!"'in <string>' requires string as left operand, not {a.ty}")

/-- `s.join(items)`: `_PyUnicode_JoinArray`, the first non-`str` item raises. -/
def strJoin (sep : Seq) (items : List SArg) : Py Seq :=
  let rec go (i : Nat) : List SArg → Py (List Seq)
    | [] => .ok []
    | .str t :: rest => do
      let r ← go (i + 1) rest
      return t :: r
    | a :: _ => .error (.typeError s!"sequence item {i}: expected str instance, {a.ty} found")
  do
    let ts ← go 0 items
    return (ts.intersperse sep).flatten

/-- `s * n`: `sequence_repeat`, Objects/abstract.c:1157-1173, and `unicode_repeat`, Objects/unicodeobject.c:12561. The text
of the `OverflowError` depends on how often this line has run: `sequence_repeat` says "cannot fit 'int' into an index-sized
integer", and once `BINARY_OP` is specialized, `seq_int_multiply`, Python/specialize.c:2147-2154, says "Python int too large
to convert to C ssize_t". So the message is left open. -/
def strRepeat (s : Seq) (n : Int) : Py Seq := do
  if n < ssizeMin ∨ n > ssizeMax then
    throw (.overflowError "~too large for a Py_ssize_t, in one of two wordings")
  if n ≤ 0 then return []
  if s.length = 0 then return []
  if n * s.length > ssizeMax then throw (.overflowError "repeated string is too long")
  return (List.replicate n.toNat s).flatten

/-- `s[i]`. -/
def strGetItem (s : Seq) (i : Int) : Py Seq := do
  let i ← Sequences.subIndex i
  let j := if i < 0 then i + s.length else i
  if 0 ≤ j ∧ j < s.length then return [s.getD j.toNat 0]
  else throw (.indexError "string index out of range")

/-- `s[slice]`. -/
def strGetSlice (s : Seq) (sl : Slice) : Py Seq := do
  let ps ← listSlicePositions s.length sl
  return ps.map (fun i => s.getD i.toNat 0)

/-- Lexicographic comparison of code points, `unicode_compare`. -/
def seqCmp : Seq → Seq → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: s, b :: t => if a < b then .lt else if a > b then .gt else seqCmp s t

/-- The comparison operators. -/
inductive SOp where
  | eq | lt | le | gt | ge
  deriving Repr, DecidableEq

def SOp.sym : SOp → String
  | .eq => "==" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="

def SOp.test (op : SOp) (o : Ordering) : Bool :=
  match op with
  | .eq => o == .eq
  | .lt => o == .lt
  | .le => o != .gt
  | .gt => o == .gt
  | .ge => o != .lt

/-- `self.data op string`. On a `str` the comparison is direct, on a `UserString`
`str` returns `NotImplemented` and the reflected `UserString` method compares the same
two texts; any other object ends in identity for `==` or a `TypeError`. -/
def strRich (op : SOp) (s : Seq) (a : SArg) : Py Bool :=
  match a with
  | .str t | .user t => .ok (op.test (seqCmp s t))
  | a =>
    if op = .eq then .ok false
    else .error (.typeError s!"'{op.sym}' not supported between instances of 'str' and '{a.ty}'")

/-! ### What `UserString` takes as given -/

/-- The six case mappings. -/
inductive CaseFn where
  | capitalize | casefold | lower | upper | swapcase | title
  deriving Repr, DecidableEq

/-- The twelve predicates. -/
inductive PredFn where
  | isalpha | isalnum | isascii | isdecimal | isdigit | isidentifier | islower | isnumeric
  | isprintable | isspace | istitle | isupper
  deriving Repr, DecidableEq

/-- The right operand of `%`: a tuple of ints, a single object (an int), a mapping, or a
`UserString` (a non-tuple with `__getitem__`, which `PyUnicode_Format` takes as a mapping). -/
inductive ModArg where
  | tuple (l : List Int)
  | single (v : Int)
  | mapping (m : List (String × Int))
  | user (s : Seq)

/-- A mapping for `format_map`: a dict's items and its class's `__missing__` (Python code, which
may raise), if it has one. -/
structure FMap where
  items : List (String × Int)
  missing : Option (String → Py Int) := none

/-- What `table[ord(c)]` gives `str.translate`: delete, a code point, or a `str`. -/
inductive TEntry where
  | del
  | cp (n : Nat)
  | str (s : Seq)

/-- A translation table, a mapping or a sequence, as `table[ord(c)]`: Python code; a raised
`LookupError` (or subclass) means "keep the character" (Objects/unicodeobject.c `charmaptranslate_lookup`). -/
abbrev TTable := Nat → Py TEntry

/-- `str` behaviour that depends on the Unicode database or a mini-language. -/
structure UniOps where
  case : CaseFn → Seq → Seq
  pred : PredFn → Seq → Bool
  encode : Seq → String → String → Py (List Nat)
  /-- `s.format(*args, **kwds)`. -/
  format : Seq → List Int → List (String × Int) → Py Seq
  /-- `s.format_map(mapping)`. -/
  formatMap : Seq → FMap → Py Seq
  /-- `s % arg`. -/
  mod : Seq → ModArg → Py Seq
  /-- `s.translate(table)`. -/
  translate : Seq → TTable → Py Seq
  hash : Seq → Int
  repr : Seq → String
  toInt : Seq → Py Int
  /-- `repr(float(s))`: float results are compared as text. -/
  toFloat : Seq → Py String
  /-- `repr(complex(s))`. -/
  toComplex : Seq → Py String

/-! ### The methods, in source order -/

/-- `self.__class__(...)` on a `str`. -/
def wrapIn (u : US) (r : Py Seq) : Py US := r.map (fun d => ⟨u.cls, d⟩)

/-- `UserString.__init__`, :1420-1426. -/
def usNew (cls : String) : SArg → US
  | .str s => ⟨cls, s⟩
  | .user s => ⟨cls, s⟩
  | .other _ text => ⟨cls, text⟩

/-- `UserString.__str__`, Lib/collections/__init__.py:1428-1429. -/
def usStr (u : US) : Seq := u.data

/-- `UserString.__getnewargs__`, :1446-1447: `(self.data[:],)`. -/
def usGetnewargs (u : US) : Seq := u.data

/-- `UserString.__eq__`, ..., `__ge__`, :1449-1472. -/
def usRich (op : SOp) (u : US) (a : SArg) : Py Bool := strRich op u.data (unwrap a)

/-- `UserString.__contains__`, :1474-1477. -/
def usContains (u : US) (a : SArg) : Py Bool := strContains u.data (unwrap a)

/-- `UserString.__getitem__`, :1482-1483, int index. -/
def usGetitem (u : US) (i : Int) : Py US := wrapIn u (strGetItem u.data i)

/-- `UserString.__getitem__`, slice. -/
def usGetslice (u : US) (s : Slice) : Py US := wrapIn u (strGetSlice u.data s)

/-- `UserString.__add__`, :1485-1490. -/
def usAdd (u : US) : SArg → US
  | .user t => ⟨u.cls, u.data ++ t⟩
  | .str t => ⟨u.cls, u.data ++ t⟩
  | .other _ text => ⟨u.cls, u.data ++ text⟩

/-- `UserString.__radd__`, :1492-1495. `str(other)` of a `UserString` is its data. -/
def usRadd (u : US) : SArg → US
  | .str t => ⟨u.cls, t ++ u.data⟩
  | .user t => ⟨u.cls, t ++ u.data⟩
  | .other _ text => ⟨u.cls, text ++ u.data⟩

/-- `UserString.__mul__`, :1497-1498; `__rmul__` is the same function, :1500. -/
def usMul (u : US) (n : Int) : Py US := wrapIn u (strRepeat u.data n)

/-- `UserString.__mod__`, :1502-1503: `self.__class__(self.data % args)`, `args` passed as it is
(a `UserString` included). -/
def usMod (ops : UniOps) (u : US) (args : ModArg) : Py US := wrapIn u (ops.mod u.data args)

/-- `UserString.__rmod__`, :1505-1506: `self.__class__(str(template) % self)`. -/
def usRmod (ops : UniOps) (u : US) (template : Seq) : Py US := wrapIn u (ops.mod template (.user u.data))

/-- `str.center(width, fillchar)`: Argument Clinic converts `width` to `Py_ssize_t` first, then
`fillchar` (Objects/clinic/unicodeobject.c.h:115-132). -/
def strCenterA (s : Seq) (w : Int) (fill : Option SArg) : Py Seq := do
  let _ ← argSsize w
  let f ← needFill fill
  strCenter s w f

/-- `str.ljust`, the same clinic order. -/
def strLjustA (s : Seq) (w : Int) (fill : Option SArg) : Py Seq := do
  let _ ← argSsize w
  let f ← needFill fill
  strLjust s w f

/-- `str.rjust`, the same clinic order. -/
def strRjustA (s : Seq) (w : Int) (fill : Option SArg) : Py Seq := do
  let _ ← argSsize w
  let f ← needFill fill
  strRjust s w f

/-- `UserString.center`, :1515-1516. -/
def usCenter (u : US) (w : Int) (fill : Option SArg) : Py US := wrapIn u (strCenterA u.data w fill)

/-- `UserString.ljust`, :1599-1600. -/
def usLjust (u : US) (w : Int) (fill : Option SArg) : Py US := wrapIn u (strLjustA u.data w fill)

/-- `UserString.rjust`, :1630-1631. -/
def usRjust (u : US) (w : Int) (fill : Option SArg) : Py US := wrapIn u (strRjustA u.data w fill)

/-- `str.count`. -/
def strCountA (s : Seq) (a : SArg) (st en : Option Int) : Py Int := do
  let t ← needArg "count() argument 1" a
  return strCount s t st en

/-- `str.find`/`rfind`. -/
def strFindA (s : Seq) (a : SArg) (st en : Option Int) (fwd : Bool) : Py Int := do
  let t ← needArg (if fwd then "find() argument 1" else "rfind() argument 1") a
  return strFind s t st en fwd

/-- `str.index`/`rindex`. -/
def strIndexA (s : Seq) (a : SArg) (st en : Option Int) (fwd : Bool) : Py Int := do
  let t ← needArg (if fwd then "index() argument 1" else "rindex() argument 1") a
  strIndex s t st en fwd

/-- The default `start=0` of `count`, `find`, `index`, `rfind`, `rindex`, `startswith`,
`endswith` (:1518, :1538, ...): an omitted argument is passed as `0`. -/
def dflt0 (st : Option Int) : Option Int := some (st.getD 0)

/-- The default `end=_sys.maxsize`. -/
def dfltMax (en : Option Int) : Option Int := some (en.getD ssizeMax)

/-- `UserString.count`, :1518-1521: `self.data.count(sub, start, end)`, the defaults passed. -/
def usCount (u : US) (a : SArg) (st en : Option Int) : Py Int :=
  strCountA u.data (unwrap a) (dflt0 st) (dfltMax en)

/-- `UserString.find`, :1544-1547, and `rfind`, :1620-1623. -/
def usFind (u : US) (a : SArg) (st en : Option Int) (fwd : Bool) : Py Int :=
  strFindA u.data (unwrap a) (dflt0 st) (dfltMax en) fwd

/-- `UserString.index`, :1555-1558, and `rindex`, :1625-1628. -/
def usIndex (u : US) (a : SArg) (st en : Option Int) (fwd : Bool) : Py Int :=
  strIndexA u.data (unwrap a) (dflt0 st) (dfltMax en) fwd

/-- `str.removeprefix`. -/
def strRemoveprefixA (s : Seq) (a : SArg) : Py Seq := do
  let p ← needArg "removeprefix() argument" a
  return strRemoveprefix s p

/-- `str.removesuffix`. -/
def strRemovesuffixA (s : Seq) (a : SArg) : Py Seq := do
  let p ← needArg "removesuffix() argument" a
  return strRemovesuffix s p

/-- `UserString.removeprefix`, Lib/collections/__init__.py:1523-1526. -/
def usRemoveprefix (u : US) (a : SArg) : Py US := wrapIn u (strRemoveprefixA u.data (unwrap a))

/-- `UserString.removesuffix`, :1528-1531. -/
def usRemovesuffix (u : US) (a : SArg) : Py US := wrapIn u (strRemovesuffixA u.data (unwrap a))

/-- `UserString.encode`, :1533-1536: `None` means the defaults. -/
def usEncode (ops : UniOps) (u : US) (encoding errors : Option String) : Py (List Nat) :=
  ops.encode u.data (encoding.getD "utf-8") (errors.getD "strict")

/-- `str.startswith`. -/
def strStartswithA (s : Seq) (a : AffixArg) (st en : Option Int) : Py Bool := do
  let p ← needAffix "startswith" a
  return strStartswith s p st en

/-- `str.endswith`. -/
def strEndswithA (s : Seq) (a : AffixArg) (st en : Option Int) : Py Bool := do
  let p ← needAffix "endswith" a
  return strEndswith s p st en

/-- `UserString.endswith`, Lib/collections/__init__.py:1538-1539. No unwrapping. -/
def usEndswith (u : US) (a : AffixArg) (st en : Option Int) : Py Bool :=
  strEndswithA u.data a (dflt0 st) (dfltMax en)

/-- `UserString.startswith`, Lib/collections/__init__.py:1648-1649. No unwrapping. -/
def usStartswith (u : US) (a : AffixArg) (st en : Option Int) : Py Bool :=
  strStartswithA u.data a (dflt0 st) (dfltMax en)

/-- `UserString.expandtabs`, :1541-1542. -/
def usExpandtabs (u : US) (t : Int) : Py US := wrapIn u (strExpandtabs u.data t)

/-- `UserString.format`, :1549-1550. Returns a plain `str`. -/
def usFormat (ops : UniOps) (u : US) (args : List Int) (kwds : List (String × Int)) : Py Seq :=
  ops.format u.data args kwds

/-- `UserString.format_map`, :1552-1553. Returns a plain `str`. -/
def usFormatMap (ops : UniOps) (u : US) (m : FMap) : Py Seq := ops.formatMap u.data m

/-- `UserString.join`, :1596-1597. Returns a plain `str`; the items are not unwrapped. -/
def usJoin (u : US) (items : List SArg) : Py Seq := strJoin u.data items

/-- `str.partition`. -/
def strPartitionA (s : Seq) (a : SArg) : Py (Seq × Seq × Seq) := do
  let t ← needStr a
  strPartition s t

/-- `str.rpartition`. -/
def strRPartitionA (s : Seq) (a : SArg) : Py (Seq × Seq × Seq) := do
  let t ← needStr a
  strRPartition s t

/-- `UserString.partition`, :1610-1611. -/
def usPartition (u : US) (a : SArg) : Py (Seq × Seq × Seq) := strPartitionA u.data a

/-- `UserString.rpartition`, :1633-1634. -/
def usRPartition (u : US) (a : SArg) : Py (Seq × Seq × Seq) := strRPartitionA u.data a

/-- `str.replace(old, new, count)`. -/
def strReplaceA (s : Seq) (o n : SArg) (count : Int) : Py Seq := do
  let o ← needArg "replace() argument 1" o
  let n ← needArg "replace() argument 2" n
  strReplace s o n count

/-- `UserString.replace`, :1613-1618. -/
def usReplace (u : US) (o n : SArg) (count : Int) : Py US :=
  wrapIn u (strReplaceA u.data (unwrap o) (unwrap n) count)

/-- `str.split(sep, maxsplit)`: clinic converts `maxsplit` first, then `unicode_split_impl` tests
`sep` (Objects/unicodeobject.c:12900-12912). -/
def strSplitA (s : Seq) (sep : Option SArg) (m : Int) : Py (List Seq) := do
  let _ ← argSsize m
  let t ← needSep sep
  strSplit s t m

/-- `str.rsplit(sep, maxsplit)`, the same order. -/
def strRSplitA (s : Seq) (sep : Option SArg) (m : Int) : Py (List Seq) := do
  let _ ← argSsize m
  let t ← needSep sep
  strRSplit s t m

/-- `UserString.split`, :1639-1640. -/
def usSplit (u : US) (sep : Option SArg) (m : Int) : Py (List Seq) := strSplitA u.data sep m

/-- `UserString.rsplit`, :1642-1643. -/
def usRSplit (u : US) (sep : Option SArg) (m : Int) : Py (List Seq) := strRSplitA u.data sep m

/-- `UserString.splitlines`, :1645-1646. -/
def usSplitlines (u : US) (keep : Bool) : List Seq := strSplitlines u.data keep

/-- `str.strip`, `lstrip`, `rstrip`. -/
def strStripA (s : Seq) (chars : Option SArg) (t : StripType) : Py Seq := do
  let name := match t with
    | .both => "strip"
    | .left => "lstrip"
    | .right => "rstrip"
  let cs ← needChars name chars
  return strStrip s cs t

/-- `UserString.strip`, :1651-1652, `lstrip`, :1605-1606, `rstrip`, :1636-1637. -/
def usStrip (u : US) (chars : Option SArg) (t : StripType) : Py US :=
  wrapIn u (strStripA u.data chars t)

/-- `str.translate(*args)`: exactly one argument (`METH_O`). -/
def strTranslateA (ops : UniOps) (s : Seq) : List TTable → Py Seq
  | [t] => ops.translate s t
  | args => .error (.typeError s!"str.translate() takes exactly one argument ({args.length} given)")

/-- `UserString.translate`, :1660-1661: `self.__class__(self.data.translate(*args))`. -/
def usTranslate (ops : UniOps) (u : US) (args : List TTable) : Py US :=
  wrapIn u (strTranslateA ops u.data args)

/-- `UserString.zfill`, :1666-1667. -/
def usZfill (u : US) (w : Int) : Py US := wrapIn u (strZfill u.data w)

/-! ### All calls, as data -/

/-- What a method returns. -/
inductive URes where
  | us (u : US)
  | str (s : Seq)
  | bool (b : Bool)
  | int (i : Int)
  | strs (l : List Seq)
  | tup (t : Seq × Seq × Seq)
  | bytes (b : List Nat)
  | text (s : String)
  deriving Repr, DecidableEq

/-- A call on a `str`-like receiver. -/
inductive SCall where
  | case (f : CaseFn)
  | pred (f : PredFn)
  | center (w : Int) (fill : Option SArg)
  | ljust (w : Int) (fill : Option SArg)
  | rjust (w : Int) (fill : Option SArg)
  | zfill (w : Int)
  | expandtabs (t : Int)
  | count (a : SArg) (st en : Option Int)
  | find (a : SArg) (st en : Option Int) (fwd : Bool)
  | index (a : SArg) (st en : Option Int) (fwd : Bool)
  | startswith (a : AffixArg) (st en : Option Int)
  | endswith (a : AffixArg) (st en : Option Int)
  | removeprefix (a : SArg)
  | removesuffix (a : SArg)
  | partition (a : SArg)
  | rpartition (a : SArg)
  | replace (o n : SArg) (c : Int)
  | split (sep : Option SArg) (m : Int)
  | rsplit (sep : Option SArg) (m : Int)
  | splitlines (keep : Bool)
  | strip (chars : Option SArg) (t : StripType)
  | join (items : List SArg)
  | contains (a : SArg)
  | rich (op : SOp) (a : SArg)
  | mul (n : Int)
  | getitem (i : Int)
  | getslice (s : Slice)
  | format (args : List Int) (kwds : List (String × Int))
  | formatMap (m : FMap)
  | mod (a : ModArg)
  | translate (args : List TTable)
  | encode (enc err : String)
  | len
  | hash
  | repr
  | toInt
  | toFloat
  | toComplex

/-- The same call on a `str`: `str`'s own method. -/
def strCall (ops : UniOps) (c : SCall) (s : Seq) : Py URes :=
  match c with
  | .case f => .ok (.str (ops.case f s))
  | .pred f => .ok (.bool (ops.pred f s))
  | .center w fill => URes.str <$> strCenterA s w fill
  | .ljust w fill => URes.str <$> strLjustA s w fill
  | .rjust w fill => URes.str <$> strRjustA s w fill
  | .zfill w => URes.str <$> strZfill s w
  | .expandtabs t => URes.str <$> strExpandtabs s t
  | .count a st en => URes.int <$> strCountA s a st en
  | .find a st en fwd => URes.int <$> strFindA s a st en fwd
  | .index a st en fwd => URes.int <$> strIndexA s a st en fwd
  | .startswith a st en => URes.bool <$> strStartswithA s a st en
  | .endswith a st en => URes.bool <$> strEndswithA s a st en
  | .removeprefix a => URes.str <$> strRemoveprefixA s a
  | .removesuffix a => URes.str <$> strRemovesuffixA s a
  | .partition a => URes.tup <$> strPartitionA s a
  | .rpartition a => URes.tup <$> strRPartitionA s a
  | .replace o n c => URes.str <$> strReplaceA s o n c
  | .split sep m => URes.strs <$> strSplitA s sep m
  | .rsplit sep m => URes.strs <$> strRSplitA s sep m
  | .splitlines keep => .ok (.strs (strSplitlines s keep))
  | .strip chars t => URes.str <$> strStripA s chars t
  | .join items => URes.str <$> strJoin s items
  | .contains a => URes.bool <$> strContains s a
  | .rich op a => URes.bool <$> strRich op s a
  | .mul n => URes.str <$> strRepeat s n
  | .getitem i => URes.str <$> strGetItem s i
  | .getslice sl => URes.str <$> strGetSlice s sl
  | .format args kw => URes.str <$> ops.format s args kw
  | .formatMap m => URes.str <$> ops.formatMap s m
  | .mod a => URes.str <$> ops.mod s a
  | .translate t => URes.str <$> strTranslateA ops s t
  | .encode enc err => URes.bytes <$> ops.encode s enc err
  | .len => .ok (.int s.length)
  | .hash => .ok (.int (ops.hash s))
  | .repr => .ok (.text (ops.repr s))
  | .toInt => URes.int <$> ops.toInt s
  | .toFloat => URes.text <$> ops.toFloat s
  | .toComplex => URes.text <$> ops.toComplex s

/-- `getattr(UserString(...), name)(...)`: every method above. -/
def usCall (ops : UniOps) (c : SCall) (u : US) : Py URes :=
  match c with
  | .case f => .ok (.us ⟨u.cls, ops.case f u.data⟩)
  | .pred f => .ok (.bool (ops.pred f u.data))
  | .center w fill => URes.us <$> usCenter u w fill
  | .ljust w fill => URes.us <$> usLjust u w fill
  | .rjust w fill => URes.us <$> usRjust u w fill
  | .zfill w => URes.us <$> usZfill u w
  | .expandtabs t => URes.us <$> usExpandtabs u t
  | .count a st en => URes.int <$> usCount u a st en
  | .find a st en fwd => URes.int <$> usFind u a st en fwd
  | .index a st en fwd => URes.int <$> usIndex u a st en fwd
  | .startswith a st en => URes.bool <$> usStartswith u a st en
  | .endswith a st en => URes.bool <$> usEndswith u a st en
  | .removeprefix a => URes.us <$> usRemoveprefix u a
  | .removesuffix a => URes.us <$> usRemovesuffix u a
  | .partition a => URes.tup <$> usPartition u a
  | .rpartition a => URes.tup <$> usRPartition u a
  | .replace o n c => URes.us <$> usReplace u o n c
  | .split sep m => URes.strs <$> usSplit u sep m
  | .rsplit sep m => URes.strs <$> usRSplit u sep m
  | .splitlines keep => .ok (.strs (usSplitlines u keep))
  | .strip chars t => URes.us <$> usStrip u chars t
  | .join items => URes.str <$> usJoin u items
  | .contains a => URes.bool <$> usContains u a
  | .rich op a => URes.bool <$> usRich op u a
  | .mul n => URes.us <$> usMul u n
  | .getitem i => URes.us <$> usGetitem u i
  | .getslice sl => URes.us <$> usGetslice u sl
  | .format args kw => URes.str <$> usFormat ops u args kw
  | .formatMap m => URes.str <$> usFormatMap ops u m
  | .mod args => URes.us <$> usMod ops u args
  | .translate t => URes.us <$> usTranslate ops u t
  | .encode enc err => URes.bytes <$> usEncode ops u (some enc) (some err)
  | .len => .ok (.int u.data.length)
  | .hash => .ok (.int (ops.hash u.data))
  | .repr => .ok (.text (ops.repr u.data))
  | .toInt => URes.int <$> ops.toInt u.data
  | .toFloat => URes.text <$> ops.toFloat u.data
  | .toComplex => URes.text <$> ops.toComplex u.data

/-- Forget the wrapper: a `UserString` result read as a `str`. -/
def URes.plain : URes → URes
  | .us u => .str u.data
  | r => r

/-- Every `str`-like argument of the call holds a `str`, the only kind `str` accepts. -/
def SArg.isStr : SArg → Bool
  | .str _ => true
  | _ => false

def optStr : Option SArg → Bool
  | none => true
  | some a => a.isStr

/-- Replace every `str` argument of a call by the equal `UserString`. -/
def SCall.wrap : SCall → SCall
  | .center w fill => .center w (fill.map SArg.wrap)
  | .ljust w fill => .ljust w (fill.map SArg.wrap)
  | .rjust w fill => .rjust w (fill.map SArg.wrap)
  | .count a st en => .count a.wrap st en
  | .find a st en fwd => .find a.wrap st en fwd
  | .index a st en fwd => .index a.wrap st en fwd
  | .startswith a st en => .startswith a.wrap st en
  | .endswith a st en => .endswith a.wrap st en
  | .removeprefix a => .removeprefix a.wrap
  | .removesuffix a => .removesuffix a.wrap
  | .partition a => .partition a.wrap
  | .rpartition a => .rpartition a.wrap
  | .replace o n c => .replace o.wrap n.wrap c
  | .split sep m => .split (sep.map SArg.wrap) m
  | .rsplit sep m => .rsplit (sep.map SArg.wrap) m
  | .strip chars t => .strip (chars.map SArg.wrap) t
  | .join items => .join (items.map SArg.wrap)
  | .contains a => .contains a.wrap
  | .rich op a => .rich op a.wrap
  | c => c

/-- Does the call take only `str` where it takes a `str`-like argument? -/
def SCall.allStr : SCall → Bool
  | .center _ f | .ljust _ f | .rjust _ f => optStr f
  | .count a _ _ | .find a _ _ _ | .index a _ _ _ => a.isStr
  | .startswith (.one a) _ _ | .endswith (.one a) _ _ => a.isStr
  | .removeprefix a | .removesuffix a | .partition a | .rpartition a => a.isStr
  | .replace o n _ => o.isStr && n.isStr
  | .split s _ | .rsplit s _ => optStr s
  | .strip c _ => optStr c
  | .join items => items.all SArg.isStr
  | .contains a | .rich _ a => a.isStr
  | _ => true

/-- `self.__class__` is kept by the result of these calls; the rest return `str`, `list`,
`tuple`, `bool`, `int`, `bytes` as their `str` twin does. -/
def SCall.keepsClass : SCall → Bool
  | .case _ | .center .. | .ljust .. | .rjust .. | .zfill _ | .expandtabs _
  | .removeprefix _ | .removesuffix _ | .replace .. | .strip .. | .mul _
  | .getitem _ | .getslice _ | .mod _ | .translate _ => true
  | _ => false

/-! ### Keyword arguments and `format()` -/

/-- `str.replace(old, new, count=n)`, keyword `count` since 3.13 (gh-106487),
Objects/unicodeobject.c `unicode_replace`. -/
def strReplaceKw (s : Seq) (o n : SArg) (kw : String) (v : Int) : Py Seq :=
  if kw = "count" then strReplaceA s o n v
  else .error (.typeError s!"replace() got an unexpected keyword argument '{kw}'")

/-- `UserString.replace(old, new, maxsplit=n)`: the parameter is named `maxsplit`, :1613. -/
def usReplaceKw (u : US) (o n : SArg) (kw : String) (v : Int) : Py US :=
  if kw = "maxsplit" then usReplace u o n v
  else .error (.typeError s!"UserString.replace() got an unexpected keyword argument '{kw}'")

/-- `format(u, spec)`: `UserString` defines no `__format__`, so `object.__format__`:
`str(self)` for an empty spec, `TypeError` for any other (Objects/typeobject.c, `object___format___impl`). -/
def usDunderFormat (u : US) (spec : String) : Py Seq :=
  if spec.isEmpty then .ok u.data
  else .error (.typeError s!"unsupported format string passed to {u.cls}.__format__")

end PyLean.CoreLibs.Coll
