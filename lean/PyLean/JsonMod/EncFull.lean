import PyLean.JsonMod.EncTwins
import PyLean.JsonMod.CApi

/-!
The two encoders of CPython 3.15.2 with what `Enc.lean` leaves out: exception notes, the
recursion limits, `str` subclasses as separators and as results of a custom `encoder`, and
subclasses of `list`, `tuple` and `dict`.

**Notes.** Every level that sees an exception pass adds a note. C: `_PyErr_FormatNote("when
serializing %T item %zd", seq, i)` (Modules/_json.c:1906), `("when serializing %T item %R", dct,
key)` (:1732) with the original key, `("when serializing %T object", obj)` (:1654). Python:
`exc.add_note(f'when serializing {type(lst).__name__} item {i}')` (Lib/json/encoder.py:316),
`f'... {type(dct).__name__} item {key!r}'` (:406) with the key after its conversion to `str`,
`f'... {type(o).__name__} object'` (:446). A note records the type and the key; `%T` prints the
fully qualified name (`_PyType_GetFullyQualifiedName`, Objects/typeobject.c:1694-1724), Python
`__name__` (`renderC`, `renderPy`).

**Recursion.** C: `_Py_EnterRecursiveCall(" while encoding a JSON object")` before a list or
tuple (:1606), a dict (:1613) and the value `default` returned (:1644), stack based as in
`DecRec.lean`: `c` is the stack room in levels. Python: every call pushes a frame (generators
too, when they start and when they are resumed); `p` is the number of frames left. The frames
are `_iterencode_once`, `_iterencode`, `_iterencode_list`, `_iterencode_dict`, `_default`,
`floatstr` and the string encoder (`py_encode_basestring(_ascii)` and its `replace` callback when
`re.sub` finds something to escape). A callback (`default`, `__str__`, `items`) is abstract and
uses one frame (a scope limit). With the room as the measure, a cycle under
`check_circular=False` ends in `RecursionError`, as in CPython; no fuel is needed.

**Subclasses.** C takes the exact-type paths only for exact `list`, `tuple`, `dict` and
`frozendict` (`PySequence_Fast`, :1922; `PyAnyDict_CheckExact`, :1838); a subclass is iterated
(`list(seq)`) or asked for `items()` (`PyMapping_Items`, Objects/abstract.c:2472-2481), and its
emptiness is the stored size (`PyDict_GET_SIZE`, :1806) or the materialised list (:1925). Python
uses `not lst`/`not dct` (`__len__`, `__bool__`) and iterates lazily. A subclass is given by
those outcomes: `bool(o)` (not raising, a scope limit: C's `list()` would call `__len__` too),
what iteration yields and whether it ends by raising, what `items()` returns.

**Separators.** C writes `item_separator` (without `indent`) and `key_separator` with
`PyUnicodeWriter_WriteStr` (:1716, :1728, :1900), which calls `str()` on a `str` subclass
(Objects/unicode_writer.c:313-331); Python joins the raw text. With `indent` the separator is a
concatenation, an exact `str`, in both.

Keys and container types are compared by identity, as `Enc.lean` does: `back k` is the `k`-th
enclosing container, re-entered; `other n t` an object of identity `n` and type `t`.
-/

namespace PyLean.JsonMod

open PyLean

/-- A Python type, for the names the encoders print. A static type has its `tp_name`; a heap
type's `tp_name` is its `__name__` or, made from a spec, `module.Name`. -/
structure PyType where
  name : String
  qualname : String := name
  module : String := "builtins"
  tpName : String := name
  heap : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- `%T`: `_PyType_GetFullyQualifiedName(type, '.')`, Objects/typeobject.c:1694-1724. -/
def PyType.fq (t : PyType) : String :=
  if !t.heap then t.tpName
  else if t.module = "builtins" ∨ t.module = "__main__" then t.qualname
  else t.module ++ "." ++ t.qualname

def tList : PyType := { name := "list" }
def tTuple : PyType := { name := "tuple" }
def tDict : PyType := { name := "dict" }
def tFrozendict : PyType := { name := "frozendict" }

/-- A dict key. `obj t o` is a key of another type (a tuple, `bytes`, a date): its type and,
for `sort_keys`, its rank among keys of that type; such keys compare only with keys of their own
type (a scope limit: a `decimal.Decimal` or `fractions.Fraction` key also compares with numbers). -/
inductive XKey where
  | str (s : PStr)
  | int (n : Int)
  | bool (b : Bool)
  | none
  | flt (bits : Nat) (repr : PStr)
  | obj (t : PyType) (ord : Int)
  deriving DecidableEq, Repr, Inhabited

/-- A `str` object: its text, whether it is exactly a `str`, and what `str(obj)` gives (for a
subclass, its `__str__`, which may raise or return something else). -/
structure SObj where
  raw : PStr
  exact : Bool
  strOf : Except PyExc PStr

def SObj.ofStr (s : PStr) : SObj := ⟨s, true, .ok s⟩

/-- An element of what a dict subclass's `items()` yields: a 2-tuple (or a `tuple` subclass of
length 2), a 2-element list, or something else, which Python's unpacking refuses with `e`. -/
inductive ItemShape where
  | tup
  | lst
  | bad (e : PyExc)

/-- What a dict subclass's `items()` call gives before iteration. -/
inductive ItemsHead where
  | ok
  | raises (e : PyExc)
  /-- It returns a non-iterable of type `t`. -/
  | notIter (t : PyType)

inductive XVal where
  | none
  | bool (b : Bool)
  | int (n : Int)
  | flt (bits : Nat) (repr : PStr)
  | str (s : PStr)
  /-- An exact `list` or `tuple` (`t` says which). -/
  | seq (t : PyType) (xs : List XVal)
  /-- A subclass of `list` or `tuple`: `bool(o)`, what iterating it yields, and the exception
  the iteration ends with (`none`: it is exhausted). -/
  | seqSub (t : PyType) (truth : Bool) (yields : List XVal) (stop : Option PyExc)
  /-- An exact `dict` or `frozendict`. -/
  | map (t : PyType) (kvs : List (XKey × XVal))
  /-- A subclass of `dict` or `frozendict`: its stored size, `bool(o)`, and `o.items()`: the
  call, what iterating the result yields, and how the iteration ends. -/
  | mapSub (t : PyType) (used : Nat) (truth : Bool) (head : ItemsHead)
      (items : List (ItemShape × XKey × XVal)) (stop : Option PyExc)
  /-- The `k`-th enclosing container (`0` the innermost): a reference cycle. -/
  | back (k : Nat)
  /-- An object of type `t` and identity `n`, handed to `default`. -/
  | other (n : Nat) (t : PyType)

/-- The key in a note: the original key (C's `%R`) or the converted text (Python's `{key!r}`
of a `str`). -/
inductive NoteKey where
  | orig (k : XKey)
  | conv (s : PStr)

/-- A note added to an exception. -/
inductive Note where
  | item (t : PyType) (i : Nat)
  | key (t : PyType) (k : NoteKey)
  | obj (t : PyType)

/-- The type name a note prints: `%T` in C, `__name__` in Python. -/
def Note.typeC : Note → String
  | .item t _ | .key t _ | .obj t => t.fq
def Note.typePy : Note → String
  | .item t _ | .key t _ | .obj t => t.name

abbrev XErr := PyExc × List Note
abbrev XR := Except XErr PStr

def xe (e : PyExc) : XErr := (e, [])

def liftE {α : Type} : Except PyExc α → Except XErr α
  | .ok a => .ok a
  | .error e => .error (xe e)

/-- `_PyErr_FormatNote` / `exc.add_note`: appends a note to the exception passing by. -/
def addNote {α : Type} (n : Note) : Except XErr α → Except XErr α
  | .error (e, ns) => .error (e, ns ++ [n])
  | r => r

def recEncC : PyExc := .named "RecursionError" "~Stack overflow (used N kB) while encoding a JSON object"
def recEncPy : PyExc := .named "RecursionError" "maximum recursion depth exceeded"

/-- What a custom `encoder` returns: a `str` object or an object of another type. -/
inductive XOut where
  | str (o : SObj)
  | nonstr (tpName : String)

structure XCfg where
  ensureAscii : Bool := true
  checkCircular : Bool := true
  allowNan : Bool := true
  sortKeys : Bool := false
  skipKeys : Bool := false
  indent : Option PStr := none
  itemSep : SObj := SObj.ofStr (cs ", ")
  keySep : SObj := SObj.ofStr (cs ": ")
  /-- `default(o)` for the object `other n t`. -/
  dflt : Nat → PyType → Except PyExc XVal := fun _ t => .error (defaultErr t.name)
  /-- `list.sort` of the items of a dict subclass under `sort_keys` (one function for both
  twins: C's `PyList_Sort` and Python's `sorted` compare the same objects). -/
  subSort : List (ItemShape × XKey × XVal) → Except PyExc (List (ItemShape × XKey × XVal)) := .ok
  /-- The `encoder` of `c_make_encoder` when it is not one of the two C functions (C only). -/
  customEnc : Option (PStr → Except PyExc XOut) := none

/-- The options the shared helpers of `Enc.lean` read. -/
def XCfg.toE (cfg : XCfg) : ECfg :=
  { ensureAscii := cfg.ensureAscii, checkCircular := cfg.checkCircular, allowNan := cfg.allowNan,
    sortKeys := cfg.sortKeys, skipKeys := cfg.skipKeys, indent := cfg.indent }

/-! ### Keys and sorting -/

def XKey.cls : XKey → Nat
  | .int _ | .bool _ | .flt _ _ => 0
  | .str _ => 1
  | .none => 2
  | .obj _ _ => 3

def XKey.toE : XKey → EKey
  | .str s => .str s
  | .int n => .int n
  | .bool b => .bool b
  | .none => .none
  | .flt b r => .flt b r
  | .obj _ o => .tup o

def xInsert (p : XKey × XVal) : List (XKey × XVal) → List (XKey × XVal)
  | [] => [p]
  | q :: t => if p.1.toE.lt q.1.toE then p :: q :: t else q :: xInsert p t

/-- `sorted(dct.items())` / `PyList_Sort(items)` for an exact dict (distinct keys, so tuples
compare by key): as `sortItems`; keys of another type compare only with keys of their own type. -/
def xSortItems (kvs : List (XKey × XVal)) : Except PyExc (List (XKey × XVal)) :=
  match kvs with
  | [] => .ok []
  | [p] => .ok [p]
  | p :: t =>
    if t.all (fun q => q.1.cls == p.1.cls && (match q.1, p.1 with
        | .obj a _, .obj b _ => a == b
        | _, _ => true)) && p.1.cls != 2 then .ok (kvs.foldr xInsert [])
    else .error (.typeError "~'<' not supported between instances")

def keyTypeErr (n : String) : PyExc := .typeError s!"keys must be str, int, float, bool or None, not {n}"

/-- The key conversion of `encoder_encode_key_value`, :1678-1702: the text, `none` for a skipped
key; `%.100s` of `tp_name` in the message. -/
def cKeyX (cfg : XCfg) : XKey → Except PyExc (Option PStr)
  | .str s => .ok (some s)
  | .flt b r => (cEncodeFloat cfg.toE b r).map some
  | .bool b => .ok (some (encodedConst (some b)))
  | .none => .ok (some (encodedConst none))
  | .int n => (intRepr n).map some
  | .obj t _ => if cfg.skipKeys then .ok none else .error (keyTypeErr (truncName 100 t.tpName))

/-! ### C: `encoder_listencode_obj` and friends, Modules/_json.c:1537-1992 -/

/-- `PyUnicodeWriter_WriteStr(writer, obj)` for a `str` object, Objects/unicode_writer.c:313-331:
the text of an exact `str`, otherwise `str(obj)`. -/
def writeStrObj (o : SObj) : Except PyExc PStr := if o.exact then .ok o.raw else o.strOf

/-- `encoder_write_string`, :1537-1557: `fast_encode` (which writes a subclass's text without
`str()`, gh-148241), or the custom `encoder`, whose result must be a `str` and goes through
`_steal_accumulate` (:1560-1566), i.e. `PyUnicodeWriter_WriteStr`. -/
def cWriteStringX (cfg : XCfg) (s : PStr) : Except PyExc PStr :=
  match cfg.customEnc with
  | none => .ok (cFastEncode cfg.toE s)
  | some g =>
    match g s with
    | .error e => .error e
    | .ok (.nonstr t) => .error (.typeError s!"encoder() must return a string, not {truncName 80 t}")
    | .ok (.str o) => writeStrObj o

/-- `if (_Py_EnterRecursiveCall(" while encoding a JSON object")) return -1;` with room `c`. -/
def cEnterX {α : Type} (c : Nat) (k : (c' : Nat) → c' < c → Except XErr α) : Except XErr α :=
  match c with
  | 0 => .error (xe recEncC)
  | c' + 1 => k c' (Nat.lt_succ_self c')

/-- The note key of C: the key object itself. -/
def cNoteKey (k : XKey) : NoteKey := .orig k

/-- The items list of `encoder_listencode_dict` for an exact dict: `PyMapping_Items` and
`PyList_Sort` under `sort_keys` (:1838-1843), otherwise `PyDict_Next` (:1858-1866); every item a
2-tuple. -/
def cExactItems (cfg : XCfg) (kvs : List (XKey × XVal)) : Except PyExc (List (ItemShape × XKey × XVal)) :=
  if cfg.sortKeys then (xSortItems kvs).map (·.map fun (k, v) => (.tup, k, v))
  else .ok (kvs.map fun (k, v) => (.tup, k, v))

/-- `PyMapping_Items(dct)` for a subclass (`method_output_as_list`, Objects/abstract.c:2433-2457)
and the sort. -/
def cSubItems (cfg : XCfg) (t : PyType) (head : ItemsHead) (items : List (ItemShape × XKey × XVal))
    (stop : Option PyExc) : Except PyExc (List (ItemShape × XKey × XVal)) :=
  match head with
  | .raises e => .error e
  | .notIter u => .error (.typeError s!"{t.fq}.items() must return an iterable, not {u.fq}")
  | .ok =>
    match stop with
    | some e => .error e
    | none => if cfg.sortKeys then cfg.subSort items else .ok items

mutual
/-- `encoder_listencode_obj(s, writer, obj, indent_level, indent_cache)`, :1569-1667, with stack
room `c`, the identities `seen` of the objects being serialized through `default` and the
enclosing containers `anc`. -/
def cObjX (cfg : XCfg) (c lvl : Nat) (seen : List Nat) (anc : List XVal) (v : XVal) : XR :=
  match v with
  | .none => .ok (cs "null")
  | .bool b => .ok (if b then cs "true" else cs "false")
  | .str s => liftE (cWriteStringX cfg s)
  | .int n => liftE (intRepr n)
  | .flt b r => liftE (cEncodeFloat cfg.toE b r)
  | .seq t xs => cEnterX c (fun c' _ => cContX cfg c' lvl seen anc false (.seq t xs))
  | .seqSub t tr ys st => cEnterX c (fun c' _ => cContX cfg c' lvl seen anc false (.seqSub t tr ys st))
  | .map t kvs => cEnterX c (fun c' _ => cContX cfg c' lvl seen anc false (.map t kvs))
  | .mapSub t u tr h its st => cEnterX c (fun c' _ => cContX cfg c' lvl seen anc false (.mapSub t u tr h its st))
  | .back k =>
    match anc[k]? with
    | some a => cEnterX c (fun c' _ => cContX cfg c' lvl seen anc true a)
    | none => .error (xe .modelFuel)
  | .other n t =>
    -- :1617-1665: markers, `default`, `_Py_EnterRecursiveCall`, the note on failure
    if cfg.checkCircular ∧ n ∈ seen then .error (xe circularErr)
    else
      match cfg.dflt n t with
      | .error e => .error (xe e)
      | .ok v' => cEnterX c (fun c' _ => addNote (.obj t) (cObjX cfg c' lvl (n :: seen) anc v'))
termination_by (2 * c, 0, 0)

/-- `encoder_listencode_list` (:1916-1992) and `encoder_listencode_dict` (:1798-1887) on the
container `a`; `cyc` says it is already being serialized (it is in `markers`). -/
def cContX (cfg : XCfg) (c lvl : Nat) (seen : List Nat) (anc : List XVal) (cyc : Bool) (a : XVal) : XR :=
  match a with
  | .seq t xs => cSeqPart cfg c lvl seen anc cyc a t (.ok xs)
  | .seqSub t _ ys st => cSeqPart cfg c lvl seen anc cyc a t (match st with
      | some e => .error e
      | none => .ok ys)
  | .map t kvs => cMapPart cfg c lvl seen anc cyc a t (kvs.length = 0) (cExactItems cfg kvs)
  | .mapSub t u _ h its st => cMapPart cfg c lvl seen anc cyc a t (u = 0) (cSubItems cfg t h its st)
  | _ => .error (xe .modelFuel)
termination_by (2 * c + 1, 2, 0)

/-- `encoder_listencode_list` after `PySequence_Fast` (`fast`). -/
def cSeqPart (cfg : XCfg) (c lvl : Nat) (seen : List Nat) (anc : List XVal) (cyc : Bool) (self : XVal)
    (t : PyType) (fast : Except PyExc (List XVal)) : XR :=
  match fast with
  | .error e => .error (xe e)
  | .ok xs =>
    if xs.length = 0 then .ok (cs "[]")
    else if cfg.checkCircular ∧ cyc then .error (xe circularErr)
    else
      match cfg.indent with
      | some ind =>
        match cSeqItemsX cfg c (lvl + 1) seen (self :: anc) t (.ok (cfg.itemSep.raw ++ cNewlineIndent ind (lvl + 1))) 0 xs with
        | .error e => .error e
        | .ok body => .ok ([91] ++ cNewlineIndent ind (lvl + 1) ++ body ++ cNewlineIndent ind lvl ++ [93])
      | none =>
        match cSeqItemsX cfg c lvl seen (self :: anc) t (writeStrObj cfg.itemSep) 0 xs with
        | .error e => .error e
        | .ok body => .ok ([91] ++ body ++ [93])
termination_by (2 * c + 1, 1, 0)

/-- `_encoder_iterate_fast_seq_lock_held`, :1890-1913: the separator before every item but the
first (`PyUnicodeWriter_WriteStr`, `sep`), then the item, and the note on failure. -/
def cSeqItemsX (cfg : XCfg) (c lvl : Nat) (seen : List Nat) (anc : List XVal) (t : PyType)
    (sep : Except PyExc PStr) (i : Nat) (xs : List XVal) : XR :=
  match xs with
  | [] => .ok []
  | x :: rest =>
    match (if i ≠ 0 then sep else .ok []) with
    | .error e => .error (xe e)
    | .ok pre =>
      match cObjX cfg c lvl seen anc x with
      | .error e => addNote (.item t i) (.error e)
      | .ok tx =>
        match cSeqItemsX cfg c lvl seen anc t sep (i + 1) rest with
        | .error e => .error e
        | .ok r => .ok (pre ++ tx ++ r)
termination_by (2 * c + 1, 0, xs.length)

/-- `encoder_listencode_dict` after the empty test (`empty`), with the items it iterates. -/
def cMapPart (cfg : XCfg) (c lvl : Nat) (seen : List Nat) (anc : List XVal) (cyc : Bool) (self : XVal)
    (t : PyType) (empty : Bool) (items : Except PyExc (List (ItemShape × XKey × XVal))) : XR :=
  if empty then .ok (cs "{}")
  else if cfg.checkCircular ∧ cyc then .error (xe circularErr)
  else
    match items with
    | .error e => .error (xe e)
    | .ok its =>
      match cfg.indent with
      | some ind =>
        match cMapItemsX cfg c (lvl + 1) seen (self :: anc) t (.ok (cfg.itemSep.raw ++ cNewlineIndent ind (lvl + 1)))
            (cNewlineIndent ind (lvl + 1)) true its with
        | .error e => .error e
        | .ok (body, first) => .ok ([123] ++ body ++ (if !first then cNewlineIndent ind lvl else []) ++ [125])
      | none =>
        match cMapItemsX cfg c lvl seen (self :: anc) t (writeStrObj cfg.itemSep) [] true its with
        | .error e => .error e
        | .ok (body, _) => .ok ([123] ++ body ++ [125])
termination_by (2 * c + 1, 1, 0)

/-- `_encoder_iterate_mapping_lock_held` (:1739-1769; the 2-tuple check) and
`_encoder_iterate_dict_lock_held` (:1772-1795) with `encoder_encode_key_value` (:1670-1736):
the separator (`PyUnicodeWriter_WriteStr`) or, for the first item, the newline (`nl`), the key
through `encoder_write_string`, `key_separator` (`PyUnicodeWriter_WriteStr`), the value and
its note. Also returns `first`. -/
def cMapItemsX (cfg : XCfg) (c lvl : Nat) (seen : List Nat) (anc : List XVal) (t : PyType)
    (sep : Except PyExc PStr) (nl : PStr) (first : Bool) (its : List (ItemShape × XKey × XVal)) :
    Except XErr (PStr × Bool) :=
  match its with
  | [] => .ok ([], first)
  | (sh, k, x) :: rest =>
    match sh with
    | .lst | .bad _ => .error (xe (.valueError "items must return 2-tuples"))
    | .tup =>
      match cKeyX cfg k with
      | .error e => .error (xe e)
      | .ok none => cMapItemsX cfg c lvl seen anc t sep nl first rest
      | .ok (some ks) =>
        match (if first then .ok nl else sep) with
        | .error e => .error (xe e)
        | .ok pre =>
          match cWriteStringX cfg ks with
          | .error e => .error (xe e)
          | .ok kt =>
            match writeStrObj cfg.keySep with
            | .error e => .error (xe e)
            | .ok ksep =>
              match cObjX cfg c lvl seen anc x with
              | .error e => addNote (.key t (cNoteKey k)) (.error e)
              | .ok tx =>
                match cMapItemsX cfg c lvl seen anc t sep nl false rest with
                | .error e => .error e
                | .ok (r, f) => .ok (pre ++ kt ++ ksep ++ tx ++ r, f)
termination_by (2 * c + 1, 0, its.length)
end

/-- `JSONEncoder.encode(o)` with `c_make_encoder`, stack room `c` at `encoder_call`
(`c_encode_basestring(_ascii)` for a `str`). -/
def dumpsCX (cfg : XCfg) (c : Nat) (v : XVal) : XR :=
  match v with
  | .str s => .ok (cStrEnc cfg.toE s)
  | _ => cObjX cfg c 0 [] [] v

/-- `c_make_encoder(...)(o, level)`, `encoder_call` (:1448-1488): `create_indent_cache(level)`
then `indent_level = 0`, so the cache's level-0 entry is `'\n' + indent * level` (`''` for a
negative level, `PySequence_Repeat`) and every level is shifted by `level`; `n` conversion of
the level first. -/
def encoderCallX (cfg : XCfg) (c : Nat) (v : XVal) (level : Int) : Except XErr (List PStr) :=
  if outOfSsize level then .error (xe ssizeErr)
  else
    match cObjX cfg c level.toNat [] [] v with
    | .ok t => .ok [t]
    | .error e => .error e

/-! ### Python: `_make_iterencode`, Lib/json/encoder.py:259-459 -/

/-- A Python call with `b` frames left: `RecursionError` when there is none. -/
def pyCallX {α : Type} (b : Nat) (k : (b' : Nat) → b' < b → Except XErr α) : Except XErr α :=
  match b with
  | 0 => .error (xe recEncPy)
  | b' + 1 => k b' (Nat.lt_succ_self b')

/-- Whether `re.sub` calls `replace`: `ESCAPE_ASCII` (encoder.py:10) or `ESCAPE` (:9) matches. -/
def needsReplace (ascii : Bool) (s : PStr) : Bool :=
  if ascii then s.any (fun c => c = 92 ∨ c = 34 ∨ ¬(32 ≤ c ∧ c ≤ 126))
  else s.any (fun c => c < 32 ∨ c = 92 ∨ c = 34)

/-- `_encoder(s)`: `py_encode_basestring(_ascii)` (encoder.py:37-68), a frame, and one more for
`replace` when something is escaped. -/
def pyEncStrX (cfg : XCfg) (b : Nat) (s : PStr) : Except XErr PStr :=
  pyCallX b fun b' _ =>
    if needsReplace cfg.ensureAscii s then pyCallX b' (fun _ _ => .ok (pyStrEnc cfg.toE s))
    else .ok (pyStrEnc cfg.toE s)

/-- `_floatstr(o)` (encoder.py:226-246), a frame. -/
def pyFloatX (cfg : XCfg) (b : Nat) (bits : Nat) (r : PStr) : Except XErr PStr :=
  pyCallX b (fun _ _ => liftE (pyFloatStr cfg.toE bits r))

/-- The key conversion of `_iterencode_dict`, encoder.py:351-371 (`key.__class__.__name__` in
the message). -/
def pyKeyX (cfg : XCfg) (b : Nat) : XKey → Except XErr (Option PStr)
  | .str s => .ok (some s)
  | .flt bits r => (pyFloatX cfg b bits r).map some
  | .bool true => .ok (some (cs "true"))
  | .bool false => .ok (some (cs "false"))
  | .none => .ok (some (cs "null"))
  | .int n => liftE ((intRepr n).map some)
  | .obj t _ => if cfg.skipKeys then .ok none else .error (xe (keyTypeErr t.name))

/-- `sorted(dct.items())` or `dct.items()` for an exact dict. -/
def pyExactItems (cfg : XCfg) (kvs : List (XKey × XVal)) : Except PyExc (List (ItemShape × XKey × XVal)) :=
  cExactItems cfg kvs

/-- `dct.items()` for a subclass: the call and `iter()` of the result (`'%.200s' object is not
iterable`); under `sort_keys`, `sorted` iterates it to the end first. The end of a lazy iteration
is returned apart. -/
def pySubItems (cfg : XCfg) (head : ItemsHead) (items : List (ItemShape × XKey × XVal))
    (stop : Option PyExc) : Except PyExc (List (ItemShape × XKey × XVal) × Option PyExc) :=
  match head with
  | .raises e => .error e
  | .notIter u => .error (.typeError s!"'{truncName 200 u.tpName}' object is not iterable")
  | .ok =>
    if cfg.sortKeys then
      match stop with
      | some e => .error e
      | none => (cfg.subSort items).map (·, none)
    else .ok (items, stop)

mutual
/-- The body of `_iterencode(o, _current_indent_level)`, encoder.py:415-449, running in its frame
with `b` frames left. -/
def pyIterX (cfg : XCfg) (b lvl : Nat) (seen : List Nat) (anc : List XVal) (v : XVal) : XR :=
  match v with
  | .str s => pyEncStrX cfg b s
  | .none => .ok (cs "null")
  | .bool true => .ok (cs "true")
  | .bool false => .ok (cs "false")
  | .int n => liftE (intRepr n)
  | .flt bits r => pyFloatX cfg b bits r
  | .seq t xs => pyCallX b (fun b' _ => pyContX cfg b' lvl seen anc false (.seq t xs))
  | .seqSub t tr ys st => pyCallX b (fun b' _ => pyContX cfg b' lvl seen anc false (.seqSub t tr ys st))
  | .map t kvs => pyCallX b (fun b' _ => pyContX cfg b' lvl seen anc false (.map t kvs))
  | .mapSub t u tr h its st => pyCallX b (fun b' _ => pyContX cfg b' lvl seen anc false (.mapSub t u tr h its st))
  | .back k =>
    match anc[k]? with
    | some a => pyCallX b (fun b' _ => pyContX cfg b' lvl seen anc true a)
    | none => .error (xe .modelFuel)
  | .other n t =>
    if cfg.checkCircular ∧ n ∈ seen then .error (xe circularErr)
    else
      -- `newobj = _default(o)`, then `yield from _iterencode(newobj, ...)` inside the `try`
      match pyCallX b (fun _ _ => liftE (cfg.dflt n t)) with
      | .error e => .error e
      | .ok v' => pyCallX b (fun b' _ => addNote (.obj t) (pyIterX cfg b' lvl (n :: seen) anc v'))
termination_by (2 * b, 0, 0)

/-- A value inside the `try` of `_iterencode_list` (encoder.py:300-313) or `_iterencode_dict`
(:385-402): the scalars and the containers as in `_iterencode`, an unknown object in a new
`_iterencode` generator (a frame). -/
def pyItemX (cfg : XCfg) (b lvl : Nat) (seen : List Nat) (anc : List XVal) (x : XVal) : XR :=
  match x with
  | .other _ _ => pyCallX b (fun b' _ => pyIterX cfg b' lvl seen anc x)
  | _ => pyIterX cfg b lvl seen anc x
termination_by (2 * b, 1, 0)

/-- `_iterencode_list` (encoder.py:265-326) or `_iterencode_dict` (:328-413) on `a`, in its frame. -/
def pyContX (cfg : XCfg) (b lvl : Nat) (seen : List Nat) (anc : List XVal) (cyc : Bool) (a : XVal) : XR :=
  match a with
  | .seq t xs => pyListPart cfg b lvl seen anc cyc a t (!xs.isEmpty) xs none
  | .seqSub t tr ys st => pyListPart cfg b lvl seen anc cyc a t tr ys st
  | .map t kvs => pyDictPart cfg b lvl seen anc cyc a t (!kvs.isEmpty) ((pyExactItems cfg kvs).map (·, none))
  | .mapSub t _ tr h its st => pyDictPart cfg b lvl seen anc cyc a t tr (pySubItems cfg h its st)
  | _ => .error (xe .modelFuel)
termination_by (2 * b + 1, 2, 0)

/-- `_iterencode_list`: `if not lst`, markers, `buf = '['` (written with the first item only),
the loop over what iteration yields, then how the iteration ends. -/
def pyListPart (cfg : XCfg) (b lvl : Nat) (seen : List Nat) (anc : List XVal) (cyc : Bool) (self : XVal)
    (t : PyType) (truth : Bool) (ys : List XVal) (stop : Option PyExc) : XR :=
  if !truth then .ok (cs "[]")
  else if cfg.checkCircular ∧ cyc then .error (xe circularErr)
  else
    match cfg.indent with
    | some ind =>
      match pyListItemsX cfg b (lvl + 1) seen (self :: anc) t ([91] ++ [10] ++ rep ind (lvl + 1))
          (cfg.itemSep.raw ++ [10] ++ rep ind (lvl + 1)) 0 ys with
      | .error e => .error e
      | .ok body =>
        match stop with
        | some e => .error (xe e)
        | none => .ok (body ++ [10] ++ rep ind lvl ++ [93])
    | none =>
      match pyListItemsX cfg b lvl seen (self :: anc) t [91] cfg.itemSep.raw 0 ys with
      | .error e => .error e
      | .ok body =>
        match stop with
        | some e => .error (xe e)
        | none => .ok (body ++ [93])
termination_by (2 * b + 1, 1, 0)

/-- The `for i, value in enumerate(lst)` loop: `buf` (the opening bracket, then the separator)
and the value; the `try` adds the note. -/
def pyListItemsX (cfg : XCfg) (b lvl : Nat) (seen : List Nat) (anc : List XVal) (t : PyType)
    (buf0 sep : PStr) (i : Nat) (ys : List XVal) : XR :=
  match ys with
  | [] => .ok []
  | x :: rest =>
    match pyItemX cfg b lvl seen anc x with
    | .error e => addNote (.item t i) (.error e)
    | .ok tx =>
      match pyListItemsX cfg b lvl seen anc t buf0 sep (i + 1) rest with
      | .error e => .error e
      | .ok r => .ok ((if i ≠ 0 then sep else buf0) ++ tx ++ r)
termination_by (2 * b + 1, 0, ys.length)

/-- `_iterencode_dict`: `if not dct`, markers, `'{'`, the items, `'}'`. `items` is the list and
the end of its iteration. -/
def pyDictPart (cfg : XCfg) (b lvl : Nat) (seen : List Nat) (anc : List XVal) (cyc : Bool) (self : XVal)
    (t : PyType) (truth : Bool) (items : Except PyExc (List (ItemShape × XKey × XVal) × Option PyExc)) : XR :=
  if !truth then .ok (cs "{}")
  else if cfg.checkCircular ∧ cyc then .error (xe circularErr)
  else
    match items with
    | .error e => .error (xe e)
    | .ok (its, stop) =>
      match cfg.indent with
      | some ind =>
        match pyDictItemsX cfg b (lvl + 1) seen (self :: anc) t ([10] ++ rep ind (lvl + 1))
            (cfg.itemSep.raw ++ [10] ++ rep ind (lvl + 1)) true its with
        | .error e => .error e
        | .ok (body, first) =>
          match stop with
          | some e => .error (xe e)
          | none => .ok ([123] ++ body ++ (if !first then [10] ++ rep ind lvl else []) ++ [125])
      | none =>
        match pyDictItemsX cfg b lvl seen (self :: anc) t [] cfg.itemSep.raw true its with
        | .error e => .error e
        | .ok (body, _) =>
          match stop with
          | some e => .error (xe e)
          | none => .ok ([123] ++ body ++ [125])
termination_by (2 * b + 1, 1, 0)

/-- The `for key, value in items` loop: unpacking, the key, `newline_indent` or `item_separator`,
`_encoder(key)`, `_key_separator`, and the value in the `try` that adds the note. -/
def pyDictItemsX (cfg : XCfg) (b lvl : Nat) (seen : List Nat) (anc : List XVal) (t : PyType)
    (nl sep : PStr) (first : Bool) (its : List (ItemShape × XKey × XVal)) : Except XErr (PStr × Bool) :=
  match its with
  | [] => .ok ([], first)
  | (sh, k, x) :: rest =>
    match sh with
    | .bad e => .error (xe e)
    | _ =>
      match pyKeyX cfg b k with
      | .error e => .error e
      | .ok none => pyDictItemsX cfg b lvl seen anc t nl sep first rest
      | .ok (some ks) =>
        match pyEncStrX cfg b ks with
        | .error e => .error e
        | .ok kt =>
          match pyItemX cfg b lvl seen anc x with
          | .error e => addNote (.key t (.conv ks)) (.error e)
          | .ok tx =>
            match pyDictItemsX cfg b lvl seen anc t nl sep false rest with
            | .error e => .error e
            | .ok (r, f) => .ok ((if first then nl else sep) ++ kt ++ cfg.keySep.raw ++ tx ++ r, f)
termination_by (2 * b + 1, 0, its.length)
end

/-- `''.join(JSONEncoder(...).iterencode(o))` and, for a value that is not a `str`,
`JSONEncoder.encode(o)` without `_json`: `p` frames left where the generator is driven;
`_iterencode_once` and `_iterencode` take one each. -/
def iterJoinPyX (cfg : XCfg) (p : Nat) (v : XVal) : XR :=
  pyCallX p fun p' _ => pyCallX p' fun p'' _ => pyIterX cfg p'' 0 [] [] v

/-- `JSONEncoder.encode(o)` without `_json`, encoder.py:185-205: a `str` goes to
`encode_basestring(_ascii)` directly. -/
def dumpsPyX (cfg : XCfg) (p : Nat) (v : XVal) : XR :=
  match v with
  | .str s => pyEncStrX cfg p s
  | _ => iterJoinPyX cfg p v

end PyLean.JsonMod
