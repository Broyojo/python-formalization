import PyLean.JsonMod.Basic

/-!
The two encoders of CPython 3.14.7: `py_encode_basestring(_ascii)` and
`_make_iterencode` (Lib/json/encoder.py) and `c_make_encoder`,
`c_encode_basestring(_ascii)` (Modules/_json.c), both reached through
`JSONEncoder.encode` (`json.dumps`).

Values (`EVal`) are trees of `None`, `bool`, `int`, `str`, `list`, `dict`,
plus two kinds of leaves that are not JSON: `back k`, a reference to the `k`-th
enclosing container (a reference cycle), and `other`, an object the encoder
does not know (a `bytes` object), for which the default `default()` raises.
Floats, `default=` callbacks and container subclasses are out of scope.

`indent` and the separators are the strings `JSONEncoder.iterencode` passes on
(an int `indent` has already become `' ' * indent`, encoder.py:249-252).
-/

namespace PyLean.JsonMod

open PyLean

/-- A dict key: `str`, `int`, `bool`, `None`, or a 1-tuple of ints (not a valid
JSON key: skipped with `skipkeys`, otherwise `TypeError`). -/
inductive EKey where
  | str (s : PStr)
  | int (n : Int)
  | bool (b : Bool)
  | none
  | tup (n : Int)
  deriving DecidableEq, Repr, Inhabited

/-- A Python object passed to `json.dumps`. -/
inductive EVal where
  | none
  | bool (b : Bool)
  | int (n : Int)
  | str (s : PStr)
  | list (xs : List EVal)
  | dict (kvs : List (EKey × EVal))
  /-- The `k`-th enclosing list or dict (`0` is the innermost): a cycle. -/
  | back (k : Nat)
  /-- A `bytes` object: `JSONEncoder.default` raises `TypeError`. -/
  | other
  deriving Repr, Inhabited

/-- Encoder options after `JSONEncoder.__init__`/`iterencode`. -/
structure ECfg where
  ensureAscii : Bool := true
  checkCircular : Bool := true
  sortKeys : Bool := false
  skipKeys : Bool := false
  indent : Option PStr := none
  itemSep : PStr := cs ", "
  keySep : PStr := cs ": "
  deriving DecidableEq, Repr, Inhabited

abbrev ER := Except PyExc PStr

mutual
/-- Nesting depth, used as fuel. -/
def EVal.depth : EVal → Nat
  | .list xs => EVal.depthList xs + 1
  | .dict kvs => EVal.depthItems kvs + 1
  | _ => 0
def EVal.depthList : List EVal → Nat
  | [] => 0
  | x :: xs => max (EVal.depth x) (EVal.depthList xs)
def EVal.depthItems : List (EKey × EVal) → Nat
  | [] => 0
  | (_, x) :: xs => max (EVal.depth x) (EVal.depthItems xs)
end

/-! ### `int.__repr__` -/

/-- Decimal digits of `n` (fuel `f > n` suffices). -/
def decDigitsF : Nat → Nat → PStr
  | 0, _ => []
  | f + 1, n => if n < 10 then [48 + n] else decDigitsF f (n / 10) ++ [48 + n % 10]

def decDigits (n : Nat) : PStr := decDigitsF (n + 1) n

/-- `int.__repr__` (`_PyLong_Format`), Objects/longobject.c:2133-2139: more than
4300 digits raise `ValueError`. -/
def intRepr (n : Int) : ER :=
  let ds := decDigits n.natAbs
  if ds.length > maxStrDigits then
    .error (.valueError "Exceeds the limit (4300 digits) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit")
  else .ok (if n < 0 then 45 :: ds else ds)

/-! ### String escaping -/

/-- Lower-case hex digit as a code point. -/
def hexCp (n : Nat) : Nat := if n < 10 then 48 + n else 87 + n

/-- `'\\u{0:04x}'.format(n)` for `n < 0x10000`. -/
def uEsc (n : Nat) : PStr :=
  [92, 117, hexCp (n / 4096 % 16), hexCp (n / 256 % 16), hexCp (n / 16 % 16), hexCp (n % 16)]

/-- `ESCAPE_DCT`, encoder.py:21-33. -/
def escDct (c : Nat) : Option PStr :=
  if c = 92 then some [92, 92]
  else if c = 34 then some [92, 34]
  else if c = 8 then some [92, 98]
  else if c = 12 then some [92, 102]
  else if c = 10 then some [92, 110]
  else if c = 13 then some [92, 114]
  else if c = 9 then some [92, 116]
  else if c < 32 then some (uEsc c)
  else none

/-- `py_encode_basestring`, encoder.py:37-43: `ESCAPE = [\x00-\x1f\\"\b\f\n\r\t]`. -/
def pyEncodeBasestring (s : PStr) : PStr :=
  [34] ++ s.flatMap (fun c => if c < 32 ∨ c = 92 ∨ c = 34 then (escDct c).getD [] else [c]) ++ [34]

/-- The `replace` callback of `py_encode_basestring_ascii`, encoder.py:53-67. -/
def pyAsciiReplace (c : Nat) : PStr :=
  match escDct c with
  | some r => r
  | none =>
    if c < 0x10000 then uEsc c
    else
      let n := c - 0x10000
      uEsc (0xd800 ||| ((n >>> 10) &&& 0x3ff)) ++ uEsc (0xdc00 ||| (n &&& 0x3ff))

/-- `py_encode_basestring_ascii`, encoder.py:49-68: `ESCAPE_ASCII = ([\\"]|[^\ -~])`. -/
def pyEncodeBasestringAscii (s : PStr) : PStr :=
  [34] ++ s.flatMap (fun c => if c = 92 ∨ c = 34 ∨ ¬(32 ≤ c ∧ c ≤ 126) then pyAsciiReplace c else [c]) ++ [34]

/-- `S_CHAR`, Modules/_json.c:31. -/
def sChar (c : Nat) : Bool := 32 ≤ c && c ≤ 126 && c != 92 && c != 34

/-- `\uXXXX` as written by `ascii_escape_unichar` (`Py_hexdigits`, lower case). -/
def cU (v : Nat) : PStr := [117, hexCp (v >>> 12 &&& 0xf), hexCp (v >>> 8 &&& 0xf), hexCp (v >>> 4 &&& 0xf), hexCp (v &&& 0xf)]

/-- `ascii_escape_unichar`, Modules/_json.c:113-147. -/
def cAsciiEscapeChar (c : Nat) : PStr :=
  92 :: (if c = 92 then [92] else if c = 34 then [34] else if c = 8 then [98]
    else if c = 12 then [102] else if c = 10 then [110] else if c = 13 then [114]
    else if c = 9 then [116]
    else if c ≥ 0x10000 then
      -- `Py_UNICODE_HIGH_SURROGATE`/`Py_UNICODE_LOW_SURROGATE`
      cU (0xd800 - (0x10000 >>> 10) + (c >>> 10)) ++ [92] ++ cU (0xdc00 + (c &&& 0x3ff))
    else cU c)

/-- `ascii_escape_unicode`, Modules/_json.c:149-210. -/
def cAsciiEscape (s : PStr) : PStr :=
  [34] ++ s.flatMap (fun c => if sChar c then [c] else cAsciiEscapeChar c) ++ [34]

/-- `escape_unicode`, Modules/_json.c:212-304 (`ENCODE_OUTPUT`). -/
def cEscapeChar (c : Nat) : PStr :=
  if c = 92 then [92, 92] else if c = 34 then [92, 34] else if c = 8 then [92, 98]
  else if c = 12 then [92, 102] else if c = 10 then [92, 110] else if c = 13 then [92, 114]
  else if c = 9 then [92, 116]
  else if c ≤ 0x1f then [92, 117, 48, 48, hexCp (c >>> 4 &&& 0xf), hexCp (c &&& 0xf)]
  else [c]

def cEscape (s : PStr) : PStr := [34] ++ s.flatMap cEscapeChar ++ [34]

/-! ### Keys and sorting -/

/-- Comparison classes for `sort_keys`: values of different classes raise
`TypeError` on `<`. -/
def EKey.cls : EKey → Nat
  | .int _ | .bool _ => 0
  | .str _ => 1
  | .none => 2
  | .tup _ => 3

/-- Lexicographic `<` on code points (`str` comparison). -/
def strLt : PStr → PStr → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => a < b || (a == b && strLt s t)

/-- `<` within a class. -/
def EKey.lt : EKey → EKey → Bool
  | .str a, .str b => strLt a b
  | .int a, .int b => a < b
  | .int a, .bool b => a < (if b then 1 else 0)
  | .bool a, .int b => (if a then 1 else 0) < b
  | .bool a, .bool b => !a && b
  | .tup a, .tup b => a < b
  | _, _ => false

def insertItem (p : EKey × EVal) : List (EKey × EVal) → List (EKey × EVal)
  | [] => [p]
  | q :: t => if p.1.lt q.1 then p :: q :: t else q :: insertItem p t

/-- `sorted(dct.items())` (encoder.py:358) and `PyList_Sort(items)` (_json.c:1714):
the keys of a dict are distinct, so tuples compare by key alone. When keys of
two classes are present some comparison between them raises; which one depends
on the sort, so the message is not modelled. -/
def sortItems (kvs : List (EKey × EVal)) : Except PyExc (List (EKey × EVal)) :=
  match kvs with
  | [] => .ok []
  | [p] => .ok [p]
  | p :: t =>
    if t.all (fun q => q.1.cls == p.1.cls) && p.1.cls != 2 then .ok (kvs.foldr insertItem [])
    else .error (.typeError "~'<' not supported between instances")

/-- `TypeError` for a key that is not str, int, float, bool or None. -/
def badKeyErr : PyExc := .typeError "keys must be str, int, float, bool or None, not tuple"

/-- `TypeError` raised by `JSONEncoder.default`. -/
def defaultErr : PyExc := .typeError "Object of type bytes is not JSON serializable"

def circularErr : PyExc := .valueError "Circular reference detected"

/-- Infinite recursion through a cycle when `check_circular=False`. -/
def recursionErr : PyExc := .named "RecursionError" "~maximum recursion depth exceeded"

/-- `indent * k`. -/
def rep (t : PStr) : Nat → PStr
  | 0 => []
  | k + 1 => t ++ rep t k

/-! ### Pure-Python encoder: `_make_iterencode`, encoder.py:265-461 -/

def pyStrEnc (cfg : ECfg) (s : PStr) : PStr :=
  if cfg.ensureAscii then pyEncodeBasestringAscii s else pyEncodeBasestring s

/-- The key conversion of `_iterencode_dict`, encoder.py:362-382: the key text,
`none` for a skipped key, or the error. -/
def pyKeyStr (cfg : ECfg) : EKey → Except PyExc (Option PStr)
  | .str s => .ok (some s)
  | .bool true => .ok (some (cs "true"))
  | .bool false => .ok (some (cs "false"))
  | .none => .ok (some (cs "null"))
  | .int n => (intRepr n).map some
  | .tup _ => if cfg.skipKeys then .ok none else .error badKeyErr

mutual
/-- `_iterencode(o, _current_indent_level)`, encoder.py:426-460. -/
def pyEnc (cfg : ECfg) : Nat → Nat → EVal → ER
  | 0, _, _ => .error .modelFuel
  | f + 1, lvl, v =>
    match v with
    | .str s => .ok (pyStrEnc cfg s)
    | .none => .ok (cs "null")
    | .bool true => .ok (cs "true")
    | .bool false => .ok (cs "false")
    | .int n => intRepr n
    | .list xs =>
      -- `_iterencode_list`, encoder.py:280-337
      if xs = [] then .ok (cs "[]")
      else
        let (lvl, nl, sep) : Nat × Option PStr × PStr :=
          match cfg.indent with
          | some ind => (lvl + 1, some ([10] ++ rep ind (lvl + 1)), cfg.itemSep ++ [10] ++ rep ind (lvl + 1))
          | none => (lvl, none, cfg.itemSep)
        match pyEncList cfg f lvl sep true xs with
        | .error e => .error e
        | .ok body =>
          let close : PStr := match cfg.indent with
            | some ind => [10] ++ rep ind (lvl - 1)
            | none => []
          .ok ([91] ++ nl.getD [] ++ body ++ close ++ [93])
    | .dict kvs =>
      -- `_iterencode_dict`, encoder.py:339-424
      if kvs = [] then .ok (cs "{}")
      else
        let (lvl, nl, sep) : Nat × Option PStr × PStr :=
          match cfg.indent with
          | some ind => (lvl + 1, some ([10] ++ rep ind (lvl + 1)), cfg.itemSep ++ [10] ++ rep ind (lvl + 1))
          | none => (lvl, none, cfg.itemSep)
        let items := if cfg.sortKeys then sortItems kvs else .ok kvs
        match items with
        | .error e => .error e
        | .ok items =>
          match pyEncItems cfg f lvl nl sep true items with
          | .error e => .error e
          | .ok (body, first) =>
            let close : PStr := match cfg.indent with
              | some ind => if first then [] else [10] ++ rep ind (lvl - 1)
              | none => []
            .ok ([123] ++ body ++ close ++ [125])
    | .back _ => .error (if cfg.checkCircular then circularErr else recursionErr)
    | .other => .error defaultErr

/-- The `for i, value in enumerate(lst)` loop of `_iterencode_list`. -/
def pyEncList (cfg : ECfg) : Nat → Nat → PStr → Bool → List EVal → ER
  | _, _, _, _, [] => .ok []
  | f, lvl, sep, first, x :: xs =>
    match pyEnc cfg f lvl x with
    | .error e => .error e
    | .ok t =>
      match pyEncList cfg f lvl sep false xs with
      | .error e => .error e
      | .ok rest => .ok ((if first then [] else sep) ++ t ++ rest)

/-- The `for key, value in items` loop of `_iterencode_dict`; also returns
whether nothing was written (`first`). -/
def pyEncItems (cfg : ECfg) : Nat → Nat → Option PStr → PStr → Bool → List (EKey × EVal) → Except PyExc (PStr × Bool)
  | _, _, _, _, first, [] => .ok ([], first)
  | f, lvl, nl, sep, first, (k, x) :: xs =>
    match pyKeyStr cfg k with
    | .error e => .error e
    | .ok none => pyEncItems cfg f lvl nl sep first xs
    | .ok (some ks) =>
      let pre : PStr := if first then nl.getD [] else sep
      match pyEnc cfg f lvl x with
      | .error e => .error e
      | .ok t =>
        match pyEncItems cfg f lvl nl sep false xs with
        | .error e => .error e
        | .ok (rest, fst) => .ok (pre ++ pyStrEnc cfg ks ++ cfg.keySep ++ t ++ rest, fst)
end

/-! ### C encoder: `encoder_listencode_obj` and friends, Modules/_json.c:1478-1886 -/

/-- `encoder_encode_string` with `fast_encode` (:1449-1467). -/
def cStrEnc (cfg : ECfg) (s : PStr) : PStr :=
  if cfg.ensureAscii then cAsciiEscape s else cEscape s

/-- The key conversion of `encoder_encode_key_value`, :1583-1607. -/
def cKeyStr (cfg : ECfg) : EKey → Except PyExc (Option PStr)
  | .str s => .ok (some s)
  | .bool b => .ok (some (if b then cs "true" else cs "false"))
  | .none => .ok (some (cs "null"))
  | .int n => (intRepr n).map some
  | .tup _ => if cfg.skipKeys then .ok none else .error badKeyErr

/-- The indent cache entries (:1275-1349): `'\n' + indent * k` and
`item_separator + '\n' + indent * k`. -/
def cNewlineIndent (ind : PStr) (k : Nat) : PStr := [10] ++ rep ind k
def cSepIndent (cfg : ECfg) (ind : PStr) (k : Nat) : PStr := cfg.itemSep ++ cNewlineIndent ind k

mutual
/-- `encoder_listencode_obj`, :1478-1573. -/
def cEnc (cfg : ECfg) : Nat → Nat → EVal → ER
  | 0, _, _ => .error .modelFuel
  | f + 1, lvl, v =>
    match v with
    | .none => .ok (cs "null")
    | .bool b => .ok (if b then cs "true" else cs "false")
    | .str s => .ok (cStrEnc cfg s)
    | .int n => intRepr n
    | .list xs =>
      -- `encoder_listencode_list`, :1790-1868
      if xs.length = 0 then .ok (cs "[]")
      else
        let (lvl, pre, sep) : Nat × PStr × PStr :=
          match cfg.indent with
          | some ind => (lvl + 1, cNewlineIndent ind (lvl + 1), cSepIndent cfg ind (lvl + 1))
          | none => (lvl, [], cfg.itemSep)
        match cEncList cfg f lvl sep 0 xs with
        | .error e => .error e
        | .ok body =>
          let post : PStr := match cfg.indent with
            | some ind => cNewlineIndent ind (lvl - 1)
            | none => []
          .ok ([91] ++ pre ++ body ++ post ++ [93])
    | .dict kvs =>
      -- `encoder_listencode_dict`, :1672-1788
      if kvs.length = 0 then .ok (cs "{}")
      else
        let (lvl, sep) : Nat × PStr :=
          match cfg.indent with
          | some ind => (lvl + 1, cSepIndent cfg ind (lvl + 1))
          | none => (lvl, cfg.itemSep)
        let items := if cfg.sortKeys then sortItems kvs else .ok kvs
        match items with
        | .error e => .error e
        | .ok items =>
          match cEncItems cfg f lvl sep true items with
          | .error e => .error e
          | .ok (body, first) =>
            let post : PStr := match cfg.indent with
              | some ind => if !first then cNewlineIndent ind (lvl - 1) else []
              | none => []
            .ok ([123] ++ body ++ post ++ [125])
    | .back _ => .error (if cfg.checkCircular then circularErr else recursionErr)
    | .other => .error defaultErr

/-- The item loop of `encoder_listencode_list`, :1841-1855. -/
def cEncList (cfg : ECfg) : Nat → Nat → PStr → Nat → List EVal → ER
  | _, _, _, _, [] => .ok []
  | f, lvl, sep, i, x :: xs =>
    let pre : PStr := if i ≠ 0 then sep else []
    match cEnc cfg f lvl x with
    | .error e => .error e
    | .ok t =>
      match cEncList cfg f lvl sep (i + 1) xs with
      | .error e => .error e
      | .ok rest => .ok (pre ++ t ++ rest)

/-- The item loop of `encoder_listencode_dict` with `encoder_encode_key_value`
(:1575-1670); also returns `first`. -/
def cEncItems (cfg : ECfg) : Nat → Nat → PStr → Bool → List (EKey × EVal) → Except PyExc (PStr × Bool)
  | _, _, _, first, [] => .ok ([], first)
  | f, lvl, sep, first, (k, x) :: xs =>
    match cKeyStr cfg k with
    | .error e => .error e
    | .ok none => cEncItems cfg f lvl sep first xs
    | .ok (some ks) =>
      let pre : PStr := if first then (match cfg.indent with
          | some ind => cNewlineIndent ind lvl
          | none => []) else sep
      match cEnc cfg f lvl x with
      | .error e => .error e
      | .ok t =>
        match cEncItems cfg f lvl sep false xs with
        | .error e => .error e
        | .ok (rest, fst) => .ok (pre ++ cStrEnc cfg ks ++ cfg.keySep ++ t ++ rest, fst)
end

/-- `JSONEncoder.encode(o)`, encoder.py:185-205, with the pure-Python encoder. -/
def dumpsPy (cfg : ECfg) (v : EVal) : ER :=
  match v with
  | .str s => .ok (pyStrEnc cfg s)
  | _ => pyEnc cfg (v.depth + 1) 0 v

/-- `JSONEncoder.encode(o)` with `c_make_encoder`. -/
def dumpsC (cfg : ECfg) (v : EVal) : ER :=
  match v with
  | .str s => .ok (if cfg.ensureAscii then cAsciiEscape s else cEscape s)
  | _ => cEnc cfg (v.depth + 1) 0 v

end PyLean.JsonMod
