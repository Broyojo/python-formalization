import PyLean.JsonMod.Basic

/-!
The two encoders of CPython 3.14.7: `py_encode_basestring(_ascii)` and
`_make_iterencode` (Lib/json/encoder.py) and `c_make_encoder`,
`c_encode_basestring(_ascii)` (Modules/_json.c), both reached through
`JSONEncoder.encode` (`json.dumps`).

Values (`EVal`) are trees of `None`, `bool`, `int`, `str`, `float`, `list`,
`dict`, plus two kinds of leaves that are not JSON: `back k`, a reference to the
`k`-th enclosing container (a reference cycle), and `other n t`, an object of
type `t` the encoder does not know, handed to `default()`, an abstract function
of the object's identity `n` (`ECfg.dflt`).

A float is its IEEE-754 bits, which decide the branches of `floatstr` and
`encoder_encode_float`, with the text of `float.__repr__` carried as data until
the binary64 model exists. Container subclasses are out of scope.

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
  /-- A float: its bits and `repr`. -/
  | flt (bits : Nat) (repr : PStr)
  deriving DecidableEq, Repr, Inhabited

/-- A Python object passed to `json.dumps`. -/
inductive EVal where
  | none
  | bool (b : Bool)
  | int (n : Int)
  | str (s : PStr)
  /-- A float: its bits and `repr`. -/
  | flt (bits : Nat) (repr : PStr)
  | list (xs : List EVal)
  | dict (kvs : List (EKey × EVal))
  /-- The `k`-th enclosing list or dict (`0` is the innermost): a cycle. -/
  | back (k : Nat)
  /-- An object of type `t` with identity `n`, handed to `default()`. -/
  | other (n : Nat) (t : String)
  deriving Repr, Inhabited

/-- `TypeError` raised by `JSONEncoder.default`, encoder.py:182-183. -/
def defaultErr (t : String) : PyExc := .typeError s!"Object of type {t} is not JSON serializable"

/-- What a custom `encoder` passed to `make_encoder` returns. -/
inductive EncOut where
  | str (s : PStr)
  /-- Not a `str`: the name of its type. -/
  | nonstr (t : String)

/-- Encoder options after `JSONEncoder.__init__`/`iterencode`. -/
structure ECfg where
  ensureAscii : Bool := true
  checkCircular : Bool := true
  allowNan : Bool := true
  sortKeys : Bool := false
  skipKeys : Bool := false
  indent : Option PStr := none
  itemSep : PStr := cs ", "
  keySep : PStr := cs ": "
  /-- `default(o)`, for the object `other n t`. -/
  dflt : Nat → String → Except PyExc EVal := fun _ t => .error (defaultErr t)
  /-- An upper bound on the nesting added by `default()`: part of the fuel. -/
  dfltDepth : Nat := 0
  /-- The `encoder` of `make_encoder`, when it is not one of the two C functions
  (`fast_encode` is then `NULL`). -/
  customEnc : Option (PStr → Except PyExc EncOut) := none

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

/-! ### Floats -/

def fltExp (bits : Nat) : Nat := bits / 2 ^ 52 % 2 ^ 11
def fltMant (bits : Nat) : Nat := bits % 2 ^ 52
def fltNeg (bits : Nat) : Bool := bits / 2 ^ 63 % 2 == 1

/-- `o != o`. -/
def fltIsNan (bits : Nat) : Bool := fltExp bits == 2047 && fltMant bits != 0
/-- `isfinite(i)`. -/
def fltIsFinite (bits : Nat) : Bool := fltExp bits != 2047
/-- `o == INFINITY`. -/
def fltIsPosInf (bits : Nat) : Bool := fltExp bits == 2047 && fltMant bits == 0 && !fltNeg bits
/-- `o == -INFINITY`. -/
def fltIsNegInf (bits : Nat) : Bool := fltExp bits == 2047 && fltMant bits == 0 && fltNeg bits

/-- `ValueError` for a non-finite float with `allow_nan=False`. -/
def outOfRange (repr : PStr) : PyExc :=
  .valueError ("Out of range float values are not JSON compliant: " ++ String.ofList (repr.map Char.ofNat))

/-- `floatstr` in `JSONEncoder.iterencode`, encoder.py:226-246. -/
def pyFloatStr (cfg : ECfg) (bits : Nat) (repr : PStr) : Except PyExc PStr :=
  let text : Option PStr :=
    if fltIsNan bits then some (cs "NaN")
    else if fltIsPosInf bits then some (cs "Infinity")
    else if fltIsNegInf bits then some (cs "-Infinity")
    else none
  match text with
  | none => .ok repr
  | some t => if !cfg.allowNan then .error (outOfRange repr) else .ok t

/-- `encoder_encode_float`, Modules/_json.c:1509-1534. -/
def cEncodeFloat (cfg : ECfg) (bits : Nat) (repr : PStr) : Except PyExc PStr :=
  if !fltIsFinite bits then
    if !cfg.allowNan then .error (outOfRange repr)
    else if fltIsPosInf bits then .ok (cs "Infinity")
    else if fltIsNegInf bits then .ok (cs "-Infinity")
    else .ok (cs "NaN")
  else .ok repr

/-- `int.__repr__` (`_PyLong_Format`), Objects/longobject.c:2209-2215: more than
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

/-- `S_CHAR`, Modules/_json.c:122. -/
def sChar (c : Nat) : Bool := 32 ≤ c && c ≤ 126 && c != 92 && c != 34

/-- `\uXXXX` as written by `ascii_escape_unichar` (`Py_hexdigits`, lower case). -/
def cU (v : Nat) : PStr := [117, hexCp (v >>> 12 &&& 0xf), hexCp (v >>> 8 &&& 0xf), hexCp (v >>> 4 &&& 0xf), hexCp (v &&& 0xf)]

/-- `ascii_escape_unichar`, Modules/_json.c:125-159. -/
def cAsciiEscapeChar (c : Nat) : PStr :=
  92 :: (if c = 92 then [92] else if c = 34 then [34] else if c = 8 then [98]
    else if c = 12 then [102] else if c = 10 then [110] else if c = 13 then [114]
    else if c = 9 then [116]
    else if c ≥ 0x10000 then
      -- `Py_UNICODE_HIGH_SURROGATE`/`Py_UNICODE_LOW_SURROGATE`
      cU (0xd800 - (0x10000 >>> 10) + (c >>> 10)) ++ [92] ++ cU (0xdc00 + (c &&& 0x3ff))
    else cU c)

/-- `ascii_escape_unicode`, Modules/_json.c@3.14.7:149-210. -/
def cAsciiEscape (s : PStr) : PStr :=
  [34] ++ s.flatMap (fun c => if sChar c then [c] else cAsciiEscapeChar c) ++ [34]

/-- `escape_unicode`, Modules/_json.c:224-368 (`ENCODE_OUTPUT`). -/
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
  | .int _ | .bool _ | .flt _ _ => 0
  | .str _ => 1
  | .none => 2
  | .tup _ => 3

/-- Lexicographic `<` on code points (`str` comparison). -/
def strLt : PStr → PStr → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => a < b || (a == b && strLt s t)

/-- A numeric key as `(rank, n, d)`: `rank` is -1, 0 or 1 for -inf, finite and
inf, and a finite value is the fraction `n / d`, `d > 0`. NaN keys are out of
scope for `sort_keys`: they make `<` inconsistent, and the order then depends on
the sort. -/
def EKey.num : EKey → Int × Int × Nat
  | .int a => (0, a, 1)
  | .bool a => (0, if a then 1 else 0, 1)
  | .flt b _ =>
    if fltIsNegInf b then (-1, 0, 1)
    else if fltIsPosInf b then (1, 0, 1)
    else
      let e := fltExp b
      let m := if e = 0 then fltMant b else fltMant b + 2 ^ 52
      let sh := if e = 0 then 1 else e
      let v : Int := if fltNeg b then -(m : Int) else m
      if sh ≥ 1075 then (0, v * 2 ^ (sh - 1075), 1) else (0, v, 2 ^ (1075 - sh))
  | _ => (0, 0, 1)

/-- `<` within a class. -/
def EKey.lt : EKey → EKey → Bool
  | .str a, .str b => strLt a b
  | .tup a, .tup b => a < b
  | a, b =>
    let (ra, na, da) := a.num
    let (rb, nb, db) := b.num
    ra < rb || (ra == rb && na * db < nb * da)

def insertItem (p : EKey × EVal) : List (EKey × EVal) → List (EKey × EVal)
  | [] => [p]
  | q :: t => if p.1.lt q.1 then p :: q :: t else q :: insertItem p t

/-- `sorted(dct.items())` (encoder.py:347) and `PyList_Sort(items)` (_json.c@3.14.7:1700):
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

def circularErr : PyExc := .valueError "Circular reference detected"

/-- Infinite recursion through a cycle when `check_circular=False`. -/
def recursionErr : PyExc := .named "RecursionError" "~maximum recursion depth exceeded"

/-- `indent * k`. -/
def rep (t : PStr) : Nat → PStr
  | 0 => []
  | k + 1 => t ++ rep t k

/-! ### Pure-Python encoder: `_make_iterencode`, encoder.py@3.14.7:265-461 -/

def pyStrEnc (cfg : ECfg) (s : PStr) : PStr :=
  if cfg.ensureAscii then pyEncodeBasestringAscii s else pyEncodeBasestring s

/-- The key conversion of `_iterencode_dict`, encoder.py:351-371: the key text,
`none` for a skipped key, or the error. -/
def pyKeyStr (cfg : ECfg) : EKey → Except PyExc (Option PStr)
  | .str s => .ok (some s)
  | .flt b r => (pyFloatStr cfg b r).map some
  | .bool true => .ok (some (cs "true"))
  | .bool false => .ok (some (cs "false"))
  | .none => .ok (some (cs "null"))
  | .int n => (intRepr n).map some
  | .tup _ => if cfg.skipKeys then .ok none else .error badKeyErr

mutual
/-- `_iterencode(o, _current_indent_level)`, encoder.py:415-449. -/
def pyEnc (cfg : ECfg) : Nat → Nat → List Nat → EVal → ER
  | 0, _, _, _ => .error .modelFuel
  | f + 1, lvl, seen, v =>
    match v with
    | .str s => .ok (pyStrEnc cfg s)
    | .none => .ok (cs "null")
    | .bool true => .ok (cs "true")
    | .bool false => .ok (cs "false")
    | .int n => intRepr n
    | .flt b r => pyFloatStr cfg b r
    | .list xs =>
      -- `_iterencode_list`, encoder.py:269-326
      if xs = [] then .ok (cs "[]")
      else
        let (lvl, nl, sep) : Nat × Option PStr × PStr :=
          match cfg.indent with
          | some ind => (lvl + 1, some ([10] ++ rep ind (lvl + 1)), cfg.itemSep ++ [10] ++ rep ind (lvl + 1))
          | none => (lvl, none, cfg.itemSep)
        match pyEncList cfg f lvl seen sep true xs with
        | .error e => .error e
        | .ok body =>
          let close : PStr := match cfg.indent with
            | some ind => [10] ++ rep ind (lvl - 1)
            | none => []
          .ok ([91] ++ nl.getD [] ++ body ++ close ++ [93])
    | .dict kvs =>
      -- `_iterencode_dict`, encoder.py:328-413
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
          match pyEncItems cfg f lvl seen nl sep true items with
          | .error e => .error e
          | .ok (body, first) =>
            let close : PStr := match cfg.indent with
              | some ind => if first then [] else [10] ++ rep ind (lvl - 1)
              | none => []
            .ok ([123] ++ body ++ close ++ [125])
    | .back _ => .error (if cfg.checkCircular then circularErr else recursionErr)
    | .other n t =>
      -- encoder.py:435-449. `seen` holds the objects being serialized: they are
      -- `markers`, and without `check_circular` a repeat recurses forever.
      if n ∈ seen then .error (if cfg.checkCircular then circularErr else recursionErr)
      else
        match cfg.dflt n t with
        | .error e => .error e
        | .ok v' => pyEnc cfg f lvl (n :: seen) v'
termination_by f _ _ v => (f, sizeOf v)

/-- The `for i, value in enumerate(lst)` loop of `_iterencode_list`. -/
def pyEncList (cfg : ECfg) : Nat → Nat → List Nat → PStr → Bool → List EVal → ER
  | _, _, _, _, _, [] => .ok []
  | f, lvl, seen, sep, first, x :: xs =>
    match pyEnc cfg f lvl seen x with
    | .error e => .error e
    | .ok t =>
      match pyEncList cfg f lvl seen sep false xs with
      | .error e => .error e
      | .ok rest => .ok ((if first then [] else sep) ++ t ++ rest)
termination_by f _ _ _ _ xs => (f, sizeOf xs)

/-- The `for key, value in items` loop of `_iterencode_dict`; also returns
whether nothing was written (`first`). -/
def pyEncItems (cfg : ECfg) : Nat → Nat → List Nat → Option PStr → PStr → Bool → List (EKey × EVal) → Except PyExc (PStr × Bool)
  | _, _, _, _, _, first, [] => .ok ([], first)
  | f, lvl, seen, nl, sep, first, (k, x) :: xs =>
    match pyKeyStr cfg k with
    | .error e => .error e
    | .ok none => pyEncItems cfg f lvl seen nl sep first xs
    | .ok (some ks) =>
      let pre : PStr := if first then nl.getD [] else sep
      match pyEnc cfg f lvl seen x with
      | .error e => .error e
      | .ok t =>
        match pyEncItems cfg f lvl seen nl sep false xs with
        | .error e => .error e
        | .ok (rest, fst) => .ok (pre ++ pyStrEnc cfg ks ++ cfg.keySep ++ t ++ rest, fst)
termination_by f _ _ _ _ _ items => (f, sizeOf items)
end

/-! ### C encoder: `encoder_listencode_obj` and friends, Modules/_json.c:1568-1994 -/

/-- `encoder_encode_string` with `fast_encode` (@3.14.7:1449-1467). -/
def cStrEnc (cfg : ECfg) (s : PStr) : PStr :=
  if cfg.ensureAscii then cAsciiEscape s else cEscape s

/-- `encoder_encode_string` with a custom `encoder` (@3.14.7:1456-1466), or with
`fast_encode`. -/
def cEncStr (cfg : ECfg) (s : PStr) : ER :=
  match cfg.customEnc with
  | none => .ok (cStrEnc cfg s)
  | some g =>
    match g s with
    | .error e => .error e
    | .ok (.str t) => .ok t
    | .ok (.nonstr t) => .error (.typeError s!"encoder() must return a string, not {(String.ofList (t.toList.take 80))}")

/-- `_encoded_const`, :1490-1507: `None`, `True`, `False` as text. -/
def encodedConst : Option Bool → PStr
  | none => cs "null"
  | some true => cs "true"
  | some false => cs "false"

/-- The key conversion of `encoder_encode_key_value`, :1677-1700. -/
def cKeyStr (cfg : ECfg) : EKey → Except PyExc (Option PStr)
  | .str s => .ok (some s)
  | .flt b r => (cEncodeFloat cfg b r).map some
  | .bool b => .ok (some (encodedConst (some b)))
  | .none => .ok (some (encodedConst none))
  | .int n => (intRepr n).map some
  | .tup _ => if cfg.skipKeys then .ok none else .error badKeyErr

/-- The indent cache entries (:1361-1436): `'\n' + indent * k` and
`item_separator + '\n' + indent * k`. -/
def cNewlineIndent (ind : PStr) (k : Nat) : PStr := [10] ++ rep ind k
def cSepIndent (cfg : ECfg) (ind : PStr) (k : Nat) : PStr := cfg.itemSep ++ cNewlineIndent ind k

mutual
/-- `encoder_listencode_obj`, :1568-1668. -/
def cEnc (cfg : ECfg) : Nat → Nat → List Nat → EVal → ER
  | 0, _, _, _ => .error .modelFuel
  | f + 1, lvl, seen, v =>
    match v with
    | .none => .ok (cs "null")
    | .bool b => .ok (if b then cs "true" else cs "false")
    | .str s => cEncStr cfg s
    | .int n => intRepr n
    | .flt b r => cEncodeFloat cfg b r
    | .list xs =>
      -- `encoder_listencode_list`, :1915-1994
      if xs.length = 0 then .ok (cs "[]")
      else
        let (lvl, pre, sep) : Nat × PStr × PStr :=
          match cfg.indent with
          | some ind => (lvl + 1, cNewlineIndent ind (lvl + 1), cSepIndent cfg ind (lvl + 1))
          | none => (lvl, [], cfg.itemSep)
        match cEncList cfg f lvl seen sep 0 xs with
        | .error e => .error e
        | .ok body =>
          let post : PStr := match cfg.indent with
            | some ind => cNewlineIndent ind (lvl - 1)
            | none => []
          .ok ([91] ++ pre ++ body ++ post ++ [93])
    | .dict kvs =>
      -- `encoder_listencode_dict`, :1797-1887
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
          match cEncItems cfg f lvl seen sep true items with
          | .error e => .error e
          | .ok (body, first) =>
            let post : PStr := match cfg.indent with
              | some ind => if !first then cNewlineIndent ind (lvl - 1) else []
              | none => []
            .ok ([123] ++ body ++ post ++ [125])
    | .back _ => .error (if cfg.checkCircular then circularErr else recursionErr)
    | .other n t =>
      -- :1629-1666, with `seen` as in `pyEnc`
      if n ∈ seen then .error (if cfg.checkCircular then circularErr else recursionErr)
      else
        match cfg.dflt n t with
        | .error e => .error e
        | .ok v' => cEnc cfg f lvl (n :: seen) v'
termination_by f _ _ v => (f, sizeOf v)

/-- The item loop of `encoder_listencode_list`, @3.14.7:1817-1832. -/
def cEncList (cfg : ECfg) : Nat → Nat → List Nat → PStr → Nat → List EVal → ER
  | _, _, _, _, _, [] => .ok []
  | f, lvl, seen, sep, i, x :: xs =>
    let pre : PStr := if i ≠ 0 then sep else []
    match cEnc cfg f lvl seen x with
    | .error e => .error e
    | .ok t =>
      match cEncList cfg f lvl seen sep (i + 1) xs with
      | .error e => .error e
      | .ok rest => .ok (pre ++ t ++ rest)
termination_by f _ _ _ _ xs => (f, sizeOf xs)

/-- The item loop of `encoder_listencode_dict` with `encoder_encode_key_value`
(:1669-1736); also returns `first`. -/
def cEncItems (cfg : ECfg) : Nat → Nat → List Nat → PStr → Bool → List (EKey × EVal) → Except PyExc (PStr × Bool)
  | _, _, _, _, first, [] => .ok ([], first)
  | f, lvl, seen, sep, first, (k, x) :: xs =>
    match cKeyStr cfg k with
    | .error e => .error e
    | .ok none => cEncItems cfg f lvl seen sep first xs
    | .ok (some ks) =>
      let pre : PStr := if first then (match cfg.indent with
          | some ind => cNewlineIndent ind lvl
          | none => []) else sep
      match cEncStr cfg ks with
      | .error e => .error e
      | .ok kt =>
        match cEnc cfg f lvl seen x with
        | .error e => .error e
        | .ok t =>
          match cEncItems cfg f lvl seen sep false xs with
          | .error e => .error e
          | .ok (rest, fst) => .ok (pre ++ kt ++ cfg.keySep ++ t ++ rest, fst)
termination_by f _ _ _ _ items => (f, sizeOf items)
end

/-- Fuel for one value. -/
def encFuel (cfg : ECfg) (v : EVal) : Nat := v.depth + 1 + cfg.dfltDepth

/-- `JSONEncoder.encode(o)`, encoder.py:185-205, with the pure-Python encoder. -/
def dumpsPy (cfg : ECfg) (v : EVal) : ER :=
  match v with
  | .str s => .ok (pyStrEnc cfg s)
  | _ => pyEnc cfg (encFuel cfg v) 0 [] v

/-- `JSONEncoder.encode(o)` with `c_make_encoder`. -/
def dumpsC (cfg : ECfg) (v : EVal) : ER :=
  match v with
  | .str s => .ok (if cfg.ensureAscii then cAsciiEscape s else cEscape s)
  | _ => cEnc cfg (encFuel cfg v) 0 [] v

end PyLean.JsonMod
