import PyLean.JsonMod.Api

/-!
The Python-callable surface of `Modules/_json.c`: `py_scanstring_impl`,
`py_encode_basestring(_ascii)_impl` behind their Argument Clinic wrappers
(`Modules/clinic/_json.c.h`), the scanner type (`scanner_new`, `scanner_call`)
and the encoder type (`encoder_new`, `encoder_call`), with the indent cache.

These wrappers see any Python object, so a `str` argument is a `StrArg`. An
`indent` that is neither `None` nor a `str` cannot come from
`JSONEncoder.iterencode` (encoder.py:249-252) and is out of scope, as are
`__bool__` raising in the `p` conversions and a `markers` dict with entries.

Allocation: `create_indent_cache` builds `'\n' + indent * level` at the call, before anything
is written, so its failures are modelled: `unicode_repeat`'s `OverflowError`, and
`PyUnicode_New`'s `MemoryError` from its own size check (Objects/unicodeobject.c:1325-1326) or
from a `malloc` of `mallocLimit = 2^47` bytes or more (no 64-bit Linux or macOS process has that
much address space; the convention of `Itertools/Model.lean`). Smaller requests are assumed to
succeed, and so is every later allocation (the writer, the other cache entries): the encoder
models have no out-of-memory failure, a scope limit.
-/

namespace PyLean.JsonMod

open PyLean

/-- A Python object where a `str` is expected. -/
inductive StrArg where
  | str (s : PStr)
  /-- Any other object, by `tp_name`. -/
  | other (t : String)

def firstArgErr (t : String) : PyExc :=
  .typeError s!"first argument must be a string, not {truncName 80 t}"

/-- `_PyArg_BadArgument`, Python/getargs.c:662-670: `%.50s` of the type name,
and `None` for the `None` object. -/
def badArgErr (fname display t : String) : PyExc :=
  .typeError s!"{fname}() {display} must be str, not {truncName 50 (if t = "NoneType" then "None" else t)}"

/-- The `n` conversion, Python/getargs.c: `PyLong_AsSsize_t`. -/
def ssizeErr : PyExc := .overflowError "Python int too large to convert to C ssize_t"

def outOfSsize (i : Int) : Bool := decide (i < ssizeMin) || decide (i > ssizeMax)

/-- `py_scanstring(s, end, strict)` called directly, Lib/json/decoder.py:70-127:
the first `STRINGCHUNK.match(s, end)` converts `end` to `Py_ssize_t`. From the
scanner `end` is an index plus one, so `pyScanstring` is what it reaches. -/
def pyScanstringCall (s : PStr) (e : Int) (strict : Bool) : DR (PStr × Int) :=
  if outOfSsize e then .error (.exc ssizeErr) else pyScanstring s e strict

/-- `scanstring(pystr, end, strict)`: the clinic wrapper `py_scanstring`
(`Modules/clinic/_json.c.h:30-69`) checks `pystr` before it converts `end`, then
`py_scanstring_impl`, Modules/_json.c:665-672, with the check of
`scanstring_unicode` on a negative `end` (:494-497). -/
def cPyScanstring (x : StrArg) (e : Int) (strict : Bool) : DR (PStr × Int) :=
  match x with
  | .other t => .error (.exc (badArgErr "scanstring" "argument 1" t))
  | .str s =>
    if outOfSsize e then .error (.exc ssizeErr)
    else if e < 0 then .error (.exc (.valueError "end is out of bounds"))
    else
      match cScanstring s e.toNat strict with
      | .ok (v, n) => .ok (v, (n : Int))
      | .error err => .error err

/-- `encode_basestring_ascii(pystr)`: the clinic wrapper
(`Modules/clinic/_json.c.h:84-98`), then `py_encode_basestring_ascii_impl`, :683-687. -/
def cPyEncodeBasestringAscii : StrArg → ER
  | .str s => .ok (cAsciiEscape s)
  | .other t => .error (badArgErr "encode_basestring_ascii" "argument" t)

/-- `encode_basestring(pystr)`: the clinic wrapper
(`Modules/clinic/_json.c.h:113-127`), then `py_encode_basestring_impl`, :698-702. -/
def cPyEncodeBasestring : StrArg → ER
  | .str s => .ok (cEscape s)
  | .other t => .error (badArgErr "encode_basestring" "argument" t)

/-! ### The scanner -/

/-- `scanner_call`, :1208-1236: `StopIteration(idx)` when nothing is found. -/
def cScannerCall (cfg : DCfg) (x : StrArg) (idx : Int) : DR (JVal × Int) :=
  if outOfSsize idx then .error (.exc ssizeErr)
  else
    match x with
    | .other t => .error (.exc (firstArgErr t))
    | .str s =>
      if idx < 0 then .error (.exc (.valueError "idx cannot be negative"))
      else
        match cScanOnce cfg s (docFuel s) idx.toNat with
        | .ok (v, e) => .ok (v, (e : Int))
        | .error err => .error err

/-- The object given to `make_scanner`. -/
structure ScanCtx where
  /-- `PyObject_GetAttrString(ctx, name)`: returns, or raises (the `AttributeError` of a missing
  attribute, or whatever a property or `__getattr__` raises). The values read are those of the
  `DCfg`. -/
  getattr : String → Except PyExc Unit
  /-- `PyObject_IsTrue(ctx.strict)`: `strict`'s `__bool__` may raise. -/
  strict : Except PyExc Bool

/-- `'%.100s' object has no attribute '%U'` (`_PyObject_GenericGetAttrWithDict`). -/
def attrErr (t a : String) : PyExc := .named "AttributeError" s!"'{truncName 100 t}' object has no attribute '{a}'"

/-- The attributes after `strict`, in the order of `scanner_new`, :1262-1280. -/
def scannerAttrs : List String :=
  ["object_hook", "object_pairs_hook", "array_hook", "parse_float", "parse_int", "parse_constant"]

/-- `scanner_new`, :1239-1287: `strict` and its truth value first (:1255-1260), then the six
attributes, each lookup's failure ending the call (`goto bail`). -/
def scannerNew (ctx : ScanCtx) (cfg : DCfg) : Except PyExc DCfg :=
  match ctx.getattr "strict" with
  | .error e => .error e
  | .ok () =>
    match ctx.strict with
    | .error e => .error e
    | .ok st =>
      match scannerAttrs.foldlM (fun _ a => ctx.getattr a) () with
      | .error e => .error e
      | .ok () => .ok { cfg with strict := st }

/-! ### The encoder -/

/-- The `markers` argument. -/
inductive MarkersArg where
  | none
  | dict
  | other (t : String)

/-- The `encoder` argument: `fast_encode` is set for the two C functions (:1348-1356),
which are then `write_escaped_ascii` and `write_escaped_unicode`. -/
inductive EncoderArg where
  | cAscii
  | cPlain
  | custom (g : PStr → Except PyExc EncOut)

/-- The first byte of the UTF-8 encoding of `c`. -/
def utf8Lead (c : Char) : Nat :=
  let v := c.toNat
  if v < 0x80 then v else if v < 0x800 then 0xC0 + v / 0x40
  else if v < 0x10000 then 0xE0 + v / 0x1000 else 0xF0 + v / 0x40000

/-- Two lower-case hex digits, as `%02x` prints a byte. -/
def hex2 (b : Nat) : String :=
  let d (k : Nat) : Char := if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
  String.ofList [d (b / 16 % 16), d (b % 16)]

/-- `snprintf("%.Ns")` of a valid UTF-8 string, then a strict decode of the buffer, when the
string ends the buffer and `pre` bytes come before it. `%.Ns` of the C library keeps exactly the
first `n` bytes, so a character the cut splits is left as an incomplete sequence at the end.
`.ok cs`: the characters kept, every one whole. `.error`: `PyUnicode_FromString` refuses the
buffer with `UnicodeDecodeError`, "unexpected end of data" over the `n` bytes of the incomplete
sequence; its `str` names the byte when there is one, the range of positions otherwise
(`UnicodeDecodeError_str`, Objects/exceptions.c:3893-3909). -/
def cCut : Nat → Nat → List Char → Except PyExc (List Char)
  | _, _, [] => .ok []
  | pre, n, c :: cs =>
    if c.utf8Size ≤ n then (c :: ·) <$> cCut (pre + c.utf8Size) (n - c.utf8Size) cs
    else if n = 0 then .ok []
    else if n = 1 then .error (.named "UnicodeDecodeError"
      s!"'utf-8' codec can't decode byte 0x{hex2 (utf8Lead c)} in position {pre}: unexpected end of data")
    else .error (.named "UnicodeDecodeError"
      s!"'utf-8' codec can't decode bytes in position {pre}-{pre + n - 1}: unexpected end of data")

/-- A `U` argument that is not a `str`, refused by `PyArg_ParseTupleAndKeywords`, with `argn`
its position: `convertsimple` calls `converterr("str", arg, ...)` (Python/getargs.c:1300-1307),
which writes `"must be %.50s, not %.50s"` with `PyOS_snprintf` (`:682-684`, `None` for the None
object); `seterror` (`:440-479`, from `vgetargskeywords`, `:1851`) prefixes `"%.200s() argument
%zd "` in another `snprintf` buffer and passes it to `PyErr_SetString` (`:477`), which decodes it
strictly (Python/errors.c:296). The cut is by bytes, so a type name whose 50th byte falls inside
a character leaves an incomplete sequence, and the exception is `UnicodeDecodeError`, not
`TypeError`. -/
def uArgErr (argn : Nat) (t : String) : PyExc :=
  let head := s!"make_encoder() argument {argn} must be str, not "
  match cCut (head.toList.map Char.utf8Size).sum 50 (if t = "NoneType" then "None" else t).toList with
  | .ok cs => .typeError (head ++ String.ofList cs)
  | .error e => e

/-- `encoder_new`, :1311-1359. The `U` conversions run before the `markers` check. -/
def encoderNew (markers : MarkersArg) (dflt : Nat → String → Except PyExc EVal) (dfltDepth : Nat)
    (encoder : EncoderArg) (indent : Option PStr) (keySep itemSep : StrArg)
    (sortKeys skipKeys allowNan : Bool) : Except PyExc ECfg :=
  match keySep with
  | .other t => .error (uArgErr 5 t)
  | .str keySep =>
    match itemSep with
    | .other t => .error (uArgErr 6 t)
    | .str itemSep =>
      match markers with
      | .other t =>
        .error (.typeError s!"make_encoder() argument 1 must be dict or None, not {truncName 200 t}")
      | m =>
        .ok { ensureAscii := (match encoder with
                | .cAscii => true
                | _ => false)
              checkCircular := (match m with
                | .none => false
                | _ => true)
              allowNan, sortKeys, skipKeys, indent, itemSep, keySep, dflt, dfltDepth
              customEnc := (match encoder with
                | .custom g => some g
                | _ => none) }

/-- The indent cache, :1362-1371: `2*k` holds `'\n' + indent * (k + initial)`,
`2*k-1` holds `item_separator` followed by that. -/
abbrev IndentCache := List PStr

/-- `malloc` of this many bytes or more fails (see the module docstring). -/
def mallocLimit : Nat := 2 ^ 47

def memoryError : PyExc := .named "MemoryError" ""

/-- `struct_size` of `PyUnicode_New`: `PyASCIIObject` (40 bytes) or `PyCompactUnicodeObject` (56). -/
def ucsStruct (maxchar : Nat) : Nat := if maxchar < 128 then 40 else 56

/-- `char_size` of `PyUnicode_New`. -/
def ucsWidth (maxchar : Nat) : Nat := if maxchar < 256 then 1 else if maxchar < 65536 then 2 else 4

/-- `PyUnicode_New(size, maxchar)` for `1 <= size` succeeds (Objects/unicodeobject.c:1269-1345):
`struct_size` 40 for ASCII (`PyASCIIObject`), 56 otherwise (`PyCompactUnicodeObject`; 3.15.2,
64-bit, checked with `sys.getsizeof`), the size check of :1325-1326, then
`PyObject_Malloc(struct_size + (size + 1) * char_size)` (:1332). -/
def unicodeNewOk (size maxchar : Nat) : Bool :=
  decide ((size : Int) ≤ (ssizeMax - ucsStruct maxchar) / ucsWidth maxchar - 1) &&
    decide (ucsStruct maxchar + (size + 1) * ucsWidth maxchar < mallocLimit)

/-- The largest code point of a string (`PyUnicode_MAX_CHAR_VALUE` picks the kind from it). -/
def strMax (s : PStr) : Nat := s.foldl max 0

/-- `unicode_repeat(str, len)`, Objects/unicodeobject.c:12560-12612 (the `sq_repeat` that
`PySequence_Repeat`, Objects/abstract.c:1747-1758, calls for a `str`): `''` below 1, the string
itself at 1, `OverflowError` when `len(str) > PY_SSIZE_T_MAX / len`, otherwise
`PyUnicode_New(len * len(str), maxchar)` (the empty singleton for size 0) and the copies. -/
def unicodeRepeat (s : PStr) (len : Int) : Except PyExc PStr :=
  if len < 1 then .ok []
  else if len = 1 then .ok s
  else if (s.length : Int) > ssizeMax / len then .error (.overflowError "repeated string is too long")
  else if len.toNat * s.length = 0 then .ok []
  else if unicodeNewOk (len.toNat * s.length) (strMax s) then .ok (rep s len.toNat)
  else .error memoryError

/-- `PyUnicode_Append(&left, right)` (Objects/unicodeobject.c:11408-11483) for two `str`s: the
empty shortcuts, the `OverflowError` of :11440-11444, then a new string (`'\n'` from
`PyUnicode_FromOrdinal` is a shared singleton, never resized in place). -/
def unicodeAppend (l r : PStr) : Except PyExc PStr :=
  if l = [] then .ok r
  else if r = [] then .ok l
  else if (l.length : Int) > ssizeMax - r.length then .error (.overflowError "strings are too large to concat")
  else if unicodeNewOk (l.length + r.length) (max (strMax l) (strMax r)) then .ok (l ++ r)
  else .error memoryError

/-- `create_indent_cache(s, indent_level)`, :1373-1390: `newline_indent = '\n'`, then, when
`indent_level` is not 0, `PyUnicode_AppendAndDel(&newline_indent, PySequence_Repeat(indent,
indent_level))` (Objects/unicodeobject.c:11485-11489; a `NULL` repeat leaves its exception and
`NULL`, :11420-11424), and the 1-list of the result. -/
def createIndentCache (ind : PStr) (level : Int) : Except PyExc IndentCache :=
  if level ≠ 0 then
    match unicodeRepeat ind level with
    | .error e => .error e
    | .ok r =>
      match unicodeAppend [10] r with
      | .error e => .error e
      | .ok nl => .ok [nl]
  else .ok [[10]]

/-- The number of copies of `indent` in the cache's first entry, which the encoders then shift
every level by (`IndentCacheSpec` ties the strings to it): `PySequence_Repeat` gives `''` below
1, so 0 copies for a negative level as for level 0. -/
def cacheCopies (level : Int) : Nat := if level < 1 then 0 else level.toNat

/-- `update_indent_cache`, :1395-1422. -/
def updateIndentCache (cfg : ECfg) (ind : PStr) (k : Nat) (c : IndentCache) : IndentCache :=
  let nl := c.getD ((k - 1) * 2) [] ++ ind
  c ++ [cfg.itemSep ++ nl, nl]

/-- `get_item_separator`, :1424-1436: the separator, and the cache afterwards. -/
def getItemSeparator (cfg : ECfg) (ind : PStr) (k : Nat) (c : IndentCache) : PStr × IndentCache :=
  let c := if k * 2 > c.length then updateIndentCache cfg ind k c else c
  (c.getD (k * 2 - 1) [], c)

/-- `write_newline_indent`, :1438-1444. -/
def writeNewlineIndent (k : Nat) (c : IndentCache) : PStr := c.getD (k * 2) []

/-- `encoder_call`, :1448-1488: the `n` conversion of the level, `create_indent_cache` when
`indent` is not `None` (its failure is the result, before anything is written), then
`indent_level = 0` with the cache, whose entries are `'\n' + indent * (copies + k)`
(`IndentCacheSpec`); a 1-tuple. -/
def encoderCall (cfg : ECfg) (v : EVal) (level : Int) : Except PyExc (List PStr) :=
  if outOfSsize level then .error ssizeErr
  else
    match (match cfg.indent with
           | none => (Except.ok () : Except PyExc Unit)
           | some ind => (createIndentCache ind level).map (fun _ => ())) with
    | .error e => .error e
    | .ok () =>
      match cEnc cfg (encFuel cfg v) (cacheCopies level) [] v with
      | .ok t => .ok [t]
      | .error e => .error e

theorem createIndentCache_lt1 (ind : PStr) {level : Int} (h : level < 1) :
    createIndentCache ind level = .ok [[10]] := by
  by_cases h0 : level = 0
  · simp [createIndentCache, h0]
  · simp [createIndentCache, h0, unicodeRepeat, h, unicodeAppend]

theorem createIndentCache_ovf (ind : PStr) {level : Int} (h2 : 2 ≤ level)
    (hov : (ind.length : Int) > ssizeMax / level) :
    createIndentCache ind level = .error (.overflowError "repeated string is too long") := by
  have h0 : level ≠ 0 := by omega
  simp [createIndentCache, h0, unicodeRepeat, show ¬ level < 1 by omega, show level ≠ 1 by omega, hov]

end PyLean.JsonMod
