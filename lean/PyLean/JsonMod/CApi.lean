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
`MemoryError` from `PySequence_Repeat(indent, level)` with a huge level is out of
scope too.
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
  /-- Its type name. -/
  tp : String
  /-- The attributes it has. -/
  attrs : List String
  /-- The outcome of `bool(context.strict)`. -/
  strict : Except PyExc Bool

def attrErr (t a : String) : PyExc := .named "AttributeError" s!"'{t}' object has no attribute '{a}'"

/-- The attributes after `strict`, in the order of `scanner_new`, :1262-1280. -/
def scannerAttrs : List String :=
  ["object_hook", "object_pairs_hook", "array_hook", "parse_float", "parse_int", "parse_constant"]

/-- `scanner_new`, :1239-1287, with the attribute values already in `cfg`. -/
def scannerNew (ctx : ScanCtx) (cfg : DCfg) : Except PyExc DCfg :=
  if !ctx.attrs.contains "strict" then .error (attrErr ctx.tp "strict")
  else
    match ctx.strict with
    | .error e => .error e
    | .ok st =>
      match scannerAttrs.find? (fun a => !ctx.attrs.contains a) with
      | some a => .error (attrErr ctx.tp a)
      | none => .ok { cfg with strict := st }

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

/-- `create_indent_cache`, :1372-1390. `PySequence_Repeat` gives `''` for a
negative level. -/
def createIndentCache (ind : PStr) (level : Int) : IndentCache :=
  [[10] ++ (if level ≠ 0 then rep ind level.toNat else [])]

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

/-- `encoder_call`, :1447-1488: a 1-tuple. The level starts the indent cache
(`indent_level = 0` afterwards); a negative one behaves like 0 because the cache
starts from `'\n'`. -/
def encoderCall (cfg : ECfg) (v : EVal) (level : Int) : Except PyExc (List PStr) :=
  if outOfSsize level then .error ssizeErr
  else
    match cEnc cfg (encFuel cfg v) level.toNat [] v with
    | .ok t => .ok [t]
    | .error e => .error e

end PyLean.JsonMod
