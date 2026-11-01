import PyLean.JsonMod.Api

/-!
The Python-callable surface of `Modules/_json.c`: `py_scanstring`,
`py_encode_basestring(_ascii)`, the scanner type (`scanner_new`, `scanner_call`)
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

/-- `%.Ns` of a type name. -/
def truncName (n : Nat) (t : String) : String := String.ofList (t.toList.take n)

/-- A Python object where a `str` is expected. -/
inductive StrArg where
  | str (s : PStr)
  /-- Any other object, by `tp_name`. -/
  | other (t : String)

def firstArgErr (t : String) : PyExc :=
  .typeError s!"first argument must be a string, not {truncName 80 t}"

/-- The `n` conversion, Python/getargs.c: `PyLong_AsSsize_t`. -/
def ssizeErr : PyExc := .overflowError "Python int too large to convert to C ssize_t"

def outOfSsize (i : Int) : Bool := decide (i < ssizeMin) || decide (i > ssizeMax)

/-- `py_scanstring`, Modules/_json.c:559-580, with the check of
`scanstring_unicode` on a negative `end` (:398-400). -/
def cPyScanstring (x : StrArg) (e : Int) (strict : Bool) : DR (PStr × Int) :=
  if outOfSsize e then .error (.exc ssizeErr)
  else
    match x with
    | .other t => .error (.exc (firstArgErr t))
    | .str s =>
      if e < 0 then .error (.exc (.valueError "end is out of bounds"))
      else
        match cScanstring s e.toNat strict with
        | .ok (v, n) => .ok (v, (n : Int))
        | .error err => .error err

/-- `py_encode_basestring_ascii`, :588-604. -/
def cPyEncodeBasestringAscii : StrArg → ER
  | .str s => .ok (cAsciiEscape s)
  | .other t => .error (firstArgErr t)

/-- `py_encode_basestring`, :613-629. -/
def cPyEncodeBasestring : StrArg → ER
  | .str s => .ok (cEscape s)
  | .other t => .error (firstArgErr t)

/-! ### The scanner -/

/-- `scanner_call`, :1127-1156: `StopIteration(idx)` when nothing is found. -/
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

/-- The attributes after `strict`, in the order of `scanner_new`, :1182-1196. -/
def scannerAttrs : List String :=
  ["object_hook", "object_pairs_hook", "parse_float", "parse_int", "parse_constant"]

/-- `scanner_new`, :1158-1203, with the attribute values already in `cfg`. -/
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

/-- The `encoder` argument: `fast_encode` is set for the two C functions (:1264-1269). -/
inductive EncoderArg where
  | cAscii
  | cPlain
  | custom (g : PStr → Except PyExc EncOut)

/-- `encoder_new`, :1226-1272. The `U` conversions run before the `markers` check. -/
def encoderNew (markers : MarkersArg) (dflt : Nat → String → Except PyExc EVal) (dfltDepth : Nat)
    (encoder : EncoderArg) (indent : Option PStr) (keySep itemSep : StrArg)
    (sortKeys skipKeys allowNan : Bool) : Except PyExc ECfg :=
  match keySep with
  | .other t => .error (.typeError s!"make_encoder() argument 5 must be str, not {t}")
  | .str keySep =>
    match itemSep with
    | .other t => .error (.typeError s!"make_encoder() argument 6 must be str, not {t}")
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

/-- The indent cache, :1275-1284: `2*k` holds `'\n' + indent * (k + initial)`,
`2*k-1` holds `item_separator` followed by that. -/
abbrev IndentCache := List PStr

/-- `create_indent_cache`, :1285-1303. `PySequence_Repeat` gives `''` for a
negative level. -/
def createIndentCache (ind : PStr) (level : Int) : IndentCache :=
  [[10] ++ (if level ≠ 0 then rep ind level.toNat else [])]

/-- `update_indent_cache`, :1308-1335. -/
def updateIndentCache (cfg : ECfg) (ind : PStr) (k : Nat) (c : IndentCache) : IndentCache :=
  let nl := c.getD ((k - 1) * 2) [] ++ ind
  c ++ [cfg.itemSep ++ nl, nl]

/-- `get_item_separator`, :1337-1349: the separator, and the cache afterwards. -/
def getItemSeparator (cfg : ECfg) (ind : PStr) (k : Nat) (c : IndentCache) : PStr × IndentCache :=
  let c := if k * 2 > c.length then updateIndentCache cfg ind k c else c
  (c.getD (k * 2 - 1) [], c)

/-- `write_newline_indent`, :1351-1357. -/
def writeNewlineIndent (k : Nat) (c : IndentCache) : PStr := c.getD (k * 2) []

/-- `encoder_call`, :1360-1401: a 1-tuple. The level starts the indent cache
(`indent_level = 0` afterwards); a negative one behaves like 0 because the cache
starts from `'\n'`. -/
def encoderCall (cfg : ECfg) (v : EVal) (level : Int) : Except PyExc (List PStr) :=
  if outOfSsize level then .error ssizeErr
  else
    match cEnc cfg (encFuel cfg v) level.toNat [] v with
    | .ok t => .ok [t]
    | .error e => .error e

end PyLean.JsonMod
