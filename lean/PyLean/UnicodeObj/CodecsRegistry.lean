import PyLean.UnicodeObj.CodecsErr

/-!
The codec registry of `Python/codecs.c` (CPython 3.15.2) and the `_codecs` functions of
`Modules/_codecsmodule.c` that reach it.

Search functions, encoders, decoders and the attributes of codec objects are Python code. The
model takes them as a `World`: what each call returns, and the registry operations it performs on
its way (a search function can register or unregister search functions while the registry is
scanning the list). Objects are values with an identity (`id`); the `id` is what `is` compares.

A failed allocation (`MemoryError`) is not modelled.
-/

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-- A Python value as these functions see it. `tuple` covers `tuple` and its subclasses
(`CodecInfo`); `exact` is `PyTuple_CheckExact`. -/
inductive Val where
  | none
  | str (s : Str)
  | bytes (b : Bytes)
  | bytearray (b : Bytes)
  | int (n : Int)
  | tuple (id : Nat) (items : List Val) (exact : Bool)
  | obj (id : Nat) (tp : String)
  deriving Repr, Inhabited

/-- `a is b`: the same object. `None` is a singleton; a `str`, `bytes` or `int` value here is a
fresh object, never identical to another. -/
def Val.is : Val → Val → Bool
  | .none, .none => true
  | .tuple i _ _, .tuple j _ _ => i == j
  | .obj i _, .obj j _ => i == j
  | _, _ => false

/-- `Py_TYPE(v)->tp_name`. -/
def Val.tpName : Val → String
  | .none => "NoneType"
  | .str _ => "str"
  | .bytes _ => "bytes"
  | .bytearray _ => "bytearray"
  | .int _ => "int"
  | .tuple _ _ true => "tuple"
  | .tuple _ _ false => "CodecInfo"
  | .obj _ tp => tp

/-- A registry operation a call performs before it returns. -/
inductive Op where
  | register (f : Val)
  | unregister (f : Val)
  deriving Repr

/-- The Python side. -/
structure World where
  /-- Calling `f` with positional arguments: the operations it performs, then its result. -/
  call : Val → List Val → List Op × Py Val
  /-- `PyObject_GetOptionalAttr(v, name)` / `PyObject_GetAttrString`: `none` when absent. -/
  getattr : Val → String → Py (Option Val)
  /-- `PyObject_IsTrue`. -/
  truth : Val → Py Bool
  /-- `PyCallable_Check`. -/
  callable : Val → Bool

/-- `interp->codecs`: the search path, the search cache, the error registry. -/
structure Reg where
  path : List Val
  cache : List (Str × Val)
  errors : List (String × Val)
  deriving Repr

/-- `PyDict_SetItem` on a dict keyed by `str`. -/
def dictSet {α : Type} (d : List (α × Val)) [BEq α] (k : α) (v : Val) : List (α × Val) :=
  if d.any (·.1 == k) then d.map (fun e => if e.1 == k then (k, v) else e) else d ++ [(k, v)]

/-- `PyErr_SetString(PyExc_LookupError, ...)`. -/
def lookupErr (msg : String) : PyExc := .named "LookupError" msg

/-! ## Search functions, codecs.c:32-82 -/

/-- `PyCodec_Register`, codecs.c:32-52. -/
def register (W : World) (st : Reg) (f : Val) : Reg × Py Unit :=
  if !W.callable f then (st, .error (.typeError "argument must be callable"))
  else ({ st with path := st.path ++ [f] }, .ok ())

/-- The loop of `PyCodec_Unregister`, codecs.c:67-79: removes the first item that `is` the
function, from index `i` on. -/
def removeFirst (f : Val) : List Val → Option (List Val)
  | [] => none
  | x :: xs => if x.is f then some xs else (removeFirst f xs).map (x :: ·)

/-- `PyCodec_Unregister`, codecs.c:54-82: the first registration is removed and the cache
cleared; an unknown function is ignored. -/
def unregister (st : Reg) (f : Val) : Reg :=
  match removeFirst f st.path with
  | some p => { st with path := p, cache := [] }
  | none => st

/-- A call's registry operations, run in order: `codecs.register` and `codecs.unregister`
from inside Python code. -/
def runOps (W : World) : Reg → List Op → Reg
  | st, [] => st
  | st, .register f :: ops => runOps W (register W st f).1 ops
  | st, .unregister f :: ops => runOps W (unregister st f) ops

/-! ## Lookup, codecs.c:84-235 -/

/-- `normalizestring`, codecs.c:87-115, on the UTF-8 bytes of the name: a space becomes `-`,
an ASCII letter its lower case (`Py_TOLOWER` leaves bytes from 128 on alone), then
`PyUnicode_FromString`. -/
def normalizestring (enc : List Nat) : Py Str :=
  if enc.length > ssizeMaxN then .error (.overflowError "string is too large")
  else (utf8Decode (enc.map fun ch => if ch = 32 then 45 else cLower ch) .strict)

/-- The search loop of `_PyCodec_Lookup`, codecs.c:175-203, from index `i` of a list whose
length was `len` when the scan began. `PyList_GetItemRef` checks the index against the list as
it is now (listobject.c, "list index out of range"). -/
def searchLoop (W : World) (v : Str) (encoding : String) (len : Nat) :
    Nat → Nat → Reg → Reg × Py Val
  | 0, _, st => (st, .error .modelFuel)
  | fuel + 1, i, st =>
    if i ≥ len then (st, .error (lookupErr s!"unknown encoding: {encoding}"))
    else
      match st.path[i]? with
      | none => (st, .error (.indexError "list index out of range"))
      | some func =>
        let (ops, r) := W.call func [.str v]
        let st := runOps W st ops
        match r with
        | .error e => (st, .error e)
        | .ok .none => searchLoop W v encoding len fuel (i + 1) st
        | .ok res =>
          match res with
          | .tuple _ items _ =>
            if items.length = 4 then (st, .ok res)
            else (st, .error (.typeError "codec search functions must return 4-tuples"))
          | _ => (st, .error (.typeError "codec search functions must return 4-tuples"))

/-- `_PyCodec_Lookup`, codecs.c:133-218, for the C string `enc` (UTF-8 bytes, no NUL). -/
def pyCodecLookup (W : World) (st : Reg) (enc : List Nat) : Reg × Py Val :=
  match normalizestring enc with
  | .error e => (st, .error e)
  | .ok v =>
    match st.cache.lookup v with
    | some r => (st, .ok r)
    | none =>
      let len := st.path.length
      if len = 0 then
        (st, .error (lookupErr "no codec search functions registered: can't find encoding"))
      else
        let encoding := toLeanString ((utf8Decode enc .strict).toOption.getD [])
        match searchLoop W v encoding len (len + 1) 0 st with
        | (st', .ok res) => ({ st' with cache := dictSet st'.cache v res }, .ok res)
        | r => r

/-- `PyCodec_KnownEncoding`, codecs.c:222-235: the error is cleared. -/
def knownEncoding (W : World) (st : Reg) (enc : List Nat) : Reg × Bool :=
  match pyCodecLookup W st enc with
  | (st', .ok _) => (st', true)
  | (st', .error _) => (st', false)

/-! ## Getting at a codec, codecs.c:237-391 -/

/-- `args_tuple`, codecs.c:237-258: `(object,)` or `(object, errors)`. -/
def argsTuple (obj : Val) (errors : Option Str) : List Val :=
  match errors with
  | none => [obj]
  | some e => [obj, .str e]

/-- `PyTuple_GET_ITEM` of a lookup result, which is a tuple of four items. -/
def tupleItem (v : Val) (index : Nat) : Val :=
  match v with
  | .tuple _ items _ => items.getD index .none
  | _ => .none

/-- `codec_getitem`, codecs.c:262-274. -/
def codecGetitem (W : World) (st : Reg) (enc : List Nat) (index : Nat) : Reg × Py Val :=
  match pyCodecLookup W st enc with
  | (st', .ok codecs) => (st', .ok (tupleItem codecs index))
  | (st', .error e) => (st', .error e)

/-- The `AttributeError` of `PyObject_GetAttrString` on a missing attribute. -/
def attrErr (v : Val) (name : String) : PyExc :=
  .named "AttributeError" s!"~'{v.tpName}' object has no attribute '{name}'"

/-- Calling a value: the operations its code performs, then its result. -/
def callVal (W : World) (st : Reg) (f : Val) (args : List Val) : Reg × Py Val :=
  let (ops, r) := W.call f args
  (runOps W st ops, r)

/-- `codec_makeincrementalcodec`, codecs.c:277-293. -/
def makeIncremental (W : World) (st : Reg) (info : Val) (errors : Option Str) (attr : String) :
    Reg × Py Val :=
  match W.getattr info attr with
  | .error e => (st, .error e)
  | .ok none => (st, .error (attrErr info attr))
  | .ok (some inc) =>
    match errors with
    | some e => callVal W st inc [.str e]
    | none => callVal W st inc []

/-- `codec_getincrementalcodec`, codecs.c:295-308. -/
def getIncremental (W : World) (st : Reg) (enc : List Nat) (errors : Option Str) (attr : String) :
    Reg × Py Val :=
  match pyCodecLookup W st enc with
  | (st', .error e) => (st', .error e)
  | (st', .ok info) => makeIncremental W st' info errors attr

/-- `codec_getstreamcodec`, codecs.c:312-331. -/
def getStream (W : World) (st : Reg) (enc : List Nat) (stream : Val) (errors : Option Str)
    (index : Nat) : Reg × Py Val :=
  match pyCodecLookup W st enc with
  | (st', .error e) => (st', .error e)
  | (st', .ok codecs) =>
    let cls := tupleItem codecs index
    match errors with
    | some e => callVal W st' cls [stream, .str e]
    | none => callVal W st' cls [stream]

/-- `PyCodec_Encoder`, `PyCodec_Decoder`, codecs.c:357-365. -/
def pyCodecEncoder (W : World) (st : Reg) (enc : List Nat) := codecGetitem W st enc 0
def pyCodecDecoder (W : World) (st : Reg) (enc : List Nat) := codecGetitem W st enc 1
/-- `PyCodec_IncrementalEncoder`, `PyCodec_IncrementalDecoder`, codecs.c:367-377. -/
def pyCodecIncEncoder (W : World) (st : Reg) (enc : List Nat) (errors : Option Str) :=
  getIncremental W st enc errors "incrementalencoder"
def pyCodecIncDecoder (W : World) (st : Reg) (enc : List Nat) (errors : Option Str) :=
  getIncremental W st enc errors "incrementaldecoder"
/-- `PyCodec_StreamReader`, `PyCodec_StreamWriter`, codecs.c:379-391. -/
def pyCodecStreamReader (W : World) (st : Reg) (enc : List Nat) (stream : Val) (errors : Option Str) :=
  getStream W st enc stream errors 2
def pyCodecStreamWriter (W : World) (st : Reg) (enc : List Nat) (stream : Val) (errors : Option Str) :=
  getStream W st enc stream errors 3

/-! ## Encoding and decoding, codecs.c:393-609 -/

/-- An exception with `_PyErr_FormatNote` applied: its notes, last added last. The message of
the exception itself is what the callee raised. -/
structure NErr where
  exc : PyExc
  notes : List String
  deriving Repr, DecidableEq

abbrev NPy (α : Type) := Except NErr α

def plain {α : Type} : Py α → NPy α
  | .ok v => .ok v
  | .error e => .error ⟨e, []⟩

/-- `_PyCodec_EncodeInternal` and `_PyCodec_DecodeInternal`, codecs.c:398-480: call the coder
with `args_tuple`, note the failure, check for a 2-tuple, return its first item. `what` is
"encoding" or "decoding"; the `TypeError`s differ by one space. -/
def codecInternal (W : World) (st : Reg) (obj coder : Val) (encoding : String) (errors : Option Str)
    (what : String) (tupleMsg : String) : Reg × NPy Val :=
  let (st', r) := callVal W st coder (argsTuple obj errors)
  match r with
  | .error e => (st', .error ⟨e, [s!"{what} with '{encoding}' codec failed"]⟩)
  | .ok res =>
    match res with
    | .tuple _ items _ =>
      if items.length = 2 then (st', .ok (items.getD 0 .none))
      else (st', .error ⟨.typeError tupleMsg, []⟩)
    | _ => (st', .error ⟨.typeError tupleMsg, []⟩)

def encodeInternal (W : World) (st : Reg) (obj encoder : Val) (encoding : String) (errors : Option Str) :=
  codecInternal W st obj encoder encoding errors "encoding" "encoder must return a tuple (object, integer)"

def decodeInternal (W : World) (st : Reg) (obj decoder : Val) (encoding : String) (errors : Option Str) :=
  codecInternal W st obj decoder encoding errors "decoding" "decoder must return a tuple (object,integer)"

/-- The C string as `%s` prints it. -/
def cstr (enc : List Nat) : String := toLeanString ((utf8Decode enc .strict).toOption.getD [])

/-- `PyCodec_Encode`, codecs.c:483-494. -/
def pyCodecEncode (W : World) (st : Reg) (obj : Val) (enc : List Nat) (errors : Option Str) :
    Reg × NPy Val :=
  match pyCodecEncoder W st enc with
  | (st', .error e) => (st', .error ⟨e, []⟩)
  | (st', .ok encoder) => encodeInternal W st' obj encoder (cstr enc) errors

/-- `PyCodec_Decode`, codecs.c:496-507. -/
def pyCodecDecode (W : World) (st : Reg) (obj : Val) (enc : List Nat) (errors : Option Str) :
    Reg × NPy Val :=
  match pyCodecDecoder W st enc with
  | (st', .error e) => (st', .error ⟨e, []⟩)
  | (st', .ok decoder) => decodeInternal W st' obj decoder (cstr enc) errors

/-- `%.400s`: at most 400 bytes, without a trailing incomplete character
(`unicode_fromformat_write_utf8`, unicodeobject.c:2623-2661). -/
def trunc400 (s : Str) : Str :=
  let rec go : Nat → Str → Str
    | _, [] => []
    | room, c :: cs =>
      let n := (utf8EncodeChar c).length
      if n ≤ room then c :: go (room - n) cs else []
  go 400 s

/-- The test of `_PyCodec_LookupTextEncoding`, codecs.c:521-551: a plain tuple passes ("assume
any raw tuple describes a text encoding"), and so does anything without `_is_text_encoding`;
otherwise `PyObject_IsTrue` of that attribute decides, and its errors propagate. -/
def isTextCodec (W : World) (codec : Val) : Py Bool :=
  match codec with
  | .tuple _ _ true => .ok true
  | _ =>
    match W.getattr codec "_is_text_encoding" with
    | .error e => .error e
    | .ok none => .ok true
    | .ok (some attr) => W.truth attr

/-- `_PyCodec_LookupTextEncoding`, codecs.c:510-555. -/
def lookupTextEncoding (W : World) (st : Reg) (enc : List Nat) (alternate : Option String) :
    Reg × Py Val :=
  match pyCodecLookup W st enc with
  | (st', .error e) => (st', .error e)
  | (st', .ok codec) =>
    match isTextCodec W codec with
    | .error e => (st', .error e)
    | .ok true => (st', .ok codec)
    | .ok false =>
      let name := toLeanString (trunc400 ((utf8Decode enc .strict).toOption.getD []))
      match alternate with
      | some cmd => (st', .error (lookupErr
          s!"'{name}' is not a text encoding; use {cmd} to handle arbitrary codecs"))
      | none => (st', .error (lookupErr s!"'{name}' is not a text encoding"))

/-- `codec_getitem_checked`, codecs.c:558-573. -/
def getitemChecked (W : World) (st : Reg) (enc : List Nat) (alternate : String) (index : Nat) :
    Reg × Py Val :=
  match lookupTextEncoding W st enc (some alternate) with
  | (st', .error e) => (st', .error e)
  | (st', .ok codec) => (st', .ok (tupleItem codec index))

/-- `_PyCodec_EncodeText`, codecs.c:575-596. -/
def encodeText (W : World) (st : Reg) (obj : Val) (enc : List Nat) (errors : Option Str) :
    Reg × NPy Val :=
  match getitemChecked W st enc "codecs.encode()" 0 with
  | (st', .error e) => (st', .error ⟨e, []⟩)
  | (st', .ok encoder) => encodeInternal W st' obj encoder (cstr enc) errors

/-- `_PyCodec_DecodeText`, codecs.c:580-609. -/
def decodeText (W : World) (st : Reg) (obj : Val) (enc : List Nat) (errors : Option Str) :
    Reg × NPy Val :=
  match getitemChecked W st enc "codecs.decode()" 1 with
  | (st', .error e) => (st', .error ⟨e, []⟩)
  | (st', .ok decoder) => decodeInternal W st' obj decoder (cstr enc) errors

/-! ## The error registry, codecs.c:611-662 -/

def builtinNames : List String :=
  ["strict", "ignore", "replace", "xmlcharrefreplace", "backslashreplace", "namereplace",
   "surrogatepass", "surrogateescape"]

/-- `PyCodec_RegisterError`, codecs.c:617-627. -/
def registerError (W : World) (st : Reg) (name : String) (h : Val) : Reg × Py Unit :=
  if !W.callable h then (st, .error (.typeError "handler must be callable"))
  else ({ st with errors := dictSet st.errors name h }, .ok ())

/-- `_PyCodec_UnregisterError`, codecs.c:629-641: `PyDict_PopString` gives 1 when it removed
something, 0 when the name was absent. -/
def unregisterError (st : Reg) (name : String) : Reg × Py Bool :=
  if builtinNames.contains name then
    (st, .error (.valueError s!"cannot un-register built-in error handler '{name}'"))
  else if st.errors.any (·.1 == name) then
    ({ st with errors := st.errors.filter (·.1 != name) }, .ok true)
  else (st, .ok false)

/-- `PyCodec_LookupError`, codecs.c:646-662. -/
def lookupError (st : Reg) (name : Option String) : Py Val :=
  let name := name.getD "strict"
  match st.errors.lookup name with
  | some h => .ok h
  | none => .error (lookupErr s!"unknown error handler name '{toLeanString (trunc400 (lit name))}'")

end PyLean.UnicodeObj.Codecs
