import PyLean.Registry
import PyLean.UnicodeObj.CodecsErrNames
import PyLean.UnicodeObj.CodecsRegProps2

/-! Registry entries for `Python/codecs.c` and `Modules/_codecsmodule.c`. -/

namespace PyLean.UnicodeObj

open PyLean.Registry PyLean.UnicodeObj.Codecs

/-- The bodies of the replacing and surrogate handlers and their dispatchers. -/
def handlerBodies : List String :=
  ["_PyCodec_IgnoreError", "PyCodec_IgnoreErrors",
   "_PyCodec_ReplaceUnicodeEncodeError", "_PyCodec_ReplaceUnicodeDecodeError",
   "_PyCodec_ReplaceUnicodeTranslateError", "PyCodec_ReplaceErrors",
   "PyCodec_XMLCharRefReplaceErrors", "_PyCodec_BackslashReplaceUnicodeEncodeError",
   "_PyCodec_BackslashReplaceUnicodeDecodeError", "_PyCodec_BackslashReplaceUnicodeTranslateError",
   "PyCodec_BackslashReplaceErrors", "PyCodec_NameReplaceErrors",
   "_PyCodec_SurrogatePassUnicodeEncodeError", "_PyCodec_SurrogatePassUnicodeDecodeError",
   "PyCodec_SurrogatePassErrors", "_PyCodec_SurrogateEscapeUnicodeEncodeError",
   "_PyCodec_SurrogateEscapeUnicodeDecodeError", "PyCodec_SurrogateEscapeErrors"]

/-- The registered functions, codecs.c:1508-1561. -/
def handlerWrappers : List String :=
  ["strict_errors", "ignore_errors", "replace_errors", "xmlcharrefreplace_errors",
   "backslashreplace_errors", "namereplace_errors", "surrogatepass_errors", "surrogateescape_errors"]

/-- What the replacements are written with. -/
def handlerWriters : List String :=
  ["codec_handler_write_unicode_hex", "n_decimal_digits_for_codepoint",
   "codec_handler_unicode_replacement_character"]

/-- The accessors of Objects/exceptions.c the handlers go through. -/
def handlerAccessors : List String :=
  ["_PyUnicodeError_GetParams", "PyUnicodeDecodeError_GetEnd", "PyUnicodeEncodeError_GetEncoding",
   "PyUnicodeDecodeError_GetEncoding"]

def codecsEntries : List Entry := [
  { id := "unicodeobj-codecs-handlers-agree", pyFile := "Python/codecs.c"
    pyFns := ["PyCodec_StrictErrors", "wrong_exception_type"] ++ handlerBodies ++ handlerWrappers ++
      handlerWriters ++ handlerAccessors
    statement := "Each of the eight standard error handlers, called directly on an exception object of an ordinary class below UnicodeEncodeError (UnicodeDecodeError, UnicodeTranslateError) with any start and end, gives what the codec-loop model of the same handler gives for start clipped to [0, max(0, len-1)] and end clipped to [min(1, len), len], cut only by the guards against a replacement longer than PY_SSIZE_T_MAX."
    source := "invariant: a handler called by a codec and the same handler called directly are one function; codecs.rst error handler table"
    status := .proven, prop := ``HandlersAgree, thm := some ``handlersAgree_proven
    notes := "The codec-loop model (CodecHandlers.lean) is difftested through real encode and decode calls; this one through codecs.lookup_error(name)(exc) with mutated attributes (codecs_handler). The class test is PyObject_TypeCheck on tp_mro and the exception flag is a separate oracle; HierOk asks only that builtin classes keep their MROs and flag and that no MRO lists two of the three layouts (mro_check), so the MRO need not be transitive. Scope limit (Ordinary): the class's MRO keeps UnicodeError and it has the flag, which only a custom mro() breaks; unicodeobj-codecs-odd-classes says what happens then. builtinHier_ok shows HierOk is satisfiable. The encoding name only reaches surrogatepass, whose code is a hypothesis here." },
  { id := "unicodeobj-codecs-handlers-safe", pyFile := "Python/codecs.c"
    pyFns := ["PyCodec_StrictErrors", "wrong_exception_type"] ++ handlerBodies ++ handlerWrappers ++
      handlerAccessors
    statement := "For every object handed to a standard handler, whatever its class and attributes, provided an encode or decode error has the exception flag, the handler raises only its argument (and only when its class has the flag), a TypeError, the failure to load unicodedata's C API, or the UTF-8 encoder's error on the encoding attribute; a position it returns lies in [0, len(object)] and past the clipped start whenever the clipped range is not empty."
    source := "invariant: no internal error, results in range, codec loops make progress"
    status := .proven, prop := ``HandlersSafe, thm := some ``handlersSafe_proven
    notes := "namereplace needs names under 256 bytes (NAME_MAXLEN, the buffer of codecs.c:1091) for the progress half. Scope limit (FlagOk): without the flag, the surrogate handlers' re-raise is a SystemError; see unicodeobj-codecs-handlers-safe-all." },
  { id := "unicodeobj-codecs-handlers-safe-all", pyFile := "Python/codecs.c"
    pyFns := ["_PyCodec_SurrogateEscapeUnicodeEncodeError", "PyCodec_SurrogateEscapeErrors", "surrogateescape_errors"]
    statement := "The same for every class: no handler leaks an internal error even when the class is below UnicodeEncodeError by MRO but lacks the exception flag."
    source := "invariant: no internal error"
    status := .refuted, prop := ``HandlersSafeAll, thm := some ``handlersSafeAll_refuted
    bug := some "unicodeobj-codecs-surrogate-handlers-systemerror"
    notes := "A subclass of a class whose metaclass mro() is [cls, UnicodeEncodeError, object] has no Py_TPFLAGS_BASE_EXC_SUBCLASS; PyErr_SetObject(PyExceptionInstance_Class(exc), exc) then raises SystemError (oddExc_systemError)." },
  { id := "unicodeobj-codecs-odd-classes", pyFile := "Python/codecs.c"
    pyFns := ["PyCodec_StrictErrors", "strict_errors", "_PyCodec_SurrogatePassUnicodeEncodeError",
      "_PyCodec_SurrogatePassUnicodeDecodeError", "PyCodec_SurrogatePassErrors", "surrogatepass_errors",
      "_PyCodec_ReplaceUnicodeDecodeError", "PyCodec_ReplaceErrors", "replace_errors",
      "PyUnicodeDecodeError_GetEnd", "PyUnicodeEncodeError_GetEncoding", "PyUnicodeDecodeError_GetEncoding"]
    statement := "On a class below UnicodeEncodeError or UnicodeDecodeError whose MRO leaves out UnicodeError, surrogatepass (and replace on a decode error) raise 'expecting a UnicodeEncodeError object, got X' (UnicodeDecodeError); on a class without the exception flag strict raises 'codec must pass exception instance', whatever its MRO."
    source := "invariant: what the C does on classes with a custom mro(); smoke-tested on 3.15.2"
    status := .proven, prop := ``OddClasses, thm := some ``oddClasses_proven },
  { id := "unicodeobj-codecs-handlers-total", pyFile := "Python/codecs.c"
    pyFns := ["wrong_exception_type", "_PyCodec_IgnoreError", "PyCodec_IgnoreErrors",
      "_PyCodec_ReplaceUnicodeEncodeError", "_PyCodec_ReplaceUnicodeDecodeError",
      "_PyCodec_ReplaceUnicodeTranslateError", "PyCodec_ReplaceErrors", "PyCodec_XMLCharRefReplaceErrors",
      "_PyCodec_BackslashReplaceUnicodeEncodeError", "_PyCodec_BackslashReplaceUnicodeDecodeError",
      "_PyCodec_BackslashReplaceUnicodeTranslateError", "PyCodec_BackslashReplaceErrors",
      "PyCodec_NameReplaceErrors", "PyCodec_SurrogatePassErrors", "PyCodec_SurrogateEscapeErrors",
      "ignore_errors", "replace_errors", "xmlcharrefreplace_errors", "backslashreplace_errors",
      "namereplace_errors", "surrogatepass_errors", "surrogateescape_errors",
      "_PyUnicodeError_GetParams", "PyUnicodeDecodeError_GetEnd"]
    statement := "ignore, replace, backslashreplace, xmlcharrefreplace and namereplace succeed exactly when the class is one they take, the object attribute has the type that class needs, (namereplace) unicodedata loads, and (replace on a decode error) the class's MRO has UnicodeError; on a class it does not take, every handler but strict raises wrong_exception_type's TypeError."
    source := "codecs.rst: the handlers replace; register_error: a handler must raise or return a replacement"
    status := .proven, prop := ``HandlersTotal, thm := some ``handlersTotal_proven },
  { id := "unicodeobj-codecs-buffers-exact", pyFile := "Python/codecs.c"
    pyFns := handlerBodies ++ handlerWriters ++ ["codec_handler_unicode_hex_width"]
    statement := "Every handler body writes exactly as many characters (bytes) as its size loop allocated, for every exception object; the decode body of surrogateescape writes at most the four slots of its stack array."
    source := "invariant: no write past the allocation; the asserts of codecs.c:770, :837, :955, :1003, :1036, :1132"
    status := .proven, prop := ``BuffersExact, thm := some ``buffersExact_proven },
  { id := "unicodeobj-codecs-surrogateescape-handlers-round-trip", pyFile := "Python/codecs.c"
    pyFns := ["_PyCodec_SurrogateEscapeUnicodeEncodeError", "_PyCodec_SurrogateEscapeUnicodeDecodeError",
      "PyCodec_SurrogateEscapeErrors", "surrogateescape_errors", "_PyUnicodeError_GetParams"]
    statement := "Whatever surrogateescape returns for a decode error with any bytes, start and end, handing that string to it again as the object of an encode error covering it gives back exactly the bytes it replaced."
    source := "PEP 383; codecs.rst: the surrogate will be turned back into the same byte when surrogateescape is used when encoding"
    status := .proven, prop := ``SurrogateEscapeHandlersRoundTrip,
    thm := some ``surrogateEscapeHandlersRoundTrip_proven },
  { id := "unicodeobj-codecs-surrogatepass-handlers-round-trip", pyFile := "Python/codecs.c"
    pyFns := ["_PyCodec_SurrogatePassUnicodeEncodeError", "_PyCodec_SurrogatePassUnicodeDecodeError",
      "PyCodec_SurrogatePassErrors", "surrogatepass_errors", "_PyUnicodeError_GetParams",
      "PyUnicodeEncodeError_GetEncoding", "PyUnicodeDecodeError_GetEncoding"]
    statement := "For every encoding name and every lone surrogate, the bytes surrogatepass writes for it, placed at start of the object of a decode error naming the same encoding (anything before and after), decode back to that surrogate, in each of utf-8, utf-16-le/be and utf-32-le/be."
    notes := "Scope limit: the decode error's MRO keeps UnicodeError (else PyUnicodeDecodeError_GetEncoding refuses it, unicodeobj-codecs-odd-classes)."
    source := "codecs.rst: surrogatepass allows encoding and decoding surrogate code points as normal code points for the utf-8/16/32 codecs"
    status := .proven, prop := ``SurrogatePassHandlersRoundTrip,
    thm := some ``surrogatePassHandlersRoundTrip_proven },
  { id := "unicodeobj-codecs-backslashreplace-unicode-escape", pyFile := "Python/codecs.c"
    pyFns := ["_PyCodec_BackslashReplaceUnicodeEncodeError", "_PyCodec_BackslashReplaceUnicodeDecodeError",
      "_PyCodec_BackslashReplaceUnicodeTranslateError", "PyCodec_BackslashReplaceErrors",
      "backslashreplace_errors", "codec_handler_write_unicode_hex", "_PyUnicodeError_GetParams"]
    statement := "For every encode or translate error with a str object and any start and end, decoding backslashreplace's replacement with unicode_escape gives back the characters it replaced; for every decode error it gives the code points of the bytes it replaced."
    source := "codecs.rst: backslashreplace uses \\xhh, \\uxxxx, \\Uxxxxxxxx on encoding and \\xhh on decoding"
    status := .proven, prop := ``BackslashReplaceUnicodeEscape,
    thm := some ``backslashReplaceUnicodeEscape_proven },
  { id := "unicodeobj-codecs-namereplace-names", pyFile := "Python/codecs.c"
    pyFns := ["PyCodec_NameReplaceErrors", "namereplace_errors"]
    statement := "namereplace writes \\N{name} exactly for the characters unicodedata.name names, and the backslashreplace escape for the others."
    source := "codecs.rst: what appears in the braces is the Name property from Unicode Character Database"
    status := .refuted, prop := ``NameReplaceWritesNames, thm := some ``nameReplaceWritesNames_refuted
    bug := some "unicodeobj-codecs-namereplace-pua-names"
    notes := "getname is called with with_alias_and_seq = 1, so the 942 Plane 15 private-use slots that hold aliases and named sequences get names: U+F0000 becomes \\N{NULL}." },
  { id := "unicodeobj-codecs-lookup-doc", pyFile := "Python/codecs.c"
    pyFns := ["_PyCodec_Lookup"]
    statement := "For every registry and name: a cached name is answered from the cache without calling anything; on a cache miss, with search functions that leave the registry alone, the answer is the first search function's that is not None (a 4-tuple, else TypeError), stored in the cache, and LookupError naming the encoding as given when none answers; after any successful lookup, every name with the same normalization (ASCII lower case, spaces to hyphens) is answered from the cache with the same object."
    source := "codecs.rst, lookup: normalization, cache, scan, LookupError, stored in the cache"
    status := .proven, prop := ``LookupDoc, thm := some ``lookupDoc_proven
    notes := "Search functions that register or unregister during the scan are the subject of unicodeobj-codecs-lookup-raises; the cache part holds for every world. What normalization does is unicodeobj-codecs-normalizestring." },
  { id := "unicodeobj-codecs-normalizestring", pyFile := "Python/codecs.c"
    pyFns := ["normalizestring"]
    statement := "For the C string of every name without a lone surrogate, normalizestring raises OverflowError past PY_SSIZE_T_MAX bytes and otherwise gives the name with every ASCII capital lower-cased and every space turned into '-', all other characters (non-ASCII included) unchanged."
    source := "codecs.rst, lookup: all ASCII letters are converted to lower case, spaces are replaced with hyphens"
    status := .proven, prop := ``NormalizeStringSpec, thm := some ``normalizeStringSpec_proven },
  { id := "unicodeobj-codecs-lookup-raises", pyFile := "Python/codecs.c"
    pyFns := ["_PyCodec_Lookup"]
    statement := "For every registry, name and search functions, including ones that change the registry during the scan, a failed lookup raises a LookupError (the builtin LookupError or its builtin subclass IndexError), the TypeError for a bad answer, or what a search function raised."
    source := "codecs.rst, lookup: If no CodecInfo object is found, a LookupError is raised"
    status := .proven, prop := ``LookupRaisesLookupError, thm := some ``lookupRaisesLookupError_proven
    notes := "When a search function unregisters search functions, the length saved at codecs.c:165 outlives the list and PyList_GetItemRef raises IndexError (unregWorld_lookup); IndexError is a LookupError, so the documentation holds, with an odd message." },
  { id := "unicodeobj-codecs-encode-decode-paths", pyFile := "Python/codecs.c"
    pyFns := ["args_tuple", "codec_getitem", "PyCodec_Encoder", "PyCodec_Decoder", "_PyCodec_EncodeInternal",
      "_PyCodec_DecodeInternal", "PyCodec_Encode", "PyCodec_Decode", "_PyCodec_LookupTextEncoding",
      "codec_getitem_checked", "_PyCodec_TextEncoder", "_PyCodec_TextDecoder", "_PyCodec_EncodeText",
      "_PyCodec_DecodeText"]
    statement := "codecs.encode/decode call the codec's first/second item with (obj,), or (obj, errors) when errors is given, and return the first item of the 2-tuple it answers, a TypeError for any other answer, the coder's exception with the note \"encoding with '<name>' codec failed\"; the text paths (str.encode, bytes.decode) do exactly the same for a plain tuple, for a codec without _is_text_encoding and for one whose _is_text_encoding is true; they raise the LookupError that points to codecs.encode()/decode() when it is false, and the error of reading it or of PyObject_IsTrue on it."
    source := "codecs.rst: Codec.encode/decode return (output object, length consumed); invariant: the generic and text paths agree on text encodings"
    status := .proven, prop := ``CodecPaths, thm := some ``codecPaths_proven },
  { id := "unicodeobj-codecs-register-doc", pyFile := "Python/codecs.c"
    pyFns := ["PyCodec_Register", "PyCodec_Unregister", "_codecs_register", "_codecs_unregister"]
    statement := "codecs.register refuses a non-callable and otherwise appends to the search path, leaving the cache; codecs.unregister removes the first registration of that very object and clears the cache, or changes nothing when it is not registered; both return None."
    source := "_codecs.register and _codecs.unregister docstrings"
    status := .proven, prop := ``RegisterDoc, thm := some ``registerDoc_proven },
  { id := "unicodeobj-codecs-error-registry", pyFile := "Python/codecs.c"
    pyFns := ["PyCodec_RegisterError", "_PyCodec_UnregisterError", "PyCodec_LookupError",
      "_codecs_register_error_impl", "_codecs__unregister_error_impl", "_codecs_lookup_error_impl"]
    statement := "register_error refuses a non-callable and otherwise makes lookup_error(name) return the handler, builtin names included; lookup_error of an unknown name raises LookupError naming it (cut to 400 bytes) and NULL means strict; _unregister_error refuses the eight builtin names and otherwise answers whether a custom handler was registered, which lookup_error then no longer finds."
    source := "codecs.rst, register_error and lookup_error; _codecs._unregister_error docstring"
    status := .proven, prop := ``ErrorRegistryDoc, thm := some ``errorRegistryDoc_proven },
  { id := "unicodeobj-codecs-capi-matches-lib", pyFile := "Lib/codecs.py"
    pyFns := ["getencoder", "getdecoder", "getincrementalencoder", "getincrementaldecoder", "getreader",
      "getwriter", "PyCodec_KnownEncoding", "codec_getitem", "PyCodec_Encoder", "PyCodec_Decoder",
      "codec_makeincrementalcodec", "codec_getincrementalcodec", "PyCodec_IncrementalEncoder",
      "PyCodec_IncrementalDecoder", "codec_getstreamcodec", "PyCodec_StreamReader", "PyCodec_StreamWriter",
      "_codecs_lookup_impl"]
    statement := "For every registry, search functions and name: PyCodec_KnownEncoding is whether codecs.lookup succeeds and never raises; on codec objects whose attributes are their items (as CodecInfo.__new__ makes them) PyCodec_Encoder/Decoder equal codecs.getencoder/getdecoder and PyCodec_StreamReader/Writer(name, stream, errors) equal codecs.getreader/getwriter(name)(stream[, errors]); PyCodec_IncrementalEncoder/Decoder(name, errors) equal codecs.getincrementalencoder/decoder(name)([errors]) except when the attribute is None, where Python raises LookupError(name) and C calls None."
    source := "invariant: the C API and its Lib/codecs.py twins; codecs.rst getencoder..getwriter"
    status := .proven, prop := ``CApiMatchesLib, thm := some ``cApiMatchesLib_proven
    notes := "The twins read different things: C the tuple items, Python the attributes. They part ways on a plain 4-tuple from a search function (no attributes) or on a CodecInfo whose attributes were reassigned; the statement takes ItemsMatchAttrs as the CodecInfo invariant. The None case is a design difference, recorded in the statement rather than filed." },
  { id := "unicodeobj-codecs-capi-matches-lib-all", pyFile := "Lib/codecs.py"
    pyFns := ["getencoder", "PyCodec_Encoder", "codec_getitem"]
    statement := "PyCodec_Encoder equals codecs.getencoder for every codec a search function returns, without the CodecInfo invariant."
    source := "_codecs.register docstring: a search function may return a tuple of functions"
    status := .refuted, prop := ``CApiMatchesLibAll, thm := some ``cApiMatchesLibAll_refuted
    bug := some "unicodeobj-codecs-getencoder-raw-tuple"
    notes := "On a plain 4-tuple C reads item 0 and codecs.encode works, Python asks for an encode attribute and raises AttributeError. codecs.rst says search functions return CodecInfo, so probably not a bug." },
  { id := "unicodeobj-codecs-escape-round-trip", pyFile := "Modules/_codecsmodule.c"
    pyFns := ["_codecs_escape_encode_impl", "_codecs_escape_decode_impl", "codec_tuple"]
    statement := "For every bytes object, codecs.escape_encode either raises OverflowError (only past PY_SSIZE_T_MAX/4 bytes) or returns escapes, with the input's length, that codecs.escape_decode decodes back to the input, with their own length."
    source := "invariant: round trip"
    status := .proven, prop := ``EscapeRoundTrip, thm := some ``escapeRoundTrip_proven
    notes := "escape_decode is PyBytes_DecodeEscape, modelled in BytesObj (decode_flat)." },
  { id := "unicodeobj-codecs-normalize-encoding-doc", pyFile := "Modules/_codecsmodule.c"
    pyFns := ["_codecs__normalize_encoding_impl"]
    statement := "_codecs._normalize_encoding (encodings.normalize_encoding since 3.15) collapses every run of non-alphanumeric characters other than '.' into one underscore and drops leading and trailing ones, for every ASCII name."
    source := "codecs.rst, encodings.normalize_encoding"
    status := .refuted, prop := ``NormalizeEncodingDoc, thm := some ``normalizeEncodingDoc_refuted
    bug := some "unicodeobj-codecs-normalize-encoding-nul"
    notes := "The C string handed to _Py_normalize_encoding ends at an embedded NUL: 'a\\x00b' gives 'a'; 3.14's Python version gave 'a_b'." }
]

end PyLean.UnicodeObj
