import PyLean.Registry
import PyLean.UnicodeObj.CodecsErrNames

/-! Registry entries for `Python/codecs.c` and `Modules/_codecsmodule.c`. -/

namespace PyLean.UnicodeObj

open PyLean.Registry PyLean.UnicodeObj.Codecs

/-- The handler bodies and helpers every handler theorem below unfolds. -/
def handlerFns : List String :=
  ["PyCodec_StrictErrors", "_PyCodec_IgnoreError", "PyCodec_IgnoreErrors",
   "_PyCodec_ReplaceUnicodeEncodeError", "_PyCodec_ReplaceUnicodeDecodeError",
   "_PyCodec_ReplaceUnicodeTranslateError", "PyCodec_ReplaceErrors",
   "PyCodec_XMLCharRefReplaceErrors", "_PyCodec_BackslashReplaceUnicodeEncodeError",
   "_PyCodec_BackslashReplaceUnicodeDecodeError", "_PyCodec_BackslashReplaceUnicodeTranslateError",
   "PyCodec_BackslashReplaceErrors", "PyCodec_NameReplaceErrors",
   "_PyCodec_SurrogatePassUnicodeEncodeError", "_PyCodec_SurrogatePassUnicodeDecodeError",
   "PyCodec_SurrogatePassErrors", "_PyCodec_SurrogateEscapeUnicodeEncodeError",
   "_PyCodec_SurrogateEscapeUnicodeDecodeError", "PyCodec_SurrogateEscapeErrors",
   "strict_errors", "ignore_errors", "replace_errors", "xmlcharrefreplace_errors",
   "backslashreplace_errors", "namereplace_errors", "surrogatepass_errors", "surrogateescape_errors",
   "wrong_exception_type", "codec_handler_write_unicode_hex", "n_decimal_digits_for_codepoint",
   "codec_handler_unicode_replacement_character",
   "_PyUnicodeError_GetParams", "PyUnicodeDecodeError_GetEnd", "PyUnicodeEncodeError_GetEncoding",
   "PyUnicodeDecodeError_GetEncoding"]

def codecsEntries : List Entry := [
  { id := "unicodeobj-codecs-handlers-agree", pyFile := "Python/codecs.c"
    pyFns := handlerFns
    statement := "Each of the eight standard error handlers, called directly on an exception object of any class below UnicodeEncodeError (UnicodeDecodeError, UnicodeTranslateError) with any start and end, gives what the codec-loop model of the same handler gives for start clipped to [0, max(0, len-1)] and end clipped to [min(1, len), len], cut only by the guards against a replacement longer than PY_SSIZE_T_MAX."
    source := "invariant: a handler called by a codec and the same handler called directly are one function; codecs.rst error handler table"
    status := .proven, prop := ``HandlersAgree, thm := some ``handlersAgree_proven
    notes := "The codec-loop model (CodecHandlers.lean) is difftested through real encode and decode calls; this one through codecs.lookup_error(name)(exc) with mutated attributes (codecs_handler). The class test is PyObject_TypeCheck, a hierarchy oracle constrained by HierOk; builtinHier_ok shows HierOk is satisfiable. The encoding name only reaches surrogatepass, whose code is a hypothesis here." },
  { id := "unicodeobj-codecs-handlers-safe", pyFile := "Python/codecs.c"
    pyFns := handlerFns
    statement := "For every object handed to a standard handler, whatever its class and attributes, the handler raises only its argument (and only when that is an exception), a TypeError, the failure to load unicodedata's C API, or the UTF-8 encoder's error on the encoding attribute; a position it returns lies in [0, len(object)] and past the clipped start whenever the clipped range is not empty."
    source := "invariant: no internal error, results in range, codec loops make progress"
    status := .proven, prop := ``HandlersSafe, thm := some ``handlersSafe_proven
    notes := "namereplace needs names under 256 bytes (NAME_MAXLEN, the buffer of codecs.c:1091) for the progress half." },
  { id := "unicodeobj-codecs-handlers-total", pyFile := "Python/codecs.c"
    pyFns := handlerFns
    statement := "ignore, replace, backslashreplace, xmlcharrefreplace and namereplace succeed exactly when the class is one they take, the object attribute has the type that class needs, and (namereplace) unicodedata loads; on a class it does not take, every handler but strict raises wrong_exception_type's TypeError."
    source := "codecs.rst: the handlers replace; register_error: a handler must raise or return a replacement"
    status := .proven, prop := ``HandlersTotal, thm := some ``handlersTotal_proven },
  { id := "unicodeobj-codecs-buffers-exact", pyFile := "Python/codecs.c"
    pyFns := handlerFns ++ ["codec_handler_unicode_hex_width"]
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
    notes := "getname is called with with_alias_and_seq = 1, so the 942 Plane 15 private-use slots that hold aliases and named sequences get names: U+F0000 becomes \\N{NULL}." }
]

end PyLean.UnicodeObj
