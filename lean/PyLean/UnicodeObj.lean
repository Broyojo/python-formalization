import PyLean.Registry
import PyLean.UnicodeObj.Diff
import PyLean.UnicodeObj.ObjectReg
import PyLean.UnicodeObj.CodecReg
import PyLean.UnicodeObj.FormatReg
import PyLean.UnicodeObj.TextReg

/-!
All of `Objects/unicodeobject.c`, `Objects/stringlib/`, `Objects/unicodectype.c`,
`Python/formatter_unicode.c`, CPython 3.14.7. The registry is split by slice:
`ObjectReg` (kinds, compare, concat, writer, iterators, stringlib glue),
`CodecReg` (codecs and error handlers), `FormatReg` (`%`, `str.format`, the format
spec mini-language) and `TextReg` (ctype, case mapping, translate, repr).
-/

namespace PyLean.UnicodeObj

open PyLean.Registry

def entries : List Entry := objectEntries ++ codecEntries ++ formatEntries ++ textEntries

end PyLean.UnicodeObj
