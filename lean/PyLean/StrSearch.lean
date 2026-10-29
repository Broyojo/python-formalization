import PyLean.Registry
import PyLean.StrSearch.Diff

/-!
Search and split methods of `str`, `bytes`, `bytearray`: `Objects/stringlib/`, `Objects/unicodeobject.c`, `Objects/bytes_methods.c`, CPython 3.14.7.
-/

namespace PyLean.StrSearch

open PyLean.Registry

def entries : List Entry := []

end PyLean.StrSearch
