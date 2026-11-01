import PyLean.Registry
import PyLean.BytesObj.Diff
import PyLean.BytesObj.Seq.Entries
import PyLean.BytesObj.Bytes.Entries
import PyLean.BytesObj.Mem.Entries

/-!
`Objects/tupleobject.c`, `Objects/bytesobject.c`, `Objects/bytearrayobject.c`, `Objects/bytes_methods.c`, `Objects/memoryobject.c`, all of `Objects/listobject.c`, CPython 3.14.7.
-/

namespace PyLean.BytesObj

open PyLean.Registry

def entries : List Entry := Seq.entries ++ Bytes.entries ++ Mem.entries

end PyLean.BytesObj
