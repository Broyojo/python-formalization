import PyLean.Registry
import PyLean.TypeObj.Diff

/-!
The data model: `Objects/typeobject.c`, `Objects/object.c`, `Objects/abstract.c`, `Objects/descrobject.c`, `Objects/funcobject.c`, `Objects/methodobject.c`, `Objects/classobject.c`, `Objects/exceptions.c`, CPython 3.14.7.
-/

namespace PyLean.TypeObj

open PyLean.Registry

def entries : List Entry := []

end PyLean.TypeObj
